import Lean4Lean.PtrEq

/-!
# A union-find whose links know the scope they rest on

The type checker learns equivalences under binders. An equivalence may rest on a variable of the
binder even when its terms do not mention it, so it must not outlive the binder's scope. Each link
records the deepest scope its justification used, as a label `(level, id)`: the level in the stack
of open scopes and the id of the scope open there. A link whose scope has ended is ignored, so
leaving a scope costs nothing.
-/

namespace Lean4Lean
open Lean

/-- The ids of the open scopes, outermost first: the scope at level `l > 0` is `ids[l-1]`. -/
abbrev Scopes := Array Nat

/-- A label `(l, id)` is current while its scope is open; level `0` always is. -/
@[inline] def Scopes.valid (ids : Scopes) (l id : Nat) : Bool := l == 0 || ids[l - 1]? == some id

/-- The id a label at level `l` gets: that of the scope open at `l`. A level beyond the open scopes
gets an id no scope has, so its label is never current. -/
@[inline] def Scopes.labelId (ids : Scopes) (l : Nat) : Nat :=
  if l == 0 then 0 else ids[l - 1]?.getD 0

/-- A union-find over terms whose links carry the label of the scope they rest on. -/
structure ScopedEquivManager where
  parent : Array Nat := #[]
  rank : Array Nat := #[]
  lvl : Array Nat := #[]
  sid : Array Nat := #[]
  toNodeMap : ExprMap Nat := {}

namespace ScopedEquivManager

/-- The link out of `n` is current. -/
@[inline] def linkOK (m : ScopedEquivManager) (ids : Scopes) (n : Nat) : Bool :=
  ids.valid (m.lvl[n]?.getD 0) (m.sid[n]?.getD 0)

/-- The root of `n` over current links, with the highest level of a link on the way. -/
def rootL (m : ScopedEquivManager) (ids : Scopes) (n : Nat) : Nat × Nat :=
  go m.parent.size n 0
where
  go : Nat → Nat → Nat → Nat × Nat
  | 0, n, l => (n, l)
  | k+1, n, l =>
    let p := m.parent[n]?.getD n
    if p == n || !m.linkOK ids n then (n, l) else go k p (max l (m.lvl[n]?.getD 0))

/-- The highest level of a link on current paths connecting two nodes, if they are connected. -/
def connLevel (m : ScopedEquivManager) (ids : Scopes) (n1 n2 : Nat) : Option Nat :=
  if n1 == n2 then some 0 else
  let (r1, l1) := m.rootL ids n1
  let (r2, l2) := m.rootL ids n2
  if r1 == r2 then some (max l1 l2) else none

def toNode (e : Expr) : StateM ScopedEquivManager Nat := fun m =>
  if let some r := m.toNodeMap[e]? then (r, m) else
  let r := m.parent.size
  (r, { m with parent := m.parent.push r, rank := m.rank.push 0, lvl := m.lvl.push 0,
               sid := m.sid.push 0, toNodeMap := m.toNodeMap.insert e r })

/-- Links `a` to `b` with the label at level `l`. -/
@[inline] def link (m : ScopedEquivManager) (ids : Scopes) (a b l : Nat) : ScopedEquivManager :=
  { m with parent := m.parent.set! a b, lvl := m.lvl.set! a l, sid := m.sid.set! a (ids.labelId l) }

/-- Records that `n1` and `n2` are equivalent at level `l`. The link joins their roots, so it rests
also on the links from each node to its root. -/
def merge (m : ScopedEquivManager) (ids : Scopes) (n1 n2 l : Nat) : ScopedEquivManager :=
  let (r1, l1) := m.rootL ids n1
  let (r2, l2) := m.rootL ids n2
  let l := max l (max l1 l2)
  if r1 == r2 || r1 ≥ m.parent.size || r2 ≥ m.parent.size then m else
  let k1 := m.rank[r1]?.getD 0
  let k2 := m.rank[r2]?.getD 0
  if k1 < k2 then m.link ids r1 r2 l
  else if k2 < k1 then m.link ids r2 r1 l
  else
    let m := m.link ids r1 r2 l
    { m with rank := m.rank.set! r2 (k2 + 1) }

end ScopedEquivManager

namespace ScopedEquivManager

/-- Records that `e1` and `e2` are equivalent at level `l`, or deeper if their free variables
belong to a deeper scope (`lv`). -/
def addEquiv (ids : Scopes) (lv : Expr → Nat) (e1 e2 : Expr) (l : Nat) :
    StateM ScopedEquivManager Unit := do
  let n1 ← toNode e1
  let n2 ← toNode e2
  modify (·.merge ids n1 n2 (max l (max (lv e1) (lv e2))))

/-- Both computations find an equivalence, at the deeper of their levels. -/
@[inline] def both (x : StateM ScopedEquivManager (Option Nat))
    (y : Unit → StateM ScopedEquivManager (Option Nat)) : StateM ScopedEquivManager (Option Nat) := do
  let some a ← x | return none
  let some b ← y () | return none
  return some (max a b)

/-- `e1` and `e2` are equivalent by current links, up to the structure of terms, with the deepest
level the equivalence rests on. -/
def isEquiv (ids : Scopes) (lv : Expr → Nat) (useHash : Bool) (e1 e2 : Expr) :
    StateM ScopedEquivManager (Option Nat) := do
  if ptrEqExpr e1 e2 then return some 0
  if useHash && e1.hash != e2.hash then return none
  if e1.isBVar && e2.isBVar then return if e1.bvarIdx! == e2.bvarIdx! then some 0 else none
  let n1 ← toNode e1
  let n2 ← toNode e2
  if let some l := (← get).connLevel ids n1 n2 then return some l
  let result ←
    match e1, e2 with
    | .const c1 l1, .const c2 l2 => pure <| if c1 == c2 && l1 == l2 then some 0 else none
    | .mvar a1, .mvar a2 | .fvar a1, .fvar a2
    | .sort a1, .sort a2 | .lit a1, .lit a2 => pure <| if a1 == a2 then some 0 else none
    | .app f1 a1, .app f2 a2 =>
      both (isEquiv ids lv useHash f1 f2) fun _ => isEquiv ids lv useHash a1 a2
    | .lam _ d1 b1 _, .lam _ d2 b2 _ =>
      both (isEquiv ids lv useHash d1 d2) fun _ => isEquiv ids lv useHash b1 b2
    | .mdata _ a1, .mdata _ a2 => isEquiv ids lv useHash a1 a2
    | .forallE _ d1 b1 _, .forallE _ d2 b2 _ =>
      both (isEquiv ids lv useHash d1 d2) fun _ => isEquiv ids lv useHash b1 b2
    | .proj s1 i1 e1, .proj s2 i2 e2 =>
      if s1 == s2 && i1 == i2 then isEquiv ids lv useHash e1 e2 else pure none
    | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
      both (both (isEquiv ids lv useHash t1 t2) fun _ => isEquiv ids lv useHash v1 v2)
        fun _ => isEquiv ids lv useHash b1 b2
    | _, _ => pure none
  let some l := result | return none
  -- the structural equivalence holds in the current scope, which the link records
  modify (·.merge ids n1 n2 ids.size)
  return some l
termination_by e1

end ScopedEquivManager

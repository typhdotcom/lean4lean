import Lean4Lean.Verify.Expr

/-!
Each `implemented_by`-style axiom in `Lean4Lean/Verify/Axioms.lean` equates a runtime function
with a Lean model. These checks run both on inputs chosen to reach the edge cases (loose bound
variables, metadata, out-of-range indices, empty arrays, levels with parameters and
metavariables) and fail the build if they disagree.
-/

namespace Lean4Lean.Tests.AxiomModels

open Lean

/-! ### Samples -/

private def lp : Level := .param `u
private def lm : Level := .mvar ⟨`m⟩

private def levels : Array Level := Id.run do
  let atoms : Array Level := #[.zero, lp, .param `v, lm, .succ .zero, .succ lp]
  let mut r := atoms
  for a in atoms do
    for b in atoms do
      r := r ++ #[.max a b, .imax a b, .succ (.max a b)]
  return r

private def md : MData := KVMap.empty.insert `k (.ofNat 1)
private def md' : MData := KVMap.empty.insert `k (.ofNat 2)

private def atoms : Array Expr := #[
  .bvar 0, .bvar 1, .bvar 2, .bvar 5, .fvar ⟨`x⟩, .fvar ⟨`y⟩, .mvar ⟨`m⟩,
  .sort .zero, .sort lp, .sort lm, .const `c [], .const `c [lp, lm], .lit (.natVal 3),
  .lit (.strVal "s")]

private def exprs : Array Expr := Id.run do
  let mut r := atoms
  for a in atoms do
    r := r.push (.mdata md a)
    r := r.push (.proj `S 1 a)
    for b in #[Expr.bvar 0, .bvar 1, .fvar ⟨`x⟩, .const `c []] do
      r := r ++ #[.app a b, .app b a, .lam `n a b .default, .forallE `n b a .implicit,
        .letE `n a b (.bvar 0) false, .letE `n b a (.app (.bvar 0) (.bvar 1)) true]
  r := r ++ #[
    .lam `a (.bvar 0) (.lam `b (.bvar 1) (.app (.bvar 0) (.app (.bvar 1) (.bvar 2))) .default)
      .default,
    .forallE `a (.sort lp) (.letE `b (.bvar 0) (.bvar 1) (.app (.bvar 0) (.bvar 3)) false) .default,
    .mdata md (.app (.mdata md' (.bvar 3)) (.proj `S 0 (.bvar 4)))]
  return r

private def substs : Array (Array Expr) := #[#[], #[.fvar ⟨`x⟩], #[.bvar 0], #[.bvar 0, .bvar 1],
  #[.bvar 1, .const `c []], #[.app (.bvar 0) (.bvar 2), .fvar ⟨`y⟩, .bvar 0]]

/-- Structural equality on every field, so that it does not rely on a modelled `BEq`. -/
private partial def same : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar a, .fvar b => a.name == b.name
  | .mvar a, .mvar b => a.name == b.name
  | .sort u, .sort v => u == v
  | .const c us, .const d vs => c == d && us == vs
  | .app f a, .app g b => same f g && same a b
  | .lam n t b i, .lam n' t' b' i' | .forallE n t b i, .forallE n' t' b' i' =>
    n == n' && i == i' && same t t' && same b b'
  | .letE n t v b d, .letE n' t' v' b' d' =>
    n == n' && d == d' && same t t' && same v v' && same b b'
  | .lit l, .lit l' => l == l'
  | .mdata m e, .mdata m' e' => m.entries.length == m'.entries.length && m == m' && same e e'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && same e e'
  | _, _ => false

/-- Structural equality of levels, so that it does not rely on the modelled `BEq`. -/
private def sameL : Level → Level → Bool
  | .zero, .zero => true
  | .succ a, .succ b => sameL a b
  | .max a b, .max c d | .imax a b, .imax c d => sameL a c && sameL b d
  | .param n, .param m => n == m
  | .mvar n, .mvar m => n.name == m.name
  | _, _ => false

/-! ### `Level` -/

#guard levels.all fun l => l.hasParam == l.hasParam'
#guard levels.all fun l => l.hasMVar == l.hasMVar'
#guard levels.all fun a => levels.all fun b => (a == b) == sameL a b

#guard [(0, 0, false, false), (12345, 7, true, false), (0xFFFFFFFFFFFF, 99, false, true),
    (3, Nat.pow 2 24 - 1, true, true)].all fun (h, d, m, p) =>
  Level.mkData h d m p == Level.mkData' h d m p

open private mkMaxAux skipExplicit isExplicitSubsumedAux from Lean.Level in
#guard
  let arrs : Array (Array Level) := #[#[], #[.zero], #[.zero, .succ .zero, lp], #[lp, .succ lp],
    #[.succ (.succ .zero), lp, .succ lp, .param `v]]
  arrs.all fun a => (List.range (a.size + 2)).all fun i =>
    skipExplicit a i == Level.Total.skipExplicit a i &&
    (List.range 4).all fun k => isExplicitSubsumedAux a k i == Level.Total.isExplicitSubsumedAux a k i &&
      mkMaxAux a k i lp 1 .zero == Level.Total.mkMaxAux a k i lp 1 .zero

/-! ### `Expr` -/

#guard exprs.all fun e => e.looseBVarRange == e.looseBVarRange'
#guard exprs.all fun e => (List.range 7).all fun i => e.hasLooseBVar i == e.hasLooseBVar' i
#guard exprs.all fun e => (List.range 3).all fun s => (List.range 3).all fun d =>
  same (e.liftLooseBVars s d) (e.liftLooseBVars' s d) &&
  same (e.lowerLooseBVars s d) (e.lowerLooseBVars' s d)
#guard exprs.all fun e => atoms.all fun a => same (e.instantiate1 a) (e.instantiate1' a)
#guard exprs.all fun e => substs.all fun s =>
  same (e.instantiate s) (e.instantiate' s.toList) && same (e.instantiateRev s) (e.instantiate s.reverse)
#guard exprs.all fun e => substs.all fun s => (List.range (s.size + 1)).all fun i =>
  (List.range (s.size + 1)).all fun j => i > j ||
    same (e.instantiateRange i j s) (e.instantiate (s.extract i j)) &&
    same (e.instantiateRevRange i j s) (e.instantiateRev (s.extract i j))
#guard exprs.all fun e => [[], [⟨`x⟩], [⟨`x⟩, ⟨`y⟩], [⟨`y⟩, ⟨`x⟩, ⟨`x⟩]].all fun xs =>
  same (e.abstract ⟨xs.map .fvar⟩) (e.abstract' xs) &&
  (List.range (xs.length + 2)).all fun n =>
    same (e.abstractRange n ⟨xs.map .fvar⟩) (e.abstract (Array.extract ⟨xs.map .fvar⟩ 0 n))
#guard exprs.all fun e => exprs.all fun e' =>
  e.eqv e' == e.eqv' e' && e.equal e' == e.eqv' e' (strict := true)
#guard
  let fs : Array (Expr → Option Expr) := #[fun _ => none,
    fun | .bvar i => some (.bvar (i + 1)) | _ => none,
    fun | .app f _ => some f | _ => none,
    fun e => if e.isFVar then some (.const `d []) else none]
  exprs.all fun e => fs.all fun f => same (e.replace f) (e.replaceNoCache f)
#guard exprs.all fun f => exprs.all fun a =>
  Expr.mkAppData f.data a.data == Expr.mkAppData' f.data a.data
#guard [(0, 0, 0), (7, 3, 255), (99, Nat.pow 2 20 - 1, 1000)].all fun (h, r, d) =>
  [false, true].all fun b => Expr.mkData h r d b (!b) b (!b) == Expr.mkData' h r d b (!b) b (!b)

/-! ### Containers -/

/-- `PersistentArrayNode.toList'`, by recursion the compiler accepts. -/
private partial def paNodeList : PersistentArrayNode α → List α
  | .node cs => cs.toList.flatMap paNodeList
  | .leaf vs => vs.toList

private def paList (a : PersistentArray α) : List α := paNodeList a.root ++ a.tail.toList

-- `toList'_push`, across the leaf and branching boundaries.
#guard (List.range 2100).foldl (init := (true, (.empty : PersistentArray Nat))) (fun (ok, a) i =>
  (ok && paList (a.push i) == paList a ++ [i], a.push i)) |>.1

/-- `PersistentHashMap.Node.toList'`, by recursion the compiler accepts. -/
private partial def phNodeList : PersistentHashMap.Node α β → List (α × β)
  | .entries es => es.toList.flatMap fun
    | .entry a b => [(a, b)]
    | .ref n => phNodeList n
    | .null => []
  | .collision ks vs _ => ks.toList.zip vs.toList

private structure Key where
  n : Nat
  deriving BEq, Repr

/-- Every key collides, so the map is a collision node. -/
private instance : Hashable Key := ⟨fun _ => 7⟩

private def phCheck {α} [BEq α] [Hashable α] (keys : List α) : Bool :=
  (keys.zipIdx.foldl (init := (true, (.empty : PersistentHashMap α Nat))) fun (ok, m) (k, i) =>
    let m' := m.insert k i
    (ok && (phNodeList m'.root).isPerm ((k, i) :: (phNodeList m.root).filter (!k == ·.1)) &&
      keys.all fun k' => m'.find? k' == (phNodeList m'.root).lookup k' &&
        m'.contains k' == (m'.find? k').isSome, m')).1

-- `WF.toList'_insert`, `WF.find?_eq` and `findAux_isSome`, with repeated keys, deep tries and a
-- collision node.
#guard phCheck ((List.range 300).map (· * 7919 % 1000) ++ [3, 3, 17])
#guard phCheck ((List.range 40).map fun i => Key.mk (i % 25))

-- `TreeMap.all_eq_all_toList`, `any_eq_any_toList`.
#guard
  let t : Std.TreeMap Nat Nat := (List.range 50).foldl (fun t i => t.insert (i * 37 % 50) i) {}
  [fun a b => decide (a < b), fun a b => decide (a + b > 60), fun _ _ => true, fun _ _ => false].all
    fun p => t.all p == t.toList.all (fun a => p a.1 a.2) && t.any p == t.toList.any (fun a => p a.1 a.2)

-- `Syntax.structEq_eq`.
#guard
  let ss : List Syntax := [.missing, .atom .none "a", .atom .none "b", mkIdent `x, mkIdent `y,
    .node .none `k #[], .node .none `k #[.atom .none "a"], .node .none `k #[.atom .none "a", .missing],
    .node .none `k' #[.atom .none "a"], .node .none `k #[.node .none `k #[mkIdent `x]]]
  ss.all fun a => ss.all fun b => Syntax.structEq a b == Syntax.structEq' a b

end Lean4Lean.Tests.AxiomModels

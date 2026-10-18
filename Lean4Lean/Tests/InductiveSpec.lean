import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.Typing.Lemmas

/-!
The recursors and iota rules `VEnv.addInduct` specifies, compared with the ones the kernel
generated for the same declarations: the recursor's type, and each rule's right-hand side, which
is the right-hand side of the spec's iota rule. Then projections: their types and rules in the
typing judgment, against what the kernel accepts.
-/

namespace Lean4Lean.Tests.InductiveSpec
open Lean Elab Term

deriving instance BEq for VLevel
deriving instance BEq for VExpr

deriving instance Inhabited for VField, VConstructor, VInductiveType

/-- A recursor's type, with its level parameters in the kernel's order. -/
elab "vrec% " c:ident : term => do
  let some (.recInfo r) := (← getEnv).find? (← realizeGlobalConstNoOverload c)
    | throwError "{c} is not a recursor"
  return toExpr (⟨r.levelParams.length, ← Lean4Lean.Meta.ofExpr r.levelParams {} r.type⟩ : VConstant)

/-- The right-hand sides of a recursor's rules, as the kernel generated them. -/
elab "vrules% " c:ident : term => do
  let some (.recInfo r) := (← getEnv).find? (← realizeGlobalConstNoOverload c)
    | throwError "{c} is not a recursor"
  let es ← r.rules.mapM fun rule => Lean4Lean.Meta.ofExpr r.levelParams {} rule.rhs
  return toExpr es

/-- Check the `i`th recursor, and the iota rules of its constructors, at block levels `ls` and
motive sort `v` (the levels the kernel's recursor was generated at). -/
def check (d : VInductDecl) (ls : List VLevel) (v : VLevel) (i : Nat)
    (recType : VConstant) (rules : List VExpr) : Bool := Id.run do
  let some T := d.types[i]? | return false
  let recLs := VLevel.params recType.uvars
  let ours := d.ctors.zipIdx.filterMap fun ((j, c), q) =>
    if j = i then some (d.iotaRule ls v recLs q j c).rhs else none
  d.recType ls v i T == recType.type && ours == rules

def _root_.Lean4Lean.VLevel.toLevel' (ns : List Name) : VLevel → Level
  | .zero => .zero
  | .succ l => .succ (l.toLevel' ns)
  | .max a b => .max (a.toLevel' ns) (b.toLevel' ns)
  | .imax a b => .imax (a.toLevel' ns) (b.toLevel' ns)
  | .param i => .param (ns.getD i .anonymous)

def _root_.Lean4Lean.VExpr.toExpr' (ns : List Name) : VExpr → Expr
  | .bvar i => .bvar i
  | .sort u => .sort (u.toLevel' ns)
  | .const c us => .const c (us.map (·.toLevel' ns))
  | .app f a => .app (f.toExpr' ns) (a.toExpr' ns)
  | .lam A b => .lam `x (A.toExpr' ns) (b.toExpr' ns) .default
  | .forallE A b => .forallE `x (A.toExpr' ns) (b.toExpr' ns) .default
  | .proj s i e => .proj s i (e.toExpr' ns)

/-- Have Lean's kernel check a rule: both sides have the stated type, and are defeq. -/
def checkDefEq (df : VDefEq) : MetaM Unit := do
  let ns := (List.range df.uvars).map (Name.mkSimple s!"u{·}")
  let ty := df.type.toExpr' ns
  let lhs := df.lhs.toExpr' ns
  let rhs := df.rhs.toExpr' ns
  for (n, v) in [(`lhs, lhs), (`rhs, rhs)] do
    let n ← mkFreshUserName n
    let decl := .defnDecl
      { name := n, levelParams := ns, type := ty, value := v, hints := .opaque, safety := .safe }
    match (← getEnv).addDeclCore 0 512 decl none with
    | .ok _ => pure ()
    | .error e => throwError "{n} does not check: {e.toMessageData {}}"
  unless Kernel.isDefEqGuarded (← getEnv) {} lhs rhs do
    throwError "sides are not defeq:{indentExpr lhs}\n{indentExpr rhs}"

/-- Check every iota rule of `d`, with the recursor at `recUVars` levels. -/
def checkIota (d : VInductDecl) (ls : List VLevel) (v : VLevel) (recUVars : Nat) : MetaM Unit :=
  for ((j, c), q) in d.ctors.zipIdx do
    checkDefEq (d.iotaRule ls v (VLevel.params recUVars) q j c)

/-! `Nat`: a recursive field. -/

def natDecl : VInductDecl where
  uvars := 0
  params := []
  level := .succ .zero
  types := [{
    name := ``Nat
    type := vexpr(Type)
    indices := []
    ctors := [
      { name := ``Nat.zero, type := vexpr(Nat), fields := [], indices := [] },
      { name := ``Nat.succ, type := vexpr(Nat → Nat), indices := []
        fields := [{ type := vexpr(Nat), level := .succ .zero, recArg := some ⟨[], 0, []⟩ }] }] }]
  isRec := true
  largeElim := true
  isUnsafe := false

#guard check natDecl [] (.param 0) 0 (vrec% Nat.rec) (vrules% Nat.rec)
run_meta checkIota natDecl [] (.param 0) 1

/-! `List`: a parameter. -/

def listDecl : VInductDecl where
  uvars := 1
  params := [.sort (.succ (.param 0))]
  level := .succ (.param 0)
  types := [{
    name := ``List
    type := vexpr(type_of% @List)
    indices := []
    ctors := [
      { name := ``List.nil, type := vexpr(type_of% @List.nil), fields := [], indices := [] },
      { name := ``List.cons, type := vexpr(type_of% @List.cons), indices := []
        fields := [
          { type := .bvar 0, level := .succ (.param 0), recArg := none },
          { type := .app (.const ``List [.param 0]) (.bvar 1), level := .succ (.param 0)
            recArg := some ⟨[], 0, []⟩ }] }] }]
  isRec := true
  largeElim := true
  isUnsafe := false

#guard check listDecl [.param 1] (.param 0) 0 (vrec% List.rec) (vrules% List.rec)
run_meta checkIota listDecl [.param 1] (.param 0) 2

/-! `Eq`: an index, and elimination from `Prop` into every sort. -/

def eqDecl : VInductDecl where
  uvars := 1
  params := [.sort (.param 0), .bvar 0]
  level := .zero
  types := [{
    name := ``Eq
    type := vexpr(type_of% @Eq)
    indices := [.bvar 1]
    ctors := [{
      name := ``Eq.refl, type := vexpr(type_of% @Eq.refl), fields := [], indices := [.bvar 0] }] }]
  isRec := false
  largeElim := true
  isUnsafe := false

#guard check eqDecl [.param 1] (.param 0) 0 (vrec% Eq.rec) (vrules% Eq.rec)
run_meta checkIota eqDecl [.param 1] (.param 0) 2

/-! `And`: a structure in `Prop` with proof fields, so it eliminates into every sort. -/

def andDecl : VInductDecl where
  uvars := 0
  params := [.sort .zero, .sort .zero]
  level := .zero
  types := [{
    name := ``And
    type := vexpr(type_of% @And)
    indices := []
    ctors := [{
      name := ``And.intro, type := vexpr(type_of% @And.intro), indices := []
      fields := [
        { type := .bvar 1, level := .zero, recArg := none },
        { type := .bvar 1, level := .zero, recArg := none }] }] }]
  isRec := false
  largeElim := true
  isUnsafe := false

#guard check andDecl [] (.param 0) 0 (vrec% And.rec) (vrules% And.rec)
run_meta checkIota andDecl [] (.param 0) 1

/-! `Or`: two constructors in `Prop`, so it eliminates only into `Prop`. -/

def orDecl : VInductDecl where
  uvars := 0
  params := [.sort .zero, .sort .zero]
  level := .zero
  types := [{
    name := ``Or
    type := vexpr(type_of% @Or)
    indices := []
    ctors := [
      { name := ``Or.inl, type := vexpr(type_of% @Or.inl), indices := []
        fields := [{ type := .bvar 1, level := .zero, recArg := none }] },
      { name := ``Or.inr, type := vexpr(type_of% @Or.inr), indices := []
        fields := [{ type := .bvar 0, level := .zero, recArg := none }] }] }]
  isRec := false
  largeElim := false
  isUnsafe := false

#guard check orDecl [] .zero 0 (vrec% Or.rec) (vrules% Or.rec)
run_meta checkIota orDecl [] .zero 0

/-! A reflexive type: the recursive field is a function. -/

inductive W where
  | leaf
  | sup (f : Nat → W)

def wDecl : VInductDecl where
  uvars := 0
  params := []
  level := .succ .zero
  types := [{
    name := ``W
    type := vexpr(Type)
    indices := []
    ctors := [
      { name := ``W.leaf, type := vexpr(W), fields := [], indices := [] },
      { name := ``W.sup, type := vexpr((Nat → W) → W), indices := []
        fields := [{ type := vexpr(Nat → W), level := .succ .zero
                     recArg := some ⟨[vexpr(Nat)], 0, []⟩ }] }] }]
  isRec := true
  largeElim := true
  isUnsafe := false

#guard check wDecl [] (.param 0) 0 (vrec% W.rec) (vrules% W.rec)
run_meta checkIota wDecl [] (.param 0) 1

/-! A mutual block. -/

mutual
inductive A where
  | base
  | mk (b : B)
inductive B where
  | mk (a : A) (n : Nat)
end

def abDecl : VInductDecl where
  uvars := 0
  params := []
  level := .succ .zero
  types := [
    { name := ``A, type := vexpr(Type), indices := []
      ctors := [
        { name := ``A.base, type := vexpr(A), fields := [], indices := [] },
        { name := ``A.mk, type := vexpr(B → A), indices := []
          fields := [{ type := vexpr(B), level := .succ .zero, recArg := some ⟨[], 1, []⟩ }] }] },
    { name := ``B, type := vexpr(Type), indices := []
      ctors := [
        { name := ``B.mk, type := vexpr(A → Nat → B), indices := []
          fields := [
            { type := vexpr(A), level := .succ .zero, recArg := some ⟨[], 0, []⟩ },
            { type := vexpr(Nat), level := .succ .zero, recArg := none }] }] }]
  isRec := true
  largeElim := true
  isUnsafe := false

#guard check abDecl [] (.param 0) 0 (vrec% A.rec) (vrules% A.rec)
#guard check abDecl [] (.param 0) 1 (vrec% B.rec) (vrules% B.rec)
run_meta checkIota abDecl [] (.param 0) 1

/-! An indexed family with a recursive field whose index is not a variable. -/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α Nat.zero
  | cons (a : α) (n : Nat) (v : Vec α n) : Vec α n.succ

def vecDecl : VInductDecl where
  uvars := 0
  params := [vexpr(Type)]
  level := .succ .zero
  types := [{
    name := ``Vec
    type := vexpr(Type → Nat → Type)
    indices := [vexpr(Nat)]
    ctors := [
      { name := ``Vec.nil, type := vexpr(type_of% @Vec.nil), fields := []
        indices := [.const ``Nat.zero []] },
      { name := ``Vec.cons, type := vexpr(type_of% @Vec.cons)
        indices := [.app (.const ``Nat.succ []) (.bvar 1)]
        fields := [
          { type := .bvar 0, level := .succ .zero, recArg := none },
          { type := vexpr(Nat), level := .succ .zero, recArg := none },
          { type := .app (.app (.const ``Vec []) (.bvar 2)) (.bvar 0), level := .succ .zero
            recArg := some ⟨[], 0, [.bvar 0]⟩ }] }] }]
  isRec := true
  largeElim := true
  isUnsafe := false

#guard check vecDecl [] (.param 0) 0 (vrec% Vec.rec) (vrules% Vec.rec)
run_meta checkIota vecDecl [] (.param 0) 1

/-! Projections: the type `projDF` gives a field, and the kernel's iota and eta for them. -/

structure P2 where
  a : Nat
  b : Fin a

def p2Decl : VInductDecl where
  uvars := 0
  params := []
  level := .succ .zero
  types := [{
    name := ``P2
    type := vexpr(Type)
    indices := []
    ctors := [{
      name := ``P2.mk, type := vexpr(type_of% @P2.mk), indices := []
      fields := [
        { type := vexpr(Nat), level := .succ .zero, recArg := none },
        { type := .app (.const ``Fin []) (.bvar 0), level := .succ .zero, recArg := none }] }] }]
  isRec := false
  largeElim := true
  isUnsafe := false

def p2 : VInductiveType := p2Decl.types[0]!
def p2mk : VConstructor := p2.ctors[0]!

#guard p2mk.projType [] ``P2 0 [] (.bvar 0) == vexpr(Nat)
#guard p2mk.projType [] ``P2 1 [] (.bvar 0) == .app (.const ``Fin []) (.proj ``P2 0 (.bvar 0))

run_meta checkIota p2Decl [] (.param 0) 1

-- `projIota`, at the second field: `(P2.mk a b).2 ≡ b`, at the field's `projType`
run_meta do
  let mk : VExpr := .appN (.const ``P2.mk []) [.bvar 1, .bvar 0]
  checkDefEq {
    uvars := 0,
    lhs := .lam vexpr(Nat) (.lam vexpr(n ⊢ Fin n) (.proj ``P2 1 mk)),
    rhs := .lam vexpr(Nat) (.lam vexpr(n ⊢ Fin n) (.bvar 0)),
    type := .forallE vexpr(Nat) (.forallE vexpr(n ⊢ Fin n) (p2mk.projType [] ``P2 1 [] mk)) }

-- `projEta`: `p ≡ P2.mk p.1 p.2`
run_meta checkDefEq {
  uvars := 0,
  lhs := .lam vexpr(P2) (.bvar 0),
  rhs := .lam vexpr(P2) (.appN (.const ``P2.mk []) (VExpr.projs ``P2 2 (.bvar 0))),
  type := vexpr(P2 → P2) }

/-- Add a declaration to Lean's kernel, reporting whether it accepts it. -/
def kernelAccepts (decl : Declaration) : CoreM Bool := do
  match (← getEnv).addDeclCore 0 512 decl none with
  | .ok _ => return true
  | .error _ => return false

/-- Have Lean's kernel check `fun x : T => x.i : F`, reporting whether it accepts it. -/
def projAccepted (T : Expr) (s : Name) (i : Nat) (F : Expr) : CoreM Bool :=
  kernelAccepts <| .defnDecl {
    name := `_proj, levelParams := [], type := .forallE `x T F .default,
    value := .lam `x T (.proj s i (.bvar 0)) .default, hints := .opaque, safety := .safe }

/-! `Foo.{u} : Sort u` with a field of type `PUnit.{u}`. Its recursor eliminates only into `Prop`,
but the kernel decides whether a projection is restricted at the instance's sort: `Foo.{1}`'s
instances are never propositions, so its projection is allowed. -/

run_cmd Command.liftTermElabM do
  let u := Level.param `u
  let mk : Constructor :=
    { name := `Foo.mk, type := .forallE `x (.const ``PUnit [u]) (.const `Foo [u]) .default }
  addDecl <| .inductDecl [`u] 0 [{ name := `Foo, type := .sort u, ctors := [mk] }] false

-- `Foo.rec` has no motive level of its own: it eliminates only into `Prop`
#guard_msgs in run_meta do
  unless (← getConstInfoRec `Foo.rec).levelParams == [`u] do throwError "Foo.rec eliminates large"

#guard_msgs in run_meta do
  unless ← projAccepted (.const `Foo [(1 : Level)]) `Foo 0 (.const ``PUnit [(1 : Level)]) do
    throwError "the kernel rejects Foo.\{1}.1"

def fooDecl : VInductDecl where
  uvars := 1
  params := []
  level := .param 0
  types := [{
    name := `Foo
    type := .sort (.param 0)
    indices := []
    ctors := [{
      name := `Foo.mk, type := .forallE (.const ``PUnit [.param 0]) (.const `Foo [.param 0])
      indices := []
      fields := [{ type := .const ``PUnit [.param 0], level := .param 0, recArg := none }] }] }]
  isRec := false
  largeElim := false
  isUnsafe := false

/-- The model types `Foo.{1}.1` too, in any environment that records `Foo`'s block. -/
example {env : VEnv} (hS : env.inducts `Foo = some (fooDecl, 0))
    (hFoo : env.constants `Foo = some ⟨1, .sort (.param 0)⟩)
    (hPUnit : env.constants ``PUnit = some ⟨1, .sort (.param 0)⟩) :
    env.HasType 0 [.const `Foo [.succ .zero]] (.proj `Foo 0 (.bvar 0))
      (.const ``PUnit [.succ .zero]) := by
  have hls : ∀ l ∈ [VLevel.succ .zero], l.WF 0 := by simp [VLevel.WF]
  exact .projDF (As := []) (As' := []) (I := []) (I' := []) (k := 0) (e := .bvar 0) (e' := .bvar 0) hS rfl rfl rfl hls rfl rfl rfl rfl rfl
    (VEnv.HasType.const hFoo hls rfl) (.bvar (by simpa using .zero))
    (fun h => (h fun _ => by simp [fooDecl, VLevel.inst, VLevel.eval]).elim)
    (VEnv.HasType.const hPUnit hls rfl)

/-! A proposition with a data field `n` and proof fields `h : True` and `h' : n = n`. Projecting
`n`, or `h'`, whose type depends on it, is refused. The kernel refuses `h` too, since a field after
it depends on `n`; `projDF` allows it, since fields after the projected one do not bear on it. -/

inductive Ex : Prop
  | mk (n : Nat) (h : True) (h' : n = n)

def exMk : VConstructor where
  name := ``Ex.mk
  type := vexpr(type_of% @Ex.mk)
  indices := []
  fields := [
    { type := vexpr(Nat), level := .succ .zero, recArg := none },
    { type := vexpr(True), level := .zero, recArg := none },
    { type := .appN (.const ``Eq [.succ .zero]) [vexpr(Nat), .bvar 1, .bvar 1], level := .zero
      recArg := none }]

def exDecl : VInductDecl where
  uvars := 0
  params := []
  level := .zero
  types := [{ name := ``Ex, type := vexpr(Prop), indices := [], ctors := [exMk] }]
  isRec := false
  largeElim := false
  isUnsafe := false

#guard_msgs in run_meta do
  let ex : Expr := .const ``Ex []
  let ok ← [(0, .const ``Nat []), (1, .const ``True []), (2, mkApp3 (.const ``Eq [1])
    (.const ``Nat []) (.proj ``Ex 0 (.bvar 0)) (.proj ``Ex 0 (.bvar 0)))].mapM fun (i, F) =>
    projAccepted ex ``Ex i F
  unless ok == [false, false, false] do throwError "the kernel accepts {ok}"

example : ¬exDecl.ProjAllowed exMk [] 0 := fun h => by
  have := (h fun h => h [] rfl).1 _ rfl
  simp [VLevel.equiv_def, VLevel.inst, VLevel.eval] at this

example : exDecl.ProjAllowed exMk [] 1 := fun _ =>
  ⟨fun _ h => by cases h; rfl, fun
    | 0, _, _, _ => .inr fun
      | 1, _, _, _, h => by cases h; rfl
      | 0, _, h, _, _ | _+2, _, _, h, _ => by omega⟩

example : ¬exDecl.ProjAllowed exMk [] 2 := fun h => by
  rcases (h fun h => h [] rfl).2 0 (by omega) _ rfl with h | h
  · simp [VLevel.equiv_def, VLevel.inst, VLevel.eval] at h
  · have := h 2 _ (by omega) (Nat.le_refl _) rfl
    simp [VExpr.Skips, VExpr.unliftN, VExpr.appN, VExpr.inst, VExpr.instVar, VExpr.liftN] at this

end Lean4Lean.Tests.InductiveSpec

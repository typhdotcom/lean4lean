import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Meta

/-!
The recursors and iota rules `VEnv.addInduct` specifies, compared with the ones the kernel
generated for the same declarations: the recursor's type, and each rule's right-hand side, which
is the right-hand side of the spec's iota rule.
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

/-! Projections, as eta states them, against the recursor applications one would write. -/

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

#guard p2Decl.proj p2 p2mk 1 0 (.bvar 0) ==
  vexpr(p ⊢ @P2.rec.{1} (fun _ => Nat) (fun a _ => a) p)
#guard p2Decl.proj p2 p2mk 1 1 (.bvar 0) ==
  vexpr(p ⊢ @P2.rec.{1} (fun p => Fin (@P2.rec.{1} (fun _ => Nat) (fun a _ => a) p))
    (fun _ b => b) p)

run_meta checkIota p2Decl [] (.param 0) 1
run_meta checkDefEq (p2Decl.etaRule p2 p2mk)

end Lean4Lean.Tests.InductiveSpec

import Lean4Lean.Environment

/-!
A constructor's field domains with an annotation whose default value mentions an earlier field,
and with `let`s, dead and used, mentioning earlier fields. `checkConstructors` also checks each
domain without its `let`s and with its annotations stripped, and opens the field at that view. Both
kernels accept the structure, and its projections and a recursor application check.

Checking the views is a divergence: Lean's kernel accepts `DeadS` below, which lean4lean rejects.
-/

namespace Lean4Lean.Tests.FieldViews

open Lean

private def nat : Expr := .const ``Nat []
private def S : Expr := .const `S []

/-- `S.mk (n : Nat) (m : optParam Nat n) (k : let x := n; Nat) (h : let y := m; y = y) : S`. -/
private def mkType : Expr :=
  .forallE `n nat (.forallE `m (mkApp2 (.const ``optParam [1]) nat (.bvar 0))
    (.forallE `k (.letE `x nat (.bvar 1) nat false)
      (.forallE `h (.letE `y nat (.bvar 1) (mkApp3 (.const ``Eq [1]) nat (.bvar 0) (.bvar 0)) false)
        S .default) .default) .default) .default

private def blockDecl : Declaration :=
  .inductDecl [] 0 [{ name := `S, type := .sort 1, ctors := [{ name := `S.mk, type := mkType }] }]
    false

/-- `fun s : S => (s.2 : Nat)`, through the projection of the field with a default value. -/
private def useVal : DefinitionVal :=
  { name := `S.useM, levelParams := [],
    type := .forallE `s S nat .default,
    value := .lam `s S (.proj `S 1 (.bvar 0)) .default, hints := .«abbrev», safety := .safe }

/-- The fourth projection, whose declared domain is a `let` mentioning the second field. -/
private def useHVal : DefinitionVal :=
  { name := `S.useH, levelParams := [],
    type := .forallE `s S (mkApp3 (.const ``Eq [1]) nat (.proj `S 1 (.bvar 0)) (.proj `S 1 (.bvar 0)))
      .default,
    value := .lam `s S (.proj `S 3 (.bvar 0)) .default, hints := .«abbrev», safety := .safe }

run_meta do
  let env := (← getEnv).toKernelEnv
  let mut kenv := env
  let mut lenv := env
  for d in [blockDecl, .defnDecl useVal, .defnDecl useHVal] do
    let .ok kenv' := kenv.addDecl {} d | throwError "Lean's kernel rejected a declaration"
    kenv := kenv'
    match Lean4Lean.addDecl lenv d with
    | .ok lenv' => lenv := lenv'
    | .error e => throwError "lean4lean rejected a declaration: {← (e.toMessageData {}).toString}"

namespace Dead

open Meta

axiom B : Type
axiom b0 : B
axiom A : B → Type
axiom P : A b0 → Prop
inductive I : (n : B) → A n → Prop | mk (x : A b0) (h : P x) : I b0 x
noncomputable def F (a : A b0) (h : I b0 a) : B :=
  I.rec (motive := fun _ _ _ => B) (fun _ _ => b0) h
axiom C : B → Type
axiom D : Type
axiom k : (n : B) → C n → C n → Unit
def G (n : B) : Type := C n
axiom T : G b0 → Prop

/-- `DeadS a hI c0 d0 g : Prop` with fields `x : D` and
`h : let y : Unit := k (F a (I.mk a (g x))) c0 d0; T (@id (G b0) c0)`. Checking the dead `let`'s
value with `x` in scope learns `C (F a hI) ≡ C b0`, through `I.mk a (g x)`, and the body is a type
only with it. Without its `let`, `h`'s domain does not mention `x`. -/
def mkDecl : MetaM Declaration := do
  let S := mkConst `DeadS
  let params {α} (k : Expr → Expr → Expr → Expr → Expr → MetaM α) : MetaM α :=
    withLocalDeclD `a (mkApp (mkConst ``A) (mkConst ``b0)) fun a =>
    withLocalDeclD `hI (mkApp2 (mkConst ``I) (mkConst ``b0) a) fun hI =>
    withLocalDeclD `c0 (mkApp (mkConst ``C) (mkApp2 (mkConst ``F) a hI)) fun c0 =>
    withLocalDeclD `d0 (mkApp (mkConst ``C) (mkConst ``b0)) fun d0 =>
    withLocalDeclD `g (.forallE `d (mkConst ``D) (mkApp (mkConst ``P) a) .default) fun g =>
      k a hI c0 d0 g
  let ty ← params fun a hI c0 d0 g => mkForallFVars #[a, hI, c0, d0, g] (.sort 0)
  let cty ← params fun a hI c0 d0 g => withLocalDeclD `x (mkConst ``D) fun x => do
    let kk := mkApp3 (mkConst ``k) (mkApp2 (mkConst ``F) a (mkApp2 (mkConst ``I.mk) a (mkApp g x)))
      c0 d0
    let gb0 := mkApp (mkConst ``G) (mkConst ``b0)
    let body := mkApp (mkConst ``T) (mkApp2 (mkConst ``id [1]) gb0 c0)
    let hty ← Meta.withLetDecl `y (mkConst ``Unit) kk fun y =>
      mkLetFVars #[y] body (usedLetOnly := false)
    withLocalDeclD `h hty fun h => mkForallFVars #[a, hI, c0, d0, g, x, h] (mkApp5 S a hI c0 d0 g)
  let ctor : Constructor := { name := `DeadS.mk, type := cty }
  return .inductDecl [] 5 [{ name := `DeadS, type := ty, ctors := [ctor] }] false

run_meta do
  let d ← mkDecl
  let kenv := (← getEnv).toKernelEnv
  unless (kenv.addDecl {} d) matches .ok _ do throwError "Lean's kernel rejected `DeadS`"
  if let .ok _ := Lean4Lean.addDecl kenv d then throwError "lean4lean accepted `DeadS`"

end Dead

end Lean4Lean.Tests.FieldViews

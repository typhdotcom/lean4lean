import Lean4Lean.Environment

/-!
Structure eta for a structure that may be a proposition, with a field that is not a proof. Its
projections are not typed (`inferProj` refuses them). Lean's kernel compares them with the
constructor's arguments anyway, inferring their types without the check; lean4lean declines
eta there rather than compare a projection it does not type (see `divergences.md`). Both report
the same type mismatch for this declaration, which is false.
-/

namespace Lean4Lean.Tests.MaybePropEta

open Lean

private def u : Level := .param `u

/-- `Foo.{u} (α : Sort u) : Sort u` with a field `x : α`. -/
private def fooDecl : Declaration :=
  .inductDecl [`u] 1 [{
    name := `Foo
    type := .forallE `α (.sort u) (.sort u) .default
    ctors := [{
      name := `Foo.mk
      type := .forallE `α (.sort u) (.forallE `x (.bvar 0) (mkApp (.const `Foo [u]) (.bvar 1))
        .default) .implicit }] }] false

/-- `∀ (α : Sort u) (a : Foo α) (b : α), a = Foo.mk b`, by `rfl`: checking it compares `a` with a
constructor application, which tries eta. -/
private def thmDecl : Declaration :=
  let fooα := mkApp (.const `Foo [u]) (.bvar 0)
  .thmDecl {
    name := `fooEta, levelParams := [`u]
    type := .forallE `α (.sort u) (.forallE `a fooα (.forallE `b (.bvar 1)
      (mkApp3 (.const ``Eq [u]) (mkApp (.const `Foo [u]) (.bvar 2)) (.bvar 1)
        (mkApp2 (.const `Foo.mk [u]) (.bvar 2) (.bvar 0))) .default) .default) .default
    value := .lam `α (.sort u) (.lam `a fooα (.lam `b (.bvar 1)
      (mkApp2 (.const ``Eq.refl [u]) (mkApp (.const `Foo [u]) (.bvar 2)) (.bvar 1)) .default)
      .default) .default }

#eval show MetaM Unit from do
  let env := (← getEnv).toKernelEnv
  let .ok kenv := env.addDecl {} fooDecl | throwError "Lean's kernel rejected `Foo`"
  let .ok lenv := Lean4Lean.addDecl env fooDecl | throwError "lean4lean rejected `Foo`"
  if let .ok _ := kenv.addDecl {} thmDecl then throwError "Lean's kernel accepted `fooEta`"
  match Lean4Lean.addDecl lenv thmDecl with
  | .ok _ => throwError "lean4lean accepted `fooEta`"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    if (msg.splitOn "invalid projection").length > 1 then
      throwError "lean4lean typed a projection it does not allow: {msg}"

end Lean4Lean.Tests.MaybePropEta

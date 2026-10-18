import Lean4Lean.Environment

/-!
Quotients are safe constants whose types mention `Eq`. With a prelude that declares `Eq` as an
unsafe inductive, Lean's kernel initializes quotients anyway; lean4lean rejects the
initialization (see `divergences.md`).
-/

namespace Lean4Lean.Tests.UnsafeEq

open Lean

private def u : Level := .param `u

/-- `{α : Sort u} → α → α → Prop` -/
private def eqType : Expr :=
  .forallE `α (.sort u) (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.sort .zero) .default)
    .default) .implicit

/-- `∀ {α : Sort u} (a : α), @Eq α a a` -/
private def reflType : Expr :=
  .forallE `α (.sort u) (.forallE `a (.bvar 0)
    (mkApp3 (.const ``Eq [u]) (.bvar 1) (.bvar 0) (.bvar 0)) .default) .implicit

private def eqDecl (isUnsafe : Bool) : Declaration :=
  .inductDecl [`u] 2
    [{ name := ``Eq, type := eqType, ctors := [{ name := ``Eq.refl, type := reflType }] }] isUnsafe

private def run (isUnsafe : Bool) : MetaM Unit := do
  let env := (← mkEmptyEnvironment).toKernelEnv
  let .ok kenv := env.addDecl {} (eqDecl isUnsafe) | throwError "Lean's kernel rejected `Eq`"
  let .ok lenv := Lean4Lean.addDecl env (eqDecl isUnsafe) | throwError "lean4lean rejected `Eq`"
  let .ok _ := kenv.addDecl {} .quotDecl | throwError "Lean's kernel now rejects quotients"
  match Lean4Lean.addDecl lenv .quotDecl, isUnsafe with
  | .ok _, false => pure ()
  | .ok _, true => throwError "lean4lean initialized quotients with an unsafe `Eq`"
  | .error e, false => throwError "lean4lean rejected quotients: {← (e.toMessageData {}).toString}"
  | .error e, true =>
    let msg ← (e.toMessageData {}).toString
    unless (msg.splitOn "'Eq' type is unsafe").length > 1 do
      throwError "lean4lean rejected quotients for the wrong reason: {msg}"

#eval run false
#eval run true

end Lean4Lean.Tests.UnsafeEq

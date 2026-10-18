import Lean4Lean.Environment

/-!
A recursive field whose type normalizes to the block only through a type annotation that is not
the identity. `isRecArg` sees the field as recursive by normalizing its declared type, while the
inductive hypothesis is built from the type with the annotation stripped by name, which does not
end in the block. Lean's kernel builds the hypothesis anyway, at the first type of the block, and
accepts an ill-typed recursor. Lean4lean checks each annotation it strips and rejects the block
(see `divergences.md`).

This needs a prelude whose `optParam` keeps its second argument rather than its first, so the
environment is assembled from scratch.
-/

namespace Lean4Lean.Tests.Annotations

open Lean

private def type1 : Expr := .sort (.succ .zero)

/-- `optParam` keeping its second argument. -/
private def optParamSnd : DefinitionVal :=
  { name := `optParam, levelParams := [],
    type := .forallE `A type1 (.forallE `B type1 type1 .default) .default,
    value := .lam `A type1 (.lam `B type1 (.bvar 0) .default) .default,
    hints := .«abbrev», safety := .safe }

/-- `optParam N I → I`: the field is recursive only after unfolding `optParam`. -/
private def mkType : Expr :=
  .forallE `x (mkApp2 (.const `optParam []) (.const `N []) (.const `I [])) (.const `I []) .default

private def blockDecl : Declaration :=
  .inductDecl [] 0 [{ name := `I, type := type1, ctors := [{ name := `I.mk, type := mkType }] }]
    false

private def prefixDecls : List Declaration :=
  [.axiomDecl { name := `N, levelParams := [], type := type1, isUnsafe := false },
   .defnDecl optParamSnd]

#eval show MetaM Unit from do
  let env := (← mkEmptyEnvironment).toKernelEnv
  let mut kenv := env
  let mut lenv := env
  for d in prefixDecls do
    let .ok kenv' := kenv.addDecl {} d | throwError "Lean's kernel rejected the prelude"
    kenv := kenv'
    let .ok lenv' := Lean4Lean.addDecl lenv d | throwError "lean4lean rejected the prelude"
    lenv := lenv'
  let .ok _ := kenv.addDecl {} blockDecl | throwError "Lean's kernel now rejects the block"
  match Lean4Lean.addDecl lenv blockDecl with
  | .ok _ => throwError "lean4lean accepted the block"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    unless (msg.splitOn "does not return its first argument").length > 1 do
      throwError "lean4lean rejected the block for the wrong reason: {msg}"

end Lean4Lean.Tests.Annotations

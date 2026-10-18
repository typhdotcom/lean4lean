import Lean4Lean.Environment

/-!
`_inhabitedExprDummy` is the constant `default : Expr` is, which lean4lean's kernel returns from a
panic. Lean4lean rejects a declaration of that name, as an axiom or as a constructor of an
inductive block; Lean's kernel accepts both (see `divergences.md`).
-/

namespace Lean4Lean.Tests.ReservedName

open Lean

private def dummy : Name := `_inhabitedExprDummy

private def type1 : Expr := .sort (.succ .zero)

private def decls : List Declaration :=
  [.axiomDecl { name := dummy, levelParams := [], type := type1, isUnsafe := false },
   .inductDecl [] 0 [{ name := `I, type := type1, ctors := [{ name := dummy, type := .const `I [] }] }]
    false]

#eval show MetaM Unit from do
  let env := (← mkEmptyEnvironment).toKernelEnv
  for d in decls do
    let .ok _ := env.addDecl {} d | throwError "Lean's kernel now rejects {d.getNames}"
    match Lean4Lean.addDecl env d with
    | .ok _ => throwError "lean4lean accepted {d.getNames}"
    | .error e =>
      let msg ← (e.toMessageData {}).toString
      unless (msg.splitOn "the kernel reserves it").length > 1 do
        throwError "lean4lean rejected {d.getNames} for the wrong reason: {msg}"

end Lean4Lean.Tests.ReservedName

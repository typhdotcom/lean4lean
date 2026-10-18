import Lean4Lean.Environment

/-!
Initialising the quotient builds the same four constants as Lean's kernel, binder names and
binder infos included.
-/

namespace Lean4Lean.Tests.QuotInit

open Lean

run_meta do
  let env ← getEnv
  let some (.inductInfo eq) := env.find? ``Eq | throwError "no `Eq`"
  let some refl := env.find? ``Eq.refl | throwError "no `Eq.refl`"
  let eqDecl := Declaration.inductDecl eq.levelParams eq.numParams
    [{ name := ``Eq, type := eq.type, ctors := [{ name := ``Eq.refl, type := refl.type }] }] false
  let .ok base := (← mkEmptyEnvironment).toKernelEnv.addDecl {} eqDecl
    | throwError "Lean's kernel rejected `Eq`"
  let .ok lean := base.addDecl {} .quotDecl | throwError "Lean's kernel rejected the quotient"
  let .ok ours := Lean4Lean.addDecl base .quotDecl | throwError "lean4lean rejected the quotient"
  for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    let (some a, some b) := (lean.find? n, ours.find? n) | throwError "{n} missing"
    unless a.type.equal b.type && a.levelParams == b.levelParams do
      throwError "{n}: lean4lean's type differs from Lean's"

end Lean4Lean.Tests.QuotInit

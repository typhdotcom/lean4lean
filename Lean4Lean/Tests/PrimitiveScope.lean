import Lean4Lean.Environment

/-!
The primitive recognizers check the closed pieces they keep outside the binders they were found
under: `Condition.check` checks the condition's pieces before building its gadget, and the
well-founded recursion recognizer checks `F` and the packed argument's type outside the measure's
telescope. Every primitive definition of Lean's prelude is still recognized.
-/

namespace Lean4Lean.Tests.PrimitiveScope

open Lean

run_meta
  let env ← Lean.getEnv
  for n in [``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.mod, ``Nat.div,
      ``Nat.gcd, ``Nat.beq, ``Nat.ble, ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
      ``Nat.shiftLeft, ``Nat.shiftRight, ``Char.ofNat, ``String.ofList] do
    let some (.defnInfo v) := env.toKernelEnv.find? n | throwError "{n} is not a definition"
    match (Primitive.checkDef v).run env.toKernelEnv (lparams := v.levelParams) with
    | .ok true => pure ()
    | .ok false => throwError "{n} was not recognized as a primitive"
    | .error _ => throwError "{n} was rejected as a primitive"

end Lean4Lean.Tests.PrimitiveScope

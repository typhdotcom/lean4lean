import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.ScopedEquivManager

/-!
# Scoped equivalences as definitional equalities in a chain of contexts

A scoped union-find of the type checker records each equivalence at a level: the scope it was
learned in. Reading the level `l` as "holds in the context `Γ l` of that scope", for contexts that
extend each other as the levels grow, gives a relation `isEquiv` can answer queries by
(`ScopedEquivManager.ERel`). A ceiling `c` sets aside the levels above it: they assert nothing,
which is how a computation is re-run in a context that keeps only the scopes up to `c`.
-/

namespace Lean4Lean.ScopedEquivManager
open Lean hiding Environment Exception
open Kernel

variable {env : VEnv} {Us : List Name}

end Lean4Lean.ScopedEquivManager

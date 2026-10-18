import Lean4Lean.Theory.Typing.LogRel.AdeqRecSat
import Lean4Lean.Theory.Typing.LogRel.AdeqIotaEta
import Lean4Lean.Theory.Typing.LogRel.ProjDFNew
import Lean4Lean.Theory.Typing.LogRel.IndHYOf

/-!
# Injectivity of well-formed environments, from an inductive block's remaining case
-/

namespace Lean4Lean

namespace LogRel

/-- Every well-formed environment has injectivity, given a block's recursors' full application. -/
theorem _root_.Lean4Lean.VEnv.WF.inj_of_recSat (HSat : IndRecSat) {env : VEnv} (henv : env.WF) :
    env.Inj :=
  henv.inj_of_cases indHY (IndRecCase.of indHY recSameOn HSat) indIotaCase indProjCase

end LogRel
end Lean4Lean

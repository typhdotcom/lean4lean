import Lean4Lean.Theory.Typing.LogRel.BlockGood
import Lean4Lean.Theory.Typing.LogRel.AdeqBlock

/-!
# An inductive block's constants added as axioms, in the model that interprets them

In `GoodOverC X cs`, the constants `cs` are related wherever they are interpreted
(`AdeqStmt.goodC`), so adding them to an environment as axioms keeps adequacy's environment cases
in that model.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}

/-- Adding constants of `cs` as axioms keeps adequacy's environment cases in `GoodOverC X cs`. -/
theorem AdequacyHyps.addGoodC (X : AxInterp) (hMX : @ModelEnv _ X env)
    {cs : List (Name × VConstant)} (hnd : (cs.map (·.1)).Nodup) {Q : Name → Prop}
    (hsame : SameOn env (GoodOverC (U := U) henv hU X Γ₀ cs) X Q)
    (hdecl : ∀ p ∈ cs, env.constants p.1 = some p.2 ∧ p.2.type.ConstsSat Q)
    {E E' : VEnv} {cs' : List (Name × VConstant)} (hsub : ∀ p ∈ cs', p ∈ cs)
    (hG : @AdequacyHyps env U _ (GoodOverC (U := U) henv hU X Γ₀ cs) henv hU E Γ₀)
    (h1 : E.addConstList cs' = some E') :
    @AdequacyHyps env U _ (GoodOverC (U := U) henv hU X Γ₀ cs) henv hU E' Γ₀ := by
  letI G : AxInterp := GoodOverC (U := U) henv hU X Γ₀ cs
  have hinds : E'.inducts = E.inducts := VEnv.addConstList_inducts h1
  have hdfs : E'.defeqs = E.defeqs := VEnv.addConstList_defeqs' h1
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => hG.extra hΓ (hdfs ▸ hd),
    fun hΓ h => hG.projDF hΓ (hinds ▸ h), fun hΓ h => hG.projIota hΓ (hinds ▸ h),
    fun hΓ h => hG.projEta hΓ (hinds ▸ h)⟩
  rcases VEnv.addConstList_constants_cases' h1 hc with hc | hci
  · exact hG.const hΓ hc hls hls' hlen heq hu h7 h8 hA
  · have hci := hsub _ hci
    obtain ⟨hcon, hQ⟩ := hdecl _ hci
    intro ρ n m a hm ha hmem
    exact AdeqStmt.goodC (Γ := Γ) X hMX hnd hsame hci hQ hcon hls hls' heq hm ha hmem

end LogRel
end Lean4Lean

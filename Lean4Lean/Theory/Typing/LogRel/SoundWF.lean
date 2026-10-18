import Lean4Lean.Theory.Typing.LogRel.IotaSound

/-!
# Soundness of the model of a well-formed environment

By induction on the declarations: each block's projections are sound (`projSoundAt_block`), and
its iota rules and the quotient's rule are, given the environment before them.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat}

variable (env) in
/-- A block's iota rules are sound, given that the environment it was declared in is. -/
def BlockSound : Prop := ∀ {E₁ d E₂}, E₁.WF → VDecl.WF E₁ (.induct d) E₂ → E₂ ≤ env →
  SoundHyps E₁ env → ∀ U, ∀ df ∈ d.iotaRules, RuleSound env U df

/-- The cases of the model's soundness that need the rules hold of a well-formed environment,
given that the quotient's rule and each block's rules and projections are sound. -/
theorem _root_.Lean4Lean.VEnv.WF.soundHyps (henv : env.WF) (hM : ModelEnv env)
    (hQ : QuotRuleSound env) (hB : BlockSound env) : SoundHyps env env := by
  obtain ⟨ds, H₀⟩ := henv
  suffices ∀ {ds' E}, VEnv.WF' ds' E → E ≤ env → SoundHyps E env from this H₀ .rfl
  intro ds' E H hle
  induction H with
  | empty => exact .empty
  | @decl _ E₂ _ E₁ hD hW ih =>
    have IH := ih (hD.le.trans hle)
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 =>
      exact IH.mono (fun h => VEnv.addConst_defeqs h1 ▸ h) (fun h => VEnv.addConst_inducts h1 ▸ h)
    | «example» => exact IH
    | «def» _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addConst_inducts h1 ▸ h)⟩
      rcases h with rfl | h
      · exact ruleSound_defn hM (hle.constants (VEnv.addDefEq_le.constants (VEnv.addConst_self h1)))
          (hle.defeqs (.inl rfl))
      · exact IH.1 U df (VEnv.addConst_defeqs h1 ▸ h)
    | mutualDef _ h1 _ =>
      refine ⟨fun U df h => ?_, fun U s d t h =>
        IH.2 U s d t (VEnv.addConsts_inducts h1 ▸ VEnv.addDefEqs_inducts ▸ h)⟩
      have h' := h
      rcases VEnv.addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
      · exact ruleSound_defn hM
          (hle.constants (VEnv.addDefEqs_le.constants (VEnv.addConsts_constants h1 ci hci)))
          (hle.defeqs h')
      · exact IH.1 U df (VEnv.addConsts_defeqs h1 ▸ h)
    | quot _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addQuot_inducts h1 ▸ h)⟩
      rcases VEnv.addQuot_defeqs h1 h with rfl | h
      · exact hQ (hle.defeqs h) U
      · exact IH.1 U df h
    | induct hd hg h1 =>
      have hR := hB ⟨_, hW⟩ (.induct hd hg h1) hle IH
      refine ⟨fun U df h => ?_, fun U s d' t h => ?_⟩
      · simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
        obtain ⟨envT, hT, envC, hC, envR, hR', hB'⟩ := h1
        rw [VEnv.addBlock_defeqs hB'] at h
        rcases VEnv.addDefEqList_defeqs' h with h | h
        · exact hR U df h
        · rw [VEnv.addConstList_defeqs' hR', VEnv.addConstList_defeqs' hC,
            VEnv.addConstList_defeqs' hT] at h
          exact IH.1 U df h
      · have h1' := h1
        simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
        obtain ⟨envT, hT, envC, hC, envR, hR', hB'⟩ := h1
        rcases VEnv.addBlock_inducts hB' h with h' | ⟨rfl, hT'⟩
        · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR',
            VEnv.addConstList_inducts hC, VEnv.addConstList_inducts hT] at h'
          exact IH.2 U s d' t h'
        · exact projSoundAt_block hM ⟨_, hW⟩ hd h1' hle IH h hT'

/-- The model of a well-formed environment, with its own structures, is sound for its typing
rules, given that the quotient's rule and each block's rules and projections are. -/
theorem _root_.Lean4Lean.VEnv.WF.strongSound {env : VEnv} (henv : env.WF)
    (hQ : @QuotRuleSound env.shapeEnv env) (hB : @BlockSound env.shapeEnv env)
    (H : env.IsDefEqStrong U Γ M N A) : @StrongSoundEq env.shapeEnv env U Γ M N A :=
  letI := env.shapeEnv
  (henv.soundHyps henv.modelEnv hQ hB).strongSound henv.modelEnv .rfl H

end LogRel
end Lean4Lean

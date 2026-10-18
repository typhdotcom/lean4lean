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

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat}

variable (env) in
/-- A block's iota rules are sound, given that the environment it was declared in is. -/
def BlockSound : Prop := ∀ {E₁ d E₂}, E₁.WF → VDecl.WF E₁ (.induct d) E₂ → E₂ ≤ env →
  NoDomI E₂ → SoundHyps E₁ env → ∀ U, ∀ df ∈ d.iotaRules, RuleSound env U df

/-- A well-formed environment's recorded blocks' types and recursors are its constants, so a model
interpreting by given shapes only constants it lacks interprets none of them. -/
theorem _root_.Lean4Lean.VEnv.WF.noDomI {E : VEnv} (hE : E.WF)
    (hd : ∀ c, AxInterp.dom c → E.constants c = none) : NoDomI E := by
  intro s d t hs
  obtain ⟨hrec, -⟩ := hE.recBlock hs
  refine ⟨fun T hT hx => ?_, fun j T hj hx => ?_⟩
  · obtain ⟨env₀, env₂, -, -, hadd, hle, -⟩ := hE.inducts_block hs
    simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
    obtain ⟨envT, hT', envC, hC, envR, hR, hB⟩ := hadd
    have := ((VEnv.addConstList_le hC).trans ((VEnv.addConstList_le hR).trans
      (VEnv.addDefEqList_le.trans ((VEnv.addBlock_le hB).trans hle)))).constants
      (VEnv.addConstList_constants_of_mem hT' (List.mem_map.2 ⟨T, hT, rfl⟩))
    rw [hd _ hx] at this; cases this
  · have := hrec j T hj; rw [hd _ hx] at this; cases this

/-- The cases of the model's soundness that need the rules hold of an environment built by
well-formed declarations, given that the quotient's rule and each block's rules and projections are
sound and no definition it has is of a constant the model interprets by given shapes. -/
theorem soundHyps_of (hM : ModelEnv env) (hQ : QuotRuleSound env) (hB : BlockSound env)
    {ds' E} (H : VEnv.WF' ds' E) (hle : E ≤ env) (hnd : NoDom E) (hni : NoDomI E) :
    SoundHyps E env := by
  induction H with
  | empty => exact .empty
  | @decl _ E₂ _ E₁ hD hW ih =>
    have IH := ih (hD.le.trans hle) (hnd.mono hD.le.defeqs) (hni.mono hD.le.inducts)
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 =>
      exact IH.mono (fun h => VEnv.addConst_defeqs h1 ▸ h) (fun h => VEnv.addConst_inducts h1 ▸ h)
    | «example» => exact IH
    | «def» _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addConst_inducts h1 ▸ h)⟩
      rcases h with rfl | h
      · exact ruleSound_defn hM (hnd (.inl rfl) rfl)
          (hle.constants (VEnv.addDefEq_le.constants (VEnv.addConst_self h1)))
          (hle.defeqs (.inl rfl))
      · exact IH.1 U df (VEnv.addConst_defeqs h1 ▸ h)
    | mutualDef _ h1 _ =>
      refine ⟨fun U df h => ?_, fun U s d t h =>
        IH.2 U s d t (VEnv.addConsts_inducts h1 ▸ VEnv.addDefEqs_inducts ▸ h)⟩
      have h' := h
      rcases VEnv.addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
      · exact ruleSound_defn hM (hnd h' rfl)
          (hle.constants (VEnv.addDefEqs_le.constants (VEnv.addConsts_constants h1 ci hci)))
          (hle.defeqs h')
      · exact IH.1 U df (VEnv.addConsts_defeqs h1 ▸ h)
    | quot _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addQuot_inducts h1 ▸ h)⟩
      rcases VEnv.addQuot_defeqs h1 h with rfl | h
      · exact hQ (hle.defeqs h) U
      · exact IH.1 U df h
    | induct hd hg h1 =>
      have hR := hB ⟨_, hW⟩ (.induct hd hg h1) hle hni IH
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
        · obtain ⟨T, hT, hTn⟩ := hT'
          exact projSoundAt_block hM ⟨_, hW⟩ hd h1' hle IH h ⟨T, hT, hTn⟩
            (hTn ▸ (hni h).1 T (List.mem_of_getElem? hT))

/-- The cases of the model's soundness that need the rules hold of a well-formed environment,
given that the quotient's rule and each block's rules and projections are sound and no definition
it has is of a constant the model interprets by given shapes. -/
theorem _root_.Lean4Lean.VEnv.WF.soundHyps (henv : env.WF) (hM : ModelEnv env)
    (hQ : QuotRuleSound env) (hB : BlockSound env) (hnd : NoDom env) (hni : NoDomI env) :
    SoundHyps env env :=
  let ⟨_, H₀⟩ := henv; soundHyps_of hM hQ hB H₀ .rfl hnd hni

omit [ShapeEnv] [AxInterp] in
/-- The model of a well-formed environment, with its own structures, is sound for its typing
rules, given that the quotient's rule and each block's rules and projections are. -/
theorem _root_.Lean4Lean.VEnv.WF.strongSound {env : VEnv} (henv : env.WF)
    (hQ : @QuotRuleSound env.shapeEnv (@AxInterp.none env.shapeEnv) env)
    (hB : @BlockSound env.shapeEnv (@AxInterp.none env.shapeEnv) env)
    (H : env.IsDefEqStrong U Γ M N A) :
    @StrongSoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env U Γ M N A :=
  letI := env.shapeEnv
  (henv.soundHyps (henv.modelEnv AxOK.none nofun) hQ hB NoDom.none NoDomI.none).strongSound
    (henv.modelEnv AxOK.none nofun) .rfl H

end LogRel
end Lean4Lean

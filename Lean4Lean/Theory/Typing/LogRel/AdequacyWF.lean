import Lean4Lean.Theory.Typing.LogRel.Mutual
import Lean4Lean.Theory.Typing.LogRel.QuotSound
import Lean4Lean.Theory.Typing.LogRel.BlockSound

/-!
# Adequacy's environment cases, declaration by declaration

The environment cases of adequacy (`AdequacyHyps`) hold of every environment a well-formed one is
built through, in every model that interprets by given shapes none of its constants: a definition
by its value's adequacy in the environment before it, a constant with no role by `bot`, and a
recursive block by its values' adequacy in the model interpreting the block's constants by the
shapes they are related at (`GoodOver`), which the induction gives since that model too
interprets none of the earlier constants by given shapes. The quotient's and inductive blocks'
steps are hypotheses here.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}

theorem AdequacyHyps.empty (X : AxInterp) :
    @AdequacyHyps env U _ X henv hU .empty Γ₀ :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h),
    fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.constants_none_of_le {E E' : VEnv} (hle : E ≤ E')
    (h : E'.constants c = none) : E.constants c = none := by
  cases e : E.constants c with
  | none => rfl
  | some _ => rw [hle.constants e] at h; cases h

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.addDefEqs_defeqs_self : ∀ {env : VEnv} {cis : List VDefVal},
    ci ∈ cis → (env.addDefEqs cis).defeqs ci.toDefEq
  | _, c :: _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (VEnv.addDefEqs_le (env := VEnv.addDefEq _ ci.toDefEq)).defeqs
        (show (VEnv.addDefEq _ _).defeqs _ from .inl rfl)
    · exact VEnv.addDefEqs_defeqs_self (env := VEnv.addDefEq _ c.toDefEq) h

/-- Adequacy's environment cases hold of every environment a well-formed one is built through, in
every model interpreting none of its constants by given shapes, given the quotient's and inductive
blocks' steps and facts about how the environment's declarations read each other. -/
theorem AdequacyHyps.of_WF' (henvW : env.WF)
    (hModel : ∀ X : AxInterp, @AxOK _ X → @ModelEnv _ X env)
    (hJ : LRJoin (U := U) henv hU Γ₀) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hHead : ∀ {ds E df c us}, VEnv.WF' ds E → E.defeqs df → df.lhs = .const c us →
      E.constants c ≠ none)
    (hCS : ∀ {ds E} {ci : VConstant}, VEnv.WF' ds E → ci.WF E →
      ci.type.ConstsSat (E.constants · ≠ none))
    (hSame : ∀ {ds E} (X Y : AxInterp), VEnv.WF' ds E → E ≤ env →
      (∀ c, X.dom c → E.constants c = none) → (∀ c, Y.dom c → E.constants c = none) →
      SameOn env X Y (E.constants · ≠ none))
    (hNoRole : ∀ {ds E c ci E'}, VEnv.WF' ds E → E.addConst c ci = some E' → E' ≤ env →
      ∀ r k, ¬ConstArity env c r k)
    (hQuot : ∀ (X : AxInterp) {ds E E'}, @AxOK _ X → VEnv.WF' ds E → VDecl.WF E .quot E' →
      E' ≤ env → (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U _ X henv hU E Γ₀ → @AdequacyHyps env U _ X henv hU E' Γ₀)
    (hInd : ∀ (X : AxInterp) {ds E E' d}, @AxOK _ X → VEnv.WF' ds E → VDecl.WF E (.induct d) E' →
      E' ≤ env → (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U _ X henv hU E Γ₀ → @AdequacyHyps env U _ X henv hU E' Γ₀) :
    ∀ {ds E}, VEnv.WF' ds E → E ≤ env → ∀ X : AxInterp, @AxOK _ X →
      (∀ c, X.dom c → E.constants c = none) → @AdequacyHyps env U _ X henv hU E Γ₀ := by
  intro ds E H
  induction H with
  | empty => intro _ X _ _; exact AdequacyHyps.empty X
  | @decl d E₂ ds E hD hW ih =>
    intro hle X hX hdom
    have hle₁ : E ≤ env := hD.le.trans hle
    have hdom₁ : ∀ c, X.dom c → E.constants c = none :=
      fun c h => VEnv.constants_none_of_le hD.le (hdom c h)
    have IH := ih hle₁ X hX hdom₁
    have hMX := hModel X hX
    have hEo : E.Ordered := VEnv.WF.ordered ⟨_, hW⟩
    have hnd {ds' : List VDecl} {E' : VEnv} (hW' : VEnv.WF' ds' E')
        (hd : ∀ c, X.dom c → E'.constants c = none) : NoDom E' :=
      fun hdf e hx => hHead hW' hdf e (hd _ hx)
    have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
      fun D => (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hW hle₁
        (hnd hW hdom₁)).strongSound hMX hle₁ D
    cases hD with
    | «axiom» _ h1 => exact IH.addNoRole h1 (hNoRole hW h1 hle)
    | «opaque» _ h1 => exact IH.addNoRole h1 (hNoRole hW h1 hle)
    | «example» => exact IH
    | «def» hv h1 =>
      refine IH.addDef hMX hEo (fun hx => ?_) hv h1 hle hS hΓ₀
      have h := hdom _ hx
      rw [VEnv.addDefEq_le.constants (VEnv.addConst_self h1)] at h; cases h
    | quot h0 h1 => exact hQuot X hX hW (.quot h0 h1) hle hdom IH
    | induct h0 h1 h2 => exact hInd X hX hW (.induct h0 h1 h2) hle hdom IH
    | @mutualDef cis E' _ hT h1 hV =>
      obtain ⟨hnd₁, hfr₁, hcs₁⟩ := VEnv.addConstList_spec ((VEnv.addConsts_eq (env := E) cis).symm.trans h1)
      simp only [List.map_map] at hnd₁ hcs₁
      have hndup : (cis.map (·.name)).Nodup := hnd₁
      have hfresh : ∀ ci ∈ cis, E.constants ci.name = none := fun ci hci =>
        hfr₁ _ (List.mem_map_of_mem (f := fun ci => (ci.name, ci.toVConstant)) hci)
      have hE'le : E' ≤ env := VEnv.addDefEqs_le.trans hle
      have hcon : ∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant := fun ci hci =>
        hE'le.constants (VEnv.addConsts_constants h1 ci hci)
      have hdomX : ∀ ci ∈ cis, ¬X.dom ci.name := fun ci hci hx => by
        have h := hdom _ hx
        rw [VEnv.addDefEqs_constants, VEnv.addConsts_constants h1 ci hci] at h; cases h
      have hdecl : ∀ ci ∈ cis, env.defeqs ci.toDefEq ∧
          env.constants ci.name = some ci.toVConstant ∧
          ci.type.ConstsSat (E.constants · ≠ none) := fun ci hci =>
        ⟨hle.defeqs (VEnv.addDefEqs_defeqs_self hci), hcon ci hci, hCS hW (hT ci hci)⟩
      have hGax := GoodOver.axOK (cis := cis) X hX hMX hJ hndup
      have hMG := hModel _ hGax
      have hdomG : ∀ c, (GoodOver (U := U) henv hU X Γ₀ cis).dom c → E.constants c = none := by
        rintro c (hc | hc)
        · exact hdom₁ c hc
        · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc; exact hfresh ci hci
      have IHG := ih hle₁ _ hGax hdomG
      have hsXG := hSame X _ hW hle₁ hdom₁ hdomG
      have hsGX := hSame _ X hW hle₁ hdomG hdom₁
      obtain ⟨ds', hW'⟩ : E'.WF := VEnv.WF.addConstList ⟨_, hW⟩ (fun p hp => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hp; exact hT ci hci)
        ((VEnv.addConsts_eq (env := E) cis).symm.trans h1)
      have hEo' : E'.Ordered := VEnv.WF.ordered ⟨_, hW'⟩
      have hS' : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A →
          @StrongSoundEq _ (GoodOver (U := U) henv hU X Γ₀ cis) env U Γ M N A := by
        letI : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
        have hndG : NoDom E' := fun hdf e hx => by
          rw [VEnv.addConsts_defeqs h1] at hdf
          exact hHead hW hdf e (hdomG _ hx)
        intro Γ M N A D
        exact (soundHyps_of hMG (quotRuleSound hMG henvW) (henvW.blockSound hMG) hW'
          hE'le hndG).strongSound hMG hE'le D
      have hG' := AdequacyHyps.addGood X hMX hMG hndup hsGX hdecl IHG h1
      have HM := MutualOK.of X hMX hMG hndup hdomX hsXG hdecl hEo' hE'le
        (fun ci hci => (hT ci hci).mono (VEnv.addConsts_le h1)) hV hS' hΓ₀ hG'
      exact AdequacyHyps.addMutual X HM IH h1

end LogRel
end Lean4Lean

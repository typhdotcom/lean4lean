import Lean4Lean.Theory.Typing.LogRel.Prefix
import Lean4Lean.Theory.Typing.LogRel.QuotSound
import Lean4Lean.Theory.Typing.LogRel.BlockSound
import Lean4Lean.Theory.Typing.ConstsSatTyping

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

omit [ShapeEnv] in
/-- A constant's type mentions only the environment's constants. -/
theorem _root_.Lean4Lean.VConstant.WF.constsSat {E : VEnv} (hE : E.Ordered) {ci : VConstant}
    (h : ci.WF E) : ci.type.ConstsSat (E.constants · ≠ none) := by
  obtain ⟨_, h⟩ := h
  exact (VEnv.IsDefEq.constsSat hE h trivial).1.mono fun c hc => by
    simpa [Option.isSome_iff_ne_none] using hc

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.lams_ne_const {body : VExpr} (hb : ∀ c us, body ≠ .const c us) :
    ∀ Bs : List VExpr, VExpr.lams Bs body ≠ .const c us
  | [] => hb _ _
  | _ :: _ => by simp [VExpr.lams]

omit [ShapeEnv] in
/-- A rule whose left-hand side is a constant is a definition's, of a constant the environment
has. -/
theorem _root_.Lean4Lean.VEnv.WF.rule_head {E : VEnv} (hE : E.WF) (hdf : E.defeqs df)
    (e : df.lhs = .const c us) : E.constants c ≠ none := by
  cases hE.ruleKind hdf with
  | defn ci h => cases e; rw [h]; simp
  | quot => cases e
  | iota _ hm =>
    obtain ⟨⟨⟨j, c'⟩, q⟩, -, rfl⟩ := List.mem_map.1 hm
    rw [iotaRule_lhs] at e
    refine absurd e (VExpr.lams_ne_const (fun c us h => ?_) _)
    simp only [iotaL, VExpr.appN_append, VExpr.appN] at h; cases h

/-- A declaration's rank: axioms add no rules, so an environment extended by axioms has the rank
it had. -/
def _root_.Lean4Lean.VDecl.rank : VDecl → Nat
  | .axiom _ => 0
  | _ => 1

/-- The rank of a list of declarations, the number of those that are not axioms. -/
def _root_.Lean4Lean.VDecl.listRank (ds : List VDecl) : Nat := (ds.map VDecl.rank).sum

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VDecl.listRank_cons (d : VDecl) (ds : List VDecl) :
    VDecl.listRank (d :: ds) = d.rank + VDecl.listRank ds := by
  simp [VDecl.listRank]

/-- Adequacy's environment cases hold of every environment a well-formed one is built through, in
every model interpreting none of its constants by given shapes, given the quotient's and inductive
blocks' steps. The steps are given the rank bound `N` of the declarations so far, so that they may
use what an induction on rank gives for environments of smaller rank. -/
theorem AdequacyHyps.of_WF' (henvW : env.WF) (N : Nat)
    (hModel : ∀ X : AxInterp, @AxOK _ X → @DomRole _ X env → @ModelEnv _ X env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hQuot : ∀ (X : AxInterp) {ds E E'}, @AxOK _ X → @DomRole _ X env → VEnv.WF' ds E →
      VDecl.listRank ds < N →
      VDecl.WF E .quot E' →
      Extends E' env → (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U _ X henv hU E Γ₀ → @AdequacyHyps env U _ X henv hU E' Γ₀)
    (hInd : ∀ (X : AxInterp) {ds E E' d}, @AxOK _ X → @DomRole _ X env → VEnv.WF' ds E →
      VDecl.listRank ds < N →
      VDecl.WF E (.induct d) E' →
      Extends E' env → (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U _ X henv hU E Γ₀ → @AdequacyHyps env U _ X henv hU E' Γ₀) :
    ∀ {ds E}, VEnv.WF' ds E → VDecl.listRank ds ≤ N → Extends E env → ∀ X : AxInterp, @AxOK _ X →
      @DomRole _ X env → (∀ c, X.dom c → E.constants c = none) →
      @AdequacyHyps env U _ X henv hU E Γ₀ := by
  have hJ : LRJoin (U := U) henv hU Γ₀ := fun hc h1 h2 d1 d2 => (LR henv hU _).join hc h1 h2 d1 d2
  intro ds E H
  induction H with
  | empty => intro _ _ X _ _ _; exact AdequacyHyps.empty X
  | @decl d E₂ ds E hD hW ih =>
    intro hN hext X hX hXD hdom
    rw [VDecl.listRank_cons] at hN
    have hN₁ : VDecl.listRank ds ≤ N := by omega
    have hle : E₂ ≤ env := hext.le
    have hext₁ : Extends E env := .step hD hext
    have hle₁ : E ≤ env := hext₁.le
    have hdom₁ : ∀ c, X.dom c → E.constants c = none :=
      fun c h => VEnv.constants_none_of_le hD.le (hdom c h)
    have IH := ih hN₁ hext₁ X hX hXD hdom₁
    have hMX := hModel X hX hXD
    have hEo : E.Ordered := VEnv.WF.ordered ⟨_, hW⟩
    have hnd {ds' : List VDecl} {E' : VEnv} (hW' : VEnv.WF' ds' E')
        (hd : ∀ c, X.dom c → E'.constants c = none) : NoDom E' :=
      fun hdf e hx => VEnv.WF.rule_head ⟨_, hW'⟩ hdf e (hd _ hx)
    have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
      fun D => (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hW hle₁
        (hnd hW hdom₁) (VEnv.WF.noDomI ⟨_, hW⟩ hdom₁)).strongSound hMX hle₁ D
    cases hD with
    | «axiom» _ h1 =>
      exact IH.addNoRole h1 (Extends.noRole hW h1 hext) fun hx => by
        have h := hdom _ hx; rw [VEnv.addConst_self h1] at h; cases h
    | «opaque» _ h1 =>
      exact IH.addNoRole h1 (Extends.noRole hW h1 hext) fun hx => by
        have h := hdom _ hx; rw [VEnv.addConst_self h1] at h; cases h
    | «example» => exact IH
    | «def» hv h1 =>
      refine IH.addDef hMX hEo (fun hx => ?_) hv h1 hle hS hΓ₀
      have h := hdom _ hx
      rw [VEnv.addDefEq_le.constants (VEnv.addConst_self h1)] at h; cases h
    | quot h0 h1 => exact hQuot X hX hXD hW (by simp [VDecl.rank] at hN; omega) (.quot h0 h1) hext hdom IH
    | induct h0 h1 h2 =>
      exact hInd X hX hXD hW (by simp [VDecl.rank] at hN; omega) (.induct h0 h1 h2) hext hdom IH
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
        ⟨hle.defeqs (VEnv.addDefEqs_defeqs_self hci), hcon ci hci, VConstant.WF.constsSat hEo (hT ci hci)⟩
      have hGax := GoodOver.axOK (cis := cis) X hX hMX hJ hndup
      have hGD : @DomRole _ (GoodOver (U := U) henv hU X Γ₀ cis) env := fun hc A =>
        hc.elim (fun hx => hXD hx A) fun hc' => by
          obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc'
          cases hMX.roles A (.delta (hdecl ci hci).1 rfl); trivial
      have hMG := hModel _ hGax hGD
      have hdomG : ∀ c, (GoodOver (U := U) henv hU X Γ₀ cis).dom c → E.constants c = none := by
        rintro c (hc | hc)
        · exact hdom₁ c hc
        · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hc; exact hfresh ci hci
      have IHG := ih hN₁ hext₁ _ hGax hGD hdomG
      have hsXG := hext₁.sameOn hW X _ hdom₁ hdomG
      have hsGX := hext₁.sameOn hW _ X hdomG hdom₁
      obtain ⟨ds', hW'⟩ : E'.WF := VEnv.WF.addConstList ⟨_, hW⟩ (fun p hp => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hp; exact hT ci hci)
        ((VEnv.addConsts_eq (env := E) cis).symm.trans h1)
      have hEo' : E'.Ordered := VEnv.WF.ordered ⟨_, hW'⟩
      have hS' : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A →
          @StrongSoundEq _ (GoodOver (U := U) henv hU X Γ₀ cis) env U Γ M N A := by
        letI : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
        have hndG : NoDom E' := fun hdf e hx => by
          rw [VEnv.addConsts_defeqs h1] at hdf
          exact VEnv.WF.rule_head ⟨_, hW⟩ hdf e (hdomG _ hx)
        intro Γ M N A D
        exact (soundHyps_of hMG (quotRuleSound hMG henvW) (henvW.blockSound hMG) hW'
          hE'le hndG (NoDomI.mono (VEnv.WF.noDomI ⟨_, hW⟩ hdomG)
            fun h => (VEnv.addConsts_inducts h1) ▸ h)).strongSound hMG hE'le D
      have hG' := AdequacyHyps.addGood X hMX hMG hndup hsGX hdecl IHG h1
      have HM := MutualOK.of X hMX hMG hndup hdomX hsXG hdecl hEo' hE'le
        (fun ci hci => (hT ci hci).mono (VEnv.addConsts_le h1)) hV hS' hΓ₀ hG'
      exact AdequacyHyps.addMutual X HM IH h1

end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.AdequacyWF
import Lean4Lean.Theory.Typing.LogRel.InjOf
import Lean4Lean.Theory.Typing.LogRel.Chain

/-!
# Injectivity of every well-formed environment, by induction on rank

The fundamental lemma's environment cases (`AdequacyHyps.of_WF'`) need, at an inductive block,
injectivity of the environment the block's rules are typed in: the environment before the block
with its types, constructors and recursors as axioms (`envR`). That environment has the rank of
the one before the block, less than the block's, so an induction on rank (`VDecl.listRank`, the
number of declarations that are not axioms) supplies it. Injectivity of an environment then comes
from its own environment cases by chain inversion (`ChainInv`), which adequacy gives at sorts
and pi types (`ChainInv.of_adequacy`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

/-- Adding constants as axioms keeps a declaration list's rank. -/
theorem _root_.Lean4Lean.VEnv.WF'.addConstList : ∀ {E E' : VEnv} {ds : List VDecl}
    {cs : List (Name × VConstant)}, E.WF' ds → (∀ p ∈ cs, p.2.WF E) →
    E.addConstList cs = some E' → ∃ ds', E'.WF' ds' ∧ VDecl.listRank ds' = VDecl.listRank ds
  | _, _, _, [], h, _, e => by cases e; exact ⟨_, h, rfl⟩
  | E, _, ds, (n, ci) :: cs, h, H, e => by
    simp only [VEnv.addConstList, List.foldlM_cons] at e
    obtain ⟨E₁, h1, h2⟩ := Option.bind_eq_some_iff.1 e
    have h₁ : E₁.WF' (.axiom { ci with name := n } :: ds) := .decl (.axiom (H _ (.head _)) h1) h
    obtain ⟨ds', h', e'⟩ := VEnv.WF'.addConstList h₁
      (fun p hp => (H p (.tail _ hp)).mono (VEnv.addConst_le h1)) h2
    exact ⟨ds', h', by rw [e', VDecl.listRank_cons]; simp [VDecl.rank]⟩

/-- The step an inductive block makes to adequacy's environment cases, given injectivity of the
environment before it and of the one its rules are typed in. -/
def IndStep : Prop :=
  ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
    ∀ (X : @AxInterp env.shapeEnv) {ds E E' d}, @AxOK env.shapeEnv X →
    @DomRole env.shapeEnv X env → VEnv.WF' ds E → E.Inj →
    (∀ envT envC envR, E.addConstList d.typeConsts = some envT →
      envT.addConstList d.ctorConsts = some envC →
      envC.addConstList d.recConsts = some envR → envT.Inj ∧ envC.Inj ∧ envR.Inj) →
    VDecl.WF E (.induct d) E' → Extends E' env → (∀ c, X.dom c → E'.constants c = none) →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
    (∀ X' : @AxInterp env.shapeEnv, @AxOK env.shapeEnv X' → @DomRole env.shapeEnv X' env →
      (∀ c, X'.dom c → E.constants c = none) →
      @AdequacyHyps env U env.shapeEnv X' henvW.ordered henvW.stepUniq E Γ₀) →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E' Γ₀

/-- The step the quotient makes to adequacy's environment cases, given injectivity of the
environment before it. -/
def QuotStep : Prop :=
  ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
    ∀ (X : @AxInterp env.shapeEnv) {ds E E'}, @AxOK env.shapeEnv X →
    @DomRole env.shapeEnv X env → VEnv.WF' ds E → E.Inj → VDecl.WF E .quot E' → Extends E' env → (∀ c, X.dom c → E'.constants c = none) →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E' Γ₀

/-- Chain inversion at projections of a well-formed environment, from its own environment cases
of adequacy at every context. -/
def ProjStep : Prop :=
  ∀ {env : VEnv} (henvW : env.WF),
    (∀ U Γ, OnCtx Γ (env.IsType U) →
      @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
        henvW.stepUniq env Γ) →
    ∀ U, ProjChain env U

/-- Every well-formed environment has injectivity, given the inductive and quotient steps of the
fundamental lemma and chain inversion at projections. -/
theorem _root_.Lean4Lean.VEnv.WF'.inj_of (hInd : IndStep) (hQuot : QuotStep)
    (hProj : ProjStep) : ∀ N (ds : List VDecl) (E : VEnv), E.WF' ds →
    VDecl.listRank ds ≤ N → E.Inj := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IH =>
  intro ds env hW hN
  have henvW : env.WF := ⟨_, hW⟩
  letI := env.shapeEnv
  -- injectivity of an environment of smaller rank, and of its extensions by axioms
  have hsmall : ∀ {ds' : List VDecl} {E : VEnv}, E.WF' ds' → VDecl.listRank ds' < N → E.Inj := fun h hr =>
    IH _ hr _ _ h (Nat.le_refl _)
  have hR : ∀ {ds' : List VDecl} {E : VEnv}, E.WF' ds' → VDecl.listRank ds' < N →
      ∀ {d : VInductDecl}, d.WF E → d.GeneratedWF E →
      ∀ envT envC envR, E.addConstList d.typeConsts = some envT →
      envT.addConstList d.ctorConsts = some envC →
      envC.addConstList d.recConsts = some envR → envT.Inj ∧ envC.Inj ∧ envR.Inj := by
    intro ds' E h hr d hd hg envT envC envR hT hC hRc
    obtain ⟨ds₁, h₁, e₁⟩ := h.addConstList (fun p hp => by
      simp only [VInductDecl.typeConsts, List.mem_map] at hp
      obtain ⟨T, hT, rfl⟩ := hp
      exact (hd.types T hT).1) hT
    obtain ⟨ds₂, h₂, e₂⟩ := h₁.addConstList (fun p hp => by
      simp only [VInductDecl.ctorConsts, VInductDecl.ctors, List.mem_map, List.mem_flatten] at hp
      obtain ⟨⟨j, c⟩, ⟨_, ⟨⟨T, i⟩, hm, rfl⟩, hc⟩, rfl⟩ := hp
      obtain ⟨c, hc, ⟨⟩⟩ := List.mem_map.1 hc
      have hT' := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hm)
      exact ((hd.ctors envT hT T (List.mem_append_left _ hT')).2 c hc).type) hC
    obtain ⟨ds₃, h₃, e₃⟩ := h₂.addConstList (hg envT envC envR hT hC hRc).1 hRc
    exact ⟨hsmall h₁ (by omega), hsmall h₂ (by omega), hsmall h₃ (by omega)⟩
  have hAdeq : ∀ U Γ, OnCtx Γ (env.IsType U) →
      @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
        henvW.stepUniq env Γ := by
    intro U Γ hΓ
    refine AdequacyHyps.of_WF' henvW N (fun X hX hXD => henvW.modelEnv hX hXD) hΓ
      (fun X _ _ _ hX hXD hW' hr hD hle hdom IH₀ =>
        hQuot henvW hΓ X hX hXD hW' (hsmall hW' hr) hD hle hdom IH₀)
      (fun X _ _ _ _ hX hXD hW' hr hD hle hdom IH₀ IHall => ?_) hW hN .refl _ AxOK.none nofun
      (fun _ h => h.elim)
    cases hD with
    | induct h0 h1 h2 =>
      exact hInd henvW hΓ X hX hXD hW' (hsmall hW' hr) (hR hW' hr h0 h1) (.induct h0 h1 h2) hle
        hdom IH₀ IHall
  exact VEnv.Inj.of_chainInv henvW fun U =>
    ChainInv.of_adequacy henvW (hAdeq U) (hProj henvW hAdeq U)

end LogRel
end Lean4Lean

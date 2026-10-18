import Lean4Lean.Theory.Typing.LogRel.AdeqQuotTy
import Lean4Lean.Theory.Typing.LogRel.ProjChainOf

/-!
# An inductive block's step to adequacy's environment cases, from its remaining cases

The block's type formers and constructors are related (`typeFormers_adeq`, `ctors_adeq`), given
that stuck values of its structure types have typed projections (`IndHY`). What else adding a
block needs is stated here as the cases still to prove: its recursors' constant case
(`IndRecCase`), its iota rules (`IndIotaCase`) and its projections (`IndProjCase`), each in the
context `IndStep` provides. With them, every well-formed environment has injectivity.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

set_option linter.unusedVariables false in
/-- The context `IndStep` gives an inductive block's step, as a predicate on what it concludes. -/
def IndStepCtx (P : ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}
    (X : @AxInterp env.shapeEnv) {E E' : VEnv} {d : VInductDecl}, Prop) : Prop :=
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
    @P env henvW U Γ₀ X E E' d

/-- Stuck values of the block's structure types have typed projections. -/
def IndHY : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {_ _ d} =>
  letI := env.shapeEnv; letI := X
  ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
    {σ σ' : VExpr.Subst}, (∀ l ∈ ls₃, l.WF U) → List.Forall₂ (· ≈ ·) ls ls₃ →
      ls.length = d.uvars → ConstAt U T.name ls F →
    LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ₀ σ σ'
      (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
    rargs.length = d.params.length + T.indices.length →
    StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
        (spineAt F (d.params ++ T.indices).length σ) ∧
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
        (spineAt F (d.params ++ T.indices).length σ')

/-- The block's recursors' constant case. -/
def IndRecCase : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {_ _ d} =>
  ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → (c, ci) ∈ d.recConsts →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
    env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (.const c ls) (.const c ls') (ci.type.instL ls)

/-- The block's iota rules, given adequacy's cases over the environment with the block's
constants, recursors included, as axioms. -/
def IndIotaCase : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq envR Γ₀ →
  ∀ {Γ df ls u}, OnCtx Γ (env.IsType U) → df ∈ d.iotaRules → (∀ l ∈ ls, l.WF U) →
    ls.length = df.uvars → u.WF U →
    env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
    env.IsDefEqStrong U [] (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U [] (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)

/-- The cases of the block's projections: adequacy's cases over the old constants and rules with
the new blocks recorded. -/
def IndProjCase : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E E' _} =>
  @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq
    { E' with constants := E.constants, defeqs := E.defeqs } Γ₀

/-- An inductive block's step, from its remaining cases. -/
theorem IndStep.of (HY : IndHY) (HRec : IndRecCase) (HIota : IndIotaCase)
    (HProj : IndProjCase) : IndStep := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
  letI := env.shapeEnv; letI := X
  have hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env :=
    fun Y hY hYD => henvW.modelEnv hY hYD
  obtain ⟨-, envT, envC, envR, h1, h2, h3, hTE', -⟩ := induct_facts hD hext.le
  have hdomT : ∀ c, X.dom c → envT.constants c = none :=
    fun c h => VEnv.constants_none_of_le hTE' (hdom c h)
  have hIT := (hR envT envC envR h1 h2 h3).1
  have hY := HY henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall
  have hadd : E.addInduct d = some E' := by cases hD with | induct _ _ h => exact h
  -- the block's constants as axioms, recursors last
  have IHR : @AdequacyHyps env U _ X henvW.ordered henvW.stepUniq envR Γ₀ := by
    have IHC := adequacyHyps_envC henvW hModel hΓ₀ X hX hXD hW hD hext hdomT IHall h1 hIT hY h2
    have hinds : envR.inducts = envC.inducts := VEnv.addConstList_inducts h3
    have hdfs : envR.defeqs = envC.defeqs := VEnv.addConstList_defeqs' h3
    refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
      fun hΓ hd => IHC.extra hΓ (hdfs ▸ hd),
      fun hΓ h => IHC.projDF hΓ (hinds ▸ h), fun hΓ h => IHC.projIota hΓ (hinds ▸ h),
      fun hΓ h => IHC.projEta hΓ (hinds ▸ h)⟩
    rcases VEnv.addConstList_constants_cases' h3 hc with hc | hci
    · exact IHC.const hΓ hc hls hls' hlen heq hu h7 h8 hA
    · exact HRec henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall hΓ hci hls hls' hlen heq hu h7 h8 hA
  refine AdequacyHyps.addInduct_of hadd (HProj henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall)
    (fun {Γ c ci ls ls' u} hΓ hm hls hls' hlen heq hu h7 h8 hA => ?_)
    (HIota henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHR)
  rcases List.mem_append.1 hm with hm | hm
  · rcases List.mem_append.1 hm with hm | hm
    · have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
          (.const c ls) (.const c ls') (ci.type.instL ls) :=
        typeFormers_adeq henvW hModel hΓ₀ X hX hXD hW hD hext hdomT IHall h1 hIT hY hm hls hls' heq
      exact @key
    · have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
          (.const c ls) (.const c ls') (ci.type.instL ls) :=
        ctors_adeq henvW hModel hΓ₀ X hX hXD hW hD hext hdomT IHall h1 hIT hY hΓ hm hls hls' hlen
          heq
      exact @key
  · exact HRec henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall hΓ hm hls hls' hlen heq hu h7 h8 hA

/-- Every well-formed environment has injectivity, given an inductive block's remaining cases. -/
theorem _root_.Lean4Lean.VEnv.WF.inj_of_cases (HY : IndHY) (HRec : IndRecCase)
    (HIota : IndIotaCase) (HProj : IndProjCase) {env : VEnv} (henv : env.WF) : env.Inj := by
  obtain ⟨ds, h⟩ := henv
  exact VEnv.WF'.inj_of' (IndStep.of HY HRec HIota HProj) quotStep _ ds env h (Nat.le_refl _)

end LogRel
end Lean4Lean

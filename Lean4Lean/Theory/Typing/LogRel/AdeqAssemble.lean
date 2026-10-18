import Lean4Lean.Theory.Typing.LogRel.InjWF
import Lean4Lean.Theory.Typing.LogRel.AdeqQuot

/-!
# Assembling the inductive and quotient steps

`VEnv.WF'.inj_of` takes the steps an inductive block and the quotient make to adequacy's
environment cases (`IndStep`, `QuotStep`). Each reduces to the cases of the constants and rules the
declaration adds (`AdequacyHyps.addInduct_of`, `AdequacyHyps.addQuot_of`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- The quotient's constants. -/
def quotConsts : List (Name × VConstant) :=
  [(``Quot, quotConst), (``Quot.mk, quotMkConst), (``Quot.lift, quotLiftConst),
    (``Quot.ind, quotIndConst)]

omit [ShapeEnv] in
/-- A constant of an environment with the quotient is the old environment's or the quotient's. -/
theorem _root_.Lean4Lean.VEnv.addQuot_constants_cases {E E' : VEnv} (h : E.addQuot = some E')
    {c : Name} {ci : VConstant} (hc : E'.constants c = some ci) :
    E.constants c = some ci ∨ (c, ci) ∈ quotConsts := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨E₁, h1, E₂, h2, E₃, h3, E₄, h4, h5⟩ := h
  cases h5
  have hc4 : E₄.constants c = some ci := hc
  have hl : E.addConstList quotConsts = some E₄ := by
    simp only [quotConsts, VEnv.addConstList, List.foldlM_cons, List.foldlM_nil,
      Option.bind_eq_bind, h1, h2, h3, h4, Option.bind_some, Option.pure_def]
  rcases VEnv.addConstList_constants_cases' hl hc4 with h | h
  · exact .inl h
  · exact .inr h

/-- Adding the quotient keeps adequacy's environment cases, given them for its constants and its
rule. -/
theorem AdequacyHyps.addQuot_of {E E' : VEnv} (h : E.addQuot = some E')
    (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    (Hc : ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → (c, ci) ∈ quotConsts →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls))
    (Hr : ∀ {Γ ls u}, OnCtx Γ (env.IsType U) → (∀ l ∈ ls, l.WF U) →
      ls.length = quotDefEq.uvars → u.WF U →
      env.IsDefEqStrong U [] (quotDefEq.type.instL ls) (quotDefEq.type.instL ls) (.sort u) →
      env.IsDefEqStrong U [] (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U [] (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U Γ (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U Γ (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls)
        (quotDefEq.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (quotDefEq.lhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls)) :
    AdequacyHyps (U := U) henv hU E' Γ₀ := by
  have hinds : E'.inducts = E.inducts := VEnv.addQuot_inducts h
  refine ⟨fun {Γ c ci ls ls' u} hΓ hci => ?_, fun {Γ df ls u} hΓ hdf => ?_,
    fun hΓ hs => IH.projDF hΓ (hinds ▸ hs), fun hΓ hs => IH.projIota hΓ (hinds ▸ hs),
    fun hΓ hs => IH.projEta hΓ (hinds ▸ hs)⟩
  · rcases VEnv.addQuot_constants_cases h hci with hci | hm
    · exact IH.const hΓ hci
    · exact Hc hΓ hm
  · rcases VEnv.addQuot_defeqs h hdf with rfl | hdf
    · exact Hr hΓ
    · exact IH.extra hΓ hdf

omit [ShapeEnv] [AxInterp] in
/-- The quotient's step to adequacy's environment cases, given the cases of its constants and of
its rule in the environment with it, under the step's premises. -/
theorem QuotStep.of
    (Hc : ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
      ∀ (X : @AxInterp env.shapeEnv) {ds E E'}, @AxOK env.shapeEnv X →
      @DomRole env.shapeEnv X env → VEnv.WF' ds E →
      E.Inj → E.QuotReady → E.addQuot = some E' → Extends E' env →
      (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
      ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → (c, ci) ∈ quotConsts →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const c ls) (.const c ls') (ci.type.instL ls))
    (Hr : ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
      ∀ (X : @AxInterp env.shapeEnv) {ds E E'}, @AxOK env.shapeEnv X →
      @DomRole env.shapeEnv X env → VEnv.WF' ds E →
      E.Inj → E.QuotReady → E.addQuot = some E' → Extends E' env →
      (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
      ∀ {Γ ls u}, OnCtx Γ (env.IsType U) → (∀ l ∈ ls, l.WF U) →
      ls.length = quotDefEq.uvars → u.WF U →
      env.IsDefEqStrong U [] (quotDefEq.type.instL ls) (quotDefEq.type.instL ls) (.sort u) →
      env.IsDefEqStrong U [] (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U [] (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U Γ (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls)
        (quotDefEq.type.instL ls) →
      env.IsDefEqStrong U Γ (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls)
        (quotDefEq.type.instL ls) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (quotDefEq.lhs.instL ls) (quotDefEq.lhs.instL ls) (quotDefEq.type.instL ls) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (quotDefEq.rhs.instL ls) (quotDefEq.rhs.instL ls) (quotDefEq.type.instL ls) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (quotDefEq.lhs.instL ls) (quotDefEq.rhs.instL ls) (quotDefEq.type.instL ls)) :
    QuotStep := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' hX hXD hW hI hD hle hdom IH
  cases hD with
  | quot h0 h1 =>
    exact @AdequacyHyps.addQuot_of env.shapeEnv X env U henvW.ordered henvW.stepUniq Γ₀ E E' h1
      IH (Hc henvW hΓ₀ X hX hXD hW hI h0 h1 hle hdom IH)
      (Hr henvW hΓ₀ X hX hXD hW hI h0 h1 hle hdom IH)

end LogRel
end Lean4Lean

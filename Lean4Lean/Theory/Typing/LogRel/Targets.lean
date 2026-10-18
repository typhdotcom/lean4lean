import Lean4Lean.Theory.Typing.LogRel.AdequacyOf
import Lean4Lean.Theory.Typing.LogRel.ModelInv

/-!
# Injectivity from the logical relation

Given adequacy's environment cases (`AdequacyHyps`) over a context `Γ`, a definitional equality in
`Γ` is related at the identity substitution, and the relation's clauses read off injectivity of
sorts and pi types.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

theorem WShape.HasType.sort_l_inv [ShapeEnv] {n} {r : SortTag} {a : WShape n}
    (h : (WShape.sort r).HasType a) : ∃ j, a = .sort j ∧ j.rel = true := by
  have := h.unfold
  generalize hs : WShape.sort r = s at this
  cases this with
  | sort h' => exact ⟨_, rfl, h'⟩
  | bot => have := congrArg (·.1) hs; cases n <;> cases this
  | forallE => have := congrArg (·.1) hs; cases this
  | lam => have := congrArg (·.1) hs; unfold WShape.lam' at this; split at this <;> cases this
  | ctor => have := congrArg (·.1) hs; cases this
  | indTy => have := congrArg (·.1) hs; cases this

/-- A shape of a sort that a sort's interpretation lies below is a sort. -/
theorem sort_shape_of_le [ShapeEnv] {env : VEnv} {ρ : Valuation} {n} {m : WShape n} {u : VLevel}
    (hm : LE_Interp env ρ m.T (.sort u)) (le : TShape.sort (levelRel u) ≤ m.T) :
    m = .sort (levelRel u) := by
  obtain h | h := WShape.le_sort.1 hm.le_sort'
  · subst h
    have := TShape.le_bot.1 (le.trans TShape.bot_eqv.1)
    simp [TShape.sort, WShape.T, WShape.sort, WShape.bot, WShape.ext_iff, Shape.sort,
      Shape.bot] at this
  · exact h

/-- Sorts the type theory equates have equivalent levels, given adequacy's environment cases. -/
theorem sort_inv_of {env : VEnv} (henvW : env.WF) {U : Nat} {Γ : List VExpr} {u v : VLevel}
    {V : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hH : @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered henvW.stepUniq env Γ)
    (d : env.IsDefEq U Γ (.sort u) (.sort v) V) : u ≈ v := by
  letI := env.shapeEnv
  have H := d.strong henvW.ordered hΓ
  have hS : ∀ {Γ M N A}, env.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    henvW.modelSound
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  obtain ⟨_, m', a, -, le_m, hm', ha, hty⟩ :=
    ((hS H).left.sound W.fits (LE_Interp.sort' (l := u) (ρ := .nil))).out
  cases sort_shape_of_le hm' le_m
  obtain ⟨_, rfl, -⟩ := WShape.HasType.sort_l_inv hty
  have R := (LR.adequacy_of (henvW.modelEnv AxOK.none nofun) .rfl hS hΓ hH H hΓ hm' ha hty).2 W
  simp only [subst_id] at R
  rcases (LR _ _ _).sort_iff.1 R with ⟨u', v', h1, h2, h⟩ | ⟨h1, -⟩
  · cases StepS.of_whnf sort_whnf h1; cases StepS.of_whnf sort_whnf h2; exact h
  · exact (NeRed.not_sort' henvW.stepUniq h1).elim

/-- Pi types the type theory equates have domains and codomains joined by equalities at sorts,
given adequacy's environment cases. -/
theorem forallE_inv_of {env : VEnv} (henvW : env.WF) {U : Nat} {Γ : List VExpr}
    {A B A' B' V : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hH : @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered henvW.stepUniq env Γ)
    (d : env.IsDefEq U Γ (.forallE A B) (.forallE A' B') V) :
    TyEq env U Γ A A' ∧ TyEq env U (A::Γ) B B' := by
  letI := env.shapeEnv
  have hM := (henvW.modelEnv AxOK.none nofun)
  have H := d.strong henvW.ordered hΓ
  have hS : ∀ {Γ M N A}, env.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    henvW.modelSound
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  have hPi : LE_Interp env .nil (WShape.T (n := 1) (.forallE .bot WShapeFun.bot))
      (.forallE A B) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  obtain ⟨_, m', a, -, le_m, hm', ha, hty⟩ := ((hS H).left.sound W.fits hPi).out
  have R := (LR.adequacy_of hM .rfl hS hΓ hH H hΓ hm' ha hty).2 W
  simp only [subst_id] at R
  cases hty.unfold with
  | bot =>
    have := TShape.le_bot.1 (le_m.trans TShape.bot_eqv.1)
    simp [WShape.T, WShape.forallE, WShape.bot, WShape.ext_iff, Shape.bot] at this
  | sort => cases (‹_› : Nat) <;> have .forallE _ _ _ _ h := hm' <;>
      cases TShape.sort_not_le_forallE h
  | @lam _ f₀ =>
    revert hm' le_m; unfold WShape.lam'; split
    · intro _ hm'; let .forallE _ _ _ _ h := hm'; cases TShape.lam_not_le_forallE h
    · intro le_m _
      have := TShape.le_bot.1 (le_m.trans TShape.bot_eqv.1)
      simp [WShape.T, WShape.forallE, WShape.bot, WShape.ext_iff, Shape.bot] at this
  | ctor => have .forallE _ _ _ _ h := hm'; cases TShape.ctor_not_le_forallE h
  | indTy => have .forallE _ _ _ _ h := hm'; cases TShape.indTy_not_le_forallE h
  | forallE =>
    simp only [LR, LRS, LRS.DefEq.sort_a, LRS.TyDefEq.forallE_iff] at R
    rcases R with ⟨_, _, _, _, r1, r2, hB, hF, -⟩ | ⟨h1, -⟩
    · cases StepS.of_whnf forallE_whnf r1; cases StepS.of_whnf forallE_whnf r2; exact ⟨hB, hF⟩
    · exact (NeRed.not_forallE henvW.stepUniq h1 .rfl).elim

end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.QuotSound

/-!
# Consequences of the model's soundness

A well-formed context has a valuation fitting it, so terms the type theory equates have the same
interpretations: a sort is never definitionally equal to a pi type, and sorts it equates have
equivalent levels.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

/-- A well-formed context has a valuation fitting it, in the model of a well-formed
environment. -/
theorem _root_.Lean4Lean.VEnv.WF.exists_fits {env : VEnv} (henv : env.WF) {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      ∃ ρ, letI := env.shapeEnv; Valuation.Fits env [] Γ ρ
  | [], _ => by letI := env.shapeEnv; exact ⟨_, .nil⟩
  | A :: Γ, ⟨hΓ, u, hA⟩ => by
    letI := env.shapeEnv
    obtain ⟨ρ, W⟩ := henv.exists_fits hΓ
    have hS : SoundTy env Γ A (.sort u) :=
      (henv.modelSound (hA.strong henv.ordered hΓ)).left.sound
    obtain ⟨a', -, ha', hT⟩ := InterpTyped.hsort (hS W) (.bot (n := 0))
    exact ⟨_, W.cons (InterpTyped.hsort (hS W)) ha' (TShape.HasType.bot' hT)⟩

/-- A sort is not definitionally equal to a pi type. -/
theorem _root_.Lean4Lean.VEnv.WF.sort_forallE_inv {env : VEnv} (henv : env.WF) {U : Nat}
    {Γ : List VExpr} {u : VLevel} {A B : VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := by
  rintro ⟨_, H⟩
  letI := env.shapeEnv
  obtain ⟨ρ, W⟩ := henv.exists_fits hΓ
  have h := ((henv.modelSound (H.strong henv.ordered hΓ)).sound W).1 (LE_Interp.sort' (l := u))
  generalize hm : TShape.sort (levelRel u) = m at h
  cases h with
  | bot =>
    have : TShape.sort (levelRel u) ≤ TShape.bot := hm ▸ TShape.bot_eqv.1
    have := TShape.le_bot.1 this
    simp [TShape.sort, WShape.T, WShape.sort, WShape.bot, WShape.ext_iff, Shape.sort,
      Shape.bot] at this
  | forallE _ _ _ _ hle =>
    subst hm
    exact TShape.sort_not_le_forallE hle

/-- Sorts the type theory equates have equivalent levels: the model reads a sort's level off its
shape. -/
theorem _root_.Lean4Lean.VEnv.WF.sort_inv {env : VEnv} (henv : env.WF) {U : Nat}
    {Γ : List VExpr} {u v : VLevel} (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨_, H⟩ := H
  letI := env.shapeEnv
  obtain ⟨ρ, W⟩ := henv.exists_fits hΓ
  have h := ((henv.modelSound (H.strong henv.ordered hΓ)).sound W).1 (LE_Interp.sort' (l := u))
  have h := WShape.LE.of_T (n := 0) h.le_sort
  have := Shape0.sort.inj (congrArg (·.1) (WShape.sort_le.1 h))
  exact VLevel.equiv_def'.2 (congrArg SortTag.lv this)

end LogRel
end Lean4Lean

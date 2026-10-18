import Lean4Lean.Theory.Typing.LogRel.RelLift

/-!
# Telescopes related from their types

Two telescopes of `k` pi binders whose types are related, one depth up, at a telescope shape are
related along it (`TeleRel.of_tyDefEq`). This is how the constructors' telescopes of an
inductive type's application become related (`IndTele`) from the constructors' types: the
relation at depth `n+1` relates a pi type's codomains at arguments of depth `n`, which is what
`TeleRel` at depth `n` quantifies over, and each codomain goes back up a depth by `LR.TyDefEq.lift`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr} [ShapeEnv] {henv : env.Ordered}
  {hU : StepUniq env}

omit [ShapeEnv] in
theorem piCount_inst_ge : ∀ (e a : VExpr) (k : Nat), piCount e ≤ piCount (e.inst a k)
  | .forallE _ B, a, k => Nat.succ_le_succ (piCount_inst_ge B a (k+1))
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .app .., _, _ | .lam .., _, _
  | .proj .., _, _ => Nat.zero_le _

omit [ShapeEnv] in
theorem exists_forallE_of_piCount : ∀ {T : VExpr}, 0 < piCount T → ∃ D B, T = .forallE D B
  | .forallE _ _, _ => ⟨_, _, rfl⟩

/-- Telescopes whose types are related one depth up at a telescope shape are related along it. -/
theorem TeleRel.of_tyDefEq : ∀ {k T T'} {tel : WShape n}, tel.HasType .type →
    k ≤ piCount T → k ≤ piCount T' →
    (LR (U := U) (Γ := Γ) henv hU (n+1)).TyDefEq T T' (tel.lift (n+1)) →
    TeleRel (LR (U := U) (Γ := Γ) henv hU n) k T T' tel
  | 0, _, _, _, _, _, _, _ => trivial
  | k+1, T, T', tel, ht, hk, hk', H => by
    cases hv : tel.piView with
    | none => exact .inl hv
    | some bg =>
      obtain ⟨b, g⟩ := bg
      cases n with
      | zero => simp at hv
      | succ n =>
      obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
      have ⟨tb, tg⟩ := WShape.piView_type ht hv
      rw [WShape.lift_forallE (Nat.le_succ n)] at H
      simp only [LR, LRS, LRS.TyDefEq.forallE_iff] at H
      obtain ⟨D, B, rT⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk)
      obtain ⟨D', B', rT'⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk')
      subst rT rT'
      rcases H with ⟨B₁, F₁, B₂, F₂, r1, r2, hBB, -, hTy, hP⟩ | ⟨hN, -⟩
      · cases StepS.determ hU .rfl forallE_whnf' r1 forallE_whnf'
        cases StepS.determ hU .rfl forallE_whnf' r2 forallE_whnf'
        refine .inr ⟨D, B, D', B', _, _, hv, .rfl, .rfl, hBB, hTy, fun a a' p hp ha hr => ?_⟩
        have h1 := (hP.1 hp ha hr).1
        have h2 := hP.2 hp ha.hasType.2 ((LR _ _ _).left ((LR _ _ _).symm hr))
        have h12 := (LR (U := U) (Γ := Γ) henv hU (n+1)).trans_ty h1 h2
        refine TeleRel.of_tyDefEq (tg p) ?_ ?_ ((LR.TyDefEq.lift (Nat.le_succ _) (tg p)).2 h12)
        · exact Nat.le_trans (Nat.le_of_succ_le_succ hk) (piCount_inst_ge _ _ _)
        · exact Nat.le_trans (Nat.le_of_succ_le_succ hk') (piCount_inst_ge _ _ _)
      · exact (NeRed.not_forallE hU hN .rfl).elim

end LogRel
end Lean4Lean

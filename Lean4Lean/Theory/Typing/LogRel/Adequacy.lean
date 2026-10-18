import Lean4Lean.Theory.Typing.LogRel.RelLift
import Lean4Lean.Theory.Typing.LogRel.SoundWF

/-!
# Adequacy of the logical relation: substitutions and the induction's statement

As upstream's `Experimental/ShapeLogRelAdequacy.lean`: the relation is over a fixed context `Γ₀`,
and a derivation in `Γ` is related after closing substitutions `σ σ'` into `Γ₀` that are related
at a valuation `ρ` of `Γ` in the model (`LR.SubstWF`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] (henv : env.Ordered) (hU : StepUniq env)

/-- One related pair of substituted values `x x'` at the type `A₀`, which is `A` and `A'` under the
two substitutions, valued by `ρ`'s variable `i`. -/
def LR.Subst1 (Γ₀ : List VExpr) (x x' A₀ A A' : VExpr) (ρ : Valuation) (i := 0) : Prop :=
  env.IsDefEq U Γ₀ x x' A ∧ ∀ {{n}} (a : WShape n), LE_Interp env ρ a.T A₀ →
    (a.HasType .type → (∃ u, env.IsDefEq U Γ₀ A A' (.sort u)) ∧
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp env ρ m.T (.bvar i) → m.HasType a →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq x x' A m a

/-- Related substitutions of `Γ` into `Γ₀`, valued by `ρ`. -/
inductive LR.SubstWF (Γ₀ : List VExpr) : VExpr.Subst → VExpr.Subst → List VExpr → Valuation → Prop where
  | id : LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp env ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType .type) →
    LE_Interp env ρ a A → x.HasType a → env.HasType U Γ A (.sort u) →
    LR.Subst1 (U := U) henv hU Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

variable {henv hU}

theorem LR.SubstWF.fits : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ → LE_Interp.Valuation.Fits env Γ₀ Γ ρ
  | .id => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq (hΓ₀ : OnCtx Γ₀ (env.IsType U)) :
    LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ → VEnv.Ctx.SubstEq env U Γ₀ σ σ' Γ
  | .id => .id henv hΓ₀
  | .cons W _ _ _ hA h0 => .cons (W.toSubstEq hΓ₀) hA h0.1

theorem LR.SubstWF.left (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
    LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _ _ _).left_ty h2⟩
    · exact (LR _ _ _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
    LR.SubstWF (U := U) henv hU Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 (.bot' .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _ _ _).symm_ty h2⟩
    · let ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _ _ _).conv (.base h1) h2 ((LR _ _ _).symm ((h0.2 a ha).2 hM hmem))

variable (henv hU) in
/-- What the induction proves of a derivation `M ≡ N : A` in `Γ` at shapes `m a`. -/
def LR.Adequate (Γ₀ Γ : List VExpr) (ρ : Valuation) (M N A : VExpr) (m a : WShape n) :=
  (∀ {{σ σ'}}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a

namespace LR.Adequate

theorem bot (ha : a.HasType .type) : Adequate (U := U) henv hU Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ _ => ⟨(LR _ _ _).bot ha, (LR _ _ _).bot ha⟩, fun _ _ => (LR _ _ _).bot ha⟩

theorem fits (H : LE_Interp.Valuation.Fits env Γ₀ Γ ρ → Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a) :
    Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem refl
    (H : ∀ {{σ σ'}}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate (U := U) henv hU Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem left : Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a → Adequate (U := U) henv hU Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem symm : Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a → Adequate (U := U) henv hU Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ => ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR _ _ _).symm (h2 W)⟩

theorem trans :
    Adequate (U := U) henv hU Γ₀ Γ ρ M₁ M₂ A m a → Adequate (U := U) henv hU Γ₀ Γ ρ M₂ M₃ A m a →
    Adequate (U := U) henv hU Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR _ _ _).trans (a2 W) (b2 W)⟩

theorem trans' : Adequate (U := U) henv hU Γ₀ Γ ρ A₁ A₂ (.sort u) a (.sort r') →
    Adequate (U := U) henv hU Γ₀ Γ ρ A₂ A₃ (.sort v) a (.sort r) →
    Adequate (U := U) henv hU Γ₀ Γ ρ A₁ A₃ (.sort u) a (.sort r')
  | ⟨a1, a2⟩, ⟨b1, b2⟩ => by
    refine ⟨fun σ σ' W => ⟨(a1 W).1, ?_⟩, fun _ W => (LR _ _ _).trans' (a2 W) (b2 W)⟩
    have h1 := (LR _ _ _).trans' (a1 W.left).2 (b2 W.left)
    have h2 := (LR _ _ _).trans' (a1 W.symm.left).2 (b2 W.symm.left)
    exact (LR _ _ _).trans ((LR _ _ _).symm h1) <| (LR _ _ _).trans (a1 W).2 h2

end LR.Adequate

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.TShape.HasType.toType' {a : TShape} (h : a.HasType (.sort r)) :
    a.HasType .type := by
  have := (TShape.HasType.def (Nat.le_refl a.1) (Nat.zero_le _)).1 h
  rw [TShape.sort, WShape.lift_sort] at this
  exact (TShape.HasType.def (Nat.le_refl a.1) (Nat.zero_le _)).2 (by
    rw [TShape.type, TShape.sort, WShape.lift_sort]; exact this.toType)

theorem _root_.Lean4Lean.LogRel.LE_Interp.le_sort' {a : WShape n}
    (H : LE_Interp env ρ a.T (.sort u)) : a ≤ .sort (levelRel u) := by
  have := (TShape.LE.lift_l (a := a.T) (b := (WShape.sort (n := n) (levelRel u)).T) (Nat.le_refl _)).1
    (H.le_sort.trans TShape.sort_eqv.2)
  rwa [WShape.lift_self] at this

/-- Extending related substitutions by a pair of related values. -/
theorem LR.Adequate.cons (hM : ModelEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hTA : SoundTy env Γ A (.sort u))
    (ihA : ∀ {ρ n} {m a : WShape n}, LE_Interp env ρ m.T A → LE_Interp env ρ a.T (.sort u) →
      m.HasType a → Adequate (U := U) henv hU Γ₀ Γ ρ A A' (.sort u) m a)
    (HA : env.IsDefEq U Γ A A' (.sort u))
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp env ρ a₁.T A)
    (hx : env.IsDefEq U Γ₀ x x' (A.subst σ))
    (hv : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁)
    (W : SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
    SubstWF (U := U) henv hU Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.hasType.1 ⟨hx, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ := hTA W.fits hA
    exact ⟨_, le_a, hA', (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType'⟩
  have ha' := (LE_Interp.weak_iff hM.closed).1 ha'
  refine ⟨fun ht => ⟨⟨_, HA.hasType.1.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)⟩, ?_⟩,
    fun m' hm' ht => ?_⟩
  · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (hTA W.fits ha').out
    refine (LR.TyDefEq.lift le_n ht).1 <| (LR _ _ _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
      (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact (LR _ _ _).toType <| (LR _ _ _).mono_r_1 hSort.le_sort' hmem'
      (.mono_r hSort.le_sort' .sort hmem') ((LR _ _ _).sort_iff_ty.2 (.inl ⟨_, _, .rfl, .rfl,
        (rfl : VLevel.Equiv _ _)⟩)) ((ihA hA' hSort hmem').1 W).1
  · have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1 (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat hM ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (LR.DefEq.lift le_n ht).1 <|
      (LR _ _ _).mono_r_2 hj2 ht' hJ <|
      (LR _ _ _).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      (LR _ _ _).mono_r_1 hj1 hp' hJ' ?_ <| (LR.DefEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd} (hA : LE_Interp env ρ a.T A) (ha : a.HasType .type) :
        (LR (U := U) (Γ := Γ₀) henv hU nd).TyDefEq (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (hTA W.left.fits hA).out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := (LR _ _ _).left_ty <| (LR _ _ _).toType <| (LR _ _ _).mono_r_1
        hSort.le_sort' hmem' (.mono_r hSort.le_sort' .sort hmem')
        ((LR _ _ _).sort_iff_ty.2 (.inl ⟨_, _, .rfl, .rfl, (rfl : VLevel.Equiv _ _)⟩)) v2
      (LR.TyDefEq.lift le_n ha).1 <| (LR _ _ _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    refine (LR _ _ _).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
    · exact (LR.TyDefEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (LR.TyDefEq.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `TyDefEq` from a `DefEq` at a sort type. -/
theorem LR.toValTy {m : WShape n'} {b : WShape n} (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type) (hSort : LE_Interp env ρ a.T (.sort u)) (hmem' : m.HasType a)
    (H : (LR (U := U) (Γ := Γ₀) henv hU n').DefEq M N (.sort u) m a) :
    (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq M N b := by
  have hle := hSort.le_sort'
  refine (LR.TyDefEq.lift le_n ht).1 ?_
  refine (LR _ _ _).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact (LR _ _ _).toType <| (LR _ _ _).mono_r_1 hle hmem'
    (.mono_r hle .sort hmem')
    ((LR _ _ _).sort_iff_ty.2 (.inl ⟨_, _, .rfl, .rfl, (rfl : VLevel.Equiv _ _)⟩)) H

end LogRel
end Lean4Lean

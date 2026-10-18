import Lean4Lean.Theory.Typing.LogRel.RelS

/-!
# The relation at lifted shapes

A shape lifted to a greater depth is related exactly where the shape is (`LR.DefEq.lift`,
`LR.TyDefEq.lift`), as upstream's.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr} [ShapeEnv]
  {henv : env.Ordered} {hU : StepUniq env}

@[simp] theorem LR_zero : LR (U := U) (Γ := Γ) henv hU 0 = LR0 hU := rfl
@[simp] theorem LR_succ : LR (U := U) (Γ := Γ) henv hU (n+1) = LRS henv hU (LR (U := U) (Γ := Γ) henv hU n) := rfl

private theorem LRS.PiDefEq.lift_aux
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n') (htpi_a : WShape.HasTypePi f b true)
    (IH1 : ∀ {M N : VExpr} {m : WShape n}, WShape.HasType m .type →
      ((LR (U := U) (Γ := Γ) henv hU n').TyDefEq M N (m.lift n') ↔ (LR (U := U) (Γ := Γ) henv hU n).TyDefEq M N m))
    (IH2 : ∀ {M N A : VExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR (U := U) (Γ := Γ) henv hU n').DefEq M N A (m.lift n') (a.lift _) ↔
        (LR (U := U) (Γ := Γ) henv hU n).DefEq M N A m a)) :
    LRS.PiDefEq (LR (U := U) (Γ := Γ) henv hU n') B F₁ F₂ (b.lift n') (f.lift n') ↔
    LRS.PiDefEq (LR (U := U) (Γ := Γ) henv hU n) B F₁ F₂ b f := by
  have htpi_w := WShape.HasTypePi.iff.1 htpi_a
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r1),
             (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ r2)⟩
    · exact (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      obtain ⟨q, d1, d2⟩ := WShapeFun.app_eq (f.lift n') _
      obtain ⟨q₀, y₀, d2₀, rfl, d3⟩ := (WShapeFun.mem_lift le).1 d2
      obtain ⟨qx', qy', d2₀', qxle, qyle, hq⟩ := WShape.HasDom.def.1 htpi_a.1 _ _ d2₀
      have v' := (IH2 hq).1 ((LR (U := U) (Γ := Γ) henv hU n').mono_l (((WShape.lift_le_lift le).2 qxle).trans d1)
        ((WShape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸ ⟨
        (LR (U := U) (Γ := Γ) henv hU n').mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l
          ((IH1 ht_q).2 r1),
        (LR (U := U) (Γ := Γ) henv hU n').mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l
          ((IH1 ht_q).2 r2)⟩
    · have hq_body := hEdge.2 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸ (LR (U := U) (Γ := Γ) henv hU n').mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l
        ((IH1 ht_q).2 hq_body)

private theorem LRS.LamDefEq.lift_aux
    {g : WShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : WShape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : VExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR (U := U) (Γ := Γ) henv hU n').DefEq M N A (m.lift n') (a.lift _) ↔
        (LR (U := U) (Γ := Γ) henv hU n).DefEq M N A m a))
    (hEdge : LRS.PiDefEq (LR (U := U) (Γ := Γ) henv hU n) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR (U := U) (Γ := Γ) henv hU n') M N A₁ A₂ (g.lift n') (a₁.lift n') (a₂.lift n') ↔
    LRS.LamDefEq (LR (U := U) (Γ := Γ) henv hU n) M N A₁ A₂ g a₁ a₂ := by
  have htm_w := WShape.HasTypeLam.iff.1 htm
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm_w.2.2 _ hp)).1 ?_, (IH (htm_w.2.2 _ hp)).1 ?_⟩
        <;> rw [WShapeFun.lift_app le, WShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IH (htm_w.2.2 _ hp)).1
      rw [WShapeFun.lift_app le, WShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun a' b' p hp ha v => ?_, fun a' p hp ha v => ?_⟩
    all_goals
      obtain ⟨_, dg1, dg2⟩ := WShapeFun.app_eq (g.lift n') p
      obtain ⟨_, da1, da2⟩ := WShapeFun.app_eq (a₂.lift n') p
      obtain ⟨qg, yg, dg2₀, rfl, dg3⟩ := (WShapeFun.mem_lift le).1 dg2
      obtain ⟨qa, ya, da2₀, rfl, da3⟩ := (WShapeFun.mem_lift le).1 da2
      have ⟨yg₁, yg₂⟩ := WShapeFun.app_of_mem dg2₀
      have ⟨ya₁, ya₂⟩ := WShapeFun.app_of_mem da2₀
      have ⟨qg', qg'le, hqg, qg'app⟩ := WShape.HasDom.iff.1 htm.2.1 qg
      have ⟨qa', qa'le, hqa, qa'app⟩ := WShape.HasDom.iff.1 htm.1.1 qa
      rw [dg3, da3]
      have v_lo := (IH hqg).1 <| (LR (U := U) (Γ := Γ) henv hU n').mono_l
        (((WShape.lift_le_lift le).2 qg'le).trans dg1) ((WShape.HasType.lift le).2 hqg) hp v
      have v_lo_qa := (IH hqa).1 <| (LR (U := U) (Γ := Γ) henv hU n').mono_l
        (((WShape.lift_le_lift le).2 qa'le).trans da1) ((WShape.HasType.lift le).2 hqa) hp v
      have ht_lo := htm_w.2.2 _ hqg
      have htm_p := WShape.HasTypePi.iff'.1 htm_w.1
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR (U := U) (Γ := Γ) henv hU n).left v_lo_qa)
      have vt_qa' := (LR (U := U) (Γ := Γ) henv hU n).mono_r_2_ty qa'app (htm_p.2 qa) (htm_p.2 qa') vt_qa
      have ht_yg_qg' : yg.HasType (a₂.app qg') :=
        ht_lo.mono_l (WShapeFun.app_mono_r qg'le |>.trans yg₁) (yg₂.trans qg'app)
      have le_a2_ya := by
        refine (a₂.app_mono_r qg'le).trans (.trans ?_ ya₁)
        rw [← WShape.lift_le_lift le, WShapeFun.lift_app le]
        exact (WShapeFun.app_mono_r dg1 (f := a₂.lift n')).trans <| da3 ▸ WShape.lift_mono le ya₂
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg := ya_sort.mono_r le_a2_ya ht_yg_qg'
      have vt_ya := (LR (U := U) (Γ := Γ) henv hU n).mono_r_2_ty ya₂ ya_sort (htm_p.2 qa) vt_qa'
      have go {M N} (r : (LR (U := U) (Γ := Γ) henv hU n).DefEq M N (A₂.inst a') (g.app qg') (a₂.app qg')) :
          (LR (U := U) (Γ := Γ) henv hU n').DefEq M N (A₂.inst a') (yg.lift n') (ya.lift n') :=
        (IH ht_yg).2 <|
        (LR (U := U) (Γ := Γ) henv hU n).mono_r_1 le_a2_ya ht_yg_qg' ht_yg vt_ya <|
        (LR (U := U) (Γ := Γ) henv hU n).mono_l (yg₂.trans qg'app) ht_yg_qg' ht_lo r
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo; exact ⟨go r1, go r2⟩
    · exact go (hP.2 hqg ha v_lo)

private theorem LR.lift_succ_aux :
    (∀ {M N : VExpr} {m : WShape n}, WShape.HasType m .type →
      (LRS.TyDefEq (LR (U := U) (Γ := Γ) henv hU n) M N (m.lift _) ↔ (LR (U := U) (Γ := Γ) henv hU n).TyDefEq M N m)) ∧
    (∀ {M N A : VExpr} {m a : WShape n}, WShape.HasType m a →
      (LRS.DefEq (LR (U := U) (Γ := Γ) henv hU n) M N A (m.lift _) (a.lift _) ↔
        (LR (U := U) (Γ := Γ) henv hU n).DefEq M N A m a)) := by
  induction n with
  | zero =>
    refine ⟨fun {M N m} _ => ?_, fun {M N A m a} _ => ?_⟩
    · cases m using WShape.casesOn <;> exact .rfl
    · cases m using WShape.casesOn <;> cases a using WShape.casesOn <;> exact .rfl
  | succ k ih =>
    refine have h1 := ?_; ⟨h1, ?_⟩
    · intro M N m hmt
      cases m using WShape.casesOn' with
      | forallE b f => ?_
      | sort r => rw [WShape.lift_sort]; exact .rfl
      | indTy r c l =>
        rw [WShape.lift_indTy (Nat.le_succ k), LRS.TyDefEq.indTy_iff, LR_succ]
        refine Iff.trans ?_ (LRS.TyDefEq.indTy_iff (IH := LR (U := U) (Γ := Γ) henv hU k) (r := r)).symm
        exact or_congr (and_congr .rfl (IndTele.lift ih.1 ih.2 hmt.indTy_tels')) .rfl
      | bot => rw [WShape.lift_bot]; exact .rfl
      | lam f hf => rw [WShape.lift_lam (Nat.le_succ k)]; exact .rfl
      | ctor c l hc => rw [WShape.lift_ctor (Nat.le_succ k)]; exact .rfl
      rw [WShape.lift_forallE (Nat.le_succ k)]
      have ⟨_, htpi, rfl⟩ := WShape.HasType.forallE_l.1 hmt
      simp only [LRS.TyDefEq.forallE_iff, LR_succ]
      refine or_congr ?_ .rfl
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, rM, rN, hB, hF, hValB, hE⟩ <;>
        refine ⟨B₁, F₁, B₂, F₂, rM, rN, hB, hF, ?_, ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).1 hE
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).2 hE
    · intro M N A m a hma
      cases a using WShape.casesOn' with
      | bot => rw [WShape.lift_bot]; exact .rfl
      | indTy r c l =>
        rw [WShape.lift_indTy (Nat.le_succ k)]
        cases m using WShape.casesOn' with
        | ctor c' fs hf =>
          rw [WShape.lift_ctor (Nat.le_succ k), LRS.DefEq.ctor_indTy, LR_succ]
          refine Iff.trans ?_ (LRS.DefEq.ctor_indTy (IH := LR (U := U) (Γ := Γ) henv hU k) (r := r) (hf := hf)).symm
          refine or_congr ?_ .rfl
          by_cases hs : IsStruct c' = true
          · simp only [hs, if_true]; exact StructVal.lift ih.1 ih.2 hma.indTy_tels
          · simp only [hs, if_false, Bool.false_eq_true]; exact CtorVal.lift ih.1 ih.2 hma.indTy_tels
        | bot => rw [WShape.lift_bot]; exact .rfl
        | sort => rw [WShape.lift_sort]; exact .rfl
        | forallE => rw [WShape.lift_forallE (Nat.le_succ k)]; exact .rfl
        | lam => rw [WShape.lift_lam (Nat.le_succ k)]; exact .rfl
        | indTy => rw [WShape.lift_indTy (Nat.le_succ k)]; exact .rfl
      | sort => rw [WShape.lift_sort]; exact h1 hma.toType
      | forallE a₁ a₂ => ?_
      | _ => cases hma.isType
      have ⟨_, htpi_a, _⟩ := WShape.HasType.forallE_l.1 hma.isType
      obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
      unfold WShape.lam'; split
      · rw [WShape.lift_lam (Nat.le_succ k), WShape.lift_forallE (Nat.le_succ k)]
        simp only [LRS.DefEq.lam_forallE, LR_succ]
        refine or_congr ?_ .rfl
        constructor <;> intro ⟨A₁, A₂, u, v, rA, eA, hA1, hValA, hA₂, hEdge, hP⟩ <;>
          [ have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge;
            have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge ] <;>
          refine ⟨A₁, A₂, u, v, rA, eA, hA1, ?_, hA₂, hEdge', ?_⟩
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA
        · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
        · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA
        · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP
      · rw [WShape.lift_bot, WShape.lift_forallE (Nat.le_succ k)]; exact .rfl

theorem LR.DefEq.lift {m a : WShape n} (le : n ≤ n') (hma : WShape.HasType m a) :
    (LR (U := U) (Γ := Γ) henv hU n').DefEq M N A (m.lift n') (a.lift _) ↔
      (LR (U := U) (Γ := Γ) henv hU n).DefEq M N A m a := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm, (WShape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((WShape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : WShape n} (le : n ≤ n') (hmt : WShape.HasType m .type) :
    (LR (U := U) (Γ := Γ) henv hU n').TyDefEq M N (m.lift _) ↔ (LR (U := U) (Γ := Γ) henv hU n).TyDefEq M N m := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm]
  have := (WShape.HasType.lift le).2 hmt
  simp [WShape.type] at this
  exact (LR.lift_succ_aux.1 this).trans ih

end LogRel
end Lean4Lean

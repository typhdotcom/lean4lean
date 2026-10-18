import Lean4Lean.Theory.Typing.LogRel.Targets
import Lean4Lean.Theory.Typing.LogRel.RelLift
import Lean4Lean.Theory.Typing.LogRel.Uniq

/-!
# Chain inversion from adequacy

A chain of equalities at sorts (`TyEq`) relates its ends in the logical relation: each link is
related by adequacy at a shape of the chain's common interpretations, which the model's soundness
makes the same along the chain, and the relation is transitive at a shape. At a sort or a pi type
the relation then reads off what `ChainInv` asks.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv}

/-- The least shape of a pi type. -/
noncomputable abbrev piShape (env : VEnv) : @WShape env.shapeEnv 1 :=
  @WShape.forallE env.shapeEnv 0 (@WShape.bot env.shapeEnv 0) (@WShapeFun.bot env.shapeEnv 0)

theorem piShape_type (env : VEnv) :
    @WShape.HasType env.shapeEnv 1 (piShape env) (@WShape.type env.shapeEnv 1) := by
  letI := env.shapeEnv
  refine WShape.HasType.forallE (WShape.HasTypePi.def.2
    ⟨WShape.HasDom.bot (.bot' .sort), fun x y h => ?_⟩)
  obtain ⟨-, rfl⟩ := WShapeFun.mem_bot.1 h
  exact .bot' .sort

/-- The relation on types at depth `n`, in a well-formed environment's own shape model. -/
abbrev TyRel (henvW : env.WF) (U : Nat) (Γ : List VExpr) (n : Nat) :
    VExpr → VExpr → @WShape env.shapeEnv n → Prop :=
  @LogRelBase.TyDefEq env.shapeEnv env U Γ n
    (@LogRel.toLogRelBase env.shapeEnv env U Γ n
      (@LR env U Γ env.shapeEnv henvW.ordered henvW.stepUniq n))

section
variable (henvW : env.WF) {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
  (hH : @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
    henvW.stepUniq env Γ)
include hΓ hH

/-- A link of a chain whose left end has the interpretations of a sort is related at that sort's
shape. -/
theorem link_sort {X Y : VExpr} {u w : VLevel} (d : env.IsDefEq U Γ X Y (.sort w))
    (hX : @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ (.sort u) X) :
    TyRel henvW U Γ 0 X Y (@WShape.sort env.shapeEnv 0 (levelRel u)) := by
  letI := env.shapeEnv
  have H := d.strong henvW.ordered hΓ
  have hS : ∀ {Γ M N A}, env.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    henvW.modelSound
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  have hsX : LE_Interp env .nil (TShape.sort (levelRel u)) X :=
    (hX W.fits).1 (LE_Interp.sort' (l := u) (ρ := .nil))
  obtain ⟨n', m', a, -, le_m, hm', ha, hty⟩ := ((hS H).left.sound W.fits hsX).out
  cases sort_shape_of_le ((hX W.fits).2 hm') le_m
  cases WShape.HasType.sort_l_inv hty
  have R := (LR.adequacy_of (henvW.modelEnv AxOK.none) .rfl hS hΓ hH H hΓ hm' ha hty).2 W
  simp only [subst_id] at R
  have R := (LR _ _ _).toType R
  have := (LR.TyDefEq.lift (U := U) (Γ := Γ) (henv := henvW.ordered) (hU := henvW.stepUniq)
    (M := X) (N := Y) (n' := n') (Nat.zero_le _) (m := WShape.sort (levelRel u))
    WShape.HasType.sort).1
  exact this (by simpa [WShape.lift_sort] using R)

/-- A link of a chain whose left end has the interpretations of a pi type is related at the
least pi shape. -/
theorem link_pi {X Y A B : VExpr} {w : VLevel} (d : env.IsDefEq U Γ X Y (.sort w))
    (hX : @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ (.forallE A B) X) :
    TyRel henvW U Γ 1 X Y (piShape env) := by
  letI := env.shapeEnv
  have H := d.strong henvW.ordered hΓ
  have hS : ∀ {Γ M N A}, env.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    henvW.modelSound
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  have hPi : LE_Interp env .nil (WShape.T (n := 1) (.forallE .bot WShapeFun.bot))
      (.forallE A B) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  obtain ⟨n', m', a, hn, le_m, hm', ha, hty⟩ := ((hS H).left.sound W.fits ((hX W.fits).1 hPi)).out
  have R := (LR.adequacy_of (henvW.modelEnv AxOK.none) .rfl hS hΓ hH H hΓ hm' ha hty).2 W
  simp only [subst_id] at R
  have hle : (piShape env).lift n' ≤ m' := (TShape.LE.lift_l hn).1 le_m
  obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by simp at hn; omega⟩
  rw [WShape.lift_forallE (Nat.zero_le _)] at hle
  obtain ⟨a', f', -, -, rfl⟩ := WShape.forallE_le.1 hle
  rcases WShape.le_sort.1 ha.le_sort' with rfl | rfl
  · have := hty.bot_r
    simp [WShape.forallE, WShape.bot, WShape.ext_iff, Shape.bot] at this
  · have R := (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq _).toType R
    have hle' : (piShape env).lift (k+1) ≤ a'.forallE f' := by
      rw [WShape.lift_forallE (Nat.zero_le _)]; exact hle
    have R := (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq _).mono_r_2_ty hle'
      ((WShape.HasType.lift hn).2 (piShape_type env)) hty.toType R
    exact (LR.TyDefEq.lift hn (piShape_type env)).1 R

/-- A chain's ends have the same interpretations, and if the left end has a sort's
interpretations, the chain is related at that sort's shape. -/
theorem chain_sort_aux {A B : VExpr} (H : TyEq env U Γ A B) :
    @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ A B ∧
    ∀ u, @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ (.sort u) A →
      TyRel henvW U Γ 0 A B (@WShape.sort env.shapeEnv 0 (levelRel u)) := by
  letI := env.shapeEnv
  induction H with
  | base d =>
    exact ⟨(henvW.modelSound (d.strong henvW.ordered hΓ)).sound,
      fun u hX => link_sort henvW hΓ hH d hX⟩
  | trans _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun u hX => ?_⟩
    exact (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq 0).trans_ty (ih1.2 u hX)
      (ih2.2 u (hX.trans ih1.1))

/-- A chain of sorts relates equivalent levels. -/
theorem chain_sort {u v : VLevel} (H : TyEq env U Γ (.sort u) (.sort v)) : u ≈ v := by
  letI := env.shapeEnv
  have R := (chain_sort_aux henvW hΓ hH H).2 u SoundEq.rfl
  rcases (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq 0).sort_iff_ty.1 R with
    ⟨u', v', h1, h2, h⟩ | ⟨h1, -⟩
  · cases StepS.of_whnf sort_whnf h1; cases StepS.of_whnf sort_whnf h2; exact h
  · exact (NeRed.not_sort' henvW.stepUniq h1).elim

/-- A chain whose left end has a pi type's interpretations is related at the least pi shape. -/
theorem chain_pi_aux {X Y : VExpr} (H : TyEq env U Γ X Y) :
    @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ X Y ∧
    ∀ A B, @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ (.forallE A B) X →
      TyRel henvW U Γ 1 X Y (piShape env) := by
  letI := env.shapeEnv
  induction H with
  | base d =>
    exact ⟨(henvW.modelSound (d.strong henvW.ordered hΓ)).sound,
      fun A B hX => link_pi henvW hΓ hH d hX⟩
  | trans _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun A B hX => ?_⟩
    exact (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq 1).trans_ty (ih1.2 A B hX)
      (ih2.2 A B (hX.trans ih1.1))

/-- A chain of pi types relates domains and codomains by chains. -/
theorem chain_forallE {A B A' B' : VExpr} (H : TyEq env U Γ (.forallE A B) (.forallE A' B')) :
    TyEq env U Γ A A' ∧ TyEq env U (A::Γ) B B' := by
  letI := env.shapeEnv
  have R := (chain_pi_aux henvW hΓ hH H).2 A B SoundEq.rfl
  simp only [TyRel, LR, LRS, LRS.TyDefEq.forallE_iff] at R
  rcases R with ⟨_, _, _, _, r1, r2, hB, hF, -⟩ | ⟨h1, -⟩
  · cases StepS.of_whnf forallE_whnf r1; cases StepS.of_whnf forallE_whnf r2; exact ⟨hB, hF⟩
  · exact (NeRed.not_forallE henvW.stepUniq h1 .rfl).elim

end

/-- Chain inversion from adequacy's environment cases at every context, given it for
projections. -/
theorem ChainInv.of_adequacy (henvW : env.WF) {U : Nat}
    (hH : ∀ Γ, OnCtx Γ (env.IsType U) →
      @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
        henvW.stepUniq env Γ)
    (hP : ProjChain env U) : ChainInv env U where
  sort hΓ H := chain_sort henvW hΓ (hH _ hΓ) H
  forallE hΓ H := chain_forallE henvW hΓ (hH _ hΓ) H
  proj := hP

end LogRel
end Lean4Lean

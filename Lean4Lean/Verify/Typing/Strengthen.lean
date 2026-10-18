import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strengthen

/-! # Strengthening, still assumed

These lemmas rest on `Theory/Typing/Strengthen.lean`, whose statements are false in general.
Only the proofs that still use them import this file. -/

namespace Lean4Lean
open Lean4Lean VEnv Lean
open scoped _root_.List

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' n Γ Γ') in
theorem VLocalDecl.weak'_iff : VLocalDecl.WF env U Γ' (d.lift' n) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weak'_iff henv hΓ' W
  | .vlet .. => HasType.weak'_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') in
theorem VLocalDecl.weakN_iff : VLocalDecl.WF env U Γ' (d.liftN n k) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weakN_iff henv hΓ' W
  | .vlet .. => HasType.weakN_iff henv hΓ' W

namespace VLCtx

variable! (henv : VEnv.WF env) in
theorem FVLift'.wf (W : FVLift' Δ Δ' dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip_fvar _ _ _ ih => exact ih hΔ'.1
  | cons_fvar _ _ hd W ih =>
    let ⟨hΔ', h1, h2⟩ := hΔ'
    refine ⟨ih hΔ', ?_, (VLocalDecl.weak'_iff henv hΔ'.toCtx W.toCtx).1 h2⟩
    rintro _ _ ⟨⟩; exact ⟨fun h => (h1 _ _ rfl).1 <| W.fvars_sublist.subset h, hd⟩
  | cons_bvar _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weak'_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

variable! (henv : VEnv.WF env) in
theorem FVLift.wf (W : FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U :=
  W.toFVLift'.wf henv hΔ'

variable! (henv : VEnv.WF env) in
theorem BVLift.wf (W : BVLift Δ Δ' dn dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip _ _ ih => exact ih hΔ'.1
  | cons _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weakN_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

end VLCtx

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hΓ' W h1 h2 h2

theorem TrExprS.weakFV'_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift' Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hc : Closed e dk) (hv : FVarsIn (· ∈ VLCtx.fvars Δ) e) :
    ∃ e', TrExprS env Us Δ e e' := by
  induction H generalizing Δ Δ₂ dk k with
  | @bvar e A Δ₁ i h1 =>
    suffices ∃ p, Δ.find? (.inl i) = some p from let ⟨_, h⟩ := this; ⟨_, .bvar h⟩
    simp [Closed] at hc
    induction W generalizing i e A Δ₁ with | @cons_bvar _ Δ₂ _ _ _ d _ ih => ?_ | _ => cases hc
    obtain ⟨d, Δ₂, rfl, hΔ₁⟩ : ∃ d Δ₁', Δ₁ = (none, d) :: Δ₁' ∧
        VLCtx.IsDefEq env Us.length Δ₁' Δ₂ := by cases d <;> cases hΔ <;> exact ⟨_, _, rfl, ‹_›⟩
    simp [VLCtx.find?] at h1 ⊢
    rcases i with _ | i <;> simp [VLCtx.next] at h1 ⊢
    obtain ⟨_, _, h1, _⟩ := h1
    have ⟨_, h1⟩ := ih h1 hΔ₁ (Nat.lt_of_succ_lt_succ hc) hv
    exact ⟨_, _, _, _, h1, rfl, rfl⟩
  | @fvar _ _ _ fv => let ⟨_, h⟩ := VLCtx.find?_eq_some.2 hv; exact ⟨_, .fvar h⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 hf ha ih1 ih2 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨f₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨a₁, ih2⟩ := ih2 W hΔ hc.2 hv.2
    have h1 := h1.defeqU_l henv hΔ₁.toCtx <| hf.uniq henv hΔ (ih1.weakFV' henv W hΔ₂)
    have h2 := h2.defeqU_l henv hΔ₁.toCtx <| ha.uniq henv hΔ (ih2.weakFV' henv W hΔ₂)
    have := VExpr.WF.weak'_iff henv hΔ₂.toCtx W.toCtx (e := f₁.app a₁)
    have := this.1 ⟨_, (h1.app h2).defeqDFC henv hΔ.defeqCtx⟩
    have ⟨_, _, h1, h2⟩ := this.app_inv henv (W.wf henv hΔ₂).toCtx
    exact ⟨_, .app h1 h2 ih1 ih2⟩
  | lam h1 ht _ ih1 ih2 =>
    let ⟨_, h1⟩ := h1
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _))
      (hΔ.cons (ofv := none) nofun <| .vlam htt) hc.2 hv.2.fvars_cons
    have h1 := HasType.weak'_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx
      |>.1 (htt.hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .lam ⟨_, h1⟩ ih1 ih2⟩
  | forallE h1 h2 ht hb ih1 ih2 =>
    let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have hΔ' := hΔ.cons (ofv := none) nofun <| .vlam htt
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _)) hΔ' hc.2 hv.2.fvars_cons
    have h1' := htt.hasType.2.defeqDFC henv hΔ.defeqCtx
    have h1 := HasType.weak'_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx |>.1 h1'
    have hΔ₂' : VLCtx.WF _ _ ((none, .vlam _) :: _) := ⟨hΔ₂, nofun, _, h1'⟩
    have h2 := (HasType.weak'_iff (A := .sort _) henv hΔ₂'.toCtx (W.cons_bvar (.vlam _)).toCtx).1 <|
      hb.uniq henv hΔ' (ih2.weakFV' henv (W.cons_bvar _) hΔ₂')
      |>.of_l (Γ := _::_) henv ⟨hΔ₁.toCtx, _, htt.hasType.1⟩ h2
      |>.hasType.2.defeqDFC henv (.succ hΔ.defeqCtx htt)
    exact ⟨_, .forallE ⟨_, h1⟩ ⟨_, h2⟩ ih1 ih2⟩
  | letE h1 ht ha _ ih1 ih2 ih3 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨val₁, ih2⟩ := ih2 W hΔ hc.2.1 hv.2.1
    have hvv := ha.uniq henv hΔ (ih2.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    let ⟨_, h2⟩ := h1.isType henv hΔ₁.toCtx
    have htt := ht.uniq henv hΔ (ih1.weakFV' henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h2
    have ⟨_, ih3⟩ := ih3 (W.cons_bvar (.vlet ..))
      (hΔ.cons nofun <| .vlet hvv htt) hc.2.2 hv.2.2.fvars_cons
    have h1 := HasType.weak'_iff henv hΔ₂.toCtx W.toCtx
      |>.1 ((htt.defeqDF hvv).hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .letE h1 ih1 ih2 ih3⟩
  | lit h1 _ ih => let ⟨_, ih⟩ := ih W hΔ .toConstructor .toConstructor; exact ⟨_, .lit h1 ih⟩
  | mdata _ ih => let ⟨_, ih⟩ := ih W hΔ hc hv; exact ⟨_, .mdata ih⟩
  | proj h1 h2 ih =>
    have hΔ₂ := (hΔ.symm henv).wf
    let ⟨_, ih⟩ := ih W hΔ hc hv
    have htt := h1.uniq henv hΔ (ih.weakFV' henv W hΔ₂)
    have h := VExpr.WF.proj_congr henv hΔ₂.toCtx (IsDefEqU.defeqDFC henv hΔ.defeqCtx h2)
      (htt.defeqDFC henv hΔ.defeqCtx)
    have h2 := (VExpr.WF.weak'_iff henv hΔ₂.toCtx W.toCtx (e := .proj ..)).1
      ⟨_, h.choose_spec.hasType.2⟩
    exact ⟨_, .proj ih h2⟩

theorem TrExprS.weakFV_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hc : Closed e dk) (hv : FVarsIn (· ∈ VLCtx.fvars Δ) e) :
    ∃ e', TrExprS env Us Δ e e' := H.weakFV'_inv henv W.toFVLift' hΔ hc hv

end Lean4Lean

namespace Lean4Lean
open VEnv

/-- A constructor's fields, with the earlier fields that are `P` removed, by strengthening. -/
theorem VInductDecl.FieldsWF.kept_assumed {env : VEnv} (henv : env.WF) {d : VInductDecl}
    {c : VConstructor} {Ds : List VExpr} (hP0 : env.IsTele d.uvars [] d.params)
    (H : d.FieldsWF env d.params.reverse 0 Ds c.fields) {P : Nat → Prop} :
    ∀ k, k < c.fields.length →
      (∀ i ≤ k, ∀ f : VField, c.fields[i]? = some f → ∀ j < i, P j → f.type.Skips 1 (i - 1 - j)) →
      (∀ f : VField, c.fields[k]? = some f →
        env.HasType d.uvars ((c.keptFieldsBy P k).reverse ++ d.params.reverse)
          (VConstructor.strippedTypeBy P k f.type) (.sort f.level)) ∧
      (∀ (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
        (∀ j < k, P j → D.Skips 1 (k - 1 - j)) →
        env.IsDefEqU d.uvars ((c.keptFieldsBy P k).reverse ++ d.params.reverse)
          (VConstructor.strippedTypeBy P k D) (VConstructor.strippedTypeBy P k f.type)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro hk hskip
  have hPc : OnCtx d.params.reverse (env.IsType d.uvars) := by simpa using hP0.onCtx trivial
  have hctx : OnCtx (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse)
      (env.IsType d.uvars) := by
    have := H.tele.1
    rw [← List.take_append_drop k c.fields, List.map_append] at this
    exact (VEnv.IsTele.append_inv this).1.onCtx hPc
  obtain ⟨W, -⟩ := H.keptTele (P := P) (Nat.le_of_lt hk)
    (fun i hi _ fi hfi j hj hq => hskip i (Nat.le_of_lt hi) fi hfi j hj hq)
    fun i hi _ fi hfi => (IH i hi (by omega)
      fun i' hi' => hskip i' (by omega)).1 fi hfi
  refine ⟨fun f hf => ?_, fun D f hD hf hD' => ?_⟩
  · have hty := H.level k f hf
    rw [VConstructor.strippedTypeBy_lift' (P := P) (i := k)
      fun j hj hq => hskip k (Nat.le_refl _) f hf j hj hq] at hty
    exact (VEnv.HasType.weak'_iff henv hctx W (A := .sort _)).1 hty
  · have hDF := H.defeq k D f hD hf
    rw [VConstructor.strippedTypeBy_lift' (P := P) (i := k) (A := D) fun j hj hq => hD' j hj hq,
      VConstructor.strippedTypeBy_lift' (P := P) (i := k)
        fun j hj hq => hskip k (Nat.le_refl _) f hf j hj hq] at hDF
    exact (VEnv.IsDefEqU.weak'_iff henv hctx W).1 hDF

end Lean4Lean

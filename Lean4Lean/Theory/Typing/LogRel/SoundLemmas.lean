import Lean4Lean.Theory.Typing.LogRel.SoundEnv

/-!
# Lemmas about the model's soundness

Injectivity of pi types in the model, interpretations of telescopes, and valuations fitting a
context built from typed interpretations.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv}

/-- Pi types with the same interpretations have domains and codomains with the same
interpretations. -/
theorem SoundEq.forallE_inv (hM : ModelEnv env) (H : SoundEq env Γ (.forallE A B) (.forallE A' B'))
    (hA : SoundTy env Γ A (.sort u)) (hA' : SoundTy env Γ A' (.sort u')) :
    SoundEq env Γ A A' ∧ SoundEq env (A::Γ) B B' := by
  refine have hAA _ ρ W m := ?_; ⟨hAA, fun Γ₀ ρ W m => ?_⟩
  · suffices ∀ {A A' B B' u}, SoundEq env Γ (.forallE A B) (.forallE A' B') →
        SoundTy env Γ A (.sort u) → LE_Interp env ρ m A → LE_Interp env ρ m A' from
      ⟨this H hA, this H.symm hA'⟩
    intro A A' B B' u H hA h
    have ⟨_, a1, a2, a3⟩ := InterpTyped.hsort (hA W) h
    refine ((H W).1 (.forallE' a2 a2 (.bot (TShape.HasType.sort_r.1 a3)) ?_)
      |>.forallE_inv hM).1.mono a1
    intro x _; simpa using .bot
  · suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq env Γ (.forallE A₁ B₁) (.forallE A₂ B₂) →
        SoundEq env Γ A A₁ → LE_Interp env ρ m B₁ → LE_Interp env ρ m B₂ from
      ⟨this H .rfl, this H.symm hAA⟩
    intro A A' B B' H hAA h
    cases W with
    | nil =>
      have := (H .nil).1 <| .forallE' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
      · have := (this.forallE_inv' hM).2 .bot
        simp [WShapeFun.single_app] at this
        refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
      · refine fun _ => ⟨_, WShape.bot_le, .bot' (.bot' .sort), ?_⟩
        simpa [WShapeFun.single_app] using .rfl
      · intro x h'; cases h'.bot_r
        simpa [WShapeFun.single_app, show m.2.T = m from rfl] using
          h.mono_l fun _ => TShape.bot_le'
    | @cons Γ ρ A a x b1 b2 b3 b4 =>
      let k := max (max x.1 m.1) a.1
      have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
      have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
      have := (hAA b1).1 (b3.lift hk.2)
      have := (H b1).1 <| .forallE' (f := .single (x.2.lift k) (m.2.lift k))
        this this (WShape.HasDom.iff.2 ?_) ?_
      · have := (this.forallE_inv' hM).2 (x.2.lift k)
        simp [WShapeFun.single_app, WShape.LE.rfl] at this
        exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
          Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
      · intro x'; simp [WShapeFun.single_app]
        split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot' b4'.isType, WShape.bot_le⟩]
        refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
      · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
        refine h.mono (TShape.lift_eqv hk.1.2).1 |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
        exact (TShape.LE.lift_l hk.1.1).2 h2

/-! ### Valuations of telescopes -/

theorem pushAll_append (ρ : Valuation) :
    ∀ (xs ys : List TShape), pushAll ρ (xs ++ ys) = pushAll (pushAll ρ xs) ys
  | [], _ => rfl
  | _ :: xs, ys => pushAll_append _ xs ys

theorem pushAll_concat (ρ : Valuation) (xs : List TShape) (x : TShape) :
    pushAll ρ (xs ++ [x]) = (pushAll ρ xs).push x := pushAll_append ..

theorem pushAll_apply (ρ : Valuation) :
    ∀ (xs : List TShape) (i : Nat), pushAll ρ xs i =
      if h : i < xs.length then xs.reverse[i]'(by simpa using h) else ρ (i - xs.length)
  | [], i => by simp [pushAll]
  | x :: xs, i => by
    show pushAll (ρ.push x) xs i = _
    rw [pushAll_apply _ xs i]
    simp only [List.reverse_cons, List.length_cons]
    by_cases h1 : i < xs.length
    · rw [dif_pos h1, dif_pos (by omega), List.getElem_append_left]
    · rw [dif_neg h1]
      by_cases h2 : i = xs.length
      · subst h2; rw [dif_pos (by omega)]; simp [Valuation.push]
      · rw [dif_neg (by omega)]
        obtain ⟨k, hk⟩ : ∃ k, i - xs.length = k + 1 := ⟨i - xs.length - 1, by omega⟩
        rw [hk]; show ρ k = _; congr 1; omega

theorem pushAll_mono {ρ ρ' : Valuation} (hρ : ρ.LE ρ') :
    ∀ {xs ys : List TShape}, List.Forall₂ (· ≤ ·) xs ys → (pushAll ρ xs).LE (pushAll ρ' ys)
  | [], [], .nil => hρ
  | _ :: _, _ :: _, .cons h1 h2 => pushAll_mono (Valuation.LE.push.2 ⟨hρ, h1⟩) h2

/-- Typed values for a closed telescope `Δ` at the terms `σs`: given interpretations `ys` of the
terms, larger ones that fit `Δ`, built from the last binder to the first. Each binder's type is
a type, and each term is typed at its binder's type instantiated by the terms before it. -/
theorem fits_ofSubst (hM : ModelEnv env) (W : Valuation.Fits env Γ₀ Γ ρ) :
    ∀ (n : Nat) (Δ σs : List VExpr) (ys : List TShape), Δ.length = n → σs.length = n →
    (∀ i (A : VExpr), Δ[i]? = some A → A.ClosedN i ∧
      ∃ u, SoundTy env (Δ.take i).reverse A (.sort u)) →
    (∀ i (A x : VExpr), Δ[i]? = some A → σs[i]? = some x →
      SoundTy env Γ x (A.subst (VExpr.Subst.dflt.consList (σs.take i)))) →
    List.Forall₂ (fun y x => LE_Interp env ρ y x) ys σs →
    ∃ P, List.Forall₂ (· ≤ ·) ys P ∧ List.Forall₂ (fun y x => LE_Interp env ρ y x) P σs ∧
      Valuation.Fits env [] Δ.reverse (pushAll .nil P)
  | 0, Δ, σs, ys, h1, h2, _, _, hy => by
    obtain rfl := List.eq_nil_of_length_eq_zero h1
    obtain rfl := List.eq_nil_of_length_eq_zero h2
    let .nil := hy
    exact ⟨[], .nil, .nil, .nil⟩
  | n+1, Δ, σs, ys, h1, h2, hΔ, hσ, hy => by
    obtain ⟨Δ, A, rfl⟩ := List.eq_nil_or_concat Δ |>.resolve_left (by rintro rfl; cases h1)
    obtain ⟨σs, x, rfl⟩ := List.eq_nil_or_concat σs |>.resolve_left (by rintro rfl; cases h2)
    simp only [List.concat_eq_append] at *
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h1 h2
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left (by
      rintro rfl; exact absurd (List.Forall₂.length_eq hy) (by simp))
    simp only [List.concat_eq_append] at *
    obtain ⟨hy, hyx⟩ := (List.Forall₂.append_of_right (r₁ := [y]) (r₂ := [x]) rfl).1 hy
    let .cons hyx .nil := hyx
    -- the last binder: a typed interpretation of `x`, at a type interpreting `A` somewhere
    have hAx : SoundTy env Γ x (A.subst (VExpr.Subst.dflt.consList σs)) := by
      have := hσ n A x (by simp [← h1]) (by simp [← h2])
      rwa [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
    obtain ⟨y', t, hle, hy', ht, hty⟩ := hAx W hyx
    obtain ⟨ρ'', htA, hρ''⟩ := (LE_Interp.subst hM).1 ht
    -- the earlier binders must be at least what `A` was interpreted at
    have hρσ (j) (hj : j < n) : LE_Interp env ρ (ρ'' (n - 1 - j)) σs[j] := by
      have := hρ'' (n - 1 - j)
      rw [VExpr.Subst.consList_lt _ _ _ (by omega), List.getElem_reverse] at this
      have e : σs.length - 1 - (n - 1 - j) = j := by omega
      simpa only [e] using this
    let zs := ys.mapIdx fun j y => y.join (ρ'' (n - 1 - j))
    have hyl : ys.length = n := by rw [List.Forall₂.length_eq hy, h2]
    have hz {j z} (h : zs[j]? = some z) : ∃ (hj : j < n), LE_Interp env ρ z σs[j] ∧
        ys[j] ≤ z ∧ ρ'' (n - 1 - j) ≤ z := by
      simp only [zs, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
      obtain ⟨y₀, h0, rfl⟩ := h
      have hj : j < n := hyl ▸ (List.getElem?_eq_some_iff.1 h0).1
      have hy₀ : ys[j] = y₀ := (List.getElem?_eq_some_iff.1 h0).2
      have h3 : LE_Interp env ρ y₀ σs[j] :=
        hy.getElem?' h0 (List.getElem?_eq_getElem (by omega))
      have hJ := TShape.Join.mk (h3.compat hM (hρσ j hj))
      exact ⟨hj, h3.join' hM (hρσ j hj), hy₀ ▸ hJ.le.1, hJ.le.2⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := fits_ofSubst hM W n Δ σs zs h1 h2
      (fun i A' hA' => by
        have := hΔ i A' (by rw [List.getElem?_append_left (by
          have := (List.getElem?_eq_some_iff.1 hA').1; omega)]; exact hA')
        rwa [List.take_append_of_le_length (by
          have := (List.getElem?_eq_some_iff.1 hA').1; omega)] at this)
      (fun i A' x' hA' hx' => by
        have hi := (List.getElem?_eq_some_iff.1 hA').1
        have := hσ i A' x' (by rw [List.getElem?_append_left (by omega)]; exact hA')
          (by rw [List.getElem?_append_left (by omega)]; exact hx')
        rwa [List.take_append_of_le_length (by omega)] at this)
      (List.forall₂_of_getElem? (by simp [zs, hyl, h2]) fun j z b hz' hb => by
        obtain ⟨hj, h3, -, -⟩ := hz hz'
        obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hb; exact h3)
    have hPl : P.length = n := by rw [List.Forall₂.length_eq hP2, h2]
    have ⟨hcl, u, hA⟩ := hΔ n A (by simp [← h1])
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hA
    -- `A` at the earlier binders' values
    have htA' : LE_Interp env (pushAll .nil P) t A := by
      have := LE_Interp.closed hM.closed hcl (ρ' := fun v => if v < n then ρ'' v else Valuation.nil v)
        (fun i hi => by simp [hi]) htA
      refine this.mono_l fun v => ?_
      by_cases hv : v < n
      · simp only [hv, if_true]
        rw [pushAll_apply, dif_pos (by omega), List.getElem_reverse]
        have hzv : zs[n - 1 - v]? = some (zs[n - 1 - v]'(by simp [zs, hyl]; omega)) :=
          List.getElem?_eq_getElem _
        obtain ⟨-, -, -, h4⟩ := hz hzv
        refine (show n - 1 - (n - 1 - v) = v by omega) ▸ h4 |>.trans ?_
        exact hP1.getElem?' hzv (List.getElem?_eq_getElem _) |>.trans (by
          simp only [hPl]; exact .rfl)
      · simp only [hv, if_false]; exact TShape.bot_le'
    refine ⟨P ++ [y'], ?_, List.forall₂_append' hP2 (.cons hy' .nil), ?_⟩
    · refine List.forall₂_append' ?_ (.cons hle .nil)
      refine List.forall₂_of_getElem? (by rw [hyl, hPl]) fun j a b ha hb => ?_
      have hzj : zs[j]? = some (zs[j]'(by have := (List.getElem?_eq_some_iff.1 ha).1; simp [zs]; omega)) :=
        List.getElem?_eq_getElem _
      obtain ⟨_, _, hzy, _⟩ := hz hzj
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      exact TShape.LE.trans hzy (hP1.getElem?' hzj hb)
    · rw [List.reverse_append, pushAll_concat]
      exact .cons hP3 (fun ha => InterpTyped.hsort (hA hP3) ha) htA' hty

/-- The hypotheses of `fits_ofSubst`: `σs` are terms in `Γ` typed along the closed telescope `Δ`,
whose types are types. -/
structure TeleSubst (env : VEnv) (Γ Δ σs : List VExpr) : Prop where
  len : Δ.length = σs.length
  tele : ∀ i (A : VExpr), Δ[i]? = some A → A.ClosedN i ∧
    ∃ u, SoundTy env (Δ.take i).reverse A (.sort u)
  typed : ∀ i (A x : VExpr), Δ[i]? = some A → σs[i]? = some x →
    SoundTy env Γ x (A.subst (VExpr.Subst.dflt.consList (σs.take i)))

/-- A valuation interpreting the substitution `σs` lies below one fitting `Δ`, at shapes
interpreting `σs`. -/
theorem TeleSubst.exists_fits (hM : ModelEnv env) (H : TeleSubst env Γ Δ σs)
    (W : Valuation.Fits env Γ₀ Γ ρ) {ρ' : Valuation}
    (hρ' : ∀ i, LE_Interp env ρ (ρ' i) (VExpr.Subst.dflt.consList σs i)) :
    ∃ P, List.Forall₂ (fun y x => LE_Interp env ρ y x) P σs ∧
      Valuation.Fits env [] Δ.reverse (pushAll .nil P) ∧
      ∀ i < σs.length, ρ' i ≤ pushAll .nil P i := by
  let ys := (List.range σs.length).map fun j => ρ' (σs.length - 1 - j)
  have hys : List.Forall₂ (fun y x => LE_Interp env ρ y x) ys σs := by
    refine List.forall₂_of_getElem? (by simp [ys]) fun j a b ha hb => ?_
    have hj' : j < σs.length := (List.getElem?_eq_some_iff.1 hb).1
    obtain rfl : a = ρ' (σs.length - 1 - j) := by simp [ys, hj'] at ha; exact ha.symm
    generalize j = j' at *
    have := hρ' (σs.length - 1 - j')
    rw [VExpr.Subst.consList_lt _ _ _ (by omega), List.getElem_reverse] at this
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    have e : σs.length - 1 - (σs.length - 1 - j') = j' := by omega
    simpa only [e] using this
  obtain ⟨P, hP1, hP2, hP3⟩ :=
    fits_ofSubst hM W σs.length Δ σs ys H.len rfl H.tele H.typed hys
  refine ⟨P, hP2, hP3, fun i hi => ?_⟩
  have hPl : P.length = σs.length := List.Forall₂.length_eq hP2
  rw [pushAll_apply, dif_pos (by omega), List.getElem_reverse]
  have hyi : ys[σs.length - 1 - i]? = some (ρ' i) := by
    simp [ys, show σs.length - 1 - i < σs.length by omega,
      show σs.length - 1 - (σs.length - 1 - i) = i by omega]
  exact hP1.getElem?' hyi (List.getElem?_eq_getElem _) |>.trans (by simp only [hPl]; exact .rfl)

theorem TeleSubst.interp (hM : ModelEnv env) (H : TeleSubst env Γ Δ σs)
    (W : Valuation.Fits env Γ₀ Γ ρ) (hcl : M.ClosedN σs.length)
    (h : LE_Interp env ρ m (M.subst (VExpr.Subst.dflt.consList σs))) :
    ∃ P, List.Forall₂ (fun y x => LE_Interp env ρ y x) P σs ∧
      Valuation.Fits env [] Δ.reverse (pushAll .nil P) ∧ LE_Interp env (pushAll .nil P) m M := by
  obtain ⟨ρ', h1, h2⟩ := (LE_Interp.subst hM).1 h
  obtain ⟨P, hP1, hP2, hP3⟩ := H.exists_fits hM W h2
  refine ⟨P, hP1, hP2, ?_⟩
  have := LE_Interp.closed hM.closed hcl
    (ρ' := fun v => if v < σs.length then ρ' v else Valuation.nil v) (fun i hi => by simp [hi]) h1
  refine this.mono_l fun v => ?_
  by_cases hv : v < σs.length
  · simp only [hv, if_true]; exact hP3 v hv
  · simp only [hv, if_false]; exact TShape.bot_le'

theorem TeleSubst.interp_subst (hM : ModelEnv env)
    (hP : List.Forall₂ (fun y x => LE_Interp env ρ y x) P σs)
    (h : LE_Interp env (pushAll .nil P) m M) :
    LE_Interp env ρ m (M.subst (VExpr.Subst.dflt.consList σs)) := by
  refine (LE_Interp.subst hM).2 ⟨_, h, fun i => ?_⟩
  have hl : P.length = σs.length := List.Forall₂.length_eq hP
  rw [pushAll_apply, VExpr.Subst.consList_apply]
  by_cases hi : i < σs.length
  · rw [dif_pos (by omega), dif_pos hi, List.getElem_reverse, List.getElem_reverse]
    exact hP.getElem?' (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) |>.mono
      (by simp only [hl]; exact .rfl)
  · rw [dif_neg (by omega)]; exact .bot

/-- Terms the model cannot tell apart over a closed telescope, instantiated by terms typed along
it. -/
theorem SoundEq.substTele (hM : ModelEnv env) (H : TeleSubst env Γ Δ σs)
    (hM' : M.ClosedN σs.length) (hN' : N.ClosedN σs.length) (h : SoundEq env Δ.reverse M N) :
    SoundEq env Γ (M.subst (VExpr.Subst.dflt.consList σs))
      (N.subst (VExpr.Subst.dflt.consList σs)) := by
  intro Γ₀ ρ W m
  suffices ∀ {M N}, M.ClosedN σs.length → SoundEq env Δ.reverse M N →
      LE_Interp env ρ m (M.subst (VExpr.Subst.dflt.consList σs)) →
      LE_Interp env ρ m (N.subst (VExpr.Subst.dflt.consList σs)) from
    ⟨this hM' h, this hN' h.symm⟩
  intro M N hcl h h1
  obtain ⟨P, hP1, hP2, hP3⟩ := H.interp hM W hcl h1
  exact TeleSubst.interp_subst hM hP1 ((h hP2).1 hP3)

/-- A typing over a closed telescope, instantiated by terms typed along it. -/
theorem SoundTy.substTele (hM : ModelEnv env) (H : TeleSubst env Γ Δ σs)
    (hM' : M.ClosedN σs.length) (h : SoundTy env Δ.reverse M T) :
    SoundTy env Γ (M.subst (VExpr.Subst.dflt.consList σs))
      (T.subst (VExpr.Subst.dflt.consList σs)) := by
  intro Γ₀ ρ W m h1
  obtain ⟨P, hP1, hP2, hP3⟩ := H.interp hM W hM' h1
  obtain ⟨m', a, a1, a2, a3, a4⟩ := h hP2 hP3
  exact ⟨m', a, a1, TeleSubst.interp_subst hM hP1 a2, TeleSubst.interp_subst hM hP1 a3, a4⟩

theorem TeleSubst.take (H : TeleSubst env Γ Δ σs) (j : Nat) :
    TeleSubst env Γ (Δ.take j) (σs.take j) where
  len := by simp [H.len]
  tele i A h := by
    have hi : i < j := by have := (List.getElem?_eq_some_iff.1 h).1; simp at this; omega
    rw [List.getElem?_take_of_lt hi] at h
    rw [List.take_take, Nat.min_eq_left (by omega)]; exact H.tele i A h
  typed i A x h1 h2 := by
    have hi : i < j := by have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
    rw [List.getElem?_take_of_lt hi] at h1 h2
    rw [List.take_take, Nat.min_eq_left (by omega)]; exact H.typed i A x h1 h2

/-! ### Application spines -/

variable {U : Nat}

theorem StrongSound.app_inv (H : StrongSound env U Γ (.app f a) T) :
    ∃ A B u, SoundTy env Γ A (.sort u) ∧ StrongSound env U Γ f (.forallE A B) ∧
      StrongSound env U Γ a A ∧ SoundEq env Γ (B.inst a) T := by
  obtain ⟨-, -, core, heq⟩ := H
  cases core with | app h1 h2 h3 => exact ⟨_, _, _, h1, h2, h3, heq⟩

theorem StrongSound.const_inv (H : StrongSound env U Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ ls.length = ci.uvars ∧ SoundEq env Γ (ci.type.instL ls) T := by
  obtain ⟨-, -, core, heq⟩ := H
  cases core with | const h1 h2 => exact ⟨_, h1, h2, heq⟩

theorem SoundEq.closed (hM : ModelEnv env) (hX : X.ClosedN) (hY : Y.ClosedN)
    (H : SoundEq env [] X Y) : SoundEq env Γ X Y := fun _ _ _ _ =>
  (closed_iff hM.closed hX).trans <| (H .nil).trans (closed_iff hM.closed hY)

theorem TeleSubst.nil : TeleSubst env Γ [] [] :=
  ⟨rfl, fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩

theorem TeleSubst.snoc (H : TeleSubst env Γ Δ σs) (hQ : Q.ClosedN Δ.length)
    (hQ' : SoundTy env Δ.reverse Q (.sort u)) (ha : SoundTy env Γ a (Q.subst (VExpr.Subst.dflt.consList σs))) :
    TeleSubst env Γ (Δ ++ [Q]) (σs ++ [a]) where
  len := by simp [H.len]
  tele i A h := by
    by_cases hi : i < Δ.length
    · rw [List.getElem?_append_left hi] at h
      rw [List.take_append_of_le_length (by omega)]; exact H.tele i A h
    · have hi' : i = Δ.length := by
        have := (List.getElem?_eq_some_iff.1 h).1; simp at this; omega
      subst hi'; simp at h; subst h
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      exact ⟨hQ, _, hQ'⟩
  typed i A x h1 h2 := by
    by_cases hi : i < Δ.length
    · rw [List.getElem?_append_left hi] at h1
      rw [List.getElem?_append_left (by rw [← H.len]; exact hi)] at h2
      rw [List.take_append_of_le_length (by rw [← H.len]; omega)]; exact H.typed i A x h1 h2
    · have hi' : i = Δ.length := by
        have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
      subst hi'; simp at h1; subst h1
      rw [H.len] at h2; simp at h2; subst h2
      rw [List.take_append_of_le_length (by rw [← H.len]; omega),
        List.take_of_length_le (by rw [← H.len]; omega)]
      exact ha

theorem MSpine.app_inv (H : MSpine env Γ (.app f a) T) :
    ∃ A B u, SoundTy env Γ A (.sort u) ∧ MSpine env Γ f (.forallE A B) ∧
      SoundTy env Γ a A ∧ SoundEq env Γ (B.inst a) T := by
  cases H with | app h1 h2 h3 h4 => exact ⟨_, _, _, h1, h2, h3, h4⟩

theorem MSpine.const_inv (H : MSpine env Γ (.const c ls) T) :
    ∃ ci, env.constants c = some ci ∧ ls.length = ci.uvars ∧ SoundEq env Γ (ci.type.instL ls) T := by
  cases H with | const h1 h2 h3 => exact ⟨_, h1, h2, h3⟩

theorem StrongSound.mspine' (H : StrongSound env U Γ ((VExpr.const c ls).appN args) T) :
    MSpine env Γ ((VExpr.const c ls).appN args) T := by
  rw [← spine_eq_appN] at H ⊢; exact H.mspine

/-- An application spine of a constant whose type the model cannot tell from a closed telescope
`Qs` with result `R`: its arguments are typed along the telescope, and its type is the rest of
the telescope at them. -/
theorem MSpine.spine (hM : ModelEnv env) {c : Name} {ls : List VLevel} {Qs : List VExpr}
    {R : VExpr} (hQ : ∀ i (A : VExpr), Qs[i]? = some A → A.ClosedN i ∧
      ∃ u, SoundTy env (Qs.take i).reverse A (.sort u))
    (hR : (VExpr.foralls Qs R).ClosedN)
    (hX : ∀ ci, env.constants c = some ci → ls.length = ci.uvars →
      SoundEq env Γ (ci.type.instL ls) (.foralls Qs R)) :
    ∀ (n : Nat) (args : List VExpr) {T}, args.length = n → n ≤ Qs.length →
    MSpine env Γ ((VExpr.const c ls).appN args) T →
    TeleSubst env Γ (Qs.take n) args ∧
    SoundEq env Γ T ((VExpr.foralls (Qs.drop n) R).subst (VExpr.Subst.dflt.consList args))
  | 0, args, T, h0, _, H => by
    obtain rfl := List.eq_nil_of_length_eq_zero h0
    obtain ⟨ci, h1, h2, h3⟩ := H.const_inv
    refine ⟨by simpa using TeleSubst.nil, ?_⟩
    simp only [List.drop_zero, VExpr.Subst.consList_nil]
    rw [VExpr.ClosedN.subst_eq hR VExpr.Subst.Fixes.zero]
    exact h3.symm.trans (hX ci h1 h2)
  | n+1, args, T, h0, hl, H => by
    obtain ⟨args, a, rfl⟩ := List.eq_nil_or_concat args |>.resolve_left (by rintro rfl; cases h0)
    simp only [List.concat_eq_append, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at h0 H ⊢
    rw [VExpr.appN_append] at H
    obtain ⟨A, B, u, hA, hf, ha, hT⟩ := H.app_inv
    obtain ⟨hS, hE⟩ := MSpine.spine hM hQ hR hX n args h0 (by omega) hf
    have hQn : Qs[n]? = some Qs[n] := List.getElem?_eq_getElem (by omega)
    obtain ⟨hcl, u', hQ'⟩ := hQ n _ hQn
    rw [List.drop_eq_getElem_cons (by omega)] at hE
    have hQs : SoundTy env Γ (Qs[n].subst (VExpr.Subst.dflt.consList args)) (.sort u') := by
      exact SoundTy.substTele hM hS (by rwa [h0]) hQ'
    obtain ⟨hAQ, hB⟩ := SoundEq.forallE_inv hM hE hA hQs
    refine ⟨?_, ?_⟩
    · rw [List.take_succ_eq_append_getElem (by omega)]
      refine hS.snoc (by rw [List.length_take, Nat.min_eq_left (by omega)]; exact hcl) hQ' ?_
      exact ha.defeq_r hAQ
    · refine hT.symm.trans ?_
      have := SoundEq.inst hM ha hA hB
      rwa [VExpr.inst_lift_cons, ← VExpr.Subst.consList_concat] at this

/-- `MSpine.spine` for a `StrongSound` spine. -/
theorem StrongSound.spine (hM : ModelEnv env) {c : Name} {ls : List VLevel} {Qs : List VExpr}
    {R : VExpr} (hQ : ∀ i (A : VExpr), Qs[i]? = some A → A.ClosedN i ∧
      ∃ u, SoundTy env (Qs.take i).reverse A (.sort u))
    (hR : (VExpr.foralls Qs R).ClosedN)
    (hX : ∀ ci, env.constants c = some ci → ls.length = ci.uvars →
      SoundEq env Γ (ci.type.instL ls) (.foralls Qs R))
    (n : Nat) (args : List VExpr) {T} (h0 : args.length = n) (hl : n ≤ Qs.length)
    (H : StrongSound env U Γ ((VExpr.const c ls).appN args) T) :
    TeleSubst env Γ (Qs.take n) args ∧
    SoundEq env Γ T ((VExpr.foralls (Qs.drop n) R).subst (VExpr.Subst.dflt.consList args)) :=
  MSpine.spine hM hQ hR hX n args h0 hl H.mspine'

/-- Conversely, arguments typed along a constant's telescope make an `MSpine`. -/
theorem MSpine.ofTele (hM : ModelEnv env) {c : Name} {ls : List VLevel} {Qs : List VExpr}
    {R : VExpr} {ci : VConstant} (hc : env.constants c = some ci) (hls : ls.length = ci.uvars)
    (hQ : ∀ i (A : VExpr), Qs[i]? = some A → A.ClosedN i ∧
      ∃ u, SoundTy env (Qs.take i).reverse A (.sort u))
    (hR : (VExpr.foralls Qs R).ClosedN)
    (hX : SoundEq env Γ (ci.type.instL ls) (.foralls Qs R)) :
    ∀ (n : Nat) (args : List VExpr), args.length = n → n ≤ Qs.length →
    TeleSubst env Γ (Qs.take n) args →
    MSpine env Γ ((VExpr.const c ls).appN args)
      ((VExpr.foralls (Qs.drop n) R).subst (VExpr.Subst.dflt.consList args))
  | 0, args, h0, _, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero h0
    simp only [List.drop_zero, VExpr.Subst.consList_nil, VExpr.appN]
    rw [VExpr.ClosedN.subst_eq hR VExpr.Subst.Fixes.zero]
    exact .const hc hls hX
  | n+1, args, h0, hl, H => by
    obtain ⟨args, a, rfl⟩ := List.eq_nil_or_concat args |>.resolve_left (by rintro rfl; cases h0)
    simp only [List.concat_eq_append, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at h0 H ⊢
    rw [List.take_succ_eq_append_getElem (by omega)] at H
    have hS : TeleSubst env Γ (Qs.take n) args := by
      have := H.take n
      rwa [List.take_left' (by simp; omega), List.take_left' (by omega)] at this
    have hf := MSpine.ofTele hM hc hls hQ hR hX n args h0 (by omega) hS
    rw [List.drop_eq_getElem_cons (by omega)] at hf
    have hQn : Qs[n]? = some Qs[n] := List.getElem?_eq_getElem (by omega)
    obtain ⟨hcl, u', hQ'⟩ := hQ n _ hQn
    have hQs : SoundTy env Γ (Qs[n].subst (VExpr.Subst.dflt.consList args)) (.sort u') :=
      SoundTy.substTele hM hS (by rwa [h0]) hQ'
    have ha : SoundTy env Γ a (Qs[n].subst (VExpr.Subst.dflt.consList args)) := by
      have := H.typed n Qs[n] a
        (by rw [List.getElem?_append_right (by simp; omega)]; simp [Nat.min_eq_left (show n ≤ Qs.length by omega)])
        (by rw [List.getElem?_append_right (by omega)]; simp [h0])
      rwa [List.take_left' h0] at this
    rw [VExpr.appN_append]
    refine .app hQs hf ha ?_
    rw [VExpr.inst_lift_cons, ← VExpr.Subst.consList_concat]; exact .rfl

/-! ### Telescopes of pi type shapes -/

theorem WShape.piApp_le_bot {f : WShape (n+1)} {x : WShape n} (hf : f.T ≤ TShape.bot) :
    (f.piApp x).T ≤ TShape.bot := by
  have hf : f ≤ .bot := WShape.LE.T_iff.1 (hf.trans TShape.bot_eqv.2)
  rw [WShape.le_bot.1 hf]
  show (WShape.piCod (.bot : WShape (n+1)) |>.app x).T ≤ _
  simp [WShape.piCod]; exact TShape.bot_eqv.1

theorem PiAppS.le_bot (H : PiAppS h as y) (hh : h ≤ TShape.bot) : y ≤ TShape.bot := by
  induction H with
  | nil h1 => exact h1.trans hh
  | cons h1 _ _ ih => exact ih (WShape.piApp_le_bot (h1.trans hh))

theorem WShape.piApp_of_not_forallE {f : WShape (n+1)} (hf : ∀ b g, f ≠ .forallE b g)
    (x : WShape n) : f.piApp x = .bot := by
  cases f using WShape.casesOn' with
  | forallE b g => exact (hf b g rfl).elim
  | _ => exact (show (WShape.bot : WShape (n+1)).app x = _ from WShape.bot_app)

/-- A pi type telescope's shape at shapes of its first binders: the rest of the telescope, at the
valuation with them pushed. -/
theorem LE_Interp.piAppS_foralls (hM : ModelEnv env) {Ds : List VExpr} {B : VExpr} :
    ∀ (Ps : List VExpr) {ρ h xs y}, LE_Interp env ρ h (.foralls (Ps ++ Ds) B) →
      PiAppS h xs y → xs.length = Ps.length → LE_Interp env (pushAll ρ xs) y (.foralls Ds B)
  | [], ρ, h, xs, y, H, hP, hl => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    let .nil h1 := hP; exact H.mono h1
  | P :: Ps, ρ, h, xs, y, H, hP, hl => by
    let .cons (f := f) (x := x) h1 h2 h3 := hP
    have H' := H.mono h1
    by_cases hf : ∃ b g, f = .forallE b g
    · obtain ⟨b, g, rfl⟩ := hf
      have := (H'.forallE_inv' hM).2 x
      rw [show (WShape.forallE b g).piApp x = g.app x by simp [WShape.piApp]] at h3
      have := piAppS_foralls hM Ps (this.mono_l (Valuation.LE.push.2 ⟨.rfl, h2⟩)) h3
        (by simpa using hl)
      exact this
    · rw [WShape.piApp_of_not_forallE (fun b g e => hf ⟨b, g, e⟩)] at h3
      exact .mono (h3.le_bot TShape.bot_eqv.1) .bot

/-- Fields fitting a pi type telescope's shape: each is typed at an interpretation of its binder's
type, at the valuation with the fields before it pushed. -/
theorem LE_Interp.fitsPi_foralls (hM : ModelEnv env) {c : WShape (n+1)} {fs : List (WShape (n+1))}
    (H : WShape.FitsPi c fs) : ∀ {Ds : List VExpr} {B : VExpr} {ρ},
    LE_Interp env ρ c.T (.foralls Ds B) → ∀ k (x : WShape (n+1)) (D : VExpr),
    fs[k]? = some x → Ds[k]? = some D → ∃ b : WShape (n+1), x.HasType b ∧
      LE_Interp env (pushAll ρ ((fs.take k).map (·.T))) b.T D := by
  induction H with
  | nil => intro _ _ _ _ k _ _ h; cases h
  | @cons b f x xs hx _ ih =>
    intro Ds B ρ H k y D hy hD
    obtain _ | ⟨D', Ds⟩ := Ds; · cases k <;> cases hD
    have H' : LE_Interp env ρ (WShape.T (n := n+1) (.forallE b f))
      (.forallE D' (.foralls Ds B)) := H
    cases k with
    | zero =>
      cases hy; cases hD
      refine ⟨b.lift (n+1), hx, ?_⟩
      exact ((H'.forallE_inv' hM).1.lift (m := b.T) (Nat.le_succ n))
    | succ k =>
      have := H'.lift (m := WShape.T (n := n+1) (.forallE b f)) (Nat.le_succ (n+1))
      simp only [WShape.T] at this
      rw [WShape.lift_forallE (Nat.le_succ n)] at this
      have h2 := (this.forallE_inv' hM).2 x
      exact ih h2 k y D hy hD

/-! ### Inductive types' shapes -/

/-- An inductive type applied to all its parameters and indices is interpreted by its `indTy`
shape, whose constructors' telescopes are their types' interpretations at the parameters. -/
theorem LE_Interp.Const.indTy_inv (hR : ConstRoles env) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    {rargs : List (WShape n)} (hl : rargs.length = d.params.length + T.indices.length)
    (H : Const env s ls R rargs y) : y ≤ TShape.bot ∨ ∃ ctys : List (WShape n),
      ctys.length = T.ctors.length ∧
      (∀ (i : Nat) (c' : VConstructor) (cty : WShape n), T.ctors[i]? = some c' →
        ctys[i]? = some cty → ∃ h, R h (c'.type.instL ls) ∧
          PiAppS h ((rargs.reverse.take d.params.length).map (·.T)) cty.T) ∧
      y ≤ (WShape.indTy (n := n) (d.rel ls) ⟨s, rargs.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩
        (rargs.reverse ++ ctys)).T := by
  have A : ConstArity env s (.indTy d t) rargs.length := hl ▸ .indTy hs hT
  cases H with
  | bot => exact .inl TShape.bot_eqv.1
  | lam he hle => exact .inl (Const.lam_le_bot hR he hle A)
  | delta h1 h2 => cases hR (ConstArity.delta h1 h2) A
  | indTy h1 h2 h3 h4 h5 h6 =>
    rw [hs] at h1; cases h1; rw [hT] at h2; cases h2
    exact .inr ⟨_, h4, h5, h6⟩
  | ctor h1 h2 h3 h4 => cases hR (ConstArity.ctor h1 h2 h3 h4) A
  | iota h1 h2 _ h4 => cases hR (ConstArity.recursor h1 h2 h4) A
  | kIota h1 h2 _ h4 => cases hR (ConstArity.recursor h1 h2 h4) A
  | quotTy h1 h2 => cases hR (ConstArity.quotTy h1 h2) A
  | quotMk h1 h2 => cases hR (ConstArity.quotMk h1 h2) A
  | quot h1 h2 => cases hR (ConstArity.quotLift h1 h2) A
  | quotK h1 h2 => cases hR (ConstArity.quotLift h1 h2) A

end LogRel
end Lean4Lean

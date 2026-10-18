import Lean4Lean.Verify.Environment.ElimNestedRun
import Lean4Lean.Verify.Environment.Restore
import Lean4Lean.Verify.Typing.Drop

/-!
# Restoring commutes with dropping unused binders

`inferProj` walks a constructor's type with the binders the rest does not mention dropped
(`Expr.dropAfter`). Restoring a nested block's translated constructor type replaces each
auxiliary application, whose arguments are the parameters (`AuxPlaced`), by the occurrence it
stands for, which mentions only parameters. So restoring keeps which field binders are mentioned,
and commutes with dropping them.
-/

namespace Lean4Lean.ElimNestedInductive
open Lean

theorem hasLooseBVar'_liftLooseBVars' : ∀ (e : Expr) {t k j : Nat}, j < k →
    (e.liftLooseBVars' t k).hasLooseBVar' (t + j) = false
  | .bvar i, t, k, j, h => by
    simp only [Expr.liftLooseBVars', Expr.hasLooseBVar', decide_eq_false_iff_not]
    split <;> omega
  | .app f a, t, k, j, h => by
    simp [Expr.liftLooseBVars', Expr.hasLooseBVar', hasLooseBVar'_liftLooseBVars' f h,
      hasLooseBVar'_liftLooseBVars' a h]
  | .lam _ ty b _, t, k, j, h | .forallE _ ty b _, t, k, j, h => by
    have := hasLooseBVar'_liftLooseBVars' b (t := t + 1) h
    rw [show t + 1 + j = t + j + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.hasLooseBVar', hasLooseBVar'_liftLooseBVars' ty h, this]
  | .letE _ ty v b _, t, k, j, h => by
    have := hasLooseBVar'_liftLooseBVars' b (t := t + 1) h
    rw [show t + 1 + j = t + j + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.hasLooseBVar', hasLooseBVar'_liftLooseBVars' ty h,
      hasLooseBVar'_liftLooseBVars' v h, this]
  | .mdata _ e, t, k, j, h | .proj _ _ e, t, k, j, h => by
    simp [Expr.liftLooseBVars', Expr.hasLooseBVar', hasLooseBVar'_liftLooseBVars' e h]
  | .const .., _, _, _, _ | .sort _, _, _, _, _ | .fvar _, _, _, _, _ | .mvar _, _, _, _, _
  | .lit _, _, _, _, _ => rfl

theorem lowerLooseBVars'_liftLooseBVars' : ∀ (e : Expr) {t k j : Nat}, j < k →
    (e.liftLooseBVars' t k).lowerLooseBVars' (t + j + 1) 1 = e.liftLooseBVars' t (k - 1)
  | .bvar i, t, k, j, h => by
    simp only [Expr.liftLooseBVars', Expr.lowerLooseBVars', show ¬t + j + 1 < 1 by omega,
      if_false, Expr.bvar.injEq]
    split <;> split <;> omega
  | .app f a, t, k, j, h => by
    simp [Expr.liftLooseBVars', Expr.lowerLooseBVars', lowerLooseBVars'_liftLooseBVars' f h,
      lowerLooseBVars'_liftLooseBVars' a h]
  | .lam _ ty b _, t, k, j, h | .forallE _ ty b _, t, k, j, h => by
    have := lowerLooseBVars'_liftLooseBVars' b (t := t + 1) h
    rw [show t + 1 + j + 1 = t + j + 1 + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.lowerLooseBVars', lowerLooseBVars'_liftLooseBVars' ty h, this]
  | .letE _ ty v b _, t, k, j, h => by
    have := lowerLooseBVars'_liftLooseBVars' b (t := t + 1) h
    rw [show t + 1 + j + 1 = t + j + 1 + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.lowerLooseBVars', lowerLooseBVars'_liftLooseBVars' ty h,
      lowerLooseBVars'_liftLooseBVars' v h, this]
  | .mdata _ e, t, k, j, h | .proj _ _ e, t, k, j, h => by
    simp [Expr.liftLooseBVars', Expr.lowerLooseBVars', lowerLooseBVars'_liftLooseBVars' e h]
  | .const .., _, _, _, _ | .sort _, _, _, _, _ | .fvar _, _, _, _, _ | .mvar _, _, _, _, _
  | .lit _, _, _, _, _ => by simp [Expr.liftLooseBVars', Expr.lowerLooseBVars']

theorem spineNM_eq : ∀ {t : Expr} {c ls xs}, spineNM t = some (c, ls, xs) →
    t = Expr.mkAppList (.const c ls) xs
  | .const .., _, _, _, h => by cases h; rfl
  | .app f a, c, ls, xs, h => by
    simp only [spineNM, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', xs'⟩, h, e⟩ := h
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
    rw [spineNM_eq h, Expr.mkAppList_append]; rfl
  | .bvar .., _, _, _, h | .fvar .., _, _, _, h | .mvar .., _, _, _, h
  | .sort .., _, _, _, h | .lam .., _, _, _, h | .forallE .., _, _, _, h
  | .letE .., _, _, _, h | .lit .., _, _, _, h | .mdata .., _, _, _, h
  | .proj .., _, _, _, h => by simp [spineNM] at h

theorem hasLooseBVar'_mkAppList_bvs {c : Name} {ls : List Level} {n k j : Nat} (h : j < k) :
    (Expr.mkAppList (.const c ls) (bvs n k)).hasLooseBVar' j = false := by
  suffices ∀ (xs : List Expr) (f : Expr), f.hasLooseBVar' j = false →
      (∀ x ∈ xs, x.hasLooseBVar' j = false) → (Expr.mkAppList f xs).hasLooseBVar' j = false from
    this _ _ rfl fun x hx => by
      induction n with
      | zero => simp [bvs] at hx
      | succ n ih =>
        simp only [bvs, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [Expr.hasLooseBVar']; omega
        · exact ih hx
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hx
    exact ih _ (by simp [Expr.hasLooseBVar', hf, hx x (.head _)]) fun y hy => hx y (.tail _ hy)

theorem lowerLooseBVars'_app {f a : Expr} {s d : Nat} (h : ¬s < d) :
    (Expr.app f a).lowerLooseBVars' s d = .app (f.lowerLooseBVars' s d) (a.lowerLooseBVars' s d) := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]

theorem lowerLooseBVars'_mkAppList {s d : Nat} (h : ¬s < d) : ∀ {f : Expr} {xs : List Expr},
    (Expr.mkAppList f xs).lowerLooseBVars' s d =
      Expr.mkAppList (f.lowerLooseBVars' s d) (xs.map (·.lowerLooseBVars' s d))
  | _, [] => rfl
  | f, x :: xs => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [lowerLooseBVars'_mkAppList h (f := .app f x), lowerLooseBVars'_app h]

theorem bvs_lower {n k j : Nat} (h : j < k) :
    (bvs n k).map (·.lowerLooseBVars' (j + 1) 1) = bvs n (k - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bvs, List.map_cons, ih, List.cons.injEq, and_true]
    simp only [Expr.lowerLooseBVars', show ¬j + 1 < 1 by omega, if_false, Expr.bvar.injEq]
    split <;> omega

theorem const_lowerLooseBVars' {c : Name} {ls : List Level} {s d : Nat} :
    (Expr.const c ls).lowerLooseBVars' s d = .const c ls := by
  unfold Expr.lowerLooseBVars'; split <;> rfl

theorem lower_lam {nm t b bi} {s d : Nat} (h : ¬s < d) :
    (Expr.lam nm t b bi).lowerLooseBVars' s d =
      .lam nm (t.lowerLooseBVars' s d) (b.lowerLooseBVars' (s + 1) d) bi := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]
theorem lower_forallE {nm t b bi} {s d : Nat} (h : ¬s < d) :
    (Expr.forallE nm t b bi).lowerLooseBVars' s d =
      .forallE nm (t.lowerLooseBVars' s d) (b.lowerLooseBVars' (s + 1) d) bi := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]
theorem lower_letE {nm t v b nd} {s d : Nat} (h : ¬s < d) :
    (Expr.letE nm t v b nd).lowerLooseBVars' s d =
      .letE nm (t.lowerLooseBVars' s d) (v.lowerLooseBVars' s d) (b.lowerLooseBVars' (s + 1) d)
        nd := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]
theorem lower_mdata {m e} {s d : Nat} (h : ¬s < d) :
    (Expr.mdata m e).lowerLooseBVars' s d = .mdata m (e.lowerLooseBVars' s d) := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]
theorem lower_proj {x i e} {s d : Nat} (h : ¬s < d) :
    (Expr.proj x i e).lowerLooseBVars' s d = .proj x i (e.lowerLooseBVars' s d) := by
  conv => lhs; unfold Expr.lowerLooseBVars'
  simp [h]

theorem spineNM_lower {s d : Nat} (h : ¬s < d) : ∀ {e : Expr},
    spineNM (e.lowerLooseBVars' s d) =
      (spineNM e).map fun x => (x.1, x.2.1, x.2.2.map (·.lowerLooseBVars' s d))
  | .const .. => by rw [const_lowerLooseBVars']; rfl
  | .app f a => by
    rw [lowerLooseBVars'_app h]
    simp only [spineNM, spineNM_lower h (e := f), Option.map_map]
    congr 1; funext x; simp
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => by
    unfold Expr.lowerLooseBVars'; split <;> rfl
  | .lam .. => by rw [lower_lam h]; rfl
  | .forallE .. => by rw [lower_forallE h]; rfl
  | .letE .. => by rw [lower_letE h]; rfl
  | .mdata .. => by rw [lower_mdata h]; rfl
  | .proj .. => by rw [lower_proj h]; rfl

theorem anySub_constP_mkAppList_bvs {f : Name → Bool} {c : Name} {ls : List Level}
    (h : f c = false) : ∀ {n K : Nat},
    (Expr.mkAppList (.const c ls) (bvs n K)).anySub (constP f) = false := by
  intro n K
  refine anySub_constP_appList.2 ⟨by simpa [Expr.anySub, constP] using h, fun x hx => ?_⟩
  induction n with
  | zero => simp [bvs] at hx
  | succ n ih =>
    simp only [bvs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact ih hx

theorem lower_bvar {i s d : Nat} (h : ¬s < d) :
    (Expr.bvar i).lowerLooseBVars' s d = .bvar (if i < s then i else i - d) := by
  unfold Expr.lowerLooseBVars'; simp [h]

/-- The node replacement restoring makes, as properties: at an auxiliary application to the
parameters `bvs n K` it gives a term `N` over the parameters, lifted past the `K` binders crossed;
elsewhere it replaces nothing. -/
structure PlacedFn (F : Expr → Option Expr) (isAux isRec : Name → Bool) (lvls : List Level)
    (n : Nat) : Prop where
  aux : ∀ c, isAux c → ∃ N : Expr, N.looseBVarRange' ≤ n ∧
    ((∀ nm d b bi, N ≠ .forallE nm d b bi) ∧ (∀ i, N ≠ .bvar i) ∧ (∀ x, N ≠ .fvar x)) ∧
    ∀ K, F (Expr.mkAppList (.const c lvls) (bvs n K)) = some (N.liftLooseBVars' 0 K)
  spine : ∀ t c ls xs, spineNM t = some (c, ls, xs) → ¬(isAux c = true ∧ xs.length = n) →
    isRec c = false → F t = none
  noSpine : ∀ t, spineNM t = none → F t = none

section
variable {F : Expr → Option Expr} {isAux isRec : Name → Bool} {lvls : List Level} {n : Nat}
  (hF : PlacedFn F isAux isRec lvls n)
include hF

theorem PlacedFn.app_none {f a : Expr}
    (hr : (Expr.app f a).anySub (constP isRec) = false)
    (hs : ¬∃ c ls xs, spineNM (.app f a) = some (c, ls, xs) ∧ isAux c ∧ xs.length = n) :
    F (.app f a) = none := by
  cases h : spineNM (.app f a) with
  | none => exact hF.noSpine _ h
  | some x =>
    obtain ⟨c, ls, xs⟩ := x
    exact hF.spine _ c ls xs h (fun h' => hs ⟨c, ls, xs, h, h'⟩) (spineNM_anySub h hr)

/-- Restoring keeps whether a field variable, below the parameters, is mentioned. -/
theorem PlacedFn.hasLooseBVar' : ∀ {e : Expr} {K j : Nat}, AuxPlaced isAux lvls n K e → j < K →
    e.anySub (constP isRec) = false →
    (e.replaceNoCache F).hasLooseBVar' j = e.hasLooseBVar' j := by
  intro e
  induction e with
  | const c ls =>
    intro K j hA hj hr
    by_cases hc : isAux c
    · obtain ⟨rfl, rfl⟩ := hA hc
      obtain ⟨N, hN, -, hFN⟩ := hF.aux c hc
      have := hFN K
      simp only [bvs, Expr.mkAppList] at this
      rw [Expr.replaceNoCache.eq_def, this]
      have h1 := hasLooseBVar'_liftLooseBVars' N (t := 0) (k := K) hj
      simp only [Nat.zero_add] at h1
      rw [h1]; rfl
    · rw [Expr.replaceNoCache.eq_def,
        hF.spine _ c ls [] rfl (by simp [hc]) (by simpa [Expr.anySub, constP] using hr)]
  | app f a ih1 ih2 =>
    intro K j hA hj hr
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      by_cases hc : isAux c = true ∧ xs.length = n
      · rw [if_pos hc] at hA
        obtain ⟨rfl, rfl⟩ := hA
        obtain ⟨N, hN, -, hFN⟩ := hF.aux c hc.1
        have ht := spineNM_eq hs
        rw [ht, Expr.replaceNoCache.eq_def, hFN K, hasLooseBVar'_mkAppList_bvs hj]
        have h1 := hasLooseBVar'_liftLooseBVars' N (t := 0) (k := K) hj
        simpa using h1
      · rw [if_neg hc] at hA
        rw [Expr.replaceNoCache_app (hF.spine _ c ls xs hs hc (spineNM_anySub hs hr))]
        have hr' := anySub_constP_app.1 hr
        simp [Expr.hasLooseBVar', ih1 hA.1 hj hr'.1, ih2 hA.2 hj hr'.2]
    · rename_i hs
      rw [Expr.replaceNoCache_app (hF.noSpine _ hs)]
      have hr' := anySub_constP_app.1 hr
      simp [Expr.hasLooseBVar', ih1 hA.1 hj hr'.1, ih2 hA.2 hj hr'.2]
  | lam _ t b _ ih1 ih2 =>
    intro K j hA hj hr
    rw [Expr.replaceNoCache_lam (hF.noSpine _ rfl)]
    have hr' := anySub_constP_lam.1 hr
    simp [Expr.hasLooseBVar', ih1 hA.1 hj hr'.1, ih2 (j := j + 1) hA.2 (by omega) hr'.2]
  | forallE _ t b _ ih1 ih2 =>
    intro K j hA hj hr
    rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl)]
    have hr' := anySub_constP_forallE.1 hr
    simp [Expr.hasLooseBVar', ih1 hA.1 hj hr'.1, ih2 (j := j + 1) hA.2 (by omega) hr'.2]
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro K j hA hj hr
    rw [Expr.replaceNoCache_letE (hF.noSpine _ rfl)]
    have hr' := anySub_constP_letE.1 hr
    simp [Expr.hasLooseBVar', ih1 hA.1 hj hr'.1, ih2 hA.2.1 hj hr'.2.1,
      ih3 (j := j + 1) hA.2.2 (by omega) hr'.2.2]
  | mdata _ e ih =>
    intro K j hA hj hr
    rw [Expr.replaceNoCache_mdata (hF.noSpine _ rfl)]
    simp [Expr.hasLooseBVar', ih hA hj (anySub_constP_mdata.1 hr)]
  | proj _ _ e ih =>
    intro K j hA hj hr
    rw [Expr.replaceNoCache_proj (hF.noSpine _ rfl)]
    simp [Expr.hasLooseBVar', ih hA hj (anySub_constP_proj.1 hr)]
  | bvar | fvar | mvar | sort | lit =>
    intros; rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]

/-- Restoring commutes with dropping a field variable a term does not mention. -/
theorem PlacedFn.lower : ∀ {e : Expr} {K j : Nat}, AuxPlaced isAux lvls n K e → j < K →
    e.anySub (constP isRec) = false → e.hasLooseBVar' j = false →
    AuxPlaced isAux lvls n (K - 1) (e.lowerLooseBVars' (j + 1) 1) ∧
    (e.lowerLooseBVars' (j + 1) 1).anySub (constP isRec) = false ∧
    (e.lowerLooseBVars' (j + 1) 1).replaceNoCache F =
      (e.replaceNoCache F).lowerLooseBVars' (j + 1) 1 := by
  have h0 {e : Expr} (he : spineNM e = none) (hleaf : e.isBVar ∨ e.isFVar ∨ e.isMVar ∨ e.isSort ∨ e.isLit) :
      e.replaceNoCache F = e := by
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ he]
    cases e <;> simp_all [Expr.isBVar, Expr.isFVar, Expr.isMVar, Expr.isSort, Expr.isLit]
  intro e
  induction e with
  | const c ls =>
    intro K j hA hj hr _
    rw [const_lowerLooseBVars']
    refine ⟨hA, hr, ?_⟩
    by_cases hc : isAux c
    · obtain ⟨rfl, rfl⟩ := hA hc
      obtain ⟨N, hN, -, hFN⟩ := hF.aux c hc
      have e1 := hFN K; have e2 := hFN (K - 1)
      simp only [bvs, Expr.mkAppList] at e1 e2
      have r1 : (Expr.const c ls).replaceNoCache F = N.liftLooseBVars' 0 K := by
        rw [Expr.replaceNoCache.eq_def, e1]
      have r2 : (Expr.const c ls).replaceNoCache F = N.liftLooseBVars' 0 (K - 1) := by
        rw [Expr.replaceNoCache.eq_def, e2]
      have := lowerLooseBVars'_liftLooseBVars' N (t := 0) (k := K) hj
      simp only [Nat.zero_add] at this
      calc (Expr.const c ls).replaceNoCache F = N.liftLooseBVars' 0 (K - 1) := r2
        _ = (N.liftLooseBVars' 0 K).lowerLooseBVars' (j + 1) 1 := this.symm
        _ = _ := by rw [r1]
    · have r : (Expr.const c ls).replaceNoCache F = .const c ls := by
        rw [Expr.replaceNoCache.eq_def,
          hF.spine _ c ls [] rfl (by simp [hc]) (by simpa [Expr.anySub, constP] using hr)]
      rw [r, const_lowerLooseBVars']
  | app f a ih1 ih2 =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    have hl' : f.hasLooseBVar' j = false ∧ a.hasLooseBVar' j = false := by
      simpa [Expr.hasLooseBVar'] using hl
    have hr' := anySub_constP_app.1 hr
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      by_cases hc : isAux c = true ∧ xs.length = n
      · rw [if_pos hc] at hA
        obtain ⟨rfl, rfl⟩ := hA
        obtain ⟨N, hN, -, hFN⟩ := hF.aux c hc.1
        have ht := spineNM_eq hs
        have hrc := spineNM_anySub hs hr
        have hlow : (Expr.app f a).lowerLooseBVars' (j + 1) 1 =
            Expr.mkAppList (.const c ls) (bvs n (K - 1)) := by
          rw [ht, lowerLooseBVars'_mkAppList h1, const_lowerLooseBVars', bvs_lower hj]
        rw [hlow]
        have hAP := auxPlaced_node (lvls := ls) (n := n) (k := K - 1) hc.1 0 [] rfl (by simp)
        rw [List.append_nil] at hAP
        refine ⟨hAP, anySub_constP_mkAppList_bvs hrc, ?_⟩
        have r1 : (Expr.app f a).replaceNoCache F = N.liftLooseBVars' 0 K := by
          rw [ht, Expr.replaceNoCache.eq_def, hFN K]
        have r2 : (Expr.mkAppList (.const c ls) (bvs n (K - 1))).replaceNoCache F =
            N.liftLooseBVars' 0 (K - 1) := by
          rw [Expr.replaceNoCache.eq_def, hFN (K - 1)]
        have := lowerLooseBVars'_liftLooseBVars' N (t := 0) (k := K) hj
        simp only [Nat.zero_add] at this
        rw [r2, r1, this]
      · rw [if_neg hc] at hA
        obtain ⟨a1, a2, a3⟩ := ih1 hA.1 hj hr'.1 hl'.1
        obtain ⟨b1, b2, b3⟩ := ih2 hA.2 hj hr'.2 hl'.2
        have hs' : spineNM (.app (f.lowerLooseBVars' (j + 1) 1) (a.lowerLooseBVars' (j + 1) 1)) =
            some (c, ls, xs.map (·.lowerLooseBVars' (j + 1) 1)) := by
          rw [← lowerLooseBVars'_app h1, spineNM_lower h1, hs]; rfl
        have hc' : ¬(isAux c = true ∧ (xs.map (·.lowerLooseBVars' (j + 1) 1)).length = n) := by
          simpa using hc
        rw [lowerLooseBVars'_app h1]
        refine ⟨?_, anySub_constP_app.2 ⟨a2, b2⟩, ?_⟩
        · unfold AuxPlaced; rw [hs']; dsimp only; rw [if_neg hc']; exact ⟨a1, b1⟩
        · rw [Expr.replaceNoCache_app (hF.spine _ c ls _ hs' hc' (spineNM_anySub hs hr)),
            Expr.replaceNoCache_app (hF.spine _ c ls xs hs hc (spineNM_anySub hs hr)),
            lowerLooseBVars'_app h1, a3, b3]
    · rename_i hs
      obtain ⟨a1, a2, a3⟩ := ih1 hA.1 hj hr'.1 hl'.1
      obtain ⟨b1, b2, b3⟩ := ih2 hA.2 hj hr'.2 hl'.2
      have hs' : spineNM (.app (f.lowerLooseBVars' (j + 1) 1) (a.lowerLooseBVars' (j + 1) 1)) =
          none := by
        rw [← lowerLooseBVars'_app h1, spineNM_lower h1, hs]; rfl
      rw [lowerLooseBVars'_app h1]
      refine ⟨?_, anySub_constP_app.2 ⟨a2, b2⟩, ?_⟩
      · unfold AuxPlaced; rw [hs']; exact ⟨a1, b1⟩
      · rw [Expr.replaceNoCache_app (hF.noSpine _ hs'), Expr.replaceNoCache_app (hF.noSpine _ hs),
          lowerLooseBVars'_app h1, a3, b3]
  | lam nm t b bi ih1 ih2 =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    have hl' : t.hasLooseBVar' j = false ∧ b.hasLooseBVar' (j + 1) = false := by
      simpa [Expr.hasLooseBVar'] using hl
    have hr' := anySub_constP_lam.1 hr
    obtain ⟨a1, a2, a3⟩ := ih1 hA.1 hj hr'.1 hl'.1
    obtain ⟨b1, b2, b3⟩ := ih2 (j := j + 1) hA.2 (by omega) hr'.2 hl'.2
    rw [show K + 1 - 1 = K - 1 + 1 by omega] at b1
    rw [lower_lam h1, Expr.replaceNoCache_lam (hF.noSpine _ rfl),
      Expr.replaceNoCache_lam (hF.noSpine _ rfl), lower_lam h1, a3, b3]
    exact ⟨⟨a1, b1⟩, anySub_constP_lam.2 ⟨a2, b2⟩, rfl⟩
  | forallE nm t b bi ih1 ih2 =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    have hl' : t.hasLooseBVar' j = false ∧ b.hasLooseBVar' (j + 1) = false := by
      simpa [Expr.hasLooseBVar'] using hl
    have hr' := anySub_constP_forallE.1 hr
    obtain ⟨a1, a2, a3⟩ := ih1 hA.1 hj hr'.1 hl'.1
    obtain ⟨b1, b2, b3⟩ := ih2 (j := j + 1) hA.2 (by omega) hr'.2 hl'.2
    rw [show K + 1 - 1 = K - 1 + 1 by omega] at b1
    rw [lower_forallE h1, Expr.replaceNoCache_forallE (hF.noSpine _ rfl),
      Expr.replaceNoCache_forallE (hF.noSpine _ rfl), lower_forallE h1, a3, b3]
    exact ⟨⟨a1, b1⟩, anySub_constP_forallE.2 ⟨a2, b2⟩, rfl⟩
  | letE nm t v b nd ih1 ih2 ih3 =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    have hl' : t.hasLooseBVar' j = false ∧ v.hasLooseBVar' j = false ∧
        b.hasLooseBVar' (j + 1) = false := by
      simpa [Expr.hasLooseBVar', Bool.or_eq_false_iff, and_assoc] using hl
    have hr' := anySub_constP_letE.1 hr
    obtain ⟨a1, a2, a3⟩ := ih1 hA.1 hj hr'.1 hl'.1
    obtain ⟨c1, c2, c3⟩ := ih2 hA.2.1 hj hr'.2.1 hl'.2.1
    obtain ⟨b1, b2, b3⟩ := ih3 (j := j + 1) hA.2.2 (by omega) hr'.2.2 hl'.2.2
    rw [show K + 1 - 1 = K - 1 + 1 by omega] at b1
    rw [lower_letE h1, Expr.replaceNoCache_letE (hF.noSpine _ rfl),
      Expr.replaceNoCache_letE (hF.noSpine _ rfl), lower_letE h1, a3, b3, c3]
    exact ⟨⟨a1, c1, b1⟩, anySub_constP_letE.2 ⟨a2, c2, b2⟩, rfl⟩
  | mdata m e ih =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    obtain ⟨a1, a2, a3⟩ := ih hA hj (anySub_constP_mdata.1 hr)
      (by simpa [Expr.hasLooseBVar'] using hl)
    rw [lower_mdata h1, Expr.replaceNoCache_mdata (hF.noSpine _ rfl),
      Expr.replaceNoCache_mdata (hF.noSpine _ rfl), lower_mdata h1, a3]
    exact ⟨a1, anySub_constP_mdata.2 a2, rfl⟩
  | proj x i e ih =>
    intro K j hA hj hr hl
    have h1 : ¬j + 1 < 1 := by omega
    obtain ⟨a1, a2, a3⟩ := ih hA hj (anySub_constP_proj.1 hr)
      (by simpa [Expr.hasLooseBVar'] using hl)
    rw [lower_proj h1, Expr.replaceNoCache_proj (hF.noSpine _ rfl),
      Expr.replaceNoCache_proj (hF.noSpine _ rfl), lower_proj h1, a3]
    exact ⟨a1, anySub_constP_proj.2 a2, rfl⟩
  | bvar i =>
    intro K j _ hj _ _
    rw [lower_bvar (by omega), h0 rfl (by simp [Expr.isBVar]), h0 rfl (by simp [Expr.isBVar]),
      lower_bvar (by omega)]
    exact ⟨trivial, rfl, rfl⟩
  | fvar x =>
    intro K j _ hj _ _
    have hlo : (Expr.fvar x).lowerLooseBVars' (j + 1) 1 = .fvar x := by
      unfold Expr.lowerLooseBVars'; split <;> rfl
    rw [hlo, h0 rfl (by simp [Expr.isFVar])]; exact ⟨trivial, rfl, hlo.symm⟩
  | mvar x =>
    intro K j _ hj _ _
    have hlo : (Expr.mvar x).lowerLooseBVars' (j + 1) 1 = .mvar x := by
      unfold Expr.lowerLooseBVars'; split <;> rfl
    rw [hlo, h0 rfl (by simp [Expr.isMVar])]; exact ⟨trivial, rfl, hlo.symm⟩
  | sort x =>
    intro K j _ hj _ _
    have hlo : (Expr.sort x).lowerLooseBVars' (j + 1) 1 = .sort x := by
      unfold Expr.lowerLooseBVars'; split <;> rfl
    rw [hlo, h0 rfl (by simp [Expr.isSort])]; exact ⟨trivial, rfl, hlo.symm⟩
  | lit x =>
    intro K j _ hj _ _
    have hlo : (Expr.lit x).lowerLooseBVars' (j + 1) 1 = .lit x := by
      unfold Expr.lowerLooseBVars'; split <;> rfl
    rw [hlo, h0 rfl (by simp [Expr.isLit])]; exact ⟨trivial, rfl, hlo.symm⟩

/-- Restoring a term placed at the parameters is not a pi type unless the term is one. -/
theorem PlacedFn.not_forallE {e : Expr} {K : Nat} (hA : AuxPlaced isAux lvls n K e)
    (hr : e.anySub (constP isRec) = false) (he : ∀ nm d b bi, e ≠ .forallE nm d b bi) :
    ∀ nm d b bi, e.replaceNoCache F ≠ .forallE nm d b bi := by
  have hlift {N : Expr} (hN : ∀ nm d b bi, N ≠ .forallE nm d b bi) (K : Nat) :
      ∀ nm d b bi, N.liftLooseBVars' 0 K ≠ .forallE nm d b bi := by
    intro nm d b bi h; cases N <;> simp [Expr.liftLooseBVars'] at h; exact hN _ _ _ _ rfl
  cases e with
  | forallE => exact (he _ _ _ _ rfl).elim
  | const c ls =>
    by_cases hc : isAux c
    · obtain ⟨rfl, rfl⟩ := hA hc
      obtain ⟨N, -, hN, hFN⟩ := hF.aux c hc
      have := hFN K; simp only [bvs, Expr.mkAppList] at this
      rw [Expr.replaceNoCache.eq_def, this]; exact hlift hN.1 K
    · rw [Expr.replaceNoCache.eq_def,
        hF.spine _ c ls [] rfl (by simp [hc]) (by simpa [Expr.anySub, constP] using hr)]
      nofun
  | app f a =>
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      by_cases hc : isAux c = true ∧ xs.length = n
      · rw [if_pos hc] at hA
        obtain ⟨rfl, rfl⟩ := hA
        obtain ⟨N, -, hN, hFN⟩ := hF.aux c hc.1
        rw [spineNM_eq hs, Expr.replaceNoCache.eq_def, hFN K]; exact hlift hN.1 K
      · rw [Expr.replaceNoCache_app (hF.spine _ c ls xs hs hc (spineNM_anySub hs hr))]; nofun
    · rename_i hs; rw [Expr.replaceNoCache_app (hF.noSpine _ hs)]; nofun
  | lam => rw [Expr.replaceNoCache_lam (hF.noSpine _ rfl)]; nofun
  | letE => rw [Expr.replaceNoCache_letE (hF.noSpine _ rfl)]; nofun
  | mdata => rw [Expr.replaceNoCache_mdata (hF.noSpine _ rfl)]; nofun
  | proj => rw [Expr.replaceNoCache_proj (hF.noSpine _ rfl)]; nofun
  | bvar | fvar | mvar | sort | lit => rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; nofun

/-- Restoring a term placed at the parameters is not a variable unless the term is one. -/
theorem PlacedFn.not_var {e : Expr} {K : Nat} (hA : AuxPlaced isAux lvls n K e)
    (hr : e.anySub (constP isRec) = false) (hb : ∀ i, e ≠ .bvar i) (hx : ∀ x, e ≠ .fvar x) :
    (∀ i, e.replaceNoCache F ≠ .bvar i) ∧ (∀ x, e.replaceNoCache F ≠ .fvar x) := by
  have hlift {N : Expr} (hN : (∀ i, N ≠ .bvar i) ∧ (∀ x, N ≠ .fvar x)) (K : Nat) :
      (∀ i, N.liftLooseBVars' 0 K ≠ .bvar i) ∧ (∀ x, N.liftLooseBVars' 0 K ≠ .fvar x) := by
    constructor <;> intro i h <;> cases N <;> simp [Expr.liftLooseBVars'] at h
    · exact hN.1 _ rfl
    · exact hN.2 _ rfl
  cases e with
  | bvar => exact (hb _ rfl).elim
  | fvar => exact (hx _ rfl).elim
  | const c ls =>
    by_cases hc : isAux c
    · obtain ⟨rfl, rfl⟩ := hA hc
      obtain ⟨N, -, hN, hFN⟩ := hF.aux c hc
      have := hFN K; simp only [bvs, Expr.mkAppList] at this
      rw [Expr.replaceNoCache.eq_def, this]; exact hlift hN.2 K
    · rw [Expr.replaceNoCache.eq_def,
        hF.spine _ c ls [] rfl (by simp [hc]) (by simpa [Expr.anySub, constP] using hr)]
      exact ⟨nofun, nofun⟩
  | app f a =>
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      by_cases hc : isAux c = true ∧ xs.length = n
      · rw [if_pos hc] at hA
        obtain ⟨rfl, rfl⟩ := hA
        obtain ⟨N, -, hN, hFN⟩ := hF.aux c hc.1
        rw [spineNM_eq hs, Expr.replaceNoCache.eq_def, hFN K]; exact hlift hN.2 K
      · rw [Expr.replaceNoCache_app (hF.spine _ c ls xs hs hc (spineNM_anySub hs hr))]
        exact ⟨nofun, nofun⟩
    · rename_i hs; rw [Expr.replaceNoCache_app (hF.noSpine _ hs)]; exact ⟨nofun, nofun⟩
  | lam => rw [Expr.replaceNoCache_lam (hF.noSpine _ rfl)]; exact ⟨nofun, nofun⟩
  | forallE => rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl)]; exact ⟨nofun, nofun⟩
  | letE => rw [Expr.replaceNoCache_letE (hF.noSpine _ rfl)]; exact ⟨nofun, nofun⟩
  | mdata => rw [Expr.replaceNoCache_mdata (hF.noSpine _ rfl)]; exact ⟨nofun, nofun⟩
  | proj => rw [Expr.replaceNoCache_proj (hF.noSpine _ rfl)]; exact ⟨nofun, nofun⟩
  | mvar | sort | lit =>
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; exact ⟨nofun, nofun⟩

theorem dropU_of_not_forallE {e : Expr} (he : ∀ nm d b bi, e ≠ .forallE nm d b bi) :
    ∀ m, Expr.dropU m e = e
  | 0 => by simp
  | _ + 1 => by cases e <;> first | rfl | exact (he _ _ _ _ rfl).elim

/-- Restoring commutes with dropping the unused binders among the first `m` of a term placed at
the parameters. -/
theorem PlacedFn.dropU : ∀ (m : Nat) {e : Expr} {K : Nat}, AuxPlaced isAux lvls n K e →
    e.anySub (constP isRec) = false →
    Expr.dropU m (e.replaceNoCache F) = (Expr.dropU m e).replaceNoCache F
  | 0, e, K, _, _ => by simp
  | m + 1, e, K, hA, hr => by
    by_cases he : ∃ nm d b bi, e = .forallE nm d b bi
    · obtain ⟨nm, d, b, bi, rfl⟩ := he
      have hr' := anySub_constP_forallE.1 hr
      rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl), Expr.dropU_forallE, Expr.dropU_forallE,
        hF.hasLooseBVar' hA.2 (Nat.zero_lt_succ K) hr'.2]
      split
      · rw [PlacedFn.dropU m hA.2 hr'.2, Expr.replaceNoCache_forallE (hF.noSpine _ rfl)]
      · rename_i hb
        obtain ⟨b1, b2, b3⟩ := hF.lower hA.2 (Nat.zero_lt_succ K) hr'.2 (by simpa using hb)
        rw [← b3, PlacedFn.dropU m b1 b2]
    · have he' : ∀ nm d b bi, e ≠ .forallE nm d b bi := fun nm d b bi h => he ⟨nm, d, b, bi, h⟩
      rw [dropU_of_not_forallE hF he', dropU_of_not_forallE hF (hF.not_forallE hA hr he')]

/-- Restoring leaves a term without auxiliary constants alone. -/
theorem PlacedFn.id_of_free : ∀ {e : Expr}, e.anySub (constP isAux) = false →
    e.anySub (constP isRec) = false → e.replaceNoCache F = e := by
  intro e
  induction e with
  | const c ls =>
    intro h1 h2
    rw [Expr.replaceNoCache.eq_def, hF.spine _ c ls [] rfl
      (by simp [show isAux c = false by simpa [Expr.anySub, constP] using h1])
      (by simpa [Expr.anySub, constP] using h2)]
  | app f a ih1 ih2 =>
    intro h1 h2
    have h1' := anySub_constP_app.1 h1; have h2' := anySub_constP_app.1 h2
    have hF0 : F (.app f a) = none := by
      cases h : spineNM (.app f a) with
      | none => exact hF.noSpine _ h
      | some x =>
        obtain ⟨c, ls, xs⟩ := x
        exact hF.spine _ c ls xs h (by simp [spineNM_anySub h h1]) (spineNM_anySub h h2)
    rw [Expr.replaceNoCache_app hF0, ih1 h1'.1 h2'.1, ih2 h1'.2 h2'.2]
  | lam _ t b _ ih1 ih2 =>
    intro h1 h2
    have h1' := anySub_constP_lam.1 h1; have h2' := anySub_constP_lam.1 h2
    rw [Expr.replaceNoCache_lam (hF.noSpine _ rfl), ih1 h1'.1 h2'.1, ih2 h1'.2 h2'.2]
  | forallE _ t b _ ih1 ih2 =>
    intro h1 h2
    have h1' := anySub_constP_forallE.1 h1; have h2' := anySub_constP_forallE.1 h2
    rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl), ih1 h1'.1 h2'.1, ih2 h1'.2 h2'.2]
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro h1 h2
    have h1' := anySub_constP_letE.1 h1; have h2' := anySub_constP_letE.1 h2
    rw [Expr.replaceNoCache_letE (hF.noSpine _ rfl), ih1 h1'.1 h2'.1, ih2 h1'.2.1 h2'.2.1,
      ih3 h1'.2.2 h2'.2.2]
  | mdata _ e ih =>
    intro h1 h2
    rw [Expr.replaceNoCache_mdata (hF.noSpine _ rfl),
      ih (anySub_constP_mdata.1 h1) (anySub_constP_mdata.1 h2)]
  | proj _ _ e ih =>
    intro h1 h2
    rw [Expr.replaceNoCache_proj (hF.noSpine _ rfl),
      ih (anySub_constP_proj.1 h1) (anySub_constP_proj.1 h2)]
  | bvar | fvar | mvar | sort | lit => intros; rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]

/-- Dropping unused binders keeps a term placed at the parameters. -/
theorem PlacedFn.dropU_placed : ∀ (m : Nat) {e : Expr} {K : Nat}, AuxPlaced isAux lvls n K e →
    e.anySub (constP isRec) = false →
    AuxPlaced isAux lvls n K (Expr.dropU m e) ∧ (Expr.dropU m e).anySub (constP isRec) = false
  | 0, e, K, hA, hr => by simpa using ⟨hA, hr⟩
  | m + 1, e, K, hA, hr => by
    cases e with
    | forallE nm d b bi =>
      have hr' := anySub_constP_forallE.1 hr
      rw [Expr.dropU_forallE]
      split
      · obtain ⟨a1, a2⟩ := PlacedFn.dropU_placed m hA.2 hr'.2
        exact ⟨⟨hA.1, a1⟩, anySub_constP_forallE.2 ⟨hr'.1, a2⟩⟩
      · rename_i hb
        obtain ⟨b1, b2, -⟩ := hF.lower hA.2 (Nat.zero_lt_succ K) hr'.2 (by simpa using hb)
        exact PlacedFn.dropU_placed m b1 b2
    | _ => exact ⟨hA, hr⟩

end

theorem constsOK_lower {p : Name → List Level → Prop} : ∀ {e : Expr} {s d : Nat},
    e.ConstsOK p → (e.lowerLooseBVars' s d).ConstsOK p := by
  intro e
  induction e with
  | app f a ih1 ih2 | lam _ f a _ ih1 ih2 | forallE _ f a _ ih1 ih2 =>
    intro s d h; unfold Expr.lowerLooseBVars'; split
    · exact h
    · exact ⟨ih1 h.1, ih2 h.2⟩
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro s d h; unfold Expr.lowerLooseBVars'; split
    · exact h
    · exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | mdata _ e ih | proj _ _ e ih =>
    intro s d h; unfold Expr.lowerLooseBVars'; split
    · exact h
    · exact ih h
  | _ => intro s d h; unfold Expr.lowerLooseBVars'; split <;> exact h

theorem constsOK_dropU {p : Name → List Level → Prop} : ∀ (m : Nat) {e : Expr},
    e.ConstsOK p → (Expr.dropU m e).ConstsOK p
  | 0, e, h => by simpa using h
  | m + 1, e, h => by
    cases e with
    | forallE nm d b bi =>
      rw [Expr.dropU_forallE]; split
      · exact ⟨h.1, constsOK_dropU m h.2⟩
      · exact constsOK_dropU m (constsOK_lower h.2)
    | _ => exact h

section
variable {F : Expr → Option Expr} {isAux isRec : Name → Bool} {lvls : List Level} {n : Nat}
  (hF : PlacedFn F isAux isRec lvls n)
include hF

/-- `e`'s first `p` binders lead to a body placed at them. -/
def PlacedAfter (isAux : Name → Bool) (lvls : List Level) (n : Nat) : Nat → Expr → Prop
  | 0, e => AuxPlaced isAux lvls n 0 e
  | p + 1, .forallE _ d b _ => d.anySub (constP isAux) = false ∧ PlacedAfter isAux lvls n p b
  | _ + 1, _ => False

/-- Restoring commutes with dropping, after the first `p` binders, the unused binders among the
next `m`. -/
theorem PlacedFn.dropAfter : ∀ (p m : Nat) {e : Expr}, PlacedAfter isAux lvls n p e →
    e.anySub (constP isRec) = false →
    Expr.dropAfter p m (e.replaceNoCache F) = (Expr.dropAfter p m e).replaceNoCache F
  | 0, m, e, hA, hr => by simpa using hF.dropU m hA hr
  | p + 1, m, .forallE nm d b bi, hA, hr => by
    have hr' := anySub_constP_forallE.1 hr
    rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl), Expr.dropAfter_forallE,
      Expr.dropAfter_forallE, Expr.replaceNoCache_forallE (hF.noSpine _ rfl),
      PlacedFn.dropAfter p m hA.2 hr'.2]

end

end Lean4Lean.ElimNestedInductive

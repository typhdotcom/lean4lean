import Lean4Lean.Verify.Typing.PTr

/-!
# Pi telescopes with unused binders dropped

`inferProj` walks a constructor's type: it instantiates each binder the rest mentions with a
value, and drops one the rest does not mention. `Expr.dropAfter p m t` is `t` with, after `p`
binders kept, those among the next `m` that the rest does not mention dropped. Instantiating
commutes with dropping (`dropAfter_instantiate1'`), so the kernel's term after a walk is the
dropped telescope instantiated by the values it took.
-/

namespace Lean4Lean
open Lean

/-- The number of binders a term's syntactic pi telescope opens. -/
def _root_.Lean.Expr.leadingForalls : Expr → Nat
  | .forallE _ _ body _ => body.leadingForalls + 1
  | _ => 0

namespace Expr
open Lean.Expr

/-- `e` with those of its first `m` binders that the rest does not mention dropped. -/
def dropU : Nat → Expr → Expr
  | m + 1, .forallE n d b bi =>
    if b.hasLooseBVar' 0 then .forallE n d (dropU m b) bi else dropU m (b.lowerLooseBVars' 1 1)
  | _, e => e

/-- `e` with its first `p` binders kept, then those of the next `m` that the rest does not
mention dropped. -/
def dropAfter : Nat → Nat → Expr → Expr
  | p + 1, m, .forallE n d b bi => .forallE n d (dropAfter p m b) bi
  | 0, m, e => dropU m e
  | _ + 1, _, e => e

@[simp] theorem dropU_zero (e : Expr) : dropU 0 e = e := by cases e <;> rfl

theorem dropU_forallE (m : Nat) (n d b bi) :
    dropU (m + 1) (.forallE n d b bi) =
      if b.hasLooseBVar' 0 then .forallE n d (dropU m b) bi
      else dropU m (b.lowerLooseBVars' 1 1) := rfl

@[simp] theorem dropAfter_zero (m : Nat) (e : Expr) : dropAfter 0 m e = dropU m e := by
  cases m <;> cases e <;> rfl

theorem dropAfter_forallE (p m : Nat) (n d b bi) :
    dropAfter (p + 1) m (.forallE n d b bi) = .forallE n d (dropAfter p m b) bi := rfl

theorem lowerLooseBVars'_eq_self {e : Expr} (h : e.looseBVarRange' ≤ s) :
    e.lowerLooseBVars' s d = e := by
  induction e generalizing s with
    simp_all [lowerLooseBVars', looseBVarRange', Nat.max_le]
  | _ => grind

theorem hasLooseBVar'_instantiate1' {v : Expr} (hv : v.looseBVarRange' = 0) :
    ∀ {e : Expr} {j k : Nat}, j ≤ k →
      (e.instantiate1' v (k + 1)).hasLooseBVar' j = e.hasLooseBVar' j := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk
    simp only [instantiate1']
    split
    · rfl
    · split
      · simp only [hasLooseBVar']
        rw [Expr.liftLooseBVars_eq_self (by omega), hasLooseBVar_of_ge_looseBVarRange (by omega)]
        simp; omega
      · simp only [hasLooseBVar', decide_eq_decide]; omega
  | app f a ih1 ih2 => intro j k h; simp [instantiate1', hasLooseBVar', ih1 h, ih2 h]
  | lam _ t b _ ih1 ih2 | forallE _ t b _ ih1 ih2 =>
    intro j k h; simp [instantiate1', hasLooseBVar', ih1 h, ih2 (Nat.succ_le_succ h)]
  | letE _ t v' b _ ih1 ih2 ih3 =>
    intro j k h
    simp [instantiate1', hasLooseBVar', ih1 h, ih2 h, ih3 (Nat.succ_le_succ h)]
  | mdata _ e ih | proj _ _ e ih => intro j k h; simp [instantiate1', hasLooseBVar', ih h]
  | _ => intros; rfl

/-- Lowering past an unused binder commutes with instantiating a closed term further out. -/
theorem lowerLooseBVars'_instantiate1' {v : Expr} (hv : v.looseBVarRange' = 0) :
    ∀ {e : Expr} {j k : Nat}, e.hasLooseBVar' j = false →
      (e.lowerLooseBVars' (j + 1) 1).instantiate1' v (k + j) =
        (e.instantiate1' v (k + j + 1)).lowerLooseBVars' (j + 1) 1 := by
  have hv' : ∀ s d, v.liftLooseBVars' s d = v := fun s d => Expr.liftLooseBVars_eq_self (by omega)
  have hvl : ∀ s d, v.lowerLooseBVars' s d = v := fun s d => lowerLooseBVars'_eq_self (by omega)
  intro e
  induction e with
  | bvar i =>
    intro j k h
    simp only [hasLooseBVar', decide_eq_false_iff_not] at h
    simp only [lowerLooseBVars', show ¬j + 1 < 1 by omega, if_false, instantiate1']
    by_cases h1 : i < j + 1
    · rw [if_pos h1, if_pos (by omega : i < k + j), if_pos (by omega : i < k + j + 1)]
      simp [lowerLooseBVars', h1]
    · rw [if_neg h1]
      by_cases h2 : i - 1 < k + j
      · rw [if_pos h2, if_pos (by omega : i < k + j + 1)]
        simp [lowerLooseBVars', h1]
      · rw [if_neg h2, if_neg (by omega : ¬i < k + j + 1)]
        by_cases h3 : i - 1 = k + j
        · rw [if_pos h3, if_pos (by omega : i = k + j + 1), hv', hv', hvl]
        · rw [if_neg h3, if_neg (by omega : ¬i = k + j + 1)]
          simp only [lowerLooseBVars', show ¬j + 1 < 1 by omega, if_false,
            show ¬i - 1 < j + 1 by omega]
  | app f a ih1 ih2 =>
    intro j k h
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    simp [lowerLooseBVars', instantiate1', ih1 h.1, ih2 h.2]
  | lam _ t b _ ih1 ih2 | forallE _ t b _ ih1 ih2 =>
    intro j k h
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    have := ih2 (j := j + 1) (k := k) h.2
    simp only [show k + (j + 1) = k + j + 1 by omega] at this
    simp [lowerLooseBVars', instantiate1', ih1 h.1, this]
  | letE _ t v' b _ ih1 ih2 ih3 =>
    intro j k h
    simp only [hasLooseBVar', Bool.or_eq_false_iff] at h
    have := ih3 (j := j + 1) (k := k) h.2
    simp only [show k + (j + 1) = k + j + 1 by omega] at this
    simp [lowerLooseBVars', instantiate1', ih1 h.1.1, ih2 h.1.2, this]
  | mdata _ e ih | proj _ _ e ih =>
    intro j k h
    simp only [hasLooseBVar'] at h
    simp [lowerLooseBVars', instantiate1', ih h]
  | _ => intros; simp [lowerLooseBVars', instantiate1']

theorem leadingForalls_lowerLooseBVars' (e : Expr) (s d : Nat) :
    (e.lowerLooseBVars' s d).leadingForalls = e.leadingForalls := by
  induction e generalizing s with
  | forallE _ _ b _ _ ih =>
    unfold lowerLooseBVars'; split
    · rfl
    · simp [Expr.leadingForalls, ih]
  | _ => unfold lowerLooseBVars'; split <;> rfl

theorem dropU_instantiate1' {v : Expr} (hv : v.looseBVarRange' = 0) :
    ∀ (m : Nat) (e : Expr) (k : Nat), m ≤ e.leadingForalls →
      (dropU m e).instantiate1' v k = dropU m (e.instantiate1' v k)
  | 0, e, k, _ => by simp
  | m + 1, .forallE n d b bi, k, hm => by
    simp only [Expr.leadingForalls, Nat.add_le_add_iff_right] at hm
    simp only [dropU_forallE, instantiate1', hasLooseBVar'_instantiate1' hv (Nat.zero_le k)]
    split
    · simp [instantiate1', dropU_instantiate1' hv m b (k + 1) hm]
    · rename_i h
      rw [dropU_instantiate1' hv m _ k (by rw [leadingForalls_lowerLooseBVars']; exact hm)]
      have := lowerLooseBVars'_instantiate1' hv (e := b) (j := 0) (k := k) (by simpa using h)
      simp only [Nat.add_zero] at this
      rw [this]
  | m + 1, .bvar _, _, hm | m + 1, .fvar _, _, hm | m + 1, .mvar _, _, hm
  | m + 1, .sort _, _, hm | m + 1, .const .., _, hm | m + 1, .app .., _, hm
  | m + 1, .lam .., _, hm | m + 1, .letE .., _, hm | m + 1, .lit _, _, hm
  | m + 1, .mdata .., _, hm | m + 1, .proj .., _, hm => by simp [Expr.leadingForalls] at hm

theorem dropAfter_instantiate1' {v : Expr} (hv : v.looseBVarRange' = 0) :
    ∀ (p m : Nat) (e : Expr) (k : Nat), p + m ≤ e.leadingForalls →
      (dropAfter p m e).instantiate1' v k = dropAfter p m (e.instantiate1' v k)
  | 0, m, e, k, h => by simpa using dropU_instantiate1' hv m e k (by simpa using h)
  | p + 1, m, .forallE n d b bi, k, h => by
    simp only [Expr.leadingForalls] at h
    simp [dropAfter_forallE, instantiate1', dropAfter_instantiate1' hv p m b (k + 1) (by omega)]
  | p + 1, _, .bvar _, _, h | p + 1, _, .fvar _, _, h | p + 1, _, .mvar _, _, h
  | p + 1, _, .sort _, _, h | p + 1, _, .const .., _, h | p + 1, _, .app .., _, h
  | p + 1, _, .lam .., _, h | p + 1, _, .letE .., _, h | p + 1, _, .lit _, _, h
  | p + 1, _, .mdata .., _, h | p + 1, _, .proj .., _, h => by
    simp [Expr.leadingForalls] at h


@[simp] theorem dropAfter_zero_right : ∀ (p : Nat) (e : Expr), dropAfter p 0 e = e
  | 0, e => by simp
  | p + 1, .forallE n d b bi => by simp [dropAfter_forallE, dropAfter_zero_right p b]
  | _ + 1, .bvar _ | _ + 1, .fvar _ | _ + 1, .mvar _ | _ + 1, .sort _ | _ + 1, .const ..
  | _ + 1, .app .. | _ + 1, .lam .. | _ + 1, .letE .. | _ + 1, .lit _ | _ + 1, .mdata ..
  | _ + 1, .proj .. => rfl

theorem hasLooseBVar'_of_looseBVarRange' :
    ∀ {e : Expr} {k : Nat}, e.looseBVarRange' = k + 1 → e.hasLooseBVar' k = true := by
  intro e
  induction e with
  | bvar i => intro k h; simp [looseBVarRange'] at h; simp [hasLooseBVar', h]
  | app f a ih1 ih2 =>
    intro k h; simp only [looseBVarRange'] at h
    simp only [hasLooseBVar', Bool.or_eq_true]
    rcases Nat.le_total f.looseBVarRange' a.looseBVarRange' with h' | h'
    · exact .inr (ih2 (by rw [Nat.max_eq_right h'] at h; exact h))
    · exact .inl (ih1 (by rw [Nat.max_eq_left h'] at h; exact h))
  | lam _ t b _ ih1 ih2 | forallE _ t b _ ih1 ih2 =>
    intro k h; simp only [looseBVarRange'] at h
    simp only [hasLooseBVar', Bool.or_eq_true]
    rcases Nat.le_total t.looseBVarRange' (b.looseBVarRange' - 1) with h' | h'
    · rw [Nat.max_eq_right h'] at h; exact .inr (ih2 (by omega))
    · rw [Nat.max_eq_left h'] at h; exact .inl (ih1 h)
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro k h; simp only [looseBVarRange'] at h
    simp only [hasLooseBVar', Bool.or_eq_true]
    rcases Nat.le_total (max t.looseBVarRange' v.looseBVarRange') (b.looseBVarRange' - 1)
      with h' | h'
    · rw [Nat.max_eq_right h'] at h; exact .inr (ih3 (by omega))
    · rw [Nat.max_eq_left h'] at h
      rcases Nat.le_total t.looseBVarRange' v.looseBVarRange' with h'' | h''
      · rw [Nat.max_eq_right h''] at h; exact .inl (.inr (ih2 h))
      · rw [Nat.max_eq_left h''] at h; exact .inl (.inl (ih1 h))
  | mdata _ e ih | proj _ _ e ih => intro k h; simp only [looseBVarRange'] at h; exact ih h
  | _ => intro k h; simp [looseBVarRange'] at h

/-! #### Instantiating universe parameters -/

section
variable {red : Bool} {F : Name → Level}

theorem hasLooseBVar'_instantiateLevelParamsCore' :
    ∀ {e : Expr} {j : Nat},
      (e.instantiateLevelParamsCore' red F).hasLooseBVar' j = e.hasLooseBVar' j := by
  intro e; induction e <;> intros <;> simp_all [instantiateLevelParamsCore', hasLooseBVar']

theorem lowerLooseBVars'_instantiateLevelParamsCore' :
    ∀ {e : Expr} {s d : Nat},
      (e.instantiateLevelParamsCore' red F).lowerLooseBVars' s d =
        (e.lowerLooseBVars' s d).instantiateLevelParamsCore' red F := by
  intro e; induction e <;> intros <;> unfold lowerLooseBVars' <;> split <;>
    simp_all [instantiateLevelParamsCore']

theorem leadingForalls_instantiateLevelParamsCore'' :
    ∀ {e : Expr}, (e.instantiateLevelParamsCore' red F).leadingForalls = e.leadingForalls := by
  intro e; induction e <;> simp_all [instantiateLevelParamsCore', Expr.leadingForalls]

theorem dropU_instantiateLevelParamsCore' :
    ∀ (m : Nat) (e : Expr),
      dropU m (e.instantiateLevelParamsCore' red F) = (dropU m e).instantiateLevelParamsCore' red F
  | 0, e => by simp
  | m + 1, .forallE n d b bi => by
    simp only [instantiateLevelParamsCore', dropU_forallE, hasLooseBVar'_instantiateLevelParamsCore']
    split
    · simp [instantiateLevelParamsCore', dropU_instantiateLevelParamsCore' m b]
    · rw [lowerLooseBVars'_instantiateLevelParamsCore', dropU_instantiateLevelParamsCore']
  | _ + 1, .bvar _ | _ + 1, .fvar _ | _ + 1, .mvar _ | _ + 1, .sort _ | _ + 1, .const ..
  | _ + 1, .app .. | _ + 1, .lam .. | _ + 1, .letE .. | _ + 1, .lit _ | _ + 1, .mdata ..
  | _ + 1, .proj .. => rfl

theorem dropAfter_instantiateLevelParamsCore' :
    ∀ (p m : Nat) (e : Expr), dropAfter p m (e.instantiateLevelParamsCore' red F) =
      (dropAfter p m e).instantiateLevelParamsCore' red F
  | 0, m, e => by simp [dropU_instantiateLevelParamsCore']
  | p + 1, m, .forallE n d b bi => by
    simp [instantiateLevelParamsCore', dropAfter_forallE, dropAfter_instantiateLevelParamsCore' p m b]
  | _ + 1, _, .bvar _ | _ + 1, _, .fvar _ | _ + 1, _, .mvar _ | _ + 1, _, .sort _
  | _ + 1, _, .const .. | _ + 1, _, .app .. | _ + 1, _, .lam .. | _ + 1, _, .letE ..
  | _ + 1, _, .lit _ | _ + 1, _, .mdata .. | _ + 1, _, .proj .. => rfl

end

theorem dropAfter_instantiateLevelParams (p m : Nat) (e : Expr) (ps : List Name)
    (ls : List Level) :
    dropAfter p m (e.instantiateLevelParams ps ls) =
      (dropAfter p m e).instantiateLevelParams ps ls := by
  simp only [instantiateLevelParams_eq, dropAfter_instantiateLevelParamsCore']

theorem instantiateLevelParams_forallE {n d b bi} {ps : List Name} {ls : List Level} :
    (Expr.forallE n d b bi).instantiateLevelParams ps ls =
      .forallE n (d.instantiateLevelParams ps ls) (b.instantiateLevelParams ps ls) bi := by
  simp only [instantiateLevelParams_eq]; rfl


end Expr

theorem FVarsIn.lowerLooseBVars {P : FVarId → Prop} :
    ∀ {e : Expr} {s d : Nat}, FVarsIn P e → FVarsIn P (e.lowerLooseBVars' s d) := by
  intro e; induction e <;> intro s d h <;> unfold Expr.lowerLooseBVars' <;> split <;>
    simp_all [FVarsIn]

theorem FVarsIn.dropU {P : FVarId → Prop} :
    ∀ (m : Nat) {e : Expr}, FVarsIn P e → FVarsIn P (Expr.dropU m e)
  | 0, e, h => by simpa using h
  | m + 1, .forallE n d b bi, h => by
    rw [Expr.dropU_forallE]; split
    · exact ⟨h.1, FVarsIn.dropU m h.2⟩
    · exact FVarsIn.dropU m (FVarsIn.lowerLooseBVars h.2)
  | _ + 1, .bvar _, h | _ + 1, .fvar _, h | _ + 1, .mvar _, h | _ + 1, .sort _, h
  | _ + 1, .const .., h | _ + 1, .app .., h | _ + 1, .lam .., h | _ + 1, .letE .., h
  | _ + 1, .lit _, h | _ + 1, .mdata .., h | _ + 1, .proj .., h => h

theorem FVarsIn.dropAfter {P : FVarId → Prop} :
    ∀ {e : Expr}, FVarsIn P e → ∀ (p m : Nat), FVarsIn P (Expr.dropAfter p m e)
  | e, h, 0, m => by simpa using FVarsIn.dropU m h
  | .forallE n d b bi, h, p + 1, m => by
    rw [Expr.dropAfter_forallE]; exact ⟨h.1, FVarsIn.dropAfter h.2 p m⟩
  | .bvar _, h, _ + 1, _ | .fvar _, h, _ + 1, _ | .mvar _, h, _ + 1, _ | .sort _, h, _ + 1, _
  | .const .., h, _ + 1, _ | .app .., h, _ + 1, _ | .lam .., h, _ + 1, _
  | .letE .., h, _ + 1, _ | .lit _, h, _ + 1, _ | .mdata .., h, _ + 1, _
  | .proj .., h, _ + 1, _ => h

theorem Expr.dropAfter_of_not_forallE {t : Expr} (h : ∀ n d b bi, t ≠ .forallE n d b bi) :
    ∀ p m, Expr.dropAfter p m t = t
  | 0, 0 => by simp
  | 0, _ + 1 => by cases t <;> first | rfl | exact (h _ _ _ _ rfl).elim
  | _ + 1, _ => by cases t <;> first | rfl | exact (h _ _ _ _ rfl).elim

/-! ### Translated domains -/

/-- `r`'s pi telescope, all of it, has domains that translate in `Δ` to types, each in the
context of the ones before it as bound variables. -/
inductive TeleDoms (env : VEnv) (Us : List Name) : VLCtx → Expr → Prop
  | nil {Δ : VLCtx} {r : Expr} :
    (∀ n d b bi, r ≠ .forallE n d b bi) → (∀ i, r ≠ .bvar i) → (∀ x, r ≠ .fvar x) →
    TeleDoms env Us Δ r
  | cons {Δ : VLCtx} {dom b : Expr} {A : VExpr} {n bi} :
    TrExprS env Us Δ dom A → env.IsType Us.length Δ.toCtx A →
    TeleDoms env Us ((none, .vlam A) :: Δ) b → TeleDoms env Us Δ (.forallE n dom b bi)

namespace TeleDoms
variable {env : VEnv} {Us : List Name}

theorem mono {env' : VEnv} (henv : env ≤ env') {Δ : VLCtx} {r : Expr}
    (H : TeleDoms env Us Δ r) : TeleDoms env' Us Δ r := by
  induction H with
  | nil h1 h2 h3 => exact .nil h1 h2 h3
  | cons h1 h2 _ ih => exact .cons (h1.mono henv) (h2.mono henv) ih

theorem instN (henv : env.Ordered) {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr}
    (h₀ : TrExprS env Us Δ₀ e₀ e₀') (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    {dk k : Nat} {Δ₁ Δ : VLCtx} (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) {r : Expr}
    (H : TeleDoms env Us Δ₁ r) : TeleDoms env Us Δ (r.instantiate1' e₀ dk) := by
  induction H generalizing Δ dk k with
  | @nil _ r h1 h2 h3 =>
    refine .nil (fun n d b bi h => ?_) (fun i h => ?_) (fun x h => ?_)
    · cases r with
      | bvar j => exact h2 j rfl
      | forallE => exact h1 _ _ _ _ rfl
      | _ => simp [Expr.instantiate1'] at h
    · cases r with
      | bvar j => exact h2 j rfl
      | _ => simp [Expr.instantiate1'] at h
    · cases r with
      | bvar j => exact h2 j rfl
      | fvar y => exact h3 y rfl
      | _ => simp [Expr.instantiate1'] at h
  | cons h1 h2 _ ih =>
    exact .cons (h₀.instN henv t₀ W h1) (h2.instN henv W.toCtx t₀) (ih (W.succ (d := .vlam _)))

theorem inst (henv : env.Ordered) {Δ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr}
    (h₀ : TrExprS env Us Δ e₀ e₀') (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀) {r : Expr}
    (H : TeleDoms env Us ((none, .vlam A₀) :: Δ) r) :
    TeleDoms env Us Δ (r.instantiate1' e₀) :=
  H.instN henv h₀ t₀ .zero

theorem weakFV (henv : env.Ordered) {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length) {r : Expr}
    (H : TeleDoms env Us Δ r) : TeleDoms env Us Δ' r := by
  induction H generalizing Δ' dk k with
  | nil h1 h2 h3 => exact .nil h1 h2 h3
  | cons h1 h2 _ ih =>
    have h2' := h2.weakN henv W.toCtx
    exact .cons (h1.weakFV henv W hΔ') h2'
      (ih (W.cons_bvar (.vlam _)) ⟨hΔ', nofun, h2'⟩)

theorem instL (henv : env.WF) {Us' ps : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us') = some ls') (eq : ps.length = ls.length)
    {Δ : VLCtx} (hΔ : VLCtx.WF env ls'.length Δ) {r : Expr} (H : TeleDoms env ps Δ r)
    {Δ₂ : VLCtx} (hΔ₂ : VLCtx.IsDefEq env Us'.length (Δ.instL ls') Δ₂) :
    TeleDoms env Us' Δ₂ (r.instantiateLevelParams ps ls) := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  have eq' := eq.trans (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 Hls))
  induction H generalizing Δ₂ with
  | @nil _ r h1 h2 h3 =>
    rw [Expr.instantiateLevelParams_eq]
    refine .nil (fun n d b bi h => ?_) (fun i h => ?_) (fun x h => ?_) <;> cases r <;>
      simp [Expr.instantiateLevelParamsCore'] at h
    · exact h1 _ _ _ _ rfl
    · exact h2 _ rfl
    · exact h3 _ rfl
  | @cons Δ dom b A n bi h1 h2 _ ih =>
    rw [Expr.instantiateLevelParams_forallE]
    obtain ⟨A₁, s1, d1⟩ := h1.instL henv hΔ Hls eq
    obtain ⟨A₂, s2, d2⟩ := s1.defeqDFC' henv hΔ₂
    have hΓ := (hΔ.instL Hls').toCtx
    obtain ⟨u, hu⟩ : env.IsType Us'.length (Δ.instL ls').toCtx (A.instL ls') :=
      VLCtx.instL_toCtx _ ▸ h2.instL Hls'
    have d2' := d2.defeqDFC henv.ordered (hΔ₂.defeqCtx.symm henv.ordered)
    have e1 : env.IsDefEq Us'.length (Δ.instL ls').toCtx (A.instL ls') A₂ (.sort u) :=
      (d1.symm.trans henv hΓ d2'.symm).of_l henv hΓ hu
    have e2 := e1.defeqDFC henv.ordered hΔ₂.defeqCtx
    exact .cons s2 ⟨_, e2.hasType.2⟩
      (ih ⟨hΔ, nofun, eq' ▸ h2⟩ (.cons hΔ₂ nofun (.vlam e1)))

theorem abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) {r : Expr}
    (H : TeleDoms env Us Δ₁ r) : TeleDoms env Us Δ (r.abstract1 v₀ dk) := by
  induction H generalizing Δ dk k with
  | @nil _ r h1 h2 h3 =>
    refine .nil (fun n d b bi h => ?_) (fun i h => ?_) (fun x h => ?_)
    · cases r with
      | forallE => exact h1 _ _ _ _ rfl
      | fvar y => simp only [Expr.abstract1] at h; split at h <;> cases h
      | _ => simp [Expr.abstract1] at h
    · cases r with
      | bvar j => exact h2 j rfl
      | fvar y => exact h3 y rfl
      | _ => simp [Expr.abstract1] at h
    · cases r with
      | fvar y => exact h3 y rfl
      | bvar j => exact h2 j rfl
      | _ => simp [Expr.abstract1] at h
  | cons h1 h2 _ ih =>
    exact .cons (h1.abstract W) (W.toCtx ▸ h2) (ih (W.succ (d := .vlam _)))

theorem defeqDFC (henv : env.WF) {Δ₁ : VLCtx} {r : Expr} (H : TeleDoms env Us Δ₁ r) :
    ∀ {Δ₂ : VLCtx}, VLCtx.IsDefEq env Us.length Δ₁ Δ₂ → TeleDoms env Us Δ₂ r := by
  induction H with
  | nil h1 h2 h3 => intros; exact .nil h1 h2 h3
  | @cons Δ dom b A n bi h1 h2 _ ih =>
    intro Δ₂ hΔ
    obtain ⟨A₂, s2, d2⟩ := h1.defeqDFC' henv hΔ
    have hΓ := hΔ.wf.toCtx
    obtain ⟨u, hu⟩ := h2
    have d2' := d2.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)
    have e1 : env.IsDefEq Us.length Δ.toCtx A A₂ (.sort u) := d2'.symm.of_l henv hΓ hu
    have e2 := e1.defeqDFC henv.ordered hΔ.defeqCtx
    exact .cons s2 ⟨_, e2.hasType.2⟩ (ih (.cons hΔ nofun (.vlam e1)))

end TeleDoms

/-- What `addInductive`'s checks of a constructor's fields give `inferProj`'s walk down its type `t`,
with `np` parameters and `nf` fields: with any of the first fields that the rest does not mention
dropped, the telescope's domains translate. -/
def CtorDoms (env : VEnv) (Us : List Name) (np nf : Nat) (t : Expr) : Prop :=
  ∀ m ≤ nf, TeleDoms env Us [] (Expr.dropAfter np m t)

theorem CtorDoms.mono {env env' : VEnv} (henv : env ≤ env') {Us : List Name} {np nf : Nat}
    {t : Expr} (H : CtorDoms env Us np nf t) : CtorDoms env' Us np nf t :=
  fun m hm => (H m hm).mono henv

end Lean4Lean

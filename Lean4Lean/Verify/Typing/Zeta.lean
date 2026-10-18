import Lean4Lean.Verify.Typing.Lemmas

/-! `Expr.zeta` translates as the term does, a term without `let`s mentions only the free
variables its translation mentions, and stripping a term's annotations strips as many off its
translation, a count that opening binders keeps. -/

namespace Lean.Expr

theorem anySub_isLet_liftLooseBVars' {e : Expr} (h : e.anySub (·.isLet) = false) (s d) :
    (e.liftLooseBVars' s d).anySub (·.isLet) = false := by
  induction e generalizing s <;>
    simp_all [Expr.anySub, liftLooseBVars', Expr.isLet]

theorem anySub_isLet_instantiate1' {e a : Expr} (h : e.anySub (·.isLet) = false)
    (ha : a.anySub (·.isLet) = false) (d) : (e.instantiate1' a d).anySub (·.isLet) = false := by
  induction e generalizing d with
  | bvar i =>
    simp only [instantiate1']; split
    · rfl
    · split
      · exact anySub_isLet_liftLooseBVars' ha _ _
      · rfl
  | _ => simp_all [Expr.anySub, instantiate1', Expr.isLet]

theorem anySub_isLet_zeta (e : Expr) : e.zeta.anySub (·.isLet) = false := by
  induction e with
  | letE _ _ v b _ _ ihv ihb =>
    simp only [zeta, instantiate1_eq]; exact anySub_isLet_instantiate1' ihb ihv _
  | _ => simp_all [Expr.anySub, zeta, Expr.isLet]

theorem zeta_of_noLet {e : Expr} (h : e.anySub (·.isLet) = false) : e.zeta = e := by
  induction e <;> simp_all [Expr.anySub, zeta, Expr.isLet]

end Lean.Expr

namespace Lean4Lean
open Lean

variable {env : VEnv} {Us : List Name}

theorem TrExprS.zeta (henv : VEnv.Ordered env) {Δ e e'} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ e.zeta e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app h1 h2 ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam h1 ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE h1 h2 ih1 ih2
  | letE _ _ _ _ _ ih2 ih3 =>
    simp only [Expr.zeta, Expr.instantiate1_eq]; exact ih3.inst_let henv ih2
  | lit h1 h2 => exact .lit h1 h2
  | mdata _ ih => exact .mdata ih
  | proj _ h2 ih => exact .proj ih h2

theorem VExpr.skips'_liftN_one {n : Nat} {e : VExpr} : ∀ {j k : Nat}, j ≤ k →
    (e.liftN 1 j).Skips' n (k + 1) → e.Skips' n k := by
  induction e with
  | bvar i =>
    intro j k hj h
    simp only [VExpr.liftN, VExpr.Skips'] at h ⊢
    unfold liftVar at h; split at h <;> omega
  | sort | const => intros; trivial
  | app f a ih1 ih2 => intro j k hj h; exact ⟨ih1 hj h.1, ih2 hj h.2⟩
  | lam t b ih1 ih2 | forallE t b ih1 ih2 =>
    intro j k hj h; exact ⟨ih1 hj h.1, ih2 (Nat.succ_le_succ hj) h.2⟩
  | proj _ _ e ih => intro j k hj h; exact ih hj h

/-- A term without `let`s mentions a free variable only where its translation mentions the
variable's value: skipping bound variables in the translation skips them in the value of every
free variable the term mentions. -/
theorem TrExprS.fvars_skips {Δ e e'} (H : TrExprS env Us Δ e e')
    (hl : e.anySub (·.isLet) = false) {n k : Nat} (hs : e'.Skips' n k) :
    ∀ fv ∈ e.fvarsList, ∃ v A, Δ.find? (.inr fv) = some (v, A) ∧ v.Skips' n k := by
  induction H generalizing k with
  | bvar | sort | const | lit => intro fv h; simp [Expr.fvarsList] at h
  | fvar h =>
    intro fv hf; simp [Expr.fvarsList] at hf; subst hf; exact ⟨_, _, h, hs⟩
  | app _ _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Expr.isLet, Bool.false_or, Bool.or_eq_false_iff] at hl
    intro fv hf; simp only [Expr.fvarsList, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ih1 hl.1 hs.1 fv hf
    · exact ih2 hl.2 hs.2 fv hf
  | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Expr.isLet, Bool.false_or, Bool.or_eq_false_iff] at hl
    intro fv hf; simp only [Expr.fvarsList, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ih1 hl.1 hs.1 fv hf
    · obtain ⟨v, A, h1, h2⟩ := ih2 hl.2 hs.2 fv hf
      simp only [VLCtx.find?, VLCtx.next] at h1
      obtain ⟨⟨v', A'⟩, h3, h4⟩ := Option.bind_eq_some_iff.1 h1
      cases h4
      exact ⟨v', A', h3, VExpr.skips'_liftN_one (Nat.zero_le _) h2⟩
  | letE => simp [Expr.anySub, Expr.isLet] at hl
  | mdata _ ih =>
    simp only [Expr.anySub, Expr.isLet, Bool.false_or] at hl
    intro fv hf; exact ih hl hs fv (by simpa [Expr.fvarsList] using hf)
  | proj _ _ ih =>
    simp only [Expr.anySub, Expr.isLet, Bool.false_or] at hl
    intro fv hf; exact ih hl hs fv (by simpa [Expr.fvarsList] using hf)

end Lean4Lean
namespace Lean.Expr

/-- How many annotations `consumeTypeAnnotations'` strips from the head of `e`. -/
def annStrips : Expr → Nat
  | .app (.app (.const ``optParam _) A) _ => A.annStrips + 1
  | .app (.app (.const ``autoParam _) A) _ => A.annStrips + 1
  | .app (.const ``outParam _) A => A.annStrips + 1
  | .app (.const ``semiOutParam _) A => A.annStrips + 1
  | _ => 0

/-- The number of annotations stripped from each binder domain of a telescope. -/
def domStrips : Expr → List Nat
  | .forallE _ d b _ => d.annStrips :: b.domStrips
  | _ => []

theorem instantiate1'_fvar_app {x : FVarId} {d : Nat} {f b : Expr} : ∀ {e : Expr},
    e.instantiate1' (.fvar x) d = .app f b →
      ∃ f' b', e = .app f' b' ∧ f'.instantiate1' (.fvar x) d = f ∧
        b'.instantiate1' (.fvar x) d = b
  | .bvar i, h => by
    simp only [instantiate1'] at h; split at h <;> [cases h; (split at h <;> simp [liftLooseBVars'] at h)]
  | .app .., h => by simp only [instantiate1'] at h; cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  | .mdata .., h | .proj .., h | .lam .., h | .forallE .., h | .letE .., h => by
    simp [instantiate1'] at h
  | .const .., h | .sort _, h | .fvar _, h | .mvar _, h | .lit _, h => by simp [instantiate1'] at h

theorem instantiate1'_fvar_const {x : FVarId} {d : Nat} {c : Name} {ls : List Level} :
    ∀ {e : Expr}, e.instantiate1' (.fvar x) d = .const c ls → e = .const c ls
  | .bvar i, h => by
    simp only [instantiate1'] at h; split at h <;> [cases h; (split at h <;> simp [liftLooseBVars'] at h)]
  | .const .., h => by simpa [instantiate1'] using h
  | .app .., h | .mdata .., h | .proj .., h | .lam .., h | .forallE .., h | .letE .., h => by
    simp [instantiate1'] at h
  | .sort _, h | .fvar _, h | .mvar _, h | .lit _, h => by simp [instantiate1'] at h

theorem annStrips_instantiate1' {x : FVarId} : ∀ {e : Expr} {d : Nat},
    (e.instantiate1' (.fvar x) d).annStrips = e.annStrips := by
  intro e
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    intro d; simp [instantiate1', annStrips, ih]
  | case5 e h1 h2 h3 h4 =>
    intro d
    rw [annStrips.eq_5 e h1 h2 h3 h4]
    generalize he' : e.instantiate1' (.fvar x) d = e'
    unfold annStrips
    split <;> try rfl
    all_goals exfalso
    · obtain ⟨f, b, rfl, hf, -⟩ := instantiate1'_fvar_app he'
      obtain ⟨g, a, rfl, hg, -⟩ := instantiate1'_fvar_app hf
      cases instantiate1'_fvar_const hg; exact h1 _ _ _ rfl
    · obtain ⟨f, b, rfl, hf, -⟩ := instantiate1'_fvar_app he'
      obtain ⟨g, a, rfl, hg, -⟩ := instantiate1'_fvar_app hf
      cases instantiate1'_fvar_const hg; exact h2 _ _ _ rfl
    · obtain ⟨f, b, rfl, hf, -⟩ := instantiate1'_fvar_app he'
      cases instantiate1'_fvar_const hf; exact h3 _ _ rfl
    · obtain ⟨f, b, rfl, hf, -⟩ := instantiate1'_fvar_app he'
      cases instantiate1'_fvar_const hf; exact h4 _ _ rfl

theorem domStrips_instantiate1' {x : FVarId} : ∀ {e : Expr} {d : Nat},
    (e.instantiate1' (.fvar x) d).domStrips = e.domStrips
  | .forallE .., _ => by simp [instantiate1', domStrips, annStrips_instantiate1',
      domStrips_instantiate1']
  | .bvar i, d => by
    simp only [instantiate1']; split <;> [rfl; (split <;> simp [liftLooseBVars', domStrips])]
  | .app .., _ | .mdata .., _ | .proj .., _ | .lam .., _ | .letE .., _
  | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => by
    simp [instantiate1', domStrips]

end Lean.Expr

namespace Lean4Lean

/-- Peel `n` annotations, as `consumeTypeAnnotations'` does, off a translation's head. -/
def VExpr.stripN : Nat → VExpr → VExpr
  | n + 1, .app (.app (.const c ls) A) v =>
    if c = ``optParam ∨ c = ``autoParam then A.stripN n else .app (.app (.const c ls) A) v
  | n + 1, .app (.const c ls) A =>
    if c = ``outParam ∨ c = ``semiOutParam then A.stripN n else .app (.const c ls) A
  | _, e => e

variable {env : VEnv} {Us : List Name}

/-- Stripping annotations off a term strips them off its translation. -/
theorem TrExprS.consumeTypeAnnotations'_stripN {Δ : VLCtx} {e : Lean.Expr} {E : VExpr}
    (H : TrExprS env Us Δ e E) : TrExprS env Us Δ e.consumeTypeAnnotations'
      (E.stripN e.annStrips) := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct generalizing E with
  | case1 _ A _ ih | case2 _ A _ ih =>
    cases H with | app _ _ hf _ => cases hf with | app _ _ hc hA => cases hc with | const =>
    simpa [Lean.Expr.consumeTypeAnnotations', Lean.Expr.annStrips, VExpr.stripN] using ih hA
  | case3 _ A ih | case4 _ A ih =>
    cases H with | app _ _ hc hA => cases hc with | const =>
    simpa [Lean.Expr.consumeTypeAnnotations', Lean.Expr.annStrips, VExpr.stripN] using ih hA
  | case5 e h1 h2 h3 h4 =>
    rw [Lean.Expr.consumeTypeAnnotations'.eq_5 e h1 h2 h3 h4, Lean.Expr.annStrips.eq_5 e h1 h2 h3 h4]
    exact H

end Lean4Lean

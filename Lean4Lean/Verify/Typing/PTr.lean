import Lean4Lean.Verify.Typing.Lemmas

/-!
# Translations without typing

`PTr` is the translation `TrExprS` computes without its typing side conditions. It is unique
(`PTr.unique`), and where a `let`-free term's translation is typed it is `TrExprS`
(`PTr.toTrExprS`).
-/

namespace Lean4Lean
open Lean

/-- The translation `TrExprS` computes, without its typing side conditions; `CL` says which
literals translate. -/
inductive PTr (Us : List Name) (CL : Literal → Prop) : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → PTr Us CL Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → PTr Us CL Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → PTr Us CL Δ (.sort u) (.sort u')
  | const : us.mapM (VLevel.ofLevel Us) = some us' → PTr Us CL Δ (.const c us) (.const c us')
  | app : PTr Us CL Δ f f' → PTr Us CL Δ a a' → PTr Us CL Δ (.app f a) (.app f' a')
  | lam : PTr Us CL Δ ty ty' → PTr Us CL ((none, .vlam ty') :: Δ) body body' →
    PTr Us CL Δ (.lam name ty body bi) (.lam ty' body')
  | forallE : PTr Us CL Δ ty ty' → PTr Us CL ((none, .vlam ty') :: Δ) body body' →
    PTr Us CL Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE : PTr Us CL Δ ty ty' → PTr Us CL Δ val val' →
    PTr Us CL ((none, .vlet ty' val') :: Δ) body body' →
    PTr Us CL Δ (.letE name ty val body nd) body'
  | lit : CL l → PTr Us CL Δ l.toConstructor e → PTr Us CL Δ (.lit l) e
  | mdata : PTr Us CL Δ e e' → PTr Us CL Δ (.mdata d e) e'
  | proj : PTr Us CL Δ e e' → PTr Us CL Δ (.proj s i e) (.proj s i e')

theorem TrExprS.toPTr {env : VEnv} (H : TrExprS env Us Δ e e') :
    PTr Us env.ContainsLits Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const _ h => exact .const h
  | app _ _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit h _ ih => exact .lit h ih
  | mdata _ ih => exact .mdata ih
  | proj _ _ ih => exact .proj ih

theorem PTr.mono_lit {CL CL' : Literal → Prop} (h : ∀ l, CL l → CL' l)
    (H : PTr Us CL Δ e e') : PTr Us CL' Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit hl _ ih => exact .lit (h _ hl) ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- A term has at most one translation in a context. -/
theorem PTr.unique {CL CL' : Literal → Prop} (H1 : PTr Us CL Δ e e₁) (H2 : PTr Us CL' Δ e e₂) :
    e₁ = e₂ := by
  induction H1 generalizing e₂ with cases H2
  | bvar h1 | fvar h1 => cases h1.symm.trans ‹_›; rfl
  | sort h1 => cases h1.symm.trans ‹_›; rfl
  | const h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ ih1 ih2 => cases ih1 ‹_›; cases ih2 ‹_›; rfl
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => cases ih1 ‹_›; cases ih2 ‹_›; rfl
  | letE _ _ _ ih1 ih2 ih3 => cases ih1 ‹_›; cases ih2 ‹_›; exact ih3 ‹_›
  | lit _ _ ih => exact ih ‹_›
  | mdata _ ih => exact ih ‹_›
  | proj _ ih => cases ih ‹_›; rfl

/-- `e` has no `let`. -/
def _root_.Lean.Expr.LetFree : Expr → Prop
  | .letE .. | .mvar _ => False
  | .app f a | .lam _ f a _ | .forallE _ f a _ => f.LetFree ∧ a.LetFree
  | .mdata _ e | .proj _ _ e => e.LetFree
  | .bvar _ | .fvar _ | .sort _ | .const .. | .lit _ => True

theorem _root_.Lean.Literal.toConstructor_letFree {l : Literal} : l.toConstructor.LetFree := by
  cases l with
  | natVal n => cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.LetFree,
      Expr.natZero, Expr.natSucc]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor, Expr.LetFree, true_and]
    induction s.toList <;> simp_all [Expr.LetFree]

/-- Where its translation is typed, a `let`-free term's plain translation is its translation. -/
theorem PTr.toTrExprS {env : VEnv} (henv : env.Ordered) {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, PTr Us env.ContainsLits Δ e e' → e.LetFree →
      OnCtx Δ.toCtx (env.IsType Us.length) → e'.WF env Us.length Δ.toCtx →
      TrExprS env Us Δ e e'
  | _, _, _, .bvar h, _, _, _ => .bvar h
  | _, _, _, .fvar h, _, _, _ => .fvar h
  | _, _, _, .sort h, _, _, _ => .sort h
  | _, _, _, .const h, _, hΓ, hwf => by
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΓ
    exact .const hci h (by rw [← hlen, Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 h)])
  | _, _, _, .app hf ha, hl, hΓ, hwf => by
    obtain ⟨A, B, hf', ha'⟩ := hwf.app_inv henv hΓ
    exact .app hf' ha' (hf.toTrExprS henv hl.1 hΓ ⟨_, hf'⟩) (ha.toTrExprS henv hl.2 hΓ ⟨_, ha'⟩)
  | _, _, _, .lam hA hb, hl, hΓ, hwf => by
    obtain ⟨hA', hb'⟩ := hwf.lam_inv henv hΓ
    exact .lam hA' (hA.toTrExprS henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hb.toTrExprS henv hl.2 ⟨hΓ, hA'⟩ hb')
  | _, _, _, .forallE hA hB, hl, hΓ, ⟨_, hT⟩ => by
    obtain ⟨hA', hB'⟩ := VEnv.HasType.forallE_inv henv hT
    exact .forallE hA' hB' (hA.toTrExprS henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hB.toTrExprS henv hl.2 ⟨hΓ, hA'⟩ (let ⟨_, h⟩ := hB'; ⟨_, h⟩))
  | _, _, _, .letE .., hl, _, _ => hl.elim
  | _, .lit l, _, .lit hc h, _, hΓ, hwf =>
    .lit hc (h.toTrExprS henv Literal.toConstructor_letFree hΓ hwf)
  | _, _, _, .mdata h, hl, hΓ, hwf => .mdata (h.toTrExprS henv hl hΓ hwf)
  | _, _, _, .proj h, hl, hΓ, hwf => by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hT, -⟩ := hwf.proj_inv henv hΓ
    exact .proj (h.toTrExprS henv hl hΓ ⟨_, hT⟩) hwf

/-! ### Weakening and instantiating plain translations -/

theorem PTr.weakBV (W : VLCtx.BVLift Δ Δ' dn dk n k) (H : PTr Us CL Δ e e') :
    PTr Us CL Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.cons _))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.cons _))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.cons _))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)


/-- A plain translation of a lift is the lift of one: the variables a lift skips are never read. -/
theorem PTr.weakBV_inv {CL : Literal → Prop} (W : VLCtx.BVLift Δ Δ' dn dk n k) {e₂ : Expr}
    {E : VExpr} (H : PTr Us CL Δ' e₂ E) {e : Expr} (he : e₂ = e.liftLooseBVars' dk dn) :
    ∃ E₀ : VExpr, PTr Us CL Δ e E₀ ∧ E = E₀.liftN n k := by
  induction H generalizing Δ dk k e with
  | bvar h1 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he; subst he
    rename_i i
    have : (Sum.inl (if i < dk then i else i + dn) : Nat ⊕ FVarId) =
      VLCtx.liftVar dn dk (.inl i) := rfl
    rw [this] at h1
    obtain ⟨e₀, _, h, rfl, -⟩ := W.find?_inv h1
    exact ⟨_, .bvar h, rfl⟩
  | fvar h1 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he; subst he
    rename_i fv
    obtain ⟨e₀, _, h, rfl, -⟩ := W.find?_inv (v := .inr fv) h1
    exact ⟨_, .fvar h, rfl⟩
  | sort h =>
    cases e <;> simp [Expr.liftLooseBVars'] at he; subst he
    exact ⟨VExpr.sort _, .sort h, rfl⟩
  | const h =>
    cases e <;> simp [Expr.liftLooseBVars'] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨VExpr.const _ _, .const h, rfl⟩
  | app _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f₀, h1, rfl⟩ := ih1 W rfl
    obtain ⟨a₀, h2, rfl⟩ := ih2 W rfl
    exact ⟨VExpr.app f₀ a₀, .app h1 h2, rfl⟩
  | lam _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, h1, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, h2, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨VExpr.lam t₀ b₀, .lam h1 h2, rfl⟩
  | forallE _ _ ih1 ih2 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, h1, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, h2, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨VExpr.forallE t₀ b₀, .forallE h1 h2, rfl⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, h1, rfl⟩ := ih1 W rfl
    obtain ⟨v₀, h2, rfl⟩ := ih2 W rfl
    obtain ⟨b₀, h3, rfl⟩ := ih3 (W.cons (.vlet t₀ v₀)) rfl
    exact ⟨b₀, .letE h1 h2 h3, rfl⟩
  | lit hl _ ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he; subst he
    obtain ⟨E₀, h, rfl⟩ :=
      ih W (Expr.liftLooseBVars_eq_self Closed.toConstructor.looseBVarRange_le).symm
    exact ⟨E₀, .lit hl h, rfl⟩
  | mdata _ ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨E₀, h, rfl⟩ := ih W rfl
    exact ⟨E₀, .mdata h, rfl⟩
  | proj _ ih =>
    cases e <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨e₀, h, rfl⟩ := ih W rfl
    exact ⟨VExpr.proj _ _ e₀, .proj h, rfl⟩

/-- A term with no loose bound variables, plainly translated under a binder, translates without
it, to what lifts to its translation. -/
theorem PTr.skips_of_closed {CL : Literal → Prop} {A : VExpr}
    (H : PTr Us CL ((none, .vlam A) :: Δ) e E) (he : e.looseBVarRange' = 0) :
    ∃ E₀ : VExpr, PTr Us CL Δ e E₀ ∧ E = E₀.liftN 1 := by
  have W : VLCtx.BVLift Δ ((none, .vlam A) :: Δ) 1 0 1 0 := .skip (.vlam A) .refl
  exact H.weakBV_inv W (Expr.liftLooseBVars_eq_self (by omega)).symm

theorem PTr.instN_var {CL : Literal → Prop} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr}
    (h₀ : PTr Us CL Δ₀ e₀ e₀') (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : Δ₁.find? v = some (e', A)) :
    PTr Us CL Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value, VExpr.inst]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV (.skip (d.inst e₀' k) .refl)
        cases d <;> simpa [← VExpr.lift_instN_lo, VExpr.liftN_zero,
          VLocalDecl.inst, VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]

theorem PTr.instN {CL : Literal → Prop} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr}
    (h₀ : PTr Us CL Δ₀ e₀ e₀') (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : PTr Us CL Δ₁ e e') : PTr Us CL Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact h₀.instN_var W h1
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem PTr.inst {CL : Literal → Prop} {A₀ : VExpr} (h₀ : PTr Us CL Δ e₀ e₀')
    (H : PTr Us CL ((none, .vlam A₀) :: Δ) e e') :
    PTr Us CL Δ (Expr.instantiate1' e e₀) (e'.inst e₀') :=
  h₀.instN .zero H

end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.TyEq
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Projection

/-!
# Uniqueness of typing from chain inversion

Two typings of a term have types joined by a chain of equalities at sorts (`TyEq`), given that
chains invert at sorts, pi types and projections' types (`ChainInv`). Unlike the stratified proof
of `IsDefEq.uniq`, chains compose without knowing their sorts agree, so the induction is on the
syntax-directed typing (`HasTypeStrong`) alone. Once chains of sorts invert, universes are unique,
a chain collapses to one equality (`TyEq.collapse`), and the environment has `VEnv.Inj`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat}

/-- Two projections of the same term at chain-related inductive types have chain-related
types. -/
def ProjChain (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ s d t T c k f ls ls' As As' I I' e u u'}, OnCtx Γ (env.IsType U) →
    env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f →
    (∀ l ∈ ls, l.WF U) → ls.length = d.uvars → (∀ l ∈ ls', l.WF U) → ls'.length = d.uvars →
    As.length = d.params.length → I.length = T.indices.length →
    As'.length = d.params.length → I'.length = T.indices.length →
    d.ProjAllowed c ls k → d.ProjAllowed c ls' k →
    env.HasType U Γ (.appN (.const s ls) (As ++ I)) (.sort u) →
    env.HasType U Γ (.appN (.const s ls') (As' ++ I')) (.sort u') →
    env.HasType U Γ e (.appN (.const s ls) (As ++ I)) →
    env.HasType U Γ (c.projType ls s k As e) (.sort (f.level.inst ls)) →
    env.HasType U Γ (c.projType ls' s k As' e) (.sort (f.level.inst ls')) →
    TyEq env U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls') (As' ++ I')) →
    TyEq env U Γ (c.projType ls s k As e) (c.projType ls' s k As' e)

/-- What uniqueness of typing needs of chains in an environment: a chain of sorts relates
equivalent levels, a chain of pi types relates domains and codomains by chains, and two
projections of the same term at chain-related inductive types have chain-related types. -/
structure ChainInv (env : VEnv) (U : Nat) : Prop where
  sort : ∀ {Γ u v}, OnCtx Γ (env.IsType U) → TyEq env U Γ (.sort u) (.sort v) → u ≈ v
  forallE : ∀ {Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    TyEq env U Γ (.forallE A B) (.forallE A' B') →
    TyEq env U Γ A A' ∧ TyEq env U (A::Γ) B B'
  proj : ProjChain env U

theorem TyEq.of_isType {Γ : List VExpr} {A : VExpr} (h : env.IsType U Γ A) :
    TyEq env U Γ A A := let ⟨_, h⟩ := h; .base h

/-- A typing at a type, unfolded to a syntax-directed one at a type the chain joins it to. -/
theorem _root_.Lean4Lean.VEnv.HasTypeStrong.toStructural (henv : env.Ordered) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {e A : VExpr} {b : Bool}
    (H : env.HasTypeStrong U Γ e A b) :
    ∃ A', env.HasTypeStrong U Γ e A' false ∧ TyEq env U Γ A' A := by
  cases b
  · exact ⟨_, H, TyEq.of_isType (H.hasType.isType henv hΓ)⟩
  generalize hb : true = b at H
  induction H with cases hb
  | base h => exact ⟨_, h, TyEq.of_isType (h.hasType.isType henv hΓ)⟩
  | defeq _ h2 _ _ _ _ _ ih => obtain ⟨_, h, c⟩ := ih hΓ rfl; exact ⟨_, h, c.trans (.base h2.defeq)⟩

/-- Uniqueness of typing up to a chain, given chain inversion. -/
theorem _root_.Lean4Lean.VEnv.HasTypeStrong.uniqChain (henv : env.Ordered) (hC : ChainInv env U)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {e A B : VExpr} {b₁ b₂ : Bool}
    (H1 : env.HasTypeStrong U Γ e A b₁) (H2 : env.HasTypeStrong U Γ e B b₂) :
    TyEq env U Γ A B := by
  induction H1 generalizing B b₂ with
  | bvar a1 _ a3 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .bvar b1 _ _ := H2; cases a1.uniq b1
    exact (TyEq.base a3.hasType).trans t
  | sort' a1 a2 a3 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .sort' _ b2 b3 := H2
    exact (TyEq.base (VEnv.IsDefEq.sortDF (l := .succ _) (l' := .succ _) a2 b2
      (VLevel.succ_congr (a3.symm.trans b3)))).trans t
  | const a1 _ _ _ _ a6 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .const b1 _ _ _ _ _ := H2; cases a1.symm.trans b1
    exact (TyEq.base a6.hasType).trans t
  | app _ _ a3 _ _ _ a7 _ _ _ _ ih5 ih6 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .app _ _ _ _ _ b6 _ _ := H2
    obtain ⟨-, hB⟩ := hC.forallE hΓ (ih5 hΓ b6)
    exact (hB.inst henv a7.hasType).trans t
  | lam _ _ a3 _ _ _ _ _ ih3 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .lam _ _ _ _ b5 _ := H2
    have hB := ih3 ⟨hΓ, _, a3.hasType⟩ b5
    exact (TyEq.forallE henv (.base a3.hasType) hB).trans t
  | forallE a1 a2 a3 _ ih1 ih2 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .forallE b1 b2 b3 b4 := H2
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, a3.hasType⟩
    have e1 := hC.sort hΓ (ih1 hΓ b3)
    have e2 := hC.sort hΓ' (ih2 hΓ' b4)
    exact (TyEq.base (VEnv.IsDefEq.sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩ (VLevel.imax_congr e1 e2))).trans t
  | proj a1 a2 a3 a4 a5 a6 a7 a8 _ _ a11 a12 a13 a14 _ ih2 =>
    obtain ⟨_, H2, t⟩ := H2.toStructural henv hΓ
    let .proj b1 b2 b3 b4 b5 b6 b7 b8 _ _ b11 b12 b13 b14 := H2
    cases a1.symm.trans b1; cases a2.symm.trans b2
    cases (List.cons.inj (a3.symm.trans b3)).1; cases a4.symm.trans b4
    exact (hC.proj hΓ a1 a2 a3 a4 a5 a6 b5 b6 a7 a8 b7 b8 a11 b11 a12.hasType b12.hasType
      a13.hasType a14.hasType b14.hasType (ih2 hΓ b13)).trans t
  | base _ ih => exact ih hΓ H2
  | defeq _ a2 _ _ _ _ _ ih => exact (TyEq.base a2.defeq).symm.trans (ih hΓ H2)

theorem uniqChain (henv : env.Ordered) (hC : ChainInv env U) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {e₁ e₂ e₃ A B : VExpr} (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    TyEq env U Γ A B :=
  (h1.strong henv hΓ).hasType'.2.uniqChain henv hC hΓ (h2.strong henv hΓ).hasType'.1

/-- A type's universe is unique. -/
theorem sort_uniq (henv : env.Ordered) (hC : ChainInv env U) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {X : VExpr} {u v : VLevel} (h1 : env.HasType U Γ X (.sort u))
    (h2 : env.HasType U Γ X (.sort v)) :
    env.IsDefEq U Γ (.sort v) (.sort u) (.sort (.succ v)) := by
  have e := hC.sort hΓ (uniqChain henv hC hΓ h1 h2)
  exact .sortDF ((h2.isType henv hΓ).sort_inv henv) ((h1.isType henv hΓ).sort_inv henv) e.symm

end LogRel
end Lean4Lean

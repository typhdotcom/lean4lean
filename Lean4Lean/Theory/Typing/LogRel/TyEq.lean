import Lean4Lean.Theory.Typing.Lemmas

/-!
# Type equality as a chain

`TyEq env U Γ A B`: `A` and `B` are joined by a chain of definitional equalities, each at some
sort. The logical relation records equalities of types this way: composing two of them needs
no agreement of their sorts, which `VEnv.IsDefEq.trans` would need and which only uniqueness of
typing provides. A chain still converts typings and contexts link by link (`TyEq.defeqDF`,
`TyEq.defeqDF_l`) and is closed under pi congruence (`TyEq.forallE`). Once universes are known to
be unique (`TyEq.collapse`), a chain is a single equality.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- `A` and `B` are joined by definitional equalities at sorts. -/
inductive TyEq : VExpr → VExpr → Prop where
  | base : env.IsDefEq U Γ A B (.sort u) → TyEq A B
  | trans : TyEq A B → TyEq B C → TyEq A C

end

namespace TyEq
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem symm (H : TyEq env U Γ A B) : TyEq env U Γ B A := by
  induction H with
  | base h => exact .base h.symm
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem refl (h : env.HasType U Γ A (.sort u)) : TyEq env U Γ A A := .base h

/-- The left end of a chain is a type. -/
theorem isType_l (H : TyEq env U Γ A B) : env.IsType U Γ A := by
  induction H with
  | base h => exact ⟨_, h.hasType.1⟩
  | trans _ _ ih => exact ih

theorem isType_r (H : TyEq env U Γ A B) : env.IsType U Γ B := H.symm.isType_l

/-- A chain converts a typing, link by link. -/
theorem defeqDF (H : TyEq env U Γ A B) (h : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ B := by
  induction H generalizing e₁ e₂ with
  | base hA => exact hA.defeqDF h
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)

/-- A chain converts the type of a context's last variable, link by link. -/
theorem defeqDF_l (henv : env.Ordered) (H : TyEq env U Γ A A')
    (h : env.IsDefEq U (A::Γ) e₁ e₂ B) : env.IsDefEq U (A'::Γ) e₁ e₂ B := by
  induction H generalizing e₁ e₂ B with
  | base hA => exact hA.defeqDF_l henv h
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)

/-- A chain of types under a variable converts along a chain of its type. -/
theorem ctx (henv : env.Ordered) (HA : TyEq env U Γ A A') (H : TyEq env U (A::Γ) B B') :
    TyEq env U (A'::Γ) B B' := by
  induction H with
  | base h => exact .base (HA.defeqDF_l henv h)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Pi congruence of chains: first the domain, at the body, then the body, at the new domain. -/
theorem forallE (henv : env.Ordered) (HA : TyEq env U Γ A A') (HB : TyEq env U (A::Γ) B B') :
    TyEq env U Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨v, hB⟩ := HB.isType_l
  have dom : ∀ {A₁ A₂}, TyEq env U Γ A₁ A₂ → env.HasType U (A₁::Γ) B (.sort v) →
      TyEq env U Γ (.forallE A₁ B) (.forallE A₂ B) ∧ env.HasType U (A₂::Γ) B (.sort v) := by
    intro A₁ A₂ H hB
    induction H with
    | base h => exact ⟨.base (.forallEDF h hB), h.defeqDF_l henv hB⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨h1, hB'⟩ := ih1 hB
      obtain ⟨h2, hB''⟩ := ih2 hB'
      exact ⟨.trans h1 h2, hB''⟩
  obtain ⟨h1, -⟩ := dom HA hB
  obtain ⟨u, hA'⟩ := HA.isType_r
  have body : ∀ {B₁ B₂}, TyEq env U (A'::Γ) B₁ B₂ →
      TyEq env U Γ (.forallE A' B₁) (.forallE A' B₂) := by
    intro B₁ B₂ H
    induction H with
    | base h => exact .base (.forallEDF hA' h)
    | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  exact .trans h1 (body (ctx henv HA HB))

/-- A chain of types under a variable, instantiated at a term of the variable's type. -/
theorem inst (henv : env.Ordered) (ha : env.HasType U Γ a A) (H : TyEq env U (A::Γ) B B') :
    TyEq env U Γ (B.inst a) (B'.inst a) := by
  induction H with
  | base h => exact .base (h.instN henv ha .zero : env.IsDefEq U Γ _ _ ((VExpr.sort _).inst a))
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Given that a type's universe is unique up to definitional equality, a chain is one equality. -/
theorem collapse
    (huniq : ∀ {X u v}, env.HasType U Γ X (.sort u) → env.HasType U Γ X (.sort v) →
      env.IsDefEq U Γ (.sort v) (.sort u) (.sort (.succ v)))
    (H : TyEq env U Γ A B) : ∃ u, env.IsDefEq U Γ A B (.sort u) := by
  induction H with
  | base h => exact ⟨_, h⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨u, h1⟩ := ih1; obtain ⟨v, h2⟩ := ih2
    exact ⟨u, h1.trans ((huniq h1.hasType.2 h2.hasType.1).defeqDF h2)⟩

end TyEq

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- `a` and `b` are joined by definitional equalities, each at some type. The logical relation
records the arguments of related inductive type applications this way; the equalities at the
argument types follow once typing is unique. -/
inductive TmEq : VExpr → VExpr → Prop where
  | base : env.IsDefEq U Γ a b A → TmEq a b
  | trans : TmEq a b → TmEq b c → TmEq a c

end

namespace TmEq
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem symm (H : TmEq env U Γ a b) : TmEq env U Γ b a := by
  induction H with
  | base h => exact .base h.symm
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem left (H : TmEq env U Γ a b) : TmEq env U Γ a a := by
  induction H with
  | base h => exact .base h.hasType.1
  | trans _ _ ih => exact ih

end TmEq

end LogRel
end Lean4Lean

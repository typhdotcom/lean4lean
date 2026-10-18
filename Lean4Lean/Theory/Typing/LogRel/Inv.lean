import Lean4Lean.Theory.Typing.Strong

/-!
# Inversion in an environment where injectivity holds

`Inj env` collects what the logical relation's fundamental lemma gives for a well-formed
environment: injectivity of sorts and pi types, sorts and pi types apart, and uniqueness of typing.
It is a hypothesis about one environment, used for the environments a declaration is checked in,
which the fundamental lemma covers by induction before the declaration's own rules exist. From it,
the body of a typed lambda is typed at the codomain.
-/

namespace Lean4Lean
namespace VEnv

/-- What the fundamental lemma gives for an environment. -/
structure Inj (env : VEnv) : Prop where
  sort_inv : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.sort u) (.sort v) → u ≈ v
  forallE_inv : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u)
  sort_forallE_inv : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B)
  uniq : ∀ {U Γ e₁ e₂ e₃ A B}, OnCtx Γ (env.IsType U) →
    env.IsDefEq U Γ e₁ e₂ A → env.IsDefEq U Γ e₂ e₃ B → ∃ u, env.IsDefEq U Γ A B (.sort u)

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem Inj.transU (hI : env.Inj) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.IsDefEqU U Γ e₂ e₃) : env.IsDefEqU U Γ e₁ e₃ := by
  obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
  obtain ⟨_, h⟩ := hI.uniq hΓ h1 h2
  exact ⟨_, h1.trans (.defeqDF h.symm h2)⟩

/-- The conversion `HasType` allows, up to `IsDefEqU`. -/
theorem Inj.defeqU (hI : env.Inj) (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A B) (h2 : env.HasType U Γ e A) : env.HasType U Γ e B := by
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, hA⟩ := h2.isType henv hΓ
  obtain ⟨_, h⟩ := hI.uniq hΓ hA h1
  exact .defeqDF (.defeqDF (.symm h) h1) h2

/-- A typed lambda's body is typed at some `B`, and the lambda's type is `forallE A B`. -/
theorem Inj.lam_inv' (hI : env.Inj) (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.lam A body) V) :
    ∃ B, env.HasType U (A::Γ) body B ∧ env.IsDefEqU U Γ (.forallE A B) V := by
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : A.lam body = e' at H
  induction H with cases eq
  | defeq _ h1 _ _ _ _ _ ih =>
    obtain ⟨B, hb, hd⟩ := ih hΓ rfl eq'
    exact ⟨B, hb, hI.transU hΓ hd ⟨_, h1.defeq⟩⟩
  | base H =>
    subst eq'; let .lam _ _ _ _ h2 h3 := H
    exact ⟨_, h2.hasType, _, h3.hasType⟩

/-- A lambda typed at a pi type over its own domain has its body typed at the codomain. -/
theorem Inj.lam_body (hI : env.Inj) (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (.lam A body) (.forallE A B)) : env.HasType U (A::Γ) body B := by
  obtain ⟨B₀, hb, hd⟩ := hI.lam_inv' henv hΓ H
  have hA := (HasType.lam_inv henv hΓ H).1
  have hΓ' : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, hA⟩
  obtain ⟨-, _, h⟩ := hI.forallE_inv hΓ hd
  exact hI.defeqU henv hΓ' ⟨_, h⟩ hb

/-- `lams Bs L` typed at `foralls Bs A` has `L : A` under `Bs`. -/
theorem Inj.lams_body (hI : env.Inj) (henv : Ordered env) :
    ∀ {Bs Γ} {L A : VExpr}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ (.lams Bs L) (.foralls Bs A) → env.HasType U (Bs.reverse ++ Γ) L A
  | [], _, _, _, _, H => H
  | B :: Bs, Γ, L, A, hΓ, H => by
    have H' := hI.lam_body henv hΓ H
    have hB := (HasType.lam_inv henv hΓ H).1
    simpa using hI.lams_body henv (Γ := B :: Γ) ⟨hΓ, hB⟩ H'

end VEnv
end Lean4Lean

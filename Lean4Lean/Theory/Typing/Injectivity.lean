import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.LogRel.ModelInv

/-!
Structural theorems of the type theory. `sort_inv` and `sort_forallE_inv` follow from the soundness
of the shape model (`Theory/Typing/LogRel`); injectivity of pi types and of inductive type formers
is the hypothesis `Injective`.
-/

namespace Lean4Lean
namespace VEnv

/-- Injectivity of pi types and of inductive type formers, in every well-formed environment and
context. Both are open problems: the theorems that rest on them, `addDecl.WF` among them, take this
class as a hypothesis. -/
class Injective : Prop where
  forallE_inv_stratified {env : VEnv} {U : Nat} {Γ : List VExpr} {A B A' B' V V' : VExpr}
    {n n' : Nat} : VEnv.WF env → OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') →
    env.HasTypeStratified U Γ (.forallE A B) V true n →
    env.HasTypeStratified U Γ (.forallE A' B') V' true n' →
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n'
  indApp_inv {env : VEnv} {U : Nat} {Γ : List VExpr} {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} {ls₁ ls₂ : List VLevel} {As₁ I₁ As₂ I₂ : List VExpr} :
    VEnv.WF env → OnCtx Γ (env.IsType U) →
    env.inducts s = some (d, t) → d.types[t]? = some T →
    (∀ l ∈ ls₁, l.WF U) → ls₁.length = d.uvars →
    (∀ l ∈ ls₂, l.WF U) → ls₂.length = d.uvars →
    As₁.length = d.params.length → I₁.length = T.indices.length →
    As₂.length = d.params.length → I₂.length = T.indices.length →
    env.IsType U Γ (.appN (.const s ls₁) (As₁ ++ I₁)) →
    env.IsType U Γ (.appN (.const s ls₂) (As₂ ++ I₂)) →
    env.IsDefEqU U Γ (.appN (.const s ls₁) (As₁ ++ I₁)) (.appN (.const s ls₂) (As₂ ++ I₂)) →
    List.Forall₂ (· ≈ ·) ls₁ ls₂ ∧
    Ctx.SubstEq env U Γ (VExpr.Subst.dflt.consList (As₁ ++ I₁))
      (VExpr.Subst.dflt.consList (As₂ ++ I₂))
      (d.params.map (·.instL ls₁) ++ T.indices.map (·.instL ls₁)).reverse

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := henv.sort_inv hΓ h1

theorem IsDefEqU.forallE_inv_stratified [Injective] (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' :=
  Injective.forallE_inv_stratified henv hΓ h1 h2 h3

theorem IsDefEqU.forallE_inv [Injective] (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  let ⟨_, eq⟩ := h1
  let ⟨h2, h3⟩ := (eq.strong henv hΓ).hasType'
  let ⟨_, h2⟩ := h2.stratify
  let ⟨_, h3⟩ := h3.stratify
  let ⟨⟨_, a1, _⟩, _, a2, _⟩ := IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3
  ⟨⟨_, a1⟩, _, a2⟩

/-- Injectivity of inductive type formers: two applications of a type of a block that are
definitionally equal have equivalent levels and definitionally equal arguments. Uniqueness of
typing needs it for projections, whose type depends on the parameters of the projected term's
type. -/
theorem IsDefEqU.indApp_inv [Injective] (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hls₁ : ∀ l ∈ ls₁, l.WF U) (hlen₁ : ls₁.length = d.uvars)
    (hls₂ : ∀ l ∈ ls₂, l.WF U) (hlen₂ : ls₂.length = d.uvars)
    (hA₁ : As₁.length = d.params.length) (hI₁ : I₁.length = T.indices.length)
    (hA₂ : As₂.length = d.params.length) (hI₂ : I₂.length = T.indices.length)
    (h1 : env.IsType U Γ (.appN (.const s ls₁) (As₁ ++ I₁)))
    (h2 : env.IsType U Γ (.appN (.const s ls₂) (As₂ ++ I₂)))
    (H : env.IsDefEqU U Γ (.appN (.const s ls₁) (As₁ ++ I₁)) (.appN (.const s ls₂) (As₂ ++ I₂))) :
    List.Forall₂ (· ≈ ·) ls₁ ls₂ ∧
    Ctx.SubstEq env U Γ (VExpr.Subst.dflt.consList (As₁ ++ I₁))
      (VExpr.Subst.dflt.consList (As₂ ++ I₂))
      (d.params.map (·.instL ls₁) ++ T.indices.map (·.instL ls₁)).reverse :=
  Injective.indApp_inv henv hΓ hs ht hls₁ hlen₁ hls₂ hlen₂ hA₁ hI₁ hA₂ hI₂ h1 h2 H

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := henv.sort_forallE_inv hΓ

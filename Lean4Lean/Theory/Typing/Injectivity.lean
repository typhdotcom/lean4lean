import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.LogRel.ModelInv

/-!
Structural theorems of the type theory. `sort_inv` and `sort_forallE_inv` follow from the soundness
of the shape model (`Theory/Typing/LogRel`); the others are not proved yet.
-/

namespace Lean4Lean
namespace VEnv

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := henv.sort_inv hΓ h1

theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
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
theorem IsDefEqU.indApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
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
      (d.params.map (·.instL ls₁) ++ T.indices.map (·.instL ls₁)).reverse := sorry

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := henv.sort_forallE_inv hΓ

import Lean4Lean.Theory.Typing.LogRel.Uniq
import Lean4Lean.Theory.Typing.LogRel.Inv
import Lean4Lean.Theory.Typing.LogRel.ModelInv

/-!
# Injectivity of an environment from chain inversion

Chain inversion (`ChainInv`) in every universe count gives `VEnv.Inj`: a chain collapses to one
equality once universes are unique, and `sort_forallE_inv` is the shape model's.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv}

/-- A chain collapses to one equality at a sort, given chain inversion. -/
theorem TyEq.collapse' (henv : env.Ordered) (hC : ChainInv env U) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (H : TyEq env U Γ A B) : ∃ u, env.IsDefEq U Γ A B (.sort u) :=
  H.collapse fun h1 h2 => sort_uniq henv hC hΓ h1 h2

/-- An equality at any type, of a term typed at a sort, is at that sort. -/
theorem defeq_at_sort (henv : env.Ordered) (hC : ChainInv env U) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEq U Γ A B V)
    (hA : env.HasType U Γ A (.sort w)) : env.IsDefEq U Γ A B (.sort w) :=
  (uniqChain henv hC hΓ h.symm hA).defeqDF h

/-- An environment with chain inversion in every universe count has injectivity. -/
theorem _root_.Lean4Lean.VEnv.Inj.of_chainInv (henv : env.WF) (hC : ∀ U, ChainInv env U) :
    env.Inj where
  sort_inv {U _ _ _} hΓ := fun ⟨_, h⟩ =>
    (hC U).sort hΓ (.base (defeq_at_sort henv.ordered (hC U) hΓ h
      (.sort (h.sort_inv' henv.ordered (.inl rfl)))))
  forallE_inv {U Γ A B A' B'} hΓ := fun ⟨_, h⟩ => by
    have hA := h.hasType.1.forallE_inv henv.ordered
    obtain ⟨⟨_, hA₁⟩, ⟨_, hB₁⟩⟩ := hA
    have ⟨h1, h2⟩ := (hC U).forallE hΓ
      (.base (defeq_at_sort henv.ordered (hC U) hΓ h (.forallEDF hA₁ hB₁)))
    exact ⟨h1.collapse' henv.ordered (hC U) hΓ, h2.collapse' henv.ordered (hC U) ⟨hΓ, _, hA₁⟩⟩
  sort_forallE_inv hΓ := henv.sort_forallE_inv hΓ
  uniq {U _ _ _ _ _ _} hΓ h1 h2 :=
    (uniqChain henv.ordered (hC U) hΓ h1 h2).collapse' henv.ordered (hC U) hΓ

end LogRel
end Lean4Lean

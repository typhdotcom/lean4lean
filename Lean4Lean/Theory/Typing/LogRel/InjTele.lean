import Lean4Lean.Theory.Typing.LogRel.Inv
import Lean4Lean.Theory.Typing.Telescope

/-!
# Telescopes, inverted under injectivity

The arguments of a well-typed application instantiate its function's pi telescope, in an
environment with injectivity (`VEnv.Inj`): `HasType.appN_invT` without the global conjectures.
-/

namespace Lean4Lean
open VExpr

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- The arguments of a well-typed application instantiate its function's telescope, in an
environment with injectivity. -/
theorem Inj.appN_invT (hI : env.Inj) (henv : env.Ordered) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {Δ As B τ f as},
    env.HasType U Γ f ((VExpr.foralls As B).subst τ) → Ctx.SubstEq env U Γ τ τ Δ →
    env.IsTele U Δ As → (f.appN as).WF env U Γ → as.length = As.length →
    Ctx.SubstEq env U Γ (τ.consList as) (τ.consList as) (As.reverse ++ Δ)
  | _, [], _, _, _, [], _, hτ, _, _, _ => hτ
  | Δ, A :: As, B, τ, f, a :: as, hf, hτ, .cons ⟨_, hA⟩ hAs, hwf, hlen => by
    have hwf1 := appN_wf_prefix henv hΓ (as := [a]) (bs := as) hwf
    obtain ⟨A₁, B₁, h1, h2⟩ := hwf1.app_inv henv hΓ
    obtain ⟨_, hu⟩ := hI.uniq hΓ h1 hf
    have ⟨⟨u, hA'⟩, _⟩ := hI.forallE_inv hΓ ⟨_, hu⟩
    have ha : env.HasType U Γ a (A.subst τ) := hI.defeqU henv hΓ ⟨_, hA'⟩ h2
    have hτ' : Ctx.SubstEq env U Γ (τ.cons a) (τ.cons a) (A :: Δ) := .cons hτ hA ha
    have hfa := hf.app ha
    rw [inst_lift_cons] at hfa
    have := Inj.appN_invT hI henv hΓ (Δ := A :: Δ) hfa hτ' hAs hwf (Nat.succ.inj hlen)
    rw [List.reverse_cons, List.append_assoc]; exact this

end VEnv
end Lean4Lean

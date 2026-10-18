import Lean4Lean.Theory.Typing.Recursor
import Lean4Lean.Theory.Typing.Substitution

/-! Quotient reduction: `Quot.lift f h (Quot.mk r a)` is `f a` by the computation rule, and
`Quot.ind p (Quot.mk r a)` is `p a` by proof irrelevance. -/

namespace Lean4Lean
open VExpr

namespace QuotRed

/-- The binders `Quot.lift` and its computation rule share: `α r β f h`. -/
def liftBinders : List VExpr := [
  .sort (.param 0),
  .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
  .sort (.param 1),
  .forallE (.bvar 2) (.bvar 1),
  .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
      (.app (.bvar 3) (.bvar 1)))))]

theorem quotLiftConst_eq : quotLiftConst = ⟨2, .foralls
    (liftBinders ++ [.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]) (.bvar 3)⟩ :=
  rfl

theorem quotDefEq_eq : quotDefEq = {
    uvars := 2
    lhs := .lams (liftBinders ++ [.bvar 4]) (.appN (.const ``Quot.lift [.param 0, .param 1])
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
        .appN (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]])
    rhs := .lams (liftBinders ++ [.bvar 4]) (.app (.bvar 2) (.bvar 0))
    type := .foralls (liftBinders ++ [.bvar 4]) (.bvar 3) } := rfl

theorem quotMkConst_eq : quotMkConst = ⟨1, .foralls
    [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
    (.app (.app (.const ``Quot [.param 0]) (.bvar 2)) (.bvar 1))⟩ := rfl

/-- The binders of `Quot.ind`: `α r β mk q`. -/
def indBinders : List VExpr :=
    [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
      .forallE (.app (.app (.const ``Quot [.param 0]) (.bvar 1)) (.bvar 0)) (.sort .zero),
      .forallE (.bvar 2) (.app (.bvar 1)
        (.app (.app (.app (.const ``Quot.mk [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 0))),
      .app (.app (.const ``Quot [.param 0]) (.bvar 3)) (.bvar 2)]

theorem quotIndConst_eq : quotIndConst = ⟨1, .foralls indBinders (.app (.bvar 2) (.bvar 0))⟩ :=
  rfl

end QuotRed

theorem VExpr.WF.lams_inv {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ As e}, OnCtx Γ (env.IsType U) → VExpr.WF env U Γ (.lams As e) →
      env.IsTele U Γ As ∧ VExpr.WF env U (As.reverse ++ Γ) e
  | _, [], _, _, h => ⟨.nil, h⟩
  | Γ, A :: As, e, hΓ, h => by
    obtain ⟨hA, hb⟩ := VExpr.WF.lam_inv henv hΓ h
    obtain ⟨h1, h2⟩ := VExpr.WF.lams_inv henv (Γ := A :: Γ) ⟨hΓ, hA⟩ hb
    exact ⟨.cons hA h1, by simpa using h2⟩

/-- A closed lambda telescope applied to arguments for all its binders is its body at them. -/
theorem VEnv.lams_appN {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {As : List VExpr} {e : VExpr} {as : List VExpr}
    (hwf : VExpr.WF env U [] (.lams As e)) (hlen : as.length = As.length)
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList as) (Subst.id.consList as) As.reverse) :
    env.IsDefEqU U Γ ((VExpr.lams As e).appN as) (e.subst (Subst.id.consList as)) := by
  obtain ⟨hAs, T, he⟩ := hwf.lams_inv henv.ordered (Γ := []) trivial
  have he' : env.HasType U (As.reverse ++ []) e T := he
  have := VEnv.IsDefEq.lams_beta henv.ordered hΓ (Δ := []) (τ := .id) .nil hAs
    he' hlen (by simpa using W)
  exact ⟨_, by simpa using this⟩

end Lean4Lean

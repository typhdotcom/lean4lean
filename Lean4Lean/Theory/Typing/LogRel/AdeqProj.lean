import Lean4Lean.Theory.Typing.LogRel.AdequacyOf

/-!
# Adequacy at the projection rules

The projection cases of `AdequacyHyps`, for every recorded block. A projection of a constructor
application steps to the field (`Step.projIota`), typed by the rule's own premises under the
related substitutions, and every interpretation of the projection interprets the field, so the
field's adequacy gives the projection's.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}

omit [ShapeEnv] [AxInterp] in
/-- A projection of a constructor application steps to the field under any substitution. -/
theorem StepS.projIota_subst {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} {ls : List VLevel} {As fs : List VExpr} {k : Nat} {a : VExpr}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (h5 : fs[k]? = some a) (h8 : As.length = d.params.length) (h9 : fs.length = c.fields.length)
    (σ : VExpr.Subst) :
    StepS env U Γ ((VExpr.proj s k ((VExpr.const c.name ls).appN (As ++ fs))).subst σ)
      (a.subst σ) := by
  show StepS env U Γ (.proj s k (((VExpr.const c.name ls).appN (As ++ fs)).subst σ)) _
  rw [subst_appN, List.map_append]
  exact .single (.projIota h1 h2 h3 (by simp [h8]) (by simp [h9])
    (by simp [List.getElem?_map, h5]))

/-- A projection of a constructor application is related to its field wherever it is
interpreted: every interpretation of it interprets the field, and it steps to the field. -/
theorem AdeqStmt.projIota (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor} {k : Nat}
    {ls : List VLevel} {As fs : List VExpr} {a : VExpr} {u : VLevel}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (h5 : fs[k]? = some a) (h8 : As.length = d.params.length) (h9 : fs.length = c.fields.length)
    (hP : env.IsDefEqStrong U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) (.sort u))
    (iha : AdeqStmt (U := U) henv hU Γ₀ Γ a a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))))
    (hS : StrongSoundEq env U Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) := by
  intro ρ n m a' hm ha hmem
  refine LR.Adequate.fits fun hW => ?_
  have ad := iha ((hS.sound hW).1 hm) ha hmem
  have tl {σ} (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ Γ) :
      TRed env U Γ₀ ((VExpr.proj s k ((VExpr.const c.name ls).appN (As ++ fs))).subst σ)
        (a.subst σ) ((c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))).subst σ) :=
    ⟨StepS.projIota_subst h1 h2 h3 h5 h8 h9 σ, hS.defeq.subst henv W hΓ₀⟩
  refine ⟨fun σ σ' W => ⟨?_, (ad.1 W).2⟩, fun σ W => ?_⟩
  · have tr : TRed env U Γ₀ ((VExpr.proj s k ((VExpr.const c.name ls).appN (As ++ fs))).subst σ')
        (a.subst σ') ((c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))).subst σ) :=
      (tl (W.symm.left.toSubstEq hΓ₀)).defeqDF
        (hP.defeq.substDF henv hΓ hΓ₀ (W.symm.toSubstEq hΓ₀))
    exact ((LR _ _ _).whr (tl (W.left.toSubstEq hΓ₀)) tr).2 (ad.1 W).1
  · exact ((LR _ _ _).whr (tl (W.toSubstEq hΓ₀))
      (.refl (tl (W.toSubstEq hΓ₀)).2.hasType.2)).2 (ad.2 W)

end LogRel
end Lean4Lean

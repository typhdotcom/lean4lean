import Lean4Lean.Theory.Typing.LogRel.AdeqProjDF

/-!
# Projections of a value that reduces to a constructor application

A value `M` of a structure-like type `s ls (As ++ I)` that reduces, typed, to a constructor
application `c ls₁ (qs ++ ms)`: its projections reduce, typed, to the fields `ms`, given that the
application is equal to the one at the type's own levels and parameters, `c ls (As ++ ms)`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- The `k`th projection of a value that reduces to a constructor application reduces, typed at
the projection's type, to the `k`th field. -/
theorem TRed.proj_ctor (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (hF : VEnv.ProjFacts env d c) {ls ls₁ : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.uvars) {As I qs ms : List VExpr} (hA : As.length = d.params.length)
    (hI : I.length = T.indices.length) (hqs : qs.length = d.params.length)
    (hms : ms.length = c.fields.length)
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    {u : VLevel}
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    {M : VExpr}
    (hM : TRed env U Γ M ((VExpr.const c.name ls₁).appN (qs ++ ms)) (.appN (.const s ls) (As ++ I)))
    (hXX : env.IsDefEq U Γ ((VExpr.const c.name ls₁).appN (qs ++ ms))
      ((VExpr.const c.name ls).appN (As ++ ms)) (.appN (.const s ls) (As ++ I)))
    (hfsT : ∀ k (h : k < ms.length) (f : VField), c.fields[k]? = some f →
      env.HasType U Γ ms[k] ((f.type.instL ls).subst (Subst.dflt.consList (As ++ ms.take k))))
    {k : Nat} {f : VField} {a : VExpr} (hf : c.fields[k]? = some f) (ha : ms[k]? = some a)
    (hP : d.ProjAllowed c ls k) :
    TRed env U Γ (.proj s k M) a (c.projType ls s k As M) := by
  have hMX' := hM.2.trans hXX
  have hPC := VEnv.projCongr henv hΓ h1 h2 h3 hF hls hlen hA hI hA hI W hS hMX' k f hf hP
  have hX' : env.HasType U Γ ((VExpr.const c.name ls).appN (As ++ ms))
      (.appN (.const s ls) (As ++ I)) := hXX.hasType.2
  have hι := VEnv.projIota_ctor henv hΓ h1 h2 h3 hF hls hlen hA hI hms W hS hX' hfsT k f a hf ha hP
  refine ⟨(StepS.proj hM.1).trans (.single (.projIota h1 h2 h3 hqs hms ha)), ?_⟩
  exact hPC.2.trans (.defeqDF hPC.1.symm hι)

end

end LogRel
end Lean4Lean

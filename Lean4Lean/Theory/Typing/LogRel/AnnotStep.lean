import Lean4Lean.Theory.Typing.LogRel.WHRed
import Lean4Lean.Theory.Typing.Substitution

/-!
# A declared domain reduces to its view

The annotations a constructor's declared field domain carries are defined by rules returning their
first argument (`VEnv.AnnotDef`), so a well-typed domain head-reduces to its view: each layer is a
delta step and beta steps.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem _root_.Lean4Lean.VExpr.StripsToBy.instL {P : Lean.Name → Prop} {e e' : VExpr} (ls : List VLevel)
    (H : e.StripsToBy P e') : (e.instL ls).StripsToBy P (e'.instL ls) := by
  induction H with
  | refl => exact .refl
  | app2 hc hP _ ih => exact .app2 hc hP ih
  | app1 hc hP _ ih => exact .app1 hc hP ih

theorem _root_.Lean4Lean.VExpr.StripsToBy.subst {P : Lean.Name → Prop} {e e' : VExpr} (σ : VExpr.Subst)
    (H : e.StripsToBy P e') : (e.subst σ).StripsToBy P (e'.subst σ) := by
  induction H with
  | refl => exact .refl
  | app2 hc hP _ ih => exact .app2 hc hP ih
  | app1 hc hP _ ih => exact .app1 hc hP ih

/-- The constant of a typed application of an annotation unfolds to its defining rule's
right-hand side, at the constant's levels. -/
theorem annot_delta (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) {c : Lean.Name}
    {ls : List VLevel} {V : VExpr} (hc : env.HasType U Γ (.const c ls) V) {k : Nat}
    (hA : env.ReturnsFirstRule c k) :
    ∃ As : List VExpr, As.length = k ∧
      Step env U Γ (.const c ls) (.lams (As.map (·.instL ls)) (.bvar (k - 1))) := by
  obtain ⟨df, As, h1, h2, h3, h4⟩ := hA
  obtain ⟨ci, hci, -, hls⟩ := hc.const_inv henv hΓ
  have hW := (henv.defEqWF h1).1
  rw [h2] at hW
  obtain ⟨ci', hci', -, hls'⟩ := VEnv.HasType.const_inv henv (Γ := []) (show OnCtx [] (env.IsType df.uvars) from trivial) hW
  rw [hci] at hci'; cases hci'
  have hst := Step.delta (env := env) (U := U) (Γ := Γ) h1 h2 (ls := ls)
    (by rw [hls, ← hls']; simp)
  rw [h4, instL_lams] at hst
  exact ⟨As, h3, by simpa [instL] using hst⟩

/-- A well-typed declared domain head-reduces to its view. -/
theorem StepS.of_stripsToBy (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) {D V : VExpr}
    (H : D.StripsToBy env.AnnotDef V) (hD : VExpr.WF env U Γ D) : StepS env U Γ D V := by
  induction H with
  | refl => exact .rfl
  | @app2 A e ls v c hc hP _ ih =>
    obtain ⟨_, _, hf, -⟩ := hD.app_inv henv hΓ
    obtain ⟨_, _, hc', hAt⟩ := VExpr.WF.app_inv henv hΓ (⟨_, hf⟩ : VExpr.WF env U Γ _)
    have hk : (if c = ``outParam ∨ c = ``semiOutParam then 1 else 2) = 2 := by
      rcases hc with rfl | rfl <;> decide
    rw [VEnv.AnnotDef, hk] at hP
    obtain ⟨As, hl, hst⟩ := annot_delta henv hΓ hc' hP
    obtain ⟨B₁, B₂, rfl⟩ : ∃ B₁ B₂, As = [B₁, B₂] := by
      match As, hl with | [B₁, B₂], _ => exact ⟨B₁, B₂, rfl⟩
    refine .trans (.single (.app (.app hst))) (.trans (.single (.app .beta)) ?_)
    refine .trans (.single ?_) (ih ⟨_, hAt⟩)
    have : (VExpr.lam (B₂.instL ls) (.bvar 1)).inst A = .lam ((B₂.instL ls).inst A) A.lift := by
      simp [inst, instVar, lift]
    simp only [lams, List.map_cons, List.map_nil, Nat.add_one_sub_one]
    rw [this]
    simpa [inst_lift] using (Step.beta (env := env) (U := U) (Γ := Γ)
      (A := (B₂.instL ls).inst A) (e := A.lift) (a := v))
  | @app1 A e ls c hc hP _ ih =>
    obtain ⟨_, _, hc', hAt⟩ := hD.app_inv henv hΓ
    have hk : (if c = ``outParam ∨ c = ``semiOutParam then 1 else 2) = 1 := by
      rcases hc with rfl | rfl <;> simp
    rw [VEnv.AnnotDef, hk] at hP
    obtain ⟨As, hl, hst⟩ := annot_delta henv hΓ hc' hP
    obtain ⟨B₁, rfl⟩ : ∃ B₁, As = [B₁] := by
      match As, hl with | [B₁], _ => exact ⟨B₁, rfl⟩
    refine .trans (.single (.app hst)) (.trans (.single ?_) (ih ⟨_, hAt⟩))
    simpa [lams, inst, instVar] using (Step.beta (env := env) (U := U) (Γ := Γ)
      (A := B₁.instL ls) (e := .bvar 0) (a := A))

end LogRel
end Lean4Lean

namespace Lean4Lean.LogRel
open VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- A constructor's declared field domain, instantiated and well typed, head-reduces to its field's
view, instantiated alike: what converts a projection's telescope domain to its `projType`. -/
theorem StepS.declDom_view (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    {E : VEnv} {d : VInductDecl} {T : VInductiveType} {c : VConstructor} (hcW : c.WF E d T)
    (hle : E ≤ env) {ps Ds : List VExpr} {B : VExpr} (hty : c.type = .foralls (ps ++ Ds) B)
    (hps : ps.length = d.params.length) {k : Nat} {D : VExpr} {f : VField}
    (hD : Ds[k]? = some D) (hf : c.fields[k]? = some f) (ls : List VLevel) (σ : VExpr.Subst)
    (hW : VExpr.WF env U Γ ((D.instL ls).subst σ)) :
    StepS env U Γ ((D.instL ls).subst σ) ((f.type.instL ls).subst σ) :=
  StepS.of_stripsToBy henv hΓ
    ((((hcW.strips ps Ds B hty hps k D f hD hf).mono
      fun _ (h : E.AnnotDef _) => h.mono hle).instL ls).subst σ) hW

end Lean4Lean.LogRel

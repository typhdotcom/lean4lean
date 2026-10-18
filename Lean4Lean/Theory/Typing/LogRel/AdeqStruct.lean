import Lean4Lean.Theory.Typing.LogRel.AdeqQuotMk

/-!
# Fields related through what reduces to them

Terms that reduce, typed along a telescope, to related fields are related along it: what a
structure's projections of a constructor application need, each projection reducing to its field.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr} [ShapeEnv] {n : Nat}

variable (env U Γ) in
/-- `ps` reduce to `ms` along the telescope `T`, instantiated with `xs`: each at its domain. -/
def RedFields : VExpr → List VExpr → List VExpr → List VExpr → Prop
  | _, [], [], [] => True
  | T, x :: xs, p :: ps, m :: ms => ∃ D B, StepS env U Γ T (.forallE D B) ∧ TRed env U Γ p m D ∧
    RedFields (B.inst x) xs ps ms
  | _, _, _, _ => False

variable {IH : LogRel env U Γ n}

/-- Fields related along a telescope related to itself are related through terms reducing to
them along it. -/
theorem FieldsRel.of_red (hU : StepUniq env) : ∀ {fs : List (WShape n)} {T} {tel : WShape n}
    {ms ns ps qs}, TeleRel IH fs.length T T tel → FieldsRel IH T tel ms ns fs →
    RedFields env U Γ T ps ps ms → RedFields env U Γ T ps qs ns → FieldsRel IH T tel ps qs fs
  | [], _, _, ms, ns, ps, qs, _, H, Rp, Rq => by
    cases ms <;> cases ns <;> cases ps <;> cases qs <;>
      first | trivial | simp [FieldsRel] at H | simp [RedFields] at Rp | simp [RedFields] at Rq
  | x :: xs, T, tel, ms, ns, ps, qs, HT, H, Rp, Rq => by
    cases ms <;> cases ns <;> try simp [FieldsRel] at H
    cases ps <;> try simp [RedFields] at Rp
    cases qs <;> try simp [RedFields] at Rq
    all_goals try (rename_i ps; cases ps <;> simp [RedFields] at Rq)
    rename_i m ms n ns p ps q qs
    obtain ⟨D, B, b, g, hv, r, hx, hd, hr, HF⟩ := H
    obtain ⟨Dp, Bp, rp, tp, Rp⟩ := Rp
    obtain ⟨Dq, Bq, rq, tq, Rq⟩ := Rq
    obtain ⟨rfl, rfl⟩ : Dp = D ∧ Bp = B := by
      have := StepS.determ hU rp forallE_whnf' r forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : Dq = Dp ∧ Bq = Bp := by
      have := StepS.determ hU rq forallE_whnf' r forallE_whnf'; simpa using this
    obtain ⟨D₁, B₁, D₂, B₂, r₁, r₂, -, -, HT'⟩ := HT.of_piView hv
    obtain ⟨rfl, rfl⟩ : D₁ = Dq ∧ B₁ = Bq := by
      have := StepS.determ hU r₁ forallE_whnf' r forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D₂ = D₁ ∧ B₂ = B₁ := by
      have := StepS.determ hU r₂ forallE_whnf' r forallE_whnf'; simpa using this
    have hmp : IH.DefEq m p D₂ x b := (IH.whr (TRed.refl hd.hasType.1) tp).2 (IH.left hr)
    have hpq : IH.DefEq p q D₂ x b := (IH.whr tp tq).2 hr
    have hpq' : env.IsDefEq U Γ p q D₂ := tp.2.trans (hd.trans tq.2.symm)
    refine ⟨D₂, B₂, b, g, hv, r, hx, hpq', hpq, ?_⟩
    exact of_red hU (HT' p p x hx hpq'.hasType.1 (IH.left hpq))
      (HF.conv hU (HT' m p x hx tp.2.symm hmp)) Rp Rq

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.subst_lift_inst (B x : VExpr) (σ : VExpr.Subst) :
    (B.subst σ.lift).inst x = B.subst (σ.cons x) := by
  rw [inst_eq, subst_subst]; congr 1; funext i
  cases i with
  | zero => rfl
  | succ i => simp [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons]

omit [ShapeEnv] in
/-- A telescope instantiated by `σ` reduces, at each step, to its next domain: the values `ps`
reducing to `ms` at the domains instantiated by `xs` give `RedFields`. -/
theorem RedFields.of_foralls (B : VExpr) : ∀ (Ds : List VExpr) (σ : VExpr.Subst)
    (xs ps ms : List VExpr), xs.length = Ds.length → ps.length = Ds.length →
    ms.length = Ds.length →
    (∀ j (h1 : j < ps.length) (h2 : j < ms.length) (h3 : j < Ds.length),
      TRed env U Γ ps[j] ms[j] (Ds[j].subst (σ.consList (xs.take j)))) →
    RedFields env U Γ ((VExpr.foralls Ds B).subst σ) xs ps ms
  | [], _, xs, ps, ms, h1, h2, h3, _ => by
    cases xs <;> cases ps <;> cases ms <;> simp_all [RedFields]
  | D :: Ds, σ, x :: xs, p :: ps, m :: ms, h1, h2, h3, H => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
    refine ⟨D.subst σ, (VExpr.foralls Ds B).subst σ.lift, .rfl,
      H 0 (by simp) (by simp) (by simp), ?_⟩
    rw [VExpr.subst_lift_inst]
    exact of_foralls B Ds (σ.cons x) xs ps ms h1 h2 h3 fun j a b c =>
      H (j+1) (by simpa using a) (by simpa using b) (by simpa using c)
  | _ :: _, _, [], _, _, h1, _, _, _ | _ :: _, _, _ :: _, [], _, _, h2, _, _
  | _ :: _, _, _ :: _, _ :: _, [], _, _, h3, _ => by simp_all

end LogRel
end Lean4Lean

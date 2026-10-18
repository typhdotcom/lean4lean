import Lean4Lean.Theory.Typing.LogRel.AdeqIota
import Lean4Lean.Theory.Typing.LogRel.IotaReplace
import Lean4Lean.Theory.Typing.LogRel.InjTele

/-!
# An iota rule whose left body computes at replaced fields

The K-like and structure-eta steps take an iota rule's left body, under a substitution of its
binders, to the right body at values for the constructor's fields other than the substitution's:
chosen proofs, or the major premise's projections. The rule is related where the replaced values
are equal to the old ones and related to whatever they are (`iotaRule_adeq_repl`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- The right body of an iota rule is the minor premise applied: a variable past the fields. -/
theorem iotaRule_rhs_body (d : VInductDecl) {lsB : List VLevel} {v : VLevel} {recLs : List VLevel}
    {q j : Nat} {c : VConstructor} {R : VExpr}
    (h : (d.iotaRule lsB v recLs q j c).rhs = .lams (d.iotaBinders lsB v c) R) :
    ∃ args, R = (VExpr.bvar (c.fields.length + (d.allCtors.length - 1 - q))).appN args := by
  have h' : (d.iotaRule lsB v recLs q j c).rhs = .lams (d.iotaBinders lsB v c)
      ((VExpr.bvar (c.fields.length + (d.allCtors.length - 1 - q))).appN
        (VExpr.bvars c.fields.length 0 ++ c.recFields.map fun (k, ra) =>
          let l := ra.binders.length
          let xs := ra.binders.zipIdx.map fun (A, i) =>
            (A.instL lsB).reseat (d.allTypes.length + d.allCtors.length) k c.fields.length 0 i
          let idx := ra.indices.map fun e =>
            (e.instL lsB).reseat (d.allTypes.length + d.allCtors.length) k c.fields.length 0 l
          .lams xs <| .app
            (.appN (d.recConst recLs ra.typeIdx) (VExpr.bvars d.params.length
              (d.allTypes.length + d.allCtors.length + c.fields.length + l) ++
              VExpr.bvars d.allTypes.length (d.allCtors.length + c.fields.length + l) ++
              VExpr.bvars d.allCtors.length (c.fields.length + l) ++ idx))
            (.appN (.bvar (l + (c.fields.length - 1 - k))) (VExpr.bvars l 0)))) := rfl
  exact ⟨_, (VExpr.lams_inj (h.symm.trans h') rfl).2⟩

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- An iota rule is related where its left body, under each related substitution `σ` of its
binders, computes to the right-hand side at `F σ`, which differs from `σ` only at the fields, by
values equal to `σ`'s (given the substitutions below equal) and related to whatever `σ`'s are. -/
theorem iotaRule_adeq_repl (henvW : env.WF) (hM : ModelEnv env) {E E₂ : VEnv} (hEE : E ≤ E₂)
    (hE₂le : E₂ ≤ env) (hEo : E.Ordered) (hE₂o : E₂.Ordered)
    (hX : SoundHyps E env) (hX₂ : SoundHyps E₂ env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    {d : VInductDecl} {q j : Nat} {c : VConstructor}
    (hdf₂ : E₂.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c))
    {L₀ R₀ A₀ : VExpr}
    (hB : (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).BodyWF E
      (d.iotaBinders d.recLevels d.motiveLevel c) L₀ R₀ A₀)
    {Γ : List VExpr} {ls : List VLevel} (hΓ : OnCtx Γ (env.IsType U)) (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.recUVars)
    (Gs Δ : List VExpr)
    (hGs : Gs = ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
      (d.params.length + d.allTypes.length + d.allCtors.length)).reverse)
    (hΔ : Δ = ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).take
      (d.params.length + d.allTypes.length + d.allCtors.length)).reverse ++ Γ)
    (F : VExpr.Subst → VExpr.Subst)
    (hFtop : ∀ σ i, c.fields.length ≤ i → F σ i = σ i)
    (hstep : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ (Gs ++ Δ) ρ →
      StepS env U Γ₀ ((iotaL d (d.recLevels.map (·.inst ls)) ls j c).subst σ)
        ((d.iotaRhs ls q j c).appN ((VExpr.bvars (d.params.length + d.allTypes.length +
          d.allCtors.length + c.fields.length) 0).map (·.subst (F σ)))))
    (HF : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ (Gs ++ Δ) ρ → ∀ i (h : i < Gs.length),
      (VEnv.Ctx.SubstEq env U Γ₀ ((F σ).drop (i+1)) (σ.drop (i+1)) (Gs.drop (i+1) ++ Δ) →
        (∃ u, env.IsDefEq U Γ₀ (Gs[i].subst ((F σ).drop (i+1))) (Gs[i].subst (σ.drop (i+1)))
          (.sort u)) →
        env.IsDefEq U Γ₀ (F σ i) (σ i) (Gs[i].subst ((F σ).drop (i+1)))) ∧
      ∀ {n} {m a : WShape n} {x : VExpr}, m.T ≤ ρ i → m.HasType a →
        env.IsDefEq U Γ₀ (σ i) x (Gs[i].subst ((F σ).drop (i+1))) →
        (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (σ i) x (Gs[i].subst ((F σ).drop (i+1))) m a →
        (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (F σ i) x (Gs[i].subst ((F σ).drop (i+1))) m a) :
    AdeqStmt (U := U) henv hU Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls) := by
  have hEenv : E ≤ env := hEE.trans hE₂le
  have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hX.strongSound hM hEenv D
  have hS₂ : ∀ {Γ M N A}, E₂.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hX₂.strongSound hM hE₂le D
  have hLform : L₀.instL ls = iotaL d (d.recLevels.map (·.inst ls)) ls j c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).1
    rw [VLevel.inst_map_id hlen, hB.lhs, VEnv.lams_instL', iotaRule_lhs] at h3
    exact (VExpr.lams_inj h3 (by simp [length_iotaBinders])).2
  have hBAform : (d.iotaBinders d.recLevels d.motiveLevel c).map (·.instL ls) =
      d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).2.2
    rw [VLevel.inst_map_id hlen, hB.type, VEnv.foralls_instL', iotaRule_type] at h3
    exact (VExpr.foralls_inj h3 (by simp [length_iotaBinders])).1
  obtain ⟨Rargs, hR0⟩ := iotaRule_rhs_body d hB.rhs
  have hRhs : d.iotaRhs ls q j c =
      (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls := rfl
  generalize hdfe : d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c = df
    at hdf₂ hB hRhs
  have hdfu : df.uvars = d.recUVars := by subst hdfe; simp [VInductDecl.iotaRule]
  have hlen' : ls.length = df.uvars := hdfu ▸ hlen
  generalize hB0 : d.iotaBinders d.recLevels d.motiveLevel c = B₀ at hB hBAform
  rw [hB.lhs, hB.rhs, hB.type, VEnv.lams_instL', VEnv.lams_instL', VEnv.foralls_instL']
  generalize hBs : B₀.map (·.instL ls) = Bs at hBAform
  have hBf : Bs = d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c :=
    hBs ▸ hBAform
  rw [← hBf] at hGs hΔ
  have teleE : E.IsTele U [] Bs := by
    have := hB.tele.instL hls (U' := U); simpa [← hBs] using this
  have onBs : OnCtx Bs.reverse (E.IsType U) := by simpa using teleE.onCtx (Γ := []) trivial
  let P : List VExpr → VExpr → Prop := fun Γ' T =>
    ∃ Δ, Γ' = Δ ++ Γ ∧ OnCtx Δ (E.IsType U) ∧ E.IsType U Δ T
  have hP : ∀ {Γ' A B}, P Γ' (.forallE A B) → P Γ' A ∧ P (A::Γ') B := by
    rintro Γ' A B ⟨Δ, rfl, hΔ, hT⟩
    obtain ⟨h1, h2⟩ := VEnv.IsType.forallE_inv hEo hT
    exact ⟨⟨Δ, rfl, hΔ, h1⟩, ⟨A::Δ, rfl, ⟨hΔ, h1⟩, h2⟩⟩
  have weakE {Δ e1 e2 A} (hΔ : OnCtx Δ (E.IsType U)) (H : E.IsDefEq U Δ e1 e2 A) :
      E.IsDefEqStrong U (Δ ++ Γ) e1 e2 A := IsDefEq.weak_closed hEo hΔ H Γ
  have adeqE {Δ e1 e2 A} (hΔ : OnCtx Δ (E.IsType U)) (hΓ' : OnCtx (Δ ++ Γ) (env.IsType U))
      (H : E.IsDefEq U Δ e1 e2 A) : AdeqStmt (U := U) henv hU Γ₀ (Δ ++ Γ) e1 e2 A :=
    LR.adequacy_of hM hEenv hS hΓ₀ IH (weakE hΔ H) hΓ'
  have hTy : ∀ {Γ' T}, OnCtx Γ' (env.IsType U) → P Γ' T → ∃ w, env.HasType U Γ' T (.sort w) ∧
      StrongSoundEq env U Γ' T T (.sort w) ∧
      AdeqStmt (U := U) henv hU Γ₀ Γ' T T (.sort w) := by
    rintro Γ' T hΓ' ⟨Δ, rfl, hΔ, w, hT⟩
    exact ⟨w, ((weakE hΔ hT).defeq).mono hEenv, hS (weakE hΔ hT), adeqE hΔ hΓ' hT⟩
  have hLt : E.HasType U Bs.reverse (L₀.instL ls) (A₀.instL ls) := by
    have := hB.hasL.instL hls (U' := U); simpa [← hBs, List.map_reverse] using this
  have hRt : E.HasType U Bs.reverse (R₀.instL ls) (A₀.instL ls) := by
    have := hB.hasR.instL hls (U' := U); simpa [← hBs, List.map_reverse] using this
  have hAt : E.IsType U Bs.reverse (A₀.instL ls) := hRt.isType hEo onBs
  have hPT : P Γ (.foralls Bs (A₀.instL ls)) :=
    ⟨[], rfl, trivial, by simpa using teleE.foralls (B := A₀.instL ls) (by simpa using hAt)⟩
  apply AdeqStmt.etaLams hM hΓ₀ P hP hTy Bs hΓ hPT
  have hEnvo : env.Ordered := henvW.ordered
  have hdfE : env.defeqs df := hE₂le.defeqs hdf₂
  have hN : d.params.length + d.allTypes.length + d.allCtors.length ≤ Bs.length := by
    rw [hBf, length_iotaBinders]; omega
  have hBlen : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length +
      c.fields.length := by
    rw [← hBs, List.length_map, ← hB0, length_iotaBinders]
  have hRform : ∃ args, R₀.instL ls =
      (VExpr.bvar (c.fields.length + (d.allCtors.length - 1 - q))).appN args :=
    ⟨_, by rw [hR0, VExpr.instL_appN]; rfl⟩
  generalize hL : L₀.instL ls = L at hLform hLt
  generalize hR : R₀.instL ls = R at hRt hRform
  generalize hA : A₀.instL ls = A at hRt hLt hAt hPT ⊢
  obtain ⟨Rargs', hRform⟩ := hRform
  -- the rule's sides are closed
  have hext : E₂.IsDefEq U [] (.lams Bs L) (.lams Bs R) (.foralls Bs A) := by
    have := VEnv.IsDefEq.extra (Γ := []) (uvars := U) hdf₂ hls hlen'
    rwa [hB.lhs, hB.rhs, hB.type, VEnv.lams_instL', VEnv.lams_instL', VEnv.foralls_instL', hBs,
      hL, hR, hA] at this
  have hcl := hext.closedN' hE₂o.closed trivial
  have hΓ' : OnCtx (Bs.reverse ++ Γ) (env.IsType U) := OnCtx.append_closed hEo hEenv hΓ onBs
  obtain ⟨w₃, hAw⟩ := hAt
  have hAenv : env.HasType U (Bs.reverse ++ Γ) A (.sort w₃) :=
    ((IsDefEq.weak_closed hEo onBs hAw Γ).defeq).mono hEenv
  have hRenv : env.HasType U (Bs.reverse ++ Γ) R A :=
    ((IsDefEq.weak_closed hEo onBs hRt Γ).defeq).mono hEenv
  have HS : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) R R A := adeqE onBs hΓ' hRt
  have HA : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) A A (.sort w₃) := adeqE onBs hΓ' hAw
  have hSA : StrongSoundEq env U (Bs.reverse ++ Γ) A A (.sort w₃) := hS (weakE onBs hAw)
  have hRbcl : R.ClosedN Bs.length := by
    simpa using (hRt.closedN' hEo.closed (onBs.ctxClosed hEo)).1
  have hLbcl : L.ClosedN Bs.length := by
    simpa using (hLt.closedN' hEo.closed (onBs.ctxClosed hEo)).1
  have hAcl : A.ClosedN Bs.length := by
    simpa using (hLt.closedN' hEo.closed (onBs.ctxClosed hEo)).2.2
  have hBenv := hB.mono hEenv
  have body {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :=
    VEnv.IsDefEq.extra_body hEnvo hΓ₀ hdfE hBenv hls hlen'
      (as := (VExpr.bvars Bs.length 0).map (·.subst σ)) (by simp [VExpr.bvars, ← hBs])
      (by have := Ctx.SubstEq.vals hEnvo (onBs.mono fun ⟨w, h⟩ => ⟨w, h.mono hEenv⟩)
            (W.toSubstEq hΓ₀).left
          simpa [hBs] using this)
  have hvl (σ : VExpr.Subst) : ((VExpr.bvars Bs.length 0).map (·.subst σ)).length = Bs.length := by
    simp [VExpr.bvars]
  have redR {σ ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ (Bs.reverse ++ Γ) ρ) :
      TRed env U Γ₀ ((etaSpine Bs (.lams Bs R)).subst σ) (R.subst σ) (A.subst σ) := by
    obtain ⟨-, -, h3⟩ := body W
    rw [etaSpine_subst hcl.2.1]
    refine ⟨?_, ?_⟩
    · have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs) (b := R) (τ := .id)
        (hvl σ)
      rwa [subst_id, subst_vals hRbcl] at this
    · rw [hB.rhs, VEnv.lams_instL', hBs, hR, hA] at h3
      rwa [subst_vals hRbcl, subst_vals hAcl] at h3
  have lsteps {σ : VExpr.Subst} : StepS env U Γ₀ ((etaSpine Bs (.lams Bs L)).subst σ)
      (L.subst σ) := by
    rw [etaSpine_subst hcl.1]
    have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs) (b := L) (τ := .id) (hvl σ)
    rwa [subst_id, subst_vals hLbcl] at this
  have ldefeq {σ ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ (Bs.reverse ++ Γ) ρ) :
      env.IsDefEq U Γ₀ ((etaSpine Bs (.lams Bs L)).subst σ) (R.subst σ) (A.subst σ) := by
    obtain ⟨h1, h2, -⟩ := body W
    have h12 := h1.trans h2
    rw [hB.lhs, VEnv.lams_instL', hBs, hL, hR, hA] at h12
    rw [etaSpine_subst hcl.1]
    rwa [subst_vals hRbcl, subst_vals hAcl] at h12
  have onBsE₂ : OnCtx Bs.reverse (E₂.IsType U) := onBs.mono fun ⟨w, h⟩ => ⟨w, h.mono hEE⟩
  have hLR : E₂.IsDefEq U Bs.reverse ((VExpr.lams Bs L).appN (VExpr.bvars Bs.length 0)) R A := by
    have W := Ctx.SubstEq.vals (Γ := []) hE₂o onBsE₂ (by simpa using VEnv.Ctx.SubstEq.id hE₂o onBsE₂)
    simp only [subst_id, List.map_id'] at W
    obtain ⟨h1, h2, -⟩ := VEnv.IsDefEq.extra_body hE₂o onBsE₂ hdf₂ (hB.mono hEE) hls hlen'
      (as := VExpr.bvars Bs.length 0) (by simp [VExpr.bvars, ← hBs]) (by simpa [hBs] using W)
    rw [hB.lhs, VEnv.lams_instL', hBs, hL, hA] at h1
    rw [hL, hR, hA] at h2
    have e1 := subst_vals hLbcl .id
    have e2 := subst_vals hRbcl .id
    have e3 := subst_vals hAcl .id
    simp only [subst_id, List.map_id'] at e1 e2 e3
    have h12 := h1.trans h2
    rwa [e2, e3] at h12
  have hLS {ρ n} {m : WShape n} (hfit : LE_Interp.Valuation.Fits env Γ₀ (Bs.reverse ++ Γ) ρ)
      (hm : LE_Interp env ρ m.T (etaSpine Bs (.lams Bs L))) : LE_Interp env ρ m.T R := by
    have D := IsDefEq.weak_closed hE₂o onBsE₂ hLR Γ
    rw [etaSpine_eq, hcl.1.liftN_eq (Nat.zero_le _)] at hm
    exact ((hS₂ D).sound hfit).1 hm
  -- the context, split at the fields
  have hGΔ : Bs.reverse ++ Γ = Gs ++ Δ := by
    rw [hGs, hΔ, ← List.append_assoc, ← List.reverse_append, List.take_append_drop]
  have hGl : Gs.length = c.fields.length := by rw [hGs]; simp; omega
  have HT : ∀ i (h : i < Gs.length), ∃ u, env.HasType U (Gs.drop (i+1) ++ Δ) Gs[i] (.sort u) ∧
      StrongSoundEq env U (Gs.drop (i+1) ++ Δ) Gs[i] Gs[i] (.sort u) ∧
      AdeqStmt (U := U) henv hU Γ₀ (Gs.drop (i+1) ++ Δ) Gs[i] Gs[i] (.sort u) := by
    intro i hi
    have hk : d.params.length + d.allTypes.length + d.allCtors.length + (Gs.length - 1 - i) <
        Bs.length := by omega
    have e1 : Gs.drop (i+1) ++ Δ = (Bs.take (d.params.length + d.allTypes.length +
        d.allCtors.length + (Gs.length - 1 - i))).reverse ++ Γ := by
      subst hGs hΔ
      rw [List.drop_reverse, ← List.append_assoc, ← List.reverse_append, ← List.take_add]
      congr 3; simp only [List.length_reverse, List.length_drop]; omega
    have e2 : Gs[i] = Bs[d.params.length + d.allTypes.length + d.allCtors.length +
        (Gs.length - 1 - i)] := by
      subst hGs
      rw [List.getElem_reverse, List.getElem_drop]
      congr 1; simp only [List.length_reverse, List.length_drop]
    have hT := (VEnv.IsTele.append_inv (by rw [List.take_append_drop]; exact teleE :
      E.IsTele U [] (Bs.take (d.params.length + d.allTypes.length + d.allCtors.length +
        (Gs.length - 1 - i)) ++ Bs.drop (d.params.length + d.allTypes.length +
        d.allCtors.length + (Gs.length - 1 - i)))))
    have hon : OnCtx (Bs.take (d.params.length + d.allTypes.length + d.allCtors.length +
        (Gs.length - 1 - i))).reverse (E.IsType U) := by simpa using hT.1.onCtx (Γ := []) trivial
    rw [List.drop_eq_getElem_cons hk] at hT
    have hTy' : E.IsType U (Bs.take (d.params.length + d.allTypes.length + d.allCtors.length +
        (Gs.length - 1 - i))).reverse Bs[d.params.length + d.allTypes.length + d.allCtors.length +
        (Gs.length - 1 - i)] := by
      have := hT.2; simp only [List.append_nil] at this
      cases this with | cons h _ => exact h
    rw [e1, e2]
    exact hTy (OnCtx.append_closed hEo hEenv hΓ hon) ⟨_, rfl, hon, hTy'⟩
  intro ρ₀ n₀ m₀ a₀ hm₀ ha₀ hmem₀
  refine AdeqStmt.of_reds_conv hΓ' hΓ₀ hAenv hSA HA HS hLS F (fun {σ σ' ρ} W => ?_)
    (fun {σ ρ} W W2 => ?_) redR hm₀ ha₀ hmem₀
  · have W' : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Gs ++ Δ) ρ := hGΔ ▸ W
    have HFσ := HF (hGΔ ▸ W.left)
    rcases LR.SubstWF.replaceTop hM hΓ₀ Gs (τ := F σ) (hGΔ ▸ hΓ') W'
        (fun i hi => hFtop σ i (hGl ▸ hi)) HT
        (fun i hi hE => (HFσ i hi).1 hE (by
          obtain ⟨u, hT, -, -⟩ := HT i hi
          exact ⟨u, hT.substDF henvW.ordered hE.wf hΓ₀ hE⟩))
        (fun i hi => (HFσ i hi).2) with W2 | H
    · exact .inl (hGΔ ▸ W2)
    · refine .inr fun {n m} hm => ?_
      rw [hRform] at hm
      exact interp_bvar_appN_bot' (H _ (by omega)) hm
  · refine ⟨lsteps.trans ((hLform ▸ hstep (hGΔ ▸ W)).trans ?_),
      (ldefeq W).trans (hRenv.substDF henv hΓ' hΓ₀ (W2.symm.toSubstEq hΓ₀))⟩
    rw [hRhs, hB.rhs, VEnv.lams_instL', hBs, hR, ← hBlen]
    have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs) (b := R) (τ := .id)
      (hvl (F σ))
    rwa [subst_id, subst_vals hRbcl] at this

end

end LogRel
end Lean4Lean

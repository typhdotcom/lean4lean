import Lean4Lean.Theory.Typing.LogRel.IndStepOf

/-!
# An inductive block's iota rules in the logical relation

Under related substitutions of its binders, an iota rule's left body computes to its right body:
by iota on the constructor, by the K-like step at a proposition with large elimination (at chosen
proofs), or by structure eta (at the major premise's projections). Where the block eliminates only
into propositions, both bodies are proofs and the relation holds at `bot`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- A constructor application, as `ctorApp` builds it: the constructor at some levels, applied to
some parameters (the occurrence's, for an auxiliary type) and the fields. -/
theorem _root_.Lean4Lean.VInductiveType.ctorApp_split (T : VInductiveType) (c : VConstructor)
    (ls : List VLevel) (ps fs : List VExpr) :
    ∃ ls' qs, T.ctorApp c ls ps fs = (VExpr.const c.name ls').appN (qs ++ fs) ∧
      qs.length = (T.nested.map (·.args.length)).getD ps.length := by
  unfold VInductiveType.ctorApp
  split
  · next h => exact ⟨_, _, rfl, by simp [h]⟩
  · next n h => exact ⟨_, _, rfl, by simp [h]⟩

/-- The left body of an iota rule, at any substitution, steps by iota to the right-hand side at the
values of the binders, at levels where the block is not a proposition and the type is not a
structure with eta. -/
theorem iotaL_step {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hs : env.inducts s = some (d, t)) (hq : d.allCtors[q]? = some (j, c))
    (hj : d.allTypes[j]? = some Tj) (hidx : c.indices.length = Tj.indices.length)
    {ls : List VLevel} (hPA : ¬d.PropAt (d.blockLevels ls)) (hER : ¬d.EtaRec j (d.blockLevels ls))
    (Γ : List VExpr) (σ : VExpr.Subst) :
    Step env U Γ ((iotaL d (d.recLevels.map (·.inst ls)) ls j c).subst σ)
      ((d.iotaRhs ls q j c).appN ((VExpr.bvars (d.params.length + d.allTypes.length +
        d.allCtors.length + c.fields.length) 0).map (·.subst σ))) := by
  rw [iotaL_eq, VExpr.subst_appN, List.map_append, List.map_append, List.map_singleton,
    appN_append_singleton]
  simp only [VInductDecl.ctorAppAt, hj, Option.getD_some, VInductiveType.ctorApp_subst]
  obtain ⟨ls', qs, e1, e2⟩ := Tj.ctorApp_split c (d.recLevels.map (·.inst ls))
    ((VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
      (·.subst σ)) ((VExpr.bvars c.fields.length 0).map (·.subst σ))
  rw [e1]
  have hb : (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length)
      c.fields.length).map (·.subst σ) =
      (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
        (·.subst σ) ++
      (VExpr.bvars (d.allTypes.length + d.allCtors.length) c.fields.length).map (·.subst σ) := by
    rw [← List.map_append, Nat.add_assoc, ← bvars_append', Nat.add_assoc]
  have hb2 : (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length +
      c.fields.length) 0).map (·.subst σ) =
      (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
        (·.subst σ) ++
      (VExpr.bvars (d.allTypes.length + d.allCtors.length) c.fields.length).map (·.subst σ) ++
      (VExpr.bvars c.fields.length 0).map (·.subst σ) := by
    rw [← hb, ← List.map_append]; congr 1
    have := bvars_append' (d.params.length + d.allTypes.length + d.allCtors.length)
      c.fields.length 0
    simpa using this.symm
  rw [hb, hb2, VExpr.subst]
  refine Step.iota hs hq hj hPA hER (by simp [VExpr.bvars]) (by simp [VExpr.bvars])
    (by simp [hidx]) ?_ (by simp [VExpr.bvars])
  rw [e2]; simp [VInductDecl.ctorParams, VExpr.bvars]

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- Every context typed in an environment the model is sound for has a fitting valuation. -/
theorem SoundHyps.exists_fits (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
    (hO : E.Ordered) : ∀ {Γ : List VExpr}, OnCtx Γ (E.IsType U) →
      ∃ ρ, Valuation.Fits env [] Γ ρ
  | [], _ => ⟨_, .nil⟩
  | A :: Γ, ⟨hΓ, u, hA⟩ => by
    obtain ⟨ρ, W⟩ := SoundHyps.exists_fits hM hX hle hO hΓ
    have hS : SoundTy env Γ A (.sort u) := (hX.strongSound' hM hle hO hΓ hA).left.sound
    obtain ⟨a', -, ha', hT⟩ := InterpTyped.hsort (hS W) (.bot (n := 0))
    exact ⟨_, W.cons (InterpTyped.hsort (hS W)) ha' (TShape.HasType.bot' hT)⟩

/-- An iota rule is related where its sides are interpreted, given adequacy over the environment
`E` its bodies are typed in (the block's constants as axioms), and model soundness over `E` and
over an environment `E₂` with the rule. -/
theorem iotaRule_adeq (henvW : env.WF) (hM : ModelEnv env) {E E₂ : VEnv} (hEE : E ≤ E₂)
    (hE₂le : E₂ ≤ env) (hEo : E.Ordered) (hE₂o : E₂.Ordered)
    (hX : SoundHyps E env) (hX₂ : SoundHyps E₂ env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor}
    (hs : env.inducts s = some (d, t)) (hq : d.allCtors[q]? = some (j, c))
    {Tj : VInductiveType} (hj : d.allTypes[j]? = some Tj)
    (hidx : c.indices.length = Tj.indices.length)
    (hdf₂ : E₂.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c))
    {L₀ R₀ A₀ : VExpr}
    (hB : (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).BodyWF E
      (d.iotaBinders d.recLevels d.motiveLevel c) L₀ R₀ A₀)
    {Γ : List VExpr} {ls : List VLevel} (hΓ : OnCtx Γ (env.IsType U)) (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.recUVars)
    (HK : d.largeElim = true → d.PropAt (d.blockLevels ls) → AdeqStmt (U := U) henv hU Γ₀ Γ
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls))
    (HE : d.largeElim = true → ¬d.PropAt (d.blockLevels ls) → d.EtaRec j (d.blockLevels ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
        ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls) := by
  rcases Classical.em (d.largeElim = true ∧ d.PropAt (d.blockLevels ls)) with hK | hK
  · exact HK hK.1 hK.2
  rcases Classical.em (d.largeElim = true ∧ ¬d.PropAt (d.blockLevels ls) ∧
    d.EtaRec j (d.blockLevels ls)) with hE' | hE'
  · exact HE hE'.1 hE'.2.1 hE'.2.2
  have hEenv : E ≤ env := hEE.trans hE₂le
  have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hX.strongSound hM hEenv D
  have hS₂ : ∀ {Γ M N A}, E₂.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hX₂.strongSound hM hE₂le D
  -- the rule's left body, and the right-hand side `iota` steps to
  have hLform : L₀.instL ls = iotaL d (d.recLevels.map (·.inst ls)) ls j c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).1
    rw [VLevel.inst_map_id hlen, hB.lhs, VEnv.lams_instL', iotaRule_lhs] at h3
    exact (VExpr.lams_inj h3 (by simp [length_iotaBinders])).2
  have hBAform : (d.iotaBinders d.recLevels d.motiveLevel c).map (·.instL ls) =
        d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c ∧
      A₀.instL ls = iotaCT d (d.recLevels.map (·.inst ls)) j c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).2.2
    rw [VLevel.inst_map_id hlen, hB.type, VEnv.foralls_instL', iotaRule_type] at h3
    exact VExpr.foralls_inj h3 (by simp [length_iotaBinders])
  have hRhs : d.iotaRhs ls q j c =
      (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls := rfl
  generalize hdfe : d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c = df
    at hdf₂ hB hRhs
  have hdfu : df.uvars = d.recUVars := by subst hdfe; simp [VInductDecl.iotaRule]
  have hlen' : ls.length = df.uvars := hdfu ▸ hlen
  generalize hB0 : d.iotaBinders d.recLevels d.motiveLevel c = B₀ at hB
  rw [hB.lhs, hB.rhs, hB.type, VEnv.lams_instL', VEnv.lams_instL', VEnv.foralls_instL']
  generalize hBs : B₀.map (·.instL ls) = Bs
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
      E.IsDefEqStrong U (Δ ++ Γ) e1 e2 A := by
    have hcl := H.closedN' hEo.closed (hΔ.ctxClosed hEo)
    have := (H.strong hEo hΔ).weakN hEo (Ctx.LiftN.right (hΔ.ctxClosed hEo) Γ)
    rwa [hcl.1.liftN_eq (Nat.le_refl _), hcl.2.1.liftN_eq (Nat.le_refl _),
      hcl.2.2.liftN_eq (Nat.le_refl _)] at this
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
  have hBlen : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length +
      c.fields.length := by
    rw [← hBs, List.length_map, ← hB0, length_iotaBinders]
  generalize hL : L₀.instL ls = L at hLform hLt
  generalize hR : R₀.instL ls = R at hRt
  generalize hA : A₀.instL ls = A at hRt hLt hAt hPT ⊢
  -- the rule's sides are closed
  have hext : E₂.IsDefEq U [] (.lams Bs L) (.lams Bs R) (.foralls Bs A) := by
    have := VEnv.IsDefEq.extra (Γ := []) (uvars := U) hdf₂ hls hlen'
    rwa [hB.lhs, hB.rhs, hB.type, VEnv.lams_instL', VEnv.lams_instL', VEnv.foralls_instL', hBs,
      hL, hR, hA] at this
  have hcl := hext.closedN' hE₂o.closed trivial
  have onBsEnv : OnCtx Bs.reverse (env.IsType U) :=
    onBs.mono fun ⟨w, h⟩ => ⟨w, h.mono hEenv⟩
  have hΓ' : OnCtx (Bs.reverse ++ Γ) (env.IsType U) := OnCtx.append_closed hEo hEenv hΓ onBs
  obtain ⟨w₃, hAw⟩ := hAt
  have hAenv : env.HasType U (Bs.reverse ++ Γ) A (.sort w₃) :=
    ((IsDefEq.weak_closed hEo onBs hAw Γ).defeq).mono hEenv
  have HS : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) R R A := adeqE onBs hΓ' hRt
  have hRbcl : R.ClosedN Bs.length := by
    simpa using (hRt.closedN' hEo.closed (onBs.ctxClosed hEo)).1
  have hLbcl : L.ClosedN Bs.length := by
    simpa using (hLt.closedN' hEo.closed (onBs.ctxClosed hEo)).1
  have hAcl : A.ClosedN Bs.length := by
    simpa using (hLt.closedN' hEo.closed (onBs.ctxClosed hEo)).2.2
  have hBenv := hB.mono hEenv
  -- the rule's bodies at the values of related substitutions
  have body {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :=
    VEnv.IsDefEq.extra_body hEnvo hΓ₀ hdfE hBenv hls hlen'
      (as := (VExpr.bvars Bs.length 0).map (·.subst σ)) (by simp [VExpr.bvars, ← hBs])
      (by have := Ctx.SubstEq.vals hEnvo onBsEnv (W.toSubstEq hΓ₀).left
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
  -- the left side's spine is the right body, in `E₂`
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
  rcases Classical.em (d.largeElim = true) with hLE | hLE
  · rcases Classical.em (d.PropAt (d.blockLevels ls)) with hPA | hPA
    · exact (hK ⟨hLE, hPA⟩).elim
    · rcases Classical.em (d.EtaRec j (d.blockLevels ls)) with hER | hER
      · exact (hE' ⟨hLE, hPA, hER⟩).elim
      · intro ρ₀ n₀ m₀ a₀ hm₀ ha₀ hmem₀
        refine AdeqStmt.of_reds hΓ' hΓ₀ hAenv HS hLS id id (fun _ => rfl) (fun _ => rfl)
          (fun W => .inl W) (fun W => W) (fun W => .inl W) ?_ redR hm₀ ha₀ hmem₀
        intro σ ρ W
        refine ⟨lsteps.trans ?_, ldefeq W⟩
        rw [hLform]
        refine (StepS.single (iotaL_step hs hq hj hidx hPA hER Γ₀ σ)).trans ?_
        rw [hRhs, hB.rhs, VEnv.lams_instL', hBs, hR, ← hBlen]
        have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs) (b := R) (τ := .id)
          (hvl σ)
        rwa [subst_id, subst_vals hRbcl] at this
  · -- the block eliminates only into propositions: both bodies are proofs
    have hv : d.motiveLevel.inst ls = .zero := by
      simp [VInductDecl.motiveLevel, VInductDecl.LargeElim, hLE, VLevel.inst]
    have hBf : Bs = d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c := by
      rw [← hBs, ← hB0, hBAform.1]
    have hAf : A = iotaCT d (d.recLevels.map (·.inst ls)) j c := by rw [← hA, hBAform.2]
    -- the right body's type is a proposition
    have hw0 : levelRel w₃ = false := by
      obtain ⟨ρ', W'⟩ := SoundHyps.exists_fits hM hX hEenv hEo onBs
      have hjl := (List.getElem?_eq_some_iff.1 hj).1
      have hBl := length_iotaBinders d (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c
      have hi : d.params.length + j < Bs.length := by rw [hBf, hBl]; omega
      obtain ⟨Ps, hK, hPs⟩ := motiveType_liftN d (d.recLevels.map (·.inst ls))
        (d.motiveLevel.inst ls) j Tj (Bs.length - (d.params.length + j))
      have hBi : Bs[d.params.length + j] =
          d.motiveType (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) j Tj := by
        have := iotaBinders_motive d (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c hj
          (hBf ▸ hi)
        simpa [hBf] using this
      rw [← hBi] at hK
      have hL := Lookup.reverse_append Bs (Γ := []) (d.params.length + j) hi
      rw [List.append_nil] at hL
      have hCTe : A = (VExpr.bvar (Bs.length - 1 - (d.params.length + j))).appN
          (c.indices.map (fun e => (e.instL (d.recLevels.map (·.inst ls))).reseat
            (d.allTypes.length + d.allCtors.length) c.fields.length c.fields.length 0 0) ++
          [d.ctorAppAt j c (d.recLevels.map (·.inst ls)) (VExpr.bvars d.params.length
            (d.allTypes.length + d.allCtors.length + c.fields.length))
            (VExpr.bvars c.fields.length 0)]) := by
        rw [hAf, iotaCT, VExpr.appN_append_singleton, hBf, hBl]
        congr 3; omega
      have hle' := spine_sort_le hM hX hEenv hEo onBs _ _ _ Ps _ hK (by simp [hPs, hidx])
        (fun T hT' => by
          obtain ⟨A', hA', hS'⟩ := bvar_type_sound hM hX hEenv hEo onBs hT'
          cases hA'.uniq hL; exact hS'.symm.le) (.sort w₃) (hCTe ▸ hAw)
      have := levelRel_of_le hle' W'
      rw [this, hv]; simp [levelRel]; exact VLevel.equiv_def.2 fun _ => rfl
    intro ρ n m a hm ha hmem
    have hbot {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        m = .bot := by
      have D := IsDefEq.weak_closed hE₂o onBsE₂ hLR.hasType.1 Γ
      have S0 := hS₂ D
      have S5 := hS (IsDefEq.weak_closed hEo onBs hAw Γ)
      rw [etaSpine_eq, hcl.1.liftN_eq (Nat.zero_le _)] at hm
      exact TShape.le_bot.1 (StrongSound.proof_le_bot' S0.left S5.left hw0 W.fits hm)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
    · obtain rfl := hbot W
      exact ⟨(LR henv hU _).bot hmem.isType, (LR henv hU _).bot hmem.isType⟩
    · obtain rfl := hbot W
      exact (LR henv hU _).bot hmem.isType

end
/-- An iota rule at a proposition with large elimination, where the K-like step computes. -/
def IotaKCase : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq envR Γ₀ →
  ∀ {Γ q j c ls}, OnCtx Γ (env.IsType U) → d.allCtors[q]? = some (j, c) →
    (∀ l ∈ ls, l.WF U) → ls.length = d.recUVars → d.largeElim = true →
    d.PropAt (d.blockLevels ls) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls)

/-- An iota rule of a structure with eta, where the recursor computes at projections. -/
def IotaEtaCase : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq envR Γ₀ →
  ∀ {Γ q j c ls}, OnCtx Γ (env.IsType U) → d.allCtors[q]? = some (j, c) →
    (∀ l ∈ ls, l.WF U) → ls.length = d.recUVars → d.largeElim = true →
    ¬d.PropAt (d.blockLevels ls) → d.EtaRec j (d.blockLevels ls) →
    @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls)

/-- A block's iota rules, given the K-like and structure-eta cases. -/
theorem IndIotaCase.of (HK : IotaKCase) (HE : IotaEtaCase) : IndIotaCase := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
    envT envC envR h1 h2 h3 IHR Γ df ls u hΓ hdf hls hlen hu _ _ _ _ _ _ _
  letI := env.shapeEnv; letI := X
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  obtain ⟨q, j, c, hq, rfl⟩ := mem_iotaRules hdf
  have hlen' : ls.length = d.recUVars := by simpa [VInductDecl.iotaRule] using hlen
  have hEW : E.WF := ⟨_, hW⟩
  have hDc := hD
  cases hDc with
  | induct hd hg hadd =>
  have hadd' := hadd
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd'
  obtain ⟨envT', hT', envC', hC', envR', hR', hB'⟩ := hadd'
  cases h1.symm.trans hT'; cases h2.symm.trans hC'; cases h3.symm.trans hR'
  have hle : E' ≤ env := hext.le
  have HB : VEnv.BlockEnvs env d E envT envC envR := ⟨hEW, hd, hg, h1, h2, h3, ⟨E', hB', hle⟩⟩
  have hWR := HB.envR_wf
  have hOR := hWR.ordered
  have hleR := HB.envR_le
  have hE'W : E'.WF := ⟨_, .decl hD hW⟩
  have hDle : E ≤ E' := hD.le
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hDle (hdom c h)
  have hle₁ : E ≤ env := hDle.trans hle
  have hX₁ : SoundHyps E env := soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX)
    hW hle₁ (fun hdf e hx => VEnv.WF.rule_head hEW hdf e (hdomE _ hx))
    (VEnv.WF.noDomI hEW hdomE)
  have hXR : SoundHyps envR env :=
    hX₁.mono (fun h => HB.envR_defeqs ▸ h) (fun h => HB.envR_inducts ▸ h)
  have hX₂ : SoundHyps E' env := soundHyps_of hMX (quotRuleSound hMX henvW)
    (henvW.blockSound hMX) (.decl hD hW) hle
    (fun hdf e hx => VEnv.WF.rule_head hE'W hdf e (hdom _ hx)) (VEnv.WF.noDomI hE'W hdom)
  have hRE' : envR ≤ E' := VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB')
  have hmem : d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c ∈
      d.iotaRules := by
    simp only [VInductDecl.iotaRules, List.mem_map]
    exact ⟨((j, c), q), List.mk_mem_zipIdx_iff_getElem?.2 hq, rfl⟩
  have hdf₂ : E'.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c) := by
    rw [VEnv.addBlock_defeqs hB']; exact VEnv.addDefEqList_defeqs_of_mem hmem
  obtain ⟨T0, hT0⟩ : ∃ T0, d.types[0]? = some T0 := by
    cases e : d.types with
    | nil => exact (hd.nonempty e).elim
    | cons T _ => exact ⟨T, rfl⟩
  have hs0 : env.inducts T0.name = some (d, 0) := hle.inducts (addBlock_inducts_head hB' hT0)
  obtain ⟨Tj, hj, hcm⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
  have hcW := (hd.ctors envT h1 Tj (List.mem_of_getElem? hj)).2 c hcm
  have hIR := (hR envT envC envR h1 h2 h3).2.2
  have hdfR := (hg envT envC envR h1 h2 h3).2 _ hmem
  have hB := VEnv.VDefEq.WF.bodyWF hOR hIR hdfR rfl rfl rfl
  have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls) :=
    iotaRule_adeq henvW hMX hRE' hle hOR hE'W.ordered hXR hX₂ hΓ₀ IHR hs0 hq hj
    hcW.indices.1 hdf₂ hB hΓ hls hlen'
    (fun hLE hPA => HK henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHR hΓ hq hls
      hlen' hLE hPA)
    (fun hLE hPA hER => HE henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHR hΓ hq
      hls hlen' hLE hPA hER)
  exact @key

end LogRel
end Lean4Lean

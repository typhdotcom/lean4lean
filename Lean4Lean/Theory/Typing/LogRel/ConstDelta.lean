import Lean4Lean.Theory.Typing.LogRel.AdequacyOf

/-!
# Adequacy at a definition's constant

A definition's constant is related wherever its value is: the constant steps to the value (`delta`)
and every interpretation of the constant interprets the value. What the value's adequacy rests on
is left to the caller: for a definition, adequacy of its typing in the environment it was declared
in; for a recursive one, adequacy in a model where its own constants are interpreted only where
they are already related.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}

/-- An interpretation of a definition's constant interprets its value. -/
theorem LE_Interp.const_delta (hM : ModelEnv env) {ci : VDefVal} (hnd : ¬AxInterp.dom ci.name)
    (hdf : env.defeqs ci.toDefEq)
    (H : LE_Interp env ρ m (.const ci.name ls)) : LE_Interp env ρ m (ci.value.instL ls) := by
  have hlhs : ci.toDefEq.lhs = .const ci.name (VLevel.params ci.toDefEq.uvars) := rfl
  cases H with
  | bot => exact .bot
  | const _ _ h3 _ _ h6 h7 =>
    cases h6 with
    | bot => exact TShape.le_bot'.1 (h3.trans TShape.bot_eqv.1) ▸ .bot
    | lam he hle =>
      have := Const.lam_le_bot hM.roles he hle (r := .delta ci.toDefEq) (.delta hdf hlhs)
      exact TShape.le_bot'.1 (h3.trans this) ▸ .bot
    | ext a0 => exact (hnd a0).elim
    | delta _ a1 a2 a3 a4 a5 =>
      cases hM.stepUniq.delta hdf a1 hlhs a2
      exact (h7 _ _ a4).mono (h3.trans a5)
    | indTy a1 a2 => cases hM.roles (.delta hdf hlhs) (.indTy a1 a2)
    | ctor a1 a2 a3 a4 => cases hM.roles (.delta hdf hlhs) (.ctor a1 a2 a3 a4)
    | quotTy _ _ _ a4 => cases a4

/-- A definition's constant is related at every shape interpreting it, at levels `ls ≈ ls'`, given
that its value is. -/
theorem AdeqStmt.delta (hM : ModelEnv env) {ci : VDefVal} (hnd : ¬AxInterp.dom ci.name)
    (hdf : env.defeqs ci.toDefEq)
    (hlen : ls.length = ci.uvars) (hlen' : ls'.length = ci.uvars)
    (hbody : AdeqStmt (U := U) henv hU Γ₀ Γ (ci.value.instL ls) (ci.value.instL ls')
      (ci.type.instL ls)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ci.name ls) (.const ci.name ls') (ci.type.instL ls) := by
  intro ρ n m a hm ha hmem
  have ad := hbody (hm.const_delta hM hnd hdf) ha hmem
  have hv : (ci.value.instL ls).ClosedN := (hM.closed.defeq hdf).instL
  have hv' : (ci.value.instL ls').ClosedN := (hM.closed.defeq hdf).instL
  have hs : StepS env U Γ₀ (.const ci.name ls) (ci.value.instL ls) :=
    .single (.delta (df := ci.toDefEq) hdf rfl hlen)
  have hs' : StepS env U Γ₀ (.const ci.name ls') (ci.value.instL ls') :=
    .single (.delta (df := ci.toDefEq) hdf rfl hlen')
  have e1 {σ} : (ci.value.instL ls).subst σ = ci.value.instL ls := hv.subst_eq .zero
  have e2 {σ} : (ci.value.instL ls').subst σ = ci.value.instL ls' := hv'.subst_eq .zero
  have c1 {σ} : (VExpr.const ci.name ls).subst σ = .const ci.name ls := rfl
  have c2 {σ} : (VExpr.const ci.name ls').subst σ = .const ci.name ls' := rfl
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
  · have ⟨h1, h2⟩ := ad.1 W
    rw [e1, e1] at h1; rw [e2, e2] at h2; rw [c1, c1, c2, c2]
    exact ⟨((LR _ _ _).whr hs hs).2 h1, ((LR _ _ _).whr hs' hs').2 h2⟩
  · have h := ad.2 W
    rw [e1, e2] at h; rw [c1, c2]
    exact ((LR _ _ _).whr hs hs').2 h

/-- A definition declared in `E₀` is related wherever it is interpreted, given adequacy for `E₀`'s
derivations: its value's typing there, instantiated and weakened, is one. -/
theorem AdeqStmt.delta_decl (hM : ModelEnv env) {E₀ : VEnv} (hE₀ : E₀.Ordered) {ci : VDefVal}
    (hnd : ¬AxInterp.dom ci.name) (hv : ci.WF E₀) (hdf : env.defeqs ci.toDefEq)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls')
    (hlen : ls.length = ci.uvars)
    (HA₀ : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → OnCtx Γ (env.IsType U) →
      AdeqStmt (U := U) henv hU Γ₀ Γ M N A)
    (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ci.name ls) (.const ci.name ls') (ci.type.instL ls) := by
  have hlen' : ls'.length = ci.uvars := Lean4Lean.List.Forall₂.length_eq heq ▸ hlen
  have h1 : E₀.IsDefEq U [] (ci.value.instL ls) (ci.value.instL ls') (ci.type.instL ls) :=
    VEnv.IsDefEq.instL_r hE₀ (U' := ci.uvars) (Γ := []) trivial hls hls' heq hv
  intro ρ n m a x y z
  exact AdeqStmt.delta hM hnd hdf hlen hlen'
    (fun {_ _ _ _} => HA₀ ((h1.strong hE₀ (Γ := []) trivial).weak0 hE₀) hΓ) x y z

/-- A definition's rule is related wherever its constant is interpreted, given that its value is. -/
theorem AdeqStmt.delta_r (hM : ModelEnv env) {ci : VDefVal} (hnd : ¬AxInterp.dom ci.name)
    (hdf : env.defeqs ci.toDefEq)
    (hlen : ls.length = ci.uvars)
    (hbody : AdeqStmt (U := U) henv hU Γ₀ Γ (ci.value.instL ls) (ci.value.instL ls)
      (ci.type.instL ls)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ci.name ls) (ci.value.instL ls) (ci.type.instL ls) := by
  intro ρ n m a hm ha hmem
  have ad := hbody (hm.const_delta hM hnd hdf) ha hmem
  have hv : (ci.value.instL ls).ClosedN := (hM.closed.defeq hdf).instL
  have hs : StepS env U Γ₀ (.const ci.name ls) (ci.value.instL ls) :=
    .single (.delta (df := ci.toDefEq) hdf rfl hlen)
  have e1 {σ} : (ci.value.instL ls).subst σ = ci.value.instL ls := hv.subst_eq .zero
  have c1 {σ} : (VExpr.const ci.name ls).subst σ = .const ci.name ls := rfl
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩
  · have ⟨h1, h2⟩ := ad.1 W
    rw [e1, e1] at h1; rw [c1, c1]
    exact ⟨((LR _ _ _).whr hs hs).2 h1, h2⟩
  · have h := ad.2 W
    rw [e1] at h; rw [c1, e1]
    exact ((LR _ _ _).whr hs .rfl).2 h

/-- Adding a definition keeps adequacy's environment cases: its constant is related by its value's
adequacy in the environment before it, and its rule by its value's. -/
theorem AdequacyHyps.addDef (hM : ModelEnv env) {E E₁ : VEnv} (hEo : E.Ordered)
    (H : AdequacyHyps (U := U) henv hU E Γ₀) {ci : VDefVal} (hnd : ¬AxInterp.dom ci.name)
    (hv : ci.WF E)
    (h1 : E.addConst ci.name ci.toVConstant = some E₁) (hle : E₁.addDefEq ci.toDefEq ≤ env)
    (hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) :
    AdequacyHyps (U := U) henv hU (E₁.addDefEq ci.toDefEq) Γ₀ := by
  have hE : E ≤ env := (VEnv.addConst_le h1).trans (VEnv.addDefEq_le.trans hle)
  have hdf : env.defeqs ci.toDefEq := hle.defeqs (.inl rfl)
  have HA₀ : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → OnCtx Γ (env.IsType U) →
      AdeqStmt (U := U) henv hU Γ₀ Γ M N A := fun D hΓ => LR.adequacy_of hM hE hS hΓ₀ H D hΓ
  have hinds : (E₁.addDefEq ci.toDefEq).inducts = E.inducts := (VEnv.addConst_inducts h1 :)
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu _ _ hA => ?_,
    fun {Γ df ls u} hΓ hd hls hlen hu _ _ _ _ _ hL hR => ?_,
    fun hΓ h => H.projDF hΓ (hinds ▸ h), fun hΓ h => H.projIota hΓ (hinds ▸ h),
    fun hΓ h => H.projEta hΓ (hinds ▸ h)⟩
  · change E₁.constants c = some ci' at hc
    unfold VEnv.addConst at h1; split at h1 <;> cases h1
    simp only at hc; split at hc
    · next e =>
      subst e; cases hc
      exact AdeqStmt.delta_decl hM hEo hnd hv hdf hls hls' heq hlen HA₀ hΓ
    · exact H.const hΓ hc hls hls' hlen heq hu ‹_› ‹_› hA
  · rcases hd with rfl | hd
    · have hlen' : ls.length = ci.uvars := hlen
      have e : ci.toDefEq.lhs.instL ls = .const ci.name ls :=
        congrArg _ (VLevel.inst_map_id (n := ci.uvars) hlen')
      show AdeqStmt (U := U) henv hU Γ₀ Γ (ci.toDefEq.lhs.instL ls) (ci.value.instL ls)
        (ci.type.instL ls)
      rw [e]; exact AdeqStmt.delta_r hM hnd hdf hlen' hR
    · rw [VEnv.addConst_defeqs h1] at hd
      exact H.extra hΓ hd hls hlen hu ‹_› ‹_› ‹_› ‹_› ‹_› hL hR

/-- A constant with no role in the environment is interpreted only by `bot`. -/
theorem LE_Interp.Const.le_bot_of_noRole (hnr : ∀ r k, ¬ConstArity env c r k)
    (H : Const env c ls R rargs m) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | lam _ m_le ih =>
    exact m_le.trans ((WShape.lam'_le_bot fun x y h => WShape.LE.T_iff.1
      ((ih x y h).trans TShape.bot_eqv.2)).T.trans TShape.bot_eqv.1)
  | ext _ h1 h2 => exact (hnr _ _ (.delta h1 h2)).elim
  | delta _ h1 h2 => exact (hnr _ _ (.delta h1 h2)).elim
  | indTy h1 h2 => exact (hnr _ _ (.indTy h1 h2)).elim
  | ctor h1 h2 h3 h4 => exact (hnr _ _ (.ctor h1 h2 h3 h4)).elim
  | iota h1 h2 _ h4 => exact (hnr _ _ (.recursor h1 h2 h4)).elim
  | kIota h1 h2 _ h4 => exact (hnr _ _ (.recursor h1 h2 h4)).elim
  | quotTy h1 h2 => exact (hnr _ _ (.quotTy h1 h2)).elim
  | quotMk h1 h2 => exact (hnr _ _ (.quotMk h1 h2)).elim
  | quot h1 h2 => exact (hnr _ _ (.quotLift h1 h2)).elim
  | quotK h1 h2 => exact (hnr _ _ (.quotLift h1 h2)).elim

/-- A constant with no role is related everywhere it is interpreted: only at `bot`. -/
theorem AdeqStmt.noRole (hnr : ∀ r k, ¬ConstArity env c r k) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const c ls) (.const c ls') A := by
  intro ρ n m a hm _ hmem
  have : m.T ≤ TShape.bot := by
    cases hm with
    | bot => exact TShape.bot_eqv.1
    | const _ _ h3 _ _ h6 => exact h3.trans (h6.le_bot_of_noRole hnr)
  cases show m = .bot from TShape.le_bot.1 (this.trans TShape.bot_le)
  exact .bot hmem.isType

/-- Adding a constant with no rules and no role keeps adequacy's environment cases. -/
theorem AdequacyHyps.addNoRole (H : AdequacyHyps (U := U) henv hU E Γ₀) {E₁ : VEnv}
    (h1 : E.addConst c ci = some E₁) (hnr : ∀ r k, ¬ConstArity env c r k) :
    AdequacyHyps (U := U) henv hU E₁ Γ₀ := by
  have hinds : E₁.inducts = E.inducts := VEnv.addConst_inducts h1
  refine ⟨fun {Γ c' ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => H.extra hΓ (VEnv.addConst_defeqs h1 ▸ hd),
    fun hΓ h => H.projDF hΓ (hinds ▸ h), fun hΓ h => H.projIota hΓ (hinds ▸ h),
    fun hΓ h => H.projEta hΓ (hinds ▸ h)⟩
  unfold VEnv.addConst at h1; split at h1 <;> cases h1
  simp only at hc; split at hc
  · next e => subst e; exact AdeqStmt.noRole hnr
  · exact H.const hΓ hc hls hls' hlen heq hu h7 h8 hA

end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.Adequacy

/-!
# Adequacy of the logical relation, given the cases that read the environment's rules

Upstream's `LR.adequacy` (`Experimental/ShapeLogRelAdequacy.lean`), by induction on a strong
derivation, for every rule that does not read the environment. The constants, rule instances and
projections are taken as hypotheses (`AdequacyHyps`), each assuming the induction's statement for
its premises.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}

variable (henv hU) in
/-- The induction's statement for `Γ ⊢ M ≡ N : A`: related at every pair of shapes interpreting
`M` and `A`. -/
def AdeqStmt (Γ₀ Γ : List VExpr) (M N A : VExpr) : Prop :=
  ∀ {ρ n} {m a : WShape n}, LE_Interp env ρ m.T M → LE_Interp env ρ a.T A → m.HasType a →
    LR.Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a

omit [ShapeEnv] in
theorem StepS.beta_subst : StepS env U Γ ((VExpr.app (.lam A e) a).subst σ) ((e.inst a).subst σ) := by
  rw [subst_inst]; exact .single .beta

omit [ShapeEnv] in
theorem StepS.eta_subst {e : VExpr} :
    StepS env U Γ (.app ((VExpr.lam A (.app e.lift (.bvar 0))).subst σ) x) (.app (e.subst σ) x) := by
  have : ((VExpr.app e.lift (.bvar 0)).subst σ.lift).inst x = .app (e.subst σ) x := by
    have h1 : (VExpr.app e.lift (.bvar 0)).subst σ.lift = .app (e.subst σ).lift (.bvar 0) := by
      show VExpr.app (e.lift.subst σ.lift) _ = _; rw [lift_subst_lift]; rfl
    rw [h1]; show VExpr.app ((e.subst σ).lift.inst x) (instVar 0 x) = _; rw [inst_lift, instVar_zero]
  exact .single (this ▸ .beta)

omit [ShapeEnv] in
theorem StepS.beta_cons {X Y : VExpr} {τ : VExpr.Subst} :
    StepS env U Γ (.app ((VExpr.lam X Y).subst τ) x) (Y.subst (τ.cons x)) := by
  rw [← inst_lift_cons]; exact .single .beta

omit [AxInterp] in
theorem LRS.LamDefEq.app_red {IH : LogRel env U Γ n}
    (hA₁ : env.HasType U Γ A₁ (.sort u)) (hA₂ : env.HasType U (A₁::Γ) A₂ (.sort v))
    (h1 : ∀ x, env.HasType U Γ x A₁ → TRed env U Γ (M₁.app x) (N₁.app x) (A₂.inst x))
    (h2 : ∀ x, env.HasType U Γ x A₁ → TRed env U Γ (M₂.app x) (N₂.app x) (A₂.inst x)) :
    LRS.LamDefEq IH N₁ N₂ A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M₁ M₂ A₁ A₂ m a₁ a₂
  | ⟨p1, p2⟩ =>
    have r {M N a b : VExpr} (h : ∀ x, env.HasType U Γ x A₁ → TRed env U Γ (M.app x) (N.app x) (A₂.inst x))
        (ha : env.IsDefEq U Γ a b A₁) : TRed env U Γ (M.app b) (N.app b) (A₂.inst a) :=
      (h _ ha.hasType.2).defeqDF (instDF_ty hA₁ hA₂ ha).symm
    ⟨fun _ _ _ hp ha hv =>
      ⟨(IH.whr (h1 _ ha.hasType.1) (r h1 ha)).2 (p1 hp ha hv).1,
        (IH.whr (h2 _ ha.hasType.1) (r h2 ha)).2 (p1 hp ha hv).2⟩,
    fun _ _ hp ha hv => (IH.whr (h1 _ ha) (h2 _ ha)).2 (p2 hp ha hv)⟩

omit [AxInterp] in
theorem LRS.LamClause.app_red {IH : LogRel env U Γ n}
    (h1 : ∀ x, env.HasType U Γ x X → TRed env U Γ (M₁.app x) (N₁.app x) (Y.inst x))
    (h2 : ∀ x, env.HasType U Γ x X → TRed env U Γ (M₂.app x) (N₂.app x) (Y.inst x)) :
    LRS.LamClause IH N₁ N₂ (.forallE X Y) f a₁ a₂ → LRS.LamClause IH M₁ M₂ (.forallE X Y) f a₁ a₂
  | ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP⟩ => by
    cases StepS.of_whnf forallE_whnf rA
    exact ⟨_, _, u, v, rA, eA, hA1, hA2, hA₂, hE, hP.app_red hA1 hA₂ h1 h2⟩

omit [ShapeEnv] [AxInterp] in
/-- Beta at a lambda under a substitution, typed at a type the substitution is related to. -/
theorem TRed.beta_at (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ Γ)
    (Wτσ : VEnv.Ctx.SubstEq env U Γ₀ τ σ Γ) (hX : env.HasType U Γ X (.sort u))
    (Hb : env.HasType U (X::Γ) Y B) (hBX : env.HasType U (X::Γ) B (.sort v))
    (hx : env.HasType U Γ₀ x (X.subst τ)) :
    TRed env U Γ₀ (.app ((VExpr.lam X Y).subst τ) x) (Y.subst (τ.cons x)) (B.subst (σ.cons x)) := by
  refine ⟨StepS.beta_cons, ?_⟩
  have hXτ := hX.subst henv Wτ hΓ₀
  have hb := Hb.subst henv (Wτ.lift henv hX) ⟨hΓ₀, _, hXτ⟩
  have hβ := VEnv.IsDefEq.beta hb hx
  rw [inst_lift_cons, inst_lift_cons] at hβ
  have hΓX : OnCtx (X::Γ) (env.IsType U) := ⟨hΓ, _, hX⟩
  exact .defeqDF (hBX.substDF henv hΓX hΓ₀
    (VEnv.Ctx.SubstEq.cons (σ := τ.cons x) (σ' := σ.cons x) Wτσ hX hx)) hβ

theorem LR.SubstWF.bvar (hM : ModelEnv env) (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
    Lookup Γ i A → m.T ≤ ρ i → LE_Interp env ρ a.T A → m.HasType a →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq ((VExpr.bvar i).subst σ) ((VExpr.bvar i).subst σ')
      (A.subst σ) m a := by
  induction W generalizing i A with
  | id =>
    intro _ hle _ hmem
    cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
    exact (LR _ _ _).bot hmem.isType
  | cons W' _ _ _ _ h0 ih =>
    intro h hle hA hmem
    cases h with
    | zero => exact lift_subst ▸ (h0.2 a hA).2 (.bvar hle) hmem
    | succ h' => exact lift_subst ▸ ih h' hle ((LE_Interp.weak_iff hM.closed).1 hA) hmem

variable (henv hU) in
/-- The cases of adequacy that read the environment's rules and blocks: constants, rule instances
and projections, each given the induction's statement for its premises. -/
structure AdequacyHyps (E : VEnv) (Γ₀ : List VExpr) : Prop where
  const : ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → E.constants c = some ci →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
    env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls)
  extra : ∀ {Γ df ls u}, OnCtx Γ (env.IsType U) → E.defeqs df → (∀ l ∈ ls, l.WF U) →
    ls.length = df.uvars → u.WF U →
    env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
    env.IsDefEqStrong U [] (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U [] (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)
  projDF : ∀ {Γ s d t T c k f ls As I As' I' e e' u}, OnCtx Γ (env.IsType U) →
    E.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length → I.length = T.indices.length →
    As'.length = d.params.length → I'.length = T.indices.length →
    u.WF U → (f.level.inst ls).WF U → d.ProjAllowed c ls k →
    env.IsDefEqStrong U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u) →
    env.IsDefEqStrong U Γ e e' (.appN (.const s ls) (As ++ I)) →
    env.IsDefEqStrong U Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const s ls) (As ++ I))
      (.appN (.const s ls) (As' ++ I')) (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e e' (.appN (.const s ls) (As ++ I)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    StrongSoundEq env U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u) →
    StrongSoundEq env U Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    StrongSoundEq env U Γ e e' (.appN (.const s ls) (As ++ I)) →
    StrongSoundEq env U Γ (.proj s k e) (.proj s k e') (c.projType ls s k As e) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.proj s k e) (.proj s k e') (c.projType ls s k As e)
  projIota : ∀ {Γ s d t T c k f fs a ls As I u}, OnCtx Γ (env.IsType U) →
    E.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → fs[k]? = some a → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length → fs.length = c.fields.length → I.length = T.indices.length →
    u.WF U → (f.level.inst ls).WF U → d.ProjAllowed c ls k →
    env.IsDefEqStrong U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I))
      (.sort u) →
    env.IsDefEqStrong U Γ (.appN (.const c.name ls) (As ++ fs))
      (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)) →
    env.IsDefEqStrong U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) (.sort (f.level.inst ls)) →
    env.IsDefEqStrong U Γ a a (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I))
      (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const c.name ls) (As ++ fs))
      (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) (.sort (f.level.inst ls)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ a a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) →
    StrongSoundEq env U Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
  projEta : ∀ {Γ s d t T c ls As e u}, OnCtx Γ (env.IsType U) →
    E.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] → T.indices = [] →
    d.isRec = false → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length → (∀ k < c.fields.length, d.ProjAllowed c ls k) → u.WF U →
    env.IsDefEqStrong U Γ (.appN (.const s ls) As) (.appN (.const s ls) As) (.sort u) →
    env.IsDefEqStrong U Γ e e (.appN (.const s ls) As) →
    env.IsDefEqStrong U Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const s ls) As) (.appN (.const s ls) As) (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e e (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    StrongSoundEq env U Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As)

/-- The cases only read which constants, rules and blocks `E` has, so they hold of any smaller
environment. -/
theorem AdequacyHyps.mono (H : AdequacyHyps (U := U) henv hU E' Γ₀) (h : E ≤ E') :
    AdequacyHyps (U := U) henv hU E Γ₀ where
  const hΓ h1 := H.const hΓ (h.constants h1)
  extra hΓ h1 := H.extra hΓ (h.defeqs h1)
  projDF hΓ h1 := H.projDF hΓ (h.inducts h1)
  projIota hΓ h1 := H.projIota hΓ (h.inducts h1)
  projEta hΓ h1 := H.projEta hΓ (h.inducts h1)

/-- The application case of adequacy at one pair of substitutions: `F X` is related at an
interpretation `m` below the application of interpretations `f` of `F` and `x` of `X`. -/
theorem LR.appCore (hM : ModelEnv env) {Γ Γ₀ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {ρ : Valuation} {n nf : Nat} {m a : WShape n}
    {f : WShape (nf+1)} {x : WShape nf} {A B : VExpr} {v : VLevel}
    (hmem : m.HasType a) (le_m : m.T ≤ (f.app x).T) {F F' X X'} {σ σ' : VExpr.Subst}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ)
    (hX : env.IsDefEq U Γ X X' A)
    (hif : LE_Interp env ρ f.T F) (hia : LE_Interp env ρ x.T X)
    (hA : LE_Interp env ρ a.T (B.inst X))
    (hFs : StrongSoundEq env U Γ F F' (.forallE A B))
    (hBs : StrongSoundEq env U Γ (B.inst X) (B.inst X') (.sort v))
    (ihf : ∀ {n'} {mf af : WShape n'}, LE_Interp env ρ mf.T F →
      LE_Interp env ρ af.T (.forallE A B) → mf.HasType af →
      LR.Adequate (U := U) henv hU Γ₀ Γ ρ F F' (.forallE A B) mf af)
    (iha : ∀ {n'} {ma aa : WShape n'}, LE_Interp env ρ ma.T X → LE_Interp env ρ aa.T A →
      ma.HasType aa → LR.Adequate (U := U) henv hU Γ₀ Γ ρ X X' A ma aa)
    (ihBa : ∀ {n'} {mb av : WShape n'}, LE_Interp env ρ mb.T (B.inst X) →
      LE_Interp env ρ av.T (.sort v) → mb.HasType av →
      LR.Adequate (U := U) henv hU Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq ((VExpr.app F X).subst σ)
      ((VExpr.app F' X').subst σ') ((B.inst X).subst σ) m a := by
  have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ := (hFs.left.sound W.fits hif).out
  have Af := ihf hf' hPi hmf
  by_cases hm0 : mf = .bot
  · simp only [hm0] at le_mf hmf
    refine (?_ : m = .bot) ▸ (LR _ _ _).bot hmem.isType
    cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
    exact TShape.le_bot.1 ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
  cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
  cases hmf.unfold with | bot => cases hm0 rfl | lam hg => ?_ | _ =>
    first
    | exact absurd le TShape.sort_not_le_forallE
    | exact absurd le TShape.indTy_not_le_forallE
  rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ g
  simp at le_nf
  let k := max n (max n₁ n₂); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have ⟨x', le_x', hx'_a₁, hgx2⟩ := WShape.HasDom.iff.1 hg.2.1 (x.lift _)
  have hia' := (hia.lift le_nf).mono le_x'.T
  have hax' := ((LE_Interp.forallE' haA hbA hd hiB).mono le).forallE_inv hM |>.2 hia'
  have hJ := TShape.Join.mk (hA.compat hM hax')
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
  have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
  have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
  have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
  have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
  have hJ_t := TShape.HasType.sort_r.2 hmem.isType
    |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
  have hmem_k := (WShape.HasType.lift hk.1).2 hmem
  rw [subst_inst]
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
  refine (LR.DefEq.lift hk.1 hmem).1 <| (LR _ _ _).mono_r_2 hJ1' hmem_k hJ_t' ?_
  have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
  refine (LR _ _ _).mono_l ?_ (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hgx'') ?_
  · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
      (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans (WShape.lam'_app ▸ hgx2.T)
  refine (LR _ _ _).mono_r_1 hJ2' hgx'' (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
  · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
      (hBs.left.sound W.fits (hA.join hM hJ hax')).out
    exact (LR _ _ _).left_ty <| (LR.TyDefEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
      subst_inst ▸ LR.toValTy le_j le_j' (TShape.HasType.sort_r.1 hJ_t) hSj hmj
        ((ihBa hBj hSj hmj).2 W.left)
  · have hAf := (LR _ _ _).trans (Af.2 W.left) (Af.1 W).2
    simp only [LR, LRS] at hAf
    unfold WShape.lam' at hAf; split at hAf
    · rw [LRS.DefEq.lam_forallE] at hAf
      rcases hAf with ⟨_, _, _, _, red, _, _, _, _, _, valPi⟩ | hn
      · cases StepS.of_whnf forallE_whnf red
        have le' := (TShape.LE.def (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
        simp only [WShape.T, WShape.lift_forallE hk.2.2, WShape.lift_forallE hk.2.1,
          WShape.forallE_le_forallE] at le'
        have Aa := iha hia' (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
        have := (LR _ _ _).trans (Aa.2 W.left) (Aa.1 W).2
        have hXσ := hX.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
        exact (LR.DefEq.lift hk.2.2 hgx').2 <| (LR _ _ _).trans
          (valPi.2 hx'_a₁ hXσ.hasType.1 <| (LR _ _ _).left this)
          (valPi.1 hx'_a₁ hXσ this).2
      · exact (NeRed.not_forallE hU hn .rfl).elim
    · refine (hm0 ?_).elim; unfold WShape.lam'; simp_all



theorem LR.adequacy_of (hM : ModelEnv env) {E : VEnv} (hE : E ≤ env)
    (hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (hH : AdequacyHyps (U := U) henv hU E Γ₀)
    (H : E.IsDefEqStrong U Γ M N A) (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ M N A := by
  induction H with
  | @bvar Γ i A _ h _ _ =>
    intro ρ n m a hM' hA hmem
    exact .refl fun _ _ W => LR.SubstWF.bvar hM W h (LE_Interp.bvar_iff.1 hM') hA hmem
  | symm H ih =>
    intro ρ n m a hM' hA hmem
    exact .fits fun W => (ih hΓ (((hS H).sound W).2 hM') hA hmem).symm
  | trans H1 _ ih1 ih2 =>
    intro ρ n m a hM' hA hmem
    exact .fits fun W => (ih1 hΓ hM' hA hmem).trans (ih2 hΓ (((hS H1).sound W).1 hM') hA hmem)
  | @sortDF l _ _ _ _ hll =>
    intro ρ n m a hM' hA hmem
    have key {u v : VLevel} (huv : u ≈ v) :
        (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.sort u) (.sort v) (.sort (.succ l)) m a := by
      obtain h | h := WShape.le_sort.1 hM'.le_sort'
      · subst h; exact (LR _ _ _).bot hmem.isType
      · subst h
        obtain ha | ha := WShape.le_sort.1 hA.le_sort'
        · subst ha; have := congrArg (·.1) hmem.bot_r; cases n <;> cases this
        · subst ha; exact (LR _ _ _).sort_iff.2 (.inl ⟨_, _, .rfl, .rfl, huv⟩)
    refine ⟨fun _ _ _ => ⟨key (rfl : VLevel.Equiv _ _), key (rfl : VLevel.Equiv _ _)⟩,
      fun _ _ => key hll⟩
  | @defeqDF Γ' A₁ B₁ _ _ _ _ Hty _ ihTy ihE =>
    intro ρ n m a hM' hA hmem
    have tyConv {σ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ' ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (A₁.subst σ) (B₁.subst σ) a := by
      have hA' := ((hS Hty).sound W.fits).2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := ((hS Hty).left.sound W.fits hA').out
      exact LR.toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hΓ hA'' hSort hmem').2 W)
    have tyEq {σ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ' ρ) :
        TyEq env U Γ₀ (A₁.subst σ) (B₁.subst σ) :=
      .base ((Hty.defeq.mono hE).subst henv (W.toSubstEq hΓ₀) hΓ₀)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := ((hS Hty).sound W.left.fits).2 hA
    · exact ⟨(LR _ _ _).conv (tyEq W.left) (tyConv W.left) ((ihE hΓ hM' hA' hmem).1 W).1,
        (LR _ _ _).conv (tyEq W.left) (tyConv W.left) ((ihE hΓ hM' hA' hmem).1 W).2⟩
    · exact (LR _ _ _).conv (tyEq W) (tyConv W) ((ihE hΓ hM' hA' hmem).2 W)
  | proofIrrel Hp _ _ =>
    intro ρ n m a hM' hA hmem
    refine .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := ((hS Hp).left.sound W hA).out
    have hS' := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; rw [levelRel_zero] at hS'
    have ha' := hS'.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS'.proofIrrel ha')
    exact .bot hmem.isType
  | beta a1 a2 HA HB He He' HBi Hinst _ _ _ _ _ ihinst =>
    intro ρ n m a hM' hA hmem
    have HS := hS (.beta a1 a2 HA HB He He' HBi Hinst)
    refine .fits fun W' => ?_
    have hN := (HS.sound W').1 hM'
    have IN := ihinst hΓ hN hA hmem
    have Hb := (VEnv.IsDefEqStrong.beta a1 a2 HA HB He He' HBi Hinst).defeq.mono hE
    have hT := HBi.defeq.mono hE
    have tl {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' _ ρ) :=
      (⟨StepS.beta_subst, Hb.subst henv (W.left.toSubstEq hΓ₀) hΓ₀⟩ :
        TRed env U Γ₀ _ _ _)
    have tr {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' _ ρ) :=
      (⟨StepS.beta_subst, .defeqDF (hT.substDF henv hΓ hΓ₀ (W.symm.toSubstEq hΓ₀))
        (Hb.subst henv (W.symm.left.toSubstEq hΓ₀) hΓ₀)⟩ : TRed env U Γ₀ _ _ _)
    refine ⟨fun σ σ' W => ⟨?_, (IN.1 W).2⟩, fun σ W => ?_⟩
    · exact ((LR _ _ _).whr (tl W) (tr W)).2 (IN.1 W).1
    · exact ((LR _ _ _).whr (tl W) (.refl (tl W).2.hasType.2)).2 (IN.2 W)
  | eta a1 a2 HA HB HB' He He' HAl _ _ _ ihe _ _ =>
    intro ρ n m a hM' hA hmem
    have HS := hS (.eta a1 a2 HA HB HB' He He' HAl)
    refine .fits fun W' => ?_
    have IN := ihe hΓ ((HS.sound W').1 hM') hA hmem
    have key {M₁ M₂ N₁ N₂ X Y}
        (h1 : ∀ x, env.HasType U Γ₀ x X → TRed env U Γ₀ (M₁.app x) (N₁.app x) (Y.inst x))
        (h2 : ∀ x, env.HasType U Γ₀ x X → TRed env U Γ₀ (M₂.app x) (N₂.app x) (Y.inst x))
        (H : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq N₁ N₂ (.forallE X Y) m a) :
        (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M₁ M₂ (.forallE X Y) m a := by
      cases hmem.unfold with
      | bot hm => exact (LR _ _ _).bot hm
      | sort => cases n <;> let .lam _ _ _ h := hM' <;> cases TShape.sort_not_le_lam' h
      | forallE => let .lam _ _ _ h := hM'; cases TShape.forallE_not_le_lam' h
      | ctor => let .lam _ _ _ h := hM'; cases TShape.ctor_not_le_lam' h
      | indTy => let .lam _ _ _ h := hM'; cases TShape.indTy_not_le_lam' h
      | @lam n' g a₁ a₂ htm =>
        revert H; unfold WShape.lam'
        split <;> intro H <;> [skip; exact (LR _ _ _).bot hmem.isType]
        simp only [LR, LRS, LRS.DefEq.lam_forallE] at H ⊢
        exact H.imp (LRS.LamClause.app_red h1 h2) id
    have He := (VEnv.IsDefEqStrong.eta a1 a2 HA HB HB' He He' HAl).defeq.mono hE
    have hT := VEnv.IsDefEq.forallEDF (HA.defeq.mono hE) (HB.defeq.mono hE)
    have tl {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' _ ρ) x
        (hx : env.HasType U Γ₀ x _) :=
      (⟨StepS.eta_subst, .appDF (He.subst henv (W.left.toSubstEq hΓ₀) hΓ₀) hx⟩ :
        TRed env U Γ₀ _ _ _)
    have tr {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' _ ρ) x
        (hx : env.HasType U Γ₀ x _) :=
      (⟨StepS.eta_subst, .appDF (.defeqDF (hT.substDF henv hΓ hΓ₀ (W.symm.toSubstEq hΓ₀))
        (He.subst henv (W.symm.left.toSubstEq hΓ₀) hΓ₀)) hx⟩ : TRed env U Γ₀ _ _ _)
    exact ⟨fun σ σ' W => ⟨key (tl W) (tr W) (IN.1 W).1,
      (IN.1 W).2⟩, fun σ W => key (tl W) (fun x hx => .refl (tl W x hx).2.hasType.2) (IN.2 W)⟩
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 _ ih8 => exact hH.const hΓ h1 h2 h3 h4 h5 h6 (h7.mono hE) (h8.mono hE) (ih8 hΓ)
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact hH.extra hΓ h1 h2 h3 h4 (h5.mono hE) (h6.mono hE) (h7.mono hE) (h8.mono hE)
      (h9.mono hE) (ih8 hΓ) (ih9 hΓ)
  | projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 ih14 ih15 ih16 =>
    exact hH.projDF hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (h14.mono hE) (h15.mono hE)
      (h16.mono hE)
      (ih14 hΓ) (ih15 hΓ) (ih16 hΓ) (hS h14) (hS h16) (hS h15)
      (hS (.projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16))
  | projIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 ih14 ih15 ih16 ih17 =>
    exact hH.projIota hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (h14.mono hE) (h15.mono hE)
      (h16.mono hE) (h17.mono hE)
      (ih14 hΓ) (ih15 hΓ) (ih16 hΓ) (ih17 hΓ)
      (hS (.projIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17))
  | projEta h1 h2 h3 h4 h5 h6 h7 h8 hPA h9 h10 h11 h12 ih10 ih11 ih12 =>
    exact hH.projEta hΓ h1 h2 h3 h4 h5 h6 h7 h8 hPA h9 (h10.mono hE) (h11.mono hE) (h12.mono hE)
      (ih10 hΓ) (ih11 hΓ) (ih12 hΓ)
      (hS (.projEta h1 h2 h3 h4 h5 h6 h7 h8 hPA h9 h10 h11 h12))
  | @forallEDF Γ A A' u body body' v _ _ HA HB HB' ihA ihB _ =>
    intro ρ n m a hM' hA hmem
    have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, (HA.defeq.mono hE).hasType.1⟩
    cases hmem.unfold with
    | bot hm => exact .bot hm
    | sort => cases n <;> have .forallE _ _ _ _ h := hM' <;> cases TShape.sort_not_le_forallE h
    | @lam _ f₀ =>
      revert hM'; unfold WShape.lam'; split <;> [skip; exact fun _ => .bot hmem.isType]
      intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
    | ctor => have .forallE _ _ _ _ h := hM'; cases TShape.ctor_not_le_forallE h
    | indTy => have .forallE _ _ _ _ h := hM'; cases TShape.indTy_not_le_forallE h
    | @forallE k a₂ a₁ r aty =>
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := (hM'.forallE_inv' hM).1
    have cons := LR.Adequate.cons hM hΓ hΓ₀ (hS HA).left.sound (ihA hΓ) (HA.defeq.mono hE)
    -- the codomains, at a related value of the domain
    have body_rel {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (body.subst (σ₁.cons x)) (body.subst (σ₂.cons x'))
          (a₂.app p) ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (body'.subst (σ₁.cons x))
          (body'.subst (σ₂.cons x')) (a₂.app p) := by
      have hB := (hM'.forallE_inv' hM).2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := ((hS HB).left.sound W'.fits hB).out
      have I := (ihB hΓA iB iv hmb).1 W'
      exact ⟨LR.toValTy le le' (aty.2 _ hp).toType iv hmb I.1,
        LR.toValTy le le' (aty.2 _ hp).toType iv hmb I.2⟩
    have body_rel' {σ : VExpr.Subst} {x p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ.cons x) (σ.cons x) (A::Γ) (ρ.push p.T)) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (body.subst (σ.cons x)) (body'.subst (σ.cons x))
          (a₂.app p) := by
      have hB := (hM'.forallE_inv' hM).2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := ((hS HB).left.sound W'.fits hB).out
      exact LR.toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB hΓA iB iv hmb).2 W')
    have hdom {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A.subst σ) (A.subst σ') a₁ ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A'.subst σ) (A'.subst σ') a₁ := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := ((hS HA).left.sound W.fits hA1).out
      have I := (ihA hΓ hA' hSort hmem').1 W
      exact ⟨LR.toValTy le_n le_a aty.1.isType hSort hmem' I.1,
        LR.toValTy le_n le_a aty.1.isType hSort hmem' I.2⟩
    have hdom' {σ : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A.subst σ) (A'.subst σ) a₁ := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := ((hS HA).left.sound W.fits hA1).out
      exact LR.toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hΓ hA' hSort hmem').2 W)
    have mkPi {B₁ F₁ B₂ F₂ X} (hB : TyEq env U Γ₀ B₁ B₂) (hF : TyEq env U (B₁::Γ₀) F₁ F₂)
        (hV : (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq B₁ B₂ a₁)
        (hE : LRS.PiDefEq (LR (U := U) (Γ := Γ₀) henv hU k) B₁ F₁ F₂ a₁ a₂)
        (hT1 : ∀ w, TyEq env U Γ₀ X (.sort w) →
          LRS.TyTyped (LR (U := U) (Γ := Γ₀) henv hU k) (.forallE B₁ F₁) (WShape.forallE a₁ a₂) ∧
          LRS.TyTyped (LR (U := U) (Γ := Γ₀) henv hU k) (.forallE B₂ F₂) (WShape.forallE a₁ a₂)) :
        (LR (U := U) (Γ := Γ₀) henv hU (k+1)).DefEq (.forallE B₁ F₁) (.forallE B₂ F₂) X
          (WShape.forallE a₁ a₂) (.sort r) := by
      simp only [LR, LRS, LRS.DefEq.sort_a, LRS.TyDefEq.forallE_iff]
      exact ⟨.inl ⟨_, _, _, _, .rfl, .rfl, hB, hF, hV, hE⟩, hT1⟩
    have mkTy {B F : VExpr} {u' v'} (hBt : env.HasType U Γ₀ B (.sort u'))
        (hFt : env.HasType U (B::Γ₀) F (.sort v'))
        (y : (LR (U := U) (Γ := Γ₀) henv hU k).TyTy B a₁)
        (hY : ∀ x p, p.HasType a₁ → env.HasType U Γ₀ x B →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x B p a₁ →
          (LR (U := U) (Γ := Γ₀) henv hU k).TyTy (F.inst x) (a₂.app p)) :
        LRS.TyTyped (LR (U := U) (Γ := Γ₀) henv hU k) (.forallE B F) (WShape.forallE a₁ a₂) :=
      (LRS.TyTyped.forallE_iff).2 (.inr ⟨B, F, u', v', .rfl, .refl (.forallE hBt hFt), hBt, hFt, y, hY⟩)
    have hAt := (HA.defeq.mono hE).hasType.1
    have hA't := (HA.defeq.mono hE).hasType.2
    have SΓ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :=
      W.toSubstEq hΓ₀
    have hAσ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        env.IsDefEq U Γ₀ (A.subst σ) (A.subst σ') (.sort u) := hAt.substDF henv hΓ hΓ₀ (SΓ W)
    have hA'σ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        env.IsDefEq U Γ₀ (A'.subst σ) (A'.subst σ') (.sort u) := hA't.substDF henv hΓ hΓ₀ (SΓ W)
    have hAA'σ {σ : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ) :
        env.IsDefEq U Γ₀ (A.subst σ) (A'.subst σ) (.sort u) := (HA.defeq.mono hE).subst henv (SΓ W) hΓ₀
    have hΓ₀A {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        OnCtx (A.subst σ :: Γ₀) (env.IsType U) := ⟨hΓ₀, _, (hAσ W).hasType.1⟩
    have hΓ₀A' {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        OnCtx (A'.subst σ :: Γ₀) (env.IsType U) := ⟨hΓ₀, _, (hA'σ W).hasType.1⟩
    have hΓA' : OnCtx (A'::Γ) (env.IsType U) := ⟨hΓ, _, hA't⟩
    have huWF := (HA.defeq.mono hE).sort_r henv hΓ
    have hvWF := (HB.defeq.mono hE).sort_r henv hΓA
    have domTy {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyTy (A.subst σ) a₁ ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).TyTy (A'.subst σ) a₁ := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := ((hS HA).left.sound W.fits hA1).out
      have I := (ihA hΓ hA' hSort hmem').1 W
      have hu : TyEq env U Γ₀ (.sort u) (.sort u) := .refl (.sort huWF)
      exact ⟨(LR.toTyTy le_n le_a aty.1.isType hSort hmem' hu I.1).1,
        (LR.toTyTy le_n le_a aty.1.isType hSort hmem' hu I.2).1⟩
    have codTy {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyTy (body.subst (σ₁.cons x)) (a₂.app p) ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).TyTy (body'.subst (σ₁.cons x)) (a₂.app p) := by
      have hB := (hM'.forallE_inv' hM).2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := ((hS HB).left.sound W'.fits hB).out
      have I := (ihB hΓA iB iv hmb).1 W'
      have hv : TyEq env U Γ₀ (.sort v) (.sort v) := .refl (.sort hvWF)
      exact ⟨(LR.toTyTy le le' (aty.2 _ hp).toType iv hmb hv I.1).1,
        (LR.toTyTy le le' (aty.2 _ hp).toType iv hmb hv I.2).1⟩
    have tyL {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        LRS.TyTyped (LR (U := U) (Γ := Γ₀) henv hU k) (.forallE (A.subst σ) (body.subst σ.lift))
          (WShape.forallE a₁ a₂) :=
      mkTy (hAσ W).hasType.1
        ((HB.defeq.mono hE).hasType.1.substDF henv hΓA (hΓ₀A W) ((SΓ W).lift henv hAt)).hasType.1
        (domTy W).1 fun x p hp hx hv => by
          simp only [inst_lift_cons]; exact (codTy hp (cons hp hA1 hx hv W.left)).1
    have tyR {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        LRS.TyTyped (LR (U := U) (Γ := Γ₀) henv hU k) (.forallE (A'.subst σ) (body'.subst σ.lift))
          (WShape.forallE a₁ a₂) :=
      mkTy (hA'σ W).hasType.1
        ((HB'.defeq.mono hE).hasType.2.substDF henv hΓA' (hΓ₀A' W) ((SΓ W).lift henv hA't)).hasType.1
        (domTy W).2 fun x p hp hx hv => by
          simp only [inst_lift_cons]
          have hc := (LR _ _ _).symm_ty (hdom' W.left)
          exact (codTy hp (cons hp hA1 ((hAA'σ W.left).symm.defeqDF hx)
            ((LR _ _ _).conv (.base (hAA'σ W.left).symm) hc hv) W.left)).2
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · refine mkPi (.base (hAσ W))
        (.base ((HB.defeq.mono hE).hasType.1.substDF henv hΓA (hΓ₀A W) ((SΓ W).lift henv hAt))) (hdom W).1
        ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩ (fun _ _ => ⟨tyL W, tyL W.symm⟩) <;>
        simp only [inst_lift_cons]
      · refine ⟨(body_rel hp (cons hp hA1 hx hv W.left)).1, ?_⟩
        have hv' := (LR _ _ _).conv (.base (hAσ W)) (hdom W).1 hv
        exact (body_rel hp (cons hp hA1 ((hAσ W).defeqDF hx) hv' W.symm.left)).1
      · exact (body_rel hp (cons hp hA1 hx hv W)).1
    · have hc := (LR _ _ _).symm_ty (hdom' W.left)
      refine mkPi (.base (hA'σ W))
        (.base ((HB'.defeq.mono hE).hasType.2.substDF henv hΓA' (hΓ₀A' W) ((SΓ W).lift henv hA't))) (hdom W).2
        ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩ (fun _ _ => ⟨tyR W, tyR W.symm⟩) <;>
        simp only [inst_lift_cons]
      · have hx₁ := (hAA'σ W.left).symm.defeqDF hx
        have hv₁ := (LR _ _ _).conv (.base (hAA'σ W.left).symm) hc hv
        refine ⟨(body_rel hp (cons hp hA1 hx₁ hv₁ W.left)).2, ?_⟩
        have hv' := (LR _ _ _).conv (.base (hAσ W)) (hdom W).1 hv₁
        exact (body_rel hp (cons hp hA1 ((hAσ W).defeqDF hx₁) hv' W.symm.left)).2
      · have hx₁ := (hAA'σ W.left).symm.defeqDF hx
        exact (body_rel hp (cons hp hA1 hx₁ ((LR _ _ _).conv (.base (hAA'σ W.left).symm) hc hv) W)).2
    · refine mkPi (.base (hAA'σ W))
        (.base ((HB.defeq.mono hE).substDF henv hΓA (hΓ₀A W) ((SΓ W).lift henv hAt))) (hdom' W)
        ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩ (fun _ _ => ⟨tyL W, tyR W⟩) <;>
        simp only [inst_lift_cons]
      · exact body_rel hp (cons hp hA1 hx hv W)
      · exact body_rel' hp (cons hp hA1 hx hv W)
  | @lamDF Γ A A' u B v body body' _ _ HA HB HB' HBody HBody' ihA ihB _ ihBody _ =>
    intro ρ n m a hM' hA hmem
    have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, (HA.defeq.mono hE).hasType.1⟩
    cases hmem.unfold with
    | bot hm => exact .bot hm
    | sort => cases n <;> let .lam _ _ _ h := hM' <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM'; cases TShape.forallE_not_le_lam' h
    | ctor => let .lam _ _ _ h := hM'; cases TShape.ctor_not_le_lam' h
    | indTy => let .lam _ _ _ h := hM'; cases TShape.indTy_not_le_lam' h
    | @lam k g a₁ a₂ htm =>
    revert hM'; unfold WShape.lam'; split <;> intro hM' <;> [skip; exact .bot hmem.isType]
    rename_i hg
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := (hA.forallE_inv' hM).1
    have cons := LR.Adequate.cons hM hΓ hΓ₀ (hS HA).left.sound (ihA hΓ) (HA.defeq.mono hE)
    have htmF := (WShape.HasTypeLam.iff.1 htm).2.2
    have IB {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :=
      ihBody hΓA (hM'.lam_inv' hM p) ((hA.forallE_inv' hM).2 p) (htmF p hp)
    have TB {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (B.subst (σ₁.cons x)) (B.subst (σ₂.cons x'))
          (a₂.app p) := by
      have hB := (hA.forallE_inv' hM).2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := ((hS HB).left.sound W'.fits hB).out
      exact LR.toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB hΓA iB iv hmb).1 W').1
    have hdom {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A.subst σ) (A.subst σ') a₁ := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := ((hS HA).left.sound W.fits hA1).out
      exact LR.toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hΓ hA' hSort hmem').1 W).1
    have hAt := (HA.defeq.mono hE).hasType.1
    have hAσ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        env.IsDefEq U Γ₀ (A.subst σ) (A.subst σ') (.sort u) :=
      hAt.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
    -- the lambda clause, at the type `(forallE A B).subst σ`
    have hA't := (HA.defeq.mono hE).hasType.2
    have hAA'σ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        env.IsDefEq U Γ₀ (A.subst σ) (A'.subst σ') (.sort u) :=
      (HA.defeq.mono hE).substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
    have bt {σ τ : VExpr.Subst} {X Y : VExpr} (Wτ : LR.SubstWF (U := U) henv hU Γ₀ τ τ Γ ρ)
        (Wτσ : LR.SubstWF (U := U) henv hU Γ₀ τ σ Γ ρ) (hX : env.HasType U Γ X (.sort u))
        (Hb : env.HasType U (X::Γ) Y B) (hBX : env.HasType U (X::Γ) B (.sort v))
        (hXA : ∀ x, env.HasType U Γ₀ x (A.subst σ) → env.HasType U Γ₀ x (X.subst τ)) :
        ∀ x, env.HasType U Γ₀ x (A.subst σ) → TRed env U Γ₀ (.app ((VExpr.lam X Y).subst τ) x)
          (Y.subst (τ.cons x)) (B.subst (σ.cons x)) :=
      fun x hx => TRed.beta_at henv hΓ hΓ₀ (Wτ.toSubstEq hΓ₀) (Wτσ.toSubstEq hΓ₀) hX Hb hBX
        (hXA x hx)
    have mkLam {X₁ Y₁ X₂ Y₂ : VExpr} {σ σ₁ σ₂ : VExpr.Subst}
        (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ)
        (t1 : ∀ x, env.HasType U Γ₀ x (A.subst σ) → TRed env U Γ₀
          (.app ((VExpr.lam X₁ Y₁).subst σ₁) x) (Y₁.subst (σ₁.cons x)) (B.subst (σ.cons x)))
        (t2 : ∀ x, env.HasType U Γ₀ x (A.subst σ) → TRed env U Γ₀
          (.app ((VExpr.lam X₂ Y₂).subst σ₂) x) (Y₂.subst (σ₂.cons x)) (B.subst (σ.cons x)))
        (h1 : ∀ {x x' p}, p.HasType a₁ → env.IsDefEq U Γ₀ x x' (A.subst σ) →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁ →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (Y₁.subst (σ₁.cons x)) (Y₁.subst (σ₁.cons x'))
            (B.subst (σ.cons x)) (g.app p) (a₂.app p) ∧
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (Y₂.subst (σ₂.cons x)) (Y₂.subst (σ₂.cons x'))
            (B.subst (σ.cons x)) (g.app p) (a₂.app p))
        (h2 : ∀ {x p}, p.HasType a₁ → env.HasType U Γ₀ x (A.subst σ) →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x (A.subst σ) p a₁ →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (Y₁.subst (σ₁.cons x)) (Y₂.subst (σ₂.cons x))
            (B.subst (σ.cons x)) (g.app p) (a₂.app p)) :
        (LR (U := U) (Γ := Γ₀) henv hU (k+1)).DefEq ((VExpr.lam X₁ Y₁).subst σ₁)
          ((VExpr.lam X₂ Y₂).subst σ₂) ((VExpr.forallE A B).subst σ) (WShape.lam g hg)
          (WShape.forallE a₁ a₂) := by
      simp only [LR, LRS, LRS.DefEq.lam_forallE]
      have hΓ₀A : OnCtx (A.subst σ :: Γ₀) (env.IsType U) := ⟨hΓ₀, _, (hAσ W).hasType.1⟩
      have hBσ := (HB.defeq.mono hE).subst henv ((W.toSubstEq hΓ₀).lift henv hAt) hΓ₀A
      have cv {x x'} (hx : env.IsDefEq U Γ₀ x x' (A.subst σ)) :
          env.IsDefEq U Γ₀ (B.subst (σ.cons x')) (B.subst (σ.cons x)) (.sort v) := by
        have := (instDF_ty (hAσ W).hasType.1 hBσ hx).symm
        rwa [inst_lift_cons, inst_lift_cons] at this
      refine .inl ⟨A.subst σ, B.subst σ.lift, u, v, .rfl,
        TyEq.refl (VEnv.IsDefEq.forallEDF (hAσ W).hasType.1 hBσ), (hAσ W).hasType.1, hdom W,
        hBσ, ⟨fun x x' p hp hx hv => ?_,
        fun x p hp hx hv => ?_⟩, ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩⟩ <;>
        simp only [inst_lift_cons]
      · have := TB hp (cons hp hA1 hx hv W); exact ⟨this, this⟩
      · exact TB hp (cons hp hA1 hx hv W)
      · have ⟨r1, r2⟩ := h1 hp hx hv
        exact ⟨((LR _ _ _).whr (t1 _ hx.hasType.1) ((t1 _ hx.hasType.2).defeqDF (cv hx))).2 r1,
          ((LR _ _ _).whr (t2 _ hx.hasType.1) ((t2 _ hx.hasType.2).defeqDF (cv hx))).2 r2⟩
      · exact ((LR _ _ _).whr (t1 _ hx) (t2 _ hx)).2 (h2 hp hx hv)
    -- the bodies at the other substitution, converted to the type at `σ`
    have other {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {x x' p}
        (hp : p.HasType a₁) (hx : env.IsDefEq U Γ₀ x x' (A.subst σ))
        (hv : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁) :
        (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (body.subst (σ'.cons x))
          (body.subst (σ'.cons x')) (B.subst (σ.cons x)) (g.app p) (a₂.app p) ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (body'.subst (σ'.cons x))
          (body'.subst (σ'.cons x')) (B.subst (σ.cons x)) (g.app p) (a₂.app p) := by
      have W2 := cons hp hA1 ((hAσ W).defeqDF hx) ((LR _ _ _).conv (.base (hAσ W)) (hdom W) hv)
        W.symm.left
      have W3 := cons hp hA1 hx.hasType.1 ((LR _ _ _).left hv) W
      have hc := (LR _ _ _).symm_ty (TB hp W3)
      have hcE : TyEq env U Γ₀ (B.subst (σ'.cons x)) (B.subst (σ.cons x)) :=
        .base ((HB.defeq.mono hE).substDF henv hΓA hΓ₀ (W3.toSubstEq hΓ₀)).symm
      have r := (IB hp W2).1 W2
      exact ⟨(LR _ _ _).conv hcE hc r.1, (LR _ _ _).conv hcE hc r.2⟩
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · refine mkLam W.left (bt W.left W.left hAt (HBody.defeq.mono hE).hasType.1 (HB.defeq.mono hE) fun _ => id)
        (bt W.symm.left W.symm hAt (HBody.defeq.mono hE).hasType.1 (HB.defeq.mono hE) fun _ hx => (hAσ W).defeqDF hx)
        (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W.left
        exact ⟨((IB hp W1).1 W1).1, (other W hp hx hv).1⟩
      · have W1 := cons hp hA1 hx hv W
        exact ((IB hp W1).1 W1).1
    · refine mkLam W.left (bt W.left W.left hA't (HBody'.defeq.mono hE).hasType.2 (HB'.defeq.mono hE) fun _ hx => (hAA'σ W.left).defeqDF hx)
        (bt W.symm.left W.symm hA't (HBody'.defeq.mono hE).hasType.2 (HB'.defeq.mono hE) fun _ hx => (hAA'σ W).defeqDF hx)
        (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W.left
        exact ⟨((IB hp W1).1 W1).2, (other W hp hx hv).2⟩
      · have W1 := cons hp hA1 hx hv W
        exact ((IB hp W1).1 W1).2
    · refine mkLam W (bt W W hAt (HBody.defeq.mono hE).hasType.1 (HB.defeq.mono hE) fun _ => id)
        (bt W W hA't (HBody'.defeq.mono hE).hasType.2 (HB'.defeq.mono hE) fun _ hx => (hAA'σ W).defeqDF hx)
        (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W
        exact ((IB hp W1).1 W1)
      · have W1 := cons hp hA1 hx hv W
        exact (IB hp W1).2 W1
  | @appDF Γ A u B v F F' X X' _ _ HA HB Hf Ha HBa ihA ihB ihf iha ihBa =>
    intro ρ n m a hM' hA hmem
    cases hM' with
    | bot => exact .bot hmem.isType
    | @app _ nf_app f _ _ _ x hif hia le_m =>
    have core {F F' X X'} {σ σ' : VExpr.Subst} W hX hif hia hA hFs hBs ihf iha ihBa :=
      @LR.appCore env U _ _ henv hU hM Γ Γ₀ hΓ hΓ₀ ρ n _ m a f x A B v hmem le_m F F' X X' σ σ' W hX hif hia hA hFs hBs ihf iha ihBa
    have HsF := hS Hf; have HsX := hS Ha; have HsB := hS HBa
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W =>
      core W (Ha.defeq.mono hE) hif hia hA HsF HsB (ihf hΓ) (iha hΓ) (ihBa hΓ)⟩
    · exact core W (Ha.defeq.mono hE).hasType.1 hif hia hA (.rfl HsF.left) (.rfl HsB.left)
        (fun hf hPi hmf => (ihf hΓ hf hPi hmf).left) (fun ha hA hma => (iha hΓ ha hA hma).left)
        (fun hB hv hmb => (ihBa hΓ hB hv hmb).left)
    · have hc : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((B.inst X).subst σ)
          ((B.inst X').subst σ) a := by
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (HsB.left.sound W.fits hA).out
        exact LR.toValTy le le' hmem.isType iv hmb ((ihBa hΓ iB iv hmb).2 W.left)
      refine (LR _ _ _).conv (.base ((HBa.defeq.mono hE).subst henv (W.left.toSubstEq hΓ₀) hΓ₀).symm)
        ((LR _ _ _).symm_ty hc) <| core W (Ha.defeq.mono hE).hasType.2
        ((HsF.sound W.fits).1 hif) ((HsX.sound W.fits).1 hia) ((HsB.sound W.fits).1 hA)
        (.rfl HsF.right) (.rfl HsB.right) (fun hf hPi hmf => ?_) (fun ha hA hma => ?_)
        (fun hB hv hmb => ?_)
      · exact (ihf hΓ ((HsF.sound W.fits).2 hf) hPi hmf).symm.left
      · exact (iha hΓ ((HsX.sound W.fits).2 ha) hA hma).symm.left
      · exact (ihBa hΓ ((HsB.sound W.fits).2 hB) hv hmb).symm.left


end LogRel
end Lean4Lean

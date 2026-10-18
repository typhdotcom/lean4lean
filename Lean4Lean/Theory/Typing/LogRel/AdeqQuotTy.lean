import Lean4Lean.Theory.Typing.LogRel.AdeqQuotMk
import Lean4Lean.Theory.Typing.LogRel.AdeqQuotLiftQ
import Lean4Lean.Theory.Typing.LogRel.AdeqTypes

/-!
# The quotient type former's constant case

`Quot` applied to its telescope's variables is related at the sort it lives in, as an application
of an inert type former whose one constructor's telescope, `Quot.mk`'s field `a : α`, is related
through the relation of `α`. With `Quot.mk`'s and `Quot.lift`'s cases this gives the quotient's
step to adequacy's environment cases (`QuotStep`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp]

omit [AxInterp] in
/-- A shape below an inductive type shape is `bot` or an inductive type shape with its head. -/
theorem WShape.le_indTy_cases {m : WShape (n+1)} {r : Bool} {h : IndHead} {l : List (WShape k)}
    (hle : m.T ≤ (WShape.indTy r h l).T) : m = .bot ∨ ∃ l', m = WShape.indTy r h l' := by
  have' le₁ := Nat.le_max_left n k; have' le₂ := Nat.le_max_right n k
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂), WShape.lift_indTy le₂] at hle
  rcases WShape.le_indTy.1 hle with h0 | ⟨l', h1, -⟩
  · cases m using WShape.casesOn' with
    | bot => exact .inl rfl
    | sort r' =>
      simp only [WShape.T, WShape.lift_sort] at h0; have := congrArg (·.1) h0
      simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot] at this
    | forallE a f =>
      rw [WShape.lift_forallE le₁] at h0; have := congrArg (·.1) h0
      simp [WShape.forallE, WShape.bot, Shape.bot] at this
    | lam f hl =>
      rw [WShape.lift_lam le₁] at h0; have := congrArg (·.1) h0
      simp [WShape.lam, WShape.bot, Shape.bot] at this
    | ctor c fs hf =>
      rw [WShape.ctor_eq_ctor', WShape.lift_ctor' le₁] at h0
      unfold WShape.ctor' at h0; split at h0
      · have := congrArg (·.1) h0; simp [WShape.ctor, WShape.bot, Shape.bot] at this
      · rename_i hz; exact (hz ((WShape.ListNonZero.lift_iff le₁).2 ∘ hf)).elim
    | indTy r' h' l'' =>
      rw [WShape.lift_indTy le₁] at h0; have := congrArg (·.1) h0
      simp [WShape.indTy, WShape.bot, Shape.bot] at this
  · cases m using WShape.casesOn' with
    | bot => exact .inl rfl
    | sort r' =>
      simp only [WShape.T, WShape.lift_sort] at h1; have := congrArg (·.1) h1
      simp [WShape.sort, WShape.indTy, Shape.sort] at this
    | forallE a f =>
      rw [WShape.lift_forallE le₁] at h1; have := congrArg (·.1) h1
      simp [WShape.forallE, WShape.indTy] at this
    | lam f hl =>
      rw [WShape.lift_lam le₁] at h1; have := congrArg (·.1) h1
      simp [WShape.lam, WShape.indTy] at this
    | ctor c fs hf =>
      rw [WShape.ctor_eq_ctor', WShape.lift_ctor' le₁] at h1
      unfold WShape.ctor' at h1; split at h1
      · have := congrArg (·.1) h1; simp [WShape.ctor, WShape.indTy] at this
      · have := congrArg (·.1) h1; simp [WShape.bot, WShape.indTy, Shape.bot] at this
    | indTy r' h' l'' =>
      rw [WShape.lift_indTy le₁] at h1
      obtain ⟨rfl, rfl, -⟩ := WShape.indTy.inj.1 h1
      exact .inr ⟨l'', rfl⟩


omit [AxInterp] in
/-- At depth 0, only `bot` is below an inductive type shape. -/
theorem WShape.le_indTy_zero {m : WShape 0} {r : Bool} {h : IndHead} {l : List (WShape k)}
    (hle : m.T ≤ (WShape.indTy r h l).T) : m = .bot := by
  have' le₂ := Nat.le_max_right 0 k
  rw [TShape.LE.def (Nat.zero_le (k+1)) (Nat.le_refl _)] at hle
  rw [WShape.lift_indTy (Nat.le_refl k)] at hle
  rcases WShape.le_indTy.1 hle with h0 | ⟨l', h1, -⟩
  · obtain ⟨mv, wf⟩ := m
    cases mv with
    | bot => rfl
    | sort r' =>
      rw [show (⟨Shape0.sort r', wf⟩ : WShape 0) = WShape.sort r' from rfl] at h0
      simp only [WShape.T, WShape.lift_sort] at h0; have := congrArg (·.1) h0
      simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot] at this
  · obtain ⟨mv, wf⟩ := m
    cases mv with
    | bot => rfl
    | sort r' =>
      rw [show (⟨Shape0.sort r', wf⟩ : WShape 0) = WShape.sort r' from rfl] at h1
      simp only [WShape.T, WShape.lift_sort] at h1; have := congrArg (·.1) h1
      simp [WShape.sort, WShape.indTy, Shape.sort] at this

/-- An interpretation of the quotient applied to two arguments is below `bot` or an inductive type
shape. -/
theorem quotTyApp_le (hM : ModelEnv env) (hdf : env.defeqs quotDefEq) {ρ : Valuation} {u : VLevel}
    {A R : VExpr} {m : TShape} (H : LE_Interp env ρ m (.app (.app (.const ``Quot [u]) A) R)) :
    m ≤ TShape.bot ∨ ∃ k r h, ∃ l : List (WShape k), m ≤ (WShape.indTy r h l).T := by
  have hA : ConstArity env ``Quot .quotTy 2 := .quotTy hdf rfl
  have H' : LE_Interp env ρ m (spine ``Quot [u] [R, A]) := by
    rw [show [R, A] = [A, R].reverse from rfl, spine_eq_appN]; exact H
  obtain ⟨n0, H0⟩ := H'.spine_inv hM.roles (fun h => hM.domRole h hA) (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y, hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 2 := by rw [List.Forall₂.length_eq hra]; simp
  cases hC with
  | bot => exact .inl (hyy.trans TShape.bot_eqv.1)
  | lam he hle => exact .inl (hyy.trans (Const.lam_le_bot hM.roles he hle (hrl ▸ hA)))
  | ext h0 => exact (hM.domRole h0 hA).elim
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotTy _ _ _ _ _ _ _ h8 => exact .inr ⟨_, _, _, _, hyy.trans h8⟩


/-- The quotient type former's telescope at a level. -/
def quotTyTele (u : VLevel) : List VExpr :=
  [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))]

omit [ShapeEnv] [AxInterp] in
theorem quot_type' (u : VLevel) : quotConst.type.instL [u] = .foralls (quotTyTele u) (.sort u) := rfl

omit [ShapeEnv] [AxInterp] in
/-- `Quot.mk`'s field telescope at the quotient's parameters. -/
theorem ctorTeleAt_quotMk (x : VLevel) (A R : VExpr) :
    ctorTeleAt quotMkConst 1 [x] [A, R] =
      .forallE A ((VExpr.app (.app (.const ``Quot [x]) (.bvar 2)) (.bvar 1)).subst
        (Subst.id.consList [A, R]).lift) := by
  rw [ctorTeleAt, quotMk_type, show piCount quotMkConst.type - 1 = 2 from rfl,
    show quotMkTele x = [.sort x, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))] ++
      [.bvar 1] from rfl, VExpr.foralls_append, piInst_foralls _ _ _ (by simp)]
  rfl

variable {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- The quotient applied to its telescope's variables, under related substitutions and at levels
equivalent to `u`: related at its sort. -/
theorem quotTySpine_core (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hq : env.constants ``Quot = some quotConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst) (hni : env.inducts ``Quot = none)
    {u : VLevel} (hu : u.WF U) {Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotTyTele u).reverse ++ Γ) ρ)
    {ls₁ ls₂ : List VLevel} (hl₁ : ∀ l ∈ ls₁, l.WF U) (hl₂ : ∀ l ∈ ls₂, l.WF U)
    (e₁ : List.Forall₂ (· ≈ ·) [u] ls₁) (e₂ : List.Forall₂ (· ≈ ·) [u] ls₂)
    {n : Nat} {m a : WShape n} (hma : m.HasType a)
    (hm : LE_Interp env ρ m.T (.app (.app (.const ``Quot [u]) (.bvar 1)) (.bvar 0))) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
      (.app (.app (.const ``Quot ls₁) (σ 1)) (σ 0))
      (.app (.app (.const ``Quot ls₂) (σ' 1)) (σ' 0)) (.sort u) m a := by
  have hEo := henvW.ordered
  obtain ⟨u₁, rfl, eu₁⟩ : ∃ u₁, ls₁ = [u₁] ∧ u ≈ u₁ := by
    cases e₁ with | cons a h => cases h; exact ⟨_, rfl, a⟩
  obtain ⟨u₂, rfl, eu₂⟩ : ∃ u₂, ls₂ = [u₂] ∧ u ≈ u₂ := by
    cases e₂ with | cons a h => cases h; exact ⟨_, rfl, a⟩
  -- the shape is `bot` or an inductive type shape
  have hcases : m = .bot ∨ ∃ (n0 : Nat) (e : n = n0 + 1) (r : Bool) (h : IndHead)
      (l : List (WShape n0)), HEq m (WShape.indTy r h l) := by
    rcases quotTyApp_le hM hdf hm with hb | ⟨k, r, h, l, hle⟩
    · exact .inl (TShape.le_bot.1 hb)
    cases n with
    | zero => exact .inl (WShape.le_indTy_zero hle)
    | succ n0 =>
      rcases WShape.le_indTy_cases hle with h0 | ⟨l', rfl⟩
      · exact .inl h0
      · exact .inr ⟨n0, rfl, r, h, l', .rfl⟩
  rcases hcases with rfl | ⟨n0, rfl, r, h, l, hEq⟩
  · exact (LR _ _ _).bot hma.isType
  cases hEq
  obtain ⟨j, rfl, -⟩ := WShape.HasType.indTy_inv hma
  obtain ⟨rfl, -⟩ := quotTy_inv hM hdf hmk hm
  have hn : Inert env ``Quot := Inert.of_role hM.roles
    (fun hdf' e => henvW.rule_lhs_params hdf' e) (.quotTy hdf rfl) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hlook : Lookup ((quotTyTele u).reverse ++ Γ) 1 (.sort u) := .succ .zero
  have WS := W.toSubstEq hΓ₀
  have hTy : env.IsDefEq U Γ₀ (σ 1) (σ' 1) (.sort u) := WS.lookup hlook
  -- the arguments, along the quotient's telescope
  have hΔ : OnCtx (quotTyTele u).reverse (env.IsType U) := by
    have hle : VEnv.empty ≤ env := ⟨nofun, nofun, nofun⟩
    have := ((quotMkTele_isTele (u := u) hu).mono hle).onCtx (Γ := []) trivial
    simpa [quotMkTele, quotTyTele] using this.1
  have W1 := Ctx.SubstEq.vals hEo hΔ WS
  simp only [show (quotTyTele u).reverse.length = 2 from rfl,
    show VExpr.bvars 2 0 = [.bvar 1, .bvar 0] from rfl, List.map_cons, List.map_nil,
    VExpr.subst] at W1
  have hΔ0 : OnCtx (quotTyTele (.param 0)).reverse (env.IsType 1) := by
    have hle : VEnv.empty ≤ env := ⟨nofun, nofun, nofun⟩
    have := ((quotMkTele_isTele (U := 1) (u := .param 0) (by simp [VLevel.WF])).mono hle).onCtx
      (Γ := []) trivial
    simpa [quotMkTele, quotTyTele] using this.1
  have eΔ (x : VLevel) : (quotTyTele (.param 0)).reverse.map (·.instL [x]) =
      (quotTyTele x).reverse := rfl
  have W2 := Ctx.SubstEq.instL_congr hEo hΓ₀ (ls := [u]) (ls' := [u₁]) (by simpa using hu)
    hl₁ (.cons eu₁ .nil) hΔ0 (by rw [eΔ]; exact W1)
  rw [eΔ] at W2
  have hcl : CtxClosed (quotTyTele u₁).reverse := by
    rw [← eΔ]; exact (hΔ0.instL hl₁).ctxClosed hEo
  have W3 := Ctx.SubstEq.congr_closed (τ := Subst.dflt.consList [σ 1, σ 0])
    (τ' := Subst.dflt.consList [σ' 1, σ' 0]) hcl (fun i hi => ?_) (fun i hi => ?_) W2
  rotate_left
  · match i, hi with | 0, _ => rfl | 1, _ => rfl
  · match i, hi with | 0, _ => rfl | 1, _ => rfl
  have IR : IndRel env U Γ₀ ⟨``Quot, 2, [``Quot.mk], [1]⟩
      ((VExpr.const ``Quot [u₁]).appN [σ 1, σ 0]) ((VExpr.const ``Quot [u₂]).appN [σ' 1, σ' 0]) := by
    refine ⟨hn, [u₁], [u₂], [σ 1, σ 0], [σ' 1, σ' 0], .rfl, .rfl,
      levels_equiv_trans (levels_equiv_symm (.cons eu₁ .nil)) (.cons eu₂ .nil), ?_, ?_, ?_⟩
    · rw [typeTele_quot hni hq]; rfl
    · rw [typeTele_quot hni hq]; rfl
    · rw [typeTele_quot hni hq, typeTele_quot hni hq]
      have := SubstRel.of_substEq hEo hΓ₀ (ls := [u₁]) (ls' := [u₂]) hl₁ hl₂
        (levels_equiv_trans (levels_equiv_symm (.cons eu₁ .nil)) (.cons eu₂ .nil)) hΔ0 (by rw [eΔ]; exact W3)
      rw [eΔ, eΔ] at this; exact this
  have IT : IndTele (LR (U := U) (Γ := Γ₀) henv hU n0) ⟨``Quot, 2, [``Quot.mk], [1]⟩ l
      ((VExpr.const ``Quot [u₁]).appN [σ 1, σ 0])
      ((VExpr.const ``Quot [u₂]).appN [σ' 1, σ' 0]) := by
    intro ls As ls' As' r1 r2 c i k ci hi hk hc
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hn.whnf r1)
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hn.whnf r2)
    obtain ⟨rfl, rfl⟩ : c = ``Quot.mk ∧ i = 0 := by
      simp [List.idxOf?_cons] at hi; exact ⟨hi.1.symm, hi.2.symm⟩
    obtain rfl : k = 1 := by simpa using hk.symm
    rw [hmk] at hc; cases hc
    rw [ctorTeleAt_quotMk, ctorTeleAt_quotMk]
    unfold TeleRel
    rcases hv : (ctorTel (⟨``Quot, 2, [``Quot.mk], [1]⟩ : IndHead) l 0).piView with _ | ⟨b, g⟩
    · exact .inl rfl
    have hb := quotTy_ctorTel_dom hM hdf hmk hm hv
    have htb := (WShape.piView_type (WShape.HasType.indTy_tels' hma 0) hv).1
    refine .inr ⟨σ 1, _, σ' 1, _, b, g, rfl, .rfl, .rfl, .base hTy,
      LR.SubstWF.varTy hM W hlook hb htb, (LR.SubstWF.varTyInfo hM W hlook hu hb htb).2,
      (LR.SubstWF.varTyInfo hM W.symm hlook hu hb htb).2, fun _ _ _ _ _ _ => trivial⟩
  have SY : ∀ M, StructTy env U Γ₀ ⟨``Quot, 2, [``Quot.mk], [1]⟩ M := by
    intro M c i k hS hi _
    have hc' : c = ``Quot.mk := by simp [List.idxOf?_cons] at hi; exact hi.1.symm
    exact absurd hS.1 (by rw [hc', quotMk_not_struct hM hdf]; decide)
  refine (LR _ _ _).sort_a_iff.2 ⟨?_, fun _ _ => ⟨?_, ?_⟩⟩
  · simp only [LR, LRS, LRS.TyDefEq.indTy_iff]; exact .inl ⟨IR, IT⟩
  · simp only [LR, LRS, LRS.TyTyped.indTy_iff]; exact .inr (SY _)
  · simp only [LR, LRS, LRS.TyTyped.indTy_iff]; exact .inr (SY _)


/-- The quotient applied to its telescope's variables at equivalent levels: related at its sort. -/
theorem AdeqStmt.quotTySpine (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hq : env.constants ``Quot = some quotConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst) (hni : env.inducts ``Quot = none)
    {u : VLevel} (hu : u.WF U) {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u] ls') {Γ : List VExpr} :
    AdeqStmt (U := U) henv hU Γ₀ ((quotTyTele u).reverse ++ Γ)
      ((VExpr.const ``Quot [u]).appN (VExpr.bvars 2 0))
      ((VExpr.const ``Quot ls').appN (VExpr.bvars 2 0)) (.sort u) := by
  intro ρ n m a hm ha hma
  have hu' : ∀ l ∈ [u], l.WF U := by simpa using hu
  have e0 : List.Forall₂ (· ≈ ·) [u] [u] := .cons (rfl : VLevel.Equiv u u) .nil
  rw [show VExpr.bvars 2 0 = [.bvar 1, .bvar 0] from rfl] at hm ⊢
  have core := @quotTySpine_core _ _ _ _ henv hU Γ₀ hM henvW hΓ₀ hdf hq hmk hni u hu
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · exact core W hu' hu' e0 e0 hma hm
  · exact core W hls' hls' heq heq hma hm
  · exact core W hu' hls' e0 heq hma hm

/-- The quotient type former's constant case: given adequacy's cases for an environment `E₀`
and model soundness for it. -/
theorem AdeqStmt.quotTy (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀)
    (hdf : env.defeqs quotDefEq) (hq : env.constants ``Quot = some quotConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst) (hni : env.inducts ``Quot = none)
    {u : VLevel} (hu : u.WF U) {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u] ls') {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot [u]) (.const ``Quot ls')
      (quotConst.type.instL [u]) := by
  have hle₀ : VEnv.empty ≤ E₀ := ⟨nofun, nofun, nofun⟩
  have hTe : E₀.IsTele U [] (quotTyTele u) := by
    have := (quotMkTele_isTele hu).mono hle₀
    rw [show quotMkTele u = quotTyTele u ++ [.bvar 1] from rfl] at this
    exact (VEnv.IsTele.append_inv this).1
  have hR : E₀.IsType U (quotTyTele u).reverse (.sort u) := ⟨_, .sort hu⟩
  have H' : AdeqStmt (U := U) henv hU Γ₀ ((quotTyTele u).reverse ++ Γ)
      (etaSpine (quotTyTele u) (.const ``Quot [u]))
      (etaSpine (quotTyTele u) (.const ``Quot ls')) (.sort u) := by
    rw [etaSpine_eq, etaSpine_eq]
    simp only [VExpr.liftN, show (quotTyTele u).length = 2 from rfl]
    intro ρ n m a
    exact AdeqStmt.quotTySpine hM henvW hΓ₀ hdf hq hmk hni hu hls' heq
  rw [quot_type']
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot [u]) (.const ``Quot ls')
      (.foralls (quotTyTele u) (.sort u)) :=
    AdeqStmt.etaLams_closed hM hΓ₀ hE₀le hE₀o hS IH hTe hΓ hR @H'
  exact @key


/-- The quotient is no recorded inductive type. -/
theorem inducts_quot_none (hM : ModelEnv env) (henvW : env.WF)
    (hdf : env.defeqs quotDefEq) : env.inducts ``Quot = none := by
  cases h : env.inducts ``Quot with
  | none => rfl
  | some p =>
    obtain ⟨d, t⟩ := p
    obtain ⟨-, -, -, -, -, -, T, hT, -⟩ := henvW.inducts h
    cases hM.roles (ConstArity.indTy h hT) (ConstArity.quotTy hdf rfl)

/-- Adding a constant whose case holds keeps adequacy's environment cases. -/
theorem AdequacyHyps.addConst_of {E E₁ : VEnv} {c : Name} {ci : VConstant}
    (IH : AdequacyHyps (U := U) henv hU E Γ₀) (h : E.addConst c ci = some E₁)
    (Hc : ∀ {Γ ls ls' u}, OnCtx Γ (env.IsType U) →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls)) :
    AdequacyHyps (U := U) henv hU E₁ Γ₀ := by
  have h1 : E.addConstList [(c, ci)] = some E₁ := by simp [VEnv.addConstList, h]
  have hinds : E₁.inducts = E.inducts := VEnv.addConstList_inducts h1
  have hdfs : E₁.defeqs = E.defeqs := VEnv.addConstList_defeqs' h1
  refine ⟨fun {Γ c' ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => IH.extra hΓ (hdfs ▸ hd),
    fun hΓ h => IH.projDF hΓ (hinds ▸ h), fun hΓ h => IH.projIota hΓ (hinds ▸ h),
    fun hΓ h => IH.projEta hΓ (hinds ▸ h)⟩
  rcases VEnv.addConstList_constants_cases' h1 hc with hc | hci
  · exact IH.const hΓ hc hls hls' hlen heq hu h7 h8 hA
  · simp only [List.mem_singleton, Prod.mk.injEq] at hci
    obtain ⟨rfl, rfl⟩ := hci
    exact Hc hΓ hls hls' hlen heq hu h7 h8 hA


omit [ShapeEnv] [AxInterp] in
/-- The quotient's step to adequacy's environment cases: `Quot`'s case from the environment before
it, and `Quot.mk`'s and `Quot.lift`'s from that environment with `Quot` added. -/
theorem quotStep : QuotStep := by
  refine QuotStep.of_consts ?_
  intro env henvW U Γ₀ hΓ₀ X ds E E' hX hXD hW _ hQR h1 hext hdom IH Γ c ci ls ls' u hΓ hm
    hls hls' hlen heq hu _ _ _
  letI := env.shapeEnv; letI := X
  have hD : VDecl.WF E .quot E' := .quot hQR h1
  have hW' : VEnv.WF' (.quot :: ds) E' := .decl hD hW
  have hle := hext.le
  have hMX := henvW.modelEnv hX hXD
  have hnd : NoDom E' := fun hdf e hx => VEnv.WF.rule_head ⟨_, hW'⟩ hdf e (hdom _ hx)
  have hS' : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hW' hle hnd
      (VEnv.WF.noDomI ⟨_, hW'⟩ hdom)).strongSound hMX hle D
  obtain ⟨hq', hmk', hlift', -, hdf'⟩ := addQuot_facts h1
  have hq := hle.constants hq'; have hmk := hle.constants hmk'
  have hlift := hle.constants hlift'; have hdf := hle.defeqs hdf'
  have hni := inducts_quot_none hMX henvW hdf
  -- the environment with `Quot` added
  have h1' := h1
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1'
  obtain ⟨E₁, a1, E₂, a2, E₃, a3, E₄, a4, a5⟩ := h1'
  have hE₁E' : E₁ ≤ E' := by
    cases a5
    exact (VEnv.addConst_le a2).trans ((VEnv.addConst_le a3).trans
      ((VEnv.addConst_le a4).trans VEnv.addDefEq_le))
  have hEE₁ : E ≤ E₁ := VEnv.addConst_le a1
  have hEo : E.Ordered := VEnv.WF.ordered ⟨_, hW⟩
  have hE₁o : E₁.Ordered := .const hEo ⟨_, by type_tac⟩ a1
  have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hS' (D.mono (hEE₁.trans hE₁E'))
  have hS₁ : ∀ {Γ M N A}, E₁.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hS' (D.mono hE₁E')
  have hquot : ∀ {Γ ls ls'}, OnCtx Γ (env.IsType U) → (∀ l ∈ ls, l.WF U) →
      (∀ l ∈ ls', l.WF U) → ls.length = quotConst.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot ls) (.const ``Quot ls') (quotConst.type.instL ls) := by
    intro Γ ls ls' hΓ hls hls' hlen heq
    match ls, hlen with
    | [u'], _ =>
    have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot [u']) (.const ``Quot ls') (quotConst.type.instL [u']) :=
      AdeqStmt.quotTy hMX henvW hΓ₀ (hEE₁.trans (hE₁E'.trans hle)) hEo hS IH hdf hq hmk hni
        (hls _ List.mem_cons_self) hls' heq hΓ
    exact @key
  have IH₁ : @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E₁ Γ₀ :=
    IH.addConst_of a1 fun hΓ hls hls' hlen heq _ _ _ _ => hquot hΓ hls hls' hlen heq
  simp only [quotConsts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot ls) (.const ``Quot ls') (quotConst.type.instL ls) :=
      hquot hΓ hls hls' hlen heq
    exact @key
  · match ls, hlen with
    | [u'], _ =>
    have hu' : u'.WF U := hls _ List.mem_cons_self
    obtain ⟨u₂, rfl, e₂⟩ : ∃ u₂, ls' = [u₂] ∧ u' ≈ u₂ := by
      cases heq with | cons a h => cases h; exact ⟨_, rfl, a⟩
    have hu₂ : u₂.WF U := hls' _ List.mem_cons_self
    have hspE : env.IsDefEq U (quotMkTele u').reverse
        ((VExpr.const ``Quot.mk [u']).appN (VExpr.bvars 3 0))
        ((VExpr.const ``Quot.mk [u₂]).appN (VExpr.bvars 3 0)) (quotMkCod [u']) := by
      have h : env.IsDefEq U [] (.const ``Quot.mk [u']) (.const ``Quot.mk [u₂])
          (quotMkConst.type.instL [u']) :=
        .constDF hmk (by simp [hu']) (by simp [hu₂]) rfl (.cons e₂ .nil)
      rw [quotMk_type] at h
      have := VEnv.IsDefEq.appN_bvars' henvW.ordered h
      simpa [VExpr.liftN, quotMkTele, quotMkCod] using this
    have hBE : E₁.IsDefEq U (quotMkTele u').reverse (quotMkCod [u']) (quotMkCod [u₂])
        (.sort u') := by
      have hq₁ : E₁.constants ``Quot = some quotConst := VEnv.addConst_self a1
      refine quot_congr hq₁ hu₂ hu' e₂ ?_ ?_
      · exact .bvar (show Lookup (quotMkTele u').reverse 2 (.sort u') from .succ (.succ .zero))
      · exact .bvar (show Lookup (quotMkTele u').reverse 1
          (.forallE (.bvar 2) (.forallE ((VExpr.bvar 2).liftN 1) (.sort .zero))) from .succ .zero)
    have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot.mk [u']) (.const ``Quot.mk [u₂]) (quotMkConst.type.instL [u']) :=
      AdeqStmt.quotMk hMX henvW hΓ₀ (hE₁E'.trans hle) hE₁o hS₁ IH₁ hdf hmk hni hu' hspE hBE hΓ
    exact @key
  · match ls, hlen with
    | [u', v'], _ =>
    have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot.lift [u', v']) (.const ``Quot.lift ls')
        (quotLiftConst.type.instL [u', v']) :=
      AdeqStmt.quotLift' hMX henvW hΓ₀ (hE₁E'.trans hle) hE₁o hS₁ IH₁
        (hEE₁.constants hQR) (VEnv.addConst_self a1) hdf hmk hlift hni
        (hls _ List.mem_cons_self) (hls _ (List.mem_cons_of_mem _ List.mem_cons_self)) hls' heq hΓ
    exact @key
  · have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot.ind ls) (.const ``Quot.ind ls') (quotIndConst.type.instL ls) := by
      exact AdeqStmt.noRole (quotInd_noRole hW h1 hext) fun hx => by
        have h := hdom _ hx; rw [(addQuot_facts h1).2.2.2.1] at h; cases h
    exact @key

end LogRel
end Lean4Lean

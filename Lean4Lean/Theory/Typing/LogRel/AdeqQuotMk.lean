import Lean4Lean.Theory.Typing.LogRel.AdeqCtor

/-!
# `Quot.mk`'s constant case

`Quot.mk` applied to its telescope's variables is related at the quotient, as a constructor
application whose field is related along `Quot.mk`'s telescope: the analogue of `ctorSpine_core`
for the quotient, whose type former has no recorded block.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp]

/-- An interpretation of `Quot.mk` applied to three arguments is `bot`, or, where the quotient is
not a proposition, below the constructor shape of an interpretation of the element. -/
theorem quotMkApp_inv (hM : ModelEnv env) (hdf : env.defeqs quotDefEq) {ls : List VLevel}
    {α r a : VExpr} {ρ : Valuation} {m : TShape}
    (H : LE_Interp env ρ m ((VExpr.const ``Quot.mk ls).appN [α, r, a])) :
    m ≤ TShape.bot ∨ ∃ u, ls = [u] ∧ ¬u ≈ .zero ∧ ∃ k, ∃ p : WShape k,
      LE_Interp env ρ p.T a ∧ m ≤ (WShape.ctor' ``Quot.mk [p]).T := by
  have hA : ConstArity env ``Quot.mk .quotMk 3 := .quotMk hdf rfl
  rw [← spine_eq_appN] at H
  obtain ⟨n0, H0⟩ := H.spine_inv hM.roles (fun h => hM.domRole h hA) (fun r n h => by
    cases hM.roles h hA; rw [← hA.determ h]; simp)
  obtain ⟨rargs, y, hra, hmy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 3 := by rw [List.Forall₂.length_eq hra]; simp
  cases hC with
  | bot => exact .inl (hmy.trans TShape.bot_eqv.1)
  | lam he hle => exact .inl (hmy.trans (Const.lam_le_bot hM.roles he hle (hrl ▸ hA)))
  | ext h0 => exact (hM.domRole h0 hA).elim
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotMk _ _ h3 h4 h5 =>
    cases hra with | cons hp _ =>
    exact .inr ⟨_, h3, h4, n0, _, hp, hmy.trans h5⟩

/-- An inductive type shape interpreting `Quot.{u} A R`: its head is the quotient's, and its
telescope for `Quot.mk` is below the interpretation of `Quot.mk`'s field telescope at shapes of
`A` and `R`. -/
theorem quotTy_inv (hM : ModelEnv env) (hdf : env.defeqs quotDefEq)
    (hmk : env.constants ``Quot.mk = some quotMkConst) {ρ : Valuation} {u : VLevel}
    {A R : VExpr} {K : Nat} {r : Bool} {h : IndHead} {l : List (WShape K)}
    (haQ : LE_Interp env ρ (WShape.indTy r h l).T (.app (.app (.const ``Quot [u]) A) R)) :
    h = ⟨``Quot, 2, [``Quot.mk], [1]⟩ ∧ ∃ (n0 : Nat) (rA rR cty : WShape n0),
      LE_Interp env ρ rA.T A ∧ LE_Interp env ρ rR.T R ∧
      LE_Interp env (pushAll ρ [rA.T, rR.T]) cty.T
        (.forallE (.bvar 1) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1))) ∧
      (ctorTel h l 0).T ≤ cty.T := by
  have hA : ConstArity env ``Quot .quotTy 2 := .quotTy hdf rfl
  have haQ' : LE_Interp env ρ (WShape.indTy r h l).T (spine ``Quot [u] [R, A]) := by
    rw [show [R, A] = [A, R].reverse from rfl, spine_eq_appN]; exact haQ
  obtain ⟨n0, H0⟩ := haQ'.spine_inv hM.roles (fun h => hM.domRole h hA) (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y, hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 2 := by rw [List.Forall₂.length_eq hra]; simp
  have hnb : ¬ y ≤ TShape.bot := fun hb => by
    have := WShape.LE.of_T ((hyy.trans hb).trans TShape.bot_eqv.2)
    simp [WShape.indTy, WShape.bot, WShape.LE.def, Shape.LE.def, Shape.bot] at this
  cases hC with
  | bot => exact (hnb TShape.bot_eqv.1).elim
  | lam he hle => exact (hnb (Const.lam_le_bot hM.roles he hle (hrl ▸ hA))).elim
  | ext h0 => exact (hM.domRole h0 hA).elim
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotTy hd' e2 e3 hl2 h5 h6 h7 h8 _g =>
    rename_i u' hh ci cty
    cases e3
    rw [hmk] at h5; cases h5
    obtain ⟨rA, rR, rfl⟩ : ∃ rA rR, rargs = [rR, rA] := by
      match rargs, hrl with | [x, y], _ => exact ⟨_, _, rfl⟩
    cases hra with | cons hR hra =>
    cases hra with | cons hAa _ =>
    have hcty : LE_Interp env (pushAll ρ [rA.T, rR.T]) cty.T
        (.forallE (.bvar 1) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1))) := by
      have := LE_Interp.piAppS_foralls hM (Ds := [.bvar 1]) [.sort u,
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))] (by
          rw [quotMk_type] at h6; exact h6) h7 rfl
      simpa using this
    have hle := hyy.trans h8
    let N := max K n0
    have hK : K ≤ N := Nat.le_max_left ..; have hn : n0 ≤ N := Nat.le_max_right ..
    have hle' := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hK) (Nat.succ_le_succ hn)).1 hle
    simp only [WShape.lift_indTy hK, WShape.lift_indTy hn, WShape.indTy_le_indTy] at hle'
    obtain ⟨-, rfl, hl⟩ := hle'
    have htel := hl.getD' (d := WShape.bot) (d' := WShape.bot) WShape.LE.rfl 2
    have e1 : (List.map (WShape.lift N) l).getD 2 WShape.bot =
        (ctorTel ⟨``Quot, 2, [``Quot.mk], [1]⟩ l 0).lift N := by
      simp only [ctorTel, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases l[2]? <;> simp
    rw [e1] at htel
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.getD_cons_succ, List.getD_cons_zero] at htel
    exact ⟨rfl, n0, rA, rR, cty, hAa, hR, hcty, (TShape.LE.def (m := N) hK hn).2 htel⟩

/-- The codomain of `Quot.mk`'s type at levels `l`, over its telescope. -/
def quotMkCod (l : List VLevel) : VExpr := .app (.app (.const ``Quot l) (.bvar 2)) (.bvar 1)

omit [ShapeEnv] [AxInterp] in
theorem quotMk_vals_subst (l : List VLevel) (τ : VExpr.Subst) :
    ((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)).subst τ =
      (VExpr.const ``Quot.mk l).appN [τ 2, τ 1, τ 0] := by
  rw [show VExpr.bvars 3 0 = [.bvar 2, .bvar 1, .bvar 0] from rfl]; rfl

omit [ShapeEnv] [AxInterp] in
theorem quotMkCod_subst (l : List VLevel) (τ : VExpr.Subst) :
    (quotMkCod l).subst τ = (VExpr.const ``Quot l).appN [τ 2, τ 1] := by
  simp [quotMkCod, VExpr.appN, VExpr.subst]

variable {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- `Quot.mk` applied to its telescope's variables, under related substitutions and at levels
whose codomains are related: related at the quotient, at a constructor shape, through its field
along `Quot.mk`'s telescope. -/
theorem quotMkSpine_core (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hni : env.inducts ``Quot = none) {u : VLevel}
    {Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotMkTele u).reverse ++ Γ) ρ)
    {ls₁ ls₂ : List VLevel} {n : Nat} {m a : WShape n} (hma : m.HasType a)
    (hm : LE_Interp env ρ m.T ((VExpr.const ``Quot.mk [u]).appN (VExpr.bvars 3 0)))
    (ha : LE_Interp env ρ a.T (quotMkCod [u]))
    (hTA : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod [u]).subst σ)
      ((quotMkCod [u]).subst σ') a)
    (hT1 : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod ls₁).subst σ)
      ((quotMkCod [u]).subst σ) a)
    (hT2 : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod ls₂).subst σ')
      ((quotMkCod [u]).subst σ) a)
    (ht1 : env.IsDefEq U Γ₀ (((VExpr.const ``Quot.mk ls₁).appN (VExpr.bvars 3 0)).subst σ)
      (((VExpr.const ``Quot.mk ls₁).appN (VExpr.bvars 3 0)).subst σ) ((quotMkCod [u]).subst σ))
    (ht2 : env.IsDefEq U Γ₀ (((VExpr.const ``Quot.mk ls₂).appN (VExpr.bvars 3 0)).subst σ')
      (((VExpr.const ``Quot.mk ls₂).appN (VExpr.bvars 3 0)).subst σ')
      ((quotMkCod [u]).subst σ)) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
      (((VExpr.const ``Quot.mk ls₁).appN (VExpr.bvars 3 0)).subst σ)
      (((VExpr.const ``Quot.mk ls₂).appN (VExpr.bvars 3 0)).subst σ')
      ((quotMkCod [u]).subst σ) m a := by
  have hm' := hm
  rw [show VExpr.bvars 3 0 = [.bvar 2, .bvar 1, .bvar 0] from rfl] at hm'
  rcases quotMkApp_inv hM hdf hm' with hb | ⟨u', hu', hnp, k', p, hp, hmle⟩
  · cases show m = .bot from TShape.le_bot.1 hb
    exact (LR _ _ _).bot hma.isType
  cases hu'
  cases n with
  | zero =>
    obtain ⟨mv, wf⟩ := m
    cases mv with
    | bot => exact (LR _ _ _).bot hma.isType
    | sort r => exact (TShape.sort_not_le_ctor' (r := r) (n := 0) hmle).elim
  | succ n0 =>
  rcases WShape.le_ctor'_cases hmle with rfl | ⟨fs, hf, rfl, hfs⟩
  · exact (LR _ _ _).bot hma.isType
  obtain ⟨I, as, rfl⟩ := WShape.HasType.ctor_inv hma
  simp only [LR, LRS, LRS.DefEq.ctor_indTy]
  unfold LRS.IndVal
  rw [if_neg (fun hs => absurd hs.1 (by rw [quotMk_not_struct hM hdf]; decide))]
  refine .inl ?_
  obtain ⟨hI, n1, rA, rR, cty, hrA, hrR, hcty, hle'⟩ := quotTy_inv hM hdf hmk ha
  subst hI
  have hInS : Inert env ``Quot := Inert.of_role hM.roles
    (fun hdf' e => henvW.rule_lhs_params hdf' e) (.quotTy hdf rfl) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hInC : Inert env ``Quot.mk := Inert.of_role hM.roles
    (fun hdf' e => henvW.rule_lhs_params hdf' e) (.quotMk hdf rfl) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hTA' := hTA
  simp only [LR, LRS, LRS.TyDefEq.indTy_iff] at hTA'
  obtain ⟨hRA, hITA⟩ := hTA'.resolve_right fun ⟨hN, _⟩ =>
    NeRed.not_inert hU hInS hN (by rw [quotMkCod_subst]; exact .rfl)
  obtain ⟨i, hi, hfit⟩ := WShape.HasType.ctor_fits hma
  obtain ⟨i', hi', hk⟩ := WShape.HasType.ctor_arity hma
  rw [hi] at hi'; cases hi'
  have hi0 : i = 0 := by simpa using hi.symm
  subst hi0
  have hfl : fs.length = 1 := by simpa using hk.symm
  have hidx (l : List VLevel) (xs : List VExpr) : ctorIdx env ``Quot ``Quot.mk l xs = [] := by
    simp [ctorIdx, hni]
  have hCP : ∀ {l : List VLevel} {τ : VExpr.Subst},
      (LR (U := U) (Γ := Γ₀) henv hU (n0+1)).TyDefEq ((quotMkCod l).subst τ)
        ((quotMkCod [u]).subst σ) (.indTy true ⟨``Quot, 2, [``Quot.mk], [1]⟩ as) →
      CtorParams env U Γ₀ ⟨``Quot, 2, [``Quot.mk], [1]⟩ ``Quot.mk l [τ 2, τ 1] [τ 0] [u]
        [σ 2, σ 1] := by
    intro l τ H
    simp only [LR, LRS, LRS.TyDefEq.indTy_iff] at H
    obtain ⟨hR, -⟩ := H.resolve_right fun ⟨_, hN⟩ =>
      NeRed.not_inert hU hInS hN (by rw [quotMkCod_subst]; exact .rfl)
    rw [quotMkCod_subst, quotMkCod_subst] at hR
    rw [show [τ 2, τ 1] = [τ 2, τ 1] ++ ctorIdx env ``Quot ``Quot.mk l ([τ 2, τ 1] ++ [τ 0]) by
      rw [hidx]; rfl] at hR
    obtain ⟨lsA, AsA, hr, hP⟩ := CtorParams.of_indRel hR
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hr)
    exact hP
  refine ⟨hInS, hInC, hITA.left' hU hRA, 0, 1, quotMkConst, [u], [σ 2, σ 1], ls₁, [σ 2, σ 1],
    [σ 0], ls₂, [σ' 2, σ' 1], [σ' 0], hi, hfl ▸ hk, hmk, ?_, ?_, ?_, hfl, ?_, hCP hT1, hCP hT2⟩
  · rw [quotMkCod_subst]; exact .rfl
  · rw [quotMk_vals_subst] at ht1 ⊢; exact ⟨.rfl, ht1⟩
  · rw [quotMk_vals_subst] at ht2 ⊢; exact ⟨.rfl, ht2⟩
  · -- the field, along `Quot.mk`'s telescope at the quotient's parameters
    have eTel : ctorTeleAt quotMkConst 1 [u] [σ 2, σ 1] =
        (VExpr.foralls [.bvar 1] (quotMkCod [u])).subst
          (Subst.id.consList ((VExpr.bvars 2 1).map (·.subst σ))) := by
      rw [ctorTeleAt, quotMk_type, show piCount quotMkConst.type - 1 = 2 from rfl,
        show quotMkTele u = [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))] ++
          [.bvar 1] from rfl, VExpr.foralls_append,
        piInst_foralls _ _ _ (by simp)]
      rfl
    rw [eTel]
    have hcl : VExpr.ClosedN (.forallE (.bvar 1) (quotMkCod [u])) 2 := by
      simp [quotMkCod, VExpr.ClosedN]
    have hT0 : LE_Interp env (pushAll (fun i => ρ (i + 3)) [rA.T, rR.T]) cty.T
        (.forallE (.bvar 1) (quotMkCod [u])) := by
      refine LE_Interp.closed hM.closed hcl (fun i hi => ?_) hcty
      rw [pushAll_apply, pushAll_apply (fun i => ρ (i + 3)), dif_pos (by simpa using hi),
        dif_pos (by simpa using hi)]
    refine ctorFields_rel hM hΓ₀ (Ps := [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1)
      (.sort .zero))]) (Ds := [.bvar 1]) (cod := quotMkCod [u]) (pp := [rA.T, rR.T]) W
      (fun j D h => ?_) hfl rfl (fun q hq => ?_) (fun j hj => ?_) (hT0.mono hle') hfit
    · cases j with
      | zero => cases h; simp [VExpr.ClosedN]
      | succ j => simp at h
    · match q, hq with
      | 0, _ => exact bvar_iff.1 hrA
      | 1, _ => exact bvar_iff.1 hrR
    · have h1 := List.Forall₂.getElem?' hfs (List.getElem?_eq_getElem hj)
        (List.getElem?_eq_getElem (show j < [p].length by simp; omega))
      obtain rfl : j = 0 := by omega
      exact h1.trans (bvar_iff.1 hp)

/-- `Quot.mk` applied to its telescope's variables at equivalent levels: related at the quotient,
given the codomains related and their soundness and the spines' typing. -/
theorem AdeqStmt.quotMkSpine (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hni : env.inducts ``Quot = none) {u : VLevel} {ls' : List VLevel}
    {Γ : List VExpr} (hΔ : OnCtx ((quotMkTele u).reverse ++ Γ) (env.IsType U)) {w : VLevel}
    (hsp : env.IsDefEq U ((quotMkTele u).reverse ++ Γ)
      ((VExpr.const ``Quot.mk [u]).appN (VExpr.bvars 3 0))
      ((VExpr.const ``Quot.mk ls').appN (VExpr.bvars 3 0)) (quotMkCod [u]))
    (hSB : StrongSoundEq env U ((quotMkTele u).reverse ++ Γ) (quotMkCod [u]) (quotMkCod ls')
      (.sort w))
    (HB : AdeqStmt (U := U) henv hU Γ₀ ((quotMkTele u).reverse ++ Γ)
      (quotMkCod [u]) (quotMkCod ls') (.sort w)) :
    AdeqStmt (U := U) henv hU Γ₀ ((quotMkTele u).reverse ++ Γ)
      ((VExpr.const ``Quot.mk [u]).appN (VExpr.bvars 3 0))
      ((VExpr.const ``Quot.mk ls').appN (VExpr.bvars 3 0)) (quotMkCod [u]) := by
  intro ρ n m a hm ha hma
  have hEo := henvW.ordered
  have tys : ∀ {σ σ'}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotMkTele u).reverse ++ Γ) ρ →
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod [u]).subst σ)
        ((quotMkCod [u]).subst σ') a ∧
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod ls').subst σ)
        ((quotMkCod ls').subst σ') a ∧
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((quotMkCod [u]).subst σ)
        ((quotMkCod ls').subst σ) a := by
    intro σ σ' W
    have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (hSB.left.sound W.fits ha).out
    have H := HB hA'' hSort hmem'
    exact ⟨LR.toValTy le_n le_a hma.isType hSort hmem' (H.1 W).1,
      LR.toValTy le_n le_a hma.isType hSort hmem' (H.1 W).2,
      LR.toValTy le_n le_a hma.isType hSort hmem' (H.2 W.left)⟩
  have typ : ∀ {σ σ'}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotMkTele u).reverse ++ Γ) ρ →
      ∀ (l : List VLevel), env.IsDefEq U ((quotMkTele u).reverse ++ Γ)
        ((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0))
        ((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)) (quotMkCod [u]) →
      env.IsDefEq U Γ₀ (((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)).subst σ)
        (((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)).subst σ) ((quotMkCod [u]).subst σ) ∧
      env.IsDefEq U Γ₀ (((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)).subst σ')
        (((VExpr.const ``Quot.mk l).appN (VExpr.bvars 3 0)).subst σ')
        ((quotMkCod [u]).subst σ) := by
    intro σ σ' W l H
    have := H.substDF hEo hΔ hΓ₀ (W.toSubstEq hΓ₀)
    exact ⟨this.hasType.1, this.hasType.2⟩
  have core := @quotMkSpine_core _ _ _ _ henv hU Γ₀ hM henvW hΓ₀ hdf hmk hni u Γ
  have hL := hsp.hasType.1
  have hR := hsp.hasType.2
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · obtain ⟨tA, -, -⟩ := tys W
    exact core W hma hm ha tA ((LR _ _ _).left_ty tA) ((LR _ _ _).symm_ty tA)
      (typ W [u] hL).1 (typ W [u] hL).2
  · obtain ⟨tA, tB, -⟩ := tys W
    obtain ⟨-, -, tAB⟩ := tys W.left
    exact core W hma hm ha tA ((LR _ _ _).symm_ty tAB)
      ((LR _ _ _).trans_ty ((LR _ _ _).symm_ty tB) ((LR _ _ _).symm_ty tAB))
      (typ W ls' hR).1 (typ W ls' hR).2
  · obtain ⟨tA, -, tAB⟩ := tys W
    exact core W hma hm ha tA ((LR _ _ _).left_ty tA) ((LR _ _ _).symm_ty tAB)
      (typ W [u] hL).1 (typ W ls' hR).2

/-- `Quot.mk`'s constant case: given adequacy's cases for an environment `E₀` in which its
codomain, the quotient, is typed (one with `Quot`), model soundness for `E₀`, its spines at
equivalent levels equal, and in `E₀` their codomains equal. -/
theorem AdeqStmt.quotMk (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀)
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hni : env.inducts ``Quot = none) {u : VLevel} (hu : u.WF U) {ls' : List VLevel} {w : VLevel}
    (hspE : env.IsDefEq U (quotMkTele u).reverse
      ((VExpr.const ``Quot.mk [u]).appN (VExpr.bvars 3 0))
      ((VExpr.const ``Quot.mk ls').appN (VExpr.bvars 3 0)) (quotMkCod [u]))
    (hBE : E₀.IsDefEq U (quotMkTele u).reverse (quotMkCod [u]) (quotMkCod ls') (.sort w))
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.mk [u]) (.const ``Quot.mk ls')
      (quotMkConst.type.instL [u]) := by
  have hEo := henvW.ordered
  have hle₀ : VEnv.empty ≤ E₀ := ⟨nofun, nofun, nofun⟩
  have hTe : E₀.IsTele U [] (quotMkTele u) := (quotMkTele_isTele hu).mono hle₀
  have onBs : OnCtx (quotMkTele u).reverse (E₀.IsType U) := by
    simpa using hTe.onCtx (Γ := []) trivial
  have onBs' : OnCtx (quotMkTele u).reverse (env.IsType U) := onBs.mono fun h => h.mono hE₀le
  have hΔ : OnCtx ((quotMkTele u).reverse ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hEo VEnv.LE.rfl hΓ onBs'
  have DB := IsDefEq.weak_closed hE₀o onBs hBE Γ
  have Dsp := IsDefEq.weak_closed hEo onBs' hspE Γ
  have HB : AdeqStmt (U := U) henv hU Γ₀ ((quotMkTele u).reverse ++ Γ)
      (quotMkCod [u]) (quotMkCod ls') (.sort w) :=
    LR.adequacy_of hM hE₀le hS hΓ₀ IH DB hΔ
  have H : AdeqStmt (U := U) henv hU Γ₀ ((quotMkTele u).reverse ++ Γ)
      ((VExpr.const ``Quot.mk [u]).appN (VExpr.bvars 3 0))
      ((VExpr.const ``Quot.mk ls').appN (VExpr.bvars 3 0)) (quotMkCod [u]) := by
    intro ρ n m a hm ha hma
    exact AdeqStmt.quotMkSpine (U := U) (henv := henv) (hU := hU) (Γ₀ := Γ₀) hM henvW hΓ₀ hdf
      hmk hni hΔ Dsp.defeq (hS DB) @HB hm ha hma
  have hR : E₀.IsType U (quotMkTele u).reverse (quotMkCod [u]) := ⟨_, hBE.hasType.1⟩
  have H' : AdeqStmt (U := U) henv hU Γ₀ ((quotMkTele u).reverse ++ Γ)
      (etaSpine (quotMkTele u) (.const ``Quot.mk [u]))
      (etaSpine (quotMkTele u) (.const ``Quot.mk ls')) (quotMkCod [u]) := by
    rw [etaSpine_eq, etaSpine_eq]
    simp only [VExpr.liftN, show (quotMkTele u).length = 3 from rfl]
    intro ρ n m a; exact H
  rw [quotMk_type]
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.mk [u]) (.const ``Quot.mk ls')
      (.foralls (quotMkTele u) (quotMkCod [u])) :=
    AdeqStmt.etaLams_closed hM hΓ₀ hE₀le hE₀o hS IH hTe hΓ hR @H'
  exact @key

end LogRel
end Lean4Lean

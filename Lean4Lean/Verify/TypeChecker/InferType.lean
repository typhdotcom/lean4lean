import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.TypeChecker.Proj
import Lean4Lean.Verify.EquivManager

open Lean4Lean

namespace Lean.Expr

theorem liftLooseBVars'_eqv {e₁ e₂ : Expr} :
    e₁ == e₂ → e₁.liftLooseBVars' s d == e₂.liftLooseBVars' s d := by
  simp [(· == ·)]; induction e₁ generalizing e₂ s
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [liftLooseBVars', eqv']
  all_goals intros; subst_vars; try simp [*]

theorem instantiate1'_eqv₂ {e₁ e₂ a₁ a₂ : Expr} (ha : a₁ == a₂) :
    e₁ == e₂ → e₁.instantiate1' a₁ k == e₂.instantiate1' a₂ k := by
  simp [(· == ·)]; induction e₁ generalizing e₂ k
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [instantiate1', eqv']
  all_goals intros; subst_vars; try simp [*]
  rename_i i
  by_cases h1 : i < k <;> simp only [h1, if_true, if_false]
  · simp [eqv']
  by_cases h2 : i = k <;> simp only [h2, if_true, if_false]
  · simpa [(· == ·)] using liftLooseBVars'_eqv ha
  · simp [eqv']

theorem bindingBody!_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) : e₁.bindingBody! == e₂.bindingBody! := by
  revert h; simp [(· == ·)]
  cases e₁ <;> cases e₂ <;> simp [eqv', bindingBody!]
  all_goals intros; simpa [(· == ·)] using eqv_refl _

theorem bindingDomain!_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) :
    e₁.bindingDomain! == e₂.bindingDomain! := by
  revert h; simp [(· == ·)]
  cases e₁ <;> cases e₂ <;> simp [eqv', bindingDomain!]
  all_goals intros; first | assumption | simpa [(· == ·)] using eqv_refl _

theorem eqv_forallE {e : Expr} (h : e == .forallE n d b bi) :
    ∃ n' d' b' bi', e = .forallE n' d' b' bi' ∧ d' == d ∧ b' == b := by
  revert h; simp [(· == ·)]; cases e <;> simp [eqv']
  intro h1 h2; exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h1, h2⟩

end Lean.Expr

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem ensureForallCore.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨hb, he, _, _, _, _, rfl⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF' [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  let ⟨_, he, eq⟩ := he
  (ensureForallCore.WF he).mono fun _ _ _ ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.defeq c.Ewf c.Δwf eq, h3⟩

theorem checkLevel.WF {c : VContext} (H : l.hasMVar' = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  exact Level.getUndefParam_none H (by rename_i h; simpa using h)

theorem inferFVar.WF [VEnv.Injective] {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => ∃ e' ty', c.TrTyping (.fvar name) ty e' ty' := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, _, h2, _, h3⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  exact ⟨_, _, h2, .fvar h1, h3, c.Δwf.find?_wf c.Ewf h1⟩

theorem inferConstant.WF [VEnv.Injective] {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      (∃ e' ty', c.TrTyping (.const name ls) ty e' ty') ∧
      ∃ ci, c.env.find? name = some ci ∧ ty = ci.instantiateTypeLevelParams ls := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF fun _ =>
      ∃ ls', ls.Forall₂ (VLevel.ofLevel c.lparams · = some ·) ls' := by
    clear hinf
    induction ls with
    | nil => exact .pure ⟨_, .nil⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      exact (ih H.2).le fun _ ⟨_, h2⟩ => ⟨_, .cons h1 h2⟩
  split <;> [rename_i h1; exact .throw]
  have main {e'} (he : c.TrExprS (.const name ls) e') : (∃ e' ty',
      c.TrTyping (.const name ls) (ci.instantiateTypeLevelParams ls) e' ty') ∧
      ∃ ci', c.env.find? name = some ci' ∧
        ci.instantiateTypeLevelParams ls = ci'.instantiateTypeLevelParams ls := by
    refine ⟨?_, ci, eq1, rfl⟩
    let .const h4 H' eq := id he
    have ⟨_, _, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    have H := List.mapM_eq_some.1 H'
    have s0 := h6.instL c.Ewf (Δ := []) trivial H' (h5.trans eq.symm)
    have s1 := s0.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [(c.Ewf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
    have ⟨_, s1, s2⟩ := s1
    refine ⟨_, _, ?_, he, s1, .defeqU_r c.Ewf c.Δwf s2.symm ?_⟩
    · intro _ _ _; exact s0.fvarsIn.mono nofun
    · exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ c.safety ≠ .safe → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; apply this]
      rename_i h; simpa [Decidable.or_iff_not_imp_left, ConstantInfo.isPartial] using h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      simp [ConstantInfo.safety]
      split <;> simp +contextual [*]
      split <;> simp [DefinitionSafety.le_safe, *]
      cases c.safety <;> decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure ⟨main h, rfl⟩

theorem inferLambda.loop.WF [VEnv.Injective] {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  unfold inferLambda.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  have hcl : ∀ a ∈ fvs, a.looseBVarRange' = 0 := by
    rw [← eqfvs]; simp [Expr.looseBVarRange']
  simp [harr, -bind_pure_comp, Expr.instantiate'_eq_instantiateList hcl]; split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_lam] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom'}
        (domty : (c.withMLC m).venv.IsType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx dom')
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlam dom') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLocalDecl hdom domty le₁.1 fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLambda.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp; rfl) ?_ (hr.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩, ?_, fun ty hty => h3 _ ⟨h2.1, hty.abstract1⟩⟩
        rw [eqfvs, ← eq]
        refine h2.2.instantiate1 fun h => ?_
        exact ((mwf'.1.1.tr.find?_eq_none.1 mwf'.1.2.1) (m.dropN_fvars_subset n hn (hdrop ▸ h))).elim
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
      have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
      have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
      exact main le domty' h1 nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .lam (ty' := dom') (body' := body') domty hdom hbody := h1
      exact main .rfl domty hdom _ hbody
  · subst ei
    refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ h2'.closed).looseBVarRange_zero ▸
      ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2''⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    exact this.mp (fun _ => id) h3'.fvarsIn

theorem inferLambda.WF [VEnv.Injective]
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl rfl rfl ?_ h1) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem inferForall.loop.WF [VEnv.Injective] {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' u, c.TrTyping e₀ ty e' (.sort u) := by
  unfold inferForall.loop
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  have hcl : ∀ a ∈ fvs, a.looseBVarRange' = 0 := by
    rw [← eqfvs]; simp [Expr.looseBVarRange']
  simp [harr, -bind_pure_comp, Expr.instantiate'_eq_instantiateList hcl]; split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    refine (inferType.WF' ?_ ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
    · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' le.1 fun a mwf' s' le₂ res => ?_
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine inferForall.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (hr.2.mono fun _ => .tail _)
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
      · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.Ewf mwf.1.tr.wf; have H := hdom₁.uniq c.Ewf hΔ h1; ?_
      have H := H.of_r c.Ewf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.Ewf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', _, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (ensureSortCore.WF h2).bind fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus ⊢
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.Ewf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    refine have h := .sort h3'; .pure ⟨_, _, fun _ _ _ => h.fvarsIn, he₀ ▸ h1', h, h4'⟩

theorem inferForall.WF [VEnv.Injective]
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s fun ty _ => ∃ e' u, c.TrTyping e ty e' (.sort u) :=
  (c.withMLC_self ▸ inferForall.loop.WF (Nat.zero_le _) rfl rfl rfl rfl hr .nil .nil rfl) hinf

theorem inferApp.loop.WF [VEnv.Injective] {c : VContext} {s : VState}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hbelow : FVarsBelow c.vlctx e fType)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length)
    (hlm : ∀ a ∈ lm, a.looseBVarRange' = 0) :
    RecM.WF c s (inferApp.loop e₀ ⟨args⟩ fType j i) fun ty _ =>
      ∃ e₁' ty', c.TrTyping (e.mkAppRevList lm |>.mkAppList lr) ty e₁' ty' := by
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs, Expr.instantiateList_reverse]
  have henv := c.Ewf; have hΔ := c.Δwf
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk := stk
    have uf := hf'.uniqU henv hΔ hety
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      have ha0 := c.mlctx.noBV ▸ ha.closed
      refine inferApp.loop.WF (lm := a::lm) stk ?_ ?_ (.app hf' ha') (by simp) rfl rfl
        (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨ha0.looseBVarRange_zero, hlm⟩)
      · exact fun _ hP he => (hbelow _ hP he).2
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · simp [Nat.add_sub_cancel_left, Expr.instantiateRevList_reverse,
        Expr.instantiate'_eq_instantiateList hlm]
      refine (ensureForallCore.WF' hfty).bind fun _ _ _ ⟨hb, ⟨_, h2, h3⟩, eq⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := eq; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (ll := ll ++ lm.reverse) (lm := [a]) stk ?_ ?_
        (.app hf' ha') (by simp) (by simp) (by simp)
        (by simpa using (c.mlctx.noBV ▸ ha.closed).looseBVarRange_zero)
      · intro _ hP he
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
        exact (hb _ hP <| (hbelow _ hP he).instantiateList hlm).2
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    rw [← List.length_reverse, List.take_length, List.reverse_reverse,
      Expr.instantiate'_eq_instantiateList hlm]
    have ⟨_, hfty, h2⟩ := hfty
    refine .pure ⟨_, _, fun _ hP he => ?_, stk.tr, hfty, hety.defeqU_r henv hΔ h2.symm⟩
    have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
    exact (hbelow _ hP he).instantiateList hlm

theorem inferApp.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
  refine (inferType.WF he'.tr).bind fun ty _ _ ⟨ty', hb, _, hty', ety⟩ => ?_
  have henv := c.Ewf; have hΔ := c.Δwf
  refine (inferApp.loop.WF (ll := []) (lm := []) he' hb
      (hty'.trExpr henv hΔ) ety rfl rfl rfl nofun).le
    fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
  have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
  exact ⟨_, e.mkAppList_getAppArgsList ▸ hb, he, h2, h3.defeqU_l henv hΔ this⟩

theorem inferLet.loop.WF [VEnv.Injective] {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length) (nds hnds)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLet n hn nds hnds ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLet.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  have hcl : ∀ a ∈ fvs, a.looseBVarRange' = 0 := by
    rw [← eqfvs]; simp [Expr.looseBVarRange']
  unfold inferLet.loop
  simp [harr, -bind_pure_comp, Expr.instantiate'_eq_instantiateList hcl]; split
  · rename_i name dom val body nd
    generalize eqF : withLetDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_letE] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom' val'}
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hval : (c.withMLC m).TrExprS (val.instantiateList fvs) val')
        (valty : (c.withMLC m).venv.HasType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx val' dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlet dom' val') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLetDecl hdom hval valty le₁.1 fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLet.loop.WF (Nat.succ_le_succ hn) (some nd :: nds)
        (by simp [hnds]) (by simp [hdrop]) (by simp [← eqfvs, harr])
        ?_ (by simp; rfl) ?_ (hr.2.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp [MLCtx.mkLetArg]; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => ?_⟩, ?_, fun ty hty => h3 _ ?_⟩
        · simp [or_imp, forall_and]
          exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
        · rw [eqfvs, ← eq]
          refine h2.2.2.instantiate1 fun h => ?_
          exact ((mwf'.1.1.tr.find?_eq_none.1 mwf'.1.2.1) (m.dropN_fvars_subset n hn (hdrop ▸ h))).elim
        · simp; split <;> rename_i h
          · exact ⟨h2.1, h2.2.1, hty.abstract1⟩
          · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using h)]
            exact hty.abstract1.instantiate1 rfl
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind
        fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5; have le := le.trans le₂
      refine (checkType.WF ?_).bind_le le fun ty _ le ⟨val', ty', _, h4, h5, h6⟩ => ?_
      · apply hr.2.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (isDefEq.WF h5 h1).bind_le le fun b _ le h7 => ?_
      cases b <;> simp
      · exact .getEnv <| .getLCtx .throw
      have valty := h6.defeqU_r c.Ewf mwf.1.tr.wf.toCtx (h7 rfl)
      exact main le h1 h4 valty nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .letE (ty' := dom') (body' := body') valty hdom hval hbody := h1
      exact main .rfl hdom hval valty _ hbody
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _ (eqfvs ▸ harr) (m.noBV ▸ hty.closed).looseBVarRange_zero]
    refine ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2'⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    refine this.mp (fun _ => id) h3'.fvarsIn
termination_by e

theorem inferLet.WF [VEnv.Injective]
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLet e inferOnly).WF c s fun ty _ =>
      ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLet.loop.WF (Nat.zero_le _) [] rfl rfl rfl rfl rfl ?_ hr) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem literal_is_primitive (H : n = ``Nat ∨ n = ``Char.ofNat ∨ n = ``String.ofList)  :
    Environment.primitives.contains n := by
  simp [Environment.primitives, NameSet.ofList]
  obtain rfl|rfl|rfl := H <;> simp +decide [NameSet.contains]

theorem infer_literal [VEnv.Injective] {c : VContext} (H : c.venv.ContainsLits l) :
    c.TrTyping (.lit l) l.type (.trLiteral l) (.const l.typeName []) := by
  refine
    have := TrExprS.trLiteral c.Ewf c.hasPrimitives l H
    ⟨fun _ _ _ => .litType, this.1, ?_, this.2⟩
  rw [← Literal.mkConst_typeName]
  have ⟨_, h⟩ := this.2.isType c.Ewf c.Δwf
  have ⟨_, h1, _, h3⟩  := h.const_inv c.Ewf c.Δwf
  exact .const h1 rfl h3

theorem infer_sort {c : VContext} (H : VLevel.ofLevel c.lparams u = some u') :
    c.TrTyping (.sort u) (.sort u.succ) (.sort u') (.sort u'.succ) := by
  refine ⟨fun _ _ _ => (?a).fvarsIn, .sort H, ?a, .sort (.of_ofLevel H)⟩
  exact .sort <| by simpa [VLevel.ofLevel]

theorem _root_.Lean.Expr.instForall_concat (e : Expr) (L : List Expr) (x : Expr) :
    e.instForall (L ++ [x]) = (e.instForall L).bindingBody!.instantiate1 x := by
  induction L generalizing e with
  | nil => rfl
  | cons a L ih => exact ih _

theorem _root_.Lean.Expr.instForall_forallE (e : Expr) (L : List Expr)
    (h : L.length < e.leadingForalls) : ∃ n d b bi, e.instForall L = .forallE n d b bi := by
  induction L generalizing e with
  | nil =>
    cases e <;> simp [Expr.leadingForalls] at h
    exact ⟨_, _, _, _, rfl⟩
  | cons a L ih =>
    cases e <;> simp [Expr.leadingForalls] at h
    rename_i b _
    refine ih (b.instantiate1 a) ?_
    have := Expr.leadingForalls_instantiate1' b a 0
    rw [← Expr.instantiate1_eq] at this
    omega

theorem mkAppN_push (f : Expr) (Ds : Array Expr) (x : Expr) :
    mkAppN f (Ds.push x) = .app (mkAppN f Ds) x := by simp [mkAppN]

/-- A term equivalent to a constant applied to arguments is that constant, or an application
equivalent to the constant applied to all but the last argument, at an equivalent last one. -/
theorem eqv_mkAppN_const {e : Expr} {J ls} {Ds : Array Expr}
    (h : e == mkAppN (.const J ls) Ds) :
    (e = .const J ls ∧ Ds = #[]) ∨ ∃ f a Ds₀ x, e = .app f a ∧ Ds = Ds₀.push x ∧
      f == mkAppN (.const J ls) Ds₀ ∧ a == x := by
  obtain ⟨L⟩ := Ds
  rcases List.eq_nil_or_concat L with rfl | ⟨L₀, x, rfl⟩
  all_goals simp only [List.concat_eq_append] at h ⊢
  · exact .inl ⟨Expr.eqv_const.1 (by simpa [mkAppN] using h), trivial⟩
  · have e1 : (⟨L₀ ++ [x]⟩ : Array Expr) = (⟨L₀⟩ : Array Expr).push x := by simp
    rw [e1, mkAppN_push] at h
    cases e with
    | app f a =>
      simp [(· == ·), Expr.eqv'] at h
      exact .inr ⟨f, a, _, x, rfl, e1, by simpa [(· == ·)] using h.1, by simpa [(· == ·)] using h.2⟩
    | _ => simp [(· == ·), Expr.eqv'] at h

theorem _root_.Lean4Lean.TypeChecker.LitApp.congr {e₁ e₂ : Expr} (h : e₁ == e₂) (H : LitApp C P e₁ ty) : LitApp C P e₂ ty :=
  fun _ _ _ _ h1 h2 h3 => H (BEq.trans h h1) h2 h3

theorem _root_.Lean4Lean.TypeChecker.LitApp.of_ne {e : Expr} (hA : ∀ f a, e ≠ .app f a) (hC : ∀ n ls, e ≠ .const n ls) :
    LitApp C P e ty := fun _ _ _ _ h _ _ => by
  rcases eqv_mkAppN_const h with ⟨rfl, -⟩ | ⟨_, _, _, _, rfl, -⟩
  · cases hC _ _ rfl
  · cases hA _ _ rfl


theorem ensureForallCore.WF₂ [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => (c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi) ∧
      (e.isForall = true → e1 = e) := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩, fun _ => rfl⟩
  rename_i h
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨⟨hb, he, _, _, _, _, rfl⟩, fun h' => (h h').elim⟩
  · exact .getEnv <| .getLCtx .throw

theorem _root_.Lean4Lean.TypeChecker.LitApp.const {C : Environment} {P} {n ls ci ty} (hci : C.find? n = some ci)
    (hty : ty = ci.instantiateTypeLevelParams ls) : LitApp C P (.const n ls) ty := by
  intro J ls' Ds ci' h hf _
  rcases eqv_mkAppN_const h with ⟨h', hD⟩ | ⟨_, _, _, _, h', -⟩
  · cases h'; cases hci.symm.trans hf; subst hty hD
    exact ⟨by simpa [Expr.instForall] using BEq.rfl, fun _ h => by simp at h⟩
  · cases h'

mutual
/-- `inferType'` on a term not in the cache. -/
theorem inferTypeCore.WF_lit [VEnv.Injective] (hb : e.hasLooseBVars = false)
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferTypeCore e inferOnly).WF c s fun ty s' => (∃ e' ty', c.TrTyping e ty e' ty') ∧
      (inferOnly = false →
        LitApp c.env (ArgTyped c.venv c.lparams c.vlctx) e ty) := by
  unfold inferTypeCore; lift_lets; intro F
  generalize hP : (fun _ (_ : VState) => _) = P
  have hF {ty e' ty' s} (H : c.TrTyping e ty e' ty')
      (HL : inferOnly = false →
        LitApp c.env (ArgTyped c.venv c.lparams c.vlctx) e ty) :
      (F ty).WF c s P := hP ▸ .pure ⟨⟨_, _, H⟩, HL⟩
  have hN {e₀ : Expr} {ty} (hA : ∀ f a, e₀ ≠ .app f a) (hC : ∀ n ls, e₀ ≠ .const n ls) :
      inferOnly = false →
        LitApp c.env (ArgTyped c.venv c.lparams c.vlctx)
          e₀ ty := fun _ => .of_ne hA hC
  split
  · extract_lets G1; split <;> [split; skip]
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h => ?_
      have ⟨_, h, _⟩ := c.trenv.find? h <|
        (c.safePrimitives h (literal_is_primitive (.inl rfl))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨_, h⟩) (hN nofun nofun)
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h1 => ?_
      refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h2 => ?_
      have ⟨_, h1, _⟩ := c.trenv.find? h1 <|
        (c.safePrimitives h1 (literal_is_primitive (.inr (.inl rfl)))).1 ▸ DefinitionSafety.le_safe
      have ⟨_, h2, _⟩ := c.trenv.find? h2 <|
        (c.safePrimitives h2 (literal_is_primitive (.inr (.inr rfl)))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨⟨_, h1⟩, ⟨_, h2⟩⟩) (hN nofun nofun)
    · rename_i h; have ⟨_, h⟩ := hinf (by simpa using h)
      have := h.lit_has_type
      simp [G1]; exact hF (infer_literal this) (hN nofun nofun)
  · refine (inferType'.WF_lit (by exact h1) ?_).bind fun _ _ _ ⟨⟨_, _, hb, h1, h⟩, _⟩ => ?_
    · exact fun h => let ⟨_, .mdata h⟩ := hinf h; ⟨_, h⟩
    exact hF ⟨hb, .mdata h1, h⟩ (hN nofun nofun)
  · refine (inferType'.WF_lit (by exact h1) ?_).bind
      fun _ _ _ ⟨⟨_, _, hb, h1, h2, h3⟩, _⟩ => ?_
    · exact fun h => let ⟨_, .proj h ..⟩ := hinf h; ⟨_, h⟩
    have hCD : ∀ n w, c.env.constants.find? n = some (.ctorInfo w) →
        c.safety ≤ (ConstantInfo.ctorInfo w).safety →
        CtorDoms c.venv w.levelParams w.numParams w.numFields w.type := by
      intro n w hw hs
      obtain ⟨d, t, cv, venv₀, -, ⟨-, -, -, -, -, -, hnp, hnf, -⟩, -, -, hle, -, hdoms⟩ :=
        c.trenv.ctorInfo_type hw hs
      rw [hnp, hnf]; exact hdoms.mono hle
    exact (inferProj.WF'_doms h1 h2 h3 hb hCD).bind fun ty _ _ ⟨ty', h⟩ => hF h (hN nofun nofun)
  · exact .readThe <| (M.WF.liftExcept inferFVar.WF).lift.bind fun _ _ _ ⟨_, _, h⟩ =>
      hF h (hN nofun nofun)
  · exact .throw
  · simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at hb
  · split <;> rename_i h
    · refine .readThe <| (M.WF.liftExcept (checkLevel.WF h1)).lift.bind fun _ _ _ ⟨_, h⟩ => ?_
      exact hF (infer_sort h) (hN nofun nofun)
    · let ⟨_, .sort h⟩ := hinf (by simpa using h)
      exact hF (infer_sort h) (hN nofun nofun)
  · refine .readThe <| (M.WF.liftExcept (inferConstant.WF h1 hinf)).lift.bind
      fun _ _ _ ⟨⟨_, _, h⟩, _, hci, hty⟩ => hF h fun _ => .const hci hty
  · exact (inferLambda.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h (hN nofun nofun)
  · exact (inferForall.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h (hN nofun nofun)
  · split <;> rename_i h
    · let ⟨_, h'⟩ := hinf h
      exact (inferApp.WF h').bind fun _ _ _ ⟨_, h'⟩ => hF h' fun h'' => by cases h.symm.trans h''
    refine (inferType'.WF_lit h1.1 ?_).bind
      fun tyf s₁ le₁ ⟨⟨_, _, hfb, hf1, hf2, hf3⟩, LF⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ h _⟩ := hinf h; ⟨_, h⟩
    refine (ensureForallCore.WF₂ hf2).bind fun _ s₂ le₂ ⟨H, hself⟩ => ?_
    obtain ⟨hb, h2, name, dType, body, bi, rfl⟩ := H
    let ⟨_, .forallE (ty' := dType') hl1 hl2 hl3 hl4, hl5⟩ := h2
    extract_lets _ G1
    refine (inferType'.WF_lit h1.2 ?_).bind
      fun aType s₃ le₃ ⟨⟨_, aType', hab, ha1, ha2, ha3⟩, _⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ _ h⟩ := hinf h; ⟨_, h⟩
    extract_lets G2
    suffices ∀ {s b}, s₃ ≤ s → (b = true → c.IsDefEqU dType' aType') → RecM.WF c s (G2 b) P by
      split
      · refine .bind ?_ (Q := fun b _ => b = true → c.IsDefEqU dType' aType')
          fun b _ le H => this le H
        intro _ mwf wf _ _ eq
        let c' := { c with eagerReduce := true }
        have ⟨_, h1, h2, h3, h4⟩ :=
          isDefEq.WF (c := c') hl3 ha2 _ mwf { wf with supp := { wf.supp with } } _ _ eq
        exact ⟨_, h1, h2, { h3 with supp := { h3.supp with } }, h4⟩
      · exact (isDefEq.WF hl3 ha2).bind fun b _ le H => this le H
    subst G2; dsimp; rintro s ⟨⟩ le₄ H
    · exact .getEnv <| .getLCtx .throw
    simp [G1, Expr.bindingBody!]
    have hf3 := hf3.defeqU_r c.Ewf c.Δwf hl5.symm
    have ha3 := ha3.defeqU_r c.Ewf c.Δwf (H rfl).symm
    refine .stateWF fun wf => ?_
    subst hP; refine hF ⟨?_, .app hf3 ha3 hf1 ha1, hl4.inst c.Ewf ha3 ha1, .app hf3 ha3⟩ ?_
    · exact fun _ hP he => (hfb.trans hb _ hP he.1).2.instantiate1 he.2
    intro hio J ls Ds ci heq hfind hsize
    rcases eqv_mkAppN_const heq with ⟨he, -⟩ | ⟨f', a', Ds₀, x, he, rfl, hf', ha'⟩
    · cases he
    cases he
    have hsz : Ds₀.size < ci.type.leadingForalls := by simp at hsize; omega
    have le₁₄ : s₁ ≤ s := le₂.trans (le₃.trans le₄)
    obtain ⟨hTf, hargs⟩ := LF (by simpa using hio) hf' hfind (Nat.le_of_lt hsz)
    have hlf : Ds₀.toList.length < (ci.instantiateTypeLevelParams ls).leadingForalls := by
      have : (ci.instantiateTypeLevelParams ls).leadingForalls = ci.type.leadingForalls := by
        unfold ConstantInfo.instantiateTypeLevelParams
        exact Expr.leadingForalls_instantiateLevelParams
      rw [this]; simpa using hsz
    obtain ⟨n, d, b, bi', hT⟩ := Expr.instForall_forallE _ _ hlf
    rw [hT] at hTf
    obtain ⟨n', d', b', bi'', rfl, hd, hb'⟩ := Expr.eqv_forallE hTf
    cases hself rfl
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Array.toList_push, Expr.instForall_concat, hT]
      simp only [Expr.instantiate1_eq, Expr.bindingBody!]
      exact Expr.instantiate1'_eqv₂ ha' hb'
    simp only [Array.size_push] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Array.getElem_push_lt hk, Array.toList_push,
        List.take_append_of_le_length (by simpa using Nat.le_of_lt hk)]
      exact hargs k hk
    · rw [Array.getElem_push_eq, Array.toList_push,
        List.take_append_of_le_length (by simp), ← Array.length_toList, List.take_length, hT]
      have hx : c.TrExprS x _ := ha1.eqv ha'
      have hd' : c.TrExprS d _ := hl3.eqv hd
      exact fun _ _ => ⟨_, _, hx, hd', ha3⟩

  · exact (inferLet.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h (hN nofun nofun)


/-- `inferType'`, and in check mode what it establishes about a constant applied within its
type's literal binders (`LitApp`), which the cache of checked types keeps. -/
theorem inferType'.WF_lit [VEnv.Injective]
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty s' => (∃ e' ty', c.TrTyping e ty e' ty') ∧
      (inferOnly = false →
        LitApp c.env (ArgTyped c.venv c.lparams c.vlctx) e ty) := by
  unfold inferType'
  split <;> [exact .throw; (rename_i hb; refine .get <| .readThe ?_)]
  split
  · rename_i r l h
    obtain ⟨_, h, hv, hc⟩ := State.cached?_spec h
    refine .stateWF fun wf => ?_
    have H : (∃ e' ty', c.TrTyping e r e' ty') ∧
        (inferOnly = false → LitApp c.env (ArgTyped c.venv c.lparams c.vlctx) e r) := by
      cases inferOnly with
      | false =>
        have := wf.inferTypeC_wf.now wf.shape h hv hc h1; exact ⟨this.1, fun _ => this.2⟩
      | true =>
        obtain ⟨e', he'⟩ := hinf rfl
        exact ⟨wf.inferTypeI_wf.now wf.shape h hv hc e' he', nofun⟩
    exact RecM.WF.taintWith.bind fun _ _ _ _ => .pure H
  have hd : ∀ fv ∈ e.fvarsList, c.lctx.Dom fv := fun fv h =>
    c.lctx_eq ▸ c.mlctx_wf.dom_of_mem ((fvarsIn_iff.1 h1).1 fv h)
  have hmv := (fvarsIn_iff.1 h1).2
  refine (RecM.WF.withTaintLearn (D := (· ∈ e.fvarsList))
    (Pre := fun m => inferOnly = true → ∃ e', TrExprS c.venv c.lparams m.vlctx e e')
    (P := fun ty m => (∃ e' ty', TrTyping c.venv c.lparams m.vlctx e ty e' ty') ∧
      (inferOnly = false → LitApp c.env (ArgTyped c.venv c.lparams m.vlctx) e ty))
    (R := fun ty => SuppBelow c.toContext e ty) hd
    (fun m hm S c₂ hA hS hD hl hc => inferTypeCore.SS (by simpa using hb) hA hS hd
      (Lean.Expr.suppIn_of_fvars hD hl hc) m hm)
    (fun c₂ hv henv hl hpre hD => by
      rw [← hv, ← hl] at hpre; rw [← hv, ← hl, ← henv]
      have h1₂ : e.FVarsIn (· ∈ c₂.vlctx.fvars) :=
        fvarsIn_iff.2 ⟨fun fv h => c₂.mlctx_wf.mem_of_dom (c₂.lctx_eq ▸ hD fv h), hmv⟩
      exact inferTypeCore.WF_lit (by simpa using hb) h1₂ hpre)
    (inferTypeCore.WF_lit (by simpa using hb) h1 hinf)).bind
    fun ⟨ty, t⟩ s le ⟨⟨⟨e', ty', H⟩, HL⟩, hR, hL⟩ => ?_
  dsimp only at HL ⊢
  rintro _ mwf wf a s' ⟨⟩
  obtain ⟨lab, hlab, hk⟩ := State.keyLabel_eq s.toState t
  have learn (k' : Expr) (hk' : (e == k') = true) (hval : s.scopeIds.valid lab (s.scopeIds.labelId lab) = true)
      (hc : c.ceiling.all (lab ≤ ·)) : ∃ L g, g ≤ s.ngen ∧ Keeps L g s.ngen ∧ Admits L g c.lctx ∧
      Learned c.venv c.lparams (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab) L g
        fun m => (∀ fv ∈ k'.fvarsList, m.lctx.Dom fv) → (inferOnly = true →
          ∃ e', TrExprS c.venv c.lparams m.vlctx k' e') →
          (∃ e' ty', TrTyping c.venv c.lparams m.vlctx k' ty e' ty') ∧
          (inferOnly = false → LitApp c.env (ArgTyped c.venv c.lparams m.vlctx) k' ty) := by
    refine ⟨c.lctx, s.ngen, Lean.NameGenerator.LE.rfl, Keeps.refl _ _, Admits.refl _ _, ?_⟩
    have hval' := le_of_valid hval; rw [le.2.1] at hval'
    have H := hL lab hlab hval' hc
    rw [← le.2.2] at H
    have hk'' : (k' == e) = true := by rwa [BEq.comm] at hk'
    intro m wfm hbm ha hD hpre
    have hDe : ∀ fv ∈ e.fvarsList, m.lctx.Dom fv := fun fv h =>
      hD fv ((fvarsIn_iff.1 (FVarsIn.eqv hk''
        (fvarsIn_iff.2 ⟨fun _ h => h, FVarsIn.eqv hk' hmv⟩))).1 fv h)
    obtain ⟨⟨_, _, b1⟩, b2⟩ := H m wfm hbm ha hDe fun hio =>
      let ⟨e'', h''⟩ := hpre hio; ⟨_, h''.eqv hk''⟩
    exact ⟨⟨_, _, b1.eqv hk' BEq.rfl⟩, fun hio => LitApp.congr hk' (b2 hio)⟩
  cases inferOnly
  · dsimp only; rw [hk]
    refine ⟨_, rfl, .rfl, { wf with
      supp := { wf.supp with
        inferTypeC := CondSupp.insert wf.supp.inferTypeC (CondSupp.of wf.supp hd hR) }
      inferTypeC_wf := wf.inferTypeC_wf.insert fun k' hk' hval hc => ?_
      ids_made := ⟨wf.ids_made.1, wf.ids_made.2.1,
        wf.ids_made.2.2.1.insert (wf.labelId_le _), wf.ids_made.2.2.2⟩ },
      ⟨_, _, H⟩, fun _ => HL rfl⟩
    obtain ⟨L, g, a1, a2, a3, a4⟩ := learn k' hk' hval hc
    refine ⟨L, g, a1, a2, a3, fun m wfm hbm ha hfv => ?_⟩
    have := a4 m wfm hbm ha (fun fv h => wfm.dom_of_mem ((fvarsIn_iff.1 hfv).1 fv h)) nofun
    exact ⟨this.1, this.2 rfl⟩
  · dsimp only; rw [hk]
    refine ⟨_, rfl, .rfl, { wf with
      supp := { wf.supp with
        inferTypeI := CondSupp.insert wf.supp.inferTypeI (CondSupp.of wf.supp hd hR) }
      inferTypeI_wf := wf.inferTypeI_wf.insert fun k' hk' hval hc => ?_
      ids_made := ⟨wf.ids_made.1, wf.ids_made.2.1.insert (wf.labelId_le _),
        wf.ids_made.2.2⟩ }, ⟨_, _, H⟩, nofun⟩
    obtain ⟨L, g, a1, a2, a3, a4⟩ := learn k' hk' hval hc
    refine ⟨L, g, a1, a2, a3, fun m wfm hbm ha e'' he'' => ?_⟩
    exact (a4 m wfm hbm ha (wfm.dom_of_tr he'') fun _ => ⟨_, he''⟩).1

end

theorem inferType'.WF [VEnv.Injective]
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  (inferType'.WF_lit h1 hinf).mono fun _ _ _ h => h.1

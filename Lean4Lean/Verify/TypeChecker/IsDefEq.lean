import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem isDefEqLambda.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqLambda e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqLambda; let c' := c.withMLC m
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hsubst]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .lam (ty' := t₁') (body' := b₁') ⟨_, a1⟩ a2 a3 := he₁
  let .lam (ty' := t₂') (body' := b₂') b1 b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.lam b₁') (t₂'.lam b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hsubst]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F; split <;> rename_i h
  · extract_lets d₂'
    have : d₂' = d₂.instantiateList fvs := by split at hx <;> [simp [d₂', hsubst]; exact hx]
    clear_value d₂'; subst this
    refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
    have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
    have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
    refine isDefEqLambda.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst]) a3'' b3'
      |>.mono fun _ _ _ h hb => ?_
    have ⟨_, bb⟩ := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb)
    exact ⟨_, .symm <| .lamDF tt'.symm <| bb.symm⟩
  · simp [Expr.hasLooseBVars] at h
    refine .stateWF fun wf => ?_
    have {bᵢ : Expr} {bᵢ'} (h : bᵢ.looseBVarRange' = 0)
        (a3 : TrExprS c'.venv c'.lparams ((none, .vlam t₂') :: c'.vlctx)
          (bᵢ.instantiateList fvs 1) bᵢ') :
        ∃ e', (c.withMLC m).TrExprS (bᵢ.instantiateList (default :: fvs)) e' ∧
          c'.venv.IsDefEqU c'.lparams.length (t₂' :: c'.vlctx.toCtx) bᵢ' e'.lift := by
      simp; rw [← Expr.instantiateList_instantiate1_comm (by rfl)]
      let v : FVarId := ⟨s.ngen.curr⟩
      have hΔ : VLCtx.WF c'.venv c.lparams.length ((some (v, []), .vlam t₂') :: m.vlctx) := by
        refine ⟨mwf.1.tr.wf, ?_, b1⟩
        rintro _ _ ⟨⟩; simp; exact fun h => s.ngen.not_reserves_self (wf.ngen_wf _ h)
      have := a3.inst_fvar c.Ewf.ordered hΔ
      have eq {e} (hb : bᵢ.looseBVarRange' = 0) (he : e.looseBVarRange' = 0) :
          (bᵢ.instantiateList fvs 1).instantiate1' e = bᵢ.instantiateList fvs 1 := by
        rw [Expr.instantiate1'_eq_self]; rw [Expr.instantiateList'_eq_self] <;> simp [*]
      rw [eq h rfl, ← eq (e := .fvar v) h rfl]
      let ⟨_, H⟩ := this.weakFV_inv c.Ewf (.skip_fvar _ _ .refl) (.refl c.Ewf hΔ)
        (m.noBV ▸ this.closed) (by rw [eq h rfl]; exact a3.fvarsIn)
      refine ⟨_, H, this.uniq c'.Ewf (.refl c'.Ewf hΔ) <| H.weakFV c'.Ewf (.skip_fvar _ _ .refl) hΔ⟩
    let ⟨_, a4, a5⟩ := this h.1 a3'
    let ⟨_, b4, b5⟩ := this h.2 b3
    exact isDefEqLambda.WF (fvs := default :: fvs) (by simp [hsubst]) a4 b4
      |>.mono fun _ _ _ h hb =>
      have hΓ := ⟨c'.Δwf, b1⟩
      have ⟨_, bb⟩ := eq.symm.trans c'.Ewf hΓ a5
        |>.trans c'.Ewf hΓ ((h hb).weak c'.Ewf (B := t₂')) |>.trans c'.Ewf hΓ b5.symm
      ⟨_, .symm <| .lamDF tt'.symm bb.symm⟩

theorem isDefEqForall.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqForall e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqForall; let c' := c.withMLC m
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hsubst]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .forallE (ty' := t₁') (body' := b₁') ⟨_, a1⟩ _ a2 a3 := he₁
  let .forallE (ty' := t₂') (body' := b₂') b1 ⟨_, bT⟩ b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.forallE b₁') (t₂'.forallE b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hsubst]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F; split <;> rename_i h
  · extract_lets d₂'
    have : d₂' = d₂.instantiateList fvs := by split at hx <;> [simp [d₂', hsubst]; exact hx]
    clear_value d₂'; subst this
    refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
    have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
    have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
    refine isDefEqForall.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst]) a3'' b3'
      |>.mono fun _ _ _ h hb => ?_
    have bb := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb) |>.of_r c'.Ewf mwf'.1.tr.wf.toCtx bT
    exact ⟨_, .symm <| .forallEDF tt'.symm <| bb.symm⟩
  · simp [Expr.hasLooseBVars] at h
    refine .stateWF fun wf => ?_
    have {bᵢ : Expr} {bᵢ'} (h : bᵢ.looseBVarRange' = 0)
        (a3 : TrExprS c'.venv c'.lparams ((none, .vlam t₂') :: c'.vlctx)
          (bᵢ.instantiateList fvs 1) bᵢ') :
        ∃ e', (c.withMLC m).TrExprS (bᵢ.instantiateList (default :: fvs)) e' ∧
          c'.venv.IsDefEqU c'.lparams.length (t₂' :: c'.vlctx.toCtx) bᵢ' e'.lift := by
      simp; rw [← Expr.instantiateList_instantiate1_comm (by rfl)]
      let v : FVarId := ⟨s.ngen.curr⟩
      have hΔ : VLCtx.WF c'.venv c.lparams.length ((some (v, []), .vlam t₂') :: m.vlctx) := by
        refine ⟨mwf.1.tr.wf, ?_, b1⟩
        rintro _ _ ⟨⟩; simp; exact fun h => s.ngen.not_reserves_self (wf.ngen_wf _ h)
      have := a3.inst_fvar c.Ewf.ordered hΔ
      have eq {e} (hb : bᵢ.looseBVarRange' = 0) (he : e.looseBVarRange' = 0) :
          (bᵢ.instantiateList fvs 1).instantiate1' e = bᵢ.instantiateList fvs 1 := by
        rw [Expr.instantiate1'_eq_self]; rw [Expr.instantiateList'_eq_self] <;> simp [*]
      rw [eq h rfl, ← eq (e := .fvar v) h rfl]
      let ⟨_, H⟩ := this.weakFV_inv c.Ewf (.skip_fvar _ _ .refl) (.refl c.Ewf hΔ)
        (m.noBV ▸ this.closed) (by rw [eq h rfl]; exact a3.fvarsIn)
      refine ⟨_, H, this.uniq c'.Ewf (.refl c'.Ewf hΔ) <| H.weakFV c'.Ewf (.skip_fvar _ _ .refl) hΔ⟩
    let ⟨_, a4, a5⟩ := this h.1 a3'
    let ⟨_, b4, b5⟩ := this h.2 b3
    exact isDefEqForall.WF (fvs := default :: fvs) (by simp [hsubst]) a4 b4
      |>.mono fun _ _ _ h hb =>
      have hΓ := ⟨c'.Δwf, b1⟩
      have bb := eq.symm.trans c'.Ewf hΓ a5 |>.trans c'.Ewf hΓ ((h hb).weak c'.Ewf (B := t₂'))
        |>.trans c'.Ewf hΓ b5.symm |>.of_r c'.Ewf hΓ bT
      ⟨_, .symm <| .forallEDF tt'.symm bb.symm⟩

theorem quickIsDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (quickIsDefEq e₁ e₂ useHash) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold quickIsDefEq
  refine .bind (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h => ?_
  · intro _ mwf wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    let ⟨_, _, a1, a2, ewf, a4⟩ := wf.ectx
    have ⟨ewf, _, h1⟩ := EquivManager.isEquiv.WF ewf hm
    refine let vs' := { s with toState := s' }; ⟨vs', rfl, .rfl, { wf with ectx := ?_ }, ?_⟩
    · exact ⟨_, _, a1, a2, ewf, a4⟩
    · intro h; apply (VEnv.IsDefEqU.weak'_iff c.Ewf a1 a2.toCtx).1
      exact (h1 h).uniq c.Ewf (a2.bvars_eq.trans c.mlctx.noBV)
        a1 (he₁.weakFV' c.Ewf a2 a1) (he₂.weakFV' c.Ewf a2 a1)
  split <;> [exact .pure fun _ => h ‹_›; split]
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqLambda.WF (subst := #[]) (fvs := []) rfl (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqForall.WF (subst := #[]) (fvs := []) rfl (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · have .sort hu := he₁; have .sort hv := he₂
    refine .pure fun h => ⟨_, .sortDF (.of_ofLevel hu) (.of_ofLevel hv) ?_⟩
    exact Level.isEquiv_wf (toLBool_true.1 h) hu hv
  · let .mdata he₁ := he₁; let .mdata he₂ := he₂
    exact .toLBoolM <| isDefEq.WF he₁ he₂
  · cases he₁
  · rename_i a1 a2 _; refine .pure fun h => ?_
    simp at h; subst h; exact he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
  · exact .pure nofun

theorem isDefEqArgs.WF {c : VContext} {s : VState}
    (H : ∃ e₁', c.TrExprS e₁.getAppFn e₁' ∧ ∃ e₂', c.TrExprS e₂.getAppFn e₂' ∧ c.IsDefEqU e₁' e₂')
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqArgs e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqArgs; split <;> (unfold Expr.getAppFn at H)
  · let .app a1 a2 a3 a4 := he₁
    let .app b1 b2 b3 b4 := he₂
    refine (isDefEq.WF a4 b4).bind fun _ _ _ h2 => ?_
    split <;> [exact .pure nofun; rename_i hb2]
    refine (isDefEqArgs.WF H a3 b3).mono fun _ _ _ h1 hb1 => ?_
    simp at hb2
    exact ⟨_, .appDF ((h1 hb1).of_l c.Ewf c.Δwf a1) ((h2 hb2).of_l c.Ewf c.Δwf a2)⟩
  · exact .pure nofun
  · exact .pure nofun
  · refine .pure fun _ => ?_
    simp [*] at H; let ⟨_, h1, _, h2, h3⟩ := H
    have a1 := he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) h1
    have a2 := he₂.uniq c.Ewf (.refl c.Ewf c.Δwf) h2
    exact a1.trans c.Ewf c.Δwf h3 |>.trans c.Ewf c.Δwf a2.symm

theorem tryEtaExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansionCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨ty₁, a1, a2, a3, a4⟩ => ?_
  refine (whnf.WF a3).bind fun _ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [skip; exact .pure nofun]
  let .forallE (ty' := ty') c1 c2 c3 c4 := b2
  replace a4 := a4.defeqU_r c.Ewf c.Δwf b3.symm
  -- have := b2.uniq c.Ewf (.refl c.Ewf c.Δwf) (.forallE c1 c2 c3 c4)
  refine (isDefEq.WF he₁ (.lam c1 c3 (.app (a4.weak c.Ewf) (.bvar .zero) (
    Expr.liftLooseBVars_eq_self (c.mlctx.noBV ▸ a2.closed).looseBVarRange_le ▸
      a2.weakBV c.Ewf (.skip (.vlam ty') .refl)) (.bvar rfl)))).mono fun _ _ _ h hb => ?_
  exact (h hb).trans c.Ewf c.Δwf ⟨_, .eta a4⟩

theorem tryEtaExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansion e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaExpansion, orM, toBool]
  refine (tryEtaExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem getSortLevel.WF
    (he : c.TrExprS e e') : (getSortLevel e).WF c s fun l _ =>
      ∃ u', VLevel.ofLevel c.lparams l = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun ty _ le ⟨ty', _, _, h1, h2⟩ => ?_
  refine (ensureSortCore.WF h1).bind fun ty _ le h => ?_
  obtain ⟨⟨u, rfl⟩, ⟨ty₂, h3, h4⟩, _⟩ := h
  let .sort hu := h3
  exact .pure ⟨_, hu, h2.defeqU_r c.Ewf c.Δwf h4.symm⟩

theorem isProp.WF
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) := by
  refine (getSortLevel.WF he).bind fun l _ le ⟨u', hu, h⟩ => .pure fun H => ?_
  exact h.defeqU_r c.Ewf c.Δwf
    ⟨_, .sortDF (.of_ofLevel hu) trivial (ofLevel_isAlwaysZero hu H)⟩

/-- A complete application of a constructor of a non-recursive structure without indices: its
block, its arguments as parameters and fields, and its type. -/
theorem _root_.Lean4Lean.TypeChecker.VContext.structCtorApp (c : VContext) {e₂ : Expr}
    {e₂' : VExpr} (he₂ : c.TrExprS e₂ e₂') {f : Name} {lsF : List Level}
    (hf : e₂.getAppFn = .const f lsF) {fInfo : ConstructorVal}
    (hci : c.env.find? f = some (.ctorInfo fInfo))
    (hnargs : e₂.getAppNumArgs = fInfo.numParams + fInfo.numFields)
    (hstruct : c.env.isNonRecStructure fInfo.induct = true) :
    ∃ d t T c' ls As fs, c.venv.inducts fInfo.induct = some (d, t) ∧ d.types[t]? = some T ∧
      T.ctors = [c'] ∧ T.indices = [] ∧ d.isRec = false ∧
      (∀ l ∈ ls, l.WF c.lparams.length) ∧ ls.length = d.uvars ∧
      fInfo.numParams = d.params.length ∧ fInfo.numFields = c'.fields.length ∧
      As.length = d.params.length ∧ fs.length = c'.fields.length ∧
      e₂' = .appN (.const c'.name ls) (As ++ fs) ∧
      List.Forall₂ c.TrExprS e₂.getAppArgsList (As ++ fs) ∧
      VEnv.Ctx.SubstEq c.venv c.lparams.length c.vlctx.toCtx
        ((VExpr.Subst.dflt.consList As).consList fs) ((VExpr.Subst.dflt.consList As).consList fs)
        ((c'.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) ∧
      c.HasType e₂' (.appN (.const fInfo.induct ls) As) := by
  have he := he₂
  rw [← Expr.mkAppRevList_getAppArgsRevList e₂, hf] at he
  obtain ⟨f', rs', rfl, hf', hrs⟩ := he.mkAppRevList_inv
  let .const hcs hls' hlen' := hf'
  have mapWF := c.trenv.map_wf
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hci hcs
  rw [Kernel.Environment.find?, mapWF.find?'_eq_find?] at hci
  obtain ⟨d, t, c', hs, hcv, -⟩ := c.trenv.ctorInfo hci hsafe
  obtain ⟨T, ht, hcidx, hcn, -, hind, hnp, hnf, -⟩ := hcv
  have hmc : f = c'.name := (hname : fInfo.name = f).symm.trans hcn
  subst hmc
  -- the structure
  obtain ⟨lp, -, hTs, -⟩ := c.trenv.blockConsts hs
  obtain ⟨v, hv, hTv⟩ := hTs t T ht
  obtain ⟨v', hv', hrec, hni', cn, hcn'⟩ : ∃ v', c.env.find? fInfo.induct = some (.inductInfo v') ∧
      v'.isRec = false ∧ v'.numIndices = 0 ∧ ∃ cn, v'.ctors = [cn] := by
    unfold Kernel.Environment.isNonRecStructure at hstruct
    split at hstruct <;> [rename_i h; cases hstruct]
    exact ⟨_, h, rfl, rfl, _, rfl⟩
  rw [Kernel.Environment.find?, mapWF.find?'_eq_find?, hind, hv] at hv'
  cases hv'
  obtain ⟨-, -, -, hni, -, hvc, -, hvr, -⟩ := hTv
  rw [hni'] at hni; rw [hcn'] at hvc; rw [hrec] at hvr
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, T.ctors = [c₁] := by
    match h : T.ctors, hvc with
    | [c₁], _ => exact ⟨c₁, rfl⟩
  have hc' : c' = c₁ := by
    rw [hc₁] at hcidx
    cases hk : fInfo.cidx <;> simp_all
  subst hc'
  have hi : T.indices = [] := List.eq_nil_of_length_eq_zero hni.symm
  -- the arguments
  have hlen : rs'.reverse.length = d.params.length + c'.fields.length := by
    rw [← hnp, ← hnf, ← hnargs, Expr.getAppNumArgs_eq, List.length_reverse,
      Lean4Lean.List.Forall₂.length_eq hrs]
  obtain ⟨hls, hlenls, As, fs, hrsAF, hA, hfs, W, hX⟩ :=
    c.Ewf.ctorApp c.Δwf.toCtx hs ht (c := c') (by simp [hc₁]) hlen (he₂.wf c.Ewf c.Δwf)
  have hil := ((c.Ewf.recFacts hs hls hlenls).ctor
    ((VInductDecl.mem_ctors_iff (j := t) (c := c')).2 ⟨T, ht, by simp [hc₁]⟩) ht).1
  rw [hi, List.length_nil, List.length_eq_zero_iff] at hil
  simp only [hil, List.map_nil, List.append_nil] at hX
  refine ⟨d, t, T, c', _, As, fs, hs, ht, hc₁, hi, hvr.symm, hls, hlenls, hnp, hnf, hA, hfs,
    by rw [hrsAF], ?_, W, by rw [hrsAF]; exact hX⟩
  rw [← hrsAF, ← Expr.getAppArgsRevList_reverse]
  exact (Lean4Lean.List.Forall₂.reverse (R := TrExprS c.venv c.lparams c.vlctx)).2 hrs

theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaStructCore
  split <;> [rename_i f lsF hf; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i fInfo; exact .pure nofun]
  split <;> [rename_i hnargs; exact .pure nofun]
  split <;> [rename_i hstruct; exact .pure nofun]
  simp only [beq_iff_eq] at hnargs
  have hΓ := c.Δwf.toCtx
  obtain ⟨d, t, T, c', ls, As, fs, hs, ht, hc, hi, hrec, hls, hlen, hnp, hnf, hA, hfs, rfl, hargs,
    W, hX₂⟩ := c.structCtorApp he₂ hf hci hnargs hstruct
  refine (inferType.WF he₁).bind fun ty₁ _ _ ⟨ty₁', _, _, a3, a4⟩ => ?_
  refine (inferType.WF he₂).bind fun ty₂ _ _ ⟨ty₂', _, _, b3, b4⟩ => ?_
  refine (isDefEq.WF a3 b3).bind fun b _ _ hb => ?_
  split <;> [rename_i hb'; exact .pure nofun]
  refine (getSortLevel.WF b3).bind fun l _ _ ⟨u', hu', hl⟩ => ?_
  -- the types of both sides
  have hT₂ := b4.uniqU c.Ewf hΓ hX₂
  have hx₁ : c.HasType e₁' (.appN (.const fInfo.induct ls) As) :=
    (a4.defeqU_r c.Ewf hΓ (hb hb')).defeqU_r c.Ewf hΓ hT₂
  have hI : ([] : List VExpr).length = T.indices.length := by simp [hi]
  have hx₁' : c.HasType e₁' (.appN (.const fInfo.induct ls) (As ++ [])) := by simpa using hx₁
  have WP := c.Ewf.projArgs hΓ hs ht hls hlen hA hI hx₁'
  simp only [List.append_nil, hi, List.map_nil] at WP
  obtain ⟨_, hS⟩ := hx₁'.isType c.Ewf.ordered hΓ
  have hPF := c.Ewf.projFacts hs ht hc
  -- the structure's sort
  have hlev : u' ≈ d.level.inst ls := by
    obtain ⟨-, -, -, -, -, -, T', hT', hname⟩ := c.Ewf.inducts hs
    cases ht.symm.trans hT'
    have hty := (c.Ewf.recFacts hs hls hlen).type ht
    rw [hi, List.map_nil, List.append_nil] at hty
    have hty0 := hty.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
    rw [← VExpr.closed_subst c.Ewf.ordered hty .dflt] at hty0
    have hsort := VEnv.HasType.appN_substT (Δ := []) (as := As) hty0 (by simp [hA])
      (by simpa using WP)
    simp only [VExpr.subst] at hsort
    rw [hname] at hsort
    exact VEnv.IsDefEqU.sort_inv c.Ewf hΓ
      ((hT₂.of_l c.Ewf hΓ hl).hasType.2.uniqU c.Ewf hΓ hsort)
  generalize hmp : (!l.isNeverZero) = mp
  dsimp only
  have hfsl : e₂.getAppArgsList.length = fInfo.numParams + c'.fields.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hargs, List.length_append, hA, hfs, hnp]
  have hsize : e₂.getAppArgs.size = fInfo.numParams + c'.fields.length := by
    rw [Expr.getAppArgs_eq, List.size_toArray, hfsl]
  -- what each step of the loop establishes about a field
  let P : Nat → Prop := fun j =>
    (mp = true → ∀ f, c'.fields[j]? = some f → f.level.inst ls ≈ .zero) ∧
    ∀ h : j < fs.length, c.IsDefEqU (.proj fInfo.induct j e₁') fs[j]
  have hPA : ∀ j < c'.fields.length, (∀ j' ≤ j, mp = true →
      ∀ f, c'.fields[j']? = some f → f.level.inst ls ≈ .zero) → d.ProjAllowed c' ls j := by
    intro j hj hlv hz
    cases mp with
    | false =>
      refine (hz fun ns => ?_).elim
      have h1 : l.isNeverZero = true := by simpa using hmp
      rw [← congrFun hlev ns]
      exact ofLevel_isNeverZero hu' h1 ns
    | true =>
      exact ⟨fun f hf => hlv j (Nat.le_refl _) rfl f hf,
        fun j' hj' f hf => .inl (hlv j' (Nat.le_of_lt hj') rfl f hf)⟩
  refine (RecM.WF.forIn'_range
    (Inv := fun a st _ => st = (none, ()) ∧ ∀ j, fInfo.numParams + j < a → P j)
    (Done := fun st _ => st.1 = some false ∨ (st.1 = none ∧ ∀ j < c'.fields.length, P j))
    ?_ ⟨rfl, fun j h => by omega⟩ ?_).bind fun r _ _ hr => ?_
  · rintro i hi st s₁ ⟨rfl, hinv⟩
    have hi1 : fInfo.numParams ≤ i := hi.1
    have hi2 : i < e₂.getAppArgs.size := hi.2.1
    obtain ⟨j, rfl⟩ : ∃ j, i = fInfo.numParams + j := ⟨i - fInfo.numParams, by omega⟩
    have hj : j < c'.fields.length := by omega
    have hjf : j < fs.length := by omega
    obtain ⟨f, hf⟩ : ∃ f, c'.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
    -- the argument and its translation
    have harg : c.TrExprS e₂.getAppArgs[fInfo.numParams + j] fs[j] := by
      have hl : e₂.getAppArgsList[fInfo.numParams + j]? = some e₂.getAppArgs[fInfo.numParams + j] := by
        simp [Expr.getAppArgs_eq]
      obtain ⟨b', hb1, hb2⟩ := List.Forall₂.getElem?_l hargs hl
      rw [List.getElem?_append_right (by omega), hA, ← hnp, Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hjf] at hb1
      cases hb1; exact hb2
    -- comparing the projection with the argument
    have hjp : ∀ s₂, (mp = true → f.level.inst ls ≈ .zero) →
        RecM.WF c s₂ (do
          let __do_lift ← isDefEq (Expr.proj fInfo.induct (fInfo.numParams + j - fInfo.numParams) e₁)
            e₂.getAppArgs[fInfo.numParams + j]
          if __do_lift = true then pure (ForInStep.yield ((none : Option Bool), ()))
          else pure (ForInStep.done (some false, ()))) fun r s' =>
            (∀ b', r = .yield b' →
              b' = (none, ()) ∧ ∀ j', fInfo.numParams + j' < fInfo.numParams + j + 1 → P j') ∧
            (∀ b', r = .done b' →
              b'.1 = some false ∨ (b'.1 = none ∧ ∀ j < c'.fields.length, P j)) := by
      intro s₂ hlv
      rw [Nat.add_sub_cancel_left]
      have hlv' : ∀ j' ≤ j, mp = true → ∀ f, c'.fields[j']? = some f → f.level.inst ls ≈ .zero := by
        intro j' hj' hm f' hf'
        rcases Nat.lt_or_ge j' j with h | h
        · exact (hinv j' (by omega)).1 hm f' hf'
        · obtain rfl : j' = j := by omega
          cases hf.symm.trans hf'; exact hlv hm
      have hP := hPA j hj hlv'
      have hPC := (VEnv.projCongr c.Ewf.ordered hΓ hs ht hc hPF hls hlen hA hI hA hI WP hS hx₁' j f
        hf hP).2
      refine (isDefEq.WF (.proj he₁ ⟨_, hPC⟩) harg).bind fun b _ _ hb => ?_
      split
      · refine .pure ⟨fun b' e => ?_, nofun⟩
        cases e
        refine ⟨rfl, fun j' hj' => ?_⟩
        rcases Nat.lt_or_ge j' j with h | h
        · exact hinv j' (by omega)
        · obtain rfl : j' = j := by omega
          exact ⟨fun hm f' hf' => by cases hf.symm.trans hf'; exact hlv hm,
            fun _ => hb ‹_›⟩
      · exact .pure ⟨nofun, fun b' e => by cases e; exact .inl rfl⟩
    split
    · rename_i hm
      refine (inferType.WF harg).bind fun A _ _ ⟨A', _, _, hA1, hA2⟩ => ?_
      refine (isProp.WF hA1).bind fun bp _ _ hbp => ?_
      split
      · refine hjp _ fun _ => ?_
        -- the argument is a proof, so its field is
        have hFT := c.Ewf.ctorApp_fieldType hΓ hs ht hc hls hfs W hf
        have hfj := VEnv.Ctx.SubstEq.getElem fs.length rfl W (by simp [hfs]) j hjf (by simp; omega)
        simp only [List.getElem_map, VExpr.Subst.consList_append] at hfj
        rw [← VExpr.Subst.consList_append, (List.getElem?_eq_some_iff.1 hf).2] at hfj
        have hsame := hA2.uniqU c.Ewf hΓ hfj
        have := (hsame.of_l c.Ewf hΓ (hbp ‹_›)).hasType.2.uniqU c.Ewf hΓ hFT
        exact (VEnv.IsDefEqU.sort_inv c.Ewf hΓ this).symm
      · exact .pure ⟨nofun, fun b' e => by cases e; exact .inl rfl⟩
    · rename_i hm
      exact hjp _ fun h => absurd h hm
  · rintro st _ ⟨rfl, hall⟩
    refine .inr ⟨rfl, fun j hj => hall j ?_⟩
    rw [hsize]; omega
  · split
    · rename_i r' hr'
      rcases hr with h | ⟨h, -⟩ <;> rw [hr'] at h <;> cases h
      exact .pure nofun
    · rename_i hr'
      rcases hr with h | ⟨-, hall⟩; · rw [hr'] at h; cases h
      refine .pure fun _ => ⟨_, c.Ewf.structEta hΓ hs ht hc hi hrec hls hlen hA hfs hx₁
        (fun j hj => hPA j hj fun j' hj' hm f hf => (hall j' (by omega)).1 hm f hf)
        (fun j hj => (hall j (by omega)).2 hj)⟩

theorem tryEtaStruct.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStruct e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaStruct, orM, toBool]
  refine (tryEtaStructCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaStructCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqApp.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqApp e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqApp; split <;> [skip; exact .pure nofun]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  split <;> [rename_i eq; exact .pure nofun]
  have ⟨_, he₁'⟩ := AppStack.build <| e₁.mkAppList_getAppArgsList ▸ he₁
  have ⟨_, he₂'⟩ := AppStack.build <| e₂.mkAppList_getAppArgsList ▸ he₂
  refine (isDefEq.WF he₁'.tr he₂'.tr).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure nofun]
  let rec loop.WF {s args₁ args₂ f₁ f₂ f₁' f₂' eq i} (l₁ r₁ l₂ r₂)
      (h₁ : args₁.toList = l₁ ++ r₁) (hi₁ : l₁.length = i)
      (h₂ : args₂.toList = l₂ ++ r₂) (hi₂ : l₂.length = i)
      (he₁ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₁ l₁) f₁' r₁)
      (he₂ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₂ l₂) f₂' r₂)
      (H1 : c.IsDefEqU f₁' f₂') :
      RecM.WF c s (loop args₁ args₂ eq i) fun b _ => b →
        ∀ e₁', c.TrExprS (f₁.mkAppList args₁.toList) e₁' →
        ∀ e₂', c.TrExprS (f₂.mkAppList args₂.toList) e₂' → c.IsDefEqU e₁' e₂' := by
    unfold loop; split <;> rename_i h
    · have hr₁ : r₁.length > 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length > 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      let .app (a := a₁) (as := r₁) a1 a2 a3 a4 a5 := he₁
      let .app (a := a₂) (as := r₂) b1 b2 b3 b4 b5 := he₂
      simp [
        show args₁[i] = a₁ by cases args₁; cases h₁; simp [hi₁],
        show args₂[i] = a₂ by cases args₂; cases h₂; simp [hi₂]]
      refine (isDefEq.WF a4 b4).bind fun _ _ _ h => ?_
      split <;> [skip; exact .pure nofun]
      have H := (H1.of_l c.Ewf c.Δwf a1).appDF <| (h ‹_›).of_l c.Ewf c.Δwf a2
      exact loop.WF (l₁ ++ [a₁]) r₁ (l₂ ++ [a₂]) r₂
        (by simp [h₁]) (by simp [hi₁]) (by simp [h₂]) (by simp [hi₂])
        (by simp [a5]) (by simp [b5]) ⟨_, H⟩
    · have hr₁ : r₁.length = 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length = 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      simp at hr₁ hr₂; subst r₁ r₂; simp at h₁ h₂; subst l₁ l₂
      refine .pure fun _ _ h1 _ h2 => ?_
      have u1 := h1.uniq c.Ewf (.refl c.Ewf c.Δwf) he₁.tr
      have u2 := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂.tr
      exact u1.trans c.Ewf c.Δwf H1 |>.trans c.Ewf c.Δwf u2.symm
  refine loop.WF [] _ [] _ (i := 0) (by simp [Expr.getAppArgs_toList]) rfl
    (by simp [Expr.getAppArgs_toList]) rfl he₁' he₂' (h ‹_›) |>.mono fun _ _ _ h2 hb => ?_
  simp [Expr.getAppArgs_toList, Expr.mkAppList_getAppArgsList] at h2
  exact h2 hb _ he₁ _ he₂

theorem isDefEqProofIrrel.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqProofIrrel e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqProofIrrel
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, a1, a2, a3, a4⟩ => ?_
  refine (isProp.WF a3).bind fun _ _ _ h1 => ?_
  split <;> [exact .pure nofun; skip]
  rename_i h; simp at h
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, b1, b2, b3, b4⟩ => .toLBoolM ?_
  refine (isDefEq.WF a3 b3).mono fun _ _ _ h2 hb => ?_
  exact ⟨_, .proofIrrel (h1 h) a4 (b4.defeqU_r c.Ewf c.Δwf (h2 hb).symm)⟩

theorem cacheFailure.WF {c : VContext} {s : VState} :
    (cacheFailure e₁ e₂).WF c s fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨{ s with toState := _ }, rfl, .rfl, { wf with }, ⟨⟩⟩

theorem tryUnfoldProjApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    (tryUnfoldProjApp e).WF c s fun oe _ =>
    ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.WF he).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

def _root_.Lean4Lean.TypeChecker.ReductionStatus.WF
    (c : VContext) (e₁' e₂' : VExpr) (allowContinue := false) : ReductionStatus → Prop
  | .continue e₁ e₂ => allowContinue ∧ c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .unknown e₁ e₂ | .false e₁ e₂ => c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .true => c.IsDefEqU e₁' e₂'

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.bool
    (H1 : c.TrExpr e₁ e₁') (H2 : c.TrExpr e₂ e₂') (H : b = true → c.IsDefEqU e₁' e₂') :
    ReductionStatus.WF c e₁' e₂' allowContinue (.bool e₁ e₂ b) :=
  match b with
  | .false => ⟨H1, H2⟩
  | .true => H rfl

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.defeq
    (h1 : c.IsDefEqU e₁' e₁'') (h2 : c.IsDefEqU e₂' e₂'')
    (H : ReductionStatus.WF c e₁' e₂' ac r) : ReductionStatus.WF c e₁'' e₂'' ac r :=
  match r, H with
  | .continue .., ⟨a1, a2, a3⟩ =>
    ⟨a1, a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .unknown .., ⟨a2, a3⟩ | .false .., ⟨a2, a3⟩ =>
    ⟨a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .true, h => h1.symm.trans c.Ewf c.Δwf h |>.trans c.Ewf c.Δwf h2

theorem lazyDeltaReductionStep.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReductionStep e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_; extract_lets delta cont F1 F2
  have hdelta {s e e' ci} (he : c.TrExprS e e') (H : isDelta c.env e = some ci) :
      (delta e).WF c s fun r _ => c.TrExpr r e' := by
    let ⟨n, h1, ⟨_, h2⟩, ls, h3, _⟩ := isDelta_is_some.1 H
    have ⟨_, stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
    have .const a1 a2 a3 := h3 ▸ stk.tr
    have ⟨b1, b2, b3, b4⟩ := c.trenv.find?_uniq h1 a1
    refine (unfoldDefinition.WF he).bind fun oe _ _ H => ?_
    obtain _ | e' := oe; · cases H h1 h2 h3 (a3.trans b3.symm)
    have ⟨_, _, c1, c2⟩ := H
    exact (whnfCore.WF c1).mono fun x _ _ h => h.2.defeq c.Ewf c.Δwf c2
  have hcont {s e₁ e₂} (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
      (cont e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
    let ⟨_, se₁, de₁⟩ := he₁; let ⟨_, se₂, de₂⟩ := he₂
    refine (quickIsDefEq.WF se₁ se₂).bind fun _ _ _ h => .pure ?_; split
    · exact ⟨rfl, he₁, he₂⟩
    · exact de₁.symm.trans c.Ewf c.Δwf (h rfl) |>.trans c.Ewf c.Δwf de₂
    · exact ⟨he₁, he₂⟩
  split
  · exact .pure ⟨he₁.trExpr c.Ewf c.Δwf, he₂.trExpr c.Ewf c.Δwf⟩
  · refine (tryUnfoldProjApp.WF he₂).bind fun _ _ _ h => ?_; split
    · exact hcont (he₁.trExpr c.Ewf c.Δwf) (h _ rfl).2
    · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  · refine (tryUnfoldProjApp.WF he₁).bind fun _ _ _ h => ?_; split
    · exact hcont (h _ rfl).2 (he₂.trExpr c.Ewf c.Δwf)
    · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  rename_i dt dt' hd1 hd2; extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  have hF1 {s} : (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' true :=
    (hdelta he₁ ‹_›).bind fun _ _ _ h1 => (hdelta he₂ ‹_›).bind fun _ _ _ h2 => hcont h1 h2
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  rename_i h1 h2; simp at h1
  cases ptrEqConstantInfo_eq h1.1.1.2
  have ⟨n₁, b1₁, ⟨_, b2₁⟩, ls₁, b3₁, _⟩ := isDelta_is_some.1 hd1
  have ⟨n₂, b1₂, ⟨_, b2₂⟩, ls₂, b3₂, _⟩ := isDelta_is_some.1 hd2
  simp [b3₁, b3₂, Expr.constLevels!] at h2
  have ⟨_, stk₁⟩ := AppStack.build (e₁.mkAppList_getAppArgsList ▸ he₁)
  have ⟨_, stk₂⟩ := AppStack.build (e₂.mkAppList_getAppArgsList ▸ he₂)
  have .const (us' := ls₁) c1₁ c2₁ c3₁ := b3₁ ▸ stk₁.tr
  have .const (us' := ls₂) c1₂ c2₂ c3₂ := b3₂ ▸ stk₂.tr
  cases (c.trenv.find?_uniq b1₁ c1₁).1
  cases (c.trenv.find?_uniq b1₂ c1₂).1
  cases c1₁.symm.trans c1₂
  have := VEnv.IsDefEq.constDF c1₁
    (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2₁) (.of_mapM_ofLevel c2₂)
    ((List.mapM_eq_some.1 c2₁).length_eq.symm.trans c3₁)
    (Level.isEquivList_wf h2 c2₁ c2₂)
  refine (isDefEqArgs.WF ⟨_, stk₁.tr, _, stk₂.tr, _, this⟩ he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  exact .pure <| h ‹_›

theorem isNatZero_wf {c : VContext} (H : isNatZero e) (h : c.TrExprS e e') : e' = .natZero := by
  have h1 : c.TrExprS (.lit (.natVal 0)) e' := by
    simp [isNatZero] at H; obtain H|H := H
    · have := h.eqv H; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · split at H <;> [exact h; cases H]
  have := TrExprS.lit_has_type (l := .natVal 0) h1
  exact h1.unique (by trivial) (TrExprS.natLit c.hasPrimitives this 0).1

theorem isNatSuccOf?_wf {c : VContext} (H : isNatSuccOf? e = some e₁)
    (h : c.TrExprS e e') : ∃ x, c.TrExprS e₁ x ∧ e' = .app .natSucc x := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · rename_i n
    have := TrExprS.lit_has_type (l := .natVal (n+1)) h
    refine ⟨_, (TrExprS.natLit c.hasPrimitives this n).1, ?_⟩
    exact h.unique (by trivial) (TrExprS.natLit c.hasPrimitives this (n+1)).1
  · let .app a1 a2 a3 a4 := h
    let .const b1 b2 b3 := a3
    cases c.hasPrimitives.natSucc b1
    simp at b3; subst b3; simp at b2; subst b2
    exact ⟨_, a4, rfl⟩

theorem isDefEqOffset.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (isDefEqOffset e₁ e₂).WF c s fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqOffset; split
  · rename_i h; simp at h
    cases isNatZero_wf h.1 he₁; cases isNatZero_wf h.2 he₂
    exact .pure fun _ => .refl <| he₁.wf c.Ewf c.Δwf
  · split <;> [skip; exact .pure nofun]
    obtain ⟨_, a1, rfl⟩ := isNatSuccOf?_wf ‹_› he₁
    obtain ⟨_, b1, rfl⟩ := isNatSuccOf?_wf ‹_› he₂
    refine .toLBoolM <| (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    let ⟨_, de'⟩ := he₁.wf c.Ewf c.Δwf
    let ⟨_, _, c1, c2⟩ := de'.hasType.1.app_inv c.Ewf c.Δwf
    exact ⟨_, c1.appDF <| (h hb).of_l c.Ewf c.Δwf c2⟩

theorem lazyDeltaReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReduction.loop e₁ e₂ n).WF c s fun r _ => r.WF c e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.WF he₁ he₂).bind fun _ _ _ h => ?_; split
  · exact .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) (he₂.trExpr c.Ewf c.Δwf) fun hb =>
      h (by simpa using hb)
  suffices hF1 : ∀ {s}, (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' by
    refine .readThe ?_; split <;> [skip; exact hF1]
    refine (reduceNat.WF he₁).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF a1 he₂).bind fun _ _ _ h => ?_
      refine .pure <| .bool ⟨_, a1, a2⟩ (he₂.trExpr c.Ewf c.Δwf) fun hb => ?_
      exact a2.symm.trans c.Ewf c.Δwf (h hb)
    refine (reduceNat.WF he₂).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF he₁ a1).bind fun _ _ _ h => ?_
      refine .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) ⟨_, a1, a2⟩ fun hb => ?_
      exact (h hb).trans c.Ewf c.Δwf a2
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (lazyDeltaReductionStep.WF he₁ he₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» =>
    let ⟨_, ⟨_, a1, a2⟩, ⟨_, b1, b2⟩⟩ := h
    exact (ih a1 b1).mono fun _ _ _ h => h.defeq a2 b2
  | _ => exact .pure h

theorem tryStringLitExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansionCore e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure nofun]
  let .lit _ he₁ := he₁
  exact .toLBoolM <| isDefEqCore.WF he₁ he₂

theorem tryStringLitExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansion e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  refine (tryStringLitExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure h]
  exact (tryStringLitExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

/-- The translation of an application of a constant. -/
theorem _root_.Lean4Lean.TrExprS.appConst_inv {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} {I : Name} {ls : List Level} (H : TrExprS env Us Δ e e')
    (hI : e.getAppFn = .const I ls) :
    ∃ ci ls' as, e' = .appN (.const I ls') as ∧ env.constants I = some ci ∧
      ls.mapM (VLevel.ofLevel Us) = some ls' ∧ ls.length = ci.uvars := by
  rw [← Expr.mkAppRevList_getAppArgsRevList e, hI] at H
  obtain ⟨f', rs', rfl, hf, -⟩ := H.mkAppRevList_inv
  let .const h1 h2 h3 := hf
  exact ⟨_, _, _, rfl, h1, h2, h3⟩

/-- Any two terms of a type whose head is an inductive type of a block, with a single fieldless
constructor, no indices and no recursion, are definitionally equal. -/
theorem _root_.Lean4Lean.TypeChecker.VContext.unitLike (c : VContext) {tType : Expr} {tT' : VExpr} {I : Name} {lsI : List Level}
    (hT : c.TrExprS tType tT') (hI : tType.getAppFn = .const I lsI) {v : InductiveVal}
    (hci : c.env.find? I = some (.inductInfo v)) (hrec : v.isRec = false) {cn : Name}
    (hctors : v.ctors = [cn]) (hidx : v.numIndices = 0) {w : ConstructorVal}
    (hcci : c.env.find? cn = some (.ctorInfo w)) (hf : w.numFields = 0) {e₁' e₂' : VExpr}
    (h₁ : c.HasType e₁' tT') (h₂ : c.HasType e₂' tT') : c.IsDefEqU e₁' e₂' := by
  obtain ⟨ci', ls', as, rfl, hc', hls', hlen'⟩ := hT.appConst_inv hI
  have mapWF := c.trenv.map_wf
  obtain ⟨hname, hsafe, hlp, -⟩ := c.trenv.find?_uniq hci hc'
  rw [Kernel.Environment.find?, mapWF.find?'_eq_find?] at hci hcci
  obtain ⟨d, t, T, hs, ht, hTv, hlpd⟩ := c.trenv.inductInfo hci hsafe
  obtain ⟨hvn, -, -, hni, -, hvc, -, hvr, -⟩ := hTv
  have hnameI : v.name = I := hname
  rw [hnameI] at hs
  obtain ⟨c', hc'eq, hcn⟩ : ∃ c', T.ctors = [c'] ∧ c'.name = cn := by
    rw [hctors] at hvc
    match h : T.ctors, hvc with
    | [c'], hvc => exact ⟨c', rfl, by simpa using hvc.symm⟩
  have hi : T.indices = [] := List.eq_nil_of_length_eq_zero (hni.symm.trans hidx)
  have hrec' : d.isRec = false := hvr.symm.trans hrec
  obtain ⟨lp, hlp', -, hcs⟩ := c.trenv.blockConsts hs
  obtain ⟨w', hw', hwc⟩ := hcs t c' (VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc'eq]⟩)
  rw [hcn, hcci] at hw'; cases hw'
  obtain ⟨-, -, -, -, -, -, -, hwf, -⟩ := hwc
  have hfields : c'.fields = [] := List.eq_nil_of_length_eq_zero (hwf.symm.trans hf)
  have hlen : ls'.length = d.uvars := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls'), hlen', ← hlp]
    exact hlpd
  have hlsw := VLevel.WF.of_mapM_ofLevel hls'
  exact ⟨_, c.Ewf.unitLike c.Δwf.toCtx hs ht hc'eq hi hrec' hfields hlsw hlen h₁ h₂⟩

theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty₁ _ _ ⟨ty₁', _, _, a3, a4⟩ => ?_
  refine (whnf.WF a3).bind fun tType _ _ ⟨_, tT', b2, b3⟩ => ?_
  split <;> [rename_i I lsI hI; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i ctor _ _ _ _ _ _ _ _ _; exact .pure nofun]
  refine (M.WF.liftExcept envGet.WF).lift.bind fun cci _ _ hcci => ?_
  split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun ty₂ _ _ ⟨ty₂', _, _, d3, d4⟩ => ?_
  refine (isDefEqCore.WF b2 d3).mono fun b _ _ h hb => ?_
  exact c.unitLike b2 hI hci rfl rfl rfl hcci rfl (a4.defeqU_r c.Ewf c.Δwf b3.symm)
    (d4.defeqU_r c.Ewf c.Δwf (h hb).symm)

theorem lazyDeltaProjReduction.finish.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj n i e₁) e₁') (he₂ : c.TrExprS (.proj n i e₂) e₂') :
    (finish n i e₁ e₂).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  unfold finish
  refine (reduceProjCore.WF he₁).bind fun _ _ _ h1 => ?_; extract_lets F
  have hF {s} : (F ⟨⟩).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
    have .proj a1 a2 := he₁; have .proj b1 _ := he₂
    refine (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    exact a2.proj_congr c.Ewf c.Δwf.toCtx (h hb)
  split <;> [have ⟨a1, _, a2, a3⟩ := h1 _ rfl; exact .pureBind hF]
  refine (reduceProjCore.WF he₂).bind fun _ _ _ h2 => ?_
  split <;> [have ⟨b1, _, b2, b3⟩ := h2 _ rfl; exact .pureBind hF]
  exact (isDefEqCore.WF a2 b2).mono fun _ _ _ h hb =>
    a3.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf b3

theorem lazyDeltaProjReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj sn i e₁) e₁') (he₂ : c.TrExprS (.proj sn i e₂) e₂') :
    (loop sn i e₁ e₂ n).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
  refine (lazyDeltaReductionStep.WF a1 b1).bind fun _ _ _ h => ?_; split
  · have ⟨_, ⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, f1⟩ := a2.proj_congr c.Ewf c.Δwf.toCtx c2.symm
    have ⟨_, f2⟩ := b2.proj_congr c.Ewf c.Δwf.toCtx d2.symm
    refine (ih (.proj c1 ⟨_, f1.hasType.2⟩) (.proj d1 ⟨_, f2.hasType.2⟩)).mono
      fun _ _ _ h hb => ?_
    exact VEnv.IsDefEqU.trans c.Ewf c.Δwf.toCtx ⟨_, f1⟩ <|
      VEnv.IsDefEqU.trans c.Ewf c.Δwf.toCtx (h hb) ⟨_, f2.symm⟩
  · exact .pure fun _ => a2.proj_congr c.Ewf c.Δwf.toCtx h
  all_goals
    have ⟨⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, f1⟩ := a2.proj_congr c.Ewf c.Δwf.toCtx c2.symm
    have ⟨_, f2⟩ := b2.proj_congr c.Ewf c.Δwf.toCtx d2.symm
    refine (finish.WF (.proj c1 ⟨_, f1.hasType.2⟩) (.proj d1 ⟨_, f2.hasType.2⟩)).mono
      fun _ _ _ h hb => ?_
    exact VEnv.IsDefEqU.trans c.Ewf c.Δwf.toCtx ⟨_, f1⟩ <|
      VEnv.IsDefEqU.trans c.Ewf c.Δwf.toCtx (h hb) ⟨_, f2.symm⟩

theorem isDefEqCore'.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore' e₁ e₂) fun b _ => b = true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine .readThe ?_
  suffices ∀ {s}, RecM.WF c s (F1 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [rename_i h1; exact this]
    refine (whnf.WF he₁).bind fun _ _ _ ⟨_, _, a1, a2⟩ => ?_
    split <;> [rename_i h2; exact this]
    refine .pure fun _ => ?_
    simp [Expr.isConstOf] at h1 h2
    split at h1 <;> simp at h1; cases h1.2; split at h2 <;> simp at h2; cases h2
    let .const b1 b2 b3 := he₂
    let .const c1 c2 c3 := a1
    cases c.hasPrimitives.boolTrue b1
    cases c.hasPrimitives.boolTrue c1
    simp at b3 c3; subst b3 c3; simp at b2 c2; subst b2 c2
    exact a2.symm
  intro; unfold F1
  refine (whnfCore.WF he₁).bind fun _ _ _ ⟨_, e₁', a1, a2⟩ => ?_
  refine (whnfCore.WF he₂).bind fun _ _ _ ⟨_, e₂', b1, b2⟩ => ?_
  extract_lets F2
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    a2.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf b2
  suffices ∀ {s}, RecM.WF c s (F2 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [skip; exact this]
    refine (quickIsDefEq.WF a1 b1).bind fun _ _ _ h => ?_
    split <;> [skip; exact this]
    exact .pure fun hb => h (by simpa using hb)
  intro; unfold F2
  refine (isDefEqProofIrrel.WF a1 b1).bind fun _ _ _ h => ?_
  split
  · exact .pure fun hb => h (by simpa using hb)
  refine (lazyDeltaReduction.loop.WF a1 b1).readThe.bind fun _ _ _ h => ?_; split
  · cases h.1
  · exact .pure fun _ => h
  · exact .pure nofun
  have ⟨⟨e₁', c1, c4⟩, ⟨e₂', d1, d4⟩⟩ := h
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    c4.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d4
  extract_lets F3
  suffices ∀ {s}, RecM.WF c s (F3 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split
    · split <;> [rename_i h2; exact this]
      refine .pure fun _ => ?_
      simp at h2; cases h2.1
      have .const c1 c2 c3 := c1; have .const d1 d2 d3 := d1
      cases d1.symm.trans c1
      have := VEnv.IsDefEq.constDF c1
        (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2) (.of_mapM_ofLevel d2)
        ((List.mapM_eq_some.1 c2).length_eq.symm.trans c3)
        (Level.isEquivList_wf h2.2 c2 d2)
      exact this.toU
    · split <;> [rename_i h; exact this]
      simp at h; subst h
      exact .pure fun _ => c1.uniq c.Ewf (.refl c.Ewf c.Δwf) d1
    · split <;> [rename_i h2; exact this]; simp at h2; obtain ⟨rfl, rfl⟩ := h2
      refine (lazyDeltaProjReduction.loop.WF c1 d1).bind fun _ _ _ h => ?_
      split <;> [refine .pure fun _ => h ‹_›; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.WF c1).bind fun _ _ _ ⟨_, e₁'', c5, c6⟩ => ?_
  refine (whnfCore.WF d1).bind fun _ _ _ ⟨_, e₂'', d5, d6⟩ => ?_
  split
  · exact (isDefEqCore.WF c5 d5).mono fun _ _ _ h hb =>
      c6.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d6
  refine (isDefEqApp.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaStruct.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryStringLitExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine (isDefEqUnitLike.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  exact .pure nofun

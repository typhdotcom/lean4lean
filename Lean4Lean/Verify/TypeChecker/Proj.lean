import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Theory.Typing.ProjKernel
import Lean4Lean.Theory.Typing.Iota

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem _root_.Lean.Expr.leadingForalls_instantiateLevelParamsCore' {red : Bool}
    {F : Name → Level} (e : Expr) :
    (Expr.instantiateLevelParamsCore' red F e).leadingForalls = e.leadingForalls := by
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', Expr.leadingForalls]

theorem _root_.Lean.Expr.leadingForalls_instantiateLevelParams {e : Expr} {ps : List Name}
    {ls : List Level} : (e.instantiateLevelParams ps ls).leadingForalls = e.leadingForalls := by
  rw [Expr.instantiateLevelParams_eq, Expr.leadingForalls_instantiateLevelParamsCore']

theorem _root_.Lean.Expr.leadingForalls_instantiate1' (e a : Expr) (k : Nat) :
    e.leadingForalls ≤ (e.instantiate1' a k).leadingForalls := by
  induction e generalizing k with
  | forallE _ _ b _ _ ih =>
    have := ih (k + 1)
    simp [Expr.instantiate1', Expr.leadingForalls]; omega
  | _ => simp [Expr.leadingForalls]

theorem Closed.of_looseBVarRange_le : ∀ {e : Expr} {k j},
    Closed e k → e.looseBVarRange' ≤ j → Closed e j := by
  intro e
  induction e <;> intro k j hc hb <;>
    simp_all [Closed, Expr.looseBVarRange', Nat.max_le] <;> grind

/-- A body without loose bound variables, translated under a binder, does not mention it. -/
theorem TrExprS.skips_of_closed {env : VEnv} {Us : List Name} {Δ : VLCtx} {A : VExpr}
    {b : Expr} {B : VExpr} (henv : env.WF) (hΔ : VLCtx.WF env Us.length ((none, .vlam A) :: Δ))
    {a : FVarId} (ha : a ∉ Δ.fvars) (H : TrExprS env Us ((none, .vlam A) :: Δ) b B)
    (hb : b.looseBVarRange' = 0) : B.Skips 1 0 := by
  have hΔ' : VLCtx.WF env Us.length ((some (a, []), .vlam A) :: Δ) :=
    ⟨hΔ.1, by rintro _ _ ⟨⟩; exact ⟨ha, nofun⟩, hΔ.2.2⟩
  have hc : Closed b 0 := .of_looseBVarRange_le H.closed (by omega)
  have h1 := H.inst_fvar henv.ordered hΔ'
  rw [Expr.instantiate1'_eq_self (by simpa using hc.looseBVarRange_le)] at h1
  obtain ⟨B₀, h0⟩ := h1.weakFV'_inv henv (.skip_fvar _ _ .refl) (.refl henv hΔ') hc
    (by simpa using H.fvarsIn)
  have h2 := h0.weakFV henv.ordered (.skip_fvar (a, []) (.vlam A) .refl) hΔ'
  cases h2.unique (TrExprS.IsUnique.all _) h1
  exact .liftN

/-- A body without loose bound variables, translated under a binder, is the lift of its
translation outside it. -/
theorem TrExprS.lower_of_closed {env : VEnv} {Us : List Name} {Δ : VLCtx} {A : VExpr}
    {b : Expr} {B : VExpr} (henv : env.WF) (hΔ : VLCtx.WF env Us.length ((none, .vlam A) :: Δ))
    {a : FVarId} (ha : a ∉ Δ.fvars) (H : TrExprS env Us ((none, .vlam A) :: Δ) b B)
    (hb : b.looseBVarRange' = 0) : ∃ B₀, TrExprS env Us Δ b B₀ ∧ B = B₀.liftN 1 := by
  have hΔ' : VLCtx.WF env Us.length ((some (a, []), .vlam A) :: Δ) :=
    ⟨hΔ.1, by rintro _ _ ⟨⟩; exact ⟨ha, nofun⟩, hΔ.2.2⟩
  have hc : Closed b 0 := .of_looseBVarRange_le H.closed (by omega)
  have h1 := H.inst_fvar henv.ordered hΔ'
  rw [Expr.instantiate1'_eq_self (by simpa using hc.looseBVarRange_le)] at h1
  obtain ⟨B₀, h0⟩ := h1.weakFV'_inv henv (.skip_fvar _ _ .refl) (.refl henv hΔ') hc
    (by simpa using H.fvarsIn)
  have h2 := h0.weakFV henv.ordered (.skip_fvar (a, []) (.vlam A) .refl) hΔ'
  exact ⟨B₀, h0, h2.unique (TrExprS.IsUnique.all _) h1 ▸ rfl⟩

namespace TypeChecker.Inner

/-- The kernel's walk down a telescope `L` over `R`, which it instantiates with `vals`: after `i`
binders, the term it holds translates, up to universe levels, to the telescope's rest. -/
structure ProjWalk (c : VContext) (L : List VExpr) (R : VExpr) (vals : List VExpr) (i : Nat)
    (r : Expr) : Prop where
  tr : ∃ X, c.TrExprS r X ∧ VEnv.EqUpToLevels c.lparams.length
    ((VExpr.foralls (L.drop i) R).subst (VExpr.Subst.dflt.consList (vals.take i))) X
  arity : L.length - i ≤ r.leadingForalls

/-- One binder of the walk: the term is a pi, whose domain translates to the telescope's next entry
at the values so far. -/
theorem ProjWalk.step {c : VContext} {L : List VExpr} {R : VExpr} {vals : List VExpr} {i : Nat}
    {r : Expr} (H : ProjWalk c L R vals i r) (hi : i < L.length) :
    ∃ nm dom b bi A B, r = .forallE nm dom b bi ∧ c.TrExprS dom A ∧
      TrExprS c.venv c.lparams ((none, .vlam A) :: c.vlctx) b B ∧ c.IsType A ∧
      VEnv.EqUpToLevels c.lparams.length
        (L[i].subst (VExpr.Subst.dflt.consList (vals.take i))) A ∧
      VEnv.EqUpToLevels c.lparams.length ((VExpr.foralls (L.drop (i + 1)) R).subst
        (VExpr.Subst.dflt.consList (vals.take i)).lift) B ∧
      L.length - (i + 1) ≤ b.leadingForalls := by
  obtain ⟨⟨X, hX, hXe⟩, har⟩ := H
  rw [List.drop_eq_getElem_cons hi] at hXe
  cases r with
  | forallE nm dom b bi =>
    cases hX with | forallE hA _ hdom hb =>
    cases hXe with | forallE e1 e2 =>
    refine ⟨nm, dom, b, bi, _, _, rfl, hdom, hb, hA, e1, e2, ?_⟩
    simp [Expr.leadingForalls] at har; omega
  | _ => simp [Expr.leadingForalls] at har; omega

/-- Instantiating the binder with a value of its domain continues the walk. -/
theorem ProjWalk.inst {c : VContext} {L : List VExpr} {R : VExpr} {vals : List VExpr} {i : Nat}
    {b : Expr} {A B : VExpr}
    (hb : TrExprS c.venv c.lparams ((none, .vlam A) :: c.vlctx) b B)
    (hB : VEnv.EqUpToLevels c.lparams.length ((VExpr.foralls (L.drop (i + 1)) R).subst
        (VExpr.Subst.dflt.consList (vals.take i)).lift) B)
    (har : L.length - (i + 1) ≤ b.leadingForalls)
    {v : Expr} {v' : VExpr} (hv : c.TrExprS v v') (hvT : c.HasType v' A)
    (hval : vals[i]? = some v') : ProjWalk c L R vals (i + 1) (b.instantiate1 v) := by
  have hΓ := c.Δwf.toCtx
  have hlv := (hvT.levelWF (VEnv.CtxStrong.strong c.Ewf.ordered hΓ).levelWF).1
  refine ⟨⟨B.inst v', ?_, ?_⟩, ?_⟩
  · rw [Expr.instantiate1_eq]; exact hb.inst c.Ewf.ordered hvT hv
  · have := VEnv.EqUpToLevels.instN (k := 0) (VEnv.EqUpToLevels.of_levelWF hlv) hB
    rw [List.take_add_one, hval, Option.toList_some, VExpr.Subst.consList_concat,
      ← VExpr.inst_lift_cons]
    exact this
  · rw [Expr.instantiate1_eq]
    exact Nat.le_trans har (Expr.leadingForalls_instantiate1' _ _ _)

/-- A body that does not mention its binder continues the walk as it is. -/
theorem ProjWalk.skip {c : VContext} {s : VState} (wf : s.WF c) {L : List VExpr} {R : VExpr}
    {vals : List VExpr} {i : Nat} {A B : VExpr} {b : Expr}
    (hA : c.IsType A) (hb : TrExprS c.venv c.lparams ((none, .vlam A) :: c.vlctx) b B)
    (hB : VEnv.EqUpToLevels c.lparams.length ((VExpr.foralls (L.drop (i + 1)) R).subst
        (VExpr.Subst.dflt.consList (vals.take i)).lift) B)
    (har : L.length - (i + 1) ≤ b.leadingForalls) (hcl : b.looseBVarRange' = 0)
    {v' : VExpr} (hlv : v'.LevelWF c.lparams.length) (hval : vals[i]? = some v') :
    ProjWalk c L R vals (i + 1) b := by
  have hΔ : VLCtx.WF c.venv c.lparams.length ((none, .vlam A) :: c.vlctx) :=
    ⟨c.Δwf, nofun, let ⟨_, h⟩ := hA; ⟨_, h⟩⟩
  obtain ⟨B₀, hB₀, rfl⟩ := TrExprS.lower_of_closed c.Ewf hΔ
    (fun h => s.ngen.not_reserves_self (wf.ngen_wf _ h)) hb hcl
  refine ⟨⟨B₀, hB₀, ?_⟩, har⟩
  have := VEnv.EqUpToLevels.instN (k := 0) (VEnv.EqUpToLevels.of_levelWF hlv) hB
  rw [show (B₀.liftN 1).inst v' = B₀ from VExpr.inst_liftN _ _] at this
  rw [List.take_add_one, hval, Option.toList_some, VExpr.Subst.consList_concat,
    ← VExpr.inst_lift_cons]
  exact this

theorem inferProj.WF' {c : VContext} {s : VState} {e ety : Expr} {e' ety' : VExpr}
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ety')
    (hb : c.FVarsBelow e ety) :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ ty', c.TrTyping (.proj st i e) ty (.proj st i e') ty' := by
  have hΓ := c.Δwf.toCtx
  unfold inferProj
  refine (whnf.WF hty).bind fun type _ _ ⟨ht1, T₂, ht2, ht3⟩ => ?_
  simp only [Expr.withApp_eq]
  refine .getEnv ?_
  have hfail {α β : Type} {k : α → RecM β} {Q} {s} {f : LocalContext → Exception} :
      RecM.WF c s ((do let l ← getLCtx; throw (f l) : RecM α) >>= k) Q :=
    (RecM.WF.getLCtx (Q := fun _ _ => False) .throw).bind fun _ _ _ h => h.elim
  have hfail' {α : Type} {Q} {s} {f : LocalContext → Exception} :
      RecM.WF c s (do let l ← getLCtx; throw (f l) : RecM α) Q := RecM.WF.getLCtx .throw
  split <;> [rename_i I_name I_levels hhead; exact hfail']
  by_cases hst : (st != I_name) = true
  · rw [if_pos hst]; exact hfail
  rw [if_neg hst]
  refine (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i I_val; exact hfail']
  generalize hcn : I_val.ctors = cs
  rcases cs with _ | ⟨cn, _ | ⟨cn₂, tl⟩⟩
  · exact hfail'
  rotate_left
  · exact hfail'
  dsimp only
  by_cases hsize : (type.getAppArgs.size != I_val.numParams + I_val.numIndices) = true
  · rw [if_pos hsize]; exact hfail
  rw [if_neg hsize]
  refine (M.WF.liftExcept envGet.WF).lift.bind fun c_info _ _ hcinfo => ?_
  split <;> [rename_i c_val; exact hfail']
  by_cases hidx : i ≥ c_val.numFields
  · rw [if_pos hidx]; exact hfail
  rw [if_neg hidx]
  by_cases hlvl : ((ConstantInfo.ctorInfo c_val).levelParams.length != I_levels.length) = true
  · rw [if_pos hlvl]; exact hfail
  rw [if_neg hlvl]
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, Nat.not_le] at hst hsize hlvl hidx
  subst hst
  -- the structure's type
  have ht2' := ht2
  rw [← Expr.mkAppList_getAppArgsList type, hhead] at ht2'
  obtain ⟨fT, argsT', rfl, hfT, hargsT⟩ := ht2'.mkAppList_inv
  cases hfT with | @const _ _ lsT' _ _ hcT hlsT hlenT => ?_
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hci hcT
  have hci' := hci
  rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?] at hci'
  obtain ⟨d, t, T, hs, ht, hTv, -⟩ := c.trenv.inductInfo hci' hsafe
  obtain ⟨hTn, -, hnp, hni, -, hctors, -, -, -⟩ := hTv
  have hIT : st = T.name := (hname : I_val.name = st).symm.trans hTn
  subst hIT
  rw [hTn] at hs
  obtain ⟨c', hc'⟩ : ∃ c', T.ctors = [c'] := by
    rw [hcn] at hctors
    match h : T.ctors, hctors with
    | [c'], _ => exact ⟨c', rfl⟩
  have hcn' : cn = c'.name := by rw [hcn, hc'] at hctors; simpa using hctors
  subst hcn'
  have hjc : (t, c') ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc']⟩
  obtain ⟨lp, -, -, hCs⟩ := c.trenv.blockConsts hs
  obtain ⟨w, hw, hwc⟩ := hCs t c' hjc
  have hcinfo' := hcinfo
  rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?, hw] at hcinfo'
  obtain rfl : w = c_val := by simpa using hcinfo'
  obtain ⟨-, -, -, -, -, -, hwnp, hwnf, -, hwar⟩ := hwc
  obtain ⟨-, -, hwlen, hwty⟩ := c.trenv.find?_uniq hcinfo (c.Ewf.ctor_constant hs hjc)
  obtain ⟨-, hTconst⟩ := c.Ewf.type_constant hs ht
  cases hcT.symm.trans hTconst
  have hlsW : ∀ l ∈ lsT', l.WF c.lparams.length := .of_mapM_ofLevel hlsT
  have hlenT' : lsT'.length = d.uvars :=
    (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsT)).symm.trans hlenT
  have hx : c.HasType e' ((VExpr.const T.name lsT').appN argsT') := hasty.defeqU_r c.Ewf hΓ ht3.symm
  have hargsL : argsT'.length = d.params.length + T.indices.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargsT, ← Expr.getAppArgs_toList, Array.length_toList,
      hsize, hnp, hni]
  obtain ⟨As, Is, rfl, hA, hI⟩ : ∃ As Is, argsT' = As ++ Is ∧ As.length = d.params.length ∧
      Is.length = T.indices.length :=
    ⟨argsT'.take d.params.length, argsT'.drop d.params.length, (List.take_append_drop ..).symm,
      by simp [hargsL], by simp [hargsL]⟩
  -- the constructor's declared type, at the structure's levels
  obtain ⟨envT, ps, Ds, hTwf, hle, hP0, hcty, htele, hFW, hwithin⟩ :=
    c.Ewf.ctorShape hs ht (c := c') (by simp [hc'])
  obtain ⟨X₀, hX₀, -⟩ := hwty.instL c.Ewf (Δ := []) trivial hlsT hlvl
  have hX₀e := TrExprS.instL_eqUpTo hlsT hlvl hwty hX₀ .nil
  have hX₀c : c.TrExprS ((ConstantInfo.ctorInfo w).instantiateTypeLevelParams I_levels) X₀ := by
    have := hX₀.weakFV c.Ewf.ordered (.from_nil c.mlctx.noBV) c.Δwf
    rwa [(hX₀.wf c.Ewf.ordered (by exact trivial)).closedN c.Ewf.ordered trivial |>.liftN_eq
      (Nat.zero_le _)]
      at this
  -- the telescope the kernel walks down, and the values it instantiates it with
  have hpsl : ps.length = d.params.length := htele.length_eq
  have hDsl : Ds.length = c'.fields.length := hFW.length
  generalize hL : (ps ++ Ds).map (VExpr.instL lsT') = L
  generalize hR : (VExpr.appN (.const T.name (VLevel.params d.uvars))
    (VExpr.bvars d.params.length c'.fields.length ++ c'.indices)).instL lsT' = R
  generalize hvals : As ++ VExpr.projs T.name c'.fields.length e' = vals
  have hLl : L.length = d.params.length + c'.fields.length := by
    rw [← hL]; simp [hpsl, hDsl]
  have hCe : c'.type.instL lsT' = VExpr.foralls L R := by
    rw [hcty, ← hL, ← hR, VExpr.instL_foralls]
  have hcT := VEnv.HasType.const (Γ := []) (c.Ewf.ctor_constant hs hjc) hlsW (by rw [hlenT'])
  have hW0 : ProjWalk c L R vals 0 ((ConstantInfo.ctorInfo w).instantiateTypeLevelParams I_levels) := by
    refine ⟨⟨X₀, hX₀c, ?_⟩, ?_⟩
    · simp only [List.drop_zero, List.take_zero, VExpr.Subst.consList_nil]
      rw [← hCe, VExpr.closed_subst c.Ewf.ordered hcT]; exact hX₀e
    · simp only [ConstantInfo.instantiateTypeLevelParams, ConstantVal.instantiateTypeLevelParams,
        Expr.leadingForalls_instantiateLevelParams, hLl, Nat.sub_zero]
      show _ ≤ w.type.leadingForalls; omega
  -- a value typed at the telescope's entry is typed at the kernel's domain
  have htrans {v' Tref A : VExpr} (hT : c.HasType v' Tref)
      (hE : VEnv.EqUpToLevels c.lparams.length Tref A) : c.HasType v' A :=
    let ⟨_, hS⟩ := hT.isType c.Ewf.ordered hΓ
    hT.defeqU_r c.Ewf hΓ ⟨_, VEnv.IsDefEq.eqUpToLevels c.Ewf.ordered hΓ hS hE⟩
  have WA := c.Ewf.projArgs hΓ hs ht hlsW hlenT' hA hI hx
  rw [List.reverse_append, VExpr.Subst.consList_append] at WA
  have WP := VEnv.Ctx.SubstEq.dropList (by simp [hI]) (by simp [hI]) WA
  -- free variables: those of the structure and of its type's arguments
  have hfvArgs : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e → ∀ a ∈ type.getAppArgsList,
      FVarsIn P a := by
    intro P hP h a ha
    have := ht1 P hP (hb P hP h)
    rw [← Expr.mkAppList_getAppArgsList type, hhead, FVarsIn.mkAppList] at this
    exact this.2 a ha
  have hfv0 : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e →
      FVarsIn P ((ConstantInfo.ctorInfo w).instantiateTypeLevelParams I_levels) :=
    fun P _ _ => hX₀.fvarsIn.mono fun _ h => by simp [VLCtx.instL] at h
  -- the parameters
  rw [hnp]
  refine (RecM.WF.forIn_range (Inv := fun a r _ => ProjWalk c L R vals a r ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e → FVarsIn P r) ?_ ⟨hW0, hfv0⟩).bind
    fun r₁ _ _ ⟨hW1, hfv1⟩ => ?_
  · intro a r s' ha ⟨hWa, hfva⟩
    obtain ⟨nm, dom, b, bi, A, B, rfl, hdom, hbB, hAT, hAe, hBe, har⟩ := hWa.step (by omega)
    refine (whnf.forallE_eq rfl).bind fun x _ _ hx => ?_
    subst hx
    refine .pure ⟨fun b' hb' => ?_, nofun⟩
    cases hb'
    have haA : a < As.length := by omega
    have hga : type.getAppArgs[a]! = type.getAppArgsList[a]'(by
        rw [Lean4Lean.List.Forall₂.length_eq hargsT]; simp; omega) := by
      rw [getElem!_pos type.getAppArgs a (by rw [hsize, hnp, hni]; omega)]
      simp [Expr.getAppArgs_eq]
    have hv : c.TrExprS type.getAppArgs[a]! As[a] := by
      have hl : type.getAppArgsList[a]? = some type.getAppArgs[a]! := by
        rw [hga, List.getElem?_eq_getElem]
      obtain ⟨b', hb1, hb2⟩ := List.Forall₂.getElem?_l hargsT hl
      rw [List.getElem?_append_left haA, List.getElem?_eq_getElem haA] at hb1
      cases hb1; exact hb2
    have hval : vals[a]? = some As[a] := by
      rw [← hvals, List.getElem?_append_left haA, List.getElem?_eq_getElem haA]
    have hP : ps[a]? = some ps[a] := List.getElem?_eq_getElem (by omega)
    have hvT := VEnv.Ctx.SubstEq.getElem_teleDefEq c.Ewf hle hΓ htele hlsW WP hA a haA _ hP
    refine ⟨ProjWalk.inst hbB hBe har hv (htrans hvT ?_) hval, fun P hP h => ?_⟩
    · have hLa : L[a]'(by omega) = ps[a].instL lsT' := by
        subst hL
        rw [List.getElem_map, List.getElem_append_left (show a < ps.length by omega)]
      rw [hLa, ← hvals, List.take_append_of_le_length (by omega)] at hAe
      exact hAe
    · rw [Expr.instantiate1_eq]
      refine FVarsIn.instantiate1 (hfva P hP h).2 ?_
      rw [hga]; exact hfvArgs P hP h _ (List.getElem_mem _)
  -- the structure's sort
  refine (getSortLevel.WF ht2).bind fun u _ _ ⟨u', hu', huT⟩ => ?_
  have hlev : u' ≈ d.level.inst lsT' := by
    have WA' := c.Ewf.projArgs hΓ hs ht hlsW hlenT' hA hI hx
    have hty := (c.Ewf.recFacts hs hlsW hlenT').type ht
    have hty0 := hty.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
    rw [← VExpr.closed_subst c.Ewf.ordered hty .dflt] at hty0
    have hsort := VEnv.HasType.appN_substT (Δ := []) (as := As ++ Is) hty0 (by simp [hA, hI])
      (by simpa using WA')
    simp only [VExpr.subst] at hsort
    exact VEnv.IsDefEqU.sort_inv c.Ewf hΓ (huT.uniqU c.Ewf hΓ hsort)
  have hmp : (!u.isNeverZero) = false → (d.level.inst lsT').IsNeverZero := fun h ns => by
    rw [← congrFun hlev ns]; exact ofLevel_isNeverZero hu' (by simpa using h) ns
  generalize hmpb : (!u.isNeverZero) = mp at hmp ⊢
  -- the fields and the projections the kernel substitutes for them
  have him : i < c'.fields.length := by rw [← hwnf]; omega
  have hLn : ∀ j (h : j < c'.fields.length), L[d.params.length + j]'(by omega) =
      (Ds[j]'(by rw [hDsl]; exact h)).instL lsT' := by
    intro j h; subst hL
    rw [List.getElem_map, List.getElem_append_right (by omega)]
    simp [hpsl]
  have hvtake : ∀ j ≤ c'.fields.length,
      vals.take (d.params.length + j) = As ++ VExpr.projs T.name j e' := by
    intro j hj
    rw [← hvals, show d.params.length + j = As.length + j by omega, List.take_append,
      VExpr.projs, VExpr.projs, ← List.map_take, List.take_range,
      show min (As.length + j - As.length) c'.fields.length = j by omega, List.take_of_length_le
      (by omega)]
  -- what the theory's projection lemma is told about each earlier field
  let Qs (j : Nat) : Prop := ∀ i' (D : VExpr), j < i' → Ds[i']? = some D → D.Skips 1 (i' - 1 - j)
  let kdom (j : Nat) (Dj : VExpr) : VExpr :=
    (Dj.instL lsT').subst (VExpr.Subst.dflt.consList (As ++ VExpr.projs T.name j e'))
  let kprop (j : Nat) : Prop := ∀ Dj, Ds[j]? = some Dj → mp = true →
    c.HasType (kdom j Dj) (.sort .zero)
  have hkernel : ∀ k (hk : k < c'.fields.length), (∀ j < k, Qs j ∨ kprop j) → kprop k →
      c.HasType (.proj T.name k e') (kdom k (Ds[k]'(by rw [hDsl]; exact hk))) := by
    intro k hk hall hk'
    have hf : c'.fields[k]? = some c'.fields[k] := List.getElem?_eq_getElem hk
    obtain ⟨-, hdf, hproj⟩ := c.Ewf.projKernel hΓ hs ht hc' hTwf hle hP0 hFW hwithin hlsW hlenT'
      hA hI hx hmp (P := Qs) (fun j i' hq hji Di hDi => hq i' Di hji hDi) k _ _
      (List.getElem?_eq_getElem (by rw [hDsl]; exact hk)) hf fun j hj Dj hDj h hm => by
        rcases Nat.lt_or_ge j k with hjk | hjk
        · exact ((hall j hjk).resolve_left (h.resolve_left (by omega))) Dj hDj hm
        · obtain rfl : j = k := by omega
          exact hk' Dj hDj hm
    exact hproj.defeqU_r c.Ewf hΓ ⟨_, hdf.symm⟩
  -- the fields before the projected one
  refine (RecM.WF.forIn_range (Inv := fun a r _ => ProjWalk c L R vals (d.params.length + a) r ∧
      (∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e → FVarsIn P r) ∧
      ∀ j < a, Qs j ∨ kprop j) ?_ ⟨by simpa using hW1, hfv1, nofun⟩).bind
    fun r₂ _ _ ⟨hW2, hfv2, hall⟩ => ?_
  · intro a r s' ha ⟨hWa, hfva, halla⟩
    have hai : a < c'.fields.length := by omega
    obtain ⟨nm, dom, b, bi, A, B, rfl, hdom, hbB, hAT, hAe, hBe, har⟩ := hWa.step (by omega)
    rw [hLn a hai, hvtake a (by omega)] at hAe
    refine (whnf.forallE_eq rfl).bind fun x s₂ _ hx => ?_
    subst hx
    have hval : vals[d.params.length + a]? = some (.proj T.name a e') := by
      rw [← hvals, List.getElem?_append_right (by omega)]
      simp [VExpr.projs, hA, hai]
    have hfvb : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e → FVarsIn P b :=
      fun P hP h => (hfva P hP h).2
    have hDa : Ds[a]? = some (Ds[a]'(by rw [hDsl]; exact hai)) := List.getElem?_eq_getElem _
    dsimp only
    by_cases hlb : b.hasLooseBVars = true
    · rw [if_pos hlb]
      have hcont (hprop : kprop a) {s''} : RecM.WF c s''
          (pure (ForInStep.yield (b.instantiate1 (.proj T.name a e)))) fun r s' =>
            (∀ b', r = .yield b' → ProjWalk c L R vals (d.params.length + (a + 1)) b' ∧
              (∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e → FVarsIn P b') ∧
              ∀ j < a + 1, Qs j ∨ kprop j) ∧ ∀ b', r ≠ .done b' := by
        have hT := hkernel a hai halla hprop
        refine .pure ⟨fun b' h => ?_, nofun⟩
        cases h
        refine ⟨ProjWalk.inst hbB hBe har (.proj he ⟨_, hT⟩) (htrans hT hAe) hval,
          fun P hP h => ?_, fun j hj => ?_⟩
        · rw [Expr.instantiate1_eq]; exact FVarsIn.instantiate1 (hfvb P hP h) h
        · rcases Nat.lt_or_ge j a with hja | hja
          · exact halla j hja
          · obtain rfl : j = a := by omega
            exact .inr hprop
      by_cases hm : mp = true
      · rw [if_pos hm]
        refine (isProp.WF hdom).bind fun bp _ _ hbp => ?_
        by_cases hbp' : (!bp) = true
        · rw [if_pos hbp']; exact hfail
        rw [if_neg hbp']
        refine hcont fun Dj hDj _ => ?_
        cases hDa.symm.trans hDj
        have hA0 := hbp (by simpa using hbp')
        exact (VEnv.IsDefEq.eqUpToLevels c.Ewf.ordered hΓ hA0 hAe.symm).hasType.2
      · rw [if_neg hm]
        exact hcont fun _ _ h => absurd h hm
    · rw [if_neg hlb]
      have hcl : b.looseBVarRange' = 0 := by simpa [Expr.hasLooseBVars] using hlb
      refine .stateWF fun wf => .pure ⟨fun b' h => ?_, nofun⟩
      cases h
      have hlv : (VExpr.proj T.name a e').LevelWF c.lparams.length :=
        (hasty.levelWF (VEnv.CtxStrong.strong c.Ewf.ordered hΓ).levelWF).1
      refine ⟨ProjWalk.skip wf hAT hbB hBe har hcl hlv hval, hfvb, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j a with hja | hja
      · exact halla j hja
      obtain rfl : j = a := by omega
      refine .inl fun i' D hji hD => ?_
      have hΔ : VLCtx.WF c.venv c.lparams.length ((none, .vlam A) :: c.vlctx) :=
        ⟨c.Δwf, nofun, let ⟨_, h⟩ := hAT; ⟨_, h⟩⟩
      obtain ⟨B₀, -, rfl⟩ := TrExprS.lower_of_closed c.Ewf hΔ
        (fun h => s₂.ngen.not_reserves_self (wf.ngen_wf _ h)) hbB hcl
      have h1 := (hBe.skips (n := 1) (k := 0)).2 .liftN
      have h2 := VExpr.skips_foralls _ (VExpr.skips_of_subst_lift h1) (i' - j - 1) (D.instL lsT') (by
        have hi' : i' < c'.fields.length := by rw [← hDsl]; exact (List.getElem?_eq_some_iff.1 hD).1
        rw [List.getElem?_drop, show d.params.length + j + 1 + (i' - j - 1) = d.params.length + i'
          by omega, List.getElem?_eq_getElem (by omega), hLn i' hi']
        congr 2; exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hD))
      rw [VExpr.skips_instL] at h2
      simpa [show i' - 1 - j = i' - j - 1 by omega] using h2
  -- the projected field
  obtain ⟨nm, dom, b, bi, A, B, rfl, hdom, -, -, hAe, -, -⟩ := hW2.step (by omega)
  rw [hLn i him, hvtake i (Nat.le_of_lt him)] at hAe
  refine (whnf.forallE_eq rfl).bind fun x _ _ hx => ?_
  subst hx
  have hDi : Ds[i]? = some (Ds[i]'(by rw [hDsl]; exact him)) := List.getElem?_eq_getElem _
  have hres (hprop : kprop i) {s''} : RecM.WF c s'' (pure dom) fun ty _ =>
      ∃ ty', c.TrTyping (.proj T.name i e) ty (.proj T.name i e') ty' := by
    have hT := hkernel i him hall hprop
    exact .pure ⟨A, fun P hP h => (hfv2 P hP h).1, .proj he ⟨_, hT⟩, hdom, htrans hT hAe⟩
  dsimp only
  by_cases hm : mp = true
  · rw [if_pos hm]
    refine (isProp.WF hdom).bind fun bp _ _ hbp => ?_
    by_cases hbp' : (!bp) = true
    · rw [if_pos hbp']; exact hfail
    rw [if_neg hbp']
    refine hres fun Dj hDj _ => ?_
    cases hDi.symm.trans hDj
    exact (VEnv.IsDefEq.eqUpToLevels c.Ewf.ordered hΓ (hbp (by simpa using hbp'))
      hAe.symm).hasType.2
  · rw [if_neg hm]
    exact hres fun _ _ h => absurd h hm

end TypeChecker.Inner

end Lean4Lean

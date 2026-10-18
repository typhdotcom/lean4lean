import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Theory.Typing.Iota

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem _root_.Lean.Expr.isAppOfArity_three {e : Expr} {n : Name}
    (h : e.isAppOfArity n 3 = true) : ∃ ls x y z, e = mkApp3 (.const n ls) x y z := by
  cases e <;> simp [Expr.isAppOfArity] at h
  rename_i f z; cases f <;> simp [Expr.isAppOfArity] at h
  rename_i f y; cases f <;> simp [Expr.isAppOfArity] at h
  rename_i f x; cases f <;> simp [Expr.isAppOfArity] at h
  subst h; exact ⟨_, _, _, _, rfl⟩

/-- An application's translation is the head's applied to the arguments', given that the result
is well formed. -/
theorem TrExprS.mkAppList {env : VEnv} {Us Δ} (henv : VEnv.Ordered env)
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    ∀ {as : List Expr} {xs : List VExpr} {f f'},
    TrExprS env Us Δ f f' → as.Forall₂ (TrExprS env Us Δ) xs →
    VExpr.WF env Us.length Δ.toCtx (f'.appN xs) →
    TrExprS env Us Δ (f.mkAppList as) (f'.appN xs)
  | [], _, _, _, hf, h, _ => by cases h; exact hf
  | a :: _, x :: xs, f, f', hf, .cons hx hxs, hwf =>
    have ⟨_, _, hfT, hxT⟩ := (VExpr.WF.appN_inv (vs := xs) henv hΔ hwf).app_inv henv hΔ
    TrExprS.mkAppList henv hΔ (f := f.app a) (f' := f'.app x) (.app hfT hxT hf hx) hxs hwf

theorem quotReduceRec.WF {c : VContext} {s : VState} (he : c.TrExprS e e')
    (hq : c.env.quotInit = true) :
    RecM.WF c s (quotReduceRec e whnf isDefEq) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hΓ := c.Δwf.toCtx
  have hQ : TrEnv' c.safety c.env.constants true c.venv := hq ▸ c.trenv
  obtain ⟨-, hmk, hlift, hind, hdf⟩ := hQ.quotReady
  unfold quotReduceRec
  split <;> [rename_i fn ls hfn; exact .pure nofun]
  lift_lets; intro args jp cont
  have he0 := he
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at he0
  obtain ⟨f', as', he', hf', hargs⟩ := he0.mkAppList_inv
  cases hf' with | const hcf hls' hlen' => ?_
  rename_i ci ls'
  have hargsL : args.toList = e.getAppArgsList := Expr.getAppArgs_toList
  have hlenA : as'.length = args.size := by
    rw [← Array.length_toList, hargsL, Lean4Lean.List.Forall₂.length_eq hargs]
  have harg : ∀ i (h : i < args.size), c.TrExprS args[i] (as'[i]'(hlenA ▸ h)) := by
    intro i h
    have hl : e.getAppArgsList[i]? = some args[i] := by
      rw [← hargsL, Array.getElem?_toList]; simp [h]
    obtain ⟨b, hb1, hb2⟩ := List.Forall₂.getElem?_l hargs hl
    rw [List.getElem?_eq_getElem (hlenA ▸ h)] at hb1; cases hb1; exact hb2
  have hcont : ∀ mkPos argPos, 2 ≤ mkPos → argPos < mkPos → (∀ (pre : List VExpr) (q' : VExpr) (lsm : List VLevel)
      (x' y' z' α r g : VExpr), pre.length = mkPos → pre[0]? = some α → pre[1]? = some r →
      pre[argPos]? = some g →
      VExpr.WF c.venv c.lparams.length c.vlctx.toCtx (.appN (.const fn ls') (pre ++ [q'])) →
      c.IsDefEqU q' (.appN (.const ``Quot.mk lsm) [x', y', z']) → c.IsDefEqU x' α →
      c.IsDefEqU y' r →
      c.IsDefEqU (.appN (.const fn ls') (pre ++ [q'])) (.app g z')) →
      RecM.WF c s (cont mkPos argPos) fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    intro mkPos argPos h2 hap hsem
    simp only [cont]
    split <;> [rename_i hpos; exact .pure nofun]
    refine (whnf.WF (harg mkPos hpos)).bind fun mk _ _ ⟨hmk1, m₂, hmk2, hmk3⟩ => ?_
    split <;> [exact .pure nofun; rename_i hmkA]
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hmkA
    obtain ⟨lsm, x, y, z, rfl⟩ := Expr.isAppOfArity_three hmkA
    simp only [Expr.appFn!, Expr.appArg!]
    obtain ⟨fm, xs, rfl, hfm, hxs⟩ := TrExprS.mkAppList_inv
      (show c.TrExprS (Expr.mkAppList (.const ``Quot.mk lsm) [x, y, z]) m₂ from hmk2)
    obtain ⟨x', y', z', rfl, hxx, hyy, hzz⟩ : ∃ x' y' z', xs = [x', y', z'] ∧ c.TrExprS x x' ∧
        c.TrExprS y y' ∧ c.TrExprS z z' := by
      match xs, hxs with
      | [x', y', z'], .cons h1 (.cons h2 (.cons h3 .nil)) => exact ⟨x', y', z', rfl, h1, h2, h3⟩
    cases hfm with | const hcm hlsm hlenm => ?_
    rename_i lsm'
    have hpos0 : 0 < args.size := by omega
    have hpos1 : 1 < args.size := by omega
    have hposA : argPos < args.size := by omega
    rw [getElem!_pos args 0 hpos0, getElem!_pos args 1 hpos1, getElem!_pos args argPos hposA]
    refine (isDefEq.WF hxx (harg 0 hpos0)).bind fun _ _ _ hb => ?_
    split <;> [rename_i hb'; exact .pure nofun]
    refine (isDefEq.WF hyy (harg 1 hpos1)).bind fun _ s' _ hb₂ => ?_
    split <;> [rename_i hb₂'; exact .pure nofun]
    -- the eliminator applied up to the quotient argument
    have hlA : mkPos < as'.length := hlenA ▸ hpos
    have has' : as' = as'.take mkPos ++ as'[mkPos] :: as'.drop (mkPos + 1) := by
      rw [List.getElem_cons_drop, List.take_append_drop]
    have hwf0 : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
        (.appN (.const fn ls') (as'.take mkPos ++ [as'[mkPos]])) := by
      have := he.wf c.Ewf c.Δwf
      rw [he', has', show as'.take mkPos ++ as'[mkPos] :: as'.drop (mkPos + 1) =
        (as'.take mkPos ++ [as'[mkPos]]) ++ as'.drop (mkPos + 1) by simp] at this
      exact VExpr.appN_wf_prefix c.Ewf.ordered hΓ this
    have hS := hsem (as'.take mkPos) as'[mkPos] lsm' x' y' z' (as'[0]'(by omega))
      (as'[1]'(by omega)) (as'[argPos]'(by omega)) (by simp; omega)
      (by simp [List.getElem?_take]; omega) (by simp [List.getElem?_take]; omega)
      (by simp [List.getElem?_take]; omega) hwf0 hmk3.symm (hb hb') (hb₂ hb₂')
    obtain ⟨_, hS'⟩ := hS
    obtain ⟨_, _, hgT, hzT⟩ := hS'.hasType.2.app_inv c.Ewf.ordered hΓ
    have hr : c.TrExpr (args[argPos].app z) (.appN (.const fn ls') (as'.take mkPos ++ [as'[mkPos]])) :=
      ⟨_, .app hgT hzT (harg argPos hposA) hzz, ⟨_, hS'.symm⟩⟩
    have hT : as'.take mkPos ++ [as'[mkPos]] = as'.take (mkPos + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlA]; rfl
    rw [hT] at hr
    have hE0 : c.TrExprS ((Expr.const fn ls).mkAppList (e.getAppArgsList.take (mkPos + 1)))
        (.appN (.const fn ls') (as'.take (mkPos + 1))) := by
      refine TrExprS.mkAppList c.Ewf.ordered hΓ (.const hcf hls' hlen') ?_ (hT ▸ hwf0)
      refine List.forall₂_of_getElem? (by simp [Lean4Lean.List.Forall₂.length_eq hargs])
        fun j a b h1 h2 => ?_
      rw [List.getElem?_take] at h1 h2
      split at h1 <;> [skip; cases h1]
      rw [if_pos ‹_›] at h2
      obtain ⟨b', hb1, hb2⟩ := List.Forall₂.getElem?_l hargs h1
      cases hb1.symm.trans h2; exact hb2
    have he1 : c.TrExprS (((Expr.const fn ls).mkAppList (e.getAppArgsList.take (mkPos + 1))).mkAppList
        (e.getAppArgsList.drop (mkPos + 1))) e' := by
      rw [← Expr.mkAppList_append, List.take_append_drop, ← hfn, Expr.mkAppList_getAppArgsList]
      exact he
    have hR := TrExpr.rebuild_mkAppList c.Ewf c.Δwf hE0 he1 hr
    have hfin : ∀ L, L = e.getAppArgsList.drop (mkPos + 1) → RecM.WF c s'
        (jp () ((args[argPos].app z).mkAppList L)) fun oe _ =>
          ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
      rintro L rfl
      refine .pure ?_; rintro _ ⟨⟩
      refine ⟨fun P hP hfv => ?_, hR⟩
      rw [← Expr.mkAppList_getAppArgsList e, hfn, FVarsIn.mkAppList] at hfv
      have hmem : ∀ i (h : i < args.size), args[i] ∈ e.getAppArgsList := fun i h => by
        rw [← hargsL]; exact Array.getElem_mem_toList h
      have hz : FVarsIn P z := by
        have := hmk1 P hP (hfv.2 _ (hmem mkPos hpos))
        simp only [FVarsIn] at this; exact this.2
      rw [FVarsIn.mkAppList]
      exact ⟨⟨hfv.2 _ (hmem argPos hposA), hz⟩, fun a ha => hfv.2 a (List.mem_of_mem_drop ha)⟩
    split
    · rw [Expr.mkAppRange_eq (l₁ := e.getAppArgsList.take (mkPos + 1))
        (l₂ := e.getAppArgsList.drop (mkPos + 1)) (l₃ := []) (by simp [hargsL])
        (by simp [← hargsL]; omega) (by simp [← hargsL])]
      exact hfin _ rfl
    · have : e.getAppArgsList.drop (mkPos + 1) = [] := by
        simp [← hargsL]; omega
      exact hfin [] this.symm
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    refine hcont 5 3 (by omega) (by omega) fun pre q' lsm x' y' z' α r g hlen h0 h1 hg hwf hq hx hy => ?_
    match pre, hlen with
    | [α₀, r₀, β, f, h], _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 hg
      subst h0 h1 hg
      exact VEnv.WF.quotLift c.Ewf hΓ hlift hmk hdf hwf hq hx hy
  split
  · rename_i h; simp only [beq_iff_eq] at h; subst h
    refine hcont 4 3 (by omega) (by omega) fun pre q' lsm x' y' z' α r g hlen h0 h1 hg hwf hq hx hy => ?_
    match pre, hlen with
    | [α₀, r₀, β, p], _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 hg
      subst h0 h1 hg
      exact VEnv.WF.quotInd c.Ewf hΓ hind hmk hwf hq hx hy
  exact .pure nofun

theorem toCtorWhenK.WF {c : VContext} {s : VState} {rval : RecursorVal} (hk : rval.k = true)
    {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (hs : c.venv.inducts T.name = some (d, t)) (ht : d.types[t]? = some T) (hK : d.IsKTarget)
    (hmi : rval.getMajorInduct = T.name) (hnp : rval.numParams = d.params.length)
    (he : c.TrExprS e e') :
    RecM.WF c s (toCtorWhenK c.env whnf inferType isDefEq rval e) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hΓ := c.Δwf.toCtx
  have hid {s} : RecM.WF c s (pure e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
    .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  unfold toCtorWhenK
  split <;> [skip; simp_all]
  refine (inferType.WF he).bind fun ty _ _ ⟨ty', hty1, _, hty2, hty3⟩ => ?_
  refine (whnf.WF hty2).bind fun appType _ _ ⟨hat1, A₂, hat2, hat3⟩ => ?_
  split <;> [rename_i appTypeI lsA hhead; exact hid]
  split <;> [exact hid; rename_i hI]
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, hmi] at hI; subst hI
  have hA₂ : c.HasType e' A₂ := hty3.defeqU_r c.Ewf hΓ (hat3.symm)
  have hat2' := hat2
  rw [← Expr.mkAppList_getAppArgsList appType, hhead] at hat2'
  obtain ⟨fA, argsA', rfl, hfA, hargsA⟩ := hat2'.mkAppList_inv
  cases hfA with | const hcA hlsA hlenA => ?_
  rename_i ciA lsA'
  obtain ⟨hz, T0, c0, htypes, -, hctors, hfields⟩ := hK
  obtain rfl : T = T0 := by
    rw [htypes] at ht
    match t, ht with | 0, ht => simpa using ht.symm
  obtain ⟨hlsW, hlenL, hlenArgs, hcT, hirr⟩ := c.Ewf.kTarget hΓ hs ht hz hctors hfields hA₂
  -- the constructor at the parameters of the major premise's type
  have hjc : (t, c0) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hctors]⟩
  have hlenArgs' : appType.getAppArgsList.length = d.params.length + T.indices.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hargsA, hlenArgs]
  have hN : c.TrExprS ((Expr.const c0.name lsA).mkAppList (appType.getAppArgsList.take d.params.length))
      (.appN (.const c0.name lsA') (argsA'.take d.params.length)) := by
    refine TrExprS.mkAppList c.Ewf.ordered hΓ
      (.const (c.Ewf.ctor_constant hs hjc) hlsA (hlenA.trans ?_)) ?_ ⟨_, hcT⟩
    · obtain ⟨-, -, -, -, -, -, T', hT', hname⟩ := c.Ewf.inducts hs
      cases ht.symm.trans hT'
      obtain ⟨env₀, envT, -, -, hT, hle, -⟩ := c.Ewf.inducts hs
      cases hcA.symm.trans (hle.constants (VEnv.addConstList_constants_of_mem hT
        (List.mem_map.2 ⟨T, List.mem_of_getElem? ht, rfl⟩)))
      rfl
    · refine List.forall₂_of_getElem? (by simp [Lean4Lean.List.Forall₂.length_eq hargsA])
        fun j a b h1 h2 => ?_
      rw [List.getElem?_take] at h1 h2
      split at h1 <;> [skip; cases h1]
      rw [if_pos ‹_›] at h2
      obtain ⟨b', hb1, hb2⟩ := List.Forall₂.getElem?_l hargsA h1
      cases hb1.symm.trans h2; exact hb2
  have hfv : c.FVarsBelow e ((Expr.const c0.name lsA).mkAppList
      (appType.getAppArgsList.take d.params.length)) := by
    intro P hP h
    have := hat1 P hP (hty1 P hP h)
    rw [← Expr.mkAppList_getAppArgsList appType, hhead, FVarsIn.mkAppList] at this
    rw [FVarsIn.mkAppList]
    exact ⟨this.1, fun a ha => this.2 a (List.mem_of_mem_take ha)⟩
  -- `mkNullaryCtor` builds it
  obtain ⟨lp, -, hTs, -⟩ := c.trenv.blockConsts hs
  obtain ⟨v, hv, hTv⟩ := hTs t T ht
  have hfind : c.env.find? T.name = some (.inductInfo v) := by
    rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?]; exact hv
  have hvc : v.ctors = [c0.name] := by rw [hTv.2.2.2.2.2.1, hctors]; rfl
  extract_lets jp
  have hjp : ∀ s, RecM.WF c s (jp ()) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    intro s
    simp only [jp, mkNullaryCtor, Expr.withApp_eq, hhead, getFirstCtor, hfind, hvc,
      List.head?_cons, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [Expr.mkAppRange_eq (args := appType.getAppArgs) (i := 0) (l₁ := [])
      (l₂ := appType.getAppArgsList.take d.params.length)
      (l₃ := appType.getAppArgsList.drop d.params.length) (by simp [Expr.getAppArgs_toList])
      rfl (by simp [hnp, hlenArgs'])]
    refine (inferType.WF hN).bind fun tyN _ _ ⟨tyN', _, _, htyN2, htyN3⟩ => ?_
    refine (isDefEq.WF hat2 htyN2).bind fun b _ _ hb => ?_
    split <;> [rename_i hb'; exact hid]
    refine .pure ⟨hfv, _, hN, ?_⟩
    exact ⟨_, (hirr _ (htyN3.defeqU_r c.Ewf hΓ (hb hb').symm)).symm⟩
  split
  · refine (RecM.WF.forIn'_range (Inv := fun _ (r : Option Expr × Unit) _ =>
      ∀ x, r.1 = some x → x = e) (Done := fun (r : Option Expr × Unit) _ =>
      ∀ x, r.1 = some x → x = e) ?_ (by simp) fun _ _ h => h).bind fun r _ _ hr => ?_
    · intro i h b s _; split
      · exact .pure ⟨nofun, fun b' h => by cases h; simp⟩
      · exact .pure ⟨fun b' h => by cases h; simp, nofun⟩
    · dsimp only; split
      · rename_i x hx; cases hr x hx; exact hid
      · exact hjp _
  · exact hjp _

theorem _root_.Lean.Expr.forIn_app_proj (I : Name) (e : Expr) (l : List Nat) (r : Expr) :
    (forIn (m := Id) l r fun i r => pure (ForInStep.yield (r.app (.proj I i e)))) =
      r.mkAppList (l.map (.proj I · e)) := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons]; exact ih _

theorem toCtorWhenStruct.WF {c : VContext} {s : VState} {I : Name} (he : c.TrExprS e e') :
    RecM.WF c s (toCtorWhenStruct c.env whnf inferType I e) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hΓ := c.Δwf.toCtx
  have hid {s} : RecM.WF c s (pure e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
    .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  unfold toCtorWhenStruct
  split; · exact hid
  rename_i hns
  refine (inferType.WF he).bind fun ty _ _ ⟨ty', hty1, _, hty2, hty3⟩ => ?_
  refine (whnf.WF hty2).bind fun eType _ _ ⟨het1, E₂, het2, het3⟩ => ?_
  split; · exact hid
  rename_i hI
  refine (inferType.WF het2).bind fun tyT _ _ ⟨tyT', _, _, htt2, htt3⟩ => ?_
  refine (whnf.WF htt2).bind fun srt _ _ ⟨_, S₂, hs2, hs3⟩ => ?_
  split <;> [rename_i u; exact hid]
  split <;> [rename_i hnz; exact hid]
  -- the structure
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hI
  obtain ⟨lsE, hhead⟩ : ∃ lsE, eType.getAppFn = .const I lsE := by
    revert hI; cases eType.getAppFn <;> simp [Expr.isConstOf]
  have het2' := het2
  rw [← Expr.mkAppList_getAppArgsList eType, hhead] at het2'
  obtain ⟨fE, argsE', rfl, hfE, hargsE⟩ := het2'.mkAppList_inv
  cases hfE with | @const _ _ lsE' _ _ hcE hlsE hlenE => ?_
  have hstruct : c.env.isNonRecStructure I = true := by
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hns
    simpa using hns.1
  obtain ⟨v, hv, hrec, hni, cn, hcn⟩ : ∃ v, c.env.find? I = some (.inductInfo v) ∧
      v.isRec = false ∧ v.numIndices = 0 ∧ ∃ cn, v.ctors = [cn] := by
    unfold Kernel.Environment.isNonRecStructure at hstruct
    split at hstruct <;> [rename_i h; cases hstruct]
    exact ⟨_, h, rfl, rfl, _, rfl⟩
  have hvfind := hv
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hv hcE
  rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?] at hv
  obtain ⟨d, t, T, hs, ht, hTv, -⟩ := c.trenv.inductInfo hv hsafe
  obtain ⟨hTn, -, -, hnidx, -, hctors, -, hrecd, -⟩ := hTv
  have hIT : I = T.name := hname.symm.trans hTn
  subst hIT
  rw [hTn] at hs
  have hi : T.indices = [] := List.eq_nil_of_length_eq_zero (hnidx.symm.trans hni)
  obtain ⟨c', hc', hcn'⟩ : ∃ c', T.ctors = [c'] ∧ cn = c'.name := by
    rw [hcn] at hctors
    match h : T.ctors, hctors with
    | [c'], h' => exact ⟨c', rfl, by simpa using h'⟩
  subst hcn'
  have hdrec : d.isRec = false := hrecd ▸ hrec
  obtain ⟨-, hconst⟩ := c.Ewf.type_constant hs ht
  cases hcE.symm.trans hconst
  have hlsW : ∀ l ∈ lsE', l.WF c.lparams.length := .of_mapM_ofLevel hlsE
  have hlenE' : lsE'.length = d.uvars := (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlsE)).symm.trans hlenE
  -- the term's type and its sort
  have hx : c.HasType e' (.appN (.const T.name lsE') argsE') := hty3.defeqU_r c.Ewf hΓ het3.symm
  have hF := c.Ewf.recFacts hs hlsW hlenE'
  have hty := hF.type ht
  rw [hi, List.map_nil, List.append_nil] at hty
  have hty0 := hty.weak0 c.Ewf.ordered (Γ := c.vlctx.toCtx)
  rw [← VExpr.closed_subst c.Ewf.ordered hty .dflt] at hty0
  have ⟨_, hS⟩ := hx.isType c.Ewf.ordered hΓ
  have hA : argsE'.length = d.params.length := by
    simpa using VEnv.HasType.appN_sort_length c.Ewf hΓ hty0 hS
  have WP := c.Ewf.projArgs hΓ hs ht hlsW hlenE' (I := []) hA (by simp [hi]) (by simpa using hx)
  simp only [List.append_nil, hi, List.map_nil] at WP
  have hsort := VEnv.HasType.appN_substT (Δ := []) (as := argsE') hty0 (by simp [hA])
    (by simpa using WP)
  simp only [VExpr.subst] at hsort
  cases hs2 with | sort hu' => ?_
  rename_i u'
  have hlev : u' ≈ d.level.inst lsE' := VEnv.IsDefEqU.sort_inv c.Ewf hΓ
    ((htt3.defeqU_r c.Ewf hΓ hs3.symm).uniqU c.Ewf hΓ hsort)
  have hnzV : (d.level.inst lsE').IsNeverZero := fun ns => by
    rw [← congrFun hlev ns]; exact ofLevel_isNeverZero hu' (by simpa using hnz) ns
  obtain ⟨hPW, hη⟩ := c.Ewf.structEtaProjs hΓ hs ht hc' hi hdrec hlsW hlenE' hnzV hA hx
  -- `expandEtaStruct` builds the constructor application
  have hjc : (t, c') ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc']⟩
  obtain ⟨lp, -, -, hCs⟩ := c.trenv.blockConsts hs
  obtain ⟨w, hw, hwc⟩ := hCs t c' hjc
  have hwfind : c.env.find? c'.name = some (.ctorInfo w) := by
    rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?]; exact hw
  obtain ⟨-, -, -, -, -, -, hwnp, hwnf, -⟩ := hwc
  have hlenL : eType.getAppArgsList.length = d.params.length := by
    rw [Lean4Lean.List.Forall₂.length_eq hargsE, hA]
  have hexp : expandEtaStruct c.env eType e = ((Expr.const c'.name lsE).mkAppList
      eType.getAppArgsList).mkAppList ((List.range c'.fields.length).map (.proj T.name · e)) := by
    simp only [expandEtaStruct, Expr.withApp_eq, hhead, getFirstCtor, hvfind, hcn,
      List.head?_cons, hwfind, Id.run,
      Std.Legacy.Range.forIn_eq_forIn_range', Expr.forIn_app_proj]
    rw [Expr.mkAppRange_eq (args := eType.getAppArgs) (i := 0) (l₁ := [])
      (l₂ := eType.getAppArgsList) (l₃ := []) (by simp [Expr.getAppArgs_toList]) rfl
      (by simp [hwnp, hlenL])]
    simp only [Std.Legacy.Range.size, hwnf, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.range_eq_range', bind_pure]
  rw [hexp]
  refine .pure ⟨fun P hP hfv => ?_, ⟨_, ?_, ⟨_, hη.symm⟩⟩⟩
  · have h1 := het1 P hP (hty1 P hP hfv)
    rw [← Expr.mkAppList_getAppArgsList eType, hhead, FVarsIn.mkAppList] at h1
    rw [FVarsIn.mkAppList, FVarsIn.mkAppList]
    refine ⟨⟨h1.1, h1.2⟩, fun a ha => ?_⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact hfv
  · rw [← Expr.mkAppList_append]
    refine TrExprS.mkAppList c.Ewf.ordered hΓ (.const (c.Ewf.ctor_constant hs hjc) hlsE hlenE)
      (forall₂_append hargsE ?_) ⟨_, hη.hasType.2⟩
    refine List.forall₂_of_getElem? (by simp [VExpr.projs]) fun j a b h1 h2 => ?_
    obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hj2, rfl⟩ := List.getElem?_eq_some_iff.1 h2
    simp only [VExpr.projs, List.getElem_map, List.getElem_range]
    exact .proj he (hPW _ (by simpa using hj1))

theorem _root_.Lean4Lean.List.Forall₂.split_left {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m : List β}, List.Forall₂ R (l₁ ++ l₂) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons h t =>
    let ⟨m₁, m₂, e, h1, h2⟩ := Lean4Lean.List.Forall₂.split_left t
    ⟨_ :: m₁, m₂, e ▸ rfl, .cons h h1, h2⟩

/-- A translation applied to arguments: its application to their translations, given that this is
well formed. -/
theorem TrExpr.mkAppList {env : VEnv} {Us Δ} (henv : VEnv.WF env)
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) {as : List Expr} {xs : List VExpr} {f f'}
    (hf : TrExpr env Us Δ f f') (has : as.Forall₂ (TrExprS env Us Δ) xs)
    (hwf : VExpr.WF env Us.length Δ.toCtx (f'.appN xs)) :
    TrExpr env Us Δ (f.mkAppList as) (f'.appN xs) :=
  let ⟨_, hf₂, hd⟩ := hf
  have hd' := VEnv.IsDefEqU.appN henv hΔ hd.symm hwf
  ⟨_, TrExprS.mkAppList henv.ordered hΔ hf₂ has (let ⟨_, h⟩ := hd'; ⟨_, h.hasType.2⟩), hd'.symm⟩

/-- The constructor a recursor's rule names, as the environment holds it: for an auxiliary type,
the earlier type's constructor, with that type's parameters. -/
theorem ruleCtorInfo {c : VContext} {s : Name} {d : VInductDecl} {t₀ t : Nat}
    {T : VInductiveType} {c' : VConstructor} (hs : c.venv.inducts s = some (d, t₀))
    (ht : d.allTypes[t]? = some T) (hcm : c' ∈ T.ctors) :
    ∃ w, c.env.find? c'.name = some (.ctorInfo w) ∧
      w.numParams = (T.nested.map (·.args.length)).getD d.params.length := by
  obtain ⟨env₀, envT, -, hd, hT, hle, -⟩ := c.Ewf.inducts hs
  rcases VInductDecl.allTypes_cases ht with ht | hTa
  · have hno : T.nested = none := (hd.types T (List.mem_of_getElem? ht)).2
    obtain ⟨lp, -, -, hCs⟩ := c.trenv.blockConsts hs
    obtain ⟨w, hw, hwc⟩ := hCs t c' (VInductDecl.mem_ctors_iff.2 ⟨T, ht, hcm⟩)
    obtain ⟨-, -, -, -, -, -, hwnp, -⟩ := hwc
    refine ⟨w, ?_, by simp [hno, hwnp]⟩
    rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?]; exact hw
  · obtain ⟨o, hno, hAux⟩ := hd.aux T hTa
    obtain ⟨⟨dI, tI, TI, hind, hTI, -, -, hargslen, -, -, hctors⟩⟩ := hAux envT hT
    obtain ⟨cI, hcI, hname, -⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors c' hcm
    obtain ⟨lp, -, -, hCs⟩ := c.trenv.blockConsts (hle.inducts hind)
    obtain ⟨w, hw, hwc⟩ := hCs tI cI (VInductDecl.mem_ctors_iff.2 ⟨TI, hTI, hcI⟩)
    obtain ⟨-, -, -, -, -, -, hwnp, -⟩ := hwc
    refine ⟨w, ?_, by simp [hno, hwnp, hargslen]⟩
    rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?, hname]; exact hw

theorem inductiveReduceRec.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hΓ := c.Δwf.toCtx
  unfold inductiveReduceRec
  split <;> [rename_i recFn ls hfn; exact .pure nofun]
  split <;> [rename_i info hfind; exact .pure nofun]
  extract_lets recArgs majorIdx jp3 jp2 jp1
  -- the recursor and its block
  have he0 := he
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at he0
  obtain ⟨f', args', he', hf', hargs⟩ := he0.mkAppList_inv
  cases hf' with | @const _ _ lsR' _ _ hcR hlsR hlenR => ?_
  obtain ⟨hname, hsafe, -, -⟩ := c.trenv.find?_uniq hfind hcR
  have hfind' := hfind
  rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?] at hfind'
  obtain ⟨d, T₀, t, T, envR, hs, -, ht, hleR, hTR, -⟩ := c.trenv.recInfo hfind' hsafe
  obtain ⟨hRn, hmi, -, -, hnp, hni, hnmot, hnmin, -, hkK, -, hrules⟩ := hTR
  have hrecFn : recFn = d.recName t := (hname : info.name = recFn).symm.trans hRn
  subst hrecFn
  obtain ⟨hrecC, -⟩ := c.Ewf.recBlock hs
  cases hcR.symm.trans (hrecC t T ht)
  have hargsL : recArgs.toList = e.getAppArgsList := Expr.getAppArgs_toList
  have hmIdx : majorIdx = d.params.length + d.allTypes.length + d.allCtors.length +
      T.indices.length := by
    simp [majorIdx, RecursorVal.getMajorIdx, hnp, hnmot, hnmin, hni]
  split <;> [rename_i major hmaj; exact .pure nofun]
  -- the recursor's arguments: parameters, motives, minor premises, indices, the major premise
  have hmaj' : e.getAppArgsList[majorIdx]? = some major := by
    rw [← hargsL, Array.getElem?_toList]; exact hmaj
  have hlenL := (List.getElem?_eq_some_iff.1 hmaj').1
  rw [hmIdx] at hlenL hmaj'
  generalize hL : e.getAppArgsList = L at hargsL hmaj' hargs hlenL
  obtain ⟨eps, R1, rfl, hl1⟩ : ∃ a b, L = a ++ b ∧ a.length = d.params.length :=
    ⟨L.take d.params.length, L.drop _, (List.take_append_drop ..).symm, by simp; omega⟩
  obtain ⟨eMs, R2, rfl, hl2⟩ : ∃ a b, R1 = a ++ b ∧ a.length = d.allTypes.length :=
    ⟨R1.take d.allTypes.length, R1.drop _, (List.take_append_drop ..).symm,
      by simp at hlenL ⊢; omega⟩
  obtain ⟨ems, R3, rfl, hl3⟩ : ∃ a b, R2 = a ++ b ∧ a.length = d.allCtors.length :=
    ⟨R2.take d.allCtors.length, R2.drop _, (List.take_append_drop ..).symm,
      by simp at hlenL ⊢; omega⟩
  obtain ⟨eidx, R4, rfl, hl4⟩ : ∃ a b, R3 = a ++ b ∧ a.length = T.indices.length :=
    ⟨R3.take T.indices.length, R3.drop _, (List.take_append_drop ..).symm,
      by simp at hlenL ⊢; omega⟩
  obtain ⟨erest, rfl⟩ : ∃ r, R4 = major :: r := by
    simp only [← List.append_assoc] at hmaj'
    rw [List.getElem?_append_right (by simp; omega)] at hmaj'
    rw [show d.params.length + d.allTypes.length + d.allCtors.length + T.indices.length -
      (eps ++ eMs ++ ems ++ eidx).length = 0 by simp; omega] at hmaj'
    match R4, hmaj' with | m :: r, h => exact ⟨r, by simp at h; rw [h]⟩
  simp only [← List.append_assoc] at hargs hL hargsL
  obtain ⟨A4, B4, rfl, h4, hB4⟩ := Lean4Lean.List.Forall₂.split_left hargs
  obtain ⟨A3, idx', rfl, h3, hidxT⟩ := Lean4Lean.List.Forall₂.split_left h4
  obtain ⟨A2, ms', rfl, h2, hmsT⟩ := Lean4Lean.List.Forall₂.split_left h3
  obtain ⟨ps', Ms', rfl, hpsT, hMsT⟩ := Lean4Lean.List.Forall₂.split_left h2
  cases hB4 with | @cons _ major' _ rest' hmajT hrestT => ?_
  have hps := (Lean4Lean.List.Forall₂.length_eq hpsT).symm.trans hl1
  have hMs := (Lean4Lean.List.Forall₂.length_eq hMsT).symm.trans hl2
  have hms := (Lean4Lean.List.Forall₂.length_eq hmsT).symm.trans hl3
  have hidx := (Lean4Lean.List.Forall₂.length_eq hidxT).symm.trans hl4
  have hwfe := he.wf c.Ewf c.Δwf
  rw [he'] at hwfe
  have H : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
      (.appN (.const (d.recName t) lsR') (ps' ++ Ms' ++ ms' ++ idx' ++ [major'])) :=
    VExpr.appN_wf_prefix c.Ewf.ordered hΓ (bs := rest') (by simpa using hwfe)
  -- the recursor applied up to its major premise, whose arguments follow
  have hE : c.TrExprS ((Expr.const (d.recName t) ls).mkAppList
      (eps ++ eMs ++ ems ++ eidx ++ [major]))
      (.appN (.const (d.recName t) lsR') (ps' ++ Ms' ++ ms' ++ idx' ++ [major'])) :=
    TrExprS.mkAppList c.Ewf.ordered hΓ (.const (hrecC t T ht) hlsR hlenR)
      (forall₂_append h4 (.cons hmajT .nil)) H
  have he1 : c.TrExprS (((Expr.const (d.recName t) ls).mkAppList
      (eps ++ eMs ++ ems ++ eidx ++ [major])).mkAppList erest) e' := by
    rw [← Expr.mkAppList_append, List.append_assoc _ [major], List.singleton_append, ← hL, ← hfn,
      Expr.mkAppList_getAppArgsList]
    exact he
  have hfvArgs : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e →
      ∀ a ∈ eps ++ eMs ++ ems ++ eidx ++ major :: erest, FVarsIn P a := by
    intro P hP h a ha
    rw [← Expr.mkAppList_getAppArgsList e, hL, FVarsIn.mkAppList] at h
    exact h.2 a ha
  have hjp2 : ∀ s major₁, c.FVarsBelow e major₁ → c.TrExpr major₁ major' →
      RecM.WF c s (jp2 () major₁) fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    intro s major₁ hm1 ⟨M₂, hM, hMd⟩
    simp only [jp2]
    split <;> [rename_i rule hrule; exact .pure nofun]
    unfold getRecRuleFor at hrule
    split at hrule <;> [rename_i fn lsM hmfn; cases hrule]
    have hmem := List.mem_of_find?_eq_some hrule
    have hctorEq : rule.ctor = fn := by simpa using List.find?_some hrule
    obtain ⟨⟨⟨j, c'⟩, q⟩, hmemF, hj, hrc, hnf, hrhs⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l hrules rule hmem
    subst j
    have hq : d.allCtors[q]? = some (t, c') :=
      List.mk_mem_zipIdx_iff_getElem?.1 (List.mem_filter.1 hmemF).1
    have hcm : c' ∈ T.ctors := by
      obtain ⟨T', hT', hc⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
      cases ht.symm.trans hT'; exact hc
    obtain ⟨w, hwfind, hwnp⟩ := ruleCtorInfo hs ht hcm
    generalize hnP : (T.nested.map (·.args.length)).getD d.params.length = nP at hwnp
    split <;> [rename_i mkInfo hmk; exact .pure nofun]
    rw [hrc, hwfind] at hmk; cases hmk
    split <;> [exact .pure nofun; rename_i hsize]
    split <;> [exact .pure nofun; rename_i hlsl]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsize hlsl
    -- the major premise is the constructor applied to parameters and fields
    have hM' := hM
    rw [← Expr.mkAppList_getAppArgsList major₁, hmfn] at hM'
    obtain ⟨fC, margs', rfl, hfC, hmargs⟩ := hM'.mkAppList_inv
    cases hfC with | @const _ _ lsC' _ _ hcC hlsC hlenC => ?_
    have hfnc : fn = c'.name := hctorEq.symm.trans hrc
    subst hfnc
    have hmsize : major₁.getAppArgsList.length = nP + c'.fields.length := by
      rw [← Expr.getAppArgs_toList, Array.length_toList, hsize, hwnp, hnf]
    have hmL : major₁.getAppArgs.toList = major₁.getAppArgsList := Expr.getAppArgs_toList
    generalize hML : major₁.getAppArgsList = ML at hmargs hmsize hmL
    obtain ⟨mps, mfs, rfl, hml1⟩ : ∃ a b, ML = a ++ b ∧ a.length = nP :=
      ⟨ML.take nP, ML.drop _, (List.take_append_drop ..).symm, by simp; omega⟩
    have hml2 : mfs.length = c'.fields.length := by simp at hmsize; omega
    obtain ⟨psC, fs, rfl, hpsCT, hfsT⟩ := Lean4Lean.List.Forall₂.split_left hmargs
    have hpsC := ((Lean4Lean.List.Forall₂.length_eq hpsCT).symm.trans hml1).trans hnP.symm
    have hfs := (Lean4Lean.List.Forall₂.length_eq hfsT).symm.trans hml2
    have hiota := c.Ewf.iota hΓ hs ht hq hps hMs hms hidx H hpsC hfs hMd.symm
    -- the rule's right-hand side at the recursor's levels
    have c1 := (TrExprS.mono hleR hrhs).instL c.Ewf (by trivial) hlsR hlsl.symm
    have c2 := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [c1.wf.closedN c.Ewf trivial |>.liftN_eq (Nat.zero_le _)] at c2
    -- the reduct
    have hfi : info.getFirstIndexIdx = d.params.length + d.allTypes.length + d.allCtors.length := by
      simp [RecursorVal.getFirstIndexIdx, hnp, hnmot, hnmin]
    have hsize' : major₁.getAppArgs.size = nP + c'.fields.length := by
      rw [hsize, hwnp, hnf]
    rw [Expr.mkAppRange_eq (args := recArgs) (i := 0) (l₁ := []) (l₂ := eps ++ eMs ++ ems)
        (l₃ := eidx ++ major :: erest) (by simp [hargsL]) rfl (by simp [hfi]; omega),
      Expr.mkAppRange_eq (args := major₁.getAppArgs) (l₁ := mps) (l₂ := mfs) (l₃ := [])
        (by simp [hmL]) (by rw [hsize', hnf]; omega) (by simp [hsize']; omega)]
    have hT2 : c.TrExpr (((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList
        (eps ++ eMs ++ ems)).mkAppList mfs)
        ((VExpr.const (d.recName t) lsR').appN (ps' ++ Ms' ++ ms' ++ idx' ++ [major'])) := by
      rw [← Expr.mkAppList_append]
      refine (TrExpr.mkAppList c.Ewf hΓ c2 (forall₂_append h3 hfsT) ?_).defeq c.Ewf hΓ hiota.symm
      exact let ⟨_, h⟩ := hiota; ⟨_, h.hasType.2⟩
    have hfv2 : c.FVarsBelow e (((rule.rhs.instantiateLevelParams info.levelParams ls).mkAppList
        (eps ++ eMs ++ ems)).mkAppList mfs) := by
      intro P hP h
      have ha := hfvArgs P hP h
      have hm := hm1 P hP h
      rw [← Expr.mkAppList_getAppArgsList major₁, hmfn, hML, FVarsIn.mkAppList] at hm
      rw [FVarsIn.mkAppList, FVarsIn.mkAppList]
      exact ⟨⟨c1.fvarsIn.mono nofun, fun a ha' =>
        ha a (List.mem_append_left _ (List.mem_append_left _ ha'))⟩,
        fun a ha' => hm.2 a (by simp [ha'])⟩
    simp only [jp3]
    split
    · rw [Expr.mkAppRange_eq (args := recArgs) (l₁ := eps ++ eMs ++ ems ++ eidx ++ [major])
        (l₂ := erest) (l₃ := []) (by simp [hargsL]) (by simp [hmIdx]; omega)
        (by rw [← Array.length_toList, hargsL]; simp)]
      refine .pure fun _ h => ?_
      cases h
      refine ⟨fun P hP h => ?_, TrExpr.rebuild_mkAppList c.Ewf c.Δwf hE he1 hT2⟩
      rw [FVarsIn.mkAppList]
      exact ⟨hfv2 P hP h, fun a ha' => hfvArgs P hP h a (by simp [ha'])⟩
    · rename_i hlt
      obtain rfl : erest = [] := by
        rw [← Array.length_toList, hargsL] at hlt
        simp [hmIdx] at hlt
        exact List.eq_nil_of_length_eq_zero (by omega)
      refine .pure fun _ h => ?_
      cases h
      exact ⟨hfv2, TrExpr.rebuild_mkAppList (as := []) c.Ewf c.Δwf hE he1 hT2⟩
  -- the major premise as a constructor application: a literal's, or by structure eta
  have hjp1 : ∀ s major₀, c.FVarsBelow e major₀ → c.TrExpr major₀ major' →
      RecM.WF c s (jp1 () major₀) fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    intro s major₀ hm0 ⟨X, hX, hXd⟩
    simp only [jp1]
    refine (whnf.WF hX).bind fun w _ _ ⟨hw1, hw2⟩ => ?_
    have hw2' := hw2.defeq c.Ewf hΓ hXd
    have hmw := hm0.trans hw1
    split
    · obtain ⟨Y, hY, hYd⟩ := hw2'
      cases hY with | lit _ hY => ?_
      exact hjp2 _ _ (fun _ _ _ => FVarsIn.natLitToConstructor) ⟨Y, hY, hYd⟩
    · obtain ⟨Y, hY, hYd⟩ := hw2'
      cases hY with | lit _ hY => ?_
      refine (whnf.WF hY).bind fun m _ _ ⟨hm1', hm2'⟩ => ?_
      exact hjp2 _ _ (fun P hP _ => hm1' P hP FVarsIn.strLitToConstructor)
        (hm2'.defeq c.Ewf hΓ hYd)
    · obtain ⟨Y, hY, hYd⟩ := hw2'
      refine (toCtorWhenStruct.WF hY).bind fun m _ _ ⟨h1, h2⟩ => ?_
      exact hjp2 _ _ (hmw.trans h1) (h2.defeq c.Ewf hΓ hYd)
  have hm0 : c.FVarsBelow e major := fun P hP h => hfvArgs P hP h major (by simp)
  dsimp only
  split
  · rename_i hk
    have hK := hkK.1 hk
    have ht' : d.types[t]? = some T := by
      obtain ⟨-, -, -, -, haux, -⟩ := hK
      rw [VInductDecl.allTypes_of_aux haux] at ht; exact ht
    have hno : T.nested = none := by
      obtain ⟨_, _, _, hd, _, _, _⟩ := c.Ewf.inducts hs
      exact (hd.types T (List.mem_of_getElem? ht')).2
    rw [hno] at hmi
    refine (toCtorWhenK.WF hk (c.Ewf.inducts_getElem hs ht') ht' hK hmi hnp hmajT).bind
      fun m _ _ ⟨h1, h2⟩ => ?_
    exact hjp1 _ _ (hm0.trans h1) h2
  · exact hjp1 _ _ hm0 (hmajT.trExpr c.Ewf c.Δwf)

end Lean4Lean.TypeChecker.Inner

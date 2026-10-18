import Lean4Lean.Theory.Typing.QuotReduce

/-! Iota reduction: a recursor applied to a constructor application is the iota rule's right-hand
side at the recursor's arguments and the constructor's fields. -/

namespace Lean4Lean
open VExpr

/-- A term over parameters and fields, reseated past `a` binders between them, substituted with
arguments for all three is the term substituted with the parameters and the fields. -/
theorem VExpr.reseat_subst_consList (e : VExpr) (σ : Subst) {a m : Nat} {ps Xs fs : List VExpr}
    (hX : Xs.length = a) (hf : fs.length = m) :
    (e.reseat a m m 0 0).subst (σ.consList (ps ++ Xs ++ fs)) = e.subst (σ.consList (ps ++ fs)) := by
  rw [VInductDecl.reseat_eq_subst _ _ _ _ _ _ (Nat.le_refl _), subst_subst]
  congr 1; funext i
  simp only [Subst.comp, Subst.ofLift, subst, Subst.consList_append]
  have hl : ((((Lift.refl.skipN a).consN m).skipN (m - m + 0)).consN 0).liftVar i =
      if i < m then i else i + a := by
    simp only [Nat.sub_self, Nat.add_zero, Lift.consN, Lift.skipN, Lift.liftVar_consN_skipN,
      liftVar, Nat.add_comm a]
  rw [hl]
  by_cases h : i < m
  · rw [if_pos h]; simp [Subst.consList_apply, hf, h]
  · rw [if_neg h]
    have h1 : ¬ i + a < m := by omega
    have h2 : ¬ i + a - m < a := by omega
    simp only [Subst.consList_apply, hf, hX, h, h1, h2, dite_false]
    rw [show i + a - m - a = i - m by omega]

theorem VExpr.bvars_subst_consList_mid (σ : Subst) (ps Xs ys : List VExpr) :
    (bvars ps.length (Xs.length + ys.length)).map (·.subst (σ.consList (ps ++ Xs ++ ys))) = ps := by
  rw [Subst.consList_append, Subst.consList_append,
    show Xs.length + ys.length = (0 + Xs.length) + ys.length by omega,
    subst_bvars_consList_ge, subst_bvars_consList_ge, subst_bvars_consList]

theorem VExpr.liftN_subst_consList_mid (e : VExpr) (σ : Subst) {a m : Nat} {ps Xs fs : List VExpr}
    (hX : Xs.length = a) (hf : fs.length = m) :
    (e.liftN a m).subst (σ.consList (ps ++ Xs ++ fs)) = e.subst (σ.consList (ps ++ fs)) := by
  simpa [reseat] using reseat_subst_consList e σ hX hf

theorem VExpr.getElem_liftTele (n : Nat) : ∀ (As : List VExpr) (k r : Nat)
    (h : r < (liftTele n As k).length),
    (liftTele n As k)[r] = (As[r]'(by simpa using h)).liftN n (k + r)
  | _ :: _, _, 0, _ => by simp [liftTele]
  | _ :: As, k, r + 1, h => by
    simp only [liftTele, List.getElem_cons_succ]
    rw [getElem_liftTele n As (k + 1) r, Nat.add_right_comm, Nat.add_assoc]

/-- The recursors and iota rules a recorded block was added with. -/
theorem VEnv.WF.recBlock {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    (hs : env.inducts s = some (d, t)) :
    (∀ i T, d.allTypes[i]? = some T → env.constants (d.recName i) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel i T⟩) ∧
    ∀ df ∈ d.iotaRules, env.defeqs df := by
  obtain ⟨env₀, env₂, -, -, hadd, hle, -⟩ := henv.inducts_block hs
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := hadd
  have hle' := VEnv.addDefEqList_le.trans ((VEnv.addBlock_le hB).trans hle)
  refine ⟨fun i T hi => ?_, fun df hdf => ?_⟩
  · refine hle'.constants ?_
    · refine VEnv.addConstList_constants_of_mem hR ?_
      simp only [VInductDecl.recConsts, List.mem_map]
      exact ⟨(T, i), List.mk_mem_zipIdx_iff_getElem?.2 hi, rfl⟩
  · exact ((VEnv.addBlock_le hB).trans hle).defeqs (VEnv.addDefEqList_defeqs_of_mem hdf)

theorem VEnv.addConstList_fresh : ∀ {env e : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some e → ∀ p ∈ cs, env.constants p.1 = none
  | _, _, [], _, _, h => nomatch h
  | env, _, (m, ci) :: cs, h, p, hp => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    have hm : env.constants m = none := by
      unfold VEnv.addConst at h1; split at h1 <;> simp_all
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hm
    · cases hc : env.constants p.1 with
      | none => rfl
      | some a =>
        have := VEnv.addConstList_fresh h2 p hp
        rw [(VEnv.addConst_le h1).constants hc] at this; cases this

theorem VEnv.addConstList_nodup : ∀ {env e : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some e → (cs.map (·.1)).Nodup
  | _, _, [], _ => .nil
  | env, _, (m, ci) :: cs, h => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    refine List.nodup_cons.2 ⟨fun hm => ?_, VEnv.addConstList_nodup h2⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    have := VEnv.addConstList_fresh h2 p hp
    rw [VEnv.addConst_self h1] at this; cases this

/-- A recorded block is recorded under each of its types, at that type's position. -/
theorem VEnv.WF.inducts_getElem {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl}
    {t₀ i : Nat} {T : VInductiveType} (hs : env.inducts s = some (d, t₀))
    (hi : d.types[i]? = some T) : env.inducts T.name = some (d, i) := by
  obtain ⟨env₀, env₂, -, -, hadd, hle, -⟩ := henv.inducts_block hs
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := hadd
  have hnd : (d.types.map (·.name)).Nodup := by
    simpa [VInductDecl.typeConsts, Function.comp_def] using VEnv.addConstList_nodup hT
  refine hle.inducts ?_
  unfold VEnv.addBlock at hB; split at hB <;> cases hB
  have hlt := (List.getElem?_eq_some_iff.1 hi).1
  have hTi := (List.getElem?_eq_some_iff.1 hi).2
  have : d.types.findIdx? (·.name == T.name) = some i := by
    refine List.findIdx?_eq_some_iff_getElem.2 ⟨hlt, by simp [hTi], fun j hj => ?_⟩
    have := mt (List.getElem_inj (i := j) (j := i)
      (h₀ := by simpa using Nat.lt_trans hj hlt) (h₁ := by simpa using hlt) hnd).1 (by omega)
    simpa [hTi] using this
  simp [this]

theorem VExpr.foralls_inj' : ∀ {As As' : List VExpr} {B B' : VExpr},
    (∀ A C, B ≠ .forallE A C) → (∀ A C, B' ≠ .forallE A C) →
    VExpr.foralls As B = .foralls As' B' → As = As' ∧ B = B'
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hB, _, h => (hB _ _ h).elim
  | _ :: _, [], _, _, _, hB', h => (hB' _ _ h.symm).elim
  | _ :: _, _ :: _, _, _, hB, hB', h => by
    simp only [foralls_cons, forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := VExpr.foralls_inj' hB hB' h
    exact ⟨rfl, rfl⟩

theorem VExpr.appN_const_inj {n n' : Name} {ls ls' : List VLevel} {xs ys : List VExpr}
    (h : VExpr.appN (.const n ls) xs = .appN (.const n' ls') ys) : xs = ys := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs', x, rfl⟩ <;>
    rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
  · rfl
  · simp [appN_append_singleton, appN] at h
  · simp [appN_append_singleton, appN] at h
  · simp only [List.concat_eq_append, appN_append_singleton] at h ⊢
    obtain ⟨h1, rfl⟩ := VExpr.app.inj h
    rw [VExpr.appN_const_inj h1]
termination_by xs.length

theorem VEnv.EqUpToLevels.foralls_inv {U : Nat} : ∀ {As As' : List VExpr} {B B' : VExpr},
    (∀ A C, B ≠ .forallE A C) → (∀ A C, B' ≠ .forallE A C) →
    VEnv.EqUpToLevels U (.foralls As B) (.foralls As' B') →
    As.length = As'.length ∧ VEnv.EqUpToLevels U B B'
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hB, _, h => by cases h; exact (hB _ _ rfl).elim
  | _ :: _, [], _, _, _, hB', h => by cases h; exact (hB' _ _ rfl).elim
  | _ :: _, _ :: _, _, _, hB, hB', h => by
    cases h with | forallE _ h =>
    obtain ⟨h1, h2⟩ := VEnv.EqUpToLevels.foralls_inv hB hB' h
    exact ⟨by simp [h1], h2⟩

theorem VEnv.EqUpToLevels.appN_const_length {U : Nat} {n n' : Name} {ls ls' : List VLevel}
    (xs ys : List VExpr)
    (h : VEnv.EqUpToLevels U (.appN (.const n ls) xs) (.appN (.const n' ls') ys)) :
    xs.length = ys.length := by
  obtain rfl | ⟨xs', x, rfl⟩ := List.eq_nil_or_concat xs
  · obtain rfl | ⟨ys', y, rfl⟩ := List.eq_nil_or_concat ys
    · rfl
    · simp only [List.concat_eq_append, appN_append_singleton] at h
      change VEnv.EqUpToLevels U (.const n ls) _ at h; cases h
  · obtain rfl | ⟨ys', y, rfl⟩ := List.eq_nil_or_concat ys
    · simp only [List.concat_eq_append, appN_append_singleton] at h
      change VEnv.EqUpToLevels U _ (.const n' ls') at h; cases h
    · simp only [List.concat_eq_append, appN_append_singleton] at h ⊢
      cases h with | app h _ => simp [VEnv.EqUpToLevels.appN_const_length xs' ys' h]
termination_by xs.length

/-- An auxiliary type's constructor has as many fields and indices as the constructor of the
earlier type it copies. -/
theorem VInductDecl.auxCounts {d dI : VInductDecl} {envT envTI : VEnv} {T TI : VInductiveType}
    {c cI : VConstructor} {o : VNested} (hno : T.nested = some o) (hcW : c.WF envT d T)
    (hTI : TI.nested = none) (hcIW : cI.WF envTI dI TI)
    (hargslen : o.args.length = dI.params.length)
    (hcorr : ∃ ps B, cI.type = .foralls ps B ∧ ps.length = dI.params.length ∧ ∃ ps' Y,
      ps'.length = d.params.length ∧ c.type = .foralls ps' Y ∧
      VEnv.EqUpToLevels d.uvars Y ((B.instL o.lvls).subst (VExpr.Subst.dflt.consList o.args))) :
    c.fields.length = cI.fields.length ∧ c.indices.length = cI.indices.length := by
  obtain ⟨ps, Ds, hty, hps, hfs, -⟩ := hcW.shape
  obtain ⟨psI', DsI, htyI, hpsI, hfsI, -⟩ := hcIW.shape
  obtain ⟨psI, BcI, hcIty, hpsIlen, ps'', Y, hps''len, hcty, hY⟩ := hcorr
  rw [hcIty, foralls_append] at htyI
  obtain ⟨rfl, hB⟩ := VExpr.foralls_inj htyI (by rw [hpsIlen, hpsI.length_eq])
  rw [hty, foralls_append] at hcty
  obtain ⟨rfl, rfl⟩ := VExpr.foralls_inj hcty (by rw [hps''len, hps.length_eq])
  rw [hB, instL_foralls, subst_foralls, VInductiveType.typeApp_of_none hTI] at hY
  simp only [VInductiveType.typeApp, hno, instL_appN, instL, subst_appN, List.map_append] at hY
  obtain ⟨hlen1, hZ⟩ := VEnv.EqUpToLevels.foralls_inv (fun _ _ => appN_const_ne_forallE)
    (fun _ _ => appN_const_ne_forallE) hY
  simp only [List.length_map, List.length_zipIdx] at hlen1
  refine ⟨by rw [← hfs.length, ← hfsI.length, hlen1], ?_⟩
  have := VEnv.EqUpToLevels.appN_const_length _ _ hZ
  simp only [List.length_append, List.length_map, VExpr.bvars, List.length_reverse,
    List.length_range, hargslen] at this
  omega

/-- Each pair of arguments of a pair of telescope substitutions, definitionally equal at its
entry instantiated by the left arguments before it. -/
theorem VEnv.Ctx.SubstEq.getElemDF {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {τ τ' : Subst} :
    ∀ (n : Nat) {As as bs : List VExpr}, as.length = n →
    VEnv.Ctx.SubstEq env U Γ (τ.consList as) (τ'.consList bs) (As.reverse ++ Δ) →
    as.length = As.length → bs.length = As.length → ∀ r (h : r < as.length) (h' : r < bs.length)
      (h'' : r < As.length),
      env.IsDefEq U Γ as[r] bs[r] (As[r].subst (τ.consList (as.take r)))
  | 0, _, as, _, hn, _, _, _, r, h, _, _ => by simp [List.eq_nil_of_length_eq_zero hn] at h
  | n + 1, As, as, bs, hn, W, hlen, hlen', r, h, h', h'' => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    obtain ⟨bs, b, rfl⟩ : ∃ bs' b, bs = bs' ++ [b] := by
      simpa using (List.eq_nil_or_concat bs).resolve_left (by rintro rfl; simp at hlen')
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn hlen'
    rw [Subst.consList_concat, Subst.consList_concat, List.reverse_append] at W
    cases W with | cons W' _ ha =>
    simp only [List.length_append, List.length_singleton] at h h' h''
    rcases Nat.lt_or_ge r as.length with hr | hr
    · have := VEnv.Ctx.SubstEq.getElemDF n hn W' hlen hlen' r hr (by omega) (by omega)
      simp only [List.getElem_append_left hr, List.getElem_append_left (show r < bs.length by omega),
        List.getElem_append_left (show r < As.length by omega),
        List.take_append_of_le_length (Nat.le_of_lt hr)]
      exact this
    · obtain rfl : r = as.length := by omega
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_append_right (show bs.length ≤ as.length by omega),
        List.getElem_append_right (show As.length ≤ as.length by omega), List.take_left']
      simp only [hlen, hlen', Nat.sub_self, List.getElem_cons_zero]
      exact ha

/-- The major premise of an iota reduction: a term of a type the recursors range over, at levels
`lsB` and parameters `ps`, that is one of the type's constructors at any levels and parameters, is
that constructor at `lsB` and `ps`; and the type's indices are determined by the term. For an
auxiliary type, the constructor is the earlier type's, and its block decides both. -/
theorem VEnv.WF.iotaHead {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t₀ i : Nat} {Ti : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t₀)) (hi : d.allTypes[i]? = some Ti)
    (hcm : c ∈ Ti.ctors) {lsB lsC : List VLevel} (hlsB : ∀ l ∈ lsB, l.WF U)
    (hlenB : lsB.length = d.uvars) {ps idx psC fs : List VExpr} {major : VExpr}
    (hps : ps.length = d.params.length) (hidx : idx.length = Ti.indices.length)
    (hpsC : psC.length = (Ti.nested.map (·.args.length)).getD d.params.length)
    (hfs : fs.length = c.fields.length)
    (hmajT : env.HasType U Γ major (Ti.typeApp lsB ps idx))
    (hmaj : env.IsDefEqU U Γ major (.appN (.const c.name lsC) (psC ++ fs))) :
    env.IsDefEqU U Γ major (Ti.ctorApp c lsB ps fs) ∧
    ∀ idx', idx'.length = Ti.indices.length → env.HasType U Γ major (Ti.typeApp lsB ps idx') →
      List.Forall₂ (env.IsDefEqU U Γ) idx idx' := by
  obtain ⟨_, hmaj0⟩ := hmaj
  have hfsT {Δ Fs : List VExpr} (hFs : fs.length = Fs.length)
      (W0 : Ctx.SubstEq env U Γ ((Subst.id.consList psC).consList fs)
        ((Subst.id.consList psC).consList fs) (Fs.reverse ++ Δ)) :
      ∀ r (h : r < fs.length), VExpr.WF env U Γ fs[r] := fun r h =>
    ⟨_, VEnv.Ctx.SubstEq.getElem _ rfl W0 hFs r h (by omega)⟩
  -- arguments definitionally equal pairwise, by the parameters' positions in a telescope
  have hargs {as bs : List VExpr} (hlen : as.length = bs.length) (hab : ∀ r (h : r < as.length)
      (h' : r < bs.length), env.IsDefEqU U Γ as[r] bs[r])
      (hfs' : ∀ r (h : r < fs.length), VExpr.WF env U Γ fs[r]) :
      List.Forall₂ (env.IsDefEqU U Γ) (as ++ fs) (bs ++ fs) := by
    refine List.forall₂_of_getElem? (by simp [hlen]) fun j a b h1 h2 => ?_
    rcases Nat.lt_or_ge j as.length with hj | hj
    · rw [List.getElem?_append_left hj] at h1
      rw [List.getElem?_append_left (by omega)] at h2
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 h1
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 h2
      exact hab _ _ _
    · rw [List.getElem?_append_right hj] at h1
      rw [List.getElem?_append_right (by omega), show j - bs.length = j - as.length by omega] at h2
      cases h1.symm.trans h2
      obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 h1
      exact hfs' _ _
  rcases VInductDecl.allTypes_cases hi with ht | hTa
  · -- one of the block's own types
    obtain ⟨_, _, _, hd, _, _, _⟩ := henv.inducts hs
    have hno : Ti.nested = none := (hd.types Ti (List.mem_of_getElem? ht)).2
    have hsi := henv.inducts_getElem hs ht
    rw [hno] at hpsC; simp only [Option.map_none, Option.getD_none] at hpsC
    rw [VInductiveType.typeApp_of_none hno] at hmajT
    rw [VInductiveType.ctorApp_of_none hno]
    have hF := henv.recFacts hs hlsB hlenB
    have hjc : (i, c) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨Ti, ht, hcm⟩
    have hcil : c.indices.length = Ti.indices.length := (hF.ctor hjc ht).1
    obtain ⟨hlsC, hlenC, As, fs', hasfs, hAs, -, W0, hX0T⟩ :=
      henv.ctorApp hΓ hsi ht hcm (args := psC ++ fs) (by simp [hpsC, hfs]) ⟨_, hmaj0.hasType.2⟩ .id
    obtain ⟨rfl, rfl⟩ := List.append_inj hasfs (hpsC.trans hAs.symm)
    have hmajC := hX0T.defeqU_l henv hΓ ⟨_, hmaj0.symm⟩
    obtain ⟨hlsBC, Wpi⟩ := VEnv.IsDefEqU.indApp_inv henv hΓ hsi ht hlsB hlenB hlsC hlenC hps hidx
      hpsC (by simp [hcil]) (hmajT.isType henv.ordered hΓ) (hmajC.isType henv.ordered hΓ)
      (hmajT.uniqU henv hΓ hmajC)
    have hpsDF : ∀ r (h : r < psC.length) (h' : r < ps.length),
        env.IsDefEqU U Γ psC[r] ps[r] := by
      intro r h h'
      have := VEnv.Ctx.SubstEq.getElemDF (Δ := [])
        (As := d.params.map (·.instL lsB) ++ Ti.indices.map (·.instL lsB)) _ rfl
        (by rw [List.append_nil]; exact Wpi) (by simp [hps, hidx]) (by simp [hpsC, hcil])
        r (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [List.getElem_append_left h, List.getElem_append_left h'] at this
      exact ⟨_, this.symm⟩
    obtain ⟨cc, hcc, hlsC', hlenC'⟩ := (appN_wf_prefix henv.ordered hΓ (as := []) (bs := psC ++ fs)
      (by rw [List.nil_append]; exact ⟨_, hmaj0.hasType.2⟩)).const_inv henv.ordered hΓ
    have hX01 : env.IsDefEqU U Γ (.appN (.const c.name lsC) (psC ++ fs))
        (.appN (.const c.name lsB) (ps ++ fs)) :=
      VEnv.IsDefEqU.appN' henv hΓ ⟨_, .constDF hcc hlsC' hlsB hlenC'
        (List.Forall₂.flip (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) hlsBC))⟩
        (hargs (by rw [hpsC, hps]) hpsDF (hfsT (by simp [hfs]) W0)) ⟨_, hmaj0.hasType.2⟩
    refine ⟨VEnv.IsDefEqU.trans henv hΓ ⟨_, hmaj0⟩ hX01, fun idx' hidx' hmaj' => ?_⟩
    rw [VInductiveType.typeApp_of_none hno] at hmaj'
    obtain ⟨-, Wpi1⟩ := VEnv.IsDefEqU.indApp_inv henv hΓ hsi ht hlsB hlenB hlsB hlenB hps hidx
      hps hidx' (hmajT.isType henv.ordered hΓ) (hmaj'.isType henv.ordered hΓ)
      (hmajT.uniqU henv hΓ hmaj')
    refine List.forall₂_of_getElem? (by simp [hidx, hidx']) fun j a b h1 h2 => ?_
    obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hj2, rfl⟩ := List.getElem?_eq_some_iff.1 h2
    have := VEnv.Ctx.SubstEq.getElemDF (Δ := [])
      (As := d.params.map (·.instL lsB) ++ Ti.indices.map (·.instL lsB)) _ rfl
      (by rw [List.append_nil]; exact Wpi1) (by simp [hps, hidx]) (by simp [hps, hidx'])
      (ps.length + j) (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at this
    exact ⟨_, this⟩
  · -- an auxiliary type: the earlier block's type and constructor
    obtain ⟨env₀, envT, -, hd, hT, hle, -⟩ := henv.inducts hs
    obtain ⟨o, hno, hAux⟩ := hd.aux Ti hTa
    obtain ⟨⟨dI, tI, TI, hind, hTI, hlvlen, hlvwf, hargslen, -, -, hctors⟩⟩ := hAux envT hT
    have hindE : env.inducts o.ind = some (dI, tI) := hle.inducts hind
    obtain ⟨env₀I, envTI, -, hdI, hTI', -, TI', hTI'', hname⟩ := henv.inducts hindE
    cases hTI.symm.trans hTI''
    rw [hno] at hpsC; simp only [Option.map_some, Option.getD_some] at hpsC
    obtain ⟨cI, hcI, hcorr⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors c hcm
    have hTIno : TI.nested = none := (hdI.types TI (List.mem_of_getElem? hTI)).2
    have hcIW := (hdI.ctors envTI hTI' TI (List.mem_append_left _ (List.mem_of_getElem? hTI))).2
      cI hcI
    have hcW := (hd.ctors envT hT Ti (List.mem_append_right _ hTa)).2 c hcm
    obtain ⟨hfl, hil⟩ := VInductDecl.auxCounts hno hcW hTIno hcIW hargslen hcorr.2
    have hcil : c.indices.length = Ti.indices.length := hcW.indices.1
    have hcIil : cI.indices.length = TI.indices.length := hcIW.indices.1
    have hlvB : ∀ l ∈ o.lvls.map (·.inst lsB), l.WF U := by
      intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hlsB
    have hlvB' : (o.lvls.map (·.inst lsB)).length = dI.uvars := by simp [hlvlen]
    have hA₁ : (o.args.map fun a => (a.instL lsB).subst (Subst.dflt.consList ps)).length =
        dI.params.length := by simp [hargslen]
    simp only [VInductiveType.typeApp, hno] at hmajT
    simp only [VInductiveType.ctorApp, hno]
    rw [hcorr.1] at hmaj0 ⊢
    obtain ⟨hlsC, hlenC, As, fs', hasfs, hAs, -, W0, hX0T⟩ :=
      henv.ctorApp hΓ hindE hTI hcI (args := psC ++ fs) (by simp [hpsC, hfs, hargslen, hfl])
        ⟨_, hmaj0.hasType.2⟩ .id
    obtain ⟨rfl, rfl⟩ := List.append_inj hasfs (hpsC.trans (hargslen.trans hAs.symm))
    have hmajC := hX0T.defeqU_l henv hΓ ⟨_, hmaj0.symm⟩
    obtain ⟨hlsBC, Wpi⟩ := VEnv.IsDefEqU.indApp_inv henv hΓ hindE hTI hlvB hlvB' hlsC hlenC hA₁
      (by rw [hidx, ← hcil, hil, hcIil]) (hpsC.trans hargslen) (by simp [hcIil])
      (hmajT.isType henv.ordered hΓ) (hmajC.isType henv.ordered hΓ) (hmajT.uniqU henv hΓ hmajC)
    have hpsDF : ∀ r (h : r < psC.length)
        (h' : r < (o.args.map fun a => (a.instL lsB).subst (Subst.dflt.consList ps)).length),
        env.IsDefEqU U Γ psC[r]
          (o.args.map fun a => (a.instL lsB).subst (Subst.dflt.consList ps))[r] := by
      intro r h h'
      have := VEnv.Ctx.SubstEq.getElemDF (Δ := [])
        (As := dI.params.map (·.instL (o.lvls.map (·.inst lsB))) ++
          TI.indices.map (·.instL (o.lvls.map (·.inst lsB)))) _ rfl
        (by rw [List.append_nil]; exact Wpi) (by simp [hargslen, hidx, ← hcil, hil, hcIil])
        (by simp [hpsC, hargslen, hcIil]) r (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [List.getElem_append_left h, List.getElem_append_left h'] at this
      exact ⟨_, this.symm⟩
    obtain ⟨cc, hcc, hlsC', hlenC'⟩ := (appN_wf_prefix henv.ordered hΓ (as := []) (bs := psC ++ fs)
      (by rw [List.nil_append]; exact ⟨_, hmaj0.hasType.2⟩)).const_inv henv.ordered hΓ
    have hX01 : env.IsDefEqU U Γ (.appN (.const cI.name lsC) (psC ++ fs))
        (.appN (.const cI.name (o.lvls.map (·.inst lsB)))
          ((o.args.map fun a => (a.instL lsB).subst (Subst.dflt.consList ps)) ++ fs)) :=
      VEnv.IsDefEqU.appN' henv hΓ ⟨_, .constDF hcc hlsC' hlvB hlenC'
        (List.Forall₂.flip (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) hlsBC))⟩
        (hargs (by rw [hpsC, hA₁, hargslen]) hpsDF (hfsT (by simp [hfs, hfl]) W0)) ⟨_, hmaj0.hasType.2⟩
    refine ⟨VEnv.IsDefEqU.trans henv hΓ ⟨_, hmaj0⟩ hX01, fun idx' hidx' hmaj' => ?_⟩
    simp only [VInductiveType.typeApp, hno] at hmaj'
    obtain ⟨-, Wpi1⟩ := VEnv.IsDefEqU.indApp_inv henv hΓ hindE hTI hlvB hlvB' hlvB hlvB' hA₁
      (by rw [hidx, ← hcil, hil, hcIil]) hA₁ (by rw [hidx', ← hcil, hil, hcIil])
      (hmajT.isType henv.ordered hΓ) (hmaj'.isType henv.ordered hΓ) (hmajT.uniqU henv hΓ hmaj')
    refine List.forall₂_of_getElem? (by simp [hidx, hidx']) fun j a b h1 h2 => ?_
    obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hj2, rfl⟩ := List.getElem?_eq_some_iff.1 h2
    have := VEnv.Ctx.SubstEq.getElemDF (Δ := [])
      (As := dI.params.map (·.instL (o.lvls.map (·.inst lsB))) ++
        TI.indices.map (·.instL (o.lvls.map (·.inst lsB)))) _ rfl
      (by rw [List.append_nil]; exact Wpi1) (by simp [hargslen, hidx, ← hcil, hil, hcIil])
      (by simp [hargslen, hidx', ← hcil, hil, hcIil])
      ((o.args.map fun a => (a.instL lsB).subst (Subst.dflt.consList ps)).length + j)
      (by simp; omega) (by simp; omega) (by simp [hargslen]; omega)
    simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at this
    exact ⟨_, this⟩

/-- Iota reduction: the recursor of a recorded block applied to a constructor application of its
type is the iota rule's right-hand side at the recursor's parameters, motives and minor
premises, and the constructor's fields. -/
theorem VEnv.WF.iota {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t₀ t q : Nat} {Tj : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t₀)) (ht : d.allTypes[t]? = some Tj)
    (hq : d.allCtors[q]? = some (t, c)) {lsR lsC : List VLevel} {ps Ms ms idx psC fs : List VExpr}
    {major : VExpr} (hps : ps.length = d.params.length) (hMs : Ms.length = d.allTypes.length)
    (hms : ms.length = d.allCtors.length) (hidx : idx.length = Tj.indices.length)
    (H : VExpr.WF env U Γ
      (.appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++ idx ++ [major])))
    (hpsC : psC.length = (Tj.nested.map (·.args.length)).getD d.params.length)
    (hfs : fs.length = c.fields.length)
    (hmaj : env.IsDefEqU U Γ major (.appN (.const c.name lsC) (psC ++ fs))) :
    env.IsDefEqU U Γ
      (.appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++ idx ++ [major]))
      (.appN ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q t c).rhs.instL lsR)
        (ps ++ Ms ++ ms ++ fs)) := by
  have hjc : (t, c) ∈ d.allCtors := List.mem_of_getElem? hq
  have hcm : c ∈ Tj.ctors := by
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_allCtors_iff.1 hjc
    cases ht.symm.trans hT'; exact hc
  obtain ⟨hrecC, hiotas⟩ := henv.recBlock hs
  have hrc := hrecC t Tj ht
  -- the recursor's levels, and the block's levels they give
  obtain ⟨ci, hci, hlsR, hlenR⟩ :=
    (appN_wf_prefix henv.ordered hΓ (as := []) (bs := ps ++ Ms ++ ms ++ idx ++ [major])
      (by simpa using H)).const_inv henv.ordered hΓ
  cases hrc.symm.trans hci
  have hlenR' : lsR.length = d.recUVars := hlenR
  have hlsB : ∀ l ∈ d.recLevels.map (·.inst lsR), l.WF U := by
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hlsR
  have hlenB : (d.recLevels.map (·.inst lsR)).length = d.uvars := by
    simp [VInductDecl.recLevels_length]
  -- the recursor's telescope, ending in the major premise
  have hrT := VEnv.HasType.const (Γ := []) hrc hlsR hlenR
  rw [VInductDecl.recType_instL] at hrT
  simp only [VInductDecl.recType] at hrT
  rw [show ∀ As (A B : VExpr), VExpr.foralls As (.forallE A B) = .foralls (As ++ [A]) B from
    fun As A B => by rw [foralls_append]; rfl] at hrT
  have htele := (IsType.foralls_inv henv.ordered
    (VEnv.IsDefEq.isType henv.ordered (Γ := []) trivial hrT)).1
  have hr0 := hrT.weak0 henv.ordered (Γ := Γ)
  rw [← subst_id (e := VExpr.foralls _ _)] at hr0
  have W := VEnv.HasType.appN_invT henv hΓ (Δ := []) hr0 .nil htele H (by
    simp [VInductDecl.recBinders, VInductDecl.motiveTypes, VInductDecl.minorTypes, hps, hMs, hms,
      hidx])
  rw [List.reverse_append, List.append_nil, Subst.consList_concat] at W
  cases W with | cons WX _ hmajT =>
  change env.HasType U Γ major (VExpr.subst _ (Subst.id.consList (ps ++ Ms ++ ms ++ idx))) at hmajT
  have hmajT' : env.HasType U Γ major
      (Tj.typeApp (d.recLevels.map (·.inst lsR)) ps idx) := by
    simp only [VInductiveType.typeApp_subst] at hmajT
    rw [show d.allTypes.length + d.allCtors.length + Tj.indices.length =
        (Ms ++ ms).length + idx.length by simp [hMs, hms, hidx], ← hps,
      show ps ++ Ms ++ ms ++ idx = ps ++ (Ms ++ ms) ++ idx by simp,
      bvars_subst_consList_mid, ← hidx, Subst.consList_append, subst_bvars_consList] at hmajT
    exact hmajT
  have hF := henv.recFacts hs hlsB hlenB
  obtain ⟨hcil, hcH0⟩ := hF.ctorHead hjc ht
  obtain ⟨hmajX1, hinj⟩ := henv.iotaHead hΓ hs ht hcm hlsB hlenB hps hidx hpsC hfs hmajT' hmaj
  -- the fields, against the constructor's telescope at the major premise's parameters
  have WPs : Ctx.SubstEq env U Γ (Subst.id.consList ps) (Subst.id.consList ps)
      (d.params.map (·.instL (d.recLevels.map (·.inst lsR)))).reverse := by
    have WX' : Ctx.SubstEq env U Γ (((Subst.id.consList ps).consList (Ms ++ ms)).consList idx)
        (((Subst.id.consList ps).consList (Ms ++ ms)).consList idx)
        ((liftTele (d.allTypes.length + d.allCtors.length)
            (Tj.indices.map (·.instL (d.recLevels.map (·.inst lsR))))).reverse ++
          (((d.motiveTypes (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR)) ++
            d.minorTypes (d.recLevels.map (·.inst lsR))).reverse ++
          (d.params.map (·.instL (d.recLevels.map (·.inst lsR)))).reverse)) := by
      simpa [VInductDecl.recBinders, Subst.consList_append, List.append_assoc] using WX
    exact Ctx.SubstEq.dropList (as := Ms ++ ms) (as' := Ms ++ ms)
      (Bs := d.motiveTypes (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) ++
        d.minorTypes (d.recLevels.map (·.inst lsR))) (by simp [hMs, hms]) (by simp [hMs, hms])
      (Ctx.SubstEq.dropList (as := idx) (as' := idx) (by simp [hidx]) (by simp [hidx]) WX')
  have hcH := hcH0.subst henv.ordered WPs hΓ
  rw [VInductiveType.ctorHead_subst, ← hps, subst_bvars_consList] at hcH
  have hX1wf : VExpr.WF env U Γ (.appN (Tj.ctorHead c (d.recLevels.map (·.inst lsR)) ps) fs) := by
    rw [← VInductiveType.ctorApp_eq]; exact let ⟨_, h⟩ := hmajX1; ⟨_, h.hasType.2⟩
  have W1 := VEnv.HasType.appN_invT henv hΓ hcH WPs (hF.fields hjc) hX1wf (by simp [hfs])
  have hX1T := VEnv.HasType.appN_substT
    (Δ := (d.params.map (·.instL (d.recLevels.map (·.inst lsR)))).reverse) hcH (by simp [hfs]) W1
  rw [VInductiveType.typeApp_subst, ← hfs, show (VExpr.bvars ps.length fs.length) =
    VExpr.bvars ps.length (0 + fs.length) by rw [Nat.zero_add], subst_bvars_consList_ge,
    subst_bvars_consList, ← VInductiveType.ctorApp_eq] at hX1T
  have hmaj1 := hX1T.defeqU_l henv hΓ hmajX1.symm
  have hidxDF := hinj _ (by simp [hcil]) hmaj1
  -- the iota rule, at the recursor's levels
  have hdf : env.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q t c) :=
    hiotas _ (List.mem_map.2 ⟨((t, c), q), List.mk_mem_zipIdx_iff_getElem?.2 hq, rfl⟩)
  have hlenE : lsR.length =
      (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q t c).uvars := by
    simp [VInductDecl.iotaRule, hlenR']
  have hE0 := VEnv.IsDefEq.extra (Γ := []) hdf hlsR hlenE
  have hE := VEnv.IsDefEq.extra (Γ := Γ) hdf hlsR hlenE
  obtain ⟨hl, hr, hty⟩ :=
    d.iotaRule_instL d.recLevels lsR (VLevel.params d.recUVars) d.motiveLevel q t c
  rw [VLevel.params_inst hlenR'] at hl hr hty
  rw [hl, hr, hty] at hE0 hE
  rw [hr]
  generalize d.recLevels.map (VLevel.inst lsR) = lsB at *
  generalize d.motiveLevel.inst lsR = v at *
  have hlenF : (d.recBinders lsB v ++ liftTele (d.allTypes.length + d.allCtors.length)
      (c.fields.map (·.type.instL lsB))).length = (ps ++ Ms ++ ms ++ fs).length := by
    simp [VInductDecl.recBinders, VInductDecl.motiveTypes, VInductDecl.minorTypes, hps, hMs, hms,
      hfs]
  obtain ⟨B, hB⟩ : ∃ B, (d.iotaRule lsB v lsR q t c).rhs = .lams (d.recBinders lsB v ++
      liftTele (d.allTypes.length + d.allCtors.length) (c.fields.map (·.type.instL lsB))) B := ⟨_, rfl⟩
  obtain ⟨L, hLB⟩ : ∃ L, (d.iotaRule lsB v lsR q t c).lhs = .lams (d.recBinders lsB v ++
      liftTele (d.allTypes.length + d.allCtors.length) (c.fields.map (·.type.instL lsB))) L ∧
      L.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs)) =
        .appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++
          (c.indices.map (·.instL lsB)).map (·.subst ((Subst.id.consList ps).consList fs)) ++
          [Tj.ctorApp c lsB ps fs]) := by
    refine ⟨_, rfl, ?_⟩
    have hargs : ps ++ Ms ++ ms ++ fs = ps ++ (Ms ++ ms) ++ fs := by simp
    have e1 : (bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = ps := by
      rw [hargs, show d.allTypes.length + d.allCtors.length + c.fields.length =
        (Ms ++ ms).length + fs.length by simp [hMs, hms, hfs], ← hps, bvars_subst_consList_mid]
    have e2 : (bvars d.allTypes.length (d.allCtors.length + c.fields.length)).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = Ms := by
      rw [Subst.consList_append, Subst.consList_append, Subst.consList_append, ← hfs, ← hms,
        subst_bvars_consList_ge, ← Nat.zero_add ms.length, subst_bvars_consList_ge, ← hMs,
        subst_bvars_consList]
    have e3 : (bvars d.allCtors.length c.fields.length).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = ms := by
      rw [Subst.consList_append, Subst.consList_append, ← hfs, ← Nat.zero_add fs.length,
        subst_bvars_consList_ge, ← hms, subst_bvars_consList]
    have e4 : (bvars c.fields.length 0).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = fs := by
      rw [Subst.consList_append, ← hfs, subst_bvars_consList]
    have e5 : (c.indices.map fun e => (instL lsB e).reseat (d.allTypes.length + d.allCtors.length)
          c.fields.length c.fields.length 0 0).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) =
        (c.indices.map (·.instL lsB)).map (·.subst ((Subst.id.consList ps).consList fs)) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun e _ => ?_
      simp only [Function.comp_apply]
      rw [hargs, reseat_subst_consList _ _ (by simp [hMs, hms]) hfs, Subst.consList_append]
    simp only [subst_appN, List.map_append, List.map_cons, List.map_nil, VInductDecl.recConst,
      subst, VInductDecl.ctorAppAt_eq ht, VInductiveType.ctorApp_subst, e1, e2, e3, e4, e5]
  rw [hB] at hE0 hE ⊢
  rw [hLB.1] at hE0 hE
  -- arguments for the rule's binders
  have WP : Ctx.SubstEq env U Γ (Subst.id.consList (ps ++ Ms ++ ms))
      (Subst.id.consList (ps ++ Ms ++ ms)) (d.recBinders lsB v).reverse := by
    have WX' : Ctx.SubstEq env U Γ ((Subst.id.consList (ps ++ Ms ++ ms)).consList idx)
        ((Subst.id.consList (ps ++ Ms ++ ms)).consList idx)
        ((liftTele (d.allTypes.length + d.allCtors.length) (Tj.indices.map (·.instL lsB))).reverse ++
          (d.recBinders lsB v).reverse) := by
      rw [← List.reverse_append, ← Subst.consList_append]; exact WX
    exact Ctx.SubstEq.dropList (by simp [hidx]) (by simp [hidx]) WX'
  have hFT := (IsTele.append_inv
    (VExpr.WF.lams_inv henv.ordered (Γ := []) trivial ⟨_, hE0.hasType.1⟩).1).2
  rw [List.append_nil] at hFT
  have Wi := VEnv.Ctx.SubstEq.ofGetElem WP _ (as := fs) rfl hFT (by simp [hfs]) fun r h h' => by
    have := VEnv.Ctx.SubstEq.getElem _ rfl W1 (by simp [hfs]) r h (by simp; omega)
    rw [VExpr.getElem_liftTele, Nat.zero_add, ← Subst.consList_append,
      show ps ++ Ms ++ ms = ps ++ (Ms ++ ms) from List.append_assoc .., 
      VExpr.liftN_subst_consList_mid _ _ (by simp [hMs, hms]) (by simp; omega), Subst.consList_append]
    exact this
  rw [← Subst.consList_append, ← List.reverse_append] at Wi
  obtain ⟨_, hL⟩ := VEnv.lams_appN henv hΓ ⟨_, hE0.hasType.1⟩ hlenF.symm Wi
  rw [hLB.2] at hL
  have hLR := VEnv.IsDefEqU.appN henv hΓ (vs := ps ++ Ms ++ ms ++ fs) ⟨_, hE⟩ ⟨_, hL.hasType.1⟩
  -- the recursor's application is the rule's left-hand side at these arguments
  have hpre := appN_wf_prefix henv.ordered hΓ (as := ps ++ Ms ++ ms) (bs := idx ++ [major])
    (by rw [← List.append_assoc]; exact H)
  have hcong := VEnv.IsDefEqU.appN' henv hΓ hpre (forall₂_append hidxDF (.cons hmajX1 .nil))
    (by rw [← appN_append, ← List.append_assoc]; exact H)
  rw [← appN_append, ← appN_append, ← List.append_assoc, ← List.append_assoc] at hcong
  exact hcong.trans henv hΓ ((VEnv.IsDefEqU.symm ⟨_, hL⟩).trans henv hΓ hLR)

/-- A recorded type is the constant its block was added with. -/
theorem VEnv.WF.type_constant {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T) :
    T.name = s ∧ env.constants s = some ⟨d.uvars, T.type⟩ := by
  obtain ⟨env₀, envT, -, -, hT, hle, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'
  exact ⟨hname, hname ▸ hle.constants (VEnv.addConstList_constants_of_mem hT
    (List.mem_map.2 ⟨T, List.mem_of_getElem? ht, rfl⟩))⟩

/-- A type of a recorded block in `Prop` with a single constructor without fields, applied to
arguments: the constructor at the arguments' parameters is a term of it at the constructor's
indices, and any two terms of it are definitionally equal, by proof irrelevance. -/
theorem VEnv.WF.kTarget {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hz : d.level ≈ .zero) (hc : T.ctors = [c]) (hf : c.fields = [])
    {ls : List VLevel} {as : List VExpr} {x : VExpr}
    (hx : env.HasType U Γ x (.appN (.const s ls) as)) :
    (∀ l ∈ ls, l.WF U) ∧ ls.length = d.uvars ∧
    as.length = d.params.length + T.indices.length ∧
    env.HasType U Γ (.appN (.const c.name ls) (as.take d.params.length))
      (.appN (.const s ls) (as.take d.params.length ++ (c.indices.map (·.instL ls)).map
        (·.subst (Subst.dflt.consList (as.take d.params.length))))) ∧
    ∀ y, env.HasType U Γ y (.appN (.const s ls) as) →
      env.IsDefEq U Γ x y (.appN (.const s ls) as) := by
  obtain ⟨env₀, envT, -, -, hT, hle, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'; subst hname
  have ⟨_, hS⟩ := hx.isType henv.ordered hΓ
  obtain ⟨ci, hci, hls, hlen⟩ := (appN_wf_prefix henv.ordered hΓ (as := []) (bs := as)
    (by rw [List.nil_append]; exact ⟨_, hS⟩)).const_inv henv.ordered hΓ
  cases hci.symm.trans (hle.constants (VEnv.addConstList_constants_of_mem hT
    (List.mem_map.2 ⟨T, List.mem_of_getElem? ht, rfl⟩)))
  have hF := henv.recFacts hs hls hlen
  have hty := hF.type ht
  have hty0 := hty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hty .dflt] at hty0
  have hlenA : as.length = d.params.length + T.indices.length := by
    simpa using VEnv.HasType.appN_sort_length henv hΓ hty0 hS
  obtain ⟨As, I, rfl, hA, hI⟩ : ∃ As I, as = As ++ I ∧ As.length = d.params.length ∧
      I.length = T.indices.length :=
    ⟨as.take d.params.length, as.drop d.params.length, (List.take_append_drop ..).symm,
      by simp [hlenA], by simp [hlenA]⟩
  have W := henv.projArgs hΓ hs ht hls hlen hA hI hx
  have hsort := VEnv.HasType.appN_substT (Δ := []) (as := As ++ I) hty0 (by simp [hA, hI])
    (by simpa using W)
  simp only [subst] at hsort
  have hprop : env.HasType U Γ (.appN (.const T.name ls) (As ++ I)) (.sort .zero) := by
    refine hsort.defeqU_r henv hΓ ⟨_, .sortDF (.inst hls) trivial ?_⟩
    simpa [VLevel.inst] using VLevel.inst_congr_l (ls := ls) hz
  -- the constructor at the parameters
  have hcm : (t, c) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc]⟩
  obtain ⟨-, hcty⟩ := hF.ctor hcm ht
  rw [hf, List.map_nil, List.append_nil, List.length_nil] at hcty
  have hc0 := hcty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hcty .dflt] at hc0
  rw [List.reverse_append, Subst.consList_append] at W
  have WP := Ctx.SubstEq.dropList (by simp [hI]) (by simp [hI]) W
  have hk := VEnv.HasType.appN_substT (Δ := []) (as := As) hc0 (by simp [hA]) (by simpa using WP)
  simp only [subst_appN, subst, List.map_append] at hk
  rw [← hA, subst_bvars_consList] at hk
  refine ⟨hls, hlen, by simp [hA, hI], ?_, fun y hy => .proofIrrel hprop hx hy⟩
  rw [List.take_left' hA]
  simpa [List.map_map, Function.comp_def] using hk

/-- A term of a non-recursive structure that is not a proposition is its constructor applied to
its type's parameters and its projections. -/
theorem VEnv.WF.structEtaProjs {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) (hi : T.indices = []) (hrec : d.isRec = false)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    (hnz : (d.level.inst ls).IsNeverZero) {As : List VExpr} {x : VExpr}
    (hA : As.length = d.params.length) (hx : env.HasType U Γ x (.appN (.const s ls) As)) :
    (∀ j < c.fields.length, VExpr.WF env U Γ (.proj s j x)) ∧
    env.IsDefEq U Γ x (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length x))
      (.appN (.const s ls) As) := by
  have hI : ([] : List VExpr).length = T.indices.length := by simp [hi]
  have hx' : env.HasType U Γ x (.appN (.const s ls) (As ++ [])) := by simpa using hx
  have W := henv.projArgs hΓ hs ht hls hlen hA hI hx'
  simp only [List.append_nil, hi, List.map_nil] at W
  obtain ⟨_, hS⟩ := hx'.isType henv.ordered hΓ
  have hP : ∀ j < c.fields.length, d.ProjAllowed c ls j := fun _ _ h => (h hnz).elim
  have hPW : ∀ j < c.fields.length, VExpr.WF env U Γ (.proj s j x) := fun j hj' => by
    obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj'⟩
    exact ⟨_, (VEnv.projCongr henv.ordered hΓ hs ht hc (henv.projFacts hs ht hc) hls hlen hA hI
      hA hI W hS hx' j f hf (hP j hj')).2⟩
  refine ⟨hPW, henv.structEta hΓ hs ht hc hi hrec hls hlen hA (by simp [VExpr.projs]) hx hP
    fun j hj => ?_⟩
  have hj' : j < c.fields.length := by simpa [VExpr.projs] using hj
  simp only [VExpr.projs, List.getElem_map, List.getElem_range]
  exact hPW j hj'

end Lean4Lean

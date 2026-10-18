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

/-- A recorded type is the constant its block was added with. -/
theorem VEnv.WF.type_constant {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T) :
    T.name = s ∧ env.constants s = some ⟨d.uvars, T.type⟩ := by
  obtain ⟨env₀, envT, -, -, hT, hle, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'
  exact ⟨hname, hname ▸ hle.constants (VEnv.addConstList_constants_of_mem hT
    (List.mem_map.2 ⟨T, List.mem_of_getElem? ht, rfl⟩))⟩

end Lean4Lean

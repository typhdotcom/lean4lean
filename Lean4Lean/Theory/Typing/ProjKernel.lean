import Lean4Lean.Theory.Typing.Recursor

/-! The projection's type as `inferProj` computes it: the constructor's declared field domain at
the parameters and the earlier projections. The kernel lets the projection past an earlier field
that is not a proof only when nothing declared after it mentions it, and the fields' views mention
no more than their declared domains do, so those fields can be removed from the context
(`VConstructor.keptLiftBy`), leaving the domain over typed projections only. -/

namespace Lean4Lean
open VExpr

theorem VExpr.skips'_liftN : ∀ (e : VExpr) {j k : Nat}, j ≤ k → e.Skips' 1 k →
    (e.liftN 1 j).Skips' 1 (k + 1)
  | .bvar i, j, k, hj, h => by
    simp only [Skips'] at h
    simp only [liftN, liftVar, Skips']; split <;> omega
  | .sort _, _, _, _, _ | .const .., _, _, _, _ => trivial
  | .app f a, _, _, hj, h => ⟨skips'_liftN f hj h.1, skips'_liftN a hj h.2⟩
  | .proj _ _ e, _, _, hj, h => skips'_liftN e hj h
  | .lam A B, _, _, hj, h | .forallE A B, _, _, hj, h =>
    ⟨skips'_liftN A hj h.1, skips'_liftN B (Nat.succ_le_succ hj) h.2⟩

/-- A term substituted by a substitution that keeps the `k`th variable and sends every other one
to a term not mentioning it mentions the `k`th variable if the term does. -/
theorem VExpr.skips'_of_subst : ∀ (e : VExpr) {S : Subst} {k : Nat}, S k = .bvar k →
    (∀ i, i ≠ k → (S i).Skips' 1 k) → (e.subst S).Skips' 1 k → e.Skips' 1 k
  | .bvar i, S, k, h1, _, h => by
    by_cases hi : i = k
    · subst hi; simp [subst, h1, Skips'] at h
    · simp only [Skips']; omega
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ => trivial
  | .app f a, S, k, h1, h2, h => ⟨skips'_of_subst f h1 h2 h.1, skips'_of_subst a h1 h2 h.2⟩
  | .proj _ _ e, S, k, h1, h2, h => skips'_of_subst e (S := S) h1 h2 h
  | .lam A B, S, k, h1, h2, h | .forallE A B, S, k, h1, h2, h => by
    refine ⟨skips'_of_subst A h1 h2 h.1, skips'_of_subst B (S := S.lift) (k := k + 1) ?_ ?_ h.2⟩
    · simp [Subst.lift, h1, lift, liftN]
    · intro i hi
      cases i with
      | zero => simp [Subst.lift, Skips']
      | succ i => exact skips'_liftN (S i) (Nat.zero_le _) (h2 i (by omega))

theorem VExpr.skips_of_subst_lift {e : VExpr} {σ : Subst} (h : (e.subst σ.lift).Skips 1 0) :
    e.Skips 1 0 := by
  rw [skips_iff] at h ⊢
  refine skips'_of_subst e (S := σ.lift) rfl (fun i hi => ?_) h
  cases i with
  | zero => contradiction
  | succ i => rw [← skips_iff]; exact Skips.liftN (e := σ i)

theorem VExpr.skips_foralls : ∀ (As : List VExpr) {B : VExpr} {k : Nat},
    (VExpr.foralls As B).Skips 1 k → ∀ i (A : VExpr), As[i]? = some A → A.Skips 1 (k + i)
  | [], _, _, _, _, _, h => nomatch h
  | A :: As, B, k, h, i, A', hA => by
    rw [skips_iff] at h
    cases i with
    | zero => cases hA; rw [skips_iff]; exact h.1
    | succ i =>
      have := skips_foralls As (B := B) (k := k + 1) (by rw [skips_iff]; exact h.2) i A' hA
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem VExpr.skips'_instL : ∀ (e : VExpr) {ls : List VLevel} {n k : Nat},
    (e.instL ls).Skips' n k ↔ e.Skips' n k
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _ => by simp [instL, Skips']
  | .app f a, _, _, _ => by simp [instL, Skips', skips'_instL f, skips'_instL a]
  | .proj _ _ e, _, _, _ => by simp [instL, Skips', skips'_instL e]
  | .lam A B, _, _, _ | .forallE A B, _, _, _ => by
    simp [instL, Skips', skips'_instL A, skips'_instL B]

theorem VExpr.skips_instL {e : VExpr} {ls : List VLevel} {n k : Nat} :
    (e.instL ls).Skips n k ↔ e.Skips n k := by
  rw [skips_iff, skips_iff, skips'_instL]

theorem VEnv.EqUpToLevels.symm {U : Nat} {e e' : VExpr} (H : VEnv.EqUpToLevels U e e') :
    VEnv.EqUpToLevels U e' e := by
  induction H with
  | bvar => exact .bvar
  | const h1 h2 h3 => exact .const h2 h1 (List.Forall₂.flip (Lean4Lean.List.Forall₂.imp
      (fun _ _ h => h.symm) h3))
  | sort h1 h2 h3 => exact .sort h2 h1 h3.symm
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

theorem VEnv.EqUpToLevels.skips' {U : Nat} {e e' : VExpr} (H : VEnv.EqUpToLevels U e e') :
    ∀ {n k}, e.Skips' n k ↔ e'.Skips' n k := by
  induction H with
  | bvar | const | sort => simp [Skips']
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => simp [Skips', ih1, ih2]
  | proj _ ih => simp [Skips', ih]

theorem VEnv.EqUpToLevels.skips {U : Nat} {e e' : VExpr} (H : VEnv.EqUpToLevels U e e')
    {n k : Nat} : e.Skips n k ↔ e'.Skips n k := by
  rw [skips_iff, skips_iff, H.skips']

theorem VEnv.TeleDefEq.getElem {env : VEnv} {U : Nat} : ∀ {Γ As Bs : List VExpr},
    env.TeleDefEq U Γ As Bs → ∀ i (A B : VExpr), As[i]? = some A → Bs[i]? = some B →
      env.IsDefEqU U ((Bs.take i).reverse ++ Γ) A B
  | _, [], [], .nil, _, _, _, h, _ => nomatch h
  | _, _ :: _, _ :: _, .cons h1 h2, 0, _, _, hA, hB => by cases hA; cases hB; simpa using h1
  | _, _ :: _, _ :: _, .cons _ h2, i + 1, A, B, hA, hB => by
    simpa using VEnv.TeleDefEq.getElem h2 i A B hA hB

/-- Arguments for a telescope are arguments, entry by entry, for one agreeing with it. -/
theorem VEnv.Ctx.SubstEq.getElem_teleDefEq {env envT : VEnv} {U U' : Nat} {Γ : List VExpr}
    (henv : env.WF) (hle : envT ≤ env) (hΓ : OnCtx Γ (env.IsType U)) {ps params : List VExpr}
    (hT : envT.TeleDefEq U' [] ps params) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    {As : List VExpr}
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (params.map (·.instL ls)).reverse)
    (hA : As.length = params.length) :
    ∀ a (h : a < As.length) (P : VExpr), ps[a]? = some P →
      env.HasType U Γ As[a] ((P.instL ls).subst (Subst.dflt.consList (As.take a))) := by
  intro a h P hP
  have hpa : a < params.length := hA ▸ h
  have hX := VEnv.Ctx.SubstEq.getElem (Δ := []) As.length rfl (by simpa using W) (by simp [hA])
    a h (by simpa using hpa)
  simp only [List.getElem_map] at hX
  have hdf := (VEnv.TeleDefEq.getElem hT a P _ hP (List.getElem?_eq_getElem hpa)).instL hls
    |>.mono hle
  simp only [List.append_nil, List.map_reverse, ← List.map_take] at hdf
  have hsplit : (params.map (·.instL ls)).reverse = ((params.drop a).map (·.instL ls)).reverse ++
      ((params.take a).map (·.instL ls)).reverse := by
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
  rw [hsplit, ← List.take_append_drop a As, Subst.consList_append] at W
  have Wa := VEnv.Ctx.SubstEq.dropList (by simp [hA]) (by simp [hA]) W
  have ⟨_, hd⟩ := hdf
  have H := IsDefEq.substDF henv.ordered Wa.wf hΓ Wa hd
  exact hX.defeqU_r henv hΓ ⟨_, H.symm⟩

/-- A recorded constructor's declared type: a telescope of its parameters, agreeing with the
block's, and of its declared field domains, whose views are its fields. -/
theorem VEnv.WF.ctorShape {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (ht : d.types[t]? = some T) (hcm : c ∈ T.ctors) :
    ∃ envT ps Ds, envT.WF ∧ envT ≤ env ∧ envT.IsTele d.uvars [] d.params ∧
      c.type = .foralls (ps ++ Ds) (.appN (.const T.name (VLevel.params d.uvars))
        (VExpr.bvars d.params.length c.fields.length ++ c.indices)) ∧
      envT.TeleDefEq d.uvars [] ps d.params ∧ d.FieldsWF envT d.params.reverse 0 Ds c.fields ∧
      ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
        ∀ j, D.Skips 1 j → f.type.Skips 1 j := by
  obtain ⟨env₀, envT, h₀, hd, hT, hle, T', hT', -⟩ := henv.inducts hs
  cases ht.symm.trans hT'
  have hcW := (hd.ctors envT hT T (List.mem_append_left _ (List.mem_of_getElem? ht))).2 c hcm
  obtain ⟨ps, Ds, hty, htele, hFW, hwithin⟩ := hcW.shape
  rw [VInductiveType.typeApp_of_none (hd.types T (List.mem_of_getElem? ht)).2] at hty
  have hTwf : envT.WF := VEnv.WF.addConstList h₀ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hd.types T hT).1) hT
  exact ⟨envT, ps, Ds, hTwf, hle, hd.params.mono (VEnv.addConstList_le hT), hty, htele, hFW,
    hwithin⟩

/-- The `k`th projection's declared domain, at the parameters and the earlier projections, is its
type, when the earlier fields whose projections are not typed (`Q`) are mentioned by no declared
domain up to the `k`th. -/
theorem VEnv.WF.declDomain_defeq {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) {envT : VEnv} {Ds : List VExpr} (hTwf : envT.WF) (hle : envT ≤ env)
    (hP0 : envT.IsTele d.uvars [] d.params)
    (hFW : d.FieldsWF envT d.params.reverse 0 Ds c.fields)
    (hwithin : ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      ∀ j, D.Skips 1 j → f.type.Skips 1 j)
    {ls : List VLevel} {As I : List VExpr} {x : VExpr} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.uvars) (hA : As.length = d.params.length)
    (hI : I.length = T.indices.length) (hx : env.HasType U Γ x (.appN (.const s ls) (As ++ I)))
    {Q : Nat → Prop} {k : Nat} {D : VExpr} {f : VField} (hD : Ds[k]? = some D)
    (hf : c.fields[k]? = some f)
    (hQ : ∀ j < k, Q j → ∀ i, j < i → i ≤ k → ∀ Di, Ds[i]? = some Di → Di.Skips 1 (i - 1 - j))
    (hkept : ∀ j < k, ¬Q j → d.ProjAllowed c ls j) :
    env.IsDefEq U Γ ((D.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s k x)))
      (c.projType ls s k As x) (.sort (f.level.inst ls)) := by
  have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  have hlenD := hFW.length
  have hskipF : ∀ i ≤ k, ∀ fi : VField, c.fields[i]? = some fi →
      ∀ j < i, Q j → fi.type.Skips 1 (i - 1 - j) := by
    intro i hi fi hfi j hj hq
    have hiD : i < Ds.length := by rw [hlenD]; exact (List.getElem?_eq_some_iff.1 hfi).1
    exact hwithin i _ fi (List.getElem?_eq_getElem hiD) hfi _
      (hQ j (by omega) hq i hj hi _ (List.getElem?_eq_getElem hiD))
  have hPc : OnCtx d.params.reverse (envT.IsType d.uvars) := by simpa using hP0.onCtx trivial
  have hctx : OnCtx (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse)
      (envT.IsType d.uvars) := by
    have := hFW.tele.1
    rw [← List.take_append_drop k c.fields, List.map_append] at this
    exact (VEnv.IsTele.append_inv this).1.onCtx hPc
  obtain ⟨W, htele⟩ := hFW.keptTele hTwf hP0 (P := Q) (Nat.le_of_lt hk)
    fun i hi _ fi hfi j hj hq => hskipF i (Nat.le_of_lt hi) fi hfi j hj hq
  -- the declared domain and the field's view, without the removed fields
  have hDs := VConstructor.strippedTypeBy_lift' (P := Q) (i := k) (A := D)
    fun j hj hq => hQ j hj hq k hj (Nat.le_refl _) D hD
  have hFs := VConstructor.strippedTypeBy_lift' (P := Q) (i := k) (A := f.type)
    fun j hj hq => hskipF k (Nat.le_refl _) f hf j hj hq
  have hDF := hFW.defeq k D f hD hf
  have hty := hFW.level k f hf
  rw [hDs, hFs] at hDF; rw [hFs] at hty
  have hDF' := (VEnv.IsDefEqU.weak'_iff hTwf hctx W).1 hDF
  have hty' := (VEnv.HasType.weak'_iff hTwf hctx W (A := .sort _)).1 hty
  have H := (hDF'.of_r hTwf (htele.onCtx hPc) hty').instL hls |>.mono hle
  simp only [List.map_append, List.map_reverse] at H
  -- the parameters and the kept projections
  have WA := henv.projArgs hΓ hs ht hls hlen hA hI hx
  rw [List.reverse_append, Subst.consList_append] at WA
  have WP := Ctx.SubstEq.dropList (by simp [hI]) (by simp [hI]) WA
  have hF := henv.projFacts hs ht hc
  have WP' := WP
  have hx' : env.HasType U Γ x (.appN (.const s ls) (As ++ I)) := hx
  have ⟨_, hS⟩ := hx.isType henv.ordered hΓ
  have hFt := (htele.instL hls).mono hle
  simp only [List.map_reverse] at hFt
  have Wk : Ctx.SubstEq env U Γ
      (Subst.dflt.consList (As ++ (VConstructor.keptIdxBy Q k).map (.proj s · x)))
      (Subst.dflt.consList (As ++ (VConstructor.keptIdxBy Q k).map (.proj s · x)))
      (((c.keptFieldsBy Q k).map (·.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) := by
    rw [Subst.consList_append]
    refine Ctx.SubstEq.ofGetElem WP _ (as := (VConstructor.keptIdxBy Q k).map (.proj s · x)) rfl
      hFt (by simp [VConstructor.keptFieldsBy_eq]) fun r h h' => ?_
    simp only [List.length_map] at h
    have hj := List.getElem_mem h
    obtain ⟨hjk, hjq⟩ := VConstructor.mem_keptIdxBy.1 hj
    generalize hj' : (VConstructor.keptIdxBy Q k)[r] = j at hjk hjq
    have hfj := List.getElem?_eq_getElem (Nat.lt_trans hjk hk)
    generalize c.fields[j] = fj at hfj
    have := (VEnv.projCongr henv.ordered hΓ hs ht hc hF hls hlen hA hI hA hI WP' hS hx' j fj hfj
      (hkept j hjk hjq)).2
    simp only [List.getElem_map, hj', VConstructor.keptFieldsBy_eq, hfj, Option.map_some,
      Option.getD_some, ← List.map_take, VConstructor.keptIdxBy_take _ _ _ h,
      ← Subst.consList_append]
    rwa [VConstructor.projType, hfj, Option.map_some, Option.getD_some, VExpr.projs,
      VConstructor.subst_strippedTypeBy (P := Q)
        (fun j' hj' hq => hskipF j (Nat.le_of_lt hjk) fj hfj j' hj' hq)] at this
  have H2 := IsDefEq.substDF henv.ordered Wk.wf hΓ Wk H
  rw [← VConstructor.subst_strippedTypeBy (P := Q)
      (fun j hj hq => hQ j hj hq k hj (Nat.le_refl _) D hD),
    ← VConstructor.subst_strippedTypeBy (P := Q)
      (fun j hj hq => hskipF k (Nat.le_refl _) f hf j hj hq)] at H2
  simpa [VConstructor.projType, hf, VExpr.projs, VExpr.instL, VExpr.subst] using H2

/-- What `inferProj` establishes about the `k`th projection of `x`, having let it past the earlier
fields that are `P`, of whose declared domains no later one mentions them, and having checked,
when the structure may be a proposition (`mp`), that the other earlier fields and the `k`th are
proofs: the projection is allowed and typed, and its declared domain is its type. -/
theorem VEnv.WF.projKernel {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) {envT : VEnv} {Ds : List VExpr} (hTwf : envT.WF) (hle : envT ≤ env)
    (hP0 : envT.IsTele d.uvars [] d.params)
    (hFW : d.FieldsWF envT d.params.reverse 0 Ds c.fields)
    (hwithin : ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      ∀ j, D.Skips 1 j → f.type.Skips 1 j)
    {ls : List VLevel} {As I : List VExpr} {x : VExpr} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.uvars) (hA : As.length = d.params.length)
    (hI : I.length = T.indices.length) (hx : env.HasType U Γ x (.appN (.const s ls) (As ++ I)))
    {mp : Bool} (hmp : mp = false → (d.level.inst ls).IsNeverZero) {P : Nat → Prop}
    (hP : ∀ j i, P j → j < i → ∀ Di, Ds[i]? = some Di → Di.Skips 1 (i - 1 - j)) :
    ∀ k (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      (∀ j ≤ k, ∀ Dj, Ds[j]? = some Dj → (j = k ∨ ¬P j) → mp = true →
        env.HasType U Γ ((Dj.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s j x)))
          (.sort .zero)) →
      d.ProjAllowed c ls k ∧
      env.IsDefEq U Γ ((D.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s k x)))
        (c.projType ls s k As x) (.sort (f.level.inst ls)) ∧
      env.HasType U Γ (.proj s k x) (c.projType ls s k As x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro D f hD hf hprop
  have hlenD := hFW.length
  have hfield : ∀ j < k, ∃ Dj fj, Ds[j]? = some Dj ∧ c.fields[j]? = some fj := fun j hj => by
    have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
    exact ⟨_, _, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)⟩
  have IH' : ∀ j < k, ∀ Dj fj, Ds[j]? = some Dj → c.fields[j]? = some fj → ¬P j → _ :=
    fun j hj Dj fj hDj hfj hPj => IH j hj Dj fj hDj hfj fun j' hj' Dj' hDj' h mp =>
      hprop j' (by omega) Dj' hDj' (h.elim (fun e => .inr (e ▸ hPj)) .inr) mp
  have hkept : ∀ j < k, ¬P j → d.ProjAllowed c ls j := fun j hj hPj =>
    let ⟨_, _, hDj, hfj⟩ := hfield j hj; (IH' j hj _ _ hDj hfj hPj).1
  have hdf := henv.declDomain_defeq hΓ hs ht hc hTwf hle hP0 hFW hwithin hls hlen hA hI hx
    (Q := P) hD hf (fun j _ hq i hji _ Di hDi => hP j i hq hji Di hDi) hkept
  -- a field whose declared domain is a proposition is a proof
  have hzero : ∀ {j Dj} {fj : VField}, Ds[j]? = some Dj → c.fields[j]? = some fj →
      env.IsDefEq U Γ ((Dj.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s j x)))
        (c.projType ls s j As x) (.sort (fj.level.inst ls)) →
      env.HasType U Γ ((Dj.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s j x)))
        (.sort .zero) → fj.level.inst ls ≈ .zero := fun _ _ h1 h2 =>
    (VEnv.IsDefEqU.sort_inv henv hΓ (h1.hasType.1.uniqU henv hΓ h2))
  have hPk : d.ProjAllowed c ls k := by
    intro hnz
    cases mp with
    | false => exact (hnz (hmp rfl)).elim
    | true =>
      refine ⟨fun f' hf' => ?_, fun j hj fj hfj => ?_⟩
      · cases hf.symm.trans hf'
        exact hzero hD hf hdf (hprop k (Nat.le_refl _) D hD (.inl rfl) rfl)
      · by_cases hPj : P j
        · refine .inr fun i fi hji hik hfi => ?_
          have hiD : i < Ds.length := by rw [hlenD]; exact (List.getElem?_eq_some_iff.1 hfi).1
          exact hwithin i _ fi (List.getElem?_eq_getElem hiD) hfi _
            (hP j i hPj hji _ (List.getElem?_eq_getElem hiD))
        · obtain ⟨Dj, fj', hDj, hfj'⟩ := hfield j hj
          cases hfj.symm.trans hfj'
          exact .inl (hzero hDj hfj (IH' j hj Dj fj hDj hfj hPj).2.1
            (hprop j (Nat.le_of_lt hj) Dj hDj (.inr hPj) rfl))
  have WA := henv.projArgs hΓ hs ht hls hlen hA hI hx
  rw [List.reverse_append, Subst.consList_append] at WA
  have WP := Ctx.SubstEq.dropList (by simp [hI]) (by simp [hI]) WA
  have ⟨_, hS⟩ := hx.isType henv.ordered hΓ
  exact ⟨hPk, hdf, (VEnv.projCongr henv.ordered hΓ hs ht hc (henv.projFacts hs ht hc) hls hlen
    hA hI hA hI WP hS hx k f hf hPk).2⟩

end Lean4Lean

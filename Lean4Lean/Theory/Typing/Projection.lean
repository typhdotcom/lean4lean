import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Projections are typed

A projection's type substitutes the earlier projections for the earlier fields. Where the kernel
lets a projection past an earlier field that is not a proof, that field's projection is not
typed, but nothing in the type mentions it: removing the fields the projection skips
(`VConstructor.keptLift`) leaves a type over typed projections only, which is what the
constructor's `projFields` clause types. From it, `projCongr` types each projection, and relates
the projections and their types at definitionally equal terms and parameters.
-/

namespace Lean4Lean
open VExpr

namespace VConstructor
variable (c : VConstructor)
open Classical

/-- The positions before `i` of the fields the `k`th projection does not skip. -/
noncomputable def keptIdx (k i : Nat) : List Nat := (List.range i).filter fun j => ¬c.Skipped k j

theorem keptIdx_succ (k i : Nat) :
    c.keptIdx k (i + 1) = c.keptIdx k i ++ if c.Skipped k i then [] else [i] := by
  simp only [keptIdx, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem keptFields_eq (k : Nat) : c.keptFields k =
    (c.keptIdx k k).map fun j => c.strippedType k j ((c.fields[j]?.map VField.type).getD default) :=
  rfl

theorem keptLift_succ (k i : Nat) : c.keptLift k (i + 1) =
    if c.Skipped k i then .skip (c.keptLift k i) else .cons (c.keptLift k i) := rfl

/-- Substituting entries for the parameters and the fields before the `i`th, through the lift
that keeps the fields the `k`th projection does not skip, substitutes just the kept entries. -/
theorem lift_l_keptLift (k : Nat) (σ : Subst) (As : List VExpr) (g : Nat → VExpr) :
    ∀ i, Subst.lift_l (c.keptLift k i) (σ.consList (As ++ (List.range i).map g)) =
      σ.consList (As ++ (c.keptIdx k i).map g)
  | 0 => by simp [keptLift, keptIdx]
  | i + 1 => by
    rw [keptLift_succ, keptIdx_succ, List.range_succ, List.map_append, ← List.append_assoc,
      List.map_singleton, Subst.consList_concat]
    split
    · simp only [Subst.lift_l_skip, Subst.cons_tail, List.append_nil]
      exact lift_l_keptLift k σ As g i
    · rw [Subst.lift_l_cons, lift_l_keptLift k σ As g i, List.map_append, List.map_singleton,
        ← List.append_assoc, Subst.consList_concat]

theorem lift'_keptLift_consN_skip {ρ : Lift} {n : Nat} {B : VExpr} :
    (B.lift' (ρ.consN n)).liftN 1 n = B.lift' ((Lift.skip ρ).consN n) := by
  rw [← lift'_consN_skipN, ← lift'_comp, ← Lift.consN_comp]; rfl

/-- A term over the parameters, the fields before the `i`th and `n` further binders that does not
mention the fields the `k`th projection skips is a lift by `keptLift`. -/
theorem exists_lift'_keptLift (k : Nat) : ∀ (i n : Nat) (A : VExpr),
    (∀ j < i, c.Skipped k j → A.Skips 1 (n + (i - 1 - j))) →
    ∃ A' : VExpr, A = A'.lift' ((c.keptLift k i).consN n)
  | 0, n, A, _ => ⟨A, by rw [lift'_depth_zero]; simp [keptLift]⟩
  | i + 1, n, A, hA => by
    rw [keptLift_succ]
    split
    · rename_i hi
      obtain ⟨B, rfl⟩ := skips_iff_exists.1 (by simpa using hA i (Nat.lt_succ_self _) hi)
      have hB : ∀ j < i, c.Skipped k j → B.Skips 1 (n + (i - 1 - j)) := by
        intro j hj hs
        have := hA j (by omega) hs
        obtain ⟨C, hC⟩ := skips_iff_exists.1 this
        have e : liftN 1 C ((i - 1 - j) + 1 + n) = liftN 1 B n := by
          rw [hC]; congr 1; omega
        obtain ⟨D, -, rfl⟩ := of_liftN_eq_liftN (k1 := i - 1 - j) (k2 := n) e
        rw [Nat.add_comm]; exact .liftN
      obtain ⟨B', rfl⟩ := exists_lift'_keptLift k i n B hB
      exact ⟨B', lift'_keptLift_consN_skip⟩
    · obtain ⟨A', rfl⟩ := exists_lift'_keptLift k i (n + 1) A fun j hj hs => by
        have := hA j (by omega) hs; rwa [show n + (i + 1 - 1 - j) = n + 1 + (i - 1 - j) by omega]
          at this
      refine ⟨A', ?_⟩
      show _ = A'.lift' ((Lift.consN (c.keptLift k i) 1).consN n)
      rw [Lift.consN_consN, Nat.add_comm]

/-- A field type that does not mention the fields the `k`th projection skips is the lift of its
stripped type. -/
theorem strippedType_lift' {k i : Nat} {A : VExpr}
    (hA : ∀ j < i, c.Skipped k j → A.Skips 1 (i - 1 - j)) :
    A = (c.strippedType k i A).lift' (c.keptLift k i) := by
  obtain ⟨A', hA'⟩ := c.exists_lift'_keptLift k i 0 A (by simpa using hA)
  simp only [Lift.consN] at hA'
  subst hA'
  rw [strippedType, subst_lift', lift_l_inv, subst_id]

/-- The `j`th field, for `j ≤ k`, does not mention the fields before it the `k`th projection
skips. -/
theorem field_skips {k j : Nat} {f : VField} (hf : c.fields[j]? = some f) (hjk : j ≤ k) :
    ∀ j' < j, c.Skipped k j' → f.type.Skips 1 (j - 1 - j') :=
  fun _ hj' h => h.2 _ _ hj' hjk hf

/-- A field's type at the parameters and the earlier projections, through its stripped type. -/
theorem field_subst_stripped {k j : Nat} {f : VField} (hf : c.fields[j]? = some f)
    (hjk : j ≤ k) (ls : List VLevel) (σ : Subst) (As : List VExpr) (g : Nat → VExpr) :
    (f.type.instL ls).subst (σ.consList (As ++ (List.range j).map g)) =
      ((c.strippedType k j f.type).instL ls).subst (σ.consList (As ++ (c.keptIdx k j).map g)) := by
  conv => lhs; rw [c.strippedType_lift' (c.field_skips hf hjk)]
  rw [instL_lift', subst_lift', lift_l_keptLift]

end VConstructor

/-! ### The block an environment records for a type -/

namespace VEnv

theorem IsTele.mono {env env' : VEnv} (henv : env ≤ env') {U Γ As}
    (H : env.IsTele U Γ As) : env'.IsTele U Γ As := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.mono henv) ih

theorem addConst_inducts {env env' : VEnv} (h : env.addConst n ci = some env') :
    env'.inducts = env.inducts := by
  unfold addConst at h; split at h <;> cases h; rfl

theorem addConstList_inducts : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' → env'.inducts = env.inducts
  | _, _, [], h => by cases h; rfl
  | _, _, _ :: _, h => by
    simp [addConstList, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConstList_inducts h2).trans (addConst_inducts h1)

theorem addConsts_inducts : ∀ {env env' : VEnv} {cis : List VDefVal},
    env.addConsts cis = some env' → env'.inducts = env.inducts
  | _, _, [], h => by cases h; rfl
  | _, _, _ :: _, h => by
    simp [addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConsts_inducts h2).trans (addConst_inducts h1)

theorem addDefEqList_inducts : ∀ {env : VEnv} {dfs : List VDefEq},
    (env.addDefEqList dfs).inducts = env.inducts
  | _, [] => rfl
  | _, _ :: _ => addDefEqList_inducts (env := addDefEq ..)

theorem addDefEqs_inducts : ∀ {env : VEnv} {cis : List VDefVal},
    (env.addDefEqs cis).inducts = env.inducts
  | _, [] => rfl
  | _, _ :: _ => addDefEqs_inducts (env := addDefEq ..)

theorem addQuot_inducts {env env' : VEnv} (h : env.addQuot = some env') :
    env'.inducts = env.inducts := by
  simp [addQuot, Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, rfl⟩ := h
  exact (addConst_inducts h4).trans <| (addConst_inducts h3).trans <|
    (addConst_inducts h2).trans (addConst_inducts h1)

theorem addBlock_inducts {env env' : VEnv} (h : env.addBlock d = some env')
    (h' : env'.inducts s = some b) :
    env.inducts s = some b ∨ b.1 = d ∧ ∃ T, d.types[b.2]? = some T ∧ T.name = s := by
  unfold addBlock at h; split at h <;> cases h
  simp only at h'
  split at h'
  · rename_i t ht
    cases h'
    obtain ⟨h1, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.1 ht
    exact .inr ⟨rfl, _, List.getElem?_eq_getElem h1, by simpa using h2⟩
  · exact .inl h'

theorem addDefEqs_le : ∀ {env : VEnv} {cis : List VDefVal}, env ≤ env.addDefEqs cis
  | _, [] => .rfl
  | _, _ :: _ => addDefEq_le.trans (addDefEqs_le (env := addDefEq ..))

theorem _root_.Lean4Lean.VDecl.WF.le {env env' : VEnv} (H : VDecl.WF env D env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact addConst_le h
  | «def» _ h => exact (addConst_le h).trans addDefEq_le
  | mutualDef _ h _ => exact (addConsts_le h).trans addDefEqs_le
  | «example» => exact .rfl
  | quot _ h =>
    simp [addQuot, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, _, h2, _, h3, _, h4, rfl⟩ := h
    exact (addConst_le h1).trans <| (addConst_le h2).trans <| (addConst_le h3).trans <|
      (addConst_le h4).trans addDefEq_le
  | induct _ _ h => exact addInduct_le h

/-- A block a well-formed environment records was added to a well-formed environment it extends,
with its types. -/
theorem WF.inducts {env : VEnv} (henv : env.WF) (h : env.inducts s = some (d, t)) :
    ∃ env₀ envT, env₀.WF ∧ d.WF env₀ ∧ env₀.addConstList d.typeConsts = some envT ∧
      envT ≤ env ∧ ∃ T, d.types[t]? = some T ∧ T.name = s := by
  obtain ⟨ds, H⟩ := henv
  induction H with
  | empty => cases h
  | @decl _ env₂ _ env₁ hD hW ih =>
    have IH : env₁.inducts s = some (d, t) → ∃ env₀ envT, env₀.WF ∧ d.WF env₀ ∧
        env₀.addConstList d.typeConsts = some envT ∧ envT ≤ env₂ ∧
        ∃ T, d.types[t]? = some T ∧ T.name = s := fun h =>
      let ⟨a, b, c, d', e, f, g⟩ := ih h
      ⟨a, b, c, d', e, f.trans hD.le, g⟩
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 => exact IH (addConst_inducts h1 ▸ h)
    | «def» _ h1 => exact IH (addConst_inducts h1 ▸ h)
    | mutualDef _ h1 _ => exact IH (addConsts_inducts h1 ▸ addDefEqs_inducts ▸ h)
    | «example» => exact IH h
    | quot _ h1 => exact IH (addQuot_inducts h1 ▸ h)
    | @induct _ d' _ hd hg h1 =>
      have h1' := h1
      simp [addInduct, Option.bind_eq_some_iff] at h1
      obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := h1
      rcases addBlock_inducts hB h with h | ⟨rfl, T, hT', rfl⟩
      · rw [addDefEqList_inducts, addConstList_inducts hR, addConstList_inducts hC,
          addConstList_inducts hT] at h
        exact IH h
      · refine ⟨_, envT, ⟨_, hW⟩, hd, hT, ?_, T, hT', rfl⟩
        exact (addConstList_le hC).trans <| (addConstList_le hR).trans <|
          addDefEqList_le.trans (addBlock_le hB)

end VEnv

namespace VConstructor
variable (c : VConstructor)
open Classical

theorem mem_keptIdx {k i j : Nat} : j ∈ c.keptIdx k i ↔ j < i ∧ ¬c.Skipped k j := by
  simp [keptIdx]

theorem keptIdx_take (k : Nat) : ∀ (i r : Nat) (h : r < (c.keptIdx k i).length),
    (c.keptIdx k i).take r = c.keptIdx k ((c.keptIdx k i)[r])
  | 0, r, h => by simp [keptIdx] at h
  | i + 1, r, h => by
    have e := c.keptIdx_succ k i
    by_cases hr : r < (c.keptIdx k i).length
    · simp only [e, List.take_append_of_le_length (Nat.le_of_lt hr),
        List.getElem_append_left hr]
      exact keptIdx_take k i r hr
    · split at e
      · rw [e] at h; simp at h; omega
      · have hr' : r = (c.keptIdx k i).length := by rw [e] at h; simp at h; omega
        subst hr'
        simp [e]

end VConstructor

theorem VInductDecl.ProjAllowed.kept {d : VInductDecl} {c : VConstructor} {ls : List VLevel}
    {k j : Nat} (H : d.ProjAllowed c ls k) (hj : j < k) (hk : ¬c.Skipped k j) :
    d.ProjAllowed c ls j := by
  intro hz
  obtain ⟨-, h2⟩ := H hz
  refine ⟨fun f hf => ?_, fun j' hj' f hf => ?_⟩
  · exact (h2 j hj f hf).resolve_right fun hu => hk ⟨hj, hu⟩
  · exact (h2 j' (by omega) f hf).imp_right fun hu i f hi hik hf => hu i f hi (by omega) hf

namespace VEnv
open VConstructor

/-- What a block's projections are typed from: its parameters, and each constructor field's
type with the fields the projection skips removed (`VConstructor.WF.projFields`), at the block's
own levels. -/
structure ProjFacts (env : VEnv) (d : VInductDecl) (c : VConstructor) : Prop where
  params : env.IsTele d.uvars [] d.params
  fields : ∀ k (f : VField), c.fields[k]? = some f →
    env.IsTele d.uvars d.params.reverse (c.keptFields k) ∧
    env.HasType d.uvars ((c.keptFields k).reverse ++ d.params.reverse)
      (c.strippedType k k f.type) (.sort f.level)

theorem ProjFacts.mono {env env' : VEnv} (henv : env ≤ env') {d c} (H : ProjFacts env d c) :
    ProjFacts env' d c :=
  ⟨H.params.mono henv, fun k f hf => (H.fields k f hf).imp (·.mono henv) (·.mono henv)⟩

/-- The facts a well-formed environment gives about the block it records for a type with a single
constructor. -/
theorem WF.projFacts {env : VEnv} (henv : env.WF) (hs : env.inducts s = some (d, t))
    (ht : d.types[t]? = some T) (hc : T.ctors = [c]) : ProjFacts env d c := by
  obtain ⟨env₀, envT, h₀, hd, hT, hle, T', hT', -⟩ := henv.inducts hs
  cases ht.symm.trans hT'
  have hcW := ((hd.ctors envT hT T (List.mem_of_getElem? ht)).2 c (by simp [hc])).projFields
  exact ⟨(hd.params.mono (addConstList_le hT)).mono hle,
    fun k f hf => (hcW k f hf).imp (·.mono hle) (·.mono hle)⟩

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {s : Name} {d : VInductDecl} {t : Nat}
  {T : VInductiveType} {c : VConstructor} {ls : List VLevel} {As As' I I' : List VExpr}
  {x x' : VExpr}

/-- The parameters and the projections the `k`th projection does not skip, at two terms: arguments
for the parameters and the kept fields. -/
theorem keptSubstEq (hF : ProjFacts env d c) (hls : ∀ l ∈ ls, l.WF U)
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As')
      (d.params.map (·.instL ls)).reverse)
    {k : Nat} {f : VField} (hf : c.fields[k]? = some f) (hP : d.ProjAllowed c ls k)
    (ih : ∀ j < k, ∀ fj : VField, c.fields[j]? = some fj → d.ProjAllowed c ls j →
      env.IsDefEq U Γ (.proj s j x) (.proj s j x') (c.projType ls s j As x)) :
    Ctx.SubstEq env U Γ
      (Subst.dflt.consList (As ++ (c.keptIdx k k).map (.proj s · x)))
      (Subst.dflt.consList (As' ++ (c.keptIdx k k).map (.proj s · x')))
      (((c.keptFields k).map (·.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) := by
  have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  have hFt := (hF.fields k f hf).1.instL hls
  simp only [List.map_reverse] at hFt
  rw [Subst.consList_append, Subst.consList_append]
  refine Ctx.SubstEq.ofGetElemDF W (c.keptIdx k k).length
    (as := (c.keptIdx k k).map (.proj s · x)) (bs := (c.keptIdx k k).map (.proj s · x'))
    (by simp) hFt (by simp [keptFields_eq]) (by simp [keptFields_eq]) fun r h h' h'' => ?_
  simp only [List.length_map] at h
  have hj := List.getElem_mem h
  obtain ⟨hjk, hjs⟩ := (c.mem_keptIdx).1 hj
  generalize hj' : (c.keptIdx k k)[r] = j at hjk hjs
  have hfj := List.getElem?_eq_getElem (Nat.lt_trans hjk hk)
  generalize c.fields[j] = fj at hfj
  have := ih j hjk fj hfj (hP.kept hjk hjs)
  simp only [List.getElem_map, hj', keptFields_eq, hfj, Option.map_some, Option.getD_some,
    ← List.map_take, keptIdx_take _ _ _ _ h, ← Subst.consList_append]
  rwa [VConstructor.projType, hfj, Option.map_some, Option.getD_some, VExpr.projs,
    c.field_subst_stripped hfj (Nat.le_of_lt hjk)] at this

theorem projType_eq {k : Nat} {f : VField} (hf : c.fields[k]? = some f) (ls : List VLevel)
    (As : List VExpr) (x : VExpr) :
    c.projType ls s k As x = ((c.strippedType k k f.type).instL ls).subst
      (Subst.dflt.consList (As ++ (c.keptIdx k k).map (.proj s · x))) := by
  rw [← c.field_subst_stripped hf (Nat.le_refl _)]
  simp [VConstructor.projType, hf, VExpr.projs]

/-- Projections of definitionally equal terms of a type with a single constructor, at
definitionally equal parameters, are definitionally equal, and so are their types. -/
theorem projCongr (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T) (hc : T.ctors = [c])
    (hF : ProjFacts env d c) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (hA' : As'.length = d.params.length) (hI' : I'.length = T.indices.length)
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As')
      (d.params.map (·.instL ls)).reverse)
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u))
    (hx : env.IsDefEq U Γ x x' (.appN (.const s ls) (As ++ I))) :
    ∀ k (f : VField), c.fields[k]? = some f → d.ProjAllowed c ls k →
      env.IsDefEq U Γ (c.projType ls s k As x) (c.projType ls s k As' x')
        (.sort (f.level.inst ls)) ∧
      env.IsDefEq U Γ (.proj s k x) (.proj s k x') (c.projType ls s k As x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro f hf hP
  have W2 := keptSubstEq hF hls W hf hP fun j hj fj hfj hPj => (ih j hj fj hfj hPj).2
  have hFk := (hF.fields k f hf).2.instL hls
  simp only [List.map_append, List.map_reverse] at hFk
  have H := IsDefEq.substDF henv W2.wf hΓ W2 hFk
  rw [← projType_eq hf, ← projType_eq hf] at H
  exact ⟨H, .projDF hs ht hc hf hls hlen hA hI hA' hI' hS hx hP H⟩

/-- The types of projections of definitionally equal terms, at definitionally equal parameters
and equivalent levels, are definitionally equal. -/
theorem projType_congr (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T) (hc : T.ctors = [c])
    (hF : ProjFacts env d c) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls')
    (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (hA' : As'.length = d.params.length) (hI' : I'.length = T.indices.length)
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As')
      (d.params.map (·.instL ls)).reverse)
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u))
    (hx : env.IsDefEq U Γ x x' (.appN (.const s ls) (As ++ I)))
    {k : Nat} {f : VField} (hf : c.fields[k]? = some f) (hP : d.ProjAllowed c ls k) :
    env.IsDefEq U Γ (c.projType ls s k As x) (c.projType ls' s k As' x')
      (.sort (f.level.inst ls)) := by
  have W2 := keptSubstEq hF hls W hf hP fun j _ fj hfj hPj =>
    (projCongr henv hΓ hs ht hc hF hls hlen hA hI hA' hI' W hS hx j fj hfj hPj).2
  obtain ⟨hFt, hFk⟩ := hF.fields k f hf
  have hΓk := hFt.onCtx (by simpa using hF.params.onCtx trivial)
  have H := IsDefEq.instL_r henv hΓk hls hls' heq hFk
  simp only [List.map_append, List.map_reverse] at H
  have H := IsDefEq.substDF henv W2.wf hΓ W2 H
  rw [← projType_eq hf, ← projType_eq hf] at H
  exact H

end
end VEnv

end Lean4Lean

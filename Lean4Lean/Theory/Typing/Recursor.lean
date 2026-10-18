import Lean4Lean.Theory.Typing.InductiveEnv

/-!
# The recursor's type is well typed

`RecFacts` collects what the recursor is built from, typed in the environment with the block's
types and constructors at the recursor's levels; `recFacts` derives it from `VInductDecl.WF`.
From it, `recType_isType` types each recursor binder by binder: the motives
(`motives_isTele`), the minor premises (`minors_isTele`, from `minor_ih` and `minor_concl`), the
indices and major premise, and the conclusion.

Each piece is typed by moving a judgment from the context it was stated in (the parameters, the
fields before it, a recursive field's binders) to the context the recursor uses, by a lift
(`Ctx.SubstEq.ofLift'`), and by instantiating a telescope with arguments
(`HasType.appN_substT`, `HasType.appN_invT`); the remaining work is equalities of substitutions,
which `subst_ext` decides by cases on the variable.
-/

namespace Lean4Lean
open VExpr

theorem VLevel.params_inst {ls : List VLevel} {n} (h : ls.length = n) :
    (VLevel.params n).map (VLevel.inst ls) = ls := by
  subst h; apply List.ext_getElem (by simp)
  intro i h1 h2; simp [VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD, h2]

namespace VExpr

theorem liftN_foralls (n : Nat) : ∀ (As : List VExpr) (B : VExpr) (k : Nat),
    (VExpr.foralls As B).liftN n k = .foralls (liftTele n As k) (B.liftN n (k + As.length))
  | [], B, k => by simp [liftTele]
  | A :: As, B, k => by
    simp only [foralls_cons, liftN, liftTele, liftN_foralls n As B (k + 1), List.length_cons]
    rw [Nat.add_right_comm k 1, Nat.add_assoc]

theorem instL_foralls (ls : List VLevel) : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.foralls As B).instL ls = .foralls (As.map (·.instL ls)) (B.instL ls)
  | [], _ => rfl
  | _ :: As, B => by simp [instL, instL_foralls ls As B]

theorem instL_bvars (ls : List VLevel) (n j : Nat) : (bvars n j).map (·.instL ls) = bvars n j := by
  simp [bvars, instL]

theorem bvars_liftN (n j k : Nat) : (bvars n j).map (·.liftN k) = bvars n (j + k) := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  congr 1; funext a; simp; omega

theorem bvars_liftN_hi (n j k c : Nat) (h : c ≤ j) :
    (bvars n j).map (·.liftN k c) = bvars n (j + k) := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  congr 1; funext a; simp; split <;> omega

theorem bvars_subst_ofLift (n j : Nat) (ρ : Lift) :
    (bvars n j).map (·.subst (.ofLift ρ)) = (List.range n).reverse.map fun i => .bvar (ρ.liftVar (i + j)) := by
  simp [bvars]

theorem bvars_map_subst (σ : Subst) (n j : Nat) :
    (bvars n j).map (·.subst σ) = (List.range n).reverse.map fun i => σ (i + j) := by
  simp [bvars]

theorem bvars_subst_skipN (n j a : Nat) :
    (bvars n j).map (·.subst (.ofLift (.skipN .refl a))) = bvars n (j + a) := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, Subst.ofLift_apply,
    Lift.liftVar_skipN, Lift.liftVar]
  apply List.map_congr_left; intro i _; congr 1; omega

end VExpr

namespace VInductDecl
variable {d : VInductDecl}

theorem recLevels_length : d.recLevels.length = d.uvars := by
  unfold recLevels; split <;> simp [VLevel.params]

theorem recLevels_WF : ∀ l ∈ d.recLevels, l.WF d.recUVars := by
  unfold recLevels recUVars
  split
  · simp [VLevel.WF]
  · exact VLevel.params_wf

theorem motiveLevel_WF : d.motiveLevel.WF d.recUVars := by
  unfold motiveLevel recUVars; split <;> simp [VLevel.WF]

theorem params_instL_recLevels : (VLevel.params d.uvars).map (VLevel.inst d.recLevels) = d.recLevels :=
  VLevel.params_inst recLevels_length

theorem mem_ctors_iff {j c} : (j, c) ∈ d.ctors ↔ ∃ T, d.types[j]? = some T ∧ c ∈ T.ctors := by
  simp only [ctors, List.mem_flatten, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨_, ⟨⟨T, i⟩, hT, rfl⟩, hc⟩
    obtain ⟨c', hc', ⟨⟩⟩ := List.mem_map.1 hc
    exact ⟨T, by simpa using hT, hc'⟩
  · rintro ⟨T, hT, hc⟩
    exact ⟨_, ⟨⟨T, j⟩, by simpa using hT, rfl⟩, List.mem_map.2 ⟨c, hc, rfl⟩⟩

theorem FieldsWF.tele {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    env.IsTele d.uvars Γ (fs.map (·.type)) ∧ env.TeleDefEq d.uvars Γ Ds (fs.map (·.type)) := by
  induction H with
  | nil => exact ⟨.nil, .nil⟩
  | cons h1 h2 _ _ _ _ _ ih => exact ⟨.cons ⟨_, h2⟩ ih.1, .cons h1 ih.2⟩

theorem FieldsWF.recArg {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i f, fs[i]? = some f →
      d.RecArgWF env (((fs.take i).map (·.type)).reverse ++ Γ) (k + i) f := by
  induction H with
  | nil => simp
  | cons _ _ _ _ _ h6 _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using h6
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons, Nat.add_right_comm, Nat.add_assoc] using this

theorem FieldsWF.length {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    Ds.length = fs.length := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

theorem FieldsWF.defeq {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i D f, Ds[i]? = some D → fs[i]? = some f →
      env.IsDefEqU d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) D f.type := by
  induction H with
  | nil => simp
  | cons h1 _ _ _ _ _ _ ih =>
    intro i D f hD hf
    cases i with
    | zero => simp at hD hf; subst hD hf; simpa using h1
    | succ i =>
      have := ih i D f (by simpa using hD) (by simpa using hf)
      simpa [List.take_succ_cons] using this

theorem FieldsWF.level {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i f, fs[i]? = some f →
      env.HasType d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) f.type (.sort f.level) := by
  induction H with
  | nil => simp
  | cons _ h2 _ _ _ _ _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using h2
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons] using this

/-- The fields before the `k`th that are not `P`, each with those that are removed, form a
telescope over the parameters, into whose context the context of all the fields before the `k`th
lifts, provided none of them mentions an earlier field that is `P`. -/
theorem FieldsWF.keptTele {env : VEnv} (henv : env.WF) {c : VConstructor} {Ds}
    (hP : env.IsTele d.uvars [] d.params) (H : d.FieldsWF env d.params.reverse 0 Ds c.fields)
    {P : Nat → Prop} {k : Nat} (hk : k ≤ c.fields.length)
    (hskip : ∀ i < k, ¬P i → ∀ f : VField, c.fields[i]? = some f →
      ∀ j < i, P j → f.type.Skips 1 (i - 1 - j)) :
    Ctx.Lift' (VConstructor.keptLiftBy P k) ((c.keptFieldsBy P k).reverse ++ d.params.reverse)
      (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse) ∧
    env.IsTele d.uvars d.params.reverse (c.keptFieldsBy P k) := by
  have hPc : OnCtx d.params.reverse (env.IsType d.uvars) := by simpa using hP.onCtx trivial
  have htele := H.tele.1
  have hctx (i) (hi : i ≤ c.fields.length) :
      OnCtx (((c.fields.take i).map (·.type)).reverse ++ d.params.reverse) (env.IsType d.uvars) := by
    have := htele
    rw [← List.take_append_drop i c.fields, List.map_append] at this
    exact (VEnv.IsTele.append_inv this).1.onCtx hPc
  let KF (i : Nat) := (VConstructor.keptIdxBy P i).map fun j =>
    VConstructor.strippedTypeBy P j ((c.fields[j]?.map VField.type).getD default)
  have main : ∀ i ≤ k, Ctx.Lift' (VConstructor.keptLiftBy P i) ((KF i).reverse ++ d.params.reverse)
      (((c.fields.take i).map (·.type)).reverse ++ d.params.reverse) ∧
      env.IsTele d.uvars d.params.reverse (KF i) := by
    intro i
    induction i with
    | zero => intro; simp [KF, VConstructor.keptLiftBy, VConstructor.keptIdxBy]; exact ⟨.refl, .nil⟩
    | succ i ih =>
      intro hi
      obtain ⟨W, ht⟩ := ih (by omega)
      have hfi := List.getElem?_eq_getElem (l := c.fields) (i := i) (by omega)
      generalize c.fields[i] = fi at hfi
      have htake : (c.fields.take (i + 1)).map (·.type) = (c.fields.take i).map (·.type) ++ [fi.type] := by
        rw [List.take_add_one, hfi]; simp
      simp only [KF, VConstructor.keptIdxBy_succ, VConstructor.keptLiftBy_succ, htake,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons_append]
      split
      · simp only [List.append_nil]; exact ⟨.skip W, ht⟩
      · rename_i hPi
        have hlift := VConstructor.strippedTypeBy_lift' (hskip i (by omega) hPi fi hfi)
        have hty := H.level i fi hfi
        rw [hlift] at hty
        have hty' := (VEnv.HasType.weak'_iff henv (hctx i (by omega)) W (A := .sort _)).1 hty
        simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, hfi,
          Option.map_some, Option.getD_some]
        refine ⟨?_, ht.concat ⟨_, by simpa [KF] using hty'⟩⟩
        have := Ctx.Lift'.cons (A := VConstructor.strippedTypeBy P i fi.type) W
        rwa [← hlift] at this
  obtain ⟨W, ht⟩ := main k (Nat.le_refl _)
  exact ⟨by simpa [KF, VConstructor.keptFieldsBy_eq] using W,
    by simpa [KF, VConstructor.keptFieldsBy_eq] using ht⟩

/-- The kernel's checks give the constructor's `projFields` clause: each field's type, typed in
the context of the fields before it, strengthens to the context without the fields the
projection skips, since it does not mention them. -/
theorem FieldsWF.projFields {env : VEnv} (henv : env.WF) {c : VConstructor} {Ds}
    (hP : env.IsTele d.uvars [] d.params) (H : d.FieldsWF env d.params.reverse 0 Ds c.fields) :
    ∀ k (f : VField), c.fields[k]? = some f →
      env.IsTele d.uvars d.params.reverse (c.keptFields k) ∧
      env.HasType d.uvars ((c.keptFields k).reverse ++ d.params.reverse)
        (c.strippedType k k f.type) (.sort f.level) := by
  intro k f hf
  have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  have hPc : OnCtx d.params.reverse (env.IsType d.uvars) := by simpa using hP.onCtx trivial
  have hctx : OnCtx (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse)
      (env.IsType d.uvars) := by
    have := H.tele.1
    rw [← List.take_append_drop k c.fields, List.map_append] at this
    exact (VEnv.IsTele.append_inv this).1.onCtx hPc
  obtain ⟨W, ht⟩ := H.keptTele henv hP (P := c.Skipped k) (Nat.le_of_lt hk)
    fun i hi _ fi hfi => c.field_skips hfi (Nat.le_of_lt hi)
  have hty := H.level k f hf
  rw [c.strippedType_lift' (c.field_skips (k := k) hf (Nat.le_refl _))] at hty
  exact ⟨ht, (VEnv.HasType.weak'_iff henv hctx W (A := .sort _)).1 hty⟩

end VInductDecl
end Lean4Lean

namespace Lean4Lean
namespace VInductDecl
open VExpr
variable {d : VInductDecl}

/-- The pieces of a well-formed declaration the recursor is built from, typed in the environment
with its types and constructors, at the recursor's levels. `type` and `ctor` state the block's own
types and constructors as constants; `typeHead` and `ctorHead` state every type the recursors
range over, auxiliary ones included, at the parameters as variables. -/
structure RecFacts (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) : Prop where
  wf : env.WF
  params : env.IsTele U [] (d.params.map (·.instL ls))
  indices : ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (T.indices.map (·.instL ls))
  type : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.HasType U [] (.const T.name ls)
      (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
        (.sort (d.level.inst ls)))
  fields : ∀ {j : Nat} {c : VConstructor}, (j, c) ∈ d.allCtors →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (c.fields.map (·.type.instL ls))
  ctor : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.ctors →
    d.types[j]? = some T →
    c.indices.length = T.indices.length ∧
    env.HasType U [] (.const c.name ls)
      (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
        (.appN (.const T.name ls)
          (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls))))
  recArg : ∀ {j : Nat} {c : VConstructor} {k : Nat} {f : VField} {ra : VRecArg},
    (j, c) ∈ d.allCtors → c.fields[k]? = some f → f.recArg = some ra →
    ∃ T, d.allTypes[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
        (d.params.map (·.instL ls)).reverse)
      (f.type.instL ls)
      (.foralls (ra.binders.map (·.instL ls)) (T.typeApp ls
        (bvars d.params.length (k + ra.binders.length)) (ra.indices.map (·.instL ls))))
  typeHead : ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.HasType U (d.params.map (·.instL ls)).reverse (T.typeHead ls (bvars d.params.length 0))
      (.foralls (T.indices.map (·.instL ls)) (.sort (d.level.inst ls)))
  ctorHead : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.allCtors →
    d.allTypes[j]? = some T →
    c.indices.length = T.indices.length ∧
    env.HasType U (d.params.map (·.instL ls)).reverse (T.ctorHead c ls (bvars d.params.length 0))
      (.foralls (c.fields.map (·.type.instL ls))
        (T.typeApp ls (bvars d.params.length c.fields.length) (c.indices.map (·.instL ls))))

theorem _root_.Lean4Lean.VExpr.bvars_liftN_lo (n j k c : Nat) (h : n + j ≤ c) :
    (bvars n j).map (·.liftN k c) = bvars n j := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  apply List.map_congr_left; intro a ha
  simp only [List.mem_reverse, List.mem_range] at ha
  simp; omega

variable (d) in
/-- `T`'s motive type under the parameters alone: `motiveType` lifts it past the motives before
it. -/
def genMotive (ls : List VLevel) (v : VLevel) (T : VInductiveType) : VExpr :=
  .foralls (T.indices.map (·.instL ls)) <| .forallE
    (T.typeApp ls (bvars d.params.length T.indices.length) (bvars T.indices.length 0)) (.sort v)

theorem _root_.Lean4Lean.VInductiveType.typeApp_liftN (T : VInductiveType) (ls : List VLevel)
    (ps idx : List VExpr) (n k : Nat) :
    (T.typeApp ls ps idx).liftN n k = T.typeApp ls (ps.map (·.liftN n k)) (idx.map (·.liftN n k)) := by
  simp only [liftN_eq_subst, VInductiveType.typeApp_subst]

theorem _root_.Lean4Lean.VInductiveType.typeApp_lift' (T : VInductiveType) (ls : List VLevel)
    (ps idx : List VExpr) (ρ : Lift) :
    (T.typeApp ls ps idx).lift' ρ = T.typeApp ls (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) := by
  simp only [lift'_eq_subst, VInductiveType.typeApp_subst]

theorem _root_.Lean4Lean.VInductiveType.ctorApp_liftN (T : VInductiveType) (c : VConstructor)
    (ls : List VLevel) (ps fs : List VExpr) (n k : Nat) :
    (T.ctorApp c ls ps fs).liftN n k =
      T.ctorApp c ls (ps.map (·.liftN n k)) (fs.map (·.liftN n k)) := by
  simp only [liftN_eq_subst, VInductiveType.ctorApp_subst]

theorem motiveType_eq {ls v j T} : d.motiveType ls v j T = (d.genMotive ls v T).liftN j := by
  simp only [motiveType, genMotive, liftN_foralls, Nat.zero_add, List.length_map, liftN,
    VInductiveType.typeApp_liftN, bvars_liftN_hi _ _ _ _ (Nat.le_refl _), Nat.add_comm j]
  rw [bvars_liftN_lo _ _ _ _ (by simp)]

/-- A motive applied to indices and to a major premise of its type at them is a type. -/
theorem motiveApp {env : VEnv} {U ls v T Γ Δ M τ idx x}
    (hM : env.HasType U Γ M ((d.genMotive ls v T).subst τ))
    (hidx : VEnv.Ctx.SubstEq env U Γ (τ.consList idx) (τ.consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ Δ))
    (hlen : idx.length = T.indices.length)
    (hx : env.HasType U Γ x (T.typeApp ls ((bvars d.params.length 0).map (·.subst τ)) idx)) :
    env.HasType U Γ (.app (.appN M idx) x) (.sort v) := by
  have h1 := VEnv.HasType.appN_substT (As := T.indices.map (·.instL ls)) hM (by simp [hlen]) hidx
  simp only [subst, VInductiveType.typeApp_subst] at h1
  rw [← hlen, subst_bvars_consList, show bvars d.params.length idx.length =
    bvars d.params.length (0 + idx.length) by rw [Nat.zero_add], subst_bvars_consList_ge] at h1
  exact h1.app hx


theorem _root_.Lean4Lean.Ctx.Lift'.skipN_append {ρ : Lift} {Γ Γ' : List VExpr} (W : Ctx.Lift' ρ Γ Γ') :
    ∀ As : List VExpr, Ctx.Lift' (ρ.skipN As.length) Γ (As ++ Γ')
  | [] => W
  | _ :: As => .skip (Ctx.Lift'.skipN_append W As)

theorem getElem_motiveTypes {ls v} {j : Nat} {T : VInductiveType} (hj : d.allTypes[j]? = some T) :
    ∃ h, (d.motiveTypes ls v)[j]'h = d.motiveType ls v j T := by
  have hlt : j < d.allTypes.length := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨by simp [motiveTypes, hlt], ?_⟩
  simp only [motiveTypes, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.1 hj).2]

@[simp] theorem length_motiveTypes {ls v} : (d.motiveTypes ls v).length = d.allTypes.length := by
  simp [motiveTypes]

theorem _root_.Lean4Lean.Lift.liftVar_consN {ρ : Lift} :
    ∀ {k i : Nat}, (ρ.consN k).liftVar i = if i < k then i else ρ.liftVar (i - k) + k
  | 0, i => by simp
  | k + 1, 0 => by simp
  | k + 1, i + 1 => by
    simp only [Lift.consN, Lift.liftVar, Lift.liftVar_consN (k := k) (i := i)]
    split <;> split <;> first | omega | (simp; omega)

theorem _root_.Lean4Lean.VExpr.Subst.consList_bvars_apply (σ : Subst) (n k i : Nat) :
    σ.consList (bvars n k) i = if i < n then .bvar (i + k) else σ (i - n) := by
  rw [Subst.consList_bvars]

theorem _root_.Lean4Lean.VExpr.Subst.consList_lift_r (ρ : Lift) :
    ∀ (σ : Subst) (as : List VExpr),
      (σ.consList as).lift_r ρ = (σ.lift_r ρ).consList (as.map (·.lift' ρ))
  | σ, [] => rfl
  | σ, a :: as => by
    show ((σ.cons a).consList as).lift_r ρ = _
    rw [VExpr.Subst.consList_lift_r ρ (σ.cons a) as]
    show _ = ((σ.lift_r ρ).cons (a.lift' ρ)).consList _
    congr 1; funext i; cases i <;> rfl

/-- Two substitutions agree, by cases on the variable. -/
macro "subst_ext" : tactic => `(tactic| (
  funext i
  simp [Subst.consList_append, Subst.consList_bvars_apply, Lift.liftVar_skipN,
    Lift.liftVar_consN, Lift.liftVar_comp, Subst.lift_r, Subst.lift_l, Subst.comp, liftVar]
  (repeat' split) <;> (try simp only [VExpr.bvar.injEq]) <;> omega))

theorem _root_.Lean4Lean.VExpr.closed_subst {env : VEnv} {U e A} (henv : env.Ordered)
    (h : env.HasType U [] e A) (σ : Subst) : A.subst σ = A := by
  have ⟨_, hA⟩ := VEnv.IsDefEq.isType henv (Γ := []) trivial h
  exact (hA.closedN henv trivial).subst_eq Subst.Fixes.zero

theorem reseat_eq_subst (e : VExpr) (a k m b l : Nat) (h : k ≤ m) :
    e.reseat a k m b l =
      e.subst (.ofLift (.consN (.skipN (.consN (.skipN .refl a) k) (m - k + b)) l)) := by
  simp only [reseat]
  rw [liftN_eq_subst, liftN_eq_subst, subst_subst]; congr 1; funext i
  simp [Subst.comp, Lift.liftVar_skipN, Lift.liftVar_consN]
  (repeat' split) <;> omega

theorem _root_.Lean4Lean.VExpr.liftTele_append (n : Nat) : ∀ (As Bs : List VExpr) (k : Nat),
    liftTele n (As ++ Bs) k = liftTele n As k ++ liftTele n Bs (k + As.length)
  | [], _, _ => rfl
  | A :: As, Bs, k => by
    simp only [List.cons_append, liftTele, liftTele_append n As Bs (k + 1), List.length_cons]
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem _root_.Lean4Lean.VExpr.liftTele'_eq_zipIdx : ∀ (ρ : Lift) (As : List VExpr),
    liftTele' ρ As = As.zipIdx.map fun (A, i) => A.lift' (ρ.consN i)
  | _, [] => rfl
  | ρ, A :: As => by
    simp only [liftTele', List.zipIdx_cons, List.map_cons, Lift.consN, Nat.zero_add]
    rw [liftTele'_eq_zipIdx ρ.cons As, List.zipIdx_succ, List.map_map]
    congr 1; apply List.map_congr_left; rintro ⟨B, i⟩ _
    simp only [Function.comp_apply]
    rw [show ρ.cons = ρ.consN 1 from rfl, Lift.consN_consN, Nat.add_comm]

theorem _root_.Lean4Lean.VEnv.IsTele.getElem {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    ∀ i (h : i < As.length), env.IsType U ((As.take i).reverse ++ Γ) As[i]
  | _, _ :: _, .cons hA _, 0, _ => hA
  | _, _ :: _, .cons _ t, i + 1, h => by
    simpa [List.take_succ_cons] using VEnv.IsTele.getElem t i (by simpa using h)

/-- A type the recursors range over, at parameters given by a substitution and at indices
instantiating its index telescope. -/
theorem RecFacts.typeApp_typing {env : VEnv} {U : Nat} {ls : List VLevel} (hF : d.RecFacts env U ls)
    {t : Nat} {T : VInductiveType} (ht : d.allTypes[t]? = some T) {Γ : List VExpr} {ρ : Lift}
    {idx : List VExpr} (Wl : Ctx.Lift' ρ (d.params.map (·.instL ls)).reverse Γ)
    (W : VEnv.Ctx.SubstEq env U Γ ((Subst.ofLift ρ).consList idx) ((Subst.ofLift ρ).consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    (hlen : idx.length = T.indices.length) :
    env.HasType U Γ (T.typeApp ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ))) idx)
      (.sort (d.level.inst ls)) := by
  have h1 := (hF.typeHead ht).weak' hF.wf.ordered Wl
  rw [lift'_eq_subst, lift'_eq_subst, VInductiveType.typeHead_subst] at h1
  have h2 := VEnv.HasType.appN_substT (Δ := (d.params.map (·.instL ls)).reverse) h1
    (by simp [hlen]) W
  rw [VInductiveType.typeApp_eq]; exact h2

/-- A constructor the recursors' minor premises range over, at parameters given by a substitution
and at fields instantiating its field telescope. -/
theorem RecFacts.ctorApp_typing {env : VEnv} {U : Nat} {ls : List VLevel} (hF : d.RecFacts env U ls)
    {j : Nat} {c : VConstructor} {T : VInductiveType} (hc : (j, c) ∈ d.allCtors)
    (hj : d.allTypes[j]? = some T) {Γ : List VExpr} {ρ : Lift} {fs : List VExpr}
    (Wl : Ctx.Lift' ρ (d.params.map (·.instL ls)).reverse Γ)
    (W : VEnv.Ctx.SubstEq env U Γ ((Subst.ofLift ρ).consList fs) ((Subst.ofLift ρ).consList fs)
      ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    (hlen : fs.length = c.fields.length) :
    env.HasType U Γ (T.ctorApp c ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ))) fs)
      (T.typeApp ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ)))
        ((c.indices.map (·.instL ls)).map (·.subst ((Subst.ofLift ρ).consList fs)))) := by
  have h1 := (hF.ctorHead hc hj).2.weak' hF.wf.ordered Wl
  rw [lift'_eq_subst, lift'_eq_subst, VInductiveType.ctorHead_subst] at h1
  have h2 := VEnv.HasType.appN_substT (Δ := (d.params.map (·.instL ls)).reverse) h1
    (by simp [hlen]) W
  rw [VInductiveType.typeApp_subst, ← hlen, show bvars d.params.length fs.length =
    bvars d.params.length (0 + fs.length) by rw [Nat.zero_add], subst_bvars_consList_ge] at h2
  rw [VInductiveType.ctorApp_eq]; exact h2

/-- The indices of a well-formed application of a type the recursors range over instantiate its
index telescope. -/
theorem RecFacts.typeApp_inv {env : VEnv} {U : Nat} {ls : List VLevel} (hF : d.RecFacts env U ls)
    {t : Nat} {T : VInductiveType} (ht : d.allTypes[t]? = some T) {Γ : List VExpr} {τ : Subst}
    {idx : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (W : VEnv.Ctx.SubstEq env U Γ τ τ (d.params.map (·.instL ls)).reverse)
    (hwf : VExpr.WF env U Γ (T.typeApp ls ((bvars d.params.length 0).map (·.subst τ)) idx))
    (hlen : idx.length = T.indices.length) :
    VEnv.Ctx.SubstEq env U Γ (τ.consList idx) (τ.consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) := by
  have h1 := (hF.typeHead ht).subst hF.wf.ordered W hΓ
  rw [VInductiveType.typeHead_subst] at h1
  rw [VInductiveType.typeApp_eq] at hwf
  exact VEnv.HasType.appN_invT hF.wf hΓ h1 W (hF.indices ht) hwf (by simp [hlen])

theorem ctorAppAt_eq {j : Nat} {T : VInductiveType} (hj : d.allTypes[j]? = some T)
    (c : VConstructor) (ls : List VLevel) (ps fs : List VExpr) :
    d.ctorAppAt j c ls ps fs = T.ctorApp c ls ps fs := by
  simp [ctorAppAt, hj]

section
variable {U : Nat} {ls : List VLevel} {v : VLevel}
set_option hygiene false
local notation "𝐔" => U
local notation "𝐥" => ls
local notation "𝐯" => v
local notation "𝐏" => (d.params.map (·.instL ls))
local notation "𝐌" => (d.motiveTypes ls v)
local notation "𝐧" => d.params.length
local notation "𝐓" => d.allTypes.length
local notation "𝐂" => d.allCtors.length
local notation "𝐅" => (c.fields.map (·.type.instL ls))
local notation "𝐦" => c.fields.length
local notation "𝐮" => c.recFields.length

/-- A motive, as a variable below the binders `Δ`. -/
theorem motive_var {env : VEnv} {t : Nat} {T : VInductiveType} (ht : d.allTypes[t]? = some T)
    (Δ : List VExpr) :
    env.HasType 𝐔 (Δ ++ 𝐌.reverse ++ 𝐏.reverse) (.bvar (Δ.length + (𝐓 - 1 - t)))
      ((d.genMotive 𝐥 𝐯 T).subst (.ofLift (.skipN .refl (Δ.length + 𝐓)))) := by
  obtain ⟨htlt', hMt⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) ht
  have htlt : t < 𝐓 := (List.getElem?_eq_some_iff.1 ht).1
  have h2 := Lookup.append_left Δ (Lookup.reverse_append 𝐌 (Γ := 𝐏.reverse) t htlt')
  rw [hMt, motiveType_eq, liftN_liftN, liftN_liftN, length_motiveTypes] at h2
  rw [show t + (𝐓 - t + Δ.length) = Δ.length + 𝐓 by omega, liftN_eq_subst] at h2
  simpa using VEnv.HasType.bvar (env := env) (U := 𝐔) h2

/-- The context of a minor premise's body, as a lift of the context of its first `k'` fields. -/
theorem fieldsLift {c : VConstructor} {q k' : Nat} (Qs' Extra : List VExpr) (hq : Qs'.length = q)
    (hk' : k' ≤ 𝐦) :
    Ctx.Lift' (.skipN (.consN (.skipN .refl (𝐓 + q)) k') (𝐦 - k' + Extra.length))
      (((c.fields.take k').map (·.type.instL 𝐥)).reverse ++ 𝐏.reverse)
      (Extra.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
  have h1 : Ctx.Lift' (.skipN .refl (𝐓 + q)) 𝐏.reverse (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) (Qs'.reverse ++ 𝐌.reverse)
    simpa [hq, Nat.add_comm] using this
  have h2 := Ctx.Lift'.tele ((c.fields.take k').map (·.type.instL 𝐥)) h1
  have h3 := Ctx.Lift'.skipN_append h2
    (Extra.reverse ++ (liftTele (𝐓 + q) ((c.fields.drop k').map (·.type.instL 𝐥)) k').reverse)
  have hF : 𝐅 = (c.fields.take k').map (·.type.instL 𝐥) ++ (c.fields.drop k').map (·.type.instL 𝐥) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hF, liftTele_append]
  simp only [List.length_append, List.length_reverse, List.length_map, Nat.zero_add,
    List.length_drop, List.length_take, Nat.min_eq_left hk', liftTele_eq_liftTele',
    List.reverse_append, List.append_assoc, Lift.consN, length_liftTele'] at h3 ⊢
  rwa [Nat.add_comm Extra.length] at h3

/-- A constructor applied to the parameters and its fields, as variables below `IHs`: its type at
its indices, which instantiate the index telescope of its type. -/
theorem ctor_typing {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.allCtors) (hj : d.allTypes[j]? = some Tj) {q : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) :
    c.indices.length = Tj.indices.length ∧
    env.HasType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse) (d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length)) (bvars 𝐦 IHs.length))
      (Tj.typeApp 𝐥 ((bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)))))
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0)) ∧
    VEnv.Ctx.SubstEq env 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
        𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Tj.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
  have henv := hF.wf.ordered
  obtain ⟨hidxlen, hcty⟩ := hF.ctorHead hc hj
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hPc : OnCtx (𝐅.reverse ++ 𝐏.reverse) (env.IsType 𝐔) := (hF.fields hc).onCtx hPP
  have h1 : Ctx.Lift' (.skipN .refl (𝐓 + q)) 𝐏.reverse (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) (Qs'.reverse ++ 𝐌.reverse)
    simpa [hq, Nat.add_comm] using this
  have hWc : Ctx.Lift' (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) (𝐅.reverse ++ 𝐏.reverse)
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have h3 := Ctx.Lift'.skipN_append (Ctx.Lift'.tele 𝐅 h1) IHs.reverse
    simpa [liftTele_eq_liftTele'] using h3
  have hWP : Ctx.Lift' (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)) 𝐏.reverse
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have h3 := Ctx.Lift'.skipN_append h1 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse)
    simpa [Lift.skipN_skipN, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h3
  have hρc : (Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
      (bvars 𝐦 IHs.length) =
      .ofLift (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) := by subst_ext
  have hidx_eq : c.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0) =
      (c.indices.map (·.instL 𝐥)).map (·.subst (.ofLift (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length))) := by
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_refl _)]
  have hps : (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)))) =
      bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length) := by
    rw [bvars_subst_skipN]; congr 1; omega
  have hx := hF.ctorApp_typing hc hj hWP (fs := bvars 𝐦 IHs.length)
    (by rw [hρc]; exact VEnv.Ctx.SubstEq.ofLift' henv hWc hPc) (by simp)
  rw [hρc, ← hidx_eq] at hx
  rw [ctorAppAt_eq hj, ← hps]
  have hidx : VEnv.Ctx.SubstEq env 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Tj.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    have hcT := VEnv.IsDefEq.isType henv hPP hcty
    have ⟨w, hR0⟩ := (VEnv.IsType.foralls_inv henv hcT).2
    have hWm : Ctx.Lift' (.skipN .refl 𝐦) 𝐏.reverse (𝐅.reverse ++ 𝐏.reverse) := by
      simpa using Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) 𝐅.reverse
    have hτm := VEnv.Ctx.SubstEq.ofLift' henv hWm hPP
    have hinv := hF.typeApp_inv hj hPc hτm (idx := c.indices.map (·.instL 𝐥))
      (by rw [bvars_subst_skipN, Nat.zero_add]; exact ⟨_, hR0⟩) (by simp [hidxlen])
    have := VEnv.Ctx.SubstEq.weak' henv hWc hinv
    rw [Subst.consList_lift_r, show (Subst.ofLift (.skipN .refl 𝐦)).lift_r
      (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) = .ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)) by
        subst_ext] at this
    simp only [lift'_eq_subst] at this
    rwa [hidx_eq]
  exact ⟨hidxlen, hx, hidx⟩

/-- The conclusion of a minor premise: the motive at the constructor applied to its fields. -/
theorem minor_concl {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.allCtors) (hj : d.allTypes[j]? = some Tj) {q : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hu : IHs.length = 𝐮) :
    env.HasType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (.app (.appN (.bvar (𝐮 + 𝐦 + q + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 𝐮 0))
        (d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + q + 𝐦 + 𝐮)) (bvars 𝐦 𝐮)))
      (.sort 𝐯) := by
  obtain ⟨hidxlen, hx, hidx⟩ := ctor_typing (v := 𝐯) hF hc hj Qs' IHs hq
  rw [hu] at hx hidx
  have := motive_var (env := env) (U := 𝐔) (ls := 𝐥) (v := 𝐯) hj (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse)
  simp only [List.length_append, List.length_reverse, hu, length_liftTele, List.length_map,
    hq] at this
  exact motiveApp this hidx (by simp [hidxlen]) hx

local notation "𝐁" => (ra.binders.map (·.instL ls))
local notation "𝐛" => ra.binders.length
local notation "𝐊" => (((c.fields.take k).map (·.type.instL ls)).reverse ++ 𝐏.reverse)
local notation "𝐱𝐬" => (ra.binders.zipIdx.map fun (A, i) =>
  (A.instL ls).reseat (d.allTypes.length + q) k c.fields.length r i)
local notation "𝐢𝐝𝐱" => (ra.indices.map fun e =>
  (e.instL ls).reseat (d.allTypes.length + q) k c.fields.length r ra.binders.length)
local notation "ρk" => (Lift.skipN (.consN (.skipN .refl (d.allTypes.length + q)) k)
  (c.fields.length - k + r))

/-- A recursive field, over its own binders in the context of a minor premise's inductive
hypotheses: its binders form a telescope, the field applied to them has the type of its view, and
that view's indices instantiate the index telescope of its type. -/
theorem recField_typing {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    (hc : (j, c) ∈ d.allCtors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) {q r : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hr : IHs.length = r) :
    ∃ T', d.allTypes[ra.typeIdx]? = some T' ∧ ra.indices.length = T'.indices.length ∧
    env.IsTele 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse) 𝐱𝐬 ∧
    env.HasType 𝐔 (𝐱𝐬.reverse ++ (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
        𝐌.reverse ++ 𝐏.reverse)) (.appN (.bvar (𝐛 + r + (𝐦 - 1 - k))) (bvars 𝐛 0))
      (T'.typeApp 𝐥 ((bvars 𝐧 0).map
        (·.subst (.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))))) 𝐢𝐝𝐱) ∧
    VEnv.Ctx.SubstEq env 𝐔 (𝐱𝐬.reverse ++ (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++
        Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList 𝐢𝐝𝐱)
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList 𝐢𝐝𝐱)
      ((T'.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
  have henv := hF.wf.ordered
  obtain ⟨T', hT', hidxlen, hdef⟩ := hF.recArg hc hk hra
  have hkm : k < 𝐦 := (List.getElem?_eq_some_iff.1 hk).1
  have hfk : c.fields[k] = f := (List.getElem?_eq_some_iff.1 hk).2
  obtain ⟨htlt', hMt⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) hT'
  have htlt : ra.typeIdx < 𝐓 := (List.getElem?_eq_some_iff.1 hT').1
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hFt := hF.fields hc
  rw [show 𝐅 = (c.fields.take (k + 1)).map (·.type.instL 𝐥) ++
    (c.fields.drop (k + 1)).map (·.type.instL 𝐥) by rw [← List.map_append, List.take_append_drop]]
    at hFt
  obtain ⟨hFk1, -⟩ := VEnv.IsTele.append_inv hFt
  rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hkm] at hFk1
  obtain ⟨hFk, hfty⟩ := VEnv.IsTele.append_inv hFk1
  simp only [Option.toList_some, List.map_cons, List.map_nil, hfk] at hfty
  have hOK : OnCtx 𝐊 (env.IsType 𝐔) := hFk.onCtx hPP
  have ⟨w, hfty⟩ : env.IsType 𝐔 𝐊 (f.type.instL 𝐥) := by
    cases hfty with | cons h _ => exact h
  have hRty := VEnv.IsType.defeqU_l hF.wf hOK hdef ⟨_, hfty⟩
  obtain ⟨hBt, hRt⟩ := VEnv.IsType.foralls_inv henv hRty
  have hxs : (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + q) k 𝐦 r i) =
      liftTele' ρk 𝐁 := by
    rw [liftTele'_eq_zipIdx, List.zipIdx_map, List.map_map]
    apply List.map_congr_left; rintro ⟨A, i⟩ _
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_of_lt hkm), lift'_eq_subst]
  rw [hxs]
  have hWk : Ctx.Lift' ρk 𝐊 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse) := by
    simpa [hr] using fieldsLift (d := d) (ls := 𝐥) (v := 𝐯) (c := c) (k' := k) Qs' IHs hq (Nat.le_of_lt hkm)
  have hWx : Ctx.Lift' (.consN ρk 𝐛) (𝐁.reverse ++ 𝐊) ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse)) := by
    simpa using Ctx.Lift'.tele 𝐁 hWk
  have hOB : OnCtx (𝐁.reverse ++ 𝐊) (env.IsType 𝐔) := hBt.onCtx hOK
  have hfield : env.HasType 𝐔 ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      (.bvar (𝐛 + r + (𝐦 - 1 - k)))
      ((VExpr.foralls 𝐁 (T'.typeApp 𝐥
        (bvars 𝐧 (k + 𝐛)) (ra.indices.map (·.instL 𝐥)))).subst (.ofLift (.skipN ρk 𝐛))) := by
    have h0 : env.HasType 𝐔 (f.type.instL 𝐥 :: 𝐊) (.bvar 0) (f.type.instL 𝐥).lift :=
      VEnv.HasType.bvar .zero
    have h1 := VEnv.HasType.defeqU_r (Γ := f.type.instL 𝐥 :: 𝐊) hF.wf ⟨hOK, w, hfty⟩
      (hdef.weakN henv .one) h0
    have W' := fieldsLift (d := d) (ls := 𝐥) (v := 𝐯) (c := c) (k' := k + 1) Qs' (IHs ++ liftTele' ρk 𝐁) hq hkm
    rw [List.take_add_one, List.getElem?_eq_getElem hkm, hfk] at W'
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, List.length_append,
      length_liftTele', List.length_map, hr] at W'
    have h2 := h1.weak' henv W'
    have e1 : (VExpr.bvar 0).lift'
        ((Lift.consN (.skipN .refl (𝐓 + q)) (k + 1)).skipN (𝐦 - (k + 1) + (r + 𝐛)))
        = .bvar (𝐛 + r + (𝐦 - 1 - k)) := by simp [Lift.liftVar_skipN]; omega
    have e2 : ((VExpr.foralls 𝐁 (T'.typeApp 𝐥
        (bvars 𝐧 (k + 𝐛)) (ra.indices.map (·.instL 𝐥)))).liftN 1).lift'
        ((Lift.consN (.skipN .refl (𝐓 + q)) (k + 1)).skipN (𝐦 - (k + 1) + (r + 𝐛))) =
        (VExpr.foralls 𝐁 (T'.typeApp 𝐥
        (bvars 𝐧 (k + 𝐛)) (ra.indices.map (·.instL 𝐥)))).subst (.ofLift (.skipN ρk 𝐛)) := by
      rw [← lift'_consN_skipN, ← lift'_comp, lift'_eq_subst]; congr 1; subst_ext
    rw [e1, e2] at h2
    simpa only [List.append_assoc] using h2
  have heqx : (Subst.ofLift (.skipN ρk 𝐛)).consList (bvars 𝐛 0) = .ofLift (.consN ρk 𝐛) := by
    subst_ext
  have hx := VEnv.HasType.appN_substT (Δ := 𝐊) (As := 𝐁) (as := bvars 𝐛 0) hfield (by simp)
    (by rw [heqx]; exact VEnv.Ctx.SubstEq.ofLift' henv hWx hOB)
  rw [heqx] at hx
  simp only [VInductiveType.typeApp_subst] at hx
  have hidx_eq : ra.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛) =
      (ra.indices.map (·.instL 𝐥)).map (·.subst (.ofLift (.consN ρk 𝐛))) := by
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_of_lt hkm)]
  have hb_eq : (bvars 𝐧 (k + 𝐛)).map (·.subst (.ofLift (.consN ρk 𝐛))) =
      (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓)))) := by
    simp only [bvars_subst_ofLift]; congr 1; funext i
    simp [Lift.liftVar_skipN, Lift.liftVar_consN]; (repeat' split) <;> omega
  rw [hb_eq, ← hidx_eq] at hx
  have hidx : VEnv.Ctx.SubstEq env 𝐔 ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList
        (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList
        (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛))
      ((T'.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    have ⟨w', hR0⟩ := hRt
    have hWm : Ctx.Lift' (.skipN .refl (k + 𝐛)) 𝐏.reverse (𝐁.reverse ++ 𝐊) := by
      have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
        (𝐁.reverse ++ ((c.fields.take k).map (·.type.instL 𝐥)).reverse)
      simpa [Nat.min_eq_left (Nat.le_of_lt hkm), Nat.add_comm] using this
    have hτm := VEnv.Ctx.SubstEq.ofLift' henv hWm hPP
    have hinv := hF.typeApp_inv hT' hOB hτm (idx := ra.indices.map (·.instL 𝐥))
      (by rw [bvars_subst_skipN, Nat.zero_add]; exact ⟨_, hR0⟩) (by simp [hidxlen])
    have := VEnv.Ctx.SubstEq.weak' henv hWx hinv
    rw [Subst.consList_lift_r, show (Subst.ofLift (.skipN .refl (k + 𝐛))).lift_r (.consN ρk 𝐛) =
      .ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓)) by subst_ext] at this
    simp only [lift'_eq_subst] at this
    rwa [hidx_eq]
  exact ⟨T', hT', hidxlen, hBt.weak' henv hWk, hx, hidx⟩

/-- An inductive hypothesis of a minor premise: over the recursive field's own binders, the motive
at its type, applied to its indices and to the field applied to the binders. -/
theorem minor_ih {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    (hc : (j, c) ∈ d.allCtors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) {q r : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hr : IHs.length = r) :
    env.IsType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.foralls 𝐱𝐬 <| .app (.appN (.bvar (𝐛 + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx))) 𝐢𝐝𝐱)
        (.appN (.bvar (𝐛 + r + (𝐦 - 1 - k))) (bvars 𝐛 0))) := by
  obtain ⟨T', hT', hidxlen, hxs, hx, hidx⟩ := recField_typing (v := 𝐯) hF hc hk hra Qs' IHs hq hr
  refine hxs.foralls ⟨𝐯, motiveApp (v := 𝐯) ?_ hidx (by simp [hidxlen]) hx⟩
  have := motive_var (env := env) (U := 𝐔) (ls := 𝐥) (v := 𝐯) hT' (𝐱𝐬.reverse ++ IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++
    Qs'.reverse)
  simp only [List.length_append, List.length_reverse, List.length_map, List.length_zipIdx, hr,
    length_liftTele, hq, List.append_assoc] at this
  rw [show 𝐛 + (r + (𝐦 + q)) = 𝐛 + r + 𝐦 + q by omega] at this
  simpa only [List.append_assoc] using this

theorem mem_recFields {c : VConstructor} {k : Nat} {ra : VRecArg} (h : (k, ra) ∈ c.recFields) :
    ∃ f, c.fields[k]? = some f ∧ f.recArg = some ra := by
  simp only [VConstructor.recFields, List.mem_filterMap] at h
  obtain ⟨⟨f, k'⟩, hm, he⟩ := h
  cases hr : f.recArg <;> simp [hr] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨f, (List.mem_zipIdx_iff_getElem?.1 hm), hr⟩

theorem minorType_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.allCtors) (hj : d.allTypes[j]? = some Tj) {q : Nat}
    (Qs' : List VExpr) (hq : Qs'.length = q) :
    env.IsType 𝐔 (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) (d.minorType 𝐥 q j c) := by
  have henv := hF.wf.ordered
  dsimp only [minorType]
  refine VEnv.IsTele.foralls (VEnv.IsTele.append ?_ ?_) ?_
  · exact (hF.fields hc).weakN henv (.zero (Qs'.reverse ++ 𝐌.reverse) (by simp [hq, Nat.add_comm]))
  · apply VEnv.IsTele.of_getElem
    intro r hr
    have hr' : r < c.recFields.length := by simpa using hr
    have hmem := List.getElem_mem hr'
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    generalize c.recFields[r] = p at hmem ⊢
    obtain ⟨k, ra⟩ := p
    obtain ⟨f, hk, hra⟩ := mem_recFields hmem
    have := minor_ih (v := 𝐯) hF hc hk hra Qs' _ hq (List.length_take_of_le (Nat.le_of_lt hr))
    simpa only [List.append_assoc] using this
  · refine ⟨v, ?_⟩
    simp only [List.reverse_append, ← List.append_assoc]
    refine minor_concl (v := 𝐯) hF hc hj Qs' _ hq ?_
    simp

theorem genMotive_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {t : Nat}
    {T : VInductiveType} (ht : d.allTypes[t]? = some T) : env.IsType 𝐔 𝐏.reverse (d.genMotive 𝐥 𝐯 T) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hI := hF.indices ht
  have hIP : OnCtx ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) := hI.onCtx hPP
  refine hI.foralls (.forallE ?_ ⟨_, .sort hv⟩)
  have hWI : Ctx.Lift' (.skipN .refl T.indices.length) 𝐏.reverse
      ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    simpa using Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      (T.indices.map (·.instL 𝐥)).reverse
  have heq : (Subst.ofLift (.skipN .refl T.indices.length)).consList
      (bvars T.indices.length 0) = .ofLift .refl := by subst_ext
  have h := hF.typeApp_typing ht hWI (idx := bvars T.indices.length 0)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv .refl hIP) (by simp)
  rw [bvars_subst_skipN, Nat.zero_add] at h
  exact ⟨_, h⟩

theorem motives_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) :
    env.IsTele 𝐔 𝐏.reverse 𝐌 := by
  have henv := hF.wf.ordered
  apply VEnv.IsTele.of_getElem
  intro i hi
  have hi' : i < 𝐓 := by simpa using hi
  obtain ⟨_, hMi⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) (List.getElem?_eq_getElem hi')
  rw [hMi, motiveType_eq]
  exact (genMotive_isType hF hv (List.getElem?_eq_getElem hi')).weakN henv
    (.zero _ (by simp [Nat.min_eq_left (Nat.le_of_lt hi')]))

theorem minors_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) :
    env.IsTele 𝐔 (𝐌.reverse ++ 𝐏.reverse) (d.minorTypes 𝐥) := by
  apply VEnv.IsTele.of_getElem
  intro q hq
  have hq' : q < 𝐂 := by simpa [minorTypes] using hq
  have hmem := List.getElem_mem hq'
  simp only [minorTypes, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  generalize d.allCtors[q] = p at hmem ⊢
  obtain ⟨j, c⟩ := p
  obtain ⟨Tj, hj, -⟩ := VInductDecl.mem_allCtors_iff.1 hmem
  have := minorType_isType (v := 𝐯) hF hmem hj ((d.minorTypes 𝐥).take q)
    (List.length_take_of_le (Nat.le_of_lt hq))
  simpa only [List.append_assoc, minorTypes] using this

@[simp] theorem length_minorTypes {ls} : (d.minorTypes ls).length = 𝐂 := by simp [minorTypes]

/-- The recursor's indices, over its binders, lift the type's index telescope. -/
theorem recIndicesLift {i : Nat} {Ti : VInductiveType} (_hi : d.allTypes[i]? = some Ti) :
    Ctx.Lift' (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)
      ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hWI := Ctx.Lift'.tele (Ti.indices.map (·.instL 𝐥)) hW0
  simp only [List.length_map] at hWI
  simpa only [List.append_assoc] using hWI

/-- The recursor's major premise, the type applied to the parameters and indices, over the
recursor's binders and the indices. -/
theorem major_type {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {i : Nat} {Ti : VInductiveType}
    (hi : d.allTypes[i]? = some Ti) :
    env.HasType 𝐔 ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (Ti.typeApp 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0))
      (.sort (d.level.inst 𝐥)) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hIP : OnCtx ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    (hF.indices hi).onCtx hPP
  have hWP : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂 + Ti.indices.length)) 𝐏.reverse
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have heq : (Subst.ofLift (.skipN .refl (𝐓 + 𝐂 + Ti.indices.length))).consList
      (bvars Ti.indices.length 0) =
      .ofLift (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length) := by subst_ext
  have h := hF.typeApp_typing hi hWP (idx := bvars Ti.indices.length 0)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv (recIndicesLift (d := d) hi) hIP)
    (by simp)
  rwa [bvars_subst_skipN, Nat.zero_add] at h

theorem recType_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {i : Nat}
    {Ti : VInductiveType} (hi : d.allTypes[i]? = some Ti) : env.IsType 𝐔 [] (d.recType 𝐥 𝐯 i Ti) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hMs := motives_isTele hF hv
  have hQs := minors_isTele (v := 𝐯) hF
  have hI := hF.indices hi
  have hilt : i < 𝐓 := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hilt', hMi⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) hi
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hWI := Ctx.Lift'.tele (Ti.indices.map (·.instL 𝐥)) hW0
  simp only [List.length_map] at hWI
  have hIP : OnCtx ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    hI.onCtx hPP
  dsimp only [recType, recBinders]
  rw [liftTele_eq_liftTele']
  simp only [Lift.consN]
  have hTele : env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥 ++
      liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))) :=
    ((hF.params.append (by simpa using hMs)).append (by simpa using hQs)).append
      (by simpa using hI.weak' henv hW0)
  have hWI' : Ctx.Lift' (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)
      ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    simpa only [List.append_assoc] using hWI
  have hX := major_type (v := 𝐯) hF hi
  refine hTele.foralls (.forallE ?_ ?_)
  · simp only [List.reverse_append, List.append_nil, ← List.append_assoc]
    exact ⟨_, hX⟩
  · simp only [List.reverse_append, List.append_nil, ← List.append_assoc]
    have hM : env.HasType 𝐔 (Ti.typeApp 𝐥
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
        (.bvar (1 + Ti.indices.length + 𝐂 + (𝐓 - 1 - i)))
        ((d.genMotive 𝐥 𝐯 Ti).subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))) := by
      have h1 := Lookup.reverse_append 𝐌 (Γ := 𝐏.reverse) i hilt'
      have h2 := Lookup.append_left (Ti.typeApp 𝐥
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse)) h1
      rw [hMi, motiveType_eq, liftN_liftN, liftN_liftN, length_motiveTypes] at h2
      simp only [List.append_assoc, List.length_append, List.length_reverse, List.length_cons,
        length_liftTele', List.length_map, length_minorTypes, List.cons_append] at h2
      rw [show i + (𝐓 - i + (Ti.indices.length + 𝐂 + 1)) = 1 + Ti.indices.length + 𝐂 + 𝐓 by omega,
        show Ti.indices.length + 𝐂 + 1 + (𝐓 - 1 - i) = 1 + Ti.indices.length + 𝐂 + (𝐓 - 1 - i) by
          omega, liftN_eq_subst] at h2
      simpa using VEnv.HasType.bvar (env := env) (U := 𝐔) h2
    have heq2 : (Subst.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓))).consList
        (bvars Ti.indices.length 1) =
        .ofLift (.skip (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)) := by subst_ext
    have hidx := VEnv.Ctx.SubstEq.ofLift' henv (.skip hWI' (A := Ti.typeApp 𝐥
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0))) hIP
    rw [← heq2] at hidx
    have hx : env.HasType 𝐔 (Ti.typeApp 𝐥
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) (.bvar 0)
        (Ti.typeApp 𝐥 ((bvars 𝐧 0).map
          (·.subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))))
          (bvars Ti.indices.length 1)) := by
      have := VEnv.HasType.bvar (env := env) (U := 𝐔) (Lookup.zero (ty := Ti.typeApp 𝐥
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0))
        (Γ := (liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      simp only [lift, VInductiveType.typeApp_liftN, bvars_liftN] at this
      rw [show (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))) =
        bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length + 1) by
          rw [bvars_subst_skipN]; congr 1; omega]
      exact this
    exact ⟨_, motiveApp hM hidx (by simp) hx⟩

theorem bvars_subst_cons (σ : Subst) (x : VExpr) (n k : Nat) :
    (bvars n (k + 1)).map (·.subst (σ.cons x)) = (bvars n k).map (·.subst σ) := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, ← Nat.add_assoc]; rfl

/-- The recursors, as terms `rc t` of their types. -/
def RecTyped (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) (v : VLevel)
    (rc : Nat → VExpr) : Prop :=
  ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.HasType U [] (rc t) (d.recType ls v t T)

/-- A recursor applied to the parameters, motives and minor premises as variables below `Δ`, to
indices, and to a major premise at those indices: the motive at them. -/
theorem rec_app {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {rc : Nat → VExpr}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 rc) {t : Nat}
    {T : VInductiveType} (ht : d.allTypes[t]? = some T) (Δ : List VExpr) {idx : List VExpr}
    {x : VExpr}
    (hidx : VEnv.Ctx.SubstEq env 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂))).consList idx)
      ((Subst.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂))).consList idx)
      ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse))
    (hlen : idx.length = T.indices.length)
    (hx : env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) x
      (T.typeApp 𝐥
        ((bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂))))) idx)) :
    env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (.appN (rc t) (bvars (𝐧 + 𝐓 + 𝐂) Δ.length ++ idx ++ [x]))
      (.app (.appN (.bvar (Δ.length + 𝐂 + (𝐓 - 1 - t))) idx) x) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hc := hrec ht
  have hRt : env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥) :=
    (hF.params.append (by simpa using motives_isTele hF hv)).append
      (by simpa using minors_isTele (v := 𝐯) hF)
  have hRc : OnCtx ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) (env.IsType 𝐔) := by
    simpa using hRt.onCtx trivial
  have hc0 := hc.weak0 henv (Γ := Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
  rw [← closed_subst henv hc (.ofLift (.skipN .refl (𝐧 + 𝐓 + 𝐂 + Δ.length)))] at hc0
  dsimp only [recType, recBinders] at hc0
  rw [liftTele_eq_liftTele',
    show ∀ (As : List VExpr) X B, VExpr.foralls As (.forallE X B) = .foralls (As ++ [X]) B by
      intro As X B; rw [foralls_append]; rfl] at hc0
  simp only [Lift.consN] at hc0
  have hσ : (Subst.ofLift (.skipN .refl (𝐧 + 𝐓 + 𝐂 + Δ.length))).consList
      (bvars (𝐧 + 𝐓 + 𝐂) Δ.length) = .ofLift (.skipN .refl Δ.length) := by subst_ext
  have hW : Ctx.Lift' (.skipN .refl Δ.length) ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    simpa only [List.append_assoc] using Ctx.Lift'.skipN_append (Ctx.Lift'.refl
      (Γ := (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) Δ
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hI : VEnv.Ctx.SubstEq env 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)
      ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (T.indices.map (·.instL 𝐥))).reverse ++
        ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) := by
    refine VEnv.Ctx.SubstEq.extendLift henv hW0 (hF.indices ht)
      (VEnv.Ctx.SubstEq.ofLift' henv hW hRc) ?_ (by simp [hlen])
    rw [show (Subst.ofLift (.skipN .refl Δ.length)).lift_l (.skipN .refl (𝐓 + 𝐂)) =
      .ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂)) by subst_ext]
    exact hidx
  have hX := major_type (v := 𝐯) hF ht
  have hx' : env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) x
      ((T.typeApp 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + T.indices.length))
        (bvars T.indices.length 0)).subst ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)) := by
    simp only [VInductiveType.typeApp_subst]
    rw [← hlen, subst_bvars_consList, show 𝐓 + 𝐂 + idx.length = (𝐓 + 𝐂) + idx.length from rfl,
      subst_bvars_consList_ge, bvars_subst_skipN]
    rwa [bvars_subst_skipN, show 0 + (Δ.length + 𝐓 + 𝐂) = 𝐓 + 𝐂 + Δ.length by omega] at hx
  have h := VEnv.HasType.appN_substT (Δ := [])
    (As := 𝐏 ++ 𝐌 ++ d.minorTypes 𝐥 ++ liftTele' (.skipN .refl (𝐓 + 𝐂)) (T.indices.map (·.instL 𝐥)) ++
      [T.typeApp 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + T.indices.length)) (bvars T.indices.length 0)])
    (as := bvars (𝐧 + 𝐓 + 𝐂) Δ.length ++ idx ++ [x]) hc0 (by simp [hlen]; omega) (by
      rw [Subst.consList_concat, Subst.consList_append, hσ]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, List.append_nil]
      refine .cons ?_ (by simpa only [List.append_assoc] using hX) ?_
      · simpa only [List.append_assoc, Subst.cons_tail] using hI
      · have := hx'
        simp only [List.append_assoc] at this
        simp only [Subst.cons_tail, Subst.cons_head]
        exact this)
  rw [Subst.consList_concat, Subst.consList_append, hσ] at h
  simp only [subst, subst_appN] at h
  have e1 : ((Subst.ofLift (.skipN .refl Δ.length)).consList idx).cons x
      (1 + T.indices.length + 𝐂 + (𝐓 - 1 - t)) = .bvar (Δ.length + 𝐂 + (𝐓 - 1 - t)) := by
    rw [show 1 + T.indices.length + 𝐂 + (𝐓 - 1 - t) = (𝐂 + (𝐓 - 1 - t) + idx.length) + 1 by
      omega]
    show (Subst.ofLift (.skipN .refl Δ.length)).consList idx (𝐂 + (𝐓 - 1 - t) + idx.length) = _
    rw [Subst.consList_ge]; simp [Lift.liftVar_skipN]; omega
  rw [e1, bvars_subst_cons, ← hlen, subst_bvars_consList] at h
  exact h

theorem _root_.Lean4Lean.VExpr.bvars_append (a b k : Nat) :
    bvars a (b + k) ++ bvars b k = bvars (a + b) k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [bvars, List.getElem_append, List.length_map, List.length_reverse, List.length_range,
    List.getElem_map, List.getElem_reverse, List.getElem_range]
  split <;> (congr 1; omega)

theorem recBinders_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) :
    env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥) :=
  (hF.params.append (by simpa using motives_isTele hF hv)).append
    (by simpa using minors_isTele (v := 𝐯) hF)

/-- The left side of an iota rule: the recursor at a constructor, over the recursor's binders and
the constructor's fields. -/
theorem iota_lhs {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {j : Nat}
    {c : VConstructor} {Tj : VInductiveType} (hc : (j, c) ∈ d.allCtors) (hj : d.allTypes[j]? = some Tj) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.appN (d.recConst recLs j) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐓 (𝐂 + 𝐦) ++
        bvars 𝐂 𝐦 ++ c.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0) ++
        [d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + 𝐦)) (bvars 𝐦 0)]))
      (.app (.appN (.bvar (𝐦 + 𝐂 + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0))
        (d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + 𝐦)) (bvars 𝐦 0))) := by
  obtain ⟨hidxlen, hx, hidx⟩ := ctor_typing (v := 𝐯) hF hc hj (d.minorTypes 𝐥) [] (q := 𝐂) (by simp)
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at hx hidx
  have := rec_app hF hv hrec hj (liftTele (𝐓 + 𝐂) 𝐅).reverse
    (idx := c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0)
    (x := d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + 𝐦)) (bvars 𝐦 0))
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hidx) (by simp [hidxlen])
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx)
  simp only [List.length_reverse, length_liftTele, List.length_map] at this
  have hb : bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐓 (𝐂 + 𝐦) ++ bvars 𝐂 𝐦 = bvars (𝐧 + 𝐓 + 𝐂) 𝐦 := by
    rw [show 𝐓 + 𝐂 + 𝐦 = 𝐓 + (𝐂 + 𝐦) by omega, bvars_append, bvars_append]
  rw [hb]
  exact this

/-- The argument an iota rule gives a minor premise for a recursive field: the recursor at the
field, over the field's own binders. -/
theorem iota_ih {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {j : Nat}
    {c : VConstructor} (hc : (j, c) ∈ d.allCtors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
        (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + 𝐛) ++
          bvars 𝐓 (𝐂 + 𝐦 + 𝐛) ++ bvars 𝐂 (𝐦 + 𝐛) ++
          ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛))
        (.appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0)))
      (.foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
        (.appN (.bvar (𝐛 + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx)))
          (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛))
        (.appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0))) := by
  obtain ⟨T', hT', hidxlen, hxs, hx, hidx⟩ :=
    recField_typing (v := 𝐯) hF hc hk hra (d.minorTypes 𝐥) [] (q := 𝐂) (r := 0) (by simp) rfl
  simp only [List.reverse_nil, List.nil_append, Nat.add_zero] at hxs hx hidx
  refine hxs.lams ?_
  have := rec_app hF hv hrec hT'
    ((ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i).reverse ++
      (liftTele (𝐓 + 𝐂) 𝐅).reverse)
    (idx := ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛)
    (x := .appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0))
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hidx) (by simp [hidxlen])
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx)
  simp only [List.length_append, List.length_reverse, List.length_map, List.length_zipIdx,
    length_liftTele] at this
  have hb : bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + 𝐛) ++ bvars 𝐓 (𝐂 + 𝐦 + 𝐛) ++ bvars 𝐂 (𝐦 + 𝐛) =
      bvars (𝐧 + 𝐓 + 𝐂) (𝐛 + 𝐦) := by
    rw [show 𝐓 + 𝐂 + 𝐦 + 𝐛 = 𝐓 + (𝐂 + 𝐦 + 𝐛) by omega, bvars_append,
      show 𝐂 + 𝐦 + 𝐛 = 𝐂 + (𝐦 + 𝐛) by omega, bvars_append, Nat.add_comm 𝐦]
  rw [hb, ← appN_append_singleton]
  simpa only [List.append_assoc] using this

theorem _root_.Lean4Lean.VExpr.liftTele'_liftTele' : ∀ (ρ ρ' : Lift) (As : List VExpr),
    liftTele' ρ (liftTele' ρ' As) = liftTele' (ρ'.comp ρ) As
  | _, _, [] => rfl
  | ρ, ρ', A :: As => by
    simp only [liftTele', ← lift'_comp, liftTele'_liftTele' ρ.cons ρ'.cons As]; rfl

/-- Instantiating the inductive hypotheses before a minor premise's `r`th one, and lifting its
fields past the minor premises after it, moves a term reseated for the minor premise to one
reseated for the iota rule. -/
theorem reseat_subst_iota (e : VExpr) {a k m r i C q : Nat} (L : List VExpr) (hL : L.length = r)
    (hk : k ≤ m) (hqC : q ≤ C) :
    (e.reseat (a + q) k m r i).subst
      ((((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i) =
      e.reseat (a + C) k m 0 i := by
  rw [show (Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0) =
    .ofLift (.consN (.skipN .refl (C - q)) m) by subst_ext]
  rw [reseat_eq_subst _ _ _ _ _ _ hk, reseat_eq_subst _ _ _ _ _ _ hk, subst_subst]
  congr 1; funext p
  simp only [Subst.comp, Subst.ofLift_apply, subst_bvar, Subst.liftN_apply,
    Subst.consList_apply, Lift.liftVar_consN, Lift.liftVar_skipN, Lift.liftVar, hL]
  (repeat' split) <;> (try simp only [VExpr.liftN, liftVar, VExpr.bvar.injEq]) <;>
    (repeat' split) <;> omega

theorem bvar_subst_iota {m r i C q x : Nat} (L : List VExpr) (hL : L.length = r) (hqC : q ≤ C)
    (hx : i + r ≤ x) :
    (((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i x =
      .bvar (if x < i + r + m then x - r else x - r + (C - q)) := by
  rw [show (Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0) =
    .ofLift (.consN (.skipN .refl (C - q)) m) by subst_ext]
  simp only [Subst.liftN_apply, Subst.consList_apply, Subst.ofLift_apply,
    Lift.liftVar_consN, Lift.liftVar_skipN, Lift.liftVar, hL]
  (repeat' split) <;> (try simp only [VExpr.liftN, liftVar, VExpr.bvar.injEq]) <;>
    (repeat' split) <;> omega

theorem bvars_subst_iota {m i C q : Nat} (L : List VExpr) :
    (bvars i 0).map (·.subst
      ((((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i)) =
      bvars i 0 := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, Subst.liftN_apply, Nat.add_zero]
  apply List.map_congr_left; intro x hx
  simp only [List.mem_reverse, List.mem_range] at hx
  simp [hx]

@[simp] theorem getElem_minorTypes {ls} {q : Nat} (h : q < (d.minorTypes ls).length) :
    (d.minorTypes ls)[q] = d.minorType ls q (d.allCtors[q]'(by simpa using h)).1
      (d.allCtors[q]'(by simpa using h)).2 := by
  simp [minorTypes]

/-- The right side of an iota rule: the minor premise applied to the fields and to the recursor
at each recursive field. -/
theorem iota_rhs {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.allCtors[q]? = some (j, c)) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.appN (.bvar (𝐦 + (𝐂 - 1 - q))) (bvars 𝐦 0 ++ c.recFields.map fun (k, ra) =>
        .lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
          (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + ra.binders.length) ++
            bvars 𝐓 (𝐂 + 𝐦 + ra.binders.length) ++ bvars 𝐂 (𝐦 + ra.binders.length) ++
            ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
          (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0))))
      (.app (.appN (.bvar (𝐦 + 𝐂 + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0))
        (d.ctorAppAt j c 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + 𝐦)) (bvars 𝐦 0))) := by
  have henv := hF.wf.ordered
  have hqC : q < 𝐂 := (List.getElem?_eq_some_iff.1 hq).1
  have hc : (j, c) ∈ d.allCtors := List.mem_of_getElem? hq
  have hqlt : q < (d.minorTypes 𝐥).length := by simpa using hqC
  have hQq : (d.minorTypes 𝐥)[q] = d.minorType 𝐥 q j c := by
    rw [getElem_minorTypes, (List.getElem?_eq_some_iff.1 hq).2]
  -- the minor premise, as a variable
  have hmin := VEnv.HasType.bvar (env := env) (U := 𝐔) <|
    Lookup.append_left (liftTele (𝐓 + 𝐂) 𝐅).reverse
      (Lookup.reverse_append (d.minorTypes 𝐥) (Γ := 𝐌.reverse ++ 𝐏.reverse) q hqlt)
  rw [hQq, liftN_liftN, liftN_eq_subst] at hmin
  simp only [List.length_reverse, length_liftTele, List.length_map, length_minorTypes,
    Lift.consN] at hmin
  dsimp only [minorType] at hmin
  obtain ⟨Tj, hj, -⟩ := VInductDecl.mem_allCtors_iff.1 hc
  rw [ctorAppAt_eq hj] at hmin
  rw [ctorAppAt_eq hj]
  simp only [List.append_assoc]
  have hWq0 : Ctx.Lift' (.skipN .refl (𝐂 - q))
      (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl
      (Γ := ((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((d.minorTypes 𝐥).drop q).reverse
    rw [show (d.minorTypes 𝐥).reverse = ((d.minorTypes 𝐥).drop q).reverse ++
      ((d.minorTypes 𝐥).take q).reverse by rw [← List.reverse_append, List.take_append_drop]]
    simpa only [List.length_reverse, List.length_drop, length_minorTypes,
      List.append_assoc] using this
  have hWq := Ctx.Lift'.tele (liftTele (𝐓 + q) 𝐅) hWq0
  have hFF : liftTele' (.skipN .refl (𝐂 - q)) (liftTele (𝐓 + q) 𝐅) = liftTele (𝐓 + 𝐂) 𝐅 := by
    rw [liftTele_eq_liftTele', liftTele_eq_liftTele', liftTele'_liftTele']
    simp only [Lift.consN]
    rw [Lift.comp_skipN]
    show liftTele' (Lift.skipN (Lift.skipN .refl (𝐓 + q)) (𝐂 - q)) _ = _
    rw [Lift.skipN_skipN, show 𝐓 + q + (𝐂 - q) = 𝐓 + 𝐂 by omega]
  rw [hFF] at hWq
  simp only [length_liftTele, List.length_map] at hWq
  have hQt : env.IsTele 𝐔 (𝐌.reverse ++ 𝐏.reverse) ((d.minorTypes 𝐥).take q) := by
    have := minors_isTele (v := 𝐯) hF
    rw [← List.take_append_drop q (d.minorTypes 𝐥)] at this
    exact (VEnv.IsTele.append_inv this).1
  have hΔq : OnCtx (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (env.IsType 𝐔) := by
    have := ((hF.params.append (by simpa using motives_isTele hF hv)).append
      (by simpa using hQt)).onCtx trivial
    simpa only [List.reverse_append, List.append_nil, List.append_assoc] using this
  have hFq : env.IsTele 𝐔 (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (liftTele (𝐓 + q) 𝐅) :=
    (hF.fields hc).weakN henv (.zero (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse)
      (by simp; omega))
  have hσ : VEnv.Ctx.SubstEq env 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++
      ((d.minorTypes 𝐥).reverse ++ (𝐌.reverse ++ 𝐏.reverse)))
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0))
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0))
      ((liftTele (𝐓 + q) 𝐅).reverse ++ (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++
        𝐏.reverse)) := by
    rw [show (Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0) =
      .ofLift (.consN (.skipN .refl (𝐂 - q)) 𝐦) by subst_ext]
    exact VEnv.Ctx.SubstEq.ofLift' henv (by simpa only [List.append_assoc] using hWq)
      (hFq.onCtx hΔq)
  have h := VEnv.HasType.appN_substT (Δ := ((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++
    𝐏.reverse) hmin (as := bvars 𝐦 0 ++ c.recFields.map fun (k, ra) =>
        .lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
          (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + ra.binders.length) ++
            bvars 𝐓 (𝐂 + 𝐦 + ra.binders.length) ++ bvars 𝐂 (𝐦 + ra.binders.length) ++
            ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
          (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0)))
    (by simp) ?W
  case W =>
    rw [Subst.consList_append, List.reverse_append, List.append_assoc]
    refine VEnv.Ctx.SubstEq.ofGetElem hσ _ rfl ?_ (by simp) ?_
    · apply VEnv.IsTele.of_getElem
      intro r hr
      have hr' : r < c.recFields.length := by simpa using hr
      have hmem := List.getElem_mem hr'
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      generalize c.recFields[r] = p at hmem ⊢
      obtain ⟨k, ra⟩ := p
      obtain ⟨f, hk, hra⟩ := mem_recFields hmem
      have := minor_ih (v := 𝐯) hF hc hk hra ((d.minorTypes 𝐥).take q) _
        (List.length_take_of_le (Nat.le_of_lt hqlt)) (List.length_take_of_le (Nat.le_of_lt hr))
      simpa only [List.append_assoc] using this
    · intro r hr hr2
      have hr' : r < c.recFields.length := by simpa using hr
      have hmem := List.getElem_mem hr'
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      generalize c.recFields[r] = p at hmem ⊢
      obtain ⟨k, ra⟩ := p
      obtain ⟨f, hk, hra⟩ := mem_recFields hmem
      have hkm : k < 𝐦 := (List.getElem?_eq_some_iff.1 hk).1
      have key : ∀ L : List VExpr, L.length = r →
          (VExpr.foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + q) k 𝐦 r i)
            (.app (.appN (.bvar (ra.binders.length + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx)))
              (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r ra.binders.length))
            (.appN (.bvar (ra.binders.length + r + (𝐦 - 1 - k))) (bvars ra.binders.length 0)))).subst
            (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L) =
          .foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i)
            (.app (.appN (.bvar (ra.binders.length + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx)))
              (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
            (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0))) := by
        intro L hL
        rw [subst_foralls]; congr 1
        · apply List.ext_getElem (by simp)
          intro i h1 h2
          simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
          exact reseat_subst_iota _ L hL (Nat.le_of_lt hkm) (Nat.le_of_lt hqC)
        · simp only [subst, subst_appN, List.map_map, List.length_map, List.length_zipIdx]
          rw [bvar_subst_iota L hL (Nat.le_of_lt hqC) (by omega),
            bvar_subst_iota L hL (Nat.le_of_lt hqC) (by omega), bvars_subst_iota,
            if_neg (by omega), if_pos (by omega),
            show ra.binders.length + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx) - r + (𝐂 - q) =
              ra.binders.length + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx) by omega,
            show ra.binders.length + r + (𝐦 - 1 - k) - r = ra.binders.length + (𝐦 - 1 - k) by
              omega]
          congr 2
          apply List.map_congr_left; intro e _
          exact reseat_subst_iota _ L hL (Nat.le_of_lt hkm) (Nat.le_of_lt hqC)
      rw [key _ (by simp; omega)]
      simpa only [List.append_assoc] using iota_ih hF hv hrec hc hk hra
  have hb : ∀ (L : List VExpr), L.length = 𝐮 → ∀ x, 𝐮 ≤ x →
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L x =
        .bvar (if x < 𝐮 + 𝐦 then x - 𝐮 else x - 𝐮 + (𝐂 - q)) := by
    intro L hL x hx
    simpa only [Subst.liftN, Nat.zero_add] using
      bvar_subst_iota (i := 0) (m := 𝐦) (C := 𝐂) (q := q) (x := x) L hL (Nat.le_of_lt hqC)
        (by omega)
  have e1 : ∀ (L : List VExpr), L.length = 𝐮 →
      (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 𝐮 0).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0 := by
    intro L hL
    rw [List.map_map]; apply List.map_congr_left; intro e _
    have := reseat_subst_iota (e.instL 𝐥) (a := 𝐓) (i := 0) L hL (Nat.le_refl 𝐦)
      (Nat.le_of_lt hqC)
    simp only [Subst.liftN] at this
    exact this
  rw [Subst.consList_append] at h
  simp only [subst, subst_appN, VInductiveType.ctorApp_subst] at h
  rw [hb _ (by simp) _ (by omega), if_neg (by omega),
    show 𝐮 + 𝐦 + q + (𝐓 - 1 - j) - 𝐮 + (𝐂 - q) = 𝐦 + 𝐂 + (𝐓 - 1 - j) by omega,
    e1 _ (by simp)] at h
  have e2 : ∀ (L : List VExpr), L.length = 𝐮 →
      (bvars 𝐧 (𝐓 + q + 𝐦 + 𝐮)).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      bvars 𝐧 (𝐓 + 𝐂 + 𝐦) := by
    intro L hL
    rw [bvars_map_subst]; conv => rhs; rw [bvars]
    apply List.map_congr_left; intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    rw [hb L hL _ (by omega), if_neg (by omega)]; congr 1; omega
  have e3 : ∀ (L : List VExpr), L.length = 𝐮 →
      (bvars 𝐦 𝐮).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      bvars 𝐦 0 := by
    intro L hL
    rw [bvars_map_subst]; conv => rhs; rw [bvars]
    apply List.map_congr_left; intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    rw [hb L hL _ (by omega), if_pos (by omega)]; congr 1; omega
  rw [e2 _ (by simp), e3 _ (by simp)] at h
  simpa only [List.append_assoc] using h

/-- An iota rule's two sides and type, as bodies over the recursor's binders and the
constructor's fields: each side is typed there. -/
theorem iotaRule_bodies {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔)
    {recLs : List VLevel} (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.allCtors[q]? = some (j, c)) :
    ∃ L R T, (d.iotaRule 𝐥 𝐯 recLs q j c).lhs = .lams (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) L ∧
      (d.iotaRule 𝐥 𝐯 recLs q j c).rhs = .lams (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) R ∧
      (d.iotaRule 𝐥 𝐯 recLs q j c).type =
        .foralls (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) T ∧
      env.IsTele 𝐔 [] (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) ∧
      env.HasType 𝐔 (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅).reverse L T ∧
      env.HasType 𝐔 (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅).reverse R T := by
  have henv := hF.wf.ordered
  have hc : (j, c) ∈ d.allCtors := List.mem_of_getElem? hq
  obtain ⟨Tj, hj, -⟩ := VInductDecl.mem_allCtors_iff.1 hc
  have hbind : env.IsTele 𝐔 [] (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) :=
    (recBinders_isTele hF hv).append (by
      simpa using (hF.fields hc).weakN henv (.zero ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
        (by simp; omega)))
  refine ⟨_, _, _, rfl, rfl, rfl, hbind, ?_, ?_⟩
  · simpa only [recBinders, List.reverse_append, List.append_nil, List.append_assoc] using
      iota_lhs hF hv hrec hc hj
  · simpa only [recBinders, List.reverse_append, List.append_nil, List.append_assoc] using
      iota_rhs hF hv hrec hq

theorem iotaRule_WF {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.allCtors[q]? = some (j, c)) (hrl : recLs.length = 𝐔) :
    (d.iotaRule 𝐥 𝐯 recLs q j c).WF env := by
  obtain ⟨L, R, T, hl, hr, ht, hbind, hL, hR⟩ := iotaRule_bodies hF hv hrec hq
  dsimp only [VDefEq.WF]
  rw [hl, hr, ht, show (d.iotaRule 𝐥 𝐯 recLs q j c).uvars = 𝐔 from hrl]
  exact ⟨hbind.lams (by simpa using hL), hbind.lams (by simpa using hR)⟩

end

theorem RecFacts.mono {env env' : VEnv} {U ls} (H : d.RecFacts env U ls) (hle : env ≤ env')
    (hwf : env'.WF) : d.RecFacts env' U ls where
  wf := hwf
  params := H.params.mono hle
  indices h := (H.indices h).mono hle
  type h := (H.type h).mono hle
  fields h := (H.fields h).mono hle
  ctor h1 h2 := let ⟨a, b⟩ := H.ctor h1 h2; ⟨a, b.mono hle⟩
  recArg h1 h2 h3 := let ⟨T, a, b, c⟩ := H.recArg h1 h2 h3; ⟨T, a, b, c.mono hle⟩
  typeHead h := (H.typeHead h).mono hle
  ctorHead h1 h2 := let ⟨a, b⟩ := H.ctorHead h1 h2; ⟨a, b.mono hle⟩

end VInductDecl
end Lean4Lean

namespace Lean4Lean
open VExpr

/-- The constant a recorded block's constructor is declared as. -/
theorem VEnv.WF.ctor_constant {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    (hs : env.inducts s = some (d, t)) {j : Nat} {c : VConstructor} (hjc : (j, c) ∈ d.ctors) :
    env.constants c.name = some ⟨d.uvars, c.type⟩ := by
  obtain ⟨env₀, env₂, -, -, hadd, hle, -⟩ := henv.inducts_block hs
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := hadd
  exact ((VEnv.addConstList_le hR).trans <| VEnv.addDefEqList_le.trans <|
    (VEnv.addBlock_le hB).trans hle).constants
    (VEnv.addConstList_constants_of_mem hC (List.mem_map.2 ⟨(j, c), hjc, rfl⟩))

theorem VExpr.foralls_inj : ∀ {As As' : List VExpr} {B B' : VExpr},
    VExpr.foralls As B = .foralls As' B' → As.length = As'.length → As = As' ∧ B = B'
  | [], [], _, _, h, _ => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, h, hl => by
    simp only [foralls_cons, forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := VExpr.foralls_inj h (by simpa using hl)
    exact ⟨rfl, rfl⟩

/-- A type that is syntactically a telescope agreeing with `Bs`, as a telescope of `Bs`. -/
theorem VEnv.IsType.foralls_teleDefEq {env : VEnv} {U : Nat} (henv : env.WF) {Γ As Bs : List VExpr}
    {R : VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hty : env.IsType U Γ (.foralls As R))
    (hTD : env.TeleDefEq U Γ As Bs) (hBs : env.IsTele U Γ Bs) :
    env.IsDefEqU U Γ (.foralls As R) (.foralls Bs R) := by
  have ⟨_, hR⟩ := VEnv.IsType.foralls_inv henv.ordered hty
  refine hTD.foralls henv hΓ hBs ?_
  have hctx := hTD.defeqCtx henv (Γ' := Γ) (VEnv.IsDefEqCtx.refl hΓ) hΓ hBs
  exact hR.defeqDFC henv.ordered hctx

theorem VExpr.subst_dflt_bvars_of_closed {e : VExpr} {n : Nat} (h : e.ClosedN n) :
    e.subst (Subst.dflt.consList (bvars n 0)) = e := by
  rw [h.subst_congr (σ' := Subst.id) fun i hi => by
    simp [Subst.consList_bvars_apply, hi, Subst.id], subst_id]

namespace VInductDecl
variable {d : VInductDecl}

theorem _root_.Lean4Lean.VEnv.TeleDefEq.length_eq {env : VEnv} {U : Nat} :
    ∀ {Γ As Bs : List VExpr}, env.TeleDefEq U Γ As Bs → As.length = Bs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => congrArg (· + 1) h.length_eq

/-- A closed term over a telescope of parameters, applied to them as variables. -/
theorem _root_.Lean4Lean.VEnv.HasType.appN_params {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Ps Is : List VExpr} {e S : VExpr} (hP : env.IsTele U [] Ps)
    (h : env.HasType U [] e (.foralls (Ps ++ Is) S)) :
    env.HasType U Ps.reverse (.appN e (bvars Ps.length 0)) (.foralls Is S) := by
  have hPP : OnCtx Ps.reverse (env.IsType U) := by simpa using hP.onCtx trivial
  have hf0 := h.weak0 henv (Γ := Ps.reverse)
  rw [← closed_subst henv h (.ofLift (.skipN .refl Ps.length)), foralls_append] at hf0
  have heq : (Subst.ofLift (.skipN .refl Ps.length)).consList (bvars Ps.length 0) =
      .ofLift .refl := by subst_ext
  have := VEnv.HasType.appN_substT (Δ := []) (As := Ps) (as := bvars Ps.length 0) hf0 (by simp)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv .refl hPP)
  rwa [heq, ← lift'_eq_subst, lift'_refl] at this

/-- An auxiliary type and its constructors, at the block's levels and at the parameters as
variables: the occurrence it stands for is typed as `T` would be, and the earlier type's
constructors at the occurrence's parameters as `T`'s constructors would be. -/
theorem auxHeads {env envT : VEnv} (hdecl : d.WF env)
    (hT : env.addConstList d.typeConsts = some envT) (henvT : envT.WF) {T : VInductiveType}
    (hTa : T ∈ d.aux) :
    ∃ o, T.nested = some o ∧ (∀ a ∈ o.args, a.ClosedN d.params.length) ∧
    envT.HasType d.uvars d.params.reverse (.appN (.const o.ind o.lvls) o.args)
      (.foralls T.indices (.sort d.level)) ∧
    ∀ c ∈ T.ctors, envT.HasType d.uvars d.params.reverse (.appN (.const c.name o.lvls) o.args)
      (.foralls (c.fields.map (·.type))
        (T.typeApp (VLevel.params d.uvars) (bvars d.params.length c.fields.length) c.indices)) := by
  have hle₁ := VEnv.addConstList_le hT
  have hP : envT.IsTele d.uvars [] d.params := hdecl.params.mono hle₁
  have hPP : OnCtx d.params.reverse (envT.IsType d.uvars) := by simpa using hP.onCtx trivial
  obtain ⟨o, hno, hAux⟩ := hdecl.aux T hTa
  obtain ⟨⟨dI, tI, TI, hind, hTI, hlvlen, hlvwf, hargslen, hargs,
    ⟨psJ, BJ, hTIty, hpsJ, ps', hTD, hTty⟩, hctors⟩⟩ := hAux envT hT
  have hps'len : ps'.length = d.params.length := hTD.length_eq
  have hTW := hdecl.ctors envT hT T (List.mem_append_right _ hTa)
  -- the block of the type the occurrence is of
  obtain ⟨env₀, envTI, h₀, hdI, hTI', hleI, TI', hTI'', hname⟩ := henvT.inducts hind
  cases hTI.symm.trans hTI''
  have henvTI : envTI.WF := VEnv.WF.addConstList h₀ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hdI.types T hT).1) hTI'
  have hTIW := hdI.ctors envTI hTI' TI (List.mem_append_left _ (List.mem_of_getElem? hTI))
  have hdIP0 : envTI.IsTele dI.uvars [] dI.params := hdI.params.mono (VEnv.addConstList_le hTI')
  have hdIP : envT.IsTele d.uvars [] (dI.params.map (·.instL o.lvls)) := by
    simpa using (hdIP0.instL hlvwf).mono hleI
  -- the occurrence's parameters, as a substitution for the earlier block's
  have hW : VEnv.Ctx.SubstEq envT d.uvars d.params.reverse (Subst.dflt.consList o.args)
      (Subst.dflt.consList o.args) ((dI.params.map (·.instL o.lvls)).reverse ++ []) :=
    VEnv.Ctx.SubstEq.ofGetElem .nil o.args.length rfl hdIP (by simp [hargslen])
      fun r h h' => by
        have h'' : r < dI.params.length := by simpa using h'
        simpa using hargs r _ _ (List.getElem?_eq_getElem h) (List.getElem?_eq_getElem h'')
  -- a constant of the earlier block, applied to the occurrence's parameters
  have happ {name : Name} {psX : List VExpr} {B : VExpr}
      (hc : envT.constants name = some ⟨dI.uvars, .foralls psX B⟩)
      (htd : envT.TeleDefEq dI.uvars [] psX dI.params)
      (hty : envT.IsType dI.uvars [] (.foralls psX B)) :
      envT.HasType d.uvars d.params.reverse (.appN (.const name o.lvls) o.args)
        ((B.instL o.lvls).subst (Subst.dflt.consList o.args)) := by
    have hdef := (VEnv.IsType.foralls_teleDefEq henvT (Γ := []) trivial hty htd
      (hdIP0.mono hleI)).instL hlvwf
    simp only [List.map_nil, instL_foralls] at hdef
    have hc0 : envT.HasType d.uvars [] (.const name o.lvls) ((VExpr.foralls psX B).instL o.lvls) :=
      .const hc hlvwf (by rw [hlvlen])
    rw [instL_foralls] at hc0
    have hc1 := hc0.defeqU_r henvT (Γ := []) trivial hdef
    have hc2 := hc1.weak0 henvT.ordered (Γ := d.params.reverse)
    rw [← closed_subst henvT.ordered hc1 .dflt] at hc2
    exact VEnv.HasType.appN_substT (Δ := []) hc2 (by simp [hargslen]) hW
  have hargsC : ∀ a ∈ o.args, a.ClosedN d.params.length := by
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
    have hi' : i < dI.params.length := hargslen ▸ (List.getElem?_eq_some_iff.1 hi).1
    have := hargs i a _ hi (List.getElem?_eq_getElem hi')
    simpa using this.closedN henvT.ordered (VEnv.CtxWF.closed henvT.ordered hPP)
  refine ⟨o, hno, hargsC, ?_, fun c hc => ?_⟩
  · -- the occurrence: through `T`'s declared type, as a lambda over its parameters
    have hcTI : envT.constants TI.name = some ⟨dI.uvars, .foralls psJ BJ⟩ := by
      rw [← hTIty]
      exact hleI.constants (VEnv.addConstList_constants_of_mem hTI'
        (List.mem_map.2 ⟨TI, List.mem_of_getElem? hTI, rfl⟩))
    have hG := happ hcTI hpsJ
      (hTIty ▸ ((hdI.types TI (List.mem_of_getElem? hTI)).1.mono
        ((VEnv.addConstList_le hTI').trans hleI)))
    rw [hname] at hG
    have hctx : envT.IsDefEqCtx d.uvars [] ps'.reverse d.params.reverse := by
      simpa using hTD.defeqCtx henvT (Γ' := []) .zero trivial hP
    have hGp := hG.defeqDFC henvT.ordered (hctx.symm henvT.ordered)
    have hPI : envT.IsTele d.uvars [] (d.params ++ T.indices) := hP.append (by simpa using hTW.1.indices)
    have hfT : envT.IsType d.uvars [] (.foralls (d.params ++ T.indices) (.sort d.level)) :=
      hPI.foralls ⟨_, .sort hdecl.level⟩
    have hTy : envT.IsType d.uvars [] T.type :=
      VEnv.IsType.defeqU_l henvT (Γ := []) trivial hTW.1.defeq.symm hfT
    rw [hTty] at hTy
    have hps' := (VEnv.IsType.foralls_inv henvT.ordered hTy).1
    have hps'C : OnCtx ps'.reverse (envT.IsType d.uvars) := by simpa using hps'.onCtx trivial
    have hF : envT.HasType d.uvars [] (.lams ps' (.appN (.const o.ind o.lvls) o.args)) T.type := by
      rw [hTty]; exact hps'.lams (by simpa using hGp)
    have hF1 := hF.defeqU_r henvT (Γ := []) trivial hTW.1.defeq
    have happly := VEnv.HasType.appN_params henvT.ordered hP hF1
    have heq : (Subst.ofLift (.skipN .refl d.params.length)).consList (bvars d.params.length 0) =
        .ofLift .refl := by subst_ext
    have hclosed : (VExpr.lams ps' (.appN (.const o.ind o.lvls) o.args)).subst
        (.ofLift (.skipN .refl d.params.length)) = .lams ps' (.appN (.const o.ind o.lvls) o.args) :=
      (hF.closedN henvT.ordered trivial).subst_eq Subst.Fixes.zero
    have hβ := VEnv.IsDefEq.lams_beta henvT.ordered (Γ₀ := ps'.reverse) hps'C (Δ := [])
      (τ := .ofLift (.skipN .refl d.params.length)) (as := bvars d.params.length 0) .nil hps'
      (by simpa using hGp) (by simp [hps'len])
      (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henvT.ordered .refl hps'C)
    rw [hclosed, heq, ← lift'_eq_subst, lift'_refl, ← lift'_eq_subst, lift'_refl] at hβ
    have hβP := hβ.defeqDFC henvT.ordered hctx
    exact (VEnv.IsDefEqU.of_l henvT hPP ⟨_, hβP⟩ happly).hasType.2
  · -- a constructor: the earlier type's, at the occurrence's parameters
    obtain ⟨cI, hcI, hcn, psI, BcI, hcIty, hpsIlen, ps'', hps''len, hcty⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r hctors c hc
    have hjc : (tI, cI) ∈ dI.ctors := mem_ctors_iff.2 ⟨TI, hTI, hcI⟩
    have hcIc := henvT.ctor_constant hind hjc
    rw [hcIty] at hcIc
    have hcIW := hTIW.2 cI hcI
    obtain ⟨psc, Dsc, hcIty', hpsc, -, -⟩ := hcIW.shape
    rw [hcIty, foralls_append] at hcIty'
    obtain ⟨rfl, -⟩ := VExpr.foralls_inj hcIty' (by rw [hpsIlen, hpsc.length_eq])
    have hH := happ hcIc (hpsc.mono hleI) ((hcIty ▸ hcIW.type).mono hleI)
    rw [← hcn] at hH
    have hcW := hTW.2 c hc
    obtain ⟨ps, Ds, hcty', hps, hfs, -⟩ := hcW.shape
    have hcty2 := hcty'
    rw [hcty, foralls_append] at hcty2
    obtain ⟨rfl, hY⟩ := VExpr.foralls_inj hcty2 (by rw [hps''len, hps.length_eq])
    rw [hY] at hH
    obtain ⟨hFs, hDF⟩ := FieldsWF.tele hfs
    have hcT := hcW.type
    rw [hcty', foralls_append] at hcT
    obtain ⟨-, hR⟩ := VEnv.IsType.foralls_inv henvT.ordered hcT
    have hctx : envT.IsDefEqCtx d.uvars [] ps''.reverse d.params.reverse := by
      simpa using hps.defeqCtx henvT (Γ' := []) .zero trivial hP
    have hR' := (hR.defeqDFC henvT.ordered (by simpa using hctx) :
      envT.IsType d.uvars d.params.reverse _)
    exact hH.defeqU_r henvT hPP
      (VEnv.IsType.foralls_teleDefEq henvT hPP hR' hDF hFs)

theorem allTypes_cases {t : Nat} {T : VInductiveType} (h : d.allTypes[t]? = some T) :
    d.types[t]? = some T ∨ T ∈ d.aux := by
  by_cases ht : t < d.types.length
  · rw [allTypes, List.getElem?_append_left ht] at h; exact .inl h
  · rw [allTypes, List.getElem?_append_right (by omega)] at h; exact .inr (List.mem_of_getElem? h)

theorem recFacts {env envT envC : VEnv} (henv : env.WF) (hdecl : d.WF env)
    (hT : env.addConstList d.typeConsts = some envT)
    (hC : envT.addConstList d.ctorConsts = some envC) {U : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars) : d.RecFacts envC U ls := by
  have henvT : envT.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hdecl.types T hT).1) hT
  have henvC : envC.WF := VEnv.WF.addConstList henvT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T, hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdecl.ctors envT hT T (List.mem_append_left _ hT')).2 c hc).type) hC
  have hle₁ : env ≤ envT := VEnv.addConstList_le hT
  have hle : envT ≤ envC := VEnv.addConstList_le hC
  have hTW {t : Nat} {T : VInductiveType} (h : d.allTypes[t]? = some T) :=
    hdecl.ctors envT hT T (List.mem_of_getElem? h)
  have hcT {t : Nat} {T : VInductiveType} (h : d.types[t]? = some T) :
      envC.constants T.name = some ⟨d.uvars, T.type⟩ :=
    hle.constants <| VEnv.addConstList_constants_of_mem hT
      (List.mem_map.2 ⟨T, List.mem_of_getElem? h, rfl⟩)
  have hcC {j : Nat} {c : VConstructor} (h : (j, c) ∈ d.ctors) :
      envC.constants c.name = some ⟨d.uvars, c.type⟩ :=
    VEnv.addConstList_constants_of_mem hC (List.mem_map.2 ⟨(j, c), h, rfl⟩)
  -- the shape of a constructor's type, in `envT` at the block's own levels
  have hshape {j : Nat} {c : VConstructor} {T : VInductiveType} (hc : (j, c) ∈ d.allCtors)
      (hj : d.allTypes[j]? = some T) :
      envT.IsTele d.uvars d.params.reverse (c.fields.map (·.type)) ∧
      envT.IsDefEqU d.uvars [] c.type (.foralls (d.params ++ c.fields.map (·.type))
        (T.typeApp (VLevel.params d.uvars) (bvars d.params.length c.fields.length)
          c.indices)) := by
    obtain ⟨T', hT', hcm⟩ := VInductDecl.mem_allCtors_iff.1 hc
    cases hj.symm.trans hT'
    have hcW := (hTW hj).2 c hcm
    obtain ⟨ps, Ds, hty, hps, hfs, -⟩ := hcW.shape
    have ⟨htele, hdeq⟩ := FieldsWF.tele hfs
    refine ⟨htele, ?_⟩
    have hP : envT.IsTele d.uvars [] d.params := hdecl.params.mono hle₁
    have hTD := hps.append (by simpa using hdeq)
    have hcty := hcW.type
    rw [hty] at hcty ⊢
    have ⟨_, hR⟩ := VEnv.IsType.foralls_inv henvT.ordered hcty
    refine hTD.foralls henvT trivial (hP.append (by simpa using htele)) ?_
    have hctx := hTD.defeqCtx henvT (Γ' := []) .zero trivial (hP.append (by simpa using htele))
    simpa using hR.defeqDFC henvT.ordered (by simpa using hctx)
  have hPl : envC.IsTele U [] (d.params.map (·.instL ls)) := by
    simpa using (hdecl.params.instL hls).mono (hle₁.trans hle)
  have hPP : OnCtx (d.params.map (·.instL ls)).reverse (envC.IsType U) := by
    simpa using hPl.onCtx trivial
  have htype {t : Nat} {T : VInductiveType} (h : d.types[t]? = some T) :
      envC.HasType U [] (.const T.name ls)
        (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
          (.sort (d.level.inst ls))) := by
    have hc : envC.HasType U [] (.const T.name ls) (T.type.instL ls) :=
      .const (hcT h) hls (by rw [hlen])
    have hdef := ((hTW (allTypes_getElem?_of_types h)).1.defeq.instL hls).mono hle
    simp only [List.map_nil, instL_foralls, List.map_append, instL] at hdef
    exact hc.defeqU_r henvC trivial hdef
  have hnone {t : Nat} {T : VInductiveType} (h : d.types[t]? = some T) : T.nested = none :=
    (hdecl.types T (List.mem_of_getElem? h)).2
  have hctor {j : Nat} {c : VConstructor} {T : VInductiveType} (hc : (j, c) ∈ d.ctors)
      (hj : d.types[j]? = some T) :
      c.indices.length = T.indices.length ∧
      envC.HasType U [] (.const c.name ls)
        (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
          (.appN (.const T.name ls)
            (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls)))) := by
    obtain ⟨T', hT', hcm⟩ := mem_ctors_iff.1 hc
    cases hj.symm.trans hT'
    refine ⟨((hTW (allTypes_getElem?_of_types hj)).2 c hcm).indices.1, ?_⟩
    have hcc : envC.HasType U [] (.const c.name ls) (c.type.instL ls) :=
      .const (hcC hc) hls (by rw [hlen])
    have hdef := ((hshape (mem_allCtors_of_ctors hc) (allTypes_getElem?_of_types hj)).2.instL
      hls).mono hle
    rw [VInductiveType.typeApp_of_none (hnone hj)] at hdef
    simp only [List.map_nil, instL_foralls, List.map_append, instL_appN, instL,
      VLevel.params_inst hlen, instL_bvars, List.map_map, Function.comp_def] at hdef
    exact hcc.defeqU_r henvC trivial hdef
  -- a closed constant over the parameters, applied to them as variables
  have hcanon {e S : VExpr} {Is : List VExpr}
      (h : envC.HasType U [] e (.foralls (d.params.map (·.instL ls) ++ Is) S)) :
      envC.HasType U (d.params.map (·.instL ls)).reverse (.appN e (bvars d.params.length 0))
        (.foralls Is S) := by
    have hf0 := h.weak0 henvC.ordered (Γ := (d.params.map (·.instL ls)).reverse)
    rw [← closed_subst henvC.ordered h (.ofLift (.skipN .refl d.params.length)),
      foralls_append] at hf0
    have heq : (Subst.ofLift (.skipN .refl d.params.length)).consList
        (bvars d.params.length 0) = .ofLift .refl := by subst_ext
    have := VEnv.HasType.appN_substT (Δ := []) (As := d.params.map (·.instL ls))
      (as := bvars d.params.length 0) hf0 (by simp)
      (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henvC.ordered .refl hPP)
    rwa [heq, ← lift'_eq_subst, lift'_refl] at this
  -- an auxiliary type's heads, at `ls`
  have haux {T : VInductiveType} (hTa : T ∈ d.aux) :
      envC.HasType U (d.params.map (·.instL ls)).reverse
        (T.typeHead ls (bvars d.params.length 0))
        (.foralls (T.indices.map (·.instL ls)) (.sort (d.level.inst ls))) ∧
      ∀ c ∈ T.ctors, envC.HasType U (d.params.map (·.instL ls)).reverse
        (T.ctorHead c ls (bvars d.params.length 0))
        (.foralls (c.fields.map (·.type.instL ls))
          (T.typeApp ls (bvars d.params.length c.fields.length)
            (c.indices.map (·.instL ls)))) := by
    obtain ⟨o, hno, hargsC, h1, h2⟩ := auxHeads hdecl hT henvT hTa
    have e1 : (d.params.reverse).map (·.instL ls) = (d.params.map (·.instL ls)).reverse := by
      simp [List.map_reverse]
    have e2 : o.args.map (fun a => (a.instL ls).subst (Subst.dflt.consList
        (bvars d.params.length 0))) = o.args.map (·.instL ls) :=
      List.map_congr_left fun a ha => subst_dflt_bvars_of_closed (hargsC a ha).instL
    refine ⟨?_, fun c hc => ?_⟩
    · have := (h1.instL hls).mono hle
      rw [e1, instL_foralls, instL_appN] at this
      simpa [VInductiveType.typeHead, hno, e2, instL] using this
    · have := ((h2 c hc).instL hls).mono hle
      rw [e1, instL_foralls, instL_appN, VInductiveType.typeApp_instL,
        VLevel.params_inst hlen, instL_bvars, List.map_map] at this
      simpa [VInductiveType.ctorHead, hno, e2, instL, Function.comp_def] using this
  refine {
    wf := henvC
    params := hPl
    indices := fun h => by
      simpa [List.map_reverse] using ((hTW h).1.indices.instL hls).mono hle
    type := htype
    fields := fun {j c} hc => by
      obtain ⟨T, hT', _⟩ := VInductDecl.mem_allCtors_iff.1 hc
      simpa [List.map_reverse, Function.comp_def] using
        ((hshape hc hT').1.instL hls).mono hle
    ctor := hctor
    recArg := fun {j c k f ra} hc hf hra => by
      obtain ⟨T', hT', hcm⟩ := VInductDecl.mem_allCtors_iff.1 hc
      obtain ⟨ps, Ds, hty, hps, hfs, -⟩ := ((hTW hT').2 c hcm).shape
      have := FieldsWF.recArg hfs k f hf
      unfold RecArgWF at this
      rw [hra] at this
      obtain ⟨T, h1, h2, h3⟩ := this
      refine ⟨T, h1, h2, ?_⟩
      have := (h3.instL hls).mono hle
      simp only [List.map_append, List.map_reverse, List.map_map, Function.comp_def, List.map_take,
        instL_foralls, VInductiveType.typeApp_instL, VLevel.params_inst hlen, instL_bvars,
        Nat.zero_add] at this
      simpa [List.map_take, Function.comp_def] using this
    typeHead := fun {t T} h => by
      rcases allTypes_cases h with h | h
      · rw [VInductiveType.typeHead_of_none (hnone h)]
        exact hcanon (htype h)
      · exact (haux h).1
    ctorHead := fun {j c T} hc hj => by
      obtain ⟨T', hT', hcm⟩ := VInductDecl.mem_allCtors_iff.1 hc
      cases hj.symm.trans hT'
      rcases allTypes_cases hj with h | h
      · have hc' : (j, c) ∈ d.ctors := mem_ctors_iff.2 ⟨T, h, hcm⟩
        refine ⟨(hctor hc' h).1, ?_⟩
        rw [VInductiveType.ctorHead_of_none (hnone h), VInductiveType.typeApp_of_none (hnone h)]
        exact hcanon (hctor hc' h).2
      · exact ⟨((hTW hj).2 c hcm).indices.1, (haux h).2 c hcm⟩ }

end VInductDecl
end Lean4Lean

namespace Lean4Lean
open VExpr

/-- The parameters and indices of a term's type at a type of a recorded block instantiate the
type's telescope. -/
theorem VEnv.WF.projArgs {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    {As I : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    {x : VExpr} (hx : env.HasType U Γ x (.appN (.const s ls) (As ++ I))) :
    VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList (As ++ I)) (Subst.dflt.consList (As ++ I))
      (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls)).reverse := by
  obtain ⟨env₀, envT, h₀, hd, hT, hle, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'; subst hname
  have hTW := (hd.ctors envT hT T (List.mem_append_left _ (List.mem_of_getElem? ht))).1
  have hle₀ := VEnv.addConstList_le hT
  have hc : env.HasType U [] (.const T.name ls) (T.type.instL ls) :=
    .const (hle.constants (VEnv.addConstList_constants_of_mem hT
      (List.mem_map.2 ⟨T, List.mem_of_getElem? ht, rfl⟩))) hls (by rw [hlen])
  have hdef := (hTW.defeq.instL hls).mono hle
  simp only [List.map_nil, instL_foralls, List.map_append, instL] at hdef
  have hc := hc.defeqU_r (Γ := []) henv trivial hdef
  have hPI : env.IsTele U [] (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls)) :=
    ((hd.params.instL hls).mono (hle₀.trans hle)).append
      (by simpa [List.map_reverse] using (hTW.indices.instL hls).mono hle)
  have hc0 := hc.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hc .dflt] at hc0
  have := VEnv.HasType.appN_invT henv hΓ (Δ := []) hc0 .nil hPI
    (let ⟨_, h⟩ := hx.isType henv.ordered hΓ; ⟨_, h⟩) (by simp [hA, hI])
  simpa using this

/-- A projection of a term, when typed, is definitionally equal to the projection of a term
definitionally equal to it. -/
theorem VExpr.WF.proj_congr {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {k : Nat} {e e' : VExpr}
    (H : VExpr.WF env U Γ (.proj s k e)) (he : env.IsDefEqU U Γ e e') :
    env.IsDefEqU U Γ (.proj s k e) (.proj s k e') := by
  obtain ⟨d, t, T, c, f, ls, As, I, h1, h2, h3, h4, h5, h6, h7, h8, hP, hx, -⟩ :=
    H.proj_inv henv.ordered hΓ
  have W := henv.projArgs hΓ h1 h2 h5 h6 h7 h8 hx
  rw [List.reverse_append, Subst.consList_append] at W
  have W := VEnv.Ctx.SubstEq.dropList (by simp [h8]) (by simp [h8]) W
  have ⟨_, hS⟩ := hx.isType henv.ordered hΓ
  exact ⟨_, (VEnv.projCongr henv.ordered hΓ h1 h2 h3 (henv.projFacts h1 h2 h3) h5 h6 h7 h8 h7 h8 W
    hS (he.of_l henv hΓ hx) k f h4 hP).2⟩

/-- A term whose type is a pi telescope ending in a sort, applied to arguments to a sort, takes
exactly as many arguments as the telescope has binders. -/
theorem VEnv.HasType.appN_sort_length {env : VEnv} {U : Nat} (henv : env.WF) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As : List VExpr} {τ : Subst} {f : VExpr} {as : List VExpr} {l u : VLevel},
    env.HasType U Γ f ((VExpr.foralls As (.sort l)).subst τ) →
    env.HasType U Γ (f.appN as) (.sort u) → as.length = As.length
  | [], _, _, [], _, _, _, _ => rfl
  | _ :: _, _, _, [], _, _, hf, h =>
    (VEnv.IsDefEqU.sort_forallE_inv henv hΓ (h.uniqU henv hΓ hf)).elim
  | As, τ, f, a :: as, l, u, hf, h => by
    have hwf := appN_wf_prefix henv.ordered hΓ (as := [a]) (bs := as) ⟨_, h⟩
    obtain ⟨A₁, B₁, h1, h2⟩ := hwf.app_inv henv.ordered hΓ
    match As, hf with
    | [], hf => exact (VEnv.IsDefEqU.sort_forallE_inv henv hΓ (hf.uniqU henv hΓ h1)).elim
    | A :: As, hf =>
      simp only [foralls_cons] at hf
      have ⟨⟨_, hA⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ (h1.uniqU henv hΓ hf)
      have hfa := hf.app (h2.defeqU_r henv hΓ ⟨_, hA⟩)
      rw [inst_lift_cons] at hfa
      exact congrArg (· + 1) (appN_sort_length henv hΓ hfa h)

/-- The facts the recursor is built from hold of any block a well-formed environment records. -/
theorem VEnv.WF.recFacts {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    (hs : env.inducts s = some (d, t)) {U : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.uvars) : d.RecFacts env U ls := by
  obtain ⟨env₀, env₂, h₀, hd, hadd, hle, -⟩ := henv.inducts_block hs
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := hadd
  exact (VInductDecl.recFacts h₀ hd hT hC hls hlen).mono
    ((VEnv.addConstList_le hR).trans <| VEnv.addDefEqList_le.trans <|
      (VEnv.addBlock_le hB).trans hle) henv

/-- Two terms of a type of a recorded block with a single fieldless constructor and no indices,
not recursive, are definitionally equal: each is, by structure eta, the constructor. -/
theorem VEnv.WF.unitLike {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) (hi : T.indices = []) (hrec : d.isRec = false) (hf : c.fields = [])
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    {As : List VExpr} {e₁ e₂ : VExpr}
    (h₁ : env.HasType U Γ e₁ (.appN (.const s ls) As))
    (h₂ : env.HasType U Γ e₂ (.appN (.const s ls) As)) :
    env.IsDefEq U Γ e₁ e₂ (.appN (.const s ls) As) := by
  have hF := henv.recFacts hs hls hlen
  obtain ⟨env₀, envT, -, -, -, -, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'; subst hname
  have hty := hF.type ht
  rw [hi, List.map_nil, List.append_nil] at hty
  have hty0 := hty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hty .dflt] at hty0
  have ⟨_, hS⟩ := h₁.isType henv.ordered hΓ
  have hA : As.length = d.params.length := by
    simpa using VEnv.HasType.appN_sort_length henv hΓ hty0 hS
  have W := henv.projArgs hΓ hs ht hls hlen (I := []) hA (by simp [hi]) (by simpa using h₁)
  simp only [List.append_nil, hi, List.map_nil] at W
  have hcm : (t, c) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc]⟩
  obtain ⟨hil, hcty⟩ := hF.ctor hcm ht
  rw [hi, List.length_nil, List.length_eq_zero_iff] at hil
  rw [hf, hil, List.map_nil, List.append_nil, List.map_nil, List.append_nil, List.length_nil] at hcty
  have hc0 := hcty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hcty .dflt] at hc0
  have hk := VEnv.HasType.appN_substT (Δ := []) (as := As) hc0 (by simp [hA]) (by simpa using W)
  simp only [subst_appN, subst] at hk
  rw [← hA, subst_bvars_consList] at hk
  have hk' : env.HasType U Γ (.appN (.const c.name ls) (As ++ VExpr.projs T.name c.fields.length e₁))
      (.appN (.const T.name ls) As) := by
    simpa [hf, VExpr.projs] using hk
  have hk'' : env.HasType U Γ (.appN (.const c.name ls) (As ++ VExpr.projs T.name c.fields.length e₂))
      (.appN (.const T.name ls) As) := by
    simpa [hf, VExpr.projs] using hk
  have e₁η := VEnv.IsDefEq.projEta hs ht hc hi hrec hls hlen hA h₁ hk'
  have e₂η := VEnv.IsDefEq.projEta hs ht hc hi hrec hls hlen hA h₂ hk''
  simp only [hf, List.length_nil, VExpr.projs, List.range_zero, List.map_nil,
    List.append_nil] at e₁η e₂η
  exact e₁η.trans e₂η.symm

/-- Each argument of a telescope's substitution, typed against its entry instantiated by the
arguments before it. -/
theorem VEnv.Ctx.SubstEq.getElem {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {σ : Subst} :
    ∀ (n : Nat) {As as : List VExpr}, as.length = n →
    VEnv.Ctx.SubstEq env U Γ (σ.consList as) (σ.consList as) (As.reverse ++ Δ) →
    as.length = As.length → ∀ r (h : r < as.length) (h' : r < As.length),
      env.HasType U Γ as[r] (As[r].subst (σ.consList (as.take r)))
  | 0, _, as, hn, _, _, r, h, _ => by simp [List.eq_nil_of_length_eq_zero hn] at h
  | n + 1, As, as, hn, W, hlen, r, h, h' => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [Subst.consList_concat, List.reverse_append] at W
    cases W with | cons W' _ ha =>
    simp only [List.length_append, List.length_singleton] at h h'
    rcases Nat.lt_or_ge r as.length with hr | hr
    · have := VEnv.Ctx.SubstEq.getElem n hn W' hlen r hr (by omega)
      simp only [List.getElem_append_left hr, List.getElem_append_left (show r < As.length by omega),
        List.take_append_of_le_length (Nat.le_of_lt hr)]
      exact this
    · obtain rfl : r = as.length := by omega
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_append_right (show As.length ≤ as.length by omega), List.take_left']
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
      exact ha

theorem VInductDecl.ProjAllowed.congr {d : VInductDecl} {c : VConstructor} {ls ls' : List VLevel}
    {k : Nat} (H : d.ProjAllowed c ls k) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    d.ProjAllowed c ls' k := by
  have e {l : VLevel} : l.inst ls ≈ l.inst ls' := VLevel.inst_congr (VLevel.equiv_def'.2 rfl) heq
  have e' {l : VLevel} : l.inst ls' ≈ .zero ↔ l.inst ls ≈ .zero :=
    ⟨fun h => VLevel.equiv_def'.2 (e.trans h), fun h => VLevel.equiv_def'.2 (e.symm.trans h)⟩
  intro hz
  obtain ⟨h1, h2⟩ := H fun hn => hz fun ns => by rw [← congrFun e ns]; exact hn ns
  exact ⟨fun f hf => e'.2 (h1 f hf), fun j hj f hf => (h2 j hj f hf).imp_left e'.2⟩

/-- A well-formed application of a recorded block's constructor to as many arguments as it has
parameters and fields: its levels, the arguments as parameters and fields instantiating the
constructor's telescope, and its type. -/
theorem VEnv.WF.ctorApp {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hcm : c ∈ T.ctors) {ls : List VLevel} {args : List VExpr}
    (hlen : args.length = d.params.length + c.fields.length)
    (hXwf : VExpr.WF env U Γ (.appN (.const c.name ls) args)) (τ : Subst := .dflt) :
    (∀ l ∈ ls, l.WF U) ∧ ls.length = d.uvars ∧ ∃ As fs, args = As ++ fs ∧
      As.length = d.params.length ∧ fs.length = c.fields.length ∧
      Ctx.SubstEq env U Γ ((τ.consList As).consList fs)
        ((τ.consList As).consList fs)
        ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) ∧
      env.HasType U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls)
        (As ++ (c.indices.map (·.instL ls)).map (·.subst ((τ.consList As).consList fs)))) := by
  have hjc : (t, c) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, hcm⟩
  obtain ⟨-, -, -, -, -, -, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'; subst hname
  obtain ⟨ci, hci, hls, hlenls⟩ :=
    (appN_wf_prefix henv.ordered hΓ (as := []) (bs := args) (by simpa using hXwf)).const_inv
      henv.ordered hΓ
  cases (henv.ctor_constant hs hjc).symm.trans hci
  have hF := henv.recFacts hs hls hlenls
  obtain ⟨hil, hcty⟩ := hF.ctor hjc ht
  have hc0 := hcty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hcty τ] at hc0
  have hPF : env.IsTele U [] (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls)) :=
    hF.params.append (by simpa using hF.fields (VInductDecl.mem_allCtors_of_ctors hjc))
  have W := VEnv.HasType.appN_invT henv hΓ (Δ := []) hc0 .nil hPF hXwf (by simp [hlen])
  obtain ⟨As, fs, rfl, hA, hfs⟩ : ∃ As fs, args = As ++ fs ∧ As.length = d.params.length ∧
      fs.length = c.fields.length :=
    ⟨args.take d.params.length, args.drop d.params.length, (List.take_append_drop ..).symm,
      by simp [hlen], by simp [hlen]⟩
  rw [List.reverse_append, List.append_nil, Subst.consList_append] at W
  have hX := VEnv.HasType.appN_substT (Δ := []) (as := As ++ fs) hc0 (by simp [hA, hfs])
    (by rw [Subst.consList_append, List.reverse_append, List.append_nil]; exact W)
  simp only [subst_appN, subst, List.map_append] at hX
  rw [Subst.consList_append, show (bvars d.params.length c.fields.length) =
      bvars d.params.length (0 + fs.length) by rw [hfs, Nat.zero_add],
    subst_bvars_consList_ge, ← hA, subst_bvars_consList] at hX
  exact ⟨hls, hlenls, As, fs, rfl, hA, hfs, W, hX⟩

/-- Each field of a constructor application, at the type of its sort. -/
theorem VEnv.WF.ctorApp_fieldType {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) {As fs : List VExpr}
    (hfs : fs.length = c.fields.length)
    (W : Ctx.SubstEq env U Γ ((Subst.dflt.consList As).consList fs)
      ((Subst.dflt.consList As).consList fs)
      ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    {j : Nat} {f : VField} (hf : c.fields[j]? = some f) :
    env.HasType U Γ ((f.type.instL ls).subst (Subst.dflt.consList (As ++ fs.take j)))
      (.sort (f.level.inst ls)) := by
  have hF := henv.projFacts hs ht hc
  have hj : j < fs.length := hfs ▸ (List.getElem?_eq_some_iff.1 hf).1
  have WA := VEnv.Ctx.SubstEq.dropList (as := fs) (as' := fs)
    (Bs := c.fields.map (·.type.instL ls)) (by simp [hfs]) (by simp [hfs]) W
  obtain ⟨hFt, hFk⟩ := hF.fields j f hf
  have hFt := hFt.instL hls
  simp only [List.map_reverse] at hFt
  -- the kept fields, as arguments for the kept telescope
  have WK := Ctx.SubstEq.ofGetElem WA (c.keptIdx j j).length
    (as := (c.keptIdx j j).map (fs[·]?.getD default)) (by simp) hFt
    (by simp [VConstructor.keptFields_eq]) fun r h h' => ?_
  · have hFk := hFk.instL hls
    simp only [List.map_append, List.map_reverse] at hFk
    have := hFk.subst henv.ordered WK hΓ
    rwa [← Subst.consList_append, ← c.field_subst_stripped hf (Nat.le_refl _),
      List.map_range_getD_eq_take _ (Nat.le_of_lt hj)] at this
  · simp only [List.length_map] at h
    have hm := List.getElem_mem h
    obtain ⟨hjk, -⟩ := (c.mem_keptIdx).1 hm
    generalize hi : (c.keptIdx j j)[r] = i at hjk
    have hi' : i < fs.length := by omega
    obtain ⟨fi, hfi⟩ : ∃ fi, c.fields[i]? = some fi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have := VEnv.Ctx.SubstEq.getElem fs.length rfl W (by simp [hfs]) i hi' (by simp; omega)
    simp only [List.getElem_map, hi, List.getElem?_eq_getElem hi', Option.getD_some,
      VConstructor.keptFields_eq, hfi, Option.map_some, ← List.map_take,
      VConstructor.keptIdx_take _ _ _ _ h, ← Subst.consList_append]
    rw [← c.field_subst_stripped hfi (Nat.le_of_lt hjk),
      List.map_range_getD_eq_take _ (Nat.le_of_lt hi')]
    simpa [(List.getElem?_eq_some_iff.1 hfi).2, Subst.consList_append] using this

/-- A typed projection of a recorded block's constructor applied to the parameters and all of its
fields is the field. -/
theorem VEnv.WF.proj_ctorApp {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hcm : c ∈ T.ctors) {ls : List VLevel} {args : List VExpr} {k : Nat} {a : VExpr}
    (hlen : args.length = d.params.length + c.fields.length)
    (ha : args[d.params.length + k]? = some a)
    (H : VExpr.WF env U Γ (.proj s k (.appN (.const c.name ls) args))) :
    env.IsDefEqU U Γ (.proj s k (.appN (.const c.name ls) args)) a := by
  obtain ⟨d₁, t₁, T₁, c₁, f, ls₁, As₁, I₁, h1, h2, h3, h4, h5, h6, h7, h8, hP, hx, -⟩ :=
    H.proj_inv henv.ordered hΓ
  cases hs.symm.trans h1; cases ht.symm.trans h2
  obtain rfl : c = c₁ := by simpa [h3] using hcm
  obtain ⟨hls, hlenls, As, fs, rfl, hA, hfs, W, hX⟩ := henv.ctorApp hΓ hs ht hcm hlen ⟨_, hx⟩
  have WA := VEnv.Ctx.SubstEq.dropList (as := fs) (as' := fs)
    (Bs := c.fields.map (·.type.instL ls)) (by simp [hfs]) (by simp [hfs]) W
  -- its two types agree
  have hT₁ := hx.isType henv.ordered hΓ
  have hT₂ := hX.isType henv.ordered hΓ
  have hil := ((henv.recFacts hs hls hlenls).ctor (VInductDecl.mem_ctors_iff.2 ⟨T, ht, hcm⟩) ht).1
  have hIl : (List.map (fun x => x.subst ((Subst.dflt.consList As).consList fs))
      (c.indices.map (·.instL ls))).length = T.indices.length := by simp [hil]
  obtain ⟨hlseq, -⟩ := VEnv.IsDefEqU.indApp_inv henv hΓ hs ht h5 h6 hls hlenls h7 h8 hA hIl
    hT₁ hT₂ (hx.uniqU henv hΓ hX)
  have hP' := hP.congr hlseq
  obtain ⟨_, hS⟩ := hT₂
  have hfsT : ∀ k (h : k < fs.length) (f : VField), c.fields[k]? = some f →
      env.HasType U Γ fs[k] ((f.type.instL ls).subst (Subst.dflt.consList (As ++ fs.take k))) := by
    intro k h f hf
    obtain ⟨hk, hfk⟩ := List.getElem?_eq_some_iff.1 hf
    have := VEnv.Ctx.SubstEq.getElem fs.length rfl W (by simp [hfs]) k h (by simp; omega)
    simpa [hfk, Subst.consList_append] using this
  have hfa : fs[k]? = some a := by
    rw [List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left] at ha
    exact ha
  exact ⟨_, VEnv.projIota_ctor henv.ordered hΓ hs ht h3 (henv.projFacts hs ht h3) hls hlenls hA hIl
    hfs WA hS hX hfsT k f a h4 hfa hP'⟩

theorem VExpr.projs_take (s : Name) (e : VExpr) {r k : Nat} (h : r ≤ k) :
    (VExpr.projs s k e).take r = VExpr.projs s r e := by
  simp [VExpr.projs, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- Structure eta, from the projections: a term of a non-recursive structure type without indices
is definitionally equal to the constructor applied to the parameters and to arguments its
projections are definitionally equal to. -/
theorem VEnv.WF.structEta {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) (hi : T.indices = []) (hrec : d.isRec = false)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars)
    {As fs : List VExpr} {x : VExpr} (hA : As.length = d.params.length)
    (hfs : fs.length = c.fields.length) (hx : env.HasType U Γ x (.appN (.const s ls) As))
    (hP : ∀ j < c.fields.length, d.ProjAllowed c ls j)
    (hdf : ∀ j (h : j < fs.length), env.IsDefEqU U Γ (.proj s j x) fs[j]) :
    env.IsDefEq U Γ x (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) As) := by
  have hF := henv.recFacts hs hls hlen
  obtain ⟨-, -, -, -, -, -, T', hT', hname⟩ := henv.inducts hs
  cases ht.symm.trans hT'; subst hname
  have hjc : (t, c) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨T, ht, by simp [hc]⟩
  have hI : ([] : List VExpr).length = T.indices.length := by simp [hi]
  have hx' : env.HasType U Γ x (.appN (.const T.name ls) (As ++ [])) := by simpa using hx
  have W := henv.projArgs hΓ hs ht hls hlen hA hI hx'
  simp only [List.append_nil, hi, List.map_nil] at W
  have ⟨_, hS⟩ := hx'.isType henv.ordered hΓ
  have hPF := henv.projFacts hs ht hc
  -- the projections, pairwise equal to the arguments at the fields' types
  have W2 : Ctx.SubstEq env U Γ ((Subst.dflt.consList As).consList (VExpr.projs T.name
      c.fields.length x)) ((Subst.dflt.consList As).consList fs)
      ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) := by
    refine Ctx.SubstEq.ofGetElemDF W c.fields.length (by simp [VExpr.projs])
      (by simpa [List.map_reverse, Function.comp_def] using hF.fields (VInductDecl.mem_allCtors_of_ctors hjc))
      (by simp [VExpr.projs]) (by simp [hfs]) fun r h h' h'' => ?_
    simp only [VExpr.projs, List.length_map, List.length_range] at h
    obtain ⟨f, hf⟩ : ∃ f, c.fields[r]? = some f := ⟨_, List.getElem?_eq_getElem h⟩
    have hPC := (VEnv.projCongr henv.ordered hΓ hs ht hc hPF hls hlen hA hI hA hI W hS hx' r f hf
      (hP r h)).2
    have := (hdf r h').of_l henv hΓ hPC.hasType.1
    simp only [VExpr.projs, List.getElem_map, List.getElem_range, List.getElem_map]
    rw [← VExpr.projs, VExpr.projs_take _ _ (Nat.le_of_lt h)]
    simpa [VConstructor.projType, hf, Subst.consList_append,
      (List.getElem?_eq_some_iff.1 hf).2] using this
  -- the constructor at both
  obtain ⟨hil, hcty⟩ := hF.ctor hjc ht
  rw [hi, List.length_nil, List.length_eq_zero_iff] at hil
  rw [hil, List.map_nil, List.append_nil] at hcty
  have hc0 := hcty.weak0 henv.ordered (Γ := Γ)
  rw [← closed_subst henv.ordered hcty .dflt] at hc0
  have hcongr := IsDefEq.appN_substTDF (Δ := []) (as := As ++ VExpr.projs T.name c.fields.length x)
    (bs := As ++ fs) hc0 (by simp [hA, VExpr.projs]) (by simp [hA, hfs])
    (by rw [Subst.consList_append, Subst.consList_append, List.reverse_append, List.append_nil]
        exact W2)
  simp only [subst_appN, subst] at hcongr
  rw [Subst.consList_append, show (bvars d.params.length c.fields.length) =
      bvars d.params.length (0 + (VExpr.projs T.name c.fields.length x).length) by
        simp [VExpr.projs],
    subst_bvars_consList_ge, ← hA, subst_bvars_consList] at hcongr
  have hη := VEnv.IsDefEq.projEta hs ht hc hi hrec hls hlen hA hx hcongr.hasType.1
  exact hη.trans hcongr

theorem List.forall₂_of_getElem? {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ (j : Nat) a b, l₁[j]? = some a → l₂[j]? = some b → R a b) →
    List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, H =>
    .cons (H 0 a b rfl rfl) (List.forall₂_of_getElem? (by simpa using hl)
      fun j a b h₁ h₂ => H (j + 1) a b h₁ h₂)

/-- Both halves of an application are well formed. `app_inv` gives the typings, which is more
than a caller peeling a spine apart wants to name: this is the form that chains. -/
theorem VExpr.WF.app_inv₂ (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) {f a : VExpr}
    (H : VExpr.WF env U Γ (f.app a)) : VExpr.WF env U Γ f ∧ VExpr.WF env U Γ a :=
  let ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ; ⟨⟨_, hf⟩, ⟨_, ha⟩⟩

variable! (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem VExpr.WF.appN_inv : ∀ {vs : List VExpr} {e},
    VExpr.WF env U Γ (e.appN vs) → VExpr.WF env U Γ e
  | [], _, h => h
  | v :: vs, e, h =>
    let ⟨_, _, h, _⟩ := (VExpr.WF.appN_inv (vs := vs) (e := e.app v) h).app_inv henv hΓ
    ⟨_, h⟩

/-- Congruence for `appN`: the arguments' typings come from the application being well formed, so
no separate hypothesis about them is needed. -/
theorem VEnv.IsDefEqU.appN {env : VEnv} (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {vs : List VExpr} {f g}, env.IsDefEqU U Γ f g → VExpr.WF env U Γ (f.appN vs) →
      env.IsDefEqU U Γ (f.appN vs) (g.appN vs) := by
  intro vs
  induction vs with
  | nil => intro _ _ h _; exact h
  | cons v vs ih =>
    intro f g h hwf
    obtain ⟨A, B, hf, hv⟩ :=
      (VExpr.WF.appN_inv henv.ordered hΓ (vs := vs) (e := f.app v) hwf).app_inv henv.ordered hΓ
    exact ih ⟨_, (h.of_l henv hΓ hf).appDF hv⟩ hwf

/-- Congruence for a whole application spine, arguments included. `IsDefEqU.appN` covers only the
function; the typings each step needs come from the application's own well-typedness, the same
way `TrExprS.appN` gets them. -/
theorem VEnv.IsDefEqU.appN' {env : VEnv} {U Γ} (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {xs ys : List VExpr} {f f'}, env.IsDefEqU U Γ f f' →
      List.Forall₂ (env.IsDefEqU U Γ) xs ys →
      VExpr.WF env U Γ (f.appN xs) →
      env.IsDefEqU U Γ (f.appN xs) (f'.appN ys)
  | [], _, _, _, hf, h, _ => by cases h; exact hf
  | x :: xs, y :: ys, f, f', hf, .cons hx hxs, hwf =>
    have ⟨_, _, hfT, hxT⟩ := (VExpr.WF.appN_inv (vs := xs) henv hΓ hwf).app_inv henv hΓ
    VEnv.IsDefEqU.appN' henv hΓ (f := f.app x) (f' := f'.app y)
      ⟨_, (hf.of_l henv hΓ hfT).appDF (hx.of_l henv hΓ hxT)⟩ hxs hwf

end Lean4Lean

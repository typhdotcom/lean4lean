import Lean4Lean.Theory.Typing.Nested

/-!
# A nested block restored from its translation

The kernel checks a nested block as a flat one whose auxiliary types are types of the block
(`VInductDecl` with `aux = []`). Restoring every term of that flat block
(`VExpr.restore`) gives the block `VInductDecl.restoreNested`: its own types, then the auxiliary
types, each standing for its occurrence. Its recursors and iota rules are those of the flat block,
restored (`restore_recType`, `restore_iotaRule_rhs`): what the kernel adds.
-/

namespace Lean4Lean
open VExpr

section
variable (R : Name → Option VAuxHead) (ren : Name → Option Name)

/-- A recursive field's view, restored. -/
def VRecArg.restore (ra : VRecArg) : VRecArg :=
  { ra with binders := ra.binders.map (·.restore R ren), indices := ra.indices.map (·.restore R ren) }

/-- A field, restored. -/
def VField.restore (f : VField) : VField :=
  { f with type := f.type.restore R ren, recArg := f.recArg.map (·.restore R ren) }

/-- A constructor, restored, named by `cname`. -/
def VConstructor.restore (cname : Name → Name) (c : VConstructor) : VConstructor where
  name := cname c.name
  type := c.type.restore R ren
  fields := c.fields.map (·.restore R ren)
  indices := c.indices.map (·.restore R ren)

/-- A type, restored, standing for `o` if it is an auxiliary type. -/
def VInductiveType.restore (cname : Name → Name) (o : Option VNested) (T : VInductiveType) :
    VInductiveType where
  name := T.name
  type := T.type.restore R ren
  indices := T.indices.map (·.restore R ren)
  ctors := T.ctors.map (·.restore R ren cname)
  nested := o

/-- What the `j`th type of a translated block with `n` own types stands for. -/
def nestedAt (n : Nat) (ns : List VNested) (j : Nat) : Option VNested :=
  if j < n then none else ns[j - n]?

/-- The block a translated nested block restores to: its first `n` types are its own, the others
stand for the occurrences `ns`. -/
def VInductDecl.restoreNested (d : VInductDecl) (n : Nat) (ns : List VNested)
    (cname : Name → Name) : VInductDecl :=
  let f := fun (p : VInductiveType × Nat) => p.1.restore R ren cname (nestedAt n ns p.2)
  { d with
    params := d.params.map (·.restore R ren)
    types := (d.types.zipIdx.take n).map f
    aux := (d.types.zipIdx.drop n).map f }

end

namespace VExpr
variable {R : Name → Option VAuxHead} {ren : Name → Option Name}

/-- A head that no prefix of the application replaces restores argument by argument. -/
theorem restore_appN_gen : ∀ {f : VExpr} (xs : List VExpr),
    (∀ ys, restoreAux R (.appN f ys) = none) →
    (VExpr.appN f xs).restore R ren = VExpr.appN (f.restore R ren) (xs.map (·.restore R ren))
  | _, [], _ => rfl
  | f, x :: xs, hf => by
    have h1 := restore_appN_gen (f := .app f x) xs fun ys => hf (x :: ys)
    simp only [VExpr.appN] at h1 ⊢
    rw [h1]
    have : restoreAux R (.app f x) = none := hf [x]
    simp only [restore, this, Option.getD_none, List.map_cons, VExpr.appN]

theorem restoreAux_appN_of_none {c : Name} (hc : R c = none) (ls : List VLevel) :
    ∀ xs : List VExpr, restoreAux R (.appN (.const c ls) xs) = none := by
  intro xs; simp [restoreAux, constSpine?_appN, hc]

/-- A constant that is not auxiliary, applied to arguments, restores argument by argument. -/
theorem restore_appN_of_none {c : Name} (hc : R c = none) (ls : List VLevel) (xs : List VExpr) :
    (VExpr.appN (.const c ls) xs).restore R ren =
      VExpr.appN ((VExpr.const c ls).restore R ren) (xs.map (·.restore R ren)) :=
  restore_appN_gen xs (restoreAux_appN_of_none hc ls)

theorem restore_const_of_none {c : Name} (hc : R c = none) (hr : ren c = none)
    (ls : List VLevel) : (VExpr.const c ls).restore R ren = .const c ls := by
  simp [restore, hr, restoreAux, constSpine?, hc]

theorem constSpine?_appN_bvar (i : Nat) : ∀ xs : List VExpr,
    (VExpr.appN (.bvar i) xs).constSpine? = none := by
  intro xs
  suffices ∀ f : VExpr, f.constSpine? = none → (VExpr.appN f xs).constSpine? = none from
    this _ rfl
  induction xs with
  | nil => intro f h; exact h
  | cons x xs ih => intro f h; exact ih _ (by simp [constSpine?, h])

/-- A variable applied to arguments restores argument by argument. -/
theorem restore_appN_bvar (i : Nat) (xs : List VExpr) :
    (VExpr.appN (.bvar i) xs).restore R ren = VExpr.appN (.bvar i) (xs.map (·.restore R ren)) :=
  restore_appN_gen xs fun ys => by simp [restoreAux, constSpine?_appN_bvar]

theorem restore_app_appN_bvar (i : Nat) (xs : List VExpr) (a : VExpr) :
    (VExpr.app (.appN (.bvar i) xs) a).restore R ren =
      .app (.appN (.bvar i) (xs.map (·.restore R ren))) (a.restore R ren) := by
  have := restore_appN_bvar (R := R) (ren := ren) i (xs ++ [a])
  simpa [VExpr.appN_append] using this

theorem restore_foralls : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.foralls As B).restore R ren = .foralls (As.map (·.restore R ren)) (B.restore R ren)
  | [], _ => rfl
  | A :: As, B => by simp [VExpr.foralls, restore, restore_foralls As B]

theorem restore_lams : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.lams As B).restore R ren = .lams (As.map (·.restore R ren)) (B.restore R ren)
  | [], _ => rfl
  | A :: As, B => by simp [VExpr.lams, restore, restore_lams As B]

theorem restore_bvars (n k : Nat) : (bvars n k).map (·.restore R ren) = bvars n k := by
  simp [bvars, restore]

theorem restore_liftTele (m : Nat) : ∀ (As : List VExpr) (k : Nat),
    (liftTele m As k).map (·.restore R ren) = liftTele m (As.map (·.restore R ren)) k
  | [], _ => rfl
  | A :: As, k => by simp [liftTele, restore_liftN, restore_liftTele m As (k + 1)]

theorem restore_reseat (e : VExpr) (a k m b l : Nat) :
    (e.reseat a k m b l).restore R ren = (e.restore R ren).reseat a k m b l := by
  simp [reseat, restore_liftN]

theorem restore_ren_none : ∀ {e : VExpr}, e.ConstsSat (ren · = none) →
    e.restore R ren = e.restore R fun _ => none
  | .bvar _, _ | .sort _, _ => rfl
  | .const c ls, h => by simp [restore, show ren c = none from h]
  | .app f a, h => by
    simp only [restore, restore_ren_none h.1, restore_ren_none h.2]
  | .lam .., h | .forallE .., h => by simp [restore, restore_ren_none h.1, restore_ren_none h.2]
  | .proj _ _ e, h => by simp [restore, restore_ren_none (e := e) h]

end VExpr

/-- What restoring a translated block `d` with `n` own types assumes of the replacement `R`, the
renaming `ren` and the constructor names `cname`: the translation is flat; its own types and
constructors are left alone; its `k`th auxiliary type and its constructors are replaced, at the
block's parameters, by the occurrence `ns[k]` and its type's constructors; and the auxiliary types'
recursors are renamed to the restored block's. -/
structure VInductDecl.RestoreSpec (d : VInductDecl) (R : Name → Option VAuxHead)
    (ren : Name → Option Name) (n : Nat) (ns : List VNested) (cname : Name → Name) : Prop where
  flat : d.aux = []
  len : d.types.length = n + ns.length
  nested : ∀ T ∈ d.types, T.nested = none
  own : ∀ j T, j < n → d.types[j]? = some T → R T.name = none ∧ ren T.name = none ∧
    ∀ c ∈ T.ctors, R c.name = none ∧ ren c.name = none ∧ cname c.name = c.name
  aux : ∀ k T o, d.types[n + k]? = some T → ns[k]? = some o →
    R T.name = some ⟨d.params.length, o.ind, o.lvls, o.args⟩ ∧ ren T.name = none ∧
    ∀ c ∈ T.ctors, R c.name = some ⟨d.params.length, cname c.name, o.lvls, o.args⟩ ∧
      ren c.name = none
  recOwn : ∀ j, j < n → R (d.recName j) = none ∧ ren (d.recName j) = none
  recAux : ∀ j, n ≤ j → j < d.types.length → R (d.recName j) = none ∧
    ren (d.recName j) = some ((d.restoreNested R ren n ns cname).recName j)

namespace VInductDecl
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name}

theorem restoreNested_allTypes :
    (d.restoreNested R ren n ns cname).allTypes =
      d.types.zipIdx.map fun p => p.1.restore R ren cname (nestedAt n ns p.2) := by
  simp only [allTypes, restoreNested, ← List.map_append, List.take_append_drop]

theorem restoreNested_allTypes_getElem? (H : d.RestoreSpec R ren n ns cname) {j : Nat} :
    (d.restoreNested R ren n ns cname).allTypes[j]? =
      d.allTypes[j]?.map (·.restore R ren cname (nestedAt n ns j)) := by
  rw [restoreNested_allTypes, allTypes_of_aux H.flat, List.getElem?_map, List.getElem?_zipIdx]
  cases d.types[j]? <;> simp

theorem restoreNested_allTypes_length :
    (d.restoreNested R ren n ns cname).allTypes.length = d.types.length := by
  rw [restoreNested_allTypes]; simp

theorem restoreNested_allCtors (H : d.RestoreSpec R ren n ns cname) :
    (d.restoreNested R ren n ns cname).allCtors =
      d.allCtors.map fun p => (p.1, p.2.restore R ren cname) := by
  have hz : ∀ (L : List VInductiveType) (f : VInductiveType × Nat → VInductiveType),
      (L.zipIdx.map f).zipIdx = L.zipIdx.map fun p => (f p, p.2) := by
    intro L f
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getElem_zipIdx]
  simp only [allCtors, restoreNested_allTypes, allTypes_of_aux H.flat, hz, List.map_flatten,
    List.map_map]
  congr 1
  refine List.map_congr_left fun ⟨T, j⟩ _ => ?_
  simp [VInductiveType.restore]

theorem restoreNested_allCtors_length (H : d.RestoreSpec R ren n ns cname) :
    (d.restoreNested R ren n ns cname).allCtors.length = d.allCtors.length := by
  rw [restoreNested_allCtors H]; simp

theorem restoreNested_params_length :
    (d.restoreNested R ren n ns cname).params.length = d.params.length := by
  simp [restoreNested]

theorem RestoreSpec.nestedAt_aux (H : d.RestoreSpec R ren n ns cname) {j : Nat} {T}
    (hj : d.types[j]? = some T) (hn : n ≤ j) :
    ∃ o, ns[j - n]? = some o ∧ nestedAt n ns j = some o ∧
      R T.name = some ⟨d.params.length, o.ind, o.lvls, o.args⟩ ∧ ren T.name = none ∧
      ∀ c ∈ T.ctors, R c.name = some ⟨d.params.length, cname c.name, o.lvls, o.args⟩ ∧
        ren c.name = none := by
  have hlt := (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨o, ho⟩ : ∃ o, ns[j - n]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by have := H.len; omega)⟩
  have hj' : d.types[n + (j - n)]? = some T := by rwa [Nat.add_sub_cancel' hn]
  exact ⟨o, ho, by simp [nestedAt, show ¬j < n by omega, ho], H.aux _ _ _ hj' ho⟩

theorem RestoreSpec.restore_typeApp (H : d.RestoreSpec R ren n ns cname) {j : Nat} {T}
    (hj : d.types[j]? = some T) (ls : List VLevel) {ps : List VExpr}
    (hps : ps.length = d.params.length) (hpc : ps.map (·.restore R ren) = ps)
    (idx : List VExpr) :
    (T.typeApp ls ps idx).restore R ren =
      (T.restore R ren cname (nestedAt n ns j)).typeApp ls ps (idx.map (·.restore R ren)) := by
  have hT := H.nested T (List.mem_of_getElem? hj)
  rw [VInductiveType.typeApp_of_none hT]
  by_cases hn : j < n
  · obtain ⟨hR, hr, -⟩ := H.own j T hn hj
    have hna : nestedAt n ns j = none := by simp [nestedAt, hn]
    rw [VExpr.restore_appN_of_none hR, VExpr.restore_const_of_none hR hr, List.map_append, hpc,
      VInductiveType.typeApp_of_none (by simp [VInductiveType.restore, hna])]
    rfl
  · obtain ⟨o, -, hna, hR, hr, -⟩ := H.nestedAt_aux hj (by omega)
    rw [VExpr.restore_appN hR hr ls hps, VInductiveType.typeApp_eq,
      VInductiveType.typeHead_eq_inst (n := o) (by simp [VInductiveType.restore, hna])
        d.params.length]

theorem RestoreSpec.restore_ctorApp (H : d.RestoreSpec R ren n ns cname) {j : Nat} {T}
    (hj : d.types[j]? = some T) {c : VConstructor} (hc : c ∈ T.ctors) (ls : List VLevel)
    {ps : List VExpr} (hps : ps.length = d.params.length) (hpc : ps.map (·.restore R ren) = ps)
    (fs : List VExpr) :
    (T.ctorApp c ls ps fs).restore R ren =
      (T.restore R ren cname (nestedAt n ns j)).ctorApp (c.restore R ren cname) ls ps
        (fs.map (·.restore R ren)) := by
  have hT := H.nested T (List.mem_of_getElem? hj)
  rw [VInductiveType.ctorApp_of_none hT]
  by_cases hn : j < n
  · obtain ⟨-, -, hcs⟩ := H.own j T hn hj
    obtain ⟨hR, hr, hcn⟩ := hcs c hc
    have hna : nestedAt n ns j = none := by simp [nestedAt, hn]
    rw [VExpr.restore_appN_of_none hR, VExpr.restore_const_of_none hR hr, List.map_append, hpc,
      VInductiveType.ctorApp_of_none (by simp [VInductiveType.restore, hna])]
    simp [VConstructor.restore, hcn]
  · obtain ⟨o, -, hna, -, -, hcs⟩ := H.nestedAt_aux hj (by omega)
    obtain ⟨hR, hr⟩ := hcs c hc
    rw [VExpr.restore_appN hR hr ls hps, VInductiveType.ctorApp_eq,
      VInductiveType.ctorHead_eq_inst (n := o) (by simp [VInductiveType.restore, hna]) _
        d.params.length]
    rfl

theorem _root_.Lean4Lean.VField.restore_recArg (f : VField) :
    (f.restore R ren).recArg = f.recArg.map (·.restore R ren) := rfl

theorem _root_.Lean4Lean.VConstructor.recFields_restore (c : VConstructor) :
    (c.restore R ren cname).recFields = c.recFields.map fun p => (p.1, p.2.restore R ren) := by
  simp only [VConstructor.recFields, VConstructor.restore]
  generalize 0 = k
  induction c.fields generalizing k with
  | nil => rfl
  | cons f fs ih =>
    rw [List.map_cons, List.zipIdx_cons, List.zipIdx_cons, List.filterMap_cons,
      List.filterMap_cons, VField.restore_recArg]
    rcases f.recArg with _ | ra
    · exact ih _
    · simp only [Option.map_some, List.map_cons, ih]

section
variable (H : d.RestoreSpec R ren n ns cname) (ls : List VLevel) (v : VLevel)
include H

theorem RestoreSpec.restore_motiveType {j : Nat} {T} (hj : d.types[j]? = some T) :
    (d.motiveType ls v j T).restore R ren =
      (d.restoreNested R ren n ns cname).motiveType ls v j
        (T.restore R ren cname (nestedAt n ns j)) := by
  simp only [motiveType, VExpr.restore_foralls, VExpr.restore_liftTele, List.map_map,
    Function.comp_def, VExpr.restore_instL, restore]
  rw [H.restore_typeApp hj ls (ps := bvars d.params.length (j + T.indices.length)) (by simp)
    (VExpr.restore_bvars ..), VExpr.restore_bvars]
  simp [restoreNested_params_length, VInductiveType.restore, List.map_map, Function.comp_def]

theorem RestoreSpec.restore_motiveTypes :
    (d.motiveTypes ls v).map (·.restore R ren) =
      (d.restoreNested R ren n ns cname).motiveTypes ls v := by
  simp only [motiveTypes, restoreNested_allTypes, allTypes_of_aux H.flat, List.map_map]
  have hz : ∀ (L : List VInductiveType) (f : VInductiveType × Nat → VInductiveType),
      (L.zipIdx.map f).zipIdx = L.zipIdx.map fun p => (f p, p.2) := by
    intro L f
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getElem_zipIdx]
  rw [hz, List.map_map]
  refine List.map_congr_left fun ⟨T, j⟩ hp => ?_
  have := List.mem_zipIdx' hp
  exact H.restore_motiveType ls v (List.getElem?_eq_some_iff.2 ⟨this.1, this.2.symm⟩)

theorem RestoreSpec.restore_ctorAppAt {j : Nat} {T} (hj : d.types[j]? = some T)
    {c : VConstructor} (hc : c ∈ T.ctors) {ps : List VExpr}
    (hps : ps.length = d.params.length) (hpc : ps.map (·.restore R ren) = ps) (fs : List VExpr) :
    (d.ctorAppAt j c ls ps fs).restore R ren =
      (d.restoreNested R ren n ns cname).ctorAppAt j (c.restore R ren cname) ls ps
        (fs.map (·.restore R ren)) := by
  simp only [ctorAppAt, restoreNested_allTypes_getElem? H, allTypes_of_aux H.flat, hj,
    Option.map_some, Option.getD_some]
  exact H.restore_ctorApp hj hc ls hps hpc fs

theorem RestoreSpec.restore_minorType {q j : Nat} {T} (hj : d.types[j]? = some T)
    {c : VConstructor} (hc : c ∈ T.ctors) :
    (d.minorType ls q j c).restore R ren =
      (d.restoreNested R ren n ns cname).minorType ls q j (c.restore R ren cname) := by
  simp only [minorType, VConstructor.recFields_restore, restoreNested_allTypes_length,
    allTypes_of_aux H.flat, restoreNested_params_length]
  rw [VExpr.restore_foralls, VExpr.restore_app_appN_bvar,
    H.restore_ctorAppAt ls hj hc (by simp) (VExpr.restore_bvars ..), VExpr.restore_bvars]
  simp only [List.map_append, VExpr.restore_liftTele, List.map_map, Function.comp_def,
    VExpr.restore_instL, VExpr.restore_reseat, VExpr.restore_foralls,
    VExpr.restore_app_appN_bvar, VExpr.restore_appN_bvar, VExpr.restore_bvars]
  simp [VConstructor.restore, VField.restore, VRecArg.restore, List.map_map, Function.comp_def,
    List.zipIdx_map, List.length_map]

theorem RestoreSpec.restore_minorTypes :
    (d.minorTypes ls).map (·.restore R ren) =
      (d.restoreNested R ren n ns cname).minorTypes ls := by
  simp only [minorTypes, restoreNested_allCtors H, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun ⟨⟨j, c⟩, q⟩ hp => ?_
  obtain ⟨T, hT, hc⟩ := mem_allCtors_iff.1 (List.fst_mem_of_mem_zipIdx hp)
  rw [allTypes_of_aux H.flat] at hT
  exact H.restore_minorType ls hT hc

theorem RestoreSpec.restore_recBinders :
    (d.recBinders ls v).map (·.restore R ren) =
      (d.restoreNested R ren n ns cname).recBinders ls v := by
  simp only [recBinders, List.map_append, H.restore_motiveTypes, H.restore_minorTypes,
    List.map_map, Function.comp_def, VExpr.restore_instL]
  simp [restoreNested, List.map_map, Function.comp_def]

theorem RestoreSpec.restore_recType {i : Nat} {Ti} (hi : d.types[i]? = some Ti) :
    (d.recType ls v i Ti).restore R ren =
      (d.restoreNested R ren n ns cname).recType ls v i
        (Ti.restore R ren cname (nestedAt n ns i)) := by
  simp only [recType, restoreNested_allTypes_length, allTypes_of_aux H.flat,
    restoreNested_allCtors_length H, restoreNested_params_length]
  rw [VExpr.restore_foralls, List.map_append, H.restore_recBinders, VExpr.restore_liftTele,
    show ∀ A B : VExpr, (VExpr.forallE A B).restore R ren = .forallE (A.restore R ren)
      (B.restore R ren) from fun _ _ => rfl,
    H.restore_typeApp hi ls (ps := bvars d.params.length _) (by simp) (VExpr.restore_bvars ..),
    VExpr.restore_bvars]
  have := VExpr.restore_app_appN_bvar (R := R) (ren := ren)
    (1 + Ti.indices.length + d.allCtors.length + (d.types.length - 1 - i))
    (bvars Ti.indices.length 1) (.bvar 0)
  rw [VExpr.restore_bvars] at this
  rw [this]
  simp [VInductiveType.restore, List.map_map, Function.comp_def, VExpr.restore_instL, restore]

theorem RestoreSpec.recName_own {j : Nat} (hj : j < n) :
    (d.restoreNested R ren n ns cname).recName j = d.recName j := by
  have hl := H.len
  have hlt : j < (d.types.zipIdx.take n).length := by simp; omega
  simp only [recName, restoreNested, List.length_map, hlt, dif_pos, show j < d.types.length by omega]
  simp [VInductiveType.restore, List.getElem_take, List.getElem_zipIdx]

theorem RestoreSpec.restore_recConst (recLs : List VLevel) {j : Nat} (hj : j < d.types.length) :
    (d.recConst recLs j).restore R ren = (d.restoreNested R ren n ns cname).recConst recLs j := by
  simp only [recConst, restore]
  by_cases hn : j < n
  · obtain ⟨hR, hr⟩ := H.recOwn j hn
    simp [hr, restoreAux, constSpine?, hR, H.recName_own hn]
  · obtain ⟨-, hr⟩ := H.recAux j (by omega) hj
    simp [hr]

theorem RestoreSpec.restore_appN_recConst (recLs : List VLevel) {j : Nat}
    (hj : j < d.types.length) (xs : List VExpr) :
    (VExpr.appN (d.recConst recLs j) xs).restore R ren =
      VExpr.appN ((d.restoreNested R ren n ns cname).recConst recLs j)
        (xs.map (·.restore R ren)) := by
  have hR : R (d.recName j) = none := by
    by_cases hn : j < n
    · exact (H.recOwn j hn).1
    · exact (H.recAux j (by omega) hj).1
  rw [recConst, VExpr.restore_appN_of_none hR, ← recConst, H.restore_recConst recLs hj]

theorem RestoreSpec.restore_iotaRule_rhs (recLs : List VLevel) {q j : Nat} {c : VConstructor}
    (hra : ∀ p ∈ c.recFields, p.2.typeIdx < d.types.length) :
    (d.iotaRule ls v recLs q j c).rhs.restore R ren =
      ((d.restoreNested R ren n ns cname).iotaRule ls v recLs q j (c.restore R ren cname)).rhs := by
  simp only [iotaRule, VConstructor.recFields_restore, restoreNested_allTypes_length,
    allTypes_of_aux H.flat, restoreNested_allCtors_length H, restoreNested_params_length]
  rw [VExpr.restore_lams, List.map_append, H.restore_recBinders, VExpr.restore_liftTele,
    VExpr.restore_appN_bvar, List.map_append, VExpr.restore_bvars]
  have hfl : (c.restore R ren cname).fields.length = c.fields.length := by
    simp [VConstructor.restore]
  rw [hfl]
  congr 3
  · simp [VConstructor.restore, VField.restore, List.map_map, Function.comp_def,
      VExpr.restore_instL]
  · simp only [List.map_map]
    refine List.map_congr_left fun ⟨k, ra⟩ hp => ?_
    have hlt := hra _ hp
    simp only [Function.comp_apply, VExpr.restore_lams, VRecArg.restore]
    have e := H.restore_appN_recConst recLs hlt
      (bvars d.params.length (d.types.length + d.allCtors.length + c.fields.length +
          ra.binders.length) ++
        bvars d.types.length (d.allCtors.length + c.fields.length + ra.binders.length) ++
        bvars d.allCtors.length (c.fields.length + ra.binders.length) ++
        ra.indices.map (fun e => (e.instL ls).reseat (d.types.length + d.allCtors.length) k
          c.fields.length 0 ra.binders.length) ++
        [.appN (.bvar (ra.binders.length + (c.fields.length - 1 - k))) (bvars ra.binders.length 0)])
    rw [VExpr.appN_append_singleton] at e
    rw [e]
    simp [List.map_map, Function.comp_def, VExpr.restore_instL, VExpr.restore_reseat,
      VExpr.restore_bvars, VExpr.restore_appN_bvar, VExpr.appN_append, List.zipIdx_map]

end

end VInductDecl

/-! ### Carrying the translation's judgments to the restored block -/

/-- A context of binders above `Γ₀`, each with its auxiliary constants at the parameters. -/
def VExpr.CtxAuxAt (R : Name → Option VAuxHead) (ls₀ : List VLevel) : List VExpr → Prop
  | [] => True
  | A :: Δ => A.AuxAt R ls₀ Δ.length ∧ CtxAuxAt R ls₀ Δ

theorem VExpr.CtxAuxAt.of_append {R : Name → Option VAuxHead} {ls₀ : List VLevel} {Δ : List VExpr} :
    ∀ {L : List VExpr}, VExpr.CtxAuxAt R ls₀ (L ++ Δ) → VExpr.CtxAuxAt R ls₀ Δ
  | [], h => h
  | _ :: _, h => of_append h.2

namespace VExpr
variable {R : Name → Option VAuxHead} {ls₀ : List VLevel}

theorem AuxAt.spine_le : ∀ {k : Nat} {e : VExpr}, e.AuxAt R ls₀ k →
    ∀ {c ls xs h}, e.constSpine? = some (c, ls, xs) → R c = some h → h.n ≤ xs.length
  | _, .const c ls, H, _, _, _, _, hs, hR => by
    simp only [VExpr.constSpine?, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    simp only [VExpr.AuxAt, hR] at H; simp [H.1]
  | k, .app f a, H, c, ls, xs, h, hs, hR => by
    simp only [VExpr.AuxAt] at H
    rw [hs] at H; simp only [hR] at H
    split at H
    · omega
    · simp only [VExpr.constSpine?, Option.map_eq_some_iff] at hs
      obtain ⟨⟨c', ls', ys⟩, hs', e⟩ := hs
      simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
      have := AuxAt.spine_le H.1 hs' hR; simp; omega
  | _, .bvar _, _, _, _, _, _, hs, _ | _, .sort _, _, _, _, _, _, hs, _
  | _, .lam .., _, _, _, _, _, hs, _ | _, .forallE .., _, _, _, _, _, hs, _
  | _, .proj .., _, _, _, _, _, hs, _ => by simp [VExpr.constSpine?] at hs

theorem AuxAt.app' {k : Nat} {f a : VExpr} (hf : f.AuxAt R ls₀ k) (ha : a.AuxAt R ls₀ k) :
    (VExpr.app f a).AuxAt R ls₀ k := by
  simp only [VExpr.AuxAt]
  split
  · rename_i c ls xs hs
    split
    · rename_i h hR
      rw [if_neg]
      · exact ⟨hf, ha⟩
      · intro hl
        simp only [VExpr.constSpine?, Option.map_eq_some_iff] at hs
        obtain ⟨⟨c', ls', ys⟩, hs', e⟩ := hs
        simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
        have := AuxAt.spine_le hf hs' hR; simp at hl; omega
    · exact ⟨hf, ha⟩
  · exact ⟨hf, ha⟩

theorem AuxAt.of_constsSat : ∀ {e : VExpr} {k}, e.ConstsSat (R · = none) → e.AuxAt R ls₀ k
  | .bvar _, _, _ | .sort _, _, _ => trivial
  | .const c ls, _, H => by simp [AuxAt, show R c = none from H]
  | .app f a, _, H => AuxAt.app' (AuxAt.of_constsSat H.1) (AuxAt.of_constsSat H.2)
  | .lam .., _, H | .forallE .., _, H => ⟨AuxAt.of_constsSat H.1, AuxAt.of_constsSat H.2⟩
  | .proj _ _ e, _, H => AuxAt.of_constsSat (e := e) H

theorem AuxAt.appN' {k : Nat} {f : VExpr} (hf : f.AuxAt R ls₀ k) :
    ∀ {ys : List VExpr}, (∀ y ∈ ys, y.AuxAt R ls₀ k) → (VExpr.appN f ys).AuxAt R ls₀ k
  | [], _ => hf
  | _ :: _, hys => AuxAt.appN' (f := .app _ _) (AuxAt.app' hf (hys _ (.head _)))
      fun y hy => hys y (.tail _ hy)

/-- An auxiliary constant at the parameters, then applied further. -/
theorem AuxAt.appN_aux {k : Nat} {c : Name} {h : VAuxHead} (hc : R c = some h)
    {ys : List VExpr} (hys : ∀ y ∈ ys, y.AuxAt R ls₀ k) :
    (VExpr.appN (.const c ls₀) (bvars h.n k ++ ys)).AuxAt R ls₀ k := by
  rw [VExpr.appN_append]
  refine AuxAt.appN' ?_ hys
  by_cases hn : h.n = 0
  · rw [hn]; simp [bvars, AuxAt, hc, hn]
  · obtain ⟨xs, x, hx⟩ : ∃ xs x, bvars h.n k = xs ++ [x] := by
      have := (List.eq_nil_or_concat (bvars h.n k)).resolve_left fun e => by
        have := congrArg List.length e; simp at this; omega
      simpa using this
    rw [hx, VExpr.appN_append_singleton]
    unfold VExpr.AuxAt
    rw [← VExpr.appN_append_singleton, ← hx, constSpine?_appN]
    simp [hc]

theorem constsSat_of_mentions {ns : List Name} : ∀ {e : VExpr}, e.mentions ns = false →
    e.ConstsSat (· ∉ ns)
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => by show c ∉ ns; simpa [mentions] using h
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    exact ⟨constsSat_of_mentions h.1, constsSat_of_mentions h.2⟩
  | .proj _ _ e, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    exact constsSat_of_mentions (e := e) h.2

end VExpr

namespace VEnv
variable {env : VEnv}

theorem ConstsSat.inst {p : Name → Prop} {e a : VExpr} {k : Nat} (he : e.ConstsSat p)
    (ha : a.ConstsSat p) : (e.inst a k).ConstsSat p := by
  rw [instN_eq]
  refine he.subst fun i => ?_
  induction k generalizing i with
  | zero => cases i <;> simp [Subst.liftN, Subst.cons, Subst.id, VExpr.ConstsSat, ha]
  | succ k ih =>
    cases i with
    | zero => trivial
    | succ i => exact (ih i).liftN

variable! {p : Name → Prop} (henv : OnTypes env fun _ e A => e.ConstsSat p ∧ A.ConstsSat p)
  (hc : ∀ {c ci}, env.constants c = some ci → p c) in
/-- The constants of a judgment's terms, from those of the environment's types and rules. -/
theorem IsDefEq.constsSat' (H : env.IsDefEq U Γ e1 e2 A) (hΓ : OnCtx Γ fun _ A => A.ConstsSat p) :
    e1.ConstsSat p ∧ e2.ConstsSat p ∧ A.ConstsSat p := by
  induction H with
  | bvar h => exact ⟨trivial, trivial, hΓ.lookup h fun h => h.liftN⟩
  | constDF h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨hc h1, hc h1, h.instL⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, ConstsSat.inst hB ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 ⟨hΓ, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, ConstsSat.inst he he', ConstsSat.inst hB he'⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, he.liftN, trivial⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨hl.instL, hr.instL, hA.instL⟩
  | projDF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih2 ih3 =>
    exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih3 hΓ).1⟩
  | projIota _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ih3 =>
    exact ⟨(ih1 hΓ).1, (ih3 hΓ).1, (ih3 hΓ).2.2⟩
  | projEta _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact ⟨(ih1 hΓ).1, (ih2 hΓ).1, (ih1 hΓ).2.2⟩

/-- An ordered environment's types and rules mention only its constants. -/
theorem Ordered.constsSat (H : env.Ordered) :
    env.OnTypes fun _ e A => e.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome) := by
  refine H.induction (fun env _ e A => e.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome)) (fun {env₁ env₂ _ _ _} hle h => ?_)
    (fun _ ih h => ?_)
  · have hm : ∀ c, (env₁.constants c).isSome = true → (env₂.constants c).isSome = true := by
      intro c hc
      obtain ⟨ci, e⟩ := Option.isSome_iff_exists.1 hc
      rw [hle.constants e]; rfl
    exact ⟨h.1.mono hm, h.2.mono hm⟩
  · have := IsDefEq.constsSat' ih (fun h => by simp [h]) h trivial
    exact ⟨this.1, this.2.2⟩

/-- A judgment of an ordered environment mentions only its constants. -/
theorem IsDefEq.constsSat (henv : env.Ordered) (H : env.IsDefEq U Γ e1 e2 A)
    (hΓ : OnCtx Γ fun _ A => A.ConstsSat (env.constants · |>.isSome)) :
    e1.ConstsSat (env.constants · |>.isSome) ∧ e2.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome) :=
  IsDefEq.constsSat' henv.constsSat (fun h => by simp [h]) H hΓ

end VEnv

/-- What carrying the translation's judgments over `E₁`, which has the auxiliary types as
constants, to the restored terms over `E₀` takes: the constant substitution `F` replacing each
auxiliary constant by the occurrence as a function of the parameters (`replaceConst_restore`), and
the parameter context `Γ₀`, which mentions no auxiliary constant. -/
structure RestoreEnv (E₁ E₀ : VEnv) (U : Nat) (F : Name → Option VExpr)
    (R : Name → Option VAuxHead) (ls₀ : List VLevel) (Γ₀ : List VExpr) : Prop where
  wf : E₀.WF
  subst : VEnv.ConstSubst F E₁ E₀
  hFR : ∀ c, R c = none → F c = none
  hR : ∀ c h, R c = some h → ∃ Ps, F c = some (h.lam Ps) ∧ Ps.length = h.n ∧
    (∀ a ∈ h.args, a.ClosedN h.n) ∧ VExpr.WF E₀ U [] ((h.lam Ps).instL ls₀) ∧
    VEnv.Ctx.SubstEq E₀ U Γ₀ .id .id (Ps.map (·.instL ls₀)).reverse
  ctx : OnCtx Γ₀ (E₀.IsType U)
  ctx₀ : Γ₀.map (·.replaceConst F) = Γ₀

namespace RestoreEnv
variable {E₁ E₀ : VEnv} {U : Nat} {F : Name → Option VExpr} {R : Name → Option VAuxHead}
  {ls₀ : List VLevel} {Γ₀ : List VExpr} (H : RestoreEnv E₁ E₀ U F R ls₀ Γ₀)
include H

theorem replaceConst_ctx {Δ : List VExpr} :
    (Δ ++ Γ₀).map (·.replaceConst F) = Δ.map (·.replaceConst F) ++ Γ₀ := by
  rw [List.map_append, H.ctx₀]

/-- A context of the translation, carried over. -/
theorem onCtx : ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₀) (E₁.IsType U) →
    OnCtx (Δ.map (·.replaceConst F) ++ Γ₀) (E₀.IsType U)
  | [], _ => by simpa using H.ctx
  | A :: Δ, ⟨hΓ, hA⟩ => by
    have hA : E₁.IsType U (Δ ++ Γ₀) A := hA
    have hA' := hA.replaceConst H.wf.ordered H.subst
    rw [H.replaceConst_ctx] at hA'
    exact ⟨onCtx hΓ, hA'⟩

/-- A well-formed term of `E₀` whose auxiliary constants sit at the parameters is its restoration,
up to definitional equality. -/
theorem defeq {Δ : List VExpr} {e : VExpr} (hΓ : OnCtx (Δ ++ Γ₀) (E₀.IsType U))
    (he : e.AuxAt R ls₀ Δ.length) (hW : VExpr.WF E₀ U (Δ ++ Γ₀) (e.replaceConst F)) :
    E₀.IsDefEqU U (Δ ++ Γ₀) (e.replaceConst F) (e.restore R fun _ => none) :=
  VEnv.replaceConst_restore H.wf H.hFR H.hR hΓ he hW

/-- A context of the translation, carried over, is its restoration, up to definitional equality. -/
theorem ctx_defeq : ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₀) (E₁.IsType U) →
    VExpr.CtxAuxAt R ls₀ Δ →
    OnCtx (Δ.map (·.replaceConst F) ++ Γ₀) (E₀.IsType U) ∧
    VEnv.IsDefEqCtx E₀ U Γ₀ (Δ.map (·.replaceConst F) ++ Γ₀)
      (Δ.map (·.restore R fun _ => none) ++ Γ₀)
  | [], _, _ => ⟨by simpa using H.ctx, .zero⟩
  | A :: Δ, ⟨hΓ, hA⟩, ⟨hAa, hΔ⟩ => by
    have hΓ : OnCtx (Δ ++ Γ₀) (E₁.IsType U) := hΓ
    have hA : E₁.IsType U (Δ ++ Γ₀) A := hA
    obtain ⟨h1, h2⟩ := ctx_defeq hΓ hΔ
    have hA' := hA.replaceConst H.wf.ordered H.subst
    rw [H.replaceConst_ctx] at hA'
    obtain ⟨u, hu⟩ := hA'
    have hd := H.defeq (e := A) h1 (by simpa using hAa) ⟨_, hu⟩
    refine ⟨⟨h1, _, hu⟩, .succ h2 (hd.of_l H.wf h1 hu)⟩

/-- A typing of the translation, carried to the restored terms. -/
theorem hasType {Δ : List VExpr} {e A : VExpr} (hΓ : OnCtx (Δ ++ Γ₀) (E₁.IsType U))
    (hΔ : VExpr.CtxAuxAt R ls₀ Δ) (he : e.AuxAt R ls₀ Δ.length) (hA : A.AuxAt R ls₀ Δ.length)
    (h : E₁.HasType U (Δ ++ Γ₀) e A) :
    E₀.HasType U (Δ.map (·.restore R fun _ => none) ++ Γ₀) (e.restore R fun _ => none)
      (A.restore R fun _ => none) := by
  obtain ⟨h1, h2⟩ := H.ctx_defeq hΓ hΔ
  have h' := h.replaceConst H.wf.ordered H.subst
  rw [H.replaceConst_ctx] at h'
  have hl : (Δ.map (·.replaceConst F)).length = Δ.length := by simp
  have he2 : e.AuxAt R ls₀ (Δ.map fun x => x.replaceConst F).length := by rw [hl]; exact he
  have hA2 : A.AuxAt R ls₀ (Δ.map fun x => x.replaceConst F).length := by rw [hl]; exact hA
  have he' := H.defeq h1 he2 ⟨_, h'⟩
  have hAT := h'.isType H.wf.ordered h1
  have hA' := H.defeq h1 hA2 (let ⟨_, h⟩ := hAT; ⟨_, h⟩)
  have := (h'.defeqU_l H.wf h1 he').defeqU_r H.wf h1 hA'
  exact this.defeqDFC H.wf.ordered h2

theorem isType {Δ : List VExpr} {A : VExpr} (hΓ : OnCtx (Δ ++ Γ₀) (E₁.IsType U))
    (hΔ : VExpr.CtxAuxAt R ls₀ Δ) (hA : A.AuxAt R ls₀ Δ.length) (h : E₁.IsType U (Δ ++ Γ₀) A) :
    E₀.IsType U (Δ.map (·.restore R fun _ => none) ++ Γ₀) (A.restore R fun _ => none) :=
  let ⟨u, h⟩ := h; ⟨u, H.hasType (A := .sort u) hΓ hΔ hA trivial h⟩

theorem isDefEqU {Δ : List VExpr} {e e' : VExpr} (hΓ : OnCtx (Δ ++ Γ₀) (E₁.IsType U))
    (hΔ : VExpr.CtxAuxAt R ls₀ Δ) (he : e.AuxAt R ls₀ Δ.length) (he' : e'.AuxAt R ls₀ Δ.length)
    (h : E₁.IsDefEqU U (Δ ++ Γ₀) e e') :
    E₀.IsDefEqU U (Δ.map (·.restore R fun _ => none) ++ Γ₀) (e.restore R fun _ => none)
      (e'.restore R fun _ => none) := by
  obtain ⟨h1, h2⟩ := H.ctx_defeq hΓ hΔ
  have h' := h.replaceConst H.wf.ordered H.subst
  rw [H.replaceConst_ctx] at h'
  have hl : (Δ.map fun x => x.replaceConst F).length = Δ.length := by simp
  have he2 : e.AuxAt R ls₀ (Δ.map fun x => x.replaceConst F).length := by rw [hl]; exact he
  have he2' : e'.AuxAt R ls₀ (Δ.map fun x => x.replaceConst F).length := by rw [hl]; exact he'
  obtain ⟨_, hh⟩ := h'
  have d1 := H.defeq h1 he2 ⟨_, hh.hasType.1⟩
  have d2 := H.defeq h1 he2' ⟨_, hh.hasType.2⟩
  exact ((d1.symm.trans H.wf h1 ⟨_, hh⟩).trans H.wf h1 d2).defeqDFC H.wf.ordered h2

/-- A telescope of the translation, carried to the restored terms: `As` sits above `Δ`, its
entries' auxiliary constants at the parameters. -/
theorem isTele : ∀ {Δ As : List VExpr}, OnCtx (Δ ++ Γ₀) (E₁.IsType U) →
    VExpr.CtxAuxAt R ls₀ (As.reverse ++ Δ) → E₁.IsTele U (Δ ++ Γ₀) As →
    E₀.IsTele U (Δ.map (·.restore R fun _ => none) ++ Γ₀) (As.map (·.restore R fun _ => none))
  | _, [], _, _, _ => .nil
  | Δ, A :: As, hΓ, hA, .cons h1 h2 => by
    have hA' : VExpr.CtxAuxAt R ls₀ (As.reverse ++ A :: Δ) := by simpa using hA
    have hAΔ : VExpr.CtxAuxAt R ls₀ (A :: Δ) := VExpr.CtxAuxAt.of_append hA'
    have h1' := H.isType hΓ hAΔ.2 hAΔ.1 h1
    exact .cons h1' (isTele (Δ := A :: Δ) ⟨hΓ, h1⟩ hA' h2)

end RestoreEnv

/-! ### The restored block's conditions on constructors -/

theorem VExpr.mentions_mono {ns ns' : List Name} (h : ∀ c ∈ ns', c ∈ ns) :
    ∀ {e : VExpr}, e.mentions ns = false → e.mentions ns' = false
  | .bvar _, _ | .sort _, _ => rfl
  | .const c _, he => by
    simp only [VExpr.mentions, List.contains_eq_mem, decide_eq_false_iff_not] at he ⊢
    exact fun hc => he (h _ hc)
  | .app f a, he | .lam f a, he | .forallE f a, he => by
    simp only [VExpr.mentions, Bool.or_eq_false_iff] at he ⊢
    exact ⟨mentions_mono h he.1, mentions_mono h he.2⟩
  | .proj s _ e, he => by
    simp only [VExpr.mentions, Bool.or_eq_false_iff, List.contains_eq_mem,
      decide_eq_false_iff_not] at he ⊢
    exact ⟨fun hc => he.1 (h _ hc), mentions_mono h he.2⟩

theorem VExpr.ConstsSat.and {p q : Name → Prop} :
    ∀ {e : VExpr}, e.ConstsSat p → e.ConstsSat q → e.ConstsSat fun c => p c ∧ q c
  | .bvar _, _, _ | .sort _, _, _ => trivial
  | .const _ _, h1, h2 => ⟨h1, h2⟩
  | .app .., h1, h2 | .lam .., h1, h2 | .forallE .., h1, h2 =>
    ⟨ConstsSat.and h1.1 h2.1, ConstsSat.and h1.2 h2.2⟩
  | .proj _ _ e, h1, h2 => ConstsSat.and (e := e) h1 h2

theorem VEnv.OnCtx.constsSat {E : VEnv} {U : Nat} (henv : E.Ordered) :
    ∀ {Γ : List VExpr}, OnCtx Γ (E.IsType U) →
      OnCtx Γ fun _ A => A.ConstsSat (E.constants · |>.isSome)
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ =>
    have ih := VEnv.OnCtx.constsSat henv h1
    ⟨ih, (VEnv.IsDefEq.constsSat henv h2 ih).1⟩

namespace VInductDecl
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name}
  {E₁ E₀ : VEnv} {F : Name → Option VExpr}

theorem restoreNested_names_sub :
    ∀ c ∈ (d.restoreNested R ren n ns cname).names, c ∈ d.names := by
  intro c hc
  simp only [names, restoreNested, List.mem_map] at hc ⊢
  obtain ⟨_, ⟨⟨T, j⟩, hm, rfl⟩, rfl⟩ := hc
  exact ⟨T, List.fst_mem_of_mem_zipIdx (List.mem_of_mem_take hm), rfl⟩

/-- Strict positivity carries from the translation to the restored block, with the auxiliary
constants replaced by the occurrences as functions of the parameters. -/
theorem RestoreSpec.positive (H : d.RestoreSpec R ren n ns cname)
    (HE : RestoreEnv E₁ E₀ d.uvars F R (VLevel.params d.uvars) d.params.reverse)
    (hE₁ : E₁.Ordered)
    (hdom : ∀ c, F c ≠ none ∨ R c ≠ none ∨ ren c ≠ none → c ∈ d.names ∨ E₁.constants c = none) :
    ∀ {Δ : List VExpr} {k : Nat} {t : VExpr}, k = Δ.length →
      d.Positive E₁ (Δ ++ d.params.reverse) k t →
      OnCtx (Δ ++ d.params.reverse) (E₁.IsType d.uvars) →
      (d.restoreNested R ren n ns cname).Positive E₀
        (Δ.map (·.replaceConst F) ++ d.params.reverse) k (t.replaceConst F) := by
  intro Δ k t hk hP hΓ
  have hsub := restoreNested_names_sub (R := R) (ren := ren) (d := d) (n := n) (ns := ns)
    (cname := cname)
  generalize hG : Δ ++ d.params.reverse = G at hP
  induction hP generalizing Δ with
  | none h1 h2 =>
    rename_i _ A _
    subst hG
    have hfree : A.ConstsSat fun c => F c = none ∧ R c = none := by
      obtain ⟨_, hA⟩ := h1
      have hA' := hA.hasType.2
      have c1 := (VEnv.IsDefEq.constsSat hE₁ hA' (VEnv.OnCtx.constsSat hE₁ hΓ)).1
      have c2 := VExpr.constsSat_of_mentions (by simpa using h2)
      refine (c1.and c2).mono fun c ⟨hc, hn⟩ => Classical.byContradiction fun hne => ?_
      rcases hdom c (by
        by_cases hF : F c = none
        · exact .inr (.inl fun hR => hne ⟨hF, hR⟩)
        · exact .inl hF) with h | h
      · exact hn h
      · simp [h] at hc
    have h1' := h1.replaceConst HE.wf.ordered HE.subst
    rw [HE.replaceConst_ctx, VExpr.replaceConst_of_constsSat (hfree.mono fun _ h => h.1)] at h1'
    exact .none h1' (by simpa using VExpr.mentions_mono hsub (by simpa using h2))
  | @pi Γ' t' A B k' h1 h2 _ ih =>
    subst hG
    obtain ⟨_, hAB⟩ := h1
    have hAt := (VEnv.HasType.forallE_inv hE₁ hAB.hasType.2).1
    have hfree : A.ConstsSat fun c => F c = none ∧ R c = none := by
      obtain ⟨_, hA'⟩ := hAt
      have c1 := (VEnv.IsDefEq.constsSat hE₁ hA' (VEnv.OnCtx.constsSat hE₁ hΓ)).1
      have c2 := VExpr.constsSat_of_mentions (by simpa using h2)
      refine (c1.and c2).mono fun c ⟨hc, hn⟩ => Classical.byContradiction fun hne => ?_
      rcases hdom c (by
        by_cases hF : F c = none
        · exact .inr (.inl fun hR => hne ⟨hF, hR⟩)
        · exact .inl hF) with h | h
      · exact hn h
      · simp [h] at hc
    have hA := VExpr.replaceConst_of_constsSat (hfree.mono fun _ h => h.1)
    have h1' := (VEnv.IsDefEqU.replaceConst HE.wf.ordered HE.subst ⟨_, hAB⟩)
    rw [HE.replaceConst_ctx] at h1'
    simp only [VExpr.replaceConst, hA] at h1'
    have ih' := ih (Δ := A :: Δ) (by simp [hk]) ⟨hΓ, hAt⟩ rfl
    simp only [List.map_cons, hA] at ih'
    exact .pi h1' (by simpa using VExpr.mentions_mono hsub (by simpa using h2)) ih'
  | @app Γ' t' k' T j is hj hlen h3 h4 =>
    subst hG
    rw [allTypes_of_aux H.flat] at hj
    have hTn := H.nested T (List.mem_of_getElem? hj)
    obtain ⟨_, h3⟩ := h3
    have hrhs := h3.hasType.2
    have cT := (VEnv.IsDefEq.constsSat hE₁ hrhs (VEnv.OnCtx.constsSat hE₁ hΓ)).1
    rw [VInductiveType.typeApp_of_none hTn, VExpr.ConstsSat.appN] at cT
    have hfree : ∀ i ∈ is, i.ConstsSat fun c => F c = none ∧ R c = none ∧ ren c = none := by
      intro i hi
      have c1 := cT.2 i (List.mem_append_right _ hi)
      have c2 := VExpr.constsSat_of_mentions (by simpa using List.all_eq_true.1 h4 i hi)
      refine (c1.and c2).mono fun c ⟨hc, hn⟩ => ?_
      refine ⟨Classical.byContradiction fun hF => ?_, Classical.byContradiction fun hR => ?_,
        Classical.byContradiction fun hr => ?_⟩ <;>
      · rcases hdom c (by simp_all) with h | h
        · exact hn h
        · simp [h] at hc
    have h3' := (VEnv.IsDefEqU.replaceConst HE.wf.ordered HE.subst ⟨_, h3⟩)
    rw [HE.replaceConst_ctx] at h3'
    have hl : (Δ.map fun x => x.replaceConst F).length = Δ.length := by simp
    have haux : (T.typeApp (VLevel.params d.uvars) (bvars d.params.length k') is).AuxAt R
        (VLevel.params d.uvars) (Δ.map fun x => x.replaceConst F).length := by
      rw [hl, ← hk, VInductiveType.typeApp_of_none hTn]
      have hisA : ∀ y ∈ is, y.AuxAt R (VLevel.params d.uvars) k' := fun y hy =>
        VExpr.AuxAt.of_constsSat ((hfree y hy).mono fun _ h => h.2.1)
      by_cases hjn : j < n
      · obtain ⟨hR, -, -⟩ := H.own j T hjn hj
        refine VExpr.AuxAt.of_constsSat ?_
        rw [VExpr.ConstsSat.appN]
        refine ⟨hR, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · simp [bvars] at hy; obtain ⟨_, _, rfl⟩ := hy; trivial
        · exact (hfree y hy).mono fun _ h => h.2.1
      · obtain ⟨o, -, -, hR, -, -⟩ := H.nestedAt_aux hj (by omega)
        exact VExpr.AuxAt.appN_aux hR hisA
    have hW := (VEnv.IsDefEqU.replaceConst HE.wf.ordered HE.subst
      ⟨_, hrhs⟩ : E₀.IsDefEqU _ _ _ _)
    rw [HE.replaceConst_ctx] at hW
    have hd := HE.defeq (HE.onCtx hΓ) haux hW
    have hisR : is.map (·.restore R ren) = is := List.map_id''' _ fun y hy =>
      VExpr.restore_of_constsSat ((hfree y hy).mono fun _ h => h.2)
    have htr : (T.typeApp (VLevel.params d.uvars) (bvars d.params.length k') is).restore R
        (fun _ => none) = (T.restore R ren cname (nestedAt n ns j)).typeApp
          (VLevel.params d.uvars) (bvars d.params.length k') is := by
      rw [← VExpr.restore_ren_none, H.restore_typeApp hj _ (by simp) (VExpr.restore_bvars ..),
        hisR]
      rw [VInductiveType.typeApp_of_none hTn, VExpr.ConstsSat.appN]
      refine ⟨?_, fun y hy => ?_⟩
      · by_cases hjn : j < n
        · exact (H.own j T hjn hj).2.1
        · obtain ⟨_, -, -, -, hr, -⟩ := H.nestedAt_aux hj (by omega)
          exact hr
      · rcases List.mem_append.1 hy with hy | hy
        · simp [bvars] at hy; obtain ⟨_, _, rfl⟩ := hy; trivial
        · exact (hfree y hy).mono fun _ h => h.2.2
    rw [htr] at hd
    refine .app (T := T.restore R ren cname (nestedAt n ns j)) (j := j) (is := is)
      (by rw [restoreNested_allTypes_getElem? H, allTypes_of_aux H.flat, hj]; rfl)
      (by simp [VInductiveType.restore, hlen]) ?_ ?_
    · rw [restoreNested_params_length]
      exact h3'.trans HE.wf (HE.onCtx hΓ) hd
    · simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      intro y hy
      exact VExpr.mentions_mono hsub (by simpa using List.all_eq_true.1 h4 y hy)

/-- Strict positivity is up to definitional equality of the type. -/
theorem Positive.defeqU {env : VEnv} (henv : env.WF) {Γ k t t'}
    (hΓ : OnCtx Γ (env.IsType d.uvars)) (h : env.IsDefEqU d.uvars Γ t t')
    (H : d.Positive env Γ k t) : d.Positive env Γ k t' := by
  cases H with
  | none h1 h2 => exact .none (h.symm.trans henv hΓ h1) h2
  | pi h1 h2 h3 => exact .pi (h.symm.trans henv hΓ h1) h2 h3
  | app h1 h2 h3 h4 => exact .app h1 h2 (h.symm.trans henv hΓ h3) h4

/-- Strict positivity is up to definitional equality of the context. -/
theorem Positive.defeqDFC {env : VEnv} (henv : env.WF) {Γ₀ Γ₁ Γ₂ : List VExpr}
    (hΓ : VEnv.IsDefEqCtx env d.uvars Γ₀ Γ₁ Γ₂) {k t} (H : d.Positive env Γ₁ k t) :
    d.Positive env Γ₂ k t := by
  induction H generalizing Γ₂ with
  | none h1 h2 => exact .none (h1.defeqDFC henv.ordered hΓ) h2
  | pi h1 h2 h3 ih =>
    rename_i A _ _
    obtain ⟨_, h1'⟩ := h1
    have hAB := h1'.hasType.2
    obtain ⟨⟨u, hA⟩, -⟩ := VEnv.HasType.forallE_inv henv.ordered hAB
    have h1'' : env.IsDefEqU d.uvars Γ₂ _ _ :=
      VEnv.IsDefEqU.defeqDFC henv.ordered hΓ ⟨_, h1'⟩
    exact .pi h1'' h2 (ih (.succ hΓ hA))
  | app h1 h2 h3 h4 => exact .app h1 h2 (h3.defeqDFC henv.ordered hΓ) h4

end VInductDecl

end Lean4Lean

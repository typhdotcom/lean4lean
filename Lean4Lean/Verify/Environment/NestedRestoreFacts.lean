import Lean4Lean.Verify.Environment.ElimNestedRun
import Lean4Lean.Verify.Environment.NestedFinal
import Lean4Lean.Verify.Environment.Constructors
import Lean4Lean.Verify.Environment.Minors
import Lean4Lean.Theory.Typing.NestedWF

/-!
# What restoring a checked nested block needs to know of it

`VInductDecl.RestoreSpec.wf` turns the flat check of a nested block's translation into the
restored block's well-formedness, given facts about the translation's terms and names. Here they
are derived from the elimination (`ElimNestedInductive.run_spec`) and from the flat check
(`AddInductive.Elaborates`, the names `AddInduct` inserts), for the tables the kernel restores
by: each auxiliary type and constructor stands for its occurrence (`VInductDecl.auxTable`), and
the auxiliary recursors are renamed as `mkAuxRecNameMap` names them.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VInductDecl

/-- The auxiliary type among the last types of `d`, the `k`th after the first `n`, whose name or
one of whose constructors' names is `c`, and the occurrence `o` it stands for. -/
def AuxAt' (d : VInductDecl) (n : Nat) (ns : List VNested) (c : Name) (k : Nat)
    (T : VInductiveType) (o : VNested) : Prop :=
  d.types[n + k]? = some T ∧ ns[k]? = some o ∧ (T.name = c ∨ ∃ c' ∈ T.ctors, c'.name = c)

open Classical in
/-- What each auxiliary type and constructor of a translated block stands for: the occurrence at
the block's parameters, its earlier type's constant or constructor `cname c`. -/
noncomputable def auxTable (d : VInductDecl) (n : Nat) (ns : List VNested) (cname : Name → Name) :
    Name → Option VAuxHead := fun c =>
  if h : ∃ o k T, d.AuxAt' n ns c k T o then
    some ⟨d.params.length, if ∃ k T, d.types[n + k]? = some T ∧ T.name = c then h.choose.ind
      else cname c, h.choose.lvls, h.choose.args⟩
  else none

theorem _root_.List.eq_of_nodup_map {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, h, _, _ => by cases h
  | x :: l, hnd, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map_of_mem hb') hnd.1
    · exact absurd (e.symm ▸ List.mem_map_of_mem ha') hnd.1
    · exact List.eq_of_nodup_map hnd.2 ha' hb' e

theorem _root_.List.nodup_map_of_inj_on {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => .nil
  | x :: l, hf, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, List.nodup_map_of_inj_on (fun a ha b hb => hf a (.tail _ ha) b (.tail _ hb))
      hnd.2⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    exact hnd.1 (hf y (.tail _ hy) x (.head _) e ▸ hy)

variable {d : VInductDecl} {n : Nat} {ns : List VNested} {cname : Name → Name}

/-- The names a translated block keeps apart: its types' among themselves, its constructors'
among themselves, and the two from each other. -/
structure NamesApart (d : VInductDecl) : Prop where
  types : (d.types.map (·.name)).Nodup
  ctors : (d.ctors.map (·.2.name)).Nodup
  apart : ∀ T ∈ d.types, ∀ T' ∈ d.types, ∀ c ∈ T'.ctors, c.name ≠ T.name

theorem NamesApart.type_index (H : d.NamesApart) {i j : Nat} {T T' : VInductiveType}
    (hi : d.types[i]? = some T) (hj : d.types[j]? = some T') (e : T.name = T'.name) : i = j := by
  have hi' := List.getElem?_eq_some_iff.1 hi
  have hj' := List.getElem?_eq_some_iff.1 hj
  have : (d.types.map (·.name))[i]? = (d.types.map (·.name))[j]? := by
    simp [List.getElem?_map, hi, hj, e]
  exact (List.getElem?_inj (by simpa using hi'.1) H.types).1 this

theorem NamesApart.ctor_index (H : d.NamesApart) {i j : Nat} {T T' : VInductiveType}
    {c c' : VConstructor} (hi : d.types[i]? = some T) (hj : d.types[j]? = some T')
    (hc : c ∈ T.ctors) (hc' : c' ∈ T'.ctors) (e : c.name = c'.name) : i = j := by
  have := List.eq_of_nodup_map (f := fun p : Nat × VConstructor => p.2.name) H.ctors
    (mem_ctors_iff.2 ⟨T, hi, hc⟩) (mem_ctors_iff.2 ⟨T', hj, hc'⟩) e
  exact congrArg Prod.fst this

/-- The occurrence a name of a translated block's auxiliary types stands for is unique. -/
theorem NamesApart.auxAt_unique (H : d.NamesApart) {c : Name} {k k' T T' o o'}
    (h : d.AuxAt' n ns c k T o) (h' : d.AuxAt' n ns c k' T' o') : k = k' ∧ T = T' ∧ o = o' := by
  obtain ⟨hT, ho, hc⟩ := h
  obtain ⟨hT', ho', hc'⟩ := h'
  have hk : k = k' := by
    have hm : n + k = n + k' := by
      rcases hc with rfl | ⟨c₁, hc₁, rfl⟩ <;> rcases hc' with e | ⟨c₂, hc₂, e⟩
      · exact H.type_index hT hT' e.symm
      · exact absurd e (H.apart T (List.mem_of_getElem? hT) T' (List.mem_of_getElem? hT') c₂ hc₂)
      · exact absurd e.symm (H.apart T' (List.mem_of_getElem? hT') T (List.mem_of_getElem? hT)
          c₁ hc₁)
      · exact H.ctor_index hT hT' hc₁ hc₂ e.symm
    omega
  subst hk
  obtain rfl : T = T' := Option.some.inj (hT.symm.trans hT')
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  exact ⟨rfl, rfl, rfl⟩

theorem auxTable_type (H : d.NamesApart) {k T o} (hT : d.types[n + k]? = some T)
    (ho : ns[k]? = some o) :
    d.auxTable n ns cname T.name = some ⟨d.params.length, o.ind, o.lvls, o.args⟩ := by
  have hA : d.AuxAt' n ns T.name k T o := ⟨hT, ho, .inl rfl⟩
  have h : ∃ o k T', d.AuxAt' n ns T.name k T' o := ⟨o, k, T, hA⟩
  unfold auxTable
  rw [dif_pos h]
  obtain ⟨k', T', hA'⟩ := h.choose_spec
  obtain ⟨-, -, rfl⟩ := H.auxAt_unique hA hA'
  rw [if_pos ⟨k, T, hT, rfl⟩]

theorem auxTable_ctor (H : d.NamesApart) {k T o c} (hT : d.types[n + k]? = some T)
    (ho : ns[k]? = some o) (hc : c ∈ T.ctors) :
    d.auxTable n ns cname c.name = some ⟨d.params.length, cname c.name, o.lvls, o.args⟩ := by
  have hA : d.AuxAt' n ns c.name k T o := ⟨hT, ho, .inr ⟨c, hc, rfl⟩⟩
  have h : ∃ o k T', d.AuxAt' n ns c.name k T' o := ⟨o, k, T, hA⟩
  unfold auxTable
  rw [dif_pos h]
  obtain ⟨k', T', hA'⟩ := h.choose_spec
  obtain ⟨-, -, rfl⟩ := H.auxAt_unique hA hA'
  rw [if_neg]
  rintro ⟨k₁, T₁, hT₁, e⟩
  exact H.apart T₁ (List.mem_of_getElem? hT₁) T (List.mem_of_getElem? hT) c hc e.symm

theorem auxTable_some {c h} (hc : d.auxTable n ns cname c = some h) :
    ∃ k T o, d.AuxAt' n ns c k T o ∧ h.n = d.params.length := by
  unfold auxTable at hc
  split at hc
  · rename_i hex
    obtain ⟨k, T, hA⟩ := hex.choose_spec
    cases hc; exact ⟨k, T, _, hA, rfl⟩
  · cases hc

theorem auxTable_none {c} (hc : ∀ k T o, ¬d.AuxAt' n ns c k T o) :
    d.auxTable n ns cname c = none := by
  unfold auxTable
  rw [dif_neg]; rintro ⟨o, k, T, h⟩; exact hc k T o h

theorem recConsts_names (hflat : d.aux = []) :
    d.recConsts.map (·.1) = (List.range d.types.length).map d.recName := by
  simp only [recConsts, allTypes_of_aux hflat, List.map_map]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem_zipIdx]

/-- The names a flat block inserts, distinct as `AddInduct` inserts them, keep its types and
constructors apart, and its recursors apart from both and from each other. -/
theorem namesApart_of_nodup (hflat : d.aux = [])
    (hnd : ((d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)).Nodup) :
    d.NamesApart ∧
      (∀ i j, i < d.types.length → j < d.types.length → d.recName i = d.recName j → i = j) ∧
      ∀ j, j < d.types.length → d.recName j ∉ d.types.map (·.name) ∧
        ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.name ≠ d.recName j := by
  simp only [List.map_append] at hnd
  obtain ⟨⟨hT, hC, hTC⟩, hR, hTCR⟩ := List.nodup_append.1 hnd |>.imp_left List.nodup_append.1
  have hTn : d.typeConsts.map (·.1) = d.types.map (·.name) := by simp [typeConsts]
  have hCn : d.ctorConsts.map (·.1) = d.ctors.map (·.2.name) := by simp [ctorConsts]
  rw [hTn] at hT hTC hTCR; rw [hCn] at hC hTC hTCR
  rw [recConsts_names hflat] at hR hTCR
  have hrmem {j} (hj : j < d.types.length) : d.recName j ∈ (List.range d.types.length).map d.recName :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  refine ⟨⟨hT, hC, fun T hT' T' hT'' c hc e => ?_⟩, fun i j hi hj e => ?_, fun j hj => ⟨fun h => ?_,
    fun T hT' c hc e => ?_⟩⟩
  · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hT''
    exact hTC _ (List.mem_map.2 ⟨T, hT', rfl⟩) _
      (List.mem_map.2 ⟨(j', c), mem_ctors_iff.2 ⟨T', hj', hc⟩, rfl⟩) e.symm
  · have := (List.getElem?_inj (l := (List.range d.types.length).map d.recName)
      (i := i) (j := j) (by simpa using hi) hR).1 (by simp [hi, hj, e])
    exact this
  · exact hTCR _ (List.mem_append_left _ h) _ (hrmem hj) rfl
  · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hT'
    exact hTCR _ (List.mem_append_right _
      (List.mem_map.2 ⟨(j', c), mem_ctors_iff.2 ⟨T, hj', hc⟩, rfl⟩)) _ (hrmem hj) e

theorem restoreNested_types_length {R ren} (hn : n ≤ d.types.length) :
    (d.restoreNested R ren n ns cname).types.length = n := by
  simp [restoreNested, Nat.min_eq_left hn]

theorem restoreNested_types_getElem? {R ren} {j : Nat} (hj : j < n) :
    (d.restoreNested R ren n ns cname).types[j]? =
      d.types[j]?.map (·.restore R ren cname none) := by
  simp only [restoreNested, List.getElem?_map, List.getElem?_take, if_pos hj, List.getElem?_zipIdx]
  cases d.types[j]? <;> simp [nestedAt, hj]

/-- The restored block names its auxiliary recursors as the kernel does: after its own first. -/
theorem restoreNested_recName {R ren} (hn : 0 < n) (hle : n ≤ d.types.length) {j : Nat}
    (hj : n ≤ j) :
    (d.restoreNested R ren n ns cname).recName j =
      (Lean.mkRecName ((d.types[0]?.map (·.name)).getD .anonymous)).appendIndexAfter
        (j - n + 1) := by
  have hl := restoreNested_types_length (R := R) (ren := ren) (ns := ns) (cname := cname) hle
  unfold recName
  rw [dif_neg (by omega), hl, restoreNested_types_getElem? hn]
  cases d.types[0]? <;> rfl

/-- The tables the kernel restores a translated block by satisfy `RestoreSpec`, given that the
recursor renaming `ren` renames exactly the auxiliary types' recursors, as the restored block
names them. -/
theorem restoreSpec_auxTable {ren : Name → Option Name} (hflat : d.aux = [])
    (hnested : ∀ T ∈ d.types, T.nested = none)
    (hnd : ((d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)).Nodup)
    (hlen : d.types.length = n + ns.length)
    (hown : ∀ j T, j < n → d.types[j]? = some T → ∀ c ∈ T.ctors, cname c.name = c.name)
    (hren : ∀ c c', ren c = some c' → ∃ j, n ≤ j ∧ j < d.types.length ∧ c = d.recName j)
    (hrenAux : ∀ j, n ≤ j → j < d.types.length →
      ren (d.recName j) = some ((d.restoreNested (d.auxTable n ns cname) ren n ns cname).recName j)) :
    d.RestoreSpec (d.auxTable n ns cname) ren n ns cname := by
  obtain ⟨HA, hRinj, hRapart⟩ := namesApart_of_nodup hflat hnd
  have hrenType : ∀ T ∈ d.types, ren T.name = none := by
    intro T hT
    cases h : ren T.name with
    | none => rfl
    | some c' =>
      obtain ⟨j, -, hj, e⟩ := hren _ _ h
      exact absurd (e ▸ List.mem_map.2 ⟨T, hT, rfl⟩) (hRapart j hj).1
  have hrenCtor : ∀ T ∈ d.types, ∀ c ∈ T.ctors, ren c.name = none := by
    intro T hT c hc
    cases h : ren c.name with
    | none => rfl
    | some c' =>
      obtain ⟨j, -, hj, e⟩ := hren _ _ h
      exact absurd e ((hRapart j hj).2 T hT c hc)
  have hRrec : ∀ j, j < d.types.length → d.auxTable n ns cname (d.recName j) = none := by
    intro j hj
    refine auxTable_none fun k T o hA => ?_
    obtain ⟨hT, -, hc⟩ := hA
    rcases hc with e | ⟨c', hc', e⟩
    · exact (hRapart j hj).1 (e ▸ List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩)
    · exact (hRapart j hj).2 T (List.mem_of_getElem? hT) c' hc' e
  refine ⟨hflat, hlen, hnested, fun j T hj hT => ?_, fun k T o hT ho => ?_, fun j hj => ?_,
    fun j hj hj' => ?_⟩
  · have hTm := List.mem_of_getElem? hT
    refine ⟨auxTable_none fun k T' o hA => ?_, hrenType T hTm, fun c hc => ?_⟩
    · obtain ⟨hT', -, hc⟩ := hA
      rcases hc with e | ⟨c', hc', e⟩
      · have := HA.type_index hT hT' e.symm; omega
      · exact HA.apart T hTm T' (List.mem_of_getElem? hT') c' hc' e
    · refine ⟨auxTable_none fun k T' o hA => ?_, hrenCtor T hTm c hc, hown j T hj hT c hc⟩
      obtain ⟨hT', -, hc'⟩ := hA
      rcases hc' with e | ⟨c', hc'', e⟩
      · exact HA.apart T' (List.mem_of_getElem? hT') T hTm c hc e.symm
      · have := HA.ctor_index hT hT' hc hc'' e.symm; omega
  · have hTm := List.mem_of_getElem? hT
    exact ⟨auxTable_type HA hT ho, hrenType T hTm, fun c hc =>
      ⟨auxTable_ctor HA hT ho hc, hrenCtor T hTm c hc⟩⟩
  · have hjl : j < d.types.length := by omega
    refine ⟨hRrec j hjl, ?_⟩
    cases h : ren (d.recName j) with
    | none => rfl
    | some c' =>
      obtain ⟨j', hj', hj'l, e⟩ := hren _ _ h
      have := hRinj j j' hjl hj'l e; omega
  · exact ⟨hRrec j hj', hrenAux j hj hj'⟩

end VInductDecl

theorem NM.get?_none_of_getD {m : NM} {n : Name}
    (h : ∀ d, m.getD n d = d) : m.get? n = none := by
  have h1 := h .anonymous
  have h2 := h `a
  rw [Std.TreeMap.getD_eq_getD_getElem?] at h1 h2
  rw [Std.TreeMap.get?_eq_getElem?]
  cases e : m[n]? with
  | none => rfl
  | some v => rw [e] at h1 h2; simp at h1 h2; rw [h1] at h2; cases h2

theorem NM.get?_some_of_getD {m : NM} {n x : Name}
    (h : ∀ d, m.getD n d = x) : m.get? n = some x := by
  have h1 := h .anonymous
  have h2 := h `a
  rw [Std.TreeMap.getD_eq_getD_getElem?] at h1 h2
  rw [Std.TreeMap.get?_eq_getElem?]
  cases e : m[n]? with
  | none => rw [e] at h1 h2; simp at h1 h2; rw [← h1] at h2; cases h2
  | some v => rw [e] at h1; simpa using h1

/-- The recursor renaming the kernel restores by, as a partial function. -/
def auxRecRen (env' : Environment) (types : List InductiveType) : Name → Option Name :=
  (mkAuxRecNameMap env' types).2.find?

/-- `mkAuxRecNameMap` renames exactly the auxiliary types' recursors of the translated block,
after the first type's recursor, as the restored block names them. -/
theorem auxRecRen_spec {env' : Environment} {T : InductiveType} {Ts : List InductiveType}
    {info : InductiveVal} {d : VInductDecl} (hflat : d.aux = [])
    (hnd : ((d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)).Nodup)
    (hf : env'.find? T.name = some (.inductInfo info)) (hall : info.all = d.types.map (·.name))
    (hlt : (T :: Ts).length < d.types.length) :
    (∀ c c', auxRecRen env' (T :: Ts) c = some c' →
      ∃ j, (T :: Ts).length ≤ j ∧ j < d.types.length ∧ c = d.recName j) ∧
    ∀ j, (T :: Ts).length ≤ j → j < d.types.length →
      auxRecRen env' (T :: Ts) (d.recName j) =
        some ((Lean.mkRecName T.name).appendIndexAfter (j - (T :: Ts).length + 1)) := by
  have hlen : (T :: Ts).length < info.all.length := by rw [hall]; simpa using hlt
  obtain ⟨h1, h2, h3⟩ := mkAuxRecNameMap_spec hf hlen
  have hL : (info.all.drop (T :: Ts).length).map Lean.mkRecName =
      ((List.range d.types.length).drop (T :: Ts).length).map d.recName := by
    rw [hall]
    refine List.ext_getElem (by simp) fun i hi hi' => ?_
    simp only [List.getElem_map, List.getElem_drop, List.getElem_range]
    have hc : (T :: Ts).length = Ts.length + 1 := rfl
    rw [VInductDecl.recName_of_types (List.getElem?_eq_getElem (by simp at hi; omega))]
  obtain ⟨-, hinj, -⟩ := VInductDecl.namesApart_of_nodup hflat hnd
  have hnd' : ((info.all.drop (T :: Ts).length).map Lean.mkRecName).Nodup := by
    rw [hL]
    refine List.nodup_map_of_inj_on (fun x hx y hy e => ?_) ((List.nodup_range).sublist (List.drop_sublist ..))
    have hx' := List.mem_range.1 (List.mem_of_mem_drop hx)
    have hy' := List.mem_range.1 (List.mem_of_mem_drop hy)
    exact hinj _ _ hx' hy' e
  refine ⟨fun c c' hc => ?_, fun j hj hj' => ?_⟩
  · have hm : c ∈ (mkAuxRecNameMap env' (T :: Ts)).1 := by
      by_contra hm
      have := NM.get?_none_of_getD (m := (mkAuxRecNameMap env' (T :: Ts)).2) fun d => h3 c d hm
      unfold auxRecRen at hc; rw [NameMap.find?] at hc
      rw [this] at hc; cases hc
    rw [h1, hL] at hm
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hj
    simp only [List.length_drop, List.length_range] at hi
    exact ⟨(T :: Ts).length + i, by omega, by omega, by simp⟩
  · unfold auxRecRen; rw [NameMap.find?]
    refine NM.get?_some_of_getD fun dflt => h2 hnd' (j - (T :: Ts).length) _ dflt ?_
    rw [hL]
    simp only [List.getElem?_map, List.getElem?_drop, Nat.add_sub_cancel' hj,
      List.getElem?_range hj', Option.map_some]

/-! ### The translated constructors' terms -/

theorem anySub_constP_of_suppIn {f : Name → Bool} : ∀ {e : Expr},
    e.SuppIn (ElimNestedInductive.ConstOnly fun c => f c = false) → e.anySub (constP f) = false
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ => rfl
  | .const c _, h => by simpa [Expr.anySub, constP] using h.1
  | .app f a, h => by
    simp [Expr.anySub, constP, anySub_constP_of_suppIn h.1, anySub_constP_of_suppIn h.2]
  | .lam _ t b _, h | .forallE _ t b _, h => by
    simp [Expr.anySub, constP, anySub_constP_of_suppIn h.1, anySub_constP_of_suppIn h.2]
  | .letE _ t v b _, h => by
    simp [Expr.anySub, constP, anySub_constP_of_suppIn h.1, anySub_constP_of_suppIn h.2.1,
      anySub_constP_of_suppIn h.2.2]
  | .mdata _ e, h | .proj _ _ e, h => by
    simp [Expr.anySub, constP, anySub_constP_of_suppIn (e := e) h]

/-- A translation of a term with its first `m` literal binders' body replaced by `b`: those
binders' translations, which mention none of `ns` where the term does not, over a translation
of `b` under them. -/
theorem TrExprS.setBody_inv {env : VEnv} {Us : List Name} (henv : env.WF) {p : Expr → Bool}
    {ns : List Name} (hns : ∀ c us, p (.const c us) = false → c ∉ ns)
    (hlit : ∀ l, env.ContainsLits l → l.toConstructor.anySub p = false)
    (hind : ∀ n b, env.inducts n = some b → n ∉ ns) :
    ∀ {m : Nat} {e b : Expr} {Δ : VLCtx} {x : VExpr}, (ElimNestedInductive.peel m e).isSome →
      e.anySub p = false → Δ.WF env Us.length → (∀ y ∈ Δ, y.2.value.mentions ns = false) →
      TrExprS env Us Δ (ElimNestedInductive.setBody m e b) x →
      ∃ As b', x = .foralls As b' ∧ As.length = m ∧ (∀ A ∈ As, A.mentions ns = false) ∧
        TrExprS env Us ((As.map fun A => (none, VLocalDecl.vlam A)).reverse ++ Δ) b b'
  | 0, _, _, _, _, _, _, _, _, H => ⟨[], _, rfl, rfl, nofun, by simpa [ElimNestedInductive.setBody] using H⟩
  | m + 1, .forallE _ dom e' _, b, Δ, x, hpe, he, hΔ, hΔv, H => by
    simp only [ElimNestedInductive.setBody] at H
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    cases H with
    | @forallE ty' body' _ _ _ _ _ h1 _ h3 h4 =>
      have hA := TrExprS.not_mentions henv hns hlit hind h3 hΔ hΔv he.1.2
      obtain ⟨As, b', rfl, hl, hm, hb⟩ := TrExprS.setBody_inv henv hns hlit hind
        (m := m) (e := e') (b := b) (Δ := (none, .vlam ty') :: Δ) hpe he.2 ⟨hΔ, nofun, h1⟩
        (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · rfl
          · exact hΔv y hy) h4
      refine ⟨ty' :: As, b', rfl, by simp [hl], fun A hA' => ?_, by simpa using hb⟩
      rcases List.mem_cons.1 hA' with rfl | hA'
      · exact hA
      · exact hm A hA'
  | _ + 1, .bvar .., _, _, _, h, _, _, _, _ | _ + 1, .fvar .., _, _, _, h, _, _, _, _
  | _ + 1, .mvar .., _, _, _, h, _, _, _, _ | _ + 1, .sort .., _, _, _, h, _, _, _, _
  | _ + 1, .const .., _, _, _, h, _, _, _, _ | _ + 1, .app .., _, _, _, h, _, _, _, _
  | _ + 1, .lam .., _, _, _, h, _, _, _, _ | _ + 1, .letE .., _, _, _, h, _, _, _, _
  | _ + 1, .lit .., _, _, _, h, _, _, _, _ | _ + 1, .mdata .., _, _, _, h, _, _, _, _
  | _ + 1, .proj .., _, _, _, h, _, _, _, _ => by simp [ElimNestedInductive.peel] at h

/-- A domain's view keeps its placement: an auxiliary constant at an annotation's place is
applied to the parameters, so what it strips to is a parameter. -/
theorem VExpr.StripsTo.auxAt {R : Name → Option VAuxHead} {ls₀ : List VLevel}
    {D X : VExpr} (H : D.StripsTo X) {k : Nat} (hD : D.AuxAt R ls₀ k) : X.AuxAt R ls₀ k := by
  have hbv {A X : VExpr} (H : A.StripsTo X) (h : ∃ i, A = .bvar i) : X.AuxAt R ls₀ k := by
    obtain ⟨i, rfl⟩ := h; cases H; trivial
  have hbvs {xs : List VExpr} {A : VExpr} {n : Nat} (h : xs = VExpr.bvars n k) (hA : A ∈ xs) :
      ∃ i, A = .bvar i := by
    subst h; simp only [VExpr.bvars, List.mem_map] at hA
    obtain ⟨i, -, rfl⟩ := hA; exact ⟨_, rfl⟩
  -- an auxiliary constant applied to `A` alone, or not auxiliary
  have hone {c : Name} {ls : List VLevel} {A X : VExpr} (H : A.StripsTo X) (ih : A.AuxAt R ls₀ k → X.AuxAt R ls₀ k)
      (hD : (VExpr.app (.const c ls) A).AuxAt R ls₀ k) : X.AuxAt R ls₀ k := by
    rw [VExpr.AuxAt] at hD
    simp only [VExpr.constSpine?, Option.map_some] at hD
    split at hD
    · split at hD
      · exact hbv H (hbvs hD.1 (by simp))
      · exact ih hD.2
    · exact ih hD.2
  induction H with
  | refl => exact hD
  | @app2 A _ ls v c hc HA ih =>
    rw [VExpr.AuxAt] at hD
    simp only [VExpr.constSpine?, Option.map_some] at hD
    split at hD
    · split at hD
      · exact hbv HA (hbvs hD.1 (by simp))
      · exact hone HA ih hD.1
    · exact hone HA ih hD.1
  | app1 _ HA ih => exact hone HA ih hD

theorem VExpr.StripsToBy.consts {P Q : Name → Prop} {D X : VExpr} (H : D.StripsToBy P X)
    (hD : D.ConstsSat Q) : D.StripsToBy (fun c => P c ∧ Q c) X := by
  induction H with
  | refl => exact .refl
  | app2 hc hP _ ih => exact .app2 hc ⟨hP, hD.1.1⟩ (ih hD.1.2)
  | app1 hc hP _ ih => exact .app1 hc ⟨hP, hD.1⟩ (ih hD.2)

/-- What restoring needs to know of one constructor of a translated block, from the elimination
that processed it (`CtorDone`) and the flat check that translated it. `auxN` are the auxiliary
types' names: what `R` names that the checking environment `E₁` has. -/
theorem ctor_restoreFacts {E₁ : VEnv} (hE : E₁.WF) {lparams : List Name} (hUs : lparams.Nodup)
    {d : VInductDecl} (hU : d.uvars = lparams.length) (hP : E₁.IsTele d.uvars [] d.params)
    {R : Name → Option VAuxHead} {ren : Name → Option Name} {auxN : List Name}
    (hRn : ∀ x h, R x = some h → h.n = d.params.length)
    (hauxN : ∀ x ∈ auxN, x ∈ d.names ∧ (R x).isSome)
    (hcls : ∀ x, (E₁.constants x).isSome → (R x ≠ none ∨ ren x ≠ none) → x ∈ auxN)
    (hlit : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP (· ∈ auxN)) = false)
    (hlitR : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP fun x => (R x).isSome) = false)
    (hind : ∀ n b, E₁.inducts n = some b → n ∉ auxN)
    (hnone : ∀ T ∈ d.allTypes, T.nested = none)
    {T : VInductiveType} {c : VConstructor} (hcW : c.WF E₁ d T) (hTn : T.nested = none)
    {pairs : List (Expr × Name)} {params : Array Expr} {c₀ ct : Constructor}
    (hpa : ∀ p ∈ pairs, (R p.2).isSome)
    (hCD : ElimNestedInductive.CtorDone pairs (lparams.map .param) params d.params.length c₀ ct)
    (hc₀ : c₀.type.anySub (constP fun x => (R x).isSome) = false)
    (hcl : c₀.type.looseBVarRange' = 0)
    (htr : TrExprS E₁ lparams [] ct.type c.type)
    (hstrips : ∀ ps Ds B, c.type = .foralls (ps ++ Ds) B → ps.length = d.params.length →
      ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      D.StripsToBy (· ∉ d.names) f.type) :
    c.RestoreFacts R ren d := by
  have hO := hE.ordered
  -- the constants the constructor's type mentions are the checking environment's
  have hCS : c.type.ConstsSat (E₁.constants · |>.isSome) := by
    obtain ⟨_, h⟩ := hcW.type
    exact (VEnv.IsDefEq.constsSat hO h trivial).1
  have hfree {x : VExpr} (h1 : x.ConstsSat (E₁.constants · |>.isSome))
      (h2 : x.ConstsSat (· ∉ auxN)) : x.ConstsSat fun y => R y = none ∧ ren y = none :=
    (h1.and h2).mono fun y ⟨h1, h2⟩ => by
      by_contra h
      exact h2 (hcls y h1 (by
        by_cases hR : R y = none
        · exact .inr fun hr => h ⟨hR, hr⟩
        · exact .inl hR))
  -- the body under the parameters places its auxiliary constants
  obtain ⟨Bx, hct, hpeel, hplaced⟩ := ElimNestedInductive.CtorDone.placed
    (isAux := fun x => (R x).isSome) hpa hCD hc₀ hcl
  rw [hct] at htr
  have hns : ∀ y us, constP (· ∈ auxN) (.const y us) = false → y ∉ auxN := by
    intro y us h; simpa [constP] using h
  have hc₀' : c₀.type.anySub (constP (· ∈ auxN)) = false :=
    AddInductive.anySub_mono (fun e he => by
      cases e with
      | const y _ =>
        simp only [constP, decide_eq_true_eq] at he ⊢; exact (hauxN y he).2
      | _ => simp [constP] at he) hc₀
  obtain ⟨As, b', hty, hAl, hAm, hb⟩ := TrExprS.setBody_inv hE hns hlit hind hpeel hc₀'
    (Δ := []) trivial nofun htr
  have hlv := VLevel.mapM_ofLevel_params hUs
  obtain ⟨hPA, hCA⟩ := ElimNestedInductive.paramsCtx R (VLevel.params lparams.length) As.reverse
  have hBA : b'.AuxAt R (VLevel.params d.uvars) 0 := by
    rw [hU]
    refine ElimNestedInductive.TrExprS.auxAt (n := d.params.length) hlv
      (fun x h hx => ⟨by simp [hx], hRn x h hx⟩) (fun x hx => Option.isSome_iff_exists.1 hx)
      hlitR (by simpa [List.map_reverse] using hb) (by simpa [hAl] using hPA) hCA hplaced
  have hCS0 := hCS
  rw [hty, VExpr.ConstsSat.foralls] at hCS
  obtain ⟨ps₀, Ds₀, hty₀, hTD, hFW, -⟩ := hcW.shape
  have hl₀ := hTD.length_eq
  obtain ⟨rfl, hb'⟩ := VExpr.foralls_inj (hty.symm.trans (hty₀.trans (VExpr.foralls_append ..)))
    (by rw [hAl, hl₀])
  rw [hb'] at hBA
  obtain ⟨hDA, -⟩ := VExpr.AuxAt.foralls hBA
  refine ⟨⟨As, b', hty, hAl, fun A hA => hfree (hCS.1 A hA) (VExpr.constsSat_of_mentions (hAm A hA)),
    by rw [hb']; exact hBA⟩, fun k f hf => ?_, fun x hx => ?_,
    fun ps Ds B hty' hps k D f hD hf => ?_⟩
  · -- a field's type and its recursive view
    have hk : k < Ds₀.length := by
      rw [hFW.length]; exact (List.getElem?_eq_some_iff.1 hf).1
    have hD : Ds₀[k]? = some Ds₀[k] := List.getElem?_eq_getElem hk
    have hS := (hstrips As Ds₀ _ (hty₀.trans (by rfl)) hAl k _ f hD hf).toStripsTo
    refine ⟨hS.auxAt (by simpa using hDA k _ hD), ?_⟩
    have hte := (VInductDecl.FieldsWF.tele hFW).1
    rw [← List.take_append_drop k c.fields, List.map_append] at hte
    have hΓ := hte.append_inv.1.onCtx (by simpa using hP.onCtx trivial)
    refine VInductDecl.RecArgWF.auxAt hO (by simpa using hΓ) (fun x h hx => ?_) hnone
      (by simpa using VInductDecl.FieldsWF.recArg hFW k f hf) _
    by_cases hx' : (E₁.constants x).isSome
    · exact .inl (hauxN x (hcls x hx' (.inl (by simp [hx])))).1
    · exact .inr (by simpa using hx')
  · -- the indices mention the auxiliary types at most
    rw [hb', VExpr.ConstsSat.foralls, VInductiveType.typeApp_of_none hTn,
      VExpr.ConstsSat.appN] at hCS
    refine (hCS.2.2.2 x (List.mem_append_right _ hx)).mono fun y hy hr => ?_
    exact (hauxN y (hcls y hy hr)).1
  · -- the annotations a field's view strips are the checking environment's, not the block's
    have hDc : D.ConstsSat (E₁.constants · |>.isSome) := by
      rw [hty', VExpr.ConstsSat.foralls] at hCS0
      exact hCS0.1 D (List.mem_append_right _ (List.mem_of_getElem? hD))
    refine ((hstrips ps Ds B hty' hps k D f hD hf).consts hDc).mono fun x ⟨h1, h2⟩ => ?_
    by_contra h
    refine h1 (hauxN x (hcls x h2 ?_)).1
    by_cases hR : R x = none
    · exact .inr fun hr => h ⟨hR, hr⟩
    · exact .inl hR

theorem _root_.List.Forall₂.getElem?_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b}, l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | a :: _, _ :: _, .cons h t, i, b, hb => by
    cases i with
    | zero => cases hb; exact ⟨a, rfl, h⟩
    | succ i => exact t.getElem?_right (by simpa using hb)

theorem _root_.List.Forall₂.getElem?_left {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a}, l₁[i]? = some a →
      ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, b :: _, .cons h t, i, a, ha => by
    cases i with
    | zero => cases ha; exact ⟨b, rfl, h⟩
    | succ i => exact t.getElem?_left (by simpa using ha)

/-- The hypotheses of `VInductDecl.RestoreSpec.wf` that come from the elimination and the flat
check, for the kernel's tables. -/
structure RestoreInputs (venv : VEnv) (d : VInductDecl) (R : Name → Option VAuxHead)
    (ren : Name → Option Name) (n : Nat) (ns : List VNested) (cname : Name → Name) : Prop where
  spec : d.RestoreSpec R ren n ns cname
  n_pos : 0 < n
  Rfresh : ∀ c h, R c = some h → venv.constants c = none
  renfresh : ∀ c c', ren c = some c' → venv.constants c = none
  Rdom : ∀ c h, R c = some h → ∃ k T, d.types[n + k]? = some T ∧
    (c = T.name ∨ ∃ c' ∈ T.ctors, c = c'.name)
  renNames : ∀ c c', ren c = some c' → c ∉ d.names
  ctorNames : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.name ∉ d.names
  ctor : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.RestoreFacts R ren d
  litR : ∀ E₁, venv.addConstList d.typeConsts = some E₁ → ∀ l, E₁.ContainsLits l →
    l.toConstructor.anySub (constP fun x => (R x).isSome) = false

/-- The kernel's restoration tables for a nested block, checked flat as `d` from the elimination
`run`'s types `types ++ auxs` (`run_spec`), satisfy what `RestoreSpec.wf` asks of them, but for
the auxiliary types' `AuxWF` and the index telescopes. `ns` are the occurrences the auxiliary
types stand for. -/
theorem restoreInputs {venv E₁ : VEnv} (henv : venv.WF) (hprim : venv.HasPrimitives)
    {d : VInductDecl} (hd : d.WF venv) (hflat : d.aux = [])
    (hE₁ : venv.addConstList d.typeConsts = some E₁)
    (hnd : ((d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)).Nodup)
    (hfr : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1), venv.constants x = none)
    (hnp : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1),
      Environment.primitives.contains x = false)
    {lparams : List Name} (hUs : lparams.Nodup) (hU : d.uvars = lparams.length)
    {nparams : Nat} (hnpar : d.params.length = nparams) {level : VLevel}
    {res : ElimNestedInductive.Result} {env' : Environment} {T₀ : InductiveType}
    {Ts auxs : List InductiveType} {pairs : List (Expr × Name)} {ns : List VNested}
    (hEl : AddInductive.Elaborates E₁ lparams nparams level res.types d)
    (hTD : List.Forall₂ (ElimNestedInductive.TypeDone pairs (lparams.map .param) res.params nparams)
      (T₀ :: Ts ++ auxs) res.types)
    (hpairs : pairs.map (·.2) = auxs.map (·.name))
    (hcl : ∀ T ∈ T₀ :: Ts ++ auxs, ElimNestedInductive.TypeClosed T)
    (hns : ns.length = auxs.length) (hauxne : auxs ≠ []) {info : InductiveVal}
    (hinfo : env'.find? T₀.name = some (.inductInfo info)) (hall : info.all = d.types.map (·.name))
    (hcname : ∀ j T, j < (T₀ :: Ts).length → d.types[j]? = some T → ∀ c ∈ T.ctors,
      res.restoreCtorName env' c.name = c.name)
    (hin : ∀ T ∈ T₀ :: Ts ++ auxs, ∀ c ∈ T.ctors, c.type.anySub
      (constP fun x => (d.auxTable (T₀ :: Ts).length ns (res.restoreCtorName env') x).isSome) = false) :
    RestoreInputs venv d (d.auxTable (T₀ :: Ts).length ns (res.restoreCtorName env'))
      (auxRecRen env' (T₀ :: Ts)) (T₀ :: Ts).length ns (res.restoreCtorName env') := by
  generalize hn : (T₀ :: Ts).length = n at *
  generalize hRdef : d.auxTable n ns (res.restoreCtorName env') = R at *
  generalize hcn : res.restoreCtorName env' = cname at *
  have hlenT : res.types.length = n + auxs.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hTD]; simp [← hn]; omega
  have hlenD : d.types.length = n + ns.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hEl.types, hlenT, hns]
  have hnested : ∀ T ∈ d.types, T.nested = none := fun T hT => (hd.types T hT).2
  obtain ⟨HA, hRinj, hRapart⟩ := VInductDecl.namesApart_of_nodup hflat hnd
  have hauxl : 0 < auxs.length := List.length_pos_iff.2 hauxne
  have hn0 : 0 < n := by rw [← hn]; simp
  obtain ⟨hren1, hren2⟩ := auxRecRen_spec (Ts := Ts) hflat hnd hinfo hall (by rw [hn]; omega)
  rw [hn] at hren1 hren2
  have hT0 : d.types[0]?.map (·.name) = some T₀.name := by
    obtain ⟨t, ht, ht'⟩ := hTD.getElem?_left (i := 0) (a := T₀) rfl
    obtain ⟨T, hT, hTt⟩ := hEl.types.getElem?_left ht
    rw [hT]; simp [hTt.1, ht'.1]
  -- the specification of the tables
  have hspec : d.RestoreSpec R (auxRecRen env' (T₀ :: Ts)) n ns cname := by
    rw [← hRdef]
    refine VInductDecl.restoreSpec_auxTable hflat hnested hnd hlenD
      (fun j T hj hT c hc => hcn ▸ hcname j T (by omega) hT c hc) hren1 fun j hj hj' => ?_
    rw [hren2 j hj hj', VInductDecl.restoreNested_recName (by omega) (by omega) hj]
    simp [hT0]
  subst hnpar
  have hE : E₁.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) hE₁
  have hle : venv ≤ E₁ := VEnv.addConstList_le hE₁
  have hmemT {T : VInductiveType} (hT : T ∈ d.types) :
      T.name ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    simp only [List.map_append, List.mem_append]
    exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T, hT, rfl⟩, rfl⟩))
  have hmemC {j : Nat} {T : VInductiveType} {c : VConstructor} (hT : d.types[j]? = some T)
      (hc : c ∈ T.ctors) :
      c.name ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    simp only [List.map_append, List.mem_append]
    exact .inl (.inr (List.mem_map.2 ⟨_, List.mem_map.2
      ⟨(j, c), VInductDecl.mem_ctors_iff.2 ⟨T, hT, hc⟩, rfl⟩, rfl⟩))
  have hmemR {j : Nat} (hj : j < d.types.length) :
      d.recName j ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    simp only [List.map_append, List.mem_append]
    exact .inr (by rw [VInductDecl.recConsts_names hflat]; exact List.mem_map.2 ⟨j, by simpa, rfl⟩)
  have hRsome {c : Name} {h : VAuxHead} (hc : R c = some h) :
      ∃ k T o, d.AuxAt' n ns c k T o ∧ h.n = d.params.length := by
    rw [← hRdef] at hc; exact VInductDecl.auxTable_some hc
  have hRtype {k : Nat} {T : VInductiveType} {o : VNested} (hT : d.types[n + k]? = some T)
      (ho : ns[k]? = some o) :
      R T.name = some ⟨d.params.length, o.ind, o.lvls, o.args⟩ := by
    rw [← hRdef]; exact VInductDecl.auxTable_type HA hT ho
  -- the auxiliary types' names
  let auxN := (d.types.drop n).map (·.name)
  have hauxN : ∀ x ∈ auxN, x ∈ d.names ∧ (R x).isSome := by
    intro x hx
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT
    rw [List.getElem?_drop] at hk
    obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 hk).1; omega)⟩
    exact ⟨List.mem_map.2 ⟨T, List.mem_of_getElem? hk, rfl⟩, by rw [hRtype hk ho]; rfl⟩
  have hauxN' {k : Nat} {T : VInductiveType} (hT : d.types[n + k]? = some T) : T.name ∈ auxN :=
    List.mem_map.2 ⟨T, List.mem_iff_getElem?.2 ⟨k, by rw [List.getElem?_drop]; exact hT⟩, rfl⟩
  have hcls : ∀ x, (E₁.constants x).isSome → (R x ≠ none ∨ auxRecRen env' (T₀ :: Ts) x ≠ none) →
      x ∈ auxN := by
    intro x hx hr
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hx
    have hcases := VEnv.addConstList_constants_cases hE₁ hci
    rcases hr with hr | hr
    · obtain ⟨h, hR'⟩ := Option.ne_none_iff_exists'.1 hr
      obtain ⟨k, T, o, ⟨hT, -, hc⟩, -⟩ := hRsome hR'
      rcases hc with rfl | ⟨c', hc', rfl⟩
      · exact hauxN' hT
      · rcases hcases with h0 | hm
        · rw [hfr _ (hmemC hT hc')] at h0; cases h0
        · obtain ⟨T', hT', e⟩ := List.mem_map.1 hm
          have e' : T'.name = c'.name := congrArg Prod.fst e
          exact absurd e'.symm (HA.apart T' hT' T (List.mem_of_getElem? hT) c' hc')
    · obtain ⟨c', hr'⟩ := Option.ne_none_iff_exists'.1 hr
      obtain ⟨j, -, hj, rfl⟩ := hren1 _ _ hr'
      rcases hcases with h0 | hm
      · rw [hfr _ (hmemR hj)] at h0; cases h0
      · exact absurd (by simpa [VInductDecl.typeConsts] using List.mem_map_of_mem (f := (·.1)) hm)
          (hRapart j hj).1
  have hlit : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP (· ∈ auxN)) = false := by
    refine Literal.toConstructor_anySub_of_fresh (ns := d.types.map (·.name)) henv hprim
      (fun x hx => hfr x (by
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx; exact hmemT hT))
      (fun x hx h0 => ?_) (fun x hx => hnp x (by
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx; exact hmemT hT)) (fun e he => ?_)
    · obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.1 hx
      rcases VEnv.addConstList_constants_cases hE₁ hci with h | hm
      · rw [h0] at h; cases h
      · simpa [VInductDecl.typeConsts] using List.mem_map_of_mem (f := (·.1)) hm
    · cases e with
      | const c us =>
        simp only [constP, decide_eq_true_eq] at he
        exact ⟨c, us, rfl, (hauxN c he).1⟩
      | _ => simp [constP] at he
  have hlitR : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP fun x => (R x).isSome) =
      false := by
    refine Literal.toConstructor_anySub_of_fresh
      (ns := (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)) henv hprim hfr
      (fun x hx h0 => ?_) hnp (fun e he => ?_)
    · obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.1 hx
      rcases VEnv.addConstList_constants_cases hE₁ hci with h | hm
      · rw [h0] at h; cases h
      · simp only [List.map_append, List.mem_append]
        exact .inl (.inl (List.mem_map_of_mem (f := (·.1)) hm))
    · cases e with
      | const c us =>
        simp only [constP] at he
        obtain ⟨h, hR'⟩ := Option.isSome_iff_exists.1 he
        obtain ⟨k, T, o, ⟨hT, -, hc⟩, -⟩ := hRsome hR'
        refine ⟨c, us, rfl, ?_⟩
        rcases hc with rfl | ⟨c', hc', rfl⟩
        · exact hmemT (List.mem_of_getElem? hT)
        · exact hmemC hT hc'
      | _ => simp [constP] at he
  have hind : ∀ x b, E₁.inducts x = some b → x ∉ auxN := by
    intro x b hb hx
    rw [VEnv.addConstList_inducts hE₁] at hb
    obtain ⟨ci, hci⟩ := henv.constants_of_inducts hb
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    rw [hfr _ (hmemT (List.mem_of_mem_drop hT))] at hci; cases hci
  have hnone : ∀ T ∈ d.allTypes, T.nested = none := by
    rw [VInductDecl.allTypes_of_aux hflat]; exact hnested
  have hP : E₁.IsTele d.uvars [] d.params := hd.params.mono hle
  have hpa : ∀ p ∈ pairs, (R p.2).isSome := by
    intro p hp
    obtain ⟨T, hT, e⟩ := List.mem_map.1 (hpairs ▸ List.mem_map_of_mem (f := fun q : Expr × Name => q.2) hp)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT
    have hk' : (T₀ :: Ts ++ auxs)[n + k]? = some T := by
      rw [List.getElem?_append_right (by simp [← hn])]; simpa [← hn] using hk
    obtain ⟨t, ht, htn, -⟩ := hTD.getElem?_left hk'
    obtain ⟨T', hT', hT'n, -⟩ := hEl.types.getElem?_left ht
    obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 hk).1; omega)⟩
    rw [← e, ← htn, ← hT'n, hRtype hT' ho]; rfl
  refine ⟨hspec, hn0, fun c h hc => ?_, fun c c' hc => ?_, fun c h hc => ?_, fun c c' hc => ?_,
    fun T hT c hc hm => ?_, fun T hT c hc => ?_, fun E₁' h => by cases hE₁.symm.trans h; exact hlitR⟩
  · obtain ⟨k, T, o, ⟨hT, -, hc'⟩, -⟩ := hRsome hc
    rcases hc' with rfl | ⟨c', hc', rfl⟩
    · exact hfr _ (hmemT (List.mem_of_getElem? hT))
    · exact hfr _ (hmemC hT hc')
  · obtain ⟨j, -, hj, rfl⟩ := hren1 _ _ hc
    exact hfr _ (hmemR hj)
  · obtain ⟨k, T, o, ⟨hT, -, hc'⟩, -⟩ := hRsome hc
    exact ⟨k, T, hT, by rcases hc' with e | ⟨c', h1, e⟩ <;> [exact .inl e.symm; exact .inr ⟨c', h1, e.symm⟩]⟩
  · obtain ⟨j, -, hj, rfl⟩ := hren1 _ _ hc
    exact (hRapart j hj).1
  · obtain ⟨T', hT', e⟩ := List.mem_map.1 hm
    exact HA.apart T' hT' T hT c hc e.symm
  · -- the constructor's facts, from its elimination and its check
    obtain ⟨t, ht, -, hcs⟩ := Lean4Lean.List.Forall₂.forall_exists_r hEl.types T hT
    obtain ⟨ct, hct, -, htr, -⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcs c hc
    obtain ⟨T₁, hT₁, -, -, hCDs⟩ := Lean4Lean.List.Forall₂.forall_exists_r hTD t ht
    obtain ⟨c₀, hc₀, hCD⟩ := Lean4Lean.List.Forall₂.forall_exists_r hCDs ct hct
    exact ctor_restoreFacts hE hUs hU hP (fun x h hx => (hRsome hx).choose_spec.choose_spec
        |>.choose_spec.2) hauxN hcls hlit hlitR hind hnone
      ((hd.ctors E₁ hE₁ T (VInductDecl.mem_allTypes_of_types hT)).2 c hc) (hnested T hT) hpa hCD
      (hin T₁ hT₁ c₀ hc₀) ((hcl T₁ hT₁).2.2 c₀ hc₀).2.1 htr
      (fun ps Ds B h1 h2 k D f h3 h4 => (AddInductive.Elaborates.stripsToBy hEl rfl T hT c hc
        ps Ds B h1 h2 k D f h3 h4).mono fun x hx hm => hx.1 (by
          rwa [VInductDecl.names, ← Lean4Lean.List.Forall₂.map_eq
            (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.symm) hEl.types)] at hm))

/-- The names a fold over types and their constructors collects, as the final phase collects the
auxiliary ones. -/
theorem foldl_typeNames_contains (ts : List InductiveType) : ∀ T ∈ ts,
    (ts.foldl (init := ({} : NameSet)) fun s t =>
      t.ctors.foldl (·.insert ·.name) (s.insert t.name)).contains T.name ∧
    ∀ c ∈ T.ctors, (ts.foldl (init := ({} : NameSet)) fun s t =>
      t.ctors.foldl (·.insert ·.name) (s.insert t.name)).contains c.name :=
  fun T hT => ⟨ns_foldl_types_contains_mem (s := ({} : NS)) ts
      ⟨T, hT, .inl rfl⟩,
    fun c hc => ns_foldl_types_contains_mem (s := ({} : NS)) ts
      ⟨T, hT, .inr (List.mem_map_of_mem hc)⟩⟩

/-- `restoreInputs`' `hin`: no input constructor names an auxiliary constant. The block's own
constructors because the final phase checks them against the auxiliary names `S`; the auxiliary
types' because the elimination builds them from the environment's constants and the block's
constructors (`run_spec`), and the auxiliary names are new. -/
theorem restoreInputs_hin [VEnv.Injective] {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {d : VInductDecl} {n : Nat} {ns : List VNested} {cname : Name → Name}
    (hfrE : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1), env.find? x = none)
    {E₁ : VEnv} {lparams : List Name} {nparams : Nat} {level : VLevel}
    {res : ElimNestedInductive.Result}
    (hEl : AddInductive.Elaborates E₁ lparams nparams level res.types d)
    {types auxs : List InductiveType}
    (hfree : ∀ f, ElimNestedInductive.EnvFree env f →
      (∀ T ∈ types, ∀ c ∈ T.ctors, c.type.anySub (constP f) = false) →
      ∀ T ∈ types ++ auxs, ∀ c ∈ T.ctors, c.type.anySub (constP f) = false)
    {S : NameSet} (hS : ∀ T ∈ res.types.drop n, S.contains T.name ∧ ∀ c ∈ T.ctors, S.contains c.name)
    (hin : ∀ T ∈ types, ∀ c ∈ T.ctors, c.type.anySub (auxP S) = false) :
    ∀ T ∈ types ++ auxs, ∀ c ∈ T.ctors,
      c.type.anySub (constP fun x => (d.auxTable n ns cname x).isSome) = false := by
  -- an auxiliary name is one of the translated block's, so new, and among `S`
  have hR : ∀ x, (d.auxTable n ns cname x).isSome →
      S.contains x ∧ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    intro x hx
    obtain ⟨h, hR⟩ := Option.isSome_iff_exists.1 hx
    obtain ⟨k, T, o, ⟨hT, -, hc⟩, -⟩ := VInductDecl.auxTable_some hR
    obtain ⟨t, ht, htn, hcs⟩ := Lean4Lean.List.Forall₂.getElem?_r hEl.types hT
    have htm : t ∈ res.types.drop n := List.mem_iff_getElem?.2 ⟨k, by rw [List.getElem?_drop]; exact ht⟩
    rcases hc with rfl | ⟨c', hc', rfl⟩
    · refine ⟨htn ▸ (hS t htm).1, ?_⟩
      simp only [List.map_append, List.mem_append]
      exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩, rfl⟩))
    · obtain ⟨ct, hct, hcn, -⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcs c' hc'
      refine ⟨hcn ▸ (hS t htm).2 ct hct, ?_⟩
      simp only [List.map_append, List.mem_append]
      exact .inl (.inr (List.mem_map.2 ⟨_, List.mem_map.2
        ⟨(n + k, c'), VInductDecl.mem_ctors_iff.2 ⟨T, hT, hc'⟩, rfl⟩, rfl⟩))
  refine hfree _ (fun m ci hci => ?_) fun T hT c hc => ?_
  · -- the environment's constants mention only constants it has
    have hTr := wf.tr (safety := .unsafe)
    obtain ⟨_, -, htr⟩ := hTr.find? hci DefinitionSafety.unsafe_le
    refine anySub_constP_of_suppIn (Expr.SuppIn.mono ⟨fun _ _ => trivial, fun _ _ => trivial,
      fun y hy => ?_⟩ (TrExprS.suppIn hTr.wf wf.hasPrimitives htr.2.2))
    cases h : (d.auxTable n ns cname y).isSome
    · simpa using h
    · obtain ⟨ci', hci'⟩ := hy
      have := hTr.constants_eq_none (hfrE y (hR y h).2)
      rw [this] at hci'; cases hci'
  · refine AddInductive.anySub_mono (fun e he => ?_) (hin T hT c hc)
    cases e with
    | const y _ => simp only [constP] at he; exact (hR y he).1
    | _ => simp [constP] at he

end Lean4Lean

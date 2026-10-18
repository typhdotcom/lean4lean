import Lean4Lean.Verify.Environment.MkRecInfos

/-!
# `declareRecursors`

`declareRecursors` adds a recursor per type of the block, its type and rules built from the local
variables `mkRecInfos` opened. Its type is the one `RecInfosData.recType` translates, with binder
annotations adjusted, and each rule is built from the minor premise and inductive hypotheses
`mkRecInfos` recorded for the constructor.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive

/-- Binder annotations do not change a translation. -/
theorem _root_.Lean4Lean.TrExprS.inferImplicit {env : VEnv} {Us : List Name} :
    ∀ (n : Nat) {Δ : VLCtx} {e : Expr} {e' : VExpr} (b : Bool), TrExprS env Us Δ e e' →
      TrExprS env Us Δ (e.inferImplicit n b) e'
  | 0, _, e, _, b, H => by cases e <;> simpa [Expr.inferImplicit] using H
  | n + 1, _, e, _, b, H => by
    cases e with
    | forallE nm dom body bi =>
      cases H with | forallE h1 h2 hd hb => ?_
      simp only [Expr.inferImplicit, mkForall]
      exact .forallE h1 h2 hd (TrExprS.inferImplicit n b hb)
    | _ => simpa [Expr.inferImplicit] using H

theorem getMajorInduct_eq (v : RecursorVal) :
    v.getMajorInduct = majorInductGo v.getMajorIdx v.type := by
  unfold RecursorVal.getMajorInduct
  generalize v.getMajorIdx = n
  generalize v.type = e
  induction n generalizing e with
  | zero => rfl
  | succ n ih => exact ih e.bindingBody!

theorem majorInductGo_inferImplicit :
    ∀ (n : Nat) (k : Nat) (e : Expr) (b : Bool),
      majorInductGo k (e.inferImplicit n b) = majorInductGo k e
  | 0, k, e, b => by cases e <;> simp [Expr.inferImplicit]
  | n + 1, k, e, b => by
    cases e with
    | forallE nm dom body bi =>
      cases k with
      | zero => simp [Expr.inferImplicit, mkForall, majorInductGo, Expr.bindingDomain!]
      | succ k =>
        simp only [Expr.inferImplicit, mkForall, majorInductGo, Expr.bindingBody!]
        exact majorInductGo_inferImplicit n k body b
    | _ => simp [Expr.inferImplicit]

theorem forIn'_list_WF {c : VContext} {β : Type} (I : Nat → β → Nat → Prop) :
    ∀ (l : List Nat) (k : Nat) {f : (a : Nat) → a ∈ l → β → StateT Nat M (ForInStep β)},
    (∀ i (hi : i < l.length), l[i] = k + i) →
    (∀ a h b s, I a b s → WF c (f a h b s) fun p => ∃ b', p.1 = .yield b' ∧ I (a + 1) b' p.2) →
    ∀ b s, I k b s → WF c (forIn' l b f s) fun p => I (k + l.length) p.1 p.2
  | [], k, f, _, _, b, s, h => WF.pure h
  | a :: l, k, f, hl, H, b, s, h => by
    obtain rfl : a = k := by have := hl 0 (by simp); exact this
    rw [List.forIn'_cons]
    refine WF.bind (H a (.head _) b s h) fun p hp => ?_
    obtain ⟨b', hp1, hp2⟩ := hp
    obtain ⟨r, s'⟩ := p
    dsimp only at hp1 hp2; subst hp1
    have := forIn'_list_WF I l (a + 1) (f := fun a' h' => f a' (.tail _ h'))
      (fun i hi => by
        have := hl (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this; omega)
      (fun a' h' b s hI => H a' _ b s hI) b' s' hp2
    rw [show a + 1 + l.length = a + (a :: l).length by simp; omega] at this
    exact this

/-- A loop over `[:n]` in `StateT Nat M` that always continues keeps an invariant. -/
theorem forIn'_range_WF {c : VContext} {β : Type} {n : Nat}
    {f : (i : Nat) → i ∈ [:n] → β → StateT Nat M (ForInStep β)} (I : Nat → β → Nat → Prop)
    {b₀ : β} {s₀ : Nat} (h0 : I 0 b₀ s₀)
    (hf : ∀ i (hi : i ∈ [:n]) b s, I i b s →
      WF c (f i hi b s) fun p => ∃ b', p.1 = .yield b' ∧ I (i + 1) b' p.2) :
    WF c (forIn' [:n] b₀ f s₀) fun p => I n p.1 p.2 := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  have := forIn'_list_WF I (List.range' [:n].start [:n].size [:n].step) 0
    (f := fun a h => f a (Std.Legacy.Range.mem_of_mem_range' h))
    (fun i hi => by simp [List.getElem_range']) (fun a h b s hI => hf a _ b s hI) b₀ s₀ h0
  simpa [Std.Legacy.Range.size] using this

theorem WF.stateT_read_bind {c : VContext} {σ α : Type} {f : Context → StateT σ M α} {s : σ}
    {Q : α × σ → Prop} (h : WF c (f c.toContext s) Q) :
    WF c ((MonadReader.read >>= f : StateT σ M α) s) Q :=
  fun a ha => h a ha

theorem WF.stateT_bind {c : VContext} {σ α β : Type} {x : StateT σ M α} {f : α → StateT σ M β}
    {s : σ} {Q : α × σ → Prop} {R : β × σ → Prop} (h1 : WF c (x s) Q)
    (h2 : ∀ a s', Q (a, s') → WF c (f a s') R) : WF c ((x >>= f : StateT σ M β) s) R :=
  fun r hr => (WF.bind (x := x s) (f := fun p => f p.1 p.2) h1 fun p hp => h2 p.1 p.2 hp) r hr

theorem WF.stateT_liftM {c : VContext} {σ α : Type} {x : Except Exception α} {s : σ}
    {Q : α → Prop} (h : x.WF Q) :
    WF c ((liftM x : StateT σ M α) s) fun p => Q p.1 ∧ p.2 = s := by
  intro p hp
  cases hx : x with
  | error e =>
    subst hx
    have hp' : (Except.error e : Except Exception (α × σ)) = Except.ok p := hp
    cases hp'
  | ok a =>
    subst hx
    have hp' : (Except.ok (a, s) : Except Exception (α × σ)) = Except.ok p := hp
    cases hp'
    exact ⟨h a rfl, rfl⟩

/-- An element of a flattened list, past the lists before its own. -/
theorem getElem?_flatten_offset {α} : ∀ (L : List (List α)) (i p : Nat),
    p < (L[i]?.map List.length).getD 0 →
    L.flatten[((L.take i).map List.length).sum + p]? = L[i]?.bind (·[p]?)
  | [], i, p, h => by simp at h
  | a :: L, 0, p, h => by
    simp at h ⊢; rw [List.getElem?_append_left h]
  | a :: L, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
    rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact getElem?_flatten_offset L i p h

/-- A stream over a subarray yields its next element. -/
theorem subarray_next {α} {s : Subarray α} (h : s.start < s.stop) :
    ∃ s', Std.Stream.next? s = some (s.array[s.start]'(Nat.lt_of_lt_of_le h s.stop_le_array_size), s') ∧
      s'.array = s.array ∧ s'.start = s.start + 1 ∧ s'.stop = s.stop := by
  simp only [Std.Stream.next?, dif_pos h]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A loop over a list in `StateT Nat M` that always continues keeps an invariant. -/
theorem forIn_list_WF {c : VContext} {α β : Type} (I : Nat → β → Nat → Prop) :
    ∀ (l : List α) (k : Nat) {f : α → β → StateT Nat M (ForInStep β)},
    (∀ j (hj : j < l.length) b s, I (k + j) b s →
      WF c (f l[j] b s) fun p => ∃ b', p.1 = .yield b' ∧ I (k + j + 1) b' p.2) →
    ∀ b s, I k b s → WF c (forIn l b f s) fun p => I (k + l.length) p.1 p.2
  | [], k, f, _, b, s, h => WF.pure h
  | a :: l, k, f, H, b, s, h => by
    rw [List.forIn_cons]
    refine WF.stateT_bind (H 0 (by simp) b s h) fun r s' hr => ?_
    obtain ⟨b', rfl, hb'⟩ := hr
    have := forIn_list_WF I l (k + 1) (f := f) (fun j hj b s hI => by
      have := H (j + 1) (by simp; omega) b s (by rwa [show k + (j + 1) = k + 1 + j by omega])
      simpa [show k + (j + 1) = k + 1 + j by omega] using this) b' s' hb'
    simpa [show k + 1 + l.length = k + (l.length + 1) by omega] using this

/-- `mkRecRules`: the rules of the `i`th recursor, one per constructor of its type, each
translating to the iota rule in any model with the recursors. -/
theorem mkRecRules.WF {c₂ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr isUnsafe elimLevel recInfos d}
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c d)
    {i : Nat} (hi : i < types.length) (s : Nat) (hs : s = (d.ctors.filter (·.1 < i)).length) :
    WF c (mkRecRules types.toArray elimLevel stats i (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors)) recInfos[i]! s) fun p =>
      p.2 = (d.ctors.filter (·.1 < i + 1)).length ∧
      ∀ envC envR : VEnv, c₂.venv ≤ envC → envC.WF →
        (∀ q ∈ d.ctorConsts, envC.constants q.1 = some q.2) →
        envC.addConstList d.recConsts = some envR → envR.WF →
        List.Forall₂ (fun (rule : RecursorRule) ((j, c), q) => j = i ∧ rule.ctor = c.name ∧
            rule.nfields = c.fields.length ∧
            TrExprS envR (getRecLevelParams elimLevel c₂.lparams) [] rule.rhs
              (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs)
          p.1 (d.ctors.zipIdx.filter (·.1.1 = i)) := by
  unfold mkRecRules
  refine WF.stateT_bind (Q := fun p => p = (c.lctx, s)) (fun _ h => by cases h; rfl) ?_
  rintro lctx s' ⟨⟩
  have hdlen : types.length = d.types.length :=
    Lean4Lean.List.Forall₂.length_eq hR.elaborates.types
  have hit : i < d.types.length := hdlen ▸ hi
  have hisz : i < recInfos.size := by rw [hR.size]; exact hi
  have hTi : d.types[i]? = some d.types[i] := List.getElem?_eq_getElem hit
  obtain ⟨t, ht, -, hcts⟩ := List.Forall₂.getElem?_r hR.elaborates.types hTi
  obtain rfl : types[i] = t := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans ht)
  have hmis : recInfos[i].minorInfos.size = d.types[i].ctors.length := by
    have := List.Forall₂.getElem?_l (j := i) hR.infoCount (show recInfos.toList[i]? = some recInfos[i] by simp [hisz])
    obtain ⟨T, hT, h⟩ := this
    rw [hTi] at hT; cases hT; exact h
  have hctl : types[i].ctors.length = d.types[i].ctors.length :=
    Lean4Lean.List.Forall₂.length_eq hcts
  -- the block's constructors, type by type
  have hdc : d.ctors = flatCtors (d.types.map (·.ctors)) := by
    simp only [VInductDecl.ctors, flatCtors, List.zipIdx_map, List.map_map]; rfl
  have hs' : s = (flatCtors ((d.types.map (·.ctors)).take i)).length := by
    rw [hs, hdc, flatCtors_filter_lt]
  have hFi := flatCtors_zipIdx_filter i (d.types.map (·.ctors)) (by simpa using hit)
  rw [← hdc, ← hs'] at hFi
  simp only [List.getElem_map] at hFi
  have hpost : (d.ctors.filter (·.1 < i + 1)).length = s + d.types[i].ctors.length := by
    rw [hdc, flatCtors_filter_lt, List.take_add_one, List.getElem?_map, hTi]
    simp [flatCtors_append, hs']
  -- the records of the minor premises, type by type
  have hinfo : ∀ p (hp : p < d.types[i].ctors.length),
      (recInfos.toList.flatMap (·.minorInfos.toList))[s + p]? =
        some (recInfos[i].minorInfos[p]'(hmis ▸ hp)) := by
    intro p hp
    have hL : (recInfos.toList.map (·.minorInfos.toList)).map List.length =
        (d.types.map (·.ctors)).map List.length := by
      have := List.Forall₂.map_eq (f := fun info : RecInfo => info.minorInfos.size)
        (g := fun T : VInductiveType => T.ctors.length) hR.infoCount
      simpa [Function.comp_def] using this
    have hs'' : s = (((recInfos.toList.map (·.minorInfos.toList)).take i).map List.length).sum := by
      rw [hs', flatCtors_length, List.map_take, List.map_take, hL]
    rw [List.flatMap_def, hs'', getElem?_flatten_offset _ _ _ (by
      simp [Array.getElem?_eq_getElem hisz, hmis, hp])]
    simp [Array.getElem?_eq_getElem hisz]
  have hget : types.toArray[i]! = types[i] := by
    rw [getElem!_pos types.toArray i (by simpa using hi)]; simp
  have hrinfo : recInfos[i]! = recInfos[i] := getElem!_pos recInfos i hisz
  rw [hget, hrinfo]
  let I : Nat → Array RecursorRule × Subarray MinorInfo → Nat → Prop := fun p b st =>
    b.2.array = recInfos[i].minorInfos ∧ b.2.start = p ∧ b.2.stop = recInfos[i].minorInfos.size ∧
    st = s + p ∧
    ∀ envC envR : VEnv, c₂.venv ≤ envC → envC.WF →
      (∀ q ∈ d.ctorConsts, envC.constants q.1 = some q.2) →
      envC.addConstList d.recConsts = some envR → envR.WF →
      List.Forall₂ (fun (rule : RecursorRule) ((j, c), q) => j = i ∧ rule.ctor = c.name ∧
          rule.nfields = c.fields.length ∧
          TrExprS envR (getRecLevelParams elimLevel c₂.lparams) [] rule.rhs
            (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs)
        b.1.toList ((d.ctors.zipIdx.filter (·.1.1 = i)).take p)
  refine WF.stateT_bind (Q := fun r => I (0 + types[i].ctors.length) r.1 r.2)
    (forIn_list_WF I types[i].ctors 0 (fun j hj b st hI => ?step) _ _ ?init) fun r st hr => ?fin
  case init =>
    exact ⟨by simp [Std.toStream], by simp [Std.toStream], by simp [Std.toStream], by simp,
      fun _ _ _ _ _ _ _ => by simp⟩
  case step =>
    rw [Nat.zero_add] at hI ⊢
    obtain ⟨ha, hst, hsp, hsst, hrules⟩ := hI
    have hj' : j < d.types[i].ctors.length := hctl ▸ hj
    obtain ⟨s', hnext, ha', hs'st, hs'sp⟩ :=
      subarray_next (s := b.2) (by rw [hst, hsp, hmis]; exact hj')
    rw [hnext]
    have hmem : ((i, d.types[i].ctors[j]), s + j) ∈ d.ctors.zipIdx := by
      have : ((i, d.types[i].ctors[j]), s + j) ∈ d.ctors.zipIdx.filter (·.1.1 = i) := by
        rw [hFi]; exact List.mem_map.2 ⟨(d.types[i].ctors[j], j),
          List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj'), rfl⟩
      exact (List.mem_filter.1 this).1
    obtain ⟨mi, hmi, hfl, htr⟩ := hR.rules (s + j) i d.types[i].ctors[j]
      (List.mem_zipIdx_iff_getElem?.1 hmem)
    rw [hinfo j hj'] at hmi
    obtain rfl := Option.some.inj hmi
    have hbmi : b.2.array[b.2.start]'(by rw [ha, hst]; exact hmis ▸ hj') =
        recInfos[i].minorInfos[j]'(hmis ▸ hj') := by
      simp only [ha, hst]
    refine WF.stateT_bind (Q := fun p => p = (st, st)) (fun _ h => by cases h; rfl) ?_
    rintro _ _ ⟨⟩
    refine WF.stateT_bind (Q := fun p => p = ((), st + 1)) (fun _ h => by cases h; rfl) ?_
    rintro _ _ ⟨⟩
    refine WF.pure ⟨_, rfl, by rw [ha', ha], by rw [hs'st, hst], by rw [hs'sp, hsp],
      by rw [hsst]; omega, fun envC envR h1 h2 h3 h4 h5 => ?_⟩
    have htk : (d.ctors.zipIdx.filter (·.1.1 = i)).take (j + 1) =
        (d.ctors.zipIdx.filter (·.1.1 = i)).take j ++ [((i, d.types[i].ctors[j]), s + j)] := by
      rw [List.take_add_one, hFi]; simp [List.getElem?_zipIdx, List.getElem?_eq_getElem hj']
    simp only [Array.toList_push, htk]
    refine (Lean4Lean.List.Forall₂.append_of_left
      (Lean4Lean.List.Forall₂.length_eq (hrules envC envR h1 h2 h3 h4 h5))).2
      ⟨hrules envC envR h1 h2 h3 h4 h5, .cons ⟨rfl, ?_, ?_, ?_⟩ .nil⟩
    · obtain ⟨cv, hcv, h⟩ := List.Forall₂.getElem?_l (j := j) hcts (List.getElem?_eq_getElem hj)
      rw [List.getElem?_eq_getElem hj'] at hcv; cases hcv; exact h.1.symm
    · simp only [hbmi]; exact hfl
    · rw [hsst]
      have := htr envC envR h1 h2 h3 h4 h5
      simp only [hbmi]
      exact this
  case fin =>
    rw [Nat.zero_add] at hr
    obtain ⟨-, -, -, hst, hrules⟩ := hr
    refine WF.pure ⟨by rw [hst, hpost, hctl], fun envC envR h1 h2 h3 h4 h5 => ?_⟩
    have := hrules envC envR h1 h2 h3 h4 h5
    rwa [List.take_of_length_le (by rw [hFi]; simp [hctl])] at this

/-- `declareRecursors`: it adds one recursor per type, each translating, in any model of the
environment with the block's types and constructors, to the spec's recursor, with its rules
translating to the iota rules in any model that also has the recursors. -/
theorem declareRecursors.WF {c₂ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr isUnsafe elimLevel recInfos d}
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c d)
    (hE : d.LargeElim ↔ elimLevel ≠ .zero)
    (hEu : elimLevel = .zero ∨ ∃ u, elimLevel = .param u ∧ u ∉ c₂.lparams)
    (hsafety : c₂.safety = inductSafety isUnsafe)
    {kflag : Bool} (hK : kflag = true ↔ d.IsKTarget) {envCtors : Environment}
    (mapWF : envCtors.constants.WF) :
    WF c (declareRecursors envCtors c₂.lparams stats types.toArray elimLevel kflag recInfos)
      fun env' =>
      ∃ recs : List RecursorVal,
        env'.constants = insertConsts envCtors.constants (recs.map .recInfo) ∧
        env'.quotInit = envCtors.quotInit ∧
        ((recs.map ConstantInfo.recInfo).map (·.name)).Nodup ∧
        (∀ ci ∈ recs.map ConstantInfo.recInfo, envCtors.constants.find? ci.name = none) ∧
        (∀ ci ∈ recs.map ConstantInfo.recInfo,
          Environment.primitives.contains ci.name → c.allowPrimitive) ∧
        List.Forall₂ (fun v (p : VInductiveType × Nat) => v.name = Lean.mkRecName p.1.name)
          recs d.types.zipIdx ∧
        ∀ (envC envR : VEnv), c₂.venv ≤ envC → envC.WF →
          (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
          envC.addConstList d.recConsts = some envR → envR.WF →
          List.Forall₂ (fun v (p : VInductiveType × Nat) =>
            TrRecVal d c₂.lparams envR p.2 p.1 v ∧
            TrConstant c.safety envC (.recInfo v)
              ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩)
            recs d.types.zipIdx := by
  have hdlen : types.length = d.types.length :=
    Lean4Lean.List.Forall₂.length_eq hR.elaborates.types
  -- what each recursor added so far satisfies
  let RecOK (v : RecursorVal) (p : VInductiveType × Nat) : Prop :=
    v.name = Lean.mkRecName p.1.name ∧
    ∀ (envC envR : VEnv), c₂.venv ≤ envC → envC.WF →
      (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
      envC.addConstList d.recConsts = some envR → envR.WF →
      TrRecVal d c₂.lparams envR p.2 p.1 v ∧
      TrConstant c.safety envC (.recInfo v) ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩
  let I : Nat → Environment → Nat → Prop := fun i env s =>
    s = (d.ctors.filter (·.1 < i)).length ∧ env.constants.WF ∧
    ∃ recs : List RecursorVal,
      env.constants = insertConsts envCtors.constants (recs.map .recInfo) ∧
      env.quotInit = envCtors.quotInit ∧
      ((recs.map ConstantInfo.recInfo).map (·.name)).Nodup ∧
      (∀ ci ∈ recs.map ConstantInfo.recInfo, envCtors.constants.find? ci.name = none) ∧
      (∀ ci ∈ recs.map ConstantInfo.recInfo,
        Environment.primitives.contains ci.name → c.allowPrimitive) ∧
      List.Forall₂ RecOK recs (d.types.zipIdx.take i)
  unfold declareRecursors
  refine WF.bind (Q := (· = c.lctx)) (fun _ h => by cases h; rfl) fun lctx hl => ?_
  subst hl
  refine WF.bind WF.read fun ctx hctx => ?_
  subst hctx
  simp only [StateT.run']
  rw [map_eq_pure_bind]
  refine WF.bind (Q := fun p => I types.length p.1 p.2) ?_ fun p hp => WF.pure ?_
  · refine WF.stateT_read_bind ?_
    simp only [bind_pure]
    refine forIn'_range_WF I ⟨by rw [List.filter_eq_nil_iff.2 (by simp)]; rfl, mapWF, [], rfl, rfl, .nil, nofun, nofun,
      by simp⟩ ?_
    intro i hi env s ⟨hs, hwf, recs, hc, hq, hnd, hfr, hpr, hrecs⟩
    have hil : i < types.length := by simpa [Membership.mem] using hi.2.1
    refine WF.stateT_bind (mkRecRules.WF hR hil s hs) fun rules s' ⟨hs', hrules⟩ => ?_
    refine WF.stateT_bind (WF.stateT_liftM (checkName.WF hwf _ _)) fun _ s'' ⟨⟨hn, hp⟩, hs''⟩ => ?_
    dsimp only at hs''; subst hs''
    refine WF.pure ⟨_, rfl, hs', ?_, ?_⟩
    · exact hwf.insert _ _ (by rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hn)
    have hn' : (insertConsts envCtors.constants (recs.map ConstantInfo.recInfo)).find?
        (mkRecName types.toArray[i].name) = none := by
      rw [← hc]; rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    obtain ⟨hn₁, hn₂⟩ := insertConsts_find?_none mapWF hfr hnd hn'
    refine ⟨recs ++ [?v], ?hc, hq, ?hnd, ?hfr, ?hpr, ?hrecs⟩
    case hc =>
      show env.constants.insert _ _ = _
      rw [List.map_append, insertConsts_append, ← hc]; rfl
    case hnd =>
      rw [List.map_append, List.map_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      rintro a ha b rfl rfl
      exact hn₂ ha
    case hfr =>
      intro ci hci
      rcases List.mem_append.1 (by simpa only [List.map_append] using hci) with h | h
      · exact hfr ci h
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; exact hn₁
    case hpr =>
      intro ci hci
      rcases List.mem_append.1 (by simpa only [List.map_append] using hci) with h | h
      · exact hpr ci h
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; exact hp
    case hrecs =>
      have hit : i < d.types.length := by omega
      rw [List.take_add_one, List.getElem?_zipIdx]
      simp only [List.getElem?_eq_getElem hit, Option.map_some, Option.toList_some, Nat.zero_add]
      refine (Lean4Lean.List.Forall₂.append_of_left (Lean4Lean.List.Forall₂.length_eq hrecs)).2
        ⟨hrecs, .cons ?_ .nil⟩
      have hTi : d.types[i]? = some d.types[i] := List.getElem?_eq_getElem hit
      obtain ⟨t, ht, htT, -⟩ := (List.Forall₂.getElem?_r hR.elaborates.types hTi)
      obtain rfl : types[i] = t :=
        Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans ht)
      have hisz : i < recInfos.size := by rw [hR.size]; exact hil
      have hinfo : recInfos[i]? = some recInfos[i]! := by
        rw [getElem!_pos _ i hisz]; exact Array.getElem?_eq_getElem hisz
      have hname : mkRecName types.toArray[i].name = mkRecName d.types[i].name := by
        simp [htT]
      refine ⟨hname, fun envC envR h1 h2 h3 h4 h5 => ⟨?_, ?_⟩⟩
      · unfold TrRecVal
        refine ⟨hname, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK, ?_, (hrules envC envR h1 h2 h3 h4 h5)⟩
        · rw [getMajorInduct_eq, majorInductGo_inferImplicit]
          simpa [RecursorVal.getMajorIdx, recTypeExpr] using hR.major i _ _ hTi hinfo
        · intro hl
          rcases hEu with rfl | ⟨u, rfl, hu⟩
          · exact absurd rfl (hE.1 hl)
          · exact ⟨u, hu, rfl⟩
        · intro hl
          rcases hEu with rfl | ⟨u, rfl, hu⟩
          · rfl
          · exact absurd (hE.2 (by simp)) hl
        · exact hR.nparams
        · show stats.nindices[i]! = _
          have := hR.nindices i _ hTi
          rw [getElem!_pos _ i (by
            have := (Array.getElem?_eq_some_iff.1 this).1; exact this)]
          exact Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans this)
        · show (recInfos.map (·.motive)).size = _; simp [hR.size, hdlen]
        · exact hR.nminors
        · show (types.toArray.map (·.name)).toList = d.types.map (·.name)
          simp only [List.map_toArray, List.toList_toArray]
          exact List.Forall₂.map_eq
            (Lean4Lean.List.Forall₂.imp (fun t T h => h.1.symm) hR.elaborates.types)
        · show (c.safety != .safe) = d.isUnsafe
          rw [hR.safety, hsafety, hR.isUnsafe]; cases isUnsafe <;> rfl
      · refine ⟨?_, ?_, ?_⟩
        · show c.safety ≤ ConstantInfo.safety (.recInfo _)
          simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
          rw [hR.safety, hsafety]
          cases isUnsafe <;> exact DefinitionSafety.le_rfl
        · show (getRecLevelParams elimLevel c₂.lparams).length = d.recUVars
          unfold VInductDecl.recUVars
          rcases hEu with rfl | ⟨u, rfl, hu⟩
          · rw [if_neg (fun h => hE.1 h rfl)]; simp [getRecLevelParams, hR.uvars]
          · rw [if_pos (hE.2 (by simp))]; simp [getRecLevelParams, hR.uvars]
        · have := (hR.recType i _ _ hTi hinfo envC h1 h2 h3).inferImplicit 1000 false
          simp only [recTypeExpr] at this; exact this
  · obtain ⟨-, -, recs, hc, hq, hnd, hfr, hpr, hrecs⟩ := hp
    have htk : d.types.zipIdx.take types.length = d.types.zipIdx := by
      rw [List.take_of_length_le (by simp [hdlen])]
    rw [htk] at hrecs
    exact ⟨recs, hc, hq, hnd, hfr, hpr, Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hrecs,
      fun envC envR h1 h2 h3 h4 h5 =>
        Lean4Lean.List.Forall₂.imp (fun _ _ h => h.2 envC envR h1 h2 h3 h4 h5) hrecs⟩



end AddInductive
end Lean4Lean

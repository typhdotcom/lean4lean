import Lean4Lean.Theory.Typing.LogRel.WHRed
import Lean4Lean.Theory.Typing.LogRel.Rules

/-!
# The rule names of a well-formed environment are unique

Head reduction (`LogRel.Step`) is deterministic when the environment's rules have unique names
(`LogRel.StepUniq`). Each declaration of a well-formed environment adds fresh constants, so every
name a rule is about plays one role: a definition's unfolding, one recursor of one block, a
constructor, `Quot.lift` or `Quot.mk` (`Roles`). That gives `VEnv.WF.stepUniq`.
-/

namespace Lean4Lean
open VExpr LogRel

namespace VEnv

theorem addConst_constants_iff {env env' : VEnv} (h : env.addConst n ci = some env') :
    env.constants n = none ∧ ∀ m, env'.constants m ≠ none ↔ env.constants m ≠ none ∨ m = n := by
  unfold addConst at h; split at h <;> cases h
  refine ⟨‹_›, fun m => ?_⟩
  by_cases e : n = m
  · subst e; simp
  · simp [e, Ne.symm e]

theorem addConstList_spec : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' →
    (cs.map (·.1)).Nodup ∧ (∀ p ∈ cs, env.constants p.1 = none) ∧
    ∀ m, env'.constants m ≠ none ↔ env.constants m ≠ none ∨ m ∈ cs.map (·.1)
  | _, _, [], h => by cases h; simp
  | _, _, (n, ci) :: cs, h => by
    simp only [addConstList, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    obtain ⟨f1, f2⟩ := addConst_constants_iff h1
    obtain ⟨g1, g2, g3⟩ := addConstList_spec h2
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, g1⟩, ?_, fun m => ?_⟩
    · obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
      exact (f2 p.1).2 (.inr e) (g2 p hp)
    · rintro p (_ | ⟨_, hp⟩)
      · exact f1
      · have := g2 p hp
        exact Classical.byContradiction fun hc => (f2 p.1).2 (.inl hc) this
    · rw [g3, f2]; simp [or_assoc]

theorem addConsts_eq {env : VEnv} (cis : List VDefVal) :
    env.addConsts cis = env.addConstList (cis.map fun ci => (ci.name, ci.toVConstant)) := by
  simp [addConsts, addConstList, List.foldlM_map]

theorem addQuot_spec {env env' : VEnv} (h : env.addQuot = some env') :
    env.constants ``Quot.lift = none ∧ env.constants ``Quot.mk = none ∧ env.constants ``Quot = none ∧
    ∀ m, env'.constants m ≠ none ↔ env.constants m ≠ none ∨ m = ``Quot ∨ m = ``Quot.mk ∨
      m = ``Quot.lift ∨ m = ``Quot.ind := by
  simp only [addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, h5⟩ := h
  cases h5
  have a1 := addConst_constants_iff h1
  have a2 := addConst_constants_iff h2
  have a3 := addConst_constants_iff h3
  have a4 := addConst_constants_iff h4
  refine ⟨?_, ?_, a1.1, fun m => ?_⟩
  · exact Classical.byContradiction fun hc => (a2.2 _).2 (.inl ((a1.2 _).2 (.inl hc))) a3.1
  · exact Classical.byContradiction fun hc => (a1.2 _).2 (.inl hc) a2.1
  · change e4.constants m ≠ none ↔ _
    rw [a4.2, a3.2, a2.2, a1.2]; simp only [or_assoc]

end VEnv

namespace StepUniqProof

/-- What a name is about, in the rules of an environment. -/
inductive Role where
  | defn (df : VDefEq)
  | recr (d : VInductDecl) (j : Nat)
  | ctor (d : VInductDecl) (t : Nat) (c : VConstructor)
  | indTy (d : VInductDecl) (t : Nat)
  | quotTy
  | quotLift
  | quotMk
  | other

/-- Every name a rule is about has its role under `ρ`, and a name the environment does not have
has none. -/
structure Roles (env : VEnv) (ρ : Name → Role) : Prop where
  defn : env.defeqs df → df.lhs = .const n us → ρ n = .defn df
  recr : env.inducts s = some (d, t) → j < d.allTypes.length → ρ (d.recName j) = .recr d j
  ctor : env.inducts s = some (d, t) → (j, c) ∈ d.allCtors → ∃ d' t' T' c',
    ρ c.name = .ctor d' t' c' ∧ d'.types[t']? = some T' ∧ c' ∈ T'.ctors ∧
    ∃ T, d.allTypes[j]? = some T ∧ T.ctors.map (·.name) = T'.ctors.map (·.name)
  ownCtor {s : Name} {d : VInductDecl} {t t' : Nat} {T : VInductiveType} {c : VConstructor} :
    env.inducts s = some (d, t) → d.types[t']? = some T → c ∈ T.ctors →
    ρ c.name = .ctor d t' c
  indTy : env.inducts n = some (d, t) → ρ n = .indTy d t
  quot : env.defeqs quotDefEq →
    ρ ``Quot.lift = .quotLift ∧ ρ ``Quot.mk = .quotMk ∧ ρ ``Quot = .quotTy
  fresh : env.constants n = none → ρ n = .other

structure Names (env : VEnv) : Prop where
  roles : ∃ ρ, Roles env ρ
  ctorNodup : env.inducts s = some (d, t) → T ∈ d.allTypes → (T.ctors.map (·.name)).Nodup
  iota : env.inducts s = some (d, t) → df ∈ d.iotaRules → env.defeqs df

theorem Roles.const (H : Roles env ρ) (h : ρ n ≠ .other) : env.constants n ≠ none :=
  fun h' => h (H.fresh h')

open Classical in
/-- `ρ`, with the names `N` given the roles `σ`. -/
noncomputable def upd (ρ σ : Name → Role) (N : Name → Prop) : Name → Role :=
  fun n => if N n then σ n else ρ n

theorem upd_old {ρ σ : Name → Role} {N : Name → Prop} (H : Roles env ρ)
    (hN : ∀ m, N m → env.constants m = none) (h : ρ n ≠ .other) : upd ρ σ N n = ρ n := by
  unfold upd; rw [if_neg fun hn => H.const h (hN _ hn)]

theorem upd_new {ρ σ : Name → Role} {N : Name → Prop} (h : N n) : upd ρ σ N n = σ n := by
  unfold upd; rw [if_pos h]

theorem quotDefEq_lhs : ∃ A b, quotDefEq.lhs = .lam A b := ⟨_, _, rfl⟩

theorem defn_ne_quot (ci : VDefVal) : ci.toDefEq ≠ quotDefEq := fun h => by
  obtain ⟨A, b, e⟩ := quotDefEq_lhs
  rw [← h] at e; cases e

theorem foralls_app_ne_bvar : ∀ {Bs Cs : List VExpr} {f a : VExpr} {i : Nat},
    VExpr.foralls Bs (.app f a) ≠ .foralls Cs (.bvar i)
  | [], [], _, _, _, h => by cases h
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | _ :: _, _ :: _, _, _, _, h => by
    injection h with _ h; exact foralls_app_ne_bvar h

theorem iotaRule_ne_quot {d : VInductDecl} (h : df ∈ d.iotaRules) : df ≠ quotDefEq := by
  rintro rfl
  simp only [VInductDecl.iotaRules, List.mem_map] at h
  obtain ⟨⟨⟨j, c⟩, q⟩, -, e⟩ := h
  obtain ⟨Cs, hC⟩ : ∃ Cs, quotDefEq.type = .foralls Cs (.bvar 3) := ⟨[_, _, _, _, _, _], rfl⟩
  have := congrArg VDefEq.type e
  rw [hC] at this
  exact foralls_app_ne_bvar this

theorem lams_ne_const : ∀ {Bs : List VExpr} {e : VExpr}, Bs ≠ [] → VExpr.lams Bs e ≠ .const n us
  | [], _, h => (h rfl).elim
  | _ :: _, _, _ => nofun

theorem iotaRule_lhs {d : VInductDecl} (hd : d.types ≠ []) (h : df ∈ d.iotaRules) :
    df.lhs ≠ .const n us := by
  simp only [VInductDecl.iotaRules, List.mem_map] at h
  obtain ⟨⟨⟨j, c⟩, q⟩, -, rfl⟩ := h
  refine lams_ne_const ?_
  have : d.motiveTypes d.recLevels d.motiveLevel ≠ [] := by
    simp only [VInductDecl.motiveTypes, ne_eq, List.map_eq_nil_iff, List.zipIdx_eq_nil_iff]
    simp [VInductDecl.allTypes, hd]
  simp [VInductDecl.recBinders, this]

/-! ### Lists -/

theorem nodup_getElem?_inj {α} : ∀ {l : List α} {i j : Nat} {x : α}, l.Nodup → l[i]? = some x →
    l[j]? = some x → i = j
  | a :: l, 0, 0, _, _, _, _ => rfl
  | a :: l, 0, j + 1, x, h, h1, h2 => by
    cases h1; exact ((List.nodup_cons.1 h).1 (List.mem_of_getElem? h2)).elim
  | a :: l, i + 1, 0, x, h, h1, h2 => by
    cases h2; exact ((List.nodup_cons.1 h).1 (List.mem_of_getElem? h1)).elim
  | a :: l, i + 1, j + 1, x, h, h1, h2 => by
    rw [nodup_getElem?_inj (List.nodup_cons.1 h).2 h1 h2]

theorem nodup_map_of_inj {α β} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj hf (List.nodup_cons.1 h).2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    cases hf _ _ e; exact (List.nodup_cons.1 h).1 hb

theorem forall₂_names {R : VConstructor → VConstructor → Prop}
    (hR : ∀ a b, R a b → b.name = a.name) :
    ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ → l₂.map (·.name) = l₁.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp [hR _ _ h, forall₂_names hR hs]

/-- Constructors of a list of types, each with its position from `k`, are distinct by position and
name when each type's constructor names are. -/
theorem ctorsAt_nodup (k : Nat) : ∀ (L : List VInductiveType),
    (∀ T ∈ L, (T.ctors.map (·.name)).Nodup) →
    (((L.zipIdx k).map fun (T, j) => T.ctors.map (j, ·)).flatten.map
      fun p => (p.1, p.2.name)).Nodup ∧
    ∀ p ∈ ((L.zipIdx k).map fun (T, j) => T.ctors.map (j, ·)).flatten, k ≤ p.1
  | [], _ => by simp
  | T :: L, H => by
    obtain ⟨ih1, ih2⟩ := ctorsAt_nodup (k + 1) L fun T hT => H T (.tail _ hT)
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.map_append,
      List.mem_append, List.map_map]
    refine ⟨List.nodup_append.2 ⟨?_, ih1, ?_⟩, ?_⟩
    · have := nodup_map_of_inj (f := fun n => (k, n)) (fun _ _ e => by cases e; rfl)
        (H T (.head _))
      simpa [List.map_map, Function.comp_def] using this
    · intro a ha b hb e
      simp only [List.mem_map] at ha hb
      obtain ⟨c, -, rfl⟩ := ha
      obtain ⟨p, hp, rfl⟩ := hb
      have := ih2 p hp
      have e := congrArg Prod.fst e
      simp at e; omega
    · rintro p (hp | hp)
      · simp only [List.mem_map] at hp; obtain ⟨c, -, rfl⟩ := hp; exact Nat.le_refl _
      · have := ih2 p hp; omega

theorem allCtors_pos {d : VInductDecl} (H : ∀ T ∈ d.allTypes, (T.ctors.map (·.name)).Nodup)
    {q q' j : Nat} {c c' : VConstructor} (h1 : d.allCtors[q]? = some (j, c))
    (h2 : d.allCtors[q']? = some (j, c')) (h3 : c.name = c'.name) : q = q' := by
  have hn := (ctorsAt_nodup 0 d.allTypes H).1
  have h1' : (d.allCtors.map fun p => (p.1, p.2.name))[q]? = some (j, c.name) := by
    simp [h1]
  have h2' : (d.allCtors.map fun p => (p.1, p.2.name))[q']? = some (j, c.name) := by
    simp [h2, h3]
  exact nodup_getElem?_inj hn h1' h2'

theorem recConsts_names (d : VInductDecl) :
    d.recConsts.map (·.1) = (List.range d.allTypes.length).map d.recName := by
  refine List.ext_getElem? fun i => ?_
  simp only [VInductDecl.recConsts, List.map_map, List.getElem?_map, List.getElem?_zipIdx]
  by_cases h : i < d.allTypes.length <;> simp [h]

theorem recName_inj {d : VInductDecl} (h : (d.recConsts.map (·.1)).Nodup) {j j' : Nat}
    (hj : j < d.allTypes.length) (hj' : j' < d.allTypes.length)
    (e : d.recName j = d.recName j') : j = j' := by
  rw [recConsts_names] at h
  refine nodup_getElem?_inj h (x := d.recName j) ?_ ?_
  · simp [List.getElem?_range hj]
  · simp [List.getElem?_range hj', e]

theorem mem_recNames {d : VInductDecl} {n : Name} :
    n ∈ d.recConsts.map (·.1) ↔ ∃ j, j < d.allTypes.length ∧ d.recName j = n := by
  rw [recConsts_names]; simp

theorem mem_ctorNames {d : VInductDecl} {T : VInductiveType} {c : VConstructor}
    (hT : T ∈ d.types) (hc : c ∈ T.ctors) : c.name ∈ d.ctorConsts.map (·.1) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hm : (j, c) ∈ d.ctors := by
    unfold VInductDecl.ctors
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩,
      List.mem_map_of_mem hc⟩
  unfold VInductDecl.ctorConsts
  rw [List.map_map]
  exact List.mem_map.2 ⟨(j, c), hm, rfl⟩

theorem types_ctors_nodup {d : VInductDecl} (h : (d.ctorConsts.map (·.1)).Nodup)
    {T : VInductiveType} (hT : T ∈ d.types) : (T.ctors.map (·.name)).Nodup := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  refine List.Nodup.sublist ?_ h
  have : T.ctors.map (j, ·) ∈ d.types.zipIdx.map fun (T, j) => T.ctors.map (j, ·) :=
    List.mem_map.2 ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩
  have := (List.sublist_flatten_of_mem this).map (fun p : Nat × VConstructor => p.2.name)
  simpa [VInductDecl.ctorConsts, VInductDecl.ctors, List.map_map, Function.comp_def] using this

theorem find_name {cis : List VDefVal} (hnd : (cis.map (·.name)).Nodup) {ci : VDefVal}
    (h : ci ∈ cis) : cis.find? (fun c => decide (c.name = ci.name)) = some ci := by
  induction cis with
  | nil => cases h
  | cons c cs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases e : c.name = ci.name
    · rw [decide_eq_true e]
      rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact (hnd.1 (e ▸ List.mem_map_of_mem h)).elim
    · rw [decide_eq_false e]
      rcases List.mem_cons.1 h with rfl | h
      · exact (e rfl).elim
      · exact ih hnd.2 h

/-! ### The invariant -/

theorem Names.empty : Names .empty where
  roles := ⟨fun _ => .other, nofun, nofun, nofun, nofun, nofun, nofun, fun _ => rfl⟩
  ctorNodup := nofun
  iota := nofun

/-- The roles stay when constants are added and the rules and blocks are kept. -/
theorem Roles.addConsts {env env' : VEnv} (H : Roles env ρ) (hd : env'.defeqs = env.defeqs)
    (hi : env'.inducts = env.inducts) (hc : ∀ n, env.constants n ≠ none → env'.constants n ≠ none) :
    Roles env' ρ where
  defn h := H.defn (hd ▸ h)
  recr h := H.recr (hi ▸ h)
  ctor h := H.ctor (hi ▸ h)
  ownCtor h := H.ownCtor (hi ▸ h)
  indTy h := H.indTy (hi ▸ h)
  quot h := H.quot (hd ▸ h)
  fresh h := H.fresh (Classical.byContradiction fun h' => hc _ h' h)

theorem Names.addConsts {env env' : VEnv} (H : Names env) (hd : env'.defeqs = env.defeqs)
    (hi : env'.inducts = env.inducts) (hc : ∀ n, env.constants n ≠ none → env'.constants n ≠ none) :
    Names env' where
  roles := let ⟨ρ, h⟩ := H.roles; ⟨ρ, h.addConsts hd hi hc⟩
  ctorNodup h := H.ctorNodup (hi ▸ h)
  iota h1 h2 := hd ▸ H.iota (hi ▸ h1) h2

open Classical in
/-- The roles of a block's new names: its recursors, and otherwise constructors. -/
noncomputable def newRole (d : VInductDecl) (n : Name) : Role :=
  if h : ∃ j, j < d.allTypes.length ∧ d.recName j = n then .recr d h.choose
  else if h : ∃ (t : Nat) (T : VInductiveType), d.types[t]? = some T ∧ T.name = n then .indTy d h.choose
  else if h : ∃ p : Nat × VConstructor, p ∈ d.ctors ∧ p.2.name = n then
    .ctor d h.choose.1 h.choose.2
  else .other

theorem Names.def' {env env₁ : VEnv} {ci : VDefVal} (H : Names env)
    (h1 : env.addConst ci.name ci.toVConstant = some env₁) : Names (env₁.addDefEq ci.toDefEq) := by
  obtain ⟨ρ, hρ⟩ := H.roles
  obtain ⟨f1, f2⟩ := VEnv.addConst_constants_iff h1
  have hd₁ := VEnv.addConst_defeqs h1
  have hi₁ := VEnv.addConst_inducts h1
  have hN : ∀ m, m = ci.name → env.constants m = none := fun _ e => e ▸ f1
  refine ⟨⟨upd ρ (fun _ => .defn ci.toDefEq) (· = ci.name), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro df n us h e
    rcases h with rfl | h
    · cases e; exact upd_new rfl
    · rw [hd₁] at h; rw [upd_old hρ hN (by rw [hρ.defn h e]; nofun), hρ.defn h e]
  · intro s d t j h hj
    change env₁.inducts s = _ at h
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.recr h hj]; nofun), hρ.recr h hj]
  · intro s d t j c h hc
    change env₁.inducts s = _ at h
    rw [hi₁] at h; obtain ⟨d', t', T', c', e, r⟩ := hρ.ctor h hc
    exact ⟨d', t', T', c', by rw [upd_old hρ hN (by rw [e]; nofun), e], r⟩
  · intro s d t t' T c h hT hc
    change env₁.inducts s = _ at h
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.ownCtor h hT hc]; nofun), hρ.ownCtor h hT hc]
  · intro n d t h
    change env₁.inducts n = _ at h
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.indTy h]; nofun), hρ.indTy h]
  · intro h
    rcases h with h | h
    · exact (defn_ne_quot ci h.symm).elim
    · rw [hd₁] at h
      obtain ⟨q1, q2, q3⟩ := hρ.quot h
      rw [upd_old hρ hN (by rw [q1]; nofun), upd_old hρ hN (by rw [q2]; nofun),
        upd_old hρ hN (by rw [q3]; nofun)]
      exact ⟨q1, q2, q3⟩
  · intro n hn
    change env₁.constants n = none at hn
    have hn' : n ≠ ci.name := fun e => (f2 n).2 (.inr e) hn
    unfold upd; rw [if_neg hn']
    exact hρ.fresh (Classical.byContradiction fun h => (f2 n).2 (.inl h) hn)
  · intro s d t T h hT; change env₁.inducts s = _ at h; rw [hi₁] at h; exact H.ctorNodup h hT
  · intro s d t df h hdf
    change env₁.inducts s = _ at h; rw [hi₁] at h; exact .inr (hd₁ ▸ H.iota h hdf)

theorem _root_.Lean4Lean.VEnv.addDefEqs_constants : ∀ {env : VEnv} {cis : List VDefVal},
    (env.addDefEqs cis).constants = env.constants
  | _, [] => rfl
  | _, _ :: _ => VEnv.addDefEqs_constants (env := VEnv.addDefEq _ _)

theorem Names.mutualDef' {env env₁ : VEnv} {cis : List VDefVal} (H : Names env)
    (h1 : env.addConsts cis = some env₁) : Names (env₁.addDefEqs cis) := by
  obtain ⟨ρ, hρ⟩ := H.roles
  rw [VEnv.addConsts_eq] at h1
  obtain ⟨g1, g2, g3⟩ := VEnv.addConstList_spec h1
  have hd₁ := VEnv.addConstList_defeqs' h1
  have hi₁ := VEnv.addConstList_inducts h1
  have hnd : (cis.map (·.name)).Nodup := by simpa [List.map_map, Function.comp_def] using g1
  let N : Name → Prop := (· ∈ cis.map (·.name))
  have hN : ∀ m, N m → env.constants m = none := fun m hm => by
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
    exact g2 _ (List.mem_map_of_mem (f := fun ci : VDefVal => (ci.name, ci.toVConstant)) hci)
  let σ : Name → Role := fun n => match cis.find? (fun c => decide (c.name = n)) with
    | some ci => .defn ci.toDefEq
    | none => .other
  have hσ (ci) (hci : ci ∈ cis) : σ ci.name = .defn ci.toDefEq := by
    simp only [σ, find_name hnd hci]
  refine ⟨⟨upd ρ σ N, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro df n us h e
    rcases VEnv.addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
    · cases e; rw [upd_new (List.mem_map_of_mem hci), hσ ci hci]
    · rw [hd₁] at h; rw [upd_old hρ hN (by rw [hρ.defn h e]; nofun), hρ.defn h e]
  · intro s d t j h hj
    rw [VEnv.addDefEqs_inducts, hi₁] at h
    rw [upd_old hρ hN (by rw [hρ.recr h hj]; nofun), hρ.recr h hj]
  · intro s d t j c h hc
    rw [VEnv.addDefEqs_inducts, hi₁] at h
    obtain ⟨d', t', T', c', e, r⟩ := hρ.ctor h hc
    exact ⟨d', t', T', c', by rw [upd_old hρ hN (by rw [e]; nofun), e], r⟩
  · intro s d t t' T c h hT hc
    rw [VEnv.addDefEqs_inducts, hi₁] at h
    rw [upd_old hρ hN (by rw [hρ.ownCtor h hT hc]; nofun), hρ.ownCtor h hT hc]
  · intro n d t h
    rw [VEnv.addDefEqs_inducts, hi₁] at h
    rw [upd_old hρ hN (by rw [hρ.indTy h]; nofun), hρ.indTy h]
  · intro h
    rcases VEnv.addDefEqs_defeqs h with ⟨ci, -, h⟩ | h
    · exact (defn_ne_quot ci h.symm).elim
    · rw [hd₁] at h
      obtain ⟨q1, q2, q3⟩ := hρ.quot h
      rw [upd_old hρ hN (by rw [q1]; nofun), upd_old hρ hN (by rw [q2]; nofun),
        upd_old hρ hN (by rw [q3]; nofun)]
      exact ⟨q1, q2, q3⟩
  · intro n hn
    rw [VEnv.addDefEqs_constants] at hn
    have hn' : ¬N n := fun e => (g3 n).2 (.inr (by
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 e
      exact List.mem_map.2 ⟨_, List.mem_map_of_mem hci, rfl⟩)) hn
    unfold upd; rw [if_neg hn']
    exact hρ.fresh (Classical.byContradiction fun h => (g3 n).2 (.inl h) hn)
  · intro s d t T h hT
    rw [VEnv.addDefEqs_inducts, hi₁] at h; exact H.ctorNodup h hT
  · intro s d t df h hdf
    rw [VEnv.addDefEqs_inducts, hi₁] at h
    exact VEnv.addDefEqs_le.defeqs (hd₁ ▸ H.iota h hdf)

theorem Names.quot' {env env' : VEnv} (H : Names env) (h1 : env.addQuot = some env')
    (hle : env ≤ env') : Names env' := by
  obtain ⟨ρ, hρ⟩ := H.roles
  obtain ⟨f1, f2, f0, f3⟩ := VEnv.addQuot_spec h1
  have hi₁ := VEnv.addQuot_inducts h1
  let N : Name → Prop := fun n => n = ``Quot.lift ∨ n = ``Quot.mk ∨ n = ``Quot
  have hN : ∀ m, N m → env.constants m = none := by rintro _ (rfl | rfl | rfl) <;> assumption
  let σ : Name → Role := fun n =>
    if n = ``Quot.lift then .quotLift else if n = ``Quot.mk then .quotMk else .quotTy
  refine ⟨⟨upd ρ σ N, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro df n us h e
    rcases VEnv.addQuot_defeqs h1 h with rfl | h
    · obtain ⟨A, b, e'⟩ := quotDefEq_lhs; rw [e'] at e; cases e
    · rw [upd_old hρ hN (by rw [hρ.defn h e]; nofun), hρ.defn h e]
  · intro s d t j h hj
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.recr h hj]; nofun), hρ.recr h hj]
  · intro s d t j c h hc
    rw [hi₁] at h; obtain ⟨d', t', T', c', e, r⟩ := hρ.ctor h hc
    exact ⟨d', t', T', c', by rw [upd_old hρ hN (by rw [e]; nofun), e], r⟩
  · intro s d t t' T c h hT hc
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.ownCtor h hT hc]; nofun), hρ.ownCtor h hT hc]
  · intro n d t h
    rw [hi₁] at h; rw [upd_old hρ hN (by rw [hρ.indTy h]; nofun), hρ.indTy h]
  · intro _
    rw [upd_new (.inl rfl), upd_new (.inr (.inl rfl)), upd_new (.inr (.inr rfl))]
    simp [σ]
  · intro n hn
    have := mt (f3 n).2 (by simpa using hn)
    simp only [not_or] at this
    unfold upd; rw [if_neg (by simp [N, this.2.1, this.2.2.1, this.2.2.2.1])]
    exact hρ.fresh (by simpa using this.1)
  · intro s d t T h hT; rw [hi₁] at h; exact H.ctorNodup h hT
  · intro s d t df h hdf
    rw [hi₁] at h
    exact hle.defeqs (H.iota h hdf)

theorem _root_.Lean4Lean.VEnv.addDefEqList_constants : ∀ {env : VEnv} {dfs : List VDefEq},
    (env.addDefEqList dfs).constants = env.constants
  | _, [] => rfl
  | _, _ :: _ => VEnv.addDefEqList_constants (env := VEnv.addDefEq _ _)

theorem _root_.Lean4Lean.VEnv.mem_addDefEqList : ∀ {env : VEnv} {dfs : List VDefEq} {df},
    df ∈ dfs → (env.addDefEqList dfs).defeqs df
  | env, df :: dfs, _, .head _ =>
    show ((env.addDefEq df).addDefEqList dfs).defeqs df from
      (VEnv.addDefEqList_le (env := env.addDefEq df)).defeqs (.inl rfl)
  | _, _ :: _, _, .tail _ h => VEnv.mem_addDefEqList (env := VEnv.addDefEq _ _) h

theorem newRole_rec {d : VInductDecl} (hnd : (d.recConsts.map (·.1)).Nodup) {j : Nat}
    (hj : j < d.allTypes.length) : newRole d (d.recName j) = .recr d j := by
  have h : ∃ j', j' < d.allTypes.length ∧ d.recName j' = d.recName j := ⟨j, hj, rfl⟩
  unfold newRole; rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [recName_inj hnd h1 hj h2]

theorem nodup_map_inj_on {α β} {f : α → β} {a b : α} :
    ∀ {l : List α}, (l.map f).Nodup → a ∈ l → b ∈ l → f a = f b → a = b
  | x :: l, h, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    cases ha with
    | head => cases hb with
      | head => rfl
      | tail _ hb => exact (h.1 (e ▸ List.mem_map_of_mem hb)).elim
    | tail _ ha => cases hb with
      | head => exact (h.1 (e.symm ▸ List.mem_map_of_mem ha)).elim
      | tail _ hb => exact nodup_map_inj_on h.2 ha hb e

theorem mem_ctors {d : VInductDecl} {T : VInductiveType} {c : VConstructor} {t : Nat}
    (hT : d.types[t]? = some T) (hc : c ∈ T.ctors) : (t, c) ∈ d.ctors :=
  List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨(T, t), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩,
    List.mem_map_of_mem hc⟩

theorem mem_typeNames {d : VInductDecl} {T : VInductiveType} {t : Nat}
    (hT : d.types[t]? = some T) : T.name ∈ d.typeConsts.map (·.1) := by
  simp only [VInductDecl.typeConsts, List.map_map]
  exact List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩

theorem newRole_ctor {d : VInductDecl} {n : Name} (h : n ∉ d.recConsts.map (·.1))
    (ht : n ∉ d.typeConsts.map (·.1)) (hnd : (d.ctorConsts.map (·.1)).Nodup)
    {p : Nat × VConstructor} (hp : p ∈ d.ctors) (hn : p.2.name = n) :
    newRole d n = .ctor d p.1 p.2 := by
  have h2 : ¬∃ (t : Nat) (T : VInductiveType), d.types[t]? = some T ∧ T.name = n := fun ⟨_, _, h1, h2⟩ =>
    ht (h2 ▸ mem_typeNames h1)
  have h3 : ∃ p : Nat × VConstructor, p ∈ d.ctors ∧ p.2.name = n := ⟨p, hp, hn⟩
  unfold newRole; rw [dif_neg (fun h' => h (mem_recNames.2 h')), dif_neg h2, dif_pos h3]
  obtain ⟨hq, hqn⟩ := h3.choose_spec
  have hnd' : (d.ctors.map (·.2.name)).Nodup := by
    simpa [VInductDecl.ctorConsts, List.map_map, Function.comp_def] using hnd
  rw [nodup_map_inj_on hnd' hq hp (hqn.trans hn.symm)]

theorem newRole_indTy {d : VInductDecl} {n : Name} (h : n ∉ d.recConsts.map (·.1))
    (hnd : (d.typeConsts.map (·.1)).Nodup) {t : Nat} {T : VInductiveType}
    (hT : d.types[t]? = some T) (hn : T.name = n) : newRole d n = .indTy d t := by
  have h2 : ∃ (t : Nat) (T : VInductiveType), d.types[t]? = some T ∧ T.name = n := ⟨t, T, hT, hn⟩
  unfold newRole; rw [dif_neg (fun h' => h (mem_recNames.2 h')), dif_pos h2]
  obtain ⟨T', h1, h2'⟩ := h2.choose_spec
  have hnd' : (d.types.map (·.name)).Nodup := by
    simpa [VInductDecl.typeConsts, List.map_map, Function.comp_def] using hnd
  congr 1
  exact nodup_getElem?_inj hnd' (x := n) (by simp [h1, h2']) (by simp [hT, hn])

theorem Names.induct' {env env' : VEnv} {d : VInductDecl} (H : Names env) (hd : d.WF env)
    (h1 : env.addInduct d = some env') : Names env' := by
  have hle := VEnv.addInduct_le h1
  obtain ⟨ρ, hρ⟩ := H.roles
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := h1
  obtain ⟨t1, t2, t3⟩ := VEnv.addConstList_spec hT
  obtain ⟨c1, c2, c3⟩ := VEnv.addConstList_spec hC
  obtain ⟨r1, r2, r3⟩ := VEnv.addConstList_spec hR
  have hc' : env'.constants = envR.constants := by
    rw [VEnv.addBlock_constants hB, VEnv.addDefEqList_constants]
  have hd' {df} (h : env'.defeqs df) : df ∈ d.iotaRules ∨ env.defeqs df := by
    rw [VEnv.addBlock_defeqs hB] at h
    rcases VEnv.addDefEqList_defeqs' h with h | h
    · exact .inl h
    · rw [VEnv.addConstList_defeqs' hR, VEnv.addConstList_defeqs' hC,
        VEnv.addConstList_defeqs' hT] at h
      exact .inr h
  have hi' {s b} (h : env'.inducts s = some b) : env.inducts s = some b ∨ b.1 = d := by
    rcases VEnv.addBlock_inducts hB h with h | ⟨h, -⟩
    · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR, VEnv.addConstList_inducts hC,
        VEnv.addConstList_inducts hT] at h
      exact .inl h
    · exact .inr h
  have envT_none {m} (h : envT.constants m = none) : env.constants m = none :=
    Classical.byContradiction fun h' => (t3 m).2 (.inl h') h
  have ctorFresh {m} (hm : m ∈ d.ctorConsts.map (·.1)) : env.constants m = none := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm; exact envT_none (c2 p hp)
  have recFreshC {m} (hm : m ∈ d.recConsts.map (·.1)) : envC.constants m = none := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm; exact r2 p hp
  have recFresh {m} (hm : m ∈ d.recConsts.map (·.1)) : env.constants m = none :=
    envT_none (Classical.byContradiction fun h' => (c3 m).2 (.inl h') (recFreshC hm))
  have recNotCtor {m} (hm : m ∈ d.recConsts.map (·.1)) : m ∉ d.ctorConsts.map (·.1) :=
    fun hm' => (c3 m).2 (.inr hm') (recFreshC hm)
  have typeNotRec {m} (hm : m ∈ d.typeConsts.map (·.1)) : m ∉ d.recConsts.map (·.1) :=
    fun hm' => (c3 m).2 (.inl ((t3 m).2 (.inr hm))) (recFreshC hm')
  have typeNotCtor {m} (hm : m ∈ d.typeConsts.map (·.1)) : m ∉ d.ctorConsts.map (·.1) := by
    intro hm'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm'
    exact (t3 p.1).2 (.inr hm) (c2 p hp)
  have typeFresh {m} (hm : m ∈ d.typeConsts.map (·.1)) : env.constants m = none := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm; exact t2 p hp
  let N : Name → Prop := fun n => n ∈ d.recConsts.map (·.1) ∨ n ∈ d.ctorConsts.map (·.1) ∨
    n ∈ d.typeConsts.map (·.1)
  have hN : ∀ m, N m → env.constants m = none := by
    rintro m (hm | hm | hm); exact recFresh hm; exact ctorFresh hm; exact typeFresh hm
  -- the auxiliary types' constructors are an earlier block's
  have auxCtor {T} (hT' : T ∈ d.aux) : ∃ s dI tI TI, env.inducts s = some (dI, tI) ∧
      dI.types[tI]? = some TI ∧ T.ctors.map (·.name) = TI.ctors.map (·.name) ∧
      ∀ c ∈ T.ctors, ∃ cI ∈ TI.ctors, c.name = cI.name := by
    obtain ⟨n, -, hA⟩ := hd.aux T hT'
    obtain ⟨dI, tI, TI, i1, i2, -, -, -, -, -, i8⟩ := (hA envT hT).ind
    rw [VEnv.addConstList_inducts hT] at i1
    refine ⟨_, dI, tI, TI, i1, i2, forall₂_names (fun _ _ h => h.1) i8, fun c hc => ?_⟩
    obtain ⟨cI, hcI, h, -⟩ := Lean4Lean.List.Forall₂.forall_exists_r i8 c hc
    exact ⟨cI, hcI, h⟩
  refine ⟨⟨upd ρ (newRole d) N, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro df n us h e
    rcases hd' h with h | h
    · exact (iotaRule_lhs hd.nonempty h e).elim
    · rw [upd_old hρ hN (by rw [hρ.defn h e]; nofun), hρ.defn h e]
  · intro s d' t j h hj
    rcases hi' h with h | rfl
    · rw [upd_old hρ hN (by rw [hρ.recr h hj]; nofun), hρ.recr h hj]
    · rw [upd_new (.inl (mem_recNames.2 ⟨j, hj, rfl⟩)), newRole_rec r1 hj]
  · intro s d' t j c h hc
    rcases hi' h with h | rfl
    · obtain ⟨d'', t'', T'', c', e, r⟩ := hρ.ctor h hc
      exact ⟨d'', t'', T'', c', by rw [upd_old hρ hN (by rw [e]; nofun), e], r⟩
    · obtain ⟨T, hT', hcT⟩ := VInductDecl.mem_allCtors_iff.1 hc
      by_cases hj : j < d'.types.length
      · have hT : d'.types[j]? = some T := by
          rwa [VInductDecl.allTypes, List.getElem?_append_left hj] at hT'
        have hm := mem_ctorNames (List.mem_of_getElem? hT) hcT
        refine ⟨_, j, T, c, ?_, hT, hcT, T, hT', rfl⟩
        rw [upd_new (.inr (.inl hm)), newRole_ctor (fun h => recNotCtor h hm)
          (fun h => typeNotCtor h hm) c1 (mem_ctors hT hcT) rfl]
      · have hTa : d'.aux[j - d'.types.length]? = some T := by
          rwa [VInductDecl.allTypes, List.getElem?_append_right (by omega)] at hT'
        obtain ⟨s, dI, tI, TI, i1, i2, i3, i4⟩ := auxCtor (List.mem_of_getElem? hTa)
        obtain ⟨cI, hcI, e⟩ := i4 c hcT
        obtain ⟨d'', t'', T'', c', this, r1, r2, T0, r3, r4⟩ := hρ.ctor i1
          (VInductDecl.mem_allCtors_iff.2 ⟨TI, VInductDecl.allTypes_getElem? i2, hcI⟩)
        refine ⟨d'', t'', T'', c', by rw [e, upd_old hρ hN (by rw [this]; nofun), this], r1, r2,
          T, hT', ?_⟩
        cases (VInductDecl.allTypes_getElem? i2).symm.trans r3
        rw [i3]; exact r4
  · intro s d' t t' T c h hT' hc
    rcases hi' h with h | rfl
    · rw [upd_old hρ hN (by rw [hρ.ownCtor h hT' hc]; nofun), hρ.ownCtor h hT' hc]
    · have hm := mem_ctorNames (List.mem_of_getElem? hT') hc
      rw [upd_new (.inr (.inl hm)), newRole_ctor (fun h => recNotCtor h hm)
        (fun h => typeNotCtor h hm) c1 (mem_ctors hT' hc) rfl]
  · intro n d' t h
    rcases VEnv.addBlock_inducts hB h with h | ⟨e, T, hT', rfl⟩
    · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR, VEnv.addConstList_inducts hC,
        VEnv.addConstList_inducts hT] at h
      rw [upd_old hρ hN (by rw [hρ.indTy h]; nofun), hρ.indTy h]
    · have e' : d' = d := e
      rw [e'] at hT' ⊢
      have hm := mem_typeNames hT'
      rw [upd_new (.inr (.inr hm)), newRole_indTy (typeNotRec hm) t1 hT' rfl]
  · intro h
    rcases hd' h with h | h
    · exact (iotaRule_ne_quot h rfl).elim
    · obtain ⟨q1, q2, q3⟩ := hρ.quot h
      rw [upd_old hρ hN (by rw [q1]; nofun), upd_old hρ hN (by rw [q2]; nofun),
        upd_old hρ hN (by rw [q3]; nofun)]
      exact ⟨q1, q2, q3⟩
  · intro n hn
    rw [hc'] at hn
    have hR' := mt (r3 n).2 (by simpa using hn)
    simp only [not_or, Classical.not_not] at hR'
    have hC' := mt (c3 n).2 (by simpa using hR'.1)
    simp only [not_or, Classical.not_not] at hC'
    unfold upd
    rw [if_neg (by rintro (h | h | h); exact hR'.2 h; exact hC'.2 h; exact (t3 n).2 (.inr h) hC'.1)]
    exact hρ.fresh (envT_none hC'.1)
  · intro s d' t T h hT'
    rcases hi' h with h | e
    · exact H.ctorNodup h hT'
    · rw [show d' = d from e] at hT'
      rcases List.mem_append.1 hT' with hT' | hT'
      · exact types_ctors_nodup c1 hT'
      · obtain ⟨s, dI, tI, TI, i1, i2, i3, -⟩ := auxCtor hT'
        rw [i3]
        exact H.ctorNodup i1 (List.mem_of_getElem? (VInductDecl.allTypes_getElem? i2))
  · intro s d' t df h hdf
    rcases hi' h with h | e
    · exact hle.defeqs (H.iota h hdf)
    · rw [show d' = d from e] at hdf
      rw [VEnv.addBlock_defeqs hB]; exact VEnv.mem_addDefEqList hdf

theorem Names.decl {env env' : VEnv} (H : Names env) (hD : VDecl.WF env dc env') :
    Names env' := by
  have hle := hD.le
  cases hD with
  | «axiom» _ h1 | «opaque» _ h1 =>
    exact H.addConsts (VEnv.addConst_defeqs h1) (VEnv.addConst_inducts h1)
      fun n hn => ((VEnv.addConst_constants_iff h1).2 n).2 (.inl hn)
  | «example» => exact H
  | «def» _ h1 => exact H.def' h1
  | mutualDef _ h1 _ => exact H.mutualDef' h1
  | quot _ h1 => exact H.quot' h1 hle
  | induct hd _ h1 => exact H.induct' hd h1

theorem names_of_WF {env : VEnv} (henv : env.WF) : Names env := by
  obtain ⟨ds, H⟩ := henv
  induction H with
  | empty => exact .empty
  | decl hD _ ih => exact ih.decl hD

theorem Names.stepUniq {env : VEnv} (H : Names env) : StepUniq env := by
  obtain ⟨ρ, hρ⟩ := H.roles
  refine {
    delta := fun h1 h2 e1 e2 => ?_
    recName := fun h1 h2 hj hj' e => ?_
    ctor := fun h1 h2 h3 e => ?_
    ctorInert := fun h1 h2 => ⟨fun h3 e => ?_, fun h3 e => ?_, fun h3 hj e => ?_⟩
    quotMk := fun h1 => ⟨fun h3 e => ?_, fun _ e => absurd e (by decide), fun h3 hj e => ?_⟩
    recDelta := fun h1 hj h2 e => ?_
    recQuot := fun h1 h2 hj e => ?_
    quotDelta := fun h1 h2 e => ?_
    iota := H.iota }
  · have := (hρ.defn h1 e1).symm.trans (hρ.defn h2 e2); injection this
  · have := (hρ.recr h1 hj).symm.trans (e ▸ hρ.recr h2 hj'); injection this; constructor <;> assumption
  · exact allCtors_pos (fun T hT => H.ctorNodup h1 hT) h2 h3 e
  · obtain ⟨_, _, _, _, hc, -⟩ := hρ.ctor h1 h2; have := hc.symm.trans (hρ.defn h3 e); cases this
  · obtain ⟨_, _, _, _, hc, -⟩ := hρ.ctor h1 h2
    have := hc.symm.trans (e ▸ (hρ.quot h3).1); cases this
  · obtain ⟨_, _, _, _, hc, -⟩ := hρ.ctor h1 h2
    have := hc.symm.trans (e ▸ hρ.recr h3 hj); cases this
  · have := (hρ.quot h1).2.1.symm.trans (hρ.defn h3 e); cases this
  · have := (hρ.quot h1).2.1.symm.trans (e ▸ hρ.recr h3 hj); cases this
  · have := (hρ.recr h1 hj).symm.trans (hρ.defn h2 e); cases this
  · have := (hρ.recr h2 hj).symm.trans (e ▸ (hρ.quot h1).1); cases this
  · have := (hρ.quot h1).1.symm.trans (hρ.defn h2 e); cases this

end StepUniqProof

/-- The rules of a well-formed environment have unique names, so head reduction is
deterministic. -/
theorem VEnv.WF.stepUniq {env : VEnv} (henv : env.WF) : StepUniq env :=
  (StepUniqProof.names_of_WF henv).stepUniq

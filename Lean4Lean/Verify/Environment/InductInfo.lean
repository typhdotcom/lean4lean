import Lean4Lean.Verify.Environment.Lemmas

/-! What a model says about the inductive types, constructors and recursors of an environment:
each is recorded with the block `VEnv.inducts` holds for its type. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem List.Forall₂.map_eq {f : α → γ} {g : β → γ} :
    ∀ {l₁ l₂}, List.Forall₂ (fun a b => f a = g b) l₁ l₂ → l₁.map f = l₂.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by simp [h, map_eq t]

/-- The constants `addInductive` inserts. -/
def _root_.Lean.ConstantInfo.InductLike : ConstantInfo → Prop
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => True
  | _ => False

theorem VEnv.addBlock_inducts_self {env env' : VEnv} {d : VInductDecl}
    (h : env.addBlock d = some env') (hnd : (d.types.map (·.name)).Nodup)
    {t : Nat} {T : VInductiveType} (hT : d.types[t]? = some T) :
    env'.inducts T.name = some (d, t) := by
  unfold VEnv.addBlock at h; split at h <;> cases h
  simp only
  have ht := (List.getElem?_eq_some_iff.1 hT)
  rw [show d.types.findIdx? (·.name == T.name) = some t from ?_]
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨ht.1, by simp [ht.2], fun j hj => ?_⟩
  simp only [beq_iff_eq]; intro he
  have := (List.getElem?_inj (i := j) (j := t) (by simp; exact Nat.lt_trans hj ht.1) hnd).1 (by
    simp [List.getElem?_map, List.getElem?_eq_getElem (Nat.lt_trans hj ht.1), he,
      List.getElem?_eq_getElem ht.1, ht.2])
  omega

/-- Induction over a model for the constants `addInductive` inserts: a property each block step
establishes for its new constants, and which survives extension, holds of every such constant
visible at the model's safety level. -/
theorem TrEnv'.inductLike {safety} {P : VEnv → ConstantInfo → Prop}
    (mono : ∀ {v v' ci}, v ≤ v' → P v ci → P v' ci)
    (step : ∀ {Q C venv decl C' venv' n ci}, TrEnv' safety C Q venv → decl.WF venv →
      AddInduct safety C venv decl C' venv' → C.find? n = none → C'.find? n = some ci →
      P venv' ci)
    {C venv} (H : TrEnv' safety C Q venv) {n ci} (h : C.find? n = some ci)
    (hs : safety ≤ ci.safety) (hk : ci.InductLike) : P venv ci := by
  have ins {C : ConstMap} {n n' : Name} {ci' : ConstantInfo} (hC : C.WF) :
      (SMap.insert C n ci').find? n' = some ci →
      C.find? n' = some ci ∨ n = n' ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H generalizing n with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := ins H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := ins H.map_wf h
    · exact mono (VEnv.addConst_le h1) (ih h)
    · cases hk
  | defn _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := ins H.map_wf h
    · exact mono ((VEnv.addConst_le h1).trans VEnv.addDefEq_le) (ih h)
    · cases hk
  | mutualDef _ hnd hfr _ hadd _ H ih =>
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, -, -, rfl⟩
    · exact mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le) (ih h)
    · cases hk
  | thm _ _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := ins H.map_wf h
    · exact mono (VEnv.addConst_le h1) (ih h)
    · cases hk
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := ins H.map_wf h
    · exact mono (VEnv.addConst_le h1) (ih h)
    · cases hk
  | quot _ h1 H ih =>
    have hle := h1.le
    obtain ⟨_, _, _, -, f1, -, _, _, _, -, f2, -, _, _, _, -, f3, -, _, _, _, -, f4, -, rfl, -⟩ := h1
    have w := H.map_wf
    rcases ins (((w.insert _ _ f1).insert _ _ f2).insert _ _ f3) h with h | ⟨-, rfl⟩
    · rcases ins ((w.insert _ _ f1).insert _ _ f2) h with h | ⟨-, rfl⟩
      · rcases ins (w.insert _ _ f1) h with h | ⟨-, rfl⟩
        · rcases ins w h with h | ⟨-, rfl⟩
          · exact mono hle (ih h)
          all_goals cases hk
        all_goals cases hk
      all_goals cases hk
    all_goals cases hk
  | induct hd h1 H ih =>
    have hle := h1.le
    have h1' := h1
    obtain ⟨-, -, -, -, hnd, hfr, ⟨_, hp, rfl⟩, -⟩ := h1
    rcases insertConsts_find?_perm H.map_wf hfr hnd hp h with h' | ⟨hm, rfl⟩
    · exact mono hle (ih h')
    · exact step H hd h1' (hfr _ hm) h

/-- An `AddInduct` step records each type of its block at its own position. -/
theorem AddInduct.inducts {safety C venv decl C' venv'}
    (H : AddInduct safety C venv decl C' venv') {t : Nat} {T : VInductiveType}
    (hT : decl.types[t]? = some T) : venv'.inducts T.name = some (decl, t) := by
  obtain @⟨_, _, _, _, types, _, _, -, hty, -, -, hnd, -, -, -, -, -, hB⟩ := H
  refine VEnv.addBlock_inducts_self hB ?_ hT
  have : (types.map (·.name)) = decl.types.map (·.name) :=
    List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) hty)
  rw [← this]
  simp only [inductConsts, List.map_append, List.map_map, List.nodup_append] at hnd
  exact hnd.1.1

/-- The constant an `AddInduct` step inserts under a fresh name is one of its own. -/
theorem AddInduct.find? {safety C venv decl C' venv'}
    (H : AddInduct safety C venv decl C' venv') {n ci} (hC : C.WF) (hn : C.find? n = none)
    (h : C'.find? n = some ci) :
    ∃ (lparams : List Name), lparams.length = decl.uvars ∧
      ((∃ v T, ci = .inductInfo v ∧ T ∈ decl.types ∧ TrInductVal decl lparams T v) ∨
       (∃ v j c, ci = .ctorInfo v ∧ (j, c) ∈ decl.ctors ∧ TrCtorVal decl lparams j c v) ∨
       (∃ v T i envR, ci = .recInfo v ∧ (T, i) ∈ decl.allTypes.zipIdx ∧ envR ≤ venv' ∧
          TrRecVal decl lparams envR i T v)) := by
  have hle := H.le
  obtain @⟨lparams, _, _, envR, types, ctors, recs, hlp, hty, hct, hrc, hnd, hfr, ⟨_, hp, rfl⟩, hT,
    hC', hR, hB⟩ := H
  rcases insertConsts_find?_perm hC hfr hnd hp h with h | ⟨hm, -⟩
  · cases hn ▸ h
  refine ⟨lparams, hlp, ?_⟩
  simp only [inductConsts, List.mem_append, List.mem_map] at hm
  obtain (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩ := hm
  · obtain ⟨T, hT, h, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hty v hv
    exact .inl ⟨v, T, rfl, hT, h⟩
  · obtain ⟨⟨j, c⟩, hc, h, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hct v hv
    exact .inr (.inl ⟨v, j, c, rfl, hc, h⟩)
  · obtain ⟨⟨T, i⟩, hTi, h, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrc v hv
    refine .inr (.inr ⟨v, T, i, envR, rfl, hTi, ?_, h⟩)
    exact VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB)

/-- A constructor a model can see belongs to the block its model records for its type. -/
theorem TrEnv'.ctorInfo {safety C Q venv} (H : TrEnv' safety C Q venv) {n v}
    (h : C.find? n = some (.ctorInfo v)) (hs : safety ≤ (ConstantInfo.ctorInfo v).safety) :
    ∃ d t c, venv.inducts v.induct = some (d, t) ∧ TrCtorVal d v.levelParams t c v ∧
      v.levelParams.length = d.uvars := by
  refine H.inductLike (P := fun venv ci => ∀ v, ci = .ctorInfo v → ∃ d t c,
      venv.inducts v.induct = some (d, t) ∧ TrCtorVal d v.levelParams t c v ∧
      v.levelParams.length = d.uvars)
    (fun hle H v hv => let ⟨d, t, c, a, b, e⟩ := H v hv; ⟨d, t, c, hle.inducts a, b, e⟩)
    (fun H₀ _ HA hn h v hv => ?_) h hs trivial v rfl
  subst hv
  obtain ⟨lp, hlp, (⟨_, _, ⟨⟩, -⟩ | ⟨v, j, c, ⟨⟩, -, hc⟩ | ⟨_, _, _, _, ⟨⟩, -⟩)⟩ :=
    HA.find? H₀.map_wf hn h
  have hc' := hc
  obtain ⟨T, hT, -, -, hlp', hind, -⟩ := hc
  subst hlp'
  exact ⟨_, j, c, hind ▸ HA.inducts hT, hc', hlp⟩

/-- An inductive type a model can see is recorded with its block. -/
theorem TrEnv'.inductInfo {safety C Q venv} (H : TrEnv' safety C Q venv) {n v}
    (h : C.find? n = some (.inductInfo v)) (hs : safety ≤ (ConstantInfo.inductInfo v).safety) :
    ∃ d t T, venv.inducts v.name = some (d, t) ∧ d.types[t]? = some T ∧
      TrInductVal d v.levelParams T v ∧ v.levelParams.length = d.uvars := by
  refine H.inductLike (P := fun venv ci => ∀ v, ci = .inductInfo v → ∃ d t T,
      venv.inducts v.name = some (d, t) ∧ d.types[t]? = some T ∧
      TrInductVal d v.levelParams T v ∧ v.levelParams.length = d.uvars)
    (fun hle H v hv => let ⟨d, t, T, a, b, e⟩ := H v hv; ⟨d, t, T, hle.inducts a, b, e⟩)
    (fun H₀ _ HA hn h v hv => ?_) h hs trivial v rfl
  subst hv
  obtain ⟨lp, hlp, (⟨v, T, ⟨⟩, hT, hi⟩ | ⟨_, _, _, ⟨⟩, -⟩ | ⟨_, _, _, _, ⟨⟩, -⟩)⟩ :=
    HA.find? H₀.map_wf hn h
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hT
  have hlp' := hi.2.1
  subst hlp'
  exact ⟨_, t, T, hi.1 ▸ HA.inducts ht, ht, hi, hlp⟩

/-- An inductive type a model can see is recorded with its block, and its declared type translates
to the type's, in an environment before the block, where the declared type's literal parameter
binders agree with the block's parameters. -/
theorem TrEnv'.inductInfo_type {safety C Q venv} (H : TrEnv' safety C Q venv) {n v}
    (h : C.find? n = some (.inductInfo v)) (hs : safety ≤ (ConstantInfo.inductInfo v).safety) :
    ∃ d t T venv₀, venv.inducts v.name = some (d, t) ∧ d.types[t]? = some T ∧
      TrInductVal d v.levelParams T v ∧ v.levelParams.length = d.uvars ∧ venv₀ ≤ venv ∧
      TrExprS venv₀ v.levelParams [] v.type T.type ∧
      (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
        ps.length = d.params.length → venv₀.TeleDefEq d.uvars [] ps d.params) := by
  refine H.inductLike (P := fun venv ci => ∀ v, ci = .inductInfo v → ∃ d t T venv₀,
      venv.inducts v.name = some (d, t) ∧ d.types[t]? = some T ∧
      TrInductVal d v.levelParams T v ∧ v.levelParams.length = d.uvars ∧ venv₀ ≤ venv ∧
      TrExprS venv₀ v.levelParams [] v.type T.type ∧
      (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
        ps.length = d.params.length → venv₀.TeleDefEq d.uvars [] ps d.params))
    (fun hle H v hv => let ⟨d, t, T, v₀, a, b, c, e, f, g⟩ := H v hv
      ⟨d, t, T, v₀, hle.inducts a, b, c, e, f.trans hle, g⟩)
    (fun H₀ _ HA hn h v hv => ?_) h hs trivial v rfl
  subst hv
  have hle := HA.le
  have HA' := HA
  obtain @⟨lp, _, _, _, types, ctors, recs, hlp, hty, -, -, hnd, hfr, ⟨_, hp, rfl⟩, -⟩ := HA
  rcases insertConsts_find?_perm H₀.map_wf hfr hnd hp h with h' | ⟨hm, -⟩
  · cases hn ▸ h'
  simp only [inductConsts, List.mem_append, List.mem_map] at hm
  obtain (⟨v', hv, hvv⟩ | ⟨_, _, ⟨⟩⟩) | ⟨_, _, ⟨⟩⟩ := hm
  cases hvv
  obtain ⟨T, hT, hi, htr, hag⟩ := Lean4Lean.List.Forall₂.forall_exists_l hty v hv
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hT
  have hlp' := hi.2.1
  subst hlp'
  exact ⟨_, t, T, _, hi.1 ▸ HA'.inducts ht, ht, hi, hlp, hle, htr.2.2, hag⟩

/-- A constructor a model can see belongs to the block its model records for its type, and its
declared type translates to the constructor's, in an environment before the block's
recursors. -/
theorem TrEnv'.ctorInfo_type {safety C Q venv} (H : TrEnv' safety C Q venv) {n w}
    (h : C.find? n = some (.ctorInfo w)) (hs : safety ≤ (ConstantInfo.ctorInfo w).safety) :
    ∃ d t c venv₀, venv.inducts w.induct = some (d, t) ∧ TrCtorVal d w.levelParams t c w ∧
      (t, c) ∈ d.ctors ∧ w.levelParams.length = d.uvars ∧ venv₀ ≤ venv ∧
      TrExprS venv₀ w.levelParams [] w.type c.type ∧
      CtorDoms venv₀ w.levelParams d.params.length c.fields.length w.type := by
  refine H.inductLike (P := fun venv ci => ∀ w, ci = .ctorInfo w → ∃ d t c venv₀,
      venv.inducts w.induct = some (d, t) ∧ TrCtorVal d w.levelParams t c w ∧
      (t, c) ∈ d.ctors ∧ w.levelParams.length = d.uvars ∧ venv₀ ≤ venv ∧
      TrExprS venv₀ w.levelParams [] w.type c.type ∧
      CtorDoms venv₀ w.levelParams d.params.length c.fields.length w.type)
    (fun hle H w hw => let ⟨d, t, c, v₀, a, b, c', e, f, g, g'⟩ := H w hw
      ⟨d, t, c, v₀, hle.inducts a, b, c', e, f.trans hle, g, g'⟩)
    (fun H₀ _ HA hn h w hw => ?_) h hs trivial w rfl
  subst hw
  have HA' := HA
  obtain @⟨lp, envT, envC, envR, types, ctors, recs, hlp, -, hct, -, hnd, hfr, ⟨_, hp, rfl⟩, -,
    hC, hR, hB⟩ := HA
  rcases insertConsts_find?_perm H₀.map_wf hfr hnd hp h with h' | ⟨hm, -⟩
  · cases hn ▸ h'
  simp only [inductConsts, List.mem_append, List.mem_map] at hm
  obtain (⟨_, _, ⟨⟩⟩ | ⟨w', hw, hww⟩) | ⟨_, _, ⟨⟩⟩ := hm
  cases hww
  obtain ⟨⟨j, c⟩, hc, hi, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_l hct w hw
  have hi' := hi
  obtain ⟨T, hT, -, -, hlp', hind, -⟩ := hi'
  subst hlp'
  have hle : envT ≤ _ := (VEnv.addConstList_le hC).trans <| (VEnv.addConstList_le hR).trans <|
    VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB)
  exact ⟨_, j, c, envT, hind ▸ HA'.inducts hT, hi, hc, hlp, hle, htr.1.2.2, htr.2⟩

/-- A recursor a model can see is recorded with its block, under the block's first type. -/
theorem TrEnv'.recInfo {safety C Q venv} (H : TrEnv' safety C Q venv) {n v}
    (h : C.find? n = some (.recInfo v)) (hs : safety ≤ (ConstantInfo.recInfo v).safety) :
    ∃ d T₀ t T envR, venv.inducts T₀.name = some (d, 0) ∧ d.types[0]? = some T₀ ∧
      d.allTypes[t]? = some T ∧ envR ≤ venv ∧
      TrRecVal d (v.levelParams.drop (v.levelParams.length - d.uvars)) envR t T v ∧
      (v.levelParams.drop (v.levelParams.length - d.uvars)).length = d.uvars := by
  refine H.inductLike (P := fun venv ci => ∀ v, ci = .recInfo v → ∃ d T₀ t T envR,
      venv.inducts T₀.name = some (d, 0) ∧ d.types[0]? = some T₀ ∧
      d.allTypes[t]? = some T ∧ envR ≤ venv ∧
      TrRecVal d (v.levelParams.drop (v.levelParams.length - d.uvars)) envR t T v ∧
      (v.levelParams.drop (v.levelParams.length - d.uvars)).length = d.uvars)
    (fun hle H v hv => by
      obtain ⟨d, T₀, t, T, e, a, a', b, c, f, g⟩ := H v hv
      exact ⟨d, T₀, t, T, e, hle.inducts a, a', b, c.trans hle, f, g⟩)
    (fun {_ _ _ decl _ _ _ _} H₀ hd HA hn h v hv => ?_) h hs trivial v rfl
  subst hv
  obtain ⟨lp, hlp, (⟨_, _, ⟨⟩, -⟩ | ⟨_, _, _, ⟨⟩, -⟩ | ⟨v, T, t, envR, ⟨⟩, hT, hle, hr⟩)⟩ :=
    HA.find? H₀.map_wf hn h
  have ht := List.mem_zipIdx' hT
  have ht' : _ = some T := List.getElem?_eq_some_iff.2 ⟨ht.1, ht.2.symm⟩
  obtain ⟨T₀, h₀⟩ : ∃ T₀, decl.types[0]? = some T₀ := by
    cases e : decl.types with
    | nil => exact (hd.nonempty e).elim
    | cons T₀ _ => exact ⟨T₀, rfl⟩
  have hdrop : v.levelParams.drop (v.levelParams.length - decl.uvars) = lp := by
    by_cases hL : decl.LargeElim
    · obtain ⟨u, -, hu⟩ := hr.2.2.1 hL
      rw [hu, ← hlp]; simp
    · rw [hr.2.2.2.1 hL, ← hlp]; simp
  exact ⟨_, T₀, t, T, envR, HA.inducts h₀, h₀, ht', hle, hdrop ▸ hr, hdrop ▸ hlp⟩

theorem _root_.Lean.SMap.WF.find?_insert_of_some {C : ConstMap} (hC : C.WF) {n x ci ci'}
    (hn : C.find? n = none) (h : C.find? x = some ci) : (C.insert n ci').find? x = some ci := by
  rw [hC.find?_insert, if_neg]; · exact h
  simp only [beq_iff_eq]; rintro rfl; cases hn ▸ h

theorem insertDefs_eq (C : ConstMap) (cis : List DefinitionVal) :
    insertDefs C cis = insertConsts C (cis.map .defnInfo) := by
  simp [insertDefs, insertConsts, List.foldl_map]; rfl

/-- What a model records about a block: the constants `addInductive` inserted for its types and
constructors, as it inserted them. -/
def BlockConsts (C : ConstMap) (d : VInductDecl) : Prop :=
  ∃ lp : List Name, lp.length = d.uvars ∧
    (∀ (j : Nat) (T : VInductiveType), d.types[j]? = some T →
      ∃ v, C.find? T.name = some (.inductInfo v) ∧ TrInductVal d lp T v) ∧
    (∀ (j : Nat) (c : VConstructor), (j, c) ∈ d.ctors →
      ∃ w, C.find? c.name = some (.ctorInfo w) ∧ TrCtorVal d lp j c w)

theorem BlockConsts.mono {C C' : ConstMap} {d}
    (H : ∀ {x ci}, C.find? x = some ci → C'.find? x = some ci) :
    BlockConsts C d → BlockConsts C' d
  | ⟨lp, h1, h2, h3⟩ => ⟨lp, h1, fun j T h => let ⟨v, a, b⟩ := h2 j T h; ⟨v, H a, b⟩,
    fun j c h => let ⟨w, a, b⟩ := h3 j c h; ⟨w, H a, b⟩⟩

/-- Every block a model records was inserted with its constants. -/
theorem TrEnv'.blockConsts {safety C Q venv} (H : TrEnv' safety C Q venv) {n d t}
    (h : venv.inducts n = some (d, t)) : BlockConsts C d := by
  induction H generalizing n with
  | empty => cases h
  | ignore h1 _ H ih => exact (ih h).mono (H.map_wf.find?_insert_of_some h1)
  | «axiom» _ h2 _ h1 H ih =>
    exact (ih (VEnv.addConst_inducts h1 ▸ h)).mono (H.map_wf.find?_insert_of_some h2)
  | defn _ h2 _ h1 H ih =>
    exact (ih (VEnv.addConst_inducts h1 ▸ h)).mono (H.map_wf.find?_insert_of_some h2)
  | thm _ h2 _ _ h1 H ih =>
    exact (ih (VEnv.addConst_inducts h1 ▸ h)).mono (H.map_wf.find?_insert_of_some h2)
  | «opaque» _ h2 _ h1 H ih =>
    exact (ih (VEnv.addConst_inducts h1 ▸ h)).mono (H.map_wf.find?_insert_of_some h2)
  | mutualDef _ hnd hfr _ hadd _ H ih =>
    refine (ih (VEnv.addConsts_inducts hadd ▸ VEnv.addDefEqs_inducts ▸ h)).mono fun hx => ?_
    rw [insertDefs_eq]
    exact insertConsts_find?_of_some H.map_wf
      (fun c hc => by obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc; exact hfr d hd)
      (by rw [List.map_map]; exact hnd) hx
  | quot _ h1 H ih =>
    have hi := VEnv.addQuot_inducts h1.to_addQuot
    obtain ⟨_, _, _, -, f1, -, _, _, _, -, f2, -, _, _, _, -, f3, -, _, _, _, -, f4, -, rfl, -⟩ := h1
    have w := H.map_wf
    refine (ih (hi ▸ h)).mono fun hx => ?_
    exact (((w.insert _ _ f1).insert _ _ f2).insert _ _ f3).find?_insert_of_some f4 <|
      ((w.insert _ _ f1).insert _ _ f2).find?_insert_of_some f3 <|
      (w.insert _ _ f1).find?_insert_of_some f2 <| w.find?_insert_of_some f1 hx
  | induct _ h1 H ih =>
    obtain @⟨lp, envT, envC, envR, types, ctors, recs, hlp, hty, hct, hrc, hnd, hfr, ⟨_, hp, rfl⟩,
      hT, hC, hR, hB⟩ := h1
    have w := H.map_wf
    have hsome {x ci} := @insertConsts_find?_of_some _ _ w (fun c hc => hfr c (hp.mem_iff.1 hc))
      ((hp.map _).nodup_iff.2 hnd) x ci
    rcases VEnv.addBlock_inducts hB h with h | ⟨rfl, -⟩
    · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR, VEnv.addConstList_inducts hC,
        VEnv.addConstList_inducts hT] at h
      exact (ih h).mono hsome
    · refine ⟨lp, hlp, fun j T hj => ?_, fun j c hc => ?_⟩
      · obtain ⟨v, hv, hvT⟩ := Lean4Lean.List.Forall₂.forall_exists_r hty T
          (List.mem_of_getElem? hj)
        refine ⟨v, ?_, hvT.1⟩
        rw [← hvT.1.1, insertConsts_perm_find? w hfr hnd hp]
        exact insertConsts_find?_of_mem w hfr hnd (ci := .inductInfo v) (by simp [inductConsts, hv])
      · obtain ⟨w', hw, hwc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hct (j, c) hc
        refine ⟨w', ?_, hwc.1⟩
        obtain ⟨_, _, _, hname, -⟩ := hwc.1
        rw [← hname, insertConsts_perm_find? w hfr hnd hp]
        exact insertConsts_find?_of_mem w hfr hnd (ci := .ctorInfo w') (by simp [inductConsts, hw])

/-- A model of an environment with quotients has the quotient constants and the computation rule
of `Quot.lift`. -/
theorem TrEnv'.quotReady {safety C venv} (H : TrEnv' safety C true venv) :
    venv.constants ``Quot = some quotConst ∧ venv.constants ``Quot.mk = some quotMkConst ∧
    venv.constants ``Quot.lift = some quotLiftConst ∧
    venv.constants ``Quot.ind = some quotIndConst ∧ venv.defeqs quotDefEq := by
  generalize hQ : true = Q at H
  induction H with
  | empty => cases hQ
  | ignore _ _ _ ih => exact ih hQ
  | «axiom» _ _ _ h1 _ ih | thm _ _ _ _ h1 _ ih | «opaque» _ _ _ h1 _ ih =>
    have le := VEnv.addConst_le h1
    obtain ⟨a, b, c, d, e⟩ := ih hQ
    exact ⟨le.constants a, le.constants b, le.constants c, le.constants d, le.defeqs e⟩
  | @defn _ _ _ _ _ ci' _ _ _ h1 _ ih =>
    have le := (VEnv.addConst_le h1).trans (VEnv.addDefEq_le (df := ci'.toDefEq))
    obtain ⟨a, b, c, d, e⟩ := ih hQ
    exact ⟨le.constants a, le.constants b, le.constants c, le.constants d, le.defeqs e⟩
  | @mutualDef _ _ _ _ _ cis' _ _ _ _ hadd _ _ ih =>
    have le := (VEnv.addConsts_le hadd).trans (VEnv.addDefEqs_le (cis := cis'))
    obtain ⟨a, b, c, d, e⟩ := ih hQ
    exact ⟨le.constants a, le.constants b, le.constants c, le.constants d, le.defeqs e⟩
  | quot _ h1 _ _ =>
    have h := h1.to_addQuot
    exact ⟨VEnv.addQuot_quot h, VEnv.addQuot_quotMk h, VEnv.addQuot_quotLift h,
      VEnv.addQuot_quotInd h, VEnv.addQuot_defeq h⟩
  | induct _ h1 _ ih =>
    have le := h1.le
    obtain ⟨a, b, c, d, e⟩ := ih hQ
    exact ⟨le.constants a, le.constants b, le.constants c, le.constants d, le.defeqs e⟩

end Lean4Lean

import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  | block : Aligned C venv → venv.addBlock d = some venv' → Aligned C venv'

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih | block _ _ ih => exact ih

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih
  | block _ h ih => rw [VEnv.addBlock_constants h]; exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem insertConsts_find?_of_not_mem : ∀ {cis : List ConstantInfo} {C : ConstMap} {name},
    C.WF → (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    name ∉ cis.map (·.name) → (insertConsts C cis).find? name = C.find? name
  | [], _, _, _, _, _, _ => rfl
  | ci :: cis, C, name, hC, hfr, hnd, hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd hn
    show (insertConsts (C.insert ci.name ci) cis).find? name = _
    have hC' := hC.insert ci.name ci (hfr ci (.head _))
    have hne (a b : Name) (h : a ≠ b) : ¬(a == b) = true := by simpa using h
    rw [insertConsts_find?_of_not_mem hC' (fun c hc => ?_) hnd.2 hn.2, hC.find?_insert,
      if_neg (hne _ _ (Ne.symm hn.1))]
    rw [hC.find?_insert, if_neg (hne _ _ fun h => hnd.1 (by rw [h]; exact List.mem_map_of_mem hc))]
    exact hfr c (.tail _ hc)

theorem insertConsts_wf : ∀ {cis : List ConstantInfo} {C : ConstMap}, C.WF →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup → (insertConsts C cis).WF
  | [], _, hC, _, _ => hC
  | ci :: cis, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertConsts_wf (cis := cis) (hC.insert _ _ (hfr _ (.head _))) (fun c hc => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr c (.tail _ hc)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem hc)

theorem insertConsts_find? : ∀ {cis : List ConstantInfo} {C : ConstMap} {name ci}, C.WF →
    (∀ c ∈ cis, C.find? c.name = none) → (cis.map (·.name)).Nodup →
    (insertConsts C cis).find? name = some ci → C.find? name = some ci ∨ ci ∈ cis ∧ ci.name = name
  | [], _, _, _, _, _, _, h => .inl h
  | c :: cs, C, name, ci, hC, hfr, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfr' : ∀ e ∈ cs, (C.insert c.name c).find? e.name = none := by
      intro e he
      rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
      simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem he)
    rcases insertConsts_find? (cis := cs) (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with
      h | h
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h; exact .inr ⟨.head _, by simpa using hb⟩
      · exact .inl h
    · exact .inr ⟨.tail _ h.1, h.2⟩

theorem Aligned.insertConsts {cis : List ConstantInfo} {vcs : List (Name × VConstant)}
    {C venv venv'} (H : Aligned safety C venv) (hnd : (cis.map (·.name)).Nodup)
    (hfr : ∀ ci ∈ cis, C.find? ci.name = none)
    (hblk : List.Forall₂ (fun ci (p : Name × VConstant) =>
      ci.name = p.1 ∧ TrConstant safety venv ci p.2) cis vcs)
    (e : venv.addConstList vcs = some venv') : Aligned safety (insertConsts C cis) venv' := by
  induction cis generalizing vcs C venv with
  | nil => cases hblk; cases e; exact H
  | cons ci cis ih =>
    obtain _ | ⟨⟨hname, htr⟩, hblk⟩ := hblk
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ih (H.const (hfr _ (.head _)) htr (hname ▸ h1) rfl) hnd.2 (fun c hc => ?_)
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.mono (VEnv.addConst_le h1)⟩) hblk) h2
    rw [H.map_wf.find?_insert, if_neg]; · exact hfr c (.tail _ hc)
    simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem hc)

theorem Aligned.addDefEqList : ∀ {dfs : List VDefEq} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqList dfs)
  | [], _, H => H
  | df :: _, venv, H =>
    show Aligned _ _ ((venv.addDefEq df).addDefEqList _) from Aligned.addDefEqList H.defeq

theorem insertConsts_append (C : ConstMap) (as bs : List ConstantInfo) :
    insertConsts C (as ++ bs) = insertConsts (insertConsts C as) bs := List.foldl_append ..

theorem AddInduct.le (H : AddInduct safety C₁ venv₁ decl C₂ venv₂) : venv₁ ≤ venv₂ :=
  VEnv.addInduct_le H.to_addInduct

theorem Aligned.addInduct (H : AddInduct safety C₁ venv₁ decl C₂ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  obtain @⟨_, _, _, _, types, ctors, recs, -, hty, hct, hrc, hnd, hfr, rfl, hT, hC, hR, hB⟩ := H
  refine .block (Aligned.addDefEqList ?_) hB
  have hnd' := hnd
  simp only [inductConsts, List.map_append, List.nodup_append] at hnd'
  obtain ⟨⟨hnd1, hnd2, hd12⟩, hnd3, hd3⟩ := hnd'
  have hC₁ := wf.map_wf
  have hfrA : ∀ ci ∈ types.map ConstantInfo.inductInfo ++ ctors.map ConstantInfo.ctorInfo,
      C₁.find? ci.name = none := fun ci hci => hfr ci (List.mem_append_left _ hci)
  have hfr1 : ∀ ci ∈ types.map ConstantInfo.inductInfo, C₁.find? ci.name = none :=
    fun ci hci => hfrA ci (List.mem_append_left _ hci)
  have hndA : ((types.map ConstantInfo.inductInfo ++ ctors.map ConstantInfo.ctorInfo).map ConstantInfo.name).Nodup := by
    simp only [List.map_append, List.nodup_append]; exact ⟨hnd1, hnd2, hd12⟩
  have w1 := wf.insertConsts hnd1 hfr1 (by
    simp only [VInductDecl.typeConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1.1, h.2⟩) hty) hT
  have w2 := w1.insertConsts hnd2 (fun ci hci => by
    rw [insertConsts_find?_of_not_mem hC₁ hfr1 hnd1 fun h => hd12 _ h _
      (List.mem_map_of_mem hci) rfl]
    exact hfrA ci (List.mem_append_right _ hci)) (by
    simp only [VInductDecl.ctorConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => ⟨h.1.choose_spec.2.2.1, h.2⟩) hct) hC
  have w3 := w2.insertConsts hnd3 (fun ci hci => by
    rw [← insertConsts_append, insertConsts_find?_of_not_mem hC₁ hfrA hndA fun h => hd3 _ (by simpa only [List.map_append] using h) _
      (List.mem_map_of_mem hci) rfl]
    exact hfr ci (List.mem_append_right _ hci)) (by
    simp only [VInductDecl.recConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => ⟨h.1.1, h.2⟩) hrc) hR
  simpa only [inductConsts, insertConsts_append] using w3

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩
  | block _ h2 ih =>
    let ⟨_, a, b⟩ := ih h; exact ⟨_, (VEnv.addBlock_le h2).constants a, b.mono (VEnv.addBlock_le h2)⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩
  | block _ h2 ih =>
    let ⟨a, b⟩ := ih h (by rwa [VEnv.addBlock_constants h2] at hs)
    exact ⟨a, b.mono (VEnv.addBlock_le h2)⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ h1 H ih =>
    have hle := h1.le
    obtain ⟨-, -, -, -, hnd, hfr, rfl, -⟩ := h1
    rcases insertConsts_find? H.map_wf hfr hnd h with h | h
    · exact (ih h).mono hle
    · simp only [inductConsts, List.mem_append, List.mem_map] at h
      obtain ⟨(⟨_, -, rfl⟩ | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩, -⟩ := h <;> cases hv

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

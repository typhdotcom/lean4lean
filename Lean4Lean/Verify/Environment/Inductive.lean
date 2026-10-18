import Lean4Lean.Verify.Environment.AddInductive

/-!
# Adding an inductive block

`addInductive` is verified up to `addInductive.WF_flat`, which says that a run on a block
without nested occurrences takes an `AddInduct` step at the level the block is checked at. Here
that step is carried to every safety level, giving the `VEnvs` an `addDecl` needs.
-/

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ### Carrying the step to other safety levels -/

theorem List.Forall₂.append {R : α → β → Prop} :
    ∀ {l₁ l₂ l₃ l₄}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h t, h' => .cons h (append t h')

theorem TrRecVal.mono {env env' : VEnv} {decl : VInductDecl} {lparams : List Name} {i : Nat}
    {T : VInductiveType} {v : RecursorVal} (henv : env ≤ env')
    (H : TrRecVal decl lparams env i T v) : TrRecVal decl lparams env' i T v := by
  obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := H
  exact ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    Lean4Lean.List.Forall₂.imp (fun _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, d.mono henv⟩) h11⟩

/-- The names `AddInduct` inserts are those `VEnv.addInduct` adds constants under. -/
theorem AddInductN.names {decl : VInductDecl} {nn : Nat} (H : AddInductN nn safety C₁ env₁ decl C₂ env₂) :
    ∃ cis, C₂ = insertConsts C₁ cis ∧ (cis.map (·.name)).Nodup ∧
      (∀ ci ∈ cis, C₁.find? ci.name = none) ∧
      (∀ ci ∈ cis, ci.safety = if decl.isUnsafe then .unsafe else .safe) ∧
      (cis.map (·.name)).Perm ((decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1)) := by
  obtain @⟨_, _, _, _, types, ctors, recs, -, hty, hct, hrc, hnd, hfr, ⟨cis, hp, rfl⟩, -⟩ := H
  refine ⟨cis, rfl, (hp.map _).nodup_iff.2 hnd, fun c hc => hfr c (hp.mem_iff.1 hc), ?_, ?_⟩
  · intro ci hci
    replace hci := hp.mem_iff.1 hci
    simp only [inductConsts, List.mem_append, List.mem_map] at hci
    obtain (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩ := hci
    · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, h⟩, -⟩ := hty.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
    · obtain ⟨_, _, ⟨_, -, -, -, -, -, -, -, h⟩, -⟩ := hct.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
    · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩, -⟩ := hrc.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
  · refine (hp.map _).trans (List.Perm.of_eq ?_)
    refine List.Forall₂.map_eq (f := fun x : ConstantInfo => x.name)
      (g := fun x : Name × VConstant => x.1) ?_
    refine .append (.append ?_ ?_) ?_
    · simp only [VInductDecl.typeConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) hty
    · simp only [VInductDecl.ctorConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => h.1.choose_spec.2.2.1) hct
    · simp only [VInductDecl.recConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => h.1.1) hrc

theorem AddInduct.names {decl : VInductDecl} (H : AddInduct safety C₁ env₁ decl C₂ env₂) :
    ∃ cis, C₂ = insertConsts C₁ cis ∧ (cis.map (·.name)).Nodup ∧
      (∀ ci ∈ cis, C₁.find? ci.name = none) ∧
      (∀ ci ∈ cis, ci.safety = if decl.isUnsafe then .unsafe else .safe) ∧
      (cis.map (·.name)).Perm ((decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1)) :=
  AddInductN.names H

/-- The step at a lower safety level, from a bigger environment that has room for the block. -/
theorem AddInduct.transport {decl : VInductDecl} (H : AddInduct sf C₁ env₁ decl C₂ env₂) (hsf : sf' ≤ sf)
    (hle : env₁ ≤ env₁') (hfr' : ∀ n, C₁.find? n = none → env₁'.constants n = none)
    (hfi' : ∀ n, C₁.find? n = none → env₁'.inducts n = none) :
    ∃ env₂', AddInduct sf' C₁ env₁' decl C₂ env₂' ∧ env₂ ≤ env₂' := by
  obtain ⟨cis, -, hnd, hfr, -, hnames⟩ := H.names
  replace hnd := hnames.nodup_iff.1 hnd
  rw [List.map_append, List.map_append] at hnd
  have hfresh : ∀ n ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1),
      env₁'.constants n = none := by
    intro n hn; replace hn := hnames.mem_iff.2 hn
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    exact hfr' _ (hfr ci hci)
  simp only [List.map_append, List.mem_append] at hfresh
  obtain ⟨⟨hndT, hndC, hdTC⟩, hndR, hdR⟩ := List.nodup_append.1 hnd |>.imp_left List.nodup_append.1
  have hfreshI : ∀ T ∈ decl.types, env₁'.inducts T.name = none := by
    intro T hT
    have : T.name ∈ cis.map (·.name) := by
      refine hnames.mem_iff.2 ?_; simp only [List.map_append, List.mem_append, VInductDecl.typeConsts,
        List.map_map, Function.comp_def]
      exact .inl (.inl (List.mem_map_of_mem hT))
    obtain ⟨ci, hci, hn⟩ := List.mem_map.1 this
    exact hn ▸ hfi' _ (hfr ci hci)
  obtain @⟨lparams, envT, envC, envR, types, ctors, recs, hl, hty, hct, hrc, hnd₀, hfr₀, hm, hT, hC,
    hR, hB⟩ := H
  obtain ⟨_, hT'⟩ := VEnv.exists_addConstList
    (fun p hp => hfresh _ (.inl (.inl (List.mem_map_of_mem hp)))) hndT
  obtain ⟨_, hC'⟩ := VEnv.exists_addConstList (fun p hp => VEnv.addConstList_constants_none hT'
      (hfresh _ (.inl (.inr (List.mem_map_of_mem hp))))
      fun h => hdTC _ h _ (List.mem_map_of_mem hp) rfl) hndC
  obtain ⟨_, hR'⟩ := VEnv.exists_addConstList (fun p hp => by
      have hp' := List.mem_map_of_mem (f := (·.1)) hp
      refine VEnv.addConstList_constants_none hC' (VEnv.addConstList_constants_none hT'
        (hfresh _ (.inr hp')) fun h => hdR _ (List.mem_append_left _ h) _ hp' rfl)
        fun h => hdR _ (List.mem_append_right _ h) _ hp' rfl) hndR
  have leT := VEnv.addConstList_mono hle hT hT'
  have leC := VEnv.addConstList_mono leT hC hC'
  have leR := VEnv.addConstList_mono leC hR hR'
  obtain ⟨_, hB'⟩ := VEnv.exists_addBlock (env := VEnv.addDefEqList _ decl.iotaRules) fun T hT => by
    rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR', VEnv.addConstList_inducts hC',
      VEnv.addConstList_inducts hT']
    exact hfreshI T hT
  refine ⟨_, .mk hl ?_ ?_ ?_ hnd₀ hfr₀ hm hT' hC' hR' hB',
    VEnv.addBlock_mono (VEnv.addDefEqList_mono leR) hB hB'⟩
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, (h.2.1.sf_mono hsf).mono hle,
      fun h1 ps B h2 h3 => (h.2.2 h1 ps B h2 h3).mono hle⟩) hty
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ ⟨_, _⟩ h => ⟨h.1, (h.2.1.sf_mono hsf).mono leT, h.2.2.mono leT⟩) hct
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ ⟨_, _⟩ h => ⟨h.1.mono leR, (h.2.sf_mono hsf).mono leC⟩) hrc

theorem TrEnv'.ignoreConsts : ∀ {cis : List ConstantInfo} {C},
    TrEnv' safety C Q venv → (cis.map (·.name)).Nodup → (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci ∈ cis, ¬safety ≤ ci.safety) → TrEnv' safety (insertConsts C cis) Q venv
  | [], _, H, _, _, _ => H
  | ci :: cis, C, H, hnd, hfr, hs => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine TrEnv'.ignoreConsts (cis := cis) (.ignore (hfr _ (.head _)) (hs _ (.head _)) H) hnd.2
      (fun c hc => ?_) (fun c hc => hs c (.tail _ hc))
    rw [H.map_wf.find?_insert, if_neg]; · exact hfr c (.tail _ hc)
    simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem hc)

theorem VEnv.HasPrimitives.addConstList {env e : VEnv} : ∀ {cs : List (Name × VConstant)},
    (∀ p ∈ cs, Environment.primitives.contains p.1 = false) →
    env.addConstList cs = some e → env.HasPrimitives → e.HasPrimitives
  | [], _, h, H => by cases h; exact H
  | _ :: _, hnp, h, H => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact addConstList (fun p hp => hnp p (.tail _ hp)) h2 (H.addConst (hnp _ (.head _)) h1)

theorem VEnv.HasPrimitives.addDefEqList : ∀ {dfs} {env : VEnv},
    env.HasPrimitives → (env.addDefEqList dfs).HasPrimitives
  | [], _, H => H
  | df :: _, env, H =>
    show ((env.addDefEq df).addDefEqList _).HasPrimitives from addDefEqList H.addDefEq

/-- A block none of whose names is a primitive keeps the primitive invariant. -/
theorem AddInduct.hasPrimitives {decl : VInductDecl}
    (hnp : ∀ n ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1),
      Environment.primitives.contains n = false)
    (H : AddInduct safety C₁ env₁ decl C₂ env₂) (h : env₁.HasPrimitives) : env₂.HasPrimitives := by
  obtain ⟨-, -, -, -, -, -, -, hT, hC, hR, hB⟩ := H
  have hnp' (cs : List (Name × VConstant)) (hcs : ∀ p ∈ cs, p ∈ decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts) :
      ∀ p ∈ cs, Environment.primitives.contains p.1 = false :=
    fun p hp => hnp _ (List.mem_map_of_mem (hcs p hp))
  refine VEnv.HasPrimitives.addBlock hB <| VEnv.HasPrimitives.addDefEqList <|
    .addConstList (hnp' _ fun _ h => List.mem_append_right _ h) hR <|
    .addConstList (hnp' _ fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) hC <|
    .addConstList (hnp' _ fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) hT h

/-- The level an inductive block is checked at, and the safety of every constant it adds. -/
abbrev inductSafety (isUnsafe : Bool) : DefinitionSafety := if isUnsafe then .unsafe else .safe

/-- An `AddInduct` step at the level the block is checked at gives one at every level. -/
theorem addInductBlock.WF [VEnv.Injective] {env env' : Environment} {ves : VEnvs} (wf : ves.WF env)
    {decl : VInductDecl} {venv' : VEnv}
    (hdecl : decl.WF (ves.venv (inductSafety decl.isUnsafe)))
    (H : AddInduct (inductSafety decl.isUnsafe) env.constants
      (ves.venv (inductSafety decl.isUnsafe)) decl env'.constants venv')
    (hq : env'.quotInit = env.quotInit)
    (hprim : ∀ safety venv₁ venv₂,
      AddInduct safety env.constants venv₁ decl env'.constants venv₂ →
      venv₁.HasPrimitives → venv₂.HasPrimitives)
    (hsafePrim : ∀ {n ci}, env'.find? n = some ci → Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hfr' (s) (n) (hn : env.constants.find? n = none) : (ves.venv s).constants n = none :=
    (wf.tr (safety := s)).constants_eq_none
      (by rwa [Kernel.Environment.find?, (wf.tr (safety := s)).map_wf.find?'_eq_find?])
  have hstep (s) : ∃ x, (s ≤ inductSafety decl.isUnsafe →
      AddInduct s env.constants (ves.venv s) decl env'.constants x) ∧
      (¬s ≤ inductSafety decl.isUnsafe → x = ves.venv s) := by
    by_cases hs : s ≤ inductSafety decl.isUnsafe
    · obtain ⟨x, h, -⟩ := H.transport hs (wf.mono hs) (hfr' s) fun n hn => by
        cases h : (ves.venv s).inducts n with
        | none => rfl
        | some b =>
          obtain ⟨_, hc⟩ := (wf.tr (safety := s)).wf.constants_of_inducts h
          cases (hfr' s n hn).symm.trans hc
      exact ⟨x, fun _ => h, fun h => (h hs).elim⟩
    · exact ⟨_, fun h => (hs h).elim, fun _ => rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hstep
  obtain ⟨cis, hC', hnd, hfr, hsafe, -⟩ := H.names
  refine ⟨ves', {
    tr {s} := ?_
    hasPrimitives {s} := ?_
    safePrimitives := hsafePrim
    mono {s s'} hle := ?_ }, fun s => ?_⟩
  · show TrEnv' s env'.constants env'.quotInit _
    rw [hq]
    by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact .induct (hdecl.mono (wf.mono hs)) ((hves' s).1 hs) wf.tr
    · rw [(hves' s).2 hs, hC']
      exact (wf.tr (safety := s)).ignoreConsts hnd hfr fun ci hci h => hs (by rw [hsafe ci hci] at h; exact h)
  · by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact hprim s _ _ ((hves' s).1 hs) wf.hasPrimitives
    · rw [(hves' s).2 hs]; exact wf.hasPrimitives
  · by_cases hs' : s' ≤ inductSafety decl.isUnsafe
    · have hs := DefinitionSafety.le_trans hle hs'
      exact VEnv.addInduct_mono (wf.mono hle) ((hves' s').1 hs').to_addInduct
        ((hves' s).1 hs).to_addInduct
    · rw [(hves' s').2 hs']
      by_cases hs : s ≤ inductSafety decl.isUnsafe
      · exact (wf.mono hle).trans ((hves' s).1 hs).le
      · rw [(hves' s).2 hs]; exact wf.mono hle
  · by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact ((hves' s).1 hs).le
    · rw [(hves' s).2 hs]; exact VEnv.LE.rfl

/-- The block has no nested occurrences: eliminating them adds no auxiliary types. -/
def IsFlat (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) : Prop :=
  ∀ res, (ElimNestedInductive.run fuel.inductiveFuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
    res.aux2nested.size = 0

end Lean4Lean

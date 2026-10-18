import Lean4Lean.Verify.Environment.PrimitiveBlock
import Lean4Lean.Verify.Environment.ElimNested

/-!
# `addInductive` on a block without nested occurrences

The phases of `AddInductive.run`, each verified on its own, assemble into an `AddInduct` step.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem ElimNestedInductive.run_ne_nil {fuel nparams : Nat} {types : List InductiveType}
    {env : Environment} {s} {res : ElimNestedInductive.Result}
    (h : (ElimNestedInductive.run fuel nparams types env).run' s = .ok res) : types ≠ [] := by
  rintro rfl; cases h

/-- `AddInductive.run` on a block without nested occurrences or primitive names. -/
theorem AddInductive.run.WF_nonPrimitive {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams nn : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig) (hne : types ≠ []) :
    (AddInductive.run nparams types nn
      { env, allowPrimitive := false, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env isUnsafe false nn) := by
  let c₀ := AddInductive.VContext.top (wf.toVEnvAt (inductSafety isUnsafe)) lparams false fuel
  change AddInductive.WF c₀ (AddInductive.run nparams types nn) _
  unfold AddInductive.run
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind (AddInductive.WF.liftExcept (checkDuplicatedUnivParams.WF _))
    fun _ hUs => ?_
  have hsafe : (c₀.safety != .safe) = isUnsafe := by cases isUnsafe <;> rfl
  simp only [hsafe]
  have henv₀ := (wf.tr (safety := inductSafety isUnsafe)).wf
  refine AddInductive.checkInductiveTypes.WF rfl henv₀
    hne fun stats c params level typeTr hT => ?_
  refine AddInductive.WF.bind (AddInductive.WF.and AddInductive.declareInductiveTypes.WF
    AddInductive.declareInductiveTypes.ne_dummy)
    fun envTypes ⟨⟨hDc, hDq, hDnd, hDfr, hDp⟩, hDd⟩ => ?_
  have hnames' := AddInductive.inductVals_names (lparams := c.lparams) (numParams := nparams)
    (numNested := nn) (isUnsafe := isUnsafe) hT.nindices
  have hmem {t} (ht : t ∈ types) : ∃ ci ∈ (AddInductive.inductVals c.lparams stats nparams
      types.toArray nn isUnsafe).map ConstantInfo.inductInfo, ci.name = t.name := by
    have : t.name ∈ types.map (·.name) := List.mem_map_of_mem ht
    rw [← hnames'] at this
    obtain ⟨ci, h1, h2⟩ := List.mem_map.1 this
    exact ⟨ci, h1, h2⟩
  refine AddInductive.WF.bind (AddInductive.declareTypeAxioms.WF hT hT.base.safety
    (fun t ht => let ⟨ci, h1, h2⟩ := hmem ht; h2 ▸ hDfr ci h1) (hnames' ▸ hDnd)
    (fun t ht hp => let ⟨ci, h1, h2⟩ := hmem ht; hDp ci h1 (h2 ▸ hp)) hT.base.allowPrimitive)
    fun envAx hAx => ?_
  obtain ⟨hAxe, venvAx, wfAx, hleAx, hAxEq, hconst, hnew⟩ := hAx
  have hAxEq := hAxEq hT.base.allowPrimitive
  refine AddInductive.WF.withEnv wfAx hleAx ?_
  have hle₀ : c₀.venv ≤ venvAx := hT.base.venv ▸ hleAx
  have hB : AddInductive.BlockFresh c₀.venv venvAx types := by
    refine ⟨henv₀, c₀.envAt.hasPrimitives, wfAx.tr.wf, fun t ht => ?_, fun t ht => ?_,
      fun n h1 h0 => ?_, hT.base.venv ▸ VEnv.addConstList_inducts hAxEq⟩
    · obtain ⟨ci, h1, h2⟩ := hmem ht
      have := hDfr ci h1; rw [h2, hT.base.env] at this
      exact c₀.envAt.tr.constants_eq_none
        (by rwa [Kernel.Environment.find?, c₀.envAt.tr.map_wf.find?'_eq_find?])
    · obtain ⟨ci, h1, h2⟩ := hmem ht
      refine Bool.eq_false_iff.2 fun hp => ?_
      have := hDp ci h1 (h2 ▸ hp); rw [hT.base.allowPrimitive] at this; cases this
    · rcases hnew n (hT.base.venv ▸ h0) h1 with hn | ⟨hp, -⟩
      · exact hn
      · cases hT.base.allowPrimitive.symm.trans hp
  refine AddInductive.WF.bind (AddInductive.checkConstructors.WF
    (c := c.withEnv envAx venvAx wfAx hleAx) hT rfl rfl hle₀ hconst hB
    (by show c.lparams.Nodup; rw [hT.base.lparams]; exact hUs))
    fun _ ⟨hC, hCt⟩ => ?_
  have mapWFT : envTypes.constants.WF := by
    rw [hDc]; exact insertConsts_wf c.envAt.tr.map_wf hDfr hDnd
  refine AddInductive.WF.bind (AddInductive.WF.withEnvRaw
    (AddInductive.declareConstructors.WF (c := { (c.withEnv envAx venvAx wfAx hleAx).toContext with
      env := envTypes }) mapWFT)) fun envCtors hDC => ?_
  refine AddInductive.WF.bind (AddInductive.getElimLevel.WF hT
    (c' := c.withEnv envAx venvAx wfAx hleAx) rfl hle₀ wfAx.tr.wf hC)
    fun elimLevel hE => ?_
  refine AddInductive.WF.bind (AddInductive.isKTarget.WF hT (c' := c.withEnv envAx venvAx wfAx hleAx)
    rfl hle₀ wfAx.tr.wf hC) fun kflag hK => ?_
  have hlp : c₀.toContext.lparams = (c.withEnv envAx venvAx wfAx hleAx).lparams :=
    hT.base.lparams.symm
  conv => arg 2; arg 2; intro; arg 2; rw [hlp]
  -- the checking environment: the block's types as axioms, closed
  have hcenv₀ : c.env = env := hT.base.env
  have hfrT (t) (ht : t ∈ types) : c.env.constants.find? t.name = none :=
    let ⟨ci, h1, h2⟩ := hmem ht; h2 ▸ hDfr ci h1
  have hax : AddInductive.typeAxioms c.lparams c.allowPrimitive isUnsafe types =
      types.map (AddInductive.typeAxiom c.lparams isUnsafe) := by
    have hp0 : c.allowPrimitive = false := hT.base.allowPrimitive
    simp [AddInductive.typeAxioms, AddInductive.typeAxiom, hp0, List.map_eq_flatMap]
  have hDax : envAx.constants = insertConsts c.env.constants
      ((types.map (AddInductive.typeAxiom c.lparams isUnsafe)).map .axiomInfo) := by
    rw [hAxe, ← hax, AddInductive.foldl_addAxiom_constants]
  have hfrA : ∀ ci ∈ (types.map (AddInductive.typeAxiom c.lparams isUnsafe)).map ConstantInfo.axiomInfo,
      c.env.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨ax, hax', rfl⟩ := List.mem_map.1 hci
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hax'
    exact hfrT t ht
  have hndA : (((types.map (AddInductive.typeAxiom c.lparams isUnsafe)).map ConstantInfo.axiomInfo).map (·.name)).Nodup := by
    simpa [List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal,
      AddInductive.typeAxiom] using (hnames' ▸ hDnd : (types.map (·.name)).Nodup)
  have hnotDefn : ∀ t ∈ types, ∀ v, envAx.find? t.name ≠ some (.defnInfo v) := by
    intro t ht v hv
    rw [Kernel.Environment.find?, wfAx.tr.map_wf.find?'_eq_find?, hDax] at hv
    rcases insertConsts_find? c.envAt.tr.map_wf hfrA hndA hv with h | ⟨h, -⟩
    · rw [hfrT t ht] at h; cases h
    · obtain ⟨_, -, h⟩ := List.mem_map.1 h; cases h
  have hclosed₀ : ConstMap.Closed c.env.constants := by
    rw [hcenv₀]
    exact TrEnv'.closed (wf.tr (safety := .unsafe)) wf.hasPrimitives
  have hclosed : ConstMap.Closed envAx.constants := by
    rw [hDax]
    refine AddInductive.ConstMap.Closed.insertAxioms _ c.envAt.tr.map_wf hclosed₀
      (fun ax hax' => ?_) (by simpa [List.map_map, Function.comp_def, ConstantInfo.name,
        ConstantInfo.toConstantVal] using hndA) (fun ax hax' => hfrA _ (List.mem_map_of_mem hax'))
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hax'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨T', hT'⟩ : ∃ T', typeTr[j]? = some T' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hT.typeTr_length]; exact (List.getElem?_eq_some_iff.1 hj).1)⟩
    obtain ⟨_, _, htr, -⟩ := hT.types j t T' hj hT'
    have := TrExprS.suppIn_env c₀.envAt.tr c₀.envAt.hasPrimitives htr
    rwa [← hT.base.env, ← hT.base.lparams] at this
  have henvB : ∀ n ci, envAx.find? n = some ci → n ∉ types.map (·.name) →
      ci.SuppIn fun m => m ∉ types.map (·.name) := by
    intro n ci h hn
    rw [Kernel.Environment.find?, wfAx.tr.map_wf.find?'_eq_find?, hDax,
      insertConsts_find?_of_not_mem c.envAt.tr.map_wf hfrA hndA (by
        simpa [List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal,
          AddInductive.typeAxiom] using hn)] at h
    refine (hclosed₀ n ci h).mono fun m hm hmem => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
    rw [hfrT t ht] at hm; cases hm
  refine AddInductive.mkRecInfos.WF (c := c.withEnv envAx venvAx wfAx hleAx) (isUnsafe := isUnsafe)
    hT rfl rfl hle₀ wfAx.tr.wf hT.base.allowPrimitive hT.base.safety hC hCt hconst hB
    (hnames' ▸ hDnd) hnotDefn hclosed
    (by show c.lparams.Nodup; rw [hT.base.lparams]; exact hUs)
    (fun t ht => let ⟨ci, h1, h2⟩ := hmem ht; h2 ▸ hDd ci h1) henvB
    hE.2 fun recInfos c₃ d hR => ?_
  have mapWFC : envCtors.constants.WF := by
    rw [hDC.1]; exact insertConsts_wf mapWFT hDC.2.2.2.1 hDC.2.2.1
  refine AddInductive.WF.mono (AddInductive.declareRecursors.WF hR hR.largeElim
    hE.2 hT.base.safety (hK d hR.compat hR.elaborates) mapWFC) fun env' hRecs => ?_
  obtain ⟨recs, hRc, hRq, hRnd, hRfr, hRp, hRnames, hRtr⟩ := hRecs
  exact AddInductive.assemble wf hne hT hDc hDnd hDfr hDp hleAx wfAx.tr.wf hAxEq (hC d) hDC.1
    hDC.2.2.1 hDC.2.2.2.1 hDC.2.2.2.2 (c₂ := c.withEnv envAx venvAx wfAx hleAx) rfl rfl hR
    (fun h => hE.1 h d hR.compat hR.elaborates) hRc
    (hRq.trans (hDC.2.1.trans (hDq.trans (by rw [hT.base.env]; rfl)))) hRnd hRfr
    (fun ci h hp => hR.allowPrimitive ▸ hRp ci h hp) hRnames (hR.safety ▸ hRtr)

/-- `AddInductive.run` on a block without nested occurrences. -/
theorem AddInductive.run.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) (hne : types ≠ [])
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (AddInductive.run nparams types 0
      { env, allowPrimitive, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env isUnsafe allowPrimitive 0) := by
  cases allowPrimitive with
  | false =>
    exact AddInductive.run.WF_nonPrimitive wf lparams nparams 0 types isUnsafe fuel hne
  | true =>
    exact AddInductive.run.WF_primitive wf lparams nparams types isUnsafe fuel (hallow rfl)

theorem addInductive.WF_flat {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hflat : IsFlat env lparams nparams types fuel)
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF
      (FlatResult ves env isUnsafe allowPrimitive 0) := by
  unfold Environment.addInductive
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  refine Except.WF.bind
    (Q := fun res => res.aux2nested.size = 0 ∧
      ElimNestedInductive.KeepsTypes nparams types res.types ∧ types ≠ [])
    (fun res h => ⟨hflat res h, ElimNestedInductive.run_flat h rfl (hflat res h),
      ElimNestedInductive.run_ne_nil h⟩)
    fun res ⟨h1, ⟨hn, h0⟩, hne⟩ => ?_
  simp only [h1]
  have hne' : res.types ≠ [] := fun h => hne (by simpa [h] using hn.symm)
  have hallow' : allowPrimitive →
      Primitive.PrimitiveInductiveResult lparams nparams res.types isUnsafe := fun hp => by
    have := hallow hp; rwa [h0 this.2.2.1]
  exact (AddInductive.run.WF wf lparams nparams res.types isUnsafe allowPrimitive fuel
    hne' hallow').bind
    fun _ h => .pure h

theorem addInductive.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF
      fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hflat : IsFlat env lparams nparams types fuel
  · refine (addInductive.WF_flat wf lparams nparams types isUnsafe allowPrimitive fuel hflat
      hallow).mono
      fun env' ⟨decl, venv', hu, hdecl, haux, H, hq, hnp, hp⟩ => ?_
    subst hu
    replace H : AddInduct (inductSafety decl.isUnsafe) env.constants
        (ves.venv (inductSafety decl.isUnsafe)) decl env'.constants venv' := by
      unfold AddInduct; rw [haux]; exact H
    cases allowPrimitive with
    | false =>
      have hnp := hnp rfl
      refine addInductBlock.WF wf hdecl H hq (fun _ _ _ H' => H'.hasPrimitives hnp)
        fun {n ci} h hn => ?_
      obtain ⟨cis, hC', hnd, hfr, -, hnames⟩ := H.names
      have hC₁ := (wf.tr (safety := .safe)).map_wf
      rw [Kernel.Environment.find?, hC', (insertConsts_wf hC₁ hfr hnd).find?'_eq_find?] at h
      rcases insertConsts_find? hC₁ hfr hnd h with h | h
      · exact wf.safePrimitives (by rwa [Kernel.Environment.find?, hC₁.find?'_eq_find?]) hn
      · have := hnp n (hnames.mem_iff.1 (h.2 ▸ List.mem_map_of_mem h.1))
        simp_all
    | true =>
      have ⟨hprim, hsafe⟩ := hp rfl
      exact addInductBlock.WF wf hdecl H hq hprim hsafe
  · -- A nested block: its auxiliary types are checked as a flat block and the result translated
    -- back to the block `VEnv.addInduct` models with `aux`. Not yet verified.
    sorry

end Lean4Lean

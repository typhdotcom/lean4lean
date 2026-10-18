import Lean4Lean.Verify.Environment.Constructors

/-!
# `addInductive` on a block without nested occurrences

The phases of `AddInductive.run`, each verified on its own, assemble into an `AddInduct` step.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- What `addInductive` establishes for a block without nested occurrences: an `AddInduct` step
at the level the block is checked at, for a well-formed `decl`. A primitive block keeps the
primitive invariant at every level; any other block adds no primitive name. -/
def FlatResult (ves : VEnvs) (env : Environment) (isUnsafe allowPrimitive : Bool)
    (env' : Environment) : Prop :=
  ∃ (decl : VInductDecl) (venv' : VEnv), decl.isUnsafe = isUnsafe ∧
    decl.WF (ves.venv (inductSafety isUnsafe)) ∧
    AddInduct (inductSafety isUnsafe) env.constants (ves.venv (inductSafety isUnsafe)) decl
      env'.constants venv' ∧
    env'.quotInit = env.quotInit ∧
    (allowPrimitive = false →
      ∀ n ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1),
        Environment.primitives.contains n = false) ∧
    (allowPrimitive = true →
      (∀ safety venv₁ venv₂,
        AddInduct safety env.constants venv₁ decl env'.constants venv₂ →
        venv₁.HasPrimitives → venv₂.HasPrimitives) ∧
      ∀ {n ci}, env'.find? n = some ci → Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = [])

/-- Eliminating nested occurrences from a block that has none returns its types unchanged: each
constructor type is opened at its parameters and closed again. -/
theorem ElimNestedInductive.run_flat {fuel nparams : Nat} {types : List InductiveType}
    {env : Environment} {lparams : List Name} {res : ElimNestedInductive.Result}
    (h : (ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res)
    (hflat : res.aux2nested.size = 0) : res.types = types :=
  sorry

/-- Everything `run` established about a block without nested occurrences or primitive names
gives `FlatResult`: the elaborated `d` is well formed, and the constants `run` added are an
`AddInduct` step. -/
theorem AddInductive.assemble {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType}
    {isUnsafe : Bool} {fuel : FuelConfig} (hne : types ≠ [])
    {stats : InductiveStats} {c : AddInductive.VContext} {params : List VExpr} {level : VLevel}
    {typeTr : List VExpr}
    (hT : AddInductive.TypesData (AddInductive.VContext.top (wf.toVEnvAt (inductSafety isUnsafe))
      lparams false fuel) nparams types stats c params level typeTr)
    {envTypes : Environment}
    (hDc : envTypes.constants = insertConsts c.env.constants
      ((AddInductive.inductVals c.lparams stats nparams types.toArray 0 isUnsafe).map .inductInfo))
    (hDnd : (((AddInductive.inductVals c.lparams stats nparams types.toArray 0 isUnsafe).map
      ConstantInfo.inductInfo).map (·.name)).Nodup)
    (hDfr : ∀ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray 0 isUnsafe).map
      ConstantInfo.inductInfo, c.env.constants.find? ci.name = none)
    (hDp : ∀ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray 0 isUnsafe).map
      ConstantInfo.inductInfo, Environment.primitives.contains ci.name → c.allowPrimitive)
    {venvAx : VEnv} (hleAx : c.venv ≤ venvAx) (henvAx : venvAx.WF)
    (hAx : c.venv.addConstList (AddInductive.typeConstsOf c.lparams.length types typeTr) =
      some venvAx)
    {d : VInductDecl}
    (hC : AddInductive.Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → AddInductive.CtorChecked venvAx c.lparams d t nidx ct)
    {envCtors : Environment}
    (hDCc : envCtors.constants = insertConsts envTypes.constants
      ((AddInductive.ctorVals c.lparams stats.params.size types isUnsafe).map .ctorInfo))
    (hDCnd : (((AddInductive.ctorVals c.lparams stats.params.size types isUnsafe).map
      ConstantInfo.ctorInfo).map (·.name)).Nodup)
    (hDCfr : ∀ ci ∈ (AddInductive.ctorVals c.lparams stats.params.size types isUnsafe).map
      ConstantInfo.ctorInfo, envTypes.constants.find? ci.name = none)
    (hDCp : ∀ ci ∈ (AddInductive.ctorVals c.lparams stats.params.size types isUnsafe).map
      ConstantInfo.ctorInfo, Environment.primitives.contains ci.name → c.allowPrimitive)
    {elimLevel : Level} {recInfos : Array RecInfo} {c₃ : AddInductive.VContext}
    {c₂ : AddInductive.VContext} (hc₂ : c₂.venv = venvAx) (hc₂U : c₂.lparams = c.lparams)
    (hR : AddInductive.RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel
      recInfos c₃ d)
    (hLE : elimLevel ≠ .zero → d.LargeElimOK)
    {env' : Environment} {recs : List RecursorVal}
    (hRc : env'.constants = insertConsts envCtors.constants (recs.map .recInfo))
    (hRq : env'.quotInit = env.quotInit)
    (hRnd : ((recs.map ConstantInfo.recInfo).map (·.name)).Nodup)
    (hRfr : ∀ ci ∈ recs.map ConstantInfo.recInfo, envCtors.constants.find? ci.name = none)
    (hRp : ∀ ci ∈ recs.map ConstantInfo.recInfo,
      Environment.primitives.contains ci.name → c.allowPrimitive)
    (hRnames : List.Forall₂ (fun v (p : VInductiveType × Nat) => v.name = Lean.mkRecName p.1.name)
      recs d.types.zipIdx)
    (hRtr : ∀ (envC envR : VEnv), venvAx ≤ envC → envC.WF →
      (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
      envC.addConstList d.recConsts = some envR → envR.WF →
      List.Forall₂ (fun v (p : VInductiveType × Nat) =>
        TrRecVal d c.lparams envR p.2 p.1 v ∧
        TrConstant c.safety envC (.recInfo v)
          ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩)
        recs d.types.zipIdx) :
    FlatResult ves env isUnsafe false env' := by
  have hb := hT.base
  have hcenv : c.env = env := hb.env
  have hcvenv : c.venv = ves.venv (inductSafety isUnsafe) := hb.venv
  have hcs : c.safety = inductSafety isUnsafe := hb.safety
  have hcp : c.allowPrimitive = false := hb.allowPrimitive
  have mapWF : c.env.constants.WF := c.envAt.tr.map_wf
  have hdecl := AddInductive.decl_WF hT hne hAx henvAx hC hc₂ hc₂U hR hLE
  have hEl : AddInductive.Elaborates venvAx c.lparams nparams level types d :=
    hc₂ ▸ hc₂U ▸ hR.elaborates
  have hU : d.uvars = c.lparams.length := hR.uvars.trans (by rw [hc₂U])
  have hAxd : c.venv.addConstList d.typeConsts = some venvAx := by
    rw [VInductDecl.typeConsts, hU,
      AddInductive.typeConsts_eq (X := fun _ _ => _) hEl.types hR.typeTr]
    exact hAx
  have htv := AddInductive.inductVals_tr hT rfl hc₂U hR
  have hcv := AddInductive.ctorVals_tr hT hcs henvAx hleAx hC hc₂ hc₂U hR
  generalize AddInductive.inductVals c.lparams stats nparams types.toArray 0 isUnsafe = tv
    at htv hDc hDnd hDfr hDp
  generalize AddInductive.ctorVals c.lparams stats.params.size types isUnsafe = cv
    at hcv hDCc hDCnd hDCfr hDCp
  have htvn : (tv.map ConstantInfo.inductInfo).map (·.name) = d.typeConsts.map (·.1) := by
    simp only [VInductDecl.typeConsts, List.map_map]
    exact List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) htv)
  have hcvn : (cv.map ConstantInfo.ctorInfo).map (·.name) = d.ctorConsts.map (·.1) := by
    simp only [VInductDecl.ctorConsts, List.map_map]
    exact List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp
      (fun _ ⟨_, _⟩ h => h.1.choose_spec.2.2.1) hcv)
  have hrn : (recs.map ConstantInfo.recInfo).map (·.name) = d.recConsts.map (·.1) := by
    simp only [VInductDecl.recConsts, List.map_map]
    exact List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => h) hRnames)
  have mapWFT : envTypes.constants.WF := by rw [hDc]; exact insertConsts_wf mapWF hDfr hDnd
  -- freshness of each group, in the constant maps and in the models
  have hfrC (ci) (hci : ci ∈ cv.map ConstantInfo.ctorInfo) :
      c.env.constants.find? ci.name = none ∧ ci.name ∉ d.typeConsts.map (·.1) := by
    have := insertConsts_find?_none mapWF hDfr hDnd (hDc ▸ hDCfr ci hci)
    exact ⟨this.1, htvn ▸ this.2⟩
  have hfrR (ci) (hci : ci ∈ recs.map ConstantInfo.recInfo) :
      c.env.constants.find? ci.name = none ∧ ci.name ∉ d.typeConsts.map (·.1) ∧
        ci.name ∉ d.ctorConsts.map (·.1) := by
    have h1 := insertConsts_find?_none mapWFT hDCfr hDCnd (hDCc ▸ hRfr ci hci)
    have h2 := insertConsts_find?_none mapWF hDfr hDnd (hDc ▸ h1.1)
    exact ⟨h2.1, htvn ▸ h2.2, hcvn ▸ h1.2⟩
  have hvfr (n) (hn : c.env.constants.find? n = none) : c.venv.constants n = none :=
    c.envAt.tr.constants_eq_none (by rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?])
  have hndC : (d.ctorConsts.map (·.1)).Nodup := hcvn ▸ hDCnd
  have hndR : (d.recConsts.map (·.1)).Nodup := hrn ▸ hRnd
  have hmemC (p) (hp : p ∈ d.ctorConsts) : ∃ ci ∈ cv.map ConstantInfo.ctorInfo, ci.name = p.1 :=
    List.mem_map.1 (hcvn ▸ List.mem_map_of_mem hp)
  have hmemR (p) (hp : p ∈ d.recConsts) : ∃ ci ∈ recs.map ConstantInfo.recInfo, ci.name = p.1 :=
    List.mem_map.1 (hrn ▸ List.mem_map_of_mem hp)
  obtain ⟨envC, hCadd⟩ := VEnv.exists_addConstList (env := venvAx) (cs := d.ctorConsts)
    (fun p hp => by
      obtain ⟨ci, hci, e⟩ := hmemC p hp
      have := hfrC ci hci; rw [← e]
      exact VEnv.addConstList_constants_none hAxd (hvfr _ this.1) this.2) hndC
  obtain ⟨envR, hRadd⟩ := VEnv.exists_addConstList (env := envC) (cs := d.recConsts)
    (fun p hp => by
      obtain ⟨ci, hci, e⟩ := hmemR p hp
      have := hfrR ci hci; rw [← e]
      exact VEnv.addConstList_constants_none hCadd
        (VEnv.addConstList_constants_none hAxd (hvfr _ this.1) this.2.1) this.2.2) hndR
  have henvC : envC.WF := VEnv.WF.addConstList henvAx (fun p hp => by
    obtain ⟨⟨j, c'⟩, hc', rfl⟩ := List.mem_map.1 hp
    obtain ⟨T, hT', hcT⟩ := VInductDecl.mem_ctors hc'
    exact ((hdecl.ctors _ hAxd T hT').2 c' hcT).type) hCadd
  have henvR : envR.WF := VEnv.WF.addConstList henvC
    (VInductDecl.recConsts_WF c.envAt.tr.wf.ordered hdecl hAxd hCadd) hRadd
  have hrecs := hRtr envC envR (VEnv.addConstList_le hCadd) henvC
    (fun p hp => VEnv.addConstList_constants_of_mem hCadd hp) hRadd henvR
  have hnames : (inductConsts tv cv recs).map (·.name) =
      (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    simp only [inductConsts, List.map_append, htvn, hcvn, hrn]
  have hfr (ci) (hci : ci ∈ inductConsts tv cv recs) : env.constants.find? ci.name = none := by
    rw [← hcenv]
    simp only [inductConsts, List.mem_append] at hci
    rcases hci with (h | h) | h
    · exact hDfr ci h
    · exact (hfrC ci h).1
    · exact (hfrR ci h).1
  have hnd : ((inductConsts tv cv recs).map (·.name)).Nodup := by
    simp only [inductConsts, List.map_append]
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hDnd, hDCnd, ?_⟩, hRnd, ?_⟩
    · intro a ha b hb e; subst e
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hb
      exact (hfrC ci hci).2 (htvn ▸ ha)
    · intro a ha b hb e; subst e
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hb
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact (hfrR ci hci).2.1 (htvn ▸ ha)
      · exact (hfrR ci hci).2.2 (hcvn ▸ ha)
  have hstep : AddInduct (inductSafety isUnsafe) env.constants (ves.venv (inductSafety isUnsafe)) d
      env'.constants ((envR.addDefEqList d.iotaRules).addDefEqList d.etaRules) := by
    refine .mk (lparams := c.lparams) hU.symm htv (hcs ▸ hcv) (hcs ▸ hrecs) hnd hfr ?_
      (hcvenv ▸ hAxd) hCadd hRadd rfl
    rw [hRc, hDCc, hDc, hcenv, inductConsts, insertConsts_append, insertConsts_append]
  refine ⟨d, _, hR.isUnsafe, hcvenv ▸ hdecl, hstep, hRq, fun _ n hn => ?_, nofun⟩
  rw [← hnames] at hn
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
  refine Bool.eq_false_iff.2 fun h => ?_
  simp only [inductConsts, List.mem_append] at hci
  have : c.allowPrimitive = true := by
    rcases hci with (hci | hci) | hci
    exacts [hDp ci hci h, hDCp ci hci h, hRp ci hci h]
  rw [hcp] at this; cases this

theorem ElimNestedInductive.run_ne_nil {fuel nparams : Nat} {types : List InductiveType}
    {env : Environment} {s} {res : ElimNestedInductive.Result}
    (h : (ElimNestedInductive.run fuel nparams types env).run' s = .ok res) : types ≠ [] := by
  rintro rfl; cases h

theorem checkDuplicatedUnivParams.WF : ∀ (ls : List Name),
    (Environment.checkDuplicatedUnivParams ls).WF fun _ => ls.Nodup
  | [] => fun _ _ => .nil
  | p :: ls => by
    unfold Environment.checkDuplicatedUnivParams
    split
    · exact fun _ h => nomatch h
    · rename_i hp
      exact fun a h => .cons (fun q hq e => hp (e ▸ hq)) (checkDuplicatedUnivParams.WF ls a h)

/-- `AddInductive.run` on a block without nested occurrences or primitive names. -/
theorem AddInductive.run.WF_nonPrimitive {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hann : (ves.venv (inductSafety isUnsafe)).AnnotationsDefine)
    (hnames : ∀ t ∈ types, t.name ∉ typeAnnotations.map (·.1)) (hne : types ≠ []) :
    (AddInductive.run nparams types 0
      { env, allowPrimitive := false, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env isUnsafe false) := by
  let c₀ := AddInductive.VContext.top (wf.toVEnvAt (inductSafety isUnsafe)) lparams false fuel
  change AddInductive.WF c₀ (AddInductive.run nparams types 0) _
  unfold AddInductive.run
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind (AddInductive.WF.liftExcept (checkDuplicatedUnivParams.WF _))
    fun _ hUs => ?_
  have hsafe : (c₀.safety != .safe) = isUnsafe := by cases isUnsafe <;> rfl
  simp only [hsafe]
  have henv₀ := (wf.tr (safety := inductSafety isUnsafe)).wf
  refine AddInductive.checkInductiveTypes.WF rfl henv₀ (hann.erase henv₀)
    hne fun stats c params level typeTr hT => ?_
  refine AddInductive.WF.bind AddInductive.declareInductiveTypes.WF
    fun envTypes ⟨hDc, hDq, hDnd, hDfr, hDp⟩ => ?_
  have hnames' := AddInductive.inductVals_names (lparams := c.lparams) (numParams := nparams)
    (numNested := 0) (isUnsafe := isUnsafe) hT.nindices
  have hmem {t} (ht : t ∈ types) : ∃ ci ∈ (AddInductive.inductVals c.lparams stats nparams
      types.toArray 0 isUnsafe).map ConstantInfo.inductInfo, ci.name = t.name := by
    have : t.name ∈ types.map (·.name) := List.mem_map_of_mem ht
    rw [← hnames'] at this
    obtain ⟨ci, h1, h2⟩ := List.mem_map.1 this
    exact ⟨ci, h1, h2⟩
  refine AddInductive.WF.bind (AddInductive.declareTypeAxioms.WF hT hT.base.safety
    (fun t ht => let ⟨ci, h1, h2⟩ := hmem ht; h2 ▸ hDfr ci h1) (hnames' ▸ hDnd)
    (fun t ht hp => let ⟨ci, h1, h2⟩ := hmem ht; hDp ci h1 (h2 ▸ hp)) hT.base.allowPrimitive)
    fun envAx hAx => ?_
  obtain ⟨_, venvAx, wfAx, hleAx, hAxEq, hconst, hnew⟩ := hAx
  have hAxEq := hAxEq hT.base.allowPrimitive
  refine AddInductive.WF.withEnv wfAx hleAx ?_
  have hle₀ : c₀.venv ≤ venvAx := hT.base.venv ▸ hleAx
  have hannAx : venvAx.AnnotationsDefine := by
    refine hann.mono hle₀ fun n k i hmemA h0 => ?_
    refine Decidable.byContradiction fun h1 => ?_
    rcases hnew n (hT.base.venv ▸ h0) h1 with hn | ⟨hp, t, ht, hn⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
      exact hnames t ht (List.mem_map.2 ⟨_, hmemA, rfl⟩)
    · cases hT.base.allowPrimitive.symm.trans hp
  have hB : AddInductive.BlockFresh c₀.venv venvAx types := by
    refine ⟨henv₀, c₀.envAt.hasPrimitives, wfAx.tr.wf, fun t ht => ?_, fun t ht => ?_,
      fun n h1 h0 => ?_⟩
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
    (hannAx.erase wfAx.tr.wf) (by show c.lparams.Nodup; rw [hT.base.lparams]; exact hUs))
    fun _ hC => ?_
  have mapWFT : envTypes.constants.WF := by
    rw [hDc]; exact insertConsts_wf c.envAt.tr.map_wf hDfr hDnd
  refine AddInductive.WF.bind (AddInductive.WF.withEnvRaw
    (AddInductive.declareConstructors.WF (c := { (c.withEnv envAx venvAx wfAx hleAx).toContext with
      env := envTypes }) mapWFT)) fun envCtors hDC => ?_
  refine AddInductive.WF.bind (AddInductive.getElimLevel.WF hT
    (c' := c.withEnv envAx venvAx wfAx hleAx) rfl hle₀ wfAx.tr.wf (hannAx.erase wfAx.tr.wf) hC)
    fun elimLevel hE => ?_
  refine AddInductive.WF.bind (AddInductive.isKTarget.WF hT (c' := c.withEnv envAx venvAx wfAx hleAx)
    rfl hle₀ wfAx.tr.wf hC) fun kflag hK => ?_
  refine AddInductive.mkRecInfos.WF (c := c.withEnv envAx venvAx wfAx hleAx) (isUnsafe := isUnsafe)
    hT rfl rfl hle₀
    wfAx.tr.wf (hannAx.erase wfAx.tr.wf) fun recInfos c₃ d hR => ?_
  have mapWFC : envCtors.constants.WF := by
    rw [hDC.1]; exact insertConsts_wf mapWFT hDC.2.2.2.1 hDC.2.2.1
  refine AddInductive.WF.mono (AddInductive.declareRecursors.WF hR hR.largeElim
    hE.2 (hK d hR.compat hR.elaborates) mapWFC) fun env' hRecs => ?_
  obtain ⟨recs, hRc, hRq, hRnd, hRfr, hRp, hRnames, hRtr⟩ := hRecs
  exact AddInductive.assemble wf hne hT hDc hDnd hDfr hDp hleAx wfAx.tr.wf hAxEq (hC d) hDC.1
    hDC.2.2.1 hDC.2.2.2.1 hDC.2.2.2.2 (c₂ := c.withEnv envAx venvAx wfAx hleAx) rfl rfl hR
    (fun h => hE.1 h d hR.compat hR.elaborates) hRc
    (hRq.trans (hDC.2.1.trans (hDq.trans (by rw [hT.base.env]; rfl)))) hRnd hRfr
    (fun ci h hp => hR.allowPrimitive ▸ hRp ci h hp) hRnames (hR.safety ▸ hRtr)

/-- `AddInductive.run` on a primitive block, `Bool` or `Nat` as the prelude declares them. The block
is checked with its constructors as axioms too, so `checkConstructors` establishes what it does in
an environment that already has them, while `AddInduct` asks for the constructors' types in the
one with only the types. What closes the gap is that these types mention only the block's type,
which for `Bool` and `Nat` is a computation; the primitive clauses of `FlatResult` are what
`PrimitiveInductiveResult` supplies. -/
theorem AddInductive.run.WF_primitive {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hann : (ves.venv (inductSafety isUnsafe)).AnnotationsDefine)
    (hnames : ∀ t ∈ types, t.name ∉ typeAnnotations.map (·.1))
    (hallow : Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (AddInductive.run nparams types 0
      { env, allowPrimitive := true, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env isUnsafe true) :=
  sorry

/-- `AddInductive.run` on a block without nested occurrences. -/
theorem AddInductive.run.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hann : (ves.venv (inductSafety isUnsafe)).AnnotationsDefine)
    (hnames : ∀ t ∈ types, t.name ∉ typeAnnotations.map (·.1)) (hne : types ≠ [])
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (AddInductive.run nparams types 0
      { env, allowPrimitive, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env isUnsafe allowPrimitive) := by
  cases allowPrimitive with
  | false =>
    exact AddInductive.run.WF_nonPrimitive wf lparams nparams types isUnsafe fuel hann hnames hne
  | true =>
    exact AddInductive.run.WF_primitive wf lparams nparams types isUnsafe fuel hann hnames
      (hallow rfl)

theorem addInductive.WF_flat {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hflat : IsFlat env lparams nparams types fuel)
    (hann : (ves.venv (inductSafety isUnsafe)).AnnotationsDefine)
    (hnames : ∀ t ∈ types, t.name ∉ typeAnnotations.map (·.1))
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF
      (FlatResult ves env isUnsafe allowPrimitive) := by
  unfold Environment.addInductive
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  refine Except.WF.bind
    (Q := fun res => res.aux2nested.size = 0 ∧ res.types = types ∧ types ≠ [])
    (fun res h => ⟨hflat res h, ElimNestedInductive.run_flat h (hflat res h),
      ElimNestedInductive.run_ne_nil h⟩)
    fun res ⟨h1, h2, hne⟩ => ?_
  simp only [h1, h2]
  exact (AddInductive.run.WF wf lparams nparams types isUnsafe allowPrimitive fuel hann hnames hne
    hallow).bind
    fun _ h => .pure h

theorem addInductive.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hann : ∀ safety, (ves.venv safety).AnnotationsDefine)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (hnames : ∀ t ∈ types, t.name ∉ typeAnnotations.map (·.1))
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF
      fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  by_cases hflat : IsFlat env lparams nparams types fuel
  · refine (addInductive.WF_flat wf lparams nparams types isUnsafe allowPrimitive fuel hflat
      (hann _) hnames hallow).mono
      fun env' ⟨decl, venv', hu, hdecl, H, hq, hnp, hp⟩ => ?_
    subst hu
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
      · have := hnp n (hnames ▸ h.2 ▸ List.mem_map_of_mem h.1)
        simp_all
    | true =>
      have ⟨hprim, hsafe⟩ := hp rfl
      exact addInductBlock.WF wf hdecl H hq hprim hsafe
  · -- `AddInduct` models blocks without nested occurrences only, so for a nested block there is
    -- nothing to show that its result is in `TrEnv`: as stated, this case is not provable until
    -- `VEnv.addInduct` covers nested inductives.
    sorry

end Lean4Lean

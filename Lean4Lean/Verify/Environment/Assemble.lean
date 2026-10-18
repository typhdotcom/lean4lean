import Lean4Lean.Verify.Environment.Recursors

/-!
# Assembling an `AddInduct` step

What the phases of `AddInductive.run` established about a block without nested occurrences
assembles into an `AddInduct` step for its elaborated declaration.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- What `addInductive` establishes for a block without nested occurrences: an `AddInduct` step
at the level the block is checked at, for a well-formed `decl`. A primitive block keeps the
primitive invariant at every level; any other block adds no primitive name. -/
def FlatResult (ves : VEnvs) (env : Environment) (isUnsafe allowPrimitive : Bool) (nn : Nat)
    (env' : Environment) : Prop :=
  ∃ (decl : VInductDecl) (venv' : VEnv), decl.isUnsafe = isUnsafe ∧
    decl.WF (ves.venv (inductSafety isUnsafe)) ∧ decl.aux = [] ∧
    AddInductN nn (inductSafety isUnsafe) env.constants (ves.venv (inductSafety isUnsafe)) decl
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
        ci.safety = .safe ∧ ci.levelParams = []) ∧
    ∀ T ∈ decl.types, ∀ c ∈ T.ctors, ∀ (ps Ds : List VExpr) (B : VExpr),
      c.type = .foralls (ps ++ Ds) B → ps.length = decl.params.length →
      ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      D.StripsTo f.type

/-- Everything `run` established about a block without nested occurrences: the elaborated `d` is
well formed, and the constants `run` added are an `AddInduct` step. `d` elaborates the block
in `venvAx`, the checking environment with the types only. -/
theorem AddInductive.assemble_step {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams nn : Nat} {types : List InductiveType}
    {isUnsafe ap : Bool} {fuel : FuelConfig} (hne : types ≠ [])
    {stats : InductiveStats} {c : AddInductive.VContext} {params : List VExpr} {level : VLevel}
    {typeTr : List VExpr}
    (hT : AddInductive.TypesData (AddInductive.VContext.top (wf.toVEnvAt (inductSafety isUnsafe))
      lparams ap fuel) nparams types stats c params level typeTr)
    {envTypes : Environment}
    (hDc : envTypes.constants = insertConsts c.env.constants
      ((AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map .inductInfo))
    (hDnd : (((AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
      ConstantInfo.inductInfo).map (·.name)).Nodup)
    (hDfr : ∀ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
      ConstantInfo.inductInfo, c.env.constants.find? ci.name = none)
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
    {elimLevel : Level} {recInfos : Array RecInfo} {c₃ : AddInductive.VContext}
    {c₂ : AddInductive.VContext} (hc₂U : c₂.lparams = c.lparams)
    (hR : AddInductive.RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel
      recInfos c₃ d)
    (hEl : AddInductive.Elaborates venvAx c.lparams nparams level types d)
    (hInd : ∀ T ∈ d.types, T.WF venvAx d)
    (hLE : elimLevel ≠ .zero → d.LargeElimOK)
    {env' : Environment} {recs : List RecursorVal}
    (hRc : env'.constants = insertConsts envCtors.constants (recs.map .recInfo))
    (hRnd : ((recs.map ConstantInfo.recInfo).map (·.name)).Nodup)
    (hRfr : ∀ ci ∈ recs.map ConstantInfo.recInfo, envCtors.constants.find? ci.name = none)
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
    d.WF (ves.venv (inductSafety isUnsafe)) ∧
    (∃ env₂, AddInductN nn (inductSafety isUnsafe) env.constants
      (ves.venv (inductSafety isUnsafe)) d env'.constants env₂) ∧
    ∀ n ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1),
      ∃ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
          ConstantInfo.inductInfo ++
        (AddInductive.ctorVals c.lparams stats.params.size types isUnsafe).map
          ConstantInfo.ctorInfo ++ recs.map ConstantInfo.recInfo, ci.name = n := by
  have hb := hT.base
  have hcenv : c.env = env := hb.env
  have hcvenv : c.venv = ves.venv (inductSafety isUnsafe) := hb.venv
  have hcs : c.safety = inductSafety isUnsafe := hb.safety
  have mapWF : c.env.constants.WF := c.envAt.tr.map_wf
  have hdecl := AddInductive.decl_WF hT hne hAx henvAx hC hc₂U hR hEl hInd hLE
  have hU : d.uvars = c.lparams.length := hR.uvars.trans (by rw [hc₂U])
  have hall : d.allTypes = d.types := VInductDecl.allTypes_of_aux hR.aux
  have hAxd : c.venv.addConstList d.typeConsts = some venvAx := by
    rw [VInductDecl.typeConsts, hU,
      AddInductive.typeConsts_eq (X := fun _ _ => _) hEl.types hR.typeTr]
    exact hAx
  have htv := AddInductive.inductVals_tr (nn := nn) hT rfl hc₂U hR
  have hcv := AddInductive.ctorVals_tr hT hcs henvAx hleAx hC hc₂U hR hEl
  generalize AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe = tv
    at htv hDc hDnd hDfr ⊢
  generalize AddInductive.ctorVals c.lparams stats.params.size types isUnsafe = cv
    at hcv hDCc hDCnd hDCfr ⊢
  have htvn : (tv.map ConstantInfo.inductInfo).map (·.name) = d.typeConsts.map (·.1) := by
    simp only [VInductDecl.typeConsts, List.map_map]
    exact List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) htv)
  have hcvn : (cv.map ConstantInfo.ctorInfo).map (·.name) = d.ctorConsts.map (·.1) := by
    simp only [VInductDecl.ctorConsts, List.map_map]
    exact List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp
      (fun _ ⟨_, _⟩ h => h.1.choose_spec.2.2.1) hcv)
  have hrn : (recs.map ConstantInfo.recInfo).map (·.name) = d.recConsts.map (·.1) := by
    simp only [VInductDecl.recConsts, hall, List.map_map]
    refine List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun v p ⟨h, hm⟩ => ?_)
      hRnames.and_mem_right)
    have ht := List.mem_zipIdx' hm
    exact h.trans (VInductDecl.recName_of_types
      (List.getElem?_eq_some_iff.2 ⟨ht.1, ht.2.symm⟩)).symm
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
    exact ((hdecl.ctors _ hAxd T (VInductDecl.mem_allTypes_of_types hT')).2 c' hcT).type) hCadd
  have henvR : envR.WF := VEnv.WF.addConstList henvC
    (VInductDecl.recConsts_WF c.envAt.tr.wf hdecl hAxd hCadd) hRadd
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
  obtain ⟨env₂, hBadd⟩ := VEnv.exists_addBlock (env := envR.addDefEqList d.iotaRules) (d := d)
    fun T hT => by
      rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hRadd,
        VEnv.addConstList_inducts hCadd, VEnv.addConstList_inducts hAxd]
      rcases hb : c.venv.inducts T.name with _ | b; · rfl
      obtain ⟨_, h⟩ := c.envAt.tr.wf.constants_of_inducts hb
      have hn : T.name ∈ d.typeConsts.map (·.1) := by simpa [VInductDecl.typeConsts] using ⟨T, hT, rfl⟩
      obtain ⟨ci, hci, e⟩ := List.mem_map.1 (htvn ▸ hn)
      have := hvfr _ (hDfr ci hci); rw [e] at this; cases h.symm.trans this
  have hstep : AddInductN nn (inductSafety isUnsafe) env.constants
      (ves.venv (inductSafety isUnsafe)) d env'.constants env₂ := by
    refine .mk (lparams := c.lparams) hU.symm htv (hcs ▸ hcv) (by rw [hall]; exact hcs ▸ hrecs)
      hnd hfr ⟨_, List.Perm.refl _, ?_⟩ (hcvenv ▸ hAxd) hCadd hRadd hBadd
    rw [hRc, hDCc, hDc, hcenv, inductConsts, insertConsts_append, insertConsts_append]
  refine ⟨hcvenv ▸ hdecl, ⟨_, hstep⟩, fun n hn => ?_⟩
  rw [← hnames] at hn
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
  exact ⟨ci, by simpa [inductConsts] using hci, rfl⟩

/-- Everything `run` established about a block without nested occurrences or primitive names
gives `FlatResult`: the elaborated `d` is well formed, and the constants `run` added are an
`AddInduct` step. -/
theorem AddInductive.assemble {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams nn : Nat} {types : List InductiveType}
    {isUnsafe : Bool} {fuel : FuelConfig} (hne : types ≠ [])
    {stats : InductiveStats} {c : AddInductive.VContext} {params : List VExpr} {level : VLevel}
    {typeTr : List VExpr}
    (hT : AddInductive.TypesData (AddInductive.VContext.top (wf.toVEnvAt (inductSafety isUnsafe))
      lparams false fuel) nparams types stats c params level typeTr)
    {envTypes : Environment}
    (hDc : envTypes.constants = insertConsts c.env.constants
      ((AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map .inductInfo))
    (hDnd : (((AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
      ConstantInfo.inductInfo).map (·.name)).Nodup)
    (hDfr : ∀ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
      ConstantInfo.inductInfo, c.env.constants.find? ci.name = none)
    (hDp : ∀ ci ∈ (AddInductive.inductVals c.lparams stats nparams types.toArray nn isUnsafe).map
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
    FlatResult ves env isUnsafe false nn env' := by
  obtain ⟨hdecl, ⟨_, hstep⟩, hnames⟩ := AddInductive.assemble_step wf hne hT hDc hDnd hDfr hleAx
    henvAx hAx hC hDCc hDCnd hDCfr hc₂U hR (hc₂ ▸ hc₂U ▸ hR.elaborates) (hc₂ ▸ hR.indices) hLE hRc
    hRnd hRfr hRnames hRtr
  have hcp : c.allowPrimitive = false := hT.base.allowPrimitive
  refine ⟨d, _, hR.isUnsafe, hdecl, hR.aux, hstep, hRq, fun _ n hn => ?_, nofun,
    hR.elaborates.stripsTo (by rw [hR.params]; exact hT.nparams)⟩
  obtain ⟨ci, hci, rfl⟩ := hnames n hn
  refine Bool.eq_false_iff.2 fun h => ?_
  simp only [List.mem_append] at hci
  have : c.allowPrimitive = true := by
    rcases hci with (hci | hci) | hci
    exacts [hDp ci hci h, hDCp ci hci h, hRp ci hci h]
  rw [hcp] at this; cases this

theorem checkDuplicatedUnivParams.WF : ∀ (ls : List Name),
    (Environment.checkDuplicatedUnivParams ls).WF fun _ => ls.Nodup
  | [] => fun _ _ => .nil
  | p :: ls => by
    unfold Environment.checkDuplicatedUnivParams
    split
    · exact fun _ h => nomatch h
    · rename_i hp
      exact fun a h => .cons (fun q hq e => hp (e ▸ hq)) (checkDuplicatedUnivParams.WF ls a h)

end Lean4Lean

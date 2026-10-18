import Lean4Lean.Theory.Typing.StructEta

/-!
# What an inductive block generates is well typed

In a well-formed environment, which uniqueness of typing applies to.
-/

namespace Lean4Lean

/-! The typing of what `VEnv.addInduct` generates, in the environments it adds it to. -/

/-- The recursors are well-typed, given the types and constructors. -/
theorem VInductDecl.recConsts_WF {decl : VInductDecl} {env envT envC : VEnv} (henv : env.WF)
    (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC) :
    ∀ p ∈ decl.recConsts, p.2.WF envC := by
  intro p hp
  have hF := VInductDecl.recFacts henv hdecl hT hC VInductDecl.recLevels_WF
    VInductDecl.recLevels_length
  simp only [VInductDecl.recConsts, List.mem_map] at hp
  obtain ⟨⟨T, i⟩, hm, rfl⟩ := hp
  exact VInductDecl.recType_isType hF VInductDecl.motiveLevel_WF (List.mem_zipIdx_iff_getElem?.1 hm)

/-- The iota rules are well-typed, given the recursors. -/
theorem VInductDecl.iotaRules_WF {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.WF) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) :
    ∀ df ∈ decl.iotaRules, df.WF envR := by
  have hF := VInductDecl.recFacts henv hdecl hT hC VInductDecl.recLevels_WF
    VInductDecl.recLevels_length
  have hF' := hF.mono (VEnv.addConstList_le hR)
    (VEnv.WF.addConstList hF.wf (recConsts_WF henv hdecl hT hC) hR)
  have hrec : decl.RecTyped envR decl.recUVars decl.recLevels decl.motiveLevel
      (decl.recConst (VLevel.params decl.recUVars)) := fun {t T} ht => by
    have hc := VEnv.addConstList_constants_of_mem hR <| List.mem_map.2
      ⟨(T, t), List.mem_zipIdx_iff_getElem?.2 ht, rfl⟩
    have ⟨_, hty⟩ := VInductDecl.recType_isType hF' VInductDecl.motiveLevel_WF ht
    have := VEnv.HasType.const (Γ := []) (ls := VLevel.params decl.recUVars) hc VLevel.params_wf
      (by simp)
    simp only [VInductDecl.recConst, ht, Option.map_some, Option.getD_some]
    rwa [(hty.levelWF trivial).1.instL_id] at this
  intro df hdf
  simp only [VInductDecl.iotaRules, List.mem_map] at hdf
  obtain ⟨⟨⟨j, c⟩, q⟩, hm, rfl⟩ := hdf
  exact VInductDecl.iotaRule_WF hF' VInductDecl.motiveLevel_WF hrec
    (List.mem_zipIdx_iff_getElem?.1 hm) (by simp)

theorem VEnv.IsTele.ctxLevelWF {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    OnCtx Γ (fun _ A => A.LevelWF U) → OnCtx (As.reverse ++ Γ) (fun _ A => A.LevelWF U)
  | _, [], .nil, hΓ => hΓ
  | _, _ :: _, .cons ⟨_, hA⟩ t, hΓ => by
    simpa using VEnv.IsTele.ctxLevelWF t ⟨hΓ, (hA.levelWF hΓ).1⟩

theorem VExpr.lams_body_inj : ∀ {As : List VExpr} {e e' : VExpr},
    VExpr.lams As e = .lams As e' → e = e'
  | [], _, _, h => h
  | _ :: _, _, _, h => VExpr.lams_body_inj (VExpr.lam.inj h).2

theorem VExpr.foralls_body_inj : ∀ {As : List VExpr} {e e' : VExpr},
    VExpr.foralls As e = .foralls As e' → e = e'
  | [], _, _, h => h
  | _ :: _, _, _, h => VExpr.foralls_body_inj (VExpr.forallE.inj h).2

theorem VEnv.IsTele.levelWF {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    OnCtx Γ (fun _ A => A.LevelWF U) → ∀ A ∈ As, A.LevelWF U
  | _, [], .nil, _ => nofun
  | _, _ :: _, .cons ⟨_, hA⟩ t, hΓ => by
    have h := (hA.levelWF hΓ).1
    intro A hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact VEnv.IsTele.levelWF t ⟨hΓ, h⟩ A hm

theorem VInductDecl.FieldsWF.getElem {d : VInductDecl} {env : VEnv} {Γ k Ds fs}
    (H : d.FieldsWF env Γ k Ds fs) : ∀ i f, fs[i]? = some f →
      env.HasType d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) f.type (.sort f.level) ∧
      f.level.WF d.uvars := by
  induction H with
  | nil => simp
  | cons _ h2 h3 _ _ _ _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using ⟨h2, h3⟩
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons] using this

namespace VInductDecl
open VExpr

theorem structCtor?_eq {d : VInductDecl} {S : VInductiveType} {c : VConstructor}
    (h : d.structCtor? = some (S, c)) : d.types = [S] ∧ S.indices = [] ∧ S.ctors = [c] := by
  unfold structCtor? at h
  split at h <;> try cases h
  rename_i S' hS
  split at h <;> cases h
  rename_i hi hc
  exact ⟨hS, hi, hc⟩

section
variable {d : VInductDecl} {S : VInductiveType} {c : VConstructor}
  (hT : d.types = [S]) (hSi : S.indices = []) (hSc : S.ctors = [c]) (hci : c.indices = [])
  (hrf : c.recFields = [])
  (hP : d.params.map (·.instL (VLevel.params d.uvars)) = d.params)
  (hF : c.fields.map (·.type.instL (VLevel.params d.uvars)) = c.fields.map (·.type))
include hT hSi hSc hci hrf hP hF
set_option linter.unusedSectionVars false

theorem ctors_struct : d.ctors = [(0, c)] := by
  simp [ctors, hT, hSc]

theorem recBinders_struct (v : VLevel) :
    d.recBinders (VLevel.params d.uvars) v =
      d.params ++ [d.structMotiveType S v, d.structMinorType c] := by
  simp [recBinders, motiveTypes, minorTypes, ctors_struct hT hSi hSc hci hrf hP hF, hT, hP,
    motiveType, minorType, hSi, hci, hrf, hF, structMotiveType, structMinorType, structApp,
    ctorApp, liftTele]

theorem recType_struct (v : VLevel) :
    d.recType (VLevel.params d.uvars) v 0 S =
      .foralls (d.params ++ [d.structMotiveType S v, d.structMinorType c, d.structApp S 2])
        (.app (.bvar 2) (.bvar 0)) := by
  rw [recType, recBinders_struct hT hSi hSc hci hrf hP hF]
  simp [ctors_struct hT hSi hSc hci hrf hP hF, hT, hSi, liftTele, foralls_append, structApp]

theorem iotaRule_struct (v : VLevel) :
    d.iotaRule (VLevel.params d.uvars) v (v :: VLevel.params d.uvars) 0 0 c =
      { uvars := d.uvars + 1
        lhs := .lams (d.iotaBinders S c v)
          (.appN (.const (Lean.mkRecName S.name) (v :: VLevel.params d.uvars))
            (bvars d.params.length (c.fields.length + 2) ++
              [.bvar (c.fields.length + 1), .bvar c.fields.length, d.ctorApp c 2]))
        rhs := .lams (d.iotaBinders S c v) (.appN (.bvar c.fields.length) (bvars c.fields.length 0))
        type := .foralls (d.iotaBinders S c v)
          (.app (.bvar (c.fields.length + 1)) (d.ctorApp c 2)) } := by
  rw [iotaRule, recBinders_struct hT hSi hSc hci hrf hP hF]
  have h1 : ∀ k, bvars 1 k = [.bvar k] := fun k => by simp [bvars]
  simp [ctors_struct hT hSi hSc hci hrf hP hF, hT, hci, hrf, hF, iotaBinders, recConst, ctorApp,
    h1, Nat.add_comm 2 c.fields.length, Nat.add_comm 1 c.fields.length]

end
end VInductDecl

/-- What structure eta is typed from, for a non-recursive structure with large elimination. -/
theorem VInductDecl.etaFacts {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.WF) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) {S : VInductiveType} {c : VConstructor}
    (hs : decl.structCtor? = some (S, c)) (hrec : decl.isRec = false) (hL : decl.LargeElim) :
    decl.EtaFacts S c (envR.addDefEqList decl.iotaRules) := by
  obtain ⟨hTs, hSi, hSc⟩ := VInductDecl.structCtor?_eq hs
  have hSmem : S ∈ decl.types := by simp [hTs]
  have hcmem : c ∈ S.ctors := by simp [hSc]
  have hTW := hdecl.ctors envT hT S hSmem
  have hcW := hTW.2 c hcmem
  obtain ⟨ps, Ds, hty, hps, hfs⟩ := hcW.shape
  have hci : c.indices = [] := List.eq_nil_of_length_eq_zero (by rw [hcW.indices.1, hSi]; rfl)
  have hrf : c.recFields = [] := by
    simp only [VConstructor.recFields, List.filterMap_eq_nil_iff]
    rintro ⟨f, k⟩ hm
    have hf : f ∈ c.fields := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hm)
    simp [hdecl.isRec hrec S hSmem c hcmem f hf]
  have hF := VInductDecl.recFacts henv hdecl hT hC (U := decl.uvars)
    (ls := VLevel.params decl.uvars) VLevel.params_wf (by simp [VLevel.params])
  have hle₁ : env ≤ envT := VEnv.addConstList_le hT
  have hle₂ : envT ≤ envC := VEnv.addConstList_le hC
  have hleR : envC ≤ envR := VEnv.addConstList_le hR
  have henvR : envR.WF :=
    VEnv.WF.addConstList hF.wf (VInductDecl.recConsts_WF henv hdecl hT hC) hR
  have hFR := hF.mono hleR henvR
  have hEo : (envR.addDefEqList decl.iotaRules).Ordered :=
    VEnv.addDefEqList_ordered henvR.ordered (VInductDecl.iotaRules_WF henv hdecl hT hC hR)
  have hle : envR ≤ envR.addDefEqList decl.iotaRules := VEnv.addDefEqList_le
  have hleT : envT ≤ envR.addDefEqList decl.iotaRules := hle₂.trans (hleR.trans hle)
  -- the declaration's expressions mention only its own level parameters
  have hPctx := hdecl.params.ctxLevelWF (Γ := []) trivial
  have hP : decl.params.map (·.instL (VLevel.params decl.uvars)) = decl.params :=
    List.map_id''' _ fun A h => (hdecl.params.levelWF trivial A h).instL_id
  have hFt := (VInductDecl.FieldsWF.tele hfs).1
  have hFid : c.fields.map (·.type.instL (VLevel.params decl.uvars)) = c.fields.map (·.type) := by
    apply List.map_congr_left; intro f hf
    exact (hFt.levelWF (by simpa using hPctx) f.type (List.mem_map_of_mem hf)).instL_id
  have hj0 : decl.types[0]? = some S := by simp [hTs]
  have hc0 : (0, c) ∈ decl.ctors := by simp [VInductDecl.ctors, hTs, hSc]
  have hq0 : decl.ctors[0]? = some (0, c) := by simp [VInductDecl.ctors, hTs, hSc]
  have hrl : ∀ v : VLevel, decl.recLevels.map (VLevel.inst (v :: VLevel.params decl.uvars)) =
      VLevel.params decl.uvars := by
    intro v
    simp [VInductDecl.recLevels, hL, VLevel.params, List.map_map, Function.comp_def,
      VLevel.inst]
    intro a ha; simp [List.getElem?_range ha]
  have hml : ∀ v : VLevel, decl.motiveLevel.inst (v :: VLevel.params decl.uvars) = v := by
    intro v; simp [VInductDecl.motiveLevel, hL, VLevel.inst]
  have hru : decl.recUVars = decl.uvars + 1 := by simp [VInductDecl.recUVars, hL]
  -- the recursor, at any motive level
  have hrecC : ∀ {v : VLevel}, v.WF decl.uvars →
      envR.HasType decl.uvars [] (.const (Lean.mkRecName S.name) (v :: VLevel.params decl.uvars))
        (decl.recType (VLevel.params decl.uvars) v 0 S) := by
    intro v hv
    have hc := VEnv.addConstList_constants_of_mem hR (List.mem_map.2
      ⟨(S, 0), List.mem_zipIdx_iff_getElem?.2 hj0, rfl⟩)
    have := VEnv.HasType.const (Γ := []) (ls := v :: VLevel.params decl.uvars) hc
      (by simpa using ⟨hv, VLevel.params_wf⟩) (by simp [hru, VLevel.params])
    rwa [VInductDecl.recType_instL, hrl, hml] at this
  have hlvl := fun {k f} (hf : c.fields[k]? = some f) => VInductDecl.FieldsWF.getElem hfs k f hf
  refine {
    henv := hEo
    closed := fun k f hf => ?_
    params := hdecl.params.mono (hle₁.trans hleT)
    fields := hFt.mono hleT
    level := fun hf => let ⟨a, b⟩ := hlvl hf; ⟨a.mono hleT, b⟩
    sort := ?_
    ctor := ?_
    recTyping := fun hv => by
      have := (hrecC hv).mono hle
      rwa [VInductDecl.recType_struct hTs hSi hSc hci hrf hP hFid] at this
    iota := fun {v} hv => ?_ }
  · have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
    have htake := (VEnv.IsTele.append_inv (show envT.IsTele decl.uvars decl.params.reverse
      ((c.fields.take k).map (·.type) ++ (c.fields.drop k).map (·.type)) by
        rw [← List.map_append, List.take_append_drop]; exact hFt)).1
    have hctx : OnCtx (((c.fields.take k).map (·.type)).reverse ++ decl.params.reverse)
        ((envR.addDefEqList decl.iotaRules).IsType decl.uvars) := by
      simpa using (htake.mono hleT).onCtx (by
        simpa using (hdecl.params.mono (hle₁.trans hleT)).onCtx trivial)
    have := ((hlvl hf).1.mono hleT).closedN hEo (VEnv.CtxWF.closed hEo hctx)
    simpa [Nat.min_eq_left (Nat.le_of_lt hk), Nat.add_comm] using this
  · have := (hF.type hj0).mono (hleR.trans hle)
    rw [hP, hSi, List.map_nil, List.append_nil] at this
    exact ⟨_, by simpa [VInductDecl.structApp, VExpr.liftN] using this.appN_bvars hEo⟩
  · have := ((hF.ctor hc0 hj0).2).mono (hleR.trans hle)
    rw [hP, hFid, hci, List.map_nil, List.append_nil] at this
    have hb : VExpr.bvars decl.params.length c.fields.length ++ VExpr.bvars c.fields.length 0 =
        VExpr.bvars (decl.params.length + c.fields.length) 0 := by
      simpa using VExpr.bvars_append decl.params.length c.fields.length 0
    have := this.appN_bvars hEo
    simp only [List.length_append, List.reverse_append, List.append_nil, List.length_map] at this
    simpa [VInductDecl.ctorApp, VInductDecl.structApp, VExpr.liftN, hb] using this
  · have hrecT : decl.RecTyped envR decl.uvars (VLevel.params decl.uvars) v
        (decl.recConst (v :: VLevel.params decl.uvars)) := fun {t T} ht => by
      obtain ⟨rfl, rfl⟩ : t = 0 ∧ S = T := by
        rw [hTs] at ht; cases t <;> simp at ht; exact ⟨rfl, ht⟩
      simpa [VInductDecl.recConst, hTs] using hrecC hv
    obtain ⟨L, R, T, hl, hr, ht, hB, hLt, hRt⟩ := VInductDecl.iotaRule_bodies hFR hv hrecT hq0
    have hrule := VInductDecl.iotaRule_struct hTs hSi hSc hci hrf hP hFid v
    have hbind : decl.recBinders (VLevel.params decl.uvars) v ++
        VExpr.liftTele (decl.types.length + decl.ctors.length)
          (c.fields.map (·.type.instL (VLevel.params decl.uvars))) = decl.iotaBinders S c v := by
      rw [VInductDecl.recBinders_struct hTs hSi hSc hci hrf hP hFid,
        VInductDecl.ctors_struct hTs hSi hSc hci hrf hP hFid, hTs, hFid]
      simp [VInductDecl.iotaBinders]
    rw [hbind] at hl hr ht hB hLt hRt
    have eL := VExpr.lams_body_inj (hl.symm.trans (congrArg VDefEq.lhs hrule))
    have eR := VExpr.lams_body_inj (hr.symm.trans (congrArg VDefEq.rhs hrule))
    have eT := VExpr.foralls_body_inj (ht.symm.trans (congrArg VDefEq.type hrule))
    subst eL eR eT
    have hmem : decl.iotaRule decl.recLevels decl.motiveLevel (VLevel.params decl.recUVars) 0 0 c ∈
        decl.iotaRules := by
      simp [VInductDecl.iotaRules, VInductDecl.ctors_struct hTs hSi hSc hci hrf hP hFid]
    have hdf := VEnv.IsDefEq.extra (Γ := []) (VEnv.addDefEqList_defeqs_of_mem (env := envR) hmem)
      (ls := v :: VLevel.params decl.uvars) (by simpa using ⟨hv, VLevel.params_wf⟩)
      (by simp [VInductDecl.iotaRule, hru, VLevel.params])
    obtain ⟨e1, e2, e3⟩ := VInductDecl.iotaRule_instL decl.recLevels
      (v :: VLevel.params decl.uvars) (VLevel.params decl.recUVars) decl.motiveLevel 0 0 c
    rw [e1, e2, e3, hrl, hml, VLevel.params_inst (by simp [hru, VLevel.params]), hrule] at hdf
    exact ⟨hB.mono hle, hLt.mono hle, hRt.mono hle, hdf⟩

/-- The eta rule is well-typed, given the iota rules: the projections it is stated with compute
on a constructor only by iota. -/
theorem VInductDecl.etaRules_WF {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.WF) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) :
    ∀ df ∈ decl.etaRules, df.WF (envR.addDefEqList decl.iotaRules) := by
  intro df hdf
  unfold VInductDecl.etaRules at hdf
  by_cases h : decl.isRec = false ∧ decl.LargeElim
  · rw [if_pos h] at hdf
    cases hs : decl.structCtor? with
    | none => simp [hs] at hdf
    | some p =>
      obtain ⟨S, c⟩ := p
      simp only [hs, List.mem_singleton] at hdf
      subst hdf
      exact (etaFacts henv hdecl hT hC hR hs h.1 h.2).etaRule_WF
  · rw [if_neg h] at hdf; simp at hdf

theorem VInductDecl.generatedWF {decl : VInductDecl} {env : VEnv} (henv : env.WF)
    (hdecl : decl.WF env) : decl.GeneratedWF env := fun _ _ _ hT hC hR =>
  ⟨recConsts_WF henv hdecl hT hC, iotaRules_WF henv hdecl hT hC hR,
    etaRules_WF henv hdecl hT hC hR⟩

end Lean4Lean

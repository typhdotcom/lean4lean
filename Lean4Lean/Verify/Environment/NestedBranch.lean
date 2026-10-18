import Lean4Lean.Verify.Environment.NestedPlaced

/-!
# `addInductive`

A block without nested occurrences is checked as it is (`Flat.lean`). A nested block is checked
flat as its translation, whose result the final phase restores (`nestedFinal`): the restored block
is well formed, and what the final phase adds is its `AddInduct` step.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- The names of the auxiliary types and constructors the elimination made. -/
def auxCtorNames (res : ElimNestedInductive.Result) (types : List InductiveType) : NameSet :=
  (res.types.drop types.length).foldl (init := {}) fun s t =>
    t.ctors.foldl (·.insert ·.name) (s.insert t.name)

/-- The check that no input constructor names an auxiliary type or constructor. -/
theorem auxNameCheck.WF (res : ElimNestedInductive.Result) (types : List InductiveType) :
    (forIn (m := Except Exception) types PUnit.unit.{1} fun indType _ => do
      forIn (m := Except Exception) indType.ctors PUnit.unit.{1} fun ctor _ => do
        if ctor.type.anySubterm (fun
            | .const c _ => (auxCtorNames res types).contains c
            | .proj s _ _ => (auxCtorNames res types).contains s
            | _ => false) = true then
          throw <| .other s!"invalid declaration '{ctor.name}', it uses an auxiliary nested type"
        pure (ForInStep.yield PUnit.unit)
      pure (ForInStep.yield PUnit.unit)).WF
      fun _ => ∀ T ∈ types, ∀ c ∈ T.ctors,
        c.type.anySub (auxP (auxCtorNames res types)) = false := by
  intro _ h T hT c hc
  have h1 := Except.forIn_yield_ok' h T hT
  obtain ⟨_, h2⟩ := Except.forIn_yield_ok (fun x u s h => by
    dsimp only at h; split at h
    · cases h
    · cases h; rfl) h1 c hc
  rw [← anySubterm_auxP]
  dsimp only at h2
  split at h2
  · cases h2
  · next hn => exact Bool.eq_false_iff.2 hn

namespace ElimNestedInductive

/-- A term without applications, where the elimination finds nothing nested. -/
def NoApp : Expr → Prop
  | .app .. => False
  | .lam _ d b _ | .forallE _ d b _ => NoApp d ∧ NoApp b
  | .letE _ t v b _ => NoApp t ∧ NoApp v ∧ NoApp b
  | .mdata _ b | .proj _ _ b => NoApp b
  | _ => True

/-- Runs leaving the state as it was, with a result satisfying `P`. -/
def Keeps (x : M α) (P : α → Prop) : Prop :=
  ∀ env s a s', x env s = .ok (a, s') → s' = s ∧ P a

theorem Keeps.bind {x : M α} {f : α → M β} {P Q} (h1 : Keeps x P)
    (h2 : ∀ a, P a → Keeps (f a) Q) : Keeps (x >>= f) Q := by
  intro env s b s' h
  obtain ⟨a, s₁, h1', h2'⟩ := bind_ok h
  obtain ⟨rfl, ha⟩ := h1 _ _ _ _ h1'
  exact h2 a ha _ _ _ _ h2'

theorem Keeps.pure {a : α} {P : α → Prop} (h : P a) : Keeps (pure a : M α) P := by
  rintro _ _ _ _ ⟨⟩; exact ⟨rfl, h⟩

theorem replaceIfNested_noApp (lctx : LocalContext) (params As : Array Expr) {e : Expr}
    (he : e.isApp = false) : Keeps (replaceIfNested lctx params As e) (· = none) := by
  unfold replaceIfNested
  refine Keeps.bind (P := (· = none)) ?_ fun r hr => ?_
  · unfold isNestedInductiveApp?
    simp only [he, Bool.not_false, if_true]
    exact Keeps.pure rfl
  · subst hr; exact Keeps.pure rfl

theorem replaceNoCacheT_noApp (lctx : LocalContext) (params As : Array Expr) :
    ∀ {e : Expr}, NoApp e →
      Keeps (e.replaceNoCacheT (replaceIfNested lctx params As)) (· = e) := by
  intro e he
  induction e with
  | app => exact he.elim
  | bvar | fvar | mvar | sort | const | lit =>
    unfold Expr.replaceNoCacheT
    exact Keeps.bind (replaceIfNested_noApp _ _ _ rfl) fun r hr => by subst hr; exact Keeps.pure rfl
  | lam _ d b _ ih1 ih2 | forallE _ d b _ ih1 ih2 =>
    unfold Expr.replaceNoCacheT
    refine Keeps.bind (replaceIfNested_noApp _ _ _ rfl) fun r hr => ?_
    subst hr
    exact Keeps.bind (ih1 he.1) fun _ h1 => Keeps.bind (ih2 he.2) fun _ h2 => Keeps.pure (by
      subst h1 h2; rfl)
  | letE _ t v b _ ih1 ih2 ih3 =>
    unfold Expr.replaceNoCacheT
    refine Keeps.bind (replaceIfNested_noApp _ _ _ rfl) fun r hr => ?_
    subst hr
    exact Keeps.bind (ih1 he.1) fun _ h1 => Keeps.bind (ih2 he.2.1) fun _ h2 =>
      Keeps.bind (ih3 he.2.2) fun _ h3 => Keeps.pure (by subst h1 h2 h3; rfl)
  | mdata _ b ih | proj _ _ b ih =>
    unfold Expr.replaceNoCacheT
    refine Keeps.bind (replaceIfNested_noApp _ _ _ rfl) fun r hr => ?_
    subst hr
    exact Keeps.bind (ih he) fun _ h1 => Keeps.pure (by subst h1; rfl)

theorem ctorStep_noApp (params : Array Expr) (ctor : Constructor) (h : NoApp ctor.type) :
    Keeps (ctorStep 0 params ctor) (· = ctor) := by
  unfold ctorStep withParams
  rw [withParams.loop]
  simp only [Array.size_empty, beq_self_eq_true, if_true]
  exact Keeps.bind (replaceNoCacheT_noApp _ _ _ h) fun e he => Keeps.pure (by
    subst he; rw [mkForall_empty])

theorem Keeps.mapM {l : List β} {f : β → M γ} {R : β → γ → Prop}
    (h : ∀ b ∈ l, Keeps (f b) (R b)) : Keeps (l.mapM f) (List.Forall₂ R l) := by
  induction l with
  | nil => exact Keeps.pure .nil
  | cons b l ih =>
    rw [List.mapM_cons]
    exact Keeps.bind (h b (.head _)) fun c hc =>
      Keeps.bind (ih fun b hb => h b (.tail _ hb)) fun cs hcs => Keeps.pure (.cons hc hcs)

theorem run.loop_noApp {lctx : LocalContext} {params : Array Expr} {env : Environment} :
    ∀ (fuel i : Nat) (s : State) (res : Result) (s' : State),
      run.loop 0 lctx params i fuel env s = .ok (res, s') → s.nestedAux = #[] →
      (∀ t ∈ s.newTypes.toList, ∀ c ∈ t.ctors, NoApp c.type) → res.aux2nested.size = 0
  | 0, i, s, res, s', h, _, _ => by rw [run.loop] at h; cases h
  | fuel + 1, i, s, res, s', h, hz, hT => by
    rw [run.loop, bind_apply] at h
    rw [show (MonadState.get : M State) env s = .ok (s, s) from rfl] at h
    dsimp only at h
    split at h
    · rename_i hi
      obtain ⟨ctors, s₁, hv, h⟩ := bind_ok h
      obtain ⟨_, s₂, hm, h⟩ := bind_ok h
      cases hm
      obtain ⟨hs₁, hcs⟩ := Keeps.mapM (R := fun b c => c = b) (fun ct hct =>
        ctorStep_noApp params ct (hT _ (Array.getElem_mem_toList hi) ct hct)) env s ctors s₁ hv
      subst s₁
      have hcs' : ctors = s.newTypes[i].ctors := by
        have : ∀ {l l' : List Constructor}, List.Forall₂ (fun b c => c = b) l l' → l' = l := by
          intro l l' h
          induction h with
          | nil => rfl
          | cons h _ ih => rw [h, ih]
        exact this hcs
      refine run.loop_noApp fuel (i + 1) _ res s' h hz fun t ht c hc => ?_
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at ht
      rcases List.mem_or_eq_of_mem_set ht with ht | rfl
      · exact hT t ht c hc
      · rw [hcs'] at hc; exact hT _ (Array.getElem_mem_toList hi) c hc
    · cases h
      simp only
      rw [hz]; rfl

end ElimNestedInductive

/-- A primitive block has no nested occurrences. -/
theorem PrimitiveInductiveResult.flat {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    (hp : Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) {fuel : Nat}
    {res : ElimNestedInductive.Result}
    (h : (ElimNestedInductive.run fuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res) :
    res.aux2nested.size = 0 := by
  obtain ⟨-, -, rfl, type, cs, rfl, -, hshape, -⟩ := hp
  obtain ⟨⟨res', s'⟩, h1, h2⟩ : ∃ p, ElimNestedInductive.run fuel 0 [type] env
      { lvls := lparams.map .param, newTypes := [type].toArray } = .ok p ∧ p.1 = res := by
    revert h; unfold StateT.run'
    cases ElimNestedInductive.run fuel 0 [type] env _ <;> simp [Functor.map, Except.map]
  subst h2
  unfold ElimNestedInductive.run at h1
  simp only [ElimNestedInductive.withParams] at h1
  rw [ElimNestedInductive.withParams.loop] at h1
  refine ElimNestedInductive.run.loop_noApp fuel 0 _ _ _ h1 rfl fun t ht c hc => ?_
  simp at ht
  subst ht
  rcases hshape with ⟨-, -, he⟩ | ⟨-, -, nm, bi, he⟩ <;> rw [he] at hc <;>
    simp at hc <;> rcases hc with rfl | rfl <;> simp [ElimNestedInductive.NoApp]

/-- The nested branch of `addInductive`: the translation checked flat into `env'`, the final
phase gives a model of what it adds. -/
theorem addInductive.WF_nested {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig}
    (hcl : ∀ T ∈ types, ElimNestedInductive.TypeClosed T)
    {res : ElimNestedInductive.Result}
    (hrun : (ElimNestedInductive.run fuel.inductiveFuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res)
    (h0 : res.aux2nested.size ≠ 0)
    (hin : ∀ T ∈ types, ∀ c ∈ T.ctors, c.type.anySub (auxP (auxCtorNames res types)) = false)
    {env' : Environment}
    (hFR : FlatResult ves env lparams nparams res.types isUnsafe false res.aux2nested.size env')
    {envF : Environment}
    (hfin : nestedFinal env env' lparams types res isUnsafe false fuel = .ok envF) :
    ∃ ves' : VEnvs, ves'.WF envF ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  -- the translation, checked flat
  obtain ⟨d, venv', hu, hd, hdaux, hflat, hq, hnp, -, ⟨E₁, level, hE₁, hEl⟩, hIdx, hM, hX, -⟩ := hFR
  obtain ⟨hU, hUs, hdpar, hlpv, htyTr, hcty⟩ := hX rfl
  have henvAt := wf.toVEnvAt (inductSafety isUnsafe)
  generalize hvenv : ves.venv (inductSafety isUnsafe) = venv at henvAt hd hflat hE₁
  have henv : venv.WF := henvAt.tr.wf
  have hCwf : env.constants.WF := henvAt.tr.map_wf
  have hnp := hnp rfl
  obtain ⟨cis, hC', hnd, hfr, -, hnames⟩ := AddInductN.names hflat
  -- the elimination
  obtain ⟨I, rest, rfl, xs, body, hoI, hxl, hxnd, hparams, hnpar, auxs, pairs, hA, haux2, hclAll,
    hTD, hfree⟩ := ElimNestedInductive.run_spec (ElimNestedInductive.EnvClosed.of_tr
      (wf.tr (safety := .unsafe))) hcl hrun
  -- the final phase
  obtain ⟨inds, recs, envT, hF⟩ := nestedFinal.WF hfin
  have hauxne : auxs ≠ [] := by
    rintro rfl; cases hA; exact h0 (by rw [haux2]; rfl)
  -- what restoring needs of the tables
  have hpairs : pairs.map (·.2) = auxs.map (·.name) := by
    have : ∀ {ps : List (Expr × Name)} {ts : List InductiveType},
        List.Forall₂ (fun e T => ElimNestedInductive.AuxMade env res.params nparams (e, T)) ps ts →
        ps.map (·.2) = ts.map (·.name) := by
      intro ps ts h
      induction h with
      | nil => rfl
      | cons h _ ih => rw [List.map_cons, List.map_cons, ih]; exact congrArg (· :: _) h.1.symm
    exact this hA
  -- the translated block's constants, as the flat check added them
  obtain ⟨lps, envT', envC', envR', hl, hT', hC'', hR', hRle, hfT, hfC, hfR⟩ :=
    hflat.flatFind hCwf hdaux
  have hfrE : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1),
      env.find? x = none := by
    intro x hx
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 (hnames.mem_iff.2 hx)
    rw [Kernel.Environment.find?, hCwf.find?'_eq_find?]; exact hfr ci hci
  have hmemT {T : VInductiveType} (hT : T ∈ d.types) :
      T.name ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    simp only [List.map_append, List.mem_append]
    exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T, hT, rfl⟩, rfl⟩))
  have hnmj : ∀ (j : Nat) (t : InductiveType) (T : VInductiveType), (I :: rest ++ auxs)[j]? = some t →
      d.types[j]? = some T →
      T.name = t.name := by
    intro j t T ht hT
    obtain ⟨t', ht', hD⟩ := hTD.getElem?_left ht
    obtain ⟨T', hT'', hE⟩ := hEl.types.getElem?_left ht'
    rw [hT] at hT''; cases hT''
    exact hE.1.trans hD.1
  have hdlen : d.types.length = (I :: rest).length + auxs.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hEl.types, ← Lean4Lean.List.Forall₂.length_eq hTD]
    simp; omega
  obtain ⟨T₀, hT₀⟩ : ∃ T, d.types[0]? = some T :=
    ⟨_, List.getElem?_eq_getElem (by rw [hdlen]; simp; omega)⟩
  obtain ⟨info, hinfo, hTr₀, -⟩ := hfT 0 T₀ hT₀
  have hT₀n : T₀.name = I.name := hnmj 0 I T₀ rfl hT₀
  rw [hT₀n] at hinfo
  have hlps : lps = lparams := by
    rcases hlpv _ _ hinfo with h | h
    · rw [hfrE _ (hT₀n ▸ hmemT (List.mem_of_getElem? hT₀))] at h; cases h
    · exact hTr₀.2.1.symm.trans h
  subst hlps
  have hall : info.all = d.types.map (·.name) := hTr₀.2.2.2.2.1
  have hlpk : ∀ t ∈ I :: rest, ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      ind.levelParams = lps := by
    intro t ht ind hind
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    have hj' : (I :: rest ++ auxs)[j]? = some t := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1]; exact hj
    obtain ⟨T, hT⟩ : ∃ T, d.types[j]? = some T := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 hj).1; rw [hdlen]; omega)⟩
    have hTn := hnmj j t T hj' hT
    rcases hlpv _ _ hind with h | h
    · rw [hfrE _ (hTn ▸ hmemT (List.mem_of_getElem? hT))] at h; cases h
    · exact h
  have hndT : (d.types.map (·.name)).Nodup := by
    have := (hnames.nodup_iff.1 hnd).sublist (by
      simp only [List.map_append]
      exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _))
    simpa [VInductDecl.typeConsts, Function.comp_def] using this
  have hcname : ∀ j T, j < (I :: rest).length → d.types[j]? = some T → ∀ c ∈ T.ctors,
      res.restoreCtorName env' c.name = c.name := by
    intro j T hj hT c hc
    obtain ⟨c₀, hf, ⟨T', hT', -, -, -, hind, -⟩, -⟩ := hfC j T hT c hc
    rw [hT] at hT'; cases hT'
    refine restoreCtorName_of_not_aux haux2 hf ?_
    rw [hind, hpairs]
    intro hm
    obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
    have hk' : (I :: rest ++ auxs)[(I :: rest).length + k]? = some a := by
      rw [List.getElem?_append_right (by omega)]; simpa using hk
    obtain ⟨T₂, hT₂⟩ : ∃ T, d.types[(I :: rest).length + k]? = some T :=
      ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hdlen]; omega)⟩
    have e := (hnmj _ _ _ hk' hT₂).trans he
    obtain ⟨h1, h1'⟩ := List.getElem?_eq_some_iff.1 hT
    obtain ⟨h2, h2'⟩ := List.getElem?_eq_some_iff.1 hT₂
    have := (List.getElem_inj (xs := d.types.map (·.name)) (i := j) (j := (I :: rest).length + k)
      (h₀ := by simpa using h1) (h₁ := by simpa using h2) hndT).1
      (by rw [List.getElem_map, List.getElem_map, h1', h2', e])
    omega
  have hnamesE : (I :: rest ++ auxs).map (·.name) = d.types.map (·.name) := by
    refine List.ext_getElem? fun j => ?_
    simp only [List.getElem?_map]
    cases ht : (I :: rest ++ auxs)[j]? with
    | none =>
      have := List.getElem?_eq_none_iff.1 ht
      rw [List.getElem?_eq_none (by rw [hdlen]; simp at this ⊢; omega)]; rfl
    | some t =>
      obtain ⟨T, hT⟩ : ∃ T, d.types[j]? = some T := ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.1 ht).1; simp at this; rw [hdlen]; simp; omega)⟩
      rw [hT]; simp [hnmj j t T ht hT]
  have hpnd : (pairs.map (·.2)).Nodup := by
    rw [hpairs]
    have := hnamesE ▸ hndT
    rw [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  -- the occurrences the auxiliary types stand for
  obtain ⟨venvT, hVT, hleT, hlitT⟩ := nested_envT wf (hvenv ▸ hflat) (hvenv ▸ hd) hnp
    (hvenv ▸ hfT) (fun j t T ht hT => hnmj j t T (by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1]; exact ht) hT)
    (by rw [hdlen]; omega) hF
  obtain ⟨IT, hIT⟩ : ∃ IT, TrExprS (ves.venv (inductSafety isUnsafe)) lps [] I.type IT := by
    obtain ⟨r₀, hr₀, hD₀⟩ := forall₂_getElem?_l hTD (i := 0) rfl
    obtain ⟨T, -, hT⟩ := forall₂_getElem?_l htyTr hr₀
    exact ⟨_, hD₀.2.1 ▸ hT.1⟩
  obtain ⟨ns, hocc⟩ := nested_occs wf hcl hrun hoI hxnd hparams hA haux2 hpnd hF hVT
    (hvenv ▸ hleT) (hvenv ▸ hlitT) hIT
  have hnsl : ns.length = auxs.length :=
    (Lean4Lean.List.Forall₂.length_eq hocc).symm.trans (Lean4Lean.List.Forall₂.length_eq hA)
  let n := (I :: rest).length
  let cname := res.restoreCtorName env'
  let R := d.auxTable n ns cname
  let ren := auxRecRen env' (I :: rest)
  have hin' := restoreInputs_hin (n := n) (ns := ns) (cname := cname) wf hfrE hEl hfree
    (S := auxCtorNames res (I :: rest)) (foldl_typeNames_contains _) hin
  have hRI := restoreInputs henv henvAt.hasPrimitives hd hdaux hE₁ (hnames.nodup_iff.1 hnd)
    (fun x hx => by
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 (hnames.mem_iff.2 hx)
      exact henvAt.tr.constants_eq_none
        (by rw [Kernel.Environment.find?, hCwf.find?'_eq_find?]; exact hfr ci hci))
    (fun x hx => hnp x hx) hUs hU hdpar hEl hTD hpairs hclAll
    (hnsl.trans rfl) hauxne hinfo hall hcname hin'
  -- the restored block is well formed
  have hnamesR : (I :: rest).map (·.name) = (d.restoreNested R ren n ns cname).names := by
    have hn : n ≤ d.types.length := by rw [hdlen]; omega
    refine List.ext_getElem? fun j => ?_
    simp only [VInductDecl.names, List.getElem?_map]
    by_cases hj : j < n
    · rw [VInductDecl.restoreNested_types_getElem? hj]
      obtain ⟨T, hT⟩ : ∃ T, d.types[j]? = some T := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨t, ht⟩ : ∃ t, (I :: rest)[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hT, ht]
      have := hnmj j t T (by rw [List.getElem?_append_left hj]; exact ht) hT
      simp [VInductiveType.restore, this]
    · rw [List.getElem?_eq_none (by simp at hj ⊢; omega), List.getElem?_eq_none
        (by rw [VInductDecl.restoreNested_types_length hn]; omega)]
      rfl
  have hlit : ∀ l, venv'.ContainsLits l → venv.ContainsLits l := by
    have hc {x : Name} (hx : Environment.primitives.contains x = true) :
        venv'.contains x → venv.contains x := fun ⟨ci, h⟩ => by
      rcases AddInductN.constants_cases hflat h with h | h
      · exact ⟨ci, h⟩
      · rw [hnp x h] at hx; cases hx
    intro l hl
    cases l with
    | natVal => exact hc (by simp +decide [Environment.primitives, NameSet.ofList,
        NameSet.contains]) hl
    | strVal => exact ⟨hc (by simp +decide [Environment.primitives, NameSet.ofList,
        NameSet.contains]) hl.1, hc (by simp +decide [Environment.primitives, NameSet.ofList,
        NameSet.contains]) hl.2⟩
  have hns : ns ≠ [] := by
    rintro rfl; exact hauxne (List.eq_nil_of_length_eq_zero (by simpa using hnsl.symm))
  have hnn : res.aux2nested.size = ns.length := by
    rw [haux2]
    refine (size_foldl_insert_nodup pairs {} hpnd (fun _ _ => rfl)).trans ?_
    rw [hnsl, ← Lean4Lean.List.Forall₂.length_eq hA]; simp
  have hSN : ∀ c, (R c).isSome ∨ ((mkAuxRecNameMap env' (I :: rest)).2.find? c).isSome →
      (auxNameSet res (I :: rest) (mkAuxRecNameMap env' (I :: rest)).1).contains c := by
    intro c hc
    refine auxNameSet_contains ?_
    rcases hc with hc | hc
    · obtain ⟨h, hR'⟩ := Option.isSome_iff_exists.1 hc
      obtain ⟨k, T, o, ⟨hT, -, hc'⟩, -⟩ := VInductDecl.auxTable_some hR'
      obtain ⟨t, ht, hE⟩ := hEl.types.getElem?_right hT
      refine .inr ⟨t, List.mem_iff_getElem?.2 ⟨k, by rw [List.getElem?_drop]; exact ht⟩, ?_⟩
      rcases hc' with rfl | ⟨c', hc', rfl⟩
      · exact .inl hE.1
      · obtain ⟨ct, hct, hce⟩ := Lean4Lean.List.Forall₂.forall_exists_r hE.2 c' hc'
        exact .inr (List.mem_map.2 ⟨ct, hct, hce.1.symm⟩)
    · refine .inl (Classical.byContradiction fun hn => ?_)
      have hlen : (I :: rest).length < info.all.length := by
        rw [hall, List.length_map, hdlen]
        have := List.length_pos_iff.2 hauxne; omega
      have := NM.get?_none_of_getD ((mkAuxRecNameMap_spec hinfo hlen).2.2 c · hn)
      rw [show (mkAuxRecNameMap env' (I :: rest)).2.find? c = _ from this] at hc
      cases hc
  have hcL : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.type.LeadFree R ren := by
    intro T hT c hc
    obtain ⟨ps, B, he, -, hps, hB⟩ := (hRI.ctor T hT c hc).shape
    rw [he]
    exact VExpr.LeadFree.foralls (fun A hA => VExpr.AuxFree.leadFree (hps A hA)) hB.leadFree
  have hO := henv.ordered
  have hall' : d.allTypes = d.types := VInductDecl.allTypes_of_aux hdaux
  have hAF (c : Name) (hc : (venv.constants c).isSome) : R c = none ∧ ren c = none := by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      refine ⟨?_, ?_⟩
      · cases h : R c with
        | none => rfl
        | some _ => rw [hRI.Rfresh c _ h] at hci; cases hci
      · cases h : ren c with
        | none => rfl
        | some _ => rw [hRI.renfresh c _ h] at hci; cases hci
  have hfreeV {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) : e.AuxFree R ren :=
    he.mono hAF
  have hfreeE {e : VExpr} (he : e.ConstsSat (E₁.constants · |>.isSome))
      (hm : e.mentions d.names = false) : e.AuxFree R ren :=
    (he.and (VExpr.constsSat_of_mentions hm)).mono fun c ⟨hc, hn⟩ => by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      rcases VEnv.addConstList_constants_cases hE₁ hci with h | h
      · exact hAF c (by rw [h]; rfl)
      · obtain ⟨T, hT, e⟩ := List.mem_map.1 h
        cases e
        exact (hn (List.mem_map_of_mem hT)).elim
  have hPP₁ : OnCtx d.params.reverse (E₁.IsType d.uvars) := by
    simpa using (hd.params.mono (VEnv.addConstList_le hE₁)).onCtx trivial
  have hP : d.LeadFreeParts R ren := {
    params := fun A hA => VExpr.AuxFree.leadFree (hfreeV (VEnv.IsTele.constsSat hO hd.params trivial A hA))
    indices := fun T hT e he => by
      rw [hall'] at hT
      have hTW := ((hd.ctors E₁ hE₁) T (by rw [hall']; exact hT)).1
      exact VExpr.AuxFree.leadFree (hfreeE (VEnv.IsTele.constsSat (VEnv.WF.addConstList henv
        (fun p hp => by obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1)
        hE₁).ordered hTW.indices hPP₁ e he) (hIdx T hT e he))
    fields := fun T hT c hc f hf => by
      rw [hall'] at hT
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hf
      have := (hRI.ctor T hT c hc).fields k f hk
      exact ⟨this.1.leadFree, fun ra hra => ⟨fun A hA => by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hA
        exact ((this.2 ra hra).1 i A hi).leadFree,
        fun e he => ((this.2 ra hra).2 e he).leadFree⟩⟩
    ctorIndices := fun T hT c hc e he => by
      rw [hall'] at hT
      have h1 := (hRI.ctor T hT c hc).indices e he
      have h2 := (((hd.ctors E₁ hE₁) T (by rw [hall']; exact hT)).2 c hc).indices.2
      have h2' : e.mentions d.names = false := by
        have := List.all_eq_true.1 h2 e he; simpa using this
      exact VExpr.AuxFree.leadFree <| (h1.and (VExpr.constsSat_of_mentions h2')).mono
        fun y ⟨hy, hn⟩ => by
          refine ⟨?_, ?_⟩
          · cases h : R y with
            | none => rfl
            | some _ => exact (hn (hy (.inl fun e => by cases e.symm.trans h))).elim
          · cases h : ren y with
            | none => rfl
            | some _ => exact (hn (hy (.inr fun e => by cases e.symm.trans h))).elim
    nested := fun T hT => by rw [hall'] at hT; exact (hd.types T hT).2
    recNames := fun j hj => by
      rw [hall'] at hj
      by_cases hjn : j < n
      · exact (hRI.spec.recOwn j hjn).1
      · exact (hRI.spec.recAux j (by omega) hj).1 }
  obtain ⟨HA, -, -⟩ := VInductDecl.namesApart_of_nodup hdaux (hnames.nodup_iff.1 hnd)
  have hpairk : ∀ k T, d.types[n + k]? = some T → ∃ K o, pairs[k]? = some (K, T.name) ∧
      ns[k]? = some o ∧ OccTr lps (ves.venv (inductSafety isUnsafe)).ContainsLits
        res.params K o := by
    intro k T hT
    obtain ⟨t, ht⟩ : ∃ t, auxs[k]? = some t := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 hT).1; rw [hdlen] at this; omega)⟩
    have hTt := hnmj (n + k) t T (by
      rw [List.getElem?_append_right (by simp [n])]; simpa [n] using ht) hT
    obtain ⟨p, hp, hpt⟩ := hA.getElem?_right ht
    obtain ⟨o, ho, hoc⟩ := hocc.getElem?_left hp
    refine ⟨p.1, o, ?_, ho, hoc⟩
    rw [hp, hTt, hpt.1]
  have hout : ∀ c h ls args out, R c = some h → res.kRepl env' lps c ls args = some out →
      ∃ us, out.getAppFn = .const h.name us := by
    intro c h ls args out hR hk
    obtain ⟨k, T, o, ⟨hT, ho, hc⟩, -⟩ := VInductDecl.auxTable_some hR
    obtain ⟨K, o', hpk, ho', hK⟩ := hpairk k T hT
    rw [ho] at ho'; cases ho'
    have hfind : res.aux2nested.find? T.name = some K := by
      rw [haux2]; exact ElimNestedInductive.auxMap_find? hpnd (List.mem_of_getElem? hpk)
    rcases hc with rfl | ⟨c', hc', rfl⟩
    · obtain rfl := Option.some.inj (hR.symm.trans (VInductDecl.auxTable_type HA hT ho))
      simp only [ElimNestedInductive.Result.kRepl, hfind] at hk; cases hk
      exact hK.inst_head ls args
    · obtain rfl := Option.some.inj (hR.symm.trans (VInductDecl.auxTable_ctor HA hT ho hc'))
      have hnf : res.aux2nested.find? c'.name = none := by
        rw [haux2]
        refine (ElimNestedInductive.foldl_insert_get?_of_not_mem fun hm => ?_).trans rfl
        have : c'.name ∈ d.types.map (·.name) := by
          rw [← hnamesE, List.map_append, List.mem_append]; exact .inr (hpairs ▸ hm)
        obtain ⟨T₁, hT₁, e⟩ := List.mem_map.1 this
        exact HA.apart T₁ hT₁ T (List.mem_of_getElem? hT) c' hc' e.symm
      obtain ⟨c₀, hf, ⟨T', hT', -, -, -, hind, -⟩, -⟩ := hfC (n + k) T hT c' hc'
      rw [hT] at hT'; cases hT'
      have hg : res.getNestedIfAuxCtor env' c'.name = some (K, T.name) := by
        simp [ElimNestedInductive.Result.getNestedIfAuxCtor, hf, hind, hfind]
      obtain ⟨us, hus⟩ := hK.inst_head ls args
      obtain ⟨Ls, Ks, Ds, hK1, -, -⟩ := hK
      simp only [ElimNestedInductive.Result.kRepl, hnf, hg, hus, Option.bind_eq_bind,
        Option.bind_some] at hk
      cases hk
      refine ⟨us, ?_⟩
      have e : cname c'.name = c'.name.replacePrefix T.name o.ind :=
        restoreCtorName_eq hg (by rw [hK1]; exact Expr.getAppFn_mkAppN' _ _)
      show _ = Expr.const (cname c'.name) us
      rw [e, Expr.getAppFn_mkAppN']; rfl
  -- the auxiliary types' occurrences, as the kernel finds them
  have hauxk : ∀ k T, d.types[n + k]? = some T → ∃ K, res.aux2nested.find? T.name = some K ∧
      ∀ c' ∈ T.ctors, res.getNestedIfAuxCtor env' c'.name = some (K, T.name) := by
    intro k T hT
    obtain ⟨K, o, hpk, -, -⟩ := hpairk k T hT
    have hfind : res.aux2nested.find? T.name = some K := by
      rw [haux2]; exact ElimNestedInductive.auxMap_find? hpnd (List.mem_of_getElem? hpk)
    refine ⟨K, hfind, fun c' hc' => ?_⟩
    obtain ⟨c₀, hf, ⟨T', hT', -, -, -, hind, -⟩, -⟩ := hfC (n + k) T hT c' hc'
    rw [hT] at hT'; cases hT'
    simp [ElimNestedInductive.Result.getNestedIfAuxCtor, hf, hind, hfind]
  have hauxName : ∀ {x}, x ∈ auxs.map (·.name) → ∃ k T, d.types[n + k]? = some T ∧ T.name = x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨T, hT⟩ : ∃ T, d.types[n + k]? = some T := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 hk).1; rw [hdlen]; simp [n]; omega)⟩
    exact ⟨k, T, hT, hnmj (n + k) t T (by
      rw [List.getElem?_append_right (by simp [n])]; simpa [n] using hk) hT⟩
  obtain ⟨-, -, hrecApart⟩ := VInductDecl.namesApart_of_nodup hdaux (hnames.nodup_iff.1 hnd)
  have hren1 := (auxRecRen_spec (Ts := rest) hdaux (hnames.nodup_iff.1 hnd) hinfo hall (by
    rw [hdlen]; have : 0 < auxs.length := List.length_pos_iff.2 hauxne; omega)).1
  have hnfk : ∀ T ∈ d.types, ∀ c' ∈ T.ctors, res.aux2nested.find? c'.name = none := by
    intro T hT c' hc'
    rw [haux2]
    refine (ElimNestedInductive.foldl_insert_get?_of_not_mem fun hm => ?_).trans rfl
    have : c'.name ∈ d.types.map (·.name) := by
      rw [← hnamesE, List.map_append, List.mem_append]; exact .inr (hpairs ▸ hm)
    obtain ⟨T₁, hT₁, e⟩ := List.mem_map.1 this
    exact HA.apart T₁ hT₁ T hT c' hc' e.symm
  -- the kernel's restoration tables are `R` and `ren`
  have hS : ∀ Us (E : VEnv), venv ≤ E → (∀ l, E.ContainsLits l → venv.ContainsLits l) →
      RestoreSpec res env' lps (mkAuxRecNameMap env' (I :: rest)).2 Us E.ContainsLits R ren := by
    intro Us E hle hElit
    exact {
      ren_eq := fun _ => rfl
      aux := fun c => by
        refine Bool.eq_iff_iff.2 ⟨fun hc => ?_, fun hc => ?_⟩
        · obtain ⟨h, hR'⟩ := Option.isSome_iff_exists.1 hc
          obtain ⟨k, T, o, ⟨hT, ho, hc'⟩, -⟩ := VInductDecl.auxTable_some hR'
          obtain ⟨K, hfind, hg⟩ := hauxk k T hT
          rcases hc' with rfl | ⟨c', hc', rfl⟩
          · simp only [Bool.or_eq_true]
            exact .inl (ElimNestedInductive.tm_contains_of_get? hfind)
          · simp [hg c' hc']
        · simp only [Bool.or_eq_true] at hc
          rcases hc with hc | hc
          · rw [haux2] at hc
            have hm := (ElimNestedInductive.foldl_insert_contains hc).resolve_left
              (fun h => by cases h)
            rw [hpairs] at hm
            obtain ⟨k, T, hT, rfl⟩ := hauxName hm
            obtain ⟨-, o, -, ho, -⟩ := hpairk k T hT
            exact (show R T.name = _ from VInductDecl.auxTable_type HA hT ho) ▸ rfl
          · obtain ⟨⟨K, a⟩, hg⟩ := Option.isSome_iff_exists.1 hc
            have hC'wf : env'.constants.WF := by rw [hC']; exact insertConsts_wf hCwf hfr hnd
            cases hf : env'.find? c with
            | none => simp [ElimNestedInductive.Result.getNestedIfAuxCtor, hf] at hg
            | some ci =>
              cases ci with
              | ctorInfo c₀ =>
                simp only [ElimNestedInductive.Result.getNestedIfAuxCtor, hf, Option.bind_eq_bind,
                  Option.bind_some] at hg
                obtain ⟨K', hK', -⟩ : ∃ K', res.aux2nested.find? c₀.induct = some K' ∧ True := by
                  cases e : res.aux2nested.find? c₀.induct with
                  | none => simp [e] at hg
                  | some K' => exact ⟨K', rfl, trivial⟩
                have hm := (ElimNestedInductive.foldl_insert_contains
                  (haux2 ▸ ElimNestedInductive.tm_contains_of_get? hK')).resolve_left
                  (fun h => by cases h)
                rw [hpairs] at hm
                obtain ⟨k, T, hT, hTn⟩ := hauxName hm
                obtain ⟨-, o, -, ho, -⟩ := hpairk k T hT
                rw [Kernel.Environment.find?, hC'wf.find?'_eq_find?] at hf
                cases hE : env.constants.find? c with
                | some ci₀ =>
                  have := insertConsts_find?_of_some hCwf hfr hnd hE
                  rw [← hC', hf] at this; cases this
                  obtain ⟨_, _, _, hi, -⟩ := TrEnv'.ctorInfo (wf.tr (safety := .unsafe)) hE
                    DefinitionSafety.unsafe_le
                  obtain ⟨ci', hci'⟩ := (wf.tr (safety := .unsafe)).wf.constants_of_inducts hi
                  obtain ⟨ci'', hf'', -⟩ := (wf.tr (safety := .unsafe)).find?_iff.2 ⟨ci', hci'⟩
                  rw [← hTn, hfrE _ (hmemT (List.mem_of_getElem? hT))] at hf''
                  cases hf''
                | none =>
                  obtain ⟨hcn, -, j, c', hjc, T', hT', -, hcn', -, hind, -⟩ :=
                    AddInductN.find_ctor hflat hCwf hE hf
                  obtain ⟨T'', hT'', hc''⟩ := VInductDecl.mem_ctors_iff.1 hjc
                  rw [hT''] at hT'; cases hT'
                  obtain rfl : j = n + k := HA.type_index hT'' hT (hind.symm.trans hTn.symm)
                  rw [hT] at hT''; cases hT''
                  rw [← hcn, hcn']
                  exact (show R c'.name = _ from VInductDecl.auxTable_ctor HA hT ho hc'') ▸ rfl
              | _ => simp [ElimNestedInductive.Result.getNestedIfAuxCtor, hf] at hg
      ren_aux := fun c hc => by
        cases e : (mkAuxRecNameMap env' (I :: rest)).2.find? c with
        | none => rfl
        | some c' =>
          obtain ⟨j, -, hj, rfl⟩ := hren1 c c' e
          obtain ⟨h, hR'⟩ := Option.isSome_iff_exists.1 hc
          obtain ⟨k, T, o, ⟨hT, -, hc'⟩, -⟩ := VInductDecl.auxTable_some hR'
          obtain ⟨hr1, hr2⟩ := hrecApart j hj
          rcases hc' with e' | ⟨c₁, hc₁, e'⟩
          · exact (hr1 (e' ▸ List.mem_map_of_mem (List.mem_of_getElem? hT))).elim
          · exact (hr2 T (List.mem_of_getElem? hT) c₁ hc₁ e').elim
      n_eq := fun c h hc => by
        obtain ⟨-, -, -, -, e⟩ := VInductDecl.auxTable_some hc
        rw [e, hdpar, hnpar]
      lit := fun l hl c hc => by
        obtain ⟨ci, hci⟩ := VEnv.ContainsLits.constNames henv henvAt.hasPrimitives (hElit l hl) c hc
        refine ⟨?_, ?_⟩
        · cases h : R c with
          | none => rfl
          | some _ => rw [hRI.Rfresh c _ h] at hci; cases hci
        · cases h : (mkAuxRecNameMap env' (I :: rest)).2.find? c with
          | none => rfl
          | some _ => rw [hRI.renfresh c _ h] at hci; cases hci
      repl := by
        have hCL : ∀ l, (ves.venv (inductSafety isUnsafe)).ContainsLits l → E.ContainsLits l :=
          fun l h => VEnv.ContainsLits.mono (hvenv ▸ hle) h
        have hAs : (d.params).length = res.nparams := by rw [hdpar, hnpar]
        refine RestoreSpec.repl_of_nested (fun c h hc => ?_) (fun c nested h hn hc => ?_)
          (fun c nested auxI h hn hg hc => ?_)
        · obtain ⟨k, T, o, ⟨hT, -, hc'⟩, -⟩ := VInductDecl.auxTable_some hc
          obtain ⟨K, hfind, hg⟩ := hauxk k T hT
          rcases hc' with rfl | ⟨c', hc', rfl⟩
          · exact .inl (by rw [hfind]; rfl)
          · exact .inr (by rw [hg c' hc']; rfl)
        · obtain ⟨k, T, o, ⟨hT, ho, hc'⟩, -⟩ := VInductDecl.auxTable_some hc
          obtain ⟨K, hfind, -⟩ := hauxk k T hT
          rcases hc' with rfl | ⟨c', hc', rfl⟩
          · obtain rfl : K = nested := Option.some.inj (hfind.symm.trans hn)
            obtain rfl := Option.some.inj (hc.symm.trans (VInductDecl.auxTable_type HA hT ho))
            obtain ⟨K', o', hpk, ho', hK⟩ := hpairk k T hT
            rw [ho] at ho'; cases ho'
            obtain rfl : K' = K := by
              have := ElimNestedInductive.auxMap_find? hpnd (List.mem_of_getElem? hpk)
              rw [haux2] at hfind; exact Option.some.inj (this.symm.trans hfind)
            obtain ⟨Ls, Ks, Ds, -, hD, hL, hys⟩ := hK
            refine ⟨d.params, hAs, ?_⟩
            rw [hD]
            exact (PTr.mkAppN_const hL (hys _ (by rw [hparams]; simpa [hxl] using hdpar))).mono_lit hCL
          · rw [hnfk T (List.mem_of_getElem? hT) c' hc'] at hn; cases hn
        · obtain ⟨k, T, o, ⟨hT, ho, hc'⟩, -⟩ := VInductDecl.auxTable_some hc
          obtain ⟨K, hfind, hgK⟩ := hauxk k T hT
          rcases hc' with rfl | ⟨c', hc', rfl⟩
          · rw [hfind] at hn; cases hn
          · rw [hgK c' hc'] at hg
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hg)
            obtain rfl := Option.some.inj (hc.symm.trans (VInductDecl.auxTable_ctor HA hT ho hc'))
            obtain ⟨K', o', hpk, ho', hK⟩ := hpairk k T hT
            rw [ho] at ho'; cases ho'
            obtain rfl : K' = K := by
              have := ElimNestedInductive.auxMap_find? hpnd (List.mem_of_getElem? hpk)
              rw [haux2] at hfind; exact Option.some.inj (this.symm.trans hfind)
            obtain ⟨Ls, Ks, Ds, hK1, hD, hL, hys⟩ := hK
            refine ⟨o.ind, Ls, Ds, d.params, hD, ?_, hAs, ?_⟩
            · exact restoreCtorName_eq (hgK c' hc') (by rw [hK1]; exact Expr.getAppFn_mkAppN' _ _)
            · exact (PTr.mkAppN_const hL (hys _ (by rw [hparams]; simpa [hxl] using hdpar))).mono_lit
                hCL }
  -- what the final phase adds is its step
  have hAux : ∀ T ∈ (d.restoreNested R ren n ns cname).aux, ∃ o, T.nested = some o ∧
      ∀ env₀, venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some env₀ →
        T.AuxWF env₀ (d.restoreNested R ren n ns cname) o :=
    nested_auxWF wf hvenv henvAt hd hdaux hflat hE₁ hEl hnp hfrE hU hUs hdpar hcl hrun hoI hxl hxnd
      hparams hnpar hA haux2 hclAll hTD hF hpairs hpnd hT' hfT
      (fun i T hT c hc => let ⟨c₀, a, b, c', _⟩ := hfC i T hT c hc; ⟨c₀, a, b, c'⟩) hnmj hdlen hcname
      (hvenv ▸ hocc) hnsl hin' hRI (hvenv ▸ htyTr) hS hcL hnamesR hlpk hnn
  have hdN : (d.restoreNested R ren n ns cname).WF venv :=
    VInductDecl.RestoreSpec.wf henv hRI.spec hd hRI.n_pos hRI.Rfresh hRI.renfresh hRI.Rdom
      hRI.renNames hRI.ctorNames hE₁ hIdx hAux hRI.ctor
  -- carrying the translation's judgments over a constructor's parameters to the restored block
  have hHE : ∀ E₁' E₀, venv.addConstList d.typeConsts = some E₁' →
      venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some E₀ →
      ∀ Qs, E₀.IsTele d.uvars [] Qs → E₀.TeleDefEq d.uvars [] Qs d.params →
      ∃ F, RestoreEnv E₁' E₀ lps.length F R (VLevel.params lps.length) Qs.reverse := by
    intro E₁' E₀ h1 h0 Qs hQ hQP
    have := hRI.spec.restoreEnv henv hRI.Rfresh hRI.renfresh hRI.Rdom hd.params
      (fun T hT => (hd.types T hT).1) h1 h0
      (fun T hT => let ⟨o, h1', h2'⟩ := hAux T hT; ⟨o, h1', h2' E₀ h0⟩) hQ hQP
    rw [hU] at this
    exact ⟨_, this⟩
  have hrenE : ∀ E₁', venv.addConstList d.typeConsts = some E₁' → ∀ c, ren c ≠ none →
      E₁'.constants c = none := by
    intro E₁' h1 c hc
    obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.1 hc
    cases h : E₁'.constants c with
    | none => rfl
    | some ci =>
      rcases VEnv.addConstList_constants_cases h1 h with h' | h'
      · rw [hRI.renfresh c c' hc'] at h'; cases h'
      · obtain ⟨T, hT, e⟩ := List.mem_map.1 h'
        cases e
        exact (hRI.renNames _ c' hc' (List.mem_map_of_mem hT)).elim
  -- where the kernel's restoration replaces
  have hpsz : res.params.size = d.params.length := by rw [hparams]; simpa [hxl] using hdpar.symm
  have hK : ∀ c K, res.aux2nested.find? c = some K → ∃ J Ls Ds,
      K.abstract res.params = Expr.mkAppList (.const J Ls) Ds ∧
        ∀ D ∈ Ds, D.looseBVarRange' ≤ d.params.length := by
    intro c K hc
    have hm : (K, c) ∈ pairs := by
      rw [haux2] at hc
      exact (foldl_insert_getElem?_mem {} hc).resolve_left (by simp)
    obtain ⟨o, -, Ls, Ks, Ds, -, hD, -, hys⟩ := Lean4Lean.List.Forall₂.forall_exists_l hocc _ hm
    refine ⟨o.ind, Ls, Ds.toList, by rw [hD, Expr.mkAppN_eq_mkAppList], fun D hD' => ?_⟩
    obtain ⟨y, -, hy⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (hys (List.replicate res.params.size (.sort .zero)) (by simp)) D hD'
    refine hy.looseBVarRange_le fun i p h => ?_
    obtain ⟨j, hj, e, -⟩ := paramCtx_find? h
    cases e
    simpa [hpsz] using hj
  have hPF := (hS lps venv VEnv.LE.rfl fun _ h => h).placedFn (by rw [hnpar, hdpar]) hK
  -- the own constructors' types have their auxiliary constants placed after the parameters
  have hpa : ∀ p ∈ pairs, (R p.2).isSome := by
    intro p hp
    have hm : p.2 ∈ auxs.map (·.name) := hpairs ▸ List.mem_map_of_mem hp
    obtain ⟨k, T₂, hT₂, e⟩ := hauxName hm
    obtain ⟨-, o, -, ho, -⟩ := hpairk k T₂ hT₂
    rw [← e]; exact (show R T₂.name = _ from VInductDecl.auxTable_type HA hT₂ ho) ▸ rfl
  have hpl : ∀ (j : Nat) T, j < n → d.types[j]? = some T → ∀ c ∈ T.ctors, ∀ c₀,
      env'.find? c.name = some (.ctorInfo c₀) →
      ElimNestedInductive.PlacedAfter (fun c => (R c).isSome) (lps.map .param)
        d.params.length d.params.length c₀.type ∧
      c₀.type.anySub (constP fun c =>
        ((mkAuxRecNameMap env' (I :: rest)).2.find? c).isSome) = false := by
    intro j T hj hT c hc c₀ hf₀
    obtain ⟨t, ht⟩ : ∃ t, (I :: rest)[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
    have ht₁ : (I :: rest ++ auxs)[j]? = some t := by
      rw [List.getElem?_append_left hj]; exact ht
    obtain ⟨t', ht', hD⟩ := hTD.getElem?_left ht₁
    obtain ⟨T'', hT'', hE⟩ := hEl.types.getElem?_left ht'
    rw [hT] at hT''; cases hT''
    obtain ⟨ct, hct, hce⟩ := Lean4Lean.List.Forall₂.forall_exists_r hE.2 c hc
    have hty := hcty t' (List.mem_of_getElem? ht') ct hct c₀ (hce.1 ▸ hf₀)
    obtain ⟨ct₀, hct₀, hCD⟩ := Lean4Lean.List.Forall₂.forall_exists_r hD.2.2 ct hct
    have htm : t ∈ I :: rest := List.mem_of_getElem? ht
    have hin₀ := hin' t (List.mem_append_left _ htm) ct₀ hct₀
    obtain ⟨B, hB, hpeel, hAP⟩ := hCD.placed (isAux := fun c => (R c).isSome) hpa hin₀
      ((hcl t htm).2.2 ct₀ hct₀).2.1
    refine ⟨?_, ?_⟩
    · rw [hty, hB, hdpar]
      exact ElimNestedInductive.placedAfter_setBody hAP hpeel hin₀
    · obtain ⟨c₀', hf₀', -, ⟨-, -, htr⟩, -⟩ := hfC j T hT c hc
      rw [hf₀] at hf₀'; cases hf₀'
      refine TrExprS.anySub_constP (fun x hx => ?_) htr
      refine hrenE envT' hT' x ?_
      rw [(hS lps venv VEnv.LE.rfl fun _ h => h).ren_eq]
      intro h; rw [h] at hx; cases hx
  -- the occurrences restoring puts back translate over the parameters
  have hocc' : ∀ E₀, venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some E₀ →
      ∀ Qs, E₀.IsTele d.uvars [] Qs → E₀.TeleDefEq d.uvars [] Qs d.params →
      ∀ c, (R c).isSome → ∃ Y, TrExprS E₀ lps (paramVLCtx Qs)
        ((Expr.mkAppList (.const c (lps.map .param))
          (ElimNestedInductive.bvs d.params.length 0)).replaceNoCache
          (ElimNestedInductive.Result.restoreFn res env' lps
            (mkAuxRecNameMap env' (I :: rest)).2)) Y := by
    have htyTr' := hvenv ▸ htyTr
    obtain ⟨r0, hr0, hTD0⟩ := hTD.getElem?_left (i := 0) (a := I) rfl
    obtain ⟨T0, -, hty0, hag0⟩ := htyTr'.getElem?_left hr0
    rw [hTD0.2.1] at hty0 hag0
    have hpeelI := hoI.peel hxnd fun x _ => Expr.SuppIn.mono
      (S := ElimNestedInductive.FVOnly fun _ => False) (S' := ElimNestedInductive.FVOnly (· ≠ x))
      ⟨fun _ h => h.elim, fun _ => id, fun _ => id⟩ (hcl I (.head _)).1
    have hlfI : xs.length ≤ I.type.leadingForalls := le_leadingForalls_of_peel hpeelI
    obtain ⟨Qs₀, B₀, hQB, hQl⟩ :=
      VExpr.exists_foralls_of_le xs.length T0.type (Nat.le_trans hlfI hty0.leadingForalls_le)
    have hQ₀ : venv.TeleDefEq d.uvars [] Qs₀ d.params :=
      hag0 (by rw [hdpar, ← hxl]; exact hlfI) Qs₀ B₀ hQB (by rw [hQl, hxl, hdpar])
    intro E₀ h0 Qs hQ hQP c hc
    have hle₀ := VEnv.addConstList_le h0
    have henv₀ : E₀.WF := VEnv.WF.addConstList henv (fun p hp => by
      obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
      exact (hdN.types T' hT').1) h0
    have hVT₀ : VEnvAt envT (inductSafety isUnsafe) E₀ :=
      typeAx_venvAt hF henvAt hflat hd hRI.spec rfl (by simp) hnn hRI.Rfresh hRI.renfresh hnamesR
        rfl hlpk h0
    have hI0 : TrExprS E₀ lps [] I.type (.foralls Qs₀ B₀) := hQB ▸ hty0.mono hle₀
    have hOT := nested_occs_tr wf hcl hrun hoI hxnd hparams hA haux2 hpnd hF hVT₀ hQl hI0
    have hP₀ : E₀.IsTele d.uvars [] d.params := hd.params.mono hle₀
    have hΔ₁ := (paramVLCtx_isDefEq henv₀ (hQ₀.mono hle₀) hP₀ trivial (Δ₁ := []) (Δ₂ := []) rfl
      .nil).symm
    have hΔ₂ := paramVLCtx_isDefEq henv₀ hQP hP₀ trivial (Δ₁ := []) (Δ₂ := []) rfl .nil
    simp only [List.append_nil] at hΔ₁ hΔ₂
    rw [hU] at hΔ₁ hΔ₂
    have S := hS lps venv VEnv.LE.rfl fun _ h => h
    refine S.occ_tr (by rw [hnpar, hdpar]) hK hUs henv₀.ordered (fun l h => h.mono hle₀)
      hQP.length_eq (by simpa [hU] using hQ.onCtx trivial)
      (fun c h hc => by rw [S.n_eq c h hc, hnpar, hdpar]) (fun c h hc => ?_)
      (fun a K J Ls Ds hfa hD D hDm => ?_) hc
    · obtain ⟨F, HE⟩ := hHE E₁ E₀ hE₁ h0 Qs hQ hQP
      exact HE.inst_wf hc
    · have hm : (K, a) ∈ pairs := by
        rw [haux2] at hfa
        exact (foldl_insert_getElem?_mem {} hfa).resolve_left (by simp)
      obtain ⟨J', Ls', Ks, hK', hKs⟩ := hOT _ hm
      simp only at hK'
      have e1 : K.abstract res.params =
          Expr.mkAppList (.const J' Ls') (Ks.toList.map (·.abstract' xs)) := by
        rw [hK', hparams]
        show (mkAppN (.const J' Ls') Ks).abstract ⟨xs.map .fvar⟩ = _
        rw [Expr.abstract_eq', Expr.mkAppN_eq_mkAppList, Expr.abstract'_mkAppList]
        rfl
      have e2 := congrArg Expr.getAppArgs (hD.symm.trans e1)
      rw [Expr.getAppArgs_mkAppList_const, Expr.getAppArgs_mkAppList_const] at e2
      have e3 : Ds = Ks.toList.map (·.abstract' xs) := by simpa using e2
      rw [e3] at hDm
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hDm
      obtain ⟨k', hk'⟩ := hKs k hk
      obtain ⟨k₂, h2⟩ := TrExprS.defeqDFC henv₀ (hΔ₁ henv₀.ordered) hk'
      exact TrExprS.defeqDFC henv₀ hΔ₂ h2
  obtain ⟨venvF, hstep⟩ := nestedAddInduct (d := d) (R := R) (ren := ren) (n := n) (ns := ns)
    (cname := cname) hF henvAt hflat hd hRI.spec hdN rfl hRI.n_pos hns hnn hS
    hP hcL hRI.Rfresh hRI.renfresh hout (fun _ _ _ _ _ => rfl) hnamesR hSN hM rfl hlit hlpk
    hHE hPF hocc' hpl hRI.litR hrenE hUs (by rw [hnpar, hdpar])
  have hu' : (d.restoreNested R ren n ns cname).isUnsafe = isUnsafe := hu
  have hdecl : (d.restoreNested R ren n ns cname).WF
      (ves.venv (inductSafety (d.restoreNested R ren n ns cname).isUnsafe)) := by
    rw [hu', hvenv]; exact hdN
  have H : AddInduct (inductSafety (d.restoreNested R ren n ns cname).isUnsafe) env.constants
      (ves.venv (inductSafety (d.restoreNested R ren n ns cname).isUnsafe))
      (d.restoreNested R ren n ns cname) envF.constants venvF := by
    rw [hu', hvenv]; exact hstep
  obtain ⟨cisF, hpF, hCF, hndF, hfrF, hpF', hq'⟩ := hF.addConsts hCwf
  have hnpF : ∀ x ∈ ((d.restoreNested R ren n ns cname).typeConsts ++
      (d.restoreNested R ren n ns cname).ctorConsts ++
      (d.restoreNested R ren n ns cname).recConsts).map (·.1),
      Environment.primitives.contains x = false := by
    intro x hx
    obtain ⟨cis', hC'', hnd', hfr', -, hnames'⟩ := AddInductN.names hstep
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 (hnames'.mem_iff.2 hx)
    have h1 : envF.constants.find? ci.name = some ci := by
      rw [hC'']; exact insertConsts_find?_of_mem hCwf hfr' hnd' hci
    rw [hCF] at h1
    have hfrF' : ∀ c ∈ cisF, env.constants.find? c.name = none :=
      fun c hc => hfrF c (hpF.mem_iff.1 hc)
    rcases insertConsts_find? hCwf hfrF' ((hpF.map _).nodup_iff.2 hndF) h1 with h | ⟨hm, -⟩
    · rw [hfr' ci hci] at h; cases h
    · cases h : Environment.primitives.contains ci.name
      · rfl
      · exact absurd (hpF' ci (hpF.mem_iff.1 hm) h) (by decide)
  refine addInductBlock.WF wf hdecl H hq' (fun _ _ _ H' => H'.hasPrimitives hnpF)
    fun {x ci} hx hxp => ?_
  obtain ⟨cis, hC', hnd, hfr, -, hnames⟩ := H.names
  have hC₁ := (wf.tr (safety := .safe)).map_wf
  rw [Kernel.Environment.find?, hC', (insertConsts_wf hC₁ hfr hnd).find?'_eq_find?] at hx
  rcases insertConsts_find? hC₁ hfr hnd hx with hx | hx
  · exact wf.safePrimitives (by rwa [Kernel.Environment.find?, hC₁.find?'_eq_find?]) hxp
  · have := hnpF x (hnames.mem_iff.1 (hx.2 ▸ List.mem_map_of_mem hx.1))
    simp_all

theorem addInductive.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (hallow : allowPrimitive → Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF
      fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rw [Environment.addInductive_eq]
  refine Except.WF.bind (addInductive_inputChecks.WF env types) fun _ hcl => ?_
  refine Except.WF.bind (Q := fun res => (ElimNestedInductive.run fuel.inductiveFuel nparams types
      env).run' { lvls := lparams.map .param, newTypes := types.toArray } = .ok res)
    (fun _ h => h) fun res hrun => ?_
  refine Except.WF.bind (auxNameCheck.WF res types) fun _ hin => ?_
  by_cases h0 : res.aux2nested.size = 0
  · have ⟨hn, h0'⟩ := ElimNestedInductive.run_flat hrun rfl h0
    have hne := ElimNestedInductive.run_ne_nil hrun
    have hne' : res.types ≠ [] := fun h => hne (by simpa [h] using hn.symm)
    have hallow' : allowPrimitive →
        Primitive.PrimitiveInductiveResult lparams nparams res.types isUnsafe := fun hp => by
      have := hallow hp; rwa [h0' this.2.2.1]
    simp only [h0]
    exact (AddInductive.run.WF wf lparams nparams res.types isUnsafe allowPrimitive fuel
      hne' hallow').bind fun _ h => .pure (FlatResult.ves wf h)
  · cases allowPrimitive with
    | true => exact (h0 (PrimitiveInductiveResult.flat (hallow rfl) hrun)).elim
    | false =>
      have hne' : res.types ≠ [] := by
        obtain ⟨I, rest, rfl, xs, body, -, -, -, -, -, auxs, pairs, -, -, -, hD, -⟩ :=
          ElimNestedInductive.run_spec (ElimNestedInductive.EnvClosed.of_tr (wf.tr (safety := .unsafe)))
            hcl hrun
        intro h; have := Lean4Lean.List.Forall₂.length_eq hD; rw [h] at this; simp at this
      refine Except.WF.bind (AddInductive.run.WF_nonPrimitive wf lparams nparams
        res.aux2nested.size res.types isUnsafe fuel hne') fun env' hFR => ?_
      simp only [h0, if_false]
      exact fun envF hfin => addInductive.WF_nested wf hcl hrun h0 hin hFR hfin

end Lean4Lean

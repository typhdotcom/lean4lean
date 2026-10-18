import Lean4Lean.Verify.Environment.NestedOccs

/-!
# The auxiliary types of a restored nested block

Each auxiliary type of the restored block is its occurrence's type instantiated there
(`VInductiveType.AuxWF`), from the elimination, the flat check of the translation and the final
phase's check of the occurrences.
-/

/-! ### Names: an auxiliary constructor's name, restored -/

namespace Lean.Name

/-- The number of components of a name. -/
def plen : Name → Nat
  | .anonymous => 0
  | .str p _ | .num p _ => p.plen + 1

theorem isPrefixOf_plen {P : Name} : ∀ {x : Name}, P.isPrefixOf x = true → P.plen ≤ x.plen
  | .anonymous, h => by
    simp only [isPrefixOf, beq_iff_eq] at h; subst h; exact Nat.le_refl _
  | .str p _, h | .num p _, h => by
    simp only [isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (isPrefixOf_plen h)

theorem replacePrefix_of_not_isPrefixOf {P A : Name} :
    ∀ {x : Name}, P.isPrefixOf x = false → x.replacePrefix P A = x
  | .anonymous, h => by
    cases P with
    | anonymous => simp [isPrefixOf] at h
    | str => rfl
    | num => rfl
  | .str p s, h => by
    simp only [isPrefixOf, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    simp only [replacePrefix, beq_iff_eq, if_neg (Ne.symm h.1), replacePrefix_of_not_isPrefixOf h.2,
      Name.mkStr]
  | .num p k, h => by
    simp only [isPrefixOf, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    simp only [replacePrefix, beq_iff_eq, if_neg (Ne.symm h.1), replacePrefix_of_not_isPrefixOf h.2,
      Name.mkNum]

theorem replacePrefix_self (x P : Name) : x.replacePrefix x P = P := by
  cases x <;> simp [replacePrefix]

theorem plen_replacePrefix {P A : Name} : ∀ {x : Name}, P.isPrefixOf x = true →
    (x.replacePrefix P A).plen + P.plen = x.plen + A.plen
  | .anonymous, h => by
    simp only [isPrefixOf, beq_iff_eq] at h; subst h; simp [replacePrefix, plen]
  | .str p s, h => by
    by_cases e : Name.str p s = P
    · subst e; rw [replacePrefix_self]; omega
    · simp only [isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h := h.resolve_left (Ne.symm e)
      simp only [replacePrefix, beq_iff_eq, if_neg e, Name.mkStr, plen]
      have := plen_replacePrefix (A := A) h; omega
  | .num p k, h => by
    by_cases e : Name.num p k = P
    · subst e; rw [replacePrefix_self]; omega
    · simp only [isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h := h.resolve_left (Ne.symm e)
      simp only [replacePrefix, beq_iff_eq, if_neg e, Name.mkNum, plen]
      have := plen_replacePrefix (A := A) h; omega

/-- Replacing a prefix and putting it back gives the name back. -/
theorem replacePrefix_replacePrefix {P A : Name} : ∀ {x : Name}, P.isPrefixOf x = true →
    (x.replacePrefix P A).replacePrefix A P = x
  | .anonymous, h => by
    simp only [isPrefixOf, beq_iff_eq] at h; subst h; simp [replacePrefix, replacePrefix_self]
  | .str p s, h => by
    by_cases e : Name.str p s = P
    · subst e; rw [replacePrefix_self, replacePrefix_self]
    · simp only [isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h := h.resolve_left (Ne.symm e)
      have hl := plen_replacePrefix (A := A) h
      have hP := isPrefixOf_plen h
      simp only [replacePrefix, beq_iff_eq, if_neg e, Name.mkStr]
      rw [if_neg (fun e' => by have := congrArg plen e'; simp only [plen] at this; omega),
        replacePrefix_replacePrefix h]
  | .num p k, h => by
    by_cases e : Name.num p k = P
    · subst e; rw [replacePrefix_self, replacePrefix_self]
    · simp only [isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h := h.resolve_left (Ne.symm e)
      have hl := plen_replacePrefix (A := A) h
      have hP := isPrefixOf_plen h
      simp only [replacePrefix, beq_iff_eq, if_neg e, Name.mkNum]
      rw [if_neg (fun e' => by have := congrArg plen e'; simp only [plen] at this; omega),
        replacePrefix_replacePrefix h]

end Lean.Name

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem VExpr.exists_foralls_of_le : ∀ (n : Nat) (e : VExpr), n ≤ e.forallsCount →
    ∃ As B, e = .foralls As B ∧ As.length = n
  | 0, e, _ => ⟨[], e, rfl, rfl⟩
  | n + 1, .forallE A b, h => by
    obtain ⟨As, B, rfl, hl⟩ := exists_foralls_of_le n b (by simp [VExpr.forallsCount] at h; omega)
    exact ⟨A :: As, B, rfl, by simp [hl]⟩
  | _ + 1, .bvar .., h | _ + 1, .sort .., h | _ + 1, .const .., h | _ + 1, .app .., h
  | _ + 1, .lam .., h | _ + 1, .proj .., h => by simp [VExpr.forallsCount] at h

theorem PTr.eqv {Us : List Name} {CL : Literal → Prop} {Δ : VLCtx} {e₁ e₂ : Expr} {e' : VExpr}
    (H : PTr Us CL Δ e₁ e') : e₁ == e₂ → PTr Us CL Δ e₂ e' := by
  simp [(· == ·)]
  induction H generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; grind [PTr]

theorem anySub_constP_eqv {f : Name → Bool} {e₁ e₂ : Expr} :
    e₁ == e₂ → e₁.anySub (constP f) = e₂.anySub (constP f) := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv', Expr.anySub, constP]
  all_goals grind

theorem constsOK_of_anySub {f : Name → Bool} :
    ∀ {e : Expr}, e.anySub (constP f) = false → e.ConstsOK fun c _ => f c = false := by
  intro e h
  induction e <;> simp_all [Expr.anySub, constP, Expr.ConstsOK]

theorem VExpr.LeadFree.ren_none {R : Name → Option VAuxHead} {ren : Name → Option Name} :
    ∀ {e : VExpr}, e.LeadFree R ren → e.LeadFree R fun _ => none
  | .bvar _, _ | .sort _, _ | .const .., _ => trivial
  | .app f a, h => by
    unfold VExpr.LeadFree at h ⊢
    split at h
    · exact fun c ls xs he x hx => (h c ls xs he x hx).mono fun _ h => ⟨h.1, rfl⟩
    · exact ⟨ren_none h.1, ren_none h.2⟩
  | .lam A b, h | .forallE A b, h => ⟨ren_none h.1, ren_none h.2⟩
  | .proj _ _ e, h => ren_none (e := e) h

/-- The kernel's restoration tables, without the renaming of recursors. -/
theorem RestoreSpec.noRen {r : ElimNestedInductive.Result} {env' : Kernel.Environment}
    {lparams : List Name} {auxRec : NameMap Name} {Us : List Name} {CL : Literal → Prop}
    {R : Name → Option VAuxHead} {ren : Name → Option Name}
    (S : RestoreSpec r env' lparams auxRec Us CL R ren) :
    RestoreSpec r env' lparams {} Us CL R fun _ => none where
  ren_eq _ := rfl
  aux := S.aux
  ren_aux _ _ := rfl
  n_eq := S.n_eq
  lit l hl c hc := ⟨(S.lit l hl c hc).1, rfl⟩
  repl := S.repl

/-- The types of a mutual block are all safe or all unsafe. -/
theorem inductInfo_all_isUnsafe {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {I J : Name} {Iv Jv : InductiveVal} (hI : env.find? I = some (.inductInfo Iv))
    (hJ : env.find? J = some (.inductInfo Jv)) (hJI : J ∈ Iv.all) :
    Iv.isUnsafe = Jv.isUnsafe := by
  have H := wf.tr (safety := .unsafe)
  have hC := H.map_wf
  rw [Kernel.Environment.find?, hC.find?'_eq_find?] at hI hJ
  obtain ⟨dI, tI, TI, hindI, -, hivI, -⟩ := H.inductInfo hI DefinitionSafety.unsafe_le
  obtain ⟨dJ, tJ, TJ, hindJ, -, hivJ, -⟩ := H.inductInfo hJ DefinitionSafety.unsafe_le
  have hJmem : J ∈ dI.names := by rw [← hivI.2.2.2.2.1]; exact hJI
  obtain ⟨T', hT'm, hT'n⟩ := List.mem_map.1 hJmem
  obtain ⟨t', ht'⟩ := List.mem_iff_getElem?.1 hT'm
  have h := H.wf.inducts_getElem hindI ht'
  have hJn : Jv.name = J := H.aligned.find?_name hJ
  rw [hT'n, ← hJn, hindJ] at h
  cases h
  exact hivI.2.2.2.2.2.2.2.2.trans hivJ.2.2.2.2.2.2.2.2.symm

/-- The auxiliary types of the block the final phase restores are well formed: each stands for its
occurrence `o`, with that type's constructors instantiated there. The hypotheses are what the nested
branch of `addInductive` has once the translation is checked flat (`hflat`, `hfT`, `hfC`, `hEl`),
the elimination's facts (`run_spec`), the final phase's checks (`hF`), the occurrences' translations
(`hocc`) and the restoration's inputs (`hRI`). -/
theorem nested_auxWF {env : Environment} {ves : VEnvs} (wf : ves.WF env) {nparams : Nat}
    {isUnsafe : Bool} {fuel : FuelConfig} {res : ElimNestedInductive.Result}
    {env' envF : Environment} {d : VInductDecl} {venv' : VEnv} {venv : VEnv}
    (hvenv : ves.venv (inductSafety isUnsafe) = venv) (henvAt : VEnvAt env (inductSafety isUnsafe) venv)
    (hd : d.WF venv) (hdaux : d.aux = [])
    (hflat : AddInductN res.aux2nested.size (inductSafety isUnsafe) env.constants venv d
      env'.constants venv')
    {E₁ : VEnv} (hE₁ : venv.addConstList d.typeConsts = some E₁)
    {lps : List Name} {level : VLevel} (hEl : AddInductive.Elaborates E₁ lps nparams level res.types d)
    (hnp : ∀ n ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1),
      Environment.primitives.contains n = false)
    (hfrE : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1), env.find? x = none)
    (hU : d.uvars = lps.length) (hUs : lps.Nodup) (hdpar : d.params.length = nparams)
    {I : InductiveType} {rest : List InductiveType}
    (hcl : ∀ T ∈ I :: rest, ElimNestedInductive.TypeClosed T)
    (hrun : (ElimNestedInductive.run fuel.inductiveFuel nparams (I :: rest) env).run'
      { lvls := lps.map .param, newTypes := (I :: rest).toArray } = .ok res)
    {xs : List FVarId} {body : Expr} (hoI : ElimNestedInductive.Opens {} I.type xs res.lctx body)
    (hxl : xs.length = nparams) (hxnd : xs.Nodup) (hparams : res.params = (xs.map .fvar).toArray)
    (hnpar : res.nparams = nparams) {auxs : List InductiveType} {pairs : List (Expr × Name)}
    (hA : List.Forall₂ (fun e T => ElimNestedInductive.AuxMade env res.params nparams (e, T))
      pairs auxs)
    (haux2 : res.aux2nested = pairs.foldl (fun m (e, n) => m.insert n e) {})
    (hclAll : ∀ T ∈ I :: rest ++ auxs, ElimNestedInductive.TypeClosed T)
    (hTD : List.Forall₂ (ElimNestedInductive.TypeDone pairs (lps.map .param) res.params nparams)
      (I :: rest ++ auxs) res.types)
    {inds : List (InductiveVal × List ConstructorVal)} {recs : List RecursorVal} {envT : Environment}
    (hF : NestedFinalOK env env' lps (I :: rest) res isUnsafe false fuel inds recs envT envF)
    (hpairs : pairs.map (·.2) = auxs.map (·.name)) (hpnd : (pairs.map (·.2)).Nodup)
    {envT' : VEnv} (hT' : venv.addConstList d.typeConsts = some envT')
    (hfT : ∀ (i : Nat) (T : VInductiveType), d.types[i]? = some T → ∃ v,
      env'.find? T.name = some (.inductInfo v) ∧ TrInductValN d lps res.aux2nested.size T v ∧
      TrConstant (inductSafety isUnsafe) venv (.inductInfo v) ⟨d.uvars, T.type⟩ ∧
      (d.params.length ≤ v.type.leadingForalls → ∀ (ps : List VExpr) (B : VExpr),
        T.type = .foralls ps B → ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params))
    (hfC : ∀ (i : Nat) (T : VInductiveType), d.types[i]? = some T → ∀ c ∈ T.ctors, ∃ c₀,
      env'.find? c.name = some (.ctorInfo c₀) ∧ TrCtorVal d lps i c c₀ ∧
      TrConstant (inductSafety isUnsafe) envT' (.ctorInfo c₀) ⟨d.uvars, c.type⟩)
    (hnmj : ∀ (j : Nat) (t : InductiveType) (T : VInductiveType), (I :: rest ++ auxs)[j]? = some t →
      d.types[j]? = some T → T.name = t.name)
    (hdlen : d.types.length = (I :: rest).length + auxs.length)
    (hcname : ∀ j T, j < (I :: rest).length → d.types[j]? = some T → ∀ c ∈ T.ctors,
      res.restoreCtorName env' c.name = c.name)
    {ns : List VNested}
    (hocc : List.Forall₂ (fun p o => OccTr lps venv.ContainsLits res.params p.1 o) pairs ns)
    (hnsl : ns.length = auxs.length)
    (hin' : ∀ T ∈ I :: rest ++ auxs, ∀ c ∈ T.ctors, c.type.anySub
      (constP fun x => (d.auxTable (I :: rest).length ns (res.restoreCtorName env') x).isSome) = false)
    (hRI : RestoreInputs venv d (d.auxTable (I :: rest).length ns (res.restoreCtorName env'))
      (auxRecRen env' (I :: rest)) (I :: rest).length ns (res.restoreCtorName env'))
    (htyTr : List.Forall₂ (fun (t : InductiveType) (T : VInductiveType) =>
      TrExprS venv lps [] t.type T.type ∧
      (d.params.length ≤ t.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
        ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params)) res.types d.types)
    (hS : ∀ Us (E : VEnv), venv ≤ E → (∀ l, E.ContainsLits l → venv.ContainsLits l) →
      RestoreSpec res env' lps (mkAuxRecNameMap env' (I :: rest)).2 Us E.ContainsLits
        (d.auxTable (I :: rest).length ns (res.restoreCtorName env')) (auxRecRen env' (I :: rest)))
    (hcL : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.type.LeadFree
      (d.auxTable (I :: rest).length ns (res.restoreCtorName env')) (auxRecRen env' (I :: rest)))
    (hnamesR : (I :: rest).map (·.name) = (d.restoreNested
      (d.auxTable (I :: rest).length ns (res.restoreCtorName env')) (auxRecRen env' (I :: rest))
      (I :: rest).length ns (res.restoreCtorName env')).names)
    (hlpk : ∀ t ∈ I :: rest, ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      ind.levelParams = lps)
    (hnn : res.aux2nested.size = ns.length) :
    let R := d.auxTable (I :: rest).length ns (res.restoreCtorName env')
    let ren := auxRecRen env' (I :: rest)
    let dN := d.restoreNested R ren (I :: rest).length ns (res.restoreCtorName env')
    ∀ T ∈ dN.aux, ∃ o, T.nested = some o ∧
      ∀ env₀, venv.addConstList dN.typeConsts = some env₀ → T.AuxWF env₀ dN o := by
  intro R ren dN T hT
  have henv := henvAt.tr.wf
  have hO := henv.ordered
  have hCwf : env.constants.WF := henvAt.tr.map_wf
  -- `T` is the translated auxiliary type at `n + k`, restored
  change T ∈ ((d.types.zipIdx.drop (I :: rest).length).map fun p =>
    p.1.restore R ren (res.restoreCtorName env') (nestedAt (I :: rest).length ns p.2)) at hT
  obtain ⟨⟨Td, j⟩, hm, rfl⟩ := List.mem_map.1 hT
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hm
  rw [List.getElem?_drop, List.getElem?_zipIdx] at hk
  obtain ⟨Td', hTd, e⟩ := Option.map_eq_some_iff.1 hk
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hkl : k < auxs.length := by
    have := (List.getElem?_eq_some_iff.1 hTd).1; rw [hdlen] at this; omega
  obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hnest : nestedAt (I :: rest).length ns ((I :: rest).length + k) = some o := by
    simp [nestedAt, ho]
  simp only [Nat.zero_add, hnest]
  refine ⟨o, rfl, fun env₀ henv₀ => ?_⟩
  -- the auxiliary type the elimination made, its record, and its occurrence
  obtain ⟨t, ht⟩ : ∃ t, auxs[k]? = some t := ⟨_, List.getElem?_eq_getElem hkl⟩
  have ht' : (I :: rest ++ auxs)[(I :: rest).length + k]? = some t := by
    rw [List.getElem?_append_right (by simp)]; simpa using ht
  obtain ⟨rk, hrk, hTDk⟩ := hTD.getElem?_left ht'
  obtain ⟨Td2, hTd2, hElk⟩ := hEl.types.getElem?_left hrk
  rw [hTd] at hTd2; cases hTd2
  obtain ⟨Td3, hTd3, htyk, hagk⟩ := htyTr.getElem?_left hrk
  rw [hTd] at hTd3; cases hTd3
  obtain ⟨p, hp, hAk⟩ := hA.getElem?_right ht
  obtain ⟨o', ho', hoc⟩ := hocc.getElem?_left hp
  rw [ho] at ho'; cases ho'
  obtain ⟨htn, cty, xsA, lctx, body, hoA, hxsAl, hxsAnd, hxA, hxAp, hctyF, hctyB, hC⟩ := hAk
  obtain ⟨J, Ls, args, nI, Jv, v, hK, hJ, hnI, hlb, hargsS, hargsF, hLsM, hargsC, hv, htyv,
    hfresh, hctorsC, I', Iv, hI', hJI, hnIv⟩ := hC
  have hxxA : xs.length = xsA.length := hxl.trans hxsAl.symm
  have hargsA : ∀ a ∈ args.toList, a.SuppIn (ElimNestedInductive.FVOnly (· ∈ xsA)) := by
    intro a ha
    exact Expr.SuppIn.mono (S := ElimNestedInductive.FVOnly (.fvar · ∈ (xsA.map Expr.fvar).toArray))
      (S' := ElimNestedInductive.FVOnly (· ∈ xsA)) ⟨fun x hx => by simpa using hx, fun _ => id, fun _ => id⟩ (hargsS a (by simpa using ha))
  -- the occurrence is `J` at the arguments, over the block's parameters
  have hKabs := ElimNestedInductive.replaceParamsVal_abstract hparams hxnd hxsAnd hxxA hnI hlb hargsA
    (I := J) (Ls := Ls)
  rw [← hK, ElimNestedInductive.abstractList_mkAppList, ElimNestedInductive.abstractList_const] at hKabs
  obtain ⟨Ls', Ks, Ds, hK1, hK2, hLs', hDs⟩ := hoc
  rw [hK2, Expr.mkAppN_eq_mkAppList] at hKabs
  have hfn := congrArg Expr.getAppFn hKabs
  have hag := congrArg Expr.getAppArgs hKabs
  rw [Expr.getAppFn_mkAppList_const, Expr.getAppFn_mkAppList_const] at hfn
  rw [Expr.getAppArgs_mkAppList_const, Expr.getAppArgs_mkAppList_const] at hag
  have hDs' : Ds.toList = (args.toList.take nI).map (·.abstractList xsA 0) := by
    simpa using congrArg Array.toList hag
  obtain ⟨oJ, olv, oargs⟩ := o
  simp only at hDs hLs' hfn ⊢
  have e1 : J = oJ := by injection hfn with h; exact h.symm
  have e2 : Ls = Ls' := by injection hfn with _ h; exact h.symm
  subst e1 e2
  have hex : (args.extract 0 nI).toList = args.toList.take nI := by
    simp [Array.toList_extract, List.extract]
  have hEC := ElimNestedInductive.EnvClosed.of_tr (wf.tr (safety := .unsafe))
  have hdNpar : dN.params = d.params :=
    restoreNested_params_eq henv hd hRI.Rfresh hRI.renfresh
  have hle₀ : venv ≤ env₀ := VEnv.addConstList_le henv₀
  have hE₀wf : env₀.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
    exact restoreNested_types_isType henv hd hRI.Rfresh hRI.renfresh T' hT') henv₀
  have hP₀ : env₀.IsTele dN.uvars [] dN.params := by
    rw [hdNpar]; exact hd.params.mono hle₀
  have hCcl : ∀ n ci, env.constants.find? n = some ci →
      ci.type.SuppIn (ElimNestedInductive.FVOnly fun _ => False) ∧ ci.type.looseBVarRange' = 0 :=
    fun n ci h => by
      have := hEC n ci (by rw [Kernel.Environment.find?, hCwf.find?'_eq_find?]; exact h)
      exact ⟨this.1, this.2.1⟩
  have hJC : env.constants.find? J = some (.inductInfo Jv) := by
    rwa [Kernel.Environment.find?, hCwf.find?'_eq_find?] at hJ
  have hIC : env.constants.find? I' = some (.inductInfo Iv) := by
    rwa [Kernel.Environment.find?, hCwf.find?'_eq_find?] at hI'
  -- the final phase's check of the occurrences, in the environment with the block's types
  have hVT : VEnvAt envT (inductSafety isUnsafe) env₀ :=
    typeAx_venvAt hF henvAt hflat hd hRI.spec rfl (by simp) hnn hRI.Rfresh hRI.renfresh hnamesR rfl
      hlpk henv₀
  have hres : ∀ x ∈ xs, ({} : TypeChecker.State).ngen.Reserves x := fun x hx =>
    ElimNestedInductive.run_params hrun x (by rw [hparams]; simp [hx])
  have hfvK := ElimNestedInductive.aux2nested_fvarsIn hEC hcl hrun hparams
  have hmem : (p.2, p.1) ∈
      Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp) := by
    rw [haux2]; exact foldl_insert_mem_toList hpnd (List.mem_of_getElem? hp)
  -- the first type's parameters
  obtain ⟨r0, hr0, hTD0⟩ := hTD.getElem?_left (i := 0) (a := I) rfl
  obtain ⟨T0, -, hty0, hag0⟩ := htyTr.getElem?_left hr0
  rw [hTD0.2.1] at hty0 hag0
  have hpeelI := hoI.peel hxnd fun x _ => Expr.SuppIn.mono
    (S := ElimNestedInductive.FVOnly fun _ => False) (S' := ElimNestedInductive.FVOnly (· ≠ x))
    ⟨fun _ h => h.elim, fun _ => id, fun _ => id⟩ (hcl I (.head _)).1
  have hlfI : xs.length ≤ I.type.leadingForalls := le_leadingForalls_of_peel hpeelI
  obtain ⟨Qs, B, hQB, hQl⟩ :=
    VExpr.exists_foralls_of_le xs.length T0.type (Nat.le_trans hlfI hty0.leadingForalls_le)
  have hQ : venv.TeleDefEq d.uvars [] Qs d.params :=
    hag0 (by rw [hdpar, ← hxl]; exact hlfI) Qs B hQB (by rw [hQl, hxl, hdpar])

  have hI0 : TrExprS env₀ lps [] I.type (.foralls Qs B) := hQB ▸ hty0.mono hle₀
  -- the occurrence's head: a constant of the environment, at its levels
  obtain ⟨ciJ, hciJ, hLsJ⟩ := occ_head hVT hF.occList hoI hxnd hres hQl hI0 hfvK hmem
    (Ds := Ks.toList) (by rw [hK1])
  have hJenv : venv.constants J = some ciJ := by
    rcases VEnv.addConstList_constants_cases henv₀ hciJ with h | h
    · exact h
    · exfalso
      obtain ⟨T', hT', e⟩ := List.mem_map.1 h
      cases e
      obtain ⟨j', T₁, -, hT₁, rfl⟩ := VInductDecl.mem_restoreNested_types.1 hT'
      have := hfrE T₁.name (by
        simp only [List.map_append, List.mem_append]
        exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T₁, List.mem_of_getElem? hT₁, rfl⟩,
          rfl⟩)))
      simp only [VInductiveType.restore] at hJ
      rw [this] at hJ; cases hJ
  obtain ⟨-, hJtr⟩ := henvAt.tr.find?_uniq hJ hJenv
  have hJs : inductSafety isUnsafe ≤ (ConstantInfo.inductInfo Jv).safety := hJtr.1
  have hIs : inductSafety isUnsafe ≤ (ConstantInfo.inductInfo Iv).safety := by
    have := inductInfo_all_isUnsafe wf hI' hJ hJI
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, this] using hJs
  have hLs : Jv.levelParams.length = Ls.length := hJtr.2.1.trans hLsJ.symm
  let Ps := xsA.map fun _ => VExpr.sort .zero
  have hPs : Ps.length = xsA.length := by simp [Ps]
  have hys : List.Forall₂ (PTr lps venv.ContainsLits (paramCtx Ps))
      ((args.extract 0 nI).toList.map (·.abstractList xsA)) oargs := by
    have := hDs Ps (by simp [Ps, hparams, ← hxxA])
    rwa [hDs', ← hex] at this
  -- the occurrence's arguments are typed at the earlier type's parameters
  have hJT : envT.find? J = some (.inductInfo Jv) := by
    obtain ⟨e1, -, e3, e4, -⟩ := hF.typeAx.spec hCwf
    have hfr' : ∀ c ∈ typeAxiomsN inds lps isUnsafe, env.constants.find? c.name = none :=
      fun c hc => by have := e4 c hc; rwa [Kernel.Environment.find?, hCwf.find?'_eq_find?] at this
    rw [Kernel.Environment.find?, e1, (insertConsts_wf hCwf hfr' e3).find?'_eq_find?]
    exact insertConsts_find?_of_some hCwf hfr' e3 hJC
  obtain ⟨-, -, TI, venvJ, -, -, -, -, hleJ, htrJ, -⟩ := henvAt.tr.inductInfo_type hJC hJs
  have hsz : nI ≤ Jv.type.leadingForalls := by
    obtain ⟨b, hb, -⟩ := ElimNestedInductive.instantiateForallParams_ok hv
    rw [Expr.instantiateLevelParams_eq, peel_instantiateLevelParamsCore'] at hb
    obtain ⟨bJ, hbJ, -⟩ := Option.map_eq_some_iff.1 hb
    exact le_leadingForalls_of_peel hbJ
  have hargTy := occ_argTypes hVT hF.occList hoI hxnd hres hQl hI0 hfvK hmem
    (hparams ▸ hK) hnI hlb hxsAnd hxxA.symm hJT (htrJ.mono (hleJ.trans hle₀)) hsz hLs' hLs hPs hys
    VEnv.LE.rfl (U := dN.uvars) hU.symm
  -- the auxiliary type's declared type is the instantiated earlier type
  have hfrv {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) : e.restore R ren = e :=
    VExpr.restore_of_constsSat (he.mono fun c hc => by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      refine ⟨?_, ?_⟩
      · cases h : R c with
        | none => rfl
        | some _ => rw [hRI.Rfresh c _ h] at hci; cases hci
      · cases h : ren c with
        | none => rfl
        | some _ => rw [hRI.renfresh c _ h] at hci; cases hci)
  have hTdty : Td'.type.restore R ren = Td'.type := by
    obtain ⟨_, h⟩ := (hd.types Td' (List.mem_of_getElem? hTd)).1
    exact hfrv (h.constsSat hO trivial).1
  rw [hTDk.2.1, htyv] at htyk hagk
  have hvcl : v.looseBVarRange' = 0 :=
    ElimNestedInductive.instantiateForallParams_closed hnI hlb
      ((ElimNestedInductive.instantiateLevelParams_looseBVarRange _ _ _).trans (hEC J _ hJ).2.1) hv
  have hlfT : xsA.length ≤ (lctx.mkForall (xsA.map Expr.fvar).toArray v).leadingForalls := by
    rw [show (xsA.map Expr.fvar).toArray = ⟨xsA.map .fvar⟩ from rfl,
      hoA.mkForall .nil (fun _ _ => LocalContext.find?_empty) hxsAnd hxA hctyB v hvcl]
    have hpeelA := hoA.peel hxsAnd hxA
    exact le_leadingForalls_of_peel
      (ElimNestedInductive.peel_setBody (by rw [hpeelA]; rfl) (b := v.abstractList xsA))
  have hctors : List.Forall₂ (fun Jc (c : VConstructor) => c.name = Jc ∧ ∃ ci v',
      env.constants.find? Jc = some ci ∧ ElimNestedInductive.instantiateForallParams
        (ci.type.instantiateLevelParams ci.levelParams Ls) nI args = .ok v' ∧
      PTr lps venv.ContainsLits [] (lctx.mkForall (xsA.map .fvar).toArray v') c.type)
      Jv.ctors (Td'.ctors.map (·.restore R ren (res.restoreCtorName env'))) := by
    -- what restoring needs, without renaming recursors: no constructor type mentions one
    have hlitE₁ : ∀ l, E₁.ContainsLits l → venv.ContainsLits l := by
      have hc {x : Name} (hx : Environment.primitives.contains x = true) :
          E₁.contains x → venv.contains x := fun ⟨ci, h⟩ => by
        rcases VEnv.addConstList_constants_cases hE₁ h with h | h
        · exact ⟨ci, h⟩
        · have := hnp x (by
            simp only [List.map_append, List.mem_append]
            exact .inl (.inl (List.mem_map.2 ⟨_, h, rfl⟩)))
          rw [this] at hx; cases hx
      intro l hl
      cases l with
      | natVal => exact hc (by simp +decide [Environment.primitives, NameSet.ofList,
          NameSet.contains]) hl
      | strVal => exact ⟨hc (by simp +decide [Environment.primitives, NameSet.ofList,
          NameSet.contains]) hl.1, hc (by simp +decide [Environment.primitives, NameSet.ofList,
          NameSet.contains]) hl.2⟩
    have S0 := (hS lps E₁ (VEnv.addConstList_le hE₁) hlitE₁).noRen
    have hisAux : ElimNestedInductive.isAuxB res env' {} = fun x => (R x).isSome := by
      funext x
      rw [S0.aux x]
      show ((({} : NameMap Name).find? x).isSome || _ || _) = _
      rw [show ({} : NameMap Name).find? x = none from rfl, Option.isSome_none, Bool.false_or]
    have hRar : ∀ c ci, E₁.constants c = some ci → (R c).isSome → ci.uvars = lps.length := by
      intro c ci hc hRc
      obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 hRc
      rcases VEnv.addConstList_constants_cases hE₁ hc with h1 | h1
      · rw [hRI.Rfresh c h hh] at h1; cases h1
      · obtain ⟨T₁, -, he⟩ := List.mem_map.1 h1; cases he; exact hU
    have hall : d.allTypes = d.types := VInductDecl.allTypes_of_aux hdaux
    have hTdm : Td' ∈ d.types := List.mem_of_getElem? hTd
    have htm : t ∈ I :: rest ++ auxs := List.mem_of_getElem? ht'
    have hfind : res.aux2nested.find? Td'.name = some p.1 := by
      rw [hElk.1, hTDk.1, htn, haux2]
      exact ElimNestedInductive.auxMap_find? hpnd (List.mem_of_getElem? hp)
    rw [List.forall₂_map_right_iff]
    refine Lean4Lean.List.forall₂_of_getElem? ((Lean4Lean.List.Forall₂.length_eq hctorsC).trans
      ((Lean4Lean.List.Forall₂.length_eq hTDk.2.2).trans
        (Lean4Lean.List.Forall₂.length_eq hElk.2))) fun i Jc cd hJc hcd => ?_
    obtain ⟨ac, hac, hR1⟩ := hctorsC.getElem?_left hJc
    obtain ⟨rc, hrc, hR2⟩ := hTDk.2.2.getElem?_left hac
    obtain ⟨cd', hcd', hR3⟩ := hElk.2.getElem?_left hrc
    rw [hcd] at hcd'; cases hcd'
    obtain ⟨hacn, ci, v', hci, hv', hact⟩ := hR1
    obtain ⟨hcdn, hcdtr, -⟩ := hR3
    have hcdm : cd ∈ Td'.ctors := List.mem_of_getElem? hcd
    have hacm : ac ∈ t.ctors := List.mem_of_getElem? hac
    refine ⟨?_, ci, v', by rwa [Kernel.Environment.find?, hCwf.find?'_eq_find?] at hci, hv', ?_⟩
    · -- the name: the earlier type's constructor, by its prefix
      obtain ⟨c₀, hf, ⟨T', hT', -, -, -, hind, -⟩, -⟩ := hfC _ Td' hTd cd hcdm
      rw [hTd] at hT'; cases hT'
      have hg : res.getNestedIfAuxCtor env' cd.name = some (p.1, Td'.name) := by
        simp [ElimNestedInductive.Result.getNestedIfAuxCtor, hf, hind, hfind]
      show res.restoreCtorName env' cd.name = Jc
      rw [restoreCtorName_eq hg (by rw [hK1]; exact Expr.getAppFn_mkAppN' _ _), hcdn, hR2.1, hacn,
        hElk.1, hTDk.1]
      cases hpre : J.isPrefixOf Jc
      · exfalso
        rw [Name.replacePrefix_of_not_isPrefixOf hpre] at hacn
        have := hfrE cd.name (by
          simp only [List.map_append, List.mem_append]
          refine .inl (.inr (List.mem_map.2 ⟨_, List.mem_map.2 ⟨((I :: rest).length + k, cd),
            VInductDecl.mem_ctors_iff.2 ⟨Td', hTd, hcdm⟩, rfl⟩, rfl⟩)))
        rw [hcdn, hR2.1, hacn, hci] at this; cases this
      · exact Name.replacePrefix_replacePrefix hpre
    · -- the type: the translated constructor, restored, is the instantiated earlier one's
      have hc₀ : ac.type.anySub (constP (ElimNestedInductive.isAuxB res env' {})) = false := by
        rw [hisAux]; exact hin' t htm ac hacm
      have hrt := ElimNestedInductive.CtorDone.restore (auxRec := {}) haux2 hpnd hparams hxnd
        hnpar hxl (fun _ _ => rfl) ElimNestedInductive.instantiateBVars hR2 hc₀
        ((hclAll t htm).2.2 ac hacm).2.1
      have hcOK : (res.restoreNested env' lps rc.type {}).ConstsOK
          fun c _ => R c = none ∧ ({} : NameMap Name).find? c = none := by
        have := constsOK_of_anySub (f := fun x => (R x).isSome)
          (by rw [anySub_constP_eqv hrt]; exact hin' t htm ac hacm)
        exact this.mono fun _ _ h => ⟨by simpa using h, rfl⟩
      have hPT := (hcdtr.toPTr.restoreNested S0 (hcdtr.auxArity hRar) hcOK
        (hcL Td' hTdm cd hcdm).ren_none).mono_lit hlitE₁
      have hren : cd.type.ConstsSat (ren · = none) := by
        obtain ⟨_, hty⟩ := ((hd.ctors E₁ hE₁ Td' (hall ▸ hTdm)).2 cd hcdm).type
        refine (hty.constsSat (VEnv.WF.addConstList henv (fun p hp => by
          obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
          exact (hd.types T hT).1) hE₁).ordered trivial).1.mono fun c hc => ?_
        cases h : ren c with
        | none => rfl
        | some c' =>
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
          rcases VEnv.addConstList_constants_cases hE₁ hci with h1 | h1
          · rw [hRI.renfresh c c' h] at h1; cases h1
          · obtain ⟨T₁, hT₁, he⟩ := List.mem_map.1 h1; cases he
            exact (hRI.renNames _ c' h (List.mem_map_of_mem hT₁)).elim
      show PTr _ _ _ _ (cd.type.restore R ren)
      rw [VExpr.restore_ren_none hren, ← hact]
      exact hPT.eqv hrt
  have := VInductiveType.AuxWF.of_created (safety := inductSafety isUnsafe) henvAt.tr hE₀wf hle₀
    (d := dN) hP₀ (CL := venv.ContainsLits) (fun _ h => h) (Us := lps) hU.symm hCcl hoA hxsAnd hxA
    hctyB (by rw [hdNpar, hdpar, hxsAl]) hJC hJs hIC hIs hJI hnIv hnI hlb hv hLs' hLs hPs hys
    (by rw [hdNpar]; exact hQ.mono hle₀) hargTy
    (T := Td'.restore R ren (res.restoreCtorName env') (some ⟨J, olv, oargs⟩))
    (by show PTr _ _ _ _ (Td'.type.restore R ren); rw [hTdty]; exact htyk.toPTr)
    (fun ps B' he hpl => by
      rw [hdNpar] at hpl ⊢
      exact (hagk (by rw [hdpar, ← hxsAl]; exact hlfT) ps B' (hTdty ▸ he) hpl).mono hle₀)
    hctors
  exact this

end Lean4Lean

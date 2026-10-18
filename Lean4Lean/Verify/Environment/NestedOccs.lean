import Lean4Lean.Verify.Environment.Flat
import Lean4Lean.Verify.Environment.NestedTr
import Lean4Lean.Verify.Environment.NestedRestoreFacts
import Lean4Lean.Verify.Environment.NestedOcc

/-!
# The occurrences of a nested block

What the flat check of a nested block's translation inserts, and the occurrences the elimination
recorded, translated: what the auxiliary types stand for.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- A constant of the environment an `AddInductN` step makes is an earlier one or one of the
block's. -/
theorem AddInductN.constants_cases {nn : Nat} {safety : DefinitionSafety} {m₁ m₂ : ConstMap}
    {env₁ env₂ : VEnv} {decl : VInductDecl} (H : AddInductN nn safety m₁ env₁ decl m₂ env₂)
    {c : Name} {ci : VConstant} (h : env₂.constants c = some ci) :
    env₁.constants c = some ci ∨
      c ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1) := by
  obtain ⟨-, -, -, -, -, -, -, hT, hC, hR, hB⟩ := H
  rw [VEnv.addBlock_constants hB, VEnv.addDefEqList_constants] at h
  have hm {L : List (Name × VConstant)} (h : (c, ci) ∈ L) : c ∈ L.map (·.1) :=
    List.mem_map.2 ⟨_, h, rfl⟩
  rcases VEnv.addConstList_constants_cases hR h with h | h
  · rcases VEnv.addConstList_constants_cases hC h with h | h
    · rcases VEnv.addConstList_constants_cases hT h with h | h
      · exact .inl h
      · exact .inr (hm (List.mem_append_left _ (List.mem_append_left _ h)))
    · exact .inr (hm (List.mem_append_left _ (List.mem_append_right _ h)))
  · exact .inr (hm (List.mem_append_right _ h))

theorem size_foldl_insert_nodup : ∀ (l : List (Expr × Name)) (m : Std.TreeMap Name Expr Name.quickCmp),
    (l.map (·.2)).Nodup → (∀ p ∈ l, m.contains p.2 = false) →
    (l.foldl (fun m x => m.insert x.2 x.1) m).size = m.size + l.length
  | [], _, _, _ => rfl
  | x :: l, m, hnd, hc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons, size_foldl_insert_nodup l _ hnd.2 (fun p hp => ?_), Std.TreeMap.size_insert,
      hc x (.head _)]
    · simp; omega
    · rw [Std.TreeMap.contains_insert, hc p (.tail _ hp)]
      have : x.2 ≠ p.2 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hp)
      simpa [Std.LawfulBEqCmp.compare_eq_iff_beq] using this

/-- A constructor an `AddInductN` step inserts under a fresh name is one of its own. -/
theorem AddInductN.find_ctor {nn : Nat} {safety : DefinitionSafety} {C C' : ConstMap}
    {venv venv' : VEnv} {decl : VInductDecl} (H : AddInductN nn safety C venv decl C' venv')
    {n : Name} {v : ConstructorVal} (hC : C.WF) (hn : C.find? n = none)
    (h : C'.find? n = some (.ctorInfo v)) :
    v.name = n ∧ ∃ lparams j c, (j, c) ∈ decl.ctors ∧ TrCtorVal decl lparams j c v := by
  obtain @⟨lparams, _, _, envR, types, ctors, recs, hlp, hty, hct, hrc, hnd, hfr, ⟨_, hp, rfl⟩, hT,
    hC', hR, hB⟩ := H
  rcases insertConsts_find?_perm hC hfr hnd hp h with h | ⟨hm, hnm⟩
  · cases hn ▸ h
  simp only [inductConsts, List.mem_append, List.mem_map] at hm
  obtain (⟨w, hw, e⟩ | ⟨w, hw, e⟩) | ⟨w, hw, e⟩ := hm
  · cases e
  · cases e
    obtain ⟨⟨j, c⟩, hc, h, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hct v hw
    exact ⟨hnm, lparams, j, c, hc, h⟩
  · cases e

/-- `restoreCtorName` leaves a constructor of a type the elimination did not make alone. -/
theorem restoreCtorName_of_not_aux {res : ElimNestedInductive.Result} {env' : Environment}
    {pairs : List (Expr × Name)} (haux : res.aux2nested = pairs.foldl (fun m (e, n) => m.insert n e) {})
    {c : Name} {c₀ : ConstructorVal} (hf : env'.find? c = some (.ctorInfo c₀))
    (hi : c₀.induct ∉ pairs.map (·.2)) : res.restoreCtorName env' c = c := by
  have : res.aux2nested.find? c₀.induct = none := by
    rw [haux]
    exact (ElimNestedInductive.foldl_insert_get?_of_not_mem hi).trans rfl
  simp [ElimNestedInductive.Result.restoreCtorName, ElimNestedInductive.Result.getNestedIfAuxCtor,
    hf, this]

/-- An occurrence `K` the elimination recorded, over the parameters `params`: the earlier type
`o.ind` at levels and arguments translating to `o`'s. -/
def OccTr (lparams : List Name) (CL : Literal → Prop) (params : Array Expr) (K : Expr)
    (o : VNested) : Prop :=
  ∃ Ls Ks Ds, K = mkAppN (.const o.ind Ls) Ks ∧ K.abstract params = mkAppN (.const o.ind Ls) Ds ∧
    Ls.mapM (VLevel.ofLevel lparams) = some o.lvls ∧
    ∀ As : List VExpr, As.length = params.size →
      List.Forall₂ (PTr lparams CL (paramCtx As)) Ds.toList o.args

theorem OccTr.inst_head {lparams : List Name} {CL : Literal → Prop} {params : Array Expr}
    {K : Expr} {o : VNested} (H : OccTr lparams CL params K o) (ls : List Level)
    (args : Array Expr) : ∃ us, ((ElimNestedInductive.Result.instantiateLevelParamsRaw
      (K.abstract params) lparams ls).instantiateRev args).getAppFn = .const o.ind us := by
  obtain ⟨Ls, -, Ds, -, hD, -⟩ := H
  rw [hD, instantiateLevelParamsRaw_eq, Expr.mkAppN_eq_mkAppList, replaceNoCache_rawFn_mkAppList,
    Expr.instantiateRev_eq_instantiate', instantiate'_mkAppList]
  simp [Expr.replaceNoCache, rawFn, Expr.instantiate', Expr.getAppFn_mkAppList_const]

theorem PTr.mkAppN_const {Us : List Name} {CL : Literal → Prop} {Δ : VLCtx} {c : Name}
    {Ls : List Level} {lvls : List VLevel} (hL : Ls.mapM (VLevel.ofLevel Us) = some lvls)
    {Ds : Array Expr} {ys : List VExpr} (h : List.Forall₂ (PTr Us CL Δ) Ds.toList ys) :
    PTr Us CL Δ (mkAppN (.const c Ls) Ds) (.appN (.const c lvls) ys) := by
  rw [Expr.mkAppN_eq_mkAppList]
  have : ∀ {f : Expr} {f' : VExpr} {xs : List Expr} {ys : List VExpr}, PTr Us CL Δ f f' →
      List.Forall₂ (PTr Us CL Δ) xs ys → PTr Us CL Δ (Expr.mkAppList f xs) (.appN f' ys) := by
    intro f f' xs ys hf h
    induction h generalizing f f' with
    | nil => exact hf
    | cons hx _ ih => exact ih (.app hf hx)
  exact this (.const hL) h

/-- A literal a well-formed environment with the primitives contains stands for constants it
has. -/
theorem VEnv.ContainsLits.constNames {venv : VEnv} (henv : venv.WF) (hp : venv.HasPrimitives)
    {l : Literal} (hl : venv.ContainsLits l) : ∀ c ∈ l.constNames, venv.contains c := by
  cases l with
  | natVal =>
    have := hp.nat hl
    simpa [Literal.constNames] using this
  | strVal =>
    obtain ⟨⟨ci₁, h1⟩, ⟨ci₂, h2⟩⟩ := hl
    obtain ⟨-, hnil, hcons⟩ := hp (``String.ofList, .stringOfList) (by simp [primSpecs]) ci₂ h2
    have hn := (hnil.constsSat henv.ordered trivial).1
    have hc := (hcons.constsSat henv.ordered trivial).1
    simp only [VExpr.listCharNil, VExpr.listCharCons, VExpr.char, VExpr.ConstsSat,
      Option.isSome_iff_exists] at hn hc
    simp only [Literal.constNames, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl)
    exacts [hn.2, hn.1, hc.1, ⟨_, h2⟩, ⟨_, h1⟩]

/-- Looking a variable up past binders `Γ`: below them, what the rest of the context has for it,
lifted past them; among them, whatever the rest is. -/
theorem VLCtx.find?_append_binders : ∀ (Γ : VLCtx), (∀ x ∈ Γ, x.1 = none) →
    ∃ g h : VExpr → VExpr, ∀ Δ : VLCtx,
      (∀ j, (Γ ++ Δ).find? (.inl (Γ.length + j)) = (Δ.find? (.inl j)).map fun p => (g p.1, h p.2)) ∧
      (∀ fv, (Γ ++ Δ).find? (.inr fv) = (Δ.find? (.inr fv)).map fun p => (g p.1, h p.2)) ∧
      (∀ i, i < Γ.length → ∀ Δ' : VLCtx, (Γ ++ Δ).find? (.inl i) = (Γ ++ Δ').find? (.inl i))
  | [], _ => ⟨id, id, fun Δ => ⟨fun j => by simp, fun fv => by simp, fun i hi => by simp at hi⟩⟩
  | (o, dcl) :: Γ, hΓ => by
    have ho : o = none := hΓ _ (.head _)
    subst ho
    obtain ⟨g, h, H⟩ := find?_append_binders Γ fun x hx => hΓ x (.tail _ hx)
    refine ⟨fun e => (g e).liftN dcl.depth, fun e => (h e).liftN dcl.depth, fun Δ => ⟨?_, ?_, ?_⟩⟩
    · intro j
      rw [show ((none, dcl) :: Γ).length + j = (Γ.length + j) + 1 by simp; omega]
      simp only [List.cons_append, VLCtx.find?, VLCtx.next, (H Δ).1 j]
      cases Δ.find? (.inl j) <;> rfl
    · intro fv
      simp only [List.cons_append, VLCtx.find?, VLCtx.next, (H Δ).2.1 fv]
      cases Δ.find? (.inr fv) <;> rfl
    · intro i hi Δ'
      cases i with
      | zero => simp [VLCtx.find?, VLCtx.next]
      | succ i =>
        simp only [List.cons_append, VLCtx.find?, VLCtx.next]
        rw [(H Δ).2.2 i (by simp at hi; omega) Δ']

theorem paramCtx_find?_bvar : ∀ {As : List VExpr} {j : Nat}, j < As.length →
    ∃ A, (paramCtx As).find? (.inl j) = some (.bvar j, A)
  | _ :: _, 0, _ => ⟨_, rfl⟩
  | _ :: As, j + 1, hj => by
    obtain ⟨A, hA⟩ := paramCtx_find?_bvar (As := As) (j := j) (by simp at hj; omega)
    refine ⟨A.liftN 1, ?_⟩
    simp only [paramCtx, List.map_cons, VLCtx.find?, VLCtx.next] at hA ⊢
    rw [hA]; simp [VLocalDecl.depth, VExpr.liftN]

/-- Abstracting the free variables of a context `Δ` of them, below binders `Γ`: the term translates
over parameters `As` in their place as it did over `Δ`. -/
theorem PTr.abstract'_params {Us : List Name} {CL : Literal → Prop} {Δ : VLCtx}
    {xs : List FVarId} {As : List VExpr}
    (hΔb : ∀ j, Δ.find? (.inl j) = none)
    (hΔf : ∀ fv e A, Δ.find? (.inr fv) = some (e, A) →
      ∃ j, j < As.length ∧ xs.reverse.idxOf? fv = some j ∧ e = .bvar j) :
    ∀ {Γ : VLCtx} {e : Expr} {e' : VExpr}, (∀ x ∈ Γ, x.1 = none) → PTr Us CL (Γ ++ Δ) e e' →
      PTr Us CL (Γ ++ paramCtx As) (e.abstract' xs Γ.length) e' := by
  intro Γ e e' hΓ H
  generalize hc : Γ ++ Δ = Δ₀ at H
  induction H generalizing Γ with
  | @bvar e A _ i h =>
    subst hc
    obtain ⟨g, k, HΓ⟩ := VLCtx.find?_append_binders Γ hΓ
    simp only [Expr.abstract']
    by_cases hi : i < Γ.length
    · rw [(HΓ Δ).2.2 i hi (paramCtx As)] at h; exact .bvar h
    · obtain ⟨j, rfl⟩ : ∃ j, i = Γ.length + j := ⟨i - Γ.length, by omega⟩
      rw [(HΓ Δ).1 j, hΔb j] at h; cases h
  | @fvar e A _ fv h =>
    subst hc
    obtain ⟨g, k, HΓ⟩ := VLCtx.find?_append_binders Γ hΓ
    rw [(HΓ Δ).2.1 fv] at h
    obtain ⟨⟨e₀, A₀⟩, h₀, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    obtain ⟨j, hj, hidx, rfl⟩ := hΔf fv e₀ A₀ h₀
    simp only [Expr.abstract', hidx]
    obtain ⟨B, hB⟩ := paramCtx_find?_bvar hj
    exact .bvar (by rw [(HΓ (paramCtx As)).1 j, hB]; rfl)
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 hΓ hc) (ih2 hΓ hc)
  | lam _ _ ih1 ih2 =>
    subst hc
    exact .lam (ih1 hΓ rfl) (ih2 (Γ := (none, _) :: Γ) (by
      rintro x (_ | ⟨_, hx⟩); · rfl
      · exact hΓ x hx) rfl)
  | forallE _ _ ih1 ih2 =>
    subst hc
    exact .forallE (ih1 hΓ rfl) (ih2 (Γ := (none, _) :: Γ) (by
      rintro x (_ | ⟨_, hx⟩); · rfl
      · exact hΓ x hx) rfl)
  | letE _ _ _ ih1 ih2 ih3 =>
    subst hc
    exact .letE (ih1 hΓ rfl) (ih2 hΓ rfl) (ih3 (Γ := (none, _) :: Γ) (by
      rintro x (_ | ⟨_, hx⟩); · rfl
      · exact hΓ x hx) rfl)
  | lit h H' _ => exact .lit h (H'.ground Literal.toConstructor_ground)
  | mdata _ ih => exact .mdata (ih hΓ hc)
  | proj _ ih => exact .proj (ih hΓ hc)

/-- The environment the final phase checks the occurrences in, the block's own types added as
axioms, has a model: `venv` with the translated block's first types. Its literals are `venv`'s,
since the block names no primitive. -/
theorem nested_envT {env : Environment} {ves : VEnvs} (wf : ves.WF env) {lparams : List Name}
    {isUnsafe : Bool} {nn : Nat} {d : VInductDecl} {env' : Environment} {venv' : VEnv}
    (hflat : AddInductN nn (inductSafety isUnsafe) env.constants (ves.venv (inductSafety isUnsafe))
      d env'.constants venv')
    (hd : d.WF (ves.venv (inductSafety isUnsafe)))
    (hnp : ∀ x ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1),
      Environment.primitives.contains x = false)
    (hfT : ∀ (i : Nat) T, d.types[i]? = some T → ∃ v, env'.find? T.name = some (.inductInfo v) ∧
      TrInductValN d lparams nn T v ∧
      TrConstant (inductSafety isUnsafe) (ves.venv (inductSafety isUnsafe)) (.inductInfo v)
        ⟨d.uvars, T.type⟩ ∧
      (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
        ps.length = d.params.length →
        (ves.venv (inductSafety isUnsafe)).TeleDefEq d.uvars [] ps d.params))
    {types : List InductiveType}
    (hnm : ∀ (j : Nat) (t : InductiveType) (T : VInductiveType), types[j]? = some t →
      d.types[j]? = some T → T.name = t.name)
    (hlen : types.length ≤ d.types.length)
    {fuel : FuelConfig} {res : ElimNestedInductive.Result}
    {inds : List (InductiveVal × List ConstructorVal)} {recs : List RecursorVal}
    {envT envF : Environment}
    (hF : NestedFinalOK env env' lparams types res isUnsafe false fuel inds recs envT envF) :
    ∃ venvT, VEnvAt envT (inductSafety isUnsafe) venvT ∧
      ves.venv (inductSafety isUnsafe) ≤ venvT ∧
      ∀ l, venvT.ContainsLits l → (ves.venv (inductSafety isUnsafe)).ContainsLits l := by
  have henvAt := wf.toVEnvAt (inductSafety isUnsafe)
  generalize ves.venv (inductSafety isUnsafe) = venv at henvAt hflat hd hfT ⊢
  have hCwf : env.constants.WF := henvAt.tr.map_wf
  obtain ⟨cis, -, hnd, hfr, -, hnames⟩ := AddInductN.names hflat
  let cs := (d.types.take types.length).map fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))
  have hmem {c : Name} {ci : VConstant} (h : (c, ci) ∈ cs) :
      c ∈ (d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1) := by
    obtain ⟨T, hT, e⟩ := List.mem_map.1 h
    cases e
    simp only [List.map_append, List.mem_append]
    exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T, List.mem_of_mem_take hT, rfl⟩, rfl⟩))
  obtain ⟨venvT, e⟩ : ∃ venvT, venv.addConstList cs = some venvT := by
    refine VEnv.exists_addConstList (fun p hp => ?_) ?_
    · obtain ⟨ci, hci, e⟩ := List.mem_map.1 (hnames.mem_iff.2 (hmem (c := p.1) (ci := p.2) hp))
      rw [← e]
      exact henvAt.tr.constants_eq_none
        (by rw [Kernel.Environment.find?, hCwf.find?'_eq_find?]; exact hfr ci hci)
    · have h1 : ((d.typeConsts ++ d.ctorConsts ++ d.recConsts).map (·.1)).Nodup :=
        hnames.nodup_iff.1 hnd
      have h2 : (d.typeConsts.map (·.1)).Nodup := by
        simp only [List.map_append] at h1
        exact (List.nodup_append.1 (List.nodup_append.1 h1).1).1
      have h3 : (cs.map (·.1)) = (d.typeConsts.map (·.1)).take types.length := by
        simp [cs, VInductDecl.typeConsts, List.map_take, Function.comp_def]
      rw [h3]; exact h2.sublist (List.take_sublist _ _)
  have hindsLen : inds.length = types.length :=
    (Lean4Lean.List.Forall₂.length_eq hF.indsSpec).symm
  have hax := hF.typeAx
  have ee : typeAxiomsN inds lparams isUnsafe =
      (inds.map fun p => AxiomVal.mk ⟨p.1.name, lparams, p.1.type⟩ isUnsafe).map .axiomInfo := by
    simp [typeAxiomsN, List.map_map, Function.comp_def]
  rw [ee] at hax
  have hinds : ∀ (j : Nat) p, inds[j]? = some p → ∃ T v, d.types[j]? = some T ∧
      j < types.length ∧ p.1 = { v with all := types.map (·.name) } ∧
      TrInductValN d lparams nn T v ∧
      TrConstant (inductSafety isUnsafe) venv (.inductInfo v) ⟨d.uvars, T.type⟩ := by
    intro j p hp
    have hj : j < types.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1; omega
    obtain ⟨t, ht⟩ : ∃ t, types[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨T, hT⟩ : ∃ T, d.types[j]? = some T := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, hv, hvT, hvc, -⟩ := hfT j T hT
    obtain ⟨p', hp', hpv⟩ := forall₂_getElem?_l hF.indsSpec ht
    rw [hp] at hp'; cases hp'
    exact ⟨T, v, hT, hj, (hpv v (hnm j t T ht hT ▸ hv)).1, hvT, hvc⟩
  have hVT : VEnvAt envT (inductSafety isUnsafe) venvT := by
    refine CheckedAdds.venvAt henvAt hax ?_ (fun ax hax' => ?_) e
    · refine Lean4Lean.List.forall₂_of_getElem? (by simp [cs, hindsLen]; omega)
        fun j a b ha hb => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨T, v, hT, hj, hpv, hvT, hsafe, hlp, htr⟩ := hinds j p hp
      simp only [cs, List.getElem?_map, List.getElem?_take, if_pos hj, hT,
        Option.map_some, Option.some.injEq] at hb
      subst hb
      refine ⟨?_, ⟨?_, ?_, ?_⟩, (hd.types T (List.mem_of_getElem? hT)).1⟩
      · show p.1.name = T.name; rw [hpv]; exact hvT.1
      · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, inductSafety]
      · show lparams.length = d.uvars; rw [← hvT.2.1]; exact hlp
      · show TrExprS venv lparams [] p.1.type T.type
        rw [hpv]; rw [← hvT.2.1]; exact htr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hax'
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
      obtain ⟨T, v, hT, -, hpv, hvT, -⟩ := hinds j p hj
      show Environment.primitives.contains p.1.name = false
      rw [hpv, show ({ v with all := types.map (·.name) } : InductiveVal).name = T.name from hvT.1]
      refine hnp _ ?_
      simp only [List.map_append, List.mem_append]
      exact .inl (.inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩, rfl⟩))
  refine ⟨venvT, hVT, VEnv.addConstList_le e, fun l hl => ?_⟩
  have hc {x : Name} (hx : Environment.primitives.contains x = true) :
      venvT.contains x → venv.contains x := fun ⟨ci, h⟩ => by
    rcases VEnv.addConstList_constants_cases e h with h | h
    · exact ⟨ci, h⟩
    · rw [hnp x (hmem h)] at hx; cases hx
  cases l with
  | natVal => exact hc (by simp +decide [Environment.primitives, NameSet.ofList,
      NameSet.contains]) hl
  | strVal => exact ⟨hc (by simp +decide [Environment.primitives, NameSet.ofList,
      NameSet.contains]) hl.1, hc (by simp +decide [Environment.primitives, NameSet.ofList,
      NameSet.contains]) hl.2⟩

theorem ElimNestedInductive.Opens.peel_isSome {lctx ty xs lctx' ty'}
    (H : ElimNestedInductive.Opens lctx ty xs lctx' ty') :
    (ElimNestedInductive.peel xs.length ty).isSome := by
  induction H with
  | nil => rfl
  | cons _ ih =>
    simp only [Expr.instantiate1_eq, ElimNestedInductive.peel_instantiate1_fvar,
      Option.isSome_map] at ih
    simpa [ElimNestedInductive.peel] using ih

theorem VLCtx.find?_inl_of_fvars : ∀ {Δ : VLCtx}, (∀ x ∈ Δ, x.1.isSome) →
    ∀ j, Δ.find? (.inl j) = none
  | [], _, _ => rfl
  | (o, d) :: Δ, h, j => by
    obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 (h _ (.head _))
    simp [VLCtx.find?, VLCtx.next, find?_inl_of_fvars (fun x hx => h x (.tail _ hx)) j]

theorem VLCtx.find?_inr_mem : ∀ {Δ : VLCtx} {fv : FVarId} {p},
    Δ.find? (.inr fv) = some p → fv ∈ Δ.fvars
  | [], _, _, h => by cases h
  | (none, d) :: Δ, fv, p, h => by
    simp only [VLCtx.find?, VLCtx.next] at h
    obtain ⟨q, hq, -⟩ := Option.bind_eq_some_iff.1 h
    simpa using find?_inr_mem hq
  | (some (y, ds), d) :: Δ, fv, p, h => by
    simp only [VLCtx.find?, VLCtx.next] at h
    by_cases e : y = fv
    · subst e; simp
    · rw [if_neg (by simpa using e)] at h
      obtain ⟨q, hq, -⟩ := Option.bind_eq_some_iff.1 h
      simp [find?_inr_mem hq]

theorem Expr.abstract'_mkAppList {xs : List FVarId} {d : Nat} :
    ∀ {f : Expr} {as : List Expr}, (Expr.mkAppList f as).abstract' xs d =
      Expr.mkAppList (f.abstract' xs d) (as.map (·.abstract' xs d))
  | _, [] => rfl
  | _, _ :: _ => Expr.abstract'_mkAppList (f := .app _ _)

theorem List.exists_forall₂_of_forall {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (.head _)
    obtain ⟨l', hl'⟩ := exists_forall₂_of_forall (l := l) fun a ha => h a (.tail _ ha)
    exact ⟨b :: l', .cons hb hl'⟩

/-- The occurrences the final phase checked translate: they are what the auxiliary types stand
for. The check runs in `envT`, the environment with the block's types as axioms, modelled by
`venvT`, whose literals are the environment's. -/
theorem nested_occs {env : Environment} {ves : VEnvs} (wf : ves.WF env) {lparams : List Name}
    {nparams : Nat} {isUnsafe ap : Bool} {fuel : FuelConfig} {I : InductiveType}
    {rest : List InductiveType} (hcl : ∀ T ∈ I :: rest, ElimNestedInductive.TypeClosed T)
    {res : ElimNestedInductive.Result}
    (hrun : (ElimNestedInductive.run fuel.inductiveFuel nparams (I :: rest) env).run'
      { lvls := lparams.map .param, newTypes := (I :: rest).toArray } = .ok res)
    {xs : List FVarId} {body : Expr}
    (hoI : ElimNestedInductive.Opens {} I.type xs res.lctx body) (hxnd : xs.Nodup)
    (hparams : res.params = (xs.map .fvar).toArray)
    {auxs : List InductiveType} {pairs : List (Expr × Name)}
    (hA : List.Forall₂ (fun e T => ElimNestedInductive.AuxMade env res.params nparams (e, T))
      pairs auxs)
    (haux2 : res.aux2nested = pairs.foldl (fun m (e, n) => m.insert n e) {})
    (hpnd : (pairs.map (·.2)).Nodup)
    {env' envT envF : Environment} {inds : List (InductiveVal × List ConstructorVal)}
    {recs : List RecursorVal}
    (hF : NestedFinalOK env env' lparams (I :: rest) res isUnsafe ap fuel inds recs envT envF)
    {venvT : VEnv} (hVT : VEnvAt envT (inductSafety isUnsafe) venvT)
    (hle : ves.venv (inductSafety isUnsafe) ≤ venvT)
    (hlitT : ∀ l, venvT.ContainsLits l → (ves.venv (inductSafety isUnsafe)).ContainsLits l)
    {IT : VExpr} (hIT : TrExprS (ves.venv (inductSafety isUnsafe)) lparams [] I.type IT) :
    ∃ ns, List.Forall₂ (fun p o => OccTr lparams (ves.venv (inductSafety isUnsafe)).ContainsLits
      res.params p.1 o) pairs ns := by
  have henv := hVT.tr.wf
  have hfvK := ElimNestedInductive.aux2nested_fvarsIn
    (ElimNestedInductive.EnvClosed.of_tr (wf.tr (safety := .unsafe))) hcl hrun hparams
  -- the first type's leading binders, which the check opens
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hoI.peel_isSome
  obtain ⟨Qs, B, rfl, hQl, -⟩ := PTr.peel hIT.toPTr hb
  obtain ⟨M, E, hMw, hMl, hME, -, hEent, -, hMfv, hMf, -⟩ :=
    ElimNestedInductive.Opens.mlctx henv.ordered hoI (M₀ := .nil) trivial rfl (by simp) hxnd hQl
      (by simpa using hIT.mono hle)
  simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_nil, List.append_nil] at hME hMfv
  let c := TypeChecker.VContext.ofMLCtx hVT lparams fuel M hMw
  have hfvc : ∀ p ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp),
      p.2.FVarsIn (· ∈ c.vlctx.fvars) := fun p hp =>
    (hfvK p hp).mono fun x hx => by
      show x ∈ M.vlctx.fvars; rw [hMfv]; exact List.mem_reverse.2 hx
  obtain ⟨s, -, hQ⟩ := TypeChecker.M.WF.runMLCtx hVT hMw
    (TypeChecker.checkType.forM_lit (c := c) _ (fun p : Name × Expr => p.2) hfvc) (hMl ▸ hF.occList)
  -- the context's variables are the parameters
  have hEsome : ∀ x ∈ M.vlctx, x.1.isSome := by
    rw [hME]; intro x hx
    obtain ⟨y, ds, A, rfl, -⟩ := hEent x hx
    rfl
  have hΔf : ∀ (As : List VExpr), As.length = xs.length → ∀ fv e A,
      M.vlctx.find? (.inr fv) = some (e, A) →
      ∃ j, j < As.length ∧ xs.reverse.idxOf? fv = some j ∧ e = .bvar j := by
    intro As hAs fv e A h
    have hm := VLCtx.find?_inr_mem h
    rw [hMfv, List.mem_reverse] at hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨A', hA'⟩ := hMf k hk
    rw [hA'] at h
    cases h
    refine ⟨xs.length - 1 - k, by omega, ?_, rfl⟩
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp; omega, by rw [List.getElem_reverse]; congr 1; omega, fun j hj e => ?_⟩
    rw [List.getElem_reverse] at e
    have := (List.getElem_inj hxnd).1 e
    omega
  refine List.exists_forall₂_of_forall fun p hp => ?_
  obtain ⟨K, n⟩ := p
  have hmem : (n, K) ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp) := by
    rw [haux2]; exact foldl_insert_mem_toList hpnd hp
  obtain ⟨⟨K', hKtr⟩, -⟩ := hQ _ hmem
  change TrExprS venvT lparams M.vlctx K K' at hKtr
  -- the occurrence's shape
  obtain ⟨T, -, hAM⟩ := Lean4Lean.List.Forall₂.forall_exists_l hA _ hp
  obtain ⟨-, cty, xs', lctx, body', -, -, -, -, -, -, -, hC⟩ := hAM
  obtain ⟨J, Ls, args, nI, Jv, v, hK, -, hnI, -⟩ := hC
  simp only at hK
  rw [hparams, ElimNestedInductive.replaceParamsVal_mkAppRange hnI] at hK
  generalize (List.map _ (args.extract 0 nI).toList).toArray = Ks at hK
  subst hK
  rw [Expr.mkAppN_eq_mkAppList] at hKtr
  obtain ⟨f', as', rfl, hf, has⟩ := TrExprS.mkAppList_inv hKtr
  cases hf with
  | const _ hls _ =>
  refine ⟨⟨J, _, as'⟩, Ls, Ks, ⟨Ks.toList.map (·.abstract' xs)⟩, rfl, ?_, hls, fun As hAs => ?_⟩
  · rw [hparams]
    show (mkAppN (.const J Ls) Ks).abstract ⟨xs.map .fvar⟩ = _
    rw [Expr.abstract_eq', Expr.mkAppN_eq_mkAppList, Expr.abstract'_mkAppList, Expr.mkAppN_eq_mkAppList]
    rfl
  · have hAs' : As.length = xs.length := by rw [hAs, hparams]; simp
    show List.Forall₂ _ (Ks.toList.map (·.abstract' xs)) as'
    rw [List.forall₂_map_left_iff]
    refine Lean4Lean.List.Forall₂.imp (fun k k' h => ?_) has
    have := PTr.abstract'_params (Us := lparams) (CL := (ves.venv (inductSafety isUnsafe)).ContainsLits)
      (As := As) (xs := xs) (VLCtx.find?_inl_of_fvars hEsome) (hΔf As hAs') (Γ := []) (by simp)
      ((h.toPTr).mono_lit hlitT)
    simpa using this

end Lean4Lean

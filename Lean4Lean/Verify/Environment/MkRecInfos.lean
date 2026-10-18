import Lean4Lean.Verify.Environment.Rules

/-!
# `mkRecInfos`

`mkRecInfos` runs in the environment with the block's constructors as axioms, at the recursor's
level parameters: `loopInd1` opens each type's indices, major premise and motive, and
`loopInd2` each constructor's minor premise. What they open determines the declaration `d` the
block elaborates to, and the recursors' types, which translate to the specification's.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive

/-- A type of the block as an axiom. -/
def typeAxiom (lparams : List Name) (isUnsafe : Bool) (t : InductiveType) : AxiomVal :=
  { name := t.name, levelParams := lparams, type := t.type, isUnsafe }

theorem foldl_addAxiom_constants : ∀ (axs : List AxiomVal) (env : Environment),
    (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).constants =
      insertConsts env.constants (axs.map .axiomInfo)
  | [], _ => rfl
  | ax :: axs, env => foldl_addAxiom_constants axs (env.add (.axiomInfo ax))

theorem foldl_addAxiom_quotInit : ∀ (axs : List AxiomVal) (env : Environment),
    (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).quotInit = env.quotInit
  | [], _ => rfl
  | ax :: axs, env => (foldl_addAxiom_quotInit axs (env.add (.axiomInfo ax))).trans rfl

/-- `declareInductiveTypes` refuses the constant a kernel panic returns as a type's name. -/
theorem declareInductiveTypes.ne_dummy {c : VContext} {stats : InductiveStats}
    {numParams numNested : Nat} {indTypes : Array InductiveType} {isUnsafe : Bool} :
    AddInductive.WF c (declareInductiveTypes stats numParams indTypes numNested isUnsafe) fun _ =>
      ∀ ci ∈ (inductVals c.lparams stats numParams indTypes numNested isUnsafe).map
        ConstantInfo.inductInfo, ci.name ≠ `_inhabitedExprDummy := by
  intro env' h ci hci
  simp only [declareInductiveTypes, ← Array.foldlM_toList] at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hci
  exact addChecked.ne_dummy (f := ConstantInfo.inductInfo) _ _ h x hx

/-- A declaration agreeing with what the checks have seen exists: any will do to read the shape of
the constructors off `CtorChecked`. -/
theorem compat_exists (U : List Name) (params : List VExpr) (level : VLevel) (isUnsafe : Bool)
    (types : List InductiveType) (nindices : Array Nat) (hn : nindices.size = types.length) :
    ∃ d, Compat U params level isUnsafe types nindices d := by
  let ty (tj : InductiveType × Nat) : VInductiveType :=
    ⟨tj.1.name, default, List.replicate nindices[tj.2]! default, [], none⟩
  refine ⟨⟨U.length, params, level, types.zipIdx.map ty, false, false, isUnsafe, []⟩, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_, fun j T hT => ?_, rfl, fun T hT => ?_⟩
  rotate_right
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hT; rfl
  · apply List.ext_getElem (by simp [VInductDecl.names]) fun i h1 h2 => ?_
    simp [VInductDecl.names, ty]
  · rw [List.getElem?_map, List.getElem?_zipIdx] at hT
    cases h : types[j]? with
    | none => simp [h] at hT
    | some t =>
      simp only [h, Option.map_some, Option.some.injEq] at hT
      subst hT
      have hj : j < types.length := (List.getElem?_eq_some_iff.1 h).1
      simp [ty, getElem!_pos nindices j (by omega)]

theorem _root_.List.exists_forall₂ {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ m, List.Forall₂ R l m
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (.head _)
    obtain ⟨m, hm⟩ := List.exists_forall₂ (l := l) fun a ha => h a (.tail _ ha)
    exact ⟨b :: m, .cons hb hm⟩

/-- Axioms inserted into a closed constant map, each of whose types mentions only its names. -/
theorem ConstMap.Closed.insertAxioms : ∀ (axs : List AxiomVal) {C : ConstMap},
    C.WF → ConstMap.Closed C →
    (∀ ax ∈ axs, ax.type.SuppIn
      ⟨fun _ => False, (· ∈ ax.levelParams), fun m => (C.find? m).isSome⟩) →
    (axs.map (·.name)).Nodup → (∀ ax ∈ axs, C.find? ax.name = none) →
    ConstMap.Closed (insertConsts C (axs.map .axiomInfo))
  | [], _, _, hcl, _, _, _ => hcl
  | ax :: axs, C, hC, hcl, hty, hnd, hfr => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfr₀ := hfr ax (.head _)
    have mono {m} (h : (C.find? m).isSome) : ((C.insert ax.name (.axiomInfo ax)).find? m).isSome := by
      rw [hC.find?_insert]; split <;> simp [h]
    have hcl' := ConstMap.Closed.insert_axiom (n := ax.name) hC hcl (hty ax (.head _))
    refine ConstMap.Closed.insertAxioms axs (hC.insert _ _ hfr₀) hcl'
      (fun a ha => @Expr.SuppIn.mono
        ⟨fun _ => False, (· ∈ a.levelParams), fun m => (C.find? m).isSome⟩
        ⟨fun _ => False, (· ∈ a.levelParams),
          fun m => ((C.insert ax.name (.axiomInfo ax)).find? m).isSome⟩
        ⟨fun _ => id, fun _ => id, fun _ => mono⟩ _ (hty a (.tail _ ha))) hnd.2
      (fun a ha => by
        rw [hC.find?_insert, if_neg]; · exact hfr a (.tail _ ha)
        simp only [beq_iff_eq]; intro hh
        exact hnd.1 (by rw [show ax.name = a.name from hh]; exact List.mem_map_of_mem ha))

theorem _root_.List.Forall₂.mem_zipWith {R : α → β → Prop} {f : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁,
      ∃ b, R a b ∧ f a b ∈ List.zipWith f l₁ l₂
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hab h, a, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, hab, .head _⟩
    · obtain ⟨b, h1, h2⟩ := h.mem_zipWith a hm
      exact ⟨b, h1, .tail _ h2⟩

/-- The block's types, without constructors, as `loopInd1` opened them. -/
def headTypes (types : List InductiveType) (typeTr : List VExpr) (tds : List TyData) :
    List VInductiveType :=
  (types.zip (typeTr.zip tds)).map fun (t, T', td) => ⟨t.name, T', td.idx, [], none⟩

theorem headTypes_length {types : List InductiveType} {typeTr : List VExpr} {tds : List TyData}
    (h1 : typeTr.length = types.length) (h2 : tds.length = types.length) :
    (headTypes types typeTr tds).length = types.length := by
  simp [headTypes, h1, h2]

theorem headTypes_getElem? {types : List InductiveType} {typeTr : List VExpr} {tds : List TyData}
    {j : Nat} {T : VInductiveType} (h : (headTypes types typeTr tds)[j]? = some T) :
    ∃ t T' td, types[j]? = some t ∧ typeTr[j]? = some T' ∧ tds[j]? = some td ∧
      T = ⟨t.name, T', td.idx, [], none⟩ := by
  simp only [headTypes, List.getElem?_map, Option.map_eq_some_iff, List.getElem?_zip_eq_some]
    at h
  obtain ⟨⟨t, T', td⟩, ⟨h1, h2⟩, rfl⟩ := h
  simp only [List.getElem?_zip_eq_some] at h2
  exact ⟨t, T', td, h1, h2.1, h2.2, rfl⟩

theorem headTypes_getElem?_of {types : List InductiveType} {typeTr : List VExpr}
    {tds : List TyData} {j : Nat} {t : InductiveType} {T' : VExpr} {td : TyData}
    (h1 : types[j]? = some t) (h2 : typeTr[j]? = some T') (h3 : tds[j]? = some td) :
    (headTypes types typeTr tds)[j]? = some ⟨t.name, T', td.idx, [], none⟩ := by
  simp only [headTypes, List.getElem?_map]
  have h23 : (typeTr.zip tds)[j]? = some (T', td) := List.getElem?_zip_eq_some.2 ⟨h2, h3⟩
  have : (types.zip (typeTr.zip tds))[j]? = some (t, T', td) := List.getElem?_zip_eq_some.2 ⟨h1, h23⟩
  rw [this]; rfl

theorem headTypes_names {types : List InductiveType} {typeTr : List VExpr} {tds : List TyData}
    (h1 : typeTr.length = types.length) (h2 : tds.length = types.length) :
    (headTypes types typeTr tds).map (·.name) = types.map (·.name) := by
  refine List.ext_getElem (by simp [headTypes, h1, h2]) fun j hj₁ hj₂ => ?_
  have hj : j < types.length := by simpa using hj₂
  have := headTypes_getElem?_of (List.getElem?_eq_getElem hj)
    (List.getElem?_eq_getElem (by rw [h1]; exact hj)) (List.getElem?_eq_getElem (by rw [h2]; exact hj))
  simp only [List.getElem_map]
  rw [List.getElem?_eq_getElem (by simpa using hj₁)] at this
  rw [Option.some.inj this]

theorem headTypes_nested {types : List InductiveType} {typeTr : List VExpr} {tds : List TyData} :
    ∀ T ∈ headTypes types typeTr tds, T.nested = none := by
  intro T hT; obtain ⟨⟨t, T', td⟩, -, rfl⟩ := List.mem_map.1 hT; rfl

theorem bvars_liftN_lo (n k : Nat) : (VExpr.bvars k 0).map (·.liftN n k) = VExpr.bvars k 0 := by
  simp only [VExpr.bvars, List.map_map, Function.comp_def, VExpr.liftN, liftVar]
  apply List.map_congr_left; intro i hi; simp at hi; simp; omega

/-- A motive's type over the parameters, below the motives before it. -/
theorem motiveTy_liftN {name : Name} {U n : Nat} {sh : List VLevel} (hsh : sh.length = U)
    {idx : List VExpr} {ml : VLevel} {d : VInductDecl} (hd : d.params.length = n) (j : Nat)
    {T : VInductiveType} (hT : T.name = name) (hidx : T.indices = idx) (hno : T.nested = none) :
    (motiveTy name U n sh idx ml).liftN j = d.motiveType sh ml j T := by
  subst hT hidx hd
  simp only [motiveTy, majorTy, VInductDecl.motiveType, VInductiveType.typeApp_of_none hno, VExpr.instL_foralls,
    VExpr.liftN_foralls, VExpr.instL_appN, VExpr.liftN_appN, VExpr.instL, VLevel.params_inst hsh,
    List.map_append, VExpr.instL_bvars, List.length_map, Nat.zero_add, VExpr.liftN]
  simp only [Nat.add_zero, VExpr.bvars_liftN_hi _ _ _ _ (Nat.le_refl _), bvars_liftN_lo,
    Nat.add_comm j]

theorem motivesCtx_isTele {base : TypeChecker.MLCtx} {fvs : List FVarId} {tys : List VExpr}
    (h : base.IsTele fvs tys) : ∀ tds : List TyData,
    (motivesCtx base tds).IsTele (fvs ++ tds.map (·.motive))
      (tys ++ tds.zipIdx.map fun (td, j) => td.mtr.liftN j) := by
  suffices ∀ n (tds : List TyData), tds.length = n → (motivesCtx base tds).IsTele
      (fvs ++ tds.map (·.motive)) (tys ++ tds.zipIdx.map fun (td, j) => td.mtr.liftN j) from
    fun tds => this _ tds rfl
  intro n
  induction n with
  | zero =>
    intro tds hl; obtain rfl := List.eq_nil_of_length_eq_zero hl; simpa [motivesCtx] using h
  | succ n ih =>
    intro tds hl
    obtain ⟨tds, td, rfl⟩ : ∃ a b, tds = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tds).resolve_left (by rintro rfl; simp at hl)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [motivesCtx_append]
    simpa [List.zipIdx_append] using (ih tds hl).vlam (fv := td.motive) (name := td.motName)
      (ty := td.mty) (ty' := td.mtr.liftN tds.length) (bi := .default)

/-- The block's types, with their constructors. -/
def withCtors (Ts : List VInductiveType) (css : List (List VConstructor)) : List VInductiveType :=
  (Ts.zip css).map fun (T, cs) => { T with ctors := cs }

theorem withCtors_length {Ts : List VInductiveType} {css : List (List VConstructor)}
    (h : css.length = Ts.length) : (withCtors Ts css).length = Ts.length := by
  simp [withCtors, h]

theorem withCtors_getElem? {Ts : List VInductiveType} {css : List (List VConstructor)} {j : Nat}
    {T : VInductiveType} (h : (withCtors Ts css)[j]? = some T) :
    ∃ T₀ cs, Ts[j]? = some T₀ ∧ css[j]? = some cs ∧ T = { T₀ with ctors := cs } := by
  simp only [withCtors, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨T₀, cs⟩, h1, rfl⟩ := h
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 h1
  exact ⟨T₀, cs, h1, h2, rfl⟩

theorem withCtors_getElem?_of {Ts : List VInductiveType} {css : List (List VConstructor)}
    {j : Nat} {T₀ : VInductiveType} {cs : List VConstructor} (h1 : Ts[j]? = some T₀)
    (h2 : css[j]? = some cs) : (withCtors Ts css)[j]? = some { T₀ with ctors := cs } := by
  have : (Ts.zip css)[j]? = some (T₀, cs) := List.getElem?_zip_eq_some.2 ⟨h1, h2⟩
  simp only [withCtors, List.getElem?_map, this]; rfl

theorem FieldsElab.of_getElem {venv : VEnv} {d : VInductDecl} :
    ∀ {Γ : List VExpr} {k : Nat} {Ds : List VExpr} {fs : List VField}, Ds.length = fs.length →
    (∀ j D f, Ds[j]? = some D → fs[j]? = some f →
      venv.IsDefEqU d.uvars (((fs.take j).map (·.type)).reverse ++ Γ) D f.type ∧
      (∀ i, D.Skips 1 i → f.type.Skips 1 i) ∧
      venv.HasType d.uvars (((fs.take j).map (·.type)).reverse ++ Γ) f.type (.sort f.level) ∧
      f.level.WF d.uvars ∧
      d.RecArgWF venv (((fs.take j).map (·.type)).reverse ++ Γ) (k + j) f) →
    FieldsElab venv d Γ k Ds fs
  | _, _, [], [], _, _ => .nil
  | Γ, k, D :: Ds, f :: fs, hl, H => by
    obtain ⟨h1, hw, h2, h3, h4⟩ := H 0 D f rfl rfl
    refine .cons (by simpa using h1) hw (by simpa using h2) h3 (by simpa using h4)
      (FieldsElab.of_getElem (by simpa using hl) fun j D' f' e1 e2 => ?_)
    have := H (j + 1) D' f' (by simpa using e1) (by simpa using e2)
    simpa [List.take_succ_cons, Nat.add_assoc, Nat.add_comm 1 j] using this

/-- A type's sort is zero exactly when that of a definitionally equal type, in an agreeing
context, is. -/
theorem sort_zero_iff {env : VEnv} {U : Nat} (henv : env.WF) {Γ₁ Γ₂ : List VExpr}
    (hc : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂) (hΓ₂ : OnCtx Γ₂ (env.IsType U)) {D F : VExpr}
    {u v : VLevel} (hD : env.HasType U Γ₁ D (.sort u)) (hDF : env.IsDefEqU U Γ₂ D F)
    (hF : env.HasType U Γ₂ F (.sort v)) : (u ≈ .zero ↔ v ≈ .zero) := by
  have hD' := hD.defeqDFC henv.ordered hc
  obtain ⟨w, hw⟩ := hDF
  obtain ⟨_, h1⟩ := VEnv.IsDefEq.uniq henv hΓ₂ hD' hw
  obtain ⟨_, h2⟩ := VEnv.IsDefEq.uniq henv hΓ₂ hw hF
  have huv : u ≈ v :=
    VEnv.IsDefEqU.sort_inv henv hΓ₂ (VEnv.IsDefEqU.trans henv hΓ₂ ⟨_, h1⟩ ⟨_, h2⟩)
  change u.eval = _ ↔ v.eval = _
  rw [show u.eval = v.eval from huv]

/-- What `loopCtors` left of a constructor is what `Elaborates` asks of it, for any declaration
whose types agree with `d₀`'s on names and indices. -/
theorem CtorDone.elab {c : VContext} {pre : List Name} {params : List VExpr}
    {types : List InductiveType} {d₀ d : VInductDecl} {VB : VEnv} {UB j : Nat}
    {hj : j < types.length} {ct : Constructor} {cv : VConstructor}
    (H : CtorDone c pre params types d₀ VB UB j hj ct cv)
    (hPT : c.venv.IsTele c.lparams.length [] params)
    (hdu : d.uvars = c.lparams.length) (hdp : d.params = params)
    (htys : ∀ (i : Nat) (T : VInductiveType), d₀.types[i]? = some T →
      ∃ T' : VInductiveType, d.types[i]? = some T' ∧ T'.name = T.name ∧ T'.indices = T.indices ∧
        T'.nested = none) (hlenT : d.types.length = d₀.types.length)
    (hnotDefn : ∀ t ∈ types, ∀ v, c.env.find? t.name ≠ some (.defnInfo v)) :
    cv.name = ct.name ∧ TrExprS c.venv c.lparams [] ct.type cv.type ∧ ∃ ps Ds,
      ps.length = params.length ∧ Ds.length = cv.fields.length ∧
      cv.type = .foralls (ps ++ Ds) (.appN (.const types[j].name
        (VLevel.params c.lparams.length)) (VExpr.bvars params.length Ds.length ++ cv.indices)) ∧
      FieldsElab c.venv d d.params.reverse 0 Ds cv.fields ∧
      (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → cv.fields[k]? = some f →
        D.StripsToBy (fun n => n ∉ types.map (·.name) ∧ c.venv.AnnotDef n) f.type) ∧
      (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → cv.fields[k]? = some f → ∀ u,
        c.venv.HasType c.lparams.length ((Ds.take k).reverse ++ ps.reverse) D (.sort u) →
        (u ≈ .zero ↔ f.level ≈ .zero)) ∧
      ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → cv.fields[k]? = some f →
        f.type = D.stripN ((ct.type.domStrips.drop params.length)[k]?.getD 0) := by
  obtain ⟨C', ps, Ds, idx, ⟨htr, -, hsh, -, htele⟩, hout⟩ := H
  have henv : c.venv.WF := c.envAt.tr.wf
  have hnm : d.names = d₀.names := by
    refine List.ext_getElem (by simp [VInductDecl.names, hlenT]) fun i h1 h2 => ?_
    simp only [VInductDecl.names, List.getElem_map]
    obtain ⟨T', hT', hn, -⟩ := htys i _ (List.getElem?_eq_getElem (by simpa [VInductDecl.names] using h2))
    rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hT'), hn]
  refine ⟨hout.name, hout.type ▸ htr, ps, Ds, htele.length_eq, hout.len.symm,
    by rw [hout.type, hout.indices]; exact hsh, ?_, fun k D f hD hf =>
      (hout.within k D f hD hf).mono fun n ⟨⟨v, hv⟩, hA⟩ => ⟨fun hn => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn; exact hnotDefn t ht v hv, hA⟩, ?_, hout.views⟩
  · rw [hdp]
    refine FieldsElab.of_getElem (by rw [hout.len]) fun k D f hD hf =>
      ⟨hdu ▸ hout.defeq k D f hD hf, fun _ h => (hout.within k D f hD hf).toStripsTo.skips h,
        hdu ▸ (hout.sort k f hf).1,
        hdu ▸ (hout.sort k f hf).2, ?_⟩
    unfold VInductDecl.RecArgWF
    split
    · rename_i ra hra
      obtain ⟨T, hT, hl, hdef, hbm, him⟩ := hout.recArg k f ra hf hra
      obtain ⟨T', hT', hn, hi, hno⟩ := htys _ T hT
      refine ⟨T', VInductDecl.allTypes_getElem?_of_types hT', hi ▸ hl, ?_, hnm ▸ hbm, hnm ▸ him⟩
      rw [VInductiveType.typeApp_of_none hno, hdu, hdp, hn, Nat.zero_add]
      simpa [List.map_take] using hdef
    · trivial
  · intro k D f hD hf u hu
    have hkD : k < Ds.length := (List.getElem?_eq_some_iff.1 hD).1
    have hTD : c.venv.TeleDefEq c.lparams.length params.reverse (Ds.take k)
        ((cv.fields.take k).map (·.type)) := by
      refine teleDefEq_of_getElem (by simp [hout.len]) fun i D' F h1 h2 => ?_
      have hik : i < k := by
        have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
      rw [List.getElem?_take_of_lt hik] at h1
      simp only [List.getElem?_map, List.getElem?_take_of_lt hik, Option.map_eq_some_iff] at h2
      obtain ⟨f', hf', rfl⟩ := h2
      have := hout.defeq i D' f' h1 hf'
      rwa [List.map_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hik), ← List.map_take]
    have hFT : c.venv.IsTele c.lparams.length params.reverse ((cv.fields.take k).map (·.type)) := by
      refine VEnv.IsTele.of_getElem fun i hi => ?_
      have hik : i < k := by simp at hi; omega
      have hif : i < cv.fields.length := by simp at hi; omega
      have h1 := (hout.sort i cv.fields[i] (List.getElem?_eq_getElem hif)).1
      have e : ((cv.fields.take k).map (·.type)).take i = (cv.fields.take i).map (·.type) := by
        rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hik)]
      simp only [List.getElem_map, List.getElem_take, e]
      exact ⟨_, h1⟩
    have hTele := hPT.append (by simpa using hFT)
    have hc := VEnv.TeleDefEq.defeqCtx henv (htele.append (by simpa using hTD)) .zero trivial hTele
    simp only [List.reverse_append, List.append_nil] at hc
    have hΓ₂ := hTele.onCtx trivial
    simp only [List.reverse_append, List.append_nil] at hΓ₂
    exact sort_zero_iff henv hc hΓ₂ hu (by simpa [List.map_take] using hout.defeq k D f hD hf)
      (by simpa [List.map_take] using (hout.sort k f hf).1)

/-- The top `n` variables of `m`, moved onto `B`, which the rest of `m` lifts into by `ρ`. -/
def graft (B : TypeChecker.MLCtx) (ρ : Lift) : Nat → TypeChecker.MLCtx → TypeChecker.MLCtx
  | 0, _ => B
  | n + 1, .vlam fv name ty ty' bi m => .vlam fv name ty (ty'.lift' (ρ.consN n)) bi (graft B ρ n m)
  | n + 1, .vlet fv name ty v ty' v' m =>
    .vlet fv name ty v (ty'.lift' (ρ.consN n)) (v'.lift' (ρ.consN n)) (graft B ρ n m)
  | _ + 1, .nil => B

theorem graft_spec {env : VEnv} {Us : List Name} (henv : env.WF) {B : TypeChecker.MLCtx}
    {ρ : Lift} (hB : B.WF env Us) {fB : List FVarId} {tB : List VExpr} (hBT : B.IsTele fB tB) :
    ∀ (n : Nat) {m : TypeChecker.MLCtx} {fvs₁ fvs₂ : List FVarId} {tys₁ tys₂ : List VExpr},
    fvs₂.length = n → tys₂.length = n →
    m.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂) → m.WF env Us → (hk : n ≤ m.length) →
    VLCtx.FVLift' (m.dropN n hk).vlctx B.vlctx 0 ρ 0 → (∀ fv ∈ fvs₂, fv ∉ B.vlctx.fvars) →
    (graft B ρ n m).WF env Us ∧ VLCtx.FVLift' m.vlctx (graft B ρ n m).vlctx 0 (ρ.consN n) 0 ∧
    (graft B ρ n m).IsTele (fB ++ fvs₂) (tB ++ tys₂.zipIdx.map fun (A, j) => A.lift' (ρ.consN j)) ∧
    (∀ fv ∈ fvs₂, ((graft B ρ n m).lctx.find? fv).map LocalDecl.erase =
      (m.lctx.find? fv).map LocalDecl.erase) ∧
    (∀ fv ∈ B.vlctx.fvars, ((graft B ρ n m).lctx.find? fv).map LocalDecl.erase =
      (B.lctx.find? fv).map LocalDecl.erase) := by
  intro n
  induction n with
  | zero =>
    intro m fvs₁ fvs₂ tys₁ tys₂ h1 h2 _ _ hk W _
    obtain rfl := List.eq_nil_of_length_eq_zero h1
    obtain rfl := List.eq_nil_of_length_eq_zero h2
    refine ⟨hB, W, by simpa [graft] using hBT, by simp, fun _ _ => rfl⟩
  | succ n ih =>
    intro m fvs₁ fvs₂ tys₁ tys₂ h1 h2 hT hm hk W hfr
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at h1)
    obtain ⟨tys₂, ty', rfl⟩ : ∃ a b, tys₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys₂).resolve_left (by rintro rfl; simp at h2)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h1 h2
    generalize hF : fvs₁ ++ (fvs₂ ++ [fv]) = F at hT
    generalize hY : tys₁ ++ (tys₂ ++ [ty']) = Y at hT
    cases hT with
    | nil => simp at hF
    | @vlam m' fvs tys fv' name ty ty'' bi hT' =>
    rw [← List.append_assoc] at hF hY
    obtain ⟨rfl, e1⟩ := List.append_inj' hF rfl
    obtain ⟨rfl, e2⟩ := List.append_inj' hY rfl
    obtain rfl := List.singleton_inj.1 e1
    obtain rfl := List.singleton_inj.1 e2
    obtain ⟨hm', hfv, hty, hTy⟩ := hm
    have hk' : n ≤ m'.length := by simpa using hk
    obtain ⟨wf, W', tele, ag, agB⟩ := ih h1 h2 (by simpa using hT') hm' hk' (by simpa using W)
      (fun x hx => hfr x (by simp [hx]))
    have htr := wf.tr
    have hfvE : (graft B ρ n m').lctx.find? fv = none := by
      cases e : (graft B ρ n m').lctx.find? fv with
      | none => rfl
      | some d =>
        have hmem := htr.find?_eq_some.1 ⟨_, e⟩
        rw [tele.fvars] at hmem
        simp only [List.reverse_append, List.mem_append, List.mem_reverse] at hmem
        rcases hmem with hx | hx
        · have := hm'.tr.find?_eq_some.2 (show fv ∈ m'.vlctx.fvars by rw [hT'.fvars]; simp [hx])
          rw [hfv] at this; cases this.choose_spec
        · exact (hfr fv (by simp) (by rw [hBT.fvars]; simpa using hx)).elim
    have htyE := hty.weakFV' henv.ordered W' htr.wf
    have hTyE := hTy.weak' henv.ordered W'.toCtx
    simp only [Lift.consN] at hTyE
    refine ⟨⟨wf, hfvE, htyE, hTyE⟩, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have := W'.cons_fvar (fv, ty.fvarsList) (.vlam ty')
        (fun x hx => (fvarsIn_iff.1 hty.fvarsIn).1 x hx)
      simpa [graft, VLocalDecl.depth, VLocalDecl.lift', Lift.consN_consN, Nat.add_comm] using this
    · have := tele.vlam (fv := fv) (name := name) (ty := ty) (ty' := ty'.lift' (ρ.consN n))
        (bi := bi)
      simpa [graft, List.zipIdx_append, h2] using this
    · show Option.map _ (((graft B ρ n m').lctx.mkLocalDecl fv name ty bi).find? x) =
        Option.map _ ((m'.lctx.mkLocalDecl fv name ty bi).find? x)
      rw [LocalContext.find?_mkLocalDecl htr.1 hfvE, LocalContext.find?_mkLocalDecl hm'.tr.1 hfv]
      split
      · simp [LocalDecl.erase]
      · rename_i hne
        exact ag x (by
          simp only [List.mem_append, List.mem_singleton] at hx
          exact hx.resolve_right fun e => hne (by simp [e]))
    · show Option.map _ (((graft B ρ n m').lctx.mkLocalDecl fv name ty bi).find? x) = _
      rw [LocalContext.find?_mkLocalDecl htr.1 hfvE, if_neg]; · exact agB x hx
      simp only [beq_iff_eq]; rintro rfl; exact hfr _ (by simp) hx

/-- The block `d₀` heads, with its constructors `css`. -/
def blockDecl (d₀ : VInductDecl) (css : List (List VConstructor)) (ir le : Bool) : VInductDecl :=
  { d₀ with types := withCtors d₀.types css, isRec := ir, largeElim := le }

theorem blockDecl_ctors {d₀ : VInductDecl} {css : List (List VConstructor)} {ir le : Bool}
    (h : css.length = d₀.types.length) : (blockDecl d₀ css ir le).ctors = flatCtors css := by
  simp only [VInductDecl.ctors, flatCtors, blockDecl]
  congr 1
  refine List.ext_getElem (by simp [withCtors_length h, h]) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hj : j < css.length := by simpa using h2
  have := withCtors_getElem?_of (Ts := d₀.types) (List.getElem?_eq_getElem (by omega))
    (List.getElem?_eq_getElem hj)
  rw [List.getElem?_eq_getElem (by simpa using h1)] at this
  rw [Option.some.inj this]

theorem blockDecl_motiveTypes {d₀ : VInductDecl} {css : List (List VConstructor)} {ir le : Bool}
    (haux : d₀.aux = []) (h : css.length = d₀.types.length) (ls : List VLevel) (v : VLevel) :
    (blockDecl d₀ css ir le).motiveTypes ls v = d₀.motiveTypes ls v := by
  simp only [VInductDecl.motiveTypes, VInductDecl.allTypes_of_aux haux,
    VInductDecl.allTypes_of_aux (decl := blockDecl d₀ css ir le) haux]
  refine List.ext_getElem (by simp [blockDecl, withCtors_length h]) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hj : j < css.length := by simp at h2; omega
  have := withCtors_getElem?_of (Ts := d₀.types) (List.getElem?_eq_getElem (by simpa using h2))
    (List.getElem?_eq_getElem hj)
  rw [List.getElem?_eq_getElem (by simpa [blockDecl] using h1)] at this
  simp only [blockDecl] at this ⊢
  rw [Option.some.inj this]; rfl

theorem blockDecl_minorType {d₀ : VInductDecl} {css : List (List VConstructor)} {ir le : Bool}
    (haux : d₀.aux = []) (hno : ∀ T ∈ d₀.types, T.nested = none)
    (h : css.length = d₀.types.length) (ls : List VLevel) (q j : Nat) (c : VConstructor) :
    (blockDecl d₀ css ir le).minorType ls q j c = d₀.minorType ls q j c := by
  have hno' : ∀ T ∈ (blockDecl d₀ css ir le).allTypes, T.nested = none := by
    intro T hT
    rw [VInductDecl.allTypes_of_aux (decl := blockDecl d₀ css ir le) haux] at hT
    obtain ⟨⟨T₀, cs⟩, hm, rfl⟩ := List.mem_map.1 hT
    exact hno T₀ (List.of_mem_zip hm).1
  have e1 : (blockDecl d₀ css ir le).allTypes.length = d₀.allTypes.length := by
    simp [VInductDecl.allTypes, blockDecl, withCtors_length h]
  simp only [VInductDecl.minorType, VInductDecl.ctorAppAt_flat hno',
    VInductDecl.ctorAppAt_flat (d := d₀) (by rwa [VInductDecl.allTypes_of_aux haux]), e1]
  rfl

theorem _root_.Lean4Lean.VEnv.addConstList_le_of {env e env' : VEnv} :
    ∀ {cs : List (Name × VConstant)}, env.addConstList cs = some e → env ≤ env' →
      (∀ p ∈ cs, env'.constants p.1 = some p.2) → e ≤ env'
  | [], h, hle, _ => by cases h; exact hle
  | (n, ci) :: cs, h, hle, hc => by
    simp only [VEnv.addConstList, List.foldlM_cons] at h
    obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    refine VEnv.addConstList_le_of h2 ⟨fun {m a} hm => ?_, fun hd => ?_, fun hb => ?_⟩
      fun p hp => hc p (.tail _ hp)
    · rw [VEnv.addConst_constants_eq h1] at hm
      dsimp only at hm
      split at hm
      · subst_vars; cases hm; exact hc _ (.head _)
      · exact hle.1 hm
    · unfold VEnv.addConst at h1; split at h1 <;> cases h1; exact hle.2 hd
    · unfold VEnv.addConst at h1; split at h1 <;> cases h1; exact hle.3 hb

/-- The block with its constructors, from what its head and each constructor are typed from. -/
theorem recFacts_blockDecl {d₀ : VInductDecl} {css : List (List VConstructor)} {ir le : Bool}
    {env : VEnv} {U : Nat} {ls : List VLevel} (hB : d₀.BlockFacts env U ls)
    (hlen : css.length = d₀.types.length)
    (hC : ∀ j cs c, css[j]? = some cs → c ∈ cs → d₀.CtorFacts env U ls j c) :
    (blockDecl d₀ css ir le).RecFacts env U ls := by
  have hfacts : ∀ {j c}, (j, c) ∈ (blockDecl d₀ css ir le).ctors →
      d₀.CtorFacts env U ls j c := by
    intro j c hm
    obtain ⟨T, hT, hc⟩ := VInductDecl.mem_ctors_iff.1 hm
    obtain ⟨T₀, cs, -, hcs, rfl⟩ := withCtors_getElem? hT
    exact hC j cs c hcs hc
  have hno : ∀ T ∈ (blockDecl d₀ css ir le).types, T.nested = none := by
    intro T hT
    obtain ⟨⟨T₀, cs⟩, hm, rfl⟩ := List.mem_map.1 hT
    exact hB.nested T₀ (List.of_mem_zip hm).1
  refine VInductDecl.RecFacts.of_flat hB.aux hno hB.wf hB.params (fun {t T} h => ?_)
    (fun {t T} h => ?_) (fun hm => (hfacts hm).fields) (fun {j c T} hm hT => ?_)
    (fun {j c k f ra} hm hk hra => ?_)
  · obtain ⟨T₀, cs, h0, -, rfl⟩ := withCtors_getElem? h
    exact hB.indices (T := T₀) h0
  · obtain ⟨T₀, cs, h0, -, rfl⟩ := withCtors_getElem? h
    exact hB.type (T := T₀) h0
  · obtain ⟨T₀, cs, h0, -, rfl⟩ := withCtors_getElem? hT
    obtain ⟨T₁, h1, h2, h3⟩ := (hfacts hm).ctor
    obtain rfl := Option.some.inj (h1.symm.trans h0)
    exact ⟨h2, h3⟩
  · obtain ⟨T₀, h1, h2, h3⟩ := (hfacts hm).recArg hk hra
    have hi : ra.typeIdx < css.length := by
      have := (List.getElem?_eq_some_iff.1 h1).1; omega
    exact ⟨_, withCtors_getElem?_of h1 (List.getElem?_eq_getElem hi), h2, h3⟩

theorem _root_.Lean4Lean.TypeChecker.MLCtx.mkForall_congr {c : TypeChecker.MLCtx} {n n' : Nat}
    (e : n = n') (h h') (b : Expr) : c.mkForall n h b = c.mkForall n' h' b := by subst e; rfl

theorem _root_.Lean4Lean.TypeChecker.MLCtx.mkForall_dropN :
    ∀ (c : TypeChecker.MLCtx) (a b : Nat) (ha : a ≤ c.length) (hb) (h) (e : Expr),
    (c.dropN a ha).mkForall b hb (c.mkForall a ha e) = c.mkForall (a + b) h e
  | _, 0, b, _, _, _, e => by simp [TypeChecker.MLCtx.dropN]
  | .vlam x name ty ty' bi c, a + 1, b, ha, hb, h, e => by
    simp only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.mkForall]
    rw [TypeChecker.MLCtx.mkForall_dropN c a b _ hb (by simp [TypeChecker.MLCtx.length] at h; omega),
      TypeChecker.MLCtx.mkForall_congr (show a + 1 + b = (a + b) + 1 by omega) h
        (by simp [TypeChecker.MLCtx.length] at h ⊢; omega)]
    rfl
  | .vlet x name ty v ty' v' c, a + 1, b, ha, hb, h, e => by
    simp only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.mkForall]
    rw [TypeChecker.MLCtx.mkForall_dropN c a b _ hb (by simp [TypeChecker.MLCtx.length] at h; omega),
      TypeChecker.MLCtx.mkForall_congr (show a + 1 + b = (a + b) + 1 by omega) h
        (by simp [TypeChecker.MLCtx.length] at h ⊢; omega)]
    rfl

theorem getAppFn_abstract1 {I : Name} {us : List Level} {x : FVarId} :
    ∀ {e : Expr} {d : Nat}, e.getAppFn = .const I us → (e.abstract1 x d).getAppFn = .const I us
  | .app f _, d, h => by
    simp only [Expr.abstract1, Expr.getAppFn] at h ⊢; exact getAppFn_abstract1 h
  | .const .., _, h => by simpa [Expr.abstract1] using h
  | .bvar _, _, h | .fvar _, _, h | .mvar _, _, h | .sort _, _, h | .lam .., _, h
  | .forallE .., _, h | .letE .., _, h | .lit _, _, h | .mdata .., _, h | .proj .., _, h => by
    simp [Expr.getAppFn] at h

theorem MajorAt.abstract1 {I : Name} {x : FVarId} :
    ∀ {k : Nat} {e : Expr} {d : Nat}, MajorAt I k e → MajorAt I k (e.abstract1 x d)
  | 0, .forallE .., _, ⟨us, h⟩ => ⟨us, getAppFn_abstract1 h⟩
  | k + 1, .forallE .., _, h => MajorAt.abstract1 (k := k) h

theorem MajorAt.mkForall {I : Name} {k : Nat} : ∀ {c : TypeChecker.MLCtx} {fvs tys},
    c.IsTele fvs tys → ∀ (m : Nat) (hm : m ≤ c.length) {e : Expr}, MajorAt I k e →
      MajorAt I (k + m) (c.mkForall m hm e)
  | _, _, _, _, 0, _, _, h => h
  | _, _, _, .vlam (fv := x) (name := name) (ty := ty) (bi := bi) hT, m + 1, hm, e, h => by
    simp only [TypeChecker.MLCtx.mkForall]
    rw [show k + (m + 1) = (k + 1) + m by omega]
    exact MajorAt.mkForall hT m _ (e := .forallE name ty (e.abstract1 x) bi)
      (MajorAt.abstract1 (k := k) h)

/-- Nested `mkForall`s over consecutive segments of the top of a telescope context. -/
theorem mkForall_nest {env : VEnv} {Us : List Name} (henv : env.WF) {lctx : LocalContext} :
    ∀ (segs : List (List FVarId)) (tyss : List (List VExpr)) {E : TypeChecker.MLCtx}
    {Bfvs : List FVarId} {Btys : List VExpr}, E.WF env Us →
    E.IsTele (Bfvs ++ segs.flatten) (Btys ++ tyss.flatten) →
    List.Forall₂ (fun (s : List FVarId) (t : List VExpr) => s.length = t.length) segs tyss →
    (∀ x ∈ segs.flatten, (lctx.find? x).map LocalDecl.erase =
      (E.lctx.find? x).map LocalDecl.erase) →
    ∀ {e : Expr} {e' : VExpr}, TrExprS env Us E.vlctx e e' →
      env.IsType Us.length E.vlctx.toCtx e' →
    ∃ hk : segs.flatten.length ≤ E.length,
      segs.foldr (fun s acc => lctx.mkForall (s.map .fvar).toArray acc) e =
        E.mkForall segs.flatten.length hk e ∧
      TrExprS env Us (E.dropN segs.flatten.length hk).vlctx
        (segs.foldr (fun s acc => lctx.mkForall (s.map .fvar).toArray acc) e)
        (.foralls tyss.flatten e') ∧
      env.IsType Us.length (E.dropN segs.flatten.length hk).vlctx.toCtx (.foralls tyss.flatten e')
  | [], [], _, _, _, _, _, _, _, _, _, he, heT => ⟨Nat.zero_le _, rfl, he, heT⟩
  | s :: segs, t :: tyss, E, Bfvs, Btys, hE, hT, .cons hl hrest, hag, e, e', he, heT => by
    have hT' : E.IsTele ((Bfvs ++ s) ++ segs.flatten) ((Btys ++ t) ++ tyss.flatten) := by
      simpa using hT
    obtain ⟨hk₁, eq₁, tr₁, ty₁⟩ := mkForall_nest henv (lctx := lctx) segs tyss hE hT' hrest
      (fun x hx => hag x (by simp only [List.flatten_cons]; exact List.mem_append_right _ hx))
      he heT
    have hrl : segs.flatten.length = tyss.flatten.length :=
      List.Forall₂.length_flatten (fun _ _ h => h) hrest
    obtain ⟨-, -, -, -, hT₁⟩ := hT'.vlctx_split segs.flatten.length rfl hrl hk₁
    have hE₁ := hE.dropN _ hk₁
    obtain ⟨hk₂, eq₂, tr₂, ty₂⟩ := mkForall_tele (lctx := lctx) henv hE₁ hT₁ hl
      (fun x hx => by
        rw [hag x (by simp only [List.flatten_cons]; exact List.mem_append_left _ hx)]
        rw [hE.find?_dropN _ hk₁ (by rw [hT₁.fvars]; simp [hx])]) tr₁ ty₁
    have hlen : (s :: segs).flatten.length = segs.flatten.length + s.length := by
      rw [List.flatten_cons, List.length_append, Nat.add_comm]
    have hk' : segs.flatten.length + s.length ≤ E.length := by
      have := TypeChecker.MLCtx.length_dropN E _ hk₁; omega
    have hk : (s :: segs).flatten.length ≤ E.length := hlen ▸ hk'
    have e₂ : (E.dropN segs.flatten.length hk₁).dropN s.length hk₂ =
        E.dropN (s :: segs).flatten.length hk := by
      rw [TypeChecker.MLCtx.dropN_dropN E _ _ hk₁ hk₂ hk']
      exact TypeChecker.MLCtx.dropN_congr hlen.symm _ _
    refine ⟨hk, ?_, ?_, ?_⟩
    · simp only [List.foldr_cons]
      rw [eq₂, eq₁, TypeChecker.MLCtx.mkForall_dropN E _ _ hk₁ hk₂ hk']
      exact TypeChecker.MLCtx.mkForall_congr hlen.symm _ _ _
    · rw [← e₂]
      simp only [List.foldr_cons, List.flatten_cons, VExpr.foralls_append]
      rw [eq₂]; exact tr₂
    · rw [← e₂]
      simp only [List.flatten_cons, VExpr.foralls_append]
      exact ty₂

/-- The variables `loopInd1` opened for one type are not another's motive. -/
theorem blocks_ne_motive {tds : List TyData} {base : List FVarId}
    (h : ((tds.reverse.map TyData.block).flatten ++ base).Nodup) {i j : Nat} {td td' : TyData}
    (hi : tds[i]? = some td) (hj : tds[j]? = some td') {x : FVarId}
    (hx : x ∈ td.fvs ++ [td.major]) : x ≠ td'.motive := by
  obtain ⟨hnd, hpw⟩ := (List.pairwise_flatten (R := (· ≠ ·))).1 (List.nodup_append.1 h).1
  rw [List.map_reverse, List.pairwise_reverse] at hpw
  have hxb : x ∈ td.block := by
    simp only [TyData.block, List.mem_cons, List.mem_reverse]
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx <;> simp [hx]
  have hmb : td'.motive ∈ td'.block := by simp [TyData.block]
  rintro rfl
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have hjl : j < tds.length := (List.getElem?_eq_some_iff.1 hj).1
    have := List.pairwise_iff_getElem.1 (List.pairwise_map.1 hpw) i j (by omega) hjl hij
    rw [Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hi),
      Option.some.inj ((List.getElem?_eq_getElem hjl).symm.trans hj)] at this
    exact this _ hmb _ hxb rfl
  · obtain rfl := Option.some.inj (hi.symm.trans hj)
    have : td.block.Nodup :=
      hnd td.block (List.mem_map_of_mem (List.mem_reverse.2 (List.mem_of_getElem? hi)))
    simp only [TyData.block, List.nodup_cons, List.mem_cons, List.mem_reverse, not_or] at this
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact this.1.2 hx
    · exact this.1.1 hx
  · have hil : i < tds.length := (List.getElem?_eq_some_iff.1 hi).1
    have := List.pairwise_iff_getElem.1 (List.pairwise_map.1 hpw) j i (by omega) hil hij
    rw [Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hj),
      Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans hi)] at this
    exact this _ hxb _ hmb rfl

/-- A recursor's conclusion, the motive at the indices and the major premise, translates over a
view `E` of the kernel's context holding the indices and the major premise on top, once the
translation is typed. -/
theorem recBody_tr {env : VEnv} {Us : List Name} (henv : env.WF) {E : TypeChecker.MLCtx}
    (hE : E.WF env Us) {Ofvs fvs : List FVarId} {major : FVarId} {Otys Itys : List VExpr}
    {majT : VExpr} (hT : E.IsTele (Ofvs ++ fvs ++ [major]) (Otys ++ Itys ++ [majT]))
    {mfv : FVarId} {mpos : Nat} {mty : VExpr}
    (hm : E.vlctx.find? (.inr mfv) = some (.bvar mpos, mty)) {v : VLevel}
    (hty : env.HasType Us.length E.vlctx.toCtx
      (.app (.appN (.bvar mpos) (VExpr.bvars fvs.length 1)) (.bvar 0)) (.sort v)) :
    TrExprS env Us E.vlctx (.app (mkAppN (.fvar mfv) (fvs.map .fvar).toArray) (.fvar major))
      (.app (.appN (.bvar mpos) (VExpr.bvars fvs.length 1)) (.bvar 0)) := by
  have hΓ := hE.tr.wf.toCtx
  obtain ⟨A, B, hF, hA⟩ := VExpr.WF.app_inv henv.ordered hΓ ⟨_, hty⟩
  have hnd : (Ofvs ++ fvs ++ [major]).Nodup := by
    have := hE.fvars_nodup; rw [hT.fvars] at this; exact List.nodup_reverse.1 this
  have hall := hT.fvars_tr (env := env) (Us := Us) hnd
  have hb : VExpr.bvars (Ofvs ++ fvs ++ [major]).length 0 =
      VExpr.bvars Ofvs.length (fvs.length + 1) ++ VExpr.bvars fvs.length 1 ++
        VExpr.bvars 1 0 := by
    have e1 := VExpr.bvars_append Ofvs.length (fvs.length + 1) 0
    have e2 := VExpr.bvars_append fvs.length 1 0
    simp only [Nat.add_zero] at e1 e2
    simp only [List.append_assoc, e2, e1, List.length_append, List.length_singleton]
  rw [hb, List.map_append, List.map_append] at hall
  have h1 := List.Forall₂.take_append (by simp [VExpr.bvars]) hall
  have hFv := List.Forall₂.drop_append (by simp [VExpr.bvars]) h1
  have hMj := List.Forall₂.drop_append (by simp [VExpr.bvars]) hall
  have trF := TrExprS.mkAppN_of_wf henv.ordered hΓ (.fvar hm) hFv ⟨_, hF⟩
  cases hMj with | cons hmaj _ => ?_
  exact .app hF (by simpa [VExpr.bvars] using hA) trF (by simpa [VExpr.bvars] using hmaj)

theorem _root_.List.Forall₂.of_mem_zipWith {R : α → β → Prop} {f : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ List.zipWith f l₁ l₂,
      ∃ a ∈ l₁, ∃ b, R a b ∧ x = f a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hab h, x, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, .head _, _, hab, rfl⟩
    · obtain ⟨a, ha, b, h1, h2⟩ := h.of_mem_zipWith x hm
      exact ⟨a, .tail _ ha, b, h1, h2⟩

theorem zipIdx_lift'_eq_liftTele (n : Nat) : ∀ (As : List VExpr) (k : Nat),
    (As.zipIdx k).map (fun (A, j) => A.lift' ((Lift.skipN .refl n).consN j)) =
      VExpr.liftTele n As k
  | [], _ => rfl
  | A :: As, k => by
    have := zipIdx_lift'_eq_liftTele n As (k + 1)
    simp only [VExpr.lift'_consN_skipN] at this
    simp only [List.zipIdx_cons, List.map_cons, VExpr.liftTele, VExpr.lift'_consN_skipN, this]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.vlctx_nil {m : TypeChecker.MLCtx}
    {tys : List VExpr} (h : m.IsTele [] tys) : m.vlctx = [] := by
  generalize hf : ([] : List FVarId) = F at h
  cases h with
  | nil => rfl
  | vlam => simp at hf

theorem _root_.Lean.Level.LParamsIn_true (l : Level) : l.LParamsIn fun _ => True := by
  induction l <;> simp_all [Level.LParamsIn]

theorem _root_.Lean.Literal.SuppIn.mono' {C C' : Name → Prop} (H : ∀ n, C n → C' n) {l : Literal}
    (h : l.SuppIn C) : l.SuppIn C' := by
  cases l <;> simp only [Literal.SuppIn] at h ⊢ <;> simp_all

/-- An expression in which `indOccP` finds no type of the block does not mention one, when its
literals do not. -/
theorem _root_.Lean4Lean.TrExprS.suppInB {env : VEnv} {Us : List Name} {B : Name → Prop}
    {indConsts : Array Expr} (hB : ∀ n us, indOccP indConsts (.const n us) = false → ¬B n)
    (hlit : ∀ l, env.ContainsLits l → l.SuppIn fun n => ¬B n) {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') (ho : e.anySub (indOccP indConsts) = false) :
    e.SuppIn (BFree B) := by
  induction H with
  | bvar | fvar => trivial
  | sort => exact Level.LParamsIn_true _
  | const =>
    refine ⟨hB _ _ (by simpa [Expr.anySub] using ho), fun u _ => Level.LParamsIn_true u⟩
  | app _ _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at ho; exact ⟨ih1 ho.1.2, ih2 ho.2⟩
  | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at ho; exact ⟨ih1 ho.1.2, ih2 ho.2⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at ho; exact ⟨ih1 ho.1.1.2, ih2 ho.1.2, ih3 ho.2⟩
  | lit h => exact hlit _ h
  | mdata _ ih | proj _ _ ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at ho; exact ih ho.2

/-- A type in which `isRec` finds no type of the block has binder domains mentioning none. -/
theorem spineIn_of_isRec {env : VEnv} {Us : List Name} {B : Name → Prop}
    {indConsts : Array Expr} (hB : ∀ n us, indOccP indConsts (.const n us) = false → ¬B n)
    (hlit : ∀ l, env.ContainsLits l → l.SuppIn fun n => ¬B n) :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, TrExprS env Us Δ e e' →
      isRec.loop indConsts e = false → spineIn (BFree B) e
  | _, .forallE .., _, H, hr => by
    cases H with | forallE _ _ hdom hbody => ?_
    simp only [isRec.loop, Bool.or_eq_false_iff] at hr
    exact ⟨hdom.suppInB hB hlit (by rw [← hasIndOcc_eq]; exact hr.1),
      spineIn_of_isRec hB hlit hbody hr.2⟩
  | _, .bvar _, _, _, _ | _, .fvar _, _, _, _ | _, .mvar _, _, _, _ | _, .sort _, _, _, _
  | _, .const .., _, _, _ | _, .app .., _, _, _ | _, .lam .., _, _, _ | _, .letE .., _, _, _
  | _, .lit _, _, _, _ | _, .mdata .., _, _, _ | _, .proj .., _, _, _ => trivial

/-- The names `mkRecInfos` keeps out of the inductive hypotheses' binders include the block's types. -/
theorem blockNames_contains (types : List InductiveType) : ∀ t ∈ types,
    (types.toArray.foldl (init := ({} : NameSet)) fun s t =>
      t.ctors.foldl (·.insert ·.name) (s.insert t.name)).contains t.name := by
  intro t ht
  rw [← Array.foldl_toList]
  exact ns_foldl_types_contains_mem (s := ({} : NS)) types ⟨t, ht, .inl rfl⟩

/-- A block's indices are a telescope in the environment before the block, unless the block is
primitive. -/
def IndicesE (c₀ : VContext) (types : List InductiveType) (d : VInductDecl) : Prop :=
  (∀ t ∈ types, Environment.primitives.contains t.name = false) →
    ∀ T ∈ d.types, c₀.venv.IsTele c₀.lparams.length d.params.reverse T.indices

/-- `mkRecInfos` in an environment `envCA` that has the block's constructors as axioms, beside the
checking environment of `c`: they are new there, the names `X`, unless the block is primitive and
`c`'s environment has them already. Its constructors' fields are read as `d`'s fields, which `run`
then builds the recursors from. -/
theorem mkRecInfos.WF_core {c₀ c₁ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c₁ params level typeTr)
    (hc : c.mlctx = c₁.mlctx) (hU : c.lparams = c₁.lparams) (hle : c₀.venv ≤ c.venv)
    (henv : c.venv.WF) (hNM : NotMentionsOK c.venv c.lparams stats types) {isUnsafe : Bool}
    (hC : ∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c.venv c.lparams d t nidx ct)
    (hCt : ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors,
      ∃ C', TrExprS c.venv c.lparams [] ct.type C')
    (hconst : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t →
      typeTr[j]? = some T' → c.venv.constants t.name = some ⟨c.lparams.length, T'⟩)
    (hwf₀ : c₀.venv.WF) (hprim₀ : c₀.venv.HasPrimitives)
    (hfresh₀ : ∀ t ∈ types, c₀.venv.constants t.name = none)
    (hnames : (types.map (·.name)).Nodup)
    (hclosed : ConstMap.Closed c.env.constants) (hUs : c.lparams.Nodup)
    (hdummy : ∀ t ∈ types, t.name ≠ `_inhabitedExprDummy)
    (hnonPrim : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors,
      spineIn (BFree (· ∈ types.map (·.name))) ct.type →
      params.length < declareConstructors.arity 0 ct.type →
      ∀ t' ∈ types, Environment.primitives.contains t'.name = false)
    (henvB : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors,
      spineIn (BFree (· ∈ types.map (·.name))) ct.type →
      params.length < declareConstructors.arity 0 ct.type →
      ∀ n ci, c.env.find? n = some ci → n ∉ types.map (·.name) →
        ci.SuppIn fun m => m ∉ types.map (·.name))
    (hlit : isRec types.toArray stats.indConsts = false →
      ∀ l, c.venv.ContainsLits l → l.SuppIn fun n => n ∉ types.map (·.name))
    {envCA : Environment} {venvC : VEnv} (hVC : VEnvAt envCA c.safety venvC)
    (hleC : c.venv ≤ venvC) {X : Name → Prop}
    (hXenv : ∀ n, ¬X n → envCA.find? n = c.env.find? n)
    (hXdefn : ∀ n v, envCA.find? n = some (.defnInfo v) → ¬X n)
    (hXfresh : ∀ n, X n → c.env.find? n = none ∧ n ≠ `_inhabitedExprDummy ∧
      Environment.primitives.contains n = false)
    (hclosedCA : ConstMap.Closed envCA.constants) (hquotCA : envCA.quotInit = c.env.quotInit)
    (hnotDefn : ∀ t ∈ types, ∀ v, envCA.find? t.name ≠ some (.defnInfo v))
    (hCtorC : ∀ (j : Nat) (t : InductiveType) ct C', types[j]? = some t → ct ∈ t.ctors →
      TrExprS c.venv c.lparams [] ct.type C' →
      venvC.constants ct.name = some ⟨c.lparams.length, C'⟩)
    (hVCC : ∀ envC : VEnv, c.venv ≤ envC →
      (∀ (j : Nat) (t : InductiveType) ct C', types[j]? = some t → ct ∈ t.ctors →
        TrExprS c.venv c.lparams [] ct.type C' →
        envC.constants ct.name = some ⟨c.lparams.length, C'⟩) → venvC ≤ envC)
    {elimLevel : Level} (hE : elimLevel = .zero ∨ ∃ u, elimLevel = .param u ∧ u ∉ c.lparams)
    (hEsim : (∀ t ∈ types, Environment.primitives.contains t.name = false) →
      (∀ n, n ∉ types.map (·.name) → c.env.find? n = c₁.env.find? n) ∧
      (∀ t ∈ types, c₁.env.find? t.name = none) ∧ ConstMap.Closed c₁.env.constants ∧
      c.env.quotInit = c₁.env.quotInit ∧ c.safety = c₁.safety ∧ c.fuel = c₁.fuel)
    {k : Array RecInfo → M α} {Q}
    (H : ∀ recInfos c' d,
      RecInfosData c nparams types stats params level typeTr isUnsafe elimLevel recInfos c' d →
      IndicesE c₀ types d → WF c' (k recInfos) Q) :
    WF (c.withEnv envCA venvC hVC hleC)
      (withReader (fun ctx => { ctx with lparams := getRecLevelParams elimLevel ctx.lparams }) <|
        mkRecInfos stats types.toArray elimLevel k) Q := by
  have henvT : c.venv.WF := henv
  -- the constructors' types are types, read off any declaration agreeing with the checks
  obtain ⟨d₁, hd₁⟩ := compat_exists c.lparams params level isUnsafe types stats.nindices
    (by rw [hT.nindices])
  -- the recursor's level parameters
  obtain ⟨pre, ml, hpre, hrl, hml, hprel⟩ : ∃ (pre : List Name) (ml : VLevel),
      (∀ u ∈ pre, u ∉ c.lparams) ∧
      (∀ l, getRecLevelParams elimLevel l = pre ++ l) ∧
      VLevel.ofLevel (pre ++ c.lparams) elimLevel = some ml ∧ pre.length ≤ 1 := by
    rcases hE with rfl | ⟨u, rfl, hu⟩
    · exact ⟨[], .zero, nofun, fun _ => rfl, rfl, by simp⟩
    · refine ⟨[u], .param 0, by simpa using hu, fun _ => rfl, ?_, by simp⟩
      simp [VLevel.ofLevel]
  have hwr : (fun (ctx : Context) => { ctx with lparams := getRecLevelParams elimLevel ctx.lparams })
      = fun ctx => { ctx with lparams := pre ++ ctx.lparams } := by
    funext ctx; rw [hrl]
  rw [hwr]
  refine WF.withLParams (c := c.withEnv envCA venvC hVC hleC) hpre ?_
  have hcbl : (VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
      hpre).lparams = pre ++ c.lparams := rfl
  have hcbenv : (VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
      hpre).env = envCA := rfl
  have hcbvenv : (VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
      hpre).venv = venvC := rfl
  have hcbml : (VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
      hpre).mlctx = c.mlctx.instL (VLevel.shift pre.length c.lparams.length) := rfl
  have hcblctx : (VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
      hpre).lctx = c.lctx := rfl
  have hcbsafety : (VContext.withLParams (c.withEnv envCA venvC hVC hleC)
      pre hpre).safety = c.safety := rfl
  have hcbfuel : (VContext.withLParams (c.withEnv envCA venvC hVC hleC)
      pre hpre).fuel = c.fuel := rfl
  have hcbng : (VContext.withLParams (c.withEnv envCA venvC hVC hleC)
      pre hpre).ngen = c.ngen := rfl
  have hcbap : (VContext.withLParams (c.withEnv envCA venvC hVC hleC)
      pre hpre).allowPrimitive = c.allowPrimitive := rfl
  generalize VContext.withLParams (c.withEnv envCA venvC hVC hleC) pre
    hpre = cb at hcbl hcbenv hcbvenv hcbml hcblctx hcbsafety hcbfuel hcbng hcbap ⊢
  -- the parameters, as the small context the normalizations run in
  obtain ⟨kp, hkp, pfvs, hMpT', hpar⟩ := hT.paramsCtx
  have hkp' : kp ≤ c.mlctx.length := by rw [hc]; exact hkp
  have hMpeq : c.mlctx.dropN kp hkp' = c₁.mlctx.dropN kp hkp :=
    TypeChecker.MLCtx.dropN_of_eq hc _ _
  generalize hMpdef : c.mlctx.dropN kp hkp' = Mp
  have hMpT : Mp.IsTele pfvs params := by rw [← hMpdef, hMpeq]; exact hMpT'
  have hMp : Mp.WF c.venv c.lparams := hMpdef ▸ c.mlctx_wf.dropN kp hkp'
  have mapWF := c.envAt.tr.map_wf
  have hsub : ∃ ρp, Sub X pre ρp (c.small Mp hMp) cb := by
    obtain ⟨ρp, W⟩ := TypeChecker.MLCtx.fvlift_dropN
      (c.mlctx.instL (VLevel.shift pre.length c.lparams.length)) kp
      (by rw [TypeChecker.MLCtx.length_instL]; exact hkp')
    rw [TypeChecker.MLCtx.dropN_instL _ _ _ hkp', hMpdef] at W
    refine ⟨ρp, {
      lparams := hcbl
      pre_fresh := hpre
      lift := by rw [hcbml]; exact W
      lctx := fun fv hfv => ?_
      venv := by rw [hcbvenv]; exact hleC
      env := fun n hn => ?_
      defn := fun n v hv hX => ?_
      fresh := fun n hX => ?_
      closed := hclosed
      closedB := ?_
      quotInit := by rw [hcbenv]; exact hquotCA
      safety := hcbsafety
      fuel := hcbfuel
      eagerReduce := rfl
      notKernel := fun fv hfv => c.notKernel fv
        (TypeChecker.MLCtx.dropN_fvars_subset kp hkp' (by rw [hMpdef]; exact hfv)) }⟩
    · rw [hcblctx, ← c.lctx_eq]
      show _ = Option.map _ (Mp.lctx.find? fv)
      have hfv' : fv ∈ (c.mlctx.dropN kp hkp').vlctx.fvars := hMpdef ▸ hfv
      rw [← hMpdef, c.mlctx_wf.find?_dropN kp hkp' hfv']
    · rw [hcbenv]; exact hXenv n hn
    · rw [hcbenv] at hv; exact hXdefn n v hv hX
    · exact hXfresh n hX
    · rw [hcbenv]; exact hclosedCA
  obtain ⟨ρp, hsub⟩ := hsub
  -- what `loopInd1` starts from
  have hlp₀ : c.lparams = c₀.lparams := hU.trans hT.base.lparams
  have hpnd : (pre ++ c.lparams).Nodup :=
    List.nodup_append.2 ⟨by
      rcases pre with _ | ⟨u, _ | ⟨v, w⟩⟩ <;> simp at hprel ⊢, hUs,
      fun a ha b hb e => hpre a ha (e ▸ hb)⟩
  have hRS : RecSetup c pre Mp pfvs params level ml types typeTr stats elimLevel envCA := {
    MpT := hMpT
    par := hpar
    levels := by rw [hlp₀]; exact hT.levels
    indConsts := by have := hT.indConsts; rwa [List.take_length] at this
    nindices := hT.nindices
    typeTr_len := hT.typeTr_length
    decl := fun j t T' hj hT' => by
      obtain ⟨idx, u, h1, h2, h3, h4, h5, -⟩ := hT.types j t T' hj hT'
      rw [← hlp₀] at h1 h2 h3
      exact ⟨idx, u, h1.mono hle, h2.mono hle, h3.mono hle, h4, h5⟩
    const := hconst
    notDefn := hnotDefn
    ml := hml
    lpnd := hpnd
    levelWF := by rw [hlp₀]; exact .of_ofLevel hT.resultLevel }
  -- the context the indices are read off in: the environment before the block, unless the block
  -- is primitive
  obtain ⟨cE, XE, hMpE, hEv, hEl, hdeclE, ⟨ρE, hsubE⟩, hcE⟩ : ∃ (cE : VContext) (XE : Name → Prop)
      (hMpE : Mp.WF cE.venv cE.lparams), cE.venv ≤ c.venv ∧ cE.lparams = c.lparams ∧
      (∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t →
        typeTr[j]? = some T' → ∃ idx₀ u,
        TrExprS cE.venv cE.lparams [] t.type T' ∧ cE.venv.IsType cE.lparams.length [] T' ∧
        cE.venv.IsDefEqU cE.lparams.length [] T' (.foralls (params ++ idx₀) (.sort u)) ∧
        u ≈ level ∧ stats.nindices[j]? = some idx₀.length) ∧
      (∃ ρ, Sub XE pre ρ (cE.small Mp hMpE) cb) ∧
      ((∀ t ∈ types, Environment.primitives.contains t.name = false) →
        cE.venv = c₀.venv ∧ cE.lparams = c₀.lparams) := by
    by_cases hSE : ∀ t ∈ types, Environment.primitives.contains t.name = false
    · obtain ⟨hEenv, hEfresh, hEclosed, hEq, hEs, hEf⟩ := hEsim hSE
      have hMpE : Mp.WF c₁.venv c₁.lparams := by
        rw [← hMpdef, hMpeq]; exact c₁.mlctx_wf.dropN kp hkp
      refine ⟨c₁, fun n => X n ∨ n ∈ types.map (·.name), hMpE, ?_, hU.symm, ?_, ⟨ρp, ?_⟩,
        fun _ => ⟨hT.base.venv, hT.base.lparams⟩⟩
      · rw [hT.base.venv]; exact hle
      · intro j t T' hj hT'
        obtain ⟨idx, u, h1, h2, h3, h4, h5, -⟩ := hT.types j t T' hj hT'
        rw [hT.base.venv, hT.base.lparams]
        exact ⟨idx, u, h1, h2, h3, h4, h5⟩
      · exact {
          lparams := by rw [hsub.lparams]; simp [hU]
          pre_fresh := by simpa [hU] using hsub.pre_fresh
          lift := by simpa [hU] using hsub.lift
          lctx := hsub.lctx
          venv := by rw [hcbvenv]; exact (hT.base.venv ▸ hle).trans hleC
          env := fun n hn => by
            simp only [not_or] at hn
            rw [hcbenv, hXenv n hn.1]; exact hEenv n hn.2
          defn := fun n v hv hX => by
            rcases hX with hX | hX
            · exact hXdefn n v (hcbenv ▸ hv) hX
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hX
              exact hnotDefn t ht v (hcbenv ▸ hv)
          fresh := fun n hX => by
            by_cases hn : n ∈ types.map (·.name)
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
              exact ⟨hEfresh t ht, hdummy t ht, hSE t ht⟩
            · have h := hXfresh n (hX.resolve_right hn)
              exact ⟨(hEenv n hn) ▸ h.1, h.2⟩
          closed := hEclosed
          closedB := hsub.closedB
          quotInit := hsub.quotInit.trans hEq
          safety := hsub.safety.trans hEs
          fuel := hsub.fuel.trans hEf
          eagerReduce := rfl
          notKernel := hsub.notKernel }
    · exact ⟨c, X, hMp, VEnv.LE.rfl, rfl, hRS.decl, ⟨ρp, hsub⟩, fun h => absurd h hSE⟩
  rw [mkRecInfos]
  refine loopInd1.WF (X := X) (hMp := hMp) (VB := venvC) (base := cb.mlctx.vlctx.fvars) hRS
    (blockNames_contains types) hNM (cE := cE) (XE := XE) (hMpE := hMpE) hEv hEl hdeclE
    ?cont types.length
    [] cb (by simp) ⟨⟨ρp, hsub⟩, ⟨ρp, hsub.ext⟩, hcbenv, hcbvenv, hcbap, by simp, by simp, by simp,
      fun _ _ h => by simp at h, ⟨ρE, hsubE⟩, fun _ _ h => by simp at h⟩
  case cont =>
  intro tds cb₁ htds hI1
  obtain ⟨ρp₁, hsub₁⟩ := hI1.sub
  obtain ⟨ρB₁, hB₁⟩ := hI1.bext
  have hlp₁ : cb₁.lparams = pre ++ c.lparams := hsub₁.lparams
  have hshl : (VLevel.shift pre.length c.lparams.length).length = c.lparams.length := by
    simp [VLevel.shift]
  have hshwf : ∀ l ∈ VLevel.shift pre.length c.lparams.length,
      l.WF (pre ++ c.lparams).length := by
    simpa using VLevel.shift_wf (k := pre.length) (n := c.lparams.length)
  have hVCle : c.venv ≤ venvC := hleC
  have hVCwf : venvC.WF := hVC.tr.wf
  have htdlen : tds.length = types.length := htds
  let d₀ : VInductDecl :=
    ⟨c.lparams.length, params, level, headTypes types typeTr tds, false, false, isUnsafe, []⟩
  have hty : ∀ (j : Nat) (T : VInductiveType), d₀.types[j]? = some T → ∃ (t : InductiveType) (T' : VExpr) (td : TyData)
      (nidx : Nat), types[j]? = some t ∧
      typeTr[j]? = some T' ∧ tds[j]? = some td ∧ stats.nindices[j]? = some nidx ∧
      T = ({ name := t.name, type := T', indices := td.idx, ctors := [] } : VInductiveType) ∧
      TypeVarsAt c pre Mp pfvs params level ml t T' nidx td.info td.idx cb₁ td.fvs td.major
        td.motive td.m ∧
      td.mtr = motiveTy t.name c.lparams.length params.length
        (VLevel.shift pre.length c.lparams.length) td.idx ml := by
    intro j T hT
    obtain ⟨t, T', td, h1, h2, h3, rfl⟩ := headTypes_getElem? hT
    obtain ⟨t', T'', nidx, h1', h2', h4, htv⟩ := hI1.recs j td h3
    obtain ⟨t'', h1'', hmtr⟩ := hI1.mtr j td h3
    obtain rfl := Option.some.inj (h1.symm.trans h1')
    obtain rfl := Option.some.inj (h1.symm.trans h1'')
    obtain rfl := Option.some.inj (h2.symm.trans h2')
    exact ⟨t, T', td, nidx, h1, h2, h3, h4, rfl, htv, hmtr⟩
  have hBF : d₀.BlockFacts venvC (pre ++ c.lparams).length
      (VLevel.shift pre.length c.lparams.length) := {
    wf := hVCwf
    aux := rfl
    nested := headTypes_nested
    params := by
      have := hT.params_tele.instL hshwf
      simp only [List.map_nil] at this
      exact this.mono (hle.trans hVCle)
    indices := fun {j T} hT => by
      obtain ⟨t, T', td, nidx, -, -, -, -, rfl, htv, -⟩ := hty j T hT
      have h1 := (htv.tele.isTele htv.wf).append_inv.1.append_inv.2
      have h2 := h1.instL hshwf
      simp only [List.append_nil, List.map_reverse] at h2
      exact h2.mono hVCle
    type := fun {j T} hT => by
      obtain ⟨t, T', td, nidx, h1, h2, -, -, rfl, htv, -⟩ := hty j T hT
      have hc := VEnv.HasType.const (Γ := []) (hVCle.1 (hconst j t T' h1 h2)) hshwf (by simp [hshl])
      have hd := (htv.defeq.instL hshwf).mono hVCle
      simp only [VExpr.instL_foralls, List.map_append, VExpr.instL, List.map_nil] at hd
      exact hc.defeqU_r hVCwf trivial hd }
  have hshape : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors, ∃ C' ps Ds idx,
      CtorShape c params types t ht ct C' ps Ds idx ∧
      venvC.constants ct.name = some ⟨c.lparams.length, C'⟩ := by
    intro t ht ct hct
    have hct' : ct ∈ types.flatMap (·.ctors) := List.mem_flatMap.2 ⟨_, List.getElem_mem ht, hct⟩
    obtain ⟨C', htr⟩ := hCt t types[t] (List.getElem?_eq_getElem ht) ct hct
    obtain ⟨nidx, hn⟩ : ∃ nidx, stats.nindices[t]? = some nidx :=
      ⟨_, Array.getElem?_eq_getElem (by rw [hT.nindices]; exact ht)⟩
    obtain ⟨hCT, ps, Ds, idx, hsh, har, htele, -⟩ :=
      hC d₁ hd₁ t types[t] (List.getElem?_eq_getElem ht) ct hct nidx hn C' htr
    rw [hd₁.params] at hsh htele
    exact ⟨C', ps, Ds, idx, ⟨htr, hCT, hsh, har, htele⟩,
      hCtorC t types[t] ct C' (List.getElem?_eq_getElem ht) hct htr⟩
  -- the motives, as the specification states them
  have hmotTys : d₀.motiveTypes (VLevel.shift pre.length c.lparams.length) ml =
      tds.zipIdx.map fun (td, j) => td.mtr.liftN j := by
    have hl : (headTypes types typeTr tds).length = tds.length := by
      rw [headTypes_length hT.typeTr_length htdlen, htdlen]
    have hall₀ : d₀.allTypes = d₀.types := VInductDecl.allTypes_of_aux rfl
    refine List.ext_getElem (by simp [VInductDecl.motiveTypes, hall₀, d₀, hl]) fun j h1 h2 => ?_
    simp only [VInductDecl.motiveTypes, hall₀, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hj : j < tds.length := by simpa using h2
    obtain ⟨t, T', td, nidx, -, -, h3, -, hT', -, hmtr⟩ :=
      hty j _ (List.getElem?_eq_getElem (by simpa [d₀, hl] using hj))
    obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans h3)
    rw [hmtr]
    exact (motiveTy_liftN (d := d₀) hshl rfl j (congrArg VInductiveType.name hT')
      (congrArg VInductiveType.indices hT') (by rw [hT'])).symm
  let motfvs := tds.map (·.motive)
  let heads := tds.map fun td => ((td.fvs.map Expr.fvar).toArray, Expr.fvar td.major)
  have hsetup : MinorsSetup c pre Mp pfvs params stats types d₀ motfvs heads
      (tds.map TyData.info).toArray := {
    MpT := hMpT
    par := hpar
    lev := hRS.levels
    ind := hRS.indConsts
    lpnd := hUs
    prend := hpnd
    names := hnames
    d₀params := rfl
    d₀len := headTypes_length hT.typeTr_length htdlen
    d₀types := fun t ht => by
      have h3 : tds[t]? = some tds[t] := List.getElem?_eq_getElem (by omega)
      obtain ⟨t', T', nidx, h1, h2, hn, htv⟩ := hI1.recs t _ h3
      refine ⟨_, headTypes_getElem?_of h1 h2 h3, ?_, ?_⟩
      · rw [List.getElem?_eq_getElem ht] at h1; cases h1; rfl
      · rw [hn, htv.nidx]
    motlen := by simp [motfvs, htdlen]
    motives := fun t ht => by
      simp [motfvs, TyData.info, getElem!_pos, htdlen, ht]
    heads := fun t ht => by
      simp [heads, TyData.info, getElem!_pos, htdlen, ht]
    nonPrim := fun t' ht' ct hct hsp har T hT => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
      obtain ⟨t, -, -, -, h1, -, -, -, rfl, -⟩ := hty j T hj
      rw [show d₀.types.map (·.name) = types.map (·.name) from
        headTypes_names hT.typeTr_length htdlen] at hsp
      exact hnonPrim t' ht' ct hct hsp har t (List.mem_of_getElem? h1)
    notDummy := fun T hT => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
      obtain ⟨t, -, -, -, h1, -, -, -, rfl, -⟩ := hty j T hj
      exact hdummy t (List.mem_of_getElem? h1)
    envB := fun t' ht' ct hct hsp har n ci h hn => by
      rw [show d₀.types.map (·.name) = types.map (·.name) from
        headTypes_names hT.typeTr_length htdlen] at hn hsp ⊢
      exact henvB t' ht' ct hct hsp har n ci h hn
    MpB := fun fv dd hd => by
      have hnames₀ : d₀.types.map (·.name) = types.map (·.name) :=
        headTypes_names hT.typeTr_length htdlen
      have hMp₀ : Mp.WF c₀.venv c₁.lparams := by
        rw [← hMpdef, hMpeq, ← hT.base.venv]; exact c₁.mlctx_wf.dropN kp hkp
      have htr := hMp₀.tr
      have hm : dd ∈ Mp.lctx.toList := by
        rw [htr.1.find?_eq_find?_toList] at hd; exact List.mem_of_find?_eq_some hd
      obtain ⟨_, _, -, -, -, h1, h2⟩ := htr.find?_of_mem hwf₀ hm
      have hle : (⟨(· ∈ Mp.vlctx.fvars), (· ∈ c₁.lparams), c₀.venv.contains⟩ : Supp) ≤
          BFree (· ∈ d₀.types.map (·.name)) := by
        refine ⟨fun _ _ => trivial, fun _ _ => trivial, fun n hn hm => ?_⟩
        rw [hnames₀] at hm
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hm
        obtain ⟨_, hc⟩ := hn
        rw [hfresh₀ t ht] at hc; cases hc
      exact ⟨(TrExprS.suppIn hwf₀ hprim₀ h2).mono hle,
        (TrExprS.suppIn hwf₀ hprim₀ h1).mono hle⟩ }
  -- what the kernel's context keeps while the minor premises are opened
  let P (cb : VContext) : Prop := cb.venv = venvC ∧ cb.lparams = pre ++ c.lparams ∧
    cb.env = envCA ∧ cb.allowPrimitive = c.allowPrimitive ∧ ∀ (j : Nat) (td : TyData), tds[j]? = some td → ∃ t T' nidx,
      types[j]? = some t ∧ typeTr[j]? = some T' ∧ stats.nindices[j]? = some nidx ∧
      TypeVarsAt c pre Mp pfvs params level ml t T' nidx td.info td.idx cb td.fvs td.major
        td.motive td.m
  have hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2) := by
    intro cb name ty ty' bi h1 h2 ⟨hv, hl, he, ha, hr⟩
    refine ⟨hv, hl, he, ha, fun j td hj => ?_⟩
    obtain ⟨t, T', nidx, a, b, c, d⟩ := hr j td hj
    exact ⟨t, T', nidx, a, b, c, d.push⟩
  have hPV : ∀ cb, P cb → cb.venv = venvC ∧ cb.lparams.length = (pre ++ c.lparams).length :=
    fun cb h => ⟨h.1, by rw [h.2.1]⟩
  have hI₀ : CtorsInv c X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P 0
      (tds.map TyData.info).toArray (flatCtors []) [] [] cb₁.mlctx.vlctx.fvars
      (motivesCtx (Mp.instL (VLevel.shift pre.length c.lparams.length)) tds) cb₁ ρp₁ ρB₁ := {
    setup := hsetup
    size := by simp [htdlen]
    minlen := rfl
    tele := by
      have := motivesCtx_isTele (hMpT.instL (VLevel.shift pre.length c.lparams.length)) tds
      simpa [hmotTys, flatCtors, motfvs] using this
    lift := by
      have := motivesCtx_lift (Mp.instL (VLevel.shift pre.length c.lparams.length)) _ tds rfl
      simpa [flatCtors, htdlen] using this
    sub := hsub₁
    ext := hB₁
    pred := ⟨hI1.venv, hlp₁, hI1.env, hI1.allowPrimitive, hI1.recs⟩
    minors := by simp [TyData.info]
    later := fun t ht _ => by simp [TyData.info]
    minfresh := nofun
    kdlen := rfl
    kdmin := rfl
    kdinfo := by simp [TyData.info]
    kdok := fun q h1 => absurd h1 (by simp)
    kdfvars := rfl
    laterInfos := fun t ht _ => by simp [TyData.info]
    infoCount := fun t ht => by simp [TyData.info, flatCtors] }
  refine loopInd2.WF (X := X) (hMp := hMp) hNM (blockNames_contains types) hP hPV hBF hshape
    ?fin types.length 0 [] _ [] []
    _ cb₁ ρp₁ ρB₁ (by simp) rfl (fun _ _ h => by simp at h) hI₀
    (fun t ht _ => by simp [TyData.info])
  case fin =>
  intro recInfos css minfvs kds Mmin cb₂ ρp₂ ρmin₂ hI₂ hcsl hcss
  obtain ⟨hv₂, hl₂, he₂, ha₂, hr₂⟩ := hI₂.pred
  let d : VInductDecl :=
    blockDecl d₀ css (isRec types.toArray stats.indConsts) !(elimLevel matches .zero)
  have hd₀len : d₀.types.length = types.length := headTypes_length hT.typeTr_length htdlen
  have hdlen : d.types.length = types.length := by
    show (withCtors d₀.types css).length = _
    rw [withCtors_length (by rw [hcsl, hd₀len]), hd₀len]
  -- a type of `d`, as `loopInd1` opened it
  have hdty : ∀ (j : Nat) (T : VInductiveType), d.types[j]? = some T →
      ∃ (t : InductiveType) (T' : VExpr) (td : TyData) (nidx : Nat) (cs : List VConstructor),
      types[j]? = some t ∧ typeTr[j]? = some T' ∧ tds[j]? = some td ∧
      stats.nindices[j]? = some nidx ∧ css[j]? = some cs ∧
      T = ({ name := t.name, type := T', indices := td.idx, ctors := cs } : VInductiveType) ∧
      TypeVarsAt c pre Mp pfvs params level ml t T' nidx td.info td.idx cb₁ td.fvs td.major
        td.motive td.m := by
    intro j T hT
    obtain ⟨T₀, cs, h0, hcs, rfl⟩ := withCtors_getElem? hT
    obtain ⟨t, T', td, nidx, h1, h2, h3, h4, rfl, htv, -⟩ := hty j T₀ h0
    exact ⟨t, T', td, nidx, cs, h1, h2, h3, h4, hcs, rfl, htv⟩
  have htys : ∀ (i : Nat) (T : VInductiveType), d₀.types[i]? = some T →
      ∃ T' : VInductiveType, d.types[i]? = some T' ∧ T'.name = T.name ∧ T'.indices = T.indices ∧
        T'.nested = none := by
    intro i T hT
    have hi : i < css.length := by
      have := (List.getElem?_eq_some_iff.1 hT).1; rw [hd₀len] at this; omega
    exact ⟨_, withCtors_getElem?_of hT (List.getElem?_eq_getElem hi), rfl, rfl,
      headTypes_nested T (List.mem_of_getElem? hT)⟩
  have hPT : c.venv.IsTele c.lparams.length [] params := by
    rw [hlp₀]; exact hT.params_tele.mono hle
  have hrecL : d.recLevels = VLevel.shift pre.length c.lparams.length ∧ d.motiveLevel = ml := by
    rcases hE with rfl | ⟨u, rfl, hu⟩
    · have hpre : pre = [] := by simpa [getRecLevelParams] using (hrl []).symm
      subst hpre
      have hml0 : ml = .zero := by simpa [VLevel.ofLevel] using hml.symm
      subst hml0
      refine ⟨?_, ?_⟩ <;> simp [VInductDecl.recLevels, VInductDecl.motiveLevel,
        VInductDecl.LargeElim, d, blockDecl, VLevel.shift, VLevel.params, d₀]
    · have hpre : pre = [u] := by simpa [getRecLevelParams] using (hrl []).symm
      subst hpre
      have hml0 : ml = .param 0 := by simp [VLevel.ofLevel] at hml; exact hml.symm
      subst hml0
      refine ⟨?_, ?_⟩ <;> simp [VInductDecl.recLevels, VInductDecl.motiveLevel,
        VInductDecl.LargeElim, d, blockDecl, VLevel.shift, d₀]
  have hMminWF : Mmin.WF venvC (pre ++ c.lparams) := by
    have := hI₂.ext.wf; rwa [hv₂, hl₂] at this
  have hcb₁nd : ((tds.reverse.map TyData.block).flatten ++ cb.mlctx.vlctx.fvars).Nodup := by
    rw [← hI1.fvars]; exact cb₁.mlctx_wf.tr.wf.fvars_nodup
  have hRF : d.RecFacts venvC (pre ++ c.lparams).length
      (VLevel.shift pre.length c.lparams.length) :=
    recFacts_blockDecl hBF (by rw [hcsl, hd₀len]) fun j cs cv hcs hcv => by
      have hjc : j < css.length := (List.getElem?_eq_some_iff.1 hcs).1
      have hj : j < types.length := by omega
      obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hjc).symm.trans hcs)
      obtain ⟨ct, -, hcd⟩ := Lean4Lean.List.Forall₂.forall_exists_r (hcss j hj hjc) cv hcv
      obtain ⟨_, _, _, _, -, hout⟩ := hcd
      exact hout.facts
  -- any model of the environment with the constructors extends the one they were added to
  have hVCC : ∀ envC : VEnv, c.venv ≤ envC →
      (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) → venvC ≤ envC := by
    intro envC hle' hcc
    refine hVCC envC hle' fun j t ct C₁ hj hct htr₁ => ?_
    have hjt : j < types.length := (List.getElem?_eq_some_iff.1 hj).1
    have hjc : j < css.length := by omega
    obtain rfl : types[j] = t := Option.some.inj ((List.getElem?_eq_getElem hjt).symm.trans hj)
    obtain ⟨cv, hcv, C', ps, Ds, idx, ⟨htr', -⟩, hout⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l (hcss j hjt hjc) ct hct
    obtain rfl := TrExprS.unique (TrExprS.IsUnique.all _) htr₁ htr'
    have hjT := withCtors_getElem?_of (Ts := d₀.types)
      (List.getElem?_eq_getElem (by rw [hd₀len]; exact hjt)) (List.getElem?_eq_getElem hjc)
    have hmem : (j, cv) ∈ d.ctors := VInductDecl.mem_ctors_iff.2 ⟨_, hjT, hcv⟩
    have := hcc _ (List.mem_map_of_mem (f := fun p : Nat × VConstructor =>
      (p.2.name, (⟨d.uvars, p.2.type⟩ : VConstant))) hmem)
    rw [hout.name, hout.type] at this
    exact this
  have hcsl' : css.length = d₀.types.length := by rw [hcsl, hd₀len]
  have hdctors : d.ctors = flatCtors css := blockDecl_ctors hcsl'
  have hdAllT : d.allTypes = d.types := VInductDecl.allTypes_of_aux rfl
  have hdAllC : d.allCtors = d.ctors := VInductDecl.allCtors_of_aux rfl
  have hbind : params.map (·.instL (VLevel.shift pre.length c.lparams.length)) ++
      d₀.motiveTypes (VLevel.shift pre.length c.lparams.length) ml ++
      (flatCtors css).zipIdx.map (fun ((j, cv), q) =>
        d₀.minorType (VLevel.shift pre.length c.lparams.length) q j cv) =
      d.recBinders (VLevel.shift pre.length c.lparams.length) ml := by
    simp only [VInductDecl.recBinders, VInductDecl.minorTypes,
      VInductDecl.allCtors_of_aux (decl := d) rfl, hdctors]
    simp only [d, blockDecl_motiveTypes rfl hcsl', blockDecl_minorType rfl headTypes_nested hcsl']
    rfl
  have hmlwf : ml.WF (pre ++ c.lparams).length := .of_ofLevel hml
  have hmotl : motfvs.length = types.length := by simp [motfvs, htdlen]
  have hminl : minfvs.length = (flatCtors css).length := hI₂.minlen
  have hparArr : stats.params = (pfvs.map Expr.fvar).toArray := by rw [← hpar]
  have hmotArr : recInfos.map (·.motive) = (motfvs.map Expr.fvar).toArray := by
    refine Array.ext (by simp [hI₂.size, hmotl]) fun j h1 h2 => ?_
    have hj : j < types.length := by simpa [hI₂.size] using h1
    have := hI₂.setup.motives j hj
    rw [getElem!_pos _ j (by rw [hI₂.size]; exact hj)] at this
    simp [this]
  have hminArr : recInfos.flatMap (·.minors) = (minfvs.map Expr.fvar).toArray := by
    apply Array.toList_inj.1
    rw [Array.toList_flatMap, List.flatMap_def, ← hI₂.minors]
  have hrecTy : ∀ (i : Nat) (T : VInductiveType) info, d.types[i]? = some T →
      recInfos[i]? = some info →
      TrExprS venvC (pre ++ c.lparams) [] (recTypeExpr cb₂.lctx stats recInfos info)
        (d.recType (VLevel.shift pre.length c.lparams.length) ml i T) ∧
      MajorAt T.name (stats.params.size + recInfos.size + (recInfos.flatMap (·.minors)).size +
        stats.nindices[i]!) (recTypeExpr cb₂.lctx stats recInfos info) := by
    intro i T info hT hinfo
    obtain ⟨t, T', td, nidx, cs, h1, h2, h3, hn, hcs, rfl, -⟩ := hdty i T hT
    obtain ⟨t₂, T₂, nidx₂, h1₂, -, hn₂, htv⟩ := hr₂ i td h3
    obtain rfl := Option.some.inj (h1.symm.trans h1₂)
    have hil : i < types.length := (List.getElem?_eq_some_iff.1 h1).1
    have hisz : i < recInfos.size := by rw [hI₂.size]; exact hil
    have htdi : tds[i]'(by omega) = td :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans h3)
    obtain rfl : recInfos[i] = info :=
      Option.some.inj ((Array.getElem?_eq_getElem hisz).symm.trans hinfo)
    have hmot : recInfos[i].motive = .fvar td.motive := by
      have := hI₂.setup.motives i hil
      rw [getElem!_pos _ i hisz] at this
      rw [this]; simp [motfvs, htdi]
    have hhead : recInfos[i].indices = (td.fvs.map .fvar).toArray ∧
        recInfos[i].major = .fvar td.major := by
      have := hI₂.setup.heads i hil
      rw [getElem!_pos _ i hisz] at this
      simp only [heads, List.getElem!_eq_getElem?_getD, List.getElem?_map, h3, Option.map_some,
        Option.getD_some, Prod.mk.injEq] at this
      exact this
    -- the view `E` of the kernel's context: the parameters, motives and minor premises, then
    -- this type's indices and major premise
    obtain ⟨hkb, hbase⟩ := htv.base
    have hlenp : pfvs.length = params.length := hMpT.length_eq
    have hidxl : td.idx.length = td.fvs.length := by
      have := htv.tele.length_eq; simp at this; omega
    have hmT : (td.m.instL (VLevel.shift pre.length c.lparams.length)).IsTele
        (pfvs ++ (td.fvs ++ [td.major]))
        (params.map (·.instL (VLevel.shift pre.length c.lparams.length)) ++
          (td.idx ++ [majorTy t.name c.lparams.length params.length td.idx.length]).map
            (·.instL (VLevel.shift pre.length c.lparams.length))) := by
      simpa [List.append_assoc] using htv.tele.instL (VLevel.shift pre.length c.lparams.length)
    have hmWF : (td.m.instL (VLevel.shift pre.length c.lparams.length)).WF venvC
        (pre ++ c.lparams) := (htv.wf.lparams_append hpre).mono hVCle
    have hkm : (td.fvs ++ [td.major]).length ≤
        (td.m.instL (VLevel.shift pre.length c.lparams.length)).length := by
      rw [TypeChecker.MLCtx.length_instL]; simpa using hkb
    have W : VLCtx.FVLift' ((td.m.instL (VLevel.shift pre.length c.lparams.length)).dropN
        (td.fvs ++ [td.major]).length hkm).vlctx Mmin.vlctx 0
        (Lift.skipN .refl (types.length + (flatCtors css).length)) 0 := by
      have e : (td.m.instL (VLevel.shift pre.length c.lparams.length)).dropN
          (td.fvs ++ [td.major]).length hkm = Mp.instL (VLevel.shift pre.length c.lparams.length) := by
        rw [TypeChecker.MLCtx.dropN_instL _ td.m _ (by simpa using hkb) hkm, ← hbase]
        congr 1; exact TypeChecker.MLCtx.dropN_congr (by simp) _ _
      rw [e]; exact hI₂.lift
    have hfr : ∀ fv ∈ td.fvs ++ [td.major], fv ∉ Mmin.vlctx.fvars := by
      intro fv hfv hmem
      rw [hI₂.tele.fvars] at hmem
      simp only [List.reverse_append, List.mem_append, List.mem_reverse] at hmem
      rcases hmem with hm | hm | hm
      · obtain ⟨cbX, hPX, rfl⟩ := hI₂.minfresh _ hm
        obtain ⟨tX, TX, nX, -, -, -, htvX⟩ := hPX.2.2.2.2 i td h3
        have hin : (⟨cbX.ngen.curr⟩ : FVarId) ∈ td.m.vlctx.fvars := by
          rw [htv.tele.fvars, List.mem_reverse, List.append_assoc]
          exact List.mem_append_right _ hfv
        have e := TypeVarsAt.agree htvX _ hin
        obtain ⟨dd, hdd⟩ := (TypeVarsAt.wf htvX).tr.find?_eq_some.2 hin
        rw [hdd] at e
        refine cbX.curr_not_dom ?_
        cases h : cbX.lctx.find? ⟨cbX.ngen.curr⟩ <;> simp_all [LocalContext.Dom]
      · obtain ⟨td', htd', rfl⟩ := List.mem_map.1 hm
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 htd'
        exact blocks_ne_motive hcb₁nd h3 hj hfv rfl
      · have hnd := htv.wf.tr.wf.fvars_nodup
        rw [htv.tele.fvars, List.nodup_reverse, List.append_assoc] at hnd
        exact (List.nodup_append.1 hnd).2.2 _ hm _ hfv rfl
    obtain ⟨wfE, -, teleE, agE, agBE⟩ := graft_spec hVCwf hMminWF hI₂.tele
      (td.fvs ++ [td.major]).length rfl (by simp [hidxl]) hmT hmWF hkm W hfr
    have hEtop : ∃ name ty ty' bi E', graft Mmin (Lift.skipN .refl
        (types.length + (flatCtors css).length)) (td.fvs ++ [td.major]).length
        (td.m.instL (VLevel.shift pre.length c.lparams.length)) =
        .vlam td.major name ty ty' bi E' ∧ ∃ us, ty.getAppFn = .const t.name us := by
      obtain ⟨name, ty, ty', bi, m', hm', us, hus⟩ := htv.top
      rw [hm', show (td.fvs ++ [td.major]).length = td.fvs.length + 1 by simp]
      exact ⟨name, ty, _, bi, _, rfl, us, hus⟩
    generalize graft Mmin _ _ _ = E at wfE teleE agE agBE hEtop
    -- its types are the recursor's binders
    have hmaj : ((majorTy t.name c.lparams.length params.length td.idx.length).instL
        (VLevel.shift pre.length c.lparams.length)).lift'
          ((Lift.skipN .refl (types.length + (flatCtors css).length)).consN td.idx.length) =
        .appN (.const t.name (VLevel.shift pre.length c.lparams.length))
          (VExpr.bvars params.length (d.types.length + d.ctors.length + td.idx.length) ++
            VExpr.bvars td.idx.length 0) := by
      rw [VExpr.lift'_consN_skipN, hdlen, hdctors]
      simp only [majorTy, VExpr.instL_appN, VExpr.instL, VLevel.params_inst hshl, List.map_append,
        VExpr.instL_bvars, VExpr.liftN_appN, VExpr.liftN]
      rw [VExpr.bvars_liftN_hi _ _ _ _ (Nat.le_refl _), bvars_liftN_lo, Nat.add_comm td.idx.length]
    have teleE' : E.IsTele (pfvs ++ motfvs ++ minfvs ++ td.fvs ++ [td.major])
        (d.recBinders (VLevel.shift pre.length c.lparams.length) ml ++
          VExpr.liftTele (d.types.length + d.ctors.length)
            (td.idx.map (·.instL (VLevel.shift pre.length c.lparams.length))) ++
          [.appN (.const t.name (VLevel.shift pre.length c.lparams.length))
            (VExpr.bvars params.length (d.types.length + d.ctors.length + td.idx.length) ++
              VExpr.bvars td.idx.length 0)]) := by
      rw [← hbind, ← hmaj, ← zipIdx_lift'_eq_liftTele, hdlen, hdctors]
      simpa [List.zipIdx_append, List.append_assoc] using teleE
    -- the recursor's conclusion is a type there
    have hIT := VInductDecl.recType_isType hRF hmlwf (hdAllT ▸ hT)
    simp only [VInductDecl.recType, hdAllT, hdAllC, VInductiveType.typeApp] at hIT
    obtain ⟨-, hIT₁⟩ := VEnv.IsType.foralls_inv hVCwf.ordered hIT
    obtain ⟨-, u, hbodyS⟩ := VEnv.IsType.forallE_inv hVCwf.ordered hIT₁
    have hbodyE : venvC.HasType (pre ++ c.lparams).length E.vlctx.toCtx
        (.app (.appN (.bvar (1 + td.idx.length + d.ctors.length + (d.types.length - 1 - i)))
          (VExpr.bvars td.idx.length 1)) (.bvar 0)) (.sort u) := by
      rw [show d.params = params from rfl] at hbodyS
      rw [teleE'.toCtx]; simpa using hbodyS
    -- the motive's position
    have hndE : (pfvs ++ motfvs ++ minfvs ++ td.fvs ++ [td.major]).Nodup := by
      have := wfE.tr.wf.fvars_nodup; rw [teleE'.fvars] at this; exact List.nodup_reverse.1 this
    have hjm : pfvs.length + i < (pfvs ++ motfvs ++ minfvs ++ td.fvs ++ [td.major]).length := by
      simp; omega
    have hm := teleE'.find?_fvar hndE hjm
    have hget : (pfvs ++ motfvs ++ minfvs ++ td.fvs ++ [td.major])[pfvs.length + i]'hjm =
        td.motive := by
      simp only [List.append_assoc]
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by simp; omega)]
      simp [motfvs, htdi]
    have hpos : (pfvs ++ motfvs ++ minfvs ++ td.fvs ++ [td.major]).length - 1 -
        (pfvs.length + i) = 1 + td.idx.length + d.ctors.length + (d.types.length - 1 - i) := by
      rw [hdlen, hdctors]; simp; omega
    rw [hget, hpos] at hm
    have hbodyTr := recBody_tr hVCwf wfE teleE' hm
      (by rw [← hidxl]; exact hbodyE)
    rw [← hidxl] at hbodyTr
    -- the kernel's local context declares each variable as `E` does
    have hagr : ∀ x ∈ [pfvs, motfvs, minfvs, td.fvs, [td.major]].flatten,
        (cb₂.lctx.find? x).map LocalDecl.erase = (E.lctx.find? x).map LocalDecl.erase := by
      intro x hx
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hx
      have hM (hxM : x ∈ Mmin.vlctx.fvars) : (cb₂.lctx.find? x).map LocalDecl.erase =
          (E.lctx.find? x).map LocalDecl.erase := by
        rw [agBE x hxM]; exact hI₂.ext.lctx x hxM
      have hD (hxD : x ∈ td.fvs ++ [td.major]) : (cb₂.lctx.find? x).map LocalDecl.erase =
          (E.lctx.find? x).map LocalDecl.erase := by
        rw [agE x hxD, TypeChecker.MLCtx.lctx_instL]
        refine TypeVarsAt.agree htv x ?_
        rw [htv.tele.fvars, List.mem_reverse, List.append_assoc]
        exact List.mem_append_right _ hxD
      rcases hx with hx | hx | hx | hx | hx
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · exact hD (List.mem_append_left _ hx)
      · exact hD (List.mem_append_right _ hx)
    obtain ⟨hkall, eqAll, trAll, -⟩ := mkForall_nest hVCwf (lctx := cb₂.lctx)
      [pfvs, motfvs, minfvs, td.fvs, [td.major]]
      [params.map (·.instL (VLevel.shift pre.length c.lparams.length)),
        d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml,
        d.minorTypes (VLevel.shift pre.length c.lparams.length),
        VExpr.liftTele (d.types.length + d.ctors.length)
          (td.idx.map (·.instL (VLevel.shift pre.length c.lparams.length))),
        [.appN (.const t.name (VLevel.shift pre.length c.lparams.length))
          (VExpr.bvars params.length (d.types.length + d.ctors.length + td.idx.length) ++
            VExpr.bvars td.idx.length 0)]]
      (Bfvs := []) (Btys := []) wfE
      (by simpa [VInductDecl.recBinders, List.append_assoc, show d.params = params from rfl]
        using teleE')
      (.cons (by simp [hlenp]) <| .cons (by simp [VInductDecl.motiveTypes, hdAllT, hmotl, hdlen]) <|
        .cons (by simp [VInductDecl.minorTypes, hdAllC, hminl, hdctors]) <|
        .cons (by simp [hidxl]) <| .cons rfl .nil)
      hagr hbodyTr ⟨_, hbodyE⟩
    have hT0 : E.IsTele [pfvs, motfvs, minfvs, td.fvs, [td.major]].flatten
        [params.map (·.instL (VLevel.shift pre.length c.lparams.length)),
          d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml,
          d.minorTypes (VLevel.shift pre.length c.lparams.length),
          VExpr.liftTele (d.types.length + d.ctors.length)
            (td.idx.map (·.instL (VLevel.shift pre.length c.lparams.length))),
          [.appN (.const t.name (VLevel.shift pre.length c.lparams.length))
            (VExpr.bvars params.length (d.types.length + d.ctors.length + td.idx.length) ++
              VExpr.bvars td.idx.length 0)]].flatten := by
      simpa [VInductDecl.recBinders, List.append_assoc, show d.params = params from rfl]
        using teleE'
    obtain ⟨hk0, h0⟩ := hT0.dropN_all
    rw [TypeChecker.MLCtx.dropN_congr hT0.length_eq hkall hk0, h0] at trAll
    -- which is what the kernel built
    have e1 : recTypeExpr cb₂.lctx stats recInfos recInfos[i] =
        [pfvs, motfvs, minfvs, td.fvs, [td.major]].foldr
          (fun s acc => cb₂.lctx.mkForall (s.map .fvar).toArray acc)
          (.app (mkAppN (.fvar td.motive) (td.fvs.map .fvar).toArray) (.fvar td.major)) := by
      simp only [recTypeExpr, hparArr, hmotArr, hminArr, hhead.1, hhead.2, hmot, List.foldr_cons,
        List.foldr_nil]
      rfl
    have e2 : d.recType (VLevel.shift pre.length c.lparams.length) ml i
        { name := t.name, type := T', indices := td.idx, ctors := cs } =
        .foralls [params.map (·.instL (VLevel.shift pre.length c.lparams.length)),
          d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml,
          d.minorTypes (VLevel.shift pre.length c.lparams.length),
          VExpr.liftTele (d.types.length + d.ctors.length)
            (td.idx.map (·.instL (VLevel.shift pre.length c.lparams.length))),
          [.appN (.const t.name (VLevel.shift pre.length c.lparams.length))
            (VExpr.bvars params.length (d.types.length + d.ctors.length + td.idx.length) ++
              VExpr.bvars td.idx.length 0)]].flatten
          (.app (.appN (.bvar (1 + td.idx.length + d.ctors.length + (d.types.length - 1 - i)))
            (VExpr.bvars td.idx.length 1)) (.bvar 0)) := by
      simp only [VInductDecl.recType, VInductDecl.recBinders, List.flatten_cons, List.flatten_nil,
        List.append_nil, VExpr.foralls_append, List.append_assoc, hdAllT, hdAllC,
        VInductiveType.typeApp]
      rfl
    refine ⟨by rw [e1, e2]; exact trAll, ?_⟩
    -- the major premise's type
    rw [e1, eqAll]
    obtain ⟨name, ty, ty', bi, E', rfl, us, hus⟩ := hEtop
    obtain ⟨-, -, -, -, hE'T⟩ := teleE'.vlctx_split 1 rfl rfl
      (by simp [TypeChecker.MLCtx.length])
    have hlenE : [pfvs, motfvs, minfvs, td.fvs, [td.major]].flatten.length =
        (pfvs ++ motfvs ++ minfvs ++ td.fvs).length + 1 := by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
        List.length_singleton]; omega
    rw [TypeChecker.MLCtx.mkForall_congr hlenE _ (by
      have := teleE'.length; simp [TypeChecker.MLCtx.length] at this ⊢; omega)]
    simp only [TypeChecker.MLCtx.mkForall]
    have hM := MajorAt.mkForall (I := t.name) (k := 0)
      (show E'.IsTele (pfvs ++ motfvs ++ minfvs ++ td.fvs) _ by
        simpa [TypeChecker.MLCtx.dropN] using hE'T) (pfvs ++ motfvs ++ minfvs ++ td.fvs).length
      (by have := teleE'.length; simp [TypeChecker.MLCtx.length] at this ⊢; omega)
      (e := .forallE name ty (Expr.abstract1 td.major
        (.app (mkAppN (.fvar td.motive) (td.fvs.map .fvar).toArray) (.fvar td.major))) bi)
      ⟨us, hus⟩
    have hidx' : stats.nindices[i]! = td.fvs.length := by
      rw [getElem!_pos _ i (by rw [hRS.nindices]; omega)]
      have := (Array.getElem?_eq_getElem (by rw [hRS.nindices]; omega)).symm.trans hn
      rw [Option.some.inj this, Option.some.inj (hn.symm.trans hn₂), ← htv.nidx, hidxl]
    have hsz : stats.params.size + recInfos.size + (recInfos.flatMap (·.minors)).size +
        stats.nindices[i]! = 0 + (pfvs ++ motfvs ++ minfvs ++ td.fvs).length := by
      rw [hidx', hparArr, hminArr, hI₂.size]; simp [hmotl, hminl]; omega
    rw [hsz]
    exact hM
  -- each constructor's rule, from what the kernel opened for its minor premise
  have hpre' : (elimLevel = .zero ∧ pre = []) ∨ ∃ u, elimLevel = .param u ∧ pre = [u] := by
    rcases hE with rfl | ⟨u, rfl, -⟩
    · exact .inl ⟨rfl, by simpa [getRecLevelParams] using (hrl []).symm⟩
    · exact .inr ⟨u, rfl, by simpa [getRecLevelParams] using (hrl []).symm⟩
  have hUV : d.recUVars = (pre ++ c.lparams).length := by
    unfold VInductDecl.recUVars
    rcases hpre' with ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩
    · rw [if_neg (by simp [VInductDecl.LargeElim, d, blockDecl])]; rfl
    · rw [if_pos (by simp [VInductDecl.LargeElim, d, blockDecl])]
      show c.lparams.length + 1 = ([u] ++ c.lparams).length
      simp
  have hrules : ∀ q j cv, d.ctors[q]? = some (j, cv) → ∃ mi,
      (recInfos.toList.flatMap (·.minorInfos.toList))[q]? = some mi ∧
      mi.fields.size = cv.fields.length ∧
      ∀ envC envR : VEnv, c.venv ≤ envC → envC.WF →
        (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
        envC.addConstList d.recConsts = some envR → envR.WF →
        TrExprS envR (pre ++ c.lparams) []
          (ruleRhs cb₂.lctx types.toArray stats (getRecLevels elimLevel stats.levels)
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) q mi)
          (d.iotaRule (VLevel.shift pre.length c.lparams.length) ml
            (VLevel.params d.recUVars) q j cv).rhs := by
    intro q j cv hq
    have hcds : (flatCtors css)[q]? = some (j, cv) := hdctors ▸ hq
    have hqc : q < (flatCtors css).length := (List.getElem?_eq_some_iff.1 hcds).1
    have hql : q < kds.length := by rw [hI₂.kdlen]; exact hqc
    have hok := hI₂.kdok q hql hqc
    rw [show (flatCtors css)[q] = (j, cv) from
      Option.some.inj ((List.getElem?_eq_getElem hqc).symm.trans hcds)] at hok
    obtain ⟨kd, hkd⟩ : ∃ kd, kds[q] = kd := ⟨_, rfl⟩
    rw [hkd] at hok
    have hlenp : pfvs.length = params.length := hMpT.length_eq
    have hfl : kd.fvs.length = cv.fields.length := by
      have := hok.tele.length_eq; simp only [List.length_append, List.length_map] at this; omega
    refine ⟨kd.info, ?_, by simp [MinorKD.info, hfl], fun envC envR h1 h2 h3 h4 h5 => ?_⟩
    · rw [List.flatMap_def, hI₂.kdinfo, List.getElem?_map, List.getElem?_eq_getElem hql, hkd]; rfl
    -- the environment with the recursors
    have hCle := hVCC envC h1 h3
    have hRle : venvC ≤ envR := hCle.trans (VEnv.addConstList_le h4)
    have hRF' := hRF.mono hRle h5
    have hrecT : d.RecTyped envR (pre ++ c.lparams).length (VLevel.shift pre.length c.lparams.length)
        ml (d.recConst (VLevel.params d.recUVars)) := fun {t T} ht => by
      have hc := VEnv.addConstList_constants_of_mem h4 <| List.mem_map.2
        ⟨(T, t), List.mem_zipIdx_iff_getElem?.2 ht, rfl⟩
      have ⟨_, hty⟩ := VInductDecl.recType_isType hRF' hmlwf ht
      have := VEnv.HasType.const (Γ := []) (ls := VLevel.params d.recUVars) hc VLevel.params_wf
        (by simp)
      simp only [VInductDecl.recConst]
      rw [hrecL.1, hrecL.2, hUV] at this
      rw [(hty.levelWF trivial).1.instL_id] at this
      rw [hUV]; exact this
    -- the view of the kernel's context: the parameters, motives and minor premises, then the
    -- constructor's fields
    have hMfi : (kd.Mf.instL (VLevel.shift pre.length c.lparams.length)).WF venvC
        (pre ++ c.lparams) := (hok.wf.lparams_append hpre).mono hVCle
    have hMfiT : (kd.Mf.instL (VLevel.shift pre.length c.lparams.length)).IsTele (pfvs ++ kd.fvs)
        (params.map (·.instL (VLevel.shift pre.length c.lparams.length)) ++
          (cv.fields.map (·.type)).map (·.instL (VLevel.shift pre.length c.lparams.length))) := by
      simpa using hok.tele.instL (VLevel.shift pre.length c.lparams.length)
    obtain ⟨hkb, hbase⟩ := hok.base
    have hkm : kd.fvs.length ≤ (kd.Mf.instL (VLevel.shift pre.length c.lparams.length)).length := by
      rw [TypeChecker.MLCtx.length_instL]; exact hkb
    have W : VLCtx.FVLift' ((kd.Mf.instL (VLevel.shift pre.length c.lparams.length)).dropN
        kd.fvs.length hkm).vlctx Mmin.vlctx 0
        (Lift.skipN .refl (types.length + (flatCtors css).length)) 0 := by
      rw [TypeChecker.MLCtx.dropN_instL _ kd.Mf _ hkb hkm, hbase]; exact hI₂.lift
    have hcb₂nd : ((kds.reverse.map MinorKD.seg).flatten ++ cb₁.mlctx.vlctx.fvars).Nodup := by
      rw [← hI₂.kdfvars]; exact cb₂.mlctx_wf.tr.wf.fvars_nodup
    have hfr : ∀ fv ∈ kd.fvs, fv ∉ Mmin.vlctx.fvars := by
      intro fv hfv hmem
      obtain ⟨hF, hM⟩ := MinorKD.fvs_fresh hcb₂nd hql (x := fv) (by rw [hkd]; exact hfv)
      rw [hI₂.tele.fvars] at hmem
      simp only [List.reverse_append, List.mem_append, List.mem_reverse] at hmem
      rcases hmem with hm | hm | hm
      · rw [← hI₂.kdmin] at hm; exact hM hm
      · obtain ⟨td, htd, rfl⟩ := List.mem_map.1 hm
        apply hF; rw [hI1.fvars]
        exact List.mem_append_left _ (List.mem_flatten.2 ⟨td.block,
          List.mem_map.2 ⟨td, List.mem_reverse.2 htd, rfl⟩, by simp [TyData.block]⟩)
      · have hnd := hok.wf.tr.wf.fvars_nodup
        rw [hok.tele.fvars, List.nodup_reverse] at hnd
        exact (List.nodup_append.1 hnd).2.2 _ hm _ hfv rfl
    obtain ⟨wfV, WV, teleV, agV, agBV⟩ := graft_spec hVCwf hMminWF hI₂.tele kd.fvs.length rfl
      (by simp [hfl]) hMfiT hMfi hkm W hfr
    generalize graft Mmin _ _ _ = V at wfV WV teleV agV agBV
    have teleV' : V.IsTele (pfvs ++ motfvs ++ minfvs ++ kd.fvs)
        (d.recBinders (VLevel.shift pre.length c.lparams.length) ml ++
          VExpr.liftTele (d.types.length + d.ctors.length)
            (cv.fields.map (·.type.instL (VLevel.shift pre.length c.lparams.length)))) := by
      rw [← hbind, ← zipIdx_lift'_eq_liftTele, hdlen, hdctors]
      simpa [List.map_map, Function.comp_def] using teleV
    have wfVR : V.WF envR (pre ++ c.lparams) := wfV.mono hRle
    have hΓ := wfVR.tr.wf
    have hnd : (pfvs ++ motfvs ++ minfvs ++ kd.fvs).Nodup := by
      have := wfV.tr.wf.fvars_nodup; rw [teleV'.fvars] at this; exact List.nodup_reverse.1 this
    -- the rule's body is typed there
    obtain ⟨-, R, Ty, -, hr, -, -, -, hRty⟩ := VInductDecl.iotaRule_bodies hRF' hmlwf hrecT
      (hdAllC ▸ hq)
    rw [iotaRule_rhs] at hr
    simp only [hdAllT, hdAllC] at hr hRty
    obtain rfl := VExpr.lams_body_inj hr.symm
    rw [← teleV'.toCtx] at hRty
    have hn : d.params.length = pfvs.length := by rw [hlenp]; rfl
    have hTl : d.types.length = motfvs.length := by rw [hdlen, hmotl]
    have hCl : d.ctors.length = minfvs.length := by rw [hdctors, hminl]
    rw [hn, hTl, hCl, ← hfl] at hRty
    -- which the kernel's body translates to
    have hqm : q < minfvs.length := by rw [hminl]; exact hqc
    have hj : pfvs.length + motfvs.length + q < (pfvs ++ motfvs ++ minfvs ++ kd.fvs).length := by
      simp; omega
    have hmq := teleV'.find?_fvar hnd hj
    have hget : (pfvs ++ motfvs ++ minfvs ++ kd.fvs)[pfvs.length + motfvs.length + q]'hj =
        minfvs[q] := by
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
      congr 1; simp
    have hpos : (pfvs ++ motfvs ++ minfvs ++ kd.fvs).length - 1 -
        (pfvs.length + motfvs.length + q) = kd.fvs.length + (minfvs.length - 1 - q) := by
      simp; omega
    rw [hget, hpos] at hmq
    have hall := teleV'.fvars_tr (env := envR) (Us := pre ++ c.lparams) hnd
    rw [List.map_append, List.length_append, ← VExpr.bvars_append, Nat.add_zero] at hall
    have hFs := List.Forall₂.drop_append (by simp [VExpr.bvars]) hall
    have hih : List.Forall₂ (TrExprS envR (pre ++ c.lparams) V.vlctx)
        (kd.ihs.toList.map fun ih => ih.value (mkAppN (mkAppN (mkAppN
          (.const (mkRecName types.toArray[ih.itIdx]!.name) (getRecLevels elimLevel stats.levels))
          (pfvs.map Expr.fvar).toArray) (motfvs.map Expr.fvar).toArray) (minfvs.map Expr.fvar).toArray))
        (cv.recFields.map fun (k, ra) =>
          ihRhs (VLevel.shift pre.length c.lparams.length) pfvs.length motfvs.length minfvs.length
            kd.fvs.length k (d.recConst (VLevel.params d.recUVars) ra.typeIdx) ra) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine Lean4Lean.List.Forall₂.imp (fun ih p h => ?_) hok.pieces.and_mem_right
      obtain ⟨k, ra⟩ := p
      obtain ⟨⟨hp, hk', hP, -⟩, hmem⟩ := h
      -- the recursor of the type the field ends in
      obtain ⟨f, hf, hra⟩ := VInductDecl.mem_recFields hmem
      obtain ⟨T, hT, -⟩ := hRF'.recArg (hdAllC ▸ List.mem_of_getElem? hq) hf hra
      obtain ⟨t, T', td, nidx, cs, ht, -, -, -, -, rfl, -⟩ := hdty _ _ (hdAllT ▸ hT)
      have hconst : ∀ Δ, TrExprS envR (pre ++ c.lparams) Δ
          (.const (mkRecName types.toArray[ih.itIdx]!.name) (getRecLevels elimLevel stats.levels))
          (d.recConst (VLevel.params d.recUVars) ra.typeIdx) := by
        intro Δ
        have hlv := getRecLevels_tr hRS.levels hpnd hpre'
        have hc := VEnv.addConstList_constants_of_mem h4 <| List.mem_map.2
          ⟨(_, ra.typeIdx), List.mem_zipIdx_iff_getElem?.2 hT, rfl⟩
        rw [hP.itIdx, show types.toArray[ra.typeIdx]! = t by
          rw [getElem!_pos types.toArray ra.typeIdx (by
            simpa using (List.getElem?_eq_some_iff.1 ht).1)]
          simpa using (List.getElem?_eq_some_iff.1 ht).2]
        simp only [VInductDecl.recConst]
        rw [hUV, show mkRecName t.name = d.recName ra.typeIdx from
          (VInductDecl.recName_of_types (hdAllT ▸ hT)).symm]
        refine .const hc hlv ?_
        rw [Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hlv), VLevel.params_length, hUV]
      have hwf : (ihRhs (VLevel.shift pre.length c.lparams.length) pfvs.length motfvs.length
          minfvs.length kd.fvs.length k (d.recConst (VLevel.params d.recUVars) ra.typeIdx) ra).WF
          envR (pre ++ c.lparams).length V.vlctx.toCtx :=
        appN_arg_wf h5.ordered hΓ.toCtx ⟨_, hRty⟩ _ (List.mem_append_right _
          (List.mem_map_of_mem (f := fun (p : Nat × VRecArg) =>
            ihRhs (VLevel.shift pre.length c.lparams.length) pfvs.length motfvs.length
              minfvs.length kd.fvs.length p.1 (d.recConst (VLevel.params d.recUVars) p.2.typeIdx)
              p.2) hmem))
      have WV' : VLCtx.FVLift' (kd.Mf.instL (VLevel.shift pre.length c.lparams.length)).vlctx
          V.vlctx 0 ((Lift.skipN .refl (motfvs.length + minfvs.length)).consN kd.fvs.length) 0 := by
        rw [hmotl, hminl]; exact WV
      exact ihRhs_tr h5 wfVR hpre rfl (hVCle.trans hRle) teleV' hok.tele (by simp [hfl]) WV' hp hk'
        hP hconst hwf
    have hargs := (Lean4Lean.List.Forall₂.append_of_left (Lean4Lean.List.Forall₂.length_eq hFs)).2
      ⟨hFs, hih⟩
    have hbodyTr := TrExprS.mkAppN_of_wf h5.ordered hΓ.toCtx (.fvar hmq) hargs ⟨_, hRty⟩
    -- abstracted over the segments the kernel opened
    have hag : ∀ x ∈ [pfvs, motfvs, minfvs, kd.fvs].flatten,
        (cb₂.lctx.find? x).map LocalDecl.erase = (V.lctx.find? x).map LocalDecl.erase := by
      intro x hx
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hx
      have hM (hxM : x ∈ Mmin.vlctx.fvars) : (cb₂.lctx.find? x).map LocalDecl.erase =
          (V.lctx.find? x).map LocalDecl.erase := by
        rw [agBV x hxM]; exact hI₂.ext.lctx x hxM
      rcases hx with hx | hx | hx | hx
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · exact hM (by rw [hI₂.tele.fvars]; simp [hx])
      · rw [agV x hx, TypeChecker.MLCtx.lctx_instL]
        exact hok.agree x (by rw [hok.tele.fvars]; simp [hx])
    have hT0 : V.IsTele [pfvs, motfvs, minfvs, kd.fvs].flatten
        [params.map (·.instL (VLevel.shift pre.length c.lparams.length)),
          d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml,
          d.minorTypes (VLevel.shift pre.length c.lparams.length),
          VExpr.liftTele (d.types.length + d.ctors.length)
            (cv.fields.map (·.type.instL (VLevel.shift pre.length c.lparams.length)))].flatten := by
      simpa [VInductDecl.recBinders, List.append_assoc, show d.params = params from rfl]
        using teleV'
    obtain ⟨hkall, trAll, -⟩ := mkLambda_nest h5 (lctx := cb₂.lctx)
      [pfvs, motfvs, minfvs, kd.fvs]
      [params.map (·.instL (VLevel.shift pre.length c.lparams.length)),
        d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml,
        d.minorTypes (VLevel.shift pre.length c.lparams.length),
        VExpr.liftTele (d.types.length + d.ctors.length)
          (cv.fields.map (·.type.instL (VLevel.shift pre.length c.lparams.length)))]
      (Bfvs := []) (Btys := []) wfVR (by simpa using hT0)
      (.cons (by simp [hlenp]) <| .cons (by simp [VInductDecl.motiveTypes, hdAllT, hmotl, hdlen]) <|
        .cons (by simp [VInductDecl.minorTypes, hdAllC, hminl, hdctors]) <| .cons (by simp [hfl]) .nil)
      hag hbodyTr hRty
    obtain ⟨hk0, h0⟩ := hT0.dropN_all
    rw [TypeChecker.MLCtx.dropN_congr hT0.length_eq hkall hk0, h0] at trAll
    -- which is what the kernel built
    rw [iotaRule_rhs, hdAllT, hdAllC, hn, hTl, hCl, ← hfl]
    rw [hTl, hCl] at trAll
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, ← List.append_assoc] at trAll
    rw [show d.recBinders (VLevel.shift pre.length c.lparams.length) ml =
      params.map (·.instL (VLevel.shift pre.length c.lparams.length)) ++
        d.motiveTypes (VLevel.shift pre.length c.lparams.length) ml ++
        d.minorTypes (VLevel.shift pre.length c.lparams.length) from rfl]
    have hmin : (minfvs.map Expr.fvar).toArray[q]! = .fvar minfvs[q] := by
      rw [getElem!_pos _ q (by simpa using hqm)]; simp
    simp only [List.foldr_cons, List.foldr_nil] at trAll
    have harr : ∀ (l : List Expr) (a : Array IHInfo) (g : IHInfo → Expr),
        (l ++ a.toList.map g).toArray = l.toArray ++ a.map g := fun l a g =>
      Array.toList_inj.1 (by simp)
    simp only [harr] at trAll
    simpa [ruleRhs, hparArr, hmotArr, hminArr, MinorKD.info, hmin, mkAppN_append] using trAll
  have hnotDefnC : ∀ t ∈ types, ∀ v, c.env.find? t.name ≠ some (.defnInfo v) := by
    intro t ht v hv
    by_cases hX : X t.name
    · rw [(hXfresh _ hX).1] at hv; cases hv
    · rw [← hXenv _ hX] at hv; exact hnotDefn t ht v hv
  have hR : RecInfosData c nparams types stats params level typeTr isUnsafe elimLevel recInfos
      cb₂ d := {
    venv := hv₂ ▸ hVCle
    lparams := by rw [hl₂, hrl]
    allowPrimitive := ha₂
    safety := hI₂.sub.safety
    size := hI₂.size
    elaborates := {
      level := rfl
      types := List.forall₂_of_getElem? hdlen.symm fun j t T h1 h2 => by
        obtain ⟨t', T', td, nidx, cs, h1', -, -, -, hcs, rfl, -⟩ := hdty j T h2
        obtain rfl := Option.some.inj (h1.symm.trans h1')
        have hj : j < types.length := (List.getElem?_eq_some_iff.1 h1).1
        have hjc : j < css.length := by omega
        obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hjc).symm.trans hcs)
        obtain rfl : types[j] = t := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans h1)
        refine ⟨rfl, Lean4Lean.List.Forall₂.imp (fun ct cv hcd => ?_) (hcss j hj hjc)⟩
        obtain ⟨h1, h2, ps, Ds, h3, h4, h5, h6, h8, h7, h9⟩ := hcd.elab hPT rfl rfl htys
          (hdlen.trans hd₀len.symm) hnotDefnC
        refine ⟨h1, h2, ps, Ds, by rw [h3, hT.nparams], h4, ?_, h6, h8, h7,
          by rw [← hT.nparams]; exact h9⟩
        rw [h5, hT.nparams] }
    first := fun hn0 => List.forall₂_of_getElem? hdlen.symm fun j t T h1 h2 => by
      obtain ⟨t', T', td, nidx, cs, h1', -, -, -, hcs, rfl, -⟩ := hdty j T h2
      obtain rfl := Option.some.inj (h1.symm.trans h1')
      have hj : j < types.length := (List.getElem?_eq_some_iff.1 h1).1
      have hjc : j < css.length := by omega
      obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hjc).symm.trans hcs)
      obtain rfl : types[j] = t := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans h1)
      refine Lean4Lean.List.Forall₂.imp (fun ct cv hcd => ?_) (hcss j hj hjc)
      obtain ⟨_, _, _, _, -, hout⟩ := hcd
      exact hout.first (by rw [show params = [] from hn0]; rfl)
    uvars := rfl
    params := rfl
    level := rfl
    isUnsafe := rfl
    isRec := rfl
    aux := rfl
    nested := fun T hT => by
      obtain ⟨⟨T₀, cs⟩, hm, rfl⟩ := List.mem_map.1 hT
      exact headTypes_nested T₀ (List.of_mem_zip hm).1
    isRecArgs := fun hfalse T₁ hT₁ cv hcv f hf => by
      have hall : ∀ t ∈ types, ∀ ct ∈ t.ctors, isRec.loop stats.indConsts ct.type = false := by
        intro t ht ct hct
        have h : isRec types.toArray stats.indConsts = false := hfalse
        simp only [isRec, List.any_toArray, List.any_eq_false, Bool.not_eq_true] at h
        exact h t ht ct hct
      have hlit := hlit hfalse
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT₁
      obtain ⟨t, T', td, nidx, cs, h1, -, -, -, hcs, rfl, -⟩ := hdty j _ hj
      have hjt : j < types.length := (List.getElem?_eq_some_iff.1 h1).1
      have hjc : j < css.length := by omega
      obtain rfl := Option.some.inj ((List.getElem?_eq_getElem hjc).symm.trans hcs)
      obtain rfl : types[j] = t := Option.some.inj ((List.getElem?_eq_getElem hjt).symm.trans h1)
      obtain ⟨ct, hct, hcd⟩ := Lean4Lean.List.Forall₂.forall_exists_r (hcss j hjt hjc) cv hcv
      obtain ⟨C', ps, Ds, idx, ⟨htr, -⟩, hout⟩ := hcd
      refine hout.recFree ?_ f hf
      rw [headTypes_names hT.typeTr_length htdlen]
      exact spineIn_of_isRec (indOccP_spec hRS.indConsts).2 hlit htr
        (hall _ (List.getElem_mem hjt) ct hct)
    largeElim := by rcases hE with rfl | ⟨u, rfl, -⟩ <;> simp [VInductDecl.LargeElim, d, blockDecl]
    typeTr := List.forall₂_of_getElem? (by rw [hdlen, hT.typeTr_length]) fun j T T' h1 h2 => by
      obtain ⟨t, T'', td, nidx, cs, -, h2', -, -, -, rfl, -⟩ := hdty j T h1
      exact Option.some.inj (h2'.symm.trans h2)
    indices := fun T hT => by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
      obtain ⟨t, T', td, nidx, cs, -, -, -, -, -, rfl, htv⟩ := hdty j T hj
      exact ⟨by simpa [d, blockDecl, d₀] using (htv.tele.isTele htv.wf).append_inv.1.append_inv.2,
        htv.defeq⟩
    idxFree := fun T hT x hx => by
      have hdn : d.names = types.map (·.name) := by
        refine List.ext_getElem (by simp [VInductDecl.names, hdlen]) fun i h1 h2 => ?_
        obtain ⟨t, T', td, nidx, cs, h1', -, -, -, -, he, -⟩ :=
          hdty i _ (List.getElem?_eq_getElem (by simpa [VInductDecl.names] using h1))
        simp only [VInductDecl.names, List.getElem_map, he]
        rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h1')]
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
      obtain ⟨t, T', td, nidx, cs, -, -, h3, -, -, rfl, -⟩ := hdty j T hj
      rw [hdn]; exact hI1.idxFree j td h3 x hx
    nindices := fun j T hT => by
      obtain ⟨t, T', td, nidx, cs, -, -, h3, hn, -, rfl, -⟩ := hdty j T hT
      obtain ⟨t', T'', nidx', -, -, hn', htv⟩ := hI1.recs j td h3
      obtain rfl := Option.some.inj (hn.symm.trans hn')
      rw [hn, ← htv.nidx]
    recType := fun i T info hT hinfo envC hle' hwf hcc => by
      rw [hrl, hrecL.1, hrecL.2]
      exact (hrecTy i T info hT hinfo).1.mono (hVCC envC hle' hcc)
    nparams := by
      show stats.params.size = params.length
      rw [← Array.length_toList, hpar, List.length_map]; exact hMpT.length_eq
    nminors := by
      have hcsl' : css.length = d₀.types.length := by rw [hcsl, hd₀len]
      rw [show d.ctors = flatCtors css from blockDecl_ctors hcsl', ← Array.length_toList,
        Array.toList_flatMap, List.flatMap_def, hI₂.minors]
      simp [hI₂.minlen]
    major := fun i T info hT hinfo => (hrecTy i T info hT hinfo).2
    infoCount := List.forall₂_of_getElem? (by simp [hI₂.size, hdlen]) fun t info T h1 h2 => by
      obtain ⟨T₀, cs, -, hcs, rfl⟩ := withCtors_getElem? h2
      have ht : t < recInfos.size := by simpa using (List.getElem?_eq_some_iff.1 h1).1
      obtain rfl : recInfos[t] = info := by simpa [Array.getElem?_eq_getElem ht] using h1
      rw [hI₂.infoCount t ht, flatCtors_filter_length, hcs]; rfl
    rules := fun q j cv hq => by rw [hrl, hrecL.1, hrecL.2]; exact hrules q j cv hq }
  refine H recInfos cb₂ d hR fun hSE T hT => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  obtain ⟨t, T', td, nidx, cs, -, -, h3, -, -, rfl, -⟩ := hdty j T hj
  obtain ⟨e1, e2⟩ := hcE hSE
  have := hI1.idxE j td h3
  rw [e1, e2] at this
  exact this


/-- `mkRecInfos`, in the checking environment with the constructors added as axioms. Its
constructors' fields are read as `d`'s fields, which `run` then builds the recursors from. -/
theorem mkRecInfos.WF {c₀ c₁ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c₁ params level typeTr)
    (hc : c.mlctx = c₁.mlctx) (hU : c.lparams = c₁.lparams) (hle : c₀.venv ≤ c.venv)
    (henv : c.venv.WF) {isUnsafe : Bool}
    (hp : c.allowPrimitive = false) (hsafety : c.safety = inductSafety isUnsafe)
    (hC : ∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c.venv c.lparams d t nidx ct)
    (hCt : ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors,
      ∃ C', TrExprS c.venv c.lparams [] ct.type C')
    (hconst : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t →
      typeTr[j]? = some T' → c.venv.constants t.name = some ⟨c.lparams.length, T'⟩)
    (hB : BlockFresh c₀.venv c.venv types) (hnames : (types.map (·.name)).Nodup)
    (hnotDefn : ∀ t ∈ types, ∀ v, c.env.find? t.name ≠ some (.defnInfo v))
    (hclosed : ConstMap.Closed c.env.constants) (hUs : c.lparams.Nodup)
    (hdummy : ∀ t ∈ types, t.name ≠ `_inhabitedExprDummy)
    (henvB : ∀ n ci, c.env.find? n = some ci → n ∉ types.map (·.name) →
      ci.SuppIn fun m => m ∉ types.map (·.name))
    {elimLevel : Level} (hE : elimLevel = .zero ∨ ∃ u, elimLevel = .param u ∧ u ∉ c.lparams)
    (hEsim : (∀ t ∈ types, Environment.primitives.contains t.name = false) →
      (∀ n, n ∉ types.map (·.name) → c.env.find? n = c₁.env.find? n) ∧
      (∀ t ∈ types, c₁.env.find? t.name = none) ∧ ConstMap.Closed c₁.env.constants ∧
      c.env.quotInit = c₁.env.quotInit ∧ c.safety = c₁.safety ∧ c.fuel = c₁.fuel)
    {k : Array RecInfo → M α} {Q}
    (H : ∀ recInfos c' d,
      RecInfosData c nparams types stats params level typeTr isUnsafe elimLevel recInfos c' d →
      IndicesE c₀ types d → WF c' (k recInfos) Q) :
    WF c (do withEnv (← declareCtorAxioms types.toArray isUnsafe) <|
      withReader (fun ctx => { ctx with lparams := getRecLevelParams elimLevel ctx.lparams }) <|
      mkRecInfos stats types.toArray elimLevel k) Q := by
  -- the constructors' types are types, read off any declaration agreeing with the checks
  obtain ⟨d₁, hd₁⟩ := compat_exists c.lparams params level isUnsafe types stats.nindices
    (by rw [hT.nindices])
  have hCT : ∀ ct ∈ types.flatMap (·.ctors), ∀ C', TrExprS c.venv c.lparams [] ct.type C' →
      c.venv.IsType c.lparams.length [] C' := by
    intro ct hct C' htr
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 hct
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨nidx, hn⟩ : ∃ nidx, stats.nindices[j]? = some nidx := by
      have : j < stats.nindices.size := by
        rw [hT.nindices]; exact (List.getElem?_eq_some_iff.1 hj).1
      exact ⟨_, Array.getElem?_eq_getElem this⟩
    exact (hC d₁ hd₁ j t hj ct hct nidx hn C' htr).1
  refine WF.bind (declareCtorAxioms.WF hsafety hp hCT) fun envCA hCA => ?_
  obtain ⟨hCAc, hCAq, hctnd, hctfr, hctr⟩ := hCA
  obtain ⟨ctorTr, hctorTr⟩ := List.exists_forall₂ (R := fun ct C' =>
    TrExprS c.venv c.lparams [] ct.type C') (l := types.flatMap (·.ctors)) (fun ct hct => by
      obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 hct
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
      exact hCt j t hj ct hct)
  obtain ⟨venvC, hadd, hVC⟩ := hctr ctorTr hctorTr
  refine WF.withEnv hVC (VEnv.addConstList_le hadd) ?_
  have mapWF := c.envAt.tr.map_wf
  have mapWFCA : envCA.constants.WF := hVC.tr.map_wf
  have hfrc : ∀ ci ∈ (ctorAxioms c.lparams isUnsafe types).map ConstantInfo.axiomInfo,
      c.env.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨ax, hax, rfl⟩ := List.mem_map.1 hci
    obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hax
    have := (hctfr ct hct).1
    rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at this
  have hndc : (((ctorAxioms c.lparams isUnsafe types).map ConstantInfo.axiomInfo).map
      (·.name)).Nodup := by
    simpa [ctorAxioms, List.map_map, Function.comp_def, ConstantInfo.name,
      ConstantInfo.toConstantVal] using hctnd
  have hnamesc : ((ctorAxioms c.lparams isUnsafe types).map ConstantInfo.axiomInfo).map (·.name) =
      (types.flatMap (·.ctors)).map (·.name) := by
    simp [ctorAxioms, List.map_map, Function.comp_def, ConstantInfo.name,
      ConstantInfo.toConstantVal]
  have hXenv : ∀ n, n ∉ (types.flatMap (·.ctors)).map (·.name) →
      envCA.find? n = c.env.find? n := by
    intro n hn
    show envCA.constants.find?' n = c.env.constants.find?' n
    rw [mapWFCA.find?'_eq_find?, mapWF.find?'_eq_find?, hCAc,
      insertConsts_find?_of_not_mem mapWF hfrc hndc (by rw [hnamesc]; exact hn)]
  have hctN : ∀ t ∈ types, t.name ∉ (types.flatMap (·.ctors)).map (·.name) := by
    intro t ht hm
    obtain ⟨ct, hct, e⟩ := List.mem_map.1 hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨T', hT'⟩ : ∃ T', typeTr[j]? = some T' :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [hT.typeTr_length]; exact (List.getElem?_eq_some_iff.1 hj).1)⟩
    have h1 := c.envAt.tr.constants_eq_none (hctfr ct hct).1
    rw [e, hconst j t T' hj hT'] at h1; cases h1
  -- a constructor's constant is the one `declareCtorAxioms` added, at any translation of its type
  have hCtorC : ∀ (j : Nat) (t : InductiveType) ct C', types[j]? = some t → ct ∈ t.ctors →
      TrExprS c.venv c.lparams [] ct.type C' →
      (ct.name, (⟨c.lparams.length, C'⟩ : VConstant)) ∈
        ctorConstsOf c.lparams.length (types.flatMap (·.ctors)) ctorTr := by
    intro j t ct C' hj hct htr
    have hct' : ct ∈ types.flatMap (·.ctors) :=
      List.mem_flatMap.2 ⟨_, List.mem_of_getElem? hj, hct⟩
    obtain ⟨C₁, htr₁, hmem⟩ := hctorTr.mem_zipWith (f := fun ct C' => (ct.name,
      (⟨c.lparams.length, C'⟩ : VConstant))) ct hct'
    obtain rfl := TrExprS.unique (TrExprS.IsUnique.all _) htr htr₁
    exact hmem
  refine mkRecInfos.WF_core hT hc hU hle henv
    (hB.notMentionsOK (by have := hT.indConsts; rwa [List.take_length] at this)) hC hCt hconst hB.wf₀ hB.prim₀ hB.fresh hnames
    hclosed hUs hdummy (fun _ _ _ _ _ _ t ht => hB.nonPrim t ht)
    (fun _ _ _ _ _ _ n ci h hn => henvB n ci h hn) (fun _ l hl => ?_) hVC (VEnv.addConstList_le hadd)
    (X := (· ∈ (types.flatMap (·.ctors)).map (·.name))) hXenv (fun n v hv hX => ?_)
    (fun n hX => ?_) ?_ (by rw [hCAq]) (fun t ht v hv => ?_)
    (fun j t ct C' hj hct htr => VEnv.addConstList_constants_of_mem hadd
      (hCtorC j t ct C' hj hct htr))
    (fun envC hle' hcc => VEnv.addConstList_le_of hadd hle' fun p hp => ?_) hE hEsim H
  · -- a literal's constants are older than the block
    have hold (n) (hp : Environment.primitives.contains n = true) (h : c.venv.contains n) :
        c₀.venv.contains n := by
      obtain ⟨ci, hci⟩ := h
      cases h0 : c₀.venv.constants n with
      | some ci => exact ⟨ci, h0⟩
      | none =>
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (hB.new n (by simp [hci]) h0)
        simp [hB.nonPrim t ht] at hp
    have hl₀ : c₀.venv.ContainsLits l := by
      cases l with
      | natVal => exact hold _ (by simp +decide [Environment.primitives, NameSet.ofList,
          NameSet.contains]) hl
      | strVal =>
        exact ⟨hold _ (by simp +decide [Environment.primitives, NameSet.ofList,
          NameSet.contains]) hl.1, hold _ (by simp +decide [Environment.primitives,
          NameSet.ofList, NameSet.contains]) hl.2⟩
    refine (hB.prim₀.lit hB.wf₀ hl₀).mono' fun n hn hm => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hm
    obtain ⟨_, hc⟩ := hn; rw [hB.fresh t ht] at hc; cases hc
  · change envCA.constants.find?' n = _ at hv
    rw [mapWFCA.find?'_eq_find?, hCAc] at hv
    rcases insertConsts_find? mapWF hfrc hndc hv with h | ⟨h, -⟩
    · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hX
      have := (hctfr ct hct).1
      rw [Kernel.Environment.find?, mapWF.find?'_eq_find?, h] at this; cases this
    · obtain ⟨ax, -, hax⟩ := List.mem_map.1 h; cases hax
  · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hX
    exact (hctfr ct hct)
  · rw [hCAc]
    refine ConstMap.Closed.insertAxioms _ mapWF hclosed (fun ax hax => ?_)
      (by simpa [List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal]
        using hndc)
      (fun ax hax => hfrc _ (List.mem_map_of_mem hax))
    obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hax
    obtain ⟨t, ht, hct'⟩ := List.mem_flatMap.1 hct
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨C', hC'⟩ := hCt j t hj ct hct'
    exact TrExprS.suppIn_env c.envAt.tr c.envAt.hasPrimitives hC'
  · rw [hXenv _ (hctN t ht)] at hv; exact hnotDefn t ht v hv
  · obtain ⟨ct, hct, C₁, htr₁, rfl⟩ := hctorTr.of_mem_zipWith p hp
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 hct
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    exact hcc j t ct C₁ hj hct htr₁

end AddInductive
end Lean4Lean

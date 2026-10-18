import Lean4Lean.Theory.Typing.LogRel.IndTeleCtors

/-!
# The type formers of an inductive block

A block's type formers are interpreted, in `GoodOverC X d.typeConsts`, by the shapes at which they
are related. That every shape `X` interprets one by is such a shape (`typeFormer_good`) is the
`hgood` premise of `AdeqStmt.blockC`: the type former is related along its telescope of parameters
and indices, which is typed before the block, at its arity by `typeFormer_sat`, whose constructor
telescopes come from the constructor types' adequacy in `GoodOverC` over the block's types as
axioms.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.ConstsSat.foralls_l {p : Name → Prop} :
    ∀ {As : List VExpr} {B : VExpr}, (VExpr.foralls As B).ConstsSat p → ∀ A ∈ As, A.ConstsSat p
  | [], _, _ => nofun
  | _ :: As, _, ⟨h1, h2⟩ => by
    intro A hA
    rcases List.mem_cons.1 hA with rfl | hA
    · exact h1
    · exact foralls_l h2 A hA

/-- The `hgood` premise of `AdeqStmt.blockC` for a block's type formers: every shape `X`
interprets a type former by, from interpretations of its constructors' types also in
`GoodOverC X d.typeConsts`, is one at which it is related. The model `X` is sound and adequate
for the environment `E` before the block, and `GoodOverC` for `E` with the block's types as
axioms (`envT`); the two read `E`'s constants alike. The typing of stuck values of structure
types (`HY`) is taken as given. -/
theorem typeFormer_good (henvW : env.WF) (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E envT : VEnv} (hEle : E ≤ env) (hEo : E.Ordered)
    (hSX : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → @StrongSoundEq _ X env U Γ M N A)
    (IHX : @AdequacyHyps env U _ X henv hU E Γ₀)
    (hTle : envT ≤ env) (hTo : envT.Ordered) (hIT : envT.Inj)
    (hSG : ∀ {Γ M N A}, envT.IsDefEqStrong U Γ M N A →
      @StrongSoundEq _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env U Γ M N A)
    (IHG : @AdequacyHyps env U _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) henv hU envT Γ₀)
    (hd : d.WF E) (h1 : E.addConstList d.typeConsts = some envT)
    (hsXG : SameOn env X (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) (E.constants · ≠ none))
    (hsGX : SameOn env (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) X (E.constants · ≠ none))
    (hs : ∀ T ∈ d.types, ∃ t, env.inducts T.name = some (d, t) ∧ d.types[t]? = some T)
    (hdomX : ∀ T ∈ d.types, ¬X.dom T.name)
    (hcon : ∀ T ∈ d.types, ∀ c' ∈ T.ctors, ∀ ci, env.constants c'.name = some ci →
      ci.type = c'.type)
    (HY : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, ConstAt U T.name ls F →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ')) :
    ∀ {n c ci ls R m' a ρ}, (c, ci) ∈ d.typeConsts → env.constants c = some ci →
      ls.length = ci.uvars → m'.HasType a → @LE_Interp _ X env ρ a (ci.type.instL ls) →
      @Const _ X env c ls R n [] m' →
      (∀ h e, R h e → @LE_Interp _ X env ρ h e ∧
        @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env ρ h e) →
      GoodC (U := U) henv hU X Γ₀ d.typeConsts c ls m' := by
  intro n c ci ls R m' a ρ hci hcon' hlen hm'a ha H hR
  obtain ⟨T, hTm, he⟩ := List.mem_map.1 hci
  cases he
  obtain ⟨t, hs', hT'⟩ := hs T hTm
  have hclX : ClosedRules env := hMX.closed
  have hclG : ClosedRules env := @ModelEnv.closed _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env hMG
  -- the pieces the interpretation reads are closed
  have H' := @Const.closed _ X env _ _ _ _ _ _ hclX H
  have hR' : ∀ h e, (e.ClosedN ∧ R h e) → @LE_Interp _ X env ρ h e := fun h e hr => (hR h e hr.2).1
  have hRG : ∀ h e, (e.ClosedN ∧ R h e) → @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env .nil h e := fun h e hr =>
    (@LE_Interp.closed_iff _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env hclG _ hr.1 _ _ _).1 (hR h e hr.2).2
  have hle₁ : E ≤ envT := VEnv.addConstList_le h1
  have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hTm
  have hP : E.IsTele d.uvars [] d.params := hd.params
  have hI : E.IsTele d.uvars d.params.reverse T.indices := hd.indices T hTA
  have hTW := (hd.ctors envT h1 T hTA)
  have hn : Inert env T.name := Inert.of_role hMX.roles (fun hdf e => henvW.rule_lhs_params hdf e)
    (ConstArity.indTy hs' hT') (fun _ h => by cases h) (fun _ _ h => by cases h)
    (fun h => by cases h)
  -- the telescope's types, related by adequacy in `X` for `E`
  let P : List VExpr → VExpr → Prop := fun Γ' A =>
    ∃ Δ, Γ' = Δ ++ Γ₀ ∧ OnCtx Δ (E.IsType U) ∧ E.IsType U Δ A
  have hPf : ∀ {Γ' A B}, P Γ' (.forallE A B) → P Γ' A ∧ P (A::Γ') B := by
    rintro Γ' A B ⟨Δ, rfl, hΔ, hT⟩
    obtain ⟨h1, h2⟩ := VEnv.IsType.forallE_inv hEo hT
    exact ⟨⟨Δ, rfl, hΔ, h1⟩, ⟨A::Δ, rfl, ⟨hΔ, h1⟩, h2⟩⟩
  have hTy : ∀ {Γ' T'}, OnCtx Γ' (env.IsType U) → P Γ' T' → ∃ w, env.HasType U Γ' T' (.sort w) ∧
      @StrongSoundEq _ X env U Γ' T' T' (.sort w) ∧
      @AdeqStmt env U _ X henv hU Γ₀ Γ' T' T' (.sort w) := by
    rintro Γ' T' hΓ' ⟨Δ, rfl, hΔ, w, hT⟩
    have D := IsDefEq.weak_closed hEo hΔ hT Γ₀
    exact ⟨w, D.defeq.mono hEle, hSX D, LR.adequacy_of hMX hEle hSX hΓ₀ IHX D hΓ'⟩
  -- the declared type at a sort, in the block's types as axioms
  have hdef : ∃ u, envT.IsDefEq d.uvars [] T.type
      (.foralls (d.params ++ T.indices) (.sort d.level)) (.sort u) := by
    obtain ⟨w, hw⟩ := (hd.types T hTm).1
    have hw' := hw.mono hle₁
    obtain ⟨V, hV⟩ := hTW.1.defeq
    obtain ⟨_, hu⟩ := hIT.uniq (Γ := []) trivial hw' hV
    exact ⟨w, .defeqDF hu.symm hV⟩
  obtain ⟨u, hdef⟩ := hdef
  have hQT : T.type.ConstsSat (E.constants · ≠ none) := by
    obtain ⟨w, hw⟩ := (hd.types T hTm).1
    exact ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hEo hw trivial).1
  have hPIE : E.IsTele d.uvars [] (d.params ++ T.indices) := VEnv.IsTele.append hP (by simpa using hI)
  have hQB : (VExpr.foralls (d.params ++ T.indices) (.sort d.level)).ConstsSat
      (E.constants · ≠ none) := by
    obtain ⟨w, hw⟩ := hPIE.foralls (B := .sort d.level) ⟨_, .sort hd.level⟩
    exact ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hEo hw trivial).1
  refine GoodC.of_spine (Γ₀ := Γ₀) hMX hΓ₀ P hPf hTy hci hcon' hlen hm'a ha H' hR'
    (hdomX T hTm) ?_
  intro ls₁ ls₂ ls₃ e1 e2 e3 w1 w2 w3
  have CV := typeFormer_conv (Γ₀ := Γ₀) X (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) hMG hsXG hsGX hΓ₀ hTle hTo hSG IHG hdef hQT hQB w3
  rw [VEnv.foralls_instL'] at CV
  obtain ⟨hinterp, hconvE, hconv⟩ := CV
  have hBp : ∀ A ∈ d.params.map (·.instL ls₃), A.ConstsSat (E.constants · ≠ none) := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := List.mem_map.1 hA
    have := hQB.foralls_l A₀ (List.mem_append_left _ hA₀)
    exact this.instL
  refine ⟨_, _, typeFormer_spineAtB (Γ₀ := Γ₀) (E := E) (ci := ⟨d.uvars, T.type⟩) hMX henvW hΓ₀
    hs' hT' (hdomX T hTm) hP hI w3 e3 hinterp hconvE (fun hb ht => hconv hb ht) ?_
    (fun rargs => HY T hTm rargs)⟩
  intro n' rargs ctys F F' σ σ' hF hF' W hlen hcl hcty l hl htel
  refine typeFormer_HC (Γ₀ := Γ₀) X (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) hMG hsXG hsGX hn (hcon T hTm) hBp hRG ?_ rargs ctys hF hF' W
    hlen hcl hcty l hl htel
  intro i c' hc' l₁ l₂ f1 f2 v1 v2
  have hcm : c' ∈ T.ctors := List.mem_of_getElem? hc'
  have e1' := levels_equiv_trans (levels_equiv_symm e3) f1
  have e2' := levels_equiv_trans (levels_equiv_symm e3) f2
  letI : AxInterp := (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts)
  exact ctorTele_adeq (Γ₀ := Γ₀) hMG hTle hTo hIT hSG hΓ₀ IHG (hP.mono hle₁) (hTW.2 c' hcm) w3
    v1 v2 e1' e2'

omit [ShapeEnv] in
/-- A recorded block's type at index `j` is recorded under its name at `j`, its types' names
being distinct. -/
theorem _root_.Lean4Lean.VEnv.addBlock_inducts_of {E E' : VEnv} {d : VInductDecl}
    {T : VInductiveType} {j : Nat} (h : E.addBlock d = some E')
    (hnd : (d.types.map (·.name)).Nodup) (hT : d.types[j]? = some T) :
    E'.inducts T.name = some (d, j) := by
  unfold VEnv.addBlock at h; split at h <;> cases h
  obtain ⟨hjl, ht⟩ := List.getElem?_eq_some_iff.1 hT
  simp only
  rw [show d.types.findIdx? (·.name == T.name) = some j from
    List.findIdx?_eq_some_iff_getElem.2 ⟨hjl, by simp [ht], fun i hi => by
      have hil : i < d.types.length := by omega
      have := mt (List.getElem_inj (xs := d.types.map (·.name)) (i := i) (j := j)
        (h₀ := by simpa using hil) (h₁ := by simpa using hjl) hnd).1 (Nat.ne_of_lt hi)
      simp only [List.getElem_map] at this
      rw [← ht]; simpa using this⟩]

omit [ShapeEnv] in
/-- What an inductive block's step knows of the block before its constructors: the environment
after it, its types' records, names and constructors' types, and the environment with its types
as axioms. -/
theorem induct_facts {E E' env : VEnv} {d : VInductDecl} (hD : VDecl.WF E (.induct d) E')
    (hle : E' ≤ env) :
    d.WF E ∧ ∃ envT envC envR, E.addConstList d.typeConsts = some envT ∧
      envT.addConstList d.ctorConsts = some envC ∧ envC.addConstList d.recConsts = some envR ∧
      envT ≤ E' ∧ (d.types.map (·.name)).Nodup ∧
      (∀ T ∈ d.types, ∃ t, env.inducts T.name = some (d, t) ∧ d.types[t]? = some T) ∧
      (∀ T ∈ d.types, env.constants T.name = some ⟨d.uvars, T.type⟩) ∧
      (∀ T ∈ d.types, ∀ c' ∈ T.ctors, env.constants c'.name = some ⟨d.uvars, c'.type⟩) := by
  cases hD with
  | induct hd _ h =>
  refine ⟨hd, ?_⟩
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨E₁, h1, E₂, h2, E₃, h3, h4⟩ := h
  have hnd : (d.types.map (·.name)).Nodup := by
    have := (VEnv.addConstList_spec h1).1
    simpa [VInductDecl.typeConsts, List.map_map, Function.comp_def] using this
  have hl₂ := VEnv.addConstList_le h2
  have hl₃ := VEnv.addConstList_le h3
  have hc : ∀ {n ci}, E₃.constants n = some ci → env.constants n = some ci := fun h =>
    hle.constants (by rw [VEnv.addBlock_constants h4, VEnv.addDefEqList_constants']; exact h)
  have hTE' : E₁ ≤ E' := hl₂.trans (hl₃.trans (VEnv.addDefEqList_le.trans (VEnv.addBlock_le h4)))
  refine ⟨E₁, E₂, E₃, h1, h2, h3, hTE', hnd, fun T hT => ?_, fun T hT => ?_, fun T hT c' hc' => ?_⟩
  · obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hT
    exact ⟨t, hle.inducts (VEnv.addBlock_inducts_of h4 hnd ht), ht⟩
  · exact hc (hl₃.constants (hl₂.constants (VEnv.addConstList_constants_of_mem h1
      (List.mem_map_of_mem (f := fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))) hT))))
  · obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hT
    exact hc (hl₃.constants (VEnv.addConstList_constants_of_mem h2
      (List.mem_map_of_mem (f := fun p : Nat × VConstructor =>
        (p.2.name, (⟨d.uvars, p.2.type⟩ : VConstant))) (StepUniqProof.mem_ctors ht hc'))))

/-- An inductive block's type formers are related, in a model `X` interpreting none of the
block's constants by given shapes: through `GoodOverC X d.typeConsts`, which the induction's
hypothesis at every model makes adequate for the environment before the block, and so, adding the
types as axioms, for `envT`, where the constructors' types are typed. The typing of stuck values
of structure types (`HY`) is taken as given. -/
theorem typeFormers_adeq (henvW : env.WF)
    (hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (X : AxInterp) (hX : @AxOK _ X) (hXD : @DomRole _ X env)
    {ds : List VDecl} {E E' envT : VEnv} {d : VInductDecl} (hW : VEnv.WF' ds E)
    (hD : VDecl.WF E (.induct d) E') (hext : Extends E' env)
    (hdom : ∀ c, X.dom c → E'.constants c = none)
    (IHall : ∀ X' : AxInterp, @AxOK _ X' → @DomRole _ X' env →
      (∀ c, X'.dom c → E.constants c = none) → @AdequacyHyps env U _ X' henv hU E Γ₀)
    (h1 : E.addConstList d.typeConsts = some envT) (hIT : envT.Inj)
    (HY : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, ConstAt U T.name ls F →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ'))
    {Γ : List VExpr} {c : Name} {ci : VConstant} {ls ls' : List VLevel}
    (hci : (c, ci) ∈ d.typeConsts) (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ X henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  have hJ : LRJoin (U := U) henv hU Γ₀ := fun hc h1 h2 d1 d2 => (LR henv hU _).join hc h1 h2 d1 d2
  have hle : E' ≤ env := hext.le
  have hext₁ : Extends E env := .step hD hext
  have hle₁ : E ≤ env := hext₁.le
  have hEW : E.WF := ⟨_, hW⟩
  have hEo : E.Ordered := hEW.ordered
  obtain ⟨hd, envT', envC, envR, h1', -, -, hTE', hnd, hs, hcT, hcC⟩ := induct_facts hD hle
  cases h1.symm.trans h1'
  have hDle : E ≤ E' := hD.le
  have hTle : envT ≤ env := hTE'.trans hle
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hDle (hdom c h)
  have hMX := hModel X hX hXD
  have hndc : (d.typeConsts.map (·.1)).Nodup := (VEnv.addConstList_spec h1).1
  have hfr : ∀ p ∈ d.typeConsts, E.constants p.1 = none := (VEnv.addConstList_spec h1).2.1
  have hcon : ∀ p ∈ d.typeConsts, env.constants p.1 = some p.2 := by
    intro p hp
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact hcT T hT
  have hdomX : ∀ T ∈ d.types, ¬X.dom T.name := fun T hT hx => by
    have h := hdom _ hx
    have h' := hTE'.constants (VEnv.addConstList_constants_of_mem h1
      (List.mem_map_of_mem (f := fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))) hT))
    rw [h'] at h; cases h
  have hGax : @AxOK _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) := GoodOverC.axOK X hX hMX hJ hndc
  have hGD : @DomRole _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env := GoodOverC.domRole X hXD fun p hp {r k} A => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    obtain ⟨t, hs', hT'⟩ := hs T hT
    cases hMX.roles A (ConstArity.indTy hs' hT'); trivial
  have hMG := hModel _ hGax hGD
  have hdomG : ∀ c, @AxInterp.dom _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) c → E.constants c = none := by
    rintro c (hc | hc)
    · exact hdomE c hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc; exact hfr p hp
  have IHG := IHall _ hGax hGD hdomG
  have hsXG := hext₁.sameOn hW X (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) hdomE hdomG
  have hsGX := hext₁.sameOn hW (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) X hdomG hdomE
  have hdeclT : ∀ p ∈ d.typeConsts, env.constants p.1 = some p.2 ∧
      p.2.type.ConstsSat (E.constants · ≠ none) := by
    intro p hp
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact ⟨hcT T hT, VConstant.WF.constsSat hEo (hd.types T hT).1⟩
  have IHGT := AdequacyHyps.addGoodC X hMX hndc hsGX hdeclT (fun p hp => hp) IHG h1
  obtain ⟨dsT, hWT⟩ : envT.WF := VEnv.WF.addConstList hEW (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) h1
  have hTo : envT.Ordered := VEnv.WF.ordered ⟨_, hWT⟩
  have hSX : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hW hle₁
      (fun hdf e hx => VEnv.WF.rule_head hEW hdf e (hdomE _ hx))
      (VEnv.WF.noDomI hEW hdomE)).strongSound hMX hle₁ D
  have hSG : ∀ {Γ M N A}, envT.IsDefEqStrong U Γ M N A →
      @StrongSoundEq _ (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts) env U Γ M N A := by
    letI : AxInterp := (GoodOverC (U := U) henv hU X Γ₀ d.typeConsts)
    intro Γ M N A D
    have hndG : NoDom envT := fun hdf e hx => by
      rw [VEnv.addConstList_defeqs' h1] at hdf
      exact VEnv.WF.rule_head hEW hdf e (hdomG _ hx)
    exact (soundHyps_of hMG (quotRuleSound hMG henvW) (henvW.blockSound hMG) hWT hTle hndG
      (NoDomI.mono (VEnv.WF.noDomI hEW hdomG) fun h => (VEnv.addConstList_inducts h1) ▸ h)).strongSound
      hMG hTle D
  have IHX := IHall X hX hXD hdomE
  have hcC' : ∀ T ∈ d.types, ∀ c' ∈ T.ctors, ∀ ci, env.constants c'.name = some ci →
      ci.type = c'.type := fun T hT c' hc' ci h => by
    rw [hcC T hT c' hc'] at h; cases h; rfl
  intro ρ n m a hm ha hmem
  exact AdeqStmt.blockC X hMX hndc hcon
    (typeFormer_good henvW X hMX hMG hΓ₀ hle₁ hEo hSX IHX hTle hTo hIT hSG IHGT hd h1 hsXG hsGX
      hs hdomX hcC' HY) hci hls hls' heq hm ha hmem

/-- Adequacy's environment cases for the environment with an inductive block's types as axioms, in
a model interpreting none of the block's constants by given shapes. -/
theorem adequacyHyps_envT (henvW : env.WF)
    (hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (X : AxInterp) (hX : @AxOK _ X) (hXD : @DomRole _ X env)
    {ds : List VDecl} {E E' envT : VEnv} {d : VInductDecl} (hW : VEnv.WF' ds E)
    (hD : VDecl.WF E (.induct d) E') (hext : Extends E' env)
    (hdom : ∀ c, X.dom c → E'.constants c = none)
    (IHall : ∀ X' : AxInterp, @AxOK _ X' → @DomRole _ X' env →
      (∀ c, X'.dom c → E.constants c = none) → @AdequacyHyps env U _ X' henv hU E Γ₀)
    (h1 : E.addConstList d.typeConsts = some envT) (hIT : envT.Inj)
    (HY : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, ConstAt U T.name ls F →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ'))
    : @AdequacyHyps env U _ X henv hU envT Γ₀ := by
  have hext₁ : Extends E env := .step hD hext
  have hDle : E ≤ E' := hD.le
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hDle (hdom c h)
  have IHX := IHall X hX hXD hdomE
  have hinds : envT.inducts = E.inducts := VEnv.addConstList_inducts h1
  have hdfs : envT.defeqs = E.defeqs := VEnv.addConstList_defeqs' h1
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => IHX.extra hΓ (hdfs ▸ hd),
    fun hΓ h => IHX.projDF hΓ (hinds ▸ h), fun hΓ h => IHX.projIota hΓ (hinds ▸ h),
    fun hΓ h => IHX.projEta hΓ (hinds ▸ h)⟩
  rcases VEnv.addConstList_constants_cases' h1 hc with hc | hci
  · exact IHX.const hΓ hc hls hls' hlen heq hu h7 h8 hA
  · exact typeFormers_adeq henvW hModel hΓ₀ X hX hXD hW hD hext hdom IHall h1 hIT HY hci hls hls' heq

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.TeleDefEq.instL' {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) : ∀ {Γ As Bs}, env.TeleDefEq U' Γ As Bs →
      env.TeleDefEq U (Γ.map (·.instL ls)) (As.map (·.instL ls)) (Bs.map (·.instL ls))
  | _, [], [], .nil => .nil
  | _, _ :: _, _ :: _, .cons h t => .cons (h.instL hls) (by simpa using VEnv.TeleDefEq.instL' hls t)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.IsDefEqCtx.mono' {env env' : VEnv} (henv : env ≤ env')
    {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr} :
    env.IsDefEqCtx U Γ₀ Γ₁ Γ₂ → env'.IsDefEqCtx U Γ₀ Γ₁ Γ₂
  | .zero => .zero
  | .succ h1 h2 => .succ (VEnv.IsDefEqCtx.mono' henv h1) (h2.mono henv)

/-- A structure's constructor is its type's only constructor. -/
theorem ctors_eq_single_of_eta {env : VEnv} (henvW : env.WF) {s : Name} {d : VInductDecl}
    {t : Nat} {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hc : c ∈ T.ctors) (he : env.IsEtaCtor c.name) :
    T.ctors = [c] := by
  have hTA : d.allTypes[t]? = some T := by
    rw [VInductDecl.allTypes, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hT).1]
    exact hT
  have hnd := (StepUniqProof.names_of_WF henvW).ctorNodup hs (List.mem_of_getElem? hTA)
  have hall : ∀ c₁ ∈ T.ctors, c₁ = c := by
    intro c₁ hc₁
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 (VInductDecl.mem_allCtors_iff.2 ⟨T, hTA, hc⟩)
    obtain ⟨q', hq'⟩ := List.mem_iff_getElem?.1 (VInductDecl.mem_allCtors_iff.2 ⟨T, hTA, hc₁⟩)
    have := henvW.etaCtorUniq hs hq hq' he
    subst this; rw [hq] at hq'; cases hq'; rfl
  match h : T.ctors, hc with
  | [c₁], _ => rw [hall c₁ (by simp [h])]
  | c₁ :: c₂ :: l, _ =>
    rw [h] at hnd hall
    have e1 := hall c₁ (by simp); have e2 := hall c₂ (by simp)
    subst e1; subst e2
    simp at hnd

/-- An inductive block's constructors are related, in a model interpreting none of the block's
constants by given shapes: by `AdeqStmt.ctor` over the environment with the block's types as
axioms, where they are typed. -/
theorem ctors_adeq (henvW : env.WF)
    (hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (X : AxInterp) (hX : @AxOK _ X) (hXD : @DomRole _ X env)
    {ds : List VDecl} {E E' envT : VEnv} {d : VInductDecl} (hW : VEnv.WF' ds E)
    (hD : VDecl.WF E (.induct d) E') (hext : Extends E' env)
    (hdom : ∀ c, X.dom c → E'.constants c = none)
    (IHall : ∀ X' : AxInterp, @AxOK _ X' → @DomRole _ X' env →
      (∀ c, X'.dom c → E.constants c = none) → @AdequacyHyps env U _ X' henv hU E Γ₀)
    (h1 : E.addConstList d.typeConsts = some envT) (hIT : envT.Inj)
    (HY : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, ConstAt U T.name ls F →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ'))
    {Γ : List VExpr} {c : Name} {ci : VConstant} {ls ls' : List VLevel}
    (hΓ : OnCtx Γ (env.IsType U)) (hci : (c, ci) ∈ d.ctorConsts) (hls : ∀ l ∈ ls, l.WF U)
    (hls' : ∀ l ∈ ls', l.WF U) (hlen : ls.length = ci.uvars)
    (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ X henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  have hle : E' ≤ env := hext.le
  have hext₁ : Extends E env := .step hD hext
  have hEW : E.WF := ⟨_, hW⟩
  obtain ⟨hd, envT', envC, envR, h1', -, -, hTE', hnd, hs, hcT, hcC⟩ := induct_facts hD hle
  cases h1.symm.trans h1'
  have hTle : envT ≤ env := hTE'.trans hle
  have hDle : E ≤ E' := hD.le
  have hMX := hModel X hX hXD
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hDle (hdom c h)
  obtain ⟨dsT, hWT⟩ : envT.WF := VEnv.WF.addConstList hEW (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) h1
  have hTo : envT.Ordered := VEnv.WF.ordered ⟨_, hWT⟩
  have hSXT : ∀ {Γ M N A}, envT.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A := by
    intro Γ M N A D
    have hndX : NoDom envT := fun hdf e hx => by
      rw [VEnv.addConstList_defeqs' h1] at hdf
      exact VEnv.WF.rule_head hEW hdf e (hdomE _ hx)
    exact (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hWT hTle hndX
      (NoDomI.mono (VEnv.WF.noDomI hEW hdomE) fun h => (VEnv.addConstList_inducts h1) ▸ h)).strongSound
      hMX hTle D
  have IHT := adequacyHyps_envT henvW hModel hΓ₀ X hX hXD hW hD hext hdom IHall h1 hIT HY
  -- the constructor
  obtain ⟨⟨j, c'⟩, hm, he⟩ := List.mem_map.1 hci
  cases he
  obtain ⟨T, hTj, hc'⟩ := VInductDecl.mem_ctors_iff.1 hm
  have hTm : T ∈ d.types := List.mem_of_getElem? hTj
  have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hTm
  obtain ⟨t, hs', hT'⟩ := hs T hTm
  have hnone : T.nested = none := (hd.types T hTm).2
  have hcW := (hd.ctors envT h1 T hTA).2 c' hc'
  obtain ⟨ps, Ds, hshape, hPD, hFW, -, -⟩ := hcW.shape
  have hlen' : ls.length = d.uvars := hlen
  have hpl : ps.length = d.params.length := hPD.length_eq''
  have hDl : Ds.length = c'.fields.length := hFW.length
  have hcty : c'.type.instL ls = .foralls (ps.map (·.instL ls) ++ Ds.map (·.instL ls))
      (ctorCod T.name c' (ps.map (·.instL ls)).length (Ds.map (·.instL ls)).length ls) := by
    rw [hshape, VEnv.foralls_instL', List.map_append, VInductiveType.typeApp_of_none hnone]
    simp only [ctorCod, instL_appN, VExpr.instL, VLevel.params_inst hlen', List.map_append,
      instL_bvars, List.length_map, hpl, hDl]
  generalize hPs : ps.map (·.instL ls) = Ps at hcty
  generalize hDs' : Ds.map (·.instL ls) = Ds' at hcty
  have hPl : Ps.length = d.params.length := by rw [← hPs, List.length_map, hpl]
  have hDl' : Ds'.length = c'.fields.length := by rw [← hDs', List.length_map, hDl]
  -- the telescope and codomain, typed with the block's types as axioms
  have hty : envT.IsType U [] (c'.type.instL ls) := by simpa using hcW.type.instL hls
  rw [hcty] at hty
  obtain ⟨hTe, ⟨w, hw⟩⟩ := VEnv.IsType.foralls_inv hTo hty
  have hTA' : d.allTypes[t]? = some T := by
    rw [VInductDecl.allTypes, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hT').1]
    exact hT'
  have hnodup := (StepUniqProof.names_of_WF henvW).ctorNodup hs' hTA
  have hci' := hcC T hTm c' hc'
  have hndT : ¬X.dom T.name := fun hx => by
    have h := hdom _ hx
    have h' := hTE'.constants (VEnv.addConstList_constants_of_mem h1
      (List.mem_map_of_mem (f := fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))) hTm))
    rw [h'] at h; cases h
  have onT : OnCtx (Ps ++ Ds').reverse (envT.IsType U) := by
    simpa using hTe.onCtx (Γ := []) trivial
  have hcl := VEnv.IsTele.closedN hTo hTe trivial
  have hDcl : ∀ j (D : VExpr), Ds'[j]? = some D → D.ClosedN (Ps.length + j) := by
    intro j D hD
    have := hcl (Ps.length + j) D (by rw [List.getElem?_append_right (by omega)]; simpa using hD)
    simpa using this
  have hicl : ∀ e ∈ c'.indices, e.ClosedN (Ps.length + Ds'.length) := by
    rw [hPl, hDl']
    exact VEnv.WF.ctor_indices_closed henvW hs' (VInductDecl.mem_allCtors_iff.2 ⟨T, hTA', hc'⟩)
  have hccl : (c'.type.instL ls).ClosedN := by
    obtain ⟨_, hty₀⟩ := hcW.type
    exact (hty₀.closedN' hTo.closed trivial).1.instL
  -- the codomain at the two levels
  obtain ⟨hTe₀, ⟨w₀, hw₀⟩⟩ := VEnv.IsType.foralls_inv hTo (hshape ▸ hcW.type)
  have onT₀ : OnCtx (ps ++ Ds).reverse (envT.IsType d.uvars) := by
    simpa using hTe₀.onCtx (Γ := []) trivial
  have hBE := VEnv.IsDefEq.instL_r hTo onT₀ hls hls' heq (by have h := hw₀; simp only [List.append_nil] at h; exact h)
  have hcod : ∀ l, l.length = d.uvars → (T.typeApp (VLevel.params d.uvars)
      (VExpr.bvars d.params.length c'.fields.length) c'.indices).instL l =
      ctorCod T.name c' Ps.length Ds'.length l := by
    intro l hl
    rw [VInductiveType.typeApp_of_none hnone]
    simp only [ctorCod, instL_appN, VExpr.instL, VLevel.params_inst hl, List.map_append,
      instL_bvars, hPl, hDl']
  rw [hcod ls hlen', hcod ls' (by have := List.Forall₂.length_eq heq; omega)] at hBE
  have hctx : ((ps ++ Ds).reverse.map (·.instL ls)) = (Ps ++ Ds').reverse := by
    rw [← hPs, ← hDs']; simp [List.map_reverse]
  rw [hctx] at hBE
  -- the constructor's spine
  have hc0 : env.IsDefEq U [] (.const c'.name ls) (.const c'.name ls') (c'.type.instL ls) :=
    .constDF hci' hls hls' (by simpa using hlen) heq
  rw [hcty] at hc0
  have hspE := VEnv.IsDefEq.appN_bvars' henvW.ordered hc0
  simp only [List.append_nil, List.length_append, VExpr.liftN] at hspE
  -- a structure's facts
  have hstr : IsStruct c'.name = true → StructHyps env U d T c' ls Ps Ds' := by
    intro hIS
    have hP₀ : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le h1)
    have onP : OnCtx d.params.reverse (envT.IsType d.uvars) := by
      simpa using hP₀.onCtx (Γ := []) trivial
    refine ⟨ctors_eq_single_of_eta henvW hs' hT' hc' (hMX.struct _ hIS), hls, hlen', ?_, ?_,
      Ds, hDs'.symm, hDl, fun k D f hD hf => ((VInductDecl.FieldsWF.atSort hIT hFW onP k D f hD hf).1.mono hTle),
      hFW.viewsTele.mono hTle⟩
    · exact onT.mono fun h => h.mono hTle
    · have hTD := VEnv.TeleDefEq.instL' hls hPD
      simp only [List.map_nil] at hTD
      rw [← hPs]
      have := VEnv.TeleDefEq.defeqCtx_of_inj hTo hIT hTD .zero trivial (by simpa using hP₀.instL hls)
      simpa using VEnv.IsDefEqCtx.mono' hTle this
  intro ρ n m a hm ha hmem
  exact AdeqStmt.ctor hMX henvW hΓ₀ hTle hTo hSXT IHT hs' hT' hc' hnodup hci' rfl hndT hstr
    hcty hPl hDl' (hcW.indices.1) hDcl hicl hccl hTe hspE hBE hΓ hm ha hmem

/-- Adequacy's environment cases for the environment with an inductive block's types and
constructors as axioms, in a model interpreting none of the block's constants by given shapes. -/
theorem adequacyHyps_envC (henvW : env.WF)
    (hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (X : AxInterp) (hX : @AxOK _ X) (hXD : @DomRole _ X env)
    {ds : List VDecl} {E E' envT : VEnv} {d : VInductDecl} (hW : VEnv.WF' ds E)
    (hD : VDecl.WF E (.induct d) E') (hext : Extends E' env)
    (hdom : ∀ c, X.dom c → E'.constants c = none)
    (IHall : ∀ X' : AxInterp, @AxOK _ X' → @DomRole _ X' env →
      (∀ c, X'.dom c → E.constants c = none) → @AdequacyHyps env U _ X' henv hU E Γ₀)
    (h1 : E.addConstList d.typeConsts = some envT) (hIT : envT.Inj)
    (HY : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, ConstAt U T.name ls F →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ'))
    {envC : VEnv} (h2 : envT.addConstList d.ctorConsts = some envC) :
    @AdequacyHyps env U _ X henv hU envC Γ₀ := by
  have IHT := adequacyHyps_envT henvW hModel hΓ₀ X hX hXD hW hD hext hdom IHall h1 hIT HY
  have hinds : envC.inducts = envT.inducts := VEnv.addConstList_inducts h2
  have hdfs : envC.defeqs = envT.defeqs := VEnv.addConstList_defeqs' h2
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => IHT.extra hΓ (hdfs ▸ hd),
    fun hΓ h => IHT.projDF hΓ (hinds ▸ h), fun hΓ h => IHT.projIota hΓ (hinds ▸ h),
    fun hΓ h => IHT.projEta hΓ (hinds ▸ h)⟩
  rcases VEnv.addConstList_constants_cases' h2 hc with hc | hci
  · exact IHT.const hΓ hc hls hls' hlen heq hu h7 h8 hA
  · exact ctors_adeq henvW hModel hΓ₀ X hX hXD hW hD hext hdom IHall h1 hIT HY hΓ hci hls hls'
      hlen heq

end LogRel
end Lean4Lean

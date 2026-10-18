import Lean4Lean.Theory.Typing.LogRel.AdeqIota

/-!
# An inductive block's recursors in the logical relation

The recursors are related through `GoodOverC X d.recConsts`, which interprets them by the shapes
at which their applications are related: the second stage after the type formers, the two models
reading the constants before the recursors alike (`recSameOn`). What is left is the recursor's full
application (`IndRecSat`), where iota computes on a constructor major premise and the right-hand
side is related in `GoodOverC`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- A recursor's type after its telescope: the motive at the indices and the major premise. -/
def recBody (d : VInductDecl) (i : Nat) (Ti : VInductiveType) : VExpr :=
  .app (.appN (.bvar (1 + Ti.indices.length + d.allCtors.length + (d.allTypes.length - 1 - i)))
    (VExpr.bvars Ti.indices.length 1)) (.bvar 0)

theorem recType_instL_tele (d : VInductDecl) (ls : List VLevel) (j : Nat) (Tj : VInductiveType) :
    (d.recType d.recLevels d.motiveLevel j Tj).instL ls =
      .foralls (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj)
        (recBody d j Tj) := by
  rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele]; rfl

/-- The models `GoodOverC X d.recConsts` and `X` read alike what the block's types, constructors
and the constants before them read off. -/
def RecSameOn : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  letI := env.shapeEnv; letI := X
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    SameOn env (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) X
      (envC.constants · ≠ none)

/-- A recursor's full application is related, in a model `X`, wherever its `Const` derivation
interprets it, given adequacy for the environment with the block's types and constructors as
axioms, in `X`, and with its recursors too, in `GoodOverC X d.recConsts`. -/
def IndRecSat : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  letI := env.shapeEnv; letI := X
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U _ X henvW.ordered henvW.stepUniq envC Γ₀ →
    @AdequacyHyps env U _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts)
      henvW.ordered henvW.stepUniq envR Γ₀ →
    ∀ {j : Nat} {Tj : VInductiveType} {ls ls₃ : List VLevel} {R : TShape → VExpr → Prop} {n : Nat}
      (rargs : List (WShape n)) {m : TShape}, d.allTypes[j]? = some Tj →
    ls.length = d.recUVars → (∀ l ∈ ls₃, l.WF U) → List.Forall₂ (· ≈ ·) ls ls₃ →
    (∀ h e, R h e → e.ClosedN ∧ LE_Interp env .nil h e ∧
      @LE_Interp _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) env .nil h e) →
    Const env (d.recName j) ls R rargs m →
    rargs.length = (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length →
    ∀ {F F' : VExpr} {σ σ' : VExpr.Subst}, ConstAt U (d.recName j) ls F →
    ConstAt U (d.recName j) ls F' →
    LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ₀ σ σ'
      ((d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).reverse ++ Γ₀)
      (valOf rargs) →
    ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a →
    LE_Interp env (valOf rargs) a.T (recBody d j Tj) →
    (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq (n+1)).DefEq
      (spineAt F (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ)
      (spineAt F' (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ')
      ((recBody d j Tj).subst σ) w a

section
variable [ShapeEnv] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- The `hgood` premise of `AdeqStmt.blockC` for a block's recursors, in a model `X`: through
`GoodC.of_spine`, the recursor's type being its telescope over the motive's application, typed
before the recursors, and given the recursor's full application (`hsat`). -/
theorem recursor_good (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {envC : VEnv} (hCle : envC ≤ env) (hCo : envC.Ordered)
    (hSC : ∀ {Γ M N A}, envC.IsDefEqStrong U Γ M N A → @StrongSoundEq _ X env U Γ M N A)
    (IHC : @AdequacyHyps env U _ X henv hU envC Γ₀)
    (hgen : ∀ p ∈ d.recConsts, p.2.WF envC)
    {s : Name} {t : Nat} (hs : env.inducts s = some (d, t))
    (hdomX : ∀ p ∈ d.recConsts, ¬X.dom p.1)
    (hsat : ∀ {j : Nat} {Tj : VInductiveType} {ls ls₃ : List VLevel} {R : TShape → VExpr → Prop}
      {n : Nat} (rargs : List (WShape n)) {m : TShape}, d.allTypes[j]? = some Tj →
      ls.length = d.recUVars → (∀ l ∈ ls₃, l.WF U) → List.Forall₂ (· ≈ ·) ls ls₃ →
      (∀ h e, R h e → e.ClosedN ∧ @LE_Interp _ X env .nil h e ∧
        @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env .nil h e) →
      @Const _ X env (d.recName j) ls R n rargs m →
      rargs.length = (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length →
      ∀ {F F' : VExpr} {σ σ' : VExpr.Subst}, ConstAt U (d.recName j) ls F →
      ConstAt U (d.recName j) ls F' →
      @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
        ((d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).reverse ++ Γ₀)
        (valOf rargs) →
      ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a →
      @LE_Interp _ X env (valOf rargs) a.T (recBody d j Tj) →
      (LR (U := U) (Γ := Γ₀) henv hU (n+1)).DefEq
        (spineAt F (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ)
        (spineAt F' (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length
          σ')
        ((recBody d j Tj).subst σ) w a) :
    ∀ {n c ci ls R m' a ρ}, (c, ci) ∈ d.recConsts → env.constants c = some ci →
      ls.length = ci.uvars → m'.HasType a → @LE_Interp _ X env ρ a (ci.type.instL ls) →
      @Const _ X env c ls R n [] m' →
      (∀ h e, R h e → @LE_Interp _ X env ρ h e ∧
        @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env ρ h e) →
      GoodC (U := U) henv hU X Γ₀ d.recConsts c ls m' := by
  intro n c ci ls R m' a ρ hci hcon' hlen hm'a ha H hR
  obtain ⟨⟨Tj, j⟩, hmem, he⟩ := List.mem_map.1 hci
  cases he
  have hj : d.allTypes[j]? = some Tj := List.mk_mem_zipIdx_iff_getElem?.1 hmem
  have hclX : ClosedRules env := hMX.closed
  have hclG : ClosedRules env := @ModelEnv.closed _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env hMG
  have H' := @Const.closed _ X env _ _ _ _ _ _ hclX H
  have hR' : ∀ h e, (e.ClosedN ∧ R h e) → @LE_Interp _ X env ρ h e := fun h e hr => (hR h e hr.2).1
  have hRB : ∀ h e, (e.ClosedN ∧ R h e) → e.ClosedN ∧ @LE_Interp _ X env .nil h e ∧
      @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env .nil h e := fun h e hr =>
    ⟨hr.1, (@LE_Interp.closed_iff _ X env hclX _ hr.1 _ _ _).1 (hR h e hr.2).1,
      (@LE_Interp.closed_iff _ (GoodOverC (U := U) henv hU X Γ₀ d.recConsts) env hclG _ hr.1 _ _ _).1
        (hR h e hr.2).2⟩
  let P : List VExpr → VExpr → Prop := fun Γ' A =>
    ∃ Δ, Γ' = Δ ++ Γ₀ ∧ OnCtx Δ (envC.IsType U) ∧ envC.IsType U Δ A
  have hPf : ∀ {Γ' A B}, P Γ' (.forallE A B) → P Γ' A ∧ P (A::Γ') B := by
    rintro Γ' A B ⟨Δ, rfl, hΔ, hT⟩
    obtain ⟨h1, h2⟩ := VEnv.IsType.forallE_inv hCo hT
    exact ⟨⟨Δ, rfl, hΔ, h1⟩, ⟨A::Δ, rfl, ⟨hΔ, h1⟩, h2⟩⟩
  have hTy : ∀ {Γ' T'}, OnCtx Γ' (env.IsType U) → P Γ' T' → ∃ w, env.HasType U Γ' T' (.sort w) ∧
      @StrongSoundEq _ X env U Γ' T' T' (.sort w) ∧
      @AdeqStmt env U _ X henv hU Γ₀ Γ' T' T' (.sort w) := by
    rintro Γ' T' hΓ' ⟨Δ, rfl, hΔ, w, hT⟩
    have D := IsDefEq.weak_closed hCo hΔ hT Γ₀
    exact ⟨w, D.defeq.mono hCle, hSC D, LR.adequacy_of hMX hCle hSC hΓ₀ IHC D hΓ'⟩
  refine GoodC.of_spine (Γ₀ := Γ₀) hMX hΓ₀ P hPf hTy hci hcon' hlen hm'a ha H' hR' (hdomX _ hci) ?_
  intro ls₁ ls₂ ls₃ e1 e2 e3 w1 w2 w3
  refine ⟨d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj, recBody d j Tj,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r k A
    have A0 := ConstArity.recursor (T := Tj) hs rfl hj
    cases hMX.roles A A0
    have := ConstArity.determ A A0
    rw [this, length_recTele]; simp [VInductDecl.majorIdx]; omega
  · refine ⟨[], by simp, trivial, ?_⟩
    have := (hgen _ hci).instL w3 (U' := U)
    simp only [List.map_nil] at this
    rwa [recType_instL_tele] at this
  · intro t' h; rwa [recType_instL_tele] at h
  · intro n' M N w b hb hwb H; rwa [recType_instL_tele]
  · intro n' rargs m H hl F F' σ σ' hF hF' W w a hw hwa ha
    exact hsat rargs hj hlen w3 e3 hRB H hl hF hF' W w a hw hwa ha

end

/-- A block's recursors' constant case, given its structure types' stuck values' typing (`IndHY`),
the second stage's models' agreement (`RecSameOn`) and the recursors' full application
(`IndRecSat`). -/
theorem IndRecCase.of (HY : IndHY) (HSame : RecSameOn) (HS : IndRecSat) : IndRecCase := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
    Γ c ci ls ls' u hΓ hm hls hls' hlen heq hu h7 h8 hA
  letI := env.shapeEnv; letI := X
  have hModel : ∀ Y : AxInterp, @AxOK _ Y → @DomRole _ Y env → @ModelEnv _ Y env :=
    fun Y hY hYD => henvW.modelEnv hY hYD
  have hMX := hModel X hX hXD
  have hle : E' ≤ env := hext.le
  have hext₁ : Extends E env := .step hD hext
  have hEW : E.WF := ⟨_, hW⟩
  have hEo : E.Ordered := hEW.ordered
  obtain ⟨hd, envT, envC, envR, h1, h2, h3, hTE', hnd, hs, hcT, hcC⟩ := induct_facts hD hle
  have hDc := hD
  cases hDc with
  | induct _ hg hadd =>
  have hadd' := hadd
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd'
  obtain ⟨envT', hT', envC', hC', envR', hR', hB'⟩ := hadd'
  cases h1.symm.trans hT'; cases h2.symm.trans hC'; cases h3.symm.trans hR'
  have HB : VEnv.BlockEnvs env d E envT envC envR := ⟨hEW, hd, hg, h1, h2, h3, ⟨E', hB', hle⟩⟩
  have hCo : envC.Ordered := HB.envC_wf.ordered
  have hCR : envC ≤ envR := VEnv.addConstList_le h3
  have hCle : envC ≤ env := hCR.trans HB.envR_le
  have hTC : envT ≤ envC := VEnv.addConstList_le h2
  have hIT := (hR envT envC envR h1 h2 h3).1
  have hJ : LRJoin (U := U) henvW.ordered henvW.stepUniq Γ₀ :=
    fun hc h1 h2 d1 d2 => (LR henvW.ordered henvW.stepUniq _).join hc h1 h2 d1 d2
  have hdomT : ∀ c, X.dom c → envT.constants c = none :=
    fun c h => VEnv.constants_none_of_le hTE' (hdom c h)
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le (VEnv.addConstList_le h1) (hdomT c h)
  have hY := HY henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall
  have IHC := adequacyHyps_envC henvW hModel hΓ₀ X hX hXD hW hD hext hdomT IHall h1 hIT hY h2
  -- the block's recursors
  obtain ⟨T0, hT0⟩ : ∃ T0, d.types[0]? = some T0 := by
    cases e : d.types with
    | nil => exact (hd.nonempty e).elim
    | cons T _ => exact ⟨T, rfl⟩
  obtain ⟨t0, hs0, -⟩ := hs T0 (List.mem_of_getElem? hT0)
  have hndR : (d.recConsts.map (·.1)).Nodup := (VEnv.addConstList_spec h3).1
  have hfrR : ∀ p ∈ d.recConsts, envC.constants p.1 = none := (VEnv.addConstList_spec h3).2.1
  have hgen : ∀ p ∈ d.recConsts, p.2.WF envC := (hg envT envC envR h1 h2 h3).1
  have hcon : ∀ p ∈ d.recConsts, env.constants p.1 = some p.2 := fun p hp =>
    HB.envR_le.constants (VEnv.addConstList_constants_of_mem h3 hp)
  have hGax : @AxOK _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) := GoodOverC.axOK X hX hMX hJ hndR
  have hGD : @DomRole _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) env := GoodOverC.domRole X hXD fun p hp {r k} A => by
    obtain ⟨⟨Tj, j⟩, hmem, rfl⟩ := List.mem_map.1 hp
    have hj : d.allTypes[j]? = some Tj := List.mk_mem_zipIdx_iff_getElem?.1 hmem
    cases hMX.roles A (ConstArity.recursor (T := Tj) hs0 rfl hj); trivial
  have hMG := hModel (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) hGax hGD
  have hdomGT : ∀ c, @AxInterp.dom _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) c → envT.constants c = none := by
    rintro c (hc | hc)
    · exact hdomT c hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      exact VEnv.constants_none_of_le hTC (hfrR p hp)
  have hdomGE : ∀ c, @AxInterp.dom _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le (VEnv.addConstList_le h1) (hdomGT c h)
  have hsGX := hext₁.sameOn hW (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) X hdomGE hdomE
  have hsXG := hext₁.sameOn hW X (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) hdomE hdomGE
  -- stuck structure values typed, in the second stage's model
  have hYG : ∀ T ∈ d.types, ∀ {ls ls₃ : List VLevel} {n} (rargs : List (WShape n)) {F : VExpr}
      {σ σ' : VExpr.Subst}, (∀ l ∈ ls₃, l.WF U) → List.Forall₂ (· ≈ ·) ls ls₃ →
      ls.length = d.uvars → ConstAt U T.name ls F →
      @LR.SubstWF env U _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) henvW.ordered henvW.stepUniq Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ) ∧
        StructTy env U Γ₀ (typeHeadOf T.name rargs.length T)
          (spineAt F (d.params ++ T.indices).length σ') := by
    intro T hT ls ls₃ n rargs F σ σ' w3 e3 hlen hF W hl
    have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hT
    have hPIE : E.IsTele d.uvars [] (d.params ++ T.indices) :=
      VEnv.IsTele.append hd.params (by simpa using hd.indices T hTA)
    have hQB : (VExpr.foralls (d.params ++ T.indices) (.sort d.level)).ConstsSat
        (E.constants · ≠ none) := by
      obtain ⟨w, hw⟩ := hPIE.foralls (B := .sort d.level) ⟨_, .sort hd.level⟩
      exact ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hEo hw trivial).1
    refine hY T hT rargs w3 e3 hlen hF (W.sameOn hsGX hsXG _ rfl fun A hA => ?_) hl
    obtain ⟨A₀, hA₀, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hA)
    exact (hQB.foralls_l A₀ hA₀).instL
  have IHGC := adequacyHyps_envC henvW hModel hΓ₀ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) hGax hGD hW hD hext hdomGT IHall h1 hIT hYG h2
  have hdecl : ∀ p ∈ d.recConsts, env.constants p.1 = some p.2 ∧
      p.2.type.ConstsSat (envC.constants · ≠ none) := fun p hp => by
    refine ⟨hcon p hp, ?_⟩
    obtain ⟨w, hw⟩ := hgen p hp
    exact ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hCo hw trivial).1
  have IHGR := AdequacyHyps.addGoodC X hMX hndR
    (HSame henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3) hdecl (fun p hp => hp)
    IHGC h3
  -- soundness of the model for the environment before the recursors
  have hX₁ : SoundHyps E env := soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX)
    hW hext₁.le (fun hdf e hx => VEnv.WF.rule_head hEW hdf e (hdomE _ hx))
    (VEnv.WF.noDomI hEW hdomE)
  have hXC : SoundHyps envC env := hX₁.mono
    (fun h => by rwa [VEnv.addConstList_defeqs' h2, VEnv.addConstList_defeqs' h1] at h)
    (fun h => by rwa [VEnv.addConstList_inducts h2, VEnv.addConstList_inducts h1] at h)
  have hdomR : ∀ p ∈ d.recConsts, ¬X.dom p.1 := fun p hp hx => by
    have h := hdom _ hx
    rw [(VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB')).constants
      (VEnv.addConstList_constants_of_mem h3 hp)] at h
    cases h
  have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
      (.const c ls) (.const c ls') (ci.type.instL ls) :=
    AdeqStmt.blockC X hMX hndR hcon
      (recursor_good X hMX hMG hΓ₀ hCle hCo (fun D => hXC.strongSound hMX hCle D) IHC hgen hs0
        hdomR (HS henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHC IHGR))
      hm hls hls' heq
  exact @key

/-- The second stage's model reads alike, with `X`, what the constants before the recursors read
off: the constants before the block by `Extends.sameOn`; the block's types and constructors are
typed before the recursors and have no rule. -/
theorem recSameOn : RecSameOn := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall envT envC envR h1 h2 h3
  letI := env.shapeEnv; letI := X
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  have hle : E' ≤ env := hext.le
  have hext₁ : Extends E env := .step hD hext
  have hEW : E.WF := ⟨_, hW⟩
  have hEo := hEW.ordered
  obtain ⟨hd, envT', envC', envR', h1', h2', h3', hTE', hnd, hs, hcT, hcC⟩ := induct_facts hD hle
  cases h1.symm.trans h1'; cases h2.symm.trans h2'; cases h3.symm.trans h3'
  have hDc := hD
  cases hDc with
  | induct _ hg hadd =>
  have hadd' := hadd
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd'
  obtain ⟨envT', hT', envC', hC', envR', hR', hB'⟩ := hadd'
  cases h1.symm.trans hT'; cases h2.symm.trans hC'; cases h3.symm.trans hR'
  have HB : VEnv.BlockEnvs env d E envT envC envR := ⟨hEW, hd, hg, h1, h2, h3, ⟨E', hB', hle⟩⟩
  have hET : E ≤ envT := VEnv.addConstList_le h1
  have hTC : envT ≤ envC := VEnv.addConstList_le h2
  have hCE' : envC ≤ E' := (VEnv.addConstList_le h3).trans
    (VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB'))
  have hTo := HB.envT_wf.ordered
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le (hET.trans (hTC.trans hCE')) (hdom c h)
  have base := hext₁.sameOn hW X X hdomE hdomE
  have hEC : ∀ c, E.constants c ≠ none → envC.constants c ≠ none := fun c h => by
    obtain ⟨ci, e⟩ := Option.ne_none_iff_exists'.1 h
    rw [(hET.trans hTC).constants e]; nofun
  have hmono {e : VExpr} (h : e.ConstsSat (E.constants · ≠ none)) :
      e.ConstsSat (envC.constants · ≠ none) := ConstsSat.mono hEC h
  have hmonoT {e : VExpr} (h : e.ConstsSat (envT.constants · ≠ none)) :
      e.ConstsSat (envC.constants · ≠ none) := ConstsSat.mono (fun c h' => by
    obtain ⟨ci, e⟩ := Option.ne_none_iff_exists'.1 h'
    rw [hTC.constants e]; nofun) h
  -- what `envC` declares
  have hcls : ∀ c, envC.constants c ≠ none → E.constants c ≠ none ∨
      (∃ T ∈ d.types, c = T.name) ∨ (∃ T ∈ d.types, ∃ c' ∈ T.ctors, c = c'.name) := by
    intro c hc
    rcases ((VEnv.addConstList_spec h2).2.2 c).1 hc with hc | hc
    · rcases ((VEnv.addConstList_spec h1).2.2 c).1 hc with hc | hc
      · exact .inl hc
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
        exact .inr (.inl ⟨T, hT, rfl⟩)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      obtain ⟨⟨j, c'⟩, hp2, rfl⟩ := List.mem_map.1 hp
      obtain ⟨T, hT, hc'⟩ := VInductDecl.mem_ctors_iff.1 hp2
      exact .inr (.inr ⟨T, List.mem_of_getElem? hT, c', hc', rfl⟩)
  -- the roles of the block's types and constructors
  have roleT : ∀ T ∈ d.types, ∃ t, ConstArity env T.name (.indTy d t)
      (d.params.length + T.indices.length) := fun T hT => by
    obtain ⟨t, h, h'⟩ := hs T hT; exact ⟨t, .indTy h h'⟩
  have roleC : ∀ T ∈ d.types, ∀ c' ∈ T.ctors, ∃ t' : Nat,
      ConstArity env c'.name (.ctor d t' c') (d.params.length + c'.fields.length) := by
    intro T hT c' hc'
    obtain ⟨t, h, h'⟩ := hs T hT; exact ⟨t, .ctor h h' hc' rfl⟩
  have hdomRec : ∀ c, c ∈ d.recConsts.map (·.1) → envC.constants c = none := by
    intro c hc; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact (VEnv.addConstList_spec h3).2.1 p hp
  refine ⟨fun hq hx => ?_, fun hq hx => hq (VEnv.constants_none_of_le hCE' (hdom _ hx)),
    fun hdf e hq => ?_, fun h hq => ?_, fun hs' hq hT0 hc0 => ?_, fun hs' hq e hq' => ?_,
    fun hdf hq h => ?_⟩
  · rcases hx with hx | hx
    · exact hq (VEnv.constants_none_of_le hCE' (hdom _ hx))
    · exact hq (hdomRec _ hx)
  · rcases hcls _ hq with hq | ⟨T, hT, rfl⟩ | ⟨T, hT, c', hc', rfl⟩
    · exact hmono (base.delta hdf e hq)
    · obtain ⟨t, A⟩ := roleT T hT; cases hMX.roles A (.delta hdf e)
    · obtain ⟨t', A⟩ := roleC T hT c' hc'; cases hMX.roles A (.delta hdf e)
  · rcases hcls _ hq with hq | ⟨T, hT, rfl⟩ | ⟨T, hT, c', hc', rfl⟩
    · exact hmono (base.constType h hq)
    · rw [hcT T hT] at h; cases h
      obtain ⟨w, hw⟩ := (hd.types T hT).1
      exact hmono (ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hEo hw trivial).1)
    · rw [hcC T hT c' hc'] at h; cases h
      obtain ⟨t, -, hT'⟩ := hs T hT
      obtain ⟨w, hw⟩ := ((hd.ctors envT h1 T (VInductDecl.mem_allTypes_of_types hT)).2 c'
        hc').type
      exact hmonoT (ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hTo hw trivial).1)
  · rcases hcls _ hq with hq | ⟨T, hT, rfl⟩ | ⟨T, hT, c', hc', rfl⟩
    · exact hmono (base.ctorType hs' hq hT0 hc0)
    · obtain ⟨t₁, h₁, -⟩ := hs T hT
      cases hs'.symm.trans h₁
      obtain ⟨w, hw⟩ := ((hd.ctors envT h1 _
        (VInductDecl.mem_allTypes_of_types (List.mem_of_getElem? hT0))).2 _ hc0).type
      exact hmonoT (ConstsSat.of_isSome (VEnv.IsDefEq.constsSat hTo hw trivial).1)
    · obtain ⟨t', A⟩ := roleC T hT c' hc'; cases hMX.roles A (.indTy hs' hT0)
  · obtain ⟨T', hT', -⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq')
    rcases hcls _ hq with hq | ⟨T, hT, rfl⟩ | ⟨T, hT, c', hc', rfl⟩
    · exact hmono (base.iotaRhs hs' hq e hq')
    · obtain ⟨t, A⟩ := roleT T hT; cases hMX.roles A (.recursor hs' e hT')
    · obtain ⟨t', A⟩ := roleC T hT c' hc'; cases hMX.roles A (.recursor hs' e hT')
  · rcases hcls _ hq with hq | ⟨T, hT, e⟩ | ⟨T, hT, c', hc', e⟩
    · exact hmono (base.quotMk hdf hq h)
    · obtain ⟨t, A⟩ := roleT T hT; cases hMX.roles A (.quotTy hdf e.symm)
    · obtain ⟨t', A⟩ := roleC T hT c' hc'; cases hMX.roles A (.quotTy hdf e.symm)

end LogRel
end Lean4Lean

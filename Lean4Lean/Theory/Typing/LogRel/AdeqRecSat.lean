import Lean4Lean.Theory.Typing.LogRel.AdeqRec

/-!
# A recursor's full application, by the `Const` derivation's case

At full arity a recursor's interpretation is `bot`, or computes by iota on a constructor shape, or
(at levels where its type is a proposition with large elimination) by the K-like rule on any major
premise. `IndRecSat` reduces to the two computing cases, `RecIotaSat` and `RecKSat`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- Iota on a constructor shape: the recursor's own block and type, a constructor `c'` of it whose
field shapes `fs` the major premise's shape `x` is above, and the right-hand side `h` applied. -/
def RecIotaSat : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  letI := env.shapeEnv; letI := X
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U _ X henvW.ordered henvW.stepUniq envC Γ₀ →
    @AdequacyHyps env U _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts)
      henvW.ordered henvW.stepUniq envR Γ₀ →
    ∀ {j : Nat} {Tj : VInductiveType} {ls ls₃ : List VLevel} {R : TShape → VExpr → Prop},
    d.allTypes[j]? = some Tj → ls.length = d.recUVars → (∀ l ∈ ls₃, l.WF U) →
    List.Forall₂ (· ≈ ·) ls ls₃ →
    (∀ h e, R h e → e.ClosedN ∧ LE_Interp env .nil h e ∧
      @LE_Interp _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) env .nil h e) →
    ∀ {F F' : VExpr} {σ σ' : VExpr.Subst}, ConstAt U (d.recName j) ls F →
    ConstAt U (d.recName j) ls F' →
  ∀ {n} {fs : List (WShape n)} {x : WShape (n+1)} {rest : List (WShape (n+1))}
    {c' : VConstructor} {q : Nat} {h m : TShape},
    d.allCtors[q]? = some (j, c') → ¬d.PropAt (d.blockLevels ls) → rest.length = d.majorIdx Tj →
    fs.length = c'.fields.length → R h (d.iotaRhs ls q j c') →
    AppS h ((rest.reverse.take (d.params.length + d.allTypes.length + d.allCtors.length)).map
      (·.T) ++ fs.map (·.T)) m → (WShape.ctor' c'.name fs).T ≤ x.T →
    LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ₀ σ σ'
      ((d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).reverse ++ Γ₀)
      (valOf (x :: rest)) →
    ∀ (w a : WShape (n+2)), w.T ≤ m → w.HasType a →
    LE_Interp env (valOf (x :: rest)) a.T (recBody d j Tj) →
    (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq (n+2)).DefEq
      (spineAt F (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ)
      (spineAt F' (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ')
      ((recBody d j Tj).subst σ) w a

/-- The K-like rule: at a proposition with large elimination, the single constructor `c'`'s
right-hand side at the field shapes read off the indices, on any major premise `e`. -/
def RecKSat : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E _ d} =>
  letI := env.shapeEnv; letI := X
  ∀ {envT envC envR}, E.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    @AdequacyHyps env U _ X henvW.ordered henvW.stepUniq envC Γ₀ →
    @AdequacyHyps env U _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts)
      henvW.ordered henvW.stepUniq envR Γ₀ →
    ∀ {j : Nat} {Tj : VInductiveType} {ls ls₃ : List VLevel} {R : TShape → VExpr → Prop},
    d.allTypes[j]? = some Tj → ls.length = d.recUVars → (∀ l ∈ ls₃, l.WF U) →
    List.Forall₂ (· ≈ ·) ls ls₃ →
    (∀ h e, R h e → e.ClosedN ∧ LE_Interp env .nil h e ∧
      @LE_Interp _ (GoodOverC (U := U) henvW.ordered henvW.stepUniq X Γ₀ d.recConsts) env .nil h e) →
    ∀ {F F' : VExpr} {σ σ' : VExpr.Subst}, ConstAt U (d.recName j) ls F →
    ConstAt U (d.recName j) ls F' →
  ∀ {n} {e : WShape n} {rargs : List (WShape n)} {c' : VConstructor} {q : Nat} {h m : TShape},
    d.allCtors[q]? = some (j, c') → Tj.ctors = [c'] → d.PropAt (d.blockLevels ls) →
    d.largeElim = true → rargs.length = d.majorIdx Tj → R h (d.iotaRhs ls q j c') →
    AppS h ((rargs.reverse.take (d.params.length + (d.allTypes.length + d.allCtors.length))).map
      (·.T) ++ kFieldShapes c' ((rargs.reverse.drop
        (d.params.length + (d.allTypes.length + d.allCtors.length))).map (·.T))) m →
    LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ₀ σ σ'
      ((d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).reverse ++ Γ₀)
      (valOf (e :: rargs)) →
    ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a →
    LE_Interp env (valOf (e :: rargs)) a.T (recBody d j Tj) →
    (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq (n+1)).DefEq
      (spineAt F (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ)
      (spineAt F' (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ')
      ((recBody d j Tj).subst σ) w a

/-- A recursor's full application, from its two computing cases: the others are `bot`, or ruled
out by the recursor's role and arity. -/
theorem IndRecSat.of (HI : RecIotaSat) (HK : RecKSat) : IndRecSat := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
    envT envC envR h1 h2 h3 IHC IHG j Tj ls ls₃ R n rargs m hj hlen w3 e3 hRB H hl
    F F' σ σ' hF hF' W w a hw hwa ha
  letI := env.shapeEnv; letI := X
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  have hle : E' ≤ env := hext.le
  obtain ⟨hd, -, -, -, -, -, -, -, -, hs, -, -⟩ := induct_facts hD hle
  obtain ⟨T0, hT0⟩ : ∃ T0, d.types[0]? = some T0 := by
    cases e : d.types with
    | nil => exact (hd.nonempty e).elim
    | cons T _ => exact ⟨T, rfl⟩
  obtain ⟨t0, hs0, -⟩ := hs T0 (List.mem_of_getElem? hT0)
  have hA : ConstArity env (d.recName j) (.recursor d j) (d.majorIdx Tj + 1) :=
    .recursor hs0 rfl hj
  have hl' : rargs.length = d.majorIdx Tj + 1 := by
    rw [hl, length_recTele]; simp [VInductDecl.majorIdx]; omega
  have hbotm : m ≤ TShape.bot → (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq (n+1)).DefEq
      (spineAt F (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ)
      (spineAt F' (d.recTele (d.recLevels.map (·.inst ls₃)) (d.motiveLevel.inst ls₃) Tj).length σ')
      ((recBody d j Tj).subst σ) w a := by
    intro hb
    cases show w = .bot from TShape.le_bot.1 (hw.trans hb)
    exact (LR _ _ _).bot hwa.isType
  -- the recursor is declared, so not interpreted by given shapes
  have hnd : ¬X.dom (d.recName j) := by
    intro h0
    have hc := hdom _ h0
    cases hD with
    | induct _ _ hadd =>
    simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
    obtain ⟨envT', hT', envC', hC', envR', hR', hB'⟩ := hadd
    cases h1.symm.trans hT'; cases h2.symm.trans hC'; cases h3.symm.trans hR'
    have hmem : (d.recName j, (⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩ : VConstant))
        ∈ d.recConsts :=
      List.mem_map.2 ⟨(Tj, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩
    have := VEnv.addConstList_constants_of_mem h3 hmem
    rw [VEnv.addBlock_constants hB', VEnv.addDefEqList_constants', this] at hc
    cases hc
  cases H with
  | bot => exact hbotm TShape.bot_eqv.1
  | lam he hle' => exact hbotm (Const.lam_le_bot hMX.roles he hle' (hl' ▸ hA))
  | ext h0 => exact (hnd h0).elim
  | delta _ h1' h2' => cases hMX.roles (.delta h1' h2') hA
  | indTy h1' h2' => cases hMX.roles (.indTy h1' h2') hA
  | ctor h1' h2' h3' h4' => cases hMX.roles (.ctor h1' h2' h3' h4') hA
  | quotTy h1' h2' => cases hMX.roles (.quotTy h1' h2') hA
  | quotMk h1' h2' => cases hMX.roles (.quotMk h1' h2') hA
  | quot h1' h2' => cases hMX.roles (.quotLift h1' h2') hA
  | quotK h1' h2' => cases hMX.roles (.quotLift h1' h2') hA
  | iota h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' =>
    have e := hMX.roles (.recursor h1' h2' h4') hA
    cases e
    cases h4'.symm.trans hj
    exact HI henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHC IHG hj hlen w3 e3 hRB
      hF hF' h3' h5' h6' h7' h8' h9' h10' W w a hw hwa ha
  | kIota h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' =>
    have e := hMX.roles (.recursor h1' h2' h4') hA
    cases e
    cases h4'.symm.trans hj
    exact HK henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall h1 h2 h3 IHC IHG hj hlen w3 e3 hRB
      hF hF' h3' h5' h6' h7' h8' h9' h10' W w a hw hwa ha

end LogRel
end Lean4Lean

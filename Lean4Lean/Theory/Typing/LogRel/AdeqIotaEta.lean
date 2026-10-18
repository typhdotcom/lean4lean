import Lean4Lean.Theory.Typing.LogRel.AdeqIotaK
import Lean4Lean.Theory.Typing.LogRel.ProjRed

/-!
# An iota rule of a structure with eta

There the recursor computes on any major premise at its projections (`Step.etaIota`), so the left
body computes to the right body with the fields replaced by the projections of the constructor
application, each of which reduces, typed, to its field.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- A recursor's telescope at its major premise. -/
theorem recTele_major (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (Tj : VInductiveType) :
    (d.recTele lsB v Tj)[d.params.length + d.allTypes.length + d.allCtors.length +
      Tj.indices.length]? = some (Tj.typeApp lsB (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + Tj.indices.length))
        (VExpr.bvars Tj.indices.length 0)) := by
  have hb : (d.recBinders lsB v).length = d.params.length + d.allTypes.length +
      d.allCtors.length := by
    simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega
  simp only [VInductDecl.recTele]
  rw [List.getElem?_append_right (by simp [hb])]
  simp [hb]

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- The major premise of an iota rule's left body at a substitution. -/
def iotaMajor (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor)
    (σ : VExpr.Subst) : VExpr :=
  (d.ctorAppAt j c lsB (VExpr.bvars d.params.length
    (d.allTypes.length + d.allCtors.length + c.fields.length))
    (VExpr.bvars c.fields.length 0)).subst σ

/-- Structure eta's replacement of a substitution's fields: the major premise's projections. -/
def etaRepl (d : VInductDecl) (s : Name) (lsB : List VLevel) (j : Nat) (c : VConstructor)
    (σ : VExpr.Subst) : VExpr.Subst :=
  (σ.drop c.fields.length).consList (VExpr.projs s c.fields.length (iotaMajor d lsB j c σ))

/-- An iota rule of a structure with eta is related where its sides are interpreted: its left
body computes by structure eta to the right body at the major premise's projections, each of
which reduces, typed, to the field. -/
theorem iotaRule_adeq_eta (henvW : env.WF) (hM : ModelEnv env) {E E₂ : VEnv} (hEE : E ≤ E₂)
    (hE₂le : E₂ ≤ env) (hEo : E.Ordered) (hE₂o : E₂.Ordered)
    (hX : SoundHyps E env) (hX₂ : SoundHyps E₂ env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    (hI : E.Inj) (hk : KClosed env)
    {d : VInductDecl} {q j : Nat} {c : VConstructor} {T : VInductiveType}
    (hsT : env.inducts T.name = some (d, j)) (hT : d.types[j]? = some T) (hTc : T.ctors = [c])
    (hq : d.allCtors[q]? = some (j, c)) (hTn : T.nested = none) (hTi : T.indices = [])
    (hcidx : c.indices.length = T.indices.length) (hF : VEnv.ProjFacts env d c)
    (hrec : E.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j T⟩)
    (hdf₂ : E₂.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c))
    {L₀ R₀ A₀ : VExpr}
    (hB : (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).BodyWF E
      (d.iotaBinders d.recLevels d.motiveLevel c) L₀ R₀ A₀)
    {Γ : List VExpr} {ls : List VLevel} (hΓ : OnCtx Γ (env.IsType U)) (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.recUVars)
    (hPA : ¬d.PropAt (d.blockLevels ls)) (hER : d.EtaRec j (d.blockLevels ls)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls) := by
  have hEenv : E ≤ env := hEE.trans hE₂le
  have hBAform : (d.iotaBinders d.recLevels d.motiveLevel c).map (·.instL ls) =
      d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).2.2
    rw [VLevel.inst_map_id hlen, hB.type, VEnv.foralls_instL', iotaRule_type] at h3
    exact (VExpr.foralls_inj h3 (by simp [length_iotaBinders])).1
  have hLform : L₀.instL ls = iotaL d (d.recLevels.map (·.inst ls)) ls j c := by
    have h3 := (d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars) d.motiveLevel q j c).1
    rw [VLevel.inst_map_id hlen, hB.lhs, VEnv.lams_instL', iotaRule_lhs] at h3
    exact (VExpr.lams_inj h3 (by simp [length_iotaBinders])).2
  generalize hBs : d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c = Bs
    at hBAform
  have teleE : E.IsTele U [] Bs := by
    have := hB.tele.instL hls (U' := U); simpa [hBAform] using this
  have hon : OnCtx Bs.reverse (E.IsType U) := by simpa using teleE.onCtx (Γ := []) trivial
  have hLt : E.HasType U Bs.reverse (iotaL d (d.recLevels.map (·.inst ls)) ls j c) (A₀.instL ls) := by
    have := hB.hasL.instL hls (U' := U)
    rw [← hLform]; simpa [← hBAform, List.map_reverse] using this
  have hGΔ : Bs.reverse ++ Γ = (Bs.drop (d.params.length + d.allTypes.length +
      d.allCtors.length)).reverse ++ ((Bs.take (d.params.length + d.allTypes.length +
      d.allCtors.length)).reverse ++ Γ) := by
    rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]
  subst hBs
  have hlsB : ∀ l ∈ d.recLevels.map (·.inst ls), l.WF U := by
    intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls
  have hlsBl : (d.recLevels.map (·.inst ls)).length = d.uvars := by
    simp only [List.length_map, VInductDecl.recLevels]; split <;> simp
  have hlsBe : d.recLevels.map (·.inst ls) = d.blockLevels ls := recLevels_inst d hlen
  have hj : d.allTypes[j]? = some T := VInductDecl.allTypes_getElem? hT
  have hcI : c.indices = [] := List.eq_nil_of_length_eq_zero (by rw [hcidx, hTi]; rfl)
  have hmaj (σ : VExpr.Subst) : iotaMajor d (d.recLevels.map (·.inst ls)) j c σ =
      (VExpr.const c.name (d.recLevels.map (·.inst ls))).appN (iotaPs d c σ ++ iotaFs c σ) := by
    simp only [iotaMajor, VInductDecl.ctorAppAt, hj, Option.getD_some, VInductiveType.ctorApp_of_none hTn,
      VExpr.subst_appN, List.map_append]; rfl
  have hPA' : ∀ k < c.fields.length, d.ProjAllowed c (d.recLevels.map (·.inst ls)) k := by
    obtain ⟨T', c', h1, h2, -, -, -, h6⟩ := hER
    cases hT.symm.trans h1
    rw [hTc] at h2; cases h2
    rw [hlsBe]; exact h6
  -- typing at a substitution of the binders
  have Hmaj {σ : VExpr.Subst} (W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ)) :
      env.HasType U Γ₀ ((VExpr.const c.name (d.recLevels.map (·.inst ls))).appN
        (iotaPs d c σ ++ iotaFs c σ))
        ((VExpr.const T.name (d.recLevels.map (·.inst ls))).appN (iotaPs d c σ ++ [])) := by
    have H := iotaL_arg_typed hI hEo hEenv henvW.ordered hls hlen hrec hcidx hon hLt hΓ₀ W0
      (d.params.length + d.allTypes.length + d.allCtors.length + T.indices.length)
      (by rw [length_iotaArgs]; omega) (by rw [length_recTele]; omega)
    rw [getElem_of_getElem?' _ (recTele_major d _ _ T)] at H
    have e1 : ((iotaArgs d (d.recLevels.map (·.inst ls)) j c).map (·.subst σ)) =
        iotaPs d c σ ++ iotaMs d c σ ++ [iotaMajor d (d.recLevels.map (·.inst ls)) j c σ] := by
      rw [iotaArgs_subst]; simp only [iotaIdx, hcI, List.map_nil, List.append_nil]; rfl
    have hl : (iotaPs d c σ ++ iotaMs d c σ).length =
        d.params.length + d.allTypes.length + d.allCtors.length := by
      simp [length_iotaPs, length_iotaMs]; omega
    have e2 : ((iotaArgs d (d.recLevels.map (·.inst ls)) j c)[d.params.length +
        d.allTypes.length + d.allCtors.length + T.indices.length]'(by
          rw [length_iotaArgs]; omega)).subst σ =
        iotaMajor d (d.recLevels.map (·.inst ls)) j c σ := by
      rw [← List.getElem_map (f := fun x : VExpr => x.subst σ)]
      refine getElem_of_getElem?' (by simp [length_iotaArgs]; omega) ?_
      rw [e1, hTi, List.length_nil, Nat.add_zero, ← hl, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]; rfl
    have e3 : ((iotaArgs d (d.recLevels.map (·.inst ls)) j c).take (d.params.length +
        d.allTypes.length + d.allCtors.length + T.indices.length)).map (·.subst σ) =
        iotaPs d c σ ++ iotaMs d c σ := by
      rw [List.map_take, e1, hTi, List.length_nil, Nat.add_zero, ← hl, List.take_left' rfl]
    rw [e2, e3, hmaj, VInductiveType.typeApp_subst, VInductiveType.typeApp_of_none hTn, hTi] at H
    simp only [List.length_nil, Nat.add_zero, VExpr.bvars, List.range_zero, List.reverse_nil,
      List.map_nil] at H
    have e4 : (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length)).map
        (·.subst (Subst.id.consList (iotaPs d c σ ++ iotaMs d c σ))) = iotaPs d c σ := by
      have := VExpr.bvars_subst_consList_mid .id (iotaPs d c σ) (iotaMs d c σ) []
      simpa [length_iotaPs, length_iotaMs] using this
    simp only [VExpr.bvars] at e4
    rw [e4] at H
    exact H
  have Hfs {σ : VExpr.Subst} (W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ))
      (k : Nat) (h : k < (iotaFs c σ).length) (f : VField) (hf : c.fields[k]? = some f) :
      env.HasType U Γ₀ (iotaFs c σ)[k] ((f.type.instL (d.recLevels.map (·.inst ls))).subst
        (Subst.dflt.consList (iotaPs d c σ ++ (iotaFs c σ).take k))) := by
    have h' : k < c.fields.length := by simpa [length_iotaFs] using h
    have KO := (kfields_own (Tj := T) hI hEo hEenv henvW.ordered hk hsT hq hcidx hls hlen hrec hon
      hLt hΓ₀ W0).fields k h h'
    rw [(List.getElem?_eq_some_iff.1 hf).2] at KO
    rwa [ClosedN.subst_consList_base (τ := Subst.dflt) (by
      simpa [length_iotaPs, Nat.min_eq_left (Nat.le_of_lt h)] using
        (hk.field hsT hq hf).instL (ls := d.recLevels.map (·.inst ls)))] at KO
  have hBsplit : d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c =
      d.params.map (·.instL (d.recLevels.map (·.inst ls))) ++
        (d.motiveTypes (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) ++
          d.minorTypes (d.recLevels.map (·.inst ls)) ++
          VExpr.liftTele (d.allTypes.length + d.allCtors.length)
            (c.fields.map (·.type.instL (d.recLevels.map (·.inst ls))))) := by
    simp [VInductDecl.iotaBinders, VInductDecl.recBinders, List.append_assoc]
  have Hps {σ : VExpr.Subst} (W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ)) :
      VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList (iotaPs d c σ))
        (Subst.dflt.consList (iotaPs d c σ))
        (d.params.map (·.instL (d.recLevels.map (·.inst ls)))).reverse := by
    have hon' : OnCtx (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
        (env.IsType U) := hon.mono fun ⟨w, h⟩ => ⟨w, h.mono hEenv⟩
    have W1 := Ctx.SubstEq.vals henvW.ordered hon' W0
    rw [List.length_reverse, length_iotaBinders, iota_vals] at W1
    rw [hBsplit, List.reverse_append, List.append_assoc (iotaPs d c σ),
      Subst.consList_append] at W1
    have W2 := VEnv.Ctx.SubstEq.dropList (by
      simp [length_iotaMs, length_iotaFs, VInductDecl.minorTypes]; omega) (by
      simp [length_iotaMs, length_iotaFs, VInductDecl.minorTypes]; omega) W1
    have hcl : CtxClosed (d.params.map (·.instL (d.recLevels.map (·.inst ls)))).reverse := by
      have := (VEnv.IsTele.append_inv (hBsplit ▸ teleE)).1.onCtx (Γ := []) trivial
      simp only [List.append_nil] at this
      exact this.ctxClosed hEo
    have hval : ∀ i < (d.params.map (·.instL (d.recLevels.map (·.inst ls)))).reverse.length,
        Subst.id.consList (iotaPs d c σ) i = Subst.dflt.consList (iotaPs d c σ) i := by
      intro i hi
      simp only [List.length_reverse, List.length_map] at hi
      rw [Subst.consList_lt _ _ _ (by rw [length_iotaPs]; exact hi),
        Subst.consList_lt _ _ _ (by rw [length_iotaPs]; exact hi)]
    exact Ctx.SubstEq.congr_closed hcl hval hval W2
  have Hproj {σ : VExpr.Subst} (W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ))
      (k : Nat) (hk' : k < c.fields.length) :
      TRed env U Γ₀ (.proj T.name k ((VExpr.const c.name (d.recLevels.map (·.inst ls))).appN
        (iotaPs d c σ ++ iotaFs c σ))) ((iotaFs c σ)[k]'(by simp [length_iotaFs]; exact hk'))
        ((c.fields[k].type.instL (d.recLevels.map (·.inst ls))).subst (Subst.id.consList
          (iotaPs d c σ ++ VExpr.projs T.name k ((VExpr.const c.name
            (d.recLevels.map (·.inst ls))).appN (iotaPs d c σ ++ iotaFs c σ))))) := by
    obtain ⟨u, hu⟩ := (Hmaj W0).isType henvW.ordered hΓ₀
    have H := TRed.proj_ctor henvW.ordered hΓ₀ hsT hT hTc hF hlsB hlsBl (As := iotaPs d c σ)
      (I := []) (length_iotaPs d c σ) (by simp [hTi]) (length_iotaPs d c σ) (length_iotaFs c σ)
      (Hps W0) hu (TRed.refl (Hmaj W0)) (Hmaj W0) (fun k h f hf => Hfs W0 k h f hf)
      (List.getElem?_eq_getElem hk')
      (List.getElem?_eq_getElem (by simp [length_iotaFs]; exact hk')) (hPA' k hk')
    simp only [VConstructor.projType, List.getElem?_eq_getElem hk', Option.map_some,
      Option.getD_some] at H
    rwa [ClosedN.subst_consList_base (τ := .id) (by
      simpa [length_iotaPs] using
        (hk.field hsT hq (List.getElem?_eq_getElem hk')).instL
          (ls := d.recLevels.map (·.inst ls)))] at H
  have hpl (σ : VExpr.Subst) : (VExpr.projs T.name c.fields.length
      (iotaMajor d (d.recLevels.map (·.inst ls)) j c σ)).length = c.fields.length :=
    VExpr.length_projs
  have e1 (σ : VExpr.Subst) :
      iotaPs d c (etaRepl d T.name (d.recLevels.map (·.inst ls)) j c σ) = iotaPs d c σ :=
    iota_params_consList _ _ _ σ (hpl σ)
  have e2 (σ : VExpr.Subst) :
      iotaMs d c (etaRepl d T.name (d.recLevels.map (·.inst ls)) j c σ) = iotaMs d c σ :=
    iotaRhs_consList_vals _ _ σ (hpl σ)
  have e3 (σ : VExpr.Subst) :
      iotaFs c (etaRepl d T.name (d.recLevels.map (·.inst ls)) j c σ) =
        VExpr.projs T.name c.fields.length (iotaMajor d (d.recLevels.map (·.inst ls)) j c σ) :=
    iota_fields_consList σ (hpl σ)
  apply iotaRule_adeq_repl henvW hM hEE hE₂le hEo hE₂o hX hX₂ hΓ₀ IH hdf₂ hB hΓ hls hlen _ _
    rfl rfl (etaRepl d T.name (d.recLevels.map (·.inst ls)) j c)
  · intro σ i hi
    obtain ⟨j', rfl⟩ : ∃ j', i = j' + c.fields.length := ⟨i - c.fields.length, by omega⟩
    have := Subst.consList_ge (σ.drop c.fields.length) (VExpr.projs T.name c.fields.length
      (iotaMajor d (d.recLevels.map (·.inst ls)) j c σ)) j'
    rw [hpl] at this; unfold etaRepl; rw [this]; rfl
  · intro σ ρ W
    rw [iota_vals, e1, e2, e3, iotaL_eq_args, subst_appN, iotaArgs_subst]
    simp only [iotaIdx, hcI, List.map_nil, List.append_nil]
    rw [Step.appN_snoc]
    exact .single (Step.etaIota hsT hT hTc hq hPA hER (length_iotaPs d c σ) (length_iotaMs d c σ))
  · intro σ ρ W i hi
    have W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
        ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ) :=
      hGΔ ▸ W.toSubstEq hΓ₀
    obtain ⟨k, hik⟩ : ∃ k, i + k + 1 = c.fields.length := ⟨c.fields.length - 1 - i, by
      simp [length_iotaBinders] at hi; omega⟩
    have hkf : k < c.fields.length := by omega
    have hcl := hk.field hsT hq (List.getElem?_eq_getElem hkf)
    have hFi : etaRepl d T.name (d.recLevels.map (·.inst ls)) j c σ i =
        .proj T.name k ((VExpr.const c.name (d.recLevels.map (·.inst ls))).appN
          (iotaPs d c σ ++ iotaFs c σ)) := by
      unfold etaRepl
      rw [Subst.consList_lt _ _ _ (by rw [hpl]; omega), List.getElem_reverse, ← hmaj]
      simp only [VExpr.projs, List.getElem_map, List.getElem_range]
      congr 1; simp only [List.length_map, List.length_range]; omega
    have hσi : σ i = (iotaFs c σ)[k]'(by simp [length_iotaFs]; omega) := by
      rw [iotaFs_getElem c σ hkf]; congr 1; omega
    have hTτ : ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
        (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i].subst
        ((etaRepl d T.name (d.recLevels.map (·.inst ls)) j c σ).drop (i+1)) =
        (c.fields[k].type.instL (d.recLevels.map (·.inst ls))).subst (Subst.id.consList
          (iotaPs d c σ ++ VExpr.projs T.name k ((VExpr.const c.name
            (d.recLevels.map (·.inst ls))).appN (iotaPs d c σ ++ iotaFs c σ)))) := by
      rw [iota_field_subst d _ _ c hik hcl _ hi]
      rw [← hmaj, ← VEnv.projs_take' T.name _ (Nat.le_of_lt hkf), ← e1 σ, ← e3 σ]; rfl
    have R := Hproj W0 k hkf
    constructor
    · rintro - -
      rw [hFi, hσi, hTτ]; exact R.2
    · intro n m a x _ _ hx H
      rw [hFi, hTτ]; rw [hσi, hTτ] at H hx
      exact ((LR _ _ _).whr R (TRed.refl hx.hasType.2)).2 H

end

/-- A block's iota rules for a structure with eta. -/
theorem iotaEtaCase : IotaEtaCase := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
    envT envC envR h1 h2 h3 IHR Γ q j c ls hΓ hq hls hlen' hLE hPA hER
  letI := env.shapeEnv; letI := X
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  have hEW : E.WF := ⟨_, hW⟩
  have hDc := hD
  cases hDc with
  | induct hd hg hadd =>
  have hadd' := hadd
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd'
  obtain ⟨envT', hT', envC', hC', envR', hR', hB'⟩ := hadd'
  cases h1.symm.trans hT'; cases h2.symm.trans hC'; cases h3.symm.trans hR'
  have hle : E' ≤ env := hext.le
  have HB : VEnv.BlockEnvs env d E envT envC envR := ⟨hEW, hd, hg, h1, h2, h3, ⟨E', hB', hle⟩⟩
  have hWR := HB.envR_wf
  have hOR := hWR.ordered
  have hE'W : E'.WF := ⟨_, .decl hD hW⟩
  have hDle : E ≤ E' := hD.le
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hDle (hdom c h)
  have hle₁ : E ≤ env := hDle.trans hle
  have hX₁ : SoundHyps E env := soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX)
    hW hle₁ (fun hdf e hx => VEnv.WF.rule_head hEW hdf e (hdomE _ hx))
    (VEnv.WF.noDomI hEW hdomE)
  have hXR : SoundHyps envR env :=
    hX₁.mono (fun h => HB.envR_defeqs ▸ h) (fun h => HB.envR_inducts ▸ h)
  have hX₂ : SoundHyps E' env := soundHyps_of hMX (quotRuleSound hMX henvW)
    (henvW.blockSound hMX) (.decl hD hW) hle
    (fun hdf e hx => VEnv.WF.rule_head hE'W hdf e (hdom _ hx)) (VEnv.WF.noDomI hE'W hdom)
  have hRE' : envR ≤ E' := VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB')
  have hmem : d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c ∈
      d.iotaRules := by
    simp only [VInductDecl.iotaRules, List.mem_map]
    exact ⟨((j, c), q), List.mk_mem_zipIdx_iff_getElem?.2 hq, rfl⟩
  have hdf₂ : E'.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c) := by
    rw [VEnv.addBlock_defeqs hB']; exact VEnv.addDefEqList_defeqs_of_mem hmem
  obtain ⟨T0, hT0⟩ : ∃ T0, d.types[0]? = some T0 := by
    cases e : d.types with
    | nil => exact (hd.nonempty e).elim
    | cons T _ => exact ⟨T, rfl⟩
  have hs0 : env.inducts T0.name = some (d, 0) := hle.inducts (addBlock_inducts_head hB' hT0)
  obtain ⟨Tj, hj, hcm⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
  have hcW := (hd.ctors envT h1 Tj (List.mem_of_getElem? hj)).2 c hcm
  have hIR := (hR envT envC envR h1 h2 h3).2.2
  have hdfR := (hg envT envC envR h1 h2 h3).2 _ hmem
  have hB := VEnv.VDefEq.WF.bodyWF hOR hIR hdfR rfl rfl rfl
  have hrecR : envR.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩ :=
    VEnv.addConstList_constants_of_mem h3
      (List.mem_map.2 ⟨(Tj, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩)
  obtain ⟨T, c', hT, hTc, hTi, -, -, -⟩ := id hER
  obtain rfl : T = Tj := Option.some.inj ((VInductDecl.allTypes_getElem? hT).symm.trans hj)
  obtain rfl : c' = c := by rw [hTc] at hcm; simpa [eq_comm] using hcm
  have hsT := henvW.inducts_getElem hs0 hT
  have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c').lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c').rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c').type.instL ls) :=
    iotaRule_adeq_eta henvW hMX hRE' hle hOR hE'W.ordered hXR hX₂ hΓ₀ IHR hIR henvW.kClosed hsT hT
      hTc hq (hd.types _ (List.mem_of_getElem? hT)).2 hTi hcW.indices.1
      (VEnv.WF.projFacts henvW hsT hT hTc) hrecR hdf₂ hB hΓ hls hlen' hPA hER
  exact @key

/-- A block's iota rules. -/
theorem indIotaCase : IndIotaCase := IndIotaCase.of iotaKCase iotaEtaCase

end LogRel
end Lean4Lean

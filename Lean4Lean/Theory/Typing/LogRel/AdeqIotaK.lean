import Lean4Lean.Theory.Typing.LogRel.IotaFields

/-!
# An iota rule at a proposition with large elimination

There the left body computes by the K-like step, on the constructor application itself, to the
right body at fields the context provides (`kFieldsOf`): the fields that are indices are the
substitution's own, read off the indices, and the others are proofs, whose values are `bot`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- A substitution is its values for the first `n` variables over the rest. -/
theorem subst_eq_consList_drop (σ : VExpr.Subst) (n : Nat) :
    σ = (σ.drop n).consList ((VExpr.bvars n 0).map (·.subst σ)) := by
  funext i
  by_cases hi : i < n
  · rw [Subst.consList_lt _ _ _ (by simpa using hi)]
    simp only [List.getElem_reverse, List.getElem_map, List.length_map]
    rw [getElem_bvars (by simp; omega)]
    simp only [VExpr.subst_bvar]
    congr 1; simp; omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
    have := Subst.consList_ge (σ.drop n) ((VExpr.bvars n 0).map (·.subst σ)) j
    simp only [List.length_map, VExpr.length_bvars] at this
    rw [this]; rfl

/-- A term closed below a list's length substitutes alike over any base. -/
theorem ClosedN.subst_consList_base {e : VExpr} {as : List VExpr} (he : e.ClosedN as.length)
    (σ τ : VExpr.Subst) : e.subst (σ.consList as) = e.subst (τ.consList as) :=
  he.subst_congr fun i hi => by rw [Subst.consList_lt _ _ _ hi, Subst.consList_lt _ _ _ hi]

/-- Related substitutions of a context's top binders: the `i`th value, at its binder's type under
the values below it, and the substitutions below it. -/
theorem _root_.Lean4Lean.VEnv.Ctx.SubstEq.dropHead {Γ₀ : List VExpr} :
    ∀ {Gs Δ : List VExpr} {σ σ' : VExpr.Subst} {i : Nat},
    VEnv.Ctx.SubstEq env U Γ₀ σ σ' (Gs ++ Δ) → (h : i < Gs.length) →
    env.IsDefEq U Γ₀ (σ i) (σ' i) (Gs[i].subst (σ.drop (i+1))) ∧
    VEnv.Ctx.SubstEq env U Γ₀ (σ.drop (i+1)) (σ'.drop (i+1)) (Gs.drop (i+1) ++ Δ)
  | _ :: _, _, _, _, 0, W, _ => by cases W with | cons W' _ hh => exact ⟨hh, W'⟩
  | _ :: Gs, _, _, _, i+1, W, h => by
    cases W with | cons W' _ _ =>
    exact VEnv.Ctx.SubstEq.dropHead (Gs := Gs) W' (by simpa using h)

section
variable [ShapeEnv] [AxInterp] {Γ₀ : List VExpr}

/-- A valuation fitting a context, at one of its top binders: `bot`, or a value of a type
interpreting the binder's type over a valuation fitting the context below it. -/
theorem _root_.Lean4Lean.LogRel.LE_Interp.Valuation.Fits.dropHead :
    ∀ {Gs Δ : List VExpr} {ρ : Valuation} {i : Nat},
    LE_Interp.Valuation.Fits env Γ₀ (Gs ++ Δ) ρ → (h : i < Gs.length) →
    ρ i = Valuation.nil i ∨ ∃ ρ' a, LE_Interp.Valuation.Fits env Γ₀ (Gs.drop (i+1) ++ Δ) ρ' ∧
      LE_Interp env ρ' a Gs[i] ∧ (ρ i).HasType a
  | _ :: _, _, _, 0, W, _ => by
    cases W with
    | nil => exact .inl rfl
    | cons W' _ h2 h3 => exact .inr ⟨_, _, W', h2, h3⟩
  | _ :: Gs, _, _, i+1, W, h => by
    cases W with
    | nil => exact .inl rfl
    | cons W' _ _ _ => exact LE_Interp.Valuation.Fits.dropHead (Gs := Gs) W' (by simpa using h)

/-- A top binder whose type is a proposition has `bot` as its value. -/
theorem _root_.Lean4Lean.LogRel.LE_Interp.Valuation.Fits.proof_bot {Gs Δ : List VExpr}
    {ρ : Valuation} {i : Nat} (W : LE_Interp.Valuation.Fits env Γ₀ (Gs ++ Δ) ρ)
    (h : i < Gs.length) (hS : SoundTy env (Gs.drop (i+1) ++ Δ) Gs[i] (.sort .zero)) :
    ρ i ≤ TShape.bot := by
  rcases W.dropHead h with e | ⟨ρ', a, W', h2, h3⟩
  · rw [e]; exact TShape.bot_le
  · obtain ⟨_, _, b1, -, b3, b4⟩ := hS W' h2
    have b4' := TShape.HasType.mono_r (by simpa [levelRel_zero] using b3.le_sort) .sort b4
    exact b4'.proofIrrel (b4'.mono_r b1 h3)

end

/-! ### The substitution's values for an iota rule's binders -/

/-- The parameters' values. -/
def iotaPs (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) : List VExpr :=
  (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
    (·.subst σ)

/-- The motives' and minor premises' values. -/
def iotaMs (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) : List VExpr :=
  (VExpr.bvars (d.allTypes.length + d.allCtors.length) c.fields.length).map (·.subst σ)

/-- The fields' values. -/
def iotaFs (c : VConstructor) (σ : VExpr.Subst) : List VExpr :=
  (VExpr.bvars c.fields.length 0).map (·.subst σ)

/-- The constructor's indices at the values. -/
def iotaIdx (d : VInductDecl) (lsB : List VLevel) (c : VConstructor) (σ : VExpr.Subst) :
    List VExpr :=
  (c.indices.map fun e => (e.instL lsB).reseat (d.allTypes.length + d.allCtors.length)
    c.fields.length c.fields.length 0 0).map (·.subst σ)

theorem iota_vals_N (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) :
    (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length).map
      (·.subst σ) = iotaPs d c σ ++ iotaMs d c σ := by
  rw [iotaPs, iotaMs, ← List.map_append, show d.params.length + d.allTypes.length +
    d.allCtors.length = d.params.length + (d.allTypes.length + d.allCtors.length) by omega,
    ← bvars_append']

theorem iota_vals (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) :
    (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length)
      0).map (·.subst σ) = iotaPs d c σ ++ iotaMs d c σ ++ iotaFs c σ := by
  rw [← iota_vals_N, iotaFs, ← List.map_append, ← bvars_append', Nat.add_zero]

theorem length_iotaPs (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) :
    (iotaPs d c σ).length = d.params.length := by simp [iotaPs]
theorem length_iotaMs (d : VInductDecl) (c : VConstructor) (σ : VExpr.Subst) :
    (iotaMs d c σ).length = d.allTypes.length + d.allCtors.length := by simp [iotaMs]
theorem length_iotaFs (c : VConstructor) (σ : VExpr.Subst) :
    (iotaFs c σ).length = c.fields.length := by simp [iotaFs]
theorem length_iotaIdx (d : VInductDecl) (lsB : List VLevel) (c : VConstructor)
    (σ : VExpr.Subst) : (iotaIdx d lsB c σ).length = c.indices.length := by simp [iotaIdx]

theorem iotaArgs_subst (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor)
    (σ : VExpr.Subst) :
    (iotaArgs d lsB j c).map (·.subst σ) = iotaPs d c σ ++ iotaMs d c σ ++ iotaIdx d lsB c σ ++
      [(d.ctorAppAt j c lsB (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + c.fields.length))
        (VExpr.bvars c.fields.length 0)).subst σ] := by
  simp only [iotaArgs, List.map_append, iota_vals_N, iotaIdx, List.map_cons, List.map_nil]

/-- The `k`th field's value is the substitution's at its variable. -/
theorem iotaFs_getElem (c : VConstructor) (σ : VExpr.Subst) {k : Nat}
    (hk : k < c.fields.length) :
    (iotaFs c σ)[k]'(by simp [iotaFs]; exact hk) = σ (c.fields.length - 1 - k) := by
  simp only [iotaFs, List.getElem_map]
  rw [getElem_bvars (by simpa using hk)]
  simp

/-- The constructor's indices at the parameters' and fields' values are the reseated indices at
the substitution. -/
theorem idxAt_iota (hk : KClosed env) {s : Name} {d : VInductDecl} {t q j : Nat}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (hq : d.allCtors[q]? = some (j, c))
    (lsB : List VLevel) (σ : VExpr.Subst) :
    VInductDecl.idxAt c lsB (iotaPs d c σ) (iotaFs c σ) = iotaIdx d lsB c σ := by
  simp only [VInductDecl.idxAt, iotaIdx, List.map_map]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp_apply]
  have hcl : (e.instL lsB).ClosedN (iotaPs d c σ ++ iotaFs c σ).length := by
    simpa [length_iotaPs, length_iotaFs] using (hk.ctorIdx hs hq he).instL (ls := lsB)
  conv => rhs; rw [subst_eq_consList_drop σ
    (d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length), iota_vals]
  rw [VExpr.reseat_subst_consList _ _ (length_iotaMs d c σ) (length_iotaFs c σ)]
  exact ClosedN.subst_consList_base hcl _ _

theorem getElem_of_getElem?' {α} {l : List α} {i : Nat} (h : i < l.length) {a : α}
    (e : l[i]? = some a) : l[i] = a := by
  rw [List.getElem?_eq_getElem h] at e; exact Option.some.inj e

/-- A recursor's telescope at an index: the type's index, past the motives and minor premises. -/
theorem recTele_index (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (Tj : VInductiveType)
    {i : Nat} (hi : i < Tj.indices.length) :
    (d.recTele lsB v Tj)[d.params.length + d.allTypes.length + d.allCtors.length + i]? =
      some ((Tj.indices[i].instL lsB).liftN (d.allTypes.length + d.allCtors.length) i) := by
  have hb : (d.recBinders lsB v).length = d.params.length + d.allTypes.length +
      d.allCtors.length := by
    simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega
  simp only [VInductDecl.recTele]
  rw [List.getElem?_append_left (by simp [hb]; omega), List.getElem?_append_right (by omega), hb,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem (by simpa using hi), VExpr.getElem_liftTele]
  simp

/-- The index arguments of the left body, at the substitution. -/
theorem iotaArgs_index (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor)
    (σ : VExpr.Subst) {i : Nat} (hi : i < c.indices.length) :
    ((iotaArgs d lsB j c).map (·.subst σ))[d.params.length + d.allTypes.length +
      d.allCtors.length + i]? = (iotaIdx d lsB c σ)[i]? ∧
    ((iotaArgs d lsB j c).map (·.subst σ)).take (d.params.length + d.allTypes.length +
      d.allCtors.length + i) = iotaPs d c σ ++ iotaMs d c σ ++ (iotaIdx d lsB c σ).take i := by
  rw [iotaArgs_subst]
  have hl : (iotaPs d c σ ++ iotaMs d c σ).length =
      d.params.length + d.allTypes.length + d.allCtors.length := by
    simp [length_iotaPs, length_iotaMs]; omega
  constructor
  · rw [List.getElem?_append_left (by simp [length_iotaPs, length_iotaMs, length_iotaIdx]; omega), ← hl,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  · rw [List.append_assoc (iotaPs d c σ ++ iotaMs d c σ), ← hl, List.take_length_add_append,
      List.take_append_of_le_length (by simp [length_iotaIdx]; omega)]

section
variable [ShapeEnv] {E : VEnv} {Γ₀ : List VExpr}

/-- The substitution's own fields are fields for the K-like step: the iota rule's left body is
typed, so the constructor's indices at them are typed along the type's indices. -/
theorem kfields_own (hI : E.Inj) (hEo : E.Ordered) (hle : E ≤ env) (henv : env.Ordered)
    (hk : KClosed env) {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hs : env.inducts s = some (d, t)) (hq : d.allCtors[q]? = some (j, c))
    (hcidx : c.indices.length = Tj.indices.length)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.recUVars)
    (hrec : E.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    (hon : OnCtx (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
      (E.IsType U)) {A : VExpr}
    (hL : E.HasType U (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
      (iotaL d (d.recLevels.map (·.inst ls)) ls j c) A)
    {Γ : List VExpr} {σ : VExpr.Subst} (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ)) :
    KFields env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
      (iotaIdx d (d.recLevels.map (·.inst ls)) c σ) (iotaFs c σ) := by
  have hBl := length_iotaBinders d (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c
  refine ⟨fun k i hk hi => ?_, fun k h h' => ?_, fun i h h' h'' => ?_⟩
  · rw [List.getElem?_eq_getElem (by simp [iotaFs]; exact hk), iotaFs_getElem c σ hk, iotaIdx,
      List.getElem?_map, iotaIdx_spec hk hi]; rfl
  · have hGΔ : (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ =
        ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
          (d.params.length + d.allTypes.length + d.allCtors.length)).reverse ++
        (((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).take
          (d.params.length + d.allTypes.length + d.allCtors.length)).reverse ++ Γ) := by
      rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]
    have W' := hGΔ ▸ W
    have hi : c.fields.length - 1 - k < ((d.iotaBinders (d.recLevels.map (·.inst ls))
        (d.motiveLevel.inst ls) c).drop
        (d.params.length + d.allTypes.length + d.allCtors.length)).reverse.length := by
      simp; omega
    obtain ⟨h1, -⟩ := W'.dropHead hi
    rw [iota_field_subst d _ _ c (i := c.fields.length - 1 - k) (k := k) (by omega)
      (by simpa using hk.field hs hq (List.getElem?_eq_getElem h')) σ hi] at h1
    rw [iotaFs_getElem c σ h']
    exact h1
  · have hi'' : i < c.indices.length := hcidx ▸ h''
    simp only [idxAt_iota hk hs hq]
    obtain ⟨e1, e2⟩ := iotaArgs_index d (d.recLevels.map (·.inst ls)) j c σ hi''
    have H := iotaL_arg_typed hI hEo hle henv hls hlen hrec hcidx hon hL hΓ₀ W
      (d.params.length + d.allTypes.length + d.allCtors.length + i)
      (by rw [length_iotaArgs]; omega) (by rw [length_recTele]; omega)
    rw [List.map_take, e2, getElem_of_getElem?' _ (recTele_index d _ _ Tj h''),
      VExpr.liftN_subst_consList_mid _ _ (length_iotaMs d c σ)
        (by simp [length_iotaIdx]; omega)] at H
    have e3 : ((iotaArgs d (d.recLevels.map (·.inst ls)) j c)[d.params.length +
        d.allTypes.length + d.allCtors.length + i]'(by rw [length_iotaArgs]; omega)).subst σ =
        (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)[i]'(by simp [length_iotaIdx]; omega) := by
      rw [← List.getElem_map (f := fun x : VExpr => x.subst σ)]
      exact getElem_of_getElem?' (by simp [length_iotaArgs]; omega)
        (e1.trans (List.getElem?_eq_getElem _))
    rw [e3] at H
    exact H
end

/-- An iota rule's context, split at its fields: the binders below the `i`th field (counting from
the top) and its binder. -/
theorem iota_top_split (Bs Γ : List VExpr) (N : Nat) (hN : N ≤ Bs.length) {i k : Nat}
    (hi : i < (Bs.drop N).reverse.length) (hk : i + k + 1 = (Bs.drop N).length) :
    (Bs.drop N).reverse.drop (i+1) ++ ((Bs.take N).reverse ++ Γ) =
      (Bs.take (N + k)).reverse ++ Γ ∧
    (Bs.drop N).reverse[i] = Bs[N + k]'(by simp at hk; omega) := by
  constructor
  · rw [List.drop_reverse, ← List.append_assoc, ← List.reverse_append, ← List.take_add]
    congr 3; simp only [List.length_drop] at hk ⊢; omega
  · rw [List.getElem_reverse, List.getElem_drop]
    congr 1; simp only [List.length_drop] at hk ⊢; omega

theorem iotaRhs_consList_vals (nTC nf : Nat) (σ : VExpr.Subst) {G : List VExpr}
    (hG : G.length = nf) :
    (VExpr.bvars nTC nf).map (·.subst ((σ.drop nf).consList G)) =
      (VExpr.bvars nTC nf).map (·.subst σ) := by
  have := iota_params_consList nTC 0 nf σ hG
  simpa using this

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- The K-like step's replacement of a substitution's fields: by `kFieldsOf`, when it gives
fields. -/
noncomputable def kRepl (env : VEnv) (U : Nat) (Γ₀ : List VExpr) (d : VInductDecl)
    (Tj : VInductiveType) (c : VConstructor) (lsB : List VLevel) (σ : VExpr.Subst) : VExpr.Subst :=
  if (kFieldsOf env U Γ₀ Tj c lsB (iotaPs d c σ) (iotaIdx d lsB c σ)).length = c.fields.length then
    (σ.drop c.fields.length).consList (kFieldsOf env U Γ₀ Tj c lsB (iotaPs d c σ) (iotaIdx d lsB c σ))
  else σ

/-- An iota rule at a proposition with large elimination is related where its sides are
interpreted: its left body computes by the K-like step to the right body at the fields
`kFieldsOf` chooses, which are the substitution's own where they are indices, and proofs
otherwise. -/
theorem iotaRule_adeq_K (henvW : env.WF) (hM : ModelEnv env) {E E₂ : VEnv} (hEE : E ≤ E₂)
    (hE₂le : E₂ ≤ env) (hEo : E.Ordered) (hE₂o : E₂.Ordered)
    (hX : SoundHyps E env) (hX₂ : SoundHyps E₂ env)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    (hI : E.Inj) (hk : KClosed env)
    {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor} {Tj : VInductiveType}
    (hs : env.inducts s = some (d, t)) (hq : d.allCtors[q]? = some (j, c))
    (hj : d.allTypes[j]? = some Tj) (hTc : Tj.ctors = [c])
    (hcidx : c.indices.length = Tj.indices.length)
    (hrec : E.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    (hdf₂ : E₂.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c))
    {L₀ R₀ A₀ : VExpr}
    (hB : (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).BodyWF E
      (d.iotaBinders d.recLevels d.motiveLevel c) L₀ R₀ A₀)
    {Γ : List VExpr} {ls : List VLevel} (hΓ : OnCtx Γ (env.IsType U)) (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.recUVars)
    (hPA : d.PropAt (d.blockLevels ls)) (hlarge : d.largeElim = true)
    (hprop : ∀ k (hk : k < c.fields.length), VInductDecl.fieldIdx c k = none →
      E.HasType U ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).take
        (d.params.length + d.allTypes.length + d.allCtors.length + k)).reverse
        ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c)[d.params.length +
          d.allTypes.length + d.allCtors.length + k]'(by rw [length_iotaBinders]; omega))
        (.sort .zero)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).type.instL ls) := by
  have hEenv : E ≤ env := hEE.trans hE₂le
  have hS : ∀ {Γ M N A}, E.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => hX.strongSound hM hEenv D
  -- the rule's binders and left body at the levels
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
  have hBl : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length +
      c.fields.length := by rw [← hBs, length_iotaBinders]
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
  -- the K-like step's fields, at a substitution of the binders
  have KW {σ σ' : VExpr.Subst} (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ' (Bs.reverse ++ Γ)) :
      KFields env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
        (iotaIdx d (d.recLevels.map (·.inst ls)) c σ) (iotaFs c σ) ∧
      (kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
        (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)).length = c.fields.length ∧
      KFields env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
        (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)
        (kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
          (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)) := by
    subst hBs
    have KO := kfields_own hI hEo hEenv henvW.ordered hk hs hq hcidx hls hlen hrec
      hon hLt hΓ₀ W.left
    exact ⟨KO, kFieldsOf_spec (length_iotaFs c σ) KO⟩
  subst hBs
  apply iotaRule_adeq_repl henvW hM hEE hE₂le hEo hE₂o hX hX₂ hΓ₀ IH hdf₂ hB hΓ hls hlen _ _
    rfl rfl (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)))
  · intro σ i hi
    unfold kRepl
    split
    · next hkl =>
      obtain ⟨j', rfl⟩ : ∃ j', i = j' + c.fields.length := ⟨i - c.fields.length, by omega⟩
      have := Subst.consList_ge (σ.drop c.fields.length) (kFieldsOf env U Γ₀ Tj c
        (d.recLevels.map (·.inst ls)) (iotaPs d c σ) (iotaIdx d (d.recLevels.map (·.inst ls)) c σ))
        j'
      rw [hkl] at this; rw [this]; rfl
    · rfl
  · intro σ ρ W
    have W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
        ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ) :=
      hGΔ ▸ W.toSubstEq hΓ₀
    obtain ⟨-, hkl, KK⟩ := KW W0
    have eF : kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ =
        (σ.drop c.fields.length).consList (kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls))
          (iotaPs d c σ) (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)) := if_pos hkl
    have e1 : iotaPs d c (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ) = iotaPs d c σ := by
      rw [eF]; exact iota_params_consList _ _ _ σ hkl
    have e2 : iotaMs d c (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ) = iotaMs d c σ := by
      rw [eF]; exact iotaRhs_consList_vals _ _ σ hkl
    have e3 : iotaFs c (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ) =
        kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
          (iotaIdx d (d.recLevels.map (·.inst ls)) c σ) := by
      rw [eF]; exact iota_fields_consList σ hkl
    rw [iota_vals, e1, e2, e3, iotaL_eq_args, subst_appN, iotaArgs_subst, Step.appN_snoc]
    exact .single (Step.kIota hs hq hj hTc hPA hlarge (length_iotaPs d c σ) (length_iotaMs d c σ)
      (by rw [length_iotaIdx, hcidx]) hkl KK)
  · intro σ ρ W i hi
    have W0 : VEnv.Ctx.SubstEq env U Γ₀ σ σ
        ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse ++ Γ) :=
      hGΔ ▸ W.toSubstEq hΓ₀
    obtain ⟨KO, hkl, KK⟩ := KW W0
    have eF : kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ =
        (σ.drop c.fields.length).consList (kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls))
          (iotaPs d c σ) (iotaIdx d (d.recLevels.map (·.inst ls)) c σ)) := if_pos hkl
    have hGl : ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
        (d.params.length + d.allTypes.length + d.allCtors.length)).length = c.fields.length := by
      simp [length_iotaBinders]
    obtain ⟨k, hik⟩ : ∃ k, i + k + 1 = c.fields.length := ⟨c.fields.length - 1 - i, by
      simp [length_iotaBinders] at hi; omega⟩
    have hkf : k < c.fields.length := by omega
    have hcl := hk.field hs hq (List.getElem?_eq_getElem hkf)
    generalize hkfs : kFieldsOf env U Γ₀ Tj c (d.recLevels.map (·.inst ls)) (iotaPs d c σ)
      (iotaIdx d (d.recLevels.map (·.inst ls)) c σ) = kf at eF hkl KK
    have hFi : kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ i = kf[k]'(by omega) := by
      rw [eF, Subst.consList_lt _ _ _ (by omega), List.getElem_reverse]
      congr 1; omega
    have hσi : σ i = (iotaFs c σ)[k]'(by simp [iotaFs]; omega) := by
      rw [iotaFs_getElem c σ hkf]; congr 1; omega
    have hTτ : ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
        (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i].subst
        ((kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ).drop (i+1)) =
        (c.fields[k].type.instL (d.recLevels.map (·.inst ls))).subst
          (Subst.id.consList (iotaPs d c σ ++ kf.take k)) := by
      rw [iota_field_subst d _ _ c hik hcl _ hi]
      have e1 : iotaPs d c (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ) =
          iotaPs d c σ := by
        rw [eF]; exact iota_params_consList _ _ _ σ hkl
      have e3 : iotaFs c (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ) = kf := by
        rw [eF]; exact iota_fields_consList σ hkl
      rw [← e1, ← e3]; rfl
    have hσt := ((W.toSubstEq hΓ₀).dropHead hi).1
    by_cases hfi : VInductDecl.fieldIdx c k = none
    · -- a proof: `bot` in the model, and equal to any other by proof irrelevance
      have hN : d.params.length + d.allTypes.length + d.allCtors.length ≤
          (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).length := by
        rw [length_iotaBinders]; omega
      obtain ⟨e1s, e2s⟩ := iota_top_split _ Γ _ hN hi (by rw [hGl]; omega)
      have hpr := hprop k hkf hfi
      have hon' := (VEnv.IsTele.append_inv (by rw [List.take_append_drop]; exact teleE :
        E.IsTele U [] ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).take
          (d.params.length + d.allTypes.length + d.allCtors.length + k) ++
          (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
          (d.params.length + d.allTypes.length + d.allCtors.length + k)))).1.onCtx (Γ := []) trivial
      simp only [List.append_nil] at hon'
      have D := IsDefEq.weak_closed hEo hon' hpr Γ
      have hpr' : env.HasType U (((d.iotaBinders (d.recLevels.map (·.inst ls))
          (d.motiveLevel.inst ls) c).drop (d.params.length + d.allTypes.length +
          d.allCtors.length)).reverse.drop (i+1) ++ ((((d.iotaBinders (d.recLevels.map (·.inst ls))
          (d.motiveLevel.inst ls) c).take (d.params.length + d.allTypes.length +
          d.allCtors.length)).reverse ++ Γ)))
          ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
            (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i] (.sort .zero) := by
        rw [e1s, e2s]; exact D.defeq.mono hEenv
      have hSnd : SoundTy env (((d.iotaBinders (d.recLevels.map (·.inst ls))
          (d.motiveLevel.inst ls) c).drop (d.params.length + d.allTypes.length +
          d.allCtors.length)).reverse.drop (i+1) ++ ((((d.iotaBinders (d.recLevels.map (·.inst ls))
          (d.motiveLevel.inst ls) c).take (d.params.length + d.allTypes.length +
          d.allCtors.length)).reverse ++ Γ)))
          ((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
            (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i] (.sort .zero) := by
        rw [e1s, e2s]; exact (hS D).left.sound
      constructor
      · rintro hE ⟨u, hTeq⟩
        have hP := hpr'.subst henvW.ordered hE.left hΓ₀
        have hFt : env.HasType U Γ₀ (kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ i)
            (((d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).drop
            (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i].subst
            ((kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ).drop (i+1))) := by
          rw [hFi, hTτ]; exact KK.fields k (by omega) hkf
        exact .proofIrrel hP hFt (VEnv.IsDefEq.defeqDF hTeq.symm hσt)
      · intro n m a x hm hmem _ _
        have hb := W.fits.proof_bot hi hSnd
        cases show m = .bot from TShape.le_bot.1 (hm.trans hb)
        exact (LR _ _ _).bot hmem.isType
    · -- an index: the substitution's own value
      obtain ⟨idx, hidx⟩ := Option.ne_none_iff_exists'.1 hfi
      have hkk : kf[k]? = (iotaFs c σ)[k]? :=
        (KK.idx k idx hkf hidx).trans (KO.idx k idx hkf hidx).symm
      have hFσ : kRepl env U Γ₀ d Tj c (d.recLevels.map (·.inst ls)) σ i = σ i := by
        rw [hFi, hσi]
        exact getElem_of_getElem?' _ (hkk.trans (List.getElem?_eq_getElem _))
      constructor
      · rintro - ⟨u, hTeq⟩
        rw [hFσ]; exact VEnv.IsDefEq.defeqDF hTeq.symm hσt
      · intro n m a x _ _ _ H
        rw [hFσ]; exact H

end

/-- An iota rule's field binder is typed at the field's level, under the binders before it. -/
theorem iota_field_typed {E envT : VEnv} (hO : E.Ordered) (hTE : envT ≤ E) {d : VInductDecl}
    {Tj : VInductiveType} {c : VConstructor} (hcW : c.WF envT d Tj) {lsB : List VLevel}
    (v : VLevel) (hlsB : ∀ l ∈ lsB, l.WF U) {k : Nat} {f : VField} (hf : c.fields[k]? = some f) :
    E.HasType U ((d.iotaBinders lsB v c).take
      (d.params.length + d.allTypes.length + d.allCtors.length + k)).reverse
      ((d.iotaBinders lsB v c)[d.params.length + d.allTypes.length + d.allCtors.length + k]'(by
        have := (List.getElem?_eq_some_iff.1 hf).1; rw [length_iotaBinders]; omega))
      (.sort (f.level.inst lsB)) := by
  have hkf : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨-, Ds, -, -, hFW, -, -⟩ := hcW.shape
  have hft := FieldsWF.hasType_getElem hFW k f hf
  have hft' := (hft.instL hlsB).mono hTE
  simp only [List.map_append, List.map_reverse, VExpr.instL, List.map_map, Function.comp_def]
    at hft'
  have W := Ctx.LiftN.liftTele (n := d.allTypes.length + d.allCtors.length)
    ((c.fields.take k).map (·.type.instL lsB))
    (Ctx.LiftN.zero (Γ := (d.params.map (·.instL lsB)).reverse)
      (d.motiveTypes lsB v ++ d.minorTypes lsB).reverse
      (by simp only [List.length_reverse, List.length_append, VInductDecl.length_motiveTypes,
        VInductDecl.minorTypes, List.length_map, List.length_zipIdx]))
  have hft'' := hft'.weakN hO W
  simp only [Nat.zero_add, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hkf),
    VExpr.liftN] at hft''
  have hBs : (d.iotaBinders lsB v c).take (d.params.length + d.allTypes.length +
      d.allCtors.length + k) = d.params.map (·.instL lsB) ++ (d.motiveTypes lsB v ++
        d.minorTypes lsB) ++ VExpr.liftTele (d.allTypes.length + d.allCtors.length)
          ((c.fields.take k).map (·.type.instL lsB)) := by
    simp only [VInductDecl.iotaBinders, VInductDecl.recBinders]
    rw [List.take_append, List.take_of_length_le (by
      simp [VInductDecl.minorTypes]; omega), take_liftTele, ← List.map_take]
    simp only [VInductDecl.minorTypes, List.length_append, List.length_map,
      VInductDecl.length_motiveTypes, List.length_zipIdx, List.append_assoc]
    rw [show d.params.length + d.allTypes.length + d.allCtors.length + k -
      (d.params.length + (d.allTypes.length + d.allCtors.length)) = k by omega]
  rw [iotaBinders_field d lsB v c hkf, (List.getElem?_eq_some_iff.1 hf).2, hBs]
  simp only [List.reverse_append, List.append_assoc] at hft'' ⊢
  exact hft''

/-- A block's iota rules at levels where it is a proposition with large elimination. -/
theorem iotaKCase : IotaKCase := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
    envT envC envR h1 h2 h3 IHR Γ q j c ls hΓ hq hls hlen' hLE hPA
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
  have hleTR : envT ≤ envR := (VEnv.addConstList_le h2).trans (VEnv.addConstList_le h3)
  have hlsB : ∀ l ∈ d.recLevels.map (·.inst ls), l.WF U := by
    intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls
  rcases hd.largeElim hLE with hnz | ⟨T, hTs1, haux, hcs⟩
  · exfalso
    have := VLevel.equiv_def.1 hPA []
    rw [VLevel.eval_inst] at this
    exact hnz _ this
  have hjT : j = 0 ∧ Tj = T := by
    rw [VInductDecl.allTypes, hTs1, haux] at hj
    cases j with
    | zero => exact ⟨rfl, (Option.some.inj hj).symm⟩
    | succ j => simp at hj
  obtain ⟨rfl, rfl⟩ := hjT
  rcases hcs with hnil | ⟨c', hc1, hfl⟩
  · rw [hnil] at hcm; cases hcm
  obtain rfl : c' = c := by rw [hc1] at hcm; simpa [eq_comm] using hcm
  have key : @AdeqStmt env U _ X henvW.ordered henvW.stepUniq Γ₀ Γ
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q 0 c').lhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q 0 c').rhs.instL ls)
      ((d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q 0 c').type.instL ls) := by
    refine iotaRule_adeq_K henvW hMX hRE' hle hOR hE'W.ordered hXR hX₂ hΓ₀ IHR hIR
      henvW.kClosed hs0 hq hj hc1 hcW.indices.1 hrecR hdf₂ hB hΓ hls hlen' hPA hLE
      fun k hk hk' => ?_
    obtain ⟨f, hf⟩ : ∃ f, c'.fields[k]? = some f := ⟨_, List.getElem?_eq_getElem hk⟩
    have hf0 : f.level.inst (d.recLevels.map (·.inst ls)) ≈ .zero := by
      by_cases h0 : f.level ≈ .zero
      · exact VLevel.inst_congr_l h0
      · have hm := hfl k f hf h0
        rw [VInductDecl.fieldIdx, List.findIdx?_eq_none_iff] at hk'
        exact absurd (hk' _ hm) (by simp [VExpr.isBVar])
    exact .defeqDF (.sortDF (VLevel.WF.inst hlsB) trivial hf0)
      (iota_field_typed hOR hleTR hcW _ hlsB hf)
  exact @key

end LogRel
end Lean4Lean

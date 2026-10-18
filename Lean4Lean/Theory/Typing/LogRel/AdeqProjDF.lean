import Lean4Lean.Theory.Typing.LogRel.IndHYOf
import Lean4Lean.Theory.Typing.LogRel.AdeqProj

/-!
# Adequacy at a projection of a new block's structure-like type

Pieces of the `projDF` and `projEta` cases for the types an inductive block adds: the type former
applied to arguments related along its telescope, and a projection of a value that reduces to a
constructor application, as a typed reduction to the field.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

section
variable {env : VEnv} {U : Nat}

/-- A type former whose declared type is definitionally a pi telescope over its parameters and
indices, applied at equivalent levels to arguments equal along that telescope: the applications
are equal at the block's sort. -/
theorem typeFormer_appN_congr (henv : env.Ordered) {Γ : List VExpr} {s : Name} {d : VInductDecl} {T : VInductiveType}
    (hci : env.constants s = some ⟨d.uvars, T.type⟩) {w : VLevel}
    (hdef : env.IsDefEq d.uvars [] T.type (.foralls (d.params ++ T.indices) (.sort d.level))
      (.sort w))
    {ls₁ ls₂ : List VLevel} (hl₁ : ∀ l ∈ ls₁, l.WF U) (hl₂ : ∀ l ∈ ls₂, l.WF U)
    (hlen : ls₁.length = d.uvars) (heq : List.Forall₂ (· ≈ ·) ls₁ ls₂)
    {X Y : List VExpr} (hX : X.length = (d.params ++ T.indices).length)
    (hY : Y.length = (d.params ++ T.indices).length)
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList X) (Subst.dflt.consList Y)
      ((d.params ++ T.indices).map (·.instL ls₁)).reverse) :
    env.IsDefEq U Γ ((VExpr.const s ls₁).appN X) ((VExpr.const s ls₂).appN Y)
      (.sort (d.level.inst ls₁)) := by
  have hc : env.IsDefEq U Γ (.const s ls₁) (.const s ls₂) (T.type.instL ls₁) :=
    .constDF hci hl₁ hl₂ hlen heq
  have hcl := (hdef.closedN' henv.closed trivial)
  have hd1 := hdef.instL (ls := ls₁) hl₁
  have hd2 : env.IsDefEq U Γ (T.type.instL ls₁)
      ((VExpr.foralls (d.params ++ T.indices) (.sort d.level)).instL ls₁) (.sort (w.inst ls₁)) := by
    have := (IsDefEq.weak_closed henv (Δ := []) trivial (by simpa using hd1) Γ).defeq
    simpa [VExpr.instL] using this
  have hf := VEnv.IsDefEq.defeqDF hd2 hc
  rw [VEnv.foralls_instL'] at hf
  have hf' : env.IsDefEq U Γ (.const s ls₁) (.const s ls₂)
      ((VExpr.foralls ((d.params ++ T.indices).map (·.instL ls₁))
        (VExpr.instL ls₁ (.sort d.level))).subst Subst.dflt) := by
    rw [VExpr.ClosedN.subst_eq (k := 0) ?_ .zero]; · exact hf
    have := hcl.2.1.instL (ls := ls₁)
    rwa [VEnv.foralls_instL'] at this
  have := VEnv.IsDefEq.appN_substTDF (Δ := []) hf' (by simpa using hX) (by simpa using hY)
    (by simpa using W)
  simpa [VExpr.instL, VExpr.subst] using this

end

/-- A block's step records the block's types and the earlier blocks, nothing else. -/
theorem induct_inducts_cases {E E' : VEnv} {d : VInductDecl} (hD : VDecl.WF E (.induct d) E')
    {s : Name} {b : VInductDecl × Nat} (h : E'.inducts s = some b) :
    E.inducts s = some b ∨ b.1 = d ∧ ∃ T, d.types[b.2]? = some T ∧ T.name = s := by
  cases hD with
  | induct _ _ hadd =>
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨E₁, h1, E₂, h2, E₃, h3, h4⟩ := hadd
  rcases VEnv.addBlock_inducts h4 h with h | h
  · left
    rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts h3, VEnv.addConstList_inducts h2,
      VEnv.addConstList_inducts h1] at h
    exact h
  · exact .inr h

/-- `E'` with only the blocks `E` does not have. -/
def newBlockEnv (E E' : VEnv) : VEnv :=
  { E' with inducts := fun s => if E.inducts s = none then E'.inducts s else none }

section
variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- The `projDF` case at one block's own types. -/
def ProjDFAt (B : VEnv) (Γ₀ : List VExpr) : Prop :=
  ∀ {Γ s d t T c k f ls As I As' I' e e' u}, OnCtx Γ (env.IsType U) →
    B.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length → I.length = T.indices.length →
    As'.length = d.params.length → I'.length = T.indices.length →
    u.WF U → (f.level.inst ls).WF U → d.ProjAllowed c ls k →
    env.IsDefEqStrong U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u) →
    env.IsDefEqStrong U Γ e e' (.appN (.const s ls) (As ++ I)) →
    env.IsDefEqStrong U Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const s ls) (As ++ I))
      (.appN (.const s ls) (As' ++ I')) (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e e' (.appN (.const s ls) (As ++ I)) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    StrongSoundEq env U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As' ++ I'))
      (.sort u) →
    StrongSoundEq env U Γ (c.projType ls s k As e) (c.projType ls s k As' e')
      (.sort (f.level.inst ls)) →
    StrongSoundEq env U Γ e e' (.appN (.const s ls) (As ++ I)) →
    StrongSoundEq env U Γ (.proj s k e) (.proj s k e') (c.projType ls s k As e) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.proj s k e) (.proj s k e') (c.projType ls s k As e)

/-- The `projEta` case at one block's own types. -/
def ProjEtaAt (B : VEnv) (Γ₀ : List VExpr) : Prop :=
  ∀ {Γ s d t T c ls As e u}, OnCtx Γ (env.IsType U) →
    B.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] → T.indices = [] →
    d.isRec = false → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length → (∀ k < c.fields.length, d.ProjAllowed c ls k) → u.WF U →
    env.IsDefEqStrong U Γ (.appN (.const s ls) As) (.appN (.const s ls) As) (.sort u) →
    env.IsDefEqStrong U Γ e e (.appN (.const s ls) As) →
    env.IsDefEqStrong U Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const s ls) As) (.appN (.const s ls) As) (.sort u) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e e (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    StrongSoundEq env U Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    AdeqStmt (U := U) henv hU Γ₀ Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As)

/-- A block's projection cases over the old constants and rules: the earlier blocks' from the
induction, `projIota` for every block, and `projDF`/`projEta` at the new block's types as given. -/
theorem AdequacyHyps.ofBlock {E E' : VEnv} {d : VInductDecl} (hD : VDecl.WF E (.induct d) E')
    (hle : E' ≤ env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    (HDF : ProjDFAt (U := U) (henv := henv) (hU := hU) (newBlockEnv E E') Γ₀)
    (HEta : ProjEtaAt (U := U) (henv := henv) (hU := hU) (newBlockEnv E E') Γ₀) :
    AdequacyHyps (U := U) henv hU { E' with constants := E.constants, defeqs := E.defeqs } Γ₀ where
  const := IH.const
  extra := IH.extra
  projDF {Γ s d t T c k f ls As I As' I' e e' u} hΓ h1 := by
    cases ho : E.inducts s with
    | some b =>
      have := hD.le.inducts ho
      rw [this] at h1; cases h1
      exact IH.projDF hΓ ho
    | none =>
      refine HDF hΓ ?_
      show (newBlockEnv E E').inducts s = _
      simp only [newBlockEnv]
      rw [if_pos ho]; exact h1
  projIota hΓ h1 h2 h3 h4 h5 _ _ h8 h9 _ _ _ _ _ _ hP _ _ _ _ iha hS :=
    AdeqStmt.projIota hΓ₀ hΓ (hle.inducts h1) h2 h3 h5 h8 h9 hP iha hS
  projEta {Γ s d t T c ls As e u} hΓ h1 := by
    cases ho : E.inducts s with
    | some b =>
      have := hD.le.inducts ho
      rw [this] at h1; cases h1
      exact IH.projEta hΓ ho
    | none =>
      refine HEta hΓ ?_
      show (newBlockEnv E E').inducts s = _
      simp only [newBlockEnv]
      rw [if_pos ho]; exact h1

end

/-- `projDF` at the types a block adds, in `IndStep`'s context. -/
def IndProjDFNew : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E E' _} =>
  @ProjDFAt env U env.shapeEnv X henvW.ordered henvW.stepUniq (newBlockEnv E E') Γ₀

/-- `projEta` at the types a block adds, in `IndStep`'s context. -/
def IndProjEtaNew : Prop := IndStepCtx fun {env} henvW {U Γ₀} X {E E' _} =>
  @ProjEtaAt env U env.shapeEnv X henvW.ordered henvW.stepUniq (newBlockEnv E E') Γ₀

/-- A block's projection cases, from `projDF` and `projEta` at the types it adds. -/
theorem IndProjCase.of (HDF : IndProjDFNew) (HEta : IndProjEtaNew) : IndProjCase := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
  letI := env.shapeEnv; letI := X
  exact AdequacyHyps.ofBlock hD hext.le hΓ₀ IH
    (HDF henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall)
    (HEta henvW hΓ₀ X hX hXD hW hI hR hD hext hdom IH IHall)

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- A projection of a stuck value of a structure-like type is stuck, at the projection's type. -/
theorem TNeRed.proj (henv : env.Ordered) (hU : StepUniq env) (hΓ : OnCtx Γ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor} {k : Nat}
    {f : VField} {ls : List VLevel} {As I : List VExpr} {u : VLevel} {M : VExpr}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (hF : VEnv.ProjFacts env d c) (h4 : c.fields[k]? = some f) (h5 : ∀ l ∈ ls, l.WF U)
    (h6 : ls.length = d.uvars) (h7 : As.length = d.params.length) (h8 : I.length = T.indices.length)
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (hT : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    (hP : d.ProjAllowed c ls k)
    (H : TNeRed env U Γ M (.appN (.const s ls) (As ++ I))) :
    TNeRed env U Γ (.proj s k M) (c.projType ls s k As M) := by
  obtain ⟨M₁, tM, wM, nM⟩ := H
  have hty := VEnv.projType_congr henv hΓ h1 h2 h3 hF h5 h6 h5
    (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) h7 h8 h7 h8 W hT tM.2 h4 hP
  exact ⟨_, TRed.proj h1 h2 h3 h4 h5 h6 h7 h8 hT.hasType.1 tM hP hty,
    Neutral.whnf_proj hU wM nM, .proj nM⟩

end

section
variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- A type's adequacy gives what the relation knows of its instances at any shape interpreting
it. -/
theorem AdeqStmt.tyInfo {Γ : List VExpr} {P P' : VExpr} {v : VLevel}
    (ihP : AdeqStmt (U := U) henv hU Γ₀ Γ P P' (.sort v))
    (hSP : StrongSound env U Γ P (.sort v)) (hv : v.WF U) {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {j : Nat} {b : WShape j}
    (hb : LE_Interp env ρ b.T P) (ht : b.HasType .type) :
    TyInfo env U Γ₀ henv hU j (P.subst σ) b := by
  obtain ⟨n', x', a', le_n, le_a, hx', ha', hty⟩ := (hSP.sound W.fits hb).out
  have H := ((ihP hx' ha' hty).1 W.left).1
  simp only [VExpr.subst] at H
  exact ⟨LR.toValTy le_n le_a ht ha' hty H,
    (LR.toTyTy le_n le_a ht ha' hty (TyEq.refl (.sort hv)) H).1⟩

end

section
variable {env : VEnv} {U : Nat} [ShapeEnv] {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- A projection of two values related at a structure-like type's constructor shape, at a type
`Q` the projection's types are equal to: given the cases where the values reduce to constructor
applications (`HC`) or are related extensionally (`HS`), the stuck case is reflection, and the
type cannot be stuck. -/
theorem projDF_core (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor} {k : Nat}
    {f : VField} {ls : List VLevel} {As I : List VExpr} {u : VLevel}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (hF : VEnv.ProjFacts env d c) (h4 : c.fields[k]? = some f) (h5 : ∀ l ∈ ls, l.WF U)
    (h6 : ls.length = d.uvars) (h7 : As.length = d.params.length) (h8 : I.length = T.indices.length)
    (WP : VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (hT : env.IsDefEq U Γ₀ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I))
      (.sort u))
    (hP : d.ProjAllowed c ls k) (hn : Inert env s)
    {M N Q : VExpr} {n N₀ : Nat} {m a : WShape n} {fs : List (WShape N₀)} {hf} {r : Bool}
    {h : IndHead} {l : List (WShape N₀)}
    (hhead : h.name = s)
    (H : (LR (U := U) (Γ := Γ₀) henv hU (N₀+1)).DefEq M N (.appN (.const s ls) (As ++ I))
      (.ctor c.name fs hf) (.indTy r h l))
    (hma : m.HasType a) (hinfo : TyInfo env U Γ₀ henv hU n Q a)
    (eM : TyEq env U Γ₀ (c.projType ls s k As M) Q) (eN : TyEq env U Γ₀ (c.projType ls s k As N) Q)
    (hMN : env.IsDefEq U Γ₀ (.proj s k M) (.proj s k N) Q)
    (HC : CtorVal (LR (U := U) (Γ := Γ₀) henv hU N₀) h l (.appN (.const s ls) (As ++ I)) M N
      c.name fs → (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.proj s k M) (.proj s k N) Q m a)
    (HS : StructVal (LR (U := U) (Γ := Γ₀) henv hU N₀) h l (.appN (.const s ls) (As ++ I)) M N
      c.name fs → (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.proj s k M) (.proj s k N) Q m a) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.proj s k M) (.proj s k N) Q m a := by
  simp only [LR, LRS, LRS.DefEq.ctor_indTy] at H
  unfold LRS.IndVal at H
  rcases H with H | hA | ⟨-, hM1, hN1⟩
  · split at H
    · exact HS H
    · exact HC H
  · exact (NeRed.not_inert hU (hhead ▸ hn) hA .rfl).elim
  · have pM := (TNeRed.proj henv hU hΓ₀ h1 h2 h3 hF h4 h5 h6 h7 h8 WP hT hP hM1).tyEq eM
    have pN := (TNeRed.proj henv hU hΓ₀ h1 h2 h3 hF h4 h5 h6 h7 h8 WP hT hP hN1).tyEq eN
    exact reflect henv hU n hma.isType hma hinfo pM pN hMN

end

section
variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}

/-- A typed interpretation `w : aI` of a value of a recorded type, above a constructor shape: at a
common depth, `w` is a constructor shape above the fields and `aI` the type's shape, and every
relation at `(w, aI)` is one at those shapes. -/
theorem proj_shape (hM : ModelEnv env) {s : Name} (hnd : ¬AxInterp.dom s) {d : VInductDecl}
    {t : Nat} {T : VInductiveType} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    {ρ : Valuation} {ls : List VLevel} {args : List VExpr}
    (hargs : args.length = d.params.length + T.indices.length) {c : Name}
    {n0 : Nat} {fs : List (WShape n0)} (hz : IsStruct c → WShape.ListNonZero fs)
    {n' : Nat} {w aI : WShape n'} (hle0 : (WShape.ctor' c fs).T ≤ w.T) (hty : w.HasType aI)
    (haI : LE_Interp env ρ aI.T ((VExpr.const s ls).appN args)) {e : VExpr}
    (hw : LE_Interp env ρ w.T e) :
    ∃ N, ∃ l' : List (WShape N), ∃ hf, ∃ I as,
      I.name = s ∧ List.Forall₂ (fun (x : WShape n0) (y : WShape N) => x.T ≤ y.T) fs l' ∧
      LE_Interp env ρ (WShape.ctor c l' hf).T e ∧
      LE_Interp env ρ (WShape.indTy true I as).T ((VExpr.const s ls).appN args) ∧
      (WShape.ctor c l' hf).HasType (.indTy true I as) ∧
      ∀ {Γ₀ : List VExpr} {M N' A : VExpr},
        (LR (U := U) (Γ := Γ₀) henv hU n').DefEq M N' A w aI →
        (LR (U := U) (Γ := Γ₀) henv hU (N+1)).DefEq M N' A (.ctor c l' hf) (.indTy true I as) := by
  let N := max n0 n'
  have hkN : n0 ≤ N := Nat.le_max_left ..
  have hnN : n' ≤ N + 1 := Nat.le_succ_of_le (Nat.le_max_right ..)
  have hle := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hkN) hnN).1 hle0
  simp only [WShape.T, WShape.lift_ctor' hkN] at hle
  obtain ⟨l', hf', hxe, hll⟩ := WShape.ctor'_le.1 hle
    (fun h => (WShape.ListNonZero.lift_iff hkN).2 (hz h))
  have hty' := (WShape.HasType.lift hnN).2 hty
  rw [hxe] at hty'
  obtain ⟨I, as, haeq⟩ := WShape.HasType.ctor_inv hty'
  have haQ' := haI.lift (n := N+1) hnN
  simp only [WShape.T] at haQ'
  rw [haeq] at haQ'
  have hI := (blockTy_inv hM hnd hs hT hargs haQ').1
  have hw' := hw.lift (n := N+1) hnN
  simp only [WShape.T] at hw'
  rw [hxe] at hw'
  rw [haeq] at hty'
  refine ⟨N, l', hf', I, as, by rw [hI], ?_, hw', haQ', hty', fun {Γ₀ M N' A} H => ?_⟩
  · exact List.Forall₂.imp (fun x y h => (TShape.lift_eqv (a := x.T) hkN).2.trans (WShape.LE.T h))
      (List.forall₂_map_left_iff.1 hll)
  · have H' := (LR.DefEq.lift hnN hty).2 H
    rw [hxe, haeq] at H'
    exact H'

end

end LogRel
end Lean4Lean

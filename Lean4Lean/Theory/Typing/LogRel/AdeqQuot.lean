import Lean4Lean.Theory.Typing.LogRel.RuleBodies
import Lean4Lean.Theory.Typing.LogRel.AdeqBlock

/-!
# `Quot.lift` in the logical relation

`Quot.lift` reduces on a major premise that reduces to `Quot.mk` (`Step.quot`), or, where the
quotient is a proposition, on any major premise at a chosen element (`Step.kQuot`). Here those
reductions are typed, with what the relation provides as their checks.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- Two terms are related wherever the first is, when under every related substitution they
reduce, by typed reductions, to a common term: the right side of a rule whose sides compute to
the same term. -/
theorem AdeqStmt.of_common (hΓ : OnCtx Γ (env.IsType U)) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {L R A : VExpr} {u : VLevel} (hA : env.HasType U Γ A (.sort u))
    (HL : AdeqStmt (U := U) henv hU Γ₀ Γ L L A)
    (hred : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ → ∃ B,
      TRed env U Γ₀ (L.subst σ) B (A.subst σ) ∧ TRed env U Γ₀ (R.subst σ) B (A.subst σ)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ L R A := by
  intro ρ n m a hm ha hmem
  have ad := HL hm ha hmem
  -- `L` and `R` are related wherever `L` is related to itself, at a type equal to `A`'s instance
  have LR1 {σ T} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ)
      (hT : env.IsDefEq U Γ₀ (A.subst σ) T (.sort u))
      (H : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (L.subst σ) (L.subst σ) T m a) :
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (L.subst σ) (R.subst σ) T m a := by
    obtain ⟨B, r1, r2⟩ := hred W
    have r1' := r1.tyEq (.base hT); have r2' := r2.tyEq (.base hT)
    exact ((LR _ _ _).whr r1' r2').2 (((LR _ _ _).whr r1' r1').1 H)
  have hAσ {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
      env.IsDefEq U Γ₀ (A.subst σ) (A.subst σ') (.sort u) :=
    hA.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
  refine ⟨fun σ σ' W => ⟨(ad.1 W).1, ?_⟩,
    fun σ W => LR1 W (hAσ W) (ad.2 W)⟩
  -- the right side at the two substitutions, through the left side
  have hσ := LR1 W.left (hAσ W.left) ((LR _ _ _).left (ad.1 W).1)
  have hσ' := LR1 W.symm.left (hAσ W).symm ((LR _ _ _).left ((LR _ _ _).symm (ad.1 W).1))
  exact (LR _ _ _).trans ((LR _ _ _).trans ((LR _ _ _).symm hσ) (ad.1 W).1) hσ'

end

/-- The type of `Quot.lift`'s major premise is a type over its other binders. -/
theorem quotLift_majorTy (hq : env.constants ``Quot = some quotConst) {u v : VLevel}
    (hu : u.WF U) (hv : v.WF U) :
    env.HasType U (QuotRed.liftBinders.map (·.instL [u, v])).reverse
      ((VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)).instL [u, v])
      (.sort u) := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  have H : env.HasType 2 QuotRed.liftBinders.reverse
      (VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)) (.sort (.param 0)) := by
    simp only [QuotRed.liftBinders, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    type_tac
  have := H.instL hls
  simpa [List.map_reverse, VExpr.instL, VLevel.inst] using this

/-- Arguments for `Quot.lift`'s first five binders and two equal major premises, as a pairing
along `Quot.lift`'s telescope. -/
theorem quotLift_pair (hq : env.constants ``Quot = some quotConst) {u v : VLevel}
    (hu : u.WF U) (hv : v.WF U) {α r β f h q q' : VExpr}
    (W5 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h])
      (Subst.id.consList [α, r, β, f, h]) (QuotRed.liftBinders.map (·.instL [u, v])).reverse)
    (hqq : env.IsDefEq U Γ q q' (.app (.app (.const ``Quot [u]) α) r)) :
    VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h, q])
      (Subst.id.consList [α, r, β, f, h, q'])
      ((QuotRed.liftBinders ++
          [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).map
        (·.instL [u, v])).reverse := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  refine .cons W5 (quotLift_majorTy hq hu hv) ?_
  simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.instL, VLevel.inst,
    VExpr.subst] using hqq

/-- `Quot.lift` on a major premise reducing to `Quot.mk`, typed: the arguments are typed along the
rule's binders (`W`), and `Quot.mk` at `u`, `α`, `r` and `a` is paired with the major premise
along `Quot.lift`'s telescope (`Wc`). -/
theorem TRed.quotLift (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) (hnp : ¬u ≈ .zero)
    {α r β f h q a α' r' : VExpr} {ls₁ : List VLevel}
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h, a])
      (Subst.id.consList [α, r, β, f, h, a])
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).reverse)
    (Wc : VEnv.Ctx.SubstEq env U Γ
      (Subst.id.consList [α, r, β, f, h, .appN (.const ``Quot.mk [u]) [α, r, a]])
      (Subst.id.consList [α, r, β, f, h, q])
      ((QuotRed.liftBinders ++
          [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).map
        (·.instL [u, v])).reverse)
    (Hq : StepS env U Γ q ((VExpr.const ``Quot.mk ls₁).appN [α', r', a])) :
    TRed env U Γ ((VExpr.const ``Quot.lift [u, v]).appN [α, r, β, f, h, q]) (.app f a) β := by
  have hnq : ¬QuotProp [u, v] := by
    rintro ⟨u', v', e, h0⟩; cases e; exact hnp h0
  refine ⟨?_, henv.quotTyped hΓ hdf hlift (henv.quotBodyWF hdf) hu hv W Wc⟩
  have h1 : StepS env U Γ ((VExpr.const ``Quot.lift [u, v]).appN [α, r, β, f, h, q])
      ((VExpr.const ``Quot.lift [u, v]).appN
        [α, r, β, f, h, (VExpr.const ``Quot.mk ls₁).appN [α', r', a]]) :=
    StepS.quotMajor (α := α) (r := r) (β := β) (f := f) (h := h) hdf hnq Hq
  exact h1.trans (.single (Step.quot hdf hnq))

/-- `Quot.mk` at `u` applied to arguments typed along `Quot.lift`'s first two binders and an element
of `α` is an element of the quotient. -/
theorem quotMk_typed (hmk : env.constants ``Quot.mk = some quotMkConst) {u v : VLevel}
    (hu : u.WF U) (_hv : v.WF U) {α r β f h w : VExpr}
    (W5 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h])
      (Subst.id.consList [α, r, β, f, h]) (QuotRed.liftBinders.map (·.instL [u, v])).reverse)
    (hw : env.HasType U Γ w α) :
    env.HasType U Γ ((VExpr.const ``Quot.mk [u]).appN [α, r, w])
      (.app (.app (.const ``Quot [u]) α) r) := by
  have W2 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r]) (Subst.id.consList [α, r])
      ([VExpr.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))].map
        (·.instL [u])).reverse := by
    have := W5.tail.tail.tail
    simpa [QuotRed.liftBinders, Subst.consList, Subst.tail, VExpr.instL, VLevel.inst] using this
  have hα : env.HasType 1 [VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
      .sort (.param 0)] (.bvar 1) (.sort (.param 0)) := by type_tac
  have W3 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, w]) (Subst.id.consList [α, r, w])
      ([VExpr.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
        .bvar 1].map (·.instL [u])).reverse := by
    have hls : ∀ l ∈ [u], l.WF U := by simp [hu]
    refine .cons W2 (by simpa [VExpr.instL, VLevel.inst] using hα.instL hls) ?_
    exact hw
  have hc : env.HasType U Γ (.const ``Quot.mk [u]) (quotMkConst.type.instL [u]) :=
    .const hmk (by simp [hu]) rfl
  rw [QuotRed.quotMkConst_eq] at hc
  have := VEnv.IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := [])
    (As := [VExpr.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
      .bvar 1].map (·.instL [u])) (as := [α, r, w]) (bs := [α, r, w])
    (by rw [subst_id, ← VEnv.foralls_instL']; exact hc) rfl rfl (by simpa using W3)
  simp only [VExpr.instL, VLevel.inst, Subst.consList, Subst.cons, VExpr.subst, List.map,
    VExpr.appN] at this ⊢
  exact this

/-- `Quot.lift` on any major premise, where the quotient is a proposition, typed: it is `f` at the
chosen element of `α`, given the arguments for the first five binders (`W5`), that `α` has an
element, and the major premise typed. -/
theorem TRed.kQuotLift (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hq : env.constants ``Quot = some quotConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) (hu0 : u ≈ .zero) {α r β f h e : VExpr}
    (W5 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h])
      (Subst.id.consList [α, r, β, f, h]) (QuotRed.liftBinders.map (·.instL [u, v])).reverse)
    (hw : env.HasType U Γ (quotWit env U Γ α) α)
    (he : env.HasType U Γ e (.app (.app (.const ``Quot [u]) α) r)) :
    TRed env U Γ ((VExpr.const ``Quot.lift [u, v]).appN [α, r, β, f, h, e])
      (.app f (quotWit env U Γ α)) β := by
  have hmkw := quotMk_typed hmk hu hv W5 hw
  -- the quotient is a proposition, so its elements are equal
  have hQ : env.HasType U Γ (.app (.app (.const ``Quot [u]) α) r) (.sort u) := by
    have := (quotLift_majorTy hq hu hv).subst henv.ordered W5 hΓ
    simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.instL, VLevel.inst,
      VExpr.subst] using this
  have hQ0 : env.HasType U Γ (.app (.app (.const ``Quot [u]) α) r) (.sort .zero) :=
    .defeqDF (.sortDF hu (by trivial) hu0) hQ
  have hirr : env.IsDefEq U Γ ((VExpr.const ``Quot.mk [u]).appN [α, r, quotWit env U Γ α]) e
      (.app (.app (.const ``Quot [u]) α) r) := .proofIrrel hQ0 hmkw he
  have hw' : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h, quotWit env U Γ α])
      (Subst.id.consList [α, r, β, f, h, quotWit env U Γ α])
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).reverse := by
    have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
    have hb : env.HasType 2 QuotRed.liftBinders.reverse (.bvar 4) (.sort (.param 0)) := by
      simp only [QuotRed.liftBinders, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append]
      type_tac
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    refine .cons W5 (by simpa [List.map_reverse, VExpr.instL, VLevel.inst] using hb.instL hls) ?_
    simp only [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.instL, VExpr.subst]
    exact hw
  refine ⟨.single (Step.kQuot hdf rfl hu0 hw), henv.quotTyped hΓ hdf hlift (henv.quotBodyWF hdf)
    hu hv hw' (quotLift_pair hq hu hv W5 hirr)⟩

end LogRel
end Lean4Lean

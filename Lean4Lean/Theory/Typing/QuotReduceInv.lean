import Lean4Lean.Theory.Typing.QuotReduce
import Lean4Lean.Theory.Typing.RecursorInv

namespace Lean4Lean
open VExpr

namespace QuotRed

end QuotRed

/-- A term of `Quot α r` definitionally equal to `Quot.mk` at an equal quotient is `Quot.mk`
at `α` and `r`, applied to a term of `α`. -/
theorem VEnv.WF.quotMk_at {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hmk : env.constants ``Quot.mk = some quotMkConst)
    {u : VLevel} {lsm : List VLevel} {α r q α' r' a : VExpr} (hu : u.WF U)
    (hαT : env.HasType U Γ α (.sort u))
    (hqT : env.HasType U Γ q (.appN (.const ``Quot [u]) [α, r]))
    (hq : env.IsDefEqU U Γ q (.appN (.const ``Quot.mk lsm) [α', r', a]))
    (hα : env.IsDefEqU U Γ α' α) (hr : env.IsDefEqU U Γ r' r) :
    env.HasType U Γ a α ∧ env.IsDefEqU U Γ q (.appN (.const ``Quot.mk [u]) [α, r, a]) := by
  have hmkT := hqT.defeqU_l henv hΓ hq
  obtain ⟨cm, hcm, hlsm, hlenm⟩ := (appN_wf_prefix henv.ordered hΓ (as := []) (bs := [α', r', a])
    (⟨_, hmkT⟩ : VExpr.WF env U Γ ((VExpr.const ``Quot.mk lsm).appN ([] ++ [α', r', a])))).const_inv
      henv.ordered hΓ
  cases hmk.symm.trans hcm
  obtain ⟨u', rfl⟩ : ∃ u', lsm = [u'] := by
    match lsm, hlenm with | [u'], _ => exact ⟨u', rfl⟩
  have hcm : env.HasType U [] (.const ``Quot.mk [u']) (quotMkConst.type.instL [u']) :=
    .const hmk hlsm hlenm
  rw [QuotRed.quotMkConst_eq] at hcm
  simp only [instL_foralls] at hcm
  have htelem := (IsType.foralls_inv henv.ordered
    (VEnv.IsDefEq.isType henv.ordered (Γ := []) trivial hcm)).1
  have hcm0 := hcm.weak0 henv.ordered (Γ := Γ)
  rw [← subst_id (e := VExpr.foralls _ _)] at hcm0
  have W3 := VEnv.HasType.appN_invT henv hΓ (Δ := []) hcm0 .nil htelem ⟨_, hmkT⟩ rfl
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_nil, List.cons_append] at W3
  rw [show [α', r', a] = [α', r'] ++ [a] from rfl, Subst.consList_concat] at W3
  cases W3 with | cons W2 _ haT =>
  change env.HasType U Γ a α' at haT
  change VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α', r']) (Subst.id.consList [α', r'])
    [_, _] at W2
  have hα'T : env.HasType U Γ α' (.sort u') := by
    have := VEnv.Ctx.SubstEq.getElem (Δ := []) (as := [α', r'])
      (As := [(VExpr.sort (.param 0)).instL [u'],
        ((VExpr.bvar 0).forallE ((VExpr.bvar 1).forallE (.sort .zero))).instL [u']])
      2 rfl (by exact W2) rfl 0 (by simp) (by simp)
    simpa [instL, VLevel.inst] using this
  have hu' : u' ≈ u := VEnv.IsDefEqU.sort_inv henv hΓ
    ((hα'T.defeqU_l henv hΓ hα).uniqU henv hΓ hαT)
  refine ⟨haT.defeqU_r henv hΓ hα, hq.trans henv hΓ (VEnv.IsDefEqU.appN' henv hΓ
    ⟨_, .constDF hmk hlsm (by simpa using hu) hlenm (.cons hu' .nil)⟩
    (.cons hα (.cons hr (.cons ⟨_, haT⟩ .nil))) ⟨_, hmkT⟩)⟩

/-- `Quot.lift` at `Quot.mk` of the same quotient reduces to the lifted function. -/
theorem VEnv.WF.quotLift {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst) (hdf : env.defeqs quotDefEq)
    {ls lsm : List VLevel} {α r β f h q α' r' a : VExpr}
    (H : VExpr.WF env U Γ (.appN (.const ``Quot.lift ls) [α, r, β, f, h, q]))
    (hq : env.IsDefEqU U Γ q (.appN (.const ``Quot.mk lsm) [α', r', a]))
    (hα : env.IsDefEqU U Γ α' α) (hr : env.IsDefEqU U Γ r' r) :
    env.IsDefEqU U Γ (.appN (.const ``Quot.lift ls) [α, r, β, f, h, q]) (.app f a) := by
  -- the eliminator's levels and arguments
  obtain ⟨ci, hci, hls, hlen⟩ :=
    (appN_wf_prefix henv.ordered hΓ (as := []) (bs := [α, r, β, f, h, q]) (by simpa using H)).const_inv
      henv.ordered hΓ
  cases hlift.symm.trans hci
  obtain ⟨u, v, rfl⟩ : ∃ u v, ls = [u, v] := by
    match ls, hlen with | [u, v], _ => exact ⟨u, v, rfl⟩
  have hc : env.HasType U [] (.const ``Quot.lift [u, v]) (quotLiftConst.type.instL [u, v]) :=
    .const hlift hls hlen
  rw [QuotRed.quotLiftConst_eq] at hc
  simp only [instL_foralls] at hc
  have htele := (IsType.foralls_inv henv.ordered
    (VEnv.IsDefEq.isType henv.ordered (Γ := []) trivial hc)).1
  have hc0 := hc.weak0 henv.ordered (Γ := Γ)
  rw [← subst_id (e := VExpr.foralls _ _)] at hc0
  have W6 := VEnv.HasType.appN_invT henv hΓ (Δ := []) hc0 .nil htele H (by simp [QuotRed.liftBinders])
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.append_nil] at W6
  rw [show [α, r, β, f, h, q] = [α, r, β, f, h] ++ [q] from rfl, Subst.consList_concat] at W6
  cases W6 with | cons W5 _ hqT =>
  change VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h])
    (Subst.id.consList [α, r, β, f, h]) _ at W5
  change env.HasType U Γ q (.appN (.const ``Quot [u]) [α, r]) at hqT
  -- the constructor application is at the eliminator's quotient
  have hmkT := hqT.defeqU_l henv hΓ hq
  obtain ⟨cm, hcm, hlsm, hlenm⟩ := (appN_wf_prefix henv.ordered hΓ (as := []) (bs := [α', r', a])
    (⟨_, hmkT⟩ : VExpr.WF env U Γ ((VExpr.const ``Quot.mk lsm).appN ([] ++ [α', r', a])))).const_inv
      henv.ordered hΓ
  cases hmk.symm.trans hcm
  obtain ⟨u', rfl⟩ : ∃ u', lsm = [u'] := by
    match lsm, hlenm with | [u'], _ => exact ⟨u', rfl⟩
  have hcm : env.HasType U [] (.const ``Quot.mk [u']) (quotMkConst.type.instL [u']) :=
    .const hmk hlsm hlenm
  rw [QuotRed.quotMkConst_eq] at hcm
  simp only [instL_foralls] at hcm
  have htelem := (IsType.foralls_inv henv.ordered
    (VEnv.IsDefEq.isType henv.ordered (Γ := []) trivial hcm)).1
  have hcm0 := hcm.weak0 henv.ordered (Γ := Γ)
  rw [← subst_id (e := VExpr.foralls _ _)] at hcm0
  have W3 := VEnv.HasType.appN_invT henv hΓ (Δ := []) hcm0 .nil htelem ⟨_, hmkT⟩ rfl
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_nil, List.cons_append] at W3
  rw [show [α', r', a] = [α', r'] ++ [a] from rfl, Subst.consList_concat] at W3
  cases W3 with | cons W2 _ haT =>
  change env.HasType U Γ a α' at haT
  change VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α', r']) (Subst.id.consList [α', r'])
    [_, _] at W2
  have hαT : env.HasType U Γ α (.sort u) := by
    have := VEnv.Ctx.SubstEq.getElem (Δ := []) (As := QuotRed.liftBinders.map (·.instL [u, v]))
      (as := [α, r, β, f, h]) 5 rfl (by rw [List.append_nil]; exact W5) rfl 0 (by simp)
      (by simp [QuotRed.liftBinders])
    simpa [QuotRed.liftBinders, instL, VLevel.inst] using this
  have hα'T : env.HasType U Γ α' (.sort u') := by
    have := VEnv.Ctx.SubstEq.getElem (Δ := []) (as := [α', r'])
      (As := [(VExpr.sort (.param 0)).instL [u'],
        ((VExpr.bvar 0).forallE ((VExpr.bvar 1).forallE (.sort .zero))).instL [u']])
      2 rfl (by exact W2) rfl 0 (by simp) (by simp)
    simpa [instL, VLevel.inst] using this
  have hu : u' ≈ u := VEnv.IsDefEqU.sort_inv henv hΓ
    ((hα'T.defeqU_l henv hΓ hα).uniqU henv hΓ hαT)
  have haT' : env.HasType U Γ a α := haT.defeqU_r henv hΓ hα
  -- the constructor at the eliminator's quotient
  have hmkr : env.IsDefEqU U Γ q (.appN (.const ``Quot.mk [u]) [α, r, a]) := by
    have hlsu : ∀ l ∈ [u], l.WF U := fun l hl => hls l (by simp at hl; simp [hl])
    refine hq.trans henv hΓ (VEnv.IsDefEqU.appN' henv hΓ ⟨_, .constDF hmk hlsm hlsu hlenm
      (.cons hu .nil)⟩
      (.cons hα (.cons hr (.cons ⟨_, haT⟩ .nil))) ⟨_, hmkT⟩)
  -- the computation rule, at these arguments
  have W6 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h, a])
      (Subst.id.consList [α, r, β, f, h, a])
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).reverse := by
    rw [show [α, r, β, f, h, a] = [α, r, β, f, h] ++ [a] from rfl, Subst.consList_concat]
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    refine .cons W5 (u := u) ?_ haT'
    simp only [QuotRed.liftBinders, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, instL, VLevel.inst]
    exact .bvar (.succ (.succ (.succ (.succ .zero))))
  have hE0 := VEnv.IsDefEq.extra (Γ := []) hdf hls hlen
  have hE := VEnv.IsDefEq.extra (Γ := Γ) hdf hls hlen
  rw [QuotRed.quotDefEq_eq] at hE0 hE
  simp only [instL_lams, instL_foralls] at hE0 hE
  have hlen6 : [α, r, β, f, h, a].length =
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).length := by
    simp [QuotRed.liftBinders]
  have hL := VEnv.lams_appN henv hΓ ⟨_, hE0.hasType.1⟩ hlen6 W6
  have hR := VEnv.lams_appN henv hΓ ⟨_, hE0.hasType.2⟩ hlen6 W6
  have hT := hE.hasType.1
  rw [← subst_id (e := VExpr.foralls _ _)] at hT
  have happ := VEnv.HasType.appN_substT (Δ := []) hT hlen6 (by simpa using W6)
  have hLR := VEnv.IsDefEqU.appN henv hΓ (vs := [α, r, β, f, h, a]) ⟨_, hE⟩ ⟨_, happ⟩
  have H' : VExpr.WF env U Γ (.app (.appN (.const ``Quot.lift [u, v]) [α, r, β, f, h]) q) := by
    simpa [VExpr.appN] using H
  obtain ⟨_, _, hX, hqA⟩ := H'.app_inv henv.ordered hΓ
  have hcong : env.IsDefEqU U Γ (.appN (.const ``Quot.lift [u, v]) [α, r, β, f, h, q])
      (.appN (.const ``Quot.lift [u, v]) [α, r, β, f, h, .appN (.const ``Quot.mk [u]) [α, r, a]]) :=
    ⟨_, by simpa [VExpr.appN] using hX.appDF (hmkr.of_l henv hΓ hqA)⟩
  have hL' : env.IsDefEqU U Γ _ (.appN (.const ``Quot.lift [u, v])
      [α, r, β, f, h, .appN (.const ``Quot.mk [u]) [α, r, a]]) := hL
  have hR' : env.IsDefEqU U Γ _ (.app f a) := hR
  exact hcong.trans henv hΓ (hL'.symm.trans henv hΓ (hLR.trans henv hΓ hR'))

/-- `Quot.ind` at `Quot.mk` of the same quotient is the induction step at its argument: both
are proofs of the same proposition. -/
theorem VEnv.WF.quotInd {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hind : env.constants ``Quot.ind = some quotIndConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    {ls lsm : List VLevel} {α r β p q α' r' a : VExpr}
    (H : VExpr.WF env U Γ (.appN (.const ``Quot.ind ls) [α, r, β, p, q]))
    (hq : env.IsDefEqU U Γ q (.appN (.const ``Quot.mk lsm) [α', r', a]))
    (hα : env.IsDefEqU U Γ α' α) (hr : env.IsDefEqU U Γ r' r) :
    env.IsDefEqU U Γ (.appN (.const ``Quot.ind ls) [α, r, β, p, q]) (.app p a) := by
  obtain ⟨ci, hci, hls, hlen⟩ :=
    (appN_wf_prefix henv.ordered hΓ (as := []) (bs := [α, r, β, p, q]) (by simpa using H)).const_inv
      henv.ordered hΓ
  cases hind.symm.trans hci
  obtain ⟨u, rfl⟩ : ∃ u, ls = [u] := by
    match ls, hlen with | [u], _ => exact ⟨u, rfl⟩
  have hc : env.HasType U [] (.const ``Quot.ind [u]) (quotIndConst.type.instL [u]) :=
    .const hind hls hlen
  rw [QuotRed.quotIndConst_eq] at hc
  simp only [instL_foralls] at hc
  have htele := (IsType.foralls_inv henv.ordered
    (VEnv.IsDefEq.isType henv.ordered (Γ := []) trivial hc)).1
  have hc0 := hc.weak0 henv.ordered (Γ := Γ)
  rw [← subst_id (e := VExpr.foralls _ _)] at hc0
  have W := VEnv.HasType.appN_invT henv hΓ (Δ := []) hc0 .nil htele H
    (by simp [QuotRed.indBinders])
  have he := VEnv.HasType.appN_substT (Δ := []) hc0 (by simp [QuotRed.indBinders]) W
  change env.HasType U Γ _ (.app β q) at he
  have hget := fun k h h' => VEnv.Ctx.SubstEq.getElem (Δ := [])
    (As := QuotRed.indBinders.map (·.instL [u])) (as := [α, r, β, p, q]) 5 rfl
    (by simpa using W) (by simp [QuotRed.indBinders]) k h h'
  have hαT : env.HasType U Γ α (.sort u) := by
    simpa [instL, VLevel.inst, QuotRed.indBinders] using hget 0 (by simp) (by simp [QuotRed.indBinders])
  have hβT : env.HasType U Γ β (.forallE (.appN (.const ``Quot [u]) [α, r]) (.sort .zero)) := by
    simpa [instL, VLevel.inst, VExpr.subst, Subst.consList, VExpr.appN, QuotRed.indBinders,
      Subst.cons, Subst.lift, VExpr.lift] using
      hget 2 (by simp) (by simp [QuotRed.indBinders])
  have hpT : env.HasType U Γ p (.forallE α (.app β.lift
      (.appN (.const ``Quot.mk [u]) [α.lift, r.lift, .bvar 0]))) := by
    simpa [instL, VLevel.inst, VExpr.subst, Subst.consList, VExpr.appN, QuotRed.indBinders,
      Subst.cons, Subst.lift, VExpr.lift] using
      hget 3 (by simp) (by simp [QuotRed.indBinders])
  have hqT : env.HasType U Γ q (.appN (.const ``Quot [u]) [α, r]) := by
    simpa [instL, VLevel.inst, VExpr.subst, Subst.consList, VExpr.appN, QuotRed.indBinders,
      Subst.cons, Subst.lift, VExpr.lift] using
      hget 4 (by simp) (by simp [QuotRed.indBinders])
  obtain ⟨haT, hmkr⟩ := henv.quotMk_at hΓ hmk (hls u (by simp)) hαT hqT hq hα hr
  have hpa := hpT.app haT
  have hpa' : env.HasType U Γ (.app p a) (.app β (.appN (.const ``Quot.mk [u]) [α, r, a])) := by
    simpa [VExpr.inst, VExpr.appN, VExpr.inst_lift] using hpa
  have hβq : env.IsDefEq U Γ (.app β q) (.app β (.appN (.const ``Quot.mk [u]) [α, r, a]))
      (.sort .zero) := by
    simpa [VExpr.inst] using hβT.appDF (hmkr.of_l henv hΓ hqT)
  exact ⟨_, .proofIrrel hβq.hasType.2 (he.defeqU_r henv hΓ ⟨_, hβq⟩) hpa'⟩

end Lean4Lean

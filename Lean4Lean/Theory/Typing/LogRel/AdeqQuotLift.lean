import Lean4Lean.Theory.Typing.LogRel.AdeqQuotRule
import Lean4Lean.Theory.Typing.LogRel.Reflect

/-!
# `Quot.lift`'s constant case

`Quot.lift` is related where its application to the variables of its telescope is: the telescope
is typed before `Quot.lift`, in an environment with `Eq` and `Quot` where adequacy's cases hold.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- `Quot.lift`'s binders at levels `u v`. -/
def quotLiftBs (u v : VLevel) : List VExpr :=
  (QuotRed.liftBinders ++ [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).map
    (·.instL [u, v])

theorem quotLiftBs_length (u v : VLevel) : (quotLiftBs u v).length = 6 := by
  simp [quotLiftBs, QuotRed.liftBinders]

theorem quotLiftConst_type_instL (u v : VLevel) :
    quotLiftConst.type.instL [u, v] = .foralls (quotLiftBs u v) (.bvar 3) := by
  rw [QuotRed.quotLiftConst_eq]
  simp only [quotLiftBs]
  rw [VEnv.foralls_instL']; rfl

/-- `Quot.lift`'s binders are a telescope in an environment with `Eq` and `Quot`. -/
theorem quotLiftTele {E : VEnv} (hEq : E.constants ``Eq = some eqConst)
    (hq : E.constants ``Quot = some quotConst) :
    E.IsTele 2 [] (QuotRed.liftBinders ++
      [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]) := by
  simp only [QuotRed.liftBinders, List.cons_append, List.nil_append]
  refine .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <|
    .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ .nil

/-- `Quot.lift`'s result type is a type over its binders. -/
theorem quotLift_resTy {E : VEnv} (hEq : E.constants ``Eq = some eqConst)
    (hq : E.constants ``Quot = some quotConst) :
    E.IsType 2 (QuotRed.liftBinders ++
      [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).reverse (.bvar 3) := by
  simp only [QuotRed.liftBinders, List.cons_append, List.nil_append, List.reverse_cons,
    List.reverse_nil]
  exact ⟨_, by type_tac⟩

/-- Equal terms whose type is a pi telescope, applied to the telescope's own variables. -/
theorem _root_.Lean4Lean.VEnv.IsDefEq.appN_bvars' (henv : env.Ordered) {B : VExpr} :
    ∀ {Γ f g As}, env.IsDefEq U Γ f g (.foralls As B) →
    env.IsDefEq U (As.reverse ++ Γ) ((f.liftN As.length).appN (VExpr.bvars As.length 0))
      ((g.liftN As.length).appN (VExpr.bvars As.length 0)) B
  | _, _, _, [], h => by simpa using h
  | Γ, f, g, A :: As, h => by
    have h1 : env.IsDefEq U (A :: Γ) (.app f.lift (.bvar 0)) (.app g.lift (.bvar 0))
        (.foralls As B) := by
      have hw := h.weakN henv (.one (A := A))
      change env.IsDefEq U (A :: Γ) f.lift g.lift
        (.forallE (A.liftN 1) ((VExpr.foralls As B).liftN 1 1)) at hw
      have := hw.appDF (.bvar .zero)
      rwa [VExpr.inst_liftN_bvar] at this
    have := VEnv.IsDefEq.appN_bvars' henv h1
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    simpa [VExpr.bvars_succ, VExpr.appN, VExpr.liftN, VExpr.liftN_liftN, Nat.add_comm] using this

/-- `Quot.lift` at levels equivalent to `u v`, applied to its telescope's variables, is its
application at `u v`. -/
theorem quotLift_spine_defeq (henv : env.Ordered)
    (hlift : env.constants ``Quot.lift = some quotLiftConst) {u v : VLevel} (hu : u.WF U)
    (hv : v.WF U) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u, v] ls) {Γ : List VExpr} :
    env.IsDefEq U ((quotLiftBs u v).reverse ++ Γ)
      ((VExpr.const ``Quot.lift [u, v]).appN (VExpr.bvars 6 0))
      ((VExpr.const ``Quot.lift ls).appN (VExpr.bvars 6 0)) (.bvar 3) := by
  have h : env.IsDefEq U Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls)
      (quotLiftConst.type.instL [u, v]) :=
    .constDF hlift (by simp [hu, hv]) hls rfl heq
  rw [quotLiftConst_type_instL] at h
  have := VEnv.IsDefEq.appN_bvars' henv h
  rw [quotLiftBs_length] at this
  simpa [VExpr.liftN] using this

theorem quotLift_vals_subst (ls : List VLevel) (σ : VExpr.Subst) :
    ((VExpr.const ``Quot.lift ls).appN (VExpr.bvars 6 0)).subst σ =
      (VExpr.const ``Quot.lift ls).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0] := by
  simp [VExpr.bvars, VExpr.appN, VExpr.subst, List.range, List.range.loop]

/-- `Quot.lift` at levels where the quotient is a proposition, on any major premise, is stuck when
the context has no element of `α`. -/
theorem quotLift_stuck (hU : StepUniq env) {Γ : List VExpr} (hdf : env.defeqs quotDefEq)
    {ls : List VLevel} {α r β f h e : VExpr} (hq : QuotProp ls)
    (hnw : ¬∃ a, env.HasType U Γ a α) :
    WHNF env U Γ ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h, e]) ∧
      Neutral env ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h, e]) := by
  have hN : Neutral env (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e) :=
    .propQuot hdf hq
  refine ⟨fun e' H => ?_, hN⟩
  have K := Neutral.kStep hU hN H
  generalize hx : VExpr.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e = x at K
  revert hx
  cases K with
  | app K' =>
    intro hx; have h1 := (VExpr.app.inj hx).1; subst h1
    exact Step.quotHead_whnf hU hdf _ K'.step
  | proj => intro hx; cases hx
  | quotMajor _ hnq _ =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hnq (h1.2.1 ▸ hq)
  | kQuot _ _ _ hw =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    have h2 := h1.2.2
    simp only [List.cons.injEq] at h2
    exact hnw ⟨_, h2.1 ▸ hw⟩
  | major r1 r2 =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hU.recQuot hdf r1 (List.getElem?_eq_some_iff.1 r2).1 h1.1.symm
  | kIota r1 _ r3 =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hU.recQuot hdf r1 (List.getElem?_eq_some_iff.1 r3).1 h1.1.symm

/-- `Quot.lift`'s first five binders at levels `u v`, as a context. -/
def quotTailCtx (u v : VLevel) : List VExpr := (QuotRed.liftBinders.map (·.instL [u, v])).reverse

theorem quotLiftBs_ctx (u v : VLevel) (Γ : List VExpr) :
    (quotLiftBs u v).reverse ++ Γ =
      .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3) :: (quotTailCtx u v ++ Γ) := by
  simp [quotLiftBs, quotTailCtx, List.map_append, VExpr.instL, VLevel.inst]

theorem quotTailCtx_eq (u v : VLevel) : ∃ Hh, quotTailCtx u v =
    [Hh, .forallE (.bvar 2) (.bvar 1), .sort v,
      .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort u] :=
  ⟨_, by simp [quotTailCtx, QuotRed.liftBinders, VExpr.instL, VLevel.inst]; rfl⟩

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- A relation at shapes `m' a'` gives it at smaller value shape `m` and any type shape `a`, when
`a` and `a'` interpret the same type term, at which the relation's type is related to itself. -/
theorem LR.retype (hM : ModelEnv env) {ρ : Valuation} {T A M N : VExpr} {k n : Nat}
    {m' a' : WShape k} {m a : WShape n}
    (H : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq M N A m' a') (hm'a' : m'.HasType a')
    (hle : m.T ≤ m'.T) (hma : m.HasType a)
    (ha' : LE_Interp env ρ a'.T T) (ha : LE_Interp env ρ a.T T)
    (hTy : ∀ {j} {b : WShape j}, LE_Interp env ρ b.T T → b.HasType .type →
      (LR (U := U) (Γ := Γ₀) henv hU j).TyDefEq A A b) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m a := by
  have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
  have ht' := (WShape.HasType.lift le_n).2 hma
  have hp' := (WShape.HasType.lift le_k).2 hm'a'
  have hle' := (TShape.LE.def le_n le_k).1 hle
  have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hm'a'.isType
  have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 hma.isType
  have hc := ha'.compat hM ha
  have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
  rw [TShape.lift_join le_k le_n] at hj
  have ⟨hj1, hj2⟩ := hj.le
  have hJ := hta₁.join' hj hta'
  have hJ' := hJ.mono_r hj1 hp'
  refine (LR.DefEq.lift le_n hma).1 <|
    (LR _ _ _).mono_r_2 hj2 ht' hJ <|
    (LR _ _ _).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
    (LR _ _ _).mono_r_1 hj1 hp' hJ' ?_ <| (LR.DefEq.lift le_k hm'a').2 H
  refine (LR _ _ _).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
  · exact hTy (ha'.lift le_k) hta₁
  · exact hTy (ha.lift le_n) hta'

/-- A variable whose type is a sort, under related substitutions, gives related types at every
shape interpreting it. -/
theorem LR.SubstWF.varTy (hM : ModelEnv env) {Γ : List VExpr} {σ σ' : VExpr.Subst}
    {ρ : Valuation} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {i : Nat} {w : VLevel}
    (hl : Lookup Γ i (.sort w)) {j : Nat} {b : WShape j} (hb : LE_Interp env ρ b.T (.bvar i))
    (ht : b.HasType .type) :
    (LR (U := U) (Γ := Γ₀) henv hU j).TyDefEq (σ i) (σ' i) b := by
  have ⟨_, x', a', le_n, le_a, hx', ha', hty⟩ :=
    (W.fits.lookup hM hl (bvar_iff.1 hb)).out
  have H := LR.SubstWF.bvar hM W hl (bvar_iff.1 hx') ha' hty
  simp only [VExpr.subst] at H
  exact LR.toValTy le_n le_a ht ha' hty H

/-- Related functions at a pi type, applied to related arguments. -/
theorem LR.app_val {k : Nat} {g : WShapeFun k} {hg : g.NonZero} {a₁ : WShape k}
    {a₂ : WShapeFun k} {F F' X X' A B : VExpr} {p : WShape k}
    (Hf : (LR (U := U) (Γ := Γ₀) henv hU (k+1)).DefEq F F' (.forallE A B) (.lam g hg)
      (.forallE a₁ a₂))
    (hp : p.HasType a₁) (hx : env.IsDefEq U Γ₀ X X' A)
    (Hx : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq X X' A p a₁) :
    (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app F X) (.app F' X') (B.inst X) (g.app p)
      (a₂.app p) := by
  simp only [LR, LRS, LRS.DefEq.lam_forallE] at Hf
  rcases Hf with ⟨_, _, _, _, red, _, _, _, _, _, valPi⟩ | hn
  · cases StepS.of_whnf forallE_whnf red
    exact (LR _ _ _).trans (valPi.2 hp hx.hasType.1 ((LR _ _ _).left Hx)) (valPi.1 hp hx Hx).2
  · exact (NeRed.not_forallE hU hn .rfl).elim

/-- Related substitutions with their head values replaced by equal values at the type of an earlier
variable whose type is a sort, where the head variable's values are only `bot`: a proof's position
retyped. Unless the substitutions are the identity on `Γ₀`, at the empty valuation. -/
theorem LR.SubstWF.replaceVar (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {Γ : List VExpr} {A : VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (A :: Γ) ρ) {i : Nat} {w : VLevel}
    (hl : Lookup Γ i (.sort w)) {x x' : VExpr} (hx : env.IsDefEq U Γ₀ x x' (σ.tail i))
    (hbot : ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (.bvar 0) → m = .bot) :
    LR.SubstWF (U := U) henv hU Γ₀ (σ.tail.cons x) (σ'.tail.cons x') (.bvar i :: Γ) ρ ∨
      ρ = .nil := by
  cases W with
  | id => exact .inr rfl
  | cons W' h1 h2 h3 hA h0 =>
    rename_i ρt _ _ x0
    obtain ⟨k, w0⟩ := x0
    cases hbot (m := w0) (.bvar (by simp [Valuation.push]; exact .rfl))
    have hfit := W'.fits
    have hB : env.HasType U Γ (.bvar i) (.sort w) := .bvar hl
    obtain ⟨m', a', -, hm', ha', hty⟩ :=
      hfit.lookup hM hl (m := WShape.T (n := 0) .bot) TShape.bot_le'
    have hm'ty : m'.HasType .type := (TShape.HasType.mono_r ha'.le_sort .sort hty).toType'
    refine .inl (.cons (by simpa using W') (fun ha => InterpTyped.hsort
      (fun h => hfit.lookup hM hl (bvar_iff.1 h)) ha) hm' (TShape.HasType.bot_T' hm'ty) hB
      ⟨by simpa [VExpr.subst] using hx, fun n a ha => ⟨fun ht => ?_, fun m hm hma => ?_⟩⟩)
    · have ha' : LE_Interp env ρt a.T (.bvar i) := by
        have := bvar_iff.1 ha; exact .bvar (by simpa [Valuation.push] using this)
      refine ⟨⟨w, by simpa [VExpr.subst] using (W'.toSubstEq hΓ₀).lookup hl⟩, ?_⟩
      simpa [VExpr.subst] using LR.SubstWF.varTy hM W' hl ha' ht
    · have hle := bvar_iff.1 hm
      simp only [Valuation.push] at hle
      cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le')
      exact (LR _ _ _).bot hma.isType

/-- A variable whose type is a sort has, under related substitutions, what reflection needs of a
type at every shape interpreting it. -/
theorem LR.SubstWF.varTyInfo (hM : ModelEnv env) {Γ : List VExpr} {σ σ' : VExpr.Subst}
    {ρ : Valuation} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {i : Nat} {w : VLevel}
    (hl : Lookup Γ i (.sort w)) (hw : w.WF U) {j : Nat} {b : WShape j}
    (hb : LE_Interp env ρ b.T (.bvar i)) (ht : b.HasType .type) :
    TyInfo env U Γ₀ henv hU j (σ i) b := by
  refine ⟨LR.SubstWF.varTy hM W.left hl hb ht, ?_⟩
  have ⟨_, x', a', le_n, le_a, hx', ha', hty⟩ := (W.fits.lookup hM hl (bvar_iff.1 hb)).out
  have H := LR.SubstWF.bvar hM W.left hl (bvar_iff.1 hx') ha' hty
  simp only [VExpr.subst] at H
  exact (LR.toTyTy le_n le_a ht ha' hty (TyEq.refl (.sort hw)) H).1

/-- The saturated `Quot.lift` at a propositional quotient, at an interpretation that applies `f` to
`bot`: it reduces to `f` at a chosen element where the context has one, related through `f a`'s
adequacy (`HS`, over the rule's binders), and is stuck otherwise. -/
theorem quotLift_caseK (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hEq : env.constants ``Eq = some eqConst)
    (hq : env.constants ``Quot = some quotConst) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) (hu0 : u ≈ .zero)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (HS : AdeqStmt (U := U) henv hU Γ₀ (.bvar 4 :: (quotTailCtx u v ++ Γ))
      (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.bvar 0)) (.bvar 3))
    {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ)
    (hbot : ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (.bvar 0) → m = .bot)
    {ls₁ ls₂ : List VLevel} (hls₁ : ∀ l ∈ ls₁, l.WF U) (hls₂ : ∀ l ∈ ls₂, l.WF U)
    (h1 : List.Forall₂ (· ≈ ·) [u, v] ls₁) (h2 : List.Forall₂ (· ≈ ·) [u, v] ls₂)
    {n : Nat} {m a : WShape n} (hma : m.HasType a) (ha : LE_Interp env ρ a.T (.bvar 3))
    (hmS : LE_Interp env ρ m.T (.app (.bvar 2) (.bvar 0))) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
      ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a := by
  have hEo := henvW.ordered
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  -- the context
  have teleE : env.IsTele U [] (quotLiftBs u v) := by
    have := (quotLiftTele hEq hq).instL hls; simpa [quotLiftBs] using this
  have onBs : OnCtx (quotLiftBs u v).reverse (env.IsType U) := by
    simpa using teleE.onCtx (Γ := []) trivial
  have hΔ : OnCtx ((quotLiftBs u v).reverse ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hEo VEnv.LE.rfl hΓ onBs
  have onCs : OnCtx (quotTailCtx u v) (env.IsType U) := by
    have e := quotLiftBs_ctx u v []
    simp only [List.append_nil] at e
    rw [e] at onBs; exact onBs.1
  obtain ⟨Hh, eT⟩ := quotTailCtx_eq u v
  have eΔ := quotLiftBs_ctx u v Γ
  rw [eT] at eΔ
  have L0 : Lookup ((quotLiftBs u v).reverse ++ Γ) 0
      (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)) := by
    rw [eΔ]; exact .zero
  have L2 : Lookup ((quotLiftBs u v).reverse ++ Γ) 2 (.forallE (.bvar 5) (.bvar 4)) := by
    rw [eΔ]; exact .succ (.succ .zero)
  have L3 : Lookup ((quotLiftBs u v).reverse ++ Γ) 3 (.sort v) := by
    rw [eΔ]; exact .succ (.succ (.succ .zero))
  have L5 : Lookup ((quotLiftBs u v).reverse ++ Γ) 5 (.sort u) := by
    rw [eΔ]; exact .succ (.succ (.succ (.succ (.succ .zero))))
  have L4t : Lookup (quotTailCtx u v ++ Γ) 4 (.sort u) := by
    rw [eT]; exact .succ (.succ (.succ (.succ .zero)))
  have hWE := W.toSubstEq hΓ₀
  have h5 : env.IsDefEq U Γ₀ (σ 5) (σ' 5) (.sort u) := by simpa [VExpr.subst] using hWE.lookup L5
  have h3 : env.IsDefEq U Γ₀ (σ 3) (σ' 3) (.sort v) := by simpa [VExpr.subst] using hWE.lookup L3
  -- the spine at both levels, equal to the one at `u v`
  have hsp (ls : List VLevel) (hls' : ∀ l ∈ ls, l.WF U) (h : List.Forall₂ (· ≈ ·) [u, v] ls)
      {τ τ'} (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ' ((quotLiftBs u v).reverse ++ Γ)) :
      env.IsDefEq U Γ₀ ((VExpr.const ``Quot.lift [u, v]).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0])
        ((VExpr.const ``Quot.lift ls).appN [τ' 5, τ' 4, τ' 3, τ' 2, τ' 1, τ' 0]) (τ 3) := by
    have := (quotLift_spine_defeq hEo hlift hu hv hls' h (Γ := Γ)).substDF hEo hΔ hΓ₀ Wτ
    simpa [quotLift_vals_subst, VExpr.subst] using this
  have hD : env.IsDefEq U Γ₀ ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) :=
    (hsp ls₁ hls₁ h1 hWE.left).symm.trans (hsp ls₂ hls₂ h2 hWE)
  obtain ⟨u₁, v₁, rfl, e₁⟩ : ∃ u₁ v₁, ls₁ = [u₁, v₁] ∧ u ≈ u₁ := by
    cases h1 with | cons a h => cases h with | cons _ h => cases h; exact ⟨_, _, rfl, a⟩
  obtain ⟨u₂, v₂, rfl, e₂⟩ : ∃ u₂ v₂, ls₂ = [u₂, v₂] ∧ u ≈ u₂ := by
    cases h2 with | cons a h => cases h with | cons _ h => cases h; exact ⟨_, _, rfl, a⟩
  have hu₁ : u₁ ≈ .zero := Eq.trans (Eq.symm e₁) hu0
  have hu₂ : u₂ ≈ .zero := Eq.trans (Eq.symm e₂) hu0
  rcases Classical.em (∃ x, env.HasType U Γ₀ x (σ 5)) with ⟨x₀, hx₀⟩ | hnw
  · -- a chosen element: both sides reduce to `f` at it
    have hw := quotWit_spec hx₀
    have hw' : env.HasType U Γ₀ (quotWit env U Γ₀ (σ' 5)) (σ' 5) := quotWit_spec (.defeqDF h5 hw)
    have hP0 : env.HasType U Γ₀ (σ 5) (.sort .zero) :=
      .defeqDF (.sortDF hu (by trivial) hu0) h5.hasType.1
    have hx : env.IsDefEq U Γ₀ (quotWit env U Γ₀ (σ 5)) (quotWit env U Γ₀ (σ' 5)) (σ.tail 4) :=
      .proofIrrel hP0 hw (.defeqDF h5.symm hw')
    have W' : LR.SubstWF (U := U) henv hU Γ₀ σ σ'
        (.app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3) :: (quotTailCtx u v ++ Γ)) ρ := by
      rw [← quotLiftBs_ctx]; exact W
    rcases LR.SubstWF.replaceVar hM hΓ₀ W' L4t hx hbot with W2 | e
    · have r := ((HS hmS ha hma).1 W2).1
      simp only [VExpr.subst, Subst.cons, Subst.tail] at r
      -- the typed reductions
      have W5 {τ τ'} (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ' ((quotLiftBs u v).reverse ++ Γ)) :
          VEnv.Ctx.SubstEq env U Γ₀ (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1])
            (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1])
            (QuotRed.liftBinders.map (·.instL [u, v])).reverse := by
        rw [quotLiftBs_ctx] at Wτ
        have := Ctx.SubstEq.vals hEo onCs Wτ.left.tail
        show VEnv.Ctx.SubstEq env U Γ₀ _ _ (quotTailCtx u v)
        rw [eT] at this ⊢
        simpa [quotTailCtx, eT, VExpr.bvars, VExpr.subst, Subst.tail, List.range, List.range.loop]
          using this
      have he {τ τ'} (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ' ((quotLiftBs u v).reverse ++ Γ)) :
          env.HasType U Γ₀ (τ 0) (.app (.app (.const ``Quot [u]) (τ 5)) (τ 4)) := by
        simpa [VExpr.subst] using (Wτ.lookup L0).hasType.1
      have kq := TRed.kQuotLift henvW hΓ₀ hdf hq hmk hlift hu hv hu0 (W5 hWE) hw (he hWE)
      have kq' := TRed.kQuotLift henvW hΓ₀ hdf hq hmk hlift hu hv hu0 (W5 (W.symm.toSubstEq hΓ₀)) hw'
        (he (W.symm.toSubstEq hΓ₀))
      have tM : TRed env U Γ₀ ((VExpr.const ``Quot.lift [u₁, v₁]).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
          (.app (σ 2) (quotWit env U Γ₀ (σ 5))) (σ 3) :=
        ⟨.single (Step.kQuot hdf rfl hu₁ hw), (hsp _ hls₁ h1 hWE.left).symm.trans kq.2⟩
      have tN : TRed env U Γ₀
          ((VExpr.const ``Quot.lift [u₂, v₂]).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0])
          (.app (σ' 2) (quotWit env U Γ₀ (σ' 5))) (σ 3) :=
        TRed.tyEq (.base h3.symm)
          ⟨.single (Step.kQuot hdf rfl hu₂ hw'), (hsp _ hls₂ h2 (W.symm.toSubstEq hΓ₀).left).symm.trans kq'.2⟩
      exact ((LR _ _ _).whr tM tN).2 r
    · subst e; cases interp_nil_app_bvar hmS; exact (LR _ _ _).bot hma.isType
  · -- no element: both sides are stuck
    have hnw' : ¬∃ x, env.HasType U Γ₀ x (σ' 5) := fun ⟨x, hx⟩ => hnw ⟨x, .defeqDF h5.symm hx⟩
    have hInfo := LR.SubstWF.varTyInfo hM W L3 hv ha hma.isType
    refine reflect henv hU n hma.isType hma hInfo ?_ ?_ hD
    · have s := quotLift_stuck hU hdf (Γ := Γ₀) (r := σ 4) (β := σ 3) (f := σ 2) (h := σ 1)
        (e := σ 0) ⟨u₁, v₁, rfl, hu₁⟩ hnw
      exact ⟨_, .refl hD.hasType.1, s.1, s.2⟩
    · have s := quotLift_stuck hU hdf (Γ := Γ₀) (r := σ' 4) (β := σ' 3) (f := σ' 2) (h := σ' 1)
        (e := σ' 0) ⟨u₂, v₂, rfl, hu₂⟩ hnw'
      exact ⟨_, .refl hD.hasType.2, s.1, s.2⟩

/-- `Quot.lift` applied to its telescope's variables is related, given `f a`'s adequacy over the
quotient rule's binders (`HS`), that a proof variable's values are `bot` (`hbotP`), and the case
of a major premise interpreted as `Quot.mk` at a quotient that is not a proposition (`HQ`). -/
theorem quotLift_spine (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hEq : env.constants ``Eq = some eqConst)
    (hq : env.constants ``Quot = some quotConst) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u, v] ls')
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (HS : AdeqStmt (U := U) henv hU Γ₀ (.bvar 4 :: (quotTailCtx u v ++ Γ))
      (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.bvar 0)) (.bvar 3))
    (hbotP : u ≈ .zero → ∀ {σ σ' ρ},
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ →
      ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (.bvar 0) → m = .bot)
    (HQ : ¬u ≈ .zero → ∀ {σ σ' ρ},
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ →
      ∀ {ls₁ ls₂ : List VLevel}, (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      List.Forall₂ (· ≈ ·) [u, v] ls₁ → List.Forall₂ (· ≈ ·) [u, v] ls₂ →
      ∀ {n} {m a : WShape n}, m.HasType a → LE_Interp env ρ a.T (.bvar 3) →
      ∀ {k} {a₀ : WShape k} {x f : WShape (k+1)}, LE_Interp env ρ x.T (.bvar 0) →
      LE_Interp env ρ f.T (.bvar 2) → AppS f.T [a₀.T] m.T →
      (WShape.ctor' ``Quot.mk [a₀]).T ≤ x.T →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
        ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
        ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a) :
    AdeqStmt (U := U) henv hU Γ₀ ((quotLiftBs u v).reverse ++ Γ)
      ((VExpr.const ``Quot.lift [u, v]).appN (VExpr.bvars 6 0))
      ((VExpr.const ``Quot.lift ls').appN (VExpr.bvars 6 0)) (.bvar 3) := by
  intro ρ n m a hm ha hma
  have huv : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  have hrefl : List.Forall₂ (· ≈ ·) [u, v] [u, v] :=
    .cons (rfl : VLevel.Equiv u u) (.cons (rfl : VLevel.Equiv v v) .nil)
  -- the constant's interpretation at the arguments' interpretations
  have hA : ConstArity env ``Quot.lift .quotLift 6 := .quotLift hdf rfl
  have hm' := hm
  rw [show VExpr.bvars 6 0 = [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0] by
    simp [VExpr.bvars, List.range, List.range.loop], ← spine_eq_appN] at hm'
  obtain ⟨n0, H0⟩ := hm'.spine_inv hM.roles (fun h => hM.domRole h hA) (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y', hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 6 := by rw [List.Forall₂.length_eq hra]; simp
  -- the saturated spine at two related substitutions and levels
  have core : ∀ {σ σ'}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ →
      ∀ {ls₁ ls₂ : List VLevel}, (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      List.Forall₂ (· ≈ ·) [u, v] ls₁ → List.Forall₂ (· ≈ ·) [u, v] ls₂ →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
        ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
        ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a := by
    intro σ σ' W ls₁ ls₂ hl₁ hl₂ h₁ h₂
    have hbotm : y' ≤ TShape.bot → (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
        ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
        ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a := by
      intro hb
      cases show m = .bot from TShape.le_bot.1 (hyy.trans hb)
      exact (LR _ _ _).bot hma.isType
    cases hC with
    | bot => exact hbotm TShape.bot_eqv.1
    | lam he hle => exact hbotm (Const.lam_le_bot hM.roles he hle (hrl ▸ hA))
    | ext h0 => exact (hM.domRole h0 hA).elim
    | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
    | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
    | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
    | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
    | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
    | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
    | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
    | quotK _ _ h3 h4 h5 =>
      cases h3
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
      cases hra with | cons _ hra =>
      cases hra with | cons _ hra =>
      cases hra with | cons hf _ =>
      let .cons (f := f') (x := x0) h6 h7 h8 := h5
      let .nil h9 := h8
      have hmS : LE_Interp env ρ m.T (.app (.bvar 2) (.bvar 0)) :=
        LE_Interp.mono hyy (.app (hf.mono h6) (.mono h7 .bot) h9)
      exact quotLift_caseK hM henvW hΓ₀ hdf hEq hq hmk hlift hu hv h4 hΓ HS W
        (hbotP h4 W) hl₁ hl₂ h₁ h₂ hma ha hmS
    | quot _ _ h3 h4 h5 h6 =>
      cases h3
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
      cases hra with | cons hx hra =>
      cases hra with | cons _ hra =>
      cases hra with | cons hf _ =>
      exact HQ h4 W hl₁ hl₂ h₁ h₂ hma ha hx hf (AppS.mono hyy .rfl h5) h6
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · rw [quotLift_vals_subst, quotLift_vals_subst]; exact core W huv huv hrefl hrefl
  · rw [quotLift_vals_subst, quotLift_vals_subst]; exact core W hls' hls' heq heq
  · rw [quotLift_vals_subst, quotLift_vals_subst]; exact core W huv hls' hrefl heq

/-- `Quot.mk` is not a structure's constructor. -/
theorem quotMk_not_struct (hM : ModelEnv env) (hdf : env.defeqs quotDefEq) :
    IsStruct ``Quot.mk = false := by
  cases h : IsStruct ``Quot.mk; · rfl
  obtain ⟨s, d, t, T, c', hs, hT, hc, -, -, e⟩ := hM.struct _ h
  have hB : ConstArity env ``Quot.mk .quotMk 3 := .quotMk hdf rfl
  cases hM.roles (.ctor hs hT (hc ▸ List.mem_singleton_self _) e) hB

/-- The domain of `Quot.mk`'s field telescope in an inductive type shape interpreting
`Quot α r` interprets `α`. -/
theorem quotTy_ctorTel_dom (hM : ModelEnv env) (hdf : env.defeqs quotDefEq)
    (hmk : env.constants ``Quot.mk = some quotMkConst) {ρ : Valuation} {u : VLevel}
    {A R : VExpr} {K : Nat} {r : Bool} {h : IndHead} {l : List (WShape K)}
    (haQ : LE_Interp env ρ (WShape.indTy r h l).T (.app (.app (.const ``Quot [u]) A) R))
    {b : WShape K} {g : WShapeFun K} (hv : (ctorTel h l 0).piView = some (b, g)) :
    LE_Interp env ρ b.T A := by
  have hA : ConstArity env ``Quot .quotTy 2 := .quotTy hdf rfl
  have haQ' : LE_Interp env ρ (WShape.indTy r h l).T (spine ``Quot [u] [R, A]) := by
    rw [show [R, A] = [A, R].reverse from rfl, spine_eq_appN]; exact haQ
  obtain ⟨n0, H0⟩ := haQ'.spine_inv hM.roles (fun h => hM.domRole h hA) (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y, hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 2 := by rw [List.Forall₂.length_eq hra]; simp
  have hnb : ¬ y ≤ TShape.bot := fun hb => by
    have := WShape.LE.of_T ((hyy.trans hb).trans TShape.bot_eqv.2)
    simp [WShape.indTy, WShape.bot, WShape.LE.def, Shape.LE.def, Shape.bot] at this
  cases hC with
  | bot => exact (hnb TShape.bot_eqv.1).elim
  | lam he hle => exact (hnb (Const.lam_le_bot hM.roles he hle (hrl ▸ hA))).elim
  | ext h0 => exact (hM.domRole h0 hA).elim
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotTy hd' e2 e3 hl2 h5 h6 h7 h8 _g =>
    rename_i u' hh ci cty
    cases e3
    rw [hmk] at h5; cases h5
    -- the type's telescope against the interpretation's
    obtain ⟨rA, rR, rfl⟩ : ∃ rA rR, rargs = [rR, rA] := by
      match rargs, hrl with | [x, y], _ => exact ⟨_, _, rfl⟩
    cases hra with | cons hR hra =>
    cases hra with | cons hAa _ =>
    have hcty : LE_Interp env (pushAll ρ [rA.T, rR.T]) cty.T
        (.forallE (.bvar 1) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1))) := by
      have := LE_Interp.piAppS_foralls hM (Ds := [.bvar 1]) [.sort u,
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))] (by
          rw [quotMk_type] at h6; exact h6) h7 rfl
      simpa using this
    have hle := hyy.trans h8
    let N := max K n0
    have hK : K ≤ N := Nat.le_max_left ..; have hn : n0 ≤ N := Nat.le_max_right ..
    have hle' := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hK) (Nat.succ_le_succ hn)).1 hle
    simp only [WShape.lift_indTy hK, WShape.lift_indTy hn, WShape.indTy_le_indTy] at hle'
    obtain ⟨-, rfl, hl⟩ := hle'
    have htel := hl.getD' (d := WShape.bot) (d' := WShape.bot) WShape.LE.rfl 2
    have e1 : (List.map (WShape.lift N) l).getD 2 WShape.bot = (ctorTel ⟨``Quot, 2, [``Quot.mk], [1]⟩ l 0).lift N := by
      simp only [ctorTel, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases l[2]? <;> simp
    rw [e1] at htel
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, List.map_cons, List.getD_cons_succ, List.getD_cons_zero] at htel
    have hT : (ctorTel ⟨``Quot, 2, [``Quot.mk], [1]⟩ l 0).T ≤ cty.T :=
      (TShape.LE.def (m := N) hK hn).2 htel
    have hctel := hcty.mono hT
    cases K with
    | zero => simp [WShape.piView] at hv
    | succ K =>
      obtain ⟨s, f, he, rfl, rfl⟩ := WShape.piView_eq_some hv
      rw [he] at hctel
      have hs := bvar_iff.1 (hctel.forallE_inv' hM).1
      simp only [pushAll, Valuation.push] at hs
      exact hAa.mono (((TShape.lift_eqv (a := s.T) (Nat.le_succ _)).1).trans hs)
/-- `Quot.lift` is related at its type wherever its application to its telescope's variables is,
given adequacy's cases for an environment `E₀` with `Eq` and `Quot` before it. -/
theorem AdeqStmt.quotLift_of_spine (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀) (hEq : E₀.constants ``Eq = some eqConst)
    (hq : E₀.constants ``Quot = some quotConst) {u v : VLevel} (hu : u.WF U) (hv : v.WF U)
    {ls' : List VLevel} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (H : AdeqStmt (U := U) henv hU Γ₀ ((quotLiftBs u v).reverse ++ Γ)
      ((VExpr.const ``Quot.lift [u, v]).appN (VExpr.bvars 6 0))
      ((VExpr.const ``Quot.lift ls').appN (VExpr.bvars 6 0)) (.bvar 3)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (quotLiftConst.type.instL [u, v]) := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  rw [quotLiftConst_type_instL]
  have hT : E₀.IsTele U [] (quotLiftBs u v) := by
    have := (quotLiftTele hEq hq).instL hls; simpa [quotLiftBs] using this
  have hR : E₀.IsType U (quotLiftBs u v).reverse (.bvar 3) := by
    have ⟨w, h⟩ := quotLift_resTy hEq hq
    exact ⟨_, by simpa [quotLiftBs, List.map_reverse, VExpr.instL] using h.instL hls⟩
  have H' : AdeqStmt (U := U) henv hU Γ₀ ((quotLiftBs u v).reverse ++ Γ)
      (etaSpine (quotLiftBs u v) (.const ``Quot.lift [u, v]))
      (etaSpine (quotLiftBs u v) (.const ``Quot.lift ls')) (.bvar 3) := by
    rw [etaSpine_eq, etaSpine_eq, quotLiftBs_length]
    intro ρ n m a; exact H
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (.foralls (quotLiftBs u v) (.bvar 3)) :=
    AdeqStmt.etaLams_closed hM hΓ₀ hE₀le hE₀o hS IH hT hΓ hR @H'
  exact @key

/-- `Quot.lift`'s constant case, given adequacy's cases for an environment `E₀` with `Eq` and `Quot`
where `Quot.lift`'s telescope is typed, model soundness for it, and the case of a major premise
interpreted as `Quot.mk` at a quotient that is not a proposition (`HQ`). -/
theorem AdeqStmt.quotLift (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀) (hEq₀ : E₀.constants ``Eq = some eqConst)
    (hq₀ : E₀.constants ``Quot = some quotConst)
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u, v] ls') {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (HQ : ¬u ≈ .zero → ∀ {σ σ' ρ},
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ →
      ∀ {ls₁ ls₂ : List VLevel}, (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      List.Forall₂ (· ≈ ·) [u, v] ls₁ → List.Forall₂ (· ≈ ·) [u, v] ls₂ →
      ∀ {n} {m a : WShape n}, m.HasType a → LE_Interp env ρ a.T (.bvar 3) →
      ∀ {k} {a₀ : WShape k} {x f : WShape (k+1)}, LE_Interp env ρ x.T (.bvar 0) →
      LE_Interp env ρ f.T (.bvar 2) → AppS f.T [a₀.T] m.T →
      (WShape.ctor' ``Quot.mk [a₀]).T ≤ x.T →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
        ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
        ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (quotLiftConst.type.instL [u, v]) := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  have hEq := hE₀le.constants hEq₀
  have hq := hE₀le.constants hq₀
  obtain ⟨Hh, eT⟩ := quotTailCtx_eq u v
  -- `f a` over the quotient rule's binders, typed with `Eq`
  have teleR : E₀.IsTele U [] ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])) := by
    have := (quotTele hEq₀).instL hls; simpa using this
  have onR : OnCtx (.bvar 4 :: quotTailCtx u v) (E₀.IsType U) := by
    have := teleR.onCtx (Γ := []) trivial
    simpa [quotTailCtx, List.map_append, VExpr.instL] using this
  have hRb : E₀.HasType U (.bvar 4 :: quotTailCtx u v) (.app (.bvar 2) (.bvar 0)) (.bvar 3) := by
    have := (quotRb_typed hEq₀).instL hls
    simpa [quotTailCtx, List.map_append, List.map_reverse, VExpr.instL] using this
  have hΔ' : OnCtx ((.bvar 4 :: quotTailCtx u v) ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hE₀o hE₀le hΓ onR
  have HS : AdeqStmt (U := U) henv hU Γ₀ (.bvar 4 :: (quotTailCtx u v ++ Γ))
      (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.bvar 0)) (.bvar 3) :=
    LR.adequacy_of hM hE₀le hS hΓ₀ IH (IsDefEq.weak_closed hE₀o onR hRb Γ) hΔ'
  -- the major premise is a proof where the quotient is a proposition
  have teleE₀ : E₀.IsTele U [] (quotLiftBs u v) := by
    have := (quotLiftTele hEq₀ hq₀).instL hls; simpa [quotLiftBs] using this
  have onBs : OnCtx (quotLiftBs u v).reverse (E₀.IsType U) := by
    simpa using teleE₀.onCtx (Γ := []) trivial
  have eB : (quotLiftBs u v).reverse =
      .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3) :: quotTailCtx u v := by
    simpa using quotLiftBs_ctx u v []
  have hbotP : u ≈ .zero → ∀ {σ σ' ρ},
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ →
      ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (.bvar 0) → m = .bot := by
    intro hp σ σ' ρ W n m hm
    have D0 : E₀.IsDefEq U (quotLiftBs u v).reverse (.bvar 0) (.bvar 0)
        (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)) := by
      refine .bvar ?_; rw [eB]; exact .zero
    have DQ : E₀.HasType U (quotLiftBs u v).reverse
        (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)) (.sort u) := by
      have h0 := quotLift_majorTy (env := E₀) (U := U) hq₀ hu hv
      have := h0.weakN hE₀o (.one (A := .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)))
      rw [eB]
      simpa [quotTailCtx, List.map_reverse, VExpr.instL, VLevel.inst, VExpr.liftN] using this
    have S0 := hS (IsDefEq.weak_closed hE₀o onBs D0 Γ)
    have SQ := hS (IsDefEq.weak_closed hE₀o onBs DQ Γ)
    have hr : levelRel u = false := by simp [levelRel, hp]
    exact TShape.le_bot.1 (StrongSound.proof_le_bot' S0.left SQ.left hr W.fits hm)
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (quotLiftConst.type.instL [u, v]) :=
    AdeqStmt.quotLift_of_spine hM hΓ₀ hE₀le hE₀o hS IH hEq₀ hq₀ hu hv hΓ
      (quotLift_spine hM henvW hΓ₀ hdf hEq hq hmk hlift hu hv hls' heq hΓ HS hbotP HQ)
  exact @key

omit [ShapeEnv] [AxInterp] in
/-- The quotient's parameters at a level. -/
theorem typeTele_quot (hni : env.inducts ``Quot = none) (hq : env.constants ``Quot = some quotConst)
    (u : VLevel) : typeTele env ``Quot [u] =
      [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))] := by
  simp only [typeTele, hni, hq]; rfl

omit [ShapeEnv] [AxInterp] in
/-- What the relation's constructor parameters say of a `Quot.mk` application at the quotient
`Quot.{u} α r`: its level is equivalent to `u`, and its parameters are `α` and `r`, up to
definitional equality. -/
theorem quotMk_params (hni : env.inducts ``Quot = none)
    (hq : env.constants ``Quot = some quotConst) {Γ₀ : List VExpr} {h : IndHead}
    (hh : h.name = ``Quot) {qs ms : List VExpr} {ls : List VLevel} {u : VLevel}
    {α r : VExpr} (hlsW : ∀ l ∈ ls, l.WF U)
    (H : CtorParams env U Γ₀ h ``Quot.mk ls qs ms [u] [α, r]) :
    ∃ u₀ α' r', ls = [u₀] ∧ u₀ ≈ u ∧ qs = [α', r'] ∧
      env.IsDefEq U Γ₀ α' α (.sort u₀) ∧
      env.IsDefEq U Γ₀ r' r (.forallE α' (.forallE (α'.liftN 1) (.sort .zero))) := by
  obtain ⟨hls, hlen, -, hR⟩ := H
  obtain ⟨u₀, rfl, hu₀⟩ : ∃ u₀, ls = [u₀] ∧ u₀ ≈ u := by
    cases hls with | cons a h => cases h; exact ⟨_, rfl, a⟩
  rw [hh] at hlen hR
  have hci : ctorIdx env ``Quot ``Quot.mk [u₀] (qs ++ ms) = [] := by simp [ctorIdx, hni]
  rw [hci, List.append_nil, typeTele_quot hni hq] at hlen
  rw [hci, List.append_nil, typeTele_quot hni hq, typeTele_quot hni hq] at hR
  obtain ⟨α', r', rfl⟩ : ∃ α' r', qs = [α', r'] := by
    match qs, hlen with | [a, b], _ => exact ⟨_, _, rfl⟩
  have hon : OnCtx [VExpr.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort u₀]
      (env.IsType U) := by
    have hle : VEnv.empty ≤ env := ⟨nofun, nofun, nofun⟩
    have := ((quotMkTele_isTele (u := u₀) (hlsW u₀ (by simp))).mono hle).onCtx (Γ := []) trivial
    simpa [quotMkTele] using this.1
  have W := SubstRel.substEq hR (by simpa using hon)
  refine ⟨u₀, α', r', rfl, hu₀, rfl, ?_, ?_⟩
  · have := W.lookup (i := 1) (A := .sort u₀) (.succ .zero)
    simpa [VExpr.Subst.consList, VExpr.Subst.cons, VExpr.subst] using this
  · have := W.lookup (i := 0) (.zero (ty := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
    simpa [VExpr.Subst.consList, VExpr.Subst.cons, VExpr.subst, VExpr.lift, VExpr.liftN,
      VExpr.Subst.lift, VExpr.Subst.head, VExpr.Subst.tail] using this

omit [ShapeEnv] [AxInterp] in
/-- `Quot.mk` at equivalent levels and equal parameters is equal. -/
theorem quotMk_congr (hmk : env.constants ``Quot.mk = some quotMkConst) {Γ : List VExpr}
    {u u₀ : VLevel} (hu : u.WF U) (hu₀ : u₀.WF U) (e : u₀ ≈ u) {α α' r r' a : VExpr}
    (hα : env.IsDefEq U Γ α' α (.sort u₀))
    (hr : env.IsDefEq U Γ r' r (.forallE α' (.forallE (α'.liftN 1) (.sort .zero))))
    (ha : env.HasType U Γ a α') :
    env.IsDefEq U Γ ((VExpr.const ``Quot.mk [u₀]).appN [α', r', a])
      ((VExpr.const ``Quot.mk [u]).appN [α, r, a])
      (.app (.app (.const ``Quot [u₀]) α') r') := by
  have hle : VEnv.empty ≤ env := ⟨nofun, nofun, nofun⟩
  have T := (quotMkTele_isTele (u := u₀) hu₀).mono hle
  simp only [quotMkTele] at T
  cases T with | cons hA0 T =>
  cases T with | cons hA1 T =>
  have ⟨_, h0⟩ := hA0; have ⟨_, h1⟩ := hA1
  have W : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α', r', a]) (Subst.id.consList [α, r, a])
      (quotMkTele u₀).reverse := by
    simp only [quotMkTele, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    cases T with | cons hA2 _ =>
    have ⟨_, h2⟩ := hA2
    refine .cons (.cons (.cons .nil h0 ?_) h1 ?_) h2 ?_
    · simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst] using hα
    · simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst, VExpr.Subst.lift,
        VExpr.liftN] using hr
    · simp only [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst]; exact ha
  have hc : env.IsDefEq U Γ (.const ``Quot.mk [u₀]) (.const ``Quot.mk [u])
      (quotMkConst.type.instL [u₀]) :=
    .constDF hmk (by simp [hu₀]) (by simp [hu]) rfl (.cons e .nil)
  rw [quotMk_type] at hc
  have := VEnv.IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := []) (As := quotMkTele u₀)
    (as := [α', r', a]) (bs := [α, r, a]) (by rw [subst_id]; exact hc) rfl rfl (by simpa using W)
  simpa [quotMkTele, VExpr.subst, Subst.consList, Subst.cons, VExpr.appN] using this

end
end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.AdeqQuotLift

/-!
# `Quot.lift` on `Quot.mk`

The remaining case of `Quot.lift`'s constant case: at a quotient that is not a proposition, a
major premise interpreted as `Quot.mk` is related, through the relation at the quotient's type,
to a `Quot.mk` application, on which `Quot.lift` reduces to `f` at its element.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- A pairing along `Quot.lift`'s telescope pairs its first five values along the rule's first
five binders. -/
theorem quotLift_W5 (henv : env.Ordered) (hEq : env.constants ``Eq = some eqConst)
    (hq : env.constants ``Quot = some quotConst) {u v : VLevel} (hu : u.WF U) (hv : v.WF U)
    {Γ₀ Γ : List VExpr} {τ τ' : VExpr.Subst}
    (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ' ((quotLiftBs u v).reverse ++ Γ)) :
    VEnv.Ctx.SubstEq env U Γ₀ (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1])
      (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1])
      (QuotRed.liftBinders.map (·.instL [u, v])).reverse := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  have teleE : env.IsTele U [] (quotLiftBs u v) := by
    have := (quotLiftTele hEq hq).instL hls; simpa [quotLiftBs] using this
  have onBs : OnCtx (quotLiftBs u v).reverse (env.IsType U) := by
    simpa using teleE.onCtx (Γ := []) trivial
  have onCs : OnCtx (quotTailCtx u v) (env.IsType U) := by
    have e := quotLiftBs_ctx u v []
    simp only [List.append_nil] at e
    rw [e] at onBs; exact onBs.1
  obtain ⟨Hh, eT⟩ := quotTailCtx_eq u v
  have Wτ' := Wτ
  rw [quotLiftBs_ctx] at Wτ'
  have := Ctx.SubstEq.vals henv onCs Wτ'.left.tail
  show VEnv.Ctx.SubstEq env U Γ₀ _ _ (quotTailCtx u v)
  rw [eT] at this ⊢
  simpa [quotTailCtx, eT, VExpr.bvars, VExpr.subst, Subst.tail, List.range, List.range.loop]
    using this

/-- `Quot.lift` at levels equivalent to `u v` on a major premise reducing to `Quot.mk` at `a`,
typed: it reduces to `f a`. -/
theorem quotLift_tred (henvW : env.WF) {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hdf : env.defeqs quotDefEq) (hEq : env.constants ``Eq = some eqConst)
    (hq : env.constants ``Quot = some quotConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) (hnp : ¬u ≈ .zero)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {τ : VExpr.Subst}
    (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ ((quotLiftBs u v).reverse ++ Γ))
    {ls₁ : List VLevel} (hls₁ : ∀ l ∈ ls₁, l.WF U) (h1 : List.Forall₂ (· ≈ ·) [u, v] ls₁)
    {a α' r' : VExpr} {ls₀ : List VLevel} (ha : env.HasType U Γ₀ a (τ 5))
    (Hq : StepS env U Γ₀ (τ 0) ((VExpr.const ``Quot.mk ls₀).appN [α', r', a]))
    (hqq : env.IsDefEq U Γ₀ ((VExpr.const ``Quot.mk [u]).appN [τ 5, τ 4, a]) (τ 0)
      (.app (.app (.const ``Quot [u]) (τ 5)) (τ 4))) :
    TRed env U Γ₀ ((VExpr.const ``Quot.lift ls₁).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0])
      (.app (τ 2) a) (τ 3) := by
  have hEo := henvW.ordered
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
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
  have W5 := quotLift_W5 hEo hEq hq hu hv Wτ
  have W6 : VEnv.Ctx.SubstEq env U Γ₀ (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1, a])
      (Subst.id.consList [τ 5, τ 4, τ 3, τ 2, τ 1, a])
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).reverse := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    refine .cons W5 (A := .bvar 4) (u := u) ?_ ?_
    · show env.HasType U (quotTailCtx u v) (.bvar 4) (.sort u)
      rw [eT]; exact .bvar (.succ (.succ (.succ (.succ .zero))))
    · simp only [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst]
      exact ha
  have Wc := quotLift_pair hq hu hv W5 hqq
  have tr := TRed.quotLift henvW hΓ₀ hdf hlift hu hv hnp (by simpa using W6) Wc Hq
  have hsp : env.IsDefEq U Γ₀ ((VExpr.const ``Quot.lift [u, v]).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0])
      ((VExpr.const ``Quot.lift ls₁).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0]) (τ 3) := by
    have := (quotLift_spine_defeq hEo hlift hu hv hls₁ h1 (Γ := Γ)).substDF hEo hΔ hΓ₀ Wτ
    simpa [quotLift_vals_subst, VExpr.subst] using this
  obtain ⟨u₁, v₁, rfl, e₁⟩ : ∃ u₁ v₁, ls₁ = [u₁, v₁] ∧ u ≈ u₁ := by
    cases h1 with | cons a h => cases h with | cons _ h => cases h; exact ⟨_, _, rfl, a⟩
  have hnq : ¬QuotProp [u₁, v₁] := by
    rintro ⟨u', v', e, h0⟩; cases e; exact hnp (Eq.trans e₁ h0)
  refine ⟨?_, hsp.symm.trans tr.2⟩
  have h2 := StepS.quotMajor (α := τ 5) (r := τ 4) (β := τ 3) (f := τ 2) (h := τ 1) hdf hnq Hq
  exact h2.trans (.single (Step.quot hdf hnq))

/-- `Quot.lift` at levels where the quotient is not a proposition, on a neutral normal form, is a
neutral normal form. -/
theorem quotLift_neutral (hU : StepUniq env) {Γ : List VExpr} (hdf : env.defeqs quotDefEq)
    {ls : List VLevel} {α r β f h e : VExpr} (hnq : ¬QuotProp ls)
    (We : WHNF env U Γ e) (Ne : Neutral env e) :
    WHNF env U Γ ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h, e]) ∧
      Neutral env ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h, e]) := by
  have hN : Neutral env (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e) :=
    .quot hdf hnq Ne
  refine ⟨fun e' H => ?_, hN⟩
  have K := Neutral.kStep hU hN H
  generalize hx : VExpr.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e = x at K
  revert hx
  cases K with
  | app K' =>
    intro hx; have h1 := (VExpr.app.inj hx).1; subst h1
    exact Step.quotHead_whnf hU hdf _ K'.step
  | proj => intro hx; cases hx
  | quotMajor _ _ K' =>
    intro hx; have h1 := (VExpr.app.inj hx).2; subst h1
    exact We _ K'.step
  | kQuot _ e2 hq =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hnq ⟨_, _, h1.2.1 ▸ e2, hq⟩
  | major r1 r2 =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hU.recQuot hdf r1 (List.getElem?_eq_some_iff.1 r2).1 h1.1.symm
  | kIota r1 _ r3 =>
    intro hx; have h1 := Lean4Lean.appN_const_inj (VExpr.app.inj hx).1
    exact hU.recQuot hdf r1 (List.getElem?_eq_some_iff.1 r3).1 h1.1.symm

/-- `Quot.lift` at levels equivalent to `u v`, applied to arguments typed along its first five
binders, is a function on the quotient. -/
theorem quotLift_head_typed (hlift : env.constants ``Quot.lift = some quotLiftConst)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {ls₁ : List VLevel} (hl₁ : ∀ l ∈ ls₁, l.WF U)
    (h₁ : List.Forall₂ (· ≈ ·) [u, v] ls₁) {Γ : List VExpr} {α r β f h : VExpr}
    (W5 : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h])
      (Subst.id.consList [α, r, β, f, h]) (QuotRed.liftBinders.map (·.instL [u, v])).reverse) :
    env.HasType U Γ ((VExpr.const ``Quot.lift ls₁).appN [α, r, β, f, h])
      (.forallE (.app (.app (.const ``Quot [u]) α) r) β.lift) := by
  have hc : env.IsDefEq U Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls₁)
      (quotLiftConst.type.instL [u, v]) :=
    .constDF hlift (by simp [hu, hv]) hl₁ rfl h₁
  rw [quotLiftConst_type_instL, quotLiftBs, List.map_append, VExpr.foralls_append] at hc
  have hc' := hc.hasType.2
  rw [← subst_id (e := VExpr.foralls _ _)] at hc'
  have := VEnv.IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := [])
    (as := [α, r, β, f, h]) (bs := [α, r, β, f, h]) hc' (by simp [QuotRed.liftBinders])
    (by simp [QuotRed.liftBinders]) (by simpa using W5)
  simp [VExpr.subst, Subst.consList, Subst.cons, Subst.lift, VExpr.instL, VLevel.inst,
    VExpr.lift] at this ⊢
  exact this

section
variable [ShapeEnv] [AxInterp]

/-- The inductive type shape of a quotient is `Quot`'s, with its one constructor `Quot.mk` of
one field. -/
theorem quotTy_head (hM : ModelEnv env) (hdf : env.defeqs quotDefEq) {ρ : Valuation} {u : VLevel}
    {A R : VExpr} {K : Nat} {r : Bool} {h : IndHead} {l : List (WShape K)}
    (haQ : LE_Interp env ρ (WShape.indTy r h l).T (.app (.app (.const ``Quot [u]) A) R)) :
    h = ⟨``Quot, 2, [``Quot.mk], [1]⟩ := by
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
  | quotTy hd' e2 e3 hl2 h5 h6 h7 h8 =>
    have hle := hyy.trans h8
    let N := max K n0
    have hK : K ≤ N := Nat.le_max_left ..; have hn : n0 ≤ N := Nat.le_max_right ..
    have hle' := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hK) (Nat.succ_le_succ hn)).1 hle
    simp only [WShape.lift_indTy hK, WShape.lift_indTy hn, WShape.indTy_le_indTy] at hle'
    exact hle'.2.1

omit [ShapeEnv] [AxInterp] in
/-- The quotient at equivalent levels and equal parameters is equal. -/
theorem quot_congr (hq : env.constants ``Quot = some quotConst) {Γ : List VExpr}
    {u u₀ : VLevel} (hu : u.WF U) (hu₀ : u₀.WF U) (e : u₀ ≈ u) {α α' r r' : VExpr}
    (hα : env.IsDefEq U Γ α' α (.sort u₀))
    (hr : env.IsDefEq U Γ r' r (.forallE α' (.forallE (α'.liftN 1) (.sort .zero)))) :
    env.IsDefEq U Γ (.app (.app (.const ``Quot [u₀]) α') r')
      (.app (.app (.const ``Quot [u]) α) r) (.sort u₀) := by
  have hle : VEnv.empty ≤ env := ⟨nofun, nofun, nofun⟩
  have T := (quotMkTele_isTele (u := u₀) hu₀).mono hle
  simp only [quotMkTele] at T
  cases T with | cons hA0 T =>
  cases T with | cons hA1 _ =>
  have ⟨_, h0⟩ := hA0; have ⟨_, h1⟩ := hA1
  have W : VEnv.Ctx.SubstEq env U Γ (Subst.id.consList [α', r']) (Subst.id.consList [α, r])
      ((quotMkTele u₀).take 2).reverse := by
    simp only [quotMkTele, List.take, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    refine .cons (.cons .nil h0 ?_) h1 ?_
    · simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst] using hα
    · simpa [Subst.consList, Subst.cons, Subst.head, Subst.tail, VExpr.subst, VExpr.Subst.lift,
        VExpr.liftN] using hr
  have hc : env.IsDefEq U Γ (.const ``Quot [u₀]) (.const ``Quot [u])
      (quotConst.type.instL [u₀]) :=
    .constDF hq (by simp [hu₀]) (by simp [hu]) rfl (.cons e .nil)
  rw [quot_type] at hc
  have := VEnv.IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := []) (As := (quotMkTele u₀).take 2)
    (as := [α', r']) (bs := [α, r]) (by rw [subst_id]; exact hc) rfl rfl (by simpa using W)
  simpa [quotMkTele, VExpr.subst, Subst.consList, Subst.cons, VExpr.appN] using this

omit [ShapeEnv] [AxInterp] in
/-- A context of types has well-formed levels. -/
theorem onCtx_levelWF {E : VEnv} : ∀ {Γ : List VExpr}, OnCtx Γ (E.IsType U) →
    OnCtx Γ fun _ A => A.LevelWF U
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨onCtx_levelWF h1, (h2.levelWF (onCtx_levelWF h1)).1⟩

/-- Related substitutions of a context with a first variable: the identity at the empty
valuation, or related substitutions of the rest at a valuation the variable's value extends. -/
theorem LR.SubstWF.cons_inv {henv : env.Ordered} {hU : StepUniq env} {Γ₀ Γ : List VExpr}
    {A : VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (A :: Γ) ρ) :
    (ρ = .nil ∧ Γ₀ = A :: Γ) ∨
      ∃ ρt x, ρ = ρt.push x ∧ LR.SubstWF (U := U) henv hU Γ₀ σ.tail σ'.tail Γ ρt := by
  cases W with
  | id => exact .inl ⟨rfl, rfl⟩
  | cons W' => exact .inr ⟨_, _, rfl, W'⟩

omit [AxInterp] in
/-- A constructor shape is typed only at an inductive type shape. -/
theorem WShape.HasType.ctor_inv {c : Name} {l : List (WShape n)} {hf} {a : WShape (n+1)}
    (H : (WShape.ctor c l hf).HasType a) : ∃ I as, a = .indTy true I as := by
  generalize em : WShape.ctor c l hf = m at H
  cases H.unfold with
  | ctor => exact ⟨_, _, rfl⟩
  | lam =>
    exfalso; revert em; unfold WShape.lam'; split <;> intro em <;> cases congrArg (·.1) em
  | _ => cases congrArg (·.1) em

variable {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- `Quot.lift`'s spine at a quotient that is not a proposition, at an interpretation that applies
`f` to the field of a `Quot.mk` shape of the major premise: the major premise is related to a
`Quot.mk` application, on which both sides reduce to `f` at related elements, or both are stuck. -/
theorem quotLift_caseQ (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀) (hEq₀ : E₀.constants ``Eq = some eqConst)
    (hq₀ : E₀.constants ``Quot = some quotConst)
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst) (hni : env.inducts ``Quot = none)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (HS : AdeqStmt (U := U) henv hU Γ₀ (.bvar 4 :: (quotTailCtx u v ++ Γ))
      (.app (.bvar 2) (.bvar 0)) (.app (.bvar 2) (.bvar 0)) (.bvar 3))
    (hnp : ¬u ≈ .zero) {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((quotLiftBs u v).reverse ++ Γ) ρ)
    {ls₁ ls₂ : List VLevel} (hl₁ : ∀ l ∈ ls₁, l.WF U) (hl₂ : ∀ l ∈ ls₂, l.WF U)
    (h₁ : List.Forall₂ (· ≈ ·) [u, v] ls₁) (h₂ : List.Forall₂ (· ≈ ·) [u, v] ls₂)
    {n : Nat} {m a : WShape n} (hma : m.HasType a) (ha : LE_Interp env ρ a.T (.bvar 3))
    {k : Nat} {a₀ : WShape k} {x f : WShape (k+1)} (hx : LE_Interp env ρ x.T (.bvar 0))
    (hf : LE_Interp env ρ f.T (.bvar 2)) (happ : AppS f.T [a₀.T] m.T)
    (hxle : (WShape.ctor' ``Quot.mk [a₀]).T ≤ x.T) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
      ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) m a := by
  have hEo := henvW.ordered
  have hq := hE₀le.constants hq₀
  have hEq := hE₀le.constants hEq₀
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  have hns := quotMk_not_struct hM hdf
  -- the context
  have teleE : env.IsTele U [] (quotLiftBs u v) := by
    have := (quotLiftTele hEq hq).instL hls; simpa [quotLiftBs] using this
  have onBs : OnCtx (quotLiftBs u v).reverse (env.IsType U) := by
    simpa using teleE.onCtx (Γ := []) trivial
  have hΔ : OnCtx ((quotLiftBs u v).reverse ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hEo VEnv.LE.rfl hΓ onBs
  obtain ⟨Hh, eT⟩ := quotTailCtx_eq u v
  have eΔ := quotLiftBs_ctx u v Γ
  rw [eT] at eΔ
  have L0 : Lookup ((quotLiftBs u v).reverse ++ Γ) 0
      (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)) := by
    rw [eΔ]; exact .zero
  have L3 : Lookup ((quotLiftBs u v).reverse ++ Γ) 3 (.sort v) := by
    rw [eΔ]; exact .succ (.succ (.succ .zero))
  have L5 : Lookup ((quotLiftBs u v).reverse ++ Γ) 5 (.sort u) := by
    rw [eΔ]; exact .succ (.succ (.succ (.succ (.succ .zero))))
  have hWE := W.toSubstEq hΓ₀
  have h5 : env.IsDefEq U Γ₀ (σ 5) (σ' 5) (.sort u) := by simpa [VExpr.subst] using hWE.lookup L5
  have h3 : env.IsDefEq U Γ₀ (σ 3) (σ' 3) (.sort v) := by simpa [VExpr.subst] using hWE.lookup L3
  -- the major premise's relation, at a constructor shape
  obtain ⟨n', x', aQ, -, hxx', hx', haQ, hty⟩ := (W.fits.lookup hM L0 (bvar_iff.1 hx)).out
  have H := LR.SubstWF.bvar hM W L0 (bvar_iff.1 hx') haQ hty
  simp only [VExpr.subst] at H
  let N := max k n'
  have hkN : k ≤ N := Nat.le_max_left ..
  have hnN : n' ≤ N + 1 := Nat.le_succ_of_le (Nat.le_max_right ..)
  have hle := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hkN) hnN).1 (hxle.trans hxx')
  simp only [WShape.T, WShape.lift_ctor' hkN] at hle
  obtain ⟨l', hf', hxe, hll⟩ := WShape.ctor'_le.1 hle (by simp [hns])
  have hty' := (WShape.HasType.lift hnN).2 hty
  rw [hxe] at hty'
  obtain ⟨I, as, haeq⟩ := WShape.HasType.ctor_inv hty'
  have haQ' := haQ.lift (n := N+1) hnN
  simp only [WShape.T] at haQ'
  rw [haeq] at haQ' hty'
  have hI := quotTy_head hM hdf haQ'
  subst hI
  have H' := (LR.DefEq.lift hnN hty).2 H
  rw [hxe, haeq] at H'
  simp only [LR, LRS, LRS.DefEq.ctor_indTy] at H'
  have hInQ : Inert env ``Quot := Inert.of_role hM.roles
    (fun hdf' e => henvW.rule_lhs_params hdf' e) (.quotTy hdf rfl) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  -- the spines are equal
  have hsp (ls : List VLevel) (hls' : ∀ l ∈ ls, l.WF U) (h : List.Forall₂ (· ≈ ·) [u, v] ls)
      {τ τ'} (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ' ((quotLiftBs u v).reverse ++ Γ)) :
      env.IsDefEq U Γ₀ ((VExpr.const ``Quot.lift [u, v]).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0])
        ((VExpr.const ``Quot.lift ls).appN [τ' 5, τ' 4, τ' 3, τ' 2, τ' 1, τ' 0]) (τ 3) := by
    have := (quotLift_spine_defeq hEo hlift hu hv hls' h (Γ := Γ)).substDF hEo hΔ hΓ₀ Wτ
    simpa [quotLift_vals_subst, VExpr.subst] using this
  have hD : env.IsDefEq U Γ₀ ((VExpr.const ``Quot.lift ls₁).appN [σ 5, σ 4, σ 3, σ 2, σ 1, σ 0])
      ((VExpr.const ``Quot.lift ls₂).appN [σ' 5, σ' 4, σ' 3, σ' 2, σ' 1, σ' 0]) (σ 3) :=
    (hsp ls₁ hl₁ h₁ hWE.left).symm.trans (hsp ls₂ hl₂ h₂ hWE)
  have hnq {ls : List VLevel} (h : List.Forall₂ (· ≈ ·) [u, v] ls) : ¬QuotProp ls := by
    rintro ⟨u', v', rfl, h0⟩
    cases h with | cons e _ => exact hnp (Eq.trans e h0)
  have hQσ : env.IsDefEq U Γ₀ (.app (.app (.const ``Quot [u]) (σ 5)) (σ 4))
      (.app (.app (.const ``Quot [u]) (σ' 5)) (σ' 4)) (.sort u) := by
    have eB : (quotLiftBs u v).reverse =
        .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3) :: quotTailCtx u v := by
      simpa using quotLiftBs_ctx u v []
    have DQ : env.HasType U (quotLiftBs u v).reverse
        (.app (.app (.const ``Quot [u]) (.bvar 5)) (.bvar 4)) (.sort u) := by
      have h0 := quotLift_majorTy (env := env) (U := U) hq hu hv
      have := h0.weakN hEo (.one (A := .app (.app (.const ``Quot [u]) (.bvar 4)) (.bvar 3)))
      rw [eB]
      simpa [quotTailCtx, List.map_reverse, VExpr.instL, VLevel.inst, VExpr.liftN] using this
    have := (IsDefEq.weak_closed hEo onBs DQ Γ).defeq.substDF hEo hΔ hΓ₀ hWE
    simpa [VExpr.subst] using this
  unfold LRS.IndVal at H'
  rw [if_neg (by simp [hns])] at H'
  rcases H' with H' | hA | ⟨-, hM1, hN1⟩
  · obtain ⟨-, -, -, i, kk, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, hi, hk, hci, hA, tM, tN, hfl,
      hFR, hP1, hP2⟩ := H'
    simp at hi; subst hi
    simp at hk; subst hk
    rw [hmk] at hci; cases hci
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf (hInQ.whnf (ls := [u]) (as := [σ 5, σ 4]))
      (show StepS env U Γ₀ ((VExpr.const ``Quot [u]).appN [σ 5, σ 4]) _ from hA))
    obtain ⟨p, rfl⟩ : ∃ p, l' = [p] := by
      match l', hfl with | [p], _ => exact ⟨p, rfl⟩
    rcases ms with _ | ⟨aₜ, _ | _⟩ <;> rcases ns with _ | ⟨aₜ', _ | _⟩ <;>
      simp only [FieldsRel] at hFR <;> try (simp at hFR; done)
    obtain ⟨D, B, b, g, hpv, hT, hpb, hmn, hrel, -⟩ := hFR
    have eT' : ∃ Y, ctorTeleAt quotMkConst 1 [u] [σ 5, σ 4] = .forallE (σ 5) Y := by
      rw [ctorTeleAt, show piCount quotMkConst.type = 3 from rfl, quotMk_type]
      simp [piInst, quotMkTele, VExpr.foralls, VExpr.inst, instVar, VExpr.inst_liftN]
    obtain ⟨Y, eTel⟩ := eT'
    rw [eTel] at hT
    cases StepS.of_whnf forallE_whnf' hT
    -- the constructor applications' levels and parameters
    have hlv := onCtx_levelWF hΓ₀
    have hlsW {ls₀ : List VLevel} {xs : List VExpr} {e A : VExpr}
        (h : env.IsDefEq U Γ₀ e ((VExpr.const ``Quot.mk ls₀).appN xs) A) : ∀ l ∈ ls₀, l.WF U := by
      have := (levelWF_appN.1 (h.levelWF hlv).2.1).1
      simpa [VExpr.LevelWF] using this
    obtain ⟨u₀, α', r', rfl, e₀, rfl, hα, hr⟩ := quotMk_params hni hq rfl (hlsW tM.2) hP1
    obtain ⟨u₀', α'', r'', rfl, e₀', rfl, hα', hr'⟩ := quotMk_params hni hq rfl (hlsW tN.2) hP2
    have hu₀ : u₀.WF U := hlsW tM.2 u₀ (by simp)
    have hu₀' : u₀'.WF U := hlsW tN.2 u₀' (by simp)
    have haₜ : env.HasType U Γ₀ aₜ (σ 5) := hmn.hasType.1
    have haₜ' : env.HasType U Γ₀ aₜ' (σ 5) := hmn.hasType.2
    -- `Quot.mk` at the major premise's level and parameters, at the quotient's
    have mk_at {u₁ : VLevel} (hu₁ : u₁.WF U) (e₁ : u₁ ≈ u) {α₁ r₁ a₁ : VExpr}
        (hα₁ : env.IsDefEq U Γ₀ α₁ (σ 5) (.sort u₁))
        (hr₁ : env.IsDefEq U Γ₀ r₁ (σ 4) (.forallE α₁ (.forallE (α₁.liftN 1) (.sort .zero))))
        (ha₁ : env.HasType U Γ₀ a₁ (σ 5)) :
        env.IsDefEq U Γ₀ ((VExpr.const ``Quot.mk [u₁]).appN [α₁, r₁, a₁])
          ((VExpr.const ``Quot.mk [u]).appN [σ 5, σ 4, a₁])
          (.app (.app (.const ``Quot [u]) (σ 5)) (σ 4)) :=
      .defeqDF (quot_congr hq hu hu₁ e₁ hα₁ hr₁)
        (quotMk_congr hmk hu hu₁ e₁ hα₁ hr₁ (.defeqDF hα₁.symm ha₁))
    -- the left side reduces to `f` at its field
    have t1 := quotLift_tred henvW hΓ₀ hdf hEq hq hlift hu hv hnp hΓ hWE.left hl₁ h₁ haₜ
      tM.1 ((tM.2.trans (mk_at hu₀ e₀ hα hr haₜ)).symm)
    -- the right side too, at the other substitution
    have L4 : Lookup ((quotLiftBs u v).reverse ++ Γ) 4
        (VExpr.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))) := by
      rw [eΔ]; exact .succ (.succ (.succ (.succ .zero)))
    have h4 : env.IsDefEq U Γ₀ (σ 4) (σ' 4)
        (.forallE (σ 5) (.forallE ((σ 5).liftN 1) (.sort .zero))) := by
      simpa [VExpr.subst, VExpr.Subst.lift, VExpr.liftN] using hWE.lookup L4
    have hmk' : env.IsDefEq U Γ₀ ((VExpr.const ``Quot.mk [u]).appN [σ 5, σ 4, aₜ'])
        ((VExpr.const ``Quot.mk [u]).appN [σ' 5, σ' 4, aₜ'])
        (.app (.app (.const ``Quot [u]) (σ 5)) (σ 4)) :=
      quotMk_congr hmk hu hu rfl h5 h4 haₜ'
    have t2 := quotLift_tred henvW hΓ₀ hdf hEq hq hlift hu hv hnp hΓ
      (W.symm.toSubstEq hΓ₀).left hl₂ h₂ (.defeqDF h5 haₜ') tN.1
      (.defeqDF hQσ ((tN.2.trans ((mk_at hu₀' e₀' hα' hr' haₜ').trans hmk')).symm))
    have t2' := t2.tyEq (.base h3.symm)
    -- the reducts are related by `f a`'s adequacy at the field
    refine ((LR _ _ _).whr t1 t2').2 ?_
    -- `x`'s argument, typed in the environment with `Quot`
    have teleR : E₀.IsTele U [] ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])) := by
      have := (quotTele hEq₀).instL hls; simpa using this
    have onR : OnCtx (.bvar 4 :: quotTailCtx u v) (E₀.IsType U) := by
      have := teleR.onCtx (Γ := []) trivial
      simpa [quotTailCtx, List.map_append, VExpr.instL] using this
    have D4 : E₀.IsDefEq U (quotTailCtx u v) (.bvar 4) (.bvar 4) (.sort u) := by
      rw [eT]; exact .bvar (.succ (.succ (.succ (.succ .zero))))
    have DS4 := IsDefEq.weak_closed hE₀o onR.1 D4 Γ
    have hΔt : OnCtx (quotTailCtx u v ++ Γ) (env.IsType U) :=
      OnCtx.append_closed hE₀o hE₀le hΓ onR.1
    have ihA : AdeqStmt (U := U) henv hU Γ₀ (quotTailCtx u v ++ Γ) (.bvar 4) (.bvar 4) (.sort u) :=
      LR.adequacy_of hM hE₀le hS hΓ₀ IH DS4 hΔt
    have W0 := W
    rw [quotLiftBs_ctx] at W0
    rcases W0.cons_inv with ⟨rfl, -⟩ | ⟨ρt, x0, rfl, W'⟩
    · have h0 := hxle.trans (bvar_iff.1 hx)
      have := TShape.le_bot.1 (h0.trans (TShape.le_bot.2 rfl))
      simp [WShape.ctor', hns] at this
      cases congrArg (·.1) this
    · have hb := quotTy_ctorTel_dom hM hdf hmk haQ' hpv
      have hb' : LE_Interp env ρt b.T (.bvar 4) :=
        (LE_Interp.weak_iff hM.closed).1 (show LE_Interp env (ρt.push x0) b.T (VExpr.bvar 4).lift
          from hb)
      have W2 := LR.Adequate.cons hM hΔt hΓ₀ (hS DS4).left.sound
        (fun hm ha hma => ihA hm ha hma) (DS4.defeq.mono hE₀le) hpb hb'
        (x := aₜ) (x' := aₜ') (by simpa [VExpr.subst, Subst.tail] using hmn)
        (by simpa [VExpr.subst, Subst.tail] using hrel) W'
      -- `f a` at the field's shape
      have hap : a₀.T ≤ p.T := by
        cases hll with | cons h _ =>
        exact (TShape.lift_eqv (a := a₀.T) hkN).2.trans (WShape.LE.T h)
      have hmS : LE_Interp env (ρt.push p.T) m.T (.app (.bvar 2) (.bvar 0)) := by
        cases happ with | cons h6 h7 h8 =>
        cases h8 with | nil h9 =>
        refine .app (.bvar ?_) (.bvar ?_) h9
        · exact h6.trans (by simpa [Valuation.push] using bvar_iff.1 hf)
        · simpa [Valuation.push] using h7.trans hap
      have haS : LE_Interp env (ρt.push p.T) a.T (.bvar 3) :=
        .bvar (by simpa [Valuation.push] using bvar_iff.1 ha)
      have r := ((HS hmS haS hma).1 W2).1
      simpa [VExpr.subst, Subst.cons, Subst.tail] using r
  · exact (NeRed.not_inert hU hInQ hA (ls := [u]) (As := [σ 5, σ 4]) .rfl).elim
  · -- both stuck: the spines are stuck
    have side {ls : List VLevel} (hls' : ∀ l ∈ ls, l.WF U) (h : List.Forall₂ (· ≈ ·) [u, v] ls)
        {τ : VExpr.Subst} (Wτ : VEnv.Ctx.SubstEq env U Γ₀ τ τ ((quotLiftBs u v).reverse ++ Γ))
        (hN : TNeRed env U Γ₀ (τ 0) (.app (.app (.const ``Quot [u]) (τ 5)) (τ 4))) :
        TNeRed env U Γ₀ ((VExpr.const ``Quot.lift ls).appN [τ 5, τ 4, τ 3, τ 2, τ 1, τ 0])
          (τ 3) := by
      obtain ⟨M₁, tM, wM, nM⟩ := hN
      have hh := quotLift_head_typed hlift hu hv hls' h (quotLift_W5 hEo hEq hq hu hv Wτ)
      have tr := TRed.quotMajor hdf (hnq h) hh tM
      rw [VExpr.inst_lift] at tr
      exact ⟨_, tr, (quotLift_neutral hU hdf (hnq h) wM nM).1,
        (quotLift_neutral hU hdf (hnq h) wM nM).2⟩
    have hInfo := LR.SubstWF.varTyInfo hM W L3 hv ha hma.isType
    refine reflect henv hU n hma.isType hma hInfo (side hl₁ h₁ hWE.left hM1) ?_ hD
    refine (side hl₂ h₂ (W.symm.toSubstEq hΓ₀).left ?_).tyEq (.base h3.symm)
    exact hN1.tyEq (.base hQσ)

/-- `Quot.lift`'s constant case, given adequacy's cases for an environment `E₀` with `Eq` and `Quot`
where `Quot.lift`'s telescope is typed, and model soundness for it. -/
theorem AdeqStmt.quotLift' (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀) (hEq₀ : E₀.constants ``Eq = some eqConst)
    (hq₀ : E₀.constants ``Quot = some quotConst)
    (hdf : env.defeqs quotDefEq) (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst) (hni : env.inducts ``Quot = none)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {ls' : List VLevel} (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) [u, v] ls') {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (quotLiftConst.type.instL [u, v]) := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
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
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const ``Quot.lift [u, v]) (.const ``Quot.lift ls')
      (quotLiftConst.type.instL [u, v]) :=
    AdeqStmt.quotLift hM henvW hΓ₀ hE₀le hE₀o hS IH hEq₀ hq₀ hdf hmk hlift hu hv hls' heq hΓ
      fun hnp {_ _ _} W {_ _} hl₁ hl₂ h₁ h₂ {_ _ _} hma ha {_ _ _ _} hx hf happ hxle =>
        quotLift_caseQ hM henvW hΓ₀ hE₀le hE₀o hS IH hEq₀ hq₀ hdf hmk hlift hni hu hv hΓ HS hnp W
          hl₁ hl₂ h₁ h₂ hma ha hx hf happ hxle
  exact @key

end

end LogRel
end Lean4Lean

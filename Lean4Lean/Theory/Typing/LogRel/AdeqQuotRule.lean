import Lean4Lean.Theory.Typing.LogRel.AdeqAssemble
import Lean4Lean.Theory.Typing.LogRel.Prefix
import Lean4Lean.Theory.Typing.InductiveLemmas

/-!
# The quotient's constants and rule in the logical relation

`Quot.ind` has no rule, so no role: it is related where it is interpreted, only at `bot`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

/-- `Quot.ind` computes nowhere: it has no role in any environment extending the quotient's. -/
theorem quotInd_noRole {ds : List VDecl} {E E' : VEnv} (hW : VEnv.WF' ds E)
    (h1 : E.addQuot = some E') (H : Extends E' env) :
    ∀ r k, ¬ConstArity env ``Quot.ind r k := by
  intro r k h
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
  obtain ⟨E₁, a1, E₂, a2, E₃, a3, E₄, a4, a5⟩ := h1
  cases a5
  have hfr : E.constants ``Quot.ind = none := by
    have := (VEnv.addConst_constants_iff a4).1
    refine VEnv.constants_none_of_le ?_ this
    exact (VEnv.addConst_le a1).trans ((VEnv.addConst_le a2).trans (VEnv.addConst_le a3))
  have hc' : (E₄.addDefEq quotDefEq).constants ``Quot.ind ≠ none := by
    show E₄.constants ``Quot.ind ≠ none
    rw [VEnv.addConst_self a4]; nofun
  have h' := H.constArity hc' h
  have hinds : (E₄.addDefEq quotDefEq).inducts = E.inducts :=
    (VEnv.addConst_inducts a4).trans <| (VEnv.addConst_inducts a3).trans <|
      (VEnv.addConst_inducts a2).trans (VEnv.addConst_inducts a1)
  have hE : E.WF := ⟨_, hW⟩
  cases h' with
  | delta hdf e =>
    rcases hdf with hdf | hdf
    · have : _ = quotDefEq := hdf; subst this
      obtain ⟨A, b, e'⟩ := StepUniqProof.quotDefEq_lhs; rw [e'] at e; cases e
    · rw [VEnv.addConst_defeqs a4, VEnv.addConst_defeqs a3, VEnv.addConst_defeqs a2,
        VEnv.addConst_defeqs a1] at hdf
      exact (ConstArity.delta hdf e).const hE hfr
  | indTy hs hT => exact (ConstArity.indTy (hinds ▸ hs) hT).const hE hfr
  | ctor hs hT hc e => exact (ConstArity.ctor (hinds ▸ hs) hT hc e).const hE hfr
  | recursor hs e hT => exact (ConstArity.recursor (hinds ▸ hs) e hT).const hE hfr
  | quotTy _ e => exact absurd e (by decide)
  | quotMk _ e => exact absurd e (by decide)
  | quotLift _ e => exact absurd e (by decide)

/-- `F` applied to a telescope's variables is its lift applied to the variables. -/
theorem etaSpine_eq : ∀ (Bs : List VExpr) (F : VExpr),
    etaSpine Bs F = (F.liftN Bs.length).appN (VExpr.bvars Bs.length 0)
  | [], F => by simp [etaSpine, VExpr.bvars]
  | B :: Bs, F => by
    show etaSpine Bs (.app F.lift (.bvar 0)) = _
    rw [etaSpine_eq Bs]
    have hb : VExpr.bvars (Bs.length + 1) 0 = .bvar Bs.length :: VExpr.bvars Bs.length 0 := by
      simp [VExpr.bvars, List.range_succ]
    simp only [List.length_cons, hb, VExpr.appN]
    congr 1
    show VExpr.app ((F.liftN 1).liftN Bs.length) ((VExpr.bvar 0).liftN Bs.length) = _
    rw [liftN_liftN, Nat.add_comm]; simp [VExpr.liftN]

/-- A closed term applied to a telescope's variables, substituted: the term applied to the
substitution's values. -/
theorem etaSpine_subst {F : VExpr} (hF : F.ClosedN) (Bs : List VExpr) (σ : VExpr.Subst) :
    (etaSpine Bs F).subst σ = F.appN ((VExpr.bvars Bs.length 0).map (·.subst σ)) := by
  rw [etaSpine_eq, subst_appN, hF.liftN_eq (Nat.zero_le _), hF.subst_eq .zero]

theorem StepS.appN (H : StepS env U Γ f f') :
    ∀ (as : List VExpr), StepS env U Γ (f.appN as) (f'.appN as)
  | [] => H
  | a :: as => StepS.appN H.app as

/-- A lambda telescope applied to as many arguments beta reduces to its body at them. -/
theorem StepS.lams_appN : ∀ {Bs : List VExpr} {as : List VExpr} {b : VExpr} {τ : VExpr.Subst},
    as.length = Bs.length →
    StepS env U Γ (((VExpr.lams Bs b).subst τ).appN as) (b.subst (τ.consList as))
  | [], [], _, _, _ => .rfl
  | B :: Bs, a :: as, b, τ, h => by
    have h' : as.length = Bs.length := by simpa using h
    show StepS env U Γ ((VExpr.app ((VExpr.lam B (VExpr.lams Bs b)).subst τ) a).appN as) _
    exact (StepS.appN StepS.beta_cons as).trans (StepS.lams_appN h')

theorem VExpr.bvars_succ_right (n : Nat) :
    VExpr.bvars (n+1) 0 = (VExpr.bvars n 1) ++ [.bvar 0] := by
  simp [VExpr.bvars, List.range_succ_eq_map, List.map_reverse, Function.comp_def]

theorem _root_.Lean4Lean.OnCtx.ctxClosed {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h, _, hA⟩ => ⟨OnCtx.ctxClosed henv h, (hA.closedN' henv.closed (OnCtx.ctxClosed henv h)).1⟩

/-- Related substitutions of a closed context followed by `Γ` restrict to the context, as the
values they give its variables. -/
theorem Ctx.SubstEq.vals {Γ₀ Γ : List VExpr} (henv : env.Ordered) :
    ∀ {Cs : List VExpr} {σ σ' : VExpr.Subst}, OnCtx Cs (env.IsType U) →
    VEnv.Ctx.SubstEq env U Γ₀ σ σ' (Cs ++ Γ) →
    VEnv.Ctx.SubstEq env U Γ₀ (Subst.id.consList ((VExpr.bvars Cs.length 0).map (·.subst σ)))
      (Subst.id.consList ((VExpr.bvars Cs.length 0).map (·.subst σ'))) Cs
  | [], _, _, _, _ => .nil
  | B :: Cs, σ, σ', ⟨hCs, u, hB⟩, W => by
    cases W with | cons W' _ h0 =>
    have IH := Ctx.SubstEq.vals henv hCs W'
    have e (s : VExpr.Subst) : (VExpr.bvars (Cs.length + 1) 0).map (·.subst s) =
        (VExpr.bvars Cs.length 0).map (·.subst s.tail) ++ [s 0] := by
      simp only [VExpr.bvars_succ_right, List.map_append, List.map_cons, List.map_nil]
      congr 1
      simp only [VExpr.bvars, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp [VExpr.subst, Subst.tail]
    simp only [List.length_cons]
    rw [e, e]
    have hcl : B.ClosedN Cs.length := by
      have := (hB.closedN' henv.closed (hCs.ctxClosed henv)).1
      simpa using this
    rw [Subst.consList_concat, Subst.consList_concat]
    refine .cons (by simpa [Subst.cons_tail] using IH) hB ?_
    simp only [Subst.cons_head, Subst.cons_tail]
    have e2 (s : VExpr.Subst) : B.subst (Subst.id.consList ((VExpr.bvars Cs.length 0).map (·.subst s.tail))) =
        B.subst s.tail := by
      refine hcl.subst_congr fun i hi => ?_
      rw [Subst.consList_lt _ _ _ (by simpa using hi)]
      simp [VExpr.bvars, VExpr.subst]
    rw [e2]; exact h0


/-- A derivation over a closed context, as a strong derivation over the context followed by any
other. -/
theorem IsDefEq.weak_closed {E : VEnv} (hEo : E.Ordered) {Δ : List VExpr}
    (hΔ : OnCtx Δ (E.IsType U)) {e1 e2 A : VExpr} (H : E.IsDefEq U Δ e1 e2 A) (Γ : List VExpr) :
    E.IsDefEqStrong U (Δ ++ Γ) e1 e2 A := by
  have hcl := H.closedN' hEo.closed (hΔ.ctxClosed hEo)
  have := (H.strong hEo hΔ).weakN hEo (Ctx.LiftN.right (hΔ.ctxClosed hEo) Γ)
  rwa [hcl.1.liftN_eq (Nat.le_refl _), hcl.2.1.liftN_eq (Nat.le_refl _),
    hcl.2.2.liftN_eq (Nat.le_refl _)] at this

theorem OnCtx.append_closed {E : VEnv} (hEo : E.Ordered) (hle : E ≤ env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) : ∀ {Δ : List VExpr}, OnCtx Δ (E.IsType U) →
    OnCtx (Δ ++ Γ) (env.IsType U)
  | [], _ => hΓ
  | _ :: _, ⟨hΔ, _, hA⟩ =>
    ⟨OnCtx.append_closed hEo hle hΓ hΔ, _, ((IsDefEq.weak_closed hEo hΔ hA Γ).defeq).mono hle⟩

/-- Substituting the values a substitution gives a closed term's variables, as a list, is
substituting by it. -/
theorem subst_vals {e : VExpr} {n : Nat} (he : e.ClosedN n) (σ : VExpr.Subst) :
    e.subst (Subst.id.consList ((VExpr.bvars n 0).map (·.subst σ))) = e.subst σ := by
  refine he.subst_congr fun i hi => ?_
  rw [Subst.consList_lt _ _ _ (by simpa using hi)]
  simp [VExpr.bvars, VExpr.subst]


section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}
/-- At the empty valuation a variable's application is interpreted only at `bot`. -/
theorem interp_nil_app_bvar {X : VExpr} {i n : Nat} {m : WShape n}
    (h : LE_Interp env .nil m.T (.app (.bvar i) X)) : m = .bot := by
  have key {k} {f : WShape (k+1)} {a : WShape k} (hf : LE_Interp env .nil f.T (.bvar i))
      (hle : m.T ≤ (f.app a).T) : m = .bot := by
    have hf' : f = .bot := by
      generalize e' : f.T = t' at hf
      cases hf with
      | bot => exact TShape.le_bot.1 (e' ▸ TShape.bot_eqv.1)
      | bvar h1 => exact TShape.le_bot.1 (e' ▸ h1.trans TShape.bot_le)
    subst hf'
    exact TShape.le_bot.1 ((WShape.bot_app ▸ hle).trans TShape.bot_eqv.1)
  generalize e : m.T = t at h
  cases h with
  | bot => exact TShape.le_bot.1 (e ▸ TShape.bot_eqv.1)
  | app hf _ hle => subst e; exact key hf hle

/-- Two terms are related where they reduce, under each related substitution, to instances of a
term `S` related to itself: `L` to `S` at `F σ` and `R` to `S` at `G σ`, where `F` and `G` keep
substitutions related and `A`. -/
theorem AdeqStmt.of_reds (hΓ : OnCtx Γ (env.IsType U)) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {L R S A : VExpr} {u : VLevel} (hA : env.HasType U Γ A (.sort u))
    (HS : AdeqStmt (U := U) henv hU Γ₀ Γ S S A)
    (hLS : ∀ {ρ n} {m : WShape n}, LE_Interp.Valuation.Fits env Γ₀ Γ ρ → LE_Interp env ρ m.T L →
      LE_Interp env ρ m.T S)
    (F G : VExpr.Subst → VExpr.Subst)
    (hFA : ∀ σ, A.subst (F σ) = A.subst σ) (hGA : ∀ σ, A.subst (G σ) = A.subst σ)
    (hF : ∀ {σ σ' ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ →
      LR.SubstWF (U := U) henv hU Γ₀ (F σ) (F σ') Γ ρ ∨
        ∀ {n} {m : WShape n}, LE_Interp env ρ m.T S → m = .bot)
    (hG : ∀ {σ σ' ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ →
      LR.SubstWF (U := U) henv hU Γ₀ (G σ) (G σ') Γ ρ)
    (hFG : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      LR.SubstWF (U := U) henv hU Γ₀ (F σ) (G σ) Γ ρ ∨
        ∀ {n} {m : WShape n}, LE_Interp env ρ m.T S → m = .bot)
    (redL : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      TRed env U Γ₀ (L.subst σ) (S.subst (F σ)) (A.subst σ))
    (redR : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      TRed env U Γ₀ (R.subst σ) (S.subst (G σ)) (A.subst σ)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ L R A := by
  intro ρ n m a hm ha hmem
  refine .fits fun hfit => ?_
  have ad := HS (hLS hfit hm) ha hmem
  have hAσ {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
      env.IsDefEq U Γ₀ (A.subst σ') (A.subst σ) (.sort u) :=
    (hA.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)).symm
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · have r1 := redL W.left
    have r2 := (redL W.symm.left).tyEq (.base (hAσ W))
    refine ((LR _ _ _).whr r1 r2).2 ?_
    rcases hF W with W2 | hb
    · have := ((ad.1 W2).1)
      rwa [hFA] at this
    · cases hb (hLS hfit hm); exact (LR _ _ _).bot hmem.isType
  · have r1 := redR W.left
    have r2 := (redR W.symm.left).tyEq (.base (hAσ W))
    refine ((LR _ _ _).whr r1 r2).2 ?_
    have := ((HS (hLS hfit hm) ha hmem).1 (hG W)).1
    rwa [hGA] at this
  · have r1 := redL W
    have r2 := redR W
    refine ((LR _ _ _).whr r1 r2).2 ?_
    rcases hFG W with W2 | hb
    · have := (ad.1 W2).1
      rwa [hFA] at this
    · cases hb (hLS hfit hm); exact (LR _ _ _).bot hmem.isType


/-- Related substitutions with their head values replaced by equal values, where the head
variable's values are only `bot`: what a proof's position allows. Unless the substitutions are the
identity on `Γ₀`, at the empty valuation. -/
theorem LR.SubstWF.replaceHead {Γ : List VExpr} {A : VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (A :: Γ) ρ) {x x' : VExpr}
    (hx : env.IsDefEq U Γ₀ x x' (A.subst σ.tail))
    (hbot : ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (.bvar 0) → m = .bot) :
    LR.SubstWF (U := U) henv hU Γ₀ (σ.tail.cons x) (σ'.tail.cons x') (A :: Γ) ρ ∨ ρ = .nil := by
  cases W with
  | id => exact .inr rfl
  | cons W' h1 h2 h3 hA h0 =>
    refine .inl (.cons (by simpa [Subst.cons_tail] using W') h1 h2 h3 hA
      ⟨by simpa [Subst.cons_tail] using hx, fun _ a ha => ⟨?_, fun m hm hmem => ?_⟩⟩)
    · simpa [Subst.cons_tail] using (h0.2 a ha).1
    · cases hbot hm; exact (LR _ _ _).bot hmem.isType
end

/-- The quotient rule's binders are a telescope in an environment with `Eq`. -/
theorem quotTele {E : VEnv} (hEq : E.constants ``Eq = some eqConst) :
    E.IsTele 2 [] (QuotRed.liftBinders ++ [VExpr.bvar 4]) := by
  simp only [QuotRed.liftBinders, List.cons_append, List.nil_append]
  refine .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <|
    .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ .nil

/-- The quotient rule's right body is typed in an environment with `Eq`. -/
theorem quotRb_typed {E : VEnv} (hEq : E.constants ``Eq = some eqConst) :
    E.HasType 2 (QuotRed.liftBinders ++ [VExpr.bvar 4]).reverse (.app (.bvar 2) (.bvar 0))
      (.bvar 3) := by
  simp only [QuotRed.liftBinders, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil]
  type_tac

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}


/-- A term is related at a closed pi telescope typed in an environment `E₀` where adequacy's cases
hold, wherever its application to the telescope's variables is: the telescope's types are
related by adequacy for `E₀`. -/
theorem AdeqStmt.etaLams_closed (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {E₀ : VEnv}
    (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀) {Bs : List VExpr} (hT : E₀.IsTele U [] Bs)
    {Γ : List VExpr} {F F' R : VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hR : E₀.IsType U Bs.reverse R)
    (H : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) (etaSpine Bs F) (etaSpine Bs F') R) :
    AdeqStmt (U := U) henv hU Γ₀ Γ F F' (.foralls Bs R) := by
  have onBs : OnCtx Bs.reverse (E₀.IsType U) := by simpa using hT.onCtx (Γ := []) trivial
  let P : List VExpr → VExpr → Prop := fun Γ' T =>
    ∃ Δ, Γ' = Δ ++ Γ ∧ OnCtx Δ (E₀.IsType U) ∧ E₀.IsType U Δ T
  have hP : ∀ {Γ' A B}, P Γ' (.forallE A B) → P Γ' A ∧ P (A::Γ') B := by
    rintro Γ' A B ⟨Δ, rfl, hΔ, hT⟩
    obtain ⟨h1, h2⟩ := VEnv.IsType.forallE_inv hE₀o hT
    exact ⟨⟨Δ, rfl, hΔ, h1⟩, ⟨A::Δ, rfl, ⟨hΔ, h1⟩, h2⟩⟩
  have hTy : ∀ {Γ' T}, OnCtx Γ' (env.IsType U) → P Γ' T → ∃ w, env.HasType U Γ' T (.sort w) ∧
      StrongSoundEq env U Γ' T T (.sort w) ∧ AdeqStmt (U := U) henv hU Γ₀ Γ' T T (.sort w) := by
    rintro Γ' T hΓ' ⟨Δ, rfl, hΔ, w, hT⟩
    have D := IsDefEq.weak_closed hE₀o hΔ hT Γ
    exact ⟨w, D.defeq.mono hE₀le, hS D, LR.adequacy_of hM hE₀le hS hΓ₀ IH D hΓ'⟩
  have hPT : P Γ (.foralls Bs R) := ⟨[], rfl, trivial, by simpa using hT.foralls (B := R) (by simpa using hR)⟩
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ F F' (.foralls Bs R) :=
    AdeqStmt.etaLams hM hΓ₀ P hP hTy Bs hΓ hPT @H
  exact @key

/-- The quotient's rule is related where its sides are interpreted: both sides compute to `f a`
(`f` at a chosen proof where the quotient is a proposition) under related substitutions of its
binders, whose types, like `f a`, are typed before the quotient, where adequacy holds. -/
theorem quotRule_adeq (henvW : env.WF) (hM : ModelEnv env) {E E' : VEnv} (hEE : E ≤ E')
    (hE'le : E' ≤ env) (hEo : E.Ordered) (hE'o : E'.Ordered) (hEq : E.constants ``Eq = some eqConst)
    (hS : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E Γ₀)
    (hdf : E'.defeqs quotDefEq) (hq : E'.constants ``Quot = some quotConst)
    (hmk : E'.constants ``Quot.mk = some quotMkConst)
    (hlift : E'.constants ``Quot.lift = some quotLiftConst)
    {Γ : List VExpr} {u v : VLevel} (hΓ : OnCtx Γ (env.IsType U)) (hu : u.WF U) (hv : v.WF U) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (quotDefEq.lhs.instL [u, v]) (quotDefEq.rhs.instL [u, v])
      (quotDefEq.type.instL [u, v]) := by
  obtain ⟨hL, hR, hT⟩ := quotDefEq_instL u v
  rw [hL, hR, hT]
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  generalize hBs : (QuotRed.liftBinders ++ [VExpr.bvar 4]).map (VExpr.instL [u, v]) = Bs
  have teleE : E.IsTele U [] Bs := by
    have := (quotTele hEq).instL hls; simpa [← hBs] using this
  have onBs : OnCtx Bs.reverse (E.IsType U) := by simpa using teleE.onCtx (Γ := []) trivial
  let P : List VExpr → VExpr → Prop := fun Γ' T =>
    ∃ Δ, Γ' = Δ ++ Γ ∧ OnCtx Δ (E.IsType U) ∧ E.IsType U Δ T
  have hP : ∀ {Γ' A B}, P Γ' (.forallE A B) → P Γ' A ∧ P (A::Γ') B := by
    rintro Γ' A B ⟨Δ, rfl, hΔ, hT⟩
    obtain ⟨h1, h2⟩ := VEnv.IsType.forallE_inv hEo hT
    exact ⟨⟨Δ, rfl, hΔ, h1⟩, ⟨A::Δ, rfl, ⟨hΔ, h1⟩, h2⟩⟩
  -- a derivation in `E` over a closed context, weakened to the context followed by `Γ`
  have weakE {Δ e1 e2 A} (hΔ : OnCtx Δ (E.IsType U)) (H : E.IsDefEq U Δ e1 e2 A) :
      E.IsDefEqStrong U (Δ ++ Γ) e1 e2 A := by
    have hcl := H.closedN' hEo.closed (hΔ.ctxClosed hEo)
    have := (H.strong hEo hΔ).weakN hEo (Ctx.LiftN.right (hΔ.ctxClosed hEo) Γ)
    rwa [hcl.1.liftN_eq (Nat.le_refl _), hcl.2.1.liftN_eq (Nat.le_refl _),
      hcl.2.2.liftN_eq (Nat.le_refl _)] at this
  have adeqE {Δ e1 e2 A} (hΔ : OnCtx Δ (E.IsType U)) (hΓ' : OnCtx (Δ ++ Γ) (env.IsType U))
      (H : E.IsDefEq U Δ e1 e2 A) : AdeqStmt (U := U) henv hU Γ₀ (Δ ++ Γ) e1 e2 A :=
    LR.adequacy_of hM (hEE.trans hE'le) (fun D => hS (D.mono hEE)) hΓ₀ IH (weakE hΔ H) hΓ'
  have hTy : ∀ {Γ' T}, OnCtx Γ' (env.IsType U) → P Γ' T → ∃ w, env.HasType U Γ' T (.sort w) ∧
      StrongSoundEq env U Γ' T T (.sort w) ∧
      AdeqStmt (U := U) henv hU Γ₀ Γ' T T (.sort w) := by
    rintro Γ' T hΓ' ⟨Δ, rfl, hΔ, w, hT⟩
    exact ⟨w, ((weakE hΔ hT).defeq).mono (hEE.trans hE'le), hS ((weakE hΔ hT).mono hEE),
      adeqE hΔ hΓ' hT⟩
  have hEnvo : env.Ordered := henvW.ordered
  have hΓ' : OnCtx (Bs.reverse ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hEo (hEE.trans hE'le) hΓ onBs
  have hRb : E.HasType U Bs.reverse (.app (.bvar 2) (.bvar 0)) (.bvar 3) := by
    have := (quotRb_typed hEq).instL hls
    simpa [← hBs, List.map_reverse, VExpr.instL] using this
  have hβ : E.IsType U Bs.reverse (.bvar 3) := hRb.isType hEo onBs
  have hPT : P Γ (.foralls Bs (.bvar 3)) :=
    ⟨[], rfl, trivial, by simpa using teleE.foralls (B := .bvar 3) (by simpa using hβ)⟩
  apply AdeqStmt.etaLams hM hΓ₀ P hP hTy Bs hΓ hPT
  -- the rule's sides are closed
  have hext : E'.IsDefEq U [] (.lams Bs (quotL u v)) (.lams Bs (.app (.bvar 2) (.bvar 0)))
      (.foralls Bs (.bvar 3)) := by
    have := VEnv.IsDefEq.extra (Γ := []) (uvars := U) hdf hls rfl
    rwa [hL, hR, hT, hBs] at this
  have hcl := hext.closedN' hE'o.closed trivial
  have hBsr : ∃ Hh, Bs.reverse = [.bvar 4, Hh, .forallE (.bvar 2) (.bvar 1), .sort v,
      .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort u] := by
    subst hBs
    exact ⟨.forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))), by simp [QuotRed.liftBinders, VExpr.instL, VLevel.inst]⟩
  obtain ⟨Hh, hBsr⟩ := hBsr
  have hlen : Bs.length = 6 := by simpa using congrArg List.length hBsr
  have hEenv : E ≤ env := hEE.trans hE'le
  have onBsEnv : OnCtx Bs.reverse (env.IsType U) :=
    onBs.mono fun ⟨w, h⟩ => ⟨w, h.mono hEenv⟩
  have hΓ' : OnCtx (Bs.reverse ++ Γ) (env.IsType U) := OnCtx.append_closed hEo hEenv hΓ onBs
  obtain ⟨w₃, hβw⟩ := hβ
  have hA : env.HasType U (Bs.reverse ++ Γ) (.bvar 3) (.sort w₃) :=
    ((IsDefEq.weak_closed hEo onBs hβw Γ).defeq).mono hEenv
  have HS : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 2) (.bvar 0)) (.bvar 3) := by exact adeqE onBs hΓ' hRb
  have hRbcl : (VExpr.app (.bvar 2) (.bvar 0)).ClosedN Bs.length := by
    simpa using (hRb.closedN' hEo.closed (onBs.ctxClosed hEo)).1
  have hLbcl : (quotL u v).ClosedN Bs.length := by
    rw [hlen]; simp [quotL, VExpr.ClosedN, VExpr.appN]
  have hdfE : env.defeqs quotDefEq := hE'le.defeqs hdf
  have hBody := VEnv.quotBodyWF (hEenv.constants hEq) (hE'le.constants hmk) (hE'le.constants hlift)
  -- the rule's bodies at the values of related substitutions
  have body {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :=
    VEnv.IsDefEq.extra_body hEnvo hΓ₀ hdfE hBody hls rfl
      (as := (VExpr.bvars Bs.length 0).map (·.subst σ)) (by simp [VExpr.bvars, ← hBs])
      (by have := Ctx.SubstEq.vals hEnvo onBsEnv (W.toSubstEq hΓ₀).left
          simpa [hBs] using this)
  have hvl (σ : VExpr.Subst) : ((VExpr.bvars Bs.length 0).map (·.subst σ)).length = Bs.length := by
    simp [VExpr.bvars]
  have h3cl : (VExpr.bvar 3).ClosedN Bs.length := by rw [hlen]; simp [VExpr.ClosedN]
  have redR {σ ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ (Bs.reverse ++ Γ) ρ) :
      TRed env U Γ₀ ((etaSpine Bs (.lams Bs (.app (.bvar 2) (.bvar 0)))).subst σ)
        ((VExpr.app (.bvar 2) (.bvar 0)).subst σ) ((VExpr.bvar 3).subst σ) := by
    obtain ⟨-, -, h3⟩ := body W
    rw [etaSpine_subst hcl.2.1]
    refine ⟨?_, ?_⟩
    · have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs)
        (b := .app (.bvar 2) (.bvar 0)) (τ := .id) (hvl σ)
      rwa [subst_id, subst_vals hRbcl] at this
    · rw [hR, hBs] at h3
      simpa [VExpr.instL, subst_vals hRbcl, subst_vals h3cl] using h3
  -- the left side's spine is the right body, in `E'`
  have onBsE' : OnCtx Bs.reverse (E'.IsType U) := onBs.mono fun ⟨w, h⟩ => ⟨w, h.mono hEE⟩
  have hLR : E'.IsDefEq U Bs.reverse ((VExpr.lams Bs (quotL u v)).appN (VExpr.bvars Bs.length 0))
      (.app (.bvar 2) (.bvar 0)) (.bvar 3) := by
    have hBody' := VEnv.quotBodyWF (hEE.constants hEq) hmk hlift
    have W := Ctx.SubstEq.vals (Γ := []) hE'o onBsE' (by simpa using VEnv.Ctx.SubstEq.id hE'o onBsE')
    simp only [subst_id, List.map_id'] at W
    obtain ⟨h1, h2, -⟩ := VEnv.IsDefEq.extra_body hE'o onBsE' hdf hBody' hls rfl
      (as := VExpr.bvars Bs.length 0) (by simp [VExpr.bvars, ← hBs]) (by simpa [hBs] using W)
    rw [hL, hBs] at h1
    have e1 := subst_vals hLbcl .id
    have e2 := subst_vals hRbcl .id
    have e3 := subst_vals h3cl .id
    simp only [subst_id, List.map_id'] at e1 e2 e3
    have h12 := h1.trans h2
    simp only [VExpr.instL] at h12
    rwa [e2, e3] at h12
  have hLS {ρ n} {m : WShape n} (hfit : LE_Interp.Valuation.Fits env Γ₀ (Bs.reverse ++ Γ) ρ)
      (hm : LE_Interp env ρ m.T (etaSpine Bs (.lams Bs (quotL u v)))) :
      LE_Interp env ρ m.T (.app (.bvar 2) (.bvar 0)) := by
    have D := IsDefEq.weak_closed hE'o onBsE' hLR Γ
    rw [etaSpine_eq, hcl.1.liftN_eq (Nat.zero_le _)] at hm
    exact ((hS D).sound hfit).1 hm
  -- the left side at a related substitution, computed to its rule body
  have lsteps {σ : VExpr.Subst} : StepS env U Γ₀ ((etaSpine Bs (.lams Bs (quotL u v))).subst σ)
      ((quotL u v).subst σ) := by
    rw [etaSpine_subst hcl.1]
    have := StepS.lams_appN (env := env) (U := U) (Γ := Γ₀) (Bs := Bs)
      (b := quotL u v) (τ := .id) (hvl σ)
    rwa [subst_id, subst_vals hLbcl] at this
  have ldefeq {σ ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ (Bs.reverse ++ Γ) ρ) :
      env.IsDefEq U Γ₀ ((etaSpine Bs (.lams Bs (quotL u v))).subst σ)
        ((VExpr.app (.bvar 2) (.bvar 0)).subst σ) ((VExpr.bvar 3).subst σ) := by
    obtain ⟨h1, h2, -⟩ := body W
    have h12 := h1.trans h2
    rw [hL, hBs] at h12
    simp only [VExpr.instL] at h12
    rw [etaSpine_subst hcl.1]
    rwa [subst_vals hRbcl, subst_vals h3cl] at h12
  have quotL_subst (σ : VExpr.Subst) : (quotL u v).subst σ =
      .app ((VExpr.const ``Quot.lift [u, v]).appN [σ 5, σ 4, σ 3, σ 2, σ 1])
        ((VExpr.const ``Quot.mk [u]).appN [σ 5, σ 4, σ 0]) := by
    simp [quotL, VExpr.subst, VExpr.appN]
  rcases Classical.em (u ≈ VLevel.zero) with hp | hp
  · -- the major premise is a proof: `Quot.lift` computes at a chosen element
    have eΓ : Bs.reverse ++ Γ = .bvar 4 :: ([Hh, .forallE (.bvar 2) (.bvar 1), .sort v,
        .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort u] ++ Γ) := by
      rw [hBsr]; rfl
    have L0 : Lookup (Bs.reverse ++ Γ) 0 (.bvar 5) := by rw [eΓ]; exact .zero
    have L5 : Lookup (Bs.reverse ++ Γ) 5 (.sort u) := by
      rw [eΓ]; exact .succ (.succ (.succ (.succ (.succ .zero))))
    have L2 : Lookup (Bs.reverse ++ Γ) 2 (.forallE (.bvar 5) (.bvar 4)) := by
      rw [eΓ]; exact .succ (.succ .zero)
    have h0 {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        env.IsDefEq U Γ₀ (σ 0) (σ' 0) (σ 5) := (W.toSubstEq hΓ₀).lookup L0
    have h5 {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        env.IsDefEq U Γ₀ (σ 5) (σ' 5) (.sort u) := (W.toSubstEq hΓ₀).lookup L5
    have hP0 {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        env.HasType U Γ₀ (σ 5) (.sort .zero) :=
      .defeqDF (.sortDF hu (by trivial) hp) (h5 W).hasType.1
    have hw {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        env.HasType U Γ₀ (quotWit env U Γ₀ (σ 5)) (σ 5) := quotWit_spec (h0 W).hasType.1
    -- the proof variable's values are `bot`
    have hbot {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ)
        {n} {m : WShape n} (hm : LE_Interp env ρ m.T (.bvar 0)) : m = .bot := by
      have D0 : E.IsDefEq U Bs.reverse (.bvar 0) (.bvar 0) (.bvar 5) := by
        refine .bvar ?_; rw [hBsr]; exact .zero
      have D5 : E.IsDefEq U Bs.reverse (.bvar 5) (.bvar 5) (.sort u) := by
        refine .bvar ?_; rw [hBsr]; exact .succ (.succ (.succ (.succ (.succ .zero))))
      have S0 := hS ((IsDefEq.weak_closed hEo onBs D0 Γ).mono hEE)
      have S5 := hS ((IsDefEq.weak_closed hEo onBs D5 Γ).mono hEE)
      have hr : levelRel u = false := by simp [levelRel, hp]
      exact TShape.le_bot.1 (StrongSound.proof_le_bot' S0.left S5.left hr W.fits hm)
    have shiftW {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ) :
        LR.SubstWF (U := U) henv hU Γ₀ σ σ' (.bvar 4 :: ([Hh, .forallE (.bvar 2) (.bvar 1),
          .sort v, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort u] ++ Γ)) ρ :=
      eΓ ▸ W
    have unshiftW {σ σ' ρ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' (.bvar 4 :: ([Hh,
        .forallE (.bvar 2) (.bvar 1), .sort v, .forallE (.bvar 0) (.forallE (.bvar 1)
        (.sort .zero)), .sort u] ++ Γ)) ρ) :
        LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ) ρ := eΓ ▸ W
    have hcons (σ : VExpr.Subst) : σ.tail.cons (σ 0) = σ := by
      funext i; cases i <;> rfl
    intro ρ₀ n₀ m₀ a₀ hm₀ ha₀ hmem₀
    refine AdeqStmt.of_reds (S := .app (.bvar 2) (.bvar 0)) hΓ' hΓ₀ hA HS hLS
      (fun σ => σ.tail.cons (quotWit env U Γ₀ (σ 5))) id (fun _ => rfl) (fun _ => rfl)
      (fun {σ σ' _} W => ?_) (fun W => W) (fun {σ _} W => ?_) (fun {σ _} W => ?_) redR hm₀ ha₀ hmem₀
    · rcases LR.SubstWF.replaceHead (shiftW W) (x := quotWit env U Γ₀ (σ 5))
        (x' := quotWit env U Γ₀ (σ' 5))
        (.proofIrrel (hP0 W) (hw W) (.defeqDF (h5 W).symm (hw W.symm))) (hbot W) with W2 | e
      · exact .inl (unshiftW W2)
      · subst e; exact .inr interp_nil_app_bvar
    · have := LR.SubstWF.replaceHead (shiftW W) (x := quotWit env U Γ₀ (σ 5))
        (x' := σ 0) (.proofIrrel (hP0 W) (hw W) (h0 W).hasType.1) (hbot W)
      rw [hcons] at this
      rcases this with W2 | e
      · exact .inl (unshiftW W2)
      · subst e; exact .inr interp_nil_app_bvar
    · refine ⟨lsteps.trans (.single ?_), ?_⟩
      · rw [quotL_subst]; exact Step.kQuot hdfE rfl hp (hw W)
      · refine (ldefeq W).trans ?_
        have hf := (W.toSubstEq hΓ₀).lookup L2
        have := VEnv.IsDefEq.appDF hf.hasType.1 (.proofIrrel (hP0 W) (h0 W).hasType.1 (hw W))
        have e : (σ.lift 4).inst (σ 0) = σ 3 := by
          simp [Subst.lift, inst_lift]
        simp only [VExpr.subst] at this
        rw [e] at this
        exact this
  · have hnq : ¬QuotProp [u, v] := by rintro ⟨u', v', e, h0⟩; cases e; exact hp h0
    intro ρ₀ n₀ m₀ a₀ hm₀ ha₀ hmem₀
    refine AdeqStmt.of_reds hΓ' hΓ₀ hA HS hLS id id (fun _ => rfl) (fun _ => rfl)
      (fun W => .inl W) (fun W => W) (fun W => .inl W) ?_ redR hm₀ ha₀ hmem₀
    intro σ ρ W
    refine ⟨lsteps.trans (.single ?_), ldefeq W⟩
    rw [quotL_subst]
    exact Step.quot hdfE hnq

end

/-- What adding the quotient declares. -/
theorem addQuot_facts {E E' : VEnv} (h : E.addQuot = some E') :
    E'.constants ``Quot = some quotConst ∧ E'.constants ``Quot.mk = some quotMkConst ∧
    E'.constants ``Quot.lift = some quotLiftConst ∧ E'.constants ``Quot.ind = some quotIndConst ∧
    E'.defeqs quotDefEq := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨E₁, a1, E₂, a2, E₃, a3, E₄, a4, a5⟩ := h
  cases a5
  have l4 := VEnv.addConst_le a4
  have l3 := VEnv.addConst_le a3
  have l2 := VEnv.addConst_le a2
  exact ⟨VEnv.addDefEq_le.constants (l4.constants (l3.constants (l2.constants
      (VEnv.addConst_self a1)))),
    VEnv.addDefEq_le.constants (l4.constants (l3.constants (VEnv.addConst_self a2))),
    VEnv.addDefEq_le.constants (l4.constants (VEnv.addConst_self a3)),
    VEnv.addDefEq_le.constants (VEnv.addConst_self a4), .inl rfl⟩

/-- The quotient's step to adequacy's environment cases, given the cases of its constants: its
rule's case is `quotRule_adeq`. -/
theorem QuotStep.of_consts
    (Hc : ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
      ∀ (X : @AxInterp env.shapeEnv) {ds E E'}, @AxOK env.shapeEnv X →
      @DomRole env.shapeEnv X env → VEnv.WF' ds E →
      E.Inj → E.QuotReady → E.addQuot = some E' → Extends E' env →
      (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
      ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → (c, ci) ∈ quotConsts →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const c ls) (.const c ls') (ci.type.instL ls)) :
    QuotStep := by
  refine QuotStep.of Hc ?_
  intro env henvW U Γ₀ hΓ₀ X ds E E' hX hXD hW _ hQR h1 hext hdom IH Γ ls u hΓ hls hlen _ _ _ _ _ _ _ _
  letI := env.shapeEnv; letI := X
  have hD : VDecl.WF E .quot E' := .quot hQR h1
  have hW' : VEnv.WF' (.quot :: ds) E' := .decl hD hW
  have hle := hext.le
  have hMX := henvW.modelEnv hX hXD
  have hnd : NoDom E' := fun hdf e hx => VEnv.WF.rule_head ⟨_, hW'⟩ hdf e (hdom _ hx)
  have hS : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    fun D => (soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hW' hle hnd
      (VEnv.WF.noDomI ⟨_, hW'⟩ hdom)).strongSound
      hMX hle D
  obtain ⟨hq, hmk, hlift, -, hdf⟩ := addQuot_facts h1
  match ls, hlen with
  | [u', v'], _ =>
  have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
      (quotDefEq.lhs.instL [u', v']) (quotDefEq.rhs.instL [u', v'])
      (quotDefEq.type.instL [u', v']) := by
   exact quotRule_adeq henvW hMX hD.le hle (VEnv.WF.ordered ⟨_, hW⟩) (VEnv.WF.ordered ⟨_, hW'⟩)
    hQR hS hΓ₀ IH hdf hq hmk hlift hΓ (hls _ List.mem_cons_self)
    (hls _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact @key

/-- The quotient's step to adequacy's environment cases, given the cases of `Quot`, `Quot.mk` and
`Quot.lift`: `Quot.ind` has no role, and the rule's case is `quotRule_adeq`. -/
theorem QuotStep.of_three
    (Hc : ∀ {env : VEnv} (henvW : env.WF) {U : Nat} {Γ₀ : List VExpr}, OnCtx Γ₀ (env.IsType U) →
      ∀ (X : @AxInterp env.shapeEnv) {ds E E'}, @AxOK env.shapeEnv X → VEnv.WF' ds E →
      E.Inj → E.QuotReady → E.addQuot = some E' → Extends E' env →
      (∀ c, X.dom c → E'.constants c = none) →
      @AdequacyHyps env U env.shapeEnv X henvW.ordered henvW.stepUniq E Γ₀ →
      ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) → (c, ci) ∈ quotConsts → c ≠ ``Quot.ind →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const c ls) (.const c ls') (ci.type.instL ls)) :
    QuotStep := by
  refine QuotStep.of_consts ?_
  intro env henvW U Γ₀ hΓ₀ X ds E E' hX _ hW hI hQR h1 hext hdom IH Γ c ci ls ls' u hΓ hm
    hls hls' hlen heq hu h7 h8 hA
  letI := env.shapeEnv; letI := X
  rcases Classical.em (c = ``Quot.ind) with hc | hc
  · subst hc
    have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const ``Quot.ind ls) (.const ``Quot.ind ls') (ci.type.instL ls) := by
      exact AdeqStmt.noRole (quotInd_noRole hW h1 hext) fun hx => by
        have h := hdom _ hx; rw [(addQuot_facts h1).2.2.2.1] at h; cases h
    exact @key
  · have key : @AdeqStmt env U env.shapeEnv X henvW.ordered henvW.stepUniq Γ₀ Γ
        (.const c ls) (.const c ls') (ci.type.instL ls) :=
      Hc henvW hΓ₀ X hX hW hI hQR h1 hext hdom IH hΓ hm hc hls hls' hlen heq hu h7 h8 @hA
    exact @key

end LogRel
end Lean4Lean

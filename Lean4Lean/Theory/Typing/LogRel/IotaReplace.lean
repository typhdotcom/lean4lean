import Lean4Lean.Theory.Typing.LogRel.AdeqQuotRule

/-!
# Related substitutions with their top values replaced

A K-like or structure-eta iota step computes to the rule's right body at values for the fields
other than the binders' own: chosen proofs, or the major premise's projections. Under related
substitutions, replacing the top binders' values one at a time by values related wherever the old
ones are keeps the substitutions related, and terms reducing to the right body at the replaced
substitution are related to it after converting the type, which mentions the fields.
-/

namespace Lean4Lean
open VExpr

/-- `σ` with its first `k` values dropped. -/
def VExpr.Subst.drop (σ : VExpr.Subst) (k : Nat) : VExpr.Subst := fun i => σ (i + k)

theorem VExpr.Subst.tail_drop (σ : VExpr.Subst) (k : Nat) : σ.tail.drop k = σ.drop (k+1) := by
  funext i; simp only [VExpr.Subst.drop, VExpr.Subst.tail, Nat.add_assoc]

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat}

section
variable [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

/-- An application of a term interpreted only at `bot` is interpreted only at `bot`. -/
theorem interp_appN_bot {ρ : Valuation} :
    ∀ {args : List VExpr} {e : VExpr},
    (∀ {n} {m : WShape n}, LE_Interp env ρ m.T e → m = .bot) →
    ∀ {n} {m : WShape n}, LE_Interp env ρ m.T (e.appN args) → m = .bot
  | [], _, he, _, _, h => he h
  | a :: args, e, he, _, _, h => by
    refine interp_appN_bot (e := .app e a) (fun {k} {m'} h' => ?_) h
    have key {k'} {f : WShape (k'+1)} {x : WShape k'} (hf : LE_Interp env ρ f.T e)
        (hle : m'.T ≤ (f.app x).T) : m' = .bot := by
      cases he hf
      exact TShape.le_bot.1 ((WShape.bot_app ▸ hle).trans TShape.bot_eqv.1)
    generalize e' : m'.T = t at h'
    cases h' with
    | bot => exact TShape.le_bot.1 (e' ▸ TShape.bot_eqv.1)
    | app hf _ hle => subst e'; exact key hf hle

/-- A variable's application, where the variable's value is `bot`, is interpreted only at `bot`. -/
theorem interp_bvar_appN_bot' {ρ : Valuation} {i : Nat} (hi : ρ i = Valuation.nil i)
    {args : List VExpr} {n} {m : WShape n} (h : LE_Interp env ρ m.T ((VExpr.bvar i).appN args)) :
    m = .bot := by
  refine interp_appN_bot (fun {k} {m'} h' => ?_) h
  generalize e' : m'.T = t at h'
  cases h' with
  | bot => exact TShape.le_bot.1 (e' ▸ TShape.bot_eqv.1)
  | bvar h1 => rw [hi] at h1; exact TShape.le_bot.1 (e' ▸ h1.trans TShape.bot_le)

/-- Related substitutions with the values of their top binders `Gs` replaced: each new value is
equal to the old at the binder's type under the new substitution, given the substitutions below it
equal, and related to whatever the old one is related to. Unless the substitutions reach `Γ₀` within `Gs`, where the valuation is `bot`
below `Gs`. -/
theorem LR.SubstWF.replaceTop (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {Δ : List VExpr} :
    ∀ (Gs : List VExpr) {σ τ σ'' : VExpr.Subst} {ρ : Valuation},
    OnCtx (Gs ++ Δ) (env.IsType U) →
    LR.SubstWF (U := U) henv hU Γ₀ σ σ'' (Gs ++ Δ) ρ →
    (∀ i, Gs.length ≤ i → τ i = σ i) →
    (∀ i (h : i < Gs.length), ∃ u, env.HasType U (Gs.drop (i+1) ++ Δ) Gs[i] (.sort u) ∧
      StrongSoundEq env U (Gs.drop (i+1) ++ Δ) Gs[i] Gs[i] (.sort u) ∧
      AdeqStmt (U := U) henv hU Γ₀ (Gs.drop (i+1) ++ Δ) Gs[i] Gs[i] (.sort u)) →
    (∀ i (h : i < Gs.length),
      VEnv.Ctx.SubstEq env U Γ₀ (τ.drop (i+1)) (σ.drop (i+1)) (Gs.drop (i+1) ++ Δ) →
      env.IsDefEq U Γ₀ (τ i) (σ i) (Gs[i].subst (τ.drop (i+1)))) →
    (∀ i (h : i < Gs.length) {n} {m a : WShape n} {x : VExpr}, m.T ≤ ρ i → m.HasType a →
      env.IsDefEq U Γ₀ (σ i) x (Gs[i].subst (τ.drop (i+1))) →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (σ i) x (Gs[i].subst (τ.drop (i+1))) m a →
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (τ i) x (Gs[i].subst (τ.drop (i+1))) m a) →
    LR.SubstWF (U := U) henv hU Γ₀ τ σ'' (Gs ++ Δ) ρ ∨
      ∀ i, Gs.length ≤ i → ρ i = Valuation.nil i
  | [], σ, τ, σ'', ρ, _, W, hτ, _, _, _ => by
    obtain rfl : τ = σ := funext fun i => hτ i (Nat.zero_le _)
    exact .inl W
  | A :: Gs, σ, τ, σ'', ρ, hΓ, W, hτ, HT, Hx, Hv => by
    cases W with
    | id => exact .inr fun _ _ => rfl
    | cons W' h1 h2 h3 _ h0 =>
    rename_i ρ' _ _ x _
    have IH {σ₂} (W₂ : LR.SubstWF (U := U) henv hU Γ₀ σ.tail σ₂ (Gs ++ Δ) ρ') :=
      LR.SubstWF.replaceTop hM hΓ₀ Gs (τ := τ.tail) hΓ.1 W₂
        (fun i hi => hτ (i+1) (by simp; omega))
        (fun i hi => by
          have := HT (i+1) (by simp; omega)
          simp only [List.getElem_cons_succ, List.drop_succ_cons] at this; exact this)
        (fun i hi hE => by
          have := Hx (i+1) (by simp; omega)
          simp only [List.getElem_cons_succ, List.drop_succ_cons] at this; exact this hE)
        (fun i hi n m a x hm hmem hx H => by
          have := Hv (i+1) (by simp; omega) (m := m) (a := a) (x := x) hm hmem
          simp only [List.getElem_cons_succ] at this; exact this hx H)
    have hnil (H : ∀ i, Gs.length ≤ i → ρ' i = Valuation.nil i) :
        ∀ i, (A :: Gs).length ≤ i → ρ'.push x i = Valuation.nil i := by
      intro i hi
      cases i with
      | zero => simp at hi
      | succ i => exact H i (by simp at hi; omega)
    rcases IH W' with W1 | H
    · rcases IH W'.left with W2 | H
      · left
        obtain ⟨u, hAu, hSA, HA⟩ := HT 0 (by simp)
        simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at hAu hSA HA
        have eST : env.IsDefEq U Γ₀ (A.subst σ.tail) (A.subst τ.tail) (.sort u) :=
          hAu.substDF henv hΓ.1 hΓ₀ (W2.symm.toSubstEq hΓ₀)
        have tyConv {n} {a : WShape n} {σ₁ σ₂} (W₁ : LR.SubstWF (U := U) henv hU Γ₀ σ₁ σ₂ (Gs ++ Δ) ρ')
            (ha : LE_Interp env (ρ'.push x) a.T A.lift) (ht : a.HasType .type) :
            (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (A.subst σ₁) (A.subst σ₂) a := by
          have ha' := (LE_Interp.weak_iff hM.closed).1 ha
          have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (hSA.left.sound W₁.fits ha').out
          exact LR.toValTy le_n le_a ht hSort hmem' ((HA hA'' hSort hmem').1 W₁).1
        have eτ : τ = τ.tail.cons τ.head := funext fun i => by cases i <;> rfl
        rw [eτ]
        refine .cons (by simpa using W1) h1 h2 h3 hAu ⟨?_, fun n a ha => ⟨fun ht => ?_, fun m hm hmem => ?_⟩⟩
        · have := Hx 0 (by simp)
          simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at this
          exact (this (W2.toSubstEq hΓ₀)).trans (.defeqDF eST h0.1)
        · simp only [VExpr.Subst.cons_tail]
          exact ⟨⟨u, hAu.substDF henv hΓ.1 hΓ₀ (W1.toSubstEq hΓ₀)⟩, tyConv W1 ha ht⟩
        · simp only [VExpr.Subst.cons_tail, VExpr.Subst.cons_head]
          have H0 := (h0.2 a ha).2 hm hmem
          have H1 := (LR _ _ _).conv (.base eST) (tyConv W2.symm ha hmem.isType) H0
          have := Hv 0 (by simp) (m := m) (a := a) (x := σ''.head) (bvar_iff.1 hm) hmem
            (.defeqDF eST h0.1) H1
          exact this
      · exact .inr (hnil H)
    · exact .inr (hnil H)

/-- Two terms are related where, under each related substitution, the right one reduces to an
instance of a term `S` related to itself, and the left one to an instance of `S` at `F σ`, which
is related to whatever `σ` is (or `S` is interpreted only at `bot`): the type `A` at `F σ` is
converted to `A` at `σ` through `A`'s own case. -/
theorem AdeqStmt.of_reds_conv (hΓ : OnCtx Γ (env.IsType U)) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {L R S A : VExpr} {u : VLevel} (hA : env.HasType U Γ A (.sort u))
    (hSA : StrongSoundEq env U Γ A A (.sort u))
    (HA : AdeqStmt (U := U) henv hU Γ₀ Γ A A (.sort u))
    (HS : AdeqStmt (U := U) henv hU Γ₀ Γ S S A)
    (hLS : ∀ {ρ n} {m : WShape n}, LE_Interp.Valuation.Fits env Γ₀ Γ ρ → LE_Interp env ρ m.T L →
      LE_Interp env ρ m.T S)
    (F : VExpr.Subst → VExpr.Subst)
    (hF : ∀ {σ σ' ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ →
      LR.SubstWF (U := U) henv hU Γ₀ (F σ) σ' Γ ρ ∨
        ∀ {n} {m : WShape n}, LE_Interp env ρ m.T S → m = .bot)
    (redL : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      LR.SubstWF (U := U) henv hU Γ₀ (F σ) σ Γ ρ →
      TRed env U Γ₀ (L.subst σ) (S.subst (F σ)) (A.subst σ))
    (redR : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      TRed env U Γ₀ (R.subst σ) (S.subst σ) (A.subst σ)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ L R A := by
  intro ρ n m a hm ha hmem
  refine .fits fun hfit => ?_
  have hS0 := hLS hfit hm
  have ad := HS hS0 ha hmem
  have hAσ {σ σ'} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
      env.IsDefEq U Γ₀ (A.subst σ') (A.subst σ) (.sort u) :=
    (hA.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)).symm
  have conv {σ σ' M N} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ)
      (H : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N (A.subst σ) m a) :
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N (A.subst σ') m a := by
    have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (hSA.left.sound hfit ha).out
    exact (LR _ _ _).conv (.base (hAσ W).symm)
      (LR.toValTy le_n le_a hmem.isType hSort hmem' ((HA hA'' hSort hmem').1 W).1) H
  have hbot (hb : ∀ {n} {m : WShape n}, LE_Interp env ρ m.T S → m = .bot) {M N T} :
      (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N T m a := by
    cases hb hS0; exact (LR _ _ _).bot hmem.isType
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · rcases hF W.left with Wa | hb
    · rcases hF W.symm.left with Wb | hb
      · rcases hF W with W1 | hb
        · rcases hF W1.symm with W2 | hb
          · have r1 := redL W.left Wa
            have r2 := (redL W.symm.left Wb).tyEq (.base (hAσ W))
            exact ((LR _ _ _).whr r1 r2).2 (conv Wa (ad.1 W2.symm).1)
          · exact hbot hb
        · exact hbot hb
      · exact hbot hb
    · exact hbot hb
  · have r1 := redR W.left
    have r2 := (redR W.symm.left).tyEq (.base (hAσ W))
    exact ((LR _ _ _).whr r1 r2).2 (ad.1 W).1
  · rcases hF W with Wa | hb
    · exact ((LR _ _ _).whr (redL W Wa) (redR W)).2 (conv Wa (ad.1 Wa).1)
    · exact hbot hb

end

end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.ConstDelta
import Lean4Lean.Theory.Typing.LogRel.AdequacyWF

/-!
# Adequacy at a block's constants

A constant is related at a pi type when its applications to related arguments are: its
application to the bound variable, in the context extended by the domain, says exactly that
(`AdeqStmt.etaLam`), since substituting an argument for the variable gives the application. So a
constant is related wherever its application to all the variables of its type's leading binders
is, in the context of those binders (`AdeqStmt.etaLams`): what a block's types, constructors and
recursors do there, applied to their arguments, is what each of them computes.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}

/-- An interpretation of a pi type is below a pi type's shape, or `bot`. -/
theorem LE_Interp.forallE_cases (H : LE_Interp env ρ x (.forallE B F)) :
    x ≤ TShape.bot ∨ ∃ (k : Nat) (b : WShape k) (f : WShapeFun k), x ≤ (WShape.forallE b f).T := by
  cases H with
  | bot => exact .inl TShape.bot_eqv.1
  | forallE _ _ _ _ le => exact .inr ⟨_, _, _, le⟩

theorem LE_Interp.not_sort_forallE (H : LE_Interp env ρ (WShape.sort (n := n) r).T (.forallE B F)) :
    False := by
  rcases H.forallE_cases with h | ⟨_, _, _, h⟩
  · have := congrArg Subtype.val (TShape.le_bot.1 h); simp [WShape.T, WShape.sort, WShape.bot] at this
    cases n <;> simp [Shape.sort, Shape.bot] at this
  · exact TShape.sort_not_le_forallE h

theorem LE_Interp.not_indTy_forallE {l : List (WShape n)}
    (H : LE_Interp env ρ (WShape.indTy (n := n) r I l).T (.forallE B F)) : False := by
  rcases H.forallE_cases with h | ⟨_, _, _, h⟩
  · have := congrArg Subtype.val (TShape.le_bot.1 h); simp [WShape.T, WShape.indTy, WShape.bot] at this
    simp [Shape.bot] at this
  · exact TShape.indTy_not_le_forallE h

/-- A term is related at a pi type wherever its application to the bound variable is, in the
context extended by the domain: substituting an argument for the variable gives the application
to it. -/
theorem AdeqStmt.etaLam (hM : ModelEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hAt : env.HasType U Γ A (.sort u)) (hBt : env.HasType U (A::Γ) B (.sort v))
    (hSA : StrongSoundEq env U Γ A A (.sort u)) (hSB : StrongSoundEq env U (A::Γ) B B (.sort v))
    (ihA : AdeqStmt (U := U) henv hU Γ₀ Γ A A (.sort u))
    (ihB : AdeqStmt (U := U) henv hU Γ₀ (A::Γ) B B (.sort v))
    (ihBody : AdeqStmt (U := U) henv hU Γ₀ (A::Γ) (.app F.lift (.bvar 0))
      (.app F'.lift (.bvar 0)) B) :
    AdeqStmt (U := U) henv hU Γ₀ Γ F F' (.forallE A B) := by
  intro ρ n m a hM' hA hmem
  have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hAt⟩
  have eb {G : VExpr} {σ : VExpr.Subst} {x : VExpr} :
      (VExpr.app G.lift (.bvar 0)).subst (σ.cons x) = .app (G.subst σ) x := by
    show VExpr.app (G.lift.subst _) _ = _; rw [lift_subst_cons]; rfl
  cases hmem.unfold with
  | bot hm => exact .bot hm
  | sort => exact (LE_Interp.not_sort_forallE hA).elim
  | forallE => exact (LE_Interp.not_sort_forallE hA).elim
  | ctor => exact (LE_Interp.not_indTy_forallE hA).elim
  | indTy => exact (LE_Interp.not_sort_forallE hA).elim
  | @lam k g a₁ a₂ htm =>
    revert hM'; unfold WShape.lam'; split <;> intro hM' <;> [skip; exact .bot hmem.isType]
    rename_i hg
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := (hA.forallE_inv' hM).1
    have cons := LR.Adequate.cons hM hΓ hΓ₀ hSA.left.sound ihA hAt
    have htmF := (WShape.HasTypeLam.iff.1 htm).2.2
    have hBodyI (p : WShape k) : LE_Interp env (ρ.push p.T) (g.app p).T (.app F.lift (.bvar 0)) := by
      have := LE_Interp.app' (LE_Interp.weak (x := p.T) hM.closed hM') (LE_Interp.bvar0 (x := p.T))
      rwa [WShape.lam_eq_lam', WShape.lam'_app] at this
    have IB {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :=
      ihBody (hBodyI p) ((hA.forallE_inv' hM).2 p) (htmF p hp)
    have TB {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
        (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (B.subst (σ₁.cons x)) (B.subst (σ₂.cons x'))
          (a₂.app p) := by
      have hB := (hA.forallE_inv' hM).2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (hSB.left.sound W'.fits hB).out
      exact LR.toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
    have hdom {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A.subst σ) (A.subst σ') a₁ := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (hSA.left.sound W.fits hA1).out
      exact LR.toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
    have hAσ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
        env.IsDefEq U Γ₀ (A.subst σ) (A.subst σ') (.sort u) :=
      hAt.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
    have mkLamF {F₁ F₂ : VExpr} {σ : VExpr.Subst}
        (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ)
        (h1 : ∀ {x x' p}, p.HasType a₁ → env.IsDefEq U Γ₀ x x' (A.subst σ) →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁ →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app F₁ x) (.app F₁ x')
            (B.subst (σ.cons x)) (g.app p) (a₂.app p) ∧
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app F₂ x) (.app F₂ x')
            (B.subst (σ.cons x)) (g.app p) (a₂.app p))
        (h2 : ∀ {x p}, p.HasType a₁ → env.HasType U Γ₀ x (A.subst σ) →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x (A.subst σ) p a₁ →
          (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app F₁ x) (.app F₂ x)
            (B.subst (σ.cons x)) (g.app p) (a₂.app p)) :
        (LR (U := U) (Γ := Γ₀) henv hU (k+1)).DefEq F₁ F₂ ((VExpr.forallE A B).subst σ)
          (WShape.lam g hg) (WShape.forallE a₁ a₂) := by
      simp only [LR, LRS, LRS.DefEq.lam_forallE]
      have hΓ₀A : OnCtx (A.subst σ :: Γ₀) (env.IsType U) := ⟨hΓ₀, _, (hAσ W).hasType.1⟩
      have hBσ := hBt.subst henv ((W.toSubstEq hΓ₀).lift henv hAt) hΓ₀A
      refine .inl ⟨A.subst σ, B.subst σ.lift, u, v, .rfl,
        TyEq.refl (VEnv.IsDefEq.forallEDF (hAσ W).hasType.1 hBσ), (hAσ W).hasType.1, hdom W,
        hBσ, ⟨fun x x' p hp hx hv => ?_,
        fun x p hp hx hv => ?_⟩, ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩⟩ <;>
        simp only [inst_lift_cons]
      · have := TB hp (cons hp hA1 hx hv W); exact ⟨this, this⟩
      · exact TB hp (cons hp hA1 hx hv W)
      · exact h1 hp hx hv
      · exact h2 hp hx hv
    -- the applications at the other substitution, converted to the type at `σ`
    have other {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {x x' p}
        (hp : p.HasType a₁) (hx : env.IsDefEq U Γ₀ x x' (A.subst σ))
        (hv : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁) :
        (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app (F.subst σ') x)
          (.app (F.subst σ') x') (B.subst (σ.cons x)) (g.app p) (a₂.app p) ∧
        (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app (F'.subst σ') x)
          (.app (F'.subst σ') x') (B.subst (σ.cons x)) (g.app p) (a₂.app p) := by
      have W2 := cons hp hA1 ((hAσ W).defeqDF hx) ((LR _ _ _).conv (.base (hAσ W)) (hdom W) hv)
        W.symm.left
      have W3 := cons hp hA1 hx.hasType.1 ((LR _ _ _).left hv) W
      have hc := (LR _ _ _).symm_ty (TB hp W3)
      have hcE : TyEq env U Γ₀ (B.subst (σ'.cons x)) (B.subst (σ.cons x)) :=
        .base (hBt.substDF henv hΓA hΓ₀ (W3.toSubstEq hΓ₀)).symm
      have r := (IB hp W2).1 W2
      simp only [eb] at r
      exact ⟨(LR _ _ _).conv hcE hc r.1, (LR _ _ _).conv hcE hc r.2⟩
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · refine mkLamF W.left (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W.left
        have r := ((IB hp W1).1 W1).1
        simp only [eb] at r
        exact ⟨r, (other W hp hx hv).1⟩
      · have W1 := cons hp hA1 hx hv W
        have r := ((IB hp W1).1 W1).1
        simp only [eb] at r
        exact r
    · refine mkLamF W.left (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W.left
        have r := ((IB hp W1).1 W1).2
        simp only [eb] at r
        exact ⟨r, (other W hp hx hv).2⟩
      · have W1 := cons hp hA1 hx hv W
        have r := ((IB hp W1).1 W1).2
        simp only [eb] at r
        exact r
    · refine mkLamF W (fun hp hx hv => ?_) (fun hp hx hv => ?_)
      · have W1 := cons hp hA1 hx hv W
        have r := (IB hp W1).1 W1
        simp only [eb] at r
        exact r
      · have W1 := cons hp hA1 hx hv W
        have r := (IB hp W1).2 W1
        simp only [eb] at r
        exact r

/-- `F` applied to the variables of the binders `Bs`, in the context extended by them. -/
def etaSpine : List VExpr → VExpr → VExpr
  | [], F => F
  | _ :: Bs, F => etaSpine Bs (.app F.lift (.bvar 0))

/-- A term is related at a pi telescope wherever its application to the telescope's variables is,
in the context extended by the telescope, given that the telescope's types are related types
(`P`, closed under taking a pi type's domain and codomain). -/
theorem AdeqStmt.etaLams (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (P : List VExpr → VExpr → Prop)
    (hP : ∀ {Γ A B}, P Γ (.forallE A B) → P Γ A ∧ P (A::Γ) B)
    (hTy : ∀ {Γ T}, OnCtx Γ (env.IsType U) → P Γ T → ∃ u, env.HasType U Γ T (.sort u) ∧
      StrongSoundEq env U Γ T T (.sort u) ∧ AdeqStmt (U := U) henv hU Γ₀ Γ T T (.sort u)) :
    ∀ (Bs : List VExpr) {Γ F F' R}, OnCtx Γ (env.IsType U) → P Γ (.foralls Bs R) →
      AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ Γ) (etaSpine Bs F) (etaSpine Bs F') R →
      AdeqStmt (U := U) henv hU Γ₀ Γ F F' (.foralls Bs R)
  | [], _, _, _, _, _, _, H => H
  | A :: Bs, Γ, F, F', R, hΓ, hPT, H => by
    obtain ⟨hPA, hPB⟩ := hP hPT
    obtain ⟨u, hAt, hSA, ihA⟩ := hTy hΓ hPA
    have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hAt⟩
    obtain ⟨v, hBt, hSB, ihB⟩ := hTy hΓA hPB
    have H' : AdeqStmt (U := U) henv hU Γ₀ (Bs.reverse ++ A :: Γ)
        (etaSpine Bs (.app F.lift (.bvar 0))) (etaSpine Bs (.app F'.lift (.bvar 0))) R := by
      have e : (A :: Bs).reverse ++ Γ = Bs.reverse ++ A :: Γ := by simp
      rw [← e]; intro ρ n m a; exact H
    exact AdeqStmt.etaLam hM hΓ hΓ₀ hAt hBt hSA hSB ihA ihB
      (AdeqStmt.etaLams hM hΓ₀ P hP hTy Bs hΓA hPB H')

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.addDefEqList_constants' : ∀ {env : VEnv} {dfs : List VDefEq},
    (env.addDefEqList dfs).constants = env.constants
  | _, [] => rfl
  | _, _ :: _ => VEnv.addDefEqList_constants' (env := VEnv.addDefEq _ _)

omit [ShapeEnv] in
/-- A constant of an environment extended by a list is the old environment's or the list's. -/
theorem _root_.Lean4Lean.VEnv.addConstList_constants_cases' :
    ∀ {env env' : VEnv} {cs : List (Name × VConstant)} {c : Name} {ci : VConstant},
    env.addConstList cs = some env' → env'.constants c = some ci →
    env.constants c = some ci ∨ (c, ci) ∈ cs
  | _, _, [], _, _, h, hc => by cases h; exact .inl hc
  | _, _, (m, ci') :: cs, c, ci, h, hc => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rcases VEnv.addConstList_constants_cases' h2 hc with h | h
    · rw [VEnv.addConst_constants_eq h1] at h
      dsimp only at h
      split at h
      · cases h; subst_vars; exact .inr (.head _)
      · exact .inl h
    · exact .inr (.tail _ h)

/-- Adding an inductive block keeps adequacy's environment cases, given them for its constants
and its iota rules, and for its projections (`HP`, over the old constants and rules and the new
blocks). -/
theorem AdequacyHyps.addInduct_of {E E' : VEnv} {d : VInductDecl} (h : E.addInduct d = some E')
    (HP : AdequacyHyps (U := U) henv hU { E' with constants := E.constants, defeqs := E.defeqs } Γ₀)
    (Hc : ∀ {Γ c ci ls ls' u}, OnCtx Γ (env.IsType U) →
      (c, ci) ∈ d.typeConsts ++ d.ctorConsts ++ d.recConsts →
      (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → u.WF U →
      env.IsDefEqStrong U [] (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      env.IsDefEqStrong U Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (ci.type.instL ls) (ci.type.instL ls') (.sort u) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls))
    (Hr : ∀ {Γ df ls u}, OnCtx Γ (env.IsType U) → df ∈ d.iotaRules → (∀ l ∈ ls, l.WF U) →
      ls.length = df.uvars → u.WF U →
      env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
      env.IsDefEqStrong U [] (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
      env.IsDefEqStrong U [] (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
      env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
      env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
      AdeqStmt (U := U) henv hU Γ₀ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)) :
    AdequacyHyps (U := U) henv hU E' Γ₀ := by
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨E₁, h1, E₂, h2, E₃, h3, h4⟩ := h
  have hc : ∀ {c ci}, E'.constants c = some ci →
      E.constants c = some ci ∨ (c, ci) ∈ d.typeConsts ++ d.ctorConsts ++ d.recConsts := by
    intro c ci hci
    rw [VEnv.addBlock_constants h4] at hci
    rw [VEnv.addDefEqList_constants'] at hci
    rcases VEnv.addConstList_constants_cases' h3 hci with hci | hm
    · rcases VEnv.addConstList_constants_cases' h2 hci with hci | hm
      · rcases VEnv.addConstList_constants_cases' h1 hci with hci | hm
        · exact .inl hci
        · exact .inr (by simp [hm])
      · exact .inr (by simp [hm])
    · exact .inr (by simp [hm])
  have hd : ∀ {df}, E'.defeqs df → E.defeqs df ∨ df ∈ d.iotaRules := by
    intro df hdf
    rw [VEnv.addBlock_defeqs h4] at hdf
    rcases VEnv.addDefEqList_defeqs' hdf with hm | hdf
    · exact .inr hm
    · rw [VEnv.addConstList_defeqs' h3, VEnv.addConstList_defeqs' h2,
        VEnv.addConstList_defeqs' h1] at hdf
      exact .inl hdf
  refine ⟨fun {Γ c ci ls ls' u} hΓ hci => ?_, fun {Γ df ls u} hΓ hdf => ?_,
    fun hΓ hs => HP.projDF hΓ hs, fun hΓ hs => HP.projIota hΓ hs,
    fun hΓ hs => HP.projEta hΓ hs⟩
  · rcases hc hci with hci | hm
    · exact HP.const hΓ hci
    · exact Hc hΓ hm
  · rcases hd hdf with hdf | hm
    · exact HP.extra hΓ hdf
    · exact Hr hΓ hm

/-- A rule whose left-hand side reduces, under every related substitution, to its right-hand side
by a typed reduction is related wherever its left-hand side is. -/
theorem AdeqStmt.of_tred (hΓ : OnCtx Γ (env.IsType U)) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u))
    (HL : AdeqStmt (U := U) henv hU Γ₀ Γ L L A)
    (hred : ∀ {σ ρ}, LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ →
      TRed env U Γ₀ (L.subst σ) (R.subst σ) (A.subst σ)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ L R A := by
  intro ρ n m a hm ha hmem
  have ad := HL hm ha hmem
  refine ⟨fun σ σ' W => ⟨(ad.1 W).1, ?_⟩, fun σ W => ?_⟩
  · have hAA : env.IsDefEq U Γ₀ (A.subst σ') (A.subst σ) (.sort u) :=
      (hA.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)).symm
    have r1 := hred W.left
    have r2 := (hred W.symm.left).tyEq (.base hAA)
    exact ((LR _ _ _).whr r1 r2).1 (ad.1 W).1
  · have r1 := hred W
    have hL := ad.2 W
    exact ((LR _ _ _).whr (.refl r1.2.hasType.1) r1).1 hL

omit [ShapeEnv] in
theorem spine_liftN : (spine c ls rAs).liftN n = spine c ls (rAs.map (·.liftN n)) := by
  induction rAs with
  | nil => rfl
  | cons A rAs ih => simp only [spine_cons, List.map_cons, VExpr.liftN, ih]

omit [ShapeEnv] in
/-- A constant's spine applied to the variables of a telescope is the spine of the variables
followed by the old arguments, lifted. -/
theorem etaSpine_spine : ∀ (Bs rAs : List VExpr),
    etaSpine Bs (spine c ls rAs) =
      spine c ls ((List.range Bs.length).map VExpr.bvar ++ rAs.map (·.liftN Bs.length))
  | [], rAs => by simp [etaSpine]
  | B :: Bs, rAs => by
    show etaSpine Bs (.app (spine c ls rAs).lift (.bvar 0)) = _
    rw [show VExpr.app (spine c ls rAs).lift (.bvar 0) = spine c ls (.bvar 0 :: rAs.map VExpr.lift)
      from by rw [spine_cons, ← spine_liftN (n := 1)]]
    rw [etaSpine_spine Bs]
    simp only [List.length_cons, List.range_succ, List.map_append, List.map_cons, List.map_map,
      List.append_assoc, List.map_nil, List.singleton_append]
    congr 2
    rw [List.cons.injEq]
    refine ⟨by simp [VExpr.liftN], List.map_congr_left fun a _ => ?_⟩
    rw [Function.comp_apply, liftN_liftN, Nat.add_comm]

/-- Adequacy converts along an equality of types it holds of. -/
theorem AdeqStmt.conv (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (hSty : StrongSoundEq env U Γ A B (.sort u))
    (ihTy : AdeqStmt (U := U) henv hU Γ₀ Γ A B (.sort u))
    (HE : AdeqStmt (U := U) henv hU Γ₀ Γ M N A) :
    AdeqStmt (U := U) henv hU Γ₀ Γ M N B := by
  intro ρ n m a hM' hA hmem
  have tyConv {σ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ) :
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (A.subst σ) (B.subst σ) a := by
    have hA' := (hSty.sound W.fits).2 hA
    have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (hSty.left.sound W.fits hA').out
    exact LR.toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
  have tyEq {σ} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ Γ ρ) :
      TyEq env U Γ₀ (A.subst σ) (B.subst σ) :=
    .base (hSty.defeq.subst henv (W.toSubstEq hΓ₀) hΓ₀)
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
    have hA' := (hSty.sound W.left.fits).2 hA
  · exact ⟨(LR _ _ _).conv (tyEq W.left) (tyConv W.left) ((HE hM' hA' hmem).1 W).1,
      (LR _ _ _).conv (tyEq W.left) (tyConv W.left) ((HE hM' hA' hmem).1 W).2⟩
  · exact (LR _ _ _).conv (tyEq W) (tyConv W) ((HE hM' hA' hmem).2 W)

omit [ShapeEnv] [AxInterp] in
/-- A constant whose role computes neither by unfolding nor as a recursor or `Quot.lift` heads no
step, given that a rule headed by a constant is at the rule's level parameters. -/
theorem Inert.of_role (hR : ConstRoles env)
    (hD : ∀ {df us}, env.defeqs df → df.lhs = .const c us → us = VLevel.params df.uvars)
    (h : ConstArity env c r k) (h1 : ∀ df, r ≠ .delta df) (h2 : ∀ d j, r ≠ .recursor d j)
    (h3 : r ≠ .quotLift) : Inert env c := by
  refine ⟨fun hdf e => ?_, fun hq e => ?_, fun hs hj e => ?_⟩
  · have := hD hdf e; subst this
    exact h1 _ (hR h (.delta hdf e))
  · exact h3 (hR h (.quotLift hq e))
  · obtain ⟨T, hT⟩ : ∃ T, _ = some T := ⟨_, List.getElem?_eq_getElem hj⟩
    exact h2 _ _ (hR h (.recursor hs e hT))

omit [ShapeEnv] [AxInterp] in
/-- A rule of a well-formed environment headed by a constant is a definition's, at its level
parameters. -/
theorem _root_.Lean4Lean.VEnv.WF.rule_lhs_params {E : VEnv} (hE : E.WF) (hdf : E.defeqs df)
    (e : df.lhs = .const c us) : us = VLevel.params df.uvars := by
  cases hE.ruleKind hdf with
  | defn ci h => cases e; rfl
  | quot => cases e
  | iota _ hm =>
    obtain ⟨⟨⟨j, c'⟩, q⟩, -, rfl⟩ := List.mem_map.1 hm
    rw [iotaRule_lhs] at e
    refine absurd e (VExpr.lams_ne_const (fun c us h => ?_) _)
    simp only [iotaL, VExpr.appN_append, VExpr.appN] at h; cases h

end LogRel
end Lean4Lean

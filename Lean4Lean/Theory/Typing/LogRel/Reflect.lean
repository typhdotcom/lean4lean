import Lean4Lean.Theory.Typing.LogRel.RelS

/-!
# Reflection of neutral terms

Two terms that reduce, typed, to neutral normal forms are related at every shape, given what the
relation needs of their type there (`TyInfo`): at a pi type shape, the type reduces, typed, to a
pi type whose codomains satisfy the same at related arguments; at a structure's shape, the
projections of neutral normal forms are typed along the constructor's telescope, with the same
for the field types. The relation says nothing more of neutral terms at sorts and at other
inductive types, so nothing is needed there.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- `M` reduces, typed at `A`, to a neutral normal form. -/
def TNeRed (M A : VExpr) : Prop :=
  ∃ M₁, TRed env U Γ M M₁ A ∧ WHNF env U Γ M₁ ∧ Neutral env M₁

end

namespace Neutral
variable (hU : StepUniq env)
include hU

/-- A neutral normal form applied is a normal form. -/
theorem whnf_app (W : WHNF env U Γ M) (H : Neutral env M) : WHNF env U Γ (.app M a) := by
  intro e' h
  have := (Neutral.app (a := a) H).kStep hU h
  generalize hx : VExpr.app M a = x at this
  cases this with
  | app h' => injection hx with hx; subst hx; exact W _ h'.step
  | proj => cases hx
  | major r1 r2 _ _ r4 =>
    injection hx with hx; subst hx; exact recHead hU r1 r2 r4 H
  | quotMajor r1 =>
    injection hx with hx; subst hx; exact quotHead hU r1 H
  | kIota r1 r2 r3 _ _ _ r7 r8 r9 =>
    injection hx with hx; subst hx
    refine recHead hU r1 r3 ?_ H
    simp [VInductDecl.majorIdx, r7, r8, r9]; omega
  | kQuot r1 =>
    injection hx with hx; subst hx; exact quotHead hU r1 H

/-- A projection of a neutral normal form is a normal form. -/
theorem whnf_proj (W : WHNF env U Γ M) (H : Neutral env M) : WHNF env U Γ (.proj s k M) := by
  intro e' h
  have := (Neutral.proj (s := s) (k := k) H).kStep hU h
  generalize hx : VExpr.proj s k M = x at this
  cases this with
  | proj h' => injection hx with _ _ hx; subst hx; exact W _ h'.step
  | _ => cases hx

end Neutral

namespace TNeRed

theorem neRed (H : TNeRed env U Γ M A) : NeRed env U Γ M :=
  let ⟨M', h1, h2, h3⟩ := H; ⟨M', h1.1, h2, h3⟩

theorem tyEq (hE : TyEq env U Γ A B) (H : TNeRed env U Γ M A) : TNeRed env U Γ M B :=
  let ⟨M', h1, h2, h3⟩ := H; ⟨M', h1.tyEq hE, h2, h3⟩

theorem app (hU : StepUniq env) (H : TNeRed env U Γ M (.forallE A B)) (ha : env.HasType U Γ a A) :
    TNeRed env U Γ (.app M a) (B.inst a) :=
  let ⟨_, h1, h2, h3⟩ := H; ⟨_, h1.app ha, Neutral.whnf_app hU h2 h3, .app h3⟩

end TNeRed

variable [ShapeEnv]

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- Fields `ms` and `ns` typed equal along the telescope `T` at shape `tel`, with field shapes
`fs`, each field type satisfying `TI` at its shape. -/
def FieldsTy (TI : VExpr → WShape n → Prop) :
    VExpr → WShape n → List VExpr → List VExpr → List (WShape n) → Prop
  | _, _, [], [], [] => True
  | T, tel, m :: ms, n :: ns, x :: xs => ∃ D B b g, tel.piView = some (b, g) ∧
    StepS env U Γ T (.forallE D B) ∧ x.HasType b ∧ env.IsDefEq U Γ m n D ∧ TI D b ∧
    FieldsTy TI (B.inst m) (g.app x) ms ns xs
  | _, _, _, _, _ => False

/-- What reflecting neutral terms at type `A` and shape `a` needs of `A`, given the relation `IH`
and the same `TI` one depth down. -/
def TyInfoS (IH : LogRel env U Γ n) (TI : VExpr → WShape n → Prop) (A : VExpr)
    (a : WShape (n+1)) : Prop :=
  (∀ b f, a = .forallE b f → NeRed env U Γ A ∨ ∃ A₁ A₂ u v,
    StepS env U Γ A (.forallE A₁ A₂) ∧ TyEq env U Γ A (.forallE A₁ A₂) ∧
    env.HasType U Γ A₁ (.sort u) ∧ IH.TyDefEq A₁ A₁ b ∧ env.HasType U (A₁::Γ) A₂ (.sort v) ∧
    LRS.PiDefEq IH A₁ A₂ A₂ b f ∧
    ∀ x p, p.HasType b → env.HasType U Γ x A₁ → IH.DefEq x x A₁ p b → TI (A₂.inst x) (f.app p)) ∧
  (∀ r h l, a = .indTy r h l → NeRed env U Γ A ∨
    ∀ c fs hf, IsStruct c = true → (WShape.ctor c fs hf).HasType (.indTy r h l) →
    ∀ M' N', WHNF env U Γ M' → Neutral env M' → WHNF env U Γ N' → Neutral env N' →
      env.IsDefEq U Γ M' N' A →
    Inert env h.name ∧ IndTele IH h l A A ∧
    ∃ i k ci lsA AsA, h.ctors.idxOf? c = some i ∧ h.arities[i]? = some k ∧
      env.constants c = some ci ∧ StepS env U Γ A ((VExpr.const h.name lsA).appN AsA) ∧
      fs.length = k ∧
      FieldsTy env U Γ TI (ctorTeleAt ci k lsA AsA) (ctorTel h l i) (VExpr.projs h.name k M')
        (VExpr.projs h.name k N') fs ∧
      TypeArgs env U Γ h lsA AsA)

end

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr) (henv : env.Ordered) (hU : StepUniq env)

/-- What reflecting neutral terms at type `A` and shape `a` needs of `A`, at every depth. -/
def TyInfo : (n : Nat) → VExpr → WShape n → Prop
  | 0, _, _ => True
  | n+1, A, a => TyInfoS env U Γ (LR henv hU n) (TyInfo n) A a

end

omit [ShapeEnv] in
theorem neutral_projs (hU : StepUniq env) (W : WHNF env U Γ M) (H : Neutral env M) :
    ∀ x ∈ VExpr.projs s k M, WHNF env U Γ x ∧ Neutral env x := by
  intro x hx
  simp only [VExpr.projs, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨Neutral.whnf_proj hU W H, .proj H⟩

/-- Fields typed along a telescope, all neutral normal forms, are related along it, given
reflection one depth down. -/
theorem FieldsTy.toRel {IH : LogRel env U Γ n} {TI : VExpr → WShape n → Prop}
    (refl : ∀ {M N A : VExpr} {m a : WShape n}, a.HasType .type → m.HasType a → TI A a →
      TNeRed env U Γ M A → TNeRed env U Γ N A → env.IsDefEq U Γ M N A → IH.DefEq M N A m a) :
    ∀ {T} {tel : WShape n} {ms ns fs}, FieldsTy env U Γ TI T tel ms ns fs →
      (∀ x ∈ ms, WHNF env U Γ x ∧ Neutral env x) → (∀ x ∈ ns, WHNF env U Γ x ∧ Neutral env x) →
      FieldsRel IH T tel ms ns fs
  | _, _, [], [], [], _, _, _ => trivial
  | _, _, _ :: _, _ :: _, _ :: _, ⟨D, B, b, g, h1, h2, h3, h4, h5, h6⟩, hm, hn => by
    have ⟨w1, n1⟩ := hm _ (.head _)
    have ⟨w2, n2⟩ := hn _ (.head _)
    refine ⟨D, B, b, g, h1, h2, h3, h4, refl h3.isType h3 h5 ⟨_, .refl h4.hasType.1, w1, n1⟩
      ⟨_, .refl h4.hasType.2, w2, n2⟩ h4, ?_⟩
    exact FieldsTy.toRel refl h6 (fun x hx => hm x (.tail _ hx)) (fun x hx => hn x (.tail _ hx))
  | _, _, [], _ :: _, _, h, _, _ | _, _, [], [], _ :: _, h, _, _
  | _, _, _ :: _, [], _, h, _, _ | _, _, _ :: _, _ :: _, [], h, _, _ => h.elim

/-- Reflection: terms that reduce, typed, to neutral normal forms are related at every shape their
type satisfies `TyInfo` at. -/
theorem reflect (henv : env.Ordered) (hU : StepUniq env) : ∀ (n : Nat) {M N A : VExpr}
    {m a : WShape n}, a.HasType .type → m.HasType a → TyInfo env U Γ henv hU n A a →
    TNeRed env U Γ M A → TNeRed env U Γ N A → env.IsDefEq U Γ M N A →
    (LR (U := U) (Γ := Γ) henv hU n).DefEq M N A m a
  | 0, M, N, A, m, a, ha, hm, _, hM, hN, _ => by
    show LR0.DefEq env U Γ M N m a
    dsimp only [LR0.DefEq]; split; · trivial
    dsimp only [LR0.TyDefEq]; split; · trivial
    exact .inr ⟨hM.neRed, hN.neRed⟩
  | n+1, M, N, A, m, a, ha, hm, hI, hM, hN, hMN => by
    show LRS.DefEq (LR henv hU n) M N A m a
    have IH := @reflect henv hU n
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort r =>
      rw [LRS.DefEq.sort_a]
      cases m using WShape.casesOn' with
      | sort => exact .inr ⟨hM.neRed, hN.neRed⟩
      | forallE => exact (LRS.TyDefEq.forallE_iff).2 (.inr ⟨hM.neRed, hN.neRed⟩)
      | indTy => exact (LRS.TyDefEq.indTy_iff).2 (.inr ⟨hM.neRed, hN.neRed⟩)
      | _ => trivial
    | forallE a₁ a₂ =>
      obtain ⟨g, rfl, hg⟩ := WShape.HasType.forallE_inv hm
      by_cases hz : g.NonZero
      case neg =>
        rw [show WShape.lam' g = .bot by simp [WShape.lam', hz]]; trivial
      rw [← WShape.lam_eq_lam' (hl := hz), LRS.DefEq.lam_forallE]
      rcases hI.1 a₁ a₂ rfl with hA | ⟨A₁, A₂, u, v, rA, eA, hA₁, hT₁, hA₂, hP, hI'⟩
      · exact .inr hA
      refine .inl ⟨A₁, A₂, u, v, rA, eA, hA₁, hT₁, hA₂, hP, ?_, ?_⟩
      · intro x y p hp hxy hv
        obtain ⟨hpi, -, hgx⟩ := WShape.HasTypeLam.iff.1 hg
        have hcod := (WShape.HasTypePi.iff.1 hpi).2 p hp
        have hti := hI' x p hp hxy.hasType.1 ((LR (U := U) (Γ := Γ) henv hU n).left hv)
        have hE : TyEq env U Γ (A₂.inst y) (A₂.inst x) :=
          .base (instDF_ty hA₁ hA₂ hxy.symm)
        have hMM := eA.defeqDF hMN.hasType.1
        have hNN := eA.defeqDF hMN.hasType.2
        exact ⟨IH hcod (hgx p hp) hti ((hM.tyEq eA).app hU hxy.hasType.1)
            (((hM.tyEq eA).app hU hxy.hasType.2).tyEq hE) (.appDF hMM hxy),
          IH hcod (hgx p hp) hti ((hN.tyEq eA).app hU hxy.hasType.1)
            (((hN.tyEq eA).app hU hxy.hasType.2).tyEq hE) (.appDF hNN hxy)⟩
      · intro x p hp hx hv
        obtain ⟨hpi, -, hgx⟩ := WShape.HasTypeLam.iff.1 hg
        have hcod := (WShape.HasTypePi.iff.1 hpi).2 p hp
        exact IH hcod (hgx p hp) (hI' x p hp hx hv) ((hM.tyEq eA).app hU hx)
          ((hN.tyEq eA).app hU hx) (.appDF (eA.defeqDF hMN) hx)
    | indTy r h l =>
      cases m using WShape.casesOn' with
      | ctor c fs hf =>
        rw [LRS.DefEq.ctor_indTy]
        unfold LRS.IndVal
        cases hc : IsStruct c
        · exact .inr (.inr ⟨rfl, hM.neRed, hN.neRed⟩)
        rw [if_pos rfl]
        rcases hI.2 r h l rfl with hA | hI'
        · exact .inr (.inl hA)
        obtain ⟨M', tM, wM, nM⟩ := hM
        obtain ⟨N', tN, wN, nN⟩ := hN
        have hMN' : env.IsDefEq U Γ M' N' A := tM.2.symm.trans (hMN.trans tN.2)
        obtain ⟨hn, hT, i, k, ci, lsA, AsA, h1, h2, h3, h4, h5, h6, h7⟩ :=
          hI' c fs hf hc hm M' N' wM nM wN nN hMN'
        exact .inl ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, tM, wM, tN, wN, h5,
          FieldsTy.toRel (fun ha hm hI hM hN hMN => IH ha hm hI hM hN hMN) h6
            (neutral_projs hU wM nM) (neutral_projs hU wN nN), h7⟩
      | _ => trivial
    | lam => exact absurd hm.isType WShape.HasType.lam_isType
    | ctor => exact absurd hm.isType WShape.HasType.ctor_isType

end LogRel
end Lean4Lean

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

theorem app (hU : StepUniq env) (H : TNeRed env U Γ M (.forallE A B)) (ha : env.HasType U Γ a A) :
    TNeRed env U Γ (.app M a) (B.inst a) :=
  let ⟨_, h1, h2, h3⟩ := H; ⟨_, h1.app ha, Neutral.whnf_app hU h2 h3, .app h3⟩

end TNeRed

variable [ShapeEnv]

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr) (henv : env.Ordered) (hU : StepUniq env)

/-- What reflecting neutral terms at type `A` and shape `a` needs of `A`: that it is related to
itself there, and what the relation knows of its typing. -/
def TyInfo (n : Nat) (A : VExpr) (a : WShape n) : Prop :=
  (LR (U := U) (Γ := Γ) henv hU n).TyDefEq A A a ∧ (LR (U := U) (Γ := Γ) henv hU n).TyTy A a

end

/-- A type related to itself at a sort has what reflection needs of it. -/
theorem TyInfo.of_defEq {henv : env.Ordered} {hU : StepUniq env} {n : Nat} {A T : VExpr}
    {a : WShape n} (H : (LR (U := U) (Γ := Γ) henv hU n).DefEq A A T a (.sort r))
    (e : TyEq env U Γ T (.sort u)) : TyInfo env U Γ henv hU n A a :=
  ⟨(LR _ _ n).toType H, (((LR _ _ n).sort_a_iff.1 H).2 u e).1⟩

omit [ShapeEnv] in
theorem neutral_projs (hU : StepUniq env) (W : WHNF env U Γ M) (H : Neutral env M) :
    ∀ x ∈ VExpr.projs s k M, WHNF env U Γ x ∧ Neutral env x := by
  intro x hx
  simp only [VExpr.projs, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨Neutral.whnf_proj hU W H, .proj H⟩

/-- A stuck type is known to the relation at every shape. -/
theorem LRS.TyTyped.of_neRed {IH : LogRel env U Γ n} (h : NeRed env U Γ M) :
    ∀ {m : WShape (n+1)}, LRS.TyTyped IH M m := by
  intro m
  cases m using WShape.casesOn' with
  | forallE => exact (LRS.TyTyped.forallE_iff).2 (.inl h)
  | indTy => exact (LRS.TyTyped.indTy_iff).2 (.inl h)
  | _ => trivial

/-- Neutral normal forms typed along a telescope related to itself are related along it, given
reflection one depth down. -/
theorem FieldsRel.of_projs {IH : LogRel env U Γ n} (hU : StepUniq env)
    (refl : ∀ {M N A : VExpr} {m a : WShape n}, a.HasType .type → m.HasType a →
      IH.TyDefEq A A a → IH.TyTy A a → TNeRed env U Γ M A → TNeRed env U Γ N A →
      env.IsDefEq U Γ M N A → IH.DefEq M N A m a) :
    ∀ {T} {tel : WShape n} {ms ns fs}, ms.length = fs.length → tel.HasType .type →
      TeleRel IH fs.length T T tel →
      TelFits tel fs → ProjsTyped env U Γ T ms ns →
      (∀ x ∈ ms, WHNF env U Γ x ∧ Neutral env x) → (∀ x ∈ ns, WHNF env U Γ x ∧ Neutral env x) →
      FieldsRel IH T tel ms ns fs
  | _, _, [], [], [], _, _, _, _, _, _, _ => trivial
  | T, tel, m :: ms, n' :: ns, x :: xs, hl, ht, HT, hfit, ⟨D, B, r, hd, hP⟩, hm, hn => by
    obtain ⟨b, g, hv, hxb, hfits⟩ := hfit
    obtain ⟨D₁, B₁, D₁', B₁', r₁, r₁', -, hDD, HT'⟩ := HT.of_piView hv
    obtain ⟨y1, -⟩ := HT.of_piView_ty hU hv r₁ r₁'
    have e1 := StepS.determ hU r₁ forallE_whnf' r forallE_whnf'
    have e2 := StepS.determ hU r₁' forallE_whnf' r forallE_whnf'
    simp only [VExpr.forallE.injEq] at e1 e2
    obtain ⟨rfl, rfl⟩ := e1; obtain ⟨rfl, rfl⟩ := e2
    have ⟨tb, tg⟩ := WShape.piView_type ht hv
    have ⟨w1, n1⟩ := hm _ (.head _)
    have ⟨w2, n2⟩ := hn _ (.head _)
    have hr := refl tb hxb (IH.left_ty hDD) y1 ⟨_, .refl hd.hasType.1, w1, n1⟩
      ⟨_, .refl hd.hasType.2, w2, n2⟩ hd
    refine ⟨_, _, b, g, hv, r, hxb, hd, hr, ?_⟩
    exact FieldsRel.of_projs hU refl (by simpa using hl) (tg x)
      (HT' m m x hxb hd.hasType.1 (IH.left hr)) hfits hP
      (fun x hx => hm x (.tail _ hx)) (fun x hx => hn x (.tail _ hx))
  | _, _, [], _ :: _, _, _, _, _, _, h, _, _ | _, _, _ :: _, [], _, _, _, _, _, h, _, _ => h.elim
  | _, _, [], [], _ :: _, hl, _, _, _, _, _, _ => by simp at hl
  | _, _, _ :: _, _ :: _, [], hl, _, _, _, _, _, _ => by simp at hl

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
  | n+1, M, N, A, m, a, ha, hm, ⟨hT, hY⟩, hM, hN, hMN => by
    show LRS.DefEq (LR henv hU n) M N A m a
    have IH := @reflect henv hU n
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort r =>
      rw [LRS.DefEq.sort_a]
      refine ⟨?_, fun _ _ => ⟨LRS.TyTyped.of_neRed hM.neRed, LRS.TyTyped.of_neRed hN.neRed⟩⟩
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
      rw [show (LR (U := U) (Γ := Γ) henv hU (n+1)).TyTy A (.forallE a₁ a₂) =
        LRS.TyTyped (LR (U := U) (Γ := Γ) henv hU n) A (.forallE a₁ a₂) from rfl] at hY
      rw [show (LR (U := U) (Γ := Γ) henv hU (n+1)).TyDefEq A A (.forallE a₁ a₂) =
        LRS.TyDefEq (LR (U := U) (Γ := Γ) henv hU n) A A (.forallE a₁ a₂) from rfl] at hT
      rw [LRS.TyTyped.forallE_iff] at hY
      rcases hY with hA | ⟨A₁, A₂, u, v, rA, eA, hA₁, hA₂, y1, hY'⟩
      · exact .inr hA
      rw [LRS.TyDefEq.forallE_iff] at hT
      obtain ⟨B₁, F₁, B₂, F₂, rM, rM', -, -, hValB, hP⟩ :=
        hT.resolve_right fun ⟨hn, _⟩ => hn.not_forallE hU rA
      cases StepS.determ hU rA forallE_whnf rM forallE_whnf
      cases StepS.determ hU rA forallE_whnf rM' forallE_whnf
      have hT₁ := (LR (U := U) (Γ := Γ) henv hU n).left_ty hValB
      have hI' : ∀ x p, p.HasType a₁ → env.HasType U Γ x A₁ →
          (LR (U := U) (Γ := Γ) henv hU n).DefEq x x A₁ p a₁ →
          TyInfo env U Γ henv hU n (A₂.inst x) (a₂.app p) := fun x p hp hx hv =>
        ⟨(LR (U := U) (Γ := Γ) henv hU n).left_ty (hP.2 hp hx hv), hY' x p hp hx hv⟩
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
        · exact .inr (.inr ⟨rfl, hM, hN⟩)
        rw [if_pos rfl]
        rw [show (LR (U := U) (Γ := Γ) henv hU (n+1)).TyTy A (.indTy r h l) =
          LRS.TyTyped (LR (U := U) (Γ := Γ) henv hU n) A (.indTy r h l) from rfl] at hY
        rw [show (LR (U := U) (Γ := Γ) henv hU (n+1)).TyDefEq A A (.indTy r h l) =
          LRS.TyDefEq (LR (U := U) (Γ := Γ) henv hU n) A A (.indTy r h l) from rfl] at hT
        rw [LRS.TyTyped.indTy_iff] at hY
        rcases hY with hA | hS
        · exact .inr (.inl hA)
        rw [LRS.TyDefEq.indTy_iff] at hT
        rcases hT with ⟨hR, hTe⟩ | ⟨hA, -⟩
        case inr => exact .inr (.inl hA)
        obtain ⟨hn, lsA, lsA', AsA, AsA', rA, -, -, hlen, -, hSR⟩ := hR
        obtain ⟨i, hi, hk⟩ := hm.ctor_arity
        obtain ⟨ci, hci, hS⟩ := hS c i fs.length hc hi hk
        obtain ⟨M', tM, wM, nM⟩ := hM
        obtain ⟨N', tN, wN, nN⟩ := hN
        have hMN' : env.IsDefEq U Γ M' N' A := tM.2.symm.trans (hMN.trans tN.2)
        have hP := hS lsA AsA rA hn.whnf M' N' wM nM wN nN hMN'
        obtain ⟨i', hi', hfit⟩ := hm.ctor_fits
        obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
        have HT := hTe lsA AsA lsA AsA rA rA c i fs.length ci hi hk hci
        exact .inl ⟨hn, hTe, i, fs.length, ci, lsA, AsA, M', N', hi, hk, hci, rA, tM, wM, tN, wN,
          rfl, FieldsRel.of_projs hU (fun ha hm hT hY hM hN hMN => IH ha hm ⟨hT, hY⟩ hM hN hMN)
            (by simp [VExpr.projs]) (hm.indTy_tels i) HT hfit hP (neutral_projs hU wM nM) (neutral_projs hU wN nN),
          TypeArgs.of_rel hlen hSR.symm⟩
      | _ => trivial
    | lam => exact absurd hm.isType WShape.HasType.lam_isType
    | ctor => exact absurd hm.isType WShape.HasType.ctor_isType

end LogRel
end Lean4Lean

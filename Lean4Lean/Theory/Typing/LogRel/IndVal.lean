import Lean4Lean.Theory.Typing.LogRel.Rel

/-!
# Constructor telescopes in the relation

A value of an inductive type is related, at a constructor shape, by its fields: both sides reduce
to applications of the constructor, and the fields are related along the constructor's field
telescope at the type's arguments (`FieldsRel`). Since the fields are dependent, the telescope's
later types depend on the earlier fields; `TeleRel` says two telescopes are related: their
domains are, and so are their rests at related arguments. The type clause at an inductive type
shape carries `TeleRel` between the constructors' telescopes at the two types' arguments, which
moves related fields from one type to the other.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

/-- `e` with its leading pi binders instantiated by `as`, syntactically. -/
def piInst : VExpr → List VExpr → VExpr
  | e, [] => e
  | .forallE _ B, a :: as => piInst (B.inst a) as
  | e, _ :: _ => e

/-- The number of leading pi binders of `e`. -/
def piCount : VExpr → Nat
  | .forallE _ B => piCount B + 1
  | _ => 0

/-- A constructor's field telescope at the levels `ls` and the type's arguments `As`: its type
with the parameters instantiated, the first `piCount - k` arguments, for `k` fields. -/
def ctorTeleAt (ci : VConstant) (k : Nat) (ls : List VLevel) (As : List VExpr) : VExpr :=
  piInst (ci.type.instL ls) (As.take (piCount ci.type - k))

variable [ShapeEnv]

/-- A shape's view as a pi type at its own depth: the domain and the codomain at an argument. -/
def WShape.piView : ∀ {n} (_ : WShape n), Option (WShape n × WShapeFun n)
  | 0, _ => none
  | n+1, ⟨.forallE b f, wf⟩ => some (WShape.lift (n+1) (n := n) ⟨b, wf.1⟩,
      WShapeFun.lift (n+1) (n := n) ⟨f, wf.2⟩)
  | _+1, _ => none

/-- The field telescope's shape of constructor `c` in an inductive type shape's arguments. -/
def ctorTel (h : IndHead) (l : List (WShape n)) (i : Nat) : WShape n := l.getD (h.nargs + i) .bot

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

@[simp] theorem WShape.piView_forallE {s : WShape n} {f : WShapeFun n} :
    (WShape.forallE s f).piView = some (s.lift (n+1), f.lift (n+1)) := rfl

@[simp] theorem WShape.piView_zero (tel : WShape 0) : tel.piView = none := rfl

theorem WShape.piView_eq_some {tel : WShape (n+1)} {b : WShape (n+1)} {g}
    (hv : tel.piView = some (b, g)) :
    ∃ s f, tel = .forallE s f ∧ b = s.lift (n+1) ∧ g = f.lift (n+1) := by
  obtain ⟨tel, wf⟩ := tel
  cases tel with
  | forallE s f =>
    refine ⟨⟨s, wf.1⟩, ⟨f, wf.2⟩, rfl, ?_⟩
    simp only [WShape.piView, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨hv.1.symm, hv.2.symm⟩
  | _ => simp [WShape.piView] at hv

theorem WShape.piView_mono {tel tel' : WShape n} (hle : tel ≤ tel')
    (hv : tel.piView = some (b, g)) : ∃ b' g', tel'.piView = some (b', g') ∧ b ≤ b' ∧
      (∀ x, g.app x ≤ g'.app x) ∧ (∀ x y, x ≤ y → g.app x ≤ g.app y) ∧
      (∀ x y, x ≤ y → g'.app x ≤ g'.app y) := by
  cases n with
  | zero => simp at hv
  | succ n =>
    obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
    obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 hle
    exact ⟨_, _, rfl, WShape.lift_mono (Nat.le_succ _) h1,
      fun x => WShapeFun.app_mono_l (WShapeFun.lift_mono (Nat.le_succ _) h2) x,
      fun _ _ h => WShapeFun.app_mono_r h, fun _ _ h => WShapeFun.app_mono_r h⟩

theorem WShape.piView_type {tel : WShape n} (ht : tel.HasType .type)
    (hv : tel.piView = some (b, g)) : b.HasType .type ∧ ∀ x, (g.app x).HasType .type := by
  cases n with
  | zero => simp at hv
  | succ n =>
    obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
    have hpi : WShape.HasTypePi f s true := by
      have := Shape.HasType.unfold ht
      cases this with | forallE H => exact Shape.HasTypePi.toType H
    have hlift : WShape.HasTypePi (f.lift (n+1)) (s.lift (n+1)) true := by
      simp only [WShape.HasTypePi, WShapeFun.lift_val (Nat.le_succ _),
        WShape.lift_val (Nat.le_succ _)]
      exact (Shape.HasTypePi.lift (Nat.le_succ _)).2 hpi
    exact ⟨hlift.dom_isType, hlift.app_isType⟩

theorem WShapeFun.lift_join' {x y : WShapeFun n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  by_cases h : x.Compat y
  · have h' : (x.lift m).Compat (y.lift m) := by
      simp only [WShapeFun.Compat, WShapeFun.lift_val le, ShapeFun.Compat.lift le]; exact h
    apply Subtype.ext
    rw [WShapeFun.lift_val le, WShapeFun.join_val h, WShapeFun.join_val h',
      WShapeFun.lift_val le, WShapeFun.lift_val le, ShapeFun.lift_join le]
  · have h' : ¬(x.lift m).Compat (y.lift m) := by
      simp only [WShapeFun.Compat, WShapeFun.lift_val le, ShapeFun.Compat.lift le]; exact h
    simp only [WShapeFun.join, dif_neg h, dif_neg h', WShapeFun.lift_bot]

/-- The pi typing of a telescope shape's view at its own depth. -/
theorem WShape.piView_pi {s : WShape n} {f : WShapeFun n}
    (ht : (WShape.forallE s f).HasType .type) :
    WShape.HasTypePi (f.lift (n+1)) (s.lift (n+1)) true := by
  have hpi : WShape.HasTypePi f s true := by
    have := Shape.HasType.unfold ht
    cases this with | forallE H => exact Shape.HasTypePi.toType H
  simp only [WShape.HasTypePi, WShapeFun.lift_val (Nat.le_succ _),
    WShape.lift_val (Nat.le_succ _)]
  exact (Shape.HasTypePi.lift (Nat.le_succ _)).2 hpi

/-- Field shapes fitting a telescope shape. -/
def TelFits : WShape n → List (WShape n) → Prop
  | _, [] => True
  | tel, x :: xs => ∃ b g, tel.piView = some (b, g) ∧ x.HasType b ∧ TelFits (g.app x) xs

theorem WShape.FitsPi.telFits {c : WShape (n+1)} {l : List (WShape (n+1))} (H : WShape.FitsPi c l) :
    TelFits c l := by
  induction H with
  | nil => trivial
  | cons h1 _ ih => exact ⟨_, _, rfl, h1, ih⟩


theorem ctysOK_tel {h : IndHead} {l : List (WShape n)}
    (H : Shape.ctysOK Shape.hasType h (l.map (·.1)) = true) (i : Nat) :
    (ctorTel h l i).HasType .type := by
  unfold ctorTel
  rw [List.getD_eq_getElem?_getD]
  cases e : l[h.nargs + i]? with
  | none => exact WShape.HasType.bot' WShape.HasType.sort
  | some x =>
    simp only [Option.getD_some]
    unfold Shape.ctysOK at H
    rw [List.all_eq_true] at H
    have hl := (List.getElem?_eq_some_iff.1 e).1
    have : x.1 ∈ (l.map (·.1)).drop h.nargs := by
      rw [List.mem_iff_getElem?]
      refine ⟨i, ?_⟩
      rw [List.getElem?_drop, List.getElem?_map, e]; rfl
    exact H _ this

omit [ShapeEnv] in
theorem _root_.List.Forall₂.getD' {R : α → β → Prop} {d : α} {d' : β} (hd : R d d') :
    ∀ {l l'}, List.Forall₂ R l l' → ∀ k, R (l.getD k d) (l'.getD k d')
  | _, _, .nil, _ => by simpa using hd
  | _, _, .cons h _, 0 => by simpa using h
  | _, _, .cons _ hs, k+1 => by simpa using getD' hd hs k

theorem ctorTel_mono {h : IndHead} {l l' : List (WShape n)} (hl : l.Forall₂ (· ≤ ·) l') (i : Nat) :
    ctorTel h l i ≤ ctorTel h l' i := hl.getD' WShape.LE.rfl _

theorem zipWith_join_getD : ∀ {l l' : List (WShape n)}, l.Forall₂ WShape.Compat l' → ∀ k,
    (l.zipWith WShape.join l').getD k .bot = (l.getD k .bot).join (l'.getD k .bot)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => rfl
  | _, _, .cons _ hs, k+1 => by simpa using zipWith_join_getD hs k

theorem ctorTel_join {h : IndHead} {l l' : List (WShape n)} (hl : l.Forall₂ WShape.Compat l')
    (i : Nat) : ctorTel h (l.zipWith WShape.join l') i = (ctorTel h l i).join (ctorTel h l' i) :=
  zipWith_join_getD hl _

/-- An inductive type shape's telescopes, where something is typed at it, are types. -/
theorem WShape.HasType.indTy_tels {m : WShape (n+1)} {h : IndHead} {l : List (WShape n)}
    (H : m.HasType (.indTy r h l)) (i : Nat) : (ctorTel h l i).HasType .type := by
  generalize ea : WShape.indTy r h l = a at H
  cases H.unfold with
  | bot h' =>
    subst ea
    generalize ea : WShape.indTy r h l = a at h'
    cases h'.unfold with
    | indTy _ hc =>
      obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 ea; exact ctysOK_tel hc i
    | _ => cases congrArg (·.1) ea
  | ctor hc =>
    obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 ea; exact ctysOK_tel (Bool.and_eq_true_iff.1 hc).1 i
  | _ => cases congrArg (·.1) ea

/-- An inductive type shape typed at a sort has telescopes that are types. -/
theorem WShape.HasType.indTy_tels' {h : IndHead} {l : List (WShape n)}
    (H : (WShape.indTy r h l).HasType (.sort j)) (i : Nat) : (ctorTel h l i).HasType .type := by
  generalize ea : WShape.indTy r h l = a at H
  cases H.unfold with
  | indTy _ hc => obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 ea; exact ctysOK_tel hc i
  | _ => cases congrArg (·.1) ea

/-- A shape typed at an inductive type shape is `bot` or a constructor shape. -/
theorem WShape.HasType.indTy_cases {m : WShape (n+1)} {h : IndHead} {l : List (WShape n)}
    (H : m.HasType (.indTy r h l)) : m = .bot ∨ ∃ c fs hf, m = .ctor c fs hf := by
  generalize ea : WShape.indTy r h l = a at H
  cases H.unfold with
  | bot => exact .inl rfl
  | ctor => exact .inr ⟨_, _, _, rfl⟩
  | _ => cases congrArg (·.1) ea

/-- A constructor shape typed at an inductive type shape fits its telescope. -/
theorem WShape.HasType.ctor_fits {h : IndHead} {l : List (WShape n)} {fs : List (WShape n)}
    {hf} (H : (WShape.ctor c fs hf).HasType (.indTy r h l)) :
    ∃ i, h.ctors.idxOf? c = some i ∧ TelFits (ctorTel h l i) fs := by
  generalize em : WShape.ctor c fs hf = m at H
  generalize ea : WShape.indTy r h l = a at H
  cases H.unfold with
  | ctor hc =>
    obtain ⟨rfl, rfl⟩ := WShape.ctor.inj.1 em
    obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 ea
    unfold Shape.ctorOK Shape.ctorTy at hc
    cases hi : h.ctors.idxOf? c with
    | none => simp [hi] at hc
    | some i =>
      refine ⟨i, rfl, ?_⟩
      simp only [hi, Option.map_some, Bool.and_eq_true] at hc
      have e : (l.map (·.1)).getD (h.nargs + i) Shape.bot = (ctorTel h l i).1 := by
        simp only [ctorTel, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases l[h.nargs + i]? <;> rfl
      rw [e] at hc
      cases n with
      | zero =>
        have := hc.2.1; simp [Shape.ctorFits] at this; subst this; trivial
      | succ n => exact (WShape.fitsPi_iff.1 hc.2.1).telFits
  | _ => first | cases congrArg (·.1) em | cases congrArg (·.1) ea


section
variable (IH : LogRel env U Γ n)

/-- Two telescopes of `k` binders related at shape `tel`: the domains are related types, and the
rests are related at related arguments. A shape that is not a pi type says nothing. -/
def TeleRel : Nat → VExpr → VExpr → WShape n → Prop
  | 0, _, _, _ => True
  | k+1, T, T', tel => tel.piView = none ∨ ∃ D B D' B' b g, tel.piView = some (b, g) ∧
    StepS env U Γ T (.forallE D B) ∧ StepS env U Γ T' (.forallE D' B') ∧
    TyEq env U Γ D D' ∧ IH.TyDefEq D D' b ∧
    ∀ a a' p, p.HasType b → env.IsDefEq U Γ a a' D → IH.DefEq a a' D p b →
      TeleRel k (B.inst a) (B'.inst a') (g.app p)

/-- Fields `ms` and `ns` related along the telescope `T` (instantiated with `ms`) at shape `tel`,
with field shapes `fs`. -/
def FieldsRel : VExpr → WShape n → List VExpr → List VExpr → List (WShape n) → Prop
  | _, _, [], [], [] => True
  | T, tel, m :: ms, n :: ns, x :: xs => ∃ D B b g, tel.piView = some (b, g) ∧
    StepS env U Γ T (.forallE D B) ∧ x.HasType b ∧ env.IsDefEq U Γ m n D ∧ IH.DefEq m n D x b ∧
    FieldsRel (B.inst m) (g.app x) ms ns xs
  | _, _, _, _, _ => False

end

variable {IH : LogRel env U Γ n}

omit [ShapeEnv] in
theorem forallE_whnf' : WHNF env U Γ (.forallE A B) := fun _ h => nomatch h

namespace TeleRel

theorem symm : ∀ {k T T'} {tel : WShape n}, TeleRel IH k T T' tel → TeleRel IH k T' T tel
  | 0, _, _, _, _ => trivial
  | _+1, _, _, _, .inl h => .inl h
  | _+1, _, _, _, .inr ⟨D, B, D', B', b, g, hv, r, r', hD, hDD, H⟩ =>
    .inr ⟨D', B', D, B, b, g, hv, r', r, hD.symm, IH.symm_ty hDD, fun a a' p hp ha hr =>
      symm (H a' a p hp (hD.symm.defeqDF ha.symm) (IH.conv (IH.symm_ty hDD) (IH.symm hr)))⟩

theorem trans (hU : StepUniq env) : ∀ {k T T' T''} {tel : WShape n},
    TeleRel IH k T T' tel → TeleRel IH k T' T'' tel → TeleRel IH k T T'' tel
  | 0, _, _, _, _, _, _ => trivial
  | _+1, _, _, _, _, .inl h, _ => .inl h
  | _+1, _, _, _, _, .inr ⟨_, _, _, _, _, _, hv, _⟩, .inl h => by rw [hv] at h; cases h
  | _+1, _, _, _, _, .inr ⟨D, B, D', B', b, g, hv, r, r', hD, hDD, H⟩,
      .inr ⟨D₂, B₂, D'', B'', b₂, g₂, hv2, r2, r'', hD2, hDD2, H2⟩ => by
    obtain ⟨rfl, rfl⟩ : D₂ = D' ∧ B₂ = B' := by
      have := StepS.determ hU r2 forallE_whnf' r' forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : b = b₂ ∧ g = g₂ := by rw [hv] at hv2; simpa using hv2
    refine .inr ⟨D, B, D'', B'', b, g, hv, r, r'', .trans hD hD2, IH.trans_ty hDD hDD2,
      fun a a'' p hp ha hr => trans hU (H a a'' p hp ha hr) (H2 a'' a'' p hp ?_ ?_)⟩
    · exact hD.defeqDF ha.hasType.2
    · exact IH.conv hDD (IH.left (IH.symm hr))

theorem left (hU : StepUniq env) (H : TeleRel IH k T T' tel) : TeleRel IH k T T tel :=
  H.trans hU H.symm

theorem right (hU : StepUniq env) (H : TeleRel IH k T T' tel) : TeleRel IH k T' T' tel :=
  H.symm.left hU

theorem whr (hU : StepUniq env) (hT : StepS env U Γ T T₁) (hT' : StepS env U Γ T' T₁') :
    ∀ {k}, TeleRel IH k T T' tel ↔ TeleRel IH k T₁ T₁' tel
  | 0 => .rfl
  | _+1 => by
    refine or_congr .rfl ⟨?_, ?_⟩
    · rintro ⟨D, B, D', B', b, g, hv, r, r', rest⟩
      exact ⟨D, B, D', B', b, g, hv, StepS.determ_l hU hT r forallE_whnf',
        StepS.determ_l hU hT' r' forallE_whnf', rest⟩
    · rintro ⟨D, B, D', B', b, g, hv, r, r', rest⟩
      exact ⟨D, B, D', B', b, g, hv, hT.trans r, hT'.trans r', rest⟩

/-- At a pi shape, a telescope relation gives the pi types. -/
theorem of_piView (H : TeleRel IH (k+1) T T' tel) (hv : tel.piView = some (b, g)) :
    ∃ D B D' B', StepS env U Γ T (.forallE D B) ∧ StepS env U Γ T' (.forallE D' B') ∧
    TyEq env U Γ D D' ∧ IH.TyDefEq D D' b ∧
    ∀ a a' p, p.HasType b → env.IsDefEq U Γ a a' D → IH.DefEq a a' D p b →
      TeleRel IH k (B.inst a) (B'.inst a') (g.app p) := by
  rcases H with h | ⟨D, B, D', B', b', g', hv', r, r', rest⟩
  · rw [hv] at h; cases h
  · obtain ⟨rfl, rfl⟩ : b = b' ∧ g = g' := by rw [hv] at hv'; simpa using hv'
    exact ⟨D, B, D', B', r, r', rest⟩

end TeleRel

namespace TeleRel

/-- A telescope relation at a shape holds at a smaller one. -/
theorem mono (hle : tel ≤ tel') (ht : tel.HasType .type) (ht' : tel'.HasType .type) :
    ∀ {k T T'}, TeleRel IH k T T' tel' → TeleRel IH k T T' tel
  | 0, _, _, _ => trivial
  | k+1, T, T', H => by
    cases hv : tel.piView with
    | none => exact .inl hv
    | some bg =>
      obtain ⟨b, g⟩ := bg
      obtain ⟨b', g', hv', hb, hg, hgm, -⟩ := WShape.piView_mono hle hv
      obtain ⟨D, B, D', B', r, r', hD, hDD, H⟩ := H.of_piView hv'
      have ⟨tb, tg⟩ := WShape.piView_type ht hv
      have ⟨tb', tg'⟩ := WShape.piView_type ht' hv'
      refine .inr ⟨D, B, D', B', b, g, hv, r, r', hD, IH.mono_r_2_ty hb tb tb' hDD,
        fun a a' p hp ha hr => ?_⟩
      have hp' := WShape.HasType.mono_r hb tb' hp
      have hr' := IH.mono_r_1 hb hp hp' (IH.left_ty hDD) hr
      exact mono (hg p) (tg p) (tg' p) (H a a' p hp' ha hr')

/-- Telescope relations at compatible shapes hold at their join. -/
theorem join (hU : StepUniq env) {k T T'} {tel₁ tel₂ : WShape n} (hC : tel₁.Compat tel₂)
    (ht₁ : tel₁.HasType .type) (ht₂ : tel₂.HasType .type) (H1 : TeleRel IH k T T' tel₁)
    (H2 : TeleRel IH k T T' tel₂) : TeleRel IH k T T' (tel₁.join tel₂) := by
  induction k generalizing T T' tel₁ tel₂ with
  | zero => trivial
  | succ k join =>
    cases hvJ : (tel₁.join tel₂).piView with
    | none => exact .inl hvJ
    | some bg =>
      obtain ⟨bJ, gJ⟩ := bg
      cases n with
      | zero => simp at hvJ
      | succ n =>
      obtain ⟨s, f, eJ, rfl, rfl⟩ := WShape.piView_eq_some hvJ
      have hJ := WShape.Join.mk hC
      rcases WShape.le_forallE_iff.1 (eJ ▸ hJ.le.1) with rfl | ⟨s₁, f₁, rfl, -, -⟩
      · rw [WShape.bot_join]; exact H2
      rcases WShape.le_forallE_iff.1 (eJ ▸ hJ.le.2) with rfl | ⟨s₂, f₂, rfl, -, -⟩
      · rw [WShape.join_bot]; exact H1
      have ⟨hC1, hC2⟩ := WShape.Compat.forallE_forallE.1 hC
      rw [WShape.forallE_join_forallE hC1 hC2] at eJ ⊢
      obtain ⟨rfl, rfl⟩ := WShape.forallE.inj.1 eJ
      obtain ⟨D, B, D', B', r, r', hD, hDD1, H1'⟩ := H1.of_piView WShape.piView_forallE
      obtain ⟨D₂, B₂, D₂', B₂', r₂, r₂', -, hDD2, H2'⟩ := H2.of_piView WShape.piView_forallE
      obtain ⟨rfl, rfl⟩ : D = D₂ ∧ B = B₂ := by
        have := StepS.determ hU r forallE_whnf' r₂ forallE_whnf'; simpa using this
      obtain ⟨rfl, rfl⟩ : D' = D₂' ∧ B' = B₂' := by
        have := StepS.determ hU r' forallE_whnf' r₂' forallE_whnf'; simpa using this
      have hpi₁ := WShape.piView_pi ht₁
      have hpi₂ := WShape.piView_pi ht₂
      have htJ := ht₁.join hC ht₂
      rw [WShape.forallE_join_forallE hC1 hC2] at htJ
      have hpiJ := WShape.piView_pi htJ
      have hCl : (s₁.lift (n+1)).Compat (s₂.lift (n+1)) := (WShape.Compat.lift (Nat.le_succ _)).2 hC1
      have hClf : WShapeFun.Compat (f₁.lift (n+1)) (f₂.lift (n+1)) := by
        simp only [WShapeFun.Compat, WShapeFun.lift_val (Nat.le_succ _),
          ShapeFun.Compat.lift (Nat.le_succ _)]; exact hC2
      have hJs := WShape.Join.mk hCl
      have hJf := WShapeFun.Join.mk hClf
      have es : (s₁.join s₂).lift (n+1) = (s₁.lift (n+1)).join (s₂.lift (n+1)) :=
        WShape.lift_join (Nat.le_succ _)
      have ef : (f₁.join f₂).lift (n+1) = (f₁.lift (n+1)).join (f₂.lift (n+1)) :=
        WShapeFun.lift_join' (Nat.le_succ _)
      refine .inr ⟨D, B, D', B', _, _, WShape.piView_forallE, r, r', hD, ?_,
        fun a a' p hp ha hr => ?_⟩
      · rw [es]; exact IH.join_ty hCl hpi₁.dom_isType hpi₂.dom_isType hDD1 hDD2
      have hsJ := hpiJ.dom_isType
      rw [es] at hp hr hsJ
      have go {s₀ : WShape n} {f₀ : WShapeFun n} (hpi : WShape.HasTypePi (f₀.lift (n+1)) (s₀.lift (n+1)) true)
          (hle : s₀.lift (n+1) ≤ (s₁.lift (n+1)).join (s₂.lift (n+1)))
          (Hh : ∀ a a' (p : WShape (n+1)), p.HasType (s₀.lift (n+1)) → env.IsDefEq U Γ a a' D →
            IH.DefEq a a' D p (s₀.lift (n+1)) → TeleRel IH k (B.inst a) (B'.inst a') ((f₀.lift (n+1)).app p)) :
          TeleRel IH k (B.inst a) (B'.inst a') ((f₀.lift (n+1)).app p) := by
        obtain ⟨d, hdle, hdt, hfd⟩ := WShape.HasDom.iff.1 hpi.1 p
        have hd1 := IH.mono_l hdle (WShape.HasType.mono_r hle hsJ hdt) hp hr
        have hd2 := IH.mono_r_2 hle hdt hsJ hd1
        exact mono hfd (hpi.app_isType p) (hpi.app_isType d) (Hh a a' d hdt ha hd2)
      have T1 := go hpi₁ hJs.le.1 H1'
      have T2 := go hpi₂ hJs.le.2 H2'
      have hJp := hJf.app_l p
      obtain ⟨hCp, -, hle'⟩ := WShape.Join.iff.1 hJp
      have TJ := join hCp (hpi₁.app_isType p) (hpi₂.app_isType p) T1 T2
      rw [ef]
      exact mono hle' (hJf.app_l p |> fun _ => by rw [← ef]; exact hpiJ.app_isType p)
        ((hpi₁.app_isType p).join hCp (hpi₂.app_isType p)) TJ

end TeleRel

namespace FieldsRel

/-- Fields related at a telescope shape are related at a smaller one, with smaller field shapes
fitting it. -/
theorem mono {T} {tel tel' : WShape n} {ms ns fs fs'} (hle : tel ≤ tel')
    (ht : tel.HasType .type) (ht' : tel'.HasType .type)
    (hfs : fs.Forall₂ (· ≤ ·) fs') (hfit : TelFits tel fs)
    (H : FieldsRel IH T tel' ms ns fs') : FieldsRel IH T tel ms ns fs := by
  induction hfs generalizing T tel tel' ms ns with
  | nil => cases ms <;> cases ns <;> first | trivial | simp [FieldsRel] at H
  | @cons x x' xs xs' hx _ ih =>
    cases ms <;> cases ns <;> try simp [FieldsRel] at H
    obtain ⟨b₀, g₀, hv₀, hxb, hfits⟩ := hfit
    obtain ⟨D, B, b', g', hv', r, hx', hd, hr, HF⟩ := H
    obtain ⟨b'', g'', hv'', hb, hg, -, hgm'⟩ := WShape.piView_mono hle hv₀
    rw [hv'] at hv''
    obtain ⟨rfl, rfl⟩ : b' = b'' ∧ g' = g'' := by simpa using hv''
    have ⟨tb, tg⟩ := WShape.piView_type ht hv₀
    have ⟨tb', tg'⟩ := WShape.piView_type ht' hv'
    have hxb' := WShape.HasType.mono_r hb tb' hxb
    have hr1 := IH.mono_l hx hxb' hx' hr
    exact ⟨D, B, b₀, g₀, hv₀, r, hxb, hd, IH.mono_r_2 hb hxb tb' hr1,
      ih ((hg x).trans (hgm' _ _ hx)) (tg x) (tg' x') hfits HF⟩

/-- Fields related at a telescope shape are related at a larger one they fit, along a telescope
related to itself there. -/
theorem mono_up (hU : StepUniq env) {T} {tel tel' : WShape n} {ms ns fs} (hle : tel ≤ tel')
    (ht : tel.HasType .type) (ht' : tel'.HasType .type)
    (hfit' : TelFits tel' fs) (HT : TeleRel IH fs.length T T tel')
    (H : FieldsRel IH T tel ms ns fs) : FieldsRel IH T tel' ms ns fs := by
  induction fs generalizing T tel tel' ms ns with
  | nil => cases ms <;> cases ns <;> first | trivial | simp [FieldsRel] at H
  | cons x xs ih =>
    cases ms <;> cases ns <;> try simp [FieldsRel] at H
    obtain ⟨D, B, b, g, hv, r, hxb, hd, hr, HF⟩ := H
    obtain ⟨b', g', hv', hb, hg, -, -⟩ := WShape.piView_mono hle hv
    obtain ⟨b₀, g₀, hv₀, hxb', hfits⟩ := hfit'
    rw [hv'] at hv₀
    obtain ⟨rfl, rfl⟩ : b' = b₀ ∧ g' = g₀ := by simpa using hv₀
    obtain ⟨D₁, B₁, D₂, B₂, r₁, r₂, -, hDD, HT'⟩ := HT.of_piView hv'
    obtain ⟨rfl, rfl⟩ : D = D₁ ∧ B = B₁ := by
      have := StepS.determ hU r forallE_whnf' r₁ forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D = D₂ ∧ B = B₂ := by
      have := StepS.determ hU r forallE_whnf' r₂ forallE_whnf'; simpa using this
    have ⟨tb, tg⟩ := WShape.piView_type ht hv
    have ⟨tb', tg'⟩ := WShape.piView_type ht' hv'
    have hr' := IH.mono_r_1 hb hxb hxb' hDD hr
    exact ⟨_, _, b', g', hv', r, hxb', hd, hr',
      ih (hg x) (tg x) (tg' x) hfits (HT' _ _ _ hxb' hd.hasType.1 (IH.left hr')) HF⟩

end FieldsRel

/-- Field shapes fitting a telescope shape fit a larger one. -/
theorem TelFits.mono_up : ∀ {tel tel' : WShape n} {fs : List (WShape n)}, tel ≤ tel' →
    tel'.HasType .type → TelFits tel fs → TelFits tel' fs
  | _, _, [], _, _, _ => trivial
  | _, _, x :: _, hle, ht', H => by
    obtain ⟨_, g, hv, hxb, H⟩ := H
    obtain ⟨b', g', hv', hb, hg, -, -⟩ := WShape.piView_mono hle hv
    have ⟨tb', tg'⟩ := WShape.piView_type ht' hv'
    exact ⟨b', g', hv', WShape.HasType.mono_r hb tb' hxb, mono_up (hg x) (tg' x) H⟩

omit [ShapeEnv] in
theorem _root_.List.Forall₂.length_eq' {R : α → β → Prop} :
    ∀ {l l'}, List.Forall₂ R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (length_eq' h)

/-- Fields related at two compatible field shapes are related at their join. -/
theorem FieldsRel.join (hU : StepUniq env) {T} {tel : WShape n} {ms ns}
    {fs₁ fs₂ : List (WShape n)}
    (hC : fs₁.Forall₂ WShape.Compat fs₂) (ht : tel.HasType .type)
    (hfit₁ : TelFits tel fs₁) (hfit₂ : TelFits tel fs₂) (HT : TeleRel IH fs₁.length T T tel)
    (H1 : FieldsRel IH T tel ms ns fs₁) (H2 : FieldsRel IH T tel ms ns fs₂) :
    FieldsRel IH T tel ms ns (fs₁.zipWith WShape.join fs₂) := by
  induction hC generalizing T tel ms ns with
  | nil => cases ms <;> cases ns <;> first | trivial | simp [FieldsRel] at H1
  | @cons x₁ x₂ xs₁ xs₂ hc hcs ih =>
    cases ms <;> cases ns <;> try simp [FieldsRel] at H1
    rename_i m ms n ns
    obtain ⟨D, B, b, g, hv, r, hx₁, hd, hr₁, HF₁⟩ := H1
    obtain ⟨D', B', b', g', hv', r', hx₂, -, hr₂, HF₂⟩ := H2
    obtain ⟨rfl, rfl⟩ : b = b' ∧ g = g' := by rw [hv] at hv'; simpa using hv'
    obtain ⟨rfl, rfl⟩ : D = D' ∧ B = B' := by
      have := StepS.determ hU r forallE_whnf' r' forallE_whnf'; simpa using this
    obtain ⟨b₁, g₁, hv₁, -, hf₁⟩ := hfit₁
    obtain ⟨b₂, g₂, hv₂, -, hf₂⟩ := hfit₂
    rw [hv] at hv₁ hv₂
    obtain ⟨rfl, rfl⟩ : b = b₁ ∧ g = g₁ := by simpa using hv₁
    obtain ⟨rfl, rfl⟩ : b = b₂ ∧ g = g₂ := by simpa using hv₂
    obtain ⟨-, tg⟩ := WShape.piView_type ht hv
    have hJ := WShape.Join.mk hc
    have hxJ := WShape.HasType.join hc hx₁ hx₂
    have hrJ := IH.join hc hx₁ hx₂ hr₁ hr₂
    obtain ⟨D₁, B₁, D₂, B₂, r₁, r₂, -, -, HT'⟩ := HT.of_piView hv
    obtain ⟨rfl, rfl⟩ : D = D₁ ∧ B = B₁ := by
      have := StepS.determ hU r forallE_whnf' r₁ forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D = D₂ ∧ B = B₂ := by
      have := StepS.determ hU r forallE_whnf' r₂ forallE_whnf'; simpa using this
    have HTJ := HT' m m _ hxJ hd.hasType.1 (IH.left hrJ)
    have le₁ : g.app x₁ ≤ g.app (x₁.join x₂) := WShapeFun.app_mono_r hJ.le.1
    have le₂ : g.app x₂ ≤ g.app (x₁.join x₂) := WShapeFun.app_mono_r hJ.le.2
    have hf₁' := TelFits.mono_up le₁ (tg _) hf₁
    have hf₂' := TelFits.mono_up le₂ (tg _) hf₂
    have hl : xs₂.length = xs₁.length := hcs.length_eq'.symm
    have HTJ₂ : TeleRel IH xs₂.length (B.inst m) (B.inst m) (g.app (x₁.join x₂)) := hl ▸ HTJ
    refine ⟨D, B, b, g, hv, r, hxJ, hd, hrJ, ih (tg _) hf₁' hf₂' HTJ ?_ ?_⟩
    · exact HF₁.mono_up hU le₁ (tg _) (tg _) hf₁' HTJ
    · exact HF₂.mono_up hU le₂ (tg _) (tg _) hf₂' HTJ₂

namespace FieldsRel

theorem length : ∀ {T} {tel : WShape n} {ms ns fs}, FieldsRel IH T tel ms ns fs →
    ms.length = fs.length ∧ ns.length = fs.length
  | _, _, [], [], [], _ => ⟨rfl, rfl⟩
  | _, _, _ :: _, _ :: _, _ :: _, ⟨_, _, _, _, _, _, _, _, _, H⟩ => by
    have := length H; simp [this.1, this.2]
  | _, _, [], [], _ :: _, h | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h
  | _, _, _ :: _, _ :: _, [], h => h.elim

theorem left : ∀ {T} {tel : WShape n} {ms ns fs}, FieldsRel IH T tel ms ns fs →
    FieldsRel IH T tel ms ms fs
  | _, _, [], [], [], _ => trivial
  | _, _, _ :: _, _ :: _, _ :: _, ⟨D, B, b, g, hv, r, hx, hd, hr, H⟩ =>
    ⟨D, B, b, g, hv, r, hx, hd.hasType.1, IH.left hr, left H⟩
  | _, _, [], [], _ :: _, h | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h
  | _, _, _ :: _, _ :: _, [], h => h.elim

/-- Fields related along one telescope are related along a related one. -/
theorem conv (hU : StepUniq env) : ∀ {T T'} {tel : WShape n} {ms ns fs},
    TeleRel IH fs.length T T' tel → FieldsRel IH T tel ms ns fs → FieldsRel IH T' tel ms ns fs
  | _, _, _, [], [], [], _, _ => trivial
  | _, _, _, _ :: _, _ :: _, _ :: _, HT, ⟨D, B, b, g, hv, r, hx, hd, hr, HF⟩ => by
    obtain ⟨D₁, B₁, D', B', r₁, r', hD, hDD, H⟩ := HT.of_piView hv
    obtain ⟨rfl, rfl⟩ : D = D₁ ∧ B = B₁ := by
      have := StepS.determ hU r forallE_whnf' r₁ forallE_whnf'; simpa using this
    exact ⟨D', B', b, g, hv, r', hx, hD.defeqDF hd, IH.conv hDD hr,
      conv hU (H _ _ _ hx hd.hasType.1 (IH.left hr)) HF⟩
  | _, _, _, [], [], _ :: _, _, h | _, _, _, [], _ :: _, _, _, h | _, _, _, _ :: _, [], _, _, h
  | _, _, _, _ :: _, _ :: _, [], _, h => h.elim

theorem symm (hU : StepUniq env) : ∀ {T} {tel : WShape n} {ms ns fs},
    TeleRel IH fs.length T T tel → FieldsRel IH T tel ms ns fs → FieldsRel IH T tel ns ms fs
  | _, _, [], [], [], _, _ => trivial
  | _, _, _ :: _, _ :: _, _ :: _, HT, ⟨D, B, b, g, hv, r, hx, hd, hr, HF⟩ => by
    obtain ⟨D₁, B₁, D₂, B₂, r₁, r₂, -, -, H⟩ := HT.of_piView hv
    obtain ⟨rfl, rfl⟩ : D = D₁ ∧ B = B₁ := by
      have := StepS.determ hU r forallE_whnf' r₁ forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D = D₂ ∧ B = B₂ := by
      have := StepS.determ hU r forallE_whnf' r₂ forallE_whnf'; simpa using this
    have hm := H _ _ _ hx hd.hasType.1 (IH.left hr)
    exact ⟨_, _, b, g, hv, r, hx, hd.symm, IH.symm hr, conv hU (H _ _ _ hx hd hr) (symm hU hm HF)⟩
  | _, _, [], [], _ :: _, _, h | _, _, [], _ :: _, _, _, h | _, _, _ :: _, [], _, _, h
  | _, _, _ :: _, _ :: _, [], _, h => h.elim

theorem trans (hU : StepUniq env) {T} {tel : WShape n} {ms ns ps fs}
    (HT : TeleRel IH fs.length T T tel) (H1 : FieldsRel IH T tel ms ns fs)
    (H2 : FieldsRel IH T tel ns ps fs) : FieldsRel IH T tel ms ps fs := by
  induction fs generalizing T tel ms ns ps with
  | nil =>
    cases ms <;> cases ns <;> cases ps <;> first | trivial | simp [FieldsRel] at H1 H2
  | cons x xs ih =>
    cases ms <;> cases ns <;> cases ps <;> try simp [FieldsRel] at H1 H2
    obtain ⟨D, B, b, g, hv, r, hx, hd, hr, HF⟩ := H1
    obtain ⟨D', B', b', g', hv', r', _, hd', hr', HF'⟩ := H2
    obtain ⟨D₁, B₁, D₂, B₂, r₁, r₂, -, -, H⟩ := HT.of_piView hv
    obtain ⟨rfl, rfl⟩ : D = D₁ ∧ B = B₁ := by
      have := StepS.determ hU r forallE_whnf' r₁ forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D = D₂ ∧ B = B₂ := by
      have := StepS.determ hU r forallE_whnf' r₂ forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : D = D' ∧ B = B' := by
      have := StepS.determ hU r forallE_whnf' r' forallE_whnf'; simpa using this
    obtain ⟨rfl, rfl⟩ : b = b' ∧ g = g' := by rw [hv] at hv'; simpa using hv'
    have hnm := H _ _ _ hx hd.symm (IH.symm hr)
    have hmm := H _ _ _ hx hd.hasType.1 (IH.left hr)
    exact ⟨_, _, b, g, hv, r, hx, hd.trans hd', IH.trans hr hr', ih hmm HF (conv hU hnm HF')⟩

end FieldsRel

section
variable (IH : LogRel env U Γ n)

/-- The constructors' telescopes of two applications of the inductive type `h` are related at
the type shape's telescopes `l`. -/
def IndTele (h : IndHead) (l : List (WShape n)) (M N : VExpr) : Prop :=
  ∀ ls As ls' As', StepS env U Γ M ((VExpr.const h.name ls).appN As) →
    StepS env U Γ N ((VExpr.const h.name ls').appN As') →
    ∀ c i k ci, h.ctors.idxOf? c = some i → h.arities[i]? = some k → env.constants c = some ci →
    TeleRel IH k (ctorTeleAt ci k ls As) (ctorTeleAt ci k ls' As') (ctorTel h l i)

/-- Two values of an inductive type at a constructor shape: both reduce to applications of the
constructor whose fields are related along its telescope at the type's arguments. -/
def CtorVal (h : IndHead) (l : List (WShape n)) (A M N : VExpr) (c : Name)
    (fs : List (WShape n)) : Prop :=
  Inert env h.name ∧ Inert env c ∧ IndTele IH h l A A ∧
  ∃ i k ci lsA AsA ls qs ms ls' qs' ns, h.ctors.idxOf? c = some i ∧ h.arities[i]? = some k ∧
    env.constants c = some ci ∧ StepS env U Γ A ((VExpr.const h.name lsA).appN AsA) ∧
    StepS env U Γ M ((VExpr.const c ls).appN (qs ++ ms)) ∧
    StepS env U Γ N ((VExpr.const c ls').appN (qs' ++ ns)) ∧ fs.length = k ∧
    FieldsRel IH (ctorTeleAt ci k lsA AsA) (ctorTel h l i) ms ns fs

/-- Two values of a structure at a constructor shape, related extensionally: their weak head
normal forms' projections are related along the constructor's telescope at the type's
arguments. -/
def StructVal (h : IndHead) (l : List (WShape n)) (A M N : VExpr) (c : Name)
    (fs : List (WShape n)) : Prop :=
  Inert env h.name ∧ IndTele IH h l A A ∧
  ∃ i k ci lsA AsA M' N', h.ctors.idxOf? c = some i ∧ h.arities[i]? = some k ∧
    env.constants c = some ci ∧ StepS env U Γ A ((VExpr.const h.name lsA).appN AsA) ∧
    StepS env U Γ M M' ∧ WHNF env U Γ M' ∧ StepS env U Γ N N' ∧ WHNF env U Γ N' ∧
    fs.length = k ∧
    FieldsRel IH (ctorTeleAt ci k lsA AsA) (ctorTel h l i) (VExpr.projs h.name k M')
      (VExpr.projs h.name k N') fs

end

namespace IndTele

theorem symm (H : IndTele IH h l M N) : IndTele IH h l N M :=
  fun _ _ _ _ r1 r2 _ _ _ _ hi hk hc => (H _ _ _ _ r2 r1 _ _ _ _ hi hk hc).symm

theorem trans (hU : StepUniq env)
    (hM : ∃ ls As, StepS env U Γ M₂ ((VExpr.const h.name ls).appN As))
    (H1 : IndTele IH h l M₁ M₂) (H2 : IndTele IH h l M₂ M₃) : IndTele IH h l M₁ M₃ :=
  let ⟨_, _, r⟩ := hM
  fun _ _ _ _ r1 r3 _ _ _ _ hi hk hc =>
    (H1 _ _ _ _ r1 r _ _ _ _ hi hk hc).trans hU (H2 _ _ _ _ r r3 _ _ _ _ hi hk hc)

theorem whr (hU : StepUniq env) (hn : Inert env h.name) (hM : StepS env U Γ M M')
    (hN : StepS env U Γ N N') : IndTele IH h l M N ↔ IndTele IH h l M' N' := by
  constructor
  · intro H _ _ _ _ r1 r2; exact H _ _ _ _ (hM.trans r1) (hN.trans r2)
  · intro H _ _ _ _ r1 r2
    exact H _ _ _ _ (StepS.determ_l hU hM r1 hn.whnf) (StepS.determ_l hU hN r2 hn.whnf)


theorem mono (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (H : IndTele IH h l' M N) : IndTele IH h l M N :=
  fun _ _ _ _ r1 r2 _ i _ _ hi hk hci =>
    (H _ _ _ _ r1 r2 _ i _ _ hi hk hci).mono (ctorTel_mono hl i) (htel i) (htel' i)

theorem join (hU : StepUniq env) (hl : l.Forall₂ WShape.Compat l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (H1 : IndTele IH h l M N) (H2 : IndTele IH h l' M N) :
    IndTele IH h (l.zipWith WShape.join l') M N :=
  fun _ _ _ _ r1 r2 _ i _ _ hi hk hci => by
    rw [ctorTel_join hl]
    exact TeleRel.join hU (hl.getD' (WShape.Compat.iff.2 ⟨.bot, WShape.LE.rfl, WShape.LE.rfl⟩) _)
      (htel i) (htel' i) (H1 _ _ _ _ r1 r2 _ i _ _ hi hk hci) (H2 _ _ _ _ r1 r2 _ i _ _ hi hk hci)

end IndTele

omit [ShapeEnv] in
private theorem forall₂_length {R : α → β → Prop} : ∀ {l l'}, List.Forall₂ R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (forall₂_length h)

private theorem forall₂_le_refl : ∀ (l : List (WShape n)), l.Forall₂ (· ≤ ·) l
  | [] => .nil
  | _ :: l => .cons WShape.LE.rfl (forall₂_le_refl l)

namespace CtorVal

theorem left (H : CtorVal IH h l A M N c fs) : CtorVal IH h l A M M c fs :=
  let ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, _, _, _, h1, h2, h3, h4, h5, _, h7, hF⟩ := H
  ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls, qs, ms, h1, h2, h3, h4, h5, h5, h7, hF.left⟩

theorem symm (hU : StepUniq env) (H : CtorVal IH h l A M N c fs) : CtorVal IH h l A N M c fs := by
  obtain ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF⟩ := H
  exact ⟨hn, hc, hT, i, fs.length, ci, lsA, AsA, ls', qs', ns, ls, qs, ms, h1, h2, h3, h4, h6, h5,
    rfl, hF.symm hU (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)⟩

omit [ShapeEnv] in
theorem appN_split (hU : StepUniq env) (hc : Inert env c)
    (r1 : StepS env U Γ N ((VExpr.const c ls).appN (qs ++ ms)))
    (r2 : StepS env U Γ N ((VExpr.const c ls').appN (qs' ++ ms')))
    (hl : ms.length = ms'.length) : ls = ls' ∧ qs = qs' ∧ ms = ms' := by
  have := StepS.determ hU r1 hc.whnf r2 hc.whnf
  obtain ⟨-, rfl, h⟩ := appN_const_inj this
  obtain ⟨rfl, rfl⟩ := List.append_inj' h hl
  exact ⟨rfl, rfl, rfl⟩

theorem trans (hU : StepUniq env) (H1 : CtorVal IH h l A M N c fs)
    (H2 : CtorVal IH h l A N P c fs) : CtorVal IH h l A M P c fs := by
  obtain ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF⟩ := H1
  obtain ⟨-, -, -, i', k', ci', lsA', AsA', ls₂, qs₂, ns₂, ls'', qs'', ps, h1', h2', h3', h4', h5',
    h6', hk, hF'⟩ := H2
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [h3] at h3'; cases h3'
  have := StepS.determ hU h4 hn.whnf h4' hn.whnf
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj this
  obtain ⟨rfl, rfl, rfl⟩ := appN_split hU hc h6 h5'
    (by rw [hF.length.2, hF'.length.1])
  exact ⟨hn, hc, hT, i, _, ci, lsA, AsA, ls, qs, ms, ls'', qs'', ps, h1, h2, h3, h4, h5, h6', rfl,
    hF.trans hU (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3) hF'⟩

theorem conv (hU : StepUniq env)
    (hB : ∃ ls As, StepS env U Γ B ((VExpr.const h.name ls).appN As))
    (hAB : IndTele IH h l A B) (hBB : IndTele IH h l B B)
    (H : CtorVal IH h l A M N c fs) : CtorVal IH h l B M N c fs := by
  obtain ⟨hn, hc, -, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF⟩ := H
  obtain ⟨lsB, AsB, rB⟩ := hB
  exact ⟨hn, hc, hBB, i, _, ci, lsB, AsB, ls, qs, ms, ls', qs', ns, h1, h2, h3, rB, h5, h6, rfl,
    hF.conv hU (hAB _ _ _ _ h4 rB _ _ _ _ h1 h2 h3)⟩

theorem whr (hU : StepUniq env) (hc : Inert env c) (hM : StepS env U Γ M M')
    (hN : StepS env U Γ N N') : CtorVal IH h l A M N c fs ↔ CtorVal IH h l A M' N' c fs := by
  constructor
  · rintro ⟨hn, hc', hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, h7,
      hF⟩
    exact ⟨hn, hc', hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4,
      StepS.determ_l hU hM h5 hc.whnf, StepS.determ_l hU hN h6 hc.whnf, h7, hF⟩
  · rintro ⟨hn, hc', hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, h7,
      hF⟩
    exact ⟨hn, hc', hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4,
      hM.trans h5, hN.trans h6, h7, hF⟩

theorem inert (H : CtorVal IH h l A M N c fs) : Inert env c := H.2.1

theorem red_l (H : CtorVal IH h l A M N c fs) :
    ∃ ls as, StepS env U Γ M ((VExpr.const c ls).appN as) :=
  let ⟨_, _, _, _, _, _, _, _, ls, qs, ms, _, _, _, _, _, _, _, h5, _⟩ := H; ⟨ls, qs ++ ms, h5⟩

theorem red_r (H : CtorVal IH h l A M N c fs) :
    ∃ ls as, StepS env U Γ N ((VExpr.const c ls).appN as) :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, ls', qs', ns, _, _, _, _, _, h6, _⟩ := H
  ⟨ls', qs' ++ ns, h6⟩

theorem red_A (H : CtorVal IH h l A M N c fs) :
    ∃ ls As, StepS env U Γ A ((VExpr.const h.name ls).appN As) :=
  let ⟨_, _, _, _, _, _, lsA, AsA, _, _, _, _, _, _, _, _, _, h4, _⟩ := H; ⟨lsA, AsA, h4⟩


theorem mono_r (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs)
    (H : CtorVal IH h l' A M N c fs) : CtorVal IH h l A M N c fs := by
  obtain ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, h7,
    hF⟩ := H
  refine ⟨hn, hc, fun _ _ _ _ r1 r2 _ i' _ _ hi hk hci => ?_, i, k, ci, lsA, AsA, ls, qs, ms, ls',
    qs', ns, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  · exact (hT _ _ _ _ r1 r2 _ i' _ _ hi hk hci).mono (ctorTel_mono hl i') (htel i') (htel' i')
  · exact hF.mono (ctorTel_mono hl i) (htel i) (htel' i)
      (forall₂_le_refl fs) (hfit i h1)

theorem mono_up (hU : StepUniq env) (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit' : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l' i) fs)
    (hT' : IndTele IH h l' A A) (H : CtorVal IH h l A M N c fs) : CtorVal IH h l' A M N c fs := by
  obtain ⟨hn, hc, -, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF⟩ := H
  exact ⟨hn, hc, hT', i, _, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF.mono_up hU (ctorTel_mono hl i) (htel i) (htel' i) (hfit' i h1)
      (hT' _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)⟩

theorem join (hU : StepUniq env) {fs₁ fs₂ : List (WShape n)} (hC : fs₁.Forall₂ WShape.Compat fs₂)
    (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit₁ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₁)
    (hfit₂ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₂)
    (H1 : CtorVal IH h l A M N c fs₁) (H2 : CtorVal IH h l A M N c fs₂) :
    CtorVal IH h l A M N c (fs₁.zipWith WShape.join fs₂) := by
  obtain ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, rfl,
    hF⟩ := H1
  obtain ⟨-, -, -, i', k', ci', lsA', AsA', ls₂, qs₂, ms₂, ls₂', qs₂', ns₂, h1', h2', h3', h4', h5',
    h6', hk, hF'⟩ := H2
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [h3] at h3'; cases h3'
  have := StepS.determ hU h4 hn.whnf h4' hn.whnf
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj this
  have hl : fs₂.length = fs₁.length := hk
  obtain ⟨rfl, rfl, rfl⟩ := appN_split hU hc h5 h5' (by rw [hF.length.1, hF'.length.1, hl])
  obtain ⟨rfl, rfl, rfl⟩ := appN_split hU hc h6 h6' (by rw [hF.length.2, hF'.length.2, hl])
  refine ⟨hn, hc, hT, i, _, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, ?_,
    FieldsRel.join hU hC (htel i) (hfit₁ i h1) (hfit₂ i h1) (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)
      hF hF'⟩
  simp [List.length_zipWith, hl]

theorem mono_l (hfs : fs.Forall₂ (· ≤ ·) fs')
    (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs)
    (H : CtorVal IH h l A M N c fs') : CtorVal IH h l A M N c fs := by
  obtain ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6, h7,
    hF⟩ := H
  exact ⟨hn, hc, hT, i, k, ci, lsA, AsA, ls, qs, ms, ls', qs', ns, h1, h2, h3, h4, h5, h6,
    (forall₂_length hfs).trans h7,
    hF.mono WShape.LE.rfl (htel i) (htel i) hfs (hfit i h1)⟩

end CtorVal

namespace StructVal

theorem left (H : StructVal IH h l A M N c fs) : StructVal IH h l A M M c fs :=
  let ⟨hn, hT, i, k, ci, lsA, AsA, M', _, h1, h2, h3, h4, h5, h6, _, _, h9, hF⟩ := H
  ⟨hn, hT, i, k, ci, lsA, AsA, M', M', h1, h2, h3, h4, h5, h6, h5, h6, h9, hF.left⟩

theorem symm (hU : StepUniq env) (H : StructVal IH h l A M N c fs) :
    StructVal IH h l A N M c fs := by
  obtain ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl, hF⟩ := H
  exact ⟨hn, hT, i, _, ci, lsA, AsA, N', M', h1, h2, h3, h4, h7, h8, h5, h6, rfl,
    hF.symm hU (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)⟩

theorem trans (hU : StepUniq env) (H1 : StructVal IH h l A M N c fs)
    (H2 : StructVal IH h l A N P c fs) : StructVal IH h l A M P c fs := by
  obtain ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl, hF⟩ := H1
  obtain ⟨-, -, i', k', ci', lsA', AsA', N₂, P', h1', h2', h3', h4', h5', h6', h7', h8', hk, hF'⟩ :=
    H2
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [h3] at h3'; cases h3'
  have := StepS.determ hU h4 hn.whnf h4' hn.whnf
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj this
  cases StepS.determ hU h7 h8 h5' h6'
  exact ⟨hn, hT, i, _, ci, lsA, AsA, M', P', h1, h2, h3, h4, h5, h6, h7', h8', rfl,
    hF.trans hU (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3) hF'⟩

theorem conv (hU : StepUniq env)
    (hB : ∃ ls As, StepS env U Γ B ((VExpr.const h.name ls).appN As))
    (hAB : IndTele IH h l A B) (hBB : IndTele IH h l B B)
    (H : StructVal IH h l A M N c fs) : StructVal IH h l B M N c fs := by
  obtain ⟨hn, -, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl, hF⟩ := H
  obtain ⟨lsB, AsB, rB⟩ := hB
  exact ⟨hn, hBB, i, _, ci, lsB, AsB, M', N', h1, h2, h3, rB, h5, h6, h7, h8, rfl,
    hF.conv hU (hAB _ _ _ _ h4 rB _ _ _ _ h1 h2 h3)⟩

theorem whr (hU : StepUniq env) (hM : StepS env U Γ M M₁) (hN : StepS env U Γ N N₁) :
    StructVal IH h l A M N c fs ↔ StructVal IH h l A M₁ N₁ c fs := by
  constructor
  · rintro ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, h9, hF⟩
    exact ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, StepS.determ_l hU hM h5 h6, h6,
      StepS.determ_l hU hN h7 h8, h8, h9, hF⟩
  · rintro ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, h9, hF⟩
    exact ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, hM.trans h5, h6, hN.trans h7, h8,
      h9, hF⟩

theorem red_A (H : StructVal IH h l A M N c fs) :
    ∃ ls As, StepS env U Γ A ((VExpr.const h.name ls).appN As) :=
  let ⟨_, _, _, _, _, lsA, AsA, _, _, _, _, _, h4, _⟩ := H; ⟨lsA, AsA, h4⟩

theorem mono_r (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs)
    (H : StructVal IH h l' A M N c fs) : StructVal IH h l A M N c fs := by
  obtain ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, h9, hF⟩ := H
  refine ⟨hn, fun _ _ _ _ r1 r2 _ i' _ _ hi hk hci => ?_, i, k, ci, lsA, AsA, M', N',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  · exact (hT _ _ _ _ r1 r2 _ i' _ _ hi hk hci).mono (ctorTel_mono hl i') (htel i') (htel' i')
  · exact hF.mono (ctorTel_mono hl i) (htel i) (htel' i) (forall₂_le_refl fs) (hfit i h1)

theorem mono_up (hU : StepUniq env) (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit' : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l' i) fs)
    (hT' : IndTele IH h l' A A) (H : StructVal IH h l A M N c fs) :
    StructVal IH h l' A M N c fs := by
  obtain ⟨hn, -, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl, hF⟩ := H
  exact ⟨hn, hT', i, _, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl,
    hF.mono_up hU (ctorTel_mono hl i) (htel i) (htel' i) (hfit' i h1)
      (hT' _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)⟩

theorem mono_l (hfs : fs.Forall₂ (· ≤ ·) fs')
    (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs)
    (H : StructVal IH h l A M N c fs') : StructVal IH h l A M N c fs := by
  obtain ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, h9, hF⟩ := H
  exact ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8,
    (forall₂_length hfs).trans h9, hF.mono WShape.LE.rfl (htel i) (htel i) hfs (hfit i h1)⟩

theorem join (hU : StepUniq env) {fs₁ fs₂ : List (WShape n)} (hC : fs₁.Forall₂ WShape.Compat fs₂)
    (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit₁ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₁)
    (hfit₂ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₂)
    (H1 : StructVal IH h l A M N c fs₁) (H2 : StructVal IH h l A M N c fs₂) :
    StructVal IH h l A M N c (fs₁.zipWith WShape.join fs₂) := by
  obtain ⟨hn, hT, i, k, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, rfl, hF⟩ := H1
  obtain ⟨-, -, i', k', ci', lsA', AsA', M₂, N₂, h1', h2', h3', h4', h5', h6', h7', h8', hk, hF'⟩ :=
    H2
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [h3] at h3'; cases h3'
  have := StepS.determ hU h4 hn.whnf h4' hn.whnf
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj this
  cases StepS.determ hU h5 h6 h5' h6'
  cases StepS.determ hU h7 h8 h7' h8'
  have hl : fs₂.length = fs₁.length := hk
  refine ⟨hn, hT, i, _, ci, lsA, AsA, M', N', h1, h2, h3, h4, h5, h6, h7, h8, ?_,
    FieldsRel.join hU hC (htel i) (hfit₁ i h1) (hfit₂ i h1) (hT _ _ _ _ h4 h4 _ _ _ _ h1 h2 h3)
      hF (hl ▸ hF')⟩
  simp [List.length_zipWith, hl]

end StructVal

/-! ### Lifting to a greater depth -/

theorem WShape.piView_lift (tel : WShape n) :
    (tel.lift (n+1)).piView = tel.piView.map (fun bg => (bg.1.lift (n+1), bg.2.lift (n+1))) := by
  cases n with
  | zero => rcases tel with ⟨s, wf⟩; cases s <;> rfl
  | succ k =>
    cases tel using WShape.casesOn' with
    | forallE s f =>
      rw [WShape.lift_forallE (Nat.le_succ k), WShape.piView_forallE, WShape.piView_forallE]
      simp only [Option.map_some, WShape.lift_lift (.inl (Nat.le_succ _)),
        WShapeFun.lift_lift (.inl (Nat.le_succ _))]
    | bot => rw [WShape.lift_bot]; rfl
    | sort => rw [WShape.lift_sort]; rfl
    | lam => rw [WShape.lift_lam (Nat.le_succ k)]; rfl
    | ctor => rw [WShape.lift_ctor (Nat.le_succ k)]; rfl
    | indTy => rw [WShape.lift_indTy (Nat.le_succ k)]; rfl

theorem WShape.piView_pi' {tel : WShape n} (ht : tel.HasType .type)
    (hv : tel.piView = some (b, g)) : WShape.HasTypePi g b true := by
  cases n with
  | zero => simp at hv
  | succ n =>
    obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
    exact WShape.piView_pi ht

theorem ctorTel_lift {h : IndHead} (l : List (WShape n)) (i : Nat) :
    ctorTel h (l.map (·.lift (n+1))) i = (ctorTel h l i).lift (n+1) := by
  unfold ctorTel
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[h.nargs + i]? <;> simp

section
variable {IH : LogRel env U Γ n} {IH' : LogRel env U Γ (n+1)}
  (hT : ∀ {M N} {m : WShape n}, m.HasType .type →
    (IH'.TyDefEq M N (m.lift (n+1)) ↔ IH.TyDefEq M N m))
  (hD : ∀ {M N A} {m a : WShape n}, m.HasType a →
    (IH'.DefEq M N A (m.lift (n+1)) (a.lift (n+1)) ↔ IH.DefEq M N A m a))
include hT hD

theorem TeleRel.lift : ∀ {k T T'} {tel : WShape n}, tel.HasType .type →
    (TeleRel IH' k T T' (tel.lift (n+1)) ↔ TeleRel IH k T T' tel)
  | 0, _, _, _, _ => .rfl
  | k+1, T, T', tel, ht => by
    cases hv : tel.piView with
    | none =>
      have hv' : (tel.lift (n+1)).piView = none := by rw [WShape.piView_lift, hv]; rfl
      exact ⟨fun _ => .inl hv, fun _ => .inl hv'⟩
    | some bg =>
      obtain ⟨b, g⟩ := bg
      have hv' : (tel.lift (n+1)).piView = some (b.lift (n+1), g.lift (n+1)) := by
        rw [WShape.piView_lift, hv]; rfl
      have hpi := WShape.piView_pi' ht hv
      have ⟨tb, tg⟩ := WShape.piView_type ht hv
      constructor
      · intro H
        obtain ⟨D, B, D', B', r, r', hDD, hTy, Hq⟩ := H.of_piView hv'
        refine .inr ⟨D, B, D', B', b, g, hv, r, r', hDD, (hT tb).1 hTy,
          fun a a' p hp ha hr => ?_⟩
        have hp' := (WShape.HasType.lift (Nat.le_succ n)).2 hp
        have := Hq a a' _ hp' ha ((hD hp).2 hr)
        rw [← WShapeFun.lift_app (Nat.le_succ n)] at this
        exact (TeleRel.lift (tg p)).1 this
      · intro H
        obtain ⟨D, B, D', B', r, r', hDD, hTy, Hq⟩ := H.of_piView hv
        have tb' : (b.lift (n+1)).HasType .type := by
          have := (WShape.HasType.lift (Nat.le_succ n)).2 tb; rwa [WShape.lift_sort] at this
        refine .inr ⟨D, B, D', B', _, _, hv', r, r', hDD, (hT tb).2 hTy,
          fun a a' p' hp' ha hr => ?_⟩
        obtain ⟨q, hq, hmem⟩ := WShapeFun.app_eq (g.lift (n+1)) p'
        obtain ⟨q₀, y₀, hmem₀, rfl, hy⟩ := (WShapeFun.mem_lift (Nat.le_succ n)).1 hmem
        obtain ⟨qx, qy, hmemx, hqx, hyq, hqxb⟩ := WShape.HasDom.def.1 hpi.1 _ _ hmem₀
        have hqxb' := (WShape.HasType.lift (Nat.le_succ n)).2 hqxb
        have hr1 := IH'.mono_l (((WShape.lift_le_lift (Nat.le_succ n)).2 hqx).trans hq) hqxb' hp' hr
        have hr2 := (hD hqxb).1 hr1
        have T1 := (TeleRel.lift (tg qx)).2 (Hq a a' qx hqxb ha hr2)
        have hy0 : y₀.HasType .type := (hpi.2 _ _ hmem₀).toType
        have hle : y₀ ≤ g.app qx := hyq.trans (g.app_of_mem hmemx).2
        rw [hy]
        have t1 : (y₀.lift (n+1)).HasType .type := by
          have := (WShape.HasType.lift (Nat.le_succ n)).2 hy0; rwa [WShape.lift_sort] at this
        have t2 : ((g.app qx).lift (n+1)).HasType .type := by
          have := (WShape.HasType.lift (Nat.le_succ n)).2 (tg qx); rwa [WShape.lift_sort] at this
        exact T1.mono ((WShape.lift_le_lift (Nat.le_succ n)).2 hle) t1 t2

omit hT in
theorem FieldsRel.lift : ∀ {T} {tel : WShape n} {ms ns fs},
    FieldsRel IH' T (tel.lift (n+1)) ms ns (fs.map (·.lift (n+1))) ↔ FieldsRel IH T tel ms ns fs
  | _, _, [], [], [] => .rfl
  | T, tel, m :: ms, n' :: ns, x :: xs => by
    simp only [List.map_cons, FieldsRel]
    constructor
    · rintro ⟨D, B, b', g', hv', r, hx, hd, hr, HF⟩
      cases hv : tel.piView with
      | none => rw [WShape.piView_lift, hv] at hv'; cases hv'
      | some bg =>
        obtain ⟨b, g⟩ := bg
        rw [WShape.piView_lift, hv] at hv'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv'
        obtain ⟨rfl, rfl⟩ := hv'
        have hx0 := (WShape.HasType.lift (Nat.le_succ n)).1 hx
        refine ⟨D, B, b, g, rfl, r, hx0, hd, (hD hx0).1 hr, ?_⟩
        rw [← WShapeFun.lift_app (Nat.le_succ n)] at HF
        exact (FieldsRel.lift).1 HF
    · rintro ⟨D, B, b, g, hv, r, hx, hd, hr, HF⟩
      refine ⟨D, B, b.lift (n+1), g.lift (n+1), by rw [WShape.piView_lift, hv]; rfl, r,
        (WShape.HasType.lift (Nat.le_succ n)).2 hx, hd, (hD hx).2 hr, ?_⟩
      rw [← WShapeFun.lift_app (Nat.le_succ n)]
      exact (FieldsRel.lift).2 HF
  | _, _, [], [], _ :: _ | _, _, [], _ :: _, _ | _, _, _ :: _, [], _
  | _, _, _ :: _, _ :: _, [] => by simp [FieldsRel]

theorem IndTele.lift {h : IndHead} {l : List (WShape n)}
    (htel : ∀ i, (ctorTel h l i).HasType .type) :
    IndTele IH' h (l.map (·.lift (n+1))) M N ↔ IndTele IH h l M N := by
  unfold IndTele
  simp only [ctorTel_lift]
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun i =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => TeleRel.lift hT hD (htel i)

theorem CtorVal.lift {h : IndHead} {l : List (WShape n)} {fs : List (WShape n)}
    (htel : ∀ i, (ctorTel h l i).HasType .type) :
    CtorVal IH' h (l.map (·.lift (n+1))) A M N c (fs.map (·.lift (n+1))) ↔
      CtorVal IH h l A M N c fs := by
  unfold CtorVal
  simp only [ctorTel_lift, List.length_map, IndTele.lift hT hD htel]
  exact and_congr .rfl <| and_congr .rfl <| and_congr .rfl <|
    exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| and_congr .rfl <|
    and_congr .rfl <| and_congr .rfl <| FieldsRel.lift hD

theorem StructVal.lift {h : IndHead} {l : List (WShape n)} {fs : List (WShape n)}
    (htel : ∀ i, (ctorTel h l i).HasType .type) :
    StructVal IH' h (l.map (·.lift (n+1))) A M N c (fs.map (·.lift (n+1))) ↔
      StructVal IH h l A M N c fs := by
  unfold StructVal
  simp only [ctorTel_lift, List.length_map, IndTele.lift hT hD htel]
  exact and_congr .rfl <| and_congr .rfl <|
    exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| and_congr .rfl <|
    and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| and_congr .rfl <| FieldsRel.lift hD

end

end LogRel
end Lean4Lean

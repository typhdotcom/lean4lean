import Lean4Lean.Theory.Typing.LogRel.WHRed
import Lean4Lean.Theory.Typing.LogRel.TyEq
import Lean4Lean.Theory.Typing.LogRel.Shape

/-!
# The logical relation

The relation is over a fixed context `Γ` and indexed by shapes of a given depth: `DefEq M N A m a`
says `M ≡ N : A` is valid at value shape `m` and type shape `a`, and `TyDefEq A B a` says the types
`A` and `B` are valid at shape `a`. A depth bounds the information the shapes carry, so the
relation is defined by recursion on it (`LR0`, then the successor), as upstream's
`Experimental/ShapeLogRel.lean`.

Types are related by what they reduce to (`Step`): two sorts at equivalent levels, or two terms
that reduce to neutral normal forms (`NeRed`). A term can be stuck and still have a sort's shape,
since the model reduces a recursor at a propositional instance on any major premise and the
reduction does so only when the context provides the constructor's fields; such terms are
related only to each other. The relation records no equality of its terms, only of the parts of
their reducts, as chains (`TyEq`), which compose without uniqueness of typing.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- `M` reduces to a neutral normal form. -/
def NeRed (M : VExpr) : Prop := ∃ M', StepS env U Γ M M' ∧ WHNF env U Γ M' ∧ Neutral env M'

/-- Types related as universes: both reduce to sorts at equivalent levels, or both are stuck. -/
def SortRel (M N : VExpr) : Prop :=
  (∃ u v, StepS env U Γ M (.sort u) ∧ StepS env U Γ N (.sort v) ∧ u ≈ v) ∨
  (NeRed env U Γ M ∧ NeRed env U Γ N)

end

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem sort_whnf : WHNF env U Γ (.sort u) := fun _ h => nomatch h

theorem Neutral.not_sort : ¬Neutral env (.sort u) := nofun

namespace NeRed
variable (hU : StepUniq env)
include hU

theorem not_sort (H : NeRed env U Γ M) (h : StepS env U Γ M (.sort u)) : False := by
  obtain ⟨M', h1, h2, h3⟩ := H
  cases StepS.determ hU h1 h2 h sort_whnf
  exact Neutral.not_sort h3

theorem whr (h : StepS env U Γ M M₁) : NeRed env U Γ M ↔ NeRed env U Γ M₁ := by
  constructor
  · intro ⟨M', h1, h2, h3⟩; exact ⟨M', StepS.determ_l hU h h1 h2, h2, h3⟩
  · intro ⟨M', h1, h2, h3⟩; exact ⟨M', h.trans h1, h2, h3⟩

end NeRed

namespace SortRel
variable (hU : StepUniq env)

theorem left (H : SortRel env U Γ M N) : SortRel env U Γ M M := by
  rcases H with ⟨u, _, h, -, -⟩ | ⟨h, -⟩
  · exact .inl ⟨u, u, h, h, (rfl : VLevel.Equiv u u)⟩
  · exact .inr ⟨h, h⟩

theorem symm (H : SortRel env U Γ M N) : SortRel env U Γ N M := by
  rcases H with ⟨u, v, h1, h2, h⟩ | ⟨h1, h2⟩
  · exact .inl ⟨v, u, h2, h1, Eq.symm h⟩
  · exact .inr ⟨h2, h1⟩

include hU in
theorem trans (H1 : SortRel env U Γ M₁ M₂) (H2 : SortRel env U Γ M₂ M₃) :
    SortRel env U Γ M₁ M₃ := by
  rcases H1 with ⟨u, v, h1, h2, h⟩ | ⟨h1, h2⟩ <;> rcases H2 with ⟨v', w, h2', h3, h'⟩ | ⟨h2', h3⟩
  · cases StepS.determ hU h2 sort_whnf h2' sort_whnf
    exact .inl ⟨u, w, h1, h3, Eq.trans h h'⟩
  · exact (h2'.not_sort hU h2).elim
  · exact (h2.not_sort hU h2').elim
  · exact .inr ⟨h1, h3⟩

include hU in
theorem whr (hM : StepS env U Γ M M') (hN : StepS env U Γ N N') :
    SortRel env U Γ M N ↔ SortRel env U Γ M' N' := by
  constructor
  · rintro (⟨u, v, h1, h2, h⟩ | ⟨h1, h2⟩)
    · exact .inl ⟨u, v, StepS.determ_l hU hM h1 sort_whnf, StepS.determ_l hU hN h2 sort_whnf, h⟩
    · exact .inr ⟨(NeRed.whr hU hM).1 h1, (NeRed.whr hU hN).1 h2⟩
  · rintro (⟨u, v, h1, h2, h⟩ | ⟨h1, h2⟩)
    · exact .inl ⟨u, v, hM.trans h1, hN.trans h2, h⟩
    · exact .inr ⟨(NeRed.whr hU hM).2 h1, (NeRed.whr hU hN).2 h2⟩

end SortRel

/-! ### The interface each depth satisfies -/

variable [ShapeEnv]

structure LogRelBase (env : VEnv) (U : Nat) (Γ : List VExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at value shape `m` and type shape `a`. -/
  DefEq (M N A : VExpr) (m a : WShape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at shape `a`. -/
  TyDefEq (A B : VExpr) (a : WShape n) : Prop

structure LogRel (env : VEnv) (U : Nat) (Γ : List VExpr) (n : Nat)
    extends LogRelBase env U Γ n where
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔ SortRel env U Γ M N
  sort_iff_ty : TyDefEq M N (.sort r) ↔ SortRel env U Γ M N
  bot : a.HasType .type → DefEq M N A .bot a
  toType : DefEq M N A m (.sort r) → TyDefEq M N m
  left : DefEq M N A m a → DefEq M M A m a
  left_ty : TyDefEq M N m → TyDefEq M M m
  symm : DefEq M N A m a → DefEq N M A m a
  symm_ty : TyDefEq M N m → TyDefEq N M m
  trans : DefEq M₁ M₂ A m a → DefEq M₂ M₃ A m a → DefEq M₁ M₃ A m a
  trans' : DefEq A₁ A₂ (.sort u) a (.sort r') → DefEq A₂ A₃ (.sort v) a (.sort r) →
    DefEq A₁ A₃ (.sort u) a (.sort r')
  trans_ty : TyDefEq M₁ M₂ m → TyDefEq M₂ M₃ m → TyDefEq M₁ M₃ m
  conv : TyDefEq A B a → DefEq M N A m a → DefEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → DefEq M N A m a' → DefEq M N A m a
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → TyDefEq A B a' → TyDefEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyDefEq A A a' →
    DefEq M N A m a → DefEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → DefEq M N A m' a → DefEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    TyDefEq A B m₁ → TyDefEq A B m₂ → TyDefEq A B (m₁.join m₂)
  join : m₁.Compat m₂ → m₁.HasType a → m₂.HasType a →
    DefEq M N A m₁ a → DefEq M N A m₂ a → DefEq M N A (m₁.join m₂) a
  whr : StepS env U Γ M M' → StepS env U Γ N N' → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : StepS env U Γ A A' → StepS env U Γ B B' → (TyDefEq A B m ↔ TyDefEq A' B' m)


/-! ### Depth 0 -/

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

def LR0.TyDefEq (M N : VExpr) : WShape 0 → Prop
  | ⟨.bot, _⟩ => True
  | ⟨.sort _, _⟩ => SortRel env U Γ M N

def LR0.DefEq (M N : VExpr) (m a : WShape 0) : Prop :=
  match a.1 with
  | .bot => True
  | .sort _ => LR0.TyDefEq env U Γ M N m

end

theorem LR0.TyDefEq.join (_hU : StepUniq env) {m₁ m₂ : WShape 0} (hC : m₁.Compat m₂) :
    LR0.TyDefEq env U Γ A B m₁ → LR0.TyDefEq env U Γ A B m₂ →
    LR0.TyDefEq env U Γ A B (m₁.join m₂) := by
  obtain ⟨⟨⟩, _⟩ := m₁ <;> obtain ⟨⟨⟩, _⟩ := m₂ <;>
    simp [LR0.TyDefEq, WShape.join, Shape.join, dif_pos hC]
  simp [WShape.Compat, Shape.Compat] at hC; subst hC; simp

def LR0 (hU : StepUniq env) : LogRel env U Γ 0 where
  DefEq M N _ := LR0.DefEq env U Γ M N
  TyDefEq := LR0.TyDefEq env U Γ
  sort_iff := by simp [LR0.DefEq, LR0.TyDefEq, WShape.sort]
  sort_iff_ty := by simp [LR0.TyDefEq, WShape.sort]
  bot {_ _ _ _} _ := by simp only [LR0.DefEq, LR0.TyDefEq, WShape.bot]; split <;> trivial
  toType := id
  left {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    exact SortRel.left
  left_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    exact SortRel.left
  symm {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    exact SortRel.symm
  symm_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    exact SortRel.symm
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR0.DefEq]; split <;> [(intros; trivial); skip]
    dsimp [LR0.TyDefEq]; split <;> [(intros; trivial); skip]
    exact SortRel.trans hU
  trans' {A₁ A₂ u a r' A₃ v r} := by
    dsimp [LR0.DefEq]; split <;> [(intros; trivial); skip]
    dsimp [LR0.TyDefEq]; split <;> [(intros; trivial); skip]
    exact SortRel.trans hU
  trans_ty {M₁ M₂ m M₃} := by
    dsimp [LR0.TyDefEq]; split <;> [(intros; trivial); skip]
    exact SortRel.trans hU
  conv _ := id
  mono_r_2 {a a' _ _ _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.DefEq]; cases le
  mono_r_2_ty {a a' _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.TyDefEq]; cases le
  mono_r_1 {a a' _ _ _ b} le h1 _ h2 := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;>
      (try exact id) <;> [cases h1.bot_r; cases le]; exact id
  mono_l {m m' M N A a} le _ _ := by
    simp only [LR0.DefEq]; split <;> [trivial; skip]
    obtain ⟨⟨⟩, _⟩ := m <;> obtain ⟨⟨⟩, _⟩ := m' <;>
      (try exact id) <;> [exact fun _ => trivial; cases le]
  join_ty {A B m₁ m₂} hC _ _ := LR0.TyDefEq.join hU hC
  join {M N A m₁ m₂ a} hC _ _ := by
    dsimp only [LR0.DefEq]; split
    · intros; trivial
    · exact LR0.TyDefEq.join hU hC
  whr {M M' N N' A m a} hM hN := by
    dsimp [LR0.DefEq]; split <;> [exact .rfl; skip]
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    exact SortRel.whr hU hM hN
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    exact SortRel.whr hU hA hB

end LogRel
end Lean4Lean

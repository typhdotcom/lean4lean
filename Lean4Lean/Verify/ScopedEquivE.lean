import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.ScopedEquivManager

/-!
# Scoped equivalences as definitional equalities in a chain of contexts

A scoped union-find of the type checker records each equivalence at a level: the scope it was
learned in. Reading the level `l` as "holds in the context `Γ l` of that scope", for contexts that
extend each other as the levels grow, gives a relation `isEquiv` can answer queries by
(`ScopedEquivManager.ERel`). A ceiling `c` sets aside the levels above it: they assert nothing,
which is how a computation is re-run in a context that keeps only the scopes up to `c`.
-/

namespace Lean4Lean.ScopedEquivManager
open Lean hiding Environment Exception
open Kernel

variable {env : VEnv} {Us : List Name}

/-- Contexts by level, each extending those of the levels below it, up to the ceiling `c`. -/
structure Chain (env : VEnv) (Us : List Name) (Γ : Nat → VLCtx) (c : Option Nat) : Prop where
  wf : ∀ l, c.all (l ≤ ·) → (Γ l).WF env Us.length
  lift : ∀ l₁ l₂, l₁ ≤ l₂ → c.all (l₂ ≤ ·) → ∃ n, VLCtx.FVLift' (Γ l₁) (Γ l₂) 0 n 0

/-- An equivalence at level `l` is a definitional equality in `Γ l`, unless `l` is above the
ceiling. -/
def ChainE (env : VEnv) (Us : List Name) (Γ : Nat → VLCtx) (c : Option Nat) :
    Nat → Expr → Expr → Prop :=
  fun l e₁ e₂ => c.all (l ≤ ·) → EquivManager.IsDefEqE env Us (Γ l) e₁ e₂

theorem ChainE.mono (henv : env.WF) (H : Chain env Us Γ c) (h : l₁ ≤ l₂)
    (h1 : ChainE env Us Γ c l₁ e₁ e₂) : ChainE env Us Γ c l₂ e₁ e₂ := fun hc => by
  have hc₁ : c.all (l₁ ≤ ·) := by cases c <;> simp_all; omega
  have ⟨_, W⟩ := H.lift l₁ l₂ h hc
  exact (h1 hc₁).weak' henv W (H.wf l₂ hc)

/-- The equivalences of a chain of contexts are a relation the scoped union-find can answer
queries by. -/
theorem Chain.erel (henv : env.WF) (H : Chain env Us Γ c) : ERel (ChainE env Us Γ c) where
  beq h _ := .relevant (.of_eqv h)
  symm h hc := (h hc).symm
  trans h1 h2 := fun hc => by
    have a1 := ChainE.mono henv H (Nat.le_max_left ..) h1 hc
    have a2 := ChainE.mono henv H (Nat.le_max_right ..) h2 hc
    exact a1.trans a2
  mono h h1 := ChainE.mono henv H h h1
  app h1 h2 := fun hc =>
    .app (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  lam h1 h2 := fun hc =>
    .lam (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  forallE h1 h2 := fun hc =>
    .forallE (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  letE h1 h2 h3 := fun hc =>
    .letE (ChainE.mono henv H (by omega) h1 hc) (ChainE.mono henv H (by omega) h2 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h3 hc)
  mdata h := fun hc => .mdata (h hc)
  proj h := fun hc => .proj (h hc)

/-- Levels below the ceiling keep their meaning when the ceiling is lowered. -/
theorem ChainE.lower {c c' : Option Nat} (hcc : ∀ l, c'.all (l ≤ ·) → c.all (l ≤ ·))
    (h : ChainE env Us Γ c l e₁ e₂) : ChainE env Us Γ c' l e₁ e₂ := fun hc => h (hcc l hc)

end Lean4Lean.ScopedEquivManager

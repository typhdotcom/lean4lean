import Lean4Lean.Verify.TypeChecker.Context

/-!
# The contexts of the open scopes

Every variable the type checker declares opens a scope (`withFreshId`), so the local context is the
context it started with, then one declaration per open scope. The context at level `l` is the one
the `l`th scope was opened in: everything below the declaration of the next scope's variable. A
fact the type checker learned at level `l` (a cached result, or a recorded equivalence) holds there,
and so in every context extending it; that is what lets it outlive the deeper scopes it was learned
under.

A computation is also run again in a context with a ceiling (`Context.ceiling`): the levels above
it are set aside, and the context's own declarations stand for every level from the ceiling up.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- `m₁` is `m₂` with some declarations removed from the top. -/
inductive MLCtx.Below : MLCtx → MLCtx → Prop
  | refl : MLCtx.Below m m
  | vlam : MLCtx.Below m₁ m₂ → MLCtx.Below m₁ (.vlam x n t t' b m₂)
  | vlet : MLCtx.Below m₁ m₂ → MLCtx.Below m₁ (.vlet x n t v t' v' m₂)

theorem MLCtx.Below.trans {m₁ m₂ m₃ : MLCtx} (h₁ : m₁.Below m₂) (h₂ : m₂.Below m₃) :
    m₁.Below m₃ := by
  induction h₂ with
  | refl => exact h₁
  | vlam _ ih => exact .vlam ih
  | vlet _ ih => exact .vlet ih

theorem MLCtx.Below.fvlift {m₁ m₂ : MLCtx} (h : m₁.Below m₂) :
    ∃ ρ, VLCtx.FVLift' m₁.vlctx m₂.vlctx 0 ρ 0 := by
  induction h with
  | refl => exact ⟨_, .refl⟩
  | vlam _ ih | vlet _ ih => let ⟨_, W⟩ := ih; exact ⟨_, .skip_fvar _ _ W⟩

theorem MLCtx.Below.wf {m₁ m₂ : MLCtx} (h : m₁.Below m₂) (wf : m₂.WF env Us) : m₁.WF env Us := by
  induction h with
  | refl => exact wf
  | vlam _ ih | vlet _ ih => exact ih wf.1

theorem MLCtx.Below.fvars {m₁ m₂ : MLCtx} (h : m₁.Below m₂) :
    m₁.vlctx.fvars ⊆ m₂.vlctx.fvars := by
  induction h with
  | refl => exact fun _ => id
  | vlam _ ih | vlet _ ih => exact fun _ hx => List.mem_cons_of_mem _ (ih hx)

/-- A declaration of the smaller context is the larger one's. -/
theorem MLCtx.Below.find? {m₁ : MLCtx} {x : FVarId} (hx : x ∈ m₁.vlctx.fvars) :
    ∀ {m₂ : MLCtx}, m₁.Below m₂ → m₂.WF env Us → m₂.lctx.find? x = m₁.lctx.find? x
  | _, .refl, _ => rfl
  | .vlam y .., .vlam h, wf => by
    have hne : y ≠ x := fun e => by
      subst e; exact (wf.1.tr.find?_eq_none.1 wf.2.1) (h.fvars hx)
    rw [← find? hx h wf.1]
    exact (LocalContext.find?_mkLocalDecl wf.1.tr.1 wf.2.1).trans (by simp [hne])
  | .vlet y .., .vlet h, wf => by
    have hne : y ≠ x := fun e => by
      subst e; exact (wf.1.tr.find?_eq_none.1 wf.2.1) (h.fvars hx)
    rw [← find? hx h wf.1]
    exact (LocalContext.find?_mkLetDecl wf.1.tr.1 wf.2.1).trans (by simp [hne])

theorem _root_.Lean.FVarId.name_ne {x y : FVarId} (h : x ≠ y) : x.name ≠ y.name :=
  fun e => h (by cases x; cases y; simp_all)

/-- The part of `m` below the declaration of `fv`: the context `fv` was declared in. If `m` does
not declare `fv`, it is empty. -/
def MLCtx.under (fv : FVarId) : MLCtx → MLCtx
  | .nil => .nil
  | .vlam x _ _ _ _ c | .vlet x _ _ _ _ _ c => if x.name = fv.name then c else c.under fv

theorem MLCtx.under_below (fv : FVarId) : ∀ m : MLCtx, (m.under fv).Below m
  | .nil => .refl
  | .vlam x .. | .vlet x .. => by
    simp only [MLCtx.under]; split
    · first | exact .vlam .refl | exact .vlet .refl
    · first | exact .vlam (under_below fv _) | exact .vlet (under_below fv _)

/-- Removing declarations from the top keeps what is below a declaration it keeps. -/
theorem MLCtx.Below.under_eq {m₁ : MLCtx} {fv : FVarId} (hfv : fv ∈ m₁.vlctx.fvars) :
    ∀ {m₂ : MLCtx}, m₁.Below m₂ → m₂.WF env Us → m₂.under fv = m₁.under fv
  | _, .refl, _ => rfl
  | .vlam y .., .vlam h, wf | .vlet y .., .vlet h, wf => by
    have hne : y ≠ fv := fun e => by
      subst e; exact (wf.1.tr.find?_eq_none.1 wf.2.1) (h.fvars hfv)
    simp only [MLCtx.under, if_neg (FVarId.name_ne hne)]; exact under_eq hfv h wf.1

/-- The context at level `l`, of a context `m` whose open scopes declare `fvs`. Levels from the
ceiling up are set aside, and stand for `top`: the context a computation is run again in. -/
def levelCtx (m : MLCtx) (fvs : Array FVarId) (ceil : Option Nat) (top : MLCtx) (l : Nat) :
    MLCtx :=
  if ceil.all (l < ·) then
    match fvs[l]? with
    | some fv => m.under fv
    | none => m
  else top

/-- The open scopes' variables are declared in `m` in order, as far as the ceiling lets them be
seen; with a ceiling, they are declared in `top`, which `m` extends. -/
structure ScopeShape (m : MLCtx) (fvs : Array FVarId) (ceil : Option Nat) (top : MLCtx) : Prop where
  mem : ∀ l fv, fvs[l]? = some fv → ceil.all (l < ·) → fv ∈ m.vlctx.fvars
  order : ∀ l fv fv', fvs[l]? = some fv → fvs[l + 1]? = some fv' → ceil.all (l + 1 < ·) →
    fv ∈ (m.under fv').vlctx.fvars
  top : ∀ lab, ceil = some lab → top.Below m ∧ lab ≤ fvs.size ∧
    ∀ fv, fvs[lab - 1]? = some fv → 0 < lab → fv ∈ top.vlctx.fvars

theorem levelCtx_some {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {l : Nat}
    {fv : FVarId} (e : fvs[l]? = some fv) (hc : ceil.all (l < ·)) :
    levelCtx m fvs ceil top l = m.under fv := by
  simp [levelCtx, e, hc]

theorem levelCtx_none {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {l : Nat}
    (e : fvs[l]? = none) (hc : ceil.all (l < ·)) : levelCtx m fvs ceil top l = m := by
  simp [levelCtx, e, hc]

theorem levelCtx_top {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {l : Nat}
    (hc : ¬ceil.all (l < ·)) : levelCtx m fvs ceil top l = top := by
  simp [levelCtx, hc]

theorem ScopeShape.levelCtx_below {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (H : ScopeShape m fvs ceil top) (l : Nat) : (levelCtx m fvs ceil top l).Below m := by
  unfold levelCtx; split
  · split
    · exact MLCtx.under_below _ _
    · exact .refl
  · rename_i hc
    cases ceil with
    | none => simp at hc
    | some lab => exact (H.top lab rfl).1

/-- The context at a level extends those at the levels below. -/
theorem ScopeShape.levelCtx_mono {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (H : ScopeShape m fvs ceil top) (wf : m.WF env Us) {l₁ l₂ : Nat} (h : l₁ ≤ l₂) :
    (levelCtx m fvs ceil top l₁).Below (levelCtx m fvs ceil top l₂) := by
  induction h with
  | refl => exact .refl
  | @step l₂ _ ih =>
    refine ih.trans ?_
    by_cases hc₂ : ceil.all (l₂ + 1 < ·)
    · have hc : ceil.all (l₂ < ·) := by cases ceil <;> simp_all; omega
      cases e₂ : fvs[l₂ + 1]? with
      | none => rw [levelCtx_none e₂ hc₂]; exact H.levelCtx_below l₂
      | some fv' =>
        have hlt : l₂ < fvs.size := by have := (Array.getElem?_eq_some_iff.1 e₂).1; omega
        obtain ⟨fv, e₁⟩ : ∃ fv, fvs[l₂]? = some fv := ⟨_, Array.getElem?_eq_getElem hlt⟩
        rw [levelCtx_some e₁ hc, levelCtx_some e₂ hc₂]
        have hin := H.order l₂ fv fv' e₁ e₂ hc₂
        rw [MLCtx.Below.under_eq hin (MLCtx.under_below fv' m) wf]
        exact MLCtx.under_below _ _
    · rw [levelCtx_top hc₂]
      by_cases hc : ceil.all (l₂ < ·)
      · -- `l₂ + 1` is the ceiling
        obtain ⟨lab, rfl⟩ : ∃ lab, ceil = some lab := by cases ceil <;> simp_all
        have hlab : lab = l₂ + 1 := by simp at hc hc₂; omega
        subst hlab
        obtain ⟨-, hsz, hmem⟩ := H.top _ rfl
        obtain ⟨fv, e₁⟩ : ∃ fv, fvs[l₂]? = some fv :=
          ⟨_, Array.getElem?_eq_getElem (by omega)⟩
        rw [levelCtx_some e₁ hc]
        have hin := hmem fv (by simpa using e₁) (by omega)
        rw [MLCtx.Below.under_eq hin (H.top _ rfl).1 wf]
        exact MLCtx.under_below _ _
      · rw [levelCtx_top hc]; exact .refl

theorem ScopeShape.levelCtx_wf {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (H : ScopeShape m fvs ceil top) (wf : m.WF env Us) (l : Nat) :
    (levelCtx m fvs ceil top l).WF env Us :=
  (H.levelCtx_below l).wf wf

/-- With no scope open and no ceiling there is nothing to declare. -/
theorem ScopeShape.nil {m top : MLCtx} : ScopeShape m #[] none top where
  mem _ _ e := by simp at e
  order _ _ _ e := by simp at e
  top _ e := by cases e

/-- Opening a scope for a variable declared on top keeps the shape. -/
theorem ScopeShape.push {m m' top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (H : ScopeShape m fvs ceil top) (hb : m.Below m') (wf' : m'.WF env Us) {x : FVarId}
    (hx : x ∈ m'.vlctx.fvars) (hux : m'.under x = m) : ScopeShape m' (fvs.push x) ceil top where
  mem l fv e hc := by
    rcases Nat.lt_or_ge l fvs.size with hl | hl
    · rw [Array.getElem?_push_lt hl] at e
      exact hb.fvars (H.mem l fv (by rw [← e, Array.getElem?_eq_getElem hl]) hc)
    · have : l = fvs.size := by
        have := (Array.getElem?_eq_some_iff.1 e).1; simp at this; omega
      subst this; rw [Array.getElem?_push_size] at e; cases e; exact hx
  order l fv fv' e e' hc := by
    have hc' : ceil.all (l < ·) := by cases ceil <;> simp_all; omega
    have hl1 : l + 1 < fvs.size + 1 := by
      have := (Array.getElem?_eq_some_iff.1 e').1; simpa using this
    have hl : l < fvs.size := by omega
    rw [Array.getElem?_push_lt hl] at e
    have e0 : fvs[l]? = some fv := by rw [← e, Array.getElem?_eq_getElem hl]
    rcases Nat.lt_or_ge (l + 1) fvs.size with hl2 | hl2
    · rw [Array.getElem?_push_lt hl2] at e'
      have e1 : fvs[l + 1]? = some fv' := by rw [← e', Array.getElem?_eq_getElem hl2]
      rw [MLCtx.Below.under_eq (H.mem _ fv' e1 hc) hb wf']
      exact H.order l fv fv' e0 e1 hc
    · have hs : fvs.size = l + 1 := by omega
      rw [← hs, Array.getElem?_push_size] at e'; cases e'
      rw [hux]; exact H.mem l fv e0 hc'
  top lab hc := by
    obtain ⟨h1, h2, h3⟩ := H.top lab hc
    refine ⟨h1.trans hb, by simp; omega, fun fv e h0 => h3 fv ?_ h0⟩
    have hl : lab - 1 < fvs.size := by omega
    rw [Array.getElem?_push_lt hl] at e; rw [Array.getElem?_eq_getElem hl, e]

/-- Declaring more variables keeps the contexts of the visible levels of the open scopes. -/
theorem levelCtx_push {m top m' : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {l : Nat}
    (H : ScopeShape m fvs ceil top) (hl : l < fvs.size) (x : FVarId)
    (hm' : m.Below m') (wf' : m'.WF env Us) :
    levelCtx m' (fvs.push x) ceil top l = levelCtx m fvs ceil top l := by
  by_cases hc : ceil.all (l < ·)
  · obtain ⟨fv, e⟩ : ∃ fv, fvs[l]? = some fv := ⟨_, Array.getElem?_eq_getElem hl⟩
    have e' : (fvs.push x)[l]? = some fv := by
      rw [Array.getElem?_push_lt hl, ← e, Array.getElem?_eq_getElem hl]
    rw [levelCtx_some e hc, levelCtx_some e' hc]
    exact MLCtx.Below.under_eq (H.mem l fv e hc) hm' wf'
  · rw [levelCtx_top hc, levelCtx_top hc]

/-- The level of a newly opened scope is the context it was opened in. -/
theorem levelCtx_push_top {m m' top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (hc : ceil.all (fvs.size < ·)) {x : FVarId} (hx : m'.under x = m) :
    levelCtx m' (fvs.push x) ceil top fvs.size = m := by
  rw [levelCtx_some (fv := x) (by simp) hc, hx]

/-- With no ceiling, the level of the innermost scope is the whole context. -/
theorem levelCtx_size {m top : MLCtx} {fvs : Array FVarId} :
    levelCtx m fvs none top fvs.size = m := levelCtx_none (by simp) (by simp)

end Lean4Lean.TypeChecker

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

/-- Levels below the ceiling keep their meaning when the ceiling is lowered. -/
theorem ChainE.lower {c c' : Option Nat} (hcc : ∀ l, c'.all (l ≤ ·) → c.all (l ≤ ·))
    (h : ChainE env Us Γ c l e₁ e₂) : ChainE env Us Γ c' l e₁ e₂ := fun hc => h (hcc l hc)

end Lean4Lean.ScopedEquivManager

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception

/-- The contexts of the levels of a well-formed context form a chain. -/
theorem ScopeShape.chain {c : VContext} {fvs : Array FVarId} {top : MLCtx}
    (H : ScopeShape c.mlctx fvs c.ceiling top) :
    ScopedEquivManager.Chain c.venv c.lparams
      (fun l => (levelCtx c.mlctx fvs c.ceiling top l).vlctx) c.ceiling where
  wf l _ := (H.levelCtx_wf c.mlctx_wf l).tr.wf
  lift _ _ h _ := (H.levelCtx_mono c.mlctx_wf h).fvlift

end Lean4Lean.TypeChecker

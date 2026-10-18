import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Environment.InductInfo
import Lean4Lean.Verify.Typing.ConditionallyTyped
import Lean4Lean.TypeChecker
import Lean4Lean.Verify.ScopedEquivManager

namespace Except

def WF (x : Except ε α) (Q : α → Prop) : Prop := ∀ a, x = .ok a → Q a

theorem WF.bind {x : Except ε α} {f : α → Except ε β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → (f a).WF R) : (x >>= f).WF R := by
  intro b
  simp [(· >>= ·), Except.bind]
  split; · simp
  exact h2 _ (h1 _ rfl) _

theorem WF.pure {Q} (H : Q a) :
    (pure a : Except ε α).WF Q := by rintro _ ⟨⟩; exact H

theorem WF.map {x : Except ε α} {f : α → β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R (f a)) : (f <$> x).WF R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ h => .pure (h2 _ h)

theorem WF.mono {x : Except ε α} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R a) : x.WF R := by
  simpa using h1.bind fun _ h => .pure (h2 _ h)

theorem WF.throw {Q} : (throw e : Except ε α).WF Q := nofun

theorem WF.le {Q R} {x : Except ε α}
    (h1 : x.WF Q) (H : ∀ a, Q a → R a) :
    x.WF R := fun _ e => H _ (h1 _ e)

theorem WF.pureBind  {f : β → Except ε α} {Q}
    {x : β} (H : WF (f x) Q) : ((Pure.pure x : Except ε β) >>= f).WF Q := H

end Except

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace EquivManager

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}
variable (env Us Δ) in
inductive IsDefEqE : Expr → Expr → Prop
  | rfl : IsDefEqE e e
  | trans : IsDefEqE e₁ e₂ → IsDefEqE e₂ e₃ → IsDefEqE e₁ e₃
  | defeq : TrExprS env Us Δ e₁ e' → TrExpr env Us Δ e₂ e' → IsDefEqE e₁ e₂
  | app : IsDefEqE f₁ f₂ → IsDefEqE a₁ a₂ → IsDefEqE (.app f₁ a₁) (.app f₂ a₂)
  | lam : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : IsDefEqE t₁ t₂ → IsDefEqE v₁ v₂ → IsDefEqE b₁ b₂ →
    IsDefEqE (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | mdata : IsDefEqE e₁ e₂ → IsDefEqE (.mdata _ e₁) (.mdata _ e₂)
  | proj : IsDefEqE e₁ e₂ → IsDefEqE (.proj s i e₁) (.proj s i e₂)

theorem IsDefEqE.symm (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ e₂ e₁ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | defeq h1 h2 => let ⟨_, h2, h3⟩ := h2; exact .defeq h2 ⟨_, h1, h3.symm⟩
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem IsDefEqE.weak' (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ' e₁ e₂ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | defeq h1 h2 => exact .defeq (h1.weakFV' henv W hΔ) (h2.weakFV' henv W hΔ)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

end EquivManager

/-- A local declaration without its position in the context, which the type checker never reads. -/
def _root_.Lean.LocalDecl.erase : LocalDecl → LocalDecl
  | .cdecl _ fv n t bi k => .cdecl 0 fv n t bi k
  | .ldecl _ fv n t v nd k => .ldecl 0 fv n t v nd k

theorem _root_.Lean.LocalDecl.erase_type {d d' : LocalDecl} (h : d.erase = d'.erase) :
    d.type = d'.type ∧ d.value' = d'.value' := by
  cases d <;> cases d' <;> simp_all [LocalDecl.erase, LocalDecl.type, LocalDecl.value']

theorem _root_.Lean.LocalContext.find?_mkLocalDecl {lctx : LocalContext} (H : lctx.WF)
    (h : lctx.find? fv = none) :
    (lctx.mkLocalDecl fv name ty bi kind).find? x =
      if fv == x then some (.cdecl lctx.decls.size fv name ty bi kind) else lctx.find? x := by
  rw [(H.mkLocalDecl h).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList,
    H.find?_eq_find?_toList]
  by_cases h' : fv = x
  · subst h'; simp [LocalDecl.fvarId]
  · simp [LocalDecl.fvarId, h', Ne.symm h']

theorem _root_.Lean.LocalContext.find?_mkLetDecl {lctx : LocalContext} (H : lctx.WF)
    (h : lctx.find? fv = none) :
    (lctx.mkLetDecl fv name ty val bi kind).find? x =
      if fv == x then some (.ldecl lctx.decls.size fv name ty val bi kind) else lctx.find? x := by
  rw [(H.mkLetDecl h).find?_eq_find?_toList, LocalContext.mkLetDecl_toList,
    H.find?_eq_find?_toList]
  by_cases h' : fv = x
  · subst h'; simp [LocalDecl.fvarId]
  · simp [LocalDecl.fvarId, h', Ne.symm h']

namespace TypeChecker

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : MLCtx → MLCtx
  | vlet (id : FVarId) (name : Name) (ty v : Expr) (ty' v' : VExpr) : MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ ty ty' _ c => (some (id, ty.fvarsList), .vlam ty') :: c.vlctx
  | .vlet id _ ty v ty' v' c => (some (id, ty.fvarsList ++ v.fvarsList), .vlet ty' v') :: c.vlctx

def MLCtx.lctx : MLCtx → LocalContext
  | .nil => {}
  | .vlam id name ty _ bi c => c.lctx.mkLocalDecl id name ty bi
  | .vlet id name ty val _ _ c => c.lctx.mkLetDecl id name ty val

@[simp] def MLCtx.length : MLCtx → Nat
  | .nil => 0
  | .vlam _ _ _ _ _ c
  | .vlet _ _ _ _ _ _ c => c.length + 1

def MLCtx.decls : MLCtx → List LocalDecl
  | .nil => {}
  | .vlam x name ty _ bi c => .cdecl c.length x name ty bi .default :: c.decls
  | .vlet x name ty v _ _ c => .ldecl c.length x name ty v false default :: c.decls

@[simp] def MLCtx.fvarRevList (c : MLCtx) (n) (hn : n ≤ c.length) : List FVarId :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam id _ _ _ _ c, h
  | n+1, .vlet id _ _ _ _ _ c, h => id :: c.fvarRevList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.fvarRevList_length {c n hn} : (MLCtx.fvarRevList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.letValList (c : MLCtx) (n) (hn : n ≤ c.length) : List (Option (Expr × Expr)) :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam _ _ _ _ _ c, h => none :: c.letValList n (Nat.le_of_succ_le_succ h)
  | n+1, .vlet _ _ ty v _ _ c, h => some (ty, v) :: c.letValList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.letValList_length {c n hn} : (MLCtx.letValList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.dropN (c : MLCtx) (n) (hn : n ≤ c.length) : MLCtx :=
  match n, c, hn with
  | 0, c, _ => c
  | n+1, .vlam _ _ _ _ _ c, h
  | n+1, .vlet _ _ _ _ _ _ c, h => c.dropN n (Nat.le_of_succ_le_succ h)
termination_by structural n

def MLCtx.WF (env : VEnv) (Us : List Name) : MLCtx → Prop
  | .nil => True
  | .vlam fv _ ty ty' _ c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧
    env.IsType Us.length c.vlctx.toCtx ty'
  | .vlet fv _ ty v ty' v' c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧ TrExprS env Us c.vlctx v v' ∧
    env.HasType Us.length c.vlctx.toCtx v' ty'

theorem MLCtx.WF.tr : ∀ {c : MLCtx}, c.WF env Us → TrLCtx env Us c.lctx c.vlctx
  | .nil, _ => ⟨.nil, .nil⟩
  | .vlam .., ⟨h1, h2, h3, h4⟩ => .mkLocalDecl h1.tr h2 h3 h4
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => .mkLetDecl h1.tr h2 h3 h4 h5

theorem MLCtx.WF.dropN {c : MLCtx} (n hn) : c.WF env Us → (c.dropN n hn).WF env Us :=
  match n, c, hn with
  | 0, _, _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h => fun H => H.1.dropN n (Nat.le_of_succ_le_succ h)

theorem MLCtx.dropN_fvars_subset {c : MLCtx} (n hn) : (c.dropN n hn).vlctx.fvars ⊆ c.vlctx.fvars :=
  match n, c, hn with
  | 0, _, _ => fun _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h =>
    List.subset_cons_of_subset _ <| dropN_fvars_subset n (Nat.le_of_succ_le_succ h)

theorem MLCtx.noBV (c : MLCtx) : c.vlctx.NoBV := by
  induction c <;> trivial

structure VContext extends Context where
  venv : VEnv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  trenv : TrEnv safety env venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx
  /-- Ghost: the context a computation run again with a ceiling started from, which the levels
  from the ceiling up stand for. -/
  top : MLCtx := mlctx

@[simp] abbrev VContext.lctx' (c : VContext) := c.mlctx.lctx
@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx' c.vlctx := c.mlctx_wf.tr
theorem VContext.Ewf [VEnv.Injective] (c : VContext) : VEnv.WF c.venv := c.trenv.wf
theorem VContext.Δwf (c : VContext) : c.vlctx.WF c.venv c.lparams.length := c.trlctx.wf

nonrec abbrev VContext.TrExprS (c : VContext) : Expr → VExpr → Prop :=
  TrExprS c.venv c.lparams c.vlctx
nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.TrLCtx (c : VContext) : Prop :=
  TrLCtx c.venv c.lparams c.lctx' c.vlctx
nonrec abbrev VContext.FVarsBelow (c : VContext) : Expr → Expr → Prop :=
  FVarsBelow c.vlctx
nonrec abbrev VContext.TrTyping (c : VContext) : Expr → Expr → VExpr → VExpr → Prop :=
  TrTyping c.venv c.lparams c.vlctx

class VContext.MLCWF (c : VContext) (m : MLCtx) : Prop where
  wf : m.WF c.venv c.lparams

instance (c : VContext) : c.MLCWF c.mlctx := ⟨c.mlctx_wf⟩

end TypeChecker
end Lean4Lean

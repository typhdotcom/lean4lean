import Lean4Lean.Verify.Support.Monad
import Lean4Lean.Verify.TypeChecker.CacheHolds

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace TypeChecker

structure VState extends State where

/-- `e` instantiated through its leading binders by `as`, one at a time, as `inferType'` does when
it checks an application. -/
def _root_.Lean.Expr.instForall : Expr → List Expr → Expr
  | e, [] => e
  | e, a :: as => (e.bindingBody!.instantiate1 a).instForall as

/-- What checking `e` against the type `ty` establishes when `e` is a constant applied to
arguments within its declared type's literal binders: `ty` is that type instantiated by them, and
each argument has `P` at its binder, instantiated by the earlier arguments. -/
def LitApp (C : Environment) (P : Expr → Expr → Prop) (e ty : Expr) : Prop :=
  ∀ ⦃J ls Ds ci⦄, e == mkAppN (.const J ls) Ds → C.find? J = some ci →
    Ds.size ≤ ci.type.leadingForalls →
    ty == (ci.instantiateTypeLevelParams ls).instForall Ds.toList ∧
    ∀ k (hk : k < Ds.size),
      P Ds[k] ((ci.instantiateTypeLevelParams ls).instForall (Ds.toList.take k)).bindingDomain!

theorem LitApp.imp {P Q : Expr → Expr → Prop} (h : ∀ a b, P a b → Q a b)
    (H : LitApp C P e ty) : LitApp C Q e ty :=
  fun _ _ _ _ h1 h2 h3 => let ⟨a, b⟩ := H h1 h2 h3; ⟨a, fun k hk => h _ _ (b k hk)⟩

/-- `x` has type `A` in `Δ` whenever both are in scope: an argument at the binder it is checked
against, which the function's earlier arguments instantiate. -/
def ArgTyped (env : VEnv) (Us : List Name) (Δ : VLCtx) (x A : Expr) : Prop :=
  FVarsIn (· ∈ Δ.fvars) x → FVarsIn (· ∈ Δ.fvars) A →
    ∃ x' A', TrExprS env Us Δ x x' ∧ TrExprS env Us Δ A A' ∧
      env.HasType Us.length Δ.toCtx x' A'

/-- What a type inferred without checking asserts in a context: it is the type of the term, if the
term translates. -/
def InferClaimI (env : VEnv) (Us : List Name) (e : Expr) (r : Cached) (m : MLCtx) : Prop :=
  ∀ e', TrExprS env Us m.vlctx e e' → ∃ e'' ty', TrTyping env Us m.vlctx e r.1 e'' ty'

/-- What a checked type asserts in a context: the term, if it lives there, has that type, and its
arguments, if it is a constant applied within its type's literal binders, are typed at them. -/
def InferClaimC (C : Environment) (env : VEnv) (Us : List Name) (e : Expr) (r : Cached)
    (m : MLCtx) : Prop :=
  FVarsIn (· ∈ m.vlctx.fvars) e →
    (∃ e' ty', TrTyping env Us m.vlctx e r.1 e' ty') ∧ LitApp C (ArgTyped env Us m.vlctx) e r.1

/-- What a weak head normal form asserts in a context: it is one of the term, if the term
translates. -/
def WHNFClaim (env : VEnv) (Us : List Name) (e : Expr) (r : Cached) (m : MLCtx) : Prop :=
  ∀ e', TrExprS env Us m.vlctx e e' → FVarsBelow m.vlctx e r.1 ∧ TrExpr env Us m.vlctx r.1 e'

/-- What a recorded equivalence asserts in a context: the terms, if they translate, are
definitionally equal. -/
def PairClaim (env : VEnv) (Us : List Name) (k : Expr × Expr) (_ : Nat × Nat) (m : MLCtx) : Prop :=
  ∀ t' u', TrExprS env Us m.vlctx k.1 t' → TrExprS env Us m.vlctx k.2 u' →
    EquivManager.IsDefEqE env Us m.vlctx k.1 k.2

def UnfoldCache.WF (c : VContext) (m : ExprMap Expr) : Prop :=
  ∀ ⦃e e' : Expr⦄, m[e]? = some e' → ∃ n ls ci, e = .const n ls ∧
      c.env.find? n = some ci ∧ e' = Inner.instantiateDeltaValue ci ls

/-- What an equivalence the state's union-find records at level `l` asserts: a definitional
equality in the context of that level, unless the level is above the ceiling. -/
abbrev VState.LinkE (c : VContext) (s : VState) : Nat → Expr → Expr → Prop :=
  ScopedEquivManager.ChainE c.venv c.lparams
    (fun l => (levelCtx c.mlctx s.scopeFV c.ceiling c.top l).vlctx) c.ceiling

class VState.WF (c : VContext) (s : VState) where
  trctx : c.TrLCtx
  supp : SuppState c.toContext s.toState
  ectx : s.eqvManager.WFE s.scopeIds (s.LinkE c) (· ≤ s.ngen.idx)
  /-- The open scopes' ids are indices the name generator has handed out. -/
  ids_wf : ∀ i ∈ s.scopeIds, 0 < i ∧ i ≤ s.ngen.idx := by simp
  /-- The recorded pairs hold at their levels. -/
  pairs_wf : LabHolds c s.toState s.eqvPairs id (PairClaim c.venv c.lparams)
  inferTypeI_wf : LabHolds c s.toState s.inferTypeI (·.2) (InferClaimI c.venv c.lparams)
  inferTypeC_wf : LabHolds c s.toState s.inferTypeC (·.2) (InferClaimC c.env c.venv c.lparams)
  whnfCore_wf : LabHolds c s.toState s.whnfCoreCache (·.2) (WHNFClaim c.venv c.lparams)
  whnf_wf : LabHolds c s.toState s.whnfCache (·.2) (WHNFClaim c.venv c.lparams)
  /-- The entries record ids of scopes the name generator has made. -/
  ids_made : LabIds s.toState s.eqvPairs id ∧ LabIds s.toState s.inferTypeI (·.2) ∧
    LabIds s.toState s.inferTypeC (·.2) ∧ LabIds s.toState s.whnfCoreCache (·.2) ∧
    LabIds s.toState s.whnfCache (·.2)
  unfold_wf : UnfoldCache.WF c s.unfold
  /-- The open scopes' variables are declared in the context, in order. -/
  shape : ScopeShape c.mlctx s.scopeFV c.ceiling c.top
  fv_size : s.scopeFV.size = s.scopeIds.size := by rfl
  /-- A ceiling sets aside only scopes below the current one. -/
  ceil_lt : ∀ lab, c.ceiling = some lab → lab < s.scopeIds.size := by intro _ h; cases h

/-- The union-find's equivalences carry over to a context a computation is run again in: one
extending the level-`lab` context, whose own level `lab` extends that one, which sees the levels
below `lab`, and which sets aside the levels above `lab` (or `lab` is the current depth, with no
ceiling on either side). -/
theorem VState.WF.ectx_transfer {c c₂ : VContext} {s : VState} (wf : s.WF c) {lab : Nat}
    (hS₂ : ScopeShape c₂.mlctx s.scopeFV c₂.ceiling c₂.top)
    (hvis : c.ceiling.all (lab ≤ ·)) (hv : c₂.venv = c.venv) (hlp : c₂.lparams = c.lparams)
    (hb : (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab).Below c₂.mlctx)
    (htop : (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab).Below
      (levelCtx c₂.mlctx s.scopeFV c₂.ceiling c₂.top lab))
    (hvis₂ : ∀ l, l < lab → c₂.ceiling.all (l < ·))
    (hc₂ : c₂.ceiling = some lab ∨ c₂.ceiling = none ∧ c.ceiling = none ∧ lab = s.scopeIds.size) :
    s.eqvManager.WFE s.scopeIds (s.LinkE c₂) (· ≤ s.ngen.idx) := by
  have wf₂ : c₂.mlctx.WF c.venv c.lparams := hv ▸ hlp ▸ c₂.mlctx_wf
  refine wf.ectx.mono' (fun _ h => h) (fun l t u h hc => ?_) (fun _ h => h) wf.ectx.bids
  show EquivManager.IsDefEqE c₂.venv c₂.lparams
    (levelCtx c₂.mlctx s.scopeFV c₂.ceiling c₂.top l).vlctx t u
  rw [hv, hlp]
  have hwf₂ := (hS₂.levelCtx_wf wf₂ l).tr.wf
  rcases Nat.lt_or_ge lab l with hl | hl
  · rcases hc₂ with e | ⟨ec₂, e, rfl⟩
    · rw [e] at hc; simp at hc; omega
    · have hsz : s.scopeFV.size ≤ l := by rw [wf.fv_size]; omega
      have a1 : levelCtx c.mlctx s.scopeFV c.ceiling c.top l = c.mlctx := by
        rw [e]; exact levelCtx_none (Array.getElem?_eq_none_iff.2 hsz) (by simp)
      have a2 : levelCtx c₂.mlctx s.scopeFV c₂.ceiling c₂.top l = c₂.mlctx := by
        rw [ec₂]; exact levelCtx_none (Array.getElem?_eq_none_iff.2 hsz) (by simp)
      have a3 : levelCtx c.mlctx s.scopeFV c.ceiling c.top s.scopeIds.size = c.mlctx := by
        rw [e, ← wf.fv_size, levelCtx_size]
      have h' : EquivManager.IsDefEqE c.venv c.lparams
          (levelCtx c.mlctx s.scopeFV c.ceiling c.top l).vlctx t u := h (by simp [e])
      rw [a1] at h'; rw [a2] at hwf₂ ⊢; rw [a3] at hb
      obtain ⟨_, W⟩ := hb.fvlift
      exact h'.weak' c.Ewf W hwf₂
  · have hcl : c.ceiling.all (l ≤ ·) := by cases e : c.ceiling <;> simp_all; omega
    obtain ⟨_, W⟩ :=
      (levelCtx_transfer wf.shape c.mlctx_wf wf₂ hl hvis hb htop hvis₂).fvlift
    exact (h hcl).weak' c.Ewf W hwf₂

/-- The taint and the memo of free variables' levels carry no invariant. -/
theorem VState.WF.setTaint {s : VState} (wf : s.WF c) (t : Nat) (f : ExprMap Nat) :
    VState.WF c ⟨{ s.toState with taint := t, fvLvl := f }⟩ :=
  ⟨wf.trctx, wf.supp.setAux rfl rfl rfl rfl rfl rfl, wf.ectx, wf.ids_wf, wf.pairs_wf,
    wf.inferTypeI_wf, wf.inferTypeC_wf, wf.whnfCore_wf, wf.whnf_wf, wf.ids_made, wf.unfold_wf,
    wf.shape, wf.fv_size, wf.ceil_lt⟩

theorem _root_.Lean4Lean.TypeChecker.State.cached?_some {s : State} {ceil : Option Nat}
    {o : Option Cached} {r : Expr} {l : Nat} (h : s.cached? ceil o = some (r, l)) :
    ∃ id, o = some (r, l, id) := by
  unfold State.cached? at h
  split at h
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- A run of the type checker makes names and leaves the open scopes as they were. -/
def VState.LE (s₁ s₂ : VState) : Prop :=
  s₁.ngen ≤ s₂.ngen ∧ s₂.scopeIds = s₁.scopeIds ∧ s₂.scopeFV = s₁.scopeFV

instance : LE VState := ⟨VState.LE⟩

theorem VState.LE.rfl {s : VState} : s ≤ s := ⟨NameGenerator.LE.rfl, Eq.refl _, Eq.refl _⟩

theorem VState.LE.trans {s₁ s₂ s₃ : VState} (h₁ : s₁ ≤ s₂) (h₂ : s₂ ≤ s₃) : s₁ ≤ s₃ :=
  ⟨NameGenerator.LE.trans h₁.1 h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem VState.LE.ngen {s₁ s₂ : VState} (h : s₁ ≤ s₂) : s₁.ngen ≤ s₂.ngen := h.1

theorem VState.LE.reservesV {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{fv}} :
    s₁.ngen.Reserves fv → s₂.ngen.Reserves fv :=
  (·.mono h.1)

theorem VState.LE.reserves {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{e}} :
    FVarsIn s₁.ngen.Reserves e → FVarsIn s₂.ngen.Reserves e :=
  (·.mono h.reservesV)

def M.WF (c : VContext) (vs : VState) (x : M α) (Q : α → VState → Prop) : Prop :=
  vs.WF c → ∀ a s', x c.toContext vs.toState = .ok (a, s') →
    ∃ vs', vs'.toState = s' ∧ vs ≤ vs' ∧ vs'.WF c ∧ Q a vs'

theorem M.WF.bind {c : VContext} {s : VState} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c s Q)
    (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) :
    (x >>= f).WF c s R := by
  intro wf₁ a vs₁
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨vs₂, eq1, le1, wf₂, h1⟩ := h1 wf₁ _ _ eq
  obtain ⟨vs₃, rfl, le2, wf₃, h2⟩ := h2 _ _ le1 h1 wf₂ _ _ (eq1 ▸ h)
  exact ⟨_, rfl, le1.trans le2, wf₃, h2⟩

theorem M.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) :
    (pure a : M α).WF c s Q := by rintro h _ _ ⟨⟩; exact ⟨_, rfl, .rfl, h, H⟩

theorem M.WF.map {c : VContext} {s : VState} {x : M α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem M.WF.mono {c : VContext} {s : VState} {x : M α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  simpa using h1.bind fun _ _ a1 a2 => .pure (h2 _ _ a1 a2)

theorem M.WF.throw {c : VContext} {s : VState} {Q} : (throw e : M α).WF c s Q := nofun

theorem M.WF.le {c : VContext} {s : VState} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩


def VContext.withMLC (c : VContext) (m : MLCtx) [wf : c.MLCWF m] : VContext :=
  { c with
    mlctx := m
    mlctx_wf := wf.1
    lctx := m.lctx
    lctx_eq := rfl }

@[simp] theorem VContext.withMLC_self (c : VContext) : c.withMLC c.mlctx = c := by
  simp [withMLC, c.lctx_eq]

/-- `withMLC` only moves the local context; the ambient environment and universe parameters are
untouched, so judgements stated at `c` and at `c.withMLC m` are interchangeable. -/
@[simp] theorem VContext.withMLC_venv (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).venv = c.venv := rfl
@[simp] theorem VContext.withMLC_lparams (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).lparams = c.lparams := rfl
@[simp] theorem VContext.withMLC_mlctx (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).mlctx = m := rfl

def VState.next (s : VState) : VState := { s with ngen := s.ngen.next }


def VState.enter (s : VState) : VState := ⟨s.toState.enter⟩
def VState.restore (s₀ s₁ : VState) : VState := ⟨s₀.toState.restore s₁.toState⟩

@[simp] theorem VState.enter_ngen (s : VState) : s.enter.ngen = s.ngen.next := rfl

/-- The levels up to the enclosing scope's, after a scope opened on top is closed. -/
theorem levelCtx_pop {m m' top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {x : FVarId}
    {l : Nat} (hS : ScopeShape m fvs ceil top) (hl : l ≤ fvs.size) (hb : m.Below m')
    (wf' : m'.WF env Us) (hx : m'.under x = m) :
    levelCtx m' (fvs.push x) ceil top l = levelCtx m fvs ceil top l := by
  rcases Nat.lt_or_ge l fvs.size with hl' | hl'
  · exact levelCtx_push hS hl' x hb wf'
  · obtain rfl : l = fvs.size := by omega
    by_cases hvis : ceil.all (fvs.size < ·)
    · rw [levelCtx_push_top hvis hx, levelCtx_none (by simp) hvis]
    · rw [levelCtx_top hvis, levelCtx_top hvis]

/-- Closing a variable's scope: what was learned in it stays, read in the enclosing context. -/
theorem VState.WF.restore {c c' : VContext} {s₀ s₁ : VState} (wf : s₀.WF c) (wf₁ : s₁.WF c')
    (le : s₀.enter ≤ s₁) (H : CtxExt c.toContext c'.toContext ⟨s₀.ngen.curr⟩)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under ⟨s₀.ngen.curr⟩ = c.mlctx)
    (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (ht : c'.top = c.top) (henv : c'.env = c.env)
    (hnew : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → fv = ⟨s₀.ngen.curr⟩) :
    (s₀.restore s₁).WF c := by
  have hr : s₁.ngen.Reserves ⟨s₀.ngen.curr⟩ := NameGenerator.next_reserves_self.mono le.1
  have hfv : s₁.scopeFV = s₀.scopeFV.push ⟨s₀.ngen.curr⟩ := le.2.2
  have hids : s₁.scopeIds = s₀.scopeIds.push (s₀.ngen.idx + 1) := le.2.1
  have hidx : s₀.ngen.idx + 1 ≤ s₁.ngen.idx := le.1.idx_le
  have hmade : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → s₁.ngen.Reserves fv :=
    fun fv a b => hnew fv a b ▸ hr
  have hwf' : c'.mlctx.WF c.venv c.lparams := hv ▸ hl ▸ c'.mlctx_wf
  have ex {cache : InferCache} {P} (h : LabHolds c' s₁.toState cache (·.2) P) :
      LabHolds c (s₀.toState.popScope s₁.toState) cache (·.2) P :=
    h.exit wf.shape hfv ⟨_, hids⟩ wf.fv_size hb hx hv hl hc ht hmade
  have hI := wf₁.inferTypeI_wf; have hC := wf₁.inferTypeC_wf
  have hW₁ := wf₁.whnfCore_wf; have hW₂ := wf₁.whnf_wf; have hP := wf₁.pairs_wf
  rw [hv, hl] at hI hW₁ hW₂ hP; rw [hv, hl, henv] at hC
  exact {
    trctx := wf.trctx
    supp := wf.supp.restore H wf₁.supp hr
    ectx := by
      refine wf₁.ectx.mono_valid (fun n h => ?_) (fun l i e₁ e₂ hval h hc' => ?_) (fun _ h => h)
        (fun l => show _ ≤ s₁.ngen.idx from Nat.le_trans (wf.ectx.bids l) (by omega))
      · unfold ScopedEquivManager.linkOK at h ⊢; rw [hids]; exact valid_push_of_valid h
      · have hle : l ≤ s₀.scopeFV.size := wf.fv_size ▸ le_of_valid hval
        have h1 := h (hc ▸ hc'); dsimp only at h1
        show EquivManager.IsDefEqE c.venv c.lparams
          (levelCtx c.mlctx s₀.scopeFV c.ceiling c.top l).vlctx e₁ e₂
        have e := levelCtx_pop (top := c.top) (ceil := c.ceiling) wf.shape hle hb hwf' hx
        rw [hfv, hc, ht, e, hv, hl] at h1
        exact h1
    ids_wf := fun i h => let ⟨h1, h2⟩ := wf.ids_wf i h; ⟨h1, show _ ≤ s₁.ngen.idx by omega⟩
    pairs_wf := hP.exit wf.shape hfv ⟨_, hids⟩ wf.fv_size hb hx hv hl hc ht hmade
    inferTypeI_wf := ex hI
    inferTypeC_wf := ex hC
    whnfCore_wf := ex hW₁
    whnf_wf := ex hW₂
    ids_made := wf₁.ids_made
    unfold_wf := by
      have := wf₁.unfold_wf; unfold UnfoldCache.WF at this ⊢; rw [henv] at this; exact this
    shape := wf.shape
    fv_size := wf.fv_size
    ceil_lt := wf.ceil_lt }

/-- Entering a variable's scope keeps the union-find's equivalences, each at its level. -/
theorem VState.WF.enter_ectx {c c' : VContext} {s : VState} (wf : s.WF c)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under ⟨s.ngen.curr⟩ = c.mlctx)
    (hxm : ⟨s.ngen.curr⟩ ∈ c'.vlctx.fvars) (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (ht : c'.top = c.top) :
    s.enter.eqvManager.WFE s.enter.scopeIds (s.enter.LinkE c') (· ≤ s.enter.ngen.idx) := by
  refine wf.ectx.mono' (fun k h => ScopedEquivManager.linkOK_push ?_ h)
    (fun l e₁ e₂ h hc' => ?_) (fun _ h => Nat.le_succ_of_le h) (fun l => ?_)
  · show _ ≠ s.ngen.idx + 1
    cases e : s.eqvManager.sid[k]? with
    | none => simp
    | some i =>
      have := wf.ectx.sids k i e
      simp only [Option.getD_some]; omega
  · have hwf' : c'.mlctx.WF c.venv c.lparams := hv ▸ hl ▸ c'.mlctx_wf
    have hB := levelCtx_below_push (l := l) wf.shape hb hwf' hx
    obtain ⟨_, W⟩ := hB.fvlift
    have h1 := h (hc ▸ hc')
    show EquivManager.IsDefEqE c'.venv c'.lparams
      (levelCtx c'.mlctx (s.scopeFV.push ⟨s.ngen.curr⟩) c'.ceiling c'.top l).vlctx e₁ e₂
    rw [hv, hl, hc, ht]
    exact h1.weak' c.Ewf W ((ScopeShape.push wf.shape hb hwf' hxm hx).levelCtx_wf hwf' l).tr.wf
  · show Scopes.labelId (s.scopeIds.push (s.ngen.idx + 1)) l ≤ s.ngen.idx + 1
    have H := ScopedEquivManager.Scopes.labelId_mem (s.scopeIds.push (s.ngen.idx + 1)) l
    generalize Scopes.labelId (s.scopeIds.push (s.ngen.idx + 1)) l = i at H ⊢
    rcases H with rfl | h
    · omega
    · rcases Array.mem_push.1 h with h | rfl
      · have := wf.ids_wf _ h; omega
      · exact Nat.le_refl _

theorem VState.WF.enter_ids {s : VState} (wf : s.WF c) :
    ∀ i ∈ s.enter.scopeIds, 0 < i ∧ i ≤ s.enter.ngen.idx := by
  intro i h
  simp only [VState.enter, State.enter, State.pushScope, Array.mem_push] at h
  show 0 < i ∧ i ≤ s.ngen.idx + 1
  rcases h with h | rfl
  · have := wf.ids_wf i h; omega
  · simp only [NameGenerator.next_idx]; omega

/-- Opening the scope of a fresh variable declared on top keeps the state well formed. -/
theorem VState.WF.enter {c c' : VContext} {s : VState} (wf : s.WF c)
    (hfresh : c.lctx.find? ⟨s.ngen.curr⟩ = none)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under ⟨s.ngen.curr⟩ = c.mlctx)
    (hxm : ⟨s.ngen.curr⟩ ∈ c'.vlctx.fvars)
    (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (ht : c'.top = c.top) (henv : c'.env = c.env)
    (hnew : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → fv = ⟨s.ngen.curr⟩)
    (hsupp : SuppState c'.toContext s.enter.toState) : s.enter.WF c' := by
  have hwf' : c'.mlctx.WF c.venv c.lparams := hv ▸ hl ▸ c'.mlctx_wf
  have en {κ ν : Type} [BEq κ] [Hashable κ] {cache : Std.HashMap κ ν} {lab} {P}
      (h : LabHolds c s.toState cache lab P) (hI : LabIds s.toState cache lab) :
      LabHolds c' s.toState.enter cache lab P :=
    h.enter hI wf.shape hb hx hv hl hc ht hnew hfresh
  have hI := en wf.inferTypeI_wf wf.ids_made.2.1
  have hC := en wf.inferTypeC_wf wf.ids_made.2.2.1
  have hW₁ := en wf.whnfCore_wf wf.ids_made.2.2.2.1
  have hW₂ := en wf.whnf_wf wf.ids_made.2.2.2.2
  have hP := en wf.pairs_wf wf.ids_made.1
  rw [← hv, ← hl] at hI hW₁ hW₂ hP; rw [← hv, ← hl, ← henv] at hC
  have hS := ScopeShape.push wf.shape hb hwf' hxm hx
  rw [← hc, ← ht] at hS
  exact {
    trctx := c'.trlctx
    supp := hsupp
    ectx := wf.enter_ectx hb hx hxm hv hl hc ht
    ids_wf := wf.enter_ids
    pairs_wf := hP
    inferTypeI_wf := hI
    inferTypeC_wf := hC
    whnfCore_wf := hW₁
    whnf_wf := hW₂
    ids_made := ⟨wf.ids_made.1.enter, wf.ids_made.2.1.enter, wf.ids_made.2.2.1.enter,
      wf.ids_made.2.2.2.1.enter, wf.ids_made.2.2.2.2.enter⟩
    unfold_wf := by
      have := wf.unfold_wf; unfold UnfoldCache.WF at this ⊢; rw [henv]; exact this
    shape := hS
    fv_size := by simp [VState.enter, State.enter, State.pushScope, wf.fv_size]
    ceil_lt := fun lab h => by
      have := wf.ceil_lt lab (hc ▸ h); simp [VState.enter, State.enter, State.pushScope]; omega }

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn with
  | 0, _, _ => e
  | n+1, .vlam x name ty _ bi c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

@[simp] def MLCtx.mkForall' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) (.forallE ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

@[simp] def MLCtx.mkLambda (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) (.lam name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

@[simp] def MLCtx.mkLambda' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) (.lam ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

-- HACK: MLCtx.mkLet equation generation fails if this is inlined
def MLCtx.mkLetArg (x : FVarId) (name : Name)
    (ty val : Expr) (nd : Option Bool) (e : Expr) : Expr :=
  let e' := Expr.abstract1 x e
  if e'.hasLooseBVar' 0 then
    .letE name ty val e' (nd.getD false)
  else if let some nd := nd then
    .letE name ty val e' nd
  else
    e'.lowerLooseBVars' 1 1

@[simp] def MLCtx.mkLet (c : MLCtx) (n) (hn : n ≤ c.length)
    (nds : List (Option Bool)) (eq : nds.length = n) (e : Expr) (asForall := false) : Expr :=
  match n, c, hn, nds, eq, e with
  | 0, _, _, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, _ :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <|
      if asForall then .forallE name ty (.abstract1 x e) bi else .lam name ty (.abstract1 x e) bi
  | n+1, .vlet x name ty val _ _ c, h, nd :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <| mkLetArg x name ty val nd e
termination_by structural n

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkForall_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  induction n generalizing c e e' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, h4⟩ := wf
      refine ih h1 ?_ (.forallE h4 H2) _
      exact .forallE h4 H2 h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem mkForall_hasType {c : MLCtx}
    (hus : us.Forall₂ (VLevel.ofLevel Us · = some ·) us')
    (hΔ : c.vlctx.SortList env Us.length us')
    (hu : VLevel.ofLevel Us u = some u')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' (.sort u')) (n hn)
    (hus : us.length = n) :
    ∃ u₀', VLevel.ofLevel Us (List.foldl (fun x y => mkLevelIMax' y x) u us) = some u₀' ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') (.sort u₀') := by
  subst hus
  induction hus generalizing c e' u u' with
  | nil => exact ⟨_, hu, H2⟩
  | cons h _ ih =>
    match c, hΔ with
    | .vlam x name ty ty' bi c, .cons hΔ hu₁ =>
      have ⟨_, h5, h6⟩ := ofLevel_mkLevelIMax' h hu
      refine ih hΔ h5 ?_ (Nat.le_of_succ_le_succ hn)
      refine .defeq (.sortDF ?_ (.of_ofLevel h5) h6.symm) (hu₁.forallE H2)
      exact ⟨.of_ofLevel h, .of_ofLevel hu⟩

theorem MLCtx.WF.mkForall'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ (.sort u)) (n hn) :
    ∃ u, env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkForall' n hn e₁) (c.mkForall' n hn e₂) (.sort u) := by
  induction n generalizing c e₁ e₂ u with
  | zero => exact ⟨_, H⟩
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.forallEDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkForall_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  let ⟨_, H1, eq⟩ := H1
  let ⟨_, H2⟩ := H2
  have eq := eq.of_r henv wf.tr.wf H2
  have ⟨_, H⟩ := wf.mkForall'_congr eq n hn
  have := wf.mkForall_trS henv H1 ⟨_, eq.hasType.1⟩ n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLambda_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf
      refine ih h1 ?_ (.lam h4 H2) _
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.WF.mkLambda'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ ty) (n hn) :
    env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e₁) (c.mkLambda' n hn e₂) (c.mkForall' n hn ty) := by
  induction n generalizing c e₁ e₂ ty with
  | zero => exact H
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.lamDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkLambda_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  let ⟨_, H1, eq⟩ := H1
  have eq := eq.of_r henv wf.tr.wf H2
  have H := wf.mkLambda'_congr eq n hn
  have := wf.mkLambda_trS henv H1 eq.hasType.1 n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLet_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn nds hnds) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLet n hn nds hnds e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' nds with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ (.lam h4 H2) ..
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ H2 ..; dsimp [mkLetArg]; split <;> [skip; split]
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h _ _; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.fvarRevList_prefix (c : MLCtx)
    {n hn} : c.fvarRevList n hn <+: c.vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp [ih]

/-- The sharper form of `fvarRevList_prefix`: the variables a telescope opened and the ones it
started from, in order. This is what says a term mentioning none of the former lives in the
context the telescope was entered at. -/
theorem MLCtx.fvars_eq_append (c : MLCtx) {n hn} :
    c.vlctx.fvars = c.fvarRevList n hn ++ (c.dropN n hn).vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp; exact ih _

/-- "Lives in the context the telescope was entered at" is an up-set for the telescope: the
variables it opened are fresh, so the predicate is false on them and their dependency condition
is vacuous. This is what lets `FVarsBelow` -- which `inferType`/`whnf` hand out -- be read as
"still in the base context". -/
theorem MLCtx.WF.isFVarUpSet_dropN : ∀ {c : MLCtx} (_ : c.WF env Us) (n hn),
    IsFVarUpSet (· ∈ (c.dropN n hn).vlctx.fvars) c.vlctx
  | _, wf, 0, _ => .fvars wf.tr.wf.fvwf
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩, _+1, _
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩, _+1, _ =>
    ⟨h1.isFVarUpSet_dropN _ _, fun h =>
      (h1.tr.find?_eq_none.1 h2 (dropN_fvars_subset (c := c) _ _ h)).elim⟩

theorem MLCtx.WF.fvars_nodup : ∀ {c : MLCtx}, c.WF env Us → c.vlctx.fvars.Nodup
  | .nil, _ => .nil
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩ => by simp [h1.fvars_nodup, h1.tr.find?_eq_none.1 h2]

theorem MLCtx.WF.fvarRevList_nodup {c : MLCtx} (wf : c.WF env Us)
    (n hn) : (c.fvarRevList n hn).Nodup :=
  c.fvarRevList_prefix.sublist.nodup wf.fvars_nodup

theorem MLCtx.WF.decls_size {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.decls.size = c.length := by
  rw [← wf.tr.1.decls_wf.toList'_length]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, ih wf.1]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, ih wf.1]

theorem MLCtx.WF.toList_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.toList = c.decls := by
  simp [LocalContext.toList]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, decls, ih wf.1, wf.1.decls_size]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, decls, ih wf.1, wf.1.decls_size]

theorem MLCtx.WF.find?_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.find? x = c.decls.find? (x == ·.fvarId) := by
  simp [wf.tr.1.find?_eq_find?_toList, wf.toList_eq]

theorem MLCtx.WF.decls_closed : ∀ {c : MLCtx}, c.WF env Us → ∀ d ∈ c.decls, d.Closed
  | .nil, _, _, h => by cases h
  | .vlam .., ⟨wf, _, h, _⟩, d, hd => by
    simp only [decls, List.mem_cons] at hd
    obtain rfl | hd := hd
    · exact (MLCtx.noBV _ ▸ h.closed).looseBVarRange_zero
    · exact wf.decls_closed d hd
  | .vlet .., ⟨wf, _, h1, h2, _⟩, d, hd => by
    simp only [decls, List.mem_cons] at hd
    obtain rfl | hd := hd
    · exact ⟨(MLCtx.noBV _ ▸ h1.closed).looseBVarRange_zero,
        (MLCtx.noBV _ ▸ h2.closed).looseBVarRange_zero⟩
    · exact wf.decls_closed d hd

theorem MLCtx.WF.find?_closed {c : MLCtx} (wf : c.WF env Us) (h : c.lctx.find? x = some d) :
    d.Closed := by
  rw [wf.find?_eq] at h; exact wf.decls_closed d (List.mem_of_find?_eq_some h)

inductive MLCtx.PartialForall : MLCtx → Nat → List FVarId → Expr → Prop where
  | nil : PartialForall c 0 [] e
  | vlam : PartialForall c n fvs (.forallE x ty (.abstract1 fv e) bi) →
    PartialForall (c.vlam fv x ty ty' bi) (n+1) (fv :: fvs) e
  | vlet : PartialForall c n fvs (
      let e' := Expr.abstract1 fv e
      if e'.hasLooseBVar' 0 then .letE x ty v e' false
      else e'.lowerLooseBVars' 1 1) →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) (fv :: fvs) e
  | skip : e.looseBVarRange' = 0 → e' = Expr.abstract1 fv e → e'.hasLooseBVar' 0 = false →
    PartialForall c n fvs e →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) fvs e

theorem MLCtx.PartialForall.full : MLCtx.PartialForall c n (c.fvarRevList n hn) e := by
  induction n generalizing c e with
  | zero => exact .nil
  | succ n ih => match c with | .vlam .. | .vlet .. => constructor; apply ih

theorem MLCtx.PartialForall.sublist (H : MLCtx.PartialForall c n l e) : l <+ c.vlctx.fvars := by
  induction H with
  | nil => simp
  | vlam _ ih | vlet _ ih => simp [ih]
  | skip _ _ _ _ ih => exact ih.trans (List.sublist_cons_self ..)

theorem MLCtx.WF.mkForall_partial {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = l.map .fvar) (hp : MLCtx.PartialForall c n l e)
    (he : e.looseBVarRange' = 0) :
    c.lctx.mkForall arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall, this, ← List.map_reverse, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold he, List.foldr_reverse]
  · clear harr this he
    induction hp with
    | nil => simp
    | vlam hp ih | vlet hp ih =>
      simp
      refine (List.foldl_congr fun _ y h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
      · refine LocalContext.mkBindingList1_congr ?_
        rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
        simp [LocalDecl.fvarId]; rintro ⟨⟩
        have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
      · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
    | skip h1 h2 h3 hp ih =>
      subst h2; simp [h3]
      rw [Expr.lowerLooseBVars_eq_instantiate h3 (v := default),
        Expr.abstract1_eq_liftLooseBVars h3, Expr.liftLooseBVars_eq_self (by simp [h1]),
        Expr.instantiate1_eq_self h1]
      refine (List.foldl_congr fun _ y h => ?_).trans (ih wf.1 _)
      refine LocalContext.mkBindingList1_congr ?_
      rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
      simp [LocalDecl.fvarId]; rintro ⟨⟩
      have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
  · intro _ h
    obtain ⟨d, hd⟩ := wf.tr.find?_eq_some.2 (hp.sublist.subset (List.mem_reverse.1 h))
    exact ⟨d, hd, wf.find?_closed hd⟩
  · exact List.nodup_reverse.2 (hp.sublist.nodup wf.fvars_nodup)

theorem MLCtx.WF.mkForall_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) (he : e.looseBVarRange' = 0) :
    c.lctx.mkForall arr e = c.mkForall n hn e := mkForall_partial wf n hn harr .full he

theorem MLCtx.WF.mkLambda_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) (he : e.looseBVarRange' = 0) :
    c.lctx.mkLambda arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda, this, ← List.map_reverse, LocalContext.mkBinding_eq,
    LocalContext.mkBindingList_eq_fold he, List.foldr_reverse]
  · clear harr this he
    induction n generalizing c e with
    | zero => simp
    | succ n ih =>
      match c with
      | .vlam .. | .vlet .. =>
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
        · refine LocalContext.mkBindingList1_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
  · intro _ h
    obtain ⟨d, hd⟩ := wf.tr.find?_eq_some.2
      ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
    exact ⟨d, hd, wf.find?_closed hd⟩
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)
end TypeChecker
end Lean4Lean

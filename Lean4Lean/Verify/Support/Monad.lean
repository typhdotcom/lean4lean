import Lean4Lean.Verify.Support.Basic

/-!
# What the type checker's state and context allow

A run of the type checker happens in a local context and an environment. `Supp.Closed c S`: what
`S` allows is closed under looking up a free variable's declaration in `c`'s local context and a
constant's declaration in its environment. Its caches only ever hold entries whose outputs are
allowed by every closed `S` that allows their keys (`SuppState`), and `M.SWF` is the
corresponding total-correctness-free statement about a computation, in the style of `M.WF` but
without any typing: a successful run keeps the caches so and satisfies its postcondition.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- The expressions of a declaration mention only its own level parameters, no free variables,
and constants allowed by `C`, as do the names the type checker looks up from it: an inductive
type's constructors, a constructor's type, and a recursor's major premise's type. -/
def _root_.Lean.ConstantInfo.SuppIn (C : Name → Prop) (ci : ConstantInfo) : Prop :=
  let S : Supp := ⟨fun _ => False, (· ∈ ci.levelParams), C⟩
  ci.type.SuppIn S ∧
  match ci with
  | .defnInfo v => v.value.SuppIn S
  | .thmInfo v => v.value.SuppIn S
  | .inductInfo v => ∀ c ∈ v.ctors, C c
  | .ctorInfo v => C v.induct
  | .recInfo v => C v.getMajorInduct ∧ ∀ r ∈ v.rules, r.rhs.SuppIn S
  | _ => True

/-- The operations on `Nat` literals the kernel reduces. -/
def natOps : List Name :=
  [``Nat.succ, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.mod, ``Nat.div,
    ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight]

/-- What `S` allows is closed under the environment: each allowed constant's declaration mentions
only allowed constants, and the results of the `Nat` reductions the kernel does natively are
allowed when the operation is. -/
structure Supp.EnvClosed (S : Supp) (env : Environment) : Prop where
  find : ∀ n ci, env.find? n = some ci → S.const n → ci.SuppIn S.const
  nat : ∀ op ∈ natOps, S.const op → S.const ``Nat ∧ S.const ``Nat.zero ∧ S.const ``Nat.succ
  bool : ∀ op ∈ [``Nat.beq, ``Nat.ble], S.const op → S.const ``Bool.true ∧ S.const ``Bool.false
  /-- What a panic in the kernel returns. -/
  dummy : S.const `_inhabitedExprDummy

/-- The declaration of a free variable `S` allows mentions only what `S` allows. -/
def Supp.CtxClosed (S : Supp) (lctx : LocalContext) : Prop :=
  ∀ fv d, S.fv fv → lctx.find? fv = some d → d.type.SuppIn S ∧ d.value'.SuppIn S

def Supp.Closed (S : Supp) (c : TypeChecker.Context) : Prop :=
  S.CtxClosed c.lctx ∧ S.EnvClosed c.env

/-- The free variables `lctx` declares. -/
def _root_.Lean.LocalContext.Dom (lctx : LocalContext) (fv : FVarId) : Prop :=
  (lctx.find? fv).isSome

/-- A cache entry `e ↦ r`: `e`'s free variables were handed out before, and `r` mentions only what
every closed `S` allowing `e` allows, when `e` lives in the current local context. -/
def CondSupp (c : TypeChecker.Context) (ngen : NameGenerator) (e r : Expr) : Prop :=
  (∀ fv ∈ e.fvarsList, ngen.Reserves fv) ∧
  ∀ S : Supp, S.Closed c → (∀ fv ∈ e.fvarsList, c.lctx.Dom fv) → e.SuppIn S → r.SuppIn S

/-- What the type checker's state holds, for `M.SWF`. -/
structure SuppState (c : TypeChecker.Context) (s : TypeChecker.State) : Prop where
  lctxWF : c.lctx.WF
  wellScoped : ∀ fv d, c.lctx.find? fv = some d →
    (∀ x ∈ d.type.fvarsList, c.lctx.Dom x) ∧ ∀ x ∈ d.value'.fvarsList, c.lctx.Dom x
  envClosed : ∀ n ci, c.env.find? n = some ci → ci.SuppIn fun _ => True
  reserves : ∀ fv, c.lctx.Dom fv → s.ngen.Reserves fv
  inferTypeI : ∀ (e r : Expr), s.inferTypeI[e]? = some r → CondSupp c s.ngen e r
  inferTypeC : ∀ (e r : Expr), s.inferTypeC[e]? = some r → CondSupp c s.ngen e r
  whnfCore : ∀ (e r : Expr), s.whnfCoreCache[e]? = some r → CondSupp c s.ngen e r
  whnf : ∀ (e r : Expr), s.whnfCache[e]? = some r → CondSupp c s.ngen e r
  unfold : ∀ (e r : Expr), s.unfold[e]? = some r → ∀ S : Supp, S.EnvClosed c.env → e.SuppIn S → r.SuppIn S

theorem _root_.Lean.Expr.SuppIn.restrict {S : Supp} {D : FVarId → Prop} {e : Expr}
    (h : e.SuppIn S) (hD : ∀ fv ∈ e.fvarsList, D fv) :
    e.SuppIn ⟨fun x => S.fv x ∧ D x, S.lvl, S.const⟩ := by
  induction e <;> simp_all [Expr.SuppIn, Expr.fvarsList]

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

theorem _root_.Lean.Expr.SuppIn.noFV {F : FVarId → Prop} {L C : Name → Prop} {e : Expr}
    (h : e.SuppIn ⟨fun _ => False, L, C⟩) : e.SuppIn ⟨F, L, C⟩ :=
  Expr.SuppIn.mono (S := ⟨fun _ => False, L, C⟩) (S' := ⟨F, L, C⟩)
    ⟨fun _ h => h.elim, fun _ => id, fun _ => id⟩ h

/-- A local declaration's type, and value if it has one, mention only what `S` allows. -/
def _root_.Lean.LocalDecl.SuppIn (S : Supp) : LocalDecl → Prop
  | .cdecl (type := t) .. => t.SuppIn S
  | .ldecl (type := t) (value := v) .. => t.SuppIn S ∧ v.SuppIn S

theorem _root_.Lean.LocalDecl.SuppIn.mono {S S' : Supp} (H : S ≤ S') :
    ∀ {d : LocalDecl}, d.SuppIn S → d.SuppIn S'
  | .cdecl .., h => Expr.SuppIn.mono H h
  | .ldecl .., ⟨h1, h2⟩ => ⟨Expr.SuppIn.mono H h1, Expr.SuppIn.mono H h2⟩

/-- `S` together with the free variables `xs`. -/
def Supp.addFVars (S : Supp) (xs : List FVarId) : Supp := ⟨fun x => S.fv x ∨ x ∈ xs, S.lvl, S.const⟩

theorem Supp.le_addFVars {S : Supp} {xs : List FVarId} : S ≤ S.addFVars xs :=
  ⟨fun _ h => .inl h, fun _ => id, fun _ => id⟩

theorem mkBindingList_go_supp {S : Supp} (hd : S.const `_inhabitedExprDummy) {isLambda : Bool}
    {lctx : LocalContext} :
    ∀ (ys : List FVarId) {b : Expr},
      (∀ i (hi : i < ys.length) d, lctx.find? ys[i] = some d →
        d.SuppIn (S.addFVars (ys.drop (i + 1)))) →
      b.SuppIn S → (LocalContext.mkBindingList.go isLambda lctx ys b).SuppIn S
  | [], _, _, hb => hb
  | x :: ys, b, H, hb => by
    refine mkBindingList_go_supp hd ys (fun i hi d h => H (i + 1) (by simpa using hi) d h) ?_
    have conv {e : Expr} (h : e.SuppIn (S.addFVars ys)) : (e.abstract' ys.reverse).SuppIn S :=
      Expr.SuppIn.abstract' (Expr.SuppIn.mono (S := S.addFVars ys) (S' := ⟨fun x => S.fv x ∨ x ∈ ys.reverse, S.lvl,
        S.const⟩) ⟨fun z hz => by simpa [Supp.addFVars] using hz, fun _ => id, fun _ => id⟩ h)
    unfold LocalContext.mkBindingList1
    split
    · rename_i h
      have hty := conv (by simpa [LocalDecl.SuppIn] using H 0 (by simp) _ h)
      split <;> exact ⟨hty, hb⟩
    · rename_i h
      have := H 0 (by simp) _ h
      simp only [LocalDecl.SuppIn] at this
      split
      · exact ⟨conv this.1, conv this.2, hb⟩
      · exact hb.lowerLooseBVars
    · exact Expr.SuppIn.default hd

/-- Abstracting local variables, each declared in terms of the ones before it and what `S`
allows, out of a term that mentions only them and what `S` allows. -/
theorem mkBindingList_supp {S : Supp} (hd : S.const `_inhabitedExprDummy) {isLambda : Bool}
    {lctx : LocalContext} {xs : List FVarId} {b : Expr}
    (H : ∀ i (hi : i < xs.length) d, lctx.find? xs[i] = some d →
      d.SuppIn (S.addFVars (xs.take i)))
    (hb : b.SuppIn (S.addFVars xs)) : (lctx.mkBindingList isLambda xs b).SuppIn S := by
  refine mkBindingList_go_supp hd _ (fun i hi d h => ?_) (Expr.SuppIn.abstract' hb)
  simp only [List.length_reverse] at hi
  have e1 : xs.reverse[i] = xs[xs.length - 1 - i] := List.getElem_reverse ..
  rw [e1] at h
  have := H _ (by omega) d h
  have e2 : xs.reverse.drop (i + 1) = (xs.take (xs.length - 1 - i)).reverse := by
    rw [List.reverse_take]; congr 1; omega
  have sub : S.addFVars (xs.take (xs.length - 1 - i)) ≤ S.addFVars (xs.reverse.drop (i + 1)) :=
    ⟨fun z hz => by rw [e2]; simpa [Supp.addFVars] using hz, fun _ => id, fun _ => id⟩
  exact this.mono sub

theorem mkForall_supp {S : Supp} (hd : S.const `_inhabitedExprDummy) {lctx : LocalContext}
    {xs : List FVarId} {b : Expr}
    (H : ∀ i (hi : i < xs.length) d, lctx.find? xs[i] = some d →
      d.SuppIn (S.addFVars (xs.take i)))
    (hb : b.SuppIn (S.addFVars xs)) : (lctx.mkForall ⟨xs.map .fvar⟩ b).SuppIn S := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]; exact mkBindingList_supp hd H hb

theorem mkLambda_supp {S : Supp} (hd : S.const `_inhabitedExprDummy) {lctx : LocalContext}
    {xs : List FVarId} {b : Expr}
    (H : ∀ i (hi : i < xs.length) d, lctx.find? xs[i] = some d →
      d.SuppIn (S.addFVars (xs.take i)))
    (hb : b.SuppIn (S.addFVars xs)) : (lctx.mkLambda ⟨xs.map .fvar⟩ b).SuppIn S := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eq]; exact mkBindingList_supp hd H hb

/-- The context `c` extended by one declaration `d` of a variable `fv` it does not declare: what is
closed in either is closed in the other, restricted to `c`'s variables. -/
structure CtxExt (c c' : TypeChecker.Context) (fv : FVarId) : Prop where
  env : c'.env = c.env
  fresh : c.lctx.find? fv = none
  find : ∀ x, x ≠ fv → c'.lctx.find? x = c.lctx.find? x
  dom : c'.lctx.Dom fv

theorem CtxExt.dom_of {c c' : TypeChecker.Context} (H : CtxExt c c' fv) {x}
    (h : c.lctx.Dom x) : c'.lctx.Dom x := by
  have : x ≠ fv := by rintro rfl; simp [LocalContext.Dom, H.fresh] at h
  simpa [LocalContext.Dom, H.find x this] using h

/-- Restricting what is allowed to `c`'s variables keeps it closed, in `c`, for any `S` closed in
an extension. -/
theorem CtxExt.closed_restrict {c c' : TypeChecker.Context} (H : CtxExt c c' fv)
    (hs : ∀ x d, c.lctx.find? x = some d →
      (∀ y ∈ d.type.fvarsList, c.lctx.Dom y) ∧ ∀ y ∈ d.value'.fvarsList, c.lctx.Dom y)
    {S : Supp} (hS : S.Closed c') : Supp.Closed ⟨fun x => S.fv x ∧ c.lctx.Dom x, S.lvl, S.const⟩ c := by
  refine ⟨fun x d ⟨h1, h2⟩ h3 => ?_, ?_⟩
  · have hx : x ≠ fv := by rintro rfl; simp [LocalContext.Dom, H.fresh] at h2
    have ⟨a, b⟩ := hS.1 x d h1 (by rw [H.find x hx]; exact h3)
    exact ⟨a.restrict (hs x d h3).1, b.restrict (hs x d h3).2⟩
  · rw [← H.env]
    exact ⟨fun n ci h1 h2 => hS.2.find n ci h1 h2, hS.2.nat, hS.2.bool, hS.2.dummy⟩

/-- The same restriction, closed in the extension, for any `S` closed in `c`. -/
theorem CtxExt.closed_restrict' {c c' : TypeChecker.Context} (H : CtxExt c c' fv)
    (hs : ∀ x d, c.lctx.find? x = some d →
      (∀ y ∈ d.type.fvarsList, c.lctx.Dom y) ∧ ∀ y ∈ d.value'.fvarsList, c.lctx.Dom y)
    {S : Supp} (hS : S.Closed c) :
    Supp.Closed ⟨fun x => S.fv x ∧ c.lctx.Dom x, S.lvl, S.const⟩ c' := by
  refine ⟨fun x d ⟨h1, h2⟩ h3 => ?_, ?_⟩
  · have hx : x ≠ fv := by rintro rfl; simp [LocalContext.Dom, H.fresh] at h2
    rw [H.find x hx] at h3
    have ⟨a, b⟩ := hS.1 x d h1 h3
    exact ⟨a.restrict (hs x d h3).1, b.restrict (hs x d h3).2⟩
  · rw [H.env]
    exact ⟨fun n ci h1 h2 => hS.2.find n ci h1 h2, hS.2.nat, hS.2.bool, hS.2.dummy⟩

theorem restrict_le {S : Supp} {D : FVarId → Prop} :
    (⟨fun x => S.fv x ∧ D x, S.lvl, S.const⟩ : Supp) ≤ S :=
  ⟨fun _ h => h.1, fun _ => id, fun _ => id⟩

/-- A cache entry made in `c` holds in an extension, if its key's variables were handed out. -/
theorem CtxExt.condSupp_up {c c' : TypeChecker.Context} (H : CtxExt c c' fv)
    (hs : ∀ x d, c.lctx.find? x = some d →
      (∀ y ∈ d.type.fvarsList, c.lctx.Dom y) ∧ ∀ y ∈ d.value'.fvarsList, c.lctx.Dom y)
    {ngen ngen' : NameGenerator} (hle : ngen ≤ ngen') (hfv : ¬ngen.Reserves fv) {e r : Expr}
    (h : CondSupp c ngen e r) : CondSupp c' ngen' e r := by
  refine ⟨fun x hx => (h.1 x hx).mono hle, fun S hS hd he => ?_⟩
  have hd' : ∀ x ∈ e.fvarsList, c.lctx.Dom x := fun x hx => by
    have hne : x ≠ fv := fun e => hfv (e ▸ h.1 x hx)
    simpa [LocalContext.Dom, H.find x hne] using hd x hx
  exact (h.2 _ (H.closed_restrict hs hS) hd' (he.restrict hd')).mono restrict_le

namespace TypeChecker

/-- A successful run of `x` keeps the state's caches as `SuppState` says, hands out free variables
only forward, and satisfies `Q`. -/
def M.SWF (c : Context) (s : State) (x : M α) (Q : α → State → Prop) : Prop :=
  SuppState c s → ∀ a s', x c s = .ok (a, s') → SuppState c s' ∧ s.ngen ≤ s'.ngen ∧ Q a s'

theorem M.SWF.bind {c : Context} {s : State} {x : M α} {f : α → M β} {Q R}
    (h1 : x.SWF c s Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → (f a).SWF c s' R) :
    (x >>= f).SWF c s R := by
  intro wf₁ b s₂
  simp only [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨wf₂, le₁, h1⟩ := h1 wf₁ _ _ eq
  obtain ⟨wf₃, le₂, h2⟩ := h2 _ _ le₁ h1 wf₂ _ _ h
  exact ⟨wf₃, le₁.trans le₂, h2⟩

theorem M.SWF.pure {c : Context} {s : State} {Q} (H : Q a s) : (pure a : M α).SWF c s Q := by
  rintro h _ _ ⟨⟩; exact ⟨h, .rfl, H⟩

theorem M.SWF.mono {c : Context} {s : State} {x : M α} {Q R}
    (h1 : x.SWF c s Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R a s') : x.SWF c s R :=
  fun wf a s' e => let ⟨h1, h2', h3⟩ := h1 wf a s' e; ⟨h1, h2', h2 _ _ h2' h3⟩

theorem M.SWF.throw {c : Context} {s : State} {Q} : (throw e : M α).SWF c s Q := nofun

theorem M.SWF.liftExcept {c : Context} {s : State} {x : Except Exception α} {Q}
    (h : x.WF Q) : M.SWF c s (liftM x) fun a _ => Q a := by
  rintro wf _ _ eq
  cases x <;> cases eq
  exact ⟨wf, .rfl, h _ rfl⟩

/-- The postcondition `whnf` and `whnfCore` satisfy: whatever a closed `S` allows in the input, it
allows in the output. -/
def SuppBelow (c : Context) (e e₁ : Expr) : Prop :=
  ∀ S : Supp, S.Closed c → e.SuppIn S → e₁.SuppIn S

theorem SuppBelow.rfl {c : Context} {e : Expr} : SuppBelow c e e := fun _ _ => id

theorem SuppBelow.trans {c : Context} {e₁ e₂ e₃ : Expr}
    (h₁ : SuppBelow c e₁ e₂) (h₂ : SuppBelow c e₂ e₃) : SuppBelow c e₁ e₃ :=
  fun S hS h => h₂ S hS (h₁ S hS h)

/-- The type checker's methods, as `M.SWF` sees them: each is called on an input in the current
local context, and whatever a closed `S` allows in it, it allows in the result. -/
structure Methods.SWF (m : Methods) : Prop where
  isDefEqCore : ∀ {c s e₁ e₂}, (∀ fv ∈ e₁.fvarsList, c.lctx.Dom fv) →
    (∀ fv ∈ e₂.fvarsList, c.lctx.Dom fv) → (m.isDefEqCore e₁ e₂).SWF c s fun _ _ => True
  whnfCore : ∀ {c s e cheapProj}, (∀ fv ∈ e.fvarsList, c.lctx.Dom fv) →
    (m.whnfCore e cheapProj).SWF c s fun e₁ _ => SuppBelow c e e₁
  whnf : ∀ {c s e}, (∀ fv ∈ e.fvarsList, c.lctx.Dom fv) →
    (m.whnf e).SWF c s fun e₁ _ => SuppBelow c e e₁
  inferType : ∀ {c s e inferOnly}, (∀ fv ∈ e.fvarsList, c.lctx.Dom fv) →
    (m.inferType e inferOnly).SWF c s fun ty _ => SuppBelow c e ty

def RecM.SWF (c : Context) (s : State) (x : RecM α) (Q : α → State → Prop) : Prop :=
  ∀ m, m.SWF → M.SWF c s (x m) Q

theorem RecM.SWF.bind {c : Context} {s : State} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.SWF c s Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → (f a).SWF c s' R) :
    (x >>= f).SWF c s R :=
  fun _ h => M.SWF.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.SWF.pure {c : Context} {s : State} {Q} (H : Q a s) : (pure a : RecM α).SWF c s Q :=
  fun _ _ => .pure H

theorem RecM.SWF.mono {c : Context} {s : State} {x : RecM α} {Q R}
    (h1 : x.SWF c s Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R a s') : x.SWF c s R :=
  fun _ h => (h1 _ h).mono h2

theorem RecM.SWF.throw {c : Context} {s : State} {Q} : (throw e : RecM α).SWF c s Q :=
  fun _ _ => .throw

theorem M.SWF.lift {c : Context} {s : State} {x : M α} {Q} (h : x.SWF c s Q) :
    RecM.SWF c s x Q := fun _ _ => h

end TypeChecker
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

theorem _root_.Lean4Lean.SuppState.ctxExt {c : Context} {s : State} (wf : SuppState c s) {name ty bi} :
    CtxExt c { c with lctx := c.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } ⟨s.ngen.curr⟩ := by
  have hf : c.lctx.find? ⟨s.ngen.curr⟩ = none := by
    cases h : c.lctx.find? ⟨s.ngen.curr⟩; · rfl
    exact absurd (wf.reserves _ (by simp [LocalContext.Dom, h])) NameGenerator.not_reserves_self
  refine ⟨rfl, hf, fun x hx => ?_, ?_⟩
  · simp only; rw [LocalContext.find?_mkLocalDecl wf.lctxWF hf]; simp [Ne.symm hx]
  · simp [LocalContext.Dom, LocalContext.find?_mkLocalDecl wf.lctxWF hf]

theorem _root_.Lean4Lean.SuppState.ctxExtLet {c : Context} {s : State} (wf : SuppState c s) {name ty val} :
    CtxExt c { c with lctx := c.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val } ⟨s.ngen.curr⟩ := by
  have hf : c.lctx.find? ⟨s.ngen.curr⟩ = none := by
    cases h : c.lctx.find? ⟨s.ngen.curr⟩; · rfl
    exact absurd (wf.reserves _ (by simp [LocalContext.Dom, h])) NameGenerator.not_reserves_self
  refine ⟨rfl, hf, fun x hx => ?_, ?_⟩
  · simp only; rw [LocalContext.find?_mkLetDecl wf.lctxWF hf]; simp [Ne.symm hx]
  · simp [LocalContext.Dom, LocalContext.find?_mkLetDecl wf.lctxWF hf]

/-- Entering a binder: the state is as `SuppState` says in the extended context. -/
theorem _root_.Lean4Lean.SuppState.enter {c c' : Context} {s : State} (wf : SuppState c s) {fv : FVarId}
    (hfv : fv = ⟨s.ngen.curr⟩) (H : CtxExt c c' fv) (hwf : c'.lctx.WF)
    (hd : ∀ d, c'.lctx.find? fv = some d →
      (∀ y ∈ d.type.fvarsList, c.lctx.Dom y) ∧ ∀ y ∈ d.value'.fvarsList, c'.lctx.Dom y) :
    SuppState c' { s with ngen := s.ngen.next } := by
  subst hfv
  have hle : s.ngen ≤ s.ngen.next := .next
  have hnr : ¬s.ngen.Reserves ⟨s.ngen.curr⟩ := NameGenerator.not_reserves_self
  have up {e r} (h : CondSupp c s.ngen e r) : CondSupp c' s.ngen.next e r :=
    H.condSupp_up wf.wellScoped hle hnr h
  refine ⟨hwf, fun x d h => ?_, H.env ▸ wf.envClosed, fun x h => ?_, fun e r h => up (wf.inferTypeI e r h),
    fun e r h => up (wf.inferTypeC e r h), fun e r h => up (wf.whnfCore e r h),
    fun e r h => up (wf.whnf e r h), fun e r h S hS => wf.unfold e r h S (H.env ▸ hS)⟩
  · by_cases hx : x = ⟨s.ngen.curr⟩
    · subst hx; have := hd d h; exact ⟨fun y hy => H.dom_of (this.1 y hy), this.2⟩
    · rw [H.find x hx] at h
      have := wf.wellScoped x d h
      exact ⟨fun y hy => H.dom_of (this.1 y hy), fun y hy => H.dom_of (this.2 y hy)⟩
  · by_cases hx : x = ⟨s.ngen.curr⟩
    · subst hx; exact NameGenerator.next_reserves_self
    · simp only [LocalContext.Dom, H.find x hx] at h
      exact (wf.reserves x h).mono hle

/-- Leaving a binder restores the caches of the state it was entered with. -/
theorem _root_.Lean4Lean.SuppState.restore {c c' : Context} {s s' : State} (wf : SuppState c s)
    {fv : FVarId} (H : CtxExt c c' fv) (wf' : SuppState c' s') (hle : s.ngen ≤ s'.ngen) :
    SuppState c (s.restore s') := by
  have up {e r} (h : CondSupp c s.ngen e r) : CondSupp c s'.ngen e r :=
    ⟨fun x hx => (h.1 x hx).mono hle, h.2⟩
  exact ⟨wf.lctxWF, wf.wellScoped, wf.envClosed, fun x h => (wf.reserves x h).mono hle,
    fun e r h => up (wf.inferTypeI e r h), fun e r h => up (wf.inferTypeC e r h),
    fun e r h => up (wf.whnfCore e r h), fun e r h => up (wf.whnf e r h),
    fun e r h S hS => wf'.unfold e r h S (H.env.symm ▸ hS)⟩

theorem RecM.SWF.withLocalDecl {c : Context} {s : State} {f : Expr → RecM α} {Q name ty bi}
    (hty : ∀ fv ∈ ty.fvarsList, c.lctx.Dom fv)
    (H : RecM.SWF { c with lctx := c.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { s with ngen := s.ngen.next } (f (.fvar ⟨s.ngen.curr⟩)) Q)
    (hQ : ∀ a (s₁ s₂ : State), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    RecM.SWF c s (withLocalDecl name bi ty f) Q := by
  intro m hm wf a s' e
  have hE := wf.ctxExt (name := name) (ty := ty) (bi := bi)
  have hwf' := wf.lctxWF.mkLocalDecl hE.fresh (fv := ⟨s.ngen.curr⟩) (name := name) (ty := ty)
    (bi := bi) (kind := .default)
  have wf₁ := wf.enter rfl hE hwf' fun d hd => by
    simp [LocalContext.find?_mkLocalDecl wf.lctxWF hE.fresh] at hd; subst hd
    exact ⟨hty, by simp [LocalDecl.value', Expr.fvarsList, hE.dom]⟩
  obtain ⟨s₁, e₁, rfl⟩ := withFreshId_run e
  obtain ⟨wf₂, hle, hQ'⟩ := H m hm wf₁ a _ e₁
  exact ⟨wf.restore hE wf₂ (NameGenerator.LE.next.trans hle), NameGenerator.LE.next.trans hle,
    hQ _ s₁ _ rfl hQ'⟩

theorem RecM.SWF.withLetDecl {c : Context} {s : State} {f : Expr → RecM α} {Q name ty val}
    (hty : ∀ fv ∈ ty.fvarsList, c.lctx.Dom fv) (hval : ∀ fv ∈ val.fvarsList, c.lctx.Dom fv)
    (H : RecM.SWF { c with lctx := c.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { s with ngen := s.ngen.next } (f (.fvar ⟨s.ngen.curr⟩)) Q)
    (hQ : ∀ a (s₁ s₂ : State), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    RecM.SWF c s (withLetDecl name ty val f) Q := by
  intro m hm wf a s' e
  have hE := wf.ctxExtLet (name := name) (ty := ty) (val := val)
  have hwf' := wf.lctxWF.mkLetDecl hE.fresh (fv := ⟨s.ngen.curr⟩) (name := name) (ty := ty)
    (val := val) (bi := false) (kind := .default)
  have wf₁ := wf.enter rfl hE hwf' fun d hd => by
    simp [LocalContext.find?_mkLetDecl wf.lctxWF hE.fresh] at hd; subst hd
    exact ⟨hty, fun y hy => hE.dom_of (hval y hy)⟩
  obtain ⟨s₁, e₁, rfl⟩ := withFreshId_run e
  obtain ⟨wf₂, hle, hQ'⟩ := H m hm wf₁ a _ e₁
  exact ⟨wf.restore hE wf₂ (NameGenerator.LE.next.trans hle), NameGenerator.LE.next.trans hle,
    hQ _ s₁ _ rfl hQ'⟩

end TypeChecker
end Lean4Lean

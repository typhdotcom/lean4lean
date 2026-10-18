import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Inductive.Add

/-!
# Verification framework for `AddInductive.M`

`AddInductive.M` reads a context holding the environment and the local context the kernel has
opened, and lifts each type checker call into a fresh run of `TypeChecker.M` over that local
context. A model of the context is a type checker model of the environment, plus a model of the
local context whose free variables the kernel's name generator has already handed out and the
type checker's never will.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

/-! ### The kernel's level tests are exact

`isNeverZero` and `isAlwaysZero` are syntactic, but on levels without metavariables they decide
the semantic properties the spec states: levels are monotone, so a level is never zero iff it is
nonzero when every parameter is `0`, and always zero iff it is zero when every parameter is `1`. -/

theorem eval_zero_of_not_isNeverZero (h : VLevel.ofLevel Us u = some u')
    (H : u.isNeverZero = false) : u'.eval [] = 0 := by
  induction u generalizing u' with
    simp [Level.isNeverZero, VLevel.ofLevel] at H h
  | zero => subst h; rfl
  | param => obtain ⟨-, rfl⟩ := h; simp [VLevel.eval]
  | max _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp [VLevel.eval, ih1 h1 H.1, ih2 h2 H.2]
  | imax _ _ _ ih2 =>
    obtain ⟨_, _, _, h2, rfl⟩ := h
    simp [VLevel.eval, Lean.Nat.imax, ih2 h2 H]

theorem ofLevel_isNeverZero_iff (h : VLevel.ofLevel Us u = some u') :
    u.isNeverZero ↔ u'.IsNeverZero := by
  refine ⟨ofLevel_isNeverZero h, fun H => ?_⟩
  cases e : u.isNeverZero; · exact (H [] (eval_zero_of_not_isNeverZero h e)).elim
  rfl

theorem eval_ones_of_not_isAlwaysZero (h : VLevel.ofLevel Us u = some u')
    (H : u.isAlwaysZero = false) : u'.eval (List.replicate Us.length 1) ≠ 0 := by
  induction u generalizing u' with
    simp [Level.isAlwaysZero, VLevel.ofLevel] at H h
  | succ => obtain ⟨_, -, rfl⟩ := h; simp [VLevel.eval]
  | param => obtain ⟨hi, rfl⟩ := h; simp [VLevel.eval, hi]
  | max a b ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp only [VLevel.eval, Nat.max_def]
    by_cases ea : a.isAlwaysZero = true
    · have := ih2 h2 (H ea); split <;> omega
    · have := ih1 h1 (by simpa using ea); split <;> omega
  | imax _ _ _ ih2 =>
    obtain ⟨_, _, _, h2, rfl⟩ := h
    have := ih2 h2 H
    simp only [VLevel.eval, Lean.Nat.imax, Nat.max_def]; split <;> [omega; split <;> omega]

theorem ofLevel_isAlwaysZero_iff (h : VLevel.ofLevel Us u = some u') :
    u.isAlwaysZero ↔ u' ≈ .zero := by
  refine ⟨ofLevel_isAlwaysZero h, fun H => ?_⟩
  cases e : u.isAlwaysZero; · exact (eval_ones_of_not_isAlwaysZero h e (VLevel.equiv_def.1 H _)).elim
  rfl

/-- The type annotations `consumeTypeAnnotations` strips by name, each with its arity and the
argument it keeps. -/
def typeAnnotations : List (Name × Nat × Nat) :=
  [(``optParam, 2, 0), (``autoParam, 2, 0), (``outParam, 1, 0), (``semiOutParam, 1, 0)]

/-- The type annotations are identities wherever they are well typed. The kernel opens
parameters, indices and fields at their stripped types, so a recursor built from them is only
well typed if this holds. Lean's prelude defines them so; neither kernel checks it. -/
def VEnv.AnnotationsErase (env : VEnv) : Prop :=
  ∀ n k i, (n, k, i) ∈ typeAnnotations →
    ∀ U Γ ls args, OnCtx Γ (env.IsType U) → args.length = k →
      VExpr.WF env U Γ (.appN (.const n ls) args) →
      env.IsDefEqU U Γ (.appN (.const n ls) args) (args.getD i default)

/-- `n` is undeclared, or declared with a rule making it the function returning the `i`th of its
`k` arguments: what a definition `fun x₁ .. xₖ => xᵢ` contributes. -/
def VEnv.DefinesProjection (env : VEnv) (n : Name) (k i : Nat) : Prop :=
  ∀ ci, env.constants n = some ci → ∃ As, As.length = k ∧
    env.defeqs ⟨ci.uvars, .const n (VLevel.params ci.uvars), .lams As (.bvar (k - 1 - i)), ci.type⟩

/-- Each type annotation is undeclared, or defined as Lean's prelude defines it. Unlike
`AnnotationsErase`, this survives extending the environment by constants with other names. -/
def VEnv.AnnotationsDefine (env : VEnv) : Prop :=
  ∀ n k i, (n, k, i) ∈ typeAnnotations → env.DefinesProjection n k i

theorem VEnv.AnnotationsDefine.mono {env env' : VEnv} (h : env.AnnotationsDefine) (hle : env ≤ env')
    (hnew : ∀ n k i, (n, k, i) ∈ typeAnnotations → env.constants n = none →
      env'.constants n = none) : env'.AnnotationsDefine := by
  intro n k i hmem ci hci
  cases hc : env.constants n with
  | none => rw [hnew n k i hmem hc] at hci; cases hci
  | some ci₀ =>
    cases (hle.constants hc).symm.trans hci
    obtain ⟨As, h1, h2⟩ := h n k i hmem _ hc
    exact ⟨As, h1, hle.defeqs h2⟩

theorem VExpr.instL_lams (ls : List VLevel) : ∀ (As : List VExpr) (e : VExpr),
    (VExpr.lams As e).instL ls = .lams (As.map (·.instL ls)) (e.instL ls)
  | [], _ => rfl
  | _ :: As, e => by simp [VExpr.lams, VExpr.instL, instL_lams ls As e]

theorem VEnv.HasType.lams_ctx {env : VEnv} (henv : env.Ordered) :
    ∀ {Γ As e T}, OnCtx Γ (env.IsType U) → env.HasType U Γ (.lams As e) T →
      OnCtx (As.reverse ++ Γ) (env.IsType U)
  | _, [], _, _, hΓ, _ => hΓ
  | Γ, A :: As, _, _, hΓ, h => by
    obtain ⟨hA, _, hb⟩ := h.lam_inv henv hΓ
    simpa using VEnv.HasType.lams_ctx henv (Γ := A :: Γ) ⟨hΓ, hA⟩ hb

/-- Annotations defined as Lean's prelude defines them erase. -/
theorem VEnv.AnnotationsDefine.erase {env : VEnv} (henv : env.WF) (H : env.AnnotationsDefine) :
    env.AnnotationsErase := by
  intro n k i hmem U Γ ls args hΓ hlen hwf
  have ⟨_, hc⟩ := VExpr.WF.appN_inv henv.ordered hΓ hwf
  obtain ⟨ci, hci, hls, hlen'⟩ := VEnv.HasType.const_inv henv.ordered hΓ hc
  obtain ⟨As, hAs, hdf⟩ := H n k i hmem ci hci
  have hrule := VEnv.IsDefEq.extra (Γ := Γ) hdf hls hlen'
  simp only [VExpr.instL, VLevel.inst_map_id hlen', VExpr.instL_lams] at hrule
  have h1 := VEnv.IsDefEqU.appN henv hΓ ⟨_, hrule⟩ hwf
  have hwf2 : VExpr.WF env U Γ ((VExpr.lams (As.map (·.instL ls)) (.bvar (k - 1 - i))).appN args) :=
    let ⟨_, h⟩ := h1; ⟨_, h.hasType.2⟩
  have hdfwf := henv.ordered.defEqWF hdf
  have hctx := (VEnv.HasType.lams_ctx henv.ordered trivial hdfwf.2).instL hls
  obtain ⟨-, h2, -⟩ := VExpr.lams_appN henv hΓ (As := As.map (·.instL ls)) (Γ := [])
    (by simpa [List.map_reverse] using hctx) (σ := .id) .nil (vs := args) (by simp [hlen, hAs])
    (by simpa using hwf2)
  have h3 := h1.trans henv hΓ (by simpa using h2)
  simp only [typeAnnotations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  obtain ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ := hmem <;>
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;>
      first | (simp at hlen; done) | simpa [VExpr.subst, VExpr.Subst.cons] using h3

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Adding constants one by one, each after `checkName`: the names are fresh and distinct, and
primitive only where allowed. -/
theorem addChecked.WF {env : Environment} (mapWF : env.constants.WF) (allow : Bool)
    (f : α → ConstantInfo) :
    ∀ (xs : List α), (xs.foldlM (m := Except Exception) (init := env) fun (env : Environment) x => do
        env.checkName (f x).name allow; return env.add (f x)).WF fun env' =>
      env'.constants = insertConsts env.constants (xs.map f) ∧ env'.quotInit = env.quotInit ∧
      ((xs.map f).map (·.name)).Nodup ∧ (∀ ci ∈ xs.map f, env.constants.find? ci.name = none) ∧
      (∀ ci ∈ xs.map f, Environment.primitives.contains ci.name → allow)
  | [] => .pure ⟨rfl, rfl, .nil, nofun, nofun⟩
  | x :: xs => by
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (checkName.WF mapWF (f x).name allow).bind fun _ ⟨hn, hp⟩ => ?_
    have hn' : env.constants.find? (f x).name = none := by
      rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at hn
    have mapWF' := mapWF.insert (f x).name (f x) hn'
    refine (addChecked.WF (env := env.add (f x)) mapWF' allow f xs).mono
      fun env' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hm => ?_, h3⟩
      obtain ⟨ci, hci, he⟩ := List.mem_map.1 hm
      have := h4 ci hci
      change (env.constants.insert (f x).name (f x)).find? ci.name = none at this
      rw [mapWF.find?_insert, if_pos (by simp [he])] at this; cases this
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨hn', fun ci hci => ?_⟩
      have := h4 ci hci
      change (env.constants.insert (f x).name (f x)).find? ci.name = none at this
      rw [mapWF.find?_insert] at this; split at this; · cases this
      exact this
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]; exact ⟨hp, h5⟩

/-- `consumeTypeAnnotations` without `partial`. -/
def _root_.Lean.Expr.consumeTypeAnnotations' : Expr → Expr
  | .app (.app (.const ``optParam _) A) _ => A.consumeTypeAnnotations'
  | .app (.app (.const ``autoParam _) A) _ => A.consumeTypeAnnotations'
  | .app (.const ``outParam _) A => A.consumeTypeAnnotations'
  | .app (.const ``semiOutParam _) A => A.consumeTypeAnnotations'
  | e => e

/-- We cannot prove this because `consumeTypeAnnotations` is partial. -/
axiom _root_.Lean.Expr.consumeTypeAnnotations_eq (e : Expr) :
    e.consumeTypeAnnotations = e.consumeTypeAnnotations'

variable! (henv : VEnv.WF env) (hann : env.AnnotationsErase)
  {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
/-- Stripping type annotations does not change a translation, up to defeq. -/
theorem TrExprS.consumeTypeAnnotations' {e e'} (H : TrExprS env Us Δ e e') :
    ∃ e'', TrExprS env Us Δ e.consumeTypeAnnotations' e'' ∧
      env.IsDefEqU Us.length Δ.toCtx e' e'' := by
  have hΓ := hΔ.toCtx
  induction e using Lean.Expr.consumeTypeAnnotations'.induct generalizing e' with
  | case1 _ A _ ih | case2 _ A _ ih =>
    cases H with | app h1 h2 hf _ => cases hf with | app _ _ hc hA => cases hc with | const =>
    have := hann _ 2 0 (by simp [typeAnnotations]) _ _ _ [_, _] hΓ rfl ⟨_, h1.app h2⟩
    obtain ⟨A'', h3, h4⟩ := ih hA
    exact ⟨A'', by simpa [Lean.Expr.consumeTypeAnnotations'] using h3,
      this.trans henv hΓ (by simpa using h4)⟩
  | case3 _ A ih | case4 _ A ih =>
    cases H with | app h1 h2 hc hA => cases hc with | const =>
    have := hann _ 1 0 (by simp [typeAnnotations]) _ _ _ [_] hΓ rfl ⟨_, h1.app h2⟩
    obtain ⟨A'', h3, h4⟩ := ih hA
    exact ⟨A'', by simpa [Lean.Expr.consumeTypeAnnotations'] using h3,
      this.trans henv hΓ (by simpa using h4)⟩
  | case5 e h1 h2 h3 h4 =>
    refine ⟨e', ?_, H.wf henv.ordered hΔ⟩
    unfold Lean.Expr.consumeTypeAnnotations'
    split <;> first | exact H | (exfalso; simp_all)

namespace AddInductive

structure VContext extends Context where
  venv : VEnv
  envAt : VEnvAt env safety venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx
  reserved : ∀ fv ∈ mlctx.vlctx.fvars, ngen.Reserves fv
  notKernel : ∀ fv ∈ mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv
  pfx : ngen.namePrefix ≠ `_kernel_fresh

/-- The type checker's view of the context. -/
def VContext.tc (c : VContext) : TypeChecker.VContext where
  env := c.env
  safety := c.safety
  lparams := c.lparams
  fuel := c.fuel
  lctx := c.lctx
  venv := c.venv
  hasPrimitives := c.envAt.hasPrimitives
  safePrimitives := c.envAt.safePrimitives
  trenv := c.envAt.tr
  mlctx := c.mlctx
  mlctx_wf := c.mlctx_wf
  lctx_eq := c.lctx_eq

def WF (c : VContext) (x : M α) (Q : α → Prop) : Prop := ∀ a, x c.toContext = .ok a → Q a

theorem WF.bind {c : VContext} {x : M α} {f : α → M β} {Q R}
    (h1 : WF c x Q) (h2 : ∀ a, Q a → WF c (f a) R) : WF c (x >>= f) R := by
  intro b
  simp only [WF, (· >>= ·), ReaderT.bind, Except.bind] at *
  split; · simp
  exact h2 _ (h1 _ ‹_›) _

theorem WF.pure {c : VContext} {Q} (H : Q a) : WF c (pure a : M α) Q := by
  rintro _ ⟨⟩; exact H

theorem WF.mono {c : VContext} {x : M α} {Q R} (h1 : WF c x Q) (h2 : ∀ a, Q a → R a) :
    WF c x R := fun _ e => h2 _ (h1 _ e)

theorem WF.throw {c : VContext} {Q} : WF c (throw e : M α) Q := nofun

theorem WF.liftExcept {c : VContext} {x : Except Exception α} {Q} (h : x.WF Q) :
    WF c (liftM x : M α) Q := fun _ e => h _ e

theorem VState.WF.emptyM (c : VContext) : TypeChecker.VState.WF c.tc {} where
  trctx := c.mlctx_wf.tr
  ngen_wf := c.notKernel
  ectx := ⟨c.mlctx.vlctx, .refl, c.tc.Δwf, .refl, .empty, c.notKernel⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- A type checker call, run over the kernel's local context. -/
theorem WF.liftTC {c : VContext} {x : TypeChecker.M α} {Q}
    (H : x.WF c.tc {} fun a _ => Q a) : WF c (monadLift x : M α) Q := by
  intro a eq
  change TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x = .ok a at eq
  simp only [TypeChecker.M.run, StateT.run', Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  obtain ⟨_, _, _, _, h⟩ := H (VState.WF.emptyM c) _ _ eq
  exact h

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.mono {env env' : VEnv} (henv : env ≤ env') :
    ∀ {m : MLCtx}, m.WF env Us → m.WF env' Us
  | .nil, h => h
  | .vlam .., ⟨h1, h2, h3, h4⟩ => ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv⟩
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv, h5.mono henv⟩

/-- The context with the environment replaced by one modelled by `venv'` at the same level, into
which the local context carries over. -/
def VContext.withEnv (c : VContext) (env' : Environment) (venv' : VEnv)
    (wf : VEnvAt env' c.safety venv') (hle : c.venv ≤ venv') : VContext :=
  { c with
    env := env'
    venv := venv'
    envAt := wf
    mlctx_wf := c.mlctx_wf.mono hle }

/-- A computation under `withEnv` that does not use the type checker, verified directly. -/
theorem WF.withEnvRaw {c : VContext} {x : M α} {Q} {env'}
    (H : (x { c.toContext with env := env' }).WF Q) : WF c (AddInductive.withEnv env' x) Q := H

theorem WF.withEnv {c : VContext} {x : M α} {Q} {env' venv'} (wf hle)
    (H : WF (c.withEnv env' venv' wf hle) x Q) : WF c (AddInductive.withEnv env' x) Q := H

/-- The context `withLocalDecl` opens: a fresh variable of type `ty`, modelled by `ty'`. -/
def VContext.push (c : VContext) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (hty : TrExprS c.venv c.lparams c.mlctx.vlctx ty ty')
    (hty' : c.venv.IsType c.lparams.length c.mlctx.vlctx.toCtx ty') : VContext :=
  { c with
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    ngen := c.ngen.next
    mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi c.mlctx
    mlctx_wf := ⟨c.mlctx_wf,
      c.mlctx_wf.tr.find?_eq_none.2 fun h => c.ngen.not_reserves_self (c.reserved _ h), hty, hty'⟩
    lctx_eq := by simp [MLCtx.lctx, c.lctx_eq]
    reserved := by
      simp only [MLCtx.vlctx]; simp
      exact ⟨c.ngen.next_reserves_self, fun _ h => (c.reserved _ h).mono .next⟩
    notKernel := by
      simp only [MLCtx.vlctx]; simp
      refine ⟨fun i h => ?_, c.notKernel⟩
      injection h with h; injection h with h; exact absurd h c.pfx }

theorem WF.withLocalDecl {c : VContext} {f : Expr → M α} {Q name ty ty' bi} (hty hty')
    (H : WF (c.push name ty ty' bi hty hty') (f (.fvar ⟨c.ngen.curr⟩)) Q) :
    WF c (Lean4Lean.withLocalDecl name bi ty f) Q := H

end AddInductive
end Lean4Lean

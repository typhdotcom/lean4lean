import Lean4Lean.Verify.Environment.RecInfos

/-!
# What the kernel computes on a few syntactic shapes

The type checker's specification says what its results mean, not what they are. Where the proof
needs the result itself: `whnf` of an axiom is the axiom, as the cache of a fresh run is empty.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

theorem RecM.bind_ok {α β : Type} {x : RecM α} {f : α → RecM β} {m : Methods}
    {ctx : TypeChecker.Context} {s s' : TypeChecker.State} {a : α}
    (h : x m ctx s = .ok (a, s')) : ReaderT.bind x f m ctx s = f a m ctx s' := by
  simp only [ReaderT.bind, bind, StateT.bind, h]; rfl

theorem M.bind_ok {α β : Type} {x : TypeChecker.M α} {f : α → TypeChecker.M β}
    {ctx : TypeChecker.Context} {s s' : TypeChecker.State} {a : α}
    (h : x ctx s = .ok (a, s')) : (x >>= f) ctx s = f a ctx s' := by
  simp only [bind, ReaderT.bind, StateT.bind, h]; rfl

theorem whnfCore'_const (n : Name) (us : List Level) (p : Bool) (m : Methods) (ctx : TypeChecker.Context)
    (s : TypeChecker.State) : Inner.whnfCore' (.const n us) p m ctx s = .ok (.const n us, s) := by
  unfold Inner.whnfCore'; rfl

theorem reduceNative_const (env : Environment) (n : Name) (us : List Level) :
    Inner.reduceNative env (.const n us) = .ok none := rfl

theorem reduceNat_const (n : Name) (us : List Level) (m : Methods) (ctx : TypeChecker.Context)
    (s : TypeChecker.State) : Inner.reduceNat (.const n us) m ctx s = .ok (none, s) := by
  unfold Inner.reduceNat; rfl

theorem unfoldDefinition_const_axiom {n : Name} {us : List Level} {ax : AxiomVal} (m : Methods)
    (ctx : TypeChecker.Context) (h : ctx.env.find? n = some (.axiomInfo ax)) (s : TypeChecker.State) :
    Inner.unfoldDefinition (.const n us) m ctx s = .ok (none, s) := by
  unfold Inner.unfoldDefinition Inner.unfoldDefinitionCore
  simp only [Expr.isApp, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind] 
  rw [show (liftM (getEnv) : RecM Environment) m ctx s = .ok (ctx.env, s) from rfl]
  simp [Inner.isDelta, Expr.getAppFn, h, ConstantInfo.deltaValue?, pure, ReaderT.pure, StateT.pure, Except.pure]

theorem whnf_loop_const_axiom {n : Name} {us : List Level} {ax : AxiomVal} (m : Methods)
    (ctx : TypeChecker.Context) (h : ctx.env.find? n = some (.axiomInfo ax)) (fuel : Nat)
    (s : TypeChecker.State) :
    Inner.whnfLoop (.const n us) (fuel + 1) m ctx s = .ok (.const n us, s) := by
  unfold Inner.whnfLoop
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show (liftM TypeChecker.getEnv : RecM Environment) m ctx s = .ok (ctx.env, s) from rfl]
  simp only [whnfCore'_const]
  rw [show (liftM (Inner.reduceNative ctx.env (.const n us)) : RecM (Option Expr)) m ctx s =
    .ok (none, s) from rfl]
  simp only
  rw [RecM.bind_ok (reduceNat_const _ _ _ _ _)]
  simp only
  rw [RecM.bind_ok (unfoldDefinition_const_axiom _ _ h _)]
  rfl

theorem whnf_const_axiom {n : Name} {us : List Level} {ax : AxiomVal}
    (ctx : TypeChecker.Context) (h : ctx.env.find? n = some (.axiomInfo ax)) (s : TypeChecker.State)
    (hs : s.whnfCache = {}) :
    ∀ r, (TypeChecker.whnf (.const n us) ctx s) = .ok r → r.1 = .const n us := by
  intro r hr
  have hr' : Inner.whnf (.const n us) (Methods.withFuel ctx.fuel.recDepth) ctx s = .ok r := hr
  clear hr
  generalize ctx.fuel.recDepth = fuel at hr'
  cases fuel with
  | zero => cases hr'
  | succ fuel =>
    simp only [Inner.whnf, Methods.withFuel] at hr'
    unfold Inner.whnf' at hr'
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind] at hr'
    rw [show (get : RecM TypeChecker.State) (Methods.withFuel fuel) ctx s = .ok (s, s) from rfl] at hr'
    simp only at hr'
    rw [show (readThe TypeChecker.Context : RecM _) (Methods.withFuel fuel) ctx s =
      .ok (ctx, s) from rfl] at hr'
    simp only [hs, Std.HashMap.getElem?_empty, TypeChecker.State.cached?] at hr'
    simp only [ReaderT.bind, StateT.bind, Except.bind] at hr'
    rw [M.bind_ok (show (readThe TypeChecker.Context : RecM _) (Methods.withFuel fuel) ctx s =
      .ok (ctx, s) from rfl)] at hr'
    generalize (if ctx.eagerReduce = true then ctx.fuel.whnfEager else ctx.fuel.whnf) = wf at hr'
    unfold TypeChecker.withTaint at hr'
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind] at hr'
    cases wf with
    | zero => cases hr'
    | succ wf =>
      simp only [get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure, Except.pure,
        StateT.pure, ReaderT.pure, whnf_loop_const_axiom _ ctx h wf] at hr'
      cases hr'; rfl

namespace AddInductive

/-- `whnf` of an axiom, run from `addInductive`, is the axiom. -/
theorem whnf_const_axiom.WF {c : VContext} {n : Name} {us : List Level} {ax : AxiomVal}
    (h : c.env.find? n = some (.axiomInfo ax)) :
    WF c (monadLift (TypeChecker.whnf (.const n us)) : M Expr) (· = .const n us) := by
  intro r hr
  change (TypeChecker.whnf (.const n us)).run c.env c.safety c.lctx c.lparams c.fuel = .ok r at hr
  simp only [TypeChecker.M.run, StateT.run'] at hr
  generalize hx : TypeChecker.whnf (.const n us) _ {} = x at hr
  rcases x with _ | ⟨r', s'⟩
  · cases hr
  · cases hr
    exact whnf_const_axiom _ h _ rfl _ hx

end AddInductive
end Lean4Lean

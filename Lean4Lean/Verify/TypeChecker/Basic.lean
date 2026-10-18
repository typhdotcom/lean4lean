import Lean4Lean.Verify.TypeChecker.State
import Lean4Lean.Verify.Support.SimIsDefEq

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace TypeChecker

structure Methods.WF (m : Methods) : Prop where
  /-- The methods run alike in contexts that agree on what their input mentions; a cached result
  holds in an enclosing scope's context by running its computation again there. -/
  ss : m.SS
  isDefEqCore : c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
    (m.isDefEqCore e₁ e₂).WF c s fun b _ => b → c.IsDefEqU e₁' e₂'
  whnfCore : c.TrExprS e e' →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  whnf : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  /-- A pi type is already in weak head normal form, and comes back as it is, without the
  metadata around it. -/
  whnf_forallE : e.consumeMData = .forallE n ty body bi →
    (m.whnf e).WF c s fun e₁ _ => e₁ = .forallE n ty body bi
  inferType : e.FVarsIn (· ∈ c.vlctx.fvars) →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    (m.inferType e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'

def RecM.WF (c : VContext) (s : VState) (x : RecM α) (Q : α → VState → Prop) : Prop :=
  ∀ m, m.WF → M.WF c s (x m) Q

theorem M.WF.liftExcept {c : VContext} {s : VState} {x : Except Exception α} {Q} (h : x.WF Q) :
    M.WF c s (liftM x) fun a _ => Q a := by
  rintro wf _ _ eq
  cases x <;> cases eq
  exact ⟨s, rfl, .rfl, wf, h _ rfl⟩

theorem M.WF.lift {c : VContext} {s : VState} {x : M α} {Q} (h : x.WF c s Q) :
    RecM.WF c s x Q := fun _ _ => h

instance : Coe (M.WF c s x Q) (RecM.WF c s x Q) := ⟨M.WF.lift⟩

theorem Inner.envGet.WF {c : VContext} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem RecM.WF.bind {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  fun _ h => M.WF.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.WF.bind_le {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (hs : s₀ ≤ s)
    (h2 : ∀ a s', s₀ ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  RecM.WF.bind h1 fun _ _ h => h2 _ _ (hs.trans h)

theorem RecM.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) : (pure a : RecM α).WF c s Q :=
  fun _ _ => .pure H

theorem RecM.WF.map {c : VContext} {s : VState} {x : RecM α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem RecM.WF.mono {c : VContext} {s : VState} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  rw [← id_map x]; exact h1.map h2

theorem RecM.WF.throw {c : VContext} {s : VState} {Q} : (throw e : RecM α).WF c s Q := nofun

theorem RecM.WF.le {c : VContext} {s : VState} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

/-- Loop invariant rule for `for h : i in [n:m] do ...`, with an invariant indexed by the next
position and a postcondition for an early `return`. -/
theorem RecM.WF.forIn'_range' {c : VContext} {Inv : Nat → β → VState → Prop}
    {Done : β → VState → Prop} :
    ∀ {l : List Nat} {n : Nat} {f : (a : Nat) → a ∈ l → β → RecM (ForInStep β)} {b : β}
      {s : VState}, l = List.range' n l.length →
    (∀ a h b s, Inv a b s → (f a h b).WF c s fun r s' =>
      (∀ b', r = .yield b' → Inv (a + 1) b' s') ∧ (∀ b', r = .done b' → Done b' s')) →
    Inv n b s → (∀ b s, Inv (n + l.length) b s → Done b s) →
    (ForIn'.forIn' l b f).WF c s Done
  | [], n, _, b, s, _, _, h, hD => by simpa using RecM.WF.pure (hD b s (by simpa using h))
  | a :: l, n, f, b, s, hl, H, h, hD => by
    simp only [List.length_cons, List.range'_succ, List.cons.injEq] at hl
    obtain ⟨rfl, hl⟩ := hl
    rw [List.forIn'_cons]
    refine (H a (.head _) b s h).bind fun r s' _ hr => ?_
    cases r with
    | done b' => exact .pure (hr.2 _ rfl)
    | yield b' =>
      exact RecM.WF.forIn'_range' hl (fun a' h' b s => H a' (.tail _ h') b s) (hr.1 _ rfl)
        (fun b s h => hD b s (by simpa [Nat.add_assoc, Nat.add_comm 1] using h))

theorem RecM.WF.forIn'_range {c : VContext} {Inv : Nat → β → VState → Prop}
    {Done : β → VState → Prop} {n m : Nat}
    {f : (a : Nat) → a ∈ [n:m] → β → RecM (ForInStep β)} {b : β} {s : VState}
    (H : ∀ a h b s, Inv a b s → (f a h b).WF c s fun r s' =>
      (∀ b', r = .yield b' → Inv (a + 1) b' s') ∧ (∀ b', r = .done b' → Done b' s'))
    (h : Inv n b s) (hD : ∀ b s, Inv (max n m) b s → Done b s) :
    (ForIn'.forIn' [n:m] b f).WF c s Done := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine RecM.WF.forIn'_range' (by simp) (fun a h' b s => H a _ b s) h fun b s h => hD b s ?_
  simpa [Std.Legacy.Range.size, show n + (m - n) = max n m by omega] using h

/-- Loop invariant rule for `for i in l do ...` over consecutive numbers, with a body that only
continues. -/
theorem RecM.WF.forIn_list_range' {c : VContext} {Inv : Nat → β → VState → Prop} :
    ∀ {l : List Nat} {n : Nat} {f : Nat → β → RecM (ForInStep β)} {b : β} {s : VState},
    l = List.range' n l.length →
    (∀ a b s, a ∈ l → Inv a b s → (f a b).WF c s fun r s' =>
      (∀ b', r = .yield b' → Inv (a + 1) b' s') ∧ ∀ b', r ≠ .done b') →
    Inv n b s → (forIn l b f).WF c s fun b' s' => Inv (n + l.length) b' s'
  | [], n, _, b, s, _, _, h => by simpa using RecM.WF.pure h
  | a :: l, n, f, b, s, hl, H, h => by
    simp only [List.length_cons, List.range'_succ, List.cons.injEq] at hl
    obtain ⟨rfl, hl⟩ := hl
    rw [List.forIn_cons]
    refine (H a b s (.head _) h).bind fun r s' _ hr => ?_
    cases r with
    | done b' => exact (hr.2 b' rfl).elim
    | yield b' =>
      refine (RecM.WF.forIn_list_range' hl (fun a' b s h' => H a' b s (.tail _ h'))
        (hr.1 _ rfl)).mono fun _ _ _ h => ?_
      simpa [Nat.add_assoc, Nat.add_comm 1] using h

/-- Loop invariant rule for `for i in [:n] do ...`, with a body that only continues. -/
theorem RecM.WF.forIn_range {c : VContext} {Inv : Nat → β → VState → Prop} {n : Nat}
    {f : Nat → β → RecM (ForInStep β)} {b : β} {s : VState}
    (H : ∀ a b s, a < n → Inv a b s → (f a b).WF c s fun r s' =>
      (∀ b', r = .yield b' → Inv (a + 1) b' s') ∧ ∀ b', r ≠ .done b')
    (h : Inv 0 b s) : (forIn [:n] b f).WF c s fun b' s' => Inv n b' s' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine (RecM.WF.forIn_list_range' (n := 0) (by simp [Std.Legacy.Range.size])
    (fun a b s h' => H a b s (by simp [Std.Legacy.Range.size] at h'; omega)) h).mono
    fun _ _ _ h => by simpa [Std.Legacy.Range.size] using h

theorem RecM.WF.taintWith {c : VContext} {s : VState} :
    (modify (·.taintWith l) : RecM Unit).WF c s fun _ _ => True := by
  rintro _ _ wf _ _ ⟨⟩; exact ⟨⟨_⟩, rfl, .rfl, wf.setTaint _ s.fvLvl, trivial⟩

theorem RecM.WF.pureBind {c : VContext} {s : VState} {f : β → RecM α} {Q}
    {x : β} (H : WF c s (f x) Q) : ((Pure.pure x : RecM β) >>= f).WF c s Q := H

theorem get.WF {c : VContext} {s : VState} :
    M.WF c s get fun a s' => s.toState = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.get {c : VContext} {s : VState} {f : State → RecM α} {Q}
    (H : WF c s (f s.toState) Q) : (get >>= f).WF c s Q := H

theorem getEnv.WF {c : VContext} {s : VState} :
    M.WF c s getEnv fun a s' => c.env = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getEnv {c : VContext} {s : VState} {f : Environment → M α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem RecM.WF.getEnv {c : VContext} {s : VState} {f : Environment → RecM α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem getLCtx.WF {c : VContext} {s : VState} :
    M.WF c s getLCtx fun a s' => c.lctx' = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, c.lctx_eq, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : VState} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx') Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.readThe {c : VContext} {s : VState} {f : Context → RecM α} {Q}
    (H : WF c s (f c.toContext) Q) : (readThe Context >>= f).WF c s Q := H

theorem getNGen.WF {c : VContext} {s : VState} :
    M.WF c s getNGen fun a s' => s.ngen = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → M α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → RecM α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.stateWF {c : VContext} {s : VState} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

@[simp] theorem toLBool_true {b : Bool} : b.toLBool = .true ↔ b = true := by
  cases b <;> simp [Bool.toLBool]

theorem RecM.WF.toLBoolM {Q : VState → Prop} {x : RecM Bool}
    (H : x.WF c s fun b s => b → Q s) : (toLBoolM x).WF c s fun b s => b = .true → Q s :=
  H.bind fun _ _ _ H => .pure fun h => H (by simpa using h)

theorem _root_.Lean4Lean.TypeChecker.VContext.dom_of_tr {c : VContext}
    {x : Expr} {x' : VExpr} (h : c.TrExprS x x') : ∀ y ∈ x.fvarsList, c.lctx.Dom y := by
  intro y hy
  have := (fvarsIn_iff.1 h.fvarsIn).1 y hy
  rw [← c.lctx_eq]
  simpa [LocalContext.Dom, Option.isSome_iff_exists] using c.trlctx.find?_eq_some.2 this

/-- The state a fresh local declaration's scope starts in is well formed. -/
theorem VState.WF.enterLocal [VEnv.Injective] {c : VContext} {m} [cwf : c.MLCWF m] {s : VState}
    (wf : s.WF (c.withMLC m)) {name ty ty' bi}
    (hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none)
    (hty : (c.withMLC m).TrExprS ty ty') [cwf' : c.MLCWF (.vlam ⟨s.ngen.curr⟩ name ty ty' bi m)] :
    VState.WF (c.withMLC (.vlam ⟨s.ngen.curr⟩ name ty ty' bi m)) s.enter := by
  have hE := wf.supp.ctxExt hfresh (name := name) (ty := ty) (bi := bi)
  refine wf.enter hfresh (.vlam .refl) (by simp [MLCtx.under, VContext.withMLC])
    (by simp [VContext.withMLC]) rfl rfl rfl rfl rfl (fun fv h1 h2 => ?_) ?_
  · exact (List.mem_cons.1 h1).resolve_right h2
  · refine wf.supp.enter rfl hE (wf.supp.lctxWF.mkLocalDecl hE.fresh) fun d hd => ?_
    have hd' : ((c.withMLC m).lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi).find? ⟨s.ngen.curr⟩ = some d := hd
    rw [LocalContext.find?_mkLocalDecl wf.supp.lctxWF hE.fresh] at hd'; simp at hd'; subst hd'
    exact ⟨VContext.dom_of_tr hty, by simp [LocalDecl.value', Expr.fvarsList]; exact hE.dom⟩

/-- The state a fresh let-declaration's scope starts in is well formed. -/
theorem VState.WF.enterLet [VEnv.Injective] {c : VContext} {m} [cwf : c.MLCWF m] {s : VState}
    (wf : s.WF (c.withMLC m)) {name ty ty' val val'}
    (hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none)
    (hty : (c.withMLC m).TrExprS ty ty') (hval : (c.withMLC m).TrExprS val val')
    [cwf' : c.MLCWF (.vlet ⟨s.ngen.curr⟩ name ty val ty' val' m)] :
    VState.WF (c.withMLC (.vlet ⟨s.ngen.curr⟩ name ty val ty' val' m)) s.enter := by
  have hE := wf.supp.ctxExtLet hfresh (name := name) (ty := ty) (val := val)
  refine wf.enter hfresh (.vlet .refl) (by simp [MLCtx.under, VContext.withMLC])
    (by simp [VContext.withMLC]) rfl rfl rfl rfl rfl (fun fv h1 h2 => ?_) ?_
  · exact (List.mem_cons.1 h1).resolve_right h2
  · refine wf.supp.enter rfl hE (wf.supp.lctxWF.mkLetDecl hE.fresh) fun d hd => ?_
    have hd' : ((c.withMLC m).lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val).find? ⟨s.ngen.curr⟩ = some d := hd
    rw [LocalContext.find?_mkLetDecl wf.supp.lctxWF hE.fresh] at hd'; simp at hd'; subst hd'
    exact ⟨VContext.dom_of_tr hty, fun y hy => hE.dom_of (VContext.dom_of_tr hval y hy)⟩

/-- The state at the end of a local declaration's scope, closed, is well formed. -/
theorem VState.WF.restoreDecl {c : VContext} {m m'} [cwf : c.MLCWF m] [cwf' : c.MLCWF m']
    {s s₁ : VState} (wf : s.WF (c.withMLC m)) (wf₁ : s₁.WF (c.withMLC m')) (le : s.enter ≤ s₁)
    (hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none)
    (H : CtxExt (c.withMLC m).toContext (c.withMLC m').toContext ⟨s.ngen.curr⟩)
    (hb : m.Below m') (hx : m'.under ⟨s.ngen.curr⟩ = m)
    (hnew : ∀ fv ∈ m'.vlctx.fvars, fv ∉ m.vlctx.fvars → fv = ⟨s.ngen.curr⟩) :
    (s.restore s₁).WF (c.withMLC m) :=
  wf.restore wf₁ le H hb hx rfl rfl rfl rfl rfl hnew

protected theorem RecM.WF.withLocalDecl [VEnv.Injective] {c : VContext} {m} [cwf : c.MLCWF m]
    {s₀ s : VState} {f : Expr → RecM α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀.ngen ≤ s.ngen)
    (H : ∀ id cwf' s', s₀.ngen ≤ s'.ngen → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q)
    (hQ : ∀ a (s₁ s₂ : VState), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by intro _ _ _ _ h; exact h) :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
  have hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none := hfresh
  have cwf' : c.MLCWF (.vlam ⟨s.ngen.curr⟩ name ty ty' bi m) := ⟨cwf.1, hfresh, hty, hty'⟩
  have wf' := wf.enterLocal hfresh hty (cwf' := cwf')
  obtain ⟨s'', rfl, hs2, wf'', hs4⟩ :=
    H _ _ _ (hs.trans NameGenerator.LE.next) s.ngen.not_reserves_self _ mwf wf' a _ e₁
  refine ⟨s.restore s'', rfl, ⟨NameGenerator.LE.next.trans hs2.1, rfl, rfl⟩, ?_,
    hQ _ s'' _ rfl hs4⟩
  exact wf.restoreDecl wf'' hs2 hfresh (wf.supp.ctxExt hfresh) (.vlam .refl)
    (by simp [MLCtx.under]) (fun fv h1 h2 => by simp at h1; exact h1.resolve_right h2)

/-- The `M`-level twin of `RecM.WF.withLocalDecl`. The primitive checker probes its
definitions under `withLocalDecl` in `M`, so it needs this form. -/
protected theorem M.WF.withLocalDecl [VEnv.Injective] {c : VContext} {m} [cwf : c.MLCWF m]
    {s₀ s : VState} {f : Expr → M α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀.ngen ≤ s.ngen)
    (H : ∀ id cwf' s', s₀.ngen ≤ s'.ngen → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q)
    (hQ : ∀ a (s₁ s₂ : VState), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by intro _ _ _ _ h; exact h) :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro wf a s' e
  obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
  have hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none := hfresh
  have cwf' : c.MLCWF (.vlam ⟨s.ngen.curr⟩ name ty ty' bi m) := ⟨cwf.1, hfresh, hty, hty'⟩
  have wf' := wf.enterLocal hfresh hty (cwf' := cwf')
  obtain ⟨s'', rfl, hs2, wf'', hs4⟩ :=
    H _ _ _ (hs.trans NameGenerator.LE.next) s.ngen.not_reserves_self wf' a _ e₁
  refine ⟨s.restore s'', rfl, ⟨NameGenerator.LE.next.trans hs2.1, rfl, rfl⟩, ?_,
    hQ _ s'' _ rfl hs4⟩
  exact wf.restoreDecl wf'' hs2 hfresh (wf.supp.ctxExt hfresh) (.vlam .refl)
    (by simp [MLCtx.under]) (fun fv h1 h2 => by simp at h1; exact h1.resolve_right h2)

protected theorem RecM.WF.withLetDecl [VEnv.Injective] {c : VContext} {m} [cwf : c.MLCWF m]
    {s₀ s : VState} {f : Expr → RecM α} {Q name ty ty'}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    (hs : s₀.ngen ≤ s.ngen)
    (H : ∀ id cwf' s', s₀.ngen ≤ s'.ngen → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlet id name ty val ty' val' m) (wf := cwf')) s' (f (.fvar id)) Q)
    (hQ : ∀ a (s₁ s₂ : VState), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by intro _ _ _ _ h; exact h) :
    (withLetDecl name ty val f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
  have hfresh : m.lctx.find? ⟨s.ngen.curr⟩ = none := hfresh
  have cwf' : c.MLCWF (.vlet ⟨s.ngen.curr⟩ name ty val ty' val' m) :=
    ⟨cwf.1, hfresh, hty, hval, hval'⟩
  have wf' := wf.enterLet hfresh hty hval (cwf' := cwf')
  obtain ⟨s'', rfl, hs2, wf'', hs4⟩ :=
    H _ _ _ (hs.trans NameGenerator.LE.next) s.ngen.not_reserves_self _ mwf wf' a _ e₁
  refine ⟨s.restore s'', rfl, ⟨NameGenerator.LE.next.trans hs2.1, rfl, rfl⟩, ?_,
    hQ _ s'' _ rfl hs4⟩
  exact wf.restoreDecl wf'' hs2 hfresh (wf.supp.ctxExtLet hfresh) (.vlet .refl)
    (by simp [MLCtx.under]) (fun fv h1 h2 => by simp at h1; exact h1.resolve_right h2)


/-- A successful run of `withTaint x`: `x` run with the taint reset. -/
theorem withTaint_run {x : RecM α} {m : Methods} {ctx : Context} {st : State} {a s'}
    (e : (TypeChecker.withTaint x) m ctx st = .ok (a, s')) :
    ∃ b s₁, x m ctx { st with taint := 0 } = .ok (b, s₁) ∧ a = (b, s₁.taint) ∧
      s' = { s₁ with taint := max st.taint s₁.taint } := by
  unfold TypeChecker.withTaint at e
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, Except.pure,
    StateT.pure, ReaderT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at e
  split at e <;> [cases e; skip]
  rename_i v e₁
  obtain ⟨b, s₁⟩ := v
  cases e
  exact ⟨b, s₁, e₁, rfl, rfl⟩


namespace Inner

theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnf he

theorem whnf.forallE_eq {c : VContext} {s : VState} (h : e.consumeMData = .forallE n ty body bi) :
    RecM.WF c s (whnf e) fun e₁ _ => e₁ = .forallE n ty body bi :=
  fun _ wf => wf.whnf_forallE h

theorem isDefEqCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  fun _ wf => wf.isDefEqCore he₁ he₂

theorem inferType.WF' {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  fun _ wf => wf.inferType h1 hinf

/-- With the translation already in hand, `hinf` is satisfied whichever mode is used, so this
holds at both settings of `inferOnly`. -/
theorem inferType.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (inferType.WF' he.fvarsIn fun _ => ⟨_, he⟩).le
    fun _ _ _ ⟨_, _, h1, h2, h3, h4⟩ => ⟨_, h1, he, h3, ?_⟩
  have := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  exact h4.defeqU_l c.Ewf c.Δwf this

theorem inferType.WF_uniq [VEnv.Injective] {c : VContext} {s : VState}
    (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  (inferType.WF he).le fun _ _ _ ⟨_, _, _, h1, h2⟩ =>
  ⟨_, h1, h2.uniqU c.Ewf c.Δwf hty⟩

theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  inferType.WF' h1 nofun

theorem whnfCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnfCore he

theorem isDelta_is_some : isDelta env e = some ci ↔
    ∃ n, env.find? n = some ci ∧ (∃ v, ci.deltaValue? = some v) ∧
      ∃ ls, e.getAppFn = .const n ls ∧ ls.length = ci.numLevelParams := by
  simp only [isDelta]
  split <;> [split <;> [split; skip]; skip] <;>
    simp_all [Option.isSome_iff_exists] <;> grind

def UnfoldDefinition.WF (c : VContext) (e e₀ : Expr) (e' : VExpr) : Option Expr → Prop
  | some e₁ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  | none => ∀ {{n ci v ls}}, c.env.find? n = some ci → ci.deltaValue? = some v →
    e₀ = .const n ls → ls.length = ci.numLevelParams → False

theorem unfoldDefinitionCore.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinitionCore e) fun oe _ => UnfoldDefinition.WF c e e e' oe := by
  dsimp [unfoldDefinitionCore]
  split <;> [refine .getEnv ?_; (rename_i H; exact .pure fun _ _ _ _ _ _ h => nomatch H _ _ h)]
  split; rotate_left
  · rename_i H; refine .pure ?_; rintro _ _ _ _ h1 h2 ⟨⟩ hlen
    cases H _ (isDelta_is_some.2 ⟨_, h1, ⟨_, h2⟩, _, rfl, hlen⟩)
  rename_i n ls oci ci h1
  obtain ⟨_, h3, ⟨_, h4⟩, _, ⟨⟩, hlen⟩ := isDelta_is_some.1 h1
  have : UnfoldDefinition.WF c (.const n ls) (.const n ls) e'
      (some (instantiateDeltaValue ci ls)) := by
    let .const a1 a2 a3 := he
    have ⟨rfl, b1, b2, b3⟩ := c.trenv.find?_uniq h3 a1
    simp [instantiateDeltaValue, h4]
    have c1 := c.trenv.of_value h3 b1 h4 |>.instL c.Ewf (by trivial) a2 (b2.trans a3.symm)
    have := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [c1.wf.closedN c.Ewf trivial |>.liftN_eq (Nat.zero_le _)] at this
    simp [VExpr.instL] at this; rw [VLevel.inst_map_id] at this
    · exact ⟨fun _ _ _ => c1.fvarsIn.mono nofun, this⟩
    · exact (List.mapM_eq_some.1 a2).length_eq.symm.trans <| a3.trans b2.symm
  split <;> [rename_i h5; exact .pure this]
  refine .pureBind <| .get ?_
  split <;> [rename_i eq; skip]
  · refine .stateWF fun wf => .pure ?_
    obtain ⟨_, _, _, ⟨⟩, a1, rfl⟩ := wf.unfold_wf eq
    cases h3.symm.trans a1; exact this
  · refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ => .pure this
    rintro _ mwf wf _ _ ⟨⟩
    have hu : ∀ (e r : Expr), (s.unfold.insert (.const n ls) (instantiateDeltaValue ci ls))[e]? =
        some r → ∀ S : Supp, S.EnvClosed c.env → e.SuppIn S → r.SuppIn S := by
      intro e' r' h' S hS he'
      rw [Std.HashMap.getElem?_insert] at h'; split at h'
      · cases h'; rename_i eq
        exact isDelta_supp hS h1 (Expr.SuppIn.eqv_rev eq he')
      · exact wf.supp.unfold _ _ h' S hS he'
    have hsupp : SuppState c.toContext { s.toState with
        unfold := s.unfold.insert (.const n ls) (instantiateDeltaValue ci ls) } :=
      { wf.supp with unfold := hu }
    refine ⟨{ s with toState := _ }, rfl, .rfl, { wf with unfold_wf := ?_, supp := hsupp }, ⟨⟩⟩
    intro e e'; simp only [Std.HashMap.getElem?_insert]
    split <;> [rintro ⟨⟩; exact (wf.unfold_wf ·)]
    rename_i eq; rw [BEq.comm, Expr.eqv_const] at eq
    exact ⟨_, _, _, eq, h3, rfl⟩

theorem unfoldDefinition.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinition e) fun oe _ => UnfoldDefinition.WF c e e.getAppFn e' oe := by
  simp [unfoldDefinition]; split; rotate_left
  · rename_i h; refine (unfoldDefinitionCore.WF he).mono fun _ _ _ H => ?_
    rwa [show e.getAppFn = e by revert h; unfold Expr.isApp Expr.getAppFn; split <;> simp]
  have ⟨f', stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  refine (unfoldDefinitionCore.WF stk.tr).bind fun oe _ _ H => ?_
  cases oe <;> [exact .pure H; refine .pure ?_]
  have ⟨h1, h2⟩ := H
  rw [Expr.mkAppRevRange_eq (l₁ := []) (l₂ := e.getAppArgsRevList) (l₃ := [])
    (by simp [Expr.getAppRevArgs_toList]) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
  simp only [Expr.getAppArgsRevList_reverse]; constructor
  · exact (e.mkAppList_getAppArgsList ▸ h1.mkAppList :)
  · exact h2.rebuild_mkAppList c.Ewf c.Δwf stk.tr (e.mkAppList_getAppArgsList ▸ he :)

theorem ensureSortCore.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      (∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' ∧ c.FVarsBelow e e1 := by
  simp [ensureSortCore]; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he.trExpr c.Ewf c.Δwf, .rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he, hb⟩
  exact .getEnv <| .getLCtx .throw

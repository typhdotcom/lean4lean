import Lean4Lean.Verify.Support.IsDefEq

/-!
# The type checker reads only what its input mentions

A run of the type checker in a context `c₁` that succeeds succeeds the same way, with the same
result and final state, in any context `c₂` that agrees with `c₁` on what the input mentions,
closed under `c₁`'s local context and environment (`Agree`). Free variables are handed out the same
way in both, so `c₂` may lack declarations of `c₁` that the input does not reach: constants of a
bigger environment, or free variables of a bigger local context.

`M.SS` pairs `M.SWF`, which provides what the intermediate results mention, with this simulation.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

/-- `c₂` agrees with `c₁` on what `S` allows: the same declarations of its constants and free
variables, up to their position in the local context, and the same settings. -/
structure Agree (S : Supp) (c₁ c₂ : Context) : Prop where
  env : ∀ n, S.const n → c₂.env.find? n = c₁.env.find? n
  lctx : ∀ fv, S.fv fv →
    (c₂.lctx.find? fv).map LocalDecl.erase = (c₁.lctx.find? fv).map LocalDecl.erase
  wf : c₂.lctx.WF
  quotInit : c₂.env.quotInit = c₁.env.quotInit
  safety : c₂.safety = c₁.safety
  eagerReduce : c₂.eagerReduce = c₁.eagerReduce
  lparams : ∀ n, S.lvl n → n ∈ c₁.lparams → n ∈ c₂.lparams
  fuel : c₂.fuel = c₁.fuel
  /-- `c₂` sets aside at least the facts `c₁` does. -/
  ceiling : ∀ l, c₂.ceiling.all (l ≤ ·) → c₁.ceiling.all (l ≤ ·) := by intro _ h; exact h

theorem Agree.refl {S : Supp} {c : Context} (wf : c.lctx.WF) : Agree S c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, wf, rfl, rfl, rfl, fun _ _ => id, rfl, fun _ h => h⟩

/-- Every free variable `c₂` declares that `c₁` does not is one the name generator `g` has not
made yet, so the variables a run that ends at `g` makes are fresh for `c₂` as for `c₁`. -/
def FreshFor (c₁ c₂ : Context) (g : NameGenerator) : Prop :=
  ∀ fv, c₂.lctx.Dom fv → c₁.lctx.Dom fv ∨ ¬g.Reserves fv

theorem FreshFor.of_dom {c₁ c₂ : Context} (H : ∀ fv, c₂.lctx.Dom fv → c₁.lctx.Dom fv) :
    FreshFor c₁ c₂ g := fun fv h => .inl (H fv h)

theorem FreshFor.mono {c₁ c₂ : Context} (H : FreshFor c₁ c₂ g') (h : g ≤ g') :
    FreshFor c₁ c₂ g := fun fv hfv => (H fv hfv).imp_right fun h' h'' => h' (h''.mono h)

theorem Agree.mono {S S' : Supp} {c₁ c₂ : Context} (H : Agree S' c₁ c₂) (h : S ≤ S') :
    Agree S c₁ c₂ :=
  { H with
    env := fun n hn => H.env n (h.const n hn)
    lctx := fun fv hfv => H.lctx fv (h.fv fv hfv)
    lparams := fun n hn => H.lparams n (h.lvl n hn) }

/-- A run from `s` to `s'` used no fact `c₂`'s ceiling sets aside, which is below the scopes open
at `s`: the ceiling is at least the taint it ends with. -/
def CeilFits (c₂ : Context) (s s' : State) : Prop :=
  ∀ lab, c₂.ceiling = some lab → s'.taint ≤ lab ∧ lab < s.scopeIds.size

theorem CeilFits.left {L : LocalContext} {c₂ : Context} {s s₁ s₂ : State} (h : CeilFits c₂ s s₂)
    (m : State.Mono L s₁ s₂) : CeilFits c₂ s s₁ := fun lab hl =>
  let ⟨h1, h2⟩ := h lab hl; ⟨Nat.le_trans m.taint h1, h2⟩

theorem CeilFits.right {L : LocalContext} {c₂ : Context} {s s₁ s₂ : State} (h : CeilFits c₂ s s₂)
    (m : State.Mono L s s₁) : CeilFits c₂ s₁ s₂ := fun lab hl =>
  let ⟨h1, h2⟩ := h lab hl; ⟨h1, m.scopeIds ▸ h2⟩

theorem CeilFits.none {c₂ : Context} {s s' : State} (h : c₂.ceiling = none) :
    CeilFits c₂ s s' := fun _ hl => by simp [h] at hl

/-- The run inside a scope, from the run that closes it. -/
theorem CeilFits.enter {c₂ c₂' : Context} {s s₁ : State} (hc : c₂'.ceiling = c₂.ceiling)
    (h : CeilFits c₂ s (s.restore s₁)) : CeilFits c₂' s.enter s₁ := fun lab hl => by
  obtain ⟨h1, h2⟩ := h lab (hc ▸ hl)
  simp only [State.restore, State.popScope] at h1
  refine ⟨?_, ?_⟩
  · have := Nat.le_trans (Nat.le_max_right _ _) h1; omega
  · simp [State.enter, State.pushScope]; omega

/-- The run `withTaint` makes, from its own. -/
theorem CeilFits.withTaint {c₂ : Context} {s s₁ : State}
    (h : CeilFits c₂ s { s₁ with taint := max s.taint s₁.taint })
    (hs : s₁.scopeIds = s.scopeIds) : CeilFits c₂ { s with taint := 0 } s₁ := fun lab hl =>
  let ⟨h1, h2⟩ := h lab hl; ⟨Nat.le_trans (Nat.le_max_right _ _) h1, h2⟩

/-- A successful run of `x₁` in `c₁` is a successful run of `x₂` in `c₂`, from the same state,
when the variables it makes are fresh for `c₂` and it used no fact `c₂` sets aside. -/
def M.Sim (c₁ c₂ : Context) (s : State) (x₁ x₂ : M α) : Prop :=
  SuppState c₁ s → ∀ a s', x₁ c₁ s = .ok (a, s') → FreshFor c₁ c₂ s'.ngen → CeilFits c₂ s s' →
    x₂ c₂ s = .ok (a, s')

/-- `x₁` is `M.SWF` in `c₁`, and `x₂` runs in `c₂` as `x₁` does in `c₁`. -/
def M.SS (c₁ c₂ : Context) (s : State) (x₁ x₂ : M α) (Q : α → State → Prop) : Prop :=
  x₁.SWF c₁ s Q ∧ M.Sim c₁ c₂ s x₁ x₂

theorem M.Sim.bind {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {f₁ f₂ : α → M β} {Q}
    (h1 : M.Sim c₁ c₂ s x₁ x₂) (hw : x₁.SWF c₁ s Q)
    (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → M.Sim c₁ c₂ s' (f₁ a) (f₂ a))
    (hw2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → (f₁ a).SWF c₁ s' fun _ _ => True) :
    M.Sim c₁ c₂ s (x₁ >>= f₁) (x₂ >>= f₂) := by
  intro wf b s₂
  simp only [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h hF hC; rename_i v eq
  obtain ⟨wf', le, mo, hq⟩ := hw wf _ _ eq
  obtain ⟨-, le₂, mo₂, -⟩ := hw2 _ _ le hq wf' _ _ h
  rw [h1 wf _ _ eq (hF.mono le₂) (hC.left mo₂)]
  exact h2 _ _ le hq wf' _ _ h hF (hC.right mo)

theorem M.SS.bind {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {f₁ f₂ : α → M β} {Q R}
    (h1 : M.SS c₁ c₂ s x₁ x₂ Q)
    (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → M.SS c₁ c₂ s' (f₁ a) (f₂ a) R) :
    M.SS c₁ c₂ s (x₁ >>= f₁) (x₂ >>= f₂) R :=
  ⟨h1.1.bind fun a s' le h => (h2 a s' le h).1,
    h1.2.bind h1.1 (fun a s' le h => (h2 a s' le h).2)
      fun a s' le h => (h2 a s' le h).1.mono fun _ _ _ _ => trivial⟩

theorem M.SS.pure {c₁ c₂ : Context} {s : State} {Q} (H : Q a s) :
    M.SS c₁ c₂ s (pure a : M α) (pure a) Q :=
  ⟨.pure H, fun _ _ _ h _ _ => h⟩

theorem M.SS.mono {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {Q R}
    (h1 : M.SS c₁ c₂ s x₁ x₂ Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R a s') :
    M.SS c₁ c₂ s x₁ x₂ R := ⟨h1.1.mono h2, h1.2⟩

/-- A computation that never succeeds in `c₁` simulates anything. -/
theorem M.Sim.fail {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α}
    (h : x₁.SWF c₁ s fun _ _ => False) : M.Sim c₁ c₂ s x₁ x₂ :=
  fun wf a s' eq _ _ => (h wf a s' eq).2.2.2.elim

/-- The type checker's methods, as `M.SS` sees them: on an input in `c₁` that mentions only what
`S` allows, they run in `c₂` as in `c₁`. -/
structure Methods.SS (m : Methods) : Prop where
  isDefEqCore : ∀ {S c₁ c₂ s e₁ e₂}, Agree S c₁ c₂ → S.Closed c₁ → Dom c₁ e₁ → Dom c₁ e₂ →
    e₁.SuppIn S → e₂.SuppIn S →
    M.SS c₁ c₂ s (m.isDefEqCore e₁ e₂) (m.isDefEqCore e₁ e₂) fun _ _ => True
  whnfCore : ∀ {S c₁ c₂ s e cheapProj}, Agree S c₁ c₂ → S.Closed c₁ → Dom c₁ e → e.SuppIn S →
    M.SS c₁ c₂ s (m.whnfCore e cheapProj) (m.whnfCore e cheapProj) fun e₁ _ => SuppBelow c₁ e e₁
  whnf : ∀ {S c₁ c₂ s e}, Agree S c₁ c₂ → S.Closed c₁ → Dom c₁ e → e.SuppIn S →
    M.SS c₁ c₂ s (m.whnf e) (m.whnf e) fun e₁ _ => SuppBelow c₁ e e₁
  inferType : ∀ {S c₁ c₂ s e inferOnly}, Agree S c₁ c₂ → S.Closed c₁ → Dom c₁ e → e.SuppIn S →
    M.SS c₁ c₂ s (m.inferType e inferOnly) (m.inferType e inferOnly) fun ty _ => SuppBelow c₁ e ty

theorem Methods.SS.swf {m : Methods} (H : m.SS) : m.SWF where
  isDefEqCore h₁ h₂ := fun wf =>
    (H.isDefEqCore (Agree.refl wf.lctxWF) wf.closedDom h₁ h₂ (dom_iff.1 h₁) (dom_iff.1 h₂)).1 wf
  whnfCore h := fun wf => (H.whnfCore (Agree.refl wf.lctxWF) wf.closedDom h (dom_iff.1 h)).1 wf
  whnf h := fun wf => (H.whnf (Agree.refl wf.lctxWF) wf.closedDom h (dom_iff.1 h)).1 wf
  inferType h := fun wf => (H.inferType (Agree.refl wf.lctxWF) wf.closedDom h (dom_iff.1 h)).1 wf

def RecM.SS (c₁ c₂ : Context) (s : State) (x₁ x₂ : RecM α) (Q : α → State → Prop) : Prop :=
  ∀ m, m.SS → M.SS c₁ c₂ s (x₁ m) (x₂ m) Q

theorem RecM.SS.bind {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {f₁ f₂ : α → RecM β} {Q R}
    (h1 : RecM.SS c₁ c₂ s x₁ x₂ Q)
    (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → RecM.SS c₁ c₂ s' (f₁ a) (f₂ a) R) :
    RecM.SS c₁ c₂ s (x₁ >>= f₁) (x₂ >>= f₂) R :=
  fun _ h => M.SS.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.SS.pure {c₁ c₂ : Context} {s : State} {Q} (H : Q a s) :
    RecM.SS c₁ c₂ s (pure a : RecM α) (pure a) Q := fun _ _ => .pure H

theorem RecM.SS.mono {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q R}
    (h1 : RecM.SS c₁ c₂ s x₁ x₂ Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R a s') :
    RecM.SS c₁ c₂ s x₁ x₂ R := fun _ h => (h1 _ h).mono h2

theorem M.SS.lift {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {Q} (h : M.SS c₁ c₂ s x₁ x₂ Q) :
    RecM.SS c₁ c₂ s x₁ x₂ Q := fun _ _ => h

theorem RecM.SS.stateWF {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q}
    (H : SuppState c₁ s → RecM.SS c₁ c₂ s x₁ x₂ Q) : RecM.SS c₁ c₂ s x₁ x₂ Q :=
  fun m hm => ⟨fun wf => (H wf m hm).1 wf, fun wf => (H wf m hm).2 wf⟩

/-- A computation that never succeeds in `c₁`. -/
theorem RecM.SS.fail {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q}
    (H : x₁.SWF c₁ s fun _ _ => False) : RecM.SS c₁ c₂ s x₁ x₂ Q :=
  fun m hm => ⟨(H m hm.swf).mono fun _ _ _ h => h.elim, .fail (H m hm.swf)⟩

theorem RecM.SS.throw {c₁ c₂ : Context} {s : State} {x₂ : RecM α} {Q} :
    RecM.SS c₁ c₂ s (throw e) x₂ Q := .fail .throw

theorem RecM.SS.get {c₁ c₂ : Context} {s : State} {f₁ f₂ : State → RecM α} {Q}
    (H : RecM.SS c₁ c₂ s (f₁ s) (f₂ s) Q) : RecM.SS c₁ c₂ s (get >>= f₁) (get >>= f₂) Q := H

theorem RecM.SS.getEnv {c₁ c₂ : Context} {s : State} {f₁ f₂ : Environment → RecM α} {Q}
    (H : RecM.SS c₁ c₂ s (f₁ c₁.env) (f₂ c₂.env) Q) :
    RecM.SS c₁ c₂ s (liftM getEnv >>= f₁) (liftM getEnv >>= f₂) Q := H

theorem RecM.SS.getLCtx {c₁ c₂ : Context} {s : State} {f₁ f₂ : LocalContext → RecM α} {Q}
    (H : RecM.SS c₁ c₂ s (f₁ c₁.lctx) (f₂ c₂.lctx) Q) :
    RecM.SS c₁ c₂ s (getLCtx >>= f₁) (getLCtx >>= f₂) Q := H

theorem RecM.SS.readThe {c₁ c₂ : Context} {s : State} {f₁ f₂ : Context → RecM α} {Q}
    (H : RecM.SS c₁ c₂ s (f₁ c₁) (f₂ c₂) Q) :
    RecM.SS c₁ c₂ s (readThe Context >>= f₁) (readThe Context >>= f₂) Q := H

/-- An `Except` computation that, when it succeeds on the left, succeeds the same on the right. -/
theorem RecM.SS.liftExcept {c₁ c₂ : Context} {s : State} {x₁ x₂ : Except Exception α} {Q}
    (hw : x₁.WF Q) (h : ∀ a, x₁ = .ok a → x₂ = .ok a) :
    RecM.SS c₁ c₂ s (liftM x₁ : M α) (liftM x₂ : M α) fun a _ => Q a := by
  refine fun _ _ => ⟨.liftExcept hw, fun _ a s' eq _ _ => ?_⟩
  cases e : x₁ <;> rw [e] at eq <;> cases eq
  rw [h _ e]; rfl

/-- The default value a panic returns. -/
theorem RecM.SS.panic {c₁ c₂ : Context} {s : State} [Inhabited α] {Q} (H : Q default s) :
    RecM.SS c₁ c₂ s (panicWithPosWithDecl modName declName line col msg : RecM α)
      (panicWithPosWithDecl modName' declName' line' col' msg') Q :=
  fun _ _ => M.SS.pure H

/-- A state update, which does not read the context. -/
theorem RecM.SS.modify {c₁ c₂ : Context} {s : State} {f : State → State} {Q}
    (H : (modify f : RecM Unit).SWF c₁ s Q) :
    RecM.SS c₁ c₂ s (modify f : RecM Unit) (modify f) Q :=
  fun m hm => ⟨H m hm.swf, fun _ _ _ eq _ _ => eq⟩

theorem RecM.SS.map {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {f : α → β} {Q R}
    (h1 : RecM.SS c₁ c₂ s x₁ x₂ Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R (f a) s') :
    RecM.SS c₁ c₂ s (f <$> x₁) (f <$> x₂) R := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

/-- Running `x` with the taint reset, recording the taint it ends with. -/
theorem RecM.SS.withTaint {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q : α → State → Prop}
    (h : ∀ s, RecM.SS c₁ c₂ s x₁ x₂ Q)
    (hQ : ∀ a (s₁ s₂ : State), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    RecM.SS c₁ c₂ s (TypeChecker.withTaint x₁) (TypeChecker.withTaint x₂)
      fun p s' => Q p.1 s' := by
  intro m hm
  have wf₀ {s} (wf : SuppState c₁ s) : SuppState c₁ { s with taint := 0 } :=
    wf.setAux rfl rfl rfl rfl rfl rfl
  have run {a s'} (e : TypeChecker.withTaint x₁ m c₁ s = .ok (a, s')) :
      ∃ s₁, x₁ m c₁ { s with taint := 0 } = .ok (a.1, s₁) ∧ a.2 = s₁.taint ∧
        s' = { s₁ with taint := max s.taint s₁.taint } := by
    unfold TypeChecker.withTaint at e
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, get, getThe,
      MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, Pure.pure, Except.pure,
      StateT.pure, ReaderT.pure, _root_.modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.get, MonadStateOf.get, MonadState.modifyGet] at e
    split at e <;> [cases e; skip]
    rename_i v e₁
    obtain ⟨b, s₁⟩ := v
    cases e
    exact ⟨_, e₁, rfl, rfl⟩
  refine ⟨fun wf a s' e => ?_, fun wf a s' e hF hC => ?_⟩
  · obtain ⟨s₁, e₁, -, rfl⟩ := run e
    obtain ⟨wf₁, le, mo, q⟩ := (h _ m hm).1 (wf₀ wf) _ _ e₁
    exact ⟨wf₁.setAux rfl rfl rfl rfl rfl rfl, le, ⟨Nat.le_max_left _ _, mo.scopeIds, mo.keeps⟩,
      hQ _ s₁ _ rfl q⟩
  · obtain ⟨s₁, e₁, ha, rfl⟩ := run e
    obtain ⟨-, -, mo, -⟩ := (h _ m hm).1 (wf₀ wf) _ _ e₁
    have e₂ := (h _ m hm).2 (wf₀ wf) _ _ e₁ hF (hC.withTaint mo.scopeIds)
    unfold TypeChecker.withTaint
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, get, getThe,
      MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, Pure.pure, Except.pure,
      StateT.pure, ReaderT.pure, _root_.modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.get, MonadStateOf.get, MonadState.modifyGet]
    rw [e₂]; obtain ⟨a1, a2⟩ := a; cases ha; rfl

/-- A cached result `c₂`'s ceiling lets through, `c₁`'s does too. -/
theorem State.cached?_ceil {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) {s : State}
    {o : Option Cached} {p} (h : s.cached? c₂.ceiling o = some p) :
    s.cached? c₁.ceiling o = some p := by
  unfold State.cached? at h ⊢
  split at h <;> [skip; cases h]
  rename_i r l id
  split at h <;> [skip; cases h]
  rename_i hv
  simp only [Bool.and_eq_true] at hv
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hv.1, hA.ceiling l hv.2⟩)]; exact h

/-- A cached result `c₁` uses and `c₂` does not is beyond `c₂`'s ceiling. -/
theorem State.cached?_blocked {c₁ c₂ : Option Nat} {s : State} {o : Option Cached} {r l}
    (h₁ : s.cached? c₁ o = some (r, l)) (h₂ : s.cached? c₂ o = none) :
    ∃ lab, c₂ = some lab ∧ lab < l := by
  unfold State.cached? at h₁ h₂
  split at h₁ <;> [skip; cases h₁]
  rename_i r' l' id
  simp only at h₂
  split at h₁ <;> [skip; cases h₁]
  cases h₁
  rename_i hv
  split at h₂ <;> [cases h₂; skip]
  rename_i hn
  simp only [Bool.and_eq_true] at hv hn
  cases c₂ with
  | none => simp at hn; simp [hn] at hv
  | some lab => exact ⟨lab, rfl, by simp at hn; have := hn hv.1; omega⟩

/-- A computation that, wherever it succeeds in `c₁`, ends with a taint beyond `c₂`'s ceiling
simulates anything in `c₂`. -/
theorem RecM.SS.blocked {c₁ c₂ : Context} {s : State} {x₁ x₂ x₃ : RecM α} {Q} {lab l : Nat}
    (hc : c₂.ceiling = some lab) (hl : lab < l) (hw : RecM.SS c₁ c₂ s x₁ x₃ Q)
    (ht : x₁.SWF c₁ s fun _ s' => l ≤ s'.taint) : RecM.SS c₁ c₂ s x₁ x₂ Q :=
  fun m hm => ⟨(hw m hm).1, fun wf a s' e _ hC => by
    have h1 := (ht m hm.swf wf a s' e).2.2.2
    have h2 := (hC lab hc).1
    omega⟩

/-- A cache lookup, where `c₁` and `c₂` may set aside different results. `F₁`'s hits must raise
the taint to the hit's level. -/
theorem RecM.SS.cached {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) {s : State}
    {o : Option Cached} {F₁ F₂ : Option (Expr × Nat) → RecM α} {Q}
    (hsome : ∀ r l, s.cached? c₁.ceiling o = some (r, l) →
      RecM.SS c₁ c₂ s (F₁ (some (r, l))) (F₂ (some (r, l))) Q)
    (hlow : ∀ r l, (F₁ (some (r, l))).SWF c₁ s fun _ s' => l ≤ s'.taint)
    (hnone : s.cached? c₁.ceiling o = none → RecM.SS c₁ c₂ s (F₁ none) (F₂ none) Q) :
    RecM.SS c₁ c₂ s (F₁ (s.cached? c₁.ceiling o)) (F₂ (s.cached? c₂.ceiling o)) Q := by
  cases h₁ : s.cached? c₁.ceiling o with
  | none =>
    cases h₂ : s.cached? c₂.ceiling o with
    | none => exact hnone h₁
    | some p => cases (State.cached?_ceil hA h₂).symm.trans h₁
  | some p =>
    obtain ⟨r, l⟩ := p
    cases h₂ : s.cached? c₂.ceiling o with
    | none =>
      obtain ⟨lab, hc, hl⟩ := State.cached?_blocked h₁ h₂
      exact .blocked hc hl (hsome r l h₁) (hlow r l)
    | some p =>
      cases (State.cached?_ceil hA h₂).symm.trans h₁
      exact hsome r l h₁

/-- `RecM.SS.cached`, in the shape a cache lookup takes in the type checker. -/
theorem RecM.SS.cached' {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) {s : State}
    {o : Option Cached} {hit₁ hit₂ : Expr → Nat → RecM α} {miss₁ miss₂ : RecM α} {Q}
    (hsome : ∀ r l, s.cached? c₁.ceiling o = some (r, l) →
      RecM.SS c₁ c₂ s (hit₁ r l) (hit₂ r l) Q)
    (hlow : ∀ r l, (hit₁ r l).SWF c₁ s fun _ s' => l ≤ s'.taint)
    (hnone : s.cached? c₁.ceiling o = none → RecM.SS c₁ c₂ s miss₁ miss₂ Q) :
    RecM.SS c₁ c₂ s
      (match s.cached? c₁.ceiling o with | some (r, l) => hit₁ r l | _ => miss₁)
      (match s.cached? c₂.ceiling o with | some (r, l) => hit₂ r l | _ => miss₂) Q :=
  RecM.SS.cached (F₁ := fun x => match x with | some (r, l) => hit₁ r l | _ => miss₁)
    (F₂ := fun x => match x with | some (r, l) => hit₂ r l | _ => miss₂) hA hsome hlow hnone

/-- A use of a fact at level `l`, gated by the ceiling, where `c₁` and `c₂` may have different
ceilings. The use must raise the taint to `l`. -/
theorem RecM.SS.ceilIf {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) {s : State} {l : Nat}
    {hit₁ hit₂ miss₁ miss₂ : RecM α} {Q}
    (hhit : c₁.ceiling.all (l ≤ ·) → RecM.SS c₁ c₂ s hit₁ hit₂ Q)
    (hlow : hit₁.SWF c₁ s fun _ s' => l ≤ s'.taint)
    (hmiss : RecM.SS c₁ c₂ s miss₁ miss₂ Q) :
    RecM.SS c₁ c₂ s (if c₁.ceiling.all (l ≤ ·) then hit₁ else miss₁)
      (if c₂.ceiling.all (l ≤ ·) then hit₂ else miss₂) Q := by
  by_cases h₂ : c₂.ceiling.all (l ≤ ·)
  · rw [if_pos (hA.ceiling l h₂), if_pos h₂]; exact hhit (hA.ceiling l h₂)
  · rw [if_neg h₂]
    by_cases h₁ : c₁.ceiling.all (l ≤ ·)
    · rw [if_pos h₁]
      cases hc : c₂.ceiling with
      | none => simp [hc] at h₂
      | some lab =>
        rw [hc] at h₂; simp at h₂
        exact .blocked hc h₂ (hhit h₁) hlow
    · rw [if_neg h₁]; exact hmiss

theorem RecM.SS.taintWith {c₁ c₂ : Context} {s : State} :
    RecM.SS c₁ c₂ s (_root_.modify (·.taintWith l) : RecM Unit)
      (_root_.modify (·.taintWith l)) fun _ _ => True :=
  RecM.SS.modify RecM.SWF.taintWith

theorem LocalDecl.erase_cdecl : (LocalDecl.cdecl i fv n t bi k).erase = .cdecl 0 fv n t bi k := rfl

theorem FreshFor.fresh {c₁ c₂ : Context} {s : State} {g : NameGenerator} (H : FreshFor c₁ c₂ g)
    (hg : s.ngen.next ≤ g) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none) :
    c₂.lctx.find? ⟨s.ngen.curr⟩ = none := by
  cases h : c₂.lctx.find? ⟨s.ngen.curr⟩; · rfl
  rcases H ⟨s.ngen.curr⟩ (by simp [LocalContext.Dom, h]) with h' | h'
  · simp [LocalContext.Dom, f₁] at h'
  · exact absurd (NameGenerator.next_reserves_self.mono hg) h'

theorem Agree.mkLocalDecl {S : Supp} {c₁ c₂ : Context} {s : State} (H : Agree S c₁ c₂)
    (wf : SuppState c₁ s) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none)
    (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none) {name ty bi} :
    Agree (S.addFVars [⟨s.ngen.curr⟩])
      { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } := by
  have E := wf.ctxExt f₁ (name := name) (ty := ty) (bi := bi)
  refine { H with lctx := fun y hy => ?_, wf := H.wf.mkLocalDecl f₂ }
  · dsimp only
    rw [LocalContext.find?_mkLocalDecl H.wf f₂, LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh]
    split
    · rfl
    · rename_i h
      exact H.lctx y (hy.resolve_right fun h' => h (by simp at h'; simp [h']))

theorem FreshFor.mkLocalDecl {c₁ c₂ : Context} {s : State} {g : NameGenerator}
    (H : FreshFor c₁ c₂ g) (wf : SuppState c₁ s) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none)
    (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none)
    (hc₂ : c₂.lctx.WF) {name ty bi} :
    FreshFor { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } g := by
  have E := wf.ctxExt f₁ (name := name) (ty := ty) (bi := bi)
  intro y hy
  unfold LocalContext.Dom at hy; dsimp only at hy
  rw [LocalContext.find?_mkLocalDecl hc₂ f₂] at hy
  split at hy
  · rename_i h; simp at h; subst h; exact .inl E.dom
  · exact (H y hy).imp_left E.dom_of

theorem Agree.mkLetDecl {S : Supp} {c₁ c₂ : Context} {s : State} (H : Agree S c₁ c₂)
    (wf : SuppState c₁ s) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none)
    (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none) {name ty val} :
    Agree (S.addFVars [⟨s.ngen.curr⟩])
      { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val } := by
  have E := wf.ctxExtLet f₁ (name := name) (ty := ty) (val := val)
  refine { H with lctx := fun y hy => ?_, wf := H.wf.mkLetDecl f₂ }
  · dsimp only
    rw [LocalContext.find?_mkLetDecl H.wf f₂, LocalContext.find?_mkLetDecl wf.lctxWF E.fresh]
    split
    · rfl
    · rename_i h
      exact H.lctx y (hy.resolve_right fun h' => h (by simp at h'; simp [h']))

theorem FreshFor.mkLetDecl {c₁ c₂ : Context} {s : State} {g : NameGenerator}
    (H : FreshFor c₁ c₂ g) (wf : SuppState c₁ s) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none)
    (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none)
    (hc₂ : c₂.lctx.WF) {name ty val} :
    FreshFor { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val } g := by
  have E := wf.ctxExtLet f₁ (name := name) (ty := ty) (val := val)
  intro y hy
  unfold LocalContext.Dom at hy; dsimp only at hy
  rw [LocalContext.find?_mkLetDecl hc₂ f₂] at hy
  split at hy
  · rename_i h; simp at h; subst h; exact .inl E.dom
  · exact (H y hy).imp_left E.dom_of

theorem RecM.SS.withLocalDecl {c₁ c₂ : Context} {s : State} {f₁ f₂ : Expr → RecM α}
    {Q name ty bi} (hty : Dom c₁ ty)
    (H₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none →
      RecM.SS { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      s.enter (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₁ (.fvar ⟨s.ngen.curr⟩)) Q)
    (H : c₁.lctx.find? ⟨s.ngen.curr⟩ = none → c₂.lctx.find? ⟨s.ngen.curr⟩ = none →
      RecM.SS { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      s.enter (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₂ (.fvar ⟨s.ngen.curr⟩)) Q)
    (hc₂ : c₂.lctx.WF)
    (hQ : ∀ a (s₁ s₂ : State), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    RecM.SS c₁ c₂ s (withLocalDecl name bi ty f₁) (withLocalDecl name bi ty f₂) Q := by
  intro m hm
  have enter (wf : SuppState c₁ s) (hf : c₁.lctx.find? ⟨s.ngen.curr⟩ = none) := by
    have hE := wf.ctxExt hf (name := name) (ty := ty) (bi := bi)
    exact And.intro hE <| wf.enter rfl hE (wf.lctxWF.mkLocalDecl hE.fresh) fun d hd => by
      simp [LocalContext.find?_mkLocalDecl wf.lctxWF hE.fresh] at hd; subst hd
      exact ⟨hty, by simp [LocalDecl.value', Expr.fvarsList, hE.dom]⟩
  refine ⟨fun wf a s' e => ?_, fun wf a s' e hF hC => ?_⟩
  · obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
    have ⟨hE, wf₁⟩ := enter wf hfresh
    obtain ⟨wf₂, hle, mo, hQ'⟩ := (H₁ hfresh m hm).1 wf₁ a _ e₁
    refine ⟨wf.restore hE wf₂ (NameGenerator.next_reserves_self.mono hle), NameGenerator.LE.next.trans hle,
      ⟨Nat.le_max_left _ _, rfl, (Keeps.next hfresh).trans (mo.keeps.of_dom fun fv h => ?_)⟩,
      hQ _ s₁ _ rfl hQ'⟩
    exact hE.dom_of h
  · obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
    obtain ⟨-, hle, -, -⟩ := (H₁ hfresh m hm).1 (enter wf hfresh).2 a _ e₁
    have f₂ := hF.fresh hle hfresh
    exact withFreshId_ok f₂ ((H hfresh f₂ m hm).2 (enter wf hfresh).2 a _ e₁
      (hF.mkLocalDecl wf hfresh f₂ hc₂)
      (hC.enter rfl))

theorem RecM.SS.withLetDecl {c₁ c₂ : Context} {s : State} {f₁ f₂ : Expr → RecM α}
    {Q name ty val} (hty : Dom c₁ ty) (hval : Dom c₁ val)
    (H₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none →
      RecM.SS { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      s.enter (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₁ (.fvar ⟨s.ngen.curr⟩)) Q)
    (H : c₁.lctx.find? ⟨s.ngen.curr⟩ = none → c₂.lctx.find? ⟨s.ngen.curr⟩ = none →
      RecM.SS { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      s.enter (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₂ (.fvar ⟨s.ngen.curr⟩)) Q)
    (hc₂ : c₂.lctx.WF)
    (hQ : ∀ a (s₁ s₂ : State), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    RecM.SS c₁ c₂ s (withLetDecl name ty val f₁) (withLetDecl name ty val f₂) Q := by
  intro m hm
  have enter (wf : SuppState c₁ s) (hf : c₁.lctx.find? ⟨s.ngen.curr⟩ = none) := by
    have hE := wf.ctxExtLet hf (name := name) (ty := ty) (val := val)
    exact And.intro hE <| wf.enter rfl hE (wf.lctxWF.mkLetDecl hE.fresh) fun d hd => by
      simp [LocalContext.find?_mkLetDecl wf.lctxWF hE.fresh] at hd; subst hd
      exact ⟨hty, fun y hy => hE.dom_of (hval y hy)⟩
  refine ⟨fun wf a s' e => ?_, fun wf a s' e hF hC => ?_⟩
  · obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
    have ⟨hE, wf₁⟩ := enter wf hfresh
    obtain ⟨wf₂, hle, mo, hQ'⟩ := (H₁ hfresh m hm).1 wf₁ a _ e₁
    refine ⟨wf.restore hE wf₂ (NameGenerator.next_reserves_self.mono hle), NameGenerator.LE.next.trans hle,
      ⟨Nat.le_max_left _ _, rfl, (Keeps.next hfresh).trans (mo.keeps.of_dom fun fv h => ?_)⟩,
      hQ _ s₁ _ rfl hQ'⟩
    exact hE.dom_of h
  · obtain ⟨hfresh, s₁, e₁, rfl⟩ := withFreshId_run e
    obtain ⟨-, hle, -, -⟩ := (H₁ hfresh m hm).1 (enter wf hfresh).2 a _ e₁
    have f₂ := hF.fresh hle hfresh
    exact withFreshId_ok f₂ ((H hfresh f₂ m hm).2 (enter wf hfresh).2 a _ e₁
      (hF.mkLetDecl wf hfresh f₂ hc₂)
      (hC.enter rfl))

theorem RecM.SS.withEagerReduce {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q}
    (H : RecM.SS { c₁ with eagerReduce := true } { c₂ with eagerReduce := true } s x₁ x₂ Q) :
    RecM.SS c₁ c₂ s (withTheReader Context (fun c => { c with eagerReduce := true }) x₁)
      (withTheReader Context (fun c => { c with eagerReduce := true }) x₂) Q :=
  fun m hm => ⟨fun wf a s' e =>
      let ⟨h1, h2, h3⟩ := (H m hm).1 { wf with } a s' e
      ⟨{ h1 with }, h2, h3⟩,
    fun wf a s' e hF => (H m hm).2 { wf with } a s' e hF⟩

theorem Agree.eagerReduce' {S : Supp} {c₁ c₂ : Context} (H : Agree S c₁ c₂) :
    Agree S { c₁ with eagerReduce := true } { c₂ with eagerReduce := true } :=
  { H with eagerReduce := rfl }

theorem RecM.SS.forIn {c₁ c₂ : Context} {f₁ f₂ : α → β → RecM (ForInStep β)} {Inv : β → Prop}
    (H : ∀ v b s, Inv b →
      RecM.SS c₁ c₂ s (f₁ v b) (f₂ v b) fun r _ => ∃ b', r = .yield b' ∧ Inv b') :
    ∀ {vs : List α} {b : β} {s : State}, Inv b →
      RecM.SS c₁ c₂ s (ForIn.forIn vs b f₁) (ForIn.forIn vs b f₂) fun b' _ => Inv b'
  | [], _, _, h => .pure h
  | v :: vs, b, s, h => by
    rw [List.forIn_cons, List.forIn_cons]
    refine (H v b s h).bind fun r s' _ hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact RecM.SS.forIn H hinv

theorem RecM.SS.forIn_range {c₁ c₂ : Context} {f₁ f₂ : Nat → β → RecM (ForInStep β)}
    {Inv : β → Prop}
    (H : ∀ v b s, Inv b →
      RecM.SS c₁ c₂ s (f₁ v b) (f₂ v b) fun r _ => ∃ b', r = .yield b' ∧ Inv b')
    {n : Nat} {b : β} {s : State} (h : Inv b) :
    RecM.SS c₁ c₂ s (ForIn.forIn [:n] b f₁) (ForIn.forIn [:n] b f₂) fun b' _ => Inv b' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact RecM.SS.forIn H h

theorem RecM.SS.forIn'_list {c₁ c₂ : Context} {Inv : β → Prop} :
    ∀ {l : List α} {f₁ f₂ : (a : α) → a ∈ l → β → RecM (ForInStep β)},
    (∀ a h b s, Inv b → RecM.SS c₁ c₂ s (f₁ a h b) (f₂ a h b) fun r _ => Inv r.value) →
    ∀ {b : β} {s : State}, Inv b →
      RecM.SS c₁ c₂ s (ForIn'.forIn' l b f₁) (ForIn'.forIn' l b f₂) fun b' _ => Inv b'
  | [], _, _, _, _, _, h => .pure h
  | a :: l, f₁, f₂, H, b, s, h => by
    rw [List.forIn'_cons, List.forIn'_cons]
    refine (H a (.head _) b s h).bind fun r s' _ hr => ?_
    cases r with
    | done b' => exact .pure hr
    | yield b' => exact RecM.SS.forIn'_list (fun a h' b s => H a (.tail _ h') b s) hr

theorem RecM.SS.forIn'_range {c₁ c₂ : Context} {Inv : β → Prop} {n m : Nat}
    {f₁ f₂ : (a : Nat) → a ∈ [n:m] → β → RecM (ForInStep β)}
    (H : ∀ a h b s, Inv b → RecM.SS c₁ c₂ s (f₁ a h b) (f₂ a h b) fun r _ => Inv r.value)
    {b : β} {s : State} (h : Inv b) :
    RecM.SS c₁ c₂ s (ForIn'.forIn' [n:m] b f₁) (ForIn'.forIn' [n:m] b f₂)
      fun b' _ => Inv b' := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact RecM.SS.forIn'_list (fun a h' b s => H a _ b s) h

theorem RecM.SS.failBind {c₁ c₂ : Context} {s : State} {g : LocalContext → Exception}
    {f : α → RecM β} {x₂ : RecM β} {Q} :
    RecM.SS c₁ c₂ s ((Lean.getLCtx >>= fun l => (MonadExcept.throw (g l) : RecM α)) >>= f)
      x₂ Q :=
  .fail RecM.SWF.failBind

theorem RecM.SS.toLBoolM {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM Bool}
    (H : RecM.SS c₁ c₂ s x₁ x₂ fun _ _ => True) :
    RecM.SS c₁ c₂ s (toLBoolM x₁) (toLBoolM x₂) fun _ _ => True :=
  H.bind fun _ _ _ _ => .pure trivial

theorem RecM.SS.orM {c₁ c₂ : Context} {s : State} {x₁ x₂ y₁ y₂ : RecM Bool}
    (hx : RecM.SS c₁ c₂ s x₁ x₂ fun _ _ => True)
    (hy : ∀ s, RecM.SS c₁ c₂ s y₁ y₂ fun _ _ => True) :
    RecM.SS c₁ c₂ s (x₁ <||> y₁) (x₂ <||> y₂) fun _ _ => True := by
  simp only [(· <||> ·), _root_.orM]
  refine hx.bind fun _ _ _ _ => ?_
  split
  · exact .pure trivial
  · exact hy _

end TypeChecker
end Lean4Lean

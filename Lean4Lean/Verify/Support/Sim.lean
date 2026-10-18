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

/-- A local declaration without its position in the context, which the type checker never reads. -/
def _root_.Lean.LocalDecl.erase : LocalDecl → LocalDecl
  | .cdecl _ fv n t bi k => .cdecl 0 fv n t bi k
  | .ldecl _ fv n t v nd k => .ldecl 0 fv n t v nd k

namespace TypeChecker

/-- `c₂` agrees with `c₁` on what `S` allows: the same declarations of its constants and free
variables, up to their position in the local context, and the same settings. `c₂` declares no
free variable `c₁` does not, so a variable fresh for `c₁` is fresh for `c₂`. -/
structure Agree (S : Supp) (c₁ c₂ : Context) : Prop where
  env : ∀ n, S.const n → c₂.env.find? n = c₁.env.find? n
  lctx : ∀ fv, S.fv fv →
    (c₂.lctx.find? fv).map LocalDecl.erase = (c₁.lctx.find? fv).map LocalDecl.erase
  wf : c₂.lctx.WF
  dom : ∀ fv, c₂.lctx.Dom fv → c₁.lctx.Dom fv
  quotInit : c₂.env.quotInit = c₁.env.quotInit
  safety : c₂.safety = c₁.safety
  eagerReduce : c₂.eagerReduce = c₁.eagerReduce
  lparams : ∀ n, S.lvl n → n ∈ c₁.lparams → n ∈ c₂.lparams
  fuel : c₂.fuel = c₁.fuel

theorem Agree.refl {S : Supp} {c : Context} (wf : c.lctx.WF) : Agree S c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, wf, fun _ => id, rfl, rfl, rfl, fun _ _ => id, rfl⟩

theorem Agree.mono {S S' : Supp} {c₁ c₂ : Context} (H : Agree S' c₁ c₂) (h : S ≤ S') :
    Agree S c₁ c₂ :=
  { H with
    env := fun n hn => H.env n (h.const n hn)
    lctx := fun fv hfv => H.lctx fv (h.fv fv hfv)
    lparams := fun n hn => H.lparams n (h.lvl n hn) }

/-- A successful run of `x₁` in `c₁` is a successful run of `x₂` in `c₂`, from the same state. -/
def M.Sim (c₁ c₂ : Context) (s : State) (x₁ x₂ : M α) : Prop :=
  SuppState c₁ s → ∀ a s', x₁ c₁ s = .ok (a, s') → x₂ c₂ s = .ok (a, s')

/-- `x₁` is `M.SWF` in `c₁`, and `x₂` runs in `c₂` as `x₁` does in `c₁`. -/
def M.SS (c₁ c₂ : Context) (s : State) (x₁ x₂ : M α) (Q : α → State → Prop) : Prop :=
  x₁.SWF c₁ s Q ∧ M.Sim c₁ c₂ s x₁ x₂

theorem M.Sim.bind {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {f₁ f₂ : α → M β} {Q}
    (h1 : M.Sim c₁ c₂ s x₁ x₂) (hw : x₁.SWF c₁ s Q)
    (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → M.Sim c₁ c₂ s' (f₁ a) (f₂ a)) :
    M.Sim c₁ c₂ s (x₁ >>= f₁) (x₂ >>= f₂) := by
  intro wf b s₂
  simp only [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨wf', le, hq⟩ := hw wf _ _ eq
  rw [h1 wf _ _ eq]
  exact h2 _ _ le hq wf' _ _ h

theorem M.SS.bind {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {f₁ f₂ : α → M β} {Q R}
    (h1 : M.SS c₁ c₂ s x₁ x₂ Q)
    (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → M.SS c₁ c₂ s' (f₁ a) (f₂ a) R) :
    M.SS c₁ c₂ s (x₁ >>= f₁) (x₂ >>= f₂) R :=
  ⟨h1.1.bind fun a s' le h => (h2 a s' le h).1,
    h1.2.bind h1.1 fun a s' le h => (h2 a s' le h).2⟩

theorem M.SS.pure {c₁ c₂ : Context} {s : State} {Q} (H : Q a s) :
    M.SS c₁ c₂ s (pure a : M α) (pure a) Q :=
  ⟨.pure H, fun _ _ _ h => h⟩

theorem M.SS.mono {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α} {Q R}
    (h1 : M.SS c₁ c₂ s x₁ x₂ Q) (h2 : ∀ a s', s.ngen ≤ s'.ngen → Q a s' → R a s') :
    M.SS c₁ c₂ s x₁ x₂ R := ⟨h1.1.mono h2, h1.2⟩

/-- A computation that never succeeds in `c₁` simulates anything. -/
theorem M.Sim.fail {c₁ c₂ : Context} {s : State} {x₁ x₂ : M α}
    (h : x₁.SWF c₁ s fun _ _ => False) : M.Sim c₁ c₂ s x₁ x₂ :=
  fun wf a s' eq => (h wf a s' eq).2.2.elim

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
  refine fun _ _ => ⟨.liftExcept hw, fun _ a s' eq => ?_⟩
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
  fun m hm => ⟨H m hm.swf, fun _ _ _ eq => eq⟩

theorem LocalDecl.erase_cdecl : (LocalDecl.cdecl i fv n t bi k).erase = .cdecl 0 fv n t bi k := rfl

theorem Agree.fresh {S : Supp} {c₁ c₂ : Context} {s : State} (H : Agree S c₁ c₂)
    (wf : SuppState c₁ s) : c₂.lctx.find? ⟨s.ngen.curr⟩ = none := by
  cases h : c₂.lctx.find? ⟨s.ngen.curr⟩; · rfl
  exact absurd (wf.reserves _ (H.dom _ (by simp [LocalContext.Dom, h])))
    NameGenerator.not_reserves_self

theorem Agree.mkLocalDecl {S : Supp} {c₁ c₂ : Context} {s : State} (H : Agree S c₁ c₂)
    (wf : SuppState c₁ s) {name ty bi} :
    Agree (S.addFVars [⟨s.ngen.curr⟩])
      { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } := by
  have E := wf.ctxExt (name := name) (ty := ty) (bi := bi)
  have f₂ := H.fresh wf
  refine { H with lctx := fun y hy => ?_, wf := H.wf.mkLocalDecl f₂, dom := fun y hy => ?_ }
  · dsimp only
    rw [LocalContext.find?_mkLocalDecl H.wf f₂, LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh]
    split
    · rfl
    · rename_i h
      exact H.lctx y (hy.resolve_right fun h' => h (by simp at h'; simp [h']))
  · unfold LocalContext.Dom at hy; dsimp only at hy
    rw [LocalContext.find?_mkLocalDecl H.wf f₂] at hy
    split at hy
    · rename_i h; simp at h; subst h; exact E.dom
    · exact E.dom_of (H.dom y hy)

theorem Agree.mkLetDecl {S : Supp} {c₁ c₂ : Context} {s : State} (H : Agree S c₁ c₂)
    (wf : SuppState c₁ s) {name ty val} :
    Agree (S.addFVars [⟨s.ngen.curr⟩])
      { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val } := by
  have E := wf.ctxExtLet (name := name) (ty := ty) (val := val)
  have f₂ := H.fresh wf
  refine { H with lctx := fun y hy => ?_, wf := H.wf.mkLetDecl f₂, dom := fun y hy => ?_ }
  · dsimp only
    rw [LocalContext.find?_mkLetDecl H.wf f₂, LocalContext.find?_mkLetDecl wf.lctxWF E.fresh]
    split
    · rfl
    · rename_i h
      exact H.lctx y (hy.resolve_right fun h' => h (by simp at h'; simp [h']))
  · unfold LocalContext.Dom at hy; dsimp only at hy
    rw [LocalContext.find?_mkLetDecl H.wf f₂] at hy
    split at hy
    · rename_i h; simp at h; subst h; exact E.dom
    · exact E.dom_of (H.dom y hy)

theorem RecM.SS.withLocalDecl {c₁ c₂ : Context} {s : State} {f₁ f₂ : Expr → RecM α}
    {Q name ty bi} (hty : Dom c₁ ty)
    (H : RecM.SS { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { s with ngen := s.ngen.next } (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₂ (.fvar ⟨s.ngen.curr⟩)) Q) :
    RecM.SS c₁ c₂ s (withLocalDecl name bi ty f₁) (withLocalDecl name bi ty f₂) Q := by
  intro m hm
  have enter (wf : SuppState c₁ s) := by
    have hE := wf.ctxExt (name := name) (ty := ty) (bi := bi)
    exact And.intro hE <| wf.enter rfl hE (wf.lctxWF.mkLocalDecl hE.fresh) fun d hd => by
      simp [LocalContext.find?_mkLocalDecl wf.lctxWF hE.fresh] at hd; subst hd
      exact ⟨hty, by simp [LocalDecl.value', Expr.fvarsList, hE.dom]⟩
  refine ⟨fun wf a s' e => ?_, fun wf a s' e => (H m hm).2 (enter wf).2 a s' e⟩
  have ⟨hE, wf₁⟩ := enter wf
  obtain ⟨wf₂, hle, hQ⟩ := (H m hm).1 wf₁ a s' e
  exact ⟨wf.exit hE wf₂ (NameGenerator.LE.next.trans hle), NameGenerator.LE.next.trans hle, hQ⟩

theorem RecM.SS.withLetDecl {c₁ c₂ : Context} {s : State} {f₁ f₂ : Expr → RecM α}
    {Q name ty val} (hty : Dom c₁ ty) (hval : Dom c₁ val)
    (H : RecM.SS { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { s with ngen := s.ngen.next } (f₁ (.fvar ⟨s.ngen.curr⟩)) (f₂ (.fvar ⟨s.ngen.curr⟩)) Q) :
    RecM.SS c₁ c₂ s (withLetDecl name ty val f₁) (withLetDecl name ty val f₂) Q := by
  intro m hm
  have enter (wf : SuppState c₁ s) := by
    have hE := wf.ctxExtLet (name := name) (ty := ty) (val := val)
    exact And.intro hE <| wf.enter rfl hE (wf.lctxWF.mkLetDecl hE.fresh) fun d hd => by
      simp [LocalContext.find?_mkLetDecl wf.lctxWF hE.fresh] at hd; subst hd
      exact ⟨hty, fun y hy => hE.dom_of (hval y hy)⟩
  refine ⟨fun wf a s' e => ?_, fun wf a s' e => (H m hm).2 (enter wf).2 a s' e⟩
  have ⟨hE, wf₁⟩ := enter wf
  obtain ⟨wf₂, hle, hQ⟩ := (H m hm).1 wf₁ a s' e
  exact ⟨wf.exit hE wf₂ (NameGenerator.LE.next.trans hle), NameGenerator.LE.next.trans hle, hQ⟩

theorem RecM.SS.withEagerReduce {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q}
    (H : RecM.SS { c₁ with eagerReduce := true } { c₂ with eagerReduce := true } s x₁ x₂ Q) :
    RecM.SS c₁ c₂ s (withTheReader Context (fun c => { c with eagerReduce := true }) x₁)
      (withTheReader Context (fun c => { c with eagerReduce := true }) x₂) Q :=
  fun m hm => ⟨fun wf a s' e =>
      let ⟨h1, h2, h3⟩ := (H m hm).1 { wf with } a s' e
      ⟨{ h1 with }, h2, h3⟩,
    fun wf a s' e => (H m hm).2 { wf with } a s' e⟩

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

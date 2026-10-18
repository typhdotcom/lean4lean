import Lean4Lean.Verify.Support.Monad

/-!
# The type checker's outputs mention only what its inputs, context and environment do

Each function of the type checker satisfies `M.SWF`/`RecM.SWF` with a postcondition saying that
whatever a closed `S` allows in its input, it allows in its output (`SuppBelow`). The proofs follow
the functions; they need no typing, so they cover the functions whose typing is not yet verified.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem _root_.Lean.Level.lparamsIn_true {l : Level} : l.LParamsIn fun _ => True := by
  induction l <;> simp_all [Level.LParamsIn]

theorem _root_.Lean.Expr.suppIn_fvars {P : FVarId → Prop} {e : Expr} :
    e.SuppIn ⟨P, fun _ => True, fun _ => True⟩ ↔ ∀ fv ∈ e.fvarsList, P fv := by
  induction e <;> simp_all [Expr.SuppIn, Expr.fvarsList, Level.lparamsIn_true, Literal.SuppIn]
  all_goals grind

/-- The free variables of the current local context, any level parameter, any constant. -/
abbrev Supp.dom (c : TypeChecker.Context) : Supp := ⟨c.lctx.Dom, fun _ => True, fun _ => True⟩

theorem SuppState.closedDom {c : TypeChecker.Context} {s : TypeChecker.State}
    (wf : SuppState c s) : (Supp.dom c).Closed c := by
  refine ⟨fun fv d _ h => ?_, ⟨fun n ci h _ => wf.envClosed n ci h, fun _ _ _ => ⟨⟨⟩, ⟨⟩, ⟨⟩⟩,
    fun _ _ _ => ⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩⟩
  have := wf.wellScoped fv d h
  exact ⟨Expr.suppIn_fvars.2 this.1, Expr.suppIn_fvars.2 this.2⟩

namespace TypeChecker

/-- Every free variable of `e` is declared in the current local context. -/
abbrev Dom (c : Context) (e : Expr) : Prop := ∀ fv ∈ e.fvarsList, c.lctx.Dom fv

theorem SuppBelow.dom {c : Context} {s : State} (wf : SuppState c s) {e e₁ : Expr}
    (h : SuppBelow c e e₁) (he : Dom c e) : Dom c e₁ :=
  Expr.suppIn_fvars.1 (h _ wf.closedDom (Expr.suppIn_fvars.2 he))

theorem CondSupp.of {c : Context} {s : State} (wf : SuppState c s) {e r : Expr} (he : Dom c e)
    (H : SuppBelow c e r) : CondSupp c s.ngen e r :=
  ⟨fun fv h => wf.reserves fv (he fv h), fun S hS _ h => H S hS h⟩

theorem CondSupp.eqv {c : Context} {ngen : NameGenerator} {e e' r : Expr}
    (h : CondSupp c ngen e r) (eq : e == e') : CondSupp c ngen e' r := by
  have sub {e₁ e₂ : Expr} (eq : e₁ == e₂) : ∀ fv ∈ e₂.fvarsList, fv ∈ e₁.fvarsList :=
    Expr.suppIn_fvars.1 <| Expr.SuppIn.eqv eq <| Expr.suppIn_fvars.2 fun _ => id
  have eq' : e' == e := BEq.symm eq
  refine ⟨fun fv hfv => h.1 fv (sub eq fv hfv), fun S hS hd he => ?_⟩
  exact h.2 S hS (fun fv hfv => hd fv (sub eq' fv hfv)) (Expr.SuppIn.eqv_rev eq he)

theorem CondSupp.insert {c : Context} {ngen : NameGenerator} {m : ExprMap Expr}
    (H : ∀ e r, m[e]? = some r → CondSupp c ngen e r) {e r : Expr} (h : CondSupp c ngen e r) :
    ∀ e' r', (m.insert e r)[e']? = some r' → CondSupp c ngen e' r' := by
  intro e' r' h'
  rw [Std.HashMap.getElem?_insert] at h'; split at h'
  · cases h'; exact CondSupp.eqv h ‹_›
  · exact H _ _ h'

theorem M.SWF.stateWF {c : Context} {s : State} {x : M α} {Q}
    (H : SuppState c s → x.SWF c s Q) : x.SWF c s Q := fun wf => H wf wf

theorem RecM.SWF.stateWF {c : Context} {s : State} {x : RecM α} {Q}
    (H : SuppState c s → x.SWF c s Q) : x.SWF c s Q := fun m hm wf => H wf m hm wf

theorem M.SWF.get {c : Context} {s : State} {f : State → M α} {Q}
    (H : (f s).SWF c s Q) : (get >>= f).SWF c s Q := H

theorem RecM.SWF.get {c : Context} {s : State} {f : State → RecM α} {Q}
    (H : (f s).SWF c s Q) : (get >>= f).SWF c s Q := H

theorem RecM.SWF.getEnv {c : Context} {s : State} {f : Environment → RecM α} {Q}
    (H : (f c.env).SWF c s Q) : (liftM getEnv >>= f).SWF c s Q := H

theorem RecM.SWF.getLCtx {c : Context} {s : State} {f : LocalContext → RecM α} {Q}
    (H : (f c.lctx).SWF c s Q) : (getLCtx >>= f).SWF c s Q := H

theorem RecM.SWF.readThe {c : Context} {s : State} {f : Context → RecM α} {Q}
    (H : (f c).SWF c s Q) : (readThe Context >>= f).SWF c s Q := H

/-- Changing what the state holds besides the caches and name generator. -/
theorem RecM.SWF.modify {c : Context} {s : State} {f : State → State} {Q}
    (hf : ∀ s, SuppState c s → SuppState c (f s) ∧ s.ngen ≤ (f s).ngen) (H : Q () (f s)) :
    (modify f : RecM Unit).SWF c s Q := by
  intro _ _ wf a s' e
  cases e; exact ⟨(hf s wf).1, (hf s wf).2, H⟩

theorem RecM.SWF.failBind {c : Context} {s : State} {g : LocalContext → Exception}
    {f : α → RecM β} {Q} :
    ((Lean.getLCtx >>= fun l => (MonadExcept.throw (g l) : RecM α)) >>= f).SWF c s Q :=
  (RecM.SWF.getLCtx .throw).bind (Q := fun _ _ => False) fun _ _ _ h => h.elim

/-- A panic in the type checker returns the default value. -/
theorem RecM.SWF.panic {c : Context} {s : State} [Inhabited α] {Q} (H : Q default s) :
    (panicWithPosWithDecl modName declName line col msg : RecM α).SWF c s Q :=
  fun _ _ => M.SWF.pure H

theorem RecM.SWF.withEagerReduce {c : Context} {s : State} {x : RecM α} {Q}
    (H : RecM.SWF { c with eagerReduce := true } s x Q) :
    RecM.SWF c s (withTheReader Context (fun c => { c with eagerReduce := true }) x) Q :=
  fun m hm wf a s' e =>
    let ⟨h1, h2, h3⟩ := H m hm { wf with } a s' e
    ⟨{ h1 with }, h2, h3⟩

/-- Loop invariant rule for `for x in xs do ...` whose body always `yield`s. -/
theorem RecM.SWF.forIn {c : Context} {f : α → β → RecM (ForInStep β)} {Inv : β → Prop}
    (H : ∀ v b s, Inv b → (f v b).SWF c s fun r _ => ∃ b', r = .yield b' ∧ Inv b') :
    ∀ {vs : List α} {b : β} {s : State}, Inv b → (ForIn.forIn vs b f).SWF c s fun b' _ => Inv b'
  | [], _, _, h => .pure h
  | v :: vs, b, s, h => by
    rw [List.forIn_cons]
    refine (H v b s h).bind fun r s' _ hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact RecM.SWF.forIn H hinv

theorem RecM.SWF.forIn_range {c : Context} {f : Nat → β → RecM (ForInStep β)} {Inv : β → Prop}
    (H : ∀ v b s, Inv b → (f v b).SWF c s fun r _ => ∃ b', r = .yield b' ∧ Inv b')
    {n : Nat} {b : β} {s : State} (h : Inv b) :
    (ForIn.forIn [:n] b f).SWF c s fun b' _ => Inv b' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact RecM.SWF.forIn H h

/-- Loop invariant rule for `for h : x in xs do ...`, whose body may also `return`. -/
theorem RecM.SWF.forIn'_list {c : Context} {Inv : β → Prop} :
    ∀ {l : List α} {f : (a : α) → a ∈ l → β → RecM (ForInStep β)},
    (∀ a h b s, Inv b → (f a h b).SWF c s fun r _ => Inv r.value) →
    ∀ {b : β} {s : State}, Inv b → (ForIn'.forIn' l b f).SWF c s fun b' _ => Inv b'
  | [], _, _, _, _, h => .pure h
  | a :: l, f, H, b, s, h => by
    rw [List.forIn'_cons]
    refine (H a (.head _) b s h).bind fun r s' _ hr => ?_
    cases r with
    | done b' => exact .pure hr
    | yield b' => exact RecM.SWF.forIn'_list (fun a h' b s => H a (.tail _ h') b s) hr

theorem RecM.SWF.forIn'_range {c : Context} {Inv : β → Prop} {n m : Nat}
    {f : (a : Nat) → a ∈ [n:m] → β → RecM (ForInStep β)}
    (H : ∀ a h b s, Inv b → (f a h b).SWF c s fun r _ => Inv r.value) {b : β} {s : State}
    (h : Inv b) : (ForIn'.forIn' [n:m] b f).SWF c s fun b' _ => Inv b' := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact RecM.SWF.forIn'_list (fun a h' b s => H a _ b s) h

namespace Inner

theorem whnf.SWF {c : Context} {s : State} (he : Dom c e) :
    RecM.SWF c s (whnf e) fun e₁ _ => SuppBelow c e e₁ := fun _ hm => hm.whnf he

theorem whnfCore.SWF {c : Context} {s : State} (he : Dom c e) :
    RecM.SWF c s (whnfCore e cheapProj) fun e₁ _ => SuppBelow c e e₁ :=
  fun _ hm => hm.whnfCore he

theorem inferType.SWF {c : Context} {s : State} (he : Dom c e) :
    RecM.SWF c s (inferType e inferOnly) fun ty _ => SuppBelow c e ty :=
  fun _ hm => hm.inferType he

theorem isDefEqCore.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    RecM.SWF c s (isDefEqCore e₁ e₂) fun _ _ => True := fun _ hm => hm.isDefEqCore h₁ h₂

theorem isDefEq.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    RecM.SWF c s (isDefEq e₁ e₂) fun _ _ => True := by
  refine (isDefEqCore.SWF h₁ h₂).bind fun b _ _ _ => ?_
  simp; split
  · rintro _ _ wf _ _ ⟨⟩
    exact ⟨⟨wf.lctxWF, wf.wellScoped, wf.envClosed, wf.reserves, wf.inferTypeI, wf.inferTypeC,
      wf.whnfCore, wf.whnf, wf.unfold⟩, .rfl, trivial⟩
  · exact .pure trivial

theorem ensureSortCore.SWF {c : Context} {s : State} (he : Dom c e) :
    RecM.SWF c s (ensureSortCore e s₀) fun e₁ _ => SuppBelow c e e₁ := by
  unfold ensureSortCore
  split; · exact .pure .rfl
  refine (whnf.SWF he).bind fun e₁ _ _ h => ?_
  split; · exact .pure h
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.SWF {c : Context} {s : State} (he : Dom c e) :
    RecM.SWF c s (ensureForallCore e s₀) fun e₁ _ => SuppBelow c e e₁ := by
  unfold ensureForallCore
  split; · exact .pure .rfl
  refine (whnf.SWF he).bind fun e₁ _ _ h => ?_
  split; · exact .pure h
  exact .getEnv <| .getLCtx .throw

theorem inferFVar.SWF {c : Context} :
    (inferFVar c name).WF fun ty => SuppBelow c (.fvar name) ty := by
  simp only [inferFVar]; split <;> [refine .pure ?_; exact .throw]
  rename_i d h
  exact fun S hS hfv => (hS.1 name d hfv h).1

theorem envGet.SWF {c : Context} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem inferConstant.SWF {c : Context} :
    (inferConstant c name ls inferOnly).WF fun ty => SuppBelow c (.const name ls) ty := by
  simp only [inferConstant]
  refine envGet.SWF.bind fun ci hci => ?_
  split; · exact .throw
  rename_i hlen
  have main : SuppBelow c (.const name ls) (ci.instantiateTypeLevelParams ls) := by
    intro S hS ⟨h1, h2⟩
    have := (hS.2.find name ci hci h1).1
    refine Expr.SuppIn.instantiateLevelParams (this.noFV (F := S.fv)) h2 ?_
    simpa [ConstantInfo.levelParams] using hlen
  have tail : (forIn ls PUnit.unit fun l (_ : PUnit) => do
      checkLevel c l; pure (ForInStep.yield PUnit.unit) : Except Exception PUnit) >>=
      (fun _ => pure (ci.instantiateTypeLevelParams ls)) |>.WF
        fun ty => SuppBelow c (.const name ls) ty :=
    Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => .pure main
  repeat' split
  all_goals first
    | exact .pure main | exact tail | exact .throw

end Inner
end TypeChecker
end Lean4Lean

import Lean4Lean.Verify.Support.WHNF

/-!
# Definitional equality keeps the state's caches as `SuppState` says

The checks return only booleans; what is proved is that every expression they hand to the
type checker's methods lives in the current local context.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

theorem Dom.instRev {c : Context} {e : Expr} {arr : Array Expr} (ha : ∀ a ∈ arr, Dom c a)
    (he : Dom c e) : Dom c (e.instantiateRev arr) :=
  dom_iff.2 <| Expr.SuppIn.instantiateRev (fun a h => dom_iff.1 (ha a h)) (dom_iff.1 he)

theorem Dom.mono {c c' : Context} {fv : FVarId} (E : CtxExt c c' fv) {e : Expr} (h : Dom c e) :
    Dom c' e := fun x hx => E.dom_of (h x hx)

theorem Dom.default {c : Context} : Dom c (default : Expr) := nofun

theorem RecM.SWF.toLBoolM {c : Context} {s : State} {x : RecM Bool}
    (H : x.SWF c s fun _ _ => True) : (toLBoolM x).SWF c s fun _ _ => True :=
  H.bind fun _ _ _ _ => .pure trivial

theorem RecM.SWF.trivial {c : Context} {s : State} {x : RecM α} (H : x.SWF c s fun _ _ => True)
    {Q : α → State → Prop} (hQ : ∀ a s, Q a s) : x.SWF c s Q :=
  H.mono fun _ _ _ _ => hQ _ _

namespace Inner

theorem isDefEqLambda.SWF {c : Context} {s : State} {subst : Array Expr}
    (hsub : ∀ a ∈ subst, Dom c a) (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqLambda e₁ e₂ subst).SWF c s fun _ _ => True := by
  unfold isDefEqLambda
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
    exact isDefEq.SWF (Dom.instRev hsub h₁) (Dom.instRev hsub h₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  have hd₁ : Dom c d₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hd₂ : Dom c d₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  have hb₁ : Dom c b₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hb₂ : Dom c b₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  suffices ∀ {x s}, (∀ y, x = some y → Dom c y) → (F x).SWF c s fun _ _ => True by
    split
    · exact (RecM.SWF.pure (a := none) (Q := fun x _ => ∀ y, x = some y → Dom c y) nofun).bind
        fun _ _ _ h => this h
    · refine (isDefEq.SWF (Dom.instRev hsub hd₁) (Dom.instRev hsub hd₂)).bind fun _ _ _ _ => ?_
      split
      · exact .pure trivial
      · exact (RecM.SWF.pure (a := some (d₂.instantiateRev subst))
          (Q := fun x _ => ∀ y, x = some y → Dom c y)
          fun _ eq => by cases eq; exact Dom.instRev hsub hd₂).bind fun _ _ _ h => this h
  intro x s hx
  unfold F; split
  · extract_lets d₂'
    have hd : Dom c d₂' := by
      unfold d₂'; cases x with
      | none => exact Dom.instRev hsub hd₂
      | some y => exact hx y rfl
    refine .stateWF fun wf => .withLocalDecl hd ?_
    have E := wf.ctxExt (name := n₂) (ty := d₂') (bi := bi₂)
    refine isDefEqLambda.SWF (fun a ha => ?_) (hb₁.mono E) (hb₂.mono E)
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact (hsub a ha).mono E
    · exact fun _ h => by simp [Expr.fvarsList] at h; subst h; exact E.dom
  · refine isDefEqLambda.SWF (fun a ha => ?_) hb₁ hb₂
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact hsub a ha
    · exact Dom.default

theorem isDefEqForall.SWF {c : Context} {s : State} {subst : Array Expr}
    (hsub : ∀ a ∈ subst, Dom c a) (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqForall e₁ e₂ subst).SWF c s fun _ _ => True := by
  unfold isDefEqForall
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
    exact isDefEq.SWF (Dom.instRev hsub h₁) (Dom.instRev hsub h₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  have hd₁ : Dom c d₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hd₂ : Dom c d₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  have hb₁ : Dom c b₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hb₂ : Dom c b₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  suffices ∀ {x s}, (∀ y, x = some y → Dom c y) → (F x).SWF c s fun _ _ => True by
    split
    · exact (RecM.SWF.pure (a := none) (Q := fun x _ => ∀ y, x = some y → Dom c y) nofun).bind
        fun _ _ _ h => this h
    · refine (isDefEq.SWF (Dom.instRev hsub hd₁) (Dom.instRev hsub hd₂)).bind fun _ _ _ _ => ?_
      split
      · exact .pure trivial
      · exact (RecM.SWF.pure (a := some (d₂.instantiateRev subst))
          (Q := fun x _ => ∀ y, x = some y → Dom c y)
          fun _ eq => by cases eq; exact Dom.instRev hsub hd₂).bind fun _ _ _ h => this h
  intro x s hx
  unfold F; split
  · extract_lets d₂'
    have hd : Dom c d₂' := by
      unfold d₂'; cases x with
      | none => exact Dom.instRev hsub hd₂
      | some y => exact hx y rfl
    refine .stateWF fun wf => .withLocalDecl hd ?_
    have E := wf.ctxExt (name := n₂) (ty := d₂') (bi := bi₂)
    refine isDefEqForall.SWF (fun a ha => ?_) (hb₁.mono E) (hb₂.mono E)
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact (hsub a ha).mono E
    · exact fun _ h => by simp [Expr.fvarsList] at h; subst h; exact E.dom
  · refine isDefEqForall.SWF (fun a ha => ?_) hb₁ hb₂
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact hsub a ha
    · exact Dom.default

theorem quickIsDefEq.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (quickIsDefEq e₁ e₂ useHash).SWF c s fun _ _ => True := by
  unfold quickIsDefEq
  refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ => ?_
  · intro _ _ wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    exact ⟨{ wf with }, .rfl, trivial⟩
  split; · exact .pure trivial
  split
  · exact .toLBoolM (isDefEqLambda.SWF nofun h₁ h₂)
  · exact .toLBoolM (isDefEqForall.SWF nofun h₁ h₂)
  · exact .pure trivial
  · exact .toLBoolM (isDefEq.SWF h₁ h₂)
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial

theorem isDefEqArgs.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqArgs e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqArgs; split
  · refine (isDefEq.SWF (fun x hx => h₁ x (by simp [Expr.fvarsList, hx]))
      (fun x hx => h₂ x (by simp [Expr.fvarsList, hx]))).bind fun _ _ _ _ => ?_
    split
    · exact .pure trivial
    · exact isDefEqArgs.SWF (fun x hx => h₁ x (by simp [Expr.fvarsList, hx]))
        (fun x hx => h₂ x (by simp [Expr.fvarsList, hx]))
  all_goals exact .pure trivial

theorem tryEtaExpansionCore.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (tryEtaExpansionCore e₁ e₂).SWF c s fun _ _ => True := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure trivial]
  refine (inferType.SWF h₂).bind fun _ _ _ h => .stateWF fun wf => ?_
  refine (whnf.SWF (h.dom wf h₂)).bind fun _ _ _ h' => .stateWF fun wf => ?_
  split <;> [skip; exact .pure trivial]
  have := (h.trans h').dom wf h₂
  refine isDefEq.SWF h₁ fun x hx => ?_
  simp [Expr.fvarsList] at hx
  rcases hx with hx | hx
  · exact this x (by simp [Expr.fvarsList, hx])
  · exact h₂ x hx

theorem orM.SWF {c : Context} {s : State} {x y : RecM Bool}
    (hx : x.SWF c s fun _ _ => True) (hy : ∀ s, y.SWF c s fun _ _ => True) :
    (x <||> y).SWF c s fun _ _ => True := by
  simp only [(· <||> ·), orM]
  refine hx.bind fun _ _ _ _ => ?_
  split
  · exact .pure trivial
  · exact hy _

theorem tryEtaExpansion.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (tryEtaExpansion e₁ e₂).SWF c s fun _ _ => True :=
  orM.SWF (tryEtaExpansionCore.SWF h₁ h₂) fun _ => tryEtaExpansionCore.SWF h₂ h₁

theorem tryEtaStructCore.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (tryEtaStructCore e₁ e₂).SWF c s fun _ _ => True := by
  unfold tryEtaStructCore
  split <;> [skip; exact .pure trivial]
  refine .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  split <;> [skip; exact .pure trivial]
  split <;> [skip; exact .pure trivial]
  refine (inferType.SWF h₁).bind fun _ _ _ ht₁ => .stateWF fun wf => ?_
  refine (inferType.SWF h₂).bind fun _ _ _ ht₂ => .stateWF fun wf' => ?_
  refine (isDefEq.SWF (ht₁.dom wf h₁) (ht₂.dom wf' h₂)).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  have hargs : ∀ a ∈ e₂.getAppArgs, Dom c a := fun a ha =>
    dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 h₂) a ha)
  refine (RecM.SWF.forIn'_range (Inv := fun _ => True) (fun i hi b s _ => ?_) trivial).bind
    fun _ _ _ _ => ?_
  · dsimp only
    refine (isDefEq.SWF (show Dom c (.proj _ _ e₁) from h₁) (hargs _ (Array.getElem_mem _))).bind
      fun _ _ _ _ => ?_
    split
    · exact .pure trivial
    · exact .pure trivial
  · dsimp only; split <;> exact .pure trivial

theorem tryEtaStruct.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (tryEtaStruct e₁ e₂).SWF c s fun _ _ => True :=
  orM.SWF (tryEtaStructCore.SWF h₁ h₂) fun _ => tryEtaStructCore.SWF h₂ h₁

theorem isDefEqApp.loop.SWF {c : Context} {s : State} {tArgs sArgs : Array Expr}
    {eq : tArgs.size = sArgs.size}
    (ht : ∀ a ∈ tArgs, Dom c a) (hs : ∀ a ∈ sArgs, Dom c a) :
    (isDefEqApp.loop tArgs sArgs eq i).SWF c s fun _ _ => True := by
  unfold isDefEqApp.loop; split
  · refine (isDefEq.SWF (ht _ (Array.getElem_mem _)) (hs _ (Array.getElem_mem _))).bind
      fun _ _ _ _ => ?_
    split
    · exact isDefEqApp.loop.SWF ht hs
    · exact .pure trivial
  · exact .pure trivial
termination_by tArgs.size - i

theorem isDefEqApp.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqApp e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqApp; split <;> [skip; exact .pure trivial]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  split <;> [skip; exact .pure trivial]
  have hf {e} (h : Dom c e) : Dom c e.getAppFn := dom_iff.2 (dom_iff.1 h).getAppFn
  have ha {e} (h : Dom c e) : ∀ a ∈ e.getAppArgs, Dom c a := fun a ha =>
    dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 h) a ha)
  refine (isDefEq.SWF (hf h₁) (hf h₂)).bind fun _ _ _ _ => ?_
  split
  · exact isDefEqApp.loop.SWF (ha h₁) (ha h₂)
  · exact .pure trivial

theorem isDefEqProofIrrel.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqProofIrrel e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqProofIrrel
  refine (inferType.SWF h₁).bind fun _ _ _ ht₁ => .stateWF fun wf => ?_
  refine (isProp.SWF (ht₁.dom wf h₁)).bind fun _ _ _ _ => ?_
  split; · exact .pure trivial
  refine (inferType.SWF h₂).bind fun _ _ _ ht₂ => .stateWF fun wf' => ?_
  exact .toLBoolM (isDefEq.SWF (ht₁.dom wf h₁) (ht₂.dom wf' h₂))

theorem cacheFailure.SWF {c : Context} {s : State} :
    (cacheFailure e₁ e₂).SWF c s fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨{ wf with }, .rfl, trivial⟩

theorem tryUnfoldProjApp.SWF {c : Context} {s : State} (he : Dom c e) :
    (tryUnfoldProjApp e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.SWF he).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

/-- What `lazyDeltaReductionStep` returns lives in the current local context. -/
def _root_.Lean4Lean.TypeChecker.ReductionStatus.Dom (c : Context) : ReductionStatus → Prop
  | .continue e₁ e₂ | .unknown e₁ e₂ | .false e₁ e₂ => TypeChecker.Dom c e₁ ∧ TypeChecker.Dom c e₂
  | .true => True

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.Dom.bool {c : Context}
    (h₁ : Dom c e₁) (h₂ : Dom c e₂) : (ReductionStatus.bool e₁ e₂ b).Dom c := by
  cases b <;> [exact ⟨h₁, h₂⟩; trivial]

theorem lazyDeltaReductionStep.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (lazyDeltaReductionStep e₁ e₂).SWF c s fun r _ => r.Dom c := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_; extract_lets delta cont F1 F2
  have hdelta {s e} (he : Dom c e) : (delta e).SWF c s fun r _ => Dom c r := by
    refine unfoldDefinition.SWF.bind fun oe _ _ H => .stateWF fun wf => ?_
    have hd : Dom c oe.get! := by
      cases oe with
      | none => exact Dom.default
      | some e' => exact (H e' rfl).dom wf he
    exact (whnfCore.SWF hd).mono fun _ _ _ h => h.dom ‹_› hd
  have hcont {s e₁' e₂'} (h₁ : Dom c e₁') (h₂ : Dom c e₂') :
      (cont e₁' e₂').SWF c s fun r _ => r.Dom c :=
    (quickIsDefEq.SWF h₁ h₂).bind fun _ _ _ _ => .pure (by
      split
      · exact ⟨h₁, h₂⟩
      · trivial
      · exact ⟨h₁, h₂⟩)
  split
  · exact .pure ⟨h₁, h₂⟩
  · refine (tryUnfoldProjApp.SWF h₂).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · exact hcont h₁ ((h _ rfl).dom wf h₂)
    · exact (hdelta h₁).bind fun _ _ _ h => hcont h h₂
  · refine (tryUnfoldProjApp.SWF h₁).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · exact hcont ((h _ rfl).dom wf h₁) h₂
    · exact (hdelta h₂).bind fun _ _ _ h => hcont h₁ h
  extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta h₂).bind fun _ _ _ h => hcont h₁ h
  · exact (hdelta h₁).bind fun _ _ _ h => hcont h h₂
  have hF1 {s} : (F1 ()).SWF c s fun r _ => r.Dom c :=
    (hdelta h₁).bind fun _ _ _ a => (hdelta h₂).bind fun _ _ _ b => hcont a b
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.SWF.lift.bind fun _ _ _ _ => hF1]
  refine (isDefEqArgs.SWF h₁ h₂).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; exact cacheFailure.SWF.lift.bind fun _ _ _ _ => hF1]

theorem isNatSuccOf?_dom {c : Context} (H : isNatSuccOf? e = some e₁) (h : Dom c e) :
    Dom c e₁ := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · exact nofun
  · exact fun x hx => h x (by simp [Expr.fvarsList, hx])

theorem isDefEqOffset.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqOffset e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqOffset; split
  · exact .pure trivial
  · split <;> [skip; exact .pure trivial]
    exact .toLBoolM (isDefEqCore.SWF (isNatSuccOf?_dom ‹_› h₁) (isNatSuccOf?_dom ‹_› h₂))

theorem reduceNat.dom {c : Context} {s : State} (he : Dom c e) :
    (reduceNat e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → Dom c e₁ :=
  .stateWF fun wf => (reduceNat.SWF he).mono fun _ _ _ h e₁ eq => (h e₁ eq).dom wf he

theorem lazyDeltaReduction.loop.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (lazyDeltaReduction.loop e₁ e₂ n).SWF c s fun r _ => r.Dom c := by
  induction n generalizing s e₁ e₂ with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.SWF h₁ h₂).bind fun _ _ _ _ => ?_; split
  · exact .pure (.bool h₁ h₂)
  suffices hF1 : ∀ {s}, (F1 ⟨⟩).SWF c s fun r _ => r.Dom c by
    refine .readThe ?_; split <;> [skip; exact hF1]
    refine (reduceNat.dom h₁).bind fun _ _ _ h => ?_; split
    · have a := h _ rfl
      exact (isDefEqCore.SWF a h₂).bind fun _ _ _ _ => .pure (.bool a h₂)
    refine (reduceNat.dom h₂).bind fun _ _ _ h => ?_; split
    · have a := h _ rfl
      exact (isDefEqCore.SWF h₁ a).bind fun _ _ _ _ => .pure (.bool h₁ a)
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (M.SWF.liftExcept reduceNative.SWF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h; skip]
  refine (M.SWF.liftExcept reduceNative.SWF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h; skip]
  refine (lazyDeltaReductionStep.SWF h₁ h₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» => exact ih h.1 h.2
  | _ => exact .pure h

theorem lazyDeltaProjReduction.finish.SWF {c : Context} {s : State}
    (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (lazyDeltaProjReduction.finish i e₁ e₂).SWF c s fun _ _ => True := by
  unfold finish
  refine .stateWF fun wf => (reduceProjCore.SWF h₁).bind fun _ _ _ ha => ?_; extract_lets F
  have hF {s} : (F ⟨⟩).SWF c s fun _ _ => True := isDefEqCore.SWF h₁ h₂
  split <;> [skip; exact hF]
  refine (reduceProjCore.SWF h₂).bind fun _ _ _ hb => ?_
  split <;> [skip; exact hF]
  exact isDefEqCore.SWF ((ha _ rfl).dom wf h₁) ((hb _ rfl).dom wf h₂)

theorem lazyDeltaProjReduction.loop.SWF {c : Context} {s : State}
    (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (lazyDeltaProjReduction.loop i e₁ e₂ n).SWF c s fun _ _ => True := by
  induction n generalizing s e₁ e₂ with | zero => exact .throw | succ n ih
  unfold loop
  refine (lazyDeltaReductionStep.SWF h₁ h₂).bind fun _ _ _ h => ?_; split
  · exact ih h.1 h.2
  · exact .pure trivial
  all_goals exact finish.SWF h.1 h.2

theorem tryStringLitExpansionCore.SWF {c : Context} {s : State} (h₂ : Dom c e₂) :
    (tryStringLitExpansionCore e₁ e₂).SWF c s fun _ _ => True := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure trivial]
  exact .toLBoolM <| isDefEqCore.SWF
    (dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)) h₂

theorem tryStringLitExpansion.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (tryStringLitExpansion e₁ e₂).SWF c s fun _ _ => True := by
  refine (tryStringLitExpansionCore.SWF h₂).bind fun _ _ _ _ => ?_
  split
  · exact tryStringLitExpansionCore.SWF h₁
  · exact .pure trivial

theorem isDefEqUnitLike.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqUnitLike e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqUnitLike
  refine (inferType.SWF h₁).bind fun _ _ _ ht => .stateWF fun wf => ?_
  refine (whnf.SWF (ht.dom wf h₁)).bind fun _ _ _ ht' => .stateWF fun wf => ?_
  have hd := (ht.trans ht').dom wf h₁
  split <;> [skip; exact .pure trivial]
  refine .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (inferType.SWF h₂).bind fun _ _ _ hs => .stateWF fun wf' => ?_
  exact isDefEqCore.SWF hd (hs.dom wf' h₂)

theorem isDefEqCore'.SWF {c : Context} {s : State} (h₁ : Dom c e₁) (h₂ : Dom c e₂) :
    (isDefEqCore' e₁ e₂).SWF c s fun _ _ => True := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.SWF h₁ h₂).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine .readThe ?_
  suffices ∀ {s}, (F1 ⟨⟩).SWF c s fun _ _ => True by
    split <;> [skip; exact this]
    refine (whnf.SWF h₁).bind fun _ _ _ _ => ?_
    split <;> [exact .pure trivial; exact this]
  intro; unfold F1
  refine (whnfCore.SWF h₁).bind fun tn _ _ ht => .stateWF fun wf => ?_
  refine (whnfCore.SWF h₂).bind fun sn _ _ hs => .stateWF fun wf' => ?_
  have a1 := ht.dom wf h₁; have b1 := hs.dom wf' h₂
  extract_lets F2
  suffices ∀ {s}, (F2 ⟨⟩).SWF c s fun _ _ => True by
    split <;> [skip; exact this]
    refine (quickIsDefEq.SWF a1 b1).bind fun _ _ _ _ => ?_
    split <;> [exact .pure trivial; exact this]
  intro; unfold F2
  refine (isDefEqProofIrrel.SWF a1 b1).bind fun _ _ _ _ => ?_
  split; · exact .pure trivial
  have hld {s} : (lazyDeltaReduction tn sn).SWF c s fun r _ => r.Dom c := by
    unfold lazyDeltaReduction; exact .readThe (lazyDeltaReduction.loop.SWF a1 b1)
  refine hld.bind fun _ _ _ h => ?_; split
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial
  rename_i tn' sn'
  have ⟨c1, d1⟩ : Dom c tn' ∧ Dom c sn' := h
  extract_lets F3
  suffices ∀ {s}, (F3 ⟨⟩).SWF c s fun _ _ => True by
    split
    · split <;> [exact .pure trivial; exact this]
    · split <;> [exact .pure trivial; exact this]
    · split <;> [skip; exact this]
      refine (show (lazyDeltaProjReduction _ _ _).SWF c _ fun _ _ => True by
        unfold lazyDeltaProjReduction
        exact .readThe (lazyDeltaProjReduction.loop.SWF c1 d1)).bind fun _ _ _ _ => ?_
      split <;> [exact .pure trivial; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.SWF c1).bind fun _ _ _ ht => .stateWF fun wf => ?_
  refine (whnfCore.SWF d1).bind fun _ _ _ hs => .stateWF fun wf' => ?_
  split
  · exact isDefEqCore.SWF (ht.dom wf c1) (hs.dom wf' d1)
  refine (isDefEqApp.SWF c1 d1).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryEtaExpansion.SWF c1 d1).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryEtaStruct.SWF c1 d1).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryStringLitExpansion.SWF c1 d1).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (isDefEqUnitLike.SWF c1 d1).bind fun _ _ _ _ => ?_
  split <;> exact .pure trivial

end Inner

open Inner in
theorem Methods.withFuel.SWF : ∀ n, (Methods.withFuel n).SWF
  | 0 => ⟨fun _ _ => .throw, fun _ => .throw, fun _ => .throw, fun _ => .throw⟩
  | n + 1 => ⟨fun h₁ h₂ => isDefEqCore'.SWF h₁ h₂ _ (withFuel.SWF n),
      fun h => whnfCore'.SWF h _ (withFuel.SWF n), fun h => whnf'.SWF h _ (withFuel.SWF n),
      fun h => inferType'.SWF h _ (withFuel.SWF n)⟩

theorem RecM.SWF.run {c : Context} {s : State} {x : RecM α} {Q} (H : x.SWF c s Q) :
    (RecM.run x).SWF c s Q := H _ (Methods.withFuel.SWF _)

end TypeChecker
end Lean4Lean

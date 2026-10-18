import Lean4Lean.Verify.Support.SimWHNF

/-!
# Definitional equality reads only what its input mentions
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

/-- Entering a binder whose type mentions only what `S` allows keeps `S` with the new variable
closed. -/
theorem _root_.Lean4Lean.Supp.Closed.push {S : Supp} {c₁ : Context} {s : State} (hS : S.Closed c₁)
    (wf : SuppState c₁ s) {name ty bi} (hty : ty.SuppIn S) :
    (S.addFVars [⟨s.ngen.curr⟩]).Closed
      { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } := by
  have E := wf.ctxExt (name := name) (ty := ty) (bi := bi)
  have T := (Tele.nil (c := c₁)).push E
  have TS := (TeleSupp.nil (c := c₁) (S := S)).push Tele.nil E fun d hd => by
    simp only [LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
      Option.some.injEq] at hd; subst hd
    exact hty.mono Supp.le_addFVars
  simpa using T.closed TS (wf.lctxWF.mkLocalDecl E.fresh) hS

namespace Inner

theorem isDefEqLambda.SS {S : Supp} {c₁ c₂ : Context} {s : State} {subst : Array Expr}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁)
    (hsub : ∀ a ∈ subst, Dom c₁ a ∧ a.SuppIn S) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂)
    (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqLambda e₁ e₂ subst) (isDefEqLambda e₁ e₂ subst) fun _ _ => True := by
  have hd {e} (h : Dom c₁ e) := Dom.instRev (fun a h => (hsub a h).1) h (arr := subst)
  have hsi {e : Expr} (h : e.SuppIn S) : (e.instantiateRev subst).SuppIn S :=
    Expr.SuppIn.instantiateRev (fun a h => (hsub a h).2) h
  unfold isDefEqLambda
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
    exact isDefEq.SS hA hS (hd h₁) (hd h₂) (hsi hs₁) (hsi hs₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  have hd₁ : Dom c₁ d₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hd₂ : Dom c₁ d₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  have hb₁ : Dom c₁ b₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hb₂ : Dom c₁ b₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  suffices ∀ {x s}, (∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S) →
      RecM.SS c₁ c₂ s (F x) (F x) fun _ _ => True by
    split
    · exact (RecM.SS.pure (a := none) (Q := fun x _ => ∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S)
        nofun).bind fun _ _ _ h => this h
    · refine (isDefEq.SS hA hS (hd hd₁) (hd hd₂) (hsi hs₁.1) (hsi hs₂.1)).bind
        fun _ _ _ _ => ?_
      split
      · exact .pure trivial
      · exact (RecM.SS.pure (a := some (d₂.instantiateRev subst))
          (Q := fun x _ => ∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S)
          fun _ eq => by cases eq; exact ⟨hd hd₂, hsi hs₂.1⟩).bind fun _ _ _ h => this h
  intro x s hx
  unfold F; split
  · extract_lets d₂'
    have hd' : Dom c₁ d₂' ∧ d₂'.SuppIn S := by
      unfold d₂'; cases x with
      | none => exact ⟨hd hd₂, hsi hs₂.1⟩
      | some y => exact hx y rfl
    refine .stateWF fun wf => .withLocalDecl hd'.1 ?_
    have E := wf.ctxExt (name := n₂) (ty := d₂') (bi := bi₂)
    refine isDefEqLambda.SS (hA.mkLocalDecl wf) (Supp.Closed.push hS wf hd'.2) (fun a ha => ?_)
      (hb₁.mono E) (hb₂.mono E) (hs₁.2.mono Supp.le_addFVars) (hs₂.2.mono Supp.le_addFVars)
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact ⟨(hsub a ha).1.mono E, (hsub a ha).2.mono Supp.le_addFVars⟩
    · exact ⟨fun _ h => by simp [Expr.fvarsList] at h; subst h; exact E.dom, .inr (by simp)⟩
  · refine isDefEqLambda.SS hA hS (fun a ha => ?_) hb₁ hb₂ hs₁.2 hs₂.2
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact hsub a ha
    · exact ⟨Dom.default, Expr.SuppIn.default hS.2.dummy⟩

theorem isDefEqForall.SS {S : Supp} {c₁ c₂ : Context} {s : State} {subst : Array Expr}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁)
    (hsub : ∀ a ∈ subst, Dom c₁ a ∧ a.SuppIn S) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂)
    (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqForall e₁ e₂ subst) (isDefEqForall e₁ e₂ subst) fun _ _ => True := by
  have hd {e} (h : Dom c₁ e) := Dom.instRev (fun a h => (hsub a h).1) h (arr := subst)
  have hsi {e : Expr} (h : e.SuppIn S) : (e.instantiateRev subst).SuppIn S :=
    Expr.SuppIn.instantiateRev (fun a h => (hsub a h).2) h
  unfold isDefEqForall
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
    exact isDefEq.SS hA hS (hd h₁) (hd h₂) (hsi hs₁) (hsi hs₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  have hd₁ : Dom c₁ d₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hd₂ : Dom c₁ d₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  have hb₁ : Dom c₁ b₁ := fun x hx => h₁ x (by simp [Expr.fvarsList, hx])
  have hb₂ : Dom c₁ b₂ := fun x hx => h₂ x (by simp [Expr.fvarsList, hx])
  suffices ∀ {x s}, (∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S) →
      RecM.SS c₁ c₂ s (F x) (F x) fun _ _ => True by
    split
    · exact (RecM.SS.pure (a := none) (Q := fun x _ => ∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S)
        nofun).bind fun _ _ _ h => this h
    · refine (isDefEq.SS hA hS (hd hd₁) (hd hd₂) (hsi hs₁.1) (hsi hs₂.1)).bind
        fun _ _ _ _ => ?_
      split
      · exact .pure trivial
      · exact (RecM.SS.pure (a := some (d₂.instantiateRev subst))
          (Q := fun x _ => ∀ y, x = some y → Dom c₁ y ∧ y.SuppIn S)
          fun _ eq => by cases eq; exact ⟨hd hd₂, hsi hs₂.1⟩).bind fun _ _ _ h => this h
  intro x s hx
  unfold F; split
  · extract_lets d₂'
    have hd' : Dom c₁ d₂' ∧ d₂'.SuppIn S := by
      unfold d₂'; cases x with
      | none => exact ⟨hd hd₂, hsi hs₂.1⟩
      | some y => exact hx y rfl
    refine .stateWF fun wf => .withLocalDecl hd'.1 ?_
    have E := wf.ctxExt (name := n₂) (ty := d₂') (bi := bi₂)
    refine isDefEqForall.SS (hA.mkLocalDecl wf) (Supp.Closed.push hS wf hd'.2) (fun a ha => ?_)
      (hb₁.mono E) (hb₂.mono E) (hs₁.2.mono Supp.le_addFVars) (hs₂.2.mono Supp.le_addFVars)
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact ⟨(hsub a ha).1.mono E, (hsub a ha).2.mono Supp.le_addFVars⟩
    · exact ⟨fun _ h => by simp [Expr.fvarsList] at h; subst h; exact E.dom, .inr (by simp)⟩
  · refine isDefEqForall.SS hA hS (fun a ha => ?_) hb₁ hb₂ hs₁.2 hs₂.2
    simp only [Array.mem_push] at ha
    obtain ha | rfl := ha
    · exact hsub a ha
    · exact ⟨Dom.default, Expr.SuppIn.default hS.2.dummy⟩

theorem quickIsDefEq.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (quickIsDefEq e₁ e₂ useHash) (quickIsDefEq e₁ e₂ useHash)
      fun _ _ => True := by
  unfold quickIsDefEq
  refine .bind (Q := fun _ _ => True) (fun m hm => ⟨?_, fun _ _ _ eq => by revert eq; exact id⟩)
    fun _ _ _ _ => ?_
  · intro wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    exact ⟨{ wf with }, .rfl, trivial⟩
  split; · exact .pure trivial
  split
  · exact .toLBoolM (isDefEqLambda.SS hA hS nofun h₁ h₂ hs₁ hs₂)
  · exact .toLBoolM (isDefEqForall.SS hA hS nofun h₁ h₂ hs₁ hs₂)
  · exact .pure trivial
  · exact .toLBoolM (isDefEq.SS hA hS h₁ h₂ hs₁ hs₂)
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial

theorem isDefEqArgs.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqArgs e₁ e₂) (isDefEqArgs e₁ e₂) fun _ _ => True := by
  unfold isDefEqArgs; split
  · refine (isDefEq.SS hA hS (fun x hx => h₁ x (by simp [Expr.fvarsList, hx]))
      (fun x hx => h₂ x (by simp [Expr.fvarsList, hx])) hs₁.2 hs₂.2).bind fun _ _ _ _ => ?_
    split
    · exact .pure trivial
    · exact isDefEqArgs.SS hA hS (fun x hx => h₁ x (by simp [Expr.fvarsList, hx]))
        (fun x hx => h₂ x (by simp [Expr.fvarsList, hx])) hs₁.1 hs₂.1
  all_goals exact .pure trivial

theorem tryEtaExpansionCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryEtaExpansionCore e₁ e₂) (tryEtaExpansionCore e₁ e₂) fun _ _ => True := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure trivial]
  refine (inferType.SS hA hS h₂ hs₂).bind fun _ _ _ h => .stateWF fun wf => ?_
  refine (whnf.SS hA hS (h.dom wf h₂) (h S hS hs₂)).bind fun _ _ _ h' => .stateWF fun wf => ?_
  split <;> [skip; exact .pure trivial]
  have := (h.trans h').dom wf h₂
  have hs := (h.trans h') S hS hs₂
  refine isDefEq.SS hA hS h₁ (fun x hx => ?_) hs₁ ⟨hs.1, hs₂, trivial⟩
  simp [Expr.fvarsList] at hx
  rcases hx with hx | hx
  · exact this x (by simp [Expr.fvarsList, hx])
  · exact h₂ x hx

theorem tryEtaExpansion.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryEtaExpansion e₁ e₂) (tryEtaExpansion e₁ e₂) fun _ _ => True :=
  .orM (tryEtaExpansionCore.SS hA hS h₁ h₂ hs₁ hs₂)
    fun _ => tryEtaExpansionCore.SS hA hS h₂ h₁ hs₂ hs₁

theorem tryEtaStructCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryEtaStructCore e₁ e₂) (tryEtaStructCore e₁ e₂) fun _ _ => True := by
  unfold tryEtaStructCore
  split <;> [skip; exact .pure trivial]
  rename_i f _ heq
  have hf := getAppFn_const_supp hs₂ heq
  refine .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hf)).bind
    fun _ _ _ hci => ?_
  split <;> [skip; exact .pure trivial]
  rename_i fInfo
  have hind : S.const fInfo.induct := (hS.2.find _ _ hci hf).2
  split <;> [skip; exact .pure trivial]
  rw [isNonRecStructure_agree hA hind]
  split <;> [skip; exact .pure trivial]
  refine (inferType.SS hA hS h₁ hs₁).bind fun _ _ _ ht₁ => .stateWF fun wf => ?_
  refine (inferType.SS hA hS h₂ hs₂).bind fun _ _ _ ht₂ => .stateWF fun wf' => ?_
  refine (isDefEq.SS hA hS (ht₁.dom wf h₁) (ht₂.dom wf' h₂) (ht₁ S hS hs₁)
    (ht₂ S hS hs₂)).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  have hargs : ∀ a ∈ e₂.getAppArgs, Dom c₁ a := fun a ha =>
    dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 h₂) a ha)
  refine (RecM.SS.forIn'_range (Inv := fun _ => True) (fun i hi b s _ => ?_) trivial).bind
    fun _ _ _ _ => ?_
  · dsimp only
    refine (isDefEq.SS hA hS (show Dom c₁ (.proj _ _ e₁) from h₁) (hargs _ (Array.getElem_mem _))
      hs₁ (hs₂.getAppArgs _ (Array.getElem_mem _))).bind fun _ _ _ _ => ?_
    split <;> exact .pure trivial
  · dsimp only; split <;> exact .pure trivial

theorem tryEtaStruct.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryEtaStruct e₁ e₂) (tryEtaStruct e₁ e₂) fun _ _ => True :=
  .orM (tryEtaStructCore.SS hA hS h₁ h₂ hs₁ hs₂) fun _ => tryEtaStructCore.SS hA hS h₂ h₁ hs₂ hs₁

theorem isDefEqApp.loop.SS {S : Supp} {c₁ c₂ : Context} {s : State} {tArgs sArgs : Array Expr}
    {eq : tArgs.size = sArgs.size} (hA : Agree S c₁ c₂) (hS : S.Closed c₁)
    (ht : ∀ a ∈ tArgs, Dom c₁ a ∧ a.SuppIn S) (hs : ∀ a ∈ sArgs, Dom c₁ a ∧ a.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqApp.loop tArgs sArgs eq i) (isDefEqApp.loop tArgs sArgs eq i)
      fun _ _ => True := by
  unfold isDefEqApp.loop; split
  · have a := ht _ (Array.getElem_mem (by assumption))
    have b := hs _ (Array.getElem_mem (by rw [← eq]; assumption))
    refine (isDefEq.SS hA hS a.1 b.1 a.2 b.2).bind fun _ _ _ _ => ?_
    split
    · exact isDefEqApp.loop.SS hA hS ht hs
    · exact .pure trivial
  · exact .pure trivial
termination_by tArgs.size - i

theorem isDefEqApp.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqApp e₁ e₂) (isDefEqApp e₁ e₂) fun _ _ => True := by
  unfold isDefEqApp; split <;> [skip; exact .pure trivial]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  split <;> [skip; exact .pure trivial]
  have hf {e} (h : Dom c₁ e) : Dom c₁ e.getAppFn := dom_iff.2 (dom_iff.1 h).getAppFn
  have ha {e : Expr} (h : Dom c₁ e) (hs : e.SuppIn S) : ∀ a ∈ e.getAppArgs, Dom c₁ a ∧ a.SuppIn S :=
    fun a ha => ⟨dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 h) a ha), hs.getAppArgs a ha⟩
  refine (isDefEq.SS hA hS (hf h₁) (hf h₂) hs₁.getAppFn hs₂.getAppFn).bind fun _ _ _ _ => ?_
  split
  · exact isDefEqApp.loop.SS hA hS (ha h₁ hs₁) (ha h₂ hs₂)
  · exact .pure trivial

theorem isDefEqProofIrrel.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqProofIrrel e₁ e₂) (isDefEqProofIrrel e₁ e₂) fun _ _ => True := by
  unfold isDefEqProofIrrel
  refine (inferType.SS hA hS h₁ hs₁).bind fun _ _ _ ht₁ => .stateWF fun wf => ?_
  refine (isProp.SS hA hS (ht₁.dom wf h₁) (ht₁ S hS hs₁)).bind fun _ _ _ _ => ?_
  split; · exact .pure trivial
  refine (inferType.SS hA hS h₂ hs₂).bind fun _ _ _ ht₂ => .stateWF fun wf' => ?_
  exact .toLBoolM (isDefEq.SS hA hS (ht₁.dom wf h₁) (ht₂.dom wf' h₂) (ht₁ S hS hs₁)
    (ht₂ S hS hs₂))

theorem cacheFailure.SS {c₁ c₂ : Context} {s : State} :
    RecM.SS c₁ c₂ s (cacheFailure e₁ e₂) (cacheFailure e₁ e₂) fun _ _ => True :=
  fun _ _ => ⟨cacheFailure.SWF, fun _ _ _ eq => by revert eq; exact id⟩

theorem tryUnfoldProjApp.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (tryUnfoldProjApp e) (tryUnfoldProjApp e)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.SS hA hS he hs).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

/-- What `lazyDeltaReductionStep` returns mentions only what `S` allows. -/
def _root_.Lean4Lean.TypeChecker.ReductionStatus.SuppIn (S : Supp) : ReductionStatus → Prop
  | .continue e₁ e₂ | .unknown e₁ e₂ | .false e₁ e₂ => e₁.SuppIn S ∧ e₂.SuppIn S
  | .true => True

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.SuppIn.bool {S : Supp}
    (h₁ : e₁.SuppIn S) (h₂ : e₂.SuppIn S) : (ReductionStatus.bool e₁ e₂ b).SuppIn S := by
  cases b <;> [exact ⟨h₁, h₂⟩; trivial]

theorem lazyDeltaReductionStep.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (lazyDeltaReductionStep e₁ e₂) (lazyDeltaReductionStep e₁ e₂)
      fun r _ => r.Dom c₁ ∧ r.SuppIn S := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_
  rw [isDelta_agree hA hs₁, isDelta_agree hA hs₂]
  extract_lets delta cont F1 F2
  have hdelta {s e} (he : Dom c₁ e) (hs : e.SuppIn S) :
      RecM.SS c₁ c₂ s (delta e) (delta e) fun r _ => Dom c₁ r ∧ r.SuppIn S := by
    refine (unfoldDefinition.SS hA hs).bind fun oe _ _ H => .stateWF fun wf => ?_
    have hd : Dom c₁ oe.get! ∧ oe.get!.SuppIn S := by
      cases oe with
      | none => exact ⟨Dom.default, Expr.SuppIn.default hS.2.dummy⟩
      | some e' => exact ⟨(H e' rfl).dom wf he, H e' rfl S hS hs⟩
    exact (whnfCore.SS hA hS hd.1 hd.2).mono fun _ _ _ h => ⟨h.dom ‹_› hd.1, h S hS hd.2⟩
  have hcont {s e₁' e₂'} (h₁ : Dom c₁ e₁') (h₂ : Dom c₁ e₂') (hs₁ : e₁'.SuppIn S)
      (hs₂ : e₂'.SuppIn S) :
      RecM.SS c₁ c₂ s (cont e₁' e₂') (cont e₁' e₂') fun r _ => r.Dom c₁ ∧ r.SuppIn S :=
    (quickIsDefEq.SS hA hS h₁ h₂ hs₁ hs₂).bind fun _ _ _ _ => .pure (by
      split
      · exact ⟨⟨h₁, h₂⟩, hs₁, hs₂⟩
      · exact ⟨trivial, trivial⟩
      · exact ⟨⟨h₁, h₂⟩, hs₁, hs₂⟩)
  split
  · exact .pure ⟨⟨h₁, h₂⟩, hs₁, hs₂⟩
  · refine (tryUnfoldProjApp.SS hA hS h₂ hs₂).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · exact hcont h₁ ((h _ rfl).dom wf h₂) hs₁ (h _ rfl S hS hs₂)
    · exact (hdelta h₁ hs₁).bind fun _ _ _ h => hcont h.1 h₂ h.2 hs₂
  · refine (tryUnfoldProjApp.SS hA hS h₁ hs₁).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · exact hcont ((h _ rfl).dom wf h₁) h₂ (h _ rfl S hS hs₁) hs₂
    · exact (hdelta h₂ hs₂).bind fun _ _ _ h => hcont h₁ h.1 hs₁ h.2
  extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta h₂ hs₂).bind fun _ _ _ h => hcont h₁ h.1 hs₁ h.2
  · exact (hdelta h₁ hs₁).bind fun _ _ _ h => hcont h.1 h₂ h.2 hs₂
  have hF1 {s} : RecM.SS c₁ c₂ s (F1 ()) (F1 ()) fun r _ => r.Dom c₁ ∧ r.SuppIn S :=
    (hdelta h₁ hs₁).bind fun _ _ _ a => (hdelta h₂ hs₂).bind fun _ _ _ b => hcont a.1 b.1 a.2 b.2
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.SS.bind fun _ _ _ _ => hF1]
  refine (isDefEqArgs.SS hA hS h₁ h₂ hs₁ hs₂).bind fun _ _ _ _ => ?_
  split <;> [exact .pure ⟨trivial, trivial⟩; exact cacheFailure.SS.bind fun _ _ _ _ => hF1]

theorem isNatSuccOf?_supp {S : Supp} (H : isNatSuccOf? e = some e₁) (h : e.SuppIn S) :
    e₁.SuppIn S := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · exact (h : Literal.SuppIn _ _)
  · exact h.2

theorem isDefEqOffset.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqOffset e₁ e₂) (isDefEqOffset e₁ e₂) fun _ _ => True := by
  unfold isDefEqOffset; split
  · exact .pure trivial
  · split <;> [skip; exact .pure trivial]
    exact .toLBoolM (isDefEqCore.SS hA hS (isNatSuccOf?_dom ‹_› h₁) (isNatSuccOf?_dom ‹_› h₂)
      (isNatSuccOf?_supp ‹_› hs₁) (isNatSuccOf?_supp ‹_› hs₂))

theorem lazyDeltaReduction.loop.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (lazyDeltaReduction.loop e₁ e₂ n) (lazyDeltaReduction.loop e₁ e₂ n)
      fun r _ => r.Dom c₁ ∧ r.SuppIn S := by
  induction n generalizing s e₁ e₂ with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.SS hA hS h₁ h₂ hs₁ hs₂).bind fun _ _ _ _ => ?_; split
  · exact .pure ⟨.bool h₁ h₂, .bool hs₁ hs₂⟩
  suffices hF1 : ∀ {s}, RecM.SS c₁ c₂ s (F1 ⟨⟩) (F1 ⟨⟩) fun r _ => r.Dom c₁ ∧ r.SuppIn S by
    refine .readThe ?_; rw [hA.eagerReduce]; split <;> [skip; exact hF1]
    refine (reduceNat.SS hA hS h₁ hs₁).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · have a := h _ rfl
      exact (isDefEqCore.SS hA hS (a.dom wf h₁) h₂ (a S hS hs₁) hs₂).bind
        fun _ _ _ _ => .pure ⟨.bool (a.dom wf h₁) h₂, .bool (a S hS hs₁) hs₂⟩
    refine (reduceNat.SS hA hS h₂ hs₂).bind fun _ _ _ h => .stateWF fun wf => ?_; split
    · have a := h _ rfl
      exact (isDefEqCore.SS hA hS h₁ (a.dom wf h₂) hs₁ (a S hS hs₂)).bind
        fun _ _ _ _ => .pure ⟨.bool h₁ (a.dom wf h₂), .bool hs₁ (a S hS hs₂)⟩
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (RecM.SS.liftExcept reduceNative.SWF fun _ h => h).bind fun _ _ _ h => ?_
  split <;> [cases h; skip]
  refine (RecM.SS.liftExcept reduceNative.SWF fun _ h => h).bind fun _ _ _ h => ?_
  split <;> [cases h; skip]
  refine (lazyDeltaReductionStep.SS hA hS h₁ h₂ hs₁ hs₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» => exact ih h.1.1 h.1.2 h.2.1 h.2.2
  | _ => exact .pure h

theorem lazyDeltaProjReduction.finish.SS {S : Supp} {c₁ c₂ : Context} {s : State}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂)
    (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (lazyDeltaProjReduction.finish i e₁ e₂)
      (lazyDeltaProjReduction.finish i e₁ e₂) fun _ _ => True := by
  unfold finish
  refine .stateWF fun wf => (reduceProjCore.SS hA hS h₁ hs₁).bind fun _ _ _ ha => ?_
  extract_lets F
  have hF {s} : RecM.SS c₁ c₂ s (F ⟨⟩) (F ⟨⟩) fun _ _ => True :=
    isDefEqCore.SS hA hS h₁ h₂ hs₁ hs₂
  split <;> [skip; exact hF]
  refine (reduceProjCore.SS hA hS h₂ hs₂).bind fun _ _ _ hb => ?_
  split <;> [skip; exact hF]
  exact isDefEqCore.SS hA hS ((ha _ rfl).dom wf h₁) ((hb _ rfl).dom wf h₂)
    (ha _ rfl S hS hs₁) (hb _ rfl S hS hs₂)

theorem lazyDeltaProjReduction.loop.SS {S : Supp} {c₁ c₂ : Context} {s : State}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂)
    (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (lazyDeltaProjReduction.loop i e₁ e₂ n)
      (lazyDeltaProjReduction.loop i e₁ e₂ n) fun _ _ => True := by
  induction n generalizing s e₁ e₂ with | zero => exact .throw | succ n ih
  unfold loop
  refine (lazyDeltaReductionStep.SS hA hS h₁ h₂ hs₁ hs₂).bind fun _ _ _ h => ?_; split
  · exact ih h.1.1 h.1.2 h.2.1 h.2.2
  · exact .pure trivial
  all_goals exact finish.SS hA hS h.1.1 h.1.2 h.2.1 h.2.2

theorem tryStringLitExpansionCore.SS {S : Supp} {c₁ c₂ : Context} {s : State}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S)
    (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryStringLitExpansionCore e₁ e₂) (tryStringLitExpansionCore e₁ e₂)
      fun _ _ => True := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure trivial]
  exact .toLBoolM <| isDefEqCore.SS hA hS
    (dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)) h₂
    (Expr.SuppIn.strLitToConstructor hs₁) hs₂

theorem tryStringLitExpansion.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (tryStringLitExpansion e₁ e₂) (tryStringLitExpansion e₁ e₂)
      fun _ _ => True := by
  refine (tryStringLitExpansionCore.SS hA hS h₂ hs₁ hs₂).bind fun _ _ _ _ => ?_
  split
  · exact tryStringLitExpansionCore.SS hA hS h₁ hs₂ hs₁
  · exact .pure trivial

theorem isDefEqUnitLike.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqUnitLike e₁ e₂) (isDefEqUnitLike e₁ e₂) fun _ _ => True := by
  unfold isDefEqUnitLike
  refine (inferType.SS hA hS h₁ hs₁).bind fun _ _ _ ht => .stateWF fun wf => ?_
  refine (whnf.SS hA hS (ht.dom wf h₁) (ht S hS hs₁)).bind fun _ _ _ ht' => .stateWF fun wf => ?_
  have hd := (ht.trans ht').dom wf h₁
  have hds := (ht.trans ht') S hS hs₁
  split <;> [skip; exact .pure trivial]
  rename_i I _ heq
  have hI := getAppFn_const_supp hds heq
  refine .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hI)).bind
    fun _ _ _ hci => ?_
  split <;> [skip; exact .pure trivial]
  rename_i _ _ _ _ _ _ c' _ _ _
  have hc : S.const c' := (hS.2.find _ _ hci hI).2 c' (by simp)
  refine (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hc)).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (inferType.SS hA hS h₂ hs₂).bind fun _ _ _ hs => .stateWF fun wf' => ?_
  exact isDefEqCore.SS hA hS hd (hs.dom wf' h₂) hds (hs S hS hs₂)

theorem isDefEqCore'.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqCore' e₁ e₂) (isDefEqCore' e₁ e₂) fun _ _ => True := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.SS hA hS h₁ h₂ hs₁ hs₂).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine .readThe ?_
  rw [hA.eagerReduce]
  suffices ∀ {s}, RecM.SS c₁ c₂ s (F1 ⟨⟩) (F1 ⟨⟩) fun _ _ => True by
    split <;> [skip; exact this]
    refine (whnf.SS hA hS h₁ hs₁).bind fun _ _ _ _ => ?_
    split <;> [exact .pure trivial; exact this]
  intro; unfold F1
  refine (whnfCore.SS hA hS h₁ hs₁).bind fun tn _ _ ht => .stateWF fun wf => ?_
  refine (whnfCore.SS hA hS h₂ hs₂).bind fun sn _ _ hs => .stateWF fun wf' => ?_
  have a1 := ht.dom wf h₁; have b1 := hs.dom wf' h₂
  have a2 := ht S hS hs₁; have b2 := hs S hS hs₂
  extract_lets F2
  suffices ∀ {s}, RecM.SS c₁ c₂ s (F2 ⟨⟩) (F2 ⟨⟩) fun _ _ => True by
    split <;> [skip; exact this]
    refine (quickIsDefEq.SS hA hS a1 b1 a2 b2).bind fun _ _ _ _ => ?_
    split <;> [exact .pure trivial; exact this]
  intro; unfold F2
  refine (isDefEqProofIrrel.SS hA hS a1 b1 a2 b2).bind fun _ _ _ _ => ?_
  split; · exact .pure trivial
  have hld {s} : RecM.SS c₁ c₂ s (lazyDeltaReduction tn sn) (lazyDeltaReduction tn sn)
      fun r _ => r.Dom c₁ ∧ r.SuppIn S := by
    unfold lazyDeltaReduction; refine .readThe ?_; rw [hA.fuel]
    exact lazyDeltaReduction.loop.SS hA hS a1 b1 a2 b2
  refine hld.bind fun _ _ _ h => ?_; split
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial
  rename_i tn' sn'
  have ⟨⟨c1, d1⟩, c2, d2⟩ : (Dom c₁ tn' ∧ Dom c₁ sn') ∧ tn'.SuppIn S ∧ sn'.SuppIn S := h
  extract_lets F3
  suffices ∀ {s}, RecM.SS c₁ c₂ s (F3 ⟨⟩) (F3 ⟨⟩) fun _ _ => True by
    split
    · split <;> [exact .pure trivial; exact this]
    · split <;> [exact .pure trivial; exact this]
    · split <;> [skip; exact this]
      refine (show RecM.SS c₁ c₂ _ (lazyDeltaProjReduction _ _ _)
          (lazyDeltaProjReduction _ _ _) fun _ _ => True by
        unfold lazyDeltaProjReduction; refine .readThe ?_; rw [hA.fuel]
        exact lazyDeltaProjReduction.loop.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
      split <;> [exact .pure trivial; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.SS hA hS c1 c2).bind fun _ _ _ ht => .stateWF fun wf => ?_
  refine (whnfCore.SS hA hS d1 d2).bind fun _ _ _ hs => .stateWF fun wf' => ?_
  split
  · exact isDefEqCore.SS hA hS (ht.dom wf c1) (hs.dom wf' d1) (ht S hS c2) (hs S hS d2)
  refine (isDefEqApp.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryEtaExpansion.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryEtaStruct.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (tryStringLitExpansion.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
  split <;> [exact .pure trivial; skip]
  refine (isDefEqUnitLike.SS hA hS c1 d1 c2 d2).bind fun _ _ _ _ => ?_
  split <;> exact .pure trivial

end Inner

open Inner in
theorem Methods.withFuel.SS : ∀ n, (Methods.withFuel n).SS
  | 0 => ⟨fun _ _ _ _ _ _ => ⟨.throw, fun _ _ _ h => nomatch h⟩,
      fun _ _ _ _ => ⟨.throw, fun _ _ _ h => nomatch h⟩,
      fun _ _ _ _ => ⟨.throw, fun _ _ _ h => nomatch h⟩,
      fun _ _ _ _ => ⟨.throw, fun _ _ _ h => nomatch h⟩⟩
  | n + 1 => ⟨fun hA hS h₁ h₂ hs₁ hs₂ => isDefEqCore'.SS hA hS h₁ h₂ hs₁ hs₂ _ (withFuel.SS n),
      fun hA hS h hs => whnfCore'.SS hA hS h hs _ (withFuel.SS n),
      fun hA hS h hs => whnf'.SS hA hS h hs _ (withFuel.SS n),
      fun hA hS h hs => inferType'.SS hA hS h hs _ (withFuel.SS n)⟩

/-- A run of the type checker in `c₁` that succeeds runs the same way in `c₂`. -/
theorem RecM.SS.run {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q}
    (H : RecM.SS c₁ c₂ s x₁ x₂ Q) (hfuel : c₂.fuel = c₁.fuel) :
    M.SS c₁ c₂ s (RecM.run x₁) (RecM.run x₂) Q := by
  have := H _ (Methods.withFuel.SS c₁.fuel.recDepth)
  exact ⟨this.1, fun wf a s' eq => by
    have := this.2 wf a s' eq
    show x₂ (Methods.withFuel c₂.fuel.recDepth) c₂ s = _
    rw [hfuel]; exact this⟩

end TypeChecker
end Lean4Lean

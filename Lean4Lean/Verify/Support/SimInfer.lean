import Lean4Lean.Verify.Support.Sim

/-!
# Type inference reads only what its input mentions
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

/-- `x₂` succeeds as `x₁` does. -/
def _root_.Except.SimOk (x₁ x₂ : Except ε α) : Prop := ∀ a, x₁ = .ok a → x₂ = .ok a

theorem _root_.Except.SimOk.rfl {x : Except ε α} : x.SimOk x := fun _ => id

theorem _root_.Except.SimOk.bind {x₁ x₂ : Except ε α} {f₁ f₂ : α → Except ε β}
    (h1 : x₁.SimOk x₂) (h2 : ∀ a, x₁ = .ok a → (f₁ a).SimOk (f₂ a)) :
    (x₁ >>= f₁).SimOk (x₂ >>= f₂) := by
  intro b h
  cases e : x₁ with
  | error => rw [e] at h; cases h
  | ok a => rw [e] at h; rw [h1 a e]; exact h2 a e b h

theorem envGet_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) (hn : S.const n) :
    (c₁.env.get n).SimOk (c₂.env.get n) := by
  intro a h
  unfold Environment.get at h ⊢
  rw [hA.env n hn]
  cases e : c₁.env.find? n <;> rw [e] at h <;> cases h; rfl

theorem checkLevel_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂)
    (hl : l.LParamsIn S.lvl) : (Inner.checkLevel c₁ l).SimOk (Inner.checkLevel c₂ l) := by
  intro a h
  unfold Inner.checkLevel at h ⊢
  split at h <;> [cases h; skip]
  rename_i h1
  have h2 := Level.getUndefParam_eq_none_iff.1 (Option.eq_none_iff_forall_ne_some.2 h1)
  rw [Level.getUndefParam_eq_none_iff.2]; · rfl
  clear h1 h
  induction l with
  | zero | mvar => trivial
  | succ _ ih => exact ih hl h2
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => exact ⟨ih1 hl.1 h2.1, ih2 hl.2 h2.2⟩
  | param n => exact hA.lparams n hl h2

theorem inferFVar_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) (hn : S.fv n) :
    (Inner.inferFVar c₁ n).SimOk (Inner.inferFVar c₂ n) := by
  intro a h
  have := hA.lctx n hn
  unfold Inner.inferFVar at h ⊢
  split at h <;> cases h
  rename_i d hd
  rw [hd] at this
  cases e : c₂.lctx.find? n with
  | none => rw [e] at this; cases this
  | some d' =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq] at this
    simp only
    cases d <;> cases d' <;> simp [LocalDecl.erase] at this <;> simp [this, LocalDecl.type] <;> rfl

theorem forIn_checkLevel_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) :
    ∀ {ls : List Level}, (∀ l ∈ ls, l.LParamsIn S.lvl) →
    (forIn ls PUnit.unit fun l _ => do Inner.checkLevel c₁ l; pure (ForInStep.yield PUnit.unit) :
      Except Exception PUnit).SimOk
    (forIn ls PUnit.unit fun l _ => do Inner.checkLevel c₂ l; pure (ForInStep.yield PUnit.unit))
  | [], _ => .rfl
  | l :: ls, hls => by
    simp only [List.forIn_cons]
    intro a h
    cases e : Inner.checkLevel c₁ l with
    | error => simp [e, bind, Except.bind] at h
    | ok u =>
      have e2 := checkLevel_agree hA (hls l (.head _)) u e
      simp only [e, e2, bind, Except.bind, pure, Except.pure] at h ⊢
      exact forIn_checkLevel_agree hA (fun l hl => hls l (.tail _ hl)) a h

theorem inferConstant_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂)
    (hn : S.const n) (hls : ∀ l ∈ ls, l.LParamsIn S.lvl) : (Inner.inferConstant c₁ n ls inferOnly).SimOk
      (Inner.inferConstant c₂ n ls inferOnly) := by
  unfold Inner.inferConstant
  refine (envGet_agree hA hn).bind fun ci _ => ?_
  simp only [hA.safety]
  have hF := forIn_checkLevel_agree hA hls
  repeat' split
  all_goals first
    | exact .rfl
    | exact hF.bind fun _ _ => .rfl

theorem mkBindingList1_agree {lctx₁ lctx₂ : LocalContext}
    (H : (lctx₂.find? x).map LocalDecl.erase = (lctx₁.find? x).map LocalDecl.erase) :
    LocalContext.mkBindingList1 isLambda lctx₂ xs x b =
      LocalContext.mkBindingList1 isLambda lctx₁ xs x b := by
  unfold LocalContext.mkBindingList1
  cases e₁ : lctx₁.find? x with
  | none =>
    cases e₂ : lctx₂.find? x
    · rfl
    · rw [e₁, e₂] at H; simp at H
  | some d₁ =>
  cases e₂ : lctx₂.find? x with
  | none => rw [e₁, e₂] at H; simp at H
  | some d₂ =>
  rw [e₁, e₂] at H; simp only [Option.map_some, Option.some.injEq] at H
  cases d₁ <;> cases d₂ <;> simp [LocalDecl.erase] at H <;> simp [H]

theorem mkBindingList_agree {lctx₁ lctx₂ : LocalContext} {xs : List FVarId}
    (H : ∀ x ∈ xs, (lctx₂.find? x).map LocalDecl.erase = (lctx₁.find? x).map LocalDecl.erase) :
    LocalContext.mkBindingList isLambda lctx₂ xs b =
      LocalContext.mkBindingList isLambda lctx₁ xs b := by
  obtain ⟨xs, rfl⟩ : ∃ xs', List.reverse xs' = xs := ⟨_, List.reverse_reverse _⟩
  simp only [LocalContext.mkBindingList, LocalContext.mkBindingList.core, List.reverse_reverse]
    at *
  generalize b.abstract' _ = b
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [LocalContext.mkBindingList.go]
    rw [mkBindingList1_agree (H x (by simp))]
    exact ih (fun y hy => H y (by simp at hy ⊢; exact .inl hy)) _

theorem mkForall_agree {lctx₁ lctx₂ : LocalContext} {xs : List FVarId}
    (H : ∀ x ∈ xs, (lctx₂.find? x).map LocalDecl.erase = (lctx₁.find? x).map LocalDecl.erase) :
    lctx₂.mkForall ⟨xs.map .fvar⟩ b = lctx₁.mkForall ⟨xs.map .fvar⟩ b := by
  rw [LocalContext.mkForall, LocalContext.mkForall, LocalContext.mkBinding_eq,
    LocalContext.mkBinding_eq, mkBindingList_agree H]

theorem RecM.SS.of_swf {c₁ c₂ : Context} {s : State} {x₁ x₂ : RecM α} {Q Q'}
    (hw : x₁.SWF c₁ s Q) (hs : RecM.SS c₁ c₂ s x₁ x₂ Q') : RecM.SS c₁ c₂ s x₁ x₂ Q :=
  fun m hm => ⟨hw m hm.swf, (hs m hm).2⟩

theorem Supp.addFVars_append {S : Supp} {xs ys : List FVarId} :
    S.addFVars (xs ++ ys) ≤ (S.addFVars xs).addFVars ys ∧
    (S.addFVars xs).addFVars ys ≤ S.addFVars (xs ++ ys) := by
  refine ⟨⟨fun z hz => ?_, fun _ => id, fun _ => id⟩, ⟨fun z hz => ?_, fun _ => id, fun _ => id⟩⟩
  · simp [Supp.addFVars] at hz ⊢; exact or_assoc.2 hz
  · simp [Supp.addFVars] at hz ⊢; exact or_assoc.1 hz

namespace Inner

theorem whnf.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂) (hS : S.Closed c₁)
    (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (whnf e) (whnf e) fun e₁ _ => SuppBelow c₁ e e₁ :=
  fun _ hm => hm.whnf hA hS he hs

theorem whnfCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (whnfCore e cheapProj) (whnfCore e cheapProj) fun e₁ _ => SuppBelow c₁ e e₁ :=
  fun _ hm => hm.whnfCore hA hS he hs

theorem inferType.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferType e inferOnly) (inferType e inferOnly) fun ty _ => SuppBelow c₁ e ty :=
  fun _ hm => hm.inferType hA hS he hs

theorem isDefEqCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEqCore e₁ e₂) (isDefEqCore e₁ e₂) fun _ _ => True :=
  fun _ hm => hm.isDefEqCore hA hS h₁ h₂ hs₁ hs₂

theorem isDefEq.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (h₁ : Dom c₁ e₁) (h₂ : Dom c₁ e₂) (hs₁ : e₁.SuppIn S) (hs₂ : e₂.SuppIn S) :
    RecM.SS c₁ c₂ s (isDefEq e₁ e₂) (isDefEq e₁ e₂) fun _ _ => True := by
  refine (RecM.SS.withTaint fun _ => isDefEqCore.SS hA hS h₁ h₂ hs₁ hs₂).bind fun b _ _ _ => ?_
  simp; split
  · refine fun m hm => ⟨?_, fun _ _ _ eq _ _ => eq⟩
    rintro wf _ _ ⟨⟩
    exact ⟨wf.setAux rfl rfl rfl rfl rfl rfl, .rfl, ⟨Nat.le_refl _, rfl, .refl _ _⟩, trivial⟩
  · exact .pure trivial

theorem ensureSortCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (ensureSortCore e s₀) (ensureSortCore e s₀) fun e₁ _ => SuppBelow c₁ e e₁ := by
  unfold ensureSortCore
  split; · exact .pure .rfl
  refine (whnf.SS hA hS he hs).bind fun e₁ _ _ h => ?_
  split; · exact .pure h
  exact .fail (.getEnv <| .getLCtx .throw)

theorem ensureForallCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (ensureForallCore e s₀) (ensureForallCore e s₀)
      fun e₁ _ => SuppBelow c₁ e e₁ := by
  unfold ensureForallCore
  split; · exact .pure .rfl
  refine (whnf.SS hA hS he hs).bind fun e₁ _ _ h => ?_
  split; · exact .pure h
  exact .fail (.getEnv <| .getLCtx .throw)

/-- The agreement a binder loop keeps: `c₁` extends `c` by `xs`, declared in terms of what `S`
allows, and `c₂` agrees with it on that and `xs`. -/
structure TeleAgree (S : Supp) (c c₁ c₂ : Context) (xs : List FVarId) : Prop where
  tele : Tele c c₁ xs
  supp : TeleSupp c₁ xs S
  agree : Agree (S.addFVars xs) c₁ c₂

theorem TeleAgree.nil {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) :
    TeleAgree S c₁ c₁ c₂ [] :=
  ⟨.nil, .nil, hA.mono ⟨fun _ h => h.resolve_right List.not_mem_nil, fun _ => id, fun _ => id⟩⟩

theorem TeleAgree.push {S : Supp} {c c₁ c₂ : Context} {xs : List FVarId} {s : State}
    (H : TeleAgree S c c₁ c₂ xs) (wf : SuppState c₁ s) {name ty bi}
    (hty : ty.SuppIn (S.addFVars xs)) (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none)
    (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none) :
    TeleAgree S c { c₁ with lctx := c₁.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl ⟨s.ngen.curr⟩ name ty bi } (xs ++ [⟨s.ngen.curr⟩]) := by
  have E := wf.ctxExt f₁ (name := name) (ty := ty) (bi := bi)
  refine ⟨H.tele.push E, H.supp.push H.tele E fun d hd => ?_,
    (H.agree.mkLocalDecl wf f₁ f₂).mono Supp.addFVars_append.1⟩
  simp only [LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
    Option.some.injEq] at hd; subst hd
  exact hty

theorem TeleAgree.pushLet {S : Supp} {c c₁ c₂ : Context} {xs : List FVarId} {s : State}
    (H : TeleAgree S c c₁ c₂ xs) (wf : SuppState c₁ s) {name ty val}
    (hty : ty.SuppIn (S.addFVars xs)) (hval : val.SuppIn (S.addFVars xs))
    (f₁ : c₁.lctx.find? ⟨s.ngen.curr⟩ = none) (f₂ : c₂.lctx.find? ⟨s.ngen.curr⟩ = none) :
    TeleAgree S c { c₁ with lctx := c₁.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl ⟨s.ngen.curr⟩ name ty val }
      (xs ++ [⟨s.ngen.curr⟩]) := by
  have E := wf.ctxExtLet f₁ (name := name) (ty := ty) (val := val)
  refine ⟨H.tele.push E, H.supp.push H.tele E fun d hd => ?_,
    (H.agree.mkLetDecl wf f₁ f₂).mono Supp.addFVars_append.1⟩
  simp only [LocalContext.find?_mkLetDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
    Option.some.injEq] at hd; subst hd
  exact ⟨hty, hval⟩

/-- The agreement of `c₁` with itself, for the run the proof of a simulation checks. -/
theorem TeleAgree.self {S : Supp} {c c₁ c₂ : Context} {xs : List FVarId}
    (H : TeleAgree S c c₁ c₂ xs) (wf : c₁.lctx.WF) : TeleAgree S c c₁ c₁ xs :=
  ⟨H.tele, H.supp, Agree.refl wf⟩

theorem TeleAgree.mkForall {S : Supp} {c c₁ c₂ : Context} {xs : List FVarId}
    (H : TeleAgree S c c₁ c₂ xs) {b : Expr} :
    c₂.lctx.mkForall ⟨xs.map .fvar⟩ b = c₁.lctx.mkForall ⟨xs.map .fvar⟩ b :=
  mkForall_agree fun x hx => H.agree.lctx x (.inr hx)

theorem inferLambda.loop.SS {S : Supp} {c c₁ c₂ : Context} {s : State} {e : Expr}
    {arr : Array Expr} {xs : List FVarId} (T : TeleAgree S c c₁ c₂ xs) (hS : S.Closed c)
    (harr : arr.toList = xs.map .fvar) (hdom : Dom c₁ e) (hse : e.SuppIn (S.addFVars xs)) :
    RecM.SS c₁ c₂ s (inferLambda.loop inferOnly arr e) (inferLambda.loop inferOnly arr e)
      fun _ _ => True := by
  unfold inferLambda.loop; split
  · rename_i name dom body bi
    have hd : Dom c₁ (dom.instantiateRev arr) :=
      Dom.instantiateRev harr T.tele.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have hds : (dom.instantiateRev arr).SuppIn (S.addFVars xs) :=
      SuppIn.instantiateRev_fvars harr hse.1
    have main {s₁} : RecM.SS c₁ c₂ s₁
        (withLocalDecl name bi (dom.instantiateRev arr) fun fv =>
          inferLambda.loop inferOnly (arr.push fv) body)
        (withLocalDecl name bi (dom.instantiateRev arr) fun fv =>
          inferLambda.loop inferOnly (arr.push fv) body) fun _ _ => True := by
      refine .stateWF fun wf => ?_
      refine .withLocalDecl hd (fun f₁ => ?_) (fun f₁ f₂ => ?_) T.agree.wf
      all_goals
        have E := wf.ctxExt f₁ (name := name) (ty := dom.instantiateRev arr) (bi := bi)
      · exact inferLambda.loop.SS ((T.self wf.lctxWF).push wf hds E.fresh E.fresh) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.mono (Supp.addFVars_mono (by simp)))
      · exact inferLambda.loop.SS (T.push wf hds f₁ f₂) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.mono (Supp.addFVars_mono (by simp)))
    split
    · refine .stateWF fun wf => ?_
      have hS' := T.tele.closed T.supp wf.lctxWF hS
      refine (inferType.SS T.agree hS' hd hds).bind fun ty _ _ hty => .stateWF fun wf' => ?_
      exact (ensureSortCore.SS T.agree hS' (hty.dom wf' hd) (hty _ hS' hds)).bind
        fun _ _ _ _ => main
    · exact main
  · refine .stateWF fun wf => ?_
    have hS' := T.tele.closed T.supp wf.lctxWF hS
    refine (inferType.SS T.agree hS' (Dom.instantiateRev harr T.tele.dom hdom)
      (SuppIn.instantiateRev_fvars harr hse)).bind fun r _ _ _ => ?_
    have : arr = ⟨xs.map .fvar⟩ := by cases arr; simp_all
    subst this
    refine .getLCtx ?_
    rw [T.mkForall]; exact .pure trivial

theorem inferLambda.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferLambda e inferOnly) (inferLambda e inferOnly)
      fun ty _ => SuppBelow c₁ e ty :=
  .of_swf (inferLambda.SWF he)
    (inferLambda.loop.SS (.nil hA) hS rfl he (hs.mono Supp.le_addFVars))

theorem inferForall.loop.SS {S : Supp} {c c₁ c₂ : Context} {s : State} {e : Expr}
    {arr : Array Expr} {us : Array Level} {xs : List FVarId} (T : TeleAgree S c c₁ c₂ xs)
    (hS : S.Closed c) (harr : arr.toList = xs.map .fvar) (hdom : Dom c₁ e)
    (hse : e.SuppIn (S.addFVars xs)) :
    RecM.SS c₁ c₂ s (inferForall.loop inferOnly arr us e) (inferForall.loop inferOnly arr us e)
      fun _ _ => True := by
  unfold inferForall.loop; split
  · rename_i name dom body bi
    have hd : Dom c₁ (dom.instantiateRev arr) :=
      Dom.instantiateRev harr T.tele.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have hds : (dom.instantiateRev arr).SuppIn (S.addFVars xs) :=
      SuppIn.instantiateRev_fvars harr hse.1
    refine .stateWF fun wf => ?_
    have hS' := T.tele.closed T.supp wf.lctxWF hS
    refine (inferType.SS T.agree hS' hd hds).bind fun ty _ _ hty => .stateWF fun wf' => ?_
    refine (ensureSortCore.SS T.agree hS' (hty.dom wf' hd) (hty _ hS' hds)).bind
      fun _ s₁ _ _ => .stateWF fun wf => ?_
    refine .withLocalDecl hd (fun f₁ => ?_) (fun f₁ f₂ => ?_) T.agree.wf
    all_goals
      have E := wf.ctxExt f₁ (name := name) (ty := dom.instantiateRev arr) (bi := bi) (s := s₁)
    · exact inferForall.loop.SS ((T.self wf.lctxWF).push wf hds E.fresh E.fresh) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.mono (Supp.addFVars_mono (by simp)))
    · exact inferForall.loop.SS (T.push wf hds f₁ f₂) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.mono (Supp.addFVars_mono (by simp)))
  · refine .stateWF fun wf => ?_
    have hS' := T.tele.closed T.supp wf.lctxWF hS
    have hd := Dom.instantiateRev harr T.tele.dom hdom
    have hds := SuppIn.instantiateRev_fvars harr hse
    refine (inferType.SS T.agree hS' hd hds).bind fun r _ _ hr => .stateWF fun wf' => ?_
    exact (ensureSortCore.SS T.agree hS' (hr.dom wf' hd) (hr _ hS' hds)).bind
      fun _ _ _ _ => .pure trivial

theorem inferForall.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferForall e inferOnly) (inferForall e inferOnly)
      fun ty _ => SuppBelow c₁ e ty :=
  .of_swf (inferForall.SWF he)
    (inferForall.loop.SS (.nil hA) hS rfl he (hs.mono Supp.le_addFVars))

theorem inferLet.loop.SS {S : Supp} {c c₁ c₂ : Context} {s : State} {e : Expr}
    {arr : Array Expr} {xs : List FVarId} (T : TeleAgree S c c₁ c₂ xs) (hS : S.Closed c)
    (harr : arr.toList = xs.map .fvar) (hdom : Dom c₁ e) (hse : e.SuppIn (S.addFVars xs)) :
    RecM.SS c₁ c₂ s (inferLet.loop inferOnly arr e) (inferLet.loop inferOnly arr e)
      fun _ _ => True := by
  unfold inferLet.loop; split
  · rename_i name type val body _
    have ht : Dom c₁ (type.instantiateRev arr) :=
      Dom.instantiateRev harr T.tele.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have hv : Dom c₁ (val.instantiateRev arr) :=
      Dom.instantiateRev harr T.tele.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have hts := SuppIn.instantiateRev_fvars harr hse.1
    have hvs := SuppIn.instantiateRev_fvars harr hse.2.1
    have main {s₁} : RecM.SS c₁ c₂ s₁
        (withLetDecl name (type.instantiateRev arr) (val.instantiateRev arr) fun fv =>
          inferLet.loop inferOnly (arr.push fv) body)
        (withLetDecl name (type.instantiateRev arr) (val.instantiateRev arr) fun fv =>
          inferLet.loop inferOnly (arr.push fv) body) fun _ _ => True := by
      refine .stateWF fun wf => ?_
      refine .withLetDecl ht hv (fun f₁ => ?_) (fun f₁ f₂ => ?_) T.agree.wf
      all_goals
        have E := wf.ctxExtLet f₁ (name := name) (ty := type.instantiateRev arr)
          (val := val.instantiateRev arr)
      · exact inferLet.loop.SS ((T.self wf.lctxWF).pushLet wf hts hvs E.fresh E.fresh) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.2.mono (Supp.addFVars_mono (by simp)))
      · exact inferLet.loop.SS (T.pushLet wf hts hvs f₁ f₂) hS (by simp [harr]) (fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))) (hse.2.2.mono (Supp.addFVars_mono (by simp)))
    split
    · refine .stateWF fun wf => ?_
      have hS' := T.tele.closed T.supp wf.lctxWF hS
      refine (inferType.SS T.agree hS' ht hts).bind fun ty _ _ hty => .stateWF fun wf => ?_
      refine (ensureSortCore.SS T.agree hS' (hty.dom wf ht) (hty _ hS' hts)).bind
        fun _ _ _ _ => ?_
      refine (inferType.SS T.agree hS' hv hvs).bind fun vty _ _ hvty => .stateWF fun wf => ?_
      refine (isDefEq.SS T.agree hS' (hvty.dom wf hv) ht (hvty _ hS' hvs) hts).bind
        fun _ _ _ _ => ?_
      split
      · exact .fail (.getEnv <| .getLCtx .throw)
      · exact main
    · exact main
  · refine .stateWF fun wf => ?_
    have hS' := T.tele.closed T.supp wf.lctxWF hS
    refine (inferType.SS T.agree hS' (Dom.instantiateRev harr T.tele.dom hdom)
      (SuppIn.instantiateRev_fvars harr hse)).bind fun r _ _ _ => ?_
    have : arr = ⟨xs.map .fvar⟩ := by cases arr; simp_all
    subst this
    refine .getLCtx ?_
    rw [T.mkForall]; exact .pure trivial

theorem inferLet.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferLet e inferOnly) (inferLet e inferOnly)
      fun ty _ => SuppBelow c₁ e ty :=
  .of_swf (inferLet.SWF he)
    (inferLet.loop.SS (.nil hA) hS rfl he (hs.mono Supp.le_addFVars))

theorem inferApp.loop.SS {S : Supp} {c₁ c₂ : Context} {s : State} {e fType : Expr}
    {args : Array Expr} (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (he : Dom c₁ e)
    (hs : e.SuppIn S) (hargs : ∀ S, S.Closed c₁ → e.SuppIn S → ∀ a ∈ args, a.SuppIn S)
    (hf : SuppBelow c₁ e fType) :
    RecM.SS c₁ c₂ s (inferApp.loop e args fType j i) (inferApp.loop e args fType j i)
      fun _ _ => True := by
  rw [inferApp.loop.eq_def]; split
  · split
    · exact inferApp.loop.SS hA hS he hs hargs fun S hS h => (hf S hS h).2
    · refine .stateWF fun wf => ?_
      have hd : Dom c₁ (fType.instantiateRevRange j i args) := by
        have hS := wf.closedDom
        exact dom_iff.2 <| Expr.SuppIn.instantiateRevRange (hargs _ hS (dom_iff.1 he))
          (hf _ hS (dom_iff.1 he))
      have hds := Expr.SuppIn.instantiateRevRange (hargs S hS hs) (hf S hS hs)
        (i := j) (j := i)
      refine (ensureForallCore.SS hA hS hd hds).bind fun r _ _ hr => ?_
      refine inferApp.loop.SS hA hS he hs hargs fun S hS h => ?_
      exact Expr.SuppIn.bindingBody! hS.2.dummy <| hr S hS <|
        Expr.SuppIn.instantiateRevRange (hargs S hS h) (hf S hS h)
  · exact .pure trivial
termination_by args.size - i

theorem inferApp.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferApp e) (inferApp e) fun ty _ => SuppBelow c₁ e ty := by
  refine .of_swf (Q' := fun _ _ => True) (inferApp.SWF he) ?_
  rw [inferApp, Expr.withApp_eq]
  have hf : Dom c₁ e.getAppFn := dom_iff.2 (Expr.SuppIn.getAppFn (dom_iff.1 he))
  refine (inferType.SS hA hS hf hs.getAppFn).bind fun ty _ _ hty => ?_
  exact inferApp.loop.SS hA hS he hs (fun S _ h => Expr.SuppIn.getAppArgs h)
    fun S hS h => hty S hS (Expr.SuppIn.getAppFn h)

theorem getSortLevel.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (getSortLevel e) (getSortLevel e)
      fun u _ => ∀ S, S.Closed c₁ → e.SuppIn S → u.LParamsIn S.lvl := by
  refine .of_swf (Q' := fun _ _ => True) (getSortLevel.SWF he) ?_
  unfold getSortLevel
  refine (inferType.SS hA hS he hs).bind fun ty _ _ hty => .stateWF fun wf => ?_
  refine (ensureSortCore.SS hA hS (hty.dom wf he) (hty _ hS hs)).bind fun r _ _ hr => ?_
  split
  · exact .pure (Q := fun _ _ => True) trivial
  · exact .panic trivial

theorem isProp.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (isProp e) (isProp e) fun _ _ => True :=
  (getSortLevel.SS hA hS he hs).bind fun _ _ _ _ => .pure trivial

theorem inferProj.SS {S : Supp} {c₁ c₂ : Context} {s : State} {struct structType : Expr}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁)
    (hd : Dom c₁ struct) (hdt : Dom c₁ structType) (hst : SuppBelow c₁ struct structType)
    (hs : (Expr.proj typeName idx struct).SuppIn S) :
    RecM.SS c₁ c₂ s (inferProj typeName idx struct structType)
      (inferProj typeName idx struct structType) fun ty _ =>
      SuppBelow c₁ (.proj typeName idx struct) ty := by
  rw [inferProj.eq_1]
  refine (whnf.SS hA hS hdt (hst S hS hs)).bind fun type _ _ htype => ?_
  rw [Expr.withApp_eq]
  refine .getEnv ?_
  dsimp only
  split
  · rename_i I_name I_levels heq
    have hI S (hS : S.Closed c₁) (h : (Expr.proj typeName idx struct).SuppIn S) :
        type.SuppIn S :=
      htype S hS (hst S hS h)
    have hIS : S.const I_name := (heq ▸ (hI S hS hs).getAppFn : Expr.SuppIn S (.const _ _)).1
    by_cases h1 : (typeName != I_name) = true
    · rw [if_pos h1, if_pos h1]; exact .failBind
    rw [if_neg h1, if_neg h1]
    refine (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hIS)).bind fun ci _ _ hci => ?_
    split
    · rename_i I_val
      split
      · rename_i ctor hctor
        by_cases h2 : (type.getAppArgs.size != I_val.numParams + I_val.numIndices) = true
        · rw [if_pos h2, if_pos h2]; exact .failBind
        rw [if_neg h2, if_neg h2]
        have hcS : S.const ctor := (hS.2.find _ _ hci hIS).2 ctor (by simp [hctor])
        refine (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hcS)).bind fun ci' _ _ hci' => ?_
        split <;> [rename_i cval; exact .fail (RecM.SWF.getLCtx .throw)]
        by_cases h3 : idx ≥ cval.numFields
        · rw [if_pos h3, if_pos h3]; exact .failBind
        rw [if_neg h3, if_neg h3]
        by_cases h4 : ((ConstantInfo.ctorInfo cval).levelParams.length != I_levels.length) = true
        · rw [if_pos h4, if_pos h4]; exact .failBind
        rw [if_neg h4, if_neg h4]
        have hlen := h4
        let P r := SuppBelow c₁ (.proj typeName idx struct) r
        have hdP : Dom c₁ (.proj typeName idx struct) := hd
        have hP {s r} (wf : SuppState c₁ s) (h : P r) : Dom c₁ r := h.dom wf hdP
        have hfacts S (hS : S.Closed c₁) (h : (Expr.proj typeName idx struct).SuppIn S) :
            S.const I_name ∧ (∀ a ∈ type.getAppArgs, a.SuppIn S) ∧
            ((ConstantInfo.ctorInfo cval).instantiateTypeLevelParams I_levels).SuppIn S := by
          have h1 := hI S hS h
          have h2 : Expr.SuppIn S (.const I_name I_levels) := heq ▸ h1.getAppFn
          have h3 := (hS.2.find _ _ hci h2.1).2 ctor (by simp [hctor])
          have h4 := (hS.2.find _ _ hci' h3).1
          refine ⟨h2.1, h1.getAppArgs,
            Expr.SuppIn.instantiateLevelParams (h4.noFV (F := S.fv)) h2.2 ?_⟩
          simpa [ConstantInfo.levelParams] using hlen
        refine (RecM.SS.forIn_range (Inv := P) (fun i r s hr => .stateWF fun wf => ?_)
          fun S hS h => (hfacts S hS h).2.2).bind fun r _ _ hr => ?_
        · refine (whnf.SS hA hS (hP wf hr) (hr S hS hs)).bind fun x _ _ hx => ?_
          split
          · exact .pure ⟨_, rfl, fun S hS h => Expr.SuppIn.inst1
              (Expr.SuppIn.getElem! hS.2.dummy (hfacts S hS h).2.1) (hx S hS (hr S hS h)).2⟩
          · exact .failBind
        refine .stateWF fun wf => (getSortLevel.SS hA hS
          (dom_iff.2 (hI _ wf.closedDom (dom_iff.1 hdP))) (hI S hS hs)).bind fun u _ _ _ => ?_
        refine (RecM.SS.forIn_range (Inv := P) (fun i r s hr => .stateWF fun wf => ?_) hr).bind
          fun r _ _ hr => .stateWF fun wf => ?_
        · refine (whnf.SS hA hS (hP wf hr) (hr S hS hs)).bind fun x _ _ hx => .stateWF fun wf => ?_
          split
          · rename_i dom b _
            have hdom : P dom := fun S hS h => (hx S hS (hr S hS h)).1
            have hb : P (b.instantiate1 (.proj I_name i struct)) := fun S hS h =>
              Expr.SuppIn.inst1 h (hx S hS (hr S hS h)).2
            split
            · split
              · refine (isProp.SS hA hS (hP wf hdom) (hdom S hS hs)).bind fun _ _ _ _ => ?_
                split
                · exact .failBind
                · exact .pure ⟨_, rfl, hb⟩
              · exact .pure ⟨_, rfl, hb⟩
            · exact .pure ⟨_, rfl, fun S hS h => (hx S hS (hr S hS h)).2⟩
          · exact .failBind
        refine (whnf.SS hA hS (hP wf hr) (hr S hS hs)).bind fun x _ _ hx => .stateWF fun wf => ?_
        split
        · rename_i dom b _
          have hdom : P dom := fun S hS h => (hx S hS (hr S hS h)).1
          split
          · refine (isProp.SS hA hS (hP wf hdom) (hdom S hS hs)).bind fun _ _ _ _ => ?_
            split
            · exact .failBind
            · exact .pure hdom
          · exact .pure hdom
        · exact .fail (.getLCtx .throw)
      · exact .fail (.getLCtx .throw)
    · exact .fail (.getLCtx .throw)
  · exact .fail (.getLCtx .throw)

mutual
theorem inferTypeCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} {e : Expr}
    (hb : e.hasLooseBVars = false)
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferTypeCore e inferOnly) (inferTypeCore e inferOnly)
      fun ty _ => SuppBelow c₁ e ty := by
  refine .of_swf (Q' := fun _ _ => True) (inferTypeCore.SWF hb he) ?_
  unfold inferTypeCore; lift_lets; intro F
  generalize hP : (fun _ (_ : State) => _) = P
  have hF {ty s} (H : SuppBelow c₁ e ty) : RecM.SS c₁ c₂ s (F ty) (F ty) P := .pure (hP ▸ trivial)
  have sub {e'} (h : ∀ fv ∈ e'.fvarsList, fv ∈ e.fvarsList) : Dom c₁ e' :=
    fun fv h' => he fv (h fv h')
  split
  · rename_i l
    have H : SuppBelow c₁ (.lit l) (mkConst l.typeName) := by
      intro S _ h; cases l <;> exact ⟨h.1, nofun⟩
    extract_lets G1; split <;> [split; skip]
    · refine .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hs.1)).bind
        fun _ _ _ _ => hF H
    · refine .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hs.2.2.2.1)).bind
        fun _ _ _ _ => ?_
      exact .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hs.2.1)).bind
        fun _ _ _ _ => hF H
    · exact hF H
  · rename_i e
    exact (inferType'.SS (e := e) hA hS he hs).bind fun _ _ _ h => hF h
  · rename_i st idx e
    have he' : Dom c₁ e := he
    refine (inferType'.SS hA hS he' hs).bind fun ty _ _ h => .stateWF fun wf => ?_
    exact (inferProj.SS hA hS he' (h.dom wf he') h hs).bind fun _ _ _ h => hF h
  · exact .readThe <| (RecM.SS.liftExcept inferFVar.SWF (inferFVar_agree hA hs)).bind
      fun _ _ _ h => hF h
  · exact .throw
  · simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at hb
  · rename_i u
    have H : SuppBelow c₁ (.sort u) (.sort (.succ u)) := fun S _ h =>
      (h : Level.LParamsIn S.lvl u)
    split
    · refine .readThe <| (RecM.SS.liftExcept (Q := fun _ => True) (fun _ _ => trivial)
        fun _ h => ?_).bind fun _ _ _ _ => hF H
      exact checkLevel_agree hA (show Level.LParamsIn S.lvl u from hs) _ h
    · exact hF H
  · exact .readThe <| (RecM.SS.liftExcept inferConstant.SWF (inferConstant_agree hA hs.1 hs.2)).bind
      fun _ _ _ h => hF h
  · exact (inferLambda.SS hA hS he hs).bind fun _ _ _ h => hF h
  · exact (inferForall.SS hA hS he hs).bind fun _ _ _ h => hF h
  · rename_i f a
    have hf : Dom c₁ f := sub fun fv h => by simp [Expr.fvarsList, h]
    have ha : Dom c₁ a := sub fun fv h => by simp [Expr.fvarsList, h]
    split
    · exact (inferApp.SS hA hS he hs).bind fun _ _ _ h => hF h
    refine (inferType'.SS hA hS hf hs.1).bind fun fty _ _ hfty => .stateWF fun wf => ?_
    refine (ensureForallCore.SS hA hS (hfty.dom wf hf) (hfty _ hS hs.1)).bind
      fun fty' _ _ hfty' => .stateWF fun wf => ?_
    have hfty'' : SuppBelow c₁ f fty' := hfty.trans hfty'
    have hd : Dom c₁ fty'.bindingDomain! := dom_iff.2 <| Expr.SuppIn.bindingDomain! trivial <|
      dom_iff.1 (hfty''.dom wf hf)
    have hds := Expr.SuppIn.bindingDomain! hS.2.dummy (hfty'' S hS hs.1)
    extract_lets _ G1
    refine (inferType'.SS hA hS ha hs.2).bind fun aty _ _ haty => .stateWF fun wf => ?_
    extract_lets G2
    suffices ∀ {s b}, RecM.SS c₁ c₂ s (G2 b) (G2 b) P by
      split
      · exact (RecM.SS.withEagerReduce (isDefEq.SS hA.eagerReduce' hS hd (haty.dom wf ha) hds
          (haty _ hS hs.2))).bind fun b _ _ _ => this
      · exact (isDefEq.SS hA hS hd (haty.dom wf ha) hds (haty _ hS hs.2)).bind
          fun b _ _ _ => this
    intro s b; subst G2; dsimp only; split
    · exact .fail (.getEnv <| .getLCtx .throw)
    · refine hF fun S hS h => ?_
      exact Expr.SuppIn.inst1 h.2 <| Expr.SuppIn.bindingBody! hS.2.dummy (hfty'' S hS h.1)
  · exact (inferLet.SS hA hS he hs).bind fun _ _ _ h => hF h


theorem inferType'.SS {S : Supp} {c₁ c₂ : Context} {s : State} {e : Expr}
    (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inferType' e inferOnly) (inferType' e inferOnly)
      fun ty _ => SuppBelow c₁ e ty := by
  refine .of_swf (Q' := fun _ _ => True) (inferType'.SWF he) ?_
  unfold inferType'
  split <;> [exact .throw; (rename_i hb; refine .get <| .readThe ?_)]
  generalize ho : (cond inferOnly s.inferTypeI s.inferTypeC)[e]? = o
  refine RecM.SS.cached' hA (fun _ _ _ => ?_) (fun _ _ => ?_) (fun _ => ?_)
  · exact RecM.SS.taintWith.bind fun _ _ _ _ => .pure (Q := fun _ _ => True) trivial
  · exact RecM.SWF.taintWith'.bind fun _ _ _ h => .pure h
  refine (RecM.SS.withTaint fun _ =>
    inferTypeCore.SS (by simpa using hb) hA hS he hs).bind fun ⟨ty, t⟩ _ _ H => ?_
  refine fun m hm => ⟨?_, fun _ _ _ eq _ _ => eq⟩
  rintro wf a s' ⟨⟩
  have hc := CondSupp.of wf he H
  cases inferOnly
  · exact ⟨{ wf with inferTypeC := CondSupp.insert wf.inferTypeC hc }, .rfl, ⟨Nat.le_refl _, rfl, .refl _ _⟩, trivial⟩
  · exact ⟨{ wf with inferTypeI := CondSupp.insert wf.inferTypeI hc }, .rfl, ⟨Nat.le_refl _, rfl, .refl _ _⟩, trivial⟩
end

end Inner
end TypeChecker
end Lean4Lean

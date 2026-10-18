import Lean4Lean.Verify.Support.TypeChecker

/-!
# Support of inferred types

Each binder the type checker opens extends the context by a fresh variable declared in terms of
the input; `Tele` tracks these, so that the binders can be abstracted again at the end.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem _root_.Lean.LocalContext.WF.find?_fvarId {lctx : LocalContext} (H : lctx.WF)
    (h : lctx.find? x = some d) : d.fvarId = x := by
  rw [H.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; exact this.symm

namespace TypeChecker

/-- `c'` extends `c` by the variables `xs`. -/
structure Tele (c c' : Context) (xs : List FVarId) : Prop where
  env : c'.env = c.env
  find : ∀ y, y ∉ xs → c'.lctx.find? y = c.lctx.find? y
  dom : ∀ x ∈ xs, c'.lctx.Dom x

/-- Each of the variables `xs` is declared in terms of the ones before it and what `S` allows. -/
def TeleSupp (c' : Context) (xs : List FVarId) (S : Supp) : Prop :=
  ∀ i (hi : i < xs.length) d, c'.lctx.find? xs[i] = some d → d.SuppIn (S.addFVars (xs.take i))

theorem Tele.nil {c : Context} : Tele c c [] := ⟨rfl, fun _ _ => rfl, nofun⟩

theorem TeleSupp.nil {c : Context} {S : Supp} : TeleSupp c [] S := fun _ h => nomatch h

theorem Tele.closed {c c' : Context} {xs : List FVarId} {S : Supp} (H : Tele c c' xs)
    (HS : TeleSupp c' xs S) (hwf : c'.lctx.WF) (hS : S.Closed c) : (S.addFVars xs).Closed c' := by
  refine ⟨fun y d hy h => ?_, H.env ▸ ⟨fun n ci h1 h2 => hS.2.find n ci h1 h2, hS.2.nat,
    hS.2.bool, hS.2.dummy⟩⟩
  by_cases hx : y ∈ xs
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := LocalDecl.SuppIn.mono (S := S.addFVars (xs.take i)) (S' := S.addFVars xs)
      ⟨fun z (hz : S.fv z ∨ z ∈ xs.take i) => hz.imp id (List.mem_of_mem_take ·), fun _ => id,
        fun _ => id⟩ (HS i hi d h)
    cases d with
    | cdecl =>
      have e : _ = xs[i] := hwf.find?_fvarId h
      simp only [LocalDecl.fvarId] at e
      exact ⟨this, .inr (e ▸ hx)⟩
    | ldecl => exact this
  · rw [H.find y hx] at h
    have := hS.1 y d (hy.resolve_right hx) h
    exact ⟨this.1.mono Supp.le_addFVars, this.2.mono Supp.le_addFVars⟩

theorem Tele.ne {c c' c'' : Context} {xs : List FVarId} (H : Tele c c' xs) {x : FVarId}
    (E : CtxExt c' c'' x) : ∀ y ∈ xs, y ≠ x := by
  rintro y hy rfl; have := H.dom y hy; simp [LocalContext.Dom, E.fresh] at this

theorem Tele.push {c c' c'' : Context} {xs : List FVarId} (H : Tele c c' xs)
    {x : FVarId} (E : CtxExt c' c'' x) : Tele c c'' (xs ++ [x]) := by
  refine ⟨E.env.trans H.env, fun y hy => ?_, fun y hy => ?_⟩
  · simp at hy; rw [E.find y hy.2, H.find y hy.1]
  · simp at hy; obtain hy | rfl := hy
    · exact E.dom_of (H.dom y hy)
    · exact E.dom

theorem TeleSupp.push {c c' c'' : Context} {xs : List FVarId} {S : Supp} (H : Tele c c' xs)
    (HS : TeleSupp c' xs S) {x : FVarId} (E : CtxExt c' c'' x)
    (hx : ∀ d, c''.lctx.find? x = some d → d.SuppIn (S.addFVars xs)) :
    TeleSupp c'' (xs ++ [x]) S := by
  intro i hi d h
  simp at hi
  by_cases hi' : i < xs.length
  · rw [List.getElem_append_left hi'] at h
    rw [E.find _ (H.ne E _ (List.getElem_mem hi'))] at h
    rw [List.take_append_of_le_length (Nat.le_of_lt hi')]
    exact HS i hi' d h
  · have : i = xs.length := by omega
    subst this
    simp at h ⊢
    exact hx d h

theorem _root_.Lean4Lean.Supp.addFVars_mono {S : Supp} {xs ys : List FVarId} (h : xs ⊆ ys) :
    S.addFVars xs ≤ S.addFVars ys :=
  ⟨fun _ (hz : _ ∨ _) => hz.imp id (h ·), fun _ => id, fun _ => id⟩

theorem dom_iff {c : Context} {e : Expr} : Dom c e ↔ e.SuppIn (Supp.dom c) :=
  Expr.suppIn_fvars.symm

theorem Dom.instantiateRev {c : Context} {e : Expr} {arr : Array Expr} {xs : List FVarId}
    (harr : arr.toList = xs.map .fvar) (hxs : ∀ x ∈ xs, c.lctx.Dom x) (he : Dom c e) :
    Dom c (e.instantiateRev arr) := by
  refine dom_iff.2 (Expr.SuppIn.instantiateRev (fun a ha => ?_) (dom_iff.1 he))
  rw [← Array.mem_toList_iff, harr] at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  exact hxs x hx

theorem SuppIn.instantiateRev_fvars {S : Supp} {e : Expr} {arr : Array Expr} {xs : List FVarId}
    (harr : arr.toList = xs.map .fvar) (he : e.SuppIn (S.addFVars xs)) :
    (e.instantiateRev arr).SuppIn (S.addFVars xs) := by
  refine Expr.SuppIn.instantiateRev (fun a ha => ?_) he
  rw [← Array.mem_toList_iff, harr] at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  exact .inr hx

theorem _root_.Lean.Level.LParamsIn.sortLevel! {S : Supp} {e : Expr} (h : e.SuppIn S) :
    e.sortLevel!.LParamsIn S.lvl := by
  cases e <;> first | exact h | exact (show Level.LParamsIn _ .zero from trivial)

theorem _root_.Lean.Level.LParamsIn.foldr_imax {P : Name → Prop} {us : Array Level} {v : Level}
    (hus : ∀ u ∈ us.toList, u.LParamsIn P) (hv : v.LParamsIn P) :
    (us.foldr mkLevelIMax' v).LParamsIn P := by
  rw [← Array.foldr_toList]
  generalize us.toList = l at hus ⊢
  induction l with
  | nil => exact hv
  | cons u us ih =>
    simp at hus ⊢
    exact Level.LParamsIn.mkLevelIMax' hus.1 (ih hus.2)

namespace Inner

theorem inferLambda.loop.SWF {c c' : Context} {s : State} {e₀ e : Expr} {arr : Array Expr}
    {xs : List FVarId} (T : Tele c c' xs) (harr : arr.toList = xs.map .fvar) (hdom : Dom c' e)
    (H : ∀ S, S.Closed c → e₀.SuppIn S → TeleSupp c' xs S ∧ e.SuppIn (S.addFVars xs)) :
    (inferLambda.loop inferOnly arr e).SWF c' s fun ty _ => SuppBelow c e₀ ty := by
  unfold inferLambda.loop; split
  · rename_i name dom body bi
    have hd : Dom c' (dom.instantiateRev arr) :=
      Dom.instantiateRev harr T.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have main {s₁} : RecM.SWF c' s₁ (withLocalDecl name bi (dom.instantiateRev arr) fun fv =>
        inferLambda.loop inferOnly (arr.push fv) body) fun ty _ => SuppBelow c e₀ ty := by
      refine .stateWF fun wf => .withLocalDecl hd ?_
      have E := wf.ctxExt (name := name) (ty := dom.instantiateRev arr) (bi := bi)
      refine inferLambda.loop.SWF (T.push E) (by simp [harr]) ?_ fun S hS he => ?_
      · exact fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))
      · have ⟨HS, h1, h2⟩ := H S hS he
        refine ⟨HS.push T E fun d hd => ?_, h2.mono (Supp.addFVars_mono (by simp))⟩
        simp only [LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
          Option.some.injEq] at hd; subst hd
        exact SuppIn.instantiateRev_fvars harr h1
    split
    · refine (inferType.SWF hd).bind fun ty _ _ hty => .stateWF fun wf => ?_
      exact (ensureSortCore.SWF (hty.dom wf hd)).bind fun _ _ _ _ => main
    · exact main
  · refine .stateWF fun wf => ?_
    refine (inferType.SWF (Dom.instantiateRev harr T.dom hdom)).bind fun r _ _ hr => ?_
    refine .getLCtx (.pure fun S hS he => ?_)
    have ⟨HS, h1⟩ := H S hS he
    have hS' := T.closed HS wf.lctxWF hS
    have hr' := hr _ hS' (SuppIn.instantiateRev_fvars harr h1)
    have : arr = ⟨xs.map .fvar⟩ := by cases arr; simp_all
    rw [this]; exact mkForall_supp hS.2.dummy HS (hr'.cheapBetaReduce hS'.2.dummy)

theorem inferLambda.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (inferLambda e inferOnly).SWF c s fun ty _ => SuppBelow c e ty :=
  inferLambda.loop.SWF .nil rfl he fun _ _ h => ⟨.nil, h.mono Supp.le_addFVars⟩

theorem inferForall.loop.SWF {c c' : Context} {s : State} {e₀ e : Expr} {arr : Array Expr}
    {us : Array Level} {xs : List FVarId} (T : Tele c c' xs) (harr : arr.toList = xs.map .fvar)
    (hdom : Dom c' e)
    (H : ∀ S, S.Closed c → e₀.SuppIn S → TeleSupp c' xs S ∧ e.SuppIn (S.addFVars xs) ∧
      ∀ u ∈ us.toList, u.LParamsIn S.lvl) :
    (inferForall.loop inferOnly arr us e).SWF c' s fun ty _ => SuppBelow c e₀ ty := by
  unfold inferForall.loop; split
  · rename_i name dom body bi
    have hd : Dom c' (dom.instantiateRev arr) :=
      Dom.instantiateRev harr T.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    refine .stateWF fun wf => (inferType.SWF hd).bind fun ty _ _ hty => .stateWF fun wf₁ => ?_
    refine (ensureSortCore.SWF (hty.dom wf₁ hd)).bind fun t1 s₁ _ ht1 => ?_
    refine .stateWF fun wf => .withLocalDecl hd ?_
    have E := wf.ctxExt (name := name) (ty := dom.instantiateRev arr) (bi := bi) (s := s₁)
    refine inferForall.loop.SWF (T.push E) (by simp [harr]) ?_ fun S hS he => ?_
    · exact fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))
    · have ⟨HS, ⟨h1, h2⟩, h3⟩ := H S hS he
      have hS' := T.closed HS wf.lctxWF hS
      have hd' := SuppIn.instantiateRev_fvars harr h1
      refine ⟨HS.push T E fun d hd => ?_, h2.mono (Supp.addFVars_mono (by simp)), ?_⟩
      · simp only [LocalContext.find?_mkLocalDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
          Option.some.injEq] at hd; subst hd
        exact hd'
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        rintro u (hu | rfl)
        · exact h3 u hu
        · exact Level.LParamsIn.sortLevel! (S := S.addFVars xs) (ht1 _ hS' (hty _ hS' hd'))
  · refine .stateWF fun wf => ?_
    have hd := Dom.instantiateRev harr T.dom hdom
    refine (inferType.SWF hd).bind fun r _ _ hr => .stateWF fun wf₁ => ?_
    refine (ensureSortCore.SWF (hr.dom wf₁ hd)).bind fun r' _ _ hr' => .pure fun S hS he => ?_
    have ⟨HS, h1, h2⟩ := H S hS he
    have hS' := T.closed HS wf.lctxWF hS
    exact Level.LParamsIn.foldr_imax h2 <| Level.LParamsIn.sortLevel! (S := S.addFVars xs) <|
      hr' _ hS' (hr _ hS' (SuppIn.instantiateRev_fvars harr h1))

theorem inferForall.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (inferForall e inferOnly).SWF c s fun ty _ => SuppBelow c e ty :=
  inferForall.loop.SWF .nil rfl he fun _ _ h => ⟨.nil, h.mono Supp.le_addFVars, nofun⟩

theorem inferLet.loop.SWF {c c' : Context} {s : State} {e₀ e : Expr} {arr : Array Expr}
    {xs : List FVarId} (T : Tele c c' xs) (harr : arr.toList = xs.map .fvar) (hdom : Dom c' e)
    (H : ∀ S, S.Closed c → e₀.SuppIn S → TeleSupp c' xs S ∧ e.SuppIn (S.addFVars xs)) :
    (inferLet.loop inferOnly arr e).SWF c' s fun ty _ => SuppBelow c e₀ ty := by
  unfold inferLet.loop; split
  · rename_i name type val body _
    have ht : Dom c' (type.instantiateRev arr) :=
      Dom.instantiateRev harr T.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have hv : Dom c' (val.instantiateRev arr) :=
      Dom.instantiateRev harr T.dom fun fv h => hdom fv (by simp [Expr.fvarsList, h])
    have main {s₁} : RecM.SWF c' s₁ (withLetDecl name (type.instantiateRev arr)
        (val.instantiateRev arr) fun fv => inferLet.loop inferOnly (arr.push fv) body)
        fun ty _ => SuppBelow c e₀ ty := by
      refine .stateWF fun wf => .withLetDecl ht hv ?_
      have E := wf.ctxExtLet (name := name) (ty := type.instantiateRev arr)
        (val := val.instantiateRev arr)
      refine inferLet.loop.SWF (T.push E) (by simp [harr]) ?_ fun S hS he => ?_
      · exact fun fv h => E.dom_of (hdom fv (by simp [Expr.fvarsList, h]))
      · have ⟨HS, h1, h2, h3⟩ := H S hS he
        refine ⟨HS.push T E fun d hd => ?_, h3.mono (Supp.addFVars_mono (by simp))⟩
        simp only [LocalContext.find?_mkLetDecl wf.lctxWF E.fresh, beq_self_eq_true, if_true,
          Option.some.injEq] at hd; subst hd
        exact ⟨SuppIn.instantiateRev_fvars harr h1, SuppIn.instantiateRev_fvars harr h2⟩
    split
    · refine (inferType.SWF ht).bind fun ty _ _ hty => .stateWF fun wf => ?_
      refine (ensureSortCore.SWF (hty.dom wf ht)).bind fun _ _ _ _ => ?_
      refine (inferType.SWF hv).bind fun vty _ _ hvty => .stateWF fun wf => ?_
      refine (isDefEq.SWF (hvty.dom wf hv) ht).bind fun _ _ _ _ => ?_
      split
      · exact .getEnv <| .getLCtx .throw
      · exact main
    · exact main
  · refine .stateWF fun wf => ?_
    refine (inferType.SWF (Dom.instantiateRev harr T.dom hdom)).bind fun r _ _ hr => ?_
    refine .getLCtx (.pure fun S hS he => ?_)
    have ⟨HS, h1⟩ := H S hS he
    have hS' := T.closed HS wf.lctxWF hS
    have hr' := hr _ hS' (SuppIn.instantiateRev_fvars harr h1)
    have : arr = ⟨xs.map .fvar⟩ := by cases arr; simp_all
    rw [this]; exact mkForall_supp hS.2.dummy HS (hr'.cheapBetaReduce hS'.2.dummy)

theorem inferLet.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (inferLet e inferOnly).SWF c s fun ty _ => SuppBelow c e ty :=
  inferLet.loop.SWF .nil rfl he fun _ _ h => ⟨.nil, h.mono Supp.le_addFVars⟩

theorem inferApp.loop.SWF {c : Context} {s : State} {e fType : Expr} {args : Array Expr}
    (he : Dom c e) (hargs : ∀ S, S.Closed c → e.SuppIn S → ∀ a ∈ args, a.SuppIn S)
    (hf : SuppBelow c e fType) :
    (inferApp.loop e args fType j i).SWF c s fun ty _ => SuppBelow c e ty := by
  rw [inferApp.loop.eq_def]; split
  · split
    · exact inferApp.loop.SWF he hargs fun S hS h => (hf S hS h).2
    · refine .stateWF fun wf => ?_
      have hd : Dom c (fType.instantiateRevRange j i args) := by
        have hS := wf.closedDom
        exact dom_iff.2 <| Expr.SuppIn.instantiateRevRange (hargs _ hS (dom_iff.1 he))
          (hf _ hS (dom_iff.1 he))
      refine (ensureForallCore.SWF hd).bind fun r _ _ hr => ?_
      refine inferApp.loop.SWF he hargs fun S hS h => ?_
      exact Expr.SuppIn.bindingBody! hS.2.dummy <| hr S hS <|
        Expr.SuppIn.instantiateRevRange (hargs S hS h) (hf S hS h)
  · exact .pure fun S hS h => Expr.SuppIn.instantiateRevRange (hargs S hS h) (hf S hS h)
termination_by args.size - i

theorem inferApp.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (inferApp e).SWF c s fun ty _ => SuppBelow c e ty := by
  rw [inferApp, Expr.withApp_eq]
  have hf : Dom c e.getAppFn := dom_iff.2 (Expr.SuppIn.getAppFn (dom_iff.1 he))
  refine (inferType.SWF hf).bind fun ty _ _ hty => ?_
  exact inferApp.loop.SWF he (fun S _ h => Expr.SuppIn.getAppArgs h)
    fun S hS h => hty S hS (Expr.SuppIn.getAppFn h)

theorem getSortLevel.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (getSortLevel e).SWF c s fun u _ => ∀ S, S.Closed c → e.SuppIn S → u.LParamsIn S.lvl := by
  unfold getSortLevel
  refine (inferType.SWF he).bind fun ty _ _ hty => .stateWF fun wf => ?_
  refine (ensureSortCore.SWF (hty.dom wf he)).bind fun r _ _ hr => ?_
  split
  · exact .pure fun S hS h => (hr S hS (hty S hS h) : Expr.SuppIn _ (.sort _))
  · exact .panic fun _ _ _ => trivial

theorem isProp.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (isProp e).SWF c s fun _ _ => True :=
  (getSortLevel.SWF he).bind fun _ _ _ _ => .pure trivial

theorem inferProj.SWF {c : Context} {s : State} {struct structType : Expr}
    (hd : Dom c struct) (hdt : Dom c structType) (hst : SuppBelow c struct structType) :
    (inferProj typeName idx struct structType).SWF c s fun ty _ =>
      SuppBelow c (.proj typeName idx struct) ty := by
  rw [inferProj.eq_1]
  refine (whnf.SWF hdt).bind fun type _ _ htype => ?_
  rw [Expr.withApp_eq]
  refine .getEnv ?_
  dsimp only
  split
  · rename_i I_name I_levels heq
    have hI S (hS : S.Closed c) (h : (Expr.proj typeName idx struct).SuppIn S) : type.SuppIn S :=
      htype S hS (hst S hS h)
    split; · exact .failBind
    refine (M.SWF.liftExcept envGet.SWF).lift.bind fun ci _ _ hci => ?_
    split
    · rename_i I_val
      split
      · rename_i ctor hctor
        split; · exact .failBind
        refine (M.SWF.liftExcept envGet.SWF).lift.bind fun ci' _ _ hci' => ?_
        split; · exact .failBind
        rename_i hlen
        let P r := SuppBelow c (.proj typeName idx struct) r
        have hdP : Dom c (.proj typeName idx struct) := hd
        have hP {s r} (wf : SuppState c s) (h : P r) : Dom c r := h.dom wf hdP
        have hfacts S (hS : S.Closed c) (h : (Expr.proj typeName idx struct).SuppIn S) :
            S.const I_name ∧ (∀ a ∈ type.getAppArgs, a.SuppIn S) ∧
            (ci'.instantiateTypeLevelParams I_levels).SuppIn S := by
          have h1 := hI S hS h
          have h2 : Expr.SuppIn S (.const I_name I_levels) := heq ▸ h1.getAppFn
          have h3 := (hS.2.find _ _ hci h2.1).2 ctor (by simp [hctor])
          have h4 := (hS.2.find _ _ hci' h3).1
          refine ⟨h2.1, h1.getAppArgs, Expr.SuppIn.instantiateLevelParams (h4.noFV (F := S.fv)) h2.2 ?_⟩
          simpa [ConstantInfo.levelParams] using hlen
        refine (RecM.SWF.forIn_range (Inv := P) (fun i r s hr => .stateWF fun wf => ?_)
          fun S hS h => (hfacts S hS h).2.2).bind fun r _ _ hr => ?_
        · refine (whnf.SWF (hP wf hr)).bind fun x _ _ hx => ?_
          split
          · exact .pure ⟨_, rfl, fun S hS h => Expr.SuppIn.inst1
              (Expr.SuppIn.getElem! hS.2.dummy (hfacts S hS h).2.1) (hx S hS (hr S hS h)).2⟩
          · exact .failBind
        refine .stateWF fun wf => (getSortLevel.SWF (dom_iff.2 (hI _ wf.closedDom (dom_iff.1 hdP))))
          |>.bind fun u _ _ _ => ?_
        refine (RecM.SWF.forIn_range (Inv := P) (fun i r s hr => .stateWF fun wf => ?_) hr).bind
          fun r _ _ hr => .stateWF fun wf => ?_
        · refine (whnf.SWF (hP wf hr)).bind fun x _ _ hx => .stateWF fun wf => ?_
          split
          · rename_i dom b _
            have hdom : P dom := fun S hS h => (hx S hS (hr S hS h)).1
            have hb : P (b.instantiate1 (.proj I_name i struct)) := fun S hS h =>
              Expr.SuppIn.inst1 h (hx S hS (hr S hS h)).2
            split
            · split
              · refine (isProp.SWF (hP wf hdom)).bind fun _ _ _ _ => ?_
                split
                · exact .failBind
                · exact .pure ⟨_, rfl, hb⟩
              · exact .pure ⟨_, rfl, hb⟩
            · exact .pure ⟨_, rfl, fun S hS h => (hx S hS (hr S hS h)).2⟩
          · exact .failBind
        refine (whnf.SWF (hP wf hr)).bind fun x _ _ hx => .stateWF fun wf => ?_
        split
        · rename_i dom b _
          have hdom : P dom := fun S hS h => (hx S hS (hr S hS h)).1
          split
          · refine (isProp.SWF (hP wf hdom)).bind fun _ _ _ _ => ?_
            split
            · exact .failBind
            · exact .pure hdom
          · exact .pure hdom
        · exact .getLCtx .throw
      · exact .getLCtx .throw
    · exact .getLCtx .throw
  · exact .getLCtx .throw

theorem inferType'.SWF {c : Context} {s : State} {e : Expr} (he : Dom c e) :
    (inferType' e inferOnly).SWF c s fun ty _ => SuppBelow c e ty := by
  unfold inferType'; lift_lets; intro F F1
  split <;> [exact .throw; refine .get <| .get ?_]
  split
  · rename_i h; refine .stateWF fun wf => .pure ?_
    generalize hic : cond .. = ic at h
    have : ∀ e r, ic[e]? = some r → CondSupp c s.ngen e r := by
      subst ic; cases inferOnly <;> [exact wf.inferTypeC; exact wf.inferTypeI]
    exact fun S hS h' => (this _ _ h).2 S hS he h'
  generalize hP : (fun _ (_ : State) => _) = P
  have hF {ty s} (H : SuppBelow c e ty) : (F ty).SWF c s P := by
    rintro _ _ wf a s' ⟨⟩
    have hc := CondSupp.of wf he H
    subst P; cases inferOnly
    · exact ⟨{ wf with inferTypeC := CondSupp.insert wf.inferTypeC hc }, .rfl, H⟩
    · exact ⟨{ wf with inferTypeI := CondSupp.insert wf.inferTypeI hc }, .rfl, H⟩
  have sub {e'} (h : ∀ fv ∈ e'.fvarsList, fv ∈ e.fvarsList) : Dom c e' := fun fv h' => he fv (h fv h')
  split
  · rename_i l _ _
    have H : SuppBelow c (.lit l) (mkConst l.typeName) := by
      intro S _ h; cases l <;> exact ⟨h.1, nofun⟩
    extract_lets G1; split <;> [split; skip]
    · exact .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => hF H
    · refine .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => ?_
      exact .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => hF H
    · exact hF H
  · rename_i e _ _
    exact (inferType'.SWF (e := e) he).bind fun _ _ _ h => hF h
  · rename_i st idx e _ _
    have he' : Dom c e := he
    refine (inferType'.SWF he').bind fun ty _ _ h => .stateWF fun wf => ?_
    exact (inferProj.SWF he' (h.dom wf he') h).bind fun _ _ _ h => hF h
  · exact .readThe <| (M.SWF.liftExcept inferFVar.SWF).lift.bind fun _ _ _ h => hF h
  · exact .throw
  · rename_i h _; simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at h
  · rename_i u _ _
    have H : SuppBelow c (.sort u) (.sort (.succ u)) := fun S _ h => (h : Level.LParamsIn S.lvl u)
    split
    · exact .readThe <| (M.SWF.liftExcept (Q := fun _ => True) fun _ _ => trivial).lift.bind
        fun _ _ _ _ => hF H
    · exact hF H
  · exact .readThe <| (M.SWF.liftExcept inferConstant.SWF).lift.bind fun _ _ _ h => hF h
  · exact (inferLambda.SWF he).bind fun _ _ _ h => hF h
  · exact (inferForall.SWF he).bind fun _ _ _ h => hF h
  · rename_i f a _ _
    have hf : Dom c f := sub fun fv h => by simp [Expr.fvarsList, h]
    have ha : Dom c a := sub fun fv h => by simp [Expr.fvarsList, h]
    split
    · exact (inferApp.SWF he).bind fun _ _ _ h => hF h
    refine (inferType'.SWF hf).bind fun fty _ _ hfty => .stateWF fun wf => ?_
    refine (ensureForallCore.SWF (hfty.dom wf hf)).bind fun fty' _ _ hfty' => .stateWF fun wf => ?_
    have hfty'' : SuppBelow c f fty' := hfty.trans hfty'
    have hd : Dom c fty'.bindingDomain! := dom_iff.2 <| Expr.SuppIn.bindingDomain! trivial <|
      dom_iff.1 (hfty''.dom wf hf)
    extract_lets _ G1
    refine (inferType'.SWF ha).bind fun aty _ _ haty => .stateWF fun wf => ?_
    extract_lets G2
    suffices ∀ {s b}, RecM.SWF c s (G2 b) P by
      split
      · exact (RecM.SWF.withEagerReduce (isDefEq.SWF hd (haty.dom wf ha))).bind
          fun b _ _ _ => this
      · exact (isDefEq.SWF hd (haty.dom wf ha)).bind fun b _ _ _ => this
    intro s b; subst G2; dsimp only; split
    · exact .getEnv <| .getLCtx .throw
    · refine hF fun S hS h => ?_
      exact Expr.SuppIn.inst1 h.2 <| Expr.SuppIn.bindingBody! hS.2.dummy (hfty'' S hS h.1)
  · exact (inferLet.SWF he).bind fun _ _ _ h => hF h

end Inner
end TypeChecker
end Lean4Lean

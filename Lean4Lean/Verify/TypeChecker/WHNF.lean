import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.TypeChecker.Recursor

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem reduceRecursor.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceRecursor
  refine .getEnv ?_
  have tail {s} : RecM.WF c s (do
      if let some r ← inductiveReduceRec c.env e whnf (fun e => inferType e) isDefEq then
        return some r
      return none) fun oe _ => ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    refine (inductiveReduceRec.WF he).bind fun _ _ _ h => ?_
    split
    · exact .pure fun _ eq => h _ (by cases eq; rfl)
    · exact .pure nofun
  split
  · rename_i hq
    refine (quotReduceRec.WF he hq).bind fun _ _ _ h => ?_
    split
    · exact .pure fun _ eq => h _ (by cases eq; rfl)
    · exact tail
  · exact tail

theorem whnfFVar.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' := by
  refine .getLCtx ?_
  simp [Expr.fvarId!]; split <;> [skip; exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, h2, _, h3, _⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  refine (whnfCore.WF h3).mono fun _ _ _ ⟨h4, h5⟩ => ?_
  refine ⟨h2.trans h4, h5.defeq c.Ewf c.Δwf ?_⟩
  refine (TrExprS.fvar h1).uniq c.Ewf ?_ he
  exact .refl c.Ewf c.Δwf

/-- `whnfCore'` on a term not in the cache. -/
theorem whnfCoreCore.WF [VEnv.Injective] {c : VContext} {s : VState}
    (hfull : (e matches .fvar _ | .app .. | .letE .. | .proj ..) = true) (he : c.TrExprS e e') :
    RecM.WF c s (whnfCoreCore e cheapProj) fun p _ =>
      c.FVarsBelow e p.1 ∧ c.TrExpr p.1 e' := by
  unfold whnfCoreCore
  generalize hP : (fun (p : Expr × Bool) (_ : VState) => _) = P
  have hid {s} (b) : RecM.WF c s (pure (e, b)) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  have hsave {e₁ s} (b) (h1 : c.FVarsBelow e e₁) (h2 : c.TrExpr e₁ e') :
      RecM.WF c s (pure (e₁, b)) P := hP ▸ .pure ⟨h1, h2⟩
  have hmap {x : RecM Expr} {s} (b) (h : x.WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') :
      RecM.WF c s ((fun a => (a, b)) <$> x) P := hP ▸ h.map fun _ _ _ h => h
  simp
  split <;> cases hfull
  · exact hmap _ (whnfFVar.WF he)
  · rename_i _ fn arg; generalize eq : fn.app arg = e at *
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine (whnfCore.WF stk.tr).bind fun _ s _ ⟨h1, h2⟩ => ?_
    split <;> [rename_i name dom body bi _; split]
    · let rec loop.WF {e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
        ∃ n f', LambdaBodyN n e' f' ∧ n ≤ rargs.size ∧
          loop cheapProj rargs i f = loop.cont cheapProj rargs n f' := by
        unfold loop; split
        · split
          · refine loop.WF (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
          · exact ⟨_, _, H, hi, rfl⟩
        · exact ⟨_, _, H, hi, rfl⟩
      refine
        let ⟨i, f, h3, h4, eq⟩ := loop.WF (e' := .lam name dom body bi) (.succ .zero) <| by
          simp [← eq, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList]
        eq ▸ ?_; clear eq
      simp [Expr.getAppRevArgs_eq] at h4 ⊢
      obtain ⟨l₁, l₂, h5, rfl⟩ : ∃ l₁ l₂, e.getAppArgsRevList = l₁ ++ l₂ ∧ l₂.length = i :=
        ⟨_, _, (List.take_append_drop (e.getAppArgsRevList.length - i) ..).symm, by simp; omega⟩
      simp [loop.cont, h5, List.take_of_length_le]
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₂ := l₁) (l₃ := l₂) (by simp) (by rfl) (by rfl)]
      rw [Expr.instantiate'_eq_instantiateList (by
        have := h5 ▸ (c.mlctx.noBV ▸ he.closed).getAppArgsRevList
        simp [or_imp, forall_and] at this
        exact fun a ha => (this.2 a ha).looseBVarRange_zero)]
      have br := BetaReduce.inst_reduce (l₁ := l₂.reverse)
        [] (by simpa using h3) (Expr.instantiateList_append ..) (h := by
          have := h5 ▸ (c.mlctx.noBV ▸ he.closed).getAppArgsRevList
          simp [or_imp, forall_and] at this ⊢
          exact this.2) |>.mkAppRevList (es := l₁)
      simp [← Expr.mkAppRevList_reverse, ← Expr.mkAppRevList_append, ← h5] at br
      have := h2.rebuild_mkAppRevList c.Ewf c.Δwf stk.tr <|
        e.mkAppRevList_getAppArgsRevList ▸ he
      have ⟨_, a1, a2⟩ := this.beta c.Ewf c.Δwf br
      have hb := e.mkAppRevList_getAppArgsRevList ▸ h1.mkAppRevList
      exact hmap _ <| (whnfCore.WF a1).mono fun _ _ _ ⟨b1, b2⟩ =>
        ⟨hb.trans (.betaReduce br) |>.trans b1, b2.defeq c.Ewf c.Δwf a2⟩
    · refine (reduceRecursor.WF he).bind fun _ _ _ h => ?_
      split <;> [skip; exact hid _]
      let ⟨h1, _, h2, eq⟩ := h _ rfl
      exact hmap _ <| (whnfCore.WF h2).mono fun _ _ _ ⟨h3, h4⟩ =>
        ⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq⟩
    · rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]; rfl) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      have {e e₁ : Expr} (hb : c.FVarsBelow e e₁) {es e₀' e'}
          (hes : c.TrExprS (e.mkAppRevList es) e₀') (he : c.TrExprS e e') (he₁ : c.TrExpr e₁ e') :
          c.FVarsBelow (e.mkAppRevList es) (e₁.mkAppRevList es) ∧
          c.TrExpr (e₁.mkAppRevList es) e₀' := by
        induction es generalizing e₁ e₀' e' with
        | nil =>
          refine ⟨hb, he₁.defeq c.Ewf c.Δwf ?_⟩
          exact he.uniq c.Ewf (.refl c.Ewf c.Δwf) hes
        | cons _ _ ih =>
          have .app h1 h2 h3 h4 := hes
          have ⟨h5, h6⟩ := ih hb h3 he he₁
          exact ⟨fun _ hP he => ⟨h5 _ hP he.1, he.2⟩,
            .app c.Ewf c.Δwf h1 h2 h6 (h4.trExpr c.Ewf c.Δwf)⟩
      have eq := e.mkAppRevList_getAppArgsRevList
      let ⟨h3, _, h4, eq⟩ := eq ▸ this h1 (eq ▸ he) stk.tr h2
      exact hmap _ <| (whnfCore.WF h4).mono fun _ _ _ ⟨h5, h6⟩ =>
        ⟨h3.trans h5, h6.defeq c.Ewf c.Δwf eq⟩
  · let .letE h1 h2 h3 h4 := he
    exact hmap _ <| (whnfCore.WF (h4.inst_let c.Ewf.ordered h3)).mono fun _ _ _ ⟨h1, h2⟩ =>
      ⟨.trans (fun _ _ he => he.2.2.instantiate1 he.2.1) h1, h2⟩
  · refine (reduceProj.WF he).bind fun _ _ _ H => ?_
    split
    · let ⟨h1, _, h2, eq⟩ := H _ rfl
      exact hmap _ <| (whnfCore.WF h2).mono fun _ _ _ ⟨h3, h4⟩ =>
        ⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq⟩
    · exact hsave _ .rfl (he.trExpr c.Ewf c.Δwf)


theorem whnfCore'.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : full e → RecM.WF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · let .mdata he := he
      exact hP ▸ whnfCore'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get <| .readThe ?_; split
  · rename_i r l eq
    obtain ⟨_, eq, hv, hc⟩ := State.cached?_spec eq
    refine .stateWF fun wf => ?_
    have ⟨h1, h4⟩ := wf.whnfCore_wf.now wf.shape eq hv hc _ he
    exact hP ▸ RecM.WF.taintWith.map fun _ _ _ _ => ⟨h1, h4⟩
  have hd := c.mlctx_wf.dom_of_tr he; rw [c.lctx_eq] at hd
  refine (RecM.WF.withTaintLearn (D := (· ∈ e.fvarsList))
    (Pre := fun m => ∃ e', TrExprS c.venv c.lparams m.vlctx e e')
    (P := fun p m => WHNFClaim c.venv c.lparams e ⟨p.1, 0, 0⟩ m)
    (R := fun p => SuppBelow c.toContext e p.1) hd
    (fun m hm S c₂ hA hS hD hl hc => whnfCoreCore.SS hA hS hfull hd
      (Lean.Expr.suppIn_of_fvars hD hl hc) m hm)
    (fun c₂ hv _ hl ⟨e'₀, h₀⟩ _ => by
      rw [← hv, ← hl] at h₀ ⊢
      exact (whnfCoreCore.WF hfull h₀).mono fun p _ _ ⟨h1, h2⟩ e'' he'' =>
        ⟨h1, h2.defeq c₂.Ewf c₂.Δwf (h₀.uniq c₂.Ewf (.refl c₂.Ewf c₂.Δwf) he'')⟩)
    (whnfCoreCore.WF hfull he)).bind fun ⟨⟨e₁, sv⟩, l⟩ s le ⟨⟨h1, h2⟩, hR, hL⟩ => ?_
  simp only
  split
  · rintro _ mwf wf a s' ⟨⟩
    obtain ⟨lab, hlab, hk⟩ := State.keyLabel_eq s.toState l
    dsimp only; rw [hk]
    refine hP ▸ ⟨_, rfl, .rfl, { wf with
      supp := { wf.supp with
        whnfCore := CondSupp.insert wf.supp.whnfCore (CondSupp.of wf.supp hd hR) }
      whnfCore_wf := wf.whnfCore_wf.insert fun k' hk' hval hc => ?_
      ids_made := ⟨wf.ids_made.1, wf.ids_made.2.1, wf.ids_made.2.2.1,
        wf.ids_made.2.2.2.1.insert (wf.labelId_le _), wf.ids_made.2.2.2.2⟩ }, h1, h2⟩
    refine ⟨c.lctx, s.ngen, Lean.NameGenerator.LE.rfl, Keeps.refl _ _, Admits.refl _ _, ?_⟩
    have hval' := le_of_valid hval; rw [le.2.1] at hval'
    have H := hL lab hlab hval' hc
    rw [← le.2.2] at H
    intro m wfm hbm ha e'' he''
    have he₀ := he''.eqv (by rwa [BEq.comm] at hk')
    have ⟨b1, b2⟩ := H m wfm hbm ha (wfm.dom_of_tr he₀) ⟨_, he₀⟩ e'' he₀
    exact ⟨b1.eqv hk' BEq.rfl, b2⟩
  · exact hP ▸ .pure ⟨h1, h2⟩

theorem whnfLoop.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    (whnfLoop e n).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  induction n generalizing s e e' with
  | zero => unfold whnfLoop; exact .throw
  | succ n ih => ?_
  unfold whnfLoop
  refine .getEnv <| (whnfCore'.WF he).bind fun e₁ s _ ⟨h1, _, he₁, eq⟩ => ?_
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h3 => ?_
  split <;> [cases h3 _ rfl; skip]
  refine (reduceNat.WF he₁).bind fun _ _ _ h3 => ?_; split
  · exact .pure ⟨.trans h1 (h3 _ rfl).1, (h3 _ rfl).2.defeq c.Ewf c.Δwf eq⟩
  refine (unfoldDefinition.WF he₁).bind fun _ _ _ H => ?_
  split <;> [skip; exact .pure ⟨h1, _, he₁, eq⟩]
  have ⟨a1, _, a2, eq'⟩ := H
  refine (ih a2).mono fun _ _ _ ⟨b1, b2⟩ => ?_
  exact ⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq⟩

theorem whnf'.WF [VEnv.Injective] {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : RecM.WF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · let .mdata he := he
      exact hP ▸ whnf'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get <| .readThe ?_; split
  · rename_i r l eq
    obtain ⟨_, eq, hv, hc⟩ := State.cached?_spec eq
    refine .stateWF fun wf => ?_
    have ⟨h1, h4⟩ := wf.whnf_wf.now wf.shape eq hv hc _ he
    exact hP ▸ RecM.WF.taintWith.map fun _ _ _ _ => ⟨h1, h4⟩
  have hd := c.mlctx_wf.dom_of_tr he; rw [c.lctx_eq] at hd
  refine .readThe <| (RecM.WF.withTaintLearn (D := (· ∈ e.fvarsList))
    (Pre := fun m => ∃ e', TrExprS c.venv c.lparams m.vlctx e e')
    (P := fun r m => WHNFClaim c.venv c.lparams e ⟨r, 0, 0⟩ m)
    (R := fun r => SuppBelow c.toContext e r) hd
    (fun m hm S c₂ hA hS hD hl hc => whnfLoop.SS hA hS hd
      (Lean.Expr.suppIn_of_fvars hD hl hc) m hm)
    (fun c₂ hv _ hl ⟨e'₀, h₀⟩ _ => by
      rw [← hv, ← hl] at h₀ ⊢
      exact (whnfLoop.WF h₀).mono fun p _ _ ⟨h1, h2⟩ e'' he'' =>
        ⟨h1, h2.defeq c₂.Ewf c₂.Δwf (h₀.uniq c₂.Ewf (.refl c₂.Ewf c₂.Δwf) he'')⟩)
    (whnfLoop.WF he)).bind fun ⟨e₁, l⟩ s le ⟨⟨h1, h2⟩, hR, hL⟩ => ?_
  rintro _ mwf wf a s' ⟨⟩
  obtain ⟨lab, hlab, hk⟩ := State.keyLabel_eq s.toState l
  dsimp only; rw [hk]
  refine hP ▸ ⟨_, rfl, .rfl, { wf with
    supp := { wf.supp with whnf := CondSupp.insert wf.supp.whnf (CondSupp.of wf.supp hd hR) }
    whnf_wf := wf.whnf_wf.insert fun k' hk' hval hc => ?_
    ids_made := ⟨wf.ids_made.1, wf.ids_made.2.1, wf.ids_made.2.2.1, wf.ids_made.2.2.2.1,
      wf.ids_made.2.2.2.2.insert (wf.labelId_le _)⟩ }, h1, h2⟩
  refine ⟨c.lctx, s.ngen, Lean.NameGenerator.LE.rfl, Keeps.refl _ _, Admits.refl _ _, ?_⟩
  have hval' := le_of_valid hval; rw [le.2.1] at hval'
  have H := hL lab hlab hval' hc
  rw [← le.2.2] at H
  intro m wfm hbm ha e'' he''
  have he₀ := he''.eqv (by rwa [BEq.comm] at hk')
  have ⟨b1, b2⟩ := H m wfm hbm ha (wfm.dom_of_tr he₀) ⟨_, he₀⟩ e'' he₀
  exact ⟨b1.eqv hk' BEq.rfl, b2⟩

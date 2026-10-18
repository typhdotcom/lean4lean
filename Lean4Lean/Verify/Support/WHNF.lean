import Lean4Lean.Verify.Support.InferType

/-!
# Support of weak head normal forms
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem getFirstCtor_supp {S : Supp} {env : Environment} (hS : S.EnvClosed env)
    (h : getFirstCtor env I = some ctor) (hI : S.const I) : S.const ctor := by
  unfold getFirstCtor at h
  split at h <;> [skip; cases h]
  rename_i info hfind
  exact (hS.find _ _ hfind hI).2 _ (List.mem_of_head? h)

theorem mkNullaryCtor_supp {S : Supp} {env : Environment} (hS : S.EnvClosed env)
    (h : mkNullaryCtor env type n = some r) (ht : type.SuppIn S) : r.SuppIn S := by
  simp only [mkNullaryCtor, Expr.withApp_eq] at h
  split at h <;> [skip; cases h]
  rename_i dName ls heq
  have hf : Expr.SuppIn S (.const dName ls) := heq ▸ ht.getAppFn
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨name, h1, rfl⟩ := h
  exact Expr.SuppIn.mkAppRange hS.dummy ht.getAppArgs
    (show Expr.SuppIn S (.const name ls) from ⟨getFirstCtor_supp hS h1 hf.1, hf.2⟩)

theorem expandEtaStruct_supp {S : Supp} {env : Environment} (hS : S.EnvClosed env)
    (ht : eType.SuppIn S) (he : e.SuppIn S) : (expandEtaStruct env eType e).SuppIn S := by
  simp only [expandEtaStruct, Expr.withApp_eq]
  split <;> [skip; exact he]
  rename_i I ls heq
  have hf : Expr.SuppIn S (.const I ls) := heq ▸ ht.getAppFn
  split <;> [skip; exact he]
  rename_i ctor h1
  split
  · rename_i info _
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    generalize List.range' _ _ _ = l
    have : ∀ (r : Expr), r.SuppIn S → (forIn (m := Id) l r fun i r =>
        ForInStep.yield (r.app (.proj I i e))).SuppIn S := by
      induction l with
      | nil => exact fun _ h => h
      | cons a l ih =>
        intro r h; rw [List.forIn_cons]
        exact ih _ (show Expr.SuppIn S (.app r (.proj I a e)) from ⟨h, he⟩)
    exact this _ (Expr.SuppIn.mkAppRange hS.dummy ht.getAppArgs
      (show Expr.SuppIn S (.const ctor ls) from ⟨getFirstCtor_supp hS h1 hf.1, hf.2⟩))
  · exact Expr.SuppIn.default hS.dummy

namespace TypeChecker.Inner

theorem whnfFVar.SWF {c : Context} {s : State} :
    (whnfFVar (.fvar fv) cheapProj).SWF c s fun e₁ _ => SuppBelow c (.fvar fv) e₁ := by
  unfold whnfFVar
  refine .getLCtx <| .stateWF fun wf => ?_
  split
  · rename_i h
    have hv : SuppBelow c (.fvar fv) _ := fun S hS h' => (hS.1 fv _ h' h).2
    exact (whnfCore.SWF (wf.wellScoped _ _ h).2).mono fun _ _ _ h => hv.trans h
  · exact .pure .rfl

theorem reduceProjCore.SWF {c : Context} {s : State} (he : Dom c struct) :
    (reduceProjCore n idx struct).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c struct e₁ := by
  unfold reduceProjCore
  extract_lets c0 jp
  have hjp {c' s} (h : SuppBelow c struct c') : (jp () c').SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c struct e₁ := by
    simp only [jp, Expr.withApp_eq]
    split
    · refine .getEnv <| (M.SWF.liftExcept envGet.SWF).lift.bind fun _ _ _ _ => ?_
      split
      · split; · exact .pure nofun
        split; · exact .pure nofun
        refine .pure fun e₁ he₁ S hS hs => ?_
        exact Expr.SuppIn.getAppArgs (h S hS hs) _ (Array.mem_of_getElem? he₁)
      · exact .pure nofun
    · exact .pure nofun
  simp only [c0]; split
  · rename_i str
    have hd : Dom c (Expr.strLitToConstructor str) :=
      dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)
    refine (whnf.SWF hd).bind fun _ _ _ h => hjp fun S hS hs => h S hS ?_
    exact Expr.SuppIn.strLitToConstructor hs
  · exact hjp .rfl

theorem reduceProj.SWF {c : Context} {s : State} (he : Dom c struct) :
    (reduceProj n idx struct cheapProj).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c struct e₁ := by
  unfold reduceProj
  refine .bind (Q := fun e₁ _ => SuppBelow c struct e₁) ?_ fun _ _ _ h => .stateWF fun wf => ?_
  · split <;> [exact whnfCore.SWF he; exact whnf.SWF he]
  exact (reduceProjCore.SWF (h.dom wf he)).mono fun _ _ _ H e₁ eq => h.trans (H e₁ eq)

theorem quotReduceRec.SWF {c : Context} {s : State} (he : Dom c e) :
    (quotReduceRec e whnf isDefEq : RecM _).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold quotReduceRec
  split
  · lift_lets; intro args jp cont
    have hargs S (hS : S.Closed c) (h : e.SuppIn S) : ∀ a ∈ args, a.SuppIn S :=
      Expr.SuppIn.getAppArgs h
    have hdargs : ∀ a ∈ args, Dom c a := fun a ha =>
      dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 he) _ ha)
    have hcont {a b s} : (cont a b).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
      simp only [cont, jp]; split
      · rename_i h
        have hd : Dom c args[a] := hdargs _ (Array.getElem_mem h)
        refine .stateWF fun wf => (whnf.SWF hd).bind fun mk _ _ hmk => ?_
        have hr : SuppBelow c e (args[b]!.app mk.appArg!) := fun S hS h' =>
          ⟨Expr.SuppIn.getElem! hS.2.dummy (hargs S hS h'), Expr.SuppIn.appArg! hS.2.dummy
            (hmk S hS (hargs S hS h' _ (Array.getElem_mem _)))⟩
        have hmkd := dom_iff.1 (hmk.dom wf hd)
        have hget {i} : Dom c args[i]! :=
          dom_iff.2 (Expr.SuppIn.getElem! trivial fun a ha => dom_iff.1 (hdargs a ha))
        split
        · exact .pure nofun
        · refine (isDefEq.SWF (dom_iff.2 (Expr.SuppIn.appArg! trivial (Expr.SuppIn.appFn! trivial
            (Expr.SuppIn.appFn! trivial hmkd)))) hget).bind fun _ _ _ _ => ?_
          split <;> [skip; exact .pure nofun]
          refine (isDefEq.SWF (dom_iff.2 (Expr.SuppIn.appArg! trivial (Expr.SuppIn.appFn! trivial
            hmkd))) hget).bind fun _ _ _ _ => ?_
          split <;> [skip; exact .pure nofun]
          split
          · refine .pure ?_; rintro _ ⟨⟩; intro S hS h'
            exact Expr.SuppIn.mkAppRange hS.2.dummy (hargs S hS h') (hr S hS h')
          · refine .pure ?_; rintro _ ⟨⟩; exact hr
      · exact .pure nofun
    split; · exact hcont
    split; · exact hcont
    exact .pure nofun
  · exact .pure nofun

theorem toCtorWhenK.SWF {c : Context} {s : State} (he : Dom c e) :
    (toCtorWhenK c.env whnf inferType isDefEq rval e : RecM _).SWF c s fun e₁ _ =>
      SuppBelow c e e₁ := by
  unfold toCtorWhenK
  split
  · refine (inferType.SWF he).bind fun ty _ _ hty => .stateWF fun wf => ?_
    refine (whnf.SWF (hty.dom wf he)).bind fun appType _ _ hat => ?_
    have hat' := hty.trans hat
    split
    · split; · exact .pure .rfl
      extract_lets jp
      have hjp {s} : (jp ()).SWF c s fun e₁ _ => SuppBelow c e e₁ := by
        simp only [jp]; split
        · rename_i n hn
          have hn' : SuppBelow c e n := fun S hS h => mkNullaryCtor_supp hS.2 hn (hat' S hS h)
          refine .stateWF fun wf => (inferType.SWF (hn'.dom wf he)).bind
            fun t _ _ ht => .stateWF fun wf => ?_
          refine (isDefEq.SWF (hat'.dom wf he) ((hn'.trans ht).dom wf he)).bind
            fun _ _ _ _ => ?_
          split
          · exact .pure hn'
          · exact .pure .rfl
        · exact .pure .rfl
      split
      · refine (RecM.SWF.forIn'_range (Inv := fun r : Option Expr × Unit => ∀ x, r.1 = some x → x = e)
          ?_ (by simp)).bind fun r _ _ hr => ?_
        · intro i h b s _; split
          · exact .pure (by simp)
          · exact .pure (by simp)
        · dsimp only; split
          · rename_i x hx; cases hr x hx; exact .pure .rfl
          · exact hjp
      · exact hjp
    · exact .pure .rfl
  · exact .panic fun S hS _ => Expr.SuppIn.default hS.2.dummy

theorem toCtorWhenStruct.SWF {c : Context} {s : State} (he : Dom c e) :
    (toCtorWhenStruct c.env whnf inferType I e : RecM _).SWF c s fun e₁ _ =>
      SuppBelow c e e₁ := by
  unfold toCtorWhenStruct
  split; · exact .pure .rfl
  refine (inferType.SWF he).bind fun ty _ _ hty => .stateWF fun wf => ?_
  refine (whnf.SWF (hty.dom wf he)).bind fun eType _ _ het => .stateWF fun wf => ?_
  have het' := hty.trans het
  split; · exact .pure .rfl
  refine (inferType.SWF (het'.dom wf he)).bind fun ty' _ _ hty' => .stateWF fun wf => ?_
  refine (whnf.SWF ((het'.trans hty').dom wf he)).bind fun _ _ _ _ => ?_
  split
  · split
    · exact .pure fun S hS h => expandEtaStruct_supp hS.2 (het' S hS h) h
    · exact .pure .rfl
  · exact .pure .rfl

theorem inductiveReduceRec.SWF {c : Context} {s : State} (he : Dom c e) :
    (inductiveReduceRec c.env e whnf inferType isDefEq : RecM _).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold inductiveReduceRec
  split <;> [skip; exact .pure nofun]
  rename_i recFn ls heq
  split <;> [skip; exact .pure nofun]
  rename_i info hfind
  extract_lets recArgs majorIdx jp3 jp2 jp1
  have hargs S (hS : S.Closed c) (h : e.SuppIn S) : ∀ a ∈ recArgs, a.SuppIn S :=
    Expr.SuppIn.getAppArgs h
  have hf S (hS : S.Closed c) (h : e.SuppIn S) : Expr.SuppIn S (.const recFn ls) :=
    heq ▸ h.getAppFn
  have hjp2 {major s} (hm : SuppBelow c e major) : (jp2 () major).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
    simp only [jp2, jp3]
    split <;> [skip; exact .pure nofun]
    rename_i rule hrule
    have hmem : rule ∈ info.rules := by
      unfold getRecRuleFor at hrule
      split at hrule <;> [exact List.mem_of_find?_eq_some hrule; cases hrule]
    split <;> [skip; exact .pure nofun]
    split; · exact .pure nofun
    split; · exact .pure nofun
    rename_i hlen
    have hrhs S (hS : S.Closed c) (h : e.SuppIn S) :
        (rule.rhs.instantiateLevelParams info.levelParams ls).SuppIn S := by
      have := (hS.2.find _ _ hfind (hf S hS h).1).2.2 rule hmem
      refine Expr.SuppIn.instantiateLevelParams (this.noFV (F := S.fv)) (hf S hS h).2 ?_
      simp at hlen; exact hlen.symm
    have base : SuppBelow c e (mkAppRange (mkAppRange (rule.rhs.instantiateLevelParams
        info.levelParams ls) 0 info.getFirstIndexIdx recArgs)
        (major.getAppArgs.size - rule.nfields) major.getAppArgs.size major.getAppArgs) :=
      fun S hS h => Expr.SuppIn.mkAppRange hS.2.dummy (Expr.SuppIn.getAppArgs (hm S hS h))
        (Expr.SuppIn.mkAppRange hS.2.dummy (hargs S hS h) (hrhs S hS h))
    split
    · refine .pure ?_; rintro _ ⟨⟩
      exact fun S hS h => Expr.SuppIn.mkAppRange hS.2.dummy (hargs S hS h) (base S hS h)
    · refine .pure ?_; rintro _ ⟨⟩; exact base
  have hjp1 {major s} (hm : SuppBelow c e major) : (jp1 () major).SWF c s fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
    simp only [jp1]
    refine .stateWF fun wf => (whnf.SWF (hm.dom wf he)).bind fun major' _ _ hm' => ?_
    have hm' := hm.trans hm'
    split
    · rename_i n _
      refine hjp2 fun S hS h => Expr.SuppIn.natLitToConstructor ?_
      exact (hm' S hS h : Expr.SuppIn S (.lit (.natVal n)))
    · rename_i str _
      have hd : Dom c (Expr.strLitToConstructor str) :=
        dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)
      refine (whnf.SWF hd).bind fun _ _ _ h => hjp2 fun S hS hs => h S hS ?_
      exact Expr.SuppIn.strLitToConstructor (hm' S hS hs : Expr.SuppIn S (.lit (.strVal str)))
    · refine .stateWF fun wf => (toCtorWhenStruct.SWF (hm'.dom wf he)).bind fun _ _ _ h => ?_
      exact hjp2 (hm'.trans h)
  split <;> [skip; exact .pure nofun]
  rename_i major0 hmajor0
  have hm0 : SuppBelow c e major0 := fun S hS h => hargs S hS h _ (Array.mem_of_getElem? hmajor0)
  dsimp only
  split
  · exact .stateWF fun wf => (toCtorWhenK.SWF (hm0.dom wf he)).bind fun _ _ _ h =>
      hjp1 (hm0.trans h)
  · exact hjp1 hm0

theorem reduceRecursor.SWF {c : Context} {s : State} (he : Dom c e) :
    (reduceRecursor e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold reduceRecursor
  refine .getEnv ?_
  have tail {s} : RecM.SWF c s (do
      if let some r ← inductiveReduceRec c.env e whnf (fun e => inferType e) isDefEq then
        return some r
      return none) fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
    refine (inductiveReduceRec.SWF he).bind fun _ _ _ h => ?_
    split
    · exact .pure fun _ eq => h _ (by cases eq; rfl)
    · exact .pure nofun
  split
  · refine (quotReduceRec.SWF he).bind fun _ _ _ h => ?_
    split
    · exact .pure fun _ eq => h _ (by cases eq; rfl)
    · exact tail
  · exact tail

theorem whnfCore'.save.SWF {c : Context} {s : State} (he : Dom c e) (h1 : SuppBelow c e e₁) :
    (whnfCore'.save e cheapProj e₁).SWF c s fun r _ => SuppBelow c e r := by
  simp [save]; split <;> [skip; exact .pure h1]
  rintro _ _ wf a s' ⟨⟩
  exact ⟨{ wf with whnfCore := CondSupp.insert wf.whnfCore (CondSupp.of wf he h1) }, .rfl, h1⟩

theorem whnfCore'.loop.SWF {c : Context} {s : State} {e f : Expr} {rargs : Array Expr}
    (he : Dom c e) (hargs : ∀ S, S.Closed c → e.SuppIn S → ∀ a ∈ rargs, a.SuppIn S)
    (hf : SuppBelow c e f) :
    (whnfCore'.loop e cheapProj rargs m f).SWF c s fun e₁ _ => SuppBelow c e e₁ := by
  have hcont {m f s} (hf : SuppBelow c e f) :
      (whnfCore'.loop.cont e cheapProj rargs m f).SWF c s fun e₁ _ => SuppBelow c e e₁ := by
    unfold whnfCore'.loop.cont
    have hr : SuppBelow c e ((f.instantiateRange (rargs.size - m) rargs.size rargs).mkAppRevRange
        0 (rargs.size - m) rargs) := fun S hS h =>
      Expr.SuppIn.mkAppRevRange hS.2.dummy (hargs S hS h)
        (Expr.SuppIn.instantiateRange (hargs S hS h) (hf S hS h))
    refine .stateWF fun wf => (whnfCore.SWF (hr.dom wf he)).bind fun _ _ _ h => ?_
    exact save.SWF he (hr.trans h)
  unfold whnfCore'.loop; split
  · split
    · exact whnfCore'.loop.SWF he hargs fun S hS h => (hf S hS h).2
    · exact hcont hf
  · exact hcont hf
termination_by rargs.size - m

theorem whnfCore'.SWF {c : Context} {s : State} (he : Dom c e) :
    (whnfCore' e cheapProj).SWF c s fun e₁ _ => SuppBelow c e e₁ := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : State) => _) = P
  have hid {s} : RecM.SWF c s (pure e) P := hP ▸ .pure .rfl
  suffices hF : full e → RecM.SWF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · exact hP ▸ whnfCore'.SWF (e := _) he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    exact fun S hS h => (wf.whnfCore _ _ eq).2 S hS he h
  have hsave {e₁ s} (h1 : SuppBelow c e e₁) : (save e cheapProj e₁).SWF c s P :=
    hP ▸ save.SWF he h1
  split <;> cases hfull
  · exact hP ▸ whnfFVar.SWF
  · rename_i fn arg _
    generalize fn.app arg = e at *
    have hargs S (_ : S.Closed c) (h : e.SuppIn S) := Expr.SuppIn.getAppRevArgs h
    have hf0 : Dom c e.getAppFn := dom_iff.2 (dom_iff.1 he).getAppFn
    refine (whnfCore.SWF hf0).bind fun f _ _ hf => .stateWF fun wf => ?_
    have hf' : SuppBelow c e f := fun S hS h => hf S hS h.getAppFn
    split
    · exact hP ▸ loop.SWF he hargs fun S hS h => (hf' S hS h : Expr.SuppIn S (.lam ..)).2
    split
    · refine (reduceRecursor.SWF he).bind fun _ _ _ h => ?_
      split
      · have h := h _ rfl
        exact hP ▸ (whnfCore.SWF (h.dom ‹_› he)).mono fun _ _ _ h' => h.trans h'
      · exact hid
    · have hr : SuppBelow c e (f.mkAppRevRange 0 e.getAppRevArgs.size e.getAppRevArgs) :=
        fun S hS h => Expr.SuppIn.mkAppRevRange hS.2.dummy (hargs S hS h) (hf' S hS h)
      refine (whnfCore.SWF (hr.dom wf he)).bind fun _ _ _ h => hsave (hr.trans h)
  · rename_i n ty val body nd _
    have hr : SuppBelow c (.letE n ty val body nd) (body.instantiate1' val) := fun S hS h =>
      Expr.SuppIn.instantiate1 h.2.1 h.2.2
    refine .stateWF fun wf => (whnfCore.SWF (hr.dom wf he)).bind fun _ _ _ h => hsave (hr.trans h)
  · rename_i tn idx st _
    have hst : Dom c st := he
    refine (reduceProj.SWF hst).bind fun _ _ _ h => ?_
    split
    · have h : SuppBelow c (.proj tn idx st) _ := fun S hS h' => h _ rfl S hS h'
      exact .stateWF fun wf => (whnfCore.SWF (h.dom wf he)).bind fun _ _ _ h' => hsave (h.trans h')
    · exact hsave .rfl

theorem isDelta_supp {S : Supp} {env : Environment} (hS : S.EnvClosed env)
    (h : isDelta env (.const n ls) = some d) (he : Expr.SuppIn S (.const n ls)) :
    (instantiateDeltaValue d ls).SuppIn S := by
  simp only [isDelta, Expr.getAppFn] at h
  split at h <;> [skip; cases h]
  rename_i ci hci
  split at h <;> [skip; cases h]
  rename_i hd
  cases h
  simp only [Bool.and_eq_true, beq_iff_eq] at hd
  have := (hS.find _ _ hci he.1).2
  unfold instantiateDeltaValue
  refine Expr.SuppIn.instantiateLevelParams (Expr.SuppIn.noFV (F := S.fv) ?_) he.2 ?_
  · revert this hd; cases d <;> simp [ConstantInfo.deltaValue?]
  · simpa [ConstantInfo.numLevelParams] using hd.2.symm

theorem unfoldDefinitionCore.SWF {c : Context} {s : State} :
    (unfoldDefinitionCore e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold unfoldDefinitionCore
  split <;> [skip; exact .pure nofun]
  rename_i n ls
  refine .getEnv ?_
  split <;> [skip; exact .pure nofun]
  rename_i d hd
  have H : SuppBelow c (.const n ls) (instantiateDeltaValue d ls) :=
    fun S hS h => isDelta_supp hS.2 hd h
  split <;> [skip; exact .pure fun _ eq => by cases eq; exact H]
  refine .get ?_
  split
  · rename_i r hr
    refine .stateWF fun wf => .pure fun _ eq => ?_
    cases eq; exact fun S hS h => wf.unfold _ _ hr S hS.2 h
  · intro _ _ wf a s' eq
    cases eq
    refine ⟨{ wf with unfold := fun e' r' h' S hS he' => ?_ }, .rfl, fun _ eq => by cases eq; exact H⟩
    rw [Std.HashMap.getElem?_insert] at h'; split at h'
    · cases h'; rename_i eq
      exact isDelta_supp hS hd (Expr.SuppIn.eqv_rev eq he')
    · exact wf.unfold _ _ h' S hS he'

theorem unfoldDefinition.SWF {c : Context} {s : State} :
    (unfoldDefinition e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold unfoldDefinition
  split
  · refine unfoldDefinitionCore.SWF.bind fun _ _ _ h => ?_
    split
    · refine .pure fun _ eq => ?_; cases eq
      exact fun S hS he => Expr.SuppIn.mkAppRevRange hS.2.dummy he.getAppRevArgs
        (h _ rfl S hS he.getAppFn)
    · exact .pure nofun
  · exact unfoldDefinitionCore.SWF

theorem reduceBinNatOp.SWF {c : Context} {s : State} (ha : Dom c a) (hb : Dom c b) :
    (reduceBinNatOp f a b).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → ∃ n, e₁ = .lit (.natVal n) := by
  unfold reduceBinNatOp
  refine (whnf.SWF ha).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  refine (whnf.SWF hb).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  exact .pure fun _ eq => by cases eq; exact ⟨_, rfl⟩

theorem reducePow.SWF {c : Context} {s : State} (ha : Dom c a) (hb : Dom c b) :
    (reducePow a b).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → ∃ n, e₁ = .lit (.natVal n) := by
  unfold reducePow
  refine (whnf.SWF ha).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  refine (whnf.SWF hb).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  split; · exact .pure nofun
  exact .pure fun _ eq => by cases eq; exact ⟨_, rfl⟩

theorem reduceBinNatPred.SWF {c : Context} {s : State} (ha : Dom c a) (hb : Dom c b) :
    (reduceBinNatPred f a b).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → ∃ b : Bool, e₁ = toExpr b := by
  unfold reduceBinNatPred
  refine (whnf.SWF ha).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  refine (whnf.SWF hb).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  exact .pure fun _ eq => by cases eq; exact ⟨_, rfl⟩

theorem reduceNat.SWF {c : Context} {s : State} (he : Dom c e) :
    (reduceNat e).SWF c s fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c e e₁ := by
  unfold reduceNat; extract_lets nargs jp fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> simp only [Bool.false_eq_true, ↓reduceIte]; · exact .pure nofun
    split <;> [skip; exact .pure nofun]
    rename_i f us a b
    have ha : Dom c a := fun fv h => he fv (by simp [Expr.fvarsList, h])
    have hb : Dom c b := fun fv h => he fv (by simp [Expr.fvarsList, h])
    have hnat (hf : f ∈ natOps) n : SuppBelow c (.app (.app (.const f us) a) b) (.lit (.natVal n)) :=
      fun S hS h => hS.2.nat f hf h.1.1.1
    have hop {g} (hf : f ∈ natOps) {s} : (reduceBinNatOp g a b).SWF c s fun oe _ =>
        ∀ e₁, oe = some e₁ → SuppBelow c (.app (.app (.const f us) a) b) e₁ :=
      (reduceBinNatOp.SWF ha hb).mono fun _ _ _ h e₁ eq => by
        obtain ⟨n, rfl⟩ := h e₁ eq; exact hnat hf n
    have hpow (hf : f ∈ natOps) {s} : (reducePow a b).SWF c s fun oe _ =>
        ∀ e₁, oe = some e₁ → SuppBelow c (.app (.app (.const f us) a) b) e₁ :=
      (reducePow.SWF ha hb).mono fun _ _ _ h e₁ eq => by
        obtain ⟨n, rfl⟩ := h e₁ eq; exact hnat hf n
    have hpred {g} (hf : f ∈ [``Nat.beq, ``Nat.ble]) {s} : (reduceBinNatPred g a b).SWF c s
        fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c (.app (.app (.const f us) a) b) e₁ :=
      (reduceBinNatPred.SWF ha hb).mono fun _ _ _ h e₁ eq => by
        obtain ⟨b, rfl⟩ := h e₁ eq
        exact fun S hS h => Expr.SuppIn.toExprBool (hS.2.bool f hf h.1.1.1)
    by_cases hX : (f == ``Nat.add) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.sub) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.mul) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.pow) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hpow (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.gcd) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.mod) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.div) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.beq) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hpred (by simp)
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.ble) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hpred (by simp)
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.land) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.lor) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.xor) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.shiftLeft) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.shiftRight) = true
    · rw [if_pos hX]; simp only [beq_iff_eq] at hX; subst hX; exact hop (by simp [natOps])
    rw [if_neg hX]
    exact .pure nofun
  · split <;> [skip; exact .pure nofun]
    rename_i hf
    have hd : Dom c e.appArg! := dom_iff.2 (Expr.SuppIn.appArg! trivial (dom_iff.1 he))
    refine (whnf.SWF hd).bind fun _ _ _ _ => ?_
    split <;> [skip; exact .pure nofun]
    refine .pure fun _ eq => ?_; cases eq
    intro S hS h
    have : Expr.SuppIn S (.const ``Nat.succ []) :=
      Expr.SuppIn.eqv hf (Expr.SuppIn.appFn! hS.2.dummy h)
    exact hS.2.nat _ (by simp [natOps]) this.1

theorem reduceNative.SWF : (reduceNative env e).WF fun oe => oe = none := by
  unfold reduceNative; split <;> [skip; exact .pure rfl]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure rfl]

theorem whnf'.SWF {c : Context} {s : State} (he : Dom c e) :
    (whnf' e).SWF c s fun e₁ _ => SuppBelow c e e₁ := by
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : State) => _) = P
  have hid {s} : RecM.SWF c s (pure e) P := hP ▸ .pure .rfl
  suffices hF : RecM.SWF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · exact hP ▸ whnf'.SWF (e := _) he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    exact fun S hS h => (wf.whnf _ _ eq).2 S hS he h
  have loop {e' n s} (he' : Dom c e') : (loop e' n).SWF c s fun e₁ _ => SuppBelow c e' e₁ := by
    induction n generalizing s e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.SWF he').bind fun e₁ _ _ h1 => .stateWF fun wf => ?_
    refine (M.SWF.liftExcept reduceNative.SWF).lift.bind fun _ _ _ h3 => ?_
    split <;> [cases h3; skip]
    refine (reduceNat.SWF (h1.dom wf he')).bind fun _ _ _ h3 => ?_; split
    · exact .pure (h1.trans (h3 _ rfl))
    refine unfoldDefinition.SWF.bind fun _ _ _ H => ?_
    split <;> [skip; exact .pure h1]
    have H := h1.trans (H _ rfl)
    exact (ih (H.dom wf he')).mono fun _ _ _ h => H.trans h
  refine .readThe <| (loop he).bind fun e₁ s _ h1 => ?_
  rintro _ _ wf a s' ⟨⟩
  exact ⟨{ wf with whnf := CondSupp.insert wf.whnf (CondSupp.of wf he h1) }, .rfl, hP ▸ h1⟩

end TypeChecker.Inner
end Lean4Lean

import Lean4Lean.Verify.Support.SimInfer

/-!
# Weak head normalization reads only what its input mentions
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

theorem getFirstCtor_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) (hI : S.const I) :
    getFirstCtor c₂.env I = getFirstCtor c₁.env I := by
  simp only [getFirstCtor, hA.env I hI]

theorem getAppFn_const_supp {S : Supp} {e : Expr} (h : e.SuppIn S)
    (heq : e.getAppFn = .const n ls) : S.const n :=
  (heq ▸ h.getAppFn : Expr.SuppIn S (.const _ _)).1

theorem mkNullaryCtor_agree {S : Supp} {c₁ c₂ : Context} {type : Expr} (hA : Agree S c₁ c₂)
    (ht : type.SuppIn S) : mkNullaryCtor c₂.env type n = mkNullaryCtor c₁.env type n := by
  simp only [mkNullaryCtor, Expr.withApp_eq]
  split
  · rename_i heq; rw [getFirstCtor_agree hA (getAppFn_const_supp ht heq)]
  · rfl

theorem expandEtaStruct_agree {S : Supp} {c₁ c₂ : Context} {eType : Expr} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (ht : eType.SuppIn S) :
    expandEtaStruct c₂.env eType e = expandEtaStruct c₁.env eType e := by
  simp only [expandEtaStruct, Expr.withApp_eq]
  split
  · rename_i I ls heq
    have hI := getAppFn_const_supp ht heq
    rw [getFirstCtor_agree hA hI]
    split
    · rename_i ctor h1
      rw [hA.env ctor (getFirstCtor_supp hS.2 h1 hI)]
    · rfl
  · rfl

theorem isNonRecStructure_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂)
    (hn : S.const n) : c₂.env.isNonRecStructure n = c₁.env.isNonRecStructure n := by
  simp only [Environment.isNonRecStructure, hA.env n hn]

theorem isConstructorApp?'_agree {S : Supp} {c₁ c₂ : Context} {e : Expr} (hA : Agree S c₁ c₂)
    (he : e.SuppIn S) : e.isConstructorApp?' c₂.env = e.isConstructorApp?' c₁.env := by
  simp only [Expr.isConstructorApp?']
  split
  · rename_i heq; rw [hA.env _ (getAppFn_const_supp he heq)]
  · rfl

theorem isDelta_agree {S : Supp} {c₁ c₂ : Context} {e : Expr} (hA : Agree S c₁ c₂)
    (he : e.SuppIn S) :
    Inner.isDelta c₂.env e = Inner.isDelta c₁.env e := by
  simp only [Inner.isDelta]
  split
  · rename_i heq; rw [hA.env _ (getAppFn_const_supp he heq)]
  · rfl

theorem isLetFVar_agree {S : Supp} {c₁ c₂ : Context} (hA : Agree S c₁ c₂) (hs : S.fv fv) :
    Inner.isLetFVar c₂.lctx fv = Inner.isLetFVar c₁.lctx fv := by
  have hl := hA.lctx fv hs
  simp only [Inner.isLetFVar]
  cases h₁ : c₁.lctx.find? fv with
  | none =>
    cases h₂ : c₂.lctx.find? fv
    · rfl
    · rw [h₁, h₂] at hl; cases hl
  | some d₁ =>
    cases h₂ : c₂.lctx.find? fv with
    | none => rw [h₁, h₂] at hl; cases hl
    | some d₂ =>
      rw [h₁, h₂] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      cases d₁ <;> cases d₂ <;> simp [LocalDecl.erase] at hl <;> rfl

namespace Inner

theorem whnfFVar.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (hs : S.fv fv) :
    RecM.SS c₁ c₂ s (whnfFVar (.fvar fv) cheapProj) (whnfFVar (.fvar fv) cheapProj)
      fun e₁ _ => SuppBelow c₁ (.fvar fv) e₁ := by
  refine .of_swf (Q' := fun _ _ => True) whnfFVar.SWF ?_
  unfold whnfFVar
  refine .getLCtx <| .stateWF fun wf => ?_
  have hl := hA.lctx fv hs
  simp only [Expr.fvarId!]
  cases h₁ : c₁.lctx.find? fv with
  | none =>
    cases h₂ : c₂.lctx.find? fv
    · exact .pure trivial
    · rw [h₁, h₂] at hl; cases hl
  | some d₁ =>
    cases h₂ : c₂.lctx.find? fv with
    | none => rw [h₁, h₂] at hl; cases hl
    | some d₂ =>
      rw [h₁, h₂] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      cases d₁ <;> cases d₂ <;> simp [LocalDecl.erase] at hl
      · exact .pure trivial
      · obtain ⟨-, -, -, rfl, -, -⟩ := hl
        refine (whnfCore.SS hA hS (wf.wellScoped _ _ h₁).2 ?_).mono fun _ _ _ _ => trivial
        exact (hS.1 fv _ hs h₁).2

theorem reduceProjCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ struct) (hs : struct.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceProjCore n idx struct) (reduceProjCore n idx struct) fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c₁ struct e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (reduceProjCore.SWF he) ?_
  unfold reduceProjCore
  extract_lets c0 jp
  have hjp {c' s} (h : SuppBelow c₁ struct c') : RecM.SS c₁ c₂ s (jp () c') (jp () c')
      fun _ _ => True := by
    simp only [jp, Expr.withApp_eq]
    split
    · rename_i mkC _ heq
      have hmk := getAppFn_const_supp (h S hS hs) heq
      refine .getEnv <| (RecM.SS.liftExcept envGet.SWF (envGet_agree hA hmk)).bind
        fun _ _ _ _ => ?_
      split <;> [(split <;> [exact .pure trivial; (split <;> exact .pure trivial)]);
        exact .pure trivial]
    · exact .pure trivial
  simp only [c0]; split
  · rename_i str
    have hd : Dom c₁ (Expr.strLitToConstructor str) :=
      dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)
    refine (whnf.SS hA hS hd (Expr.SuppIn.strLitToConstructor hs)).bind fun _ _ _ h => hjp ?_
    exact fun S hS hs => h S hS (Expr.SuppIn.strLitToConstructor hs)
  · exact hjp .rfl

theorem reduceProj.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ struct) (hs : struct.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceProj n idx struct cheapProj) (reduceProj n idx struct cheapProj)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ struct e₁ := by
  unfold reduceProj
  refine .bind (Q := fun e₁ _ => SuppBelow c₁ struct e₁) ?_ fun _ _ _ h => .stateWF fun wf => ?_
  · split <;> [exact whnfCore.SS hA hS he hs; exact whnf.SS hA hS he hs]
  exact (reduceProjCore.SS hA hS (h.dom wf he) (h S hS hs)).mono
    fun _ _ _ H e₁ eq => h.trans (H e₁ eq)

theorem quotReduceRec.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (quotReduceRec e whnf isDefEq : RecM _) (quotReduceRec e whnf isDefEq)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (quotReduceRec.SWF he) ?_
  unfold quotReduceRec
  split
  · lift_lets; intro args jp cont
    have hargs : ∀ a ∈ args, a.SuppIn S := Expr.SuppIn.getAppArgs hs
    have hdargs : ∀ a ∈ args, Dom c₁ a := fun a ha =>
      dom_iff.2 (Expr.SuppIn.getAppArgs (dom_iff.1 he) _ ha)
    have hcont {a b s} : RecM.SS c₁ c₂ s (cont a b) (cont a b) fun _ _ => True := by
      simp only [cont, jp]; split
      · rename_i h
        have hd : Dom c₁ args[a] := hdargs _ (Array.getElem_mem h)
        refine .stateWF fun wf => (whnf.SS hA hS hd (hargs _ (Array.getElem_mem h))).bind
          fun mk _ _ hmk => ?_
        have hmkd := dom_iff.1 (hmk.dom wf hd)
        have hmks := hmk S hS (hargs _ (Array.getElem_mem h))
        have hget {i : Nat} : Dom c₁ args[i]! :=
          dom_iff.2 (Expr.SuppIn.getElem! trivial fun a ha => dom_iff.1 (hdargs a ha))
        have hgets {i : Nat} : Expr.SuppIn S args[i]! := Expr.SuppIn.getElem! hS.2.dummy hargs
        split
        · exact .pure trivial
        · refine (isDefEq.SS hA hS
            (dom_iff.2 (Expr.SuppIn.appArg! trivial (Expr.SuppIn.appFn! trivial
              (Expr.SuppIn.appFn! trivial hmkd)))) hget
            (Expr.SuppIn.appArg! hS.2.dummy (Expr.SuppIn.appFn! hS.2.dummy
              (Expr.SuppIn.appFn! hS.2.dummy hmks))) hgets).bind fun _ _ _ _ => ?_
          split <;> [skip; exact .pure trivial]
          refine (isDefEq.SS hA hS
            (dom_iff.2 (Expr.SuppIn.appArg! trivial (Expr.SuppIn.appFn! trivial hmkd))) hget
            (Expr.SuppIn.appArg! hS.2.dummy (Expr.SuppIn.appFn! hS.2.dummy hmks)) hgets).bind
            fun _ _ _ _ => ?_
          split <;> [skip; exact .pure trivial]
          split <;> exact .pure trivial
      · exact .pure trivial
    split; · exact hcont
    split; · exact hcont
    exact .pure trivial
  · exact .pure trivial

theorem toCtorWhenK.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (toCtorWhenK c₁.env whnf inferType isDefEq rval e : RecM _)
      (toCtorWhenK c₂.env whnf inferType isDefEq rval e) fun e₁ _ => SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (toCtorWhenK.SWF he) ?_
  unfold toCtorWhenK
  split
  · refine (inferType.SS hA hS he hs).bind fun ty _ _ hty => .stateWF fun wf => ?_
    refine (whnf.SS hA hS (hty.dom wf he) (hty S hS hs)).bind fun appType _ _ hat => ?_
    have hat' := hty.trans hat
    rw [mkNullaryCtor_agree hA (hat' S hS hs)]
    split
    · split; · exact .pure trivial
      extract_lets jp
      have hjp {s} : RecM.SS c₁ c₂ s (jp ()) (jp ()) fun _ _ => True := by
        simp only [jp]; split
        · rename_i n hn
          have hn' : SuppBelow c₁ e n := fun S hS h => mkNullaryCtor_supp hS.2 hn (hat' S hS h)
          refine .stateWF fun wf => (inferType.SS hA hS (hn'.dom wf he) (hn' S hS hs)).bind
            fun t _ _ ht => .stateWF fun wf => ?_
          refine (isDefEq.SS hA hS (hat'.dom wf he) ((hn'.trans ht).dom wf he) (hat' S hS hs)
            ((hn'.trans ht) S hS hs)).bind fun _ _ _ _ => ?_
          split <;> exact .pure trivial
        · exact .pure trivial
      split
      · refine (RecM.SS.forIn'_range (Inv := fun r : Option Expr × Unit => True)
          (fun _ _ _ _ _ => ?_) trivial).bind fun r _ _ _ => ?_
        · split <;> exact .pure trivial
        · dsimp only; split
          · exact .pure trivial
          · exact hjp
      · exact hjp
    · exact .pure trivial
  · exact .panic trivial

theorem toCtorWhenStruct.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) (hI : S.const I) :
    RecM.SS c₁ c₂ s (toCtorWhenStruct c₁.env whnf inferType I e : RecM _)
      (toCtorWhenStruct c₂.env whnf inferType I e) fun e₁ _ => SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (toCtorWhenStruct.SWF he) ?_
  unfold toCtorWhenStruct
  rw [isNonRecStructure_agree hA hI, isConstructorApp?'_agree hA hs]
  split; · exact .pure trivial
  refine (inferType.SS hA hS he hs).bind fun ty _ _ hty => .stateWF fun wf => ?_
  refine (whnf.SS hA hS (hty.dom wf he) (hty S hS hs)).bind
    fun eType _ _ het => .stateWF fun wf => ?_
  have het' := hty.trans het
  split; · exact .pure trivial
  refine (inferType.SS hA hS (het'.dom wf he) (het' S hS hs)).bind
    fun ty' _ _ hty' => .stateWF fun wf => ?_
  refine (whnf.SS hA hS ((het'.trans hty').dom wf he) ((het'.trans hty') S hS hs)).bind
    fun _ _ _ _ => ?_
  rw [expandEtaStruct_agree hA hS (het' S hS hs)]
  split
  · split <;> exact .pure trivial
  · exact .pure trivial

theorem inductiveReduceRec.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (inductiveReduceRec c₁.env e whnf inferType isDefEq : RecM _)
      (inductiveReduceRec c₂.env e whnf inferType isDefEq) fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (inductiveReduceRec.SWF he) ?_
  unfold inductiveReduceRec
  split <;> [skip; exact .pure trivial]
  rename_i recFn ls heq
  have hrec := getAppFn_const_supp hs heq
  rw [hA.env recFn hrec]
  split <;> [skip; exact .pure trivial]
  rename_i info hfind
  extract_lets recArgs majorIdx jp3 jp2 jp1 jp2' jp1'
  have hargs : ∀ a ∈ recArgs, a.SuppIn S := Expr.SuppIn.getAppArgs hs
  have hjp2 {major s} (hm : major.SuppIn S) :
      RecM.SS c₁ c₂ s (jp2 () major) (jp2' () major) fun _ _ => True := by
    simp only [jp2, jp2', jp3]
    split <;> [skip; exact .pure trivial]
    rename_i rule hrule
    have hctor : S.const rule.ctor := by
      unfold getRecRuleFor at hrule
      split at hrule <;> [skip; cases hrule]
      rename_i fn _ hfn
      have := List.find?_some hrule
      simp only [beq_iff_eq] at this
      rw [this]; exact getAppFn_const_supp hm hfn
    rw [hA.env _ hctor]
    split <;> [skip; exact .pure trivial]
    split; · exact .pure trivial
    split; · exact .pure trivial
    split <;> exact .pure trivial
  have hjp1 {major s} (hm : SuppBelow c₁ e major) :
      RecM.SS c₁ c₂ s (jp1 () major) (jp1' () major) fun _ _ => True := by
    simp only [jp1, jp1']
    refine .stateWF fun wf => (whnf.SS hA hS (hm.dom wf he) (hm S hS hs)).bind
      fun major' _ _ hm' => ?_
    have hm' := hm.trans hm'
    split
    · rename_i n _
      exact hjp2 (Expr.SuppIn.natLitToConstructor (hm' S hS hs : Expr.SuppIn S (.lit (.natVal n))))
    · rename_i str _
      have hd : Dom c₁ (Expr.strLitToConstructor str) :=
        dom_iff.2 (Expr.SuppIn.strLitToConstructor ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩)
      have hss := Expr.SuppIn.strLitToConstructor
        (hm' S hS hs : Expr.SuppIn S (.lit (.strVal str)))
      exact (whnf.SS hA hS hd hss).bind fun _ _ _ h => hjp2 (h S hS hss)
    · refine .stateWF fun wf => (toCtorWhenStruct.SS hA hS (hm'.dom wf he) (hm' S hS hs)
        (hS.2.find _ _ hfind hrec).2.1).bind fun _ _ _ h => hjp2 (h S hS (hm' S hS hs))
  split <;> [skip; exact .pure trivial]
  rename_i major0 hmajor0
  have hm0 : SuppBelow c₁ e major0 := fun S hS h =>
    Expr.SuppIn.getAppArgs h _ (Array.mem_of_getElem? hmajor0)
  dsimp only
  split
  · exact .stateWF fun wf => (toCtorWhenK.SS hA hS (hm0.dom wf he) (hm0 S hS hs)).bind
      fun _ _ _ h => hjp1 (hm0.trans h)
  · exact hjp1 hm0

theorem reduceRecursor.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceRecursor e) (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (reduceRecursor.SWF he) ?_
  unfold reduceRecursor
  refine .getEnv ?_
  rw [hA.quotInit]
  extract_lets jp jp'
  have tail {s} : RecM.SS c₁ c₂ s (jp ()) (jp' ()) fun _ _ => True :=
    (inductiveReduceRec.SS hA hS he hs).bind fun _ _ _ _ => by
      split <;> exact .pure trivial
  split
  · refine (quotReduceRec.SS hA hS he hs).bind fun _ _ _ _ => ?_
    split
    · exact .pure trivial
    · exact tail
  · exact tail

theorem whnfCore'.save.SS {c₁ c₂ : Context} {s : State} (he : Dom c₁ e)
    (h1 : SuppBelow c₁ e e₁) :
    RecM.SS c₁ c₂ s (whnfCore'.save e cheapProj e₁) (whnfCore'.save e cheapProj e₁)
      fun r _ => SuppBelow c₁ e r := by
  refine fun _ hm => ⟨save.SWF he h1 _ hm.swf, fun _ _ _ => ?_⟩
  simp only [save]; split <;> exact fun h _ => h

theorem whnfCore'.loop.SS {S : Supp} {c₁ c₂ : Context} {s : State} {e f : Expr}
    {rargs : Array Expr} (hA : Agree S c₁ c₂) (hS : S.Closed c₁) (he : Dom c₁ e)
    (hs : e.SuppIn S) (hargs : ∀ S, S.Closed c₁ → e.SuppIn S → ∀ a ∈ rargs, a.SuppIn S)
    (hf : SuppBelow c₁ e f) :
    RecM.SS c₁ c₂ s (whnfCore'.loop e cheapProj rargs m f) (whnfCore'.loop e cheapProj rargs m f)
      fun e₁ _ => SuppBelow c₁ e e₁ := by
  have hcont {m f s} (hf : SuppBelow c₁ e f) :
      RecM.SS c₁ c₂ s (whnfCore'.loop.cont e cheapProj rargs m f)
        (whnfCore'.loop.cont e cheapProj rargs m f) fun e₁ _ => SuppBelow c₁ e e₁ := by
    unfold whnfCore'.loop.cont
    have hr : SuppBelow c₁ e ((f.instantiateRange (rargs.size - m) rargs.size rargs).mkAppRevRange
        0 (rargs.size - m) rargs) := fun S hS h =>
      Expr.SuppIn.mkAppRevRange hS.2.dummy (hargs S hS h)
        (Expr.SuppIn.instantiateRange (hargs S hS h) (hf S hS h))
    refine .stateWF fun wf => (whnfCore.SS hA hS (hr.dom wf he) (hr S hS hs)).bind
      fun _ _ _ h => ?_
    exact save.SS he (hr.trans h)
  unfold whnfCore'.loop; split
  · split
    · exact whnfCore'.loop.SS hA hS he hs hargs fun S hS h => (hf S hS h).2
    · exact hcont hf
  · exact hcont hf
termination_by rargs.size - m

theorem whnfCore'.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (whnfCore' e cheapProj) (whnfCore' e cheapProj)
      fun e₁ _ => SuppBelow c₁ e e₁ := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : State) => _) = P
  have hid {s} : RecM.SS c₁ c₂ s (pure e) (pure e) P := hP ▸ .pure .rfl
  suffices hF : full e → RecM.SS c₁ c₂ s (F ⟨⟩) (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · exact hP ▸ whnfCore'.SS (e := _) hA hS he hs
    · refine .getLCtx ?_; rw [isLetFVar_agree hA hs]; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    exact fun S hS h => (wf.whnfCore _ _ eq).2 S hS he h
  have hsave {e₁ s} (h1 : SuppBelow c₁ e e₁) :
      RecM.SS c₁ c₂ s (save e cheapProj e₁) (save e cheapProj e₁) P :=
    hP ▸ save.SS he h1
  split <;> cases hfull
  · exact hP ▸ whnfFVar.SS hA hS hs
  · rename_i fn arg _
    generalize fn.app arg = e at *
    have hargs S (_ : S.Closed c₁) (h : e.SuppIn S) := Expr.SuppIn.getAppRevArgs h
    have hf0 : Dom c₁ e.getAppFn := dom_iff.2 (dom_iff.1 he).getAppFn
    refine (whnfCore.SS hA hS hf0 hs.getAppFn).bind fun f _ _ hf => .stateWF fun wf => ?_
    have hf' : SuppBelow c₁ e f := fun S hS h => hf S hS h.getAppFn
    split
    · exact hP ▸ loop.SS hA hS he hs hargs fun S hS h => (hf' S hS h : Expr.SuppIn S (.lam ..)).2
    split
    · refine (reduceRecursor.SS hA hS he hs).bind fun _ _ _ h => ?_
      split
      · have h := h _ rfl
        exact hP ▸ (whnfCore.SS hA hS (h.dom ‹_› he) (h S hS hs)).mono
          fun _ _ _ h' => h.trans h'
      · exact hid
    · have hr : SuppBelow c₁ e (f.mkAppRevRange 0 e.getAppRevArgs.size e.getAppRevArgs) :=
        fun S hS h => Expr.SuppIn.mkAppRevRange hS.2.dummy (hargs S hS h) (hf' S hS h)
      refine (whnfCore.SS hA hS (hr.dom wf he) (hr S hS hs)).bind fun _ _ _ h =>
        hsave (hr.trans h)
  · rename_i n ty val body nd _
    have hr : SuppBelow c₁ (.letE n ty val body nd) (body.instantiate1' val) := fun S hS h =>
      Expr.SuppIn.instantiate1 h.2.1 h.2.2
    refine .stateWF fun wf => (whnfCore.SS hA hS (hr.dom wf he) (hr S hS hs)).bind
      fun _ _ _ h => hsave (hr.trans h)
  · rename_i tn idx st _
    have hst : Dom c₁ st := he
    refine (reduceProj.SS hA hS hst hs).bind fun _ _ _ h => ?_
    split
    · have h : SuppBelow c₁ (.proj tn idx st) _ := fun S hS h' => h _ rfl S hS h'
      exact .stateWF fun wf => (whnfCore.SS hA hS (h.dom wf he) (h S hS hs)).bind
        fun _ _ _ h' => hsave (h.trans h')
    · exact hsave .rfl

theorem unfoldDefinitionCore.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (unfoldDefinitionCore e) (unfoldDefinitionCore e)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) unfoldDefinitionCore.SWF ?_
  unfold unfoldDefinitionCore
  split <;> [skip; exact .pure trivial]
  refine .getEnv ?_
  rw [isDelta_agree hA hs]
  split <;> [skip; exact .pure trivial]
  rename_i d hd
  split <;> [skip; exact .pure trivial]
  refine .get ?_
  split
  · exact .pure trivial
  · refine fun _ hm => ⟨?_, fun _ _ _ eq _ => by revert eq; exact id⟩
    intro wf a s' eq
    cases eq
    refine ⟨{ wf with unfold := fun e' r' h' S hS he' => ?_ }, .rfl, trivial⟩
    rw [Std.HashMap.getElem?_insert] at h'; split at h'
    · cases h'; rename_i eq
      exact isDelta_supp hS hd (Expr.SuppIn.eqv_rev eq he')
    · exact wf.unfold _ _ h' S hS he'

theorem unfoldDefinition.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (unfoldDefinition e) (unfoldDefinition e)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) unfoldDefinition.SWF ?_
  unfold unfoldDefinition
  split
  · refine (unfoldDefinitionCore.SS hA hs.getAppFn).bind fun _ _ _ _ => ?_
    split <;> exact .pure trivial
  · exact (unfoldDefinitionCore.SS hA hs).mono fun _ _ _ _ => trivial

theorem reduceBinNatOp.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (ha : Dom c₁ a) (hb : Dom c₁ b) (has : a.SuppIn S) (hbs : b.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceBinNatOp f a b) (reduceBinNatOp f a b) fun _ _ => True := by
  unfold reduceBinNatOp
  refine (whnf.SS hA hS ha has).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (whnf.SS hA hS hb hbs).bind fun _ _ _ _ => ?_
  split <;> exact .pure trivial

theorem reducePow.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (ha : Dom c₁ a) (hb : Dom c₁ b) (has : a.SuppIn S) (hbs : b.SuppIn S) :
    RecM.SS c₁ c₂ s (reducePow a b) (reducePow a b) fun _ _ => True := by
  unfold reducePow
  refine (whnf.SS hA hS ha has).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (whnf.SS hA hS hb hbs).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  split <;> exact .pure trivial

theorem reduceBinNatPred.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (ha : Dom c₁ a) (hb : Dom c₁ b) (has : a.SuppIn S) (hbs : b.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceBinNatPred f a b) (reduceBinNatPred f a b) fun _ _ => True := by
  unfold reduceBinNatPred
  refine (whnf.SS hA hS ha has).bind fun _ _ _ _ => ?_
  split <;> [skip; exact .pure trivial]
  refine (whnf.SS hA hS hb hbs).bind fun _ _ _ _ => ?_
  split <;> exact .pure trivial

theorem reduceNat.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (reduceNat e) (reduceNat e)
      fun oe _ => ∀ e₁, oe = some e₁ → SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (reduceNat.SWF he) ?_
  unfold reduceNat; extract_lets nargs jp fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> simp only [Bool.false_eq_true, ↓reduceIte]; · exact .pure trivial
    split <;> [skip; exact .pure trivial]
    rename_i f us a b
    have ha : Dom c₁ a := fun fv h => he fv (by simp [Expr.fvarsList, h])
    have hb : Dom c₁ b := fun fv h => he fv (by simp [Expr.fvarsList, h])
    have hop {g s} := reduceBinNatOp.SS (f := g) (s := s) hA hS ha hb hs.1.2 hs.2
    have hpow {s} := reducePow.SS (s := s) hA hS ha hb hs.1.2 hs.2
    have hpred {g s} := reduceBinNatPred.SS (f := g) (s := s) hA hS ha hb hs.1.2 hs.2
    by_cases hX : (f == ``Nat.add) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.sub) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.mul) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.pow) = true
    · rw [if_pos hX]; exact hpow
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.gcd) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.mod) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.div) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.beq) = true
    · rw [if_pos hX]; exact hpred
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.ble) = true
    · rw [if_pos hX]; exact hpred
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.land) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.lor) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.xor) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.shiftLeft) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    by_cases hX : (f == ``Nat.shiftRight) = true
    · rw [if_pos hX]; exact hop
    rw [if_neg hX]
    exact .pure trivial
  · split <;> [skip; exact .pure trivial]
    have hd : Dom c₁ e.appArg! := dom_iff.2 (Expr.SuppIn.appArg! trivial (dom_iff.1 he))
    refine (whnf.SS hA hS hd (Expr.SuppIn.appArg! hS.2.dummy hs)).bind fun _ _ _ _ => ?_
    split <;> exact .pure trivial

theorem whnf'.SS {S : Supp} {c₁ c₂ : Context} {s : State} (hA : Agree S c₁ c₂)
    (hS : S.Closed c₁) (he : Dom c₁ e) (hs : e.SuppIn S) :
    RecM.SS c₁ c₂ s (whnf' e) (whnf' e) fun e₁ _ => SuppBelow c₁ e e₁ := by
  refine .of_swf (Q' := fun _ _ => True) (whnf'.SWF he) ?_
  unfold whnf'; extract_lets F
  have hid {s} : RecM.SS c₁ c₂ s (pure e) (pure e) fun _ _ => True := .pure trivial
  suffices hF : RecM.SS c₁ c₂ s (F ()) (F ()) fun _ _ => True by
    split
    any_goals exact hid
    any_goals exact hF
    · rename_i _ e'
      exact (whnf'.SS (e := e') hA hS he hs).mono fun _ _ _ _ => trivial
    · refine .getLCtx ?_; rw [isLetFVar_agree hA hs]; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · exact .pure trivial
  have loop {e' n s} (he' : Dom c₁ e') (hs' : e'.SuppIn S) :
      RecM.SS c₁ c₂ s (loop e' n) (loop e' n) fun e₁ _ => SuppBelow c₁ e' e₁ := by
    refine .of_swf (Q' := fun _ _ => True) ?_ ?_
    · exact (show RecM.SWF c₁ s (loop e' n) fun e₁ _ => SuppBelow c₁ e' e₁ by
        clear hs'
        induction n generalizing s e' with | zero => exact .throw | succ n ih => ?_
        refine .getEnv <| (whnfCore'.SWF he').bind fun e₁ _ _ h1 => .stateWF fun wf => ?_
        refine (M.SWF.liftExcept reduceNative.SWF).lift.bind fun _ _ _ h3 => ?_
        split <;> [cases h3; skip]
        refine (reduceNat.SWF (h1.dom wf he')).bind fun _ _ _ h3 => ?_; split
        · exact .pure (h1.trans (h3 _ rfl))
        refine unfoldDefinition.SWF.bind fun _ _ _ H => ?_
        split <;> [skip; exact .pure h1]
        have H := h1.trans (H _ rfl)
        exact (ih (H.dom wf he')).mono fun _ _ _ h => H.trans h)
    induction n generalizing s e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.SS hA hS he' hs').bind fun e₁ _ _ h1 => .stateWF fun wf => ?_
    refine (RecM.SS.liftExcept reduceNative.SWF fun _ h => h).bind fun _ _ _ h3 => ?_
    split <;> [cases h3; skip]
    refine (reduceNat.SS hA hS (h1.dom wf he') (h1 S hS hs')).bind fun _ _ _ h3 => ?_; split
    · exact .pure trivial
    refine (unfoldDefinition.SS hA (h1 S hS hs')).bind fun _ _ _ H => ?_
    split <;> [skip; exact .pure trivial]
    have H := h1.trans (H _ rfl)
    exact ih (H.dom wf he') (H S hS hs')
  refine .readThe ?_
  rw [hA.eagerReduce, hA.fuel]
  refine (loop he hs).bind fun e₁ s _ h1 => ?_
  refine fun _ hm => ⟨?_, fun _ _ _ eq _ => by revert eq; exact id⟩
  rintro wf a s' ⟨⟩
  exact ⟨{ wf with whnf := CondSupp.insert wf.whnf (CondSupp.of wf he h1) }, .rfl, trivial⟩

end Inner
end TypeChecker
end Lean4Lean

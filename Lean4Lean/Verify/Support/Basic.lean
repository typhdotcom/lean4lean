import Lean4Lean.Verify.TypeChecker.Basic

/-!
# What an expression mentions

`Expr.SuppIn S e`: every free variable, level parameter and constant `e` mentions is allowed by
`S`. A literal mentions the constants the kernel expands it into. The type checker's outputs
mention nothing their inputs, the local context and the environment do not
(`Lean4Lean.Verify.Support.TypeChecker`); the lemmas here are the syntactic half of that.
-/

namespace Lean4Lean
open Lean

/-- The free variables, level parameters and constants an expression may mention. -/
structure Supp where
  fv : FVarId → Prop
  lvl : Name → Prop
  const : Name → Prop

/-- `S` allows everything `S'` does not forbid. -/
structure Supp.LE (S S' : Supp) : Prop where
  fv : ∀ x, S.fv x → S'.fv x
  lvl : ∀ x, S.lvl x → S'.lvl x
  const : ∀ x, S.const x → S'.const x

instance : LE Supp := ⟨Supp.LE⟩

theorem Supp.LE.rfl {S : Supp} : S ≤ S := ⟨fun _ => id, fun _ => id, fun _ => id⟩

theorem Supp.LE.trans {S₁ S₂ S₃ : Supp} (h₁ : S₁ ≤ S₂) (h₂ : S₂ ≤ S₃) : S₁ ≤ S₃ :=
  ⟨fun _ h => h₂.fv _ (h₁.fv _ h), fun _ h => h₂.lvl _ (h₁.lvl _ h),
    fun _ h => h₂.const _ (h₁.const _ h)⟩

end Lean4Lean

namespace Lean
open Lean4Lean

/-- Every level parameter `l` mentions satisfies `P`. -/
def Level.LParamsIn (P : Name → Prop) : Level → Prop
  | .zero | .mvar _ => True
  | .succ l => l.LParamsIn P
  | .max a b | .imax a b => a.LParamsIn P ∧ b.LParamsIn P
  | .param n => P n

/-- The constants the kernel expands a literal into. -/
def Literal.SuppIn (C : Name → Prop) : Literal → Prop
  | .natVal _ => C ``Nat ∧ C ``Nat.zero ∧ C ``Nat.succ
  | .strVal _ => C ``String ∧ C ``String.ofList ∧ C ``Char ∧ C ``Char.ofNat ∧ C ``List.nil ∧
    C ``List.cons ∧ C ``Nat ∧ C ``Nat.zero ∧ C ``Nat.succ

/-- Every free variable, level parameter and constant `e` mentions is allowed by `S`. A
projection's structure name is not a mention: the kernel only compares it with the head of the
structure's type, and never looks it up. -/
def Expr.SuppIn (S : Supp) : Expr → Prop
  | .bvar _ | .mvar _ => True
  | .fvar fv => S.fv fv
  | .sort u => u.LParamsIn S.lvl
  | .const c us => S.const c ∧ ∀ u ∈ us, u.LParamsIn S.lvl
  | .lit l => l.SuppIn S.const
  | .app f a => f.SuppIn S ∧ a.SuppIn S
  | .lam _ d b _ | .forallE _ d b _ => d.SuppIn S ∧ b.SuppIn S
  | .letE _ t v b _ => t.SuppIn S ∧ v.SuppIn S ∧ b.SuppIn S
  | .mdata _ e => e.SuppIn S
  | .proj _ _ e => e.SuppIn S

namespace Level

theorem LParamsIn.mono {P Q : Name → Prop} (H : ∀ x, P x → Q x) {l : Level}
    (h : l.LParamsIn P) : l.LParamsIn Q := by
  induction l <;> simp_all [LParamsIn]


theorem LParamsIn.mkLevelMax' {P : Name → Prop} {u v : Level} (hu : u.LParamsIn P)
    (hv : v.LParamsIn P) : (mkLevelMax' u v).LParamsIn P := by
  let subsumes (u v : Level) : Bool :=
    if v.isExplicit && u.getOffset ≥ v.getOffset then true
    else match u with
      | Level.max u₁ u₂ => v == u₁ || v == u₂
      | _ => false
  let mkLevelMaxCore (u v : Level) :=
    if u == v then u
    else if u.isZero then v
    else if v.isZero then u
    else if subsumes u v then u
    else if subsumes v u then v
    else if u.getLevelOffset == v.getLevelOffset then
      if u.getOffset ≥ v.getOffset then u else v
    else
      .max u v
  change (mkLevelMaxCore u v).LParamsIn P
  simp only [mkLevelMaxCore]
  repeat' split
  all_goals first | exact hu | exact hv | exact ⟨hu, hv⟩

theorem LParamsIn.mkLevelIMax' {P : Name → Prop} {u v : Level} (hu : u.LParamsIn P)
    (hv : v.LParamsIn P) : (mkLevelIMax' u v).LParamsIn P := by
  let mkLevelIMaxCore (u v : Level) :=
    if v.isNeverZero then _root_.Lean.mkLevelMax' u v
    else if v.isZero then v
    else if u.isZero then v
    else if u == v then u
    else Level.imax u v
  change (mkLevelIMaxCore u v).LParamsIn P
  simp only [mkLevelIMaxCore]
  repeat' split
  all_goals first | exact hu | exact hv | exact ⟨hu, hv⟩ | exact hu.mkLevelMax' hv

theorem LParamsIn.substParams' {P Q : Name → Prop} {s : Name → Level}
    (hs : ∀ x, P x → (s x).LParamsIn Q) :
    ∀ {l : Level} {red}, l.LParamsIn P → (l.substParams' s red).LParamsIn Q
  | .zero, _, _ | .mvar _, _, _ => trivial
  | .succ l, _, h => LParamsIn.substParams' (l := l) hs h
  | .max a b, red, ⟨h1, h2⟩ => by
    simp only [Level.substParams']; split
    · exact (LParamsIn.substParams' hs h1).mkLevelMax' (LParamsIn.substParams' hs h2)
    · exact ⟨LParamsIn.substParams' hs h1, LParamsIn.substParams' hs h2⟩
  | .imax a b, red, ⟨h1, h2⟩ => by
    simp only [Level.substParams']; split
    · exact (LParamsIn.substParams' hs h1).mkLevelIMax' (LParamsIn.substParams' hs h2)
    · exact ⟨LParamsIn.substParams' hs h1, LParamsIn.substParams' hs h2⟩
  | .param n, _, h => hs n h

theorem LParamsIn.of_hasParam' {P : Name → Prop} : ∀ {l : Level}, l.hasParam' = false → l.LParamsIn P
  | .zero, _ | .mvar _, _ => trivial
  | .succ l, h => LParamsIn.of_hasParam' (l := l) h
  | .max a b, h | .imax a b, h => by
    simp only [hasParam', Bool.or_eq_false_iff] at h
    exact ⟨LParamsIn.of_hasParam' h.1, LParamsIn.of_hasParam' h.2⟩
  | .param _, h => by cases h

theorem getUndefParam_eq_none_iff {l : Level} {ps : List Name} :
    l.getUndefParam ps = none ↔ l.LParamsIn (· ∈ ps) := by
  suffices ∀ s, ((l.forEach (getUndefParam.F ps)).run s).run.snd = none ↔
      s = none ∧ l.LParamsIn (· ∈ ps) from (this none).trans (by simp)
  intro s
  induction l generalizing s with
  | succ l ih =>
    rw [Level.forEach]; simp only [getUndefParam.F]
    cases s <;> by_cases h : l.succ.hasParam' <;> simp [h, ih, LParamsIn]
    exact LParamsIn.of_hasParam' (by simpa [hasParam'] using h)
  | max a b iha ihb =>
    rw [Level.forEach]; simp only [getUndefParam.F]
    cases s <;> by_cases h : (a.max b).hasParam' <;> simp [h, iha, ihb, LParamsIn]
    simp only [hasParam', Bool.not_eq_true, Bool.or_eq_false_iff] at h
    exact ⟨LParamsIn.of_hasParam' h.1, LParamsIn.of_hasParam' h.2⟩
  | imax a b iha ihb =>
    rw [Level.forEach]; simp only [getUndefParam.F]
    cases s <;> by_cases h : (a.imax b).hasParam' <;> simp [h, iha, ihb, LParamsIn]
    simp only [hasParam', Bool.not_eq_true, Bool.or_eq_false_iff] at h
    exact ⟨LParamsIn.of_hasParam' h.1, LParamsIn.of_hasParam' h.2⟩
  | param n =>
    rw [Level.forEach]; simp only [getUndefParam.F]
    cases s <;> simp [hasParam', LParamsIn]; split <;> simp_all
  | _ => rw [Level.forEach]; cases s <;> simp [getUndefParam.F, hasParam', LParamsIn]

end Level

namespace Literal

theorem SuppIn.mono {C C' : Name → Prop} (H : ∀ x, C x → C' x) :
    ∀ {l : Literal}, l.SuppIn C → l.SuppIn C'
  | .natVal _, ⟨a, b, c⟩ => ⟨H _ a, H _ b, H _ c⟩
  | .strVal _, ⟨a, b, c, d, e, f, g, h, i⟩ =>
    ⟨H _ a, H _ b, H _ c, H _ d, H _ e, H _ f, H _ g, H _ h, H _ i⟩

end Literal

namespace Expr

theorem SuppIn.mono {S S' : Supp} (H : S ≤ S') {e : Expr} (h : e.SuppIn S) : e.SuppIn S' := by
  induction e <;> simp_all [SuppIn]
  · exact H.fv _ h
  · exact h.mono H.lvl
  · exact ⟨H.const _ h.1, fun u hu => (h.2 u hu).mono H.lvl⟩
  · exact h.mono H.const

theorem SuppIn.liftLooseBVars {S : Supp} :
    ∀ {e : Expr} {s d}, e.SuppIn S → (e.liftLooseBVars' s d).SuppIn S := by
  intro e; induction e <;> intros <;> simp_all [SuppIn, liftLooseBVars']

theorem SuppIn.lowerLooseBVars {S : Supp} :
    ∀ {e : Expr} {s d}, e.SuppIn S → (e.lowerLooseBVars' s d).SuppIn S := by
  intro e; induction e <;> intros <;> unfold lowerLooseBVars' <;> split <;>
    simp_all [SuppIn]

theorem SuppIn.instantiate1 {S : Supp} {a : Expr} (ha : a.SuppIn S) :
    ∀ {e : Expr} {d}, e.SuppIn S → (e.instantiate1' a d).SuppIn S := by
  intro e; induction e <;> intros <;> simp_all [SuppIn, instantiate1']
  split <;> [simp [SuppIn]; split <;> simp [SuppIn, ha.liftLooseBVars]]

theorem SuppIn.inst1 {S : Supp} {a e : Expr} (ha : a.SuppIn S) (he : e.SuppIn S) :
    (e.instantiate1 a).SuppIn S := by
  rw [instantiate1_eq]; exact SuppIn.instantiate1 ha he

theorem SuppIn.instantiateList {S : Supp} {as : List Expr} (ha : ∀ a ∈ as, a.SuppIn S) :
    ∀ {e : Expr} {k}, e.SuppIn S → (e.instantiateList as k).SuppIn S := by
  induction as with
  | nil => exact fun h => h
  | cons a as ih =>
    intro e k h
    exact ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (SuppIn.instantiate1 (ha a (.head _)) h)

theorem SuppIn.instantiateRevList {S : Supp} {as : List Expr} (ha : ∀ a ∈ as, a.SuppIn S) :
    ∀ {e : Expr} {k}, e.SuppIn S → (e.instantiateRevList as k).SuppIn S := by
  induction as with
  | nil => exact fun h => h
  | cons a as ih =>
    intro e k h
    exact SuppIn.instantiate1 (ha a (.head _)) (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h)

theorem SuppIn.instantiate' {S : Supp} {as : List Expr} (ha : ∀ a ∈ as, a.SuppIn S) :
    ∀ {e : Expr} {d}, e.SuppIn S → (e.instantiate' as d).SuppIn S := by
  intro e; induction e <;> intros <;> simp_all [SuppIn, Expr.instantiate']
  split
  · simp [SuppIn]
  · split
    · exact (ha _ (List.getElem_mem _)).liftLooseBVars
    · simp [SuppIn]

theorem SuppIn.instantiate {S : Supp} {e : Expr} {as : Array Expr}
    (ha : ∀ a ∈ as, a.SuppIn S) (h : e.SuppIn S) : (e.instantiate as).SuppIn S := by
  rw [instantiate_eq']; exact SuppIn.instantiate' (fun a h => ha a (by simpa using h)) h

theorem SuppIn.instantiateRev {S : Supp} {e : Expr} {as : Array Expr}
    (ha : ∀ a ∈ as, a.SuppIn S) (h : e.SuppIn S) : (e.instantiateRev as).SuppIn S := by
  rw [instantiateRev_eq]; exact h.instantiate fun a h => ha a (by simpa using h)

theorem SuppIn.instantiateRevRange {S : Supp} {e : Expr} {as : Array Expr} {i j : Nat}
    (ha : ∀ a ∈ as, a.SuppIn S) (h : e.SuppIn S) :
    (e.instantiateRevRange i j as).SuppIn S := by
  rw [instantiateRevRange_eq]
  exact h.instantiateRev fun a h => ha a (Array.mem_def.2 (List.mem_of_mem_drop (List.mem_of_mem_take
    (by rwa [Array.mem_def, Array.toList_extract] at h))))

theorem SuppIn.instantiateRange {S : Supp} {e : Expr} {as : Array Expr} {i j : Nat}
    (ha : ∀ a ∈ as, a.SuppIn S) (h : e.SuppIn S) :
    (e.instantiateRange i j as).SuppIn S := by
  rw [instantiateRange_eq]
  exact h.instantiate fun a h => ha a (Array.mem_def.2 (List.mem_of_mem_drop (List.mem_of_mem_take
    (by rwa [Array.mem_def, Array.toList_extract] at h))))

theorem SuppIn.abstract1 {S : Supp} {v : FVarId} :
    ∀ {e : Expr} {k}, e.SuppIn ⟨fun x => S.fv x ∨ x = v, S.lvl, S.const⟩ →
      (e.abstract1 v k).SuppIn S := by
  intro e; induction e <;> intros <;> simp_all [SuppIn, Expr.abstract1]
  split <;> simp_all [SuppIn]; exact (‹_ ∨ _›).resolve_right (Ne.symm ‹_›)

theorem SuppIn.abstract' {S : Supp} {vs : List FVarId} : ∀ {e : Expr} {k},
    e.SuppIn ⟨fun x => S.fv x ∨ x ∈ vs, S.lvl, S.const⟩ → (e.abstract' vs k).SuppIn S := by
  intro e; induction e <;> intros <;> simp_all [SuppIn, Expr.abstract']
  rename_i v _ h
  split
  · simp [SuppIn]
  · rename_i hv; refine h.resolve_right fun hm => ?_
    rw [List.idxOf?_eq_none_iff] at hv; exact hv (List.mem_reverse.2 hm)

theorem SuppIn.abstractList {S : Supp} : ∀ {vs : List FVarId} {e : Expr} {k},
    e.SuppIn ⟨fun x => S.fv x ∨ x ∈ vs, S.lvl, S.const⟩ → (e.abstractList vs k).SuppIn S
  | [], e, _, h => by
    show e.SuppIn S
    exact SuppIn.mono (S := ⟨fun x => S.fv x ∨ x ∈ [], S.lvl, S.const⟩) (S' := S)
      ⟨fun _ hx => by simpa using hx, fun _ => id, fun _ => id⟩ h
  | v :: vs, e, k, h => by
    show ((e.abstract1 v k).abstractList vs k).SuppIn S
    refine SuppIn.abstractList (vs := vs) (SuppIn.abstract1 (SuppIn.mono
      (S := ⟨fun x => S.fv x ∨ x ∈ v :: vs, S.lvl, S.const⟩)
      (S' := ⟨fun x => (S.fv x ∨ x ∈ vs) ∨ x = v, S.lvl, S.const⟩)
      ⟨fun x hx => ?_, fun _ => id, fun _ => id⟩ h))
    simp only [List.mem_cons] at hx; rcases hx with hx | hx | hx
    · exact .inl (.inl hx)
    · exact .inr hx
    · exact .inl (.inr hx)

theorem SuppIn.appRevList {S : Supp} {f : Expr} :
    ∀ {es : List Expr}, (f.mkAppRevList es).SuppIn S ↔ f.SuppIn S ∧ ∀ e ∈ es, e.SuppIn S
  | [] => by simp [mkAppRevList]
  | _ :: _ => by simp [mkAppRevList, SuppIn, SuppIn.appRevList, and_comm, and_left_comm]

theorem SuppIn.appList {S : Supp} {f : Expr} {es : List Expr} :
    (f.mkAppList es).SuppIn S ↔ f.SuppIn S ∧ ∀ e ∈ es, e.SuppIn S := by
  rw [← mkAppRevList_reverse, SuppIn.appRevList]; simp

theorem SuppIn.getAppFn {S : Supp} : ∀ {e : Expr}, e.SuppIn S → e.getAppFn.SuppIn S
  | .app f _, h => SuppIn.getAppFn (e := f) h.1
  | .bvar .., h | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lam .., h
  | .forallE .., h | .letE .., h | .lit .., h | .mdata .., h | .proj .., h => h

theorem SuppIn.getAppArgsRevList {S : Supp} {e : Expr} (h : e.SuppIn S) :
    ∀ a ∈ e.getAppArgsRevList, a.SuppIn S := by
  rw [← mkAppRevList_getAppArgsRevList e] at h
  exact (SuppIn.appRevList.1 h).2


theorem SuppIn.default {S : Supp} (h : S.const `_inhabitedExprDummy) : (default : Expr).SuppIn S := by
  show (Expr.const _ []).SuppIn S; exact ⟨h, nofun⟩

theorem SuppIn.getRevArg! {S : Supp} (hd : S.const `_inhabitedExprDummy) :
    ∀ {e : Expr} {i}, e.SuppIn S → (e.getRevArg! i).SuppIn S
  | .app _ a, 0, h => h.2
  | .app f _, i+1, h => SuppIn.getRevArg! hd (e := f) (i := i) h.1
  | .bvar .., _, _ | .fvar .., _, _ | .mvar .., _, _ | .sort .., _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit .., _, _
  | .mdata .., _, _ | .proj .., _, _ => by
    simpa [Expr.getRevArg!] using SuppIn.default hd

theorem SuppIn.appFn! {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr} (h : e.SuppIn S) :
    e.appFn!.SuppIn S := by
  cases e <;> simp_all [Expr.appFn!, SuppIn] <;> exact SuppIn.default hd

theorem SuppIn.appArg! {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr} (h : e.SuppIn S) :
    e.appArg!.SuppIn S := by
  cases e <;> simp_all [Expr.appArg!, SuppIn] <;> exact SuppIn.default hd

theorem SuppIn.bindingBody! {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr} (h : e.SuppIn S) :
    e.bindingBody!.SuppIn S := by
  cases e <;> simp_all [Expr.bindingBody!, SuppIn] <;> exact SuppIn.default hd

theorem SuppIn.bindingDomain! {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr} (h : e.SuppIn S) :
    e.bindingDomain!.SuppIn S := by
  cases e <;> simp_all [Expr.bindingDomain!, SuppIn] <;> exact SuppIn.default hd

theorem SuppIn.getAppArgs {S : Supp} {e : Expr} (h : e.SuppIn S) :
    ∀ a ∈ e.getAppArgs, a.SuppIn S := by
  intro a ha
  rw [getAppArgs_eq_rev] at ha
  exact h.getAppArgsRevList a (by simpa using ha)

theorem SuppIn.getAppRevArgs {S : Supp} {e : Expr} (h : e.SuppIn S) :
    ∀ a ∈ e.getAppRevArgs, a.SuppIn S := by
  intro a ha
  rw [getAppRevArgs_eq] at ha
  exact h.getAppArgsRevList a (by simpa using ha)

theorem SuppIn.getElem! {S : Supp} (hd : S.const `_inhabitedExprDummy) {as : Array Expr}
    (h : ∀ a ∈ as, a.SuppIn S) {i : Nat} : as[i]!.SuppIn S := by
  rw [getElem!_def]; split
  · exact h _ (Array.mem_of_getElem? ‹_›)
  · exact SuppIn.default hd

open private mkAppRangeAux from Lean.Expr in
theorem SuppIn.mkAppRange_aux {S : Supp} (hd : S.const `_inhabitedExprDummy) {as : Array Expr}
    (h : ∀ a ∈ as, a.SuppIn S) {j : Nat} : ∀ {i f}, f.SuppIn S → (mkAppRangeAux j as i f).SuppIn S
  | i, f, hf => by
    rw [mkAppRangeAux]; split
    · exact SuppIn.mkAppRange_aux hd h ⟨hf, SuppIn.getElem! hd h⟩
    · exact hf
termination_by i => j - i

theorem SuppIn.mkAppRange {S : Supp} (hd : S.const `_inhabitedExprDummy) {as : Array Expr}
    (h : ∀ a ∈ as, a.SuppIn S) {f : Expr} (hf : f.SuppIn S) {i j : Nat} :
    (_root_.Lean.mkAppRange f i j as).SuppIn S := SuppIn.mkAppRange_aux hd h hf

open private mkAppRevRangeAux from Lean.Expr in
theorem SuppIn.mkAppRevRange_aux {S : Supp} (hd : S.const `_inhabitedExprDummy)
    {as : Array Expr} (h : ∀ a ∈ as, a.SuppIn S) {j : Nat} :
    ∀ {i f}, f.SuppIn S → (mkAppRevRangeAux as j f i).SuppIn S
  | i, f, hf => by
    rw [mkAppRevRangeAux]; split
    · exact hf
    · exact SuppIn.mkAppRevRange_aux hd h ⟨hf, SuppIn.getElem! hd h⟩
termination_by i => i

theorem SuppIn.mkAppRevRange {S : Supp} (hd : S.const `_inhabitedExprDummy) {as : Array Expr}
    (h : ∀ a ∈ as, a.SuppIn S) {f : Expr} (hf : f.SuppIn S) {i j : Nat} :
    (f.mkAppRevRange i j as).SuppIn S := SuppIn.mkAppRevRange_aux hd h hf

theorem SuppIn.mkAppN {S : Supp} {as : Array Expr}
    (h : ∀ a ∈ as, a.SuppIn S) {f : Expr} (hf : f.SuppIn S) :
    (_root_.Lean.mkAppN f as).SuppIn S := by
  rw [_root_.Lean.mkAppN, ← Array.foldl_toList]
  have h' : ∀ a ∈ as.toList, a.SuppIn S := fun a ha => h a (by simpa using ha)
  clear h; generalize as.toList = l at h'
  induction l generalizing f with
  | nil => exact hf
  | cons a l ih => exact ih ⟨hf, h' a (.head _)⟩ (fun b hb => h' b (.tail _ hb))

theorem SuppIn.betaReduce {S : Supp} {e e' : Expr} (H : BetaReduce e e') (h : e.SuppIn S) :
    e'.SuppIn S := by
  induction H with
  | refl => exact h
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)
  | app _ ih => exact ⟨ih h.1, h.2⟩
  | beta => exact SuppIn.instantiate1 h.2 h.1.2

theorem SuppIn.lambdaBodyN {S : Supp} {n : Nat} {e fn : Expr} (H : LambdaBodyN n e fn)
    (h : e.SuppIn S) : fn.SuppIn S := by
  induction H with
  | zero => exact h
  | succ _ ih => exact ih h.2

theorem SuppIn.cheapBetaReduce_cont {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr}
    (h : e.SuppIn S) {i fn} (H : LambdaBodyN i e.getAppFn fn) :
    (Expr.cheapBetaReduce.cont e e.getAppArgs i fn).SuppIn S := by
  unfold Expr.cheapBetaReduce.cont; split
  · exact SuppIn.mkAppRange hd h.getAppArgs (h.getAppFn.lambdaBodyN H)
  · split
    · split
      · exact SuppIn.mkAppRange hd h.getAppArgs (SuppIn.getElem! hd h.getAppArgs)
      · exact SuppIn.default hd
    · exact h

theorem SuppIn.cheapBetaReduce_loop {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr}
    (h : e.SuppIn S) {i fn} (H : LambdaBodyN i e.getAppFn fn) :
    (Expr.cheapBetaReduce.loop e e.getAppArgs i fn).SuppIn S := by
  unfold Expr.cheapBetaReduce.loop; split
  · split
    · exact SuppIn.cheapBetaReduce_loop hd h (by simpa [Nat.add_comm] using H.add (.succ .zero))
    · exact SuppIn.cheapBetaReduce_cont hd h H
  · exact SuppIn.cheapBetaReduce_cont hd h H
termination_by e.getAppArgs.size - i

theorem SuppIn.cheapBetaReduce {S : Supp} (hd : S.const `_inhabitedExprDummy) {e : Expr}
    (h : e.SuppIn S) : e.cheapBetaReduce.SuppIn S := by
  simp only [Expr.cheapBetaReduce]
  split; · exact h
  split; · exact h
  exact SuppIn.cheapBetaReduce_loop hd h .zero

theorem SuppIn.eqv {S : Supp} {e₁ e₂ : Expr} : e₁ == e₂ → e₁.SuppIn S → e₂.SuppIn S := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; revert ‹SuppIn ..›; simp [SuppIn]
  all_goals grind

theorem SuppIn.eqv_rev {S : Supp} {e₁ e₂ : Expr} : e₁ == e₂ → e₂.SuppIn S → e₁.SuppIn S := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; revert ‹SuppIn ..›; simp [SuppIn]
  all_goals grind

theorem SuppIn.instantiateLevelParams {S : Supp} {e : Expr} {ps : List Name} {ls : List Level}
    (h : e.SuppIn ⟨S.fv, (· ∈ ps), S.const⟩) (hls : ∀ l ∈ ls, l.LParamsIn S.lvl)
    (hlen : ps.length = ls.length) : (e.instantiateLevelParams ps ls).SuppIn S := by
  rw [instantiateLevelParams_eq]
  generalize (!ps.isEmpty && !ls.isEmpty) = red
  have hs : ∀ x, x ∈ ps → (((ps.idxOf? x).bind (ls[·]?)).getD (.param x)).LParamsIn S.lvl := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, ps.idxOf? x = some i := by
      cases h : ps.idxOf? x
      · simp [List.idxOf?_eq_none_iff] at h; exact absurd hx h
      · exact ⟨_, rfl⟩
    have hi' : i < ls.length := hlen ▸ (List.idxOf?_eq_some_iff.1 hi).1
    simp [hi, List.getElem?_eq_getElem hi']
    exact hls _ (List.getElem_mem _)
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', SuppIn]
  · exact h.substParams' hs
  · exact fun u hu => (h.2 u hu).substParams' hs

theorem SuppIn.natLitToConstructor {S : Supp} {n : Nat}
    (h : S.const ``Nat ∧ S.const ``Nat.zero ∧ S.const ``Nat.succ) :
    (Expr.natLitToConstructor n).SuppIn S := by
  cases n <;> simp_all [Expr.natLitToConstructor, Expr.natZero, Expr.natSucc, SuppIn,
    Literal.SuppIn]

theorem SuppIn.strLitToConstructor {S : Supp} {s : String} (h : (Literal.strVal s).SuppIn S.const) :
    (Expr.strLitToConstructor s).SuppIn S := by
  simp only [Literal.SuppIn] at h
  simp only [Expr.strLitToConstructor, SuppIn]
  refine ⟨⟨h.2.1, nofun⟩, ?_⟩
  induction s.toList <;> simp_all [SuppIn, Level.LParamsIn, Literal.SuppIn]

theorem SuppIn.toConstructor {S : Supp} {l : Literal} (h : l.SuppIn S.const) :
    l.toConstructor.SuppIn S := by
  cases l with
  | natVal => exact SuppIn.natLitToConstructor h
  | strVal => exact SuppIn.strLitToConstructor h

theorem SuppIn.toExprBool {S : Supp} {b : Bool} (h : S.const ``Bool.true ∧ S.const ``Bool.false) :
    (toExpr b).SuppIn S := by
  cases b <;> simp [toExpr, SuppIn, h]

end Expr
end Lean

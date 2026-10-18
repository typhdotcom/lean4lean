import Lean4Lean.Theory.Typing.LogRel.ProjSound

/-!
# Realizing constructor applications in the model

An interpretation of a constant applied to arguments is built by `LE_Interp.apps_realize` from a
`Const` derivation, given a shape for the whole application typed at an interpretation of its
type. For a constructor application that shape is a constructor shape, typed at an inductive type
shape whose field telescope the fields fit. The telescope is built here as a pi type shape with a
single point per binder (`piTele`), at the shapes of a valuation fitting the constructor's type.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv}

/-- A pi type shape for a telescope with one point per binder: at each binder its domain shape
and the argument shape it is defined at, then the codomain shape `r`. -/
def piTele : List (TShape × TShape) → TShape → TShape
  | [], r => r
  | (b, x) :: L, r =>
    let i := piTele L r
    (WShape.forallE (b.2.lift (max b.1 (max x.1 i.1)))
      (WShapeFun.single (x.2.lift (max b.1 (max x.1 i.1)))
        (i.2.lift (max b.1 (max x.1 i.1))))).T

theorem PiAppS.mono_h {h h' : TShape} (hh : h ≤ h') {as : List TShape} {m : TShape} :
    PiAppS h as m → PiAppS h' as m
  | .nil h1 => .nil (h1.trans hh)
  | .cons h1 h2 h3 => .cons (h1.trans hh) h2 h3

/-- The telescope's codomain at its argument shapes. -/
theorem piTele_piAppS : ∀ (L : List (TShape × TShape)) (r : TShape),
    PiAppS (piTele L r) (L.map (·.2)) r
  | [], r => .nil .rfl
  | (b, x) :: L, r => by
    have ih := piTele_piAppS L r
    have hn1 : x.1 ≤ max b.1 (max x.1 (piTele L r).1) := by omega
    have hn2 : (piTele L r).1 ≤ max b.1 (max x.1 (piTele L r).1) := by omega
    refine .cons .rfl (TShape.lift_eqv hn1).1 ?_
    rw [WShape.piApp, WShape.piCod_forallE, WShape.lam'_app, WShapeFun.single_app,
      if_pos WShape.LE.rfl]
    exact PiAppS.mono_h (TShape.lift_eqv hn2).2 ih

/-- The telescope interprets a pi type whose binders its domain shapes interpret, at the
argument shapes before them, when each argument shape is typed at its domain. -/
theorem piTele_interp : ∀ (L : List (TShape × TShape)) (Δ : List VExpr) {σ : Valuation}
    {B : VExpr} {r : TShape}, L.length = Δ.length →
    (∀ j b x A, L[j]? = some (b, x) → Δ[j]? = some A →
      LE_Interp env (pushAll σ ((L.take j).map (·.2))) b A ∧ x.HasType b) →
    LE_Interp env (pushAll σ (L.map (·.2))) r B →
    LE_Interp env σ (piTele L r) (.foralls Δ B)
  | [], [], _, _, _, _, _, hr => hr
  | [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, h, _, _ => by cases h
  | (b, x) :: L, A :: Δ, σ, B, r, hl, hj, hr => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have ⟨h0, hx⟩ := hj 0 b x A rfl rfl
    simp only [List.take_zero, List.map_nil, pushAll] at h0
    have ih := piTele_interp L Δ (σ := σ.push x) hl
      (fun j b' x' A' h1 h2 => by simpa [pushAll] using hj (j+1) b' x' A' h1 h2)
      (by simpa [pushAll] using hr)
    let n := max b.1 (max x.1 (piTele L r).1)
    have hn0 : b.1 ≤ n := by omega
    have hn1 : x.1 ≤ n := by omega
    have hn2 : (piTele L r).1 ≤ n := by omega
    show LE_Interp env σ (WShape.forallE (b.2.lift n) (WShapeFun.single (x.2.lift n)
      ((piTele L r).2.lift n))).T _
    refine .forallE' (h0.lift hn0) (h0.lift hn0)
      (WShape.HasDom.single.2 (.inl ((TShape.HasType.def hn1 hn0).1 hx))) fun y hy => ?_
    rw [WShapeFun.single_app]
    split
    · rename_i hxy
      refine (ih.lift hn2).mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
      exact (TShape.lift_eqv hn1).2.trans (WShape.LE.T hxy)
    · exact .bot

/-- The telescope is a type when its argument shapes are typed at its domains and its codomain is
a type. -/
theorem piTele_typed : ∀ (L : List (TShape × TShape)) {r : TShape} {rel : Bool},
    (∀ b x, (b, x) ∈ L → x.HasType b) → r.HasType (TShape.sort rel) →
    (piTele L r).HasType (TShape.sort rel)
  | [], _, _, _, hr => hr
  | (b, x) :: L, r, rel, hL, hr => by
    have ih := piTele_typed L (fun b' x' h => hL b' x' (.tail _ h)) hr
    let n := max b.1 (max x.1 (piTele L r).1)
    have hn0 : b.1 ≤ n := by omega
    have hn1 : x.1 ≤ n := by omega
    have hn2 : (piTele L r).1 ≤ n := by omega
    show (WShape.forallE (b.2.lift n) (WShapeFun.single (x.2.lift n)
      ((piTele L r).2.lift n))).T.HasType _
    have hx : (x.2.lift n).HasType (b.2.lift n) :=
      (TShape.HasType.def hn1 hn0).1 (hL b x (.head _))
    have hi : ((piTele L r).2.lift n).HasType (.sort rel) := by
      have := (TShape.HasType.def hn2 (Nat.zero_le n)).1 ih
      simpa [TShape.sort, WShape.lift_sort] using this
    refine (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2 ?_
    simp only [WShape.lift_self, TShape.sort, WShape.lift_sort]
    refine WShape.HasType.forallE (WShape.HasTypePi.def.2
      ⟨WShape.HasDom.single.2 (.inl hx), fun y z hyz => ?_⟩)
    rcases WShapeFun.mem_single.1 hyz with h | ⟨-, h⟩ <;> cases h
    · exact hi
    · exact .bot' .sort


/-- Argument shapes typed at the telescope's domains fit it. -/
theorem piTele_fitsPi : ∀ (L : List (TShape × TShape)) (r : TShape) (n : Nat),
    (∀ b x, (b, x) ∈ L → x.HasType b) → (piTele L r).1 ≤ n + 1 →
    (∀ x ∈ L.map (·.2), x.1 ≤ n + 1) →
    WShape.FitsPi ((piTele L r).2.lift (n+1)) (L.map fun p => p.2.2.lift (n+1))
  | [], _, _, _, _, _ => .nil
  | (b, x) :: L, r, n, hL, hle, hxs => by
    let k := max b.1 (max x.1 (piTele L r).1)
    have hk : k ≤ n := by simpa [piTele] using hle
    have hk0 : b.1 ≤ k := by omega
    have hk1 : x.1 ≤ k := by omega
    have hk2 : (piTele L r).1 ≤ k := by omega
    have hx1 : x.1 ≤ n + 1 := hxs x (.head _)
    show WShape.FitsPi ((WShape.forallE (b.2.lift k) (WShapeFun.single (x.2.lift k)
      ((piTele L r).2.lift k))).lift (n+1)) _
    rw [WShape.lift_forallE hk, WShapeFun.lift_single hk, List.map_cons]
    refine .cons ?_ ?_
    · rw [WShape.lift_lift (.inl hk), WShape.lift_lift (.inl (by omega))]
      exact (TShape.HasType.def hx1 (by omega)).1 (hL b x (.head _))
    · rw [WShapeFun.lift_single (Nat.le_succ n), WShapeFun.single_app,
        WShape.lift_lift (.inl hk), WShape.lift_lift (.inl hk), WShape.lift_lift (.inl (by omega)),
        if_pos WShape.LE.rfl,
        WShape.lift_lift (.inl (by omega))]
      exact piTele_fitsPi L r n (fun b' x' h => hL b' x' (.tail _ h)) (by omega)
        (fun x' h => hxs x' (.tail _ h))


theorem LE_Interp.Valuation.Fits.cons_inv {Δ : List VExpr} {A : VExpr} {σ : Valuation}
    (H : Valuation.Fits env [] (A :: Δ) σ) : ∃ ρ x a, σ = ρ.push x ∧
      Valuation.Fits env [] Δ ρ ∧
      (∀ {a}, LE_Interp env ρ a A → ∃ a', a ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType .type) ∧
      LE_Interp env ρ a A ∧ x.HasType a := by
  generalize e : A :: Δ = Δ' at H
  cases H with
  | nil => cases e
  | cons W h1 h2 h3 => cases e; exact ⟨_, _, _, rfl, W, h1, h2, h3⟩

theorem Valuation.push_inj {ρ ρ' : Valuation} {x x' : TShape} (h : ρ.push x = ρ'.push x') :
    ρ = ρ' ∧ x = x' :=
  ⟨funext fun i => congrFun h (i+1), congrFun h 0⟩

/-- The binders of a telescope a valuation fits: at each, a domain shape that is a type,
interpreting the binder's type at the values before it, at which the value is typed. -/
theorem Valuation.Fits.tele : ∀ (n : Nat) (Δ : List VExpr) (P : List TShape), Δ.length = n →
    P.length = n → Valuation.Fits env [] Δ.reverse (pushAll .nil P) →
    ∃ L : List (TShape × TShape), L.map (·.2) = P ∧ L.length = n ∧
      ∀ j b x A, L[j]? = some (b, x) → Δ[j]? = some A →
        LE_Interp env (pushAll .nil ((L.take j).map (·.2))) b A ∧ x.HasType b ∧
        b.HasType TShape.type
  | 0, Δ, P, h1, h2, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero h1
    obtain rfl := List.eq_nil_of_length_eq_zero h2
    exact ⟨[], rfl, rfl, fun _ _ _ _ h => by cases h⟩
  | n+1, Δ, P, h1, h2, W => by
    obtain ⟨Δ, A, rfl⟩ := List.eq_nil_or_concat Δ |>.resolve_left (by rintro rfl; cases h1)
    obtain ⟨P, x, rfl⟩ := List.eq_nil_or_concat P |>.resolve_left (by rintro rfl; cases h2)
    simp only [List.concat_eq_append, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at h1 h2 W
    rw [List.reverse_append, pushAll_concat] at W
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at W
    obtain ⟨a, W, hA, ha, hx⟩ : ∃ a, Valuation.Fits env [] Δ.reverse (pushAll .nil P) ∧
        (∀ {a}, LE_Interp env (pushAll .nil P) a A →
          ∃ a', a ≤ a' ∧ LE_Interp env (pushAll .nil P) a' A ∧ a'.HasType .type) ∧
        LE_Interp env (pushAll .nil P) a A ∧ x.HasType a := by
      obtain ⟨ρ, x', a, e, W, h1, h2, h3⟩ := W.cons_inv
      obtain ⟨rfl, rfl⟩ := Valuation.push_inj e
      exact ⟨a, W, h1, h2, h3⟩
    obtain ⟨L, hL1, hL2, hL3⟩ := Valuation.Fits.tele n Δ P h1 h2 W
    obtain ⟨a', hle, ha', hty⟩ := hA ha
    have hx' : x.HasType a' := TShape.HasType.mono_r hle hty hx
    refine ⟨L ++ [(a', x)], by simp [hL1], by simp [hL2], fun j b y B hj hB => ?_⟩
    rw [List.concat_eq_append] at hB
    have hjl : j < n + 1 := by
      have := (List.getElem?_eq_some_iff.1 hj).1; simp [hL2] at this; omega
    by_cases hjn : j < n
    · rw [List.getElem?_append_left (by omega)] at hj
      rw [List.getElem?_append_left (by omega)] at hB
      rw [List.take_append_of_le_length (by omega)]
      exact hL3 j b y B hj hB
    · obtain rfl : j = n := by omega
      rw [List.getElem?_append_right (by omega), hL2, Nat.sub_self] at hj
      rw [List.getElem?_append_right (by omega), h1, Nat.sub_self] at hB
      cases hj; cases hB
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), hL1]
      exact ⟨ha', hx', hty⟩


theorem WShape.ctysOK_of {N : Nat} {h : IndHead} {pre ctys : List (WShape N)}
    (hpre : pre.length = h.nargs) (hcty : ∀ x ∈ ctys, x.HasType .type) :
    Shape.ctysOK Shape.hasType h ((pre ++ ctys).map (·.1)) = true := by
  unfold Shape.ctysOK
  rw [List.map_append, List.drop_append_of_le_length (by simp [hpre]),
    List.drop_of_length_le (by simp [hpre]), List.nil_append, List.all_eq_true]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact hcty y hy

/-- A constructor shape whose fields fit its telescope, recorded in an inductive type shape whose
telescopes are types, is typed at it, and the inductive type shape is a type. -/
theorem WShape.ctor'_typed {N : Nat} {h : IndHead} {pre ctys : List (WShape (N+1))} {c : Name}
    {i : Nat} {cty : WShape (N+1)} {l : List (WShape (N+1))}
    (hpre : pre.length = h.nargs) (hi : h.ctors.idxOf? c = some i) (hc : ctys[i]? = some cty)
    (hcty : ∀ x ∈ ctys, x.HasType .type) (hfit : WShape.FitsPi cty l)
    (har : h.arityOK c l.length = true) :
    (WShape.ctor' c l).HasType (.indTy true h (pre ++ ctys)) ∧
      (WShape.indTy true h (pre ++ ctys)).HasType (.sort true) := by
  have hok := WShape.ctysOK_of hpre hcty
  refine ⟨WShape.HasType.ctor' ?_, WShape.HasType.indTy (.inl rfl) hok⟩
  unfold Shape.ctorOK Shape.ctorTy
  rw [hok, Bool.true_and, hi, Option.map_some]
  have e : ((pre ++ ctys).map (·.1)).getD (h.nargs + i) Shape.bot = cty.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_append_right (by omega),
      hpre, Nat.add_sub_cancel_left, hc]; rfl
  simp only [e, Shape.ctorFits, List.length_map, har, Bool.and_true]
  exact WShape.fitsPi_iff.2 hfit


theorem PiAppS.mono_m {h : TShape} : ∀ {as : List TShape} {m m' : TShape}, m' ≤ m →
    PiAppS h as m → PiAppS h as m'
  | _, _, _, hm, .nil h1 => .nil (hm.trans h1)
  | _, _, _, hm, .cons h1 h2 h3 => .cons h1 h2 (PiAppS.mono_m hm h3)

theorem PiAppS.mono_args {h : TShape} : ∀ {as as' : List TShape} {m : TShape},
    List.Forall₂ (· ≤ ·) as as' → PiAppS h as m → PiAppS h as' m
  | _, _, _, .nil, H => H
  | _, _, _, .cons ha hl, .cons h1 h2 h3 => .cons h1 (h2.trans ha) (PiAppS.mono_args hl h3)

theorem PiAppS.bot : ∀ (as : List TShape), PiAppS TShape.bot as TShape.bot
  | [] => .nil .rfl
  | _ :: as => .cons (f := (WShape.bot : WShape (0+1))) (x := (WShape.bot : WShape 0))
      TShape.bot_eqv.1 TShape.bot_le' (by
        have : (WShape.bot : WShape (0+1)).piApp .bot = .bot := by
          simp [WShape.piApp, WShape.piCod_bot, WShape.bot_app]
        rw [this]; exact PiAppS.mono_h TShape.bot_eqv.2 (PiAppS.bot as))

/-- A telescope's codomain at its first argument shapes is the telescope of the rest. -/
theorem piTele_append_piAppS : ∀ (L₁ L₂ : List (TShape × TShape)) (r : TShape),
    PiAppS (piTele (L₁ ++ L₂) r) (L₁.map (·.2)) (piTele L₂ r)
  | [], _, _ => .nil .rfl
  | (b, x) :: L₁, L₂, r => by
    rw [List.cons_append]
    have ih := piTele_append_piAppS L₁ L₂ r
    have hn1 : x.1 ≤ max b.1 (max x.1 (piTele (L₁ ++ L₂) r).1) := by omega
    have hn2 : (piTele (L₁ ++ L₂) r).1 ≤ max b.1 (max x.1 (piTele (L₁ ++ L₂) r).1) := by omega
    refine .cons .rfl (TShape.lift_eqv hn1).1 ?_
    rw [WShape.piApp, WShape.piCod_forallE, WShape.lam'_app, WShapeFun.single_app,
      if_pos WShape.LE.rfl]
    exact PiAppS.mono_h (TShape.lift_eqv hn2).2 ih


/-- An inductive type applied to its parameters and indices, typed in the model: the arguments
along the type's telescope, and its type the block's sort. -/
theorem typeSpine (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env) (hle : envT ≤ env)
    (hO : envT.Ordered) {d : VInductDecl} {T : VInductiveType} {s : Name}
    (hTW : T.WF envT d) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩) {ls : List VLevel} {U : Nat}
    (hls : ∀ l ∈ ls, l.WF U) {Γ As I : List VExpr} {T' : VExpr}
    (hn : (As ++ I).length = d.params.length + T.indices.length)
    (H : MSpine env Γ ((VExpr.const s ls).appN (As ++ I)) T') :
    TeleSubst env Γ ((d.params ++ T.indices).map (·.instL ls)) (As ++ I) ∧
      SoundEq env Γ T' (.sort (d.level.inst ls)) := by
  have hQT : envT.IsTele U [] ((d.params ++ T.indices).map (·.instL ls)) := by
    simpa using ((hPT.append (by simpa using hTW.indices)).instL hls (Γ := []))
  obtain ⟨_, hdef⟩ := hTW.defeq
  have hdef' := hdef.instL hls (ls := ls)
  rw [VEnv.foralls_instL'] at hdef'
  have hRcl := (hdef'.closedN' hO.closed trivial).2.1
  have hTcl : (T.type.instL ls).ClosedN := (hdef'.closedN' hO.closed trivial).1
  have := MSpine.spine hM
    (Qs := (d.params ++ T.indices).map (·.instL ls)) (R := .sort (d.level.inst ls))
    (fun i A hA => ⟨by simpa using VEnv.IsTele.closedN hO hQT trivial i A hA,
      by simpa using IsTele.soundAt hM hX hle hO hQT trivial i A hA⟩)
    hRcl (fun ci hci _ => by
      cases hcT.symm.trans hci
      exact SoundEq.closed hM hTcl hRcl
        (hX.strongSound' hM hle hO (Γ := []) trivial hdef').sound)
    (As ++ I).length (As ++ I) rfl (by simp [hn]) H
  rw [List.take_of_length_le (by simp [hn]), List.drop_of_length_le (by simp [hn])] at this
  exact this


theorem forall₂_le_of_pushAll {ys P : List TShape} (hl : ys.length = P.length)
    (h : ∀ i < ys.length, pushAll .nil ys i ≤ pushAll .nil P i) : List.Forall₂ (· ≤ ·) ys P := by
  refine List.forall₂_of_getElem? hl fun j a b ha hb => ?_
  have hj : j < ys.length := (List.getElem?_eq_some_iff.1 ha).1
  have := h (ys.length - 1 - j) (by omega)
  rw [pushAll_apply, pushAll_apply, dif_pos (by omega), dif_pos (by omega),
    List.getElem_reverse, List.getElem_reverse] at this
  obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  have e1 : ys.length - 1 - (ys.length - 1 - j) = j := by omega
  have e2 : P.length - 1 - (ys.length - 1 - j) = j := by omega
  simpa only [e1, e2] using this

theorem forall₂_lift {ρ : Valuation} {K : Nat} : ∀ {xs : List TShape} {As : List VExpr},
    (∀ x ∈ xs, x.1 ≤ K) → List.Forall₂ (fun y x => LE_Interp env ρ y x) xs As →
    List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) (xs.map fun x => x.2.lift K) As
  | _, _, _, .nil => .nil
  | _, _, hK, .cons h hl => .cons (h.lift (hK _ (.head _)))
      (forall₂_lift (fun x hx => hK x (.tail _ hx)) hl)

theorem forall₂_le_lift {K : Nat} : ∀ {xs : List TShape}, (∀ x ∈ xs, x.1 ≤ K) →
    List.Forall₂ (· ≤ ·) xs (xs.map fun x => (x.2.lift K).T)
  | [], _ => .nil
  | _ :: _, hK => .cons (TShape.lift_eqv (hK _ (.head _))).2
      (forall₂_le_lift fun x hx => hK x (.tail _ hx))

theorem forall₂_le_trans : ∀ {xs ys zs : List TShape}, List.Forall₂ (· ≤ ·) xs ys →
    List.Forall₂ (· ≤ ·) ys zs → List.Forall₂ (· ≤ ·) xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 h2, .cons h3 h4 => .cons (h1.trans h3) (forall₂_le_trans h2 h4)

theorem forall₂_bot {ρ : Valuation} {n : Nat} : ∀ (I : List VExpr),
    List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A)
      (I.map fun _ => (WShape.bot : WShape n)) I
  | [] => .nil
  | _ :: I => .cons .bot (forall₂_bot I)

/-- A level above every shape of a list. -/
def maxLvl (l : List TShape) : Nat := l.foldr (fun x n => max x.1 n) 0

theorem le_maxLvl : ∀ {l : List TShape} {x : TShape}, x ∈ l → x.1 ≤ maxLvl l
  | _ :: _, _, .head _ => Nat.le_max_left ..
  | _ :: _, _, .tail _ h => Nat.le_trans (le_maxLvl h) (Nat.le_max_right ..)


/-- A constructor application typed at its inductive type, at levels where that is not a
proposition, has an interpretation that is a constructor shape, with fields interpreting the
fields and above any given interpretations of them. -/
theorem ctorApp_realize (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {s : Name} {d : VInductDecl} {t i : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hci : T.ctors[i]? = some c)
    (hidx : (T.ctors.map (·.name)).idxOf? c.name = some i)
    (hTW : T.WF envT d) (hcW : c.WF envT d T) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    {ls : List VLevel} {U : Nat} (hls : ∀ l ∈ ls, l.WF U) (hP : ¬d.PropAt ls)
    {Γ₀ Γ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ)
    {As fs I : List VExpr} {u : VLevel} (hAs : As.length = d.params.length)
    (hfs : fs.length = c.fields.length) (hI : I.length = T.indices.length)
    (hTS : MSpine env Γ ((VExpr.const s ls).appN (As ++ I)) (.sort u))
    (hCS : MSpine env Γ ((VExpr.const c.name ls).appN (As ++ fs))
      ((VExpr.const s ls).appN (As ++ I)))
    {ys : List TShape} (hys : List.Forall₂ (fun y x => LE_Interp env ρ y x) ys (As ++ fs)) :
    ∃ N, ∃ rf : List (WShape N), List.Forall₂ (fun y x => y ≤ x.T) (ys.drop d.params.length) rf ∧
      List.Forall₂ (fun x A => LE_Interp env ρ x.T A) rf fs ∧
      LE_Interp env ρ (WShape.ctor' c.name rf).T ((VExpr.const c.name ls).appN (As ++ fs)) := by
  -- the sort of the inductive type is relevant
  obtain ⟨-, hsort⟩ := typeSpine hM hX hle hO hTW hPT hcT hls (by simp [hAs, hI]) hTS
  have hrel : levelRel u = true := by
    rw [SoundEq.sort.1 hsort]; simpa [levelRel, VInductDecl.PropAt] using hP
  -- the constructor's telescope
  obtain ⟨Ps, Ds, hcty, hPD, hFW, -⟩ := hcW.shape
  have hPs : Ps.length = d.params.length := hPD.length_eq
  have hDs : Ds.length = c.fields.length := hFW.length
  have hcty' : c.type.instL ls = .foralls ((Ps ++ Ds).map (·.instL ls))
      ((T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length c.fields.length)
        c.indices).instL ls) := by
    rw [hcty, VEnv.foralls_instL']
  obtain ⟨_, hcTy⟩ := hcW.type
  have hccl : (c.type.instL ls).ClosedN := (hcTy.closedN hO trivial).instL
  have hQc : envT.IsTele U [] ((Ps ++ Ds).map (·.instL ls)) := by
    have := (VEnv.IsType.foralls_inv hO (by rw [← hcty]; exact ⟨_, hcTy⟩)).1
    simpa using this.instL hls (Γ := [])
  have hn : (As ++ fs).length = ((Ps ++ Ds).map (·.instL ls)).length := by
    simp [hAs, hfs, hPs, hDs]
  have hTSc := (MSpine.spine hM
    (Qs := (Ps ++ Ds).map (·.instL ls)) (R := (T.typeApp (VLevel.params d.uvars)
        (VExpr.bvars d.params.length c.fields.length) c.indices).instL ls)
    (fun i A hA => ⟨by simpa using VEnv.IsTele.closedN hO hQc trivial i A hA,
      by simpa using IsTele.soundAt hM hX hle hO hQc trivial i A hA⟩)
    (hcty' ▸ hccl) (fun ci hci _ => by cases hcC.symm.trans hci; rw [hcty']; exact .rfl)
    (As ++ fs).length (As ++ fs) rfl (by omega) hCS).1
  rw [List.take_of_length_le (by omega)] at hTSc
  -- values fitting it, above `ys`
  obtain ⟨PC, hP1, hP2, hP3⟩ := hTSc.exists_fits hM W (pushAll_consList hys)
  have hPCl : PC.length = (As ++ fs).length := List.Forall₂.length_eq hP1
  have hysl : ys.length = (As ++ fs).length := List.Forall₂.length_eq hys
  have hyP : List.Forall₂ (· ≤ ·) ys PC :=
    forall₂_le_of_pushAll (by omega) (fun i hi => hP3 i (by omega))
  obtain ⟨L, hL1, hL2, hL3⟩ := Valuation.Fits.tele _ _ PC rfl (by omega) hP2
  -- the constructor's type as a telescope of single points, and its fields' part
  have hkey : ∀ b x, (b, x) ∈ L → x.HasType b := by
    intro b x h
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    have hj' : j < ((Ps ++ Ds).map (·.instL ls)).length := by rw [hL2] at hj; exact hj
    exact (hL3 j b x _ (by rw [List.getElem?_eq_getElem hj, e])
      (List.getElem?_eq_getElem hj')).2.1
  have hcI : LE_Interp env ρ (piTele L TShape.bot) (c.type.instL ls) := by
    have := piTele_interp L ((Ps ++ Ds).map (·.instL ls)) (σ := .nil) (r := TShape.bot)
      (B := (T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length c.fields.length)
        c.indices).instL ls) hL2
      (fun j b x A h1 h2 => ⟨(hL3 j b x A h1 h2).1, (hL3 j b x A h1 h2).2.1⟩) .bot
    rw [← hcty'] at this
    exact (closed_iff hM.closed hccl).1 this
  let np := d.params.length
  let Lp := L.take np
  let Lf := L.drop np
  let cty := piTele Lf TShape.bot
  have hPi : PiAppS (piTele L TShape.bot) (Lp.map (·.2)) cty := by
    have := piTele_append_piAppS Lp Lf TShape.bot
    rwa [List.take_append_drop] at this
  have hkeyf : ∀ b x, (b, x) ∈ Lf → x.HasType b := fun b x h => hkey b x (List.mem_of_mem_drop h)
  have hctyT : cty.HasType (TShape.sort true) :=
    piTele_typed Lf hkeyf (WShape.HasType.T (n := 0) (.bot' .sort))
  have hLp : Lp.map (·.2) = PC.take np := by rw [← hL1, List.map_take]
  have hLf : Lf.map (·.2) = PC.drop np := by rw [← hL1, List.map_drop]
  -- a common level
  let K := max cty.1 (maxLvl PC)
  have hK1 : cty.1 ≤ K + 1 := by omega
  have hK2 : ∀ x ∈ PC, x.1 ≤ K + 1 := fun x h => by have := le_maxLvl h; omega
  let lft (x : TShape) : WShape (K+1) := x.2.lift (K+1)
  have hlft : ∀ x ∈ PC, x ≤ (lft x).T ∧ (lft x).T ≤ x := fun x h =>
    ⟨(TShape.lift_eqv (hK2 x h)).2, (TShape.lift_eqv (hK2 x h)).1⟩
  let params := (Lp.map (·.2)).map lft
  let rfN := (Lf.map (·.2)).map lft
  let idx : List (WShape (K+1)) := I.map fun _ => .bot
  let ctyK : WShape (K+1) := cty.2.lift (K+1)
  let ctys : List (WShape (K+1)) :=
    (List.range T.ctors.length).map fun j => if j = i then ctyK else .bot
  let hd : IndHead := ⟨s, d.params.length + T.indices.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩
  have hil : i < T.ctors.length := (List.getElem?_eq_some_iff.1 hci).1
  have hplen : params.length = np := by
    simp [params, Lp, hL2]; omega
  have hidxl : idx.length = T.indices.length := by simp [idx, hI]
  have hctysi : ctys[i]? = some ctyK := by simp [ctys, hil]
  have hctysT : ∀ x ∈ ctys, x.HasType .type := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    split
    · have := (TShape.HasType.def hK1 (Nat.zero_le _)).1 hctyT
      simpa [TShape.sort, WShape.lift_sort] using this
    · exact .bot' .sort
  have hfit : WShape.FitsPi ctyK rfN := by
    have := piTele_fitsPi Lf TShape.bot K hkeyf hK1 (fun x hx => hK2 x (by
      rw [hLf] at hx; exact List.mem_of_mem_drop hx))
    show WShape.FitsPi ctyK ((Lf.map (·.2)).map lft)
    rw [List.map_map]; exact this
  have har : hd.arityOK c.name rfN.length = true := by
    have : rfN.length = c.fields.length := by simp [rfN, Lf, hL2, hPs, hDs]; omega
    simp [IndHead.arityOK, hd, hidx, this, hci]
  obtain ⟨hctorTy, hindTy⟩ := WShape.ctor'_typed (N := K) (h := hd) (pre := params ++ idx)
    (by simp [hd, hplen, hidxl, np]) hidx hctysi hctysT hfit har
  -- the arguments' shapes interpret them
  have hPa : List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) params As := by
    have h1 := List.forall₂_take' (k := np) hP1
    rw [List.take_left' hAs] at h1
    have := forall₂_lift (K := K+1) (fun x hx => hK2 x (List.mem_of_mem_take hx)) h1
    rwa [← hLp] at this
  have hFa : List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) rfN fs := by
    have h1 := List.forall₂_drop' (k := np) hP1
    rw [List.drop_left' hAs] at h1
    have := forall₂_lift (K := K+1) (fun x hx => hK2 x (List.mem_of_mem_drop hx)) h1
    rwa [← hLf] at this
  have hIa : List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) idx I := forall₂_bot I
  have hrel' : d.rel ls = true := by simp [VInductDecl.rel, hP]
  -- the inductive type at the arguments, with the constructor's telescope at the parameters
  have hCT : Const env s ls (LE_Interp env ρ) (params ++ idx).reverse
      (WShape.indTy true hd (params ++ idx ++ ctys)).T := by
    have hlT : (params ++ idx).reverse.length = d.params.length + T.indices.length := by
      simp [hplen, hidxl, np]; omega
    refine .indTy (ctys := ctys) hs hT hlT (by simp [ctys]) (fun j c' cty' hc' hcty' => ?_) ?_
    · have hj : j < T.ctors.length := (List.getElem?_eq_some_iff.1 hc').1
      obtain rfl : cty' = if j = i then ctyK else .bot := by
        simp [ctys, hj] at hcty'; exact hcty'.symm
      rw [List.reverse_reverse, List.take_left' hplen]
      by_cases hji : j = i
      · subst hji
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hci)
        rw [if_pos rfl]
        refine ⟨_, hcI, PiAppS.mono_m (TShape.lift_eqv hK1).1 (PiAppS.mono_args ?_ hPi)⟩
        have := forall₂_le_lift (K := K+1) (xs := Lp.map (·.2)) fun x hx => hK2 x (by
          rw [hLp] at hx; exact List.mem_of_mem_take hx)
        simpa [params, lft, List.map_map] using this
      · rw [if_neg hji]
        exact ⟨_, .bot, (PiAppS.bot _).mono_m TShape.bot_eqv.1⟩
    · rw [hrel', hlT, List.reverse_reverse]; exact .rfl
  have hsortI : LE_Interp env ρ (WShape.sort (n := K+2) true).T (.sort u) := by
    refine .sort ?_
    rw [hrel]
    have := (TShape.lift_eqv (a := TShape.sort true) (m := K+2) (Nat.zero_le _)).1
    simpa [TShape.sort, WShape.lift_sort] using this
  have hTyI : LE_Interp env ρ (WShape.indTy true hd (params ++ idx ++ ctys)).T
      ((VExpr.const s ls).appN (As ++ I)) := by
    rw [← spine_eq_appN] at hTS ⊢
    exact LE_Interp.apps_realize hM W (WShape.HasType.T hindTy) hsortI hTS
      ((List.Forall₂.reverse).2 (List.forall₂_append' hPa hIa)) hCT
  -- the constructor application
  have hCC : Const env c.name ls (LE_Interp env ρ) (params ++ rfN).reverse
      (WShape.ctor' c.name rfN).T := by
    refine .ctor hs hT (List.mem_of_getElem? hci) rfl hP (by simp [hplen, rfN, Lf, hL2]; omega) ?_
    rw [List.reverse_reverse, List.drop_left' hplen]; exact .rfl
  have hCI : LE_Interp env ρ (WShape.ctor' c.name rfN).T
      ((VExpr.const c.name ls).appN (As ++ fs)) := by
    rw [← spine_eq_appN] at hCS ⊢
    exact LE_Interp.apps_realize hM W (WShape.HasType.T hctorTy) hTyI hCS
      ((List.Forall₂.reverse).2 (List.forall₂_append' hPa hFa)) hCC
  refine ⟨K + 1, rfN, ?_, hFa, hCI⟩
  have h1 := List.forall₂_drop' (k := np) hyP
  rw [← hLf] at h1
  have h2 := forall₂_le_lift (K := K+1) (xs := Lf.map (·.2)) fun x hx => hK2 x (by
    rw [hLf] at hx; exact List.mem_of_mem_drop hx)
  have h3 := forall₂_le_trans h1 h2
  simp only [rfN, lft, List.map_map] at h3 ⊢
  exact List.forall₂_map_right_iff.1 (by simpa [List.map_map] using h3)


/-- A proof's interpretations are `bot`. -/
theorem StrongSound.proof_le_bot {U : Nat} {Γ₀ Γ : List VExpr} {ρ : Valuation} {a A : VExpr}
    {l : VLevel} (H1 : StrongSound env U Γ a A) (H2 : StrongSound env U Γ A (.sort l))
    (hl : l ≈ .zero) (W : Valuation.Fits env Γ₀ Γ ρ) {m : TShape} (h : LE_Interp env ρ m a) :
    m ≤ TShape.bot := by
  obtain ⟨_, _, a1, -, a3, a4⟩ := H1.sound W h
  obtain ⟨_, _, b1, -, b3, b4⟩ := H2.sound W a3
  have hr : levelRel l = false := by simp [levelRel, hl]
  have b4' := TShape.HasType.mono_r (by simpa [hr] using b3.le_sort) .sort b4
  exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))

/-- A field's interpretations interpret its projection out of the constructor application. -/
theorem projIota_ge (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hcs : T.ctors = [c])
    (hTW : T.WF envT d) (hcW : c.WF envT d T) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    {Γ : List VExpr} {k : Nat} {f : VField} {fs : List VExpr} {a : VExpr} {ls : List VLevel}
    {As I : List VExpr} {u : VLevel} {U : Nat}
    (hf : c.fields[k]? = some f) (ha : fs[k]? = some a)
    (hls : ∀ l ∈ ls, l.WF U) (hAs : As.length = d.params.length)
    (hfs : fs.length = c.fields.length) (hI : I.length = T.indices.length)
    (hPA : d.ProjAllowed c ls k)
    (hTS : StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u))
    (hCS : StrongSound env U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)))
    (hPT' : StrongSound env U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (.sort (f.level.inst ls)))
    (haS : StrongSound env U Γ a (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))))
    {Γ₀ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ) {m : TShape}
    (hm : LE_Interp env ρ m a) :
    LE_Interp env ρ m (.proj s k ((VExpr.const c.name ls).appN (As ++ fs))) := by
  by_cases hP : d.PropAt ls
  · have hz : f.level.inst ls ≈ .zero := by
      refine ((hPA fun h => ?_).1 f hf)
      exact h [] (by simpa [VLevel.eval] using VLevel.equiv_def.1 hP [])
    exact LE_Interp.mono (haS.proof_le_bot hPT' hz W hm) .bot
  -- interpretations of the arguments: `m` at the field, `bot` elsewhere
  let ys : List TShape := As.map (fun _ => TShape.bot) ++
    (List.range fs.length).map fun j => if j = k then m else TShape.bot
  have hys : List.Forall₂ (fun y x => LE_Interp env ρ y x) ys (As ++ fs) := by
    refine List.forall₂_append' ?_ ?_
    · refine List.forall₂_of_getElem? (by simp) fun j y x hy hx => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
      obtain ⟨_, -, rfl⟩ := hy
      exact LE_Interp.bot (n := 0)
    · refine List.forall₂_of_getElem? (by simp) fun j y x hy hx => ?_
      have hj : j < fs.length := (List.getElem?_eq_some_iff.1 hx).1
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some,
        Option.some.injEq] at hy
      subst hy
      split
      · subst j; cases ha.symm.trans hx; exact hm
      · exact LE_Interp.bot (n := 0)
  obtain ⟨N, rf, hrf, -, hCI⟩ := ctorApp_realize hM hX hle hO hs hT (i := 0) (by simp [hcs])
    (by simp [hcs]) hTW hcW hPT hcT hcC hls hP W hAs hfs hI hTS.mspine' hCS.mspine' hys
  rw [List.drop_left' (by simp [hAs])] at hrf
  have hk : k < fs.length := (List.getElem?_eq_some_iff.1 ha).1
  obtain ⟨y, hy⟩ : ∃ y, rf[k]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by rw [← List.Forall₂.length_eq hrf]; simp [hk])⟩
  have hmy : m ≤ y.T := by
    have hyk : ((List.range fs.length).map fun j => if j = k then m else TShape.bot)[k]? =
        some m := by simp [hk]
    exact hrf.getElem?' hyk hy
  exact .proj hs hT hcs hCI hy hmy

end LogRel
end Lean4Lean

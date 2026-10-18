import Lean4Lean.Verify.Environment.Run

/-!
# Verifying `checkConstructors`

Each constructor's type is walked as the kernel walks it: parameters checked against the block's,
then each field checked to be a type of a small enough sort, positive in a safe block, and finally
the type's result checked to be the block's type at the parameters.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem VExpr.mentions_liftN {ns : List Name} {n : Nat} :
    ∀ (e : VExpr) (k : Nat), (e.liftN n k).mentions ns = e.mentions ns
  | .bvar _, _ | .sort _, _ | .const .., _ => rfl
  | .app f a, k => by simp [VExpr.liftN, VExpr.mentions, mentions_liftN f, mentions_liftN a]
  | .lam A b, k | .forallE A b, k => by
    simp [VExpr.liftN, VExpr.mentions, mentions_liftN A, mentions_liftN b]
  | .proj _ _ e, k => by simp [VExpr.liftN, VExpr.mentions, mentions_liftN e]

theorem VLCtx.find?_not_mentions {ns : List Name} : ∀ {Δ : VLCtx} {v e A},
    (∀ x ∈ Δ, x.2.value.mentions ns = false) → Δ.find? v = some (e, A) → e.mentions ns = false
  | [], _, _, _, _, h => by cases h
  | (ofv, d) :: Δ, v, e, A, H, h => by
    simp only [VLCtx.find?] at h
    split at h
    · cases h; exact H _ (.head _)
    · obtain ⟨⟨e₁, A₁⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      cases h2
      rw [VExpr.mentions_liftN]
      exact find?_not_mentions (fun x hx => H x (.tail _ hx)) h1

theorem _root_.Lean.Literal.toConstructor_anySub {p : Expr → Bool} (l : Literal)
    (hp : ∀ e, p e = true → ∃ c us, e = .const c us ∧ c ∉ [``Nat.zero, ``Nat.succ] ∧
      (l.typeName = ``String → c ∉ [``String.ofList, ``Char.ofNat, ``Char, ``List.nil, ``List.cons])) :
    l.toConstructor.anySub p = false := by
  have hl : ∀ l, p (.lit l) = false := by
    intro l; cases h : p (.lit l); · rfl
    obtain ⟨_, _, ⟨⟩, _⟩ := hp _ h
  have happ : ∀ f a, p (.app f a) = false := by
    intro f a; cases h : p (.app f a); · rfl
    obtain ⟨_, _, ⟨⟩, _⟩ := hp _ h
  have hc (c us) (h : c ∈ [``Nat.zero, ``Nat.succ] ∨ l.typeName = ``String ∧
      c ∈ [``String.ofList, ``Char.ofNat, ``Char, ``List.nil, ``List.cons]) :
      p (.const c us) = false := by
    cases e : p (.const c us); · rfl
    obtain ⟨_, _, ⟨⟩, h1, h2⟩ := hp _ e
    rcases h with h | ⟨h3, h⟩; exacts [absurd h h1, absurd h (h2 h3)]
  cases l with
  | natVal n =>
    cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc,
      Expr.anySub, hc, hl, happ]
  | strVal s =>
    have h1 := hc ``String.ofList [] (.inr ⟨rfl, by simp⟩)
    have h2 := hc ``Char.ofNat [] (.inr ⟨rfl, by simp⟩)
    have h3 := hc ``Char [] (.inr ⟨rfl, by simp⟩)
    have h4 := hc ``List.nil [.zero] (.inr ⟨rfl, by simp⟩)
    have h5 := hc ``List.cons [.zero] (.inr ⟨rfl, by simp⟩)
    simp only [Literal.toConstructor, Expr.strLitToConstructor, Expr.anySub, happ, h1,
      Bool.false_or]
    induction s.toList with
    | nil => simp [Expr.anySub, happ, h3, h4]
    | cons a as ih => simp [Expr.anySub, happ, hl, h2, h3, h5, ih]

/-- A translation mentions a constant only if the expression does, or through a literal or a
projection's type, which is a type a block was recorded for. For the names a block adds, neither
brings them in. -/
theorem TrExprS.not_mentions {venv : VEnv} {Us : List Name} {p : Expr → Bool}
    {ns : List Name} (henv : venv.WF)
    (hns : ∀ c us, p (.const c us) = false → c ∉ ns)
    (hlit : ∀ l, venv.ContainsLits l → l.toConstructor.anySub p = false)
    (hind : ∀ n b, venv.inducts n = some b → n ∉ ns)
    {Δ e e'} (H : TrExprS venv Us Δ e e') (hΔ : Δ.WF venv Us.length)
    (hΔv : ∀ x ∈ Δ, x.2.value.mentions ns = false)
    (he : e.anySub p = false) : e'.mentions ns = false := by
  induction H with
  | bvar h1 | fvar h1 => exact VLCtx.find?_not_mentions hΔv h1
  | sort => rfl
  | const =>
    rename_i c _ _ us _ _ _
    simp only [VExpr.mentions, List.contains_eq_mem, decide_eq_false_iff_not]
    exact hns _ us (by simpa [Expr.anySub] using he)
  | app _ _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    simp [VExpr.mentions, ih1 hΔ hΔv he.1.2, ih2 hΔ hΔv he.2]
  | lam h1 _ _ ih1 ih2 | forallE h1 _ _ _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    have hΔ' : VLCtx.WF venv Us.length ((none, .vlam _) :: _) := ⟨hΔ, nofun, h1⟩
    simp [VExpr.mentions, ih1 hΔ hΔv he.1.2, ih2 hΔ' (by
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact hΔv x hx) he.2]
  | letE h1 _ _ _ _ ih2 ih3 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    have hv := ih2 hΔ hΔv he.1.2
    refine ih3 ⟨hΔ, nofun, h1⟩ (fun x hx => ?_) he.2
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hv
    · exact hΔv x hx
  | lit h1 _ ih => exact ih hΔ hΔv (hlit _ h1)
  | mdata _ ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    exact ih hΔ hΔv he.2
  | proj h1 h2 ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at he
    obtain ⟨_, _, _, _, _, _, _, _, hs, -⟩ := h2.proj_inv henv.ordered hΔ.toCtx
    simp [VExpr.mentions, ih hΔ hΔv he.2, hind _ _ hs]

/-- The constants literals translate through come from before a block of fresh, non-primitive
names: the primitive ones by name, and `Char`, `List.nil` and `List.cons` because `String.ofList`'s
specification types them. -/
theorem Literal.toConstructor_anySub_of_fresh {venv₀ venv : VEnv} {ns : List Name}
    (henv₀ : venv₀.WF) (hprim₀ : venv₀.HasPrimitives)
    (hfresh : ∀ n ∈ ns, venv₀.constants n = none)
    (hnew : ∀ n, venv.constants n ≠ none → venv₀.constants n = none → n ∈ ns)
    (hnp : ∀ n ∈ ns, Environment.primitives.contains n = false)
    {p : Expr → Bool} (hp : ∀ e, p e = true → ∃ c us, e = .const c us ∧ c ∈ ns)
    (l : Literal) (hl : venv.ContainsLits l) : l.toConstructor.anySub p = false := by
  have hprimc {n} (h : n ∈ ns) (s) (hs : (n, s) ∈ primSpecs) : False := by
    have := mem_primSpecs_contains hs; simp [hnp n h] at this
  have hold {n} (hs : ∃ s, (n, s) ∈ primSpecs) (h : venv.contains n) : venv₀.contains n := by
    obtain ⟨s, hs⟩ := hs
    obtain ⟨ci, hci⟩ := h
    cases h0 : venv₀.constants n with
    | some ci => exact ⟨ci, h0⟩
    | none => exact (hprimc (hnew n (by simp [hci]) h0) s hs).elim
  refine l.toConstructor_anySub fun e he => ?_
  obtain ⟨c, us, rfl, hc⟩ := hp e he
  refine ⟨c, us, rfl, ?_, fun hstr => ?_⟩
  · intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hprimc hc (.typeEq .nat) (by simp [primSpecs])
    · exact hprimc hc (.typeEq (.forallE .nat .nat)) (by simp [primSpecs])
  · cases l with
    | natVal => simp [Literal.typeName] at hstr
    | strVal s =>
    obtain ⟨-, hso⟩ := hl
    have ⟨ci, hci⟩ := hold ⟨.stringOfList, by simp [primSpecs]⟩ hso
    obtain ⟨-, hnil, hcons⟩ := hprim₀ (``String.ofList, .stringOfList) (by simp [primSpecs]) ci hci
    have hΓ : OnCtx ([] : List VExpr) (venv₀.IsType 0) := trivial
    obtain ⟨_, _, hnil1, hnil2⟩ := hnil.app_inv henv₀.ordered hΓ
    obtain ⟨_, _, hcons1, -⟩ := hcons.app_inv henv₀.ordered hΓ
    obtain ⟨_, h1, -⟩ := hnil1.const_inv henv₀.ordered hΓ
    obtain ⟨_, h2, -⟩ := hnil2.const_inv henv₀.ordered hΓ
    obtain ⟨_, h3, -⟩ := hcons1.const_inv henv₀.ordered hΓ
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have h0 := hfresh c hc
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact hprimc hc .stringOfList (by simp [primSpecs])
    · exact hprimc hc (.typeEq (.forallE .nat .char)) (by simp [primSpecs])
    · simp [h2] at h0
    · simp [h1] at h0
    · simp [h3] at h0

theorem List.forIn_early_none {β : Type} (bad : Nat → Bool) (r : β) : ∀ (l : List Nat),
    (forIn (m := Id) l ((none : Option β), ()) fun i _ =>
      if bad i = true then pure (ForInStep.done (some r, ())) else pure (.yield (none, ()))).1 = none →
    ∀ i ∈ l, bad i = false
  | [], _ => nofun
  | a :: l, h => by
    simp only [List.forIn_cons] at h
    cases hb : bad a
    · simp only [hb, Bool.false_eq_true, if_false] at h
      intro i hi; rcases List.mem_cons.1 hi with rfl | hi
      · exact hb
      · exact List.forIn_early_none bad r l h i hi
    · simp [hb] at h

theorem Std.Range.forIn_early_none {β : Type} (bad : Nat → Bool) (r : β) (a b : Nat)
    (h : (forIn (m := Id) [a:b] ((none : Option β), ()) fun i _ =>
      if bad i = true then pure (ForInStep.done (some r, ())) else pure (.yield (none, ()))).1 = none) :
    ∀ i, a ≤ i → i < b → bad i = false := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  intro i h1 h2
  refine List.forIn_early_none bad r _ h i ?_
  simp [List.mem_range'_1, Std.Legacy.Range.size]; omega

theorem List.forIn_find_some (good : Nat → Bool) : ∀ (l : List Nat),
    ∃ r, (forIn (m := Option) l ((none : Option Nat), ()) fun i _ =>
      if good i = true then pure (ForInStep.done (some i, ())) else pure (.yield (none, ()))) =
      some (r, ()) ∧ ∀ j, r = some j → j ∈ l ∧ good j = true
  | [] => ⟨none, rfl, nofun⟩
  | a :: l => by
    simp only [List.forIn_cons]
    cases hb : good a
    · simp only [Bool.false_eq_true, if_false]
      obtain ⟨r, h1, h2⟩ := List.forIn_find_some good l
      exact ⟨r, by simpa using h1, fun j hj => let h := h2 j hj; ⟨.tail _ h.1, h.2⟩⟩
    · simp only [if_true]
      exact ⟨some a, rfl, fun j hj => by cases hj; exact ⟨.head _, hb⟩⟩

theorem List.forIn_early (bad : Nat → Bool) : ∀ (l : List Nat),
    (forIn (m := Id) l ((none : Option Bool), ()) fun i _ =>
      if bad i = true then pure (ForInStep.done (some false, ())) else pure (.yield (none, ()))) =
      if l.any bad then (some false, ()) else (none, ())
  | [] => rfl
  | a :: l => by
    simp only [List.forIn_cons, List.any_cons]
    by_cases h : bad a = true
    · simp [h]; rfl
    · simp only [h, if_false, Bool.false_eq_true, Bool.false_or]
      exact List.forIn_early bad l

theorem VLCtx.find?_fvar_index : ∀ {Δ : VLCtx}, Δ.FVWF →
    (∀ x ∈ Δ, x.1.isSome ∧ ∃ A, x.2 = .vlam A) →
    ∀ {p fv}, Δ.fvars[p]? = some fv → ∃ A, Δ.find? (.inr fv) = some (.bvar p, A)
  | [], _, _, _, _, h => by simp at h
  | (none, _) :: _, _, H, _, _, _ => by simpa using (H _ (.head _)).1
  | (some (fv', deps), d) :: Δ, hfv, H, p, fv, h => by
    obtain ⟨-, A, rfl⟩ := H _ (.head _)
    cases p with
    | zero =>
      simp at h; subst h
      exact ⟨_, by simp [VLCtx.find?, VLCtx.next, VLocalDecl.value]; rfl⟩
    | succ p =>
      simp at h
      have hne : fv' ≠ fv := fun e => by
        subst e; exact (hfv.2 _ _ rfl).1 (List.mem_of_getElem? h)
      obtain ⟨A', hA'⟩ := find?_fvar_index hfv.1 (fun x hx => H x (.tail _ hx)) h
      refine ⟨A'.liftN 1, ?_⟩
      simp [VLCtx.find?, VLCtx.next, hne, hA', VLocalDecl.depth, VExpr.liftN]

theorem List.idxOf_getElem_of_nodup {α} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup)
    {j : Nat} (hj : j < l.length) : l.idxOf l[j] = j := by
  have hlt : l.idxOf l[j] < l.length := List.idxOf_lt_length_iff.2 (List.getElem_mem hj)
  exact (List.getElem_inj (h₀ := hlt) (h₁ := hj) h).1 (List.getElem_idxOf hlt)

theorem VLevel.mapM_ofLevel_params {Us : List Name} (h : Us.Nodup) :
    (Us.map Level.param).mapM (VLevel.ofLevel Us) = some (VLevel.params Us.length) := by
  rw [List.mapM_eq_some]
  refine List.forall₂_of_getElem? (by simp) fun j a b h1 h2 => ?_
  simp only [List.getElem?_map, Option.map_eq_some_iff, VLevel.params] at h1 h2
  obtain ⟨n, hn, rfl⟩ := h1
  obtain ⟨j', hj', rfl⟩ := h2
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.1 hn
  simp [List.getElem?_range hjl] at hj'; subst hj'
  simp [VLevel.ofLevel, List.idxOf_getElem_of_nodup h hjl, hjl]

/-- `e` is a pi telescope of `n` binders ending in a sort. -/
def VExpr.EndsInSort : Nat → VExpr → Prop
  | 0, .sort _ => True
  | n + 1, .forallE _ B => EndsInSort n B
  | _, _ => False

theorem VExpr.EndsInSort.inst : ∀ {n : Nat} {e : VExpr} (a : VExpr) (k : Nat),
    e.EndsInSort n → (e.inst a k).EndsInSort n
  | 0, .sort _, _, _, _ => trivial
  | n + 1, .forallE _ B, a, k, h => EndsInSort.inst (n := n) (e := B) a (k + 1) h

theorem VExpr.EndsInSort.foralls {u : VLevel} : ∀ (As : List VExpr),
    (VExpr.foralls As (.sort u)).EndsInSort As.length
  | [] => trivial
  | _ :: As => EndsInSort.foralls (u := u) As

/-- An application of a term whose type ends in a sort after as many binders is a type. -/
theorem VEnv.IsType.appN_of_endsInSort {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) : ∀ (as : List VExpr) {f F G : VExpr},
    env.HasType U Γ f F → env.IsDefEqU U Γ F G → G.EndsInSort as.length →
    VExpr.WF env U Γ (f.appN as) → env.IsType U Γ (f.appN as)
  | [], _, _, .sort _, hf, hFG, _, _ => ⟨_, hf.defeqU_r henv hΓ hFG⟩
  | a :: as, f, F, .forallE A' B', hf, hFG, hG, hwf => by
    have ⟨_, hfa⟩ := VExpr.WF.appN_inv henv.ordered hΓ (vs := as) (e := .app f a) hwf
    obtain ⟨A, B, hfAB, ha⟩ := VEnv.HasType.app_inv henv.ordered hΓ hfa
    have h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B') :=
      ((hf.uniqU henv hΓ hfAB).symm).trans henv hΓ hFG
    obtain ⟨-, u, hBB'⟩ := h1.forallE_inv henv hΓ
    have h2 := hBB'.instDF henv.ordered hΓ ha
    exact IsType.appN_of_endsInSort henv hΓ as (f := .app f a) (.app hfAB ha) ⟨_, h2⟩
      (VExpr.EndsInSort.inst (n := as.length) (e := B') a 0 hG) hwf

namespace AddInductive
open TypeChecker

theorem isValidIndApp?_some {stats : InductiveStats} {t : Expr} {j : Nat}
    (h : isValidIndApp? stats t = some j) :
    j < stats.indConsts.size ∧ isValidIndAppIdx stats t j = true := by
  unfold isValidIndApp? at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  obtain ⟨r, hr, hgood⟩ := List.forIn_find_some (isValidIndAppIdx stats t)
    (List.range' 0 [:stats.indConsts.size].size)
  rw [hr] at h
  cases r with
  | none => simp at h
  | some r =>
    simp at h; subst h
    have := hgood _ rfl
    simp [List.mem_range'_1, Std.Legacy.Range.size] at this
    exact ⟨this.1, this.2⟩

theorem isValidIndAppIdx_true {stats : InductiveStats} {t : Expr} {j : Nat}
    (h : isValidIndAppIdx stats t j = true) :
    t.getAppFn == stats.indConsts[j]! ∧
    t.getAppArgs.size = stats.params.size + stats.nindices[j]! ∧
    (∀ k < stats.params.size, (stats.params[k]! != t.getAppArgs[k]!) = false) ∧
    (∀ k, stats.params.size ≤ k → k < t.getAppArgs.size →
      hasIndOcc stats.indConsts t.getAppArgs[k]! = false) := by
  unfold isValidIndAppIdx at h
  simp only [Expr.withApp_eq] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨by simpa using hc.1, hc.2, ?_⟩
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_early] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true, List.mem_range'_1,
      Std.Legacy.Range.size] at h1 h2
    exact ⟨fun k hk => h1 k (by omega), fun k hk1 hk2 => h2 k (by omega)⟩
  · cases h

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.vlam_entries {m : TypeChecker.MLCtx} {fvs tys}
    (h : m.IsTele fvs tys) : ∀ x ∈ m.vlctx, x.1.isSome ∧ ∃ A, x.2 = .vlam A := by
  induction h with
  | nil => nofun
  | vlam _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨rfl, _, rfl⟩
    · exact ih x hx

theorem _root_.Lean4Lean.VLCtx.fvars_length_of_some {Δ : VLCtx} (h : ∀ x ∈ Δ, x.1.isSome) :
    Δ.fvars.length = Δ.length := by
  induction Δ with
  | nil => rfl
  | cons x Δ ih =>
    match x, h x (.head _) with
    | (some _, _), _ => simp [ih fun x hx => h x (.tail _ hx)]

theorem Expr.eqv'_const {a : Expr} {n ls} (h : a.eqv' (.const n ls) = true) : a = .const n ls := by
  cases a <;> simp [Expr.eqv'] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

theorem Expr.eqv'_fvar {a : Expr} {fv} (h : (Expr.fvar fv).eqv' a = true) : a = .fvar fv := by
  cases a <;> simp [Expr.eqv'] at h
  subst h; rfl

/-- The parameters' variables `pfvs` sit below `k` other variables in a context of local
variables. -/
def ParamsAt (Δ : VLCtx) (k : Nat) (pfvs : List FVarId) : Prop :=
  Δ.FVWF ∧ (∀ x ∈ Δ, x.1.isSome ∧ ∃ A, x.2 = .vlam A) ∧
  ∀ i (hi : i < pfvs.length), Δ.fvars[k + (pfvs.length - 1 - i)]? = some pfvs[i]

theorem ParamsAt.tele {Δtop : VLCtx} {m : MLCtx} {pfvs params}
    (hm : m.IsTele pfvs params) (hfvwf : (Δtop ++ m.vlctx).FVWF)
    (htop : ∀ x ∈ Δtop, x.1.isSome ∧ ∃ A, x.2 = .vlam A) :
    ParamsAt (Δtop ++ m.vlctx) Δtop.length pfvs := by
  refine ⟨hfvwf, fun x hx => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact htop x hx
    · exact hm.vlam_entries x hx
  · have hfvars : (Δtop ++ m.vlctx).fvars = Δtop.fvars ++ pfvs.reverse := by
      rw [← hm.fvars]; simp [VLCtx.fvars]
    have htopl : Δtop.fvars.length = Δtop.length :=
      VLCtx.fvars_length_of_some fun x hx => (htop x hx).1
    rw [hfvars, List.getElem?_append_right (by omega), htopl, Nat.add_sub_cancel_left,
      List.getElem?_reverse (by omega)]
    rw [show pfvs.length - 1 - (pfvs.length - 1 - i) = i by omega]
    exact List.getElem?_eq_getElem _

/-- The expression `isValidIndAppIdx` accepts translates to the `j`th type at the parameters, the
variables `k` binders up, and at indices the block does not occur in. -/
theorem validIndApp_tr {venv : VEnv} {Us : List Name} (hUs : Us.Nodup)
    {stats : InductiveStats} {types : List InductiveType} {pfvs : List FVarId}
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = Us.map .param)
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    {Δ : VLCtx} {k : Nat} (hΔ : ParamsAt Δ k pfvs)
    {e : Expr} {E : VExpr} {j : Nat} (hval : isValidIndAppIdx stats e j = true)
    (hj : j < types.length) (hS : TrExprS venv Us Δ e E)
    {params' level isUnsafe d} (hd : Compat Us params' level isUnsafe types stats.nindices d)
    (hdp : d.params.length = pfvs.length)
    (hnm : ∀ a a', TrExprS venv Us Δ a a' →
      hasIndOcc stats.indConsts a = false → a'.mentions d.names = false) :
    ∃ T is, d.types[j]? = some T ∧ is.length = T.indices.length ∧
      E = .appN (.const T.name (VLevel.params d.uvars))
        (VExpr.bvars d.params.length k ++ is) ∧
      is.all (!·.mentions d.names) := by
  obtain ⟨hfvwf, hentries, hposΔ⟩ := hΔ
  obtain ⟨hI, hsz, hpa, hocc⟩ := isValidIndAppIdx_true hval
  have hlenp : stats.params.size = pfvs.length := by
    rw [← Array.length_toList, hpar, List.length_map]
  have hjs : j < stats.indConsts.size := by rw [← Array.length_toList, hind]; simpa
  have hindj : stats.indConsts[j]! = .const types[j].name (Us.map .param) := by
    rw [getElem!_pos stats.indConsts j hjs, ← Array.getElem_toList]
    simp [hind, hlev]
  rw [hindj] at hI
  have hfn : e.getAppFn = .const types[j].name (Us.map .param) :=
    Expr.eqv'_const (by rw [← Expr.eqv_eq]; exact hI)
  have hargs : e.getAppArgs = e.getAppArgsList.toArray := Expr.getAppArgs_eq
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at hS
  obtain ⟨F', as', rfl, hF, has⟩ := TrExprS.mkAppList_inv hS
  cases hF with | const _ hus _ => ?_
  rw [VLevel.mapM_ofLevel_params hUs] at hus; cases hus
  have hdn : d.types.map (·.name) = types.map (·.name) := hd.names
  have hjd : j < d.types.length := by have := congrArg List.length hdn; simp at this; omega
  have hTn : d.types[j].name = types[j].name := by
    have := congrArg (·[j]?) hdn; simpa [hjd, hj] using this
  have hnidx := hd.indices j d.types[j] (by simp [hjd])
  have hnij : stats.nindices[j]! = d.types[j].indices.length := by
    rw [getElem!_pos stats.nindices j (by
      have := Array.getElem?_eq_some_iff.1 hnidx; exact this.1)]
    have := Array.getElem?_eq_some_iff.1 hnidx; exact this.2
  have hlen' : as'.length = pfvs.length + d.types[j].indices.length := by
    rw [← (Lean4Lean.List.Forall₂.length_eq has), ← hnij, ← hlenp, ← hsz, hargs]; simp
  have hparam : ∀ i (hi : i < pfvs.length), as'[i]? = some (.bvar (pfvs.length - 1 - i + k)) := by
    intro i hi
    have hka : i < e.getAppArgsList.length := by
      rw [(Lean4Lean.List.Forall₂.length_eq has), hlen']; omega
    have hi' : i < pfvs.length := by omega
    have hpk : stats.params[i]! = .fvar (pfvs[i]'hi') := by
      rw [getElem!_pos stats.params i (by rw [hlenp]; exact hi), ← Array.getElem_toList]
      simp [hpar]
    have h1 := hpa i (by rw [hlenp]; exact hi)
    rw [hpk] at h1
    replace h1 : (Expr.fvar (pfvs[i]'hi') == e.getAppArgs[i]!) = true := by simpa [bne] using h1
    have h2 : e.getAppArgsList[i] = .fvar (pfvs[i]'hi') := by
      have := Expr.eqv'_fvar (by rw [← Expr.eqv_eq]; exact h1)
      rw [hargs] at this; simpa [List.getElem?_eq_getElem hka] using this
    obtain ⟨a', ha', htr⟩ := List.Forall₂.getElem?_l has (List.getElem?_eq_getElem hka)
    rw [ha']
    rw [h2] at htr
    cases htr with | fvar hf => ?_
    have hpos : Δ.fvars[pfvs.length - 1 - i + k]? = some (pfvs[i]'hi') := by
      have := hposΔ i hi'; rwa [Nat.add_comm] at this
    obtain ⟨_, hf'⟩ := VLCtx.find?_fvar_index hfvwf hentries hpos
    rw [hf'] at hf; cases hf; rfl
  refine ⟨d.types[j], as'.drop pfvs.length, by simp [hjd], by simp [hlen'], ?_, ?_⟩
  · rw [hTn, hd.uvars, hdp]
    conv => lhs; rw [← List.take_append_drop pfvs.length as']
    congr 2
    refine List.ext_getElem? fun m => ?_
    by_cases hm : m < pfvs.length
    · rw [List.getElem?_take, if_pos hm, hparam m hm]
      simp [VExpr.bvars, hm]
    · rw [List.getElem?_take, if_neg hm]
      simp [VExpr.bvars]; omega
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_drop]
    have hm' : pfvs.length + m < e.getAppArgsList.length := by
      rw [Lean4Lean.List.Forall₂.length_eq has]; simp at hm; omega
    obtain ⟨a', ha', htr⟩ := List.Forall₂.getElem?_l has (List.getElem?_eq_getElem hm')
    rw [List.getElem?_eq_getElem (by simp at hm; omega)] at ha'; cases ha'
    have := hocc (pfvs.length + m) (by omega) (by rw [hargs]; simpa using hm')
    rw [hargs] at this
    simp only [List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hm', Option.getD_some] at this
    simp [hnm _ _ htr this]


/-- What `hasIndOcc` looks for. -/
def indOccP (indConsts : Array Expr) : Expr → Bool
  | .const e _ => indConsts.any fun I => I.constName! == e
  | _ => false

theorem hasIndOcc_eq (indConsts : Array Expr) (e : Expr) :
    hasIndOcc indConsts e = e.anySub (indOccP indConsts) := by
  unfold hasIndOcc
  refine (anySubterm_eq (fun a b h => ?_) e).trans (congrArg (Expr.anySub · e) ?_)
  · cases a <;> cases b <;>
      simp only [(· == ·), Expr.eqv_eq, Expr.eqv', Bool.and_eq_true, reduceCtorEq] at h <;>
      try rfl
    all_goals
      rename_i n₁ _ n₂ _
      have : n₁ = n₂ := eq_of_beq (h.1 : (n₁ == n₂) = true)
      subst this; rfl
  · funext x; cases x <;> rfl

theorem indOccP_spec {stats : InductiveStats} {types : List InductiveType}
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels) :
    (∀ e, indOccP stats.indConsts e = true → ∃ c us, e = .const c us ∧ c ∈ types.map (·.name)) ∧
    (∀ c us, indOccP stats.indConsts (.const c us) = false → c ∉ types.map (·.name)) := by
  have key (c) : (stats.indConsts.any fun I => I.constName! == c) = true ↔
      c ∈ types.map (·.name) := by
    rw [← Array.any_toList, hind, List.any_map, List.any_eq_true]
    simp only [Function.comp, Expr.constName!, beq_iff_eq, List.mem_map]
  refine ⟨fun e h => ?_, fun c us h hm => ?_⟩
  · cases e with
    | const c us => exact ⟨c, us, rfl, (key c).1 h⟩
    | _ => cases h
  · rw [← key] at hm; simp [indOccP, hm] at h

/-- The freshness of a non-primitive block in the environment it is checked against. -/
structure BlockFresh (venv₀ venv : VEnv) (types : List InductiveType) : Prop where
  wf₀ : venv₀.WF
  prim₀ : venv₀.HasPrimitives
  wf : venv.WF
  fresh : ∀ t ∈ types, venv₀.constants t.name = none
  nonPrim : ∀ t ∈ types, Environment.primitives.contains t.name = false
  new : ∀ n, venv.constants n ≠ none → venv₀.constants n = none → n ∈ types.map (·.name)
  inducts : venv.inducts = venv₀.inducts

theorem BlockFresh.not_mentions {venv₀ venv : VEnv} {types : List InductiveType}
    (H : BlockFresh venv₀ venv types) {stats : InductiveStats}
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    {Us : List Name} {Δ : VLCtx} (hΔ : Δ.WF venv Us.length)
    (hvl : ∀ x ∈ Δ, x.1.isSome ∧ ∃ A, x.2 = .vlam A)
    {a a'} (ha : TrExprS venv Us Δ a a') (hocc : hasIndOcc stats.indConsts a = false) :
    a'.mentions (types.map (·.name)) = false := by
  have ⟨hp, hns⟩ := indOccP_spec hind
  have hfresh' : ∀ n ∈ types.map (·.name), venv₀.constants n = none := by
    intro n hn; obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn; exact H.fresh t ht
  have hnp' : ∀ n ∈ types.map (·.name), Environment.primitives.contains n = false := by
    intro n hn; obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn; exact H.nonPrim t ht
  refine TrExprS.not_mentions H.wf hns
    (Literal.toConstructor_anySub_of_fresh H.wf₀ H.prim₀ hfresh' H.new hnp' hp)
    (fun n b hb hn => ?_) ha hΔ (fun x hx => ?_) (hasIndOcc_eq _ _ ▸ hocc)
  · obtain ⟨_, h⟩ := H.wf₀.constants_of_inducts (H.inducts ▸ hb)
    cases h.symm.trans (hfresh' n hn)
  obtain ⟨-, A, hA⟩ := hvl x hx
  rw [hA]; rfl

theorem anySub_consumeTypeAnnotations' {p : Expr → Bool} {e : Expr} (h : e.anySub p = false) :
    e.consumeTypeAnnotations'.anySub p = false := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    unfold Lean.Expr.consumeTypeAnnotations'
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    exact ih (by simp_all)
  | case5 e h1 h2 h3 h4 =>
    unfold Lean.Expr.consumeTypeAnnotations'
    split <;> first | exact h | (exfalso; simp_all)

/-- `checkPositivity`'s loop, on a type `T` in the context of the parameters and the variables
`Δtop` opened above them. -/
theorem checkPositivity.loop.WF {venv₀ : VEnv} {types : List InductiveType} {Us : List Name}
    (hUs : Us.Nodup) {stats : InductiveStats} {Mp : MLCtx} {pfvs : List FVarId}
    {params : List VExpr} (hMp : Mp.IsTele pfvs params)
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = Us.map .param)
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    {params' : List VExpr} {level : VLevel} {isUnsafe : Bool} {ctor : Name} {idx : Nat} :
    ∀ fuel t (c : VContext) (Δtop : VLCtx) T, c.lparams = Us → BlockFresh venv₀ c.venv types →
      (∀ x ∈ Δtop, x.1.isSome ∧ ∃ A, x.2 = .vlam A) →
      (∃ ρ, VLCtx.FVLift' (Δtop ++ Mp.vlctx) c.mlctx.vlctx 0 ρ 0) →
      TrExprS c.venv c.lparams (Δtop ++ Mp.vlctx) t T →
      WF c (checkPositivity.loop stats ctor idx t fuel) fun _ =>
        ∀ d, Compat Us params' level isUnsafe types stats.nindices d →
          d.params.length = params.length →
          d.Positive c.venv (Δtop ++ Mp.vlctx).toCtx Δtop.length T := by
  intro fuel
  induction fuel with
  | zero => intros; rw [checkPositivity.loop.eq_1]; exact .throw
  | succ fuel ih =>
  intro t c Δtop T hU hB htop ⟨ρ, W⟩ hT
  have henv := hB.wf
  have hΔb := c.mlctx_wf.tr.wf
  have hΔs := W.wf henv hΔb
  have hΓ := hΔs.toCtx
  have hvl : ∀ x ∈ Δtop ++ Mp.vlctx, x.1.isSome ∧ ∃ A, x.2 = .vlam A := by
    intro x hx; rcases List.mem_append.1 hx with hx | hx
    · exact htop x hx
    · exact hMp.vlam_entries x hx
  rw [checkPositivity.loop.eq_2]
  have hTb := hT.weakFV' henv.ordered W hΔb; simp only [Lift.consN] at hTb
  refine WF.bind (WF.liftTC (TypeChecker.whnf.WF hTb)) fun e₁ ⟨hbelow, htr₁⟩ => ?_
  have hfv₁ := hbelow _ (W.isFVarUpSet rfl hΔb.fvwf) hT.fvarsIn
  obtain ⟨T₁, hS₁, hT₁⟩ := TrExpr.strengthen henv W hΔb (MLCtx.noBV _) htr₁ hfv₁
  split
  · rename_i hno
    refine WF.pure fun d hd hdp => .none (A := T₁) ?_ ?_
    · rw [hd.uvars, ← hU]; exact hT₁.symm
    · rw [hd.names]
      simpa using hB.not_mentions hind hΔs hvl hS₁ (by simpa using hno)
  · rename_i hocc
    split
    · rename_i name dom body bi _
      cases hS₁ with | forallE hdomT hbodyT hdom hbody => ?_
      rename_i dom' body'
      split
      · exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
      rename_i hdocc
      simp only [Bool.not_eq_true] at hdocc
      dsimp only
      refine AddInductive.WF.bind consumeTypeAnnotations.WF fun _ ⟨hx, hok⟩ => ?_; subst hx
      obtain ⟨tys, hty, hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔs hok hdom (Lean.Expr.StripHeads.true _)
      have htyT : c.venv.IsType c.lparams.length (Δtop ++ Mp.vlctx).toCtx tys :=
        hdomT.defeqU_l henv hΓ hdefty
      obtain ⟨u, hdomS⟩ := hdomT
      have hdomty := hdefty.of_l henv hΓ hdomS
      have hΔeq : VLCtx.IsDefEq c.venv c.lparams.length
          ((none, .vlam dom') :: (Δtop ++ Mp.vlctx)) ((none, .vlam tys) :: (Δtop ++ Mp.vlctx)) :=
        .cons (VLCtx.IsDefEq.refl henv.ordered hΔs) nofun (.vlam hdomty)
      obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv hΔeq
      have hbodyeq := hbody.uniq henv hΔeq hbody''
      have hWc := W.toCtx; simp only [Lift.consN] at hWc
      have htyb := hty.weakFV' henv.ordered W hΔb; simp only [Lift.consN] at htyb
      have htyTb : c.venv.IsType c.lparams.length c.mlctx.vlctx.toCtx (tys.lift' ρ) :=
        htyT.weak' henv.ordered hWc
      refine AddInductive.WF.withLocalDecl htyb htyTb ?_
      have W' : VLCtx.FVLift'
          (((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δtop) ++
            Mp.vlctx)
          (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx.vlctx
          0 (ρ.consN 1) 0 :=
        W.cons_fvar (⟨c.ngen.curr⟩, _) (.vlam tys) hty.fvarsList
      have hΔb' := (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx_wf.tr.wf
      have hΔs' := W'.wf henv hΔb'
      have hinst : TrExprS c.venv c.lparams
          (((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δtop) ++
            Mp.vlctx)
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' := by
        rw [Lean.Expr.instantiate1_eq]; exact hbody''.inst_fvar henv.ordered hΔs'
      refine (ih _ (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb) _ body''
        hU hB ?_ ⟨_, W'⟩ hinst).mono fun _ hpos => ?_
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨rfl, _, rfl⟩
        · exact htop x hx
      intro d hd hdp
      have hpos := hpos d hd hdp
      obtain ⟨v, hbodyS⟩ := hbodyT
      have h1 : c.venv.IsDefEq c.lparams.length (Δtop ++ Mp.vlctx).toCtx
          (.forallE dom' body') (.forallE tys body'') (.sort (.imax u v)) :=
        .forallEDF hdomty (hbodyeq.of_l henv ⟨hΓ, _, hdomS⟩ hbodyS)
      refine .pi (A := tys) (B := body'') ?_ ?_ ?_
      · rw [hd.uvars, ← hU]; exact hT₁.symm.trans henv hΓ ⟨_, h1⟩
      · rw [hd.names]
        simpa using hB.not_mentions hind hΔs hvl hty (by
          rw [hasIndOcc_eq] at hdocc ⊢; exact anySub_consumeTypeAnnotations' hdocc)
      · exact hpos
    · split
      · exact .throw
      rename_i hnone
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hnone
      obtain ⟨hjs, hval⟩ := isValidIndApp?_some hj
      have hjt : j < types.length := by
        rw [← Array.length_toList, hind, List.length_map] at hjs; exact hjs
      refine WF.pure fun d hd hdp => ?_
      obtain ⟨Tj, is, hTj, hlen, hE, hall⟩ := validIndApp_tr hUs hpar hlev hind
        (ParamsAt.tele hMp (W.wf henv hΔb).fvwf htop) hval hjt (hU ▸ hS₁) hd
        (hdp.trans hMp.length_eq.symm) fun a a' ha hno => by
          rw [hd.names]; exact hB.not_mentions hind (hU ▸ hΔs) hvl ha hno
      refine .app (VInductDecl.allTypes_getElem?_of_types hTj) hlen ?_ hall
      rw [VInductiveType.typeApp_of_none (hd.nested Tj (List.mem_of_getElem? hTj))]
      rw [hdp, ← hMp.length_eq] at hE ⊢
      rw [← hE, hd.uvars, ← hU]; exact hT₁.symm

theorem declareConstructors.arity_succ : ∀ (i : Nat) (e : Expr),
    declareConstructors.arity (i + 1) e = declareConstructors.arity i e + 1
  | i, .forallE _ _ b _ => by
    simp only [declareConstructors.arity]; exact arity_succ (i + 1) b
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const .. | _, .app .. | _, .lam ..
  | _, .letE .. | _, .lit _ | _, .mdata .. | _, .proj .. => by simp [declareConstructors.arity]

theorem declareConstructors.arity_instantiate1' {x : FVarId} : ∀ (e : Expr) (i d : Nat),
    declareConstructors.arity i (e.instantiate1' (.fvar x) d) = declareConstructors.arity i e
  | .forallE _ _ b _, i, d => by
    simp only [Expr.instantiate1', declareConstructors.arity]
    exact arity_instantiate1' b (i + 1) (d + 1)
  | .bvar j, i, d => by
    simp only [Expr.instantiate1']
    split <;> [rfl; split] <;> simp [declareConstructors.arity, Expr.liftLooseBVars']
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .app .., _, _
  | .lam .., _, _ | .letE .., _, _ | .lit _, _, _ | .mdata .., _, _ | .proj .., _, _ => by
    simp [Expr.instantiate1', declareConstructors.arity]

theorem _root_.Lean4Lean.VLCtx.IsDefEq.vlam_entries {env : VEnv} {U : Nat} {Δ₁ Δ₂ : VLCtx}
    (H : VLCtx.IsDefEq env U Δ₁ Δ₂) (h : ∀ x ∈ Δ₂, x.1.isSome ∧ ∃ A, x.2 = .vlam A) :
    ∀ x ∈ Δ₁, x.1.isSome ∧ ∃ A, x.2 = .vlam A := by
  induction H with
  | nil => nofun
  | cons _ _ hd ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨h1, A, h2⟩ := h _ (.head _)
      refine ⟨h1, ?_⟩
      cases hd with | vlam => exact ⟨_, rfl⟩ | vlet => cases h2
    · exact ih (fun x hx => h x (.tail _ hx)) x hx

theorem checkConstructors.loop.WF {venv₀ : VEnv} {types : List InductiveType} {Us : List Name}
    (hUs : Us.Nodup) {stats : InductiveStats} {Mp : MLCtx} {pfvs : List FVarId}
    {params : List VExpr} (hMp : Mp.IsTele pfvs params)
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = Us.map .param)
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    {level : VLevel} (hres : VLevel.ofLevel Us stats.resultLevel = some level)
    {isUnsafe : Bool} {idx : Nat} {t₀ : InductiveType} (ht₀ : types[idx]? = some t₀) {n : Name} :
    ∀ fuel t i (c : VContext) (Δc Δk : VLCtx) (k : Nat) R,
      c.lparams = Us → BlockFresh venv₀ c.venv types →
      (∃ m hm, c.mlctx.dropN m hm = Mp) →
      ((i < params.length ∧ k = 0 ∧ ∃ hk, Δk = (Mp.dropN (params.length - i) hk).vlctx) ∨
        (params.length ≤ i ∧ k = i - params.length ∧ ∃ Δf, Δk = Δf ++ Mp.vlctx ∧
          Δf.length = k ∧ ∀ x ∈ Δf, x.1.isSome ∧ ∃ A, x.2 = .vlam A)) →
      VLCtx.IsDefEq c.venv Us.length Δc Δk →
      (∃ ρ, VLCtx.FVLift' Δk c.mlctx.vlctx 0 ρ 0) →
      TrExprS c.venv Us Δc t R →
      AddInductive.WF c (checkConstructors.loop stats isUnsafe idx n t i fuel) fun _ =>
        ∀ d, Compat Us params level isUnsafe types stats.nindices d →
        ∃ ps Ds ix, R = .foralls (ps ++ Ds) (.appN (.const t₀.name (VLevel.params Us.length))
            (VExpr.bvars params.length (k + Ds.length) ++ ix)) ∧
          declareConstructors.arity 0 t = ps.length + Ds.length ∧
          c.venv.TeleDefEq Us.length Δk.toCtx ps (params.drop i) ∧
          (∀ nidx, stats.nindices[idx]? = some nidx → ix.length = nidx) ∧
          ix.all (!·.mentions d.names) ∧
          FieldsChecked c.venv d (ps.reverse ++ Δc.toCtx) k Ds := by
  intro fuel
  induction fuel with
  | zero => intros; rw [checkConstructors.loop.eq_1]; exact .throw
  | succ fuel ih =>
  intro t i c Δc Δk k R hU hB hMc hph hΔ ⟨ρ, W⟩ hR
  subst hU
  have henv := hB.wf
  have hΔb := c.mlctx_wf.tr.wf
  have hΔk := W.wf henv hΔb
  have hΔc := hΔ.wf
  have hpl := hMp.length_eq
  have hlenp : stats.params.size = params.length := by
    rw [← Array.length_toList, hpar, List.length_map, hpl]
  by_cases hfa : ∃ name dom body bi, t = .forallE name dom body bi
  · obtain ⟨name, dom, body, bi, rfl⟩ := hfa
    rw [checkConstructors.loop.eq_2]
    cases hR with | forallE hAT hBT hA hB' => ?_
    rename_i A B
    obtain ⟨dk, hdk⟩ := hA.defeqDFC henv hΔ
    have hdkA := hA.uniq henv hΔ hdk
    split
    · -- a parameter
      rename_i param hparam
      have hi : i < params.length := by
        have := (Array.getElem?_eq_some_iff.1 hparam).1; omega
      have hip : i < pfvs.length := by omega
      have hpv : param = .fvar pfvs[i] := by
        have := Array.getElem?_eq_some_iff.1 hparam; rw [← this.2]
        simp [← Array.getElem_toList, hpar]
      subst hpv
      obtain ⟨-, rfl, hk, rfl⟩ := hph.resolve_right (by omega)
      have hpi' : params.take (i + 1) = params.take i ++ [params[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      have hfi' : pfvs.take (i + 1) = pfvs.take i ++ [pfvs[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hip]; rfl
      obtain ⟨hk', hT1⟩ := hMp.dropN' (params.length - (i + 1)) (by omega)
      rw [show params.length - (params.length - (i + 1)) = i + 1 by omega, hpi', hfi'] at hT1
      obtain ⟨name_i, ty_i, bi_i, m', hm', -⟩ := hT1.snoc_inv
      have hm'eq : Mp.dropN (params.length - i) hk = m' := by
        rw [← MLCtx.dropN_congr (show params.length - (i + 1) + 1 = params.length - i by omega)
          (by omega) hk, ← MLCtx.dropN_dropN Mp _ 1 hk' (by simp [hm'])]
        simp [hm']
      rw [hm'eq] at W hΔk hΔ hdk
      obtain ⟨m₁, hm₁, hMc'⟩ := hMc
      have hn₁' : m₁ + (params.length - (i + 1)) ≤ c.mlctx.length := by
        have := MLCtx.length_dropN c.mlctx m₁ hm₁; rw [hMc'] at this; omega
      have hcm : c.mlctx.dropN (m₁ + (params.length - (i + 1))) hn₁' =
          .vlam pfvs[i] name_i ty_i params[i] bi_i m' := by
        rw [← MLCtx.dropN_dropN c.mlctx m₁ _ hm₁ (by rw [hMc']; exact hk'),
          MLCtx.dropN_of_eq hMc' _ hk', hm']
      have hwf := MLCtx.WF.dropN _ hn₁' c.mlctx_wf
      rw [hcm] at hwf
      obtain ⟨-, -, hty_i, -⟩ := hwf
      obtain ⟨d', hd', hd'ty⟩ := c.mlctx_wf.find?_dropN_vlam _ _ hcm
      rw [c.lctx_eq] at hd'
      refine WF.bind (getType.WF hd') fun t ht => ?_
      subst ht; rw [hd'ty]
      have h1 := hdk.weakFV' henv.ordered W hΔb
      have h2 := hty_i.weakFV' henv.ordered W hΔb
      simp only [Lift.consN] at h1 h2
      refine WF.bind (WF.liftTC (TypeChecker.isDefEq.WF h1 h2)) fun b hb => ?_
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
      | true =>
      simp only [if_true]
      have hWc := W.toCtx; simp only [Lift.consN] at hWc
      have hdd : c.venv.IsDefEqU c.lparams.length m'.vlctx.toCtx dk params[i] :=
        (VEnv.IsDefEqU.weak'_iff henv hΔb.toCtx hWc).1 (hb rfl)
      have hAd : c.venv.IsDefEqU c.lparams.length m'.vlctx.toCtx A params[i] :=
        (hdkA.defeqDFC henv.ordered hΔ.defeqCtx).trans henv hΔk.toCtx hdd
      obtain ⟨u, hAS⟩ := hAT
      have hAd' : c.venv.IsDefEq c.lparams.length Δc.toCtx A params[i] (.sort u) :=
        (hAd.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)).of_l henv hΔc.toCtx hAS
      obtain ⟨ρ', W'⟩ := MLCtx.fvlift_dropN c.mlctx _ hn₁'
      rw [hcm] at W'
      have hΔk' := W'.wf henv hΔb
      have hΔ' : VLCtx.IsDefEq c.venv c.lparams.length
          ((some (pfvs[i], ty_i.fvarsList), .vlam A) :: Δc)
          (MLCtx.vlam pfvs[i] name_i ty_i params[i] bi_i m').vlctx := by
        refine .cons hΔ (by rw [hΔ.fvars]; exact hΔk'.2.1) (.vlam hAd')
      have hR' : TrExprS c.venv c.lparams ((some (pfvs[i], ty_i.fvarsList), .vlam A) :: Δc)
          (body.instantiate1 (.fvar pfvs[i])) B := by
        rw [Lean.Expr.instantiate1_eq]; exact hB'.inst_fvar henv.ordered hΔ'.wf
      refine (ih _ (i + 1) c _ _ 0 B rfl hB ⟨m₁, hm₁, hMc'⟩ ?_ hΔ' ⟨_, W'⟩ hR').mono
        fun _ H d hd => ?_
      · by_cases hi1 : i + 1 < params.length
        · exact .inl ⟨hi1, rfl, hk', by rw [hm']⟩
        · refine .inr ⟨by omega, by omega, [], ?_, rfl, nofun⟩
          have : params.length - (i + 1) = 0 := by omega
          rw [List.nil_append, ← hm', MLCtx.dropN_congr this _ (Nat.zero_le _)]; rfl
      obtain ⟨ps, Ds, ix, hRe, har, htele, hix, hall, hfc⟩ := H d hd
      refine ⟨A :: ps, Ds, ix, ?_, ?_, ?_, hix, hall, ?_⟩
      · rw [hRe]; rfl
      · simp only [declareConstructors.arity, declareConstructors.arity_succ]
        rw [Lean.Expr.instantiate1_eq, declareConstructors.arity_instantiate1'] at har
        simp [har]; omega
      · rw [List.drop_eq_getElem_cons hi, hm'eq]
        exact .cons hAd htele
      · simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
        exact hfc
    · -- a field
      rename_i hnone
      have hi : params.length ≤ i := by
        rw [← hlenp]
        exact Decidable.byContradiction fun h => hnone _ (Array.getElem?_eq_getElem (by omega))
      obtain ⟨-, hk, Δf, rfl, hΔfl, hΔfv⟩ := hph.resolve_left (by omega)
      subst hΔfl
      have h1 := hdk.weakFV' henv.ordered W hΔb; simp only [Lift.consN] at h1
      refine WF.bind (WF.liftTC (TypeChecker.ensureType.WF h1)) fun s ⟨e', he', u, u', hs, hu, hty⟩ => ?_
      subst hs
      have hWc := W.toCtx; simp only [Lift.consN] at hWc
      have hdu : c.venv.HasType c.lparams.length (Δf ++ Mp.vlctx).toCtx dk (.sort u') := by
        have h3 := he'.uniq henv (.refl henv.ordered hΔb) h1
        have h4 := hty.defeqU_l henv hΔb.toCtx h3
        exact (VEnv.HasType.weak'_iff (A := .sort u') henv hΔb.toCtx hWc).1 h4
      have hAu : c.venv.HasType c.lparams.length Δc.toCtx A (.sort u') :=
        (hdu.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)).defeqU_l henv hΔc.toCtx
          hdkA.symm
      -- what follows the checks: the field becomes a local variable
      have cont (hlevel : level ≈ .zero ∨ u' ≤ level)
          (hposF : isUnsafe = false → ∀ d, Compat c.lparams params level isUnsafe types
            stats.nindices d → d.params.length = params.length →
            d.Positive c.venv (Δf ++ Mp.vlctx).toCtx Δf.length dk) :
          AddInductive.WF c (consumeTypeAnnotations dom >>= fun d => withLocalDecl name bi d fun arg =>
            checkConstructors.loop stats isUnsafe idx n (body.instantiate1 arg) (i + 1) fuel)
            fun _ => ∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
              ∃ ps Ds ix, A.forallE B = .foralls (ps ++ Ds)
                (.appN (.const t₀.name (VLevel.params c.lparams.length))
                  (VExpr.bvars params.length (Δf.length + Ds.length) ++ ix)) ∧
              declareConstructors.arity 0 (.forallE name dom body bi) = ps.length + Ds.length ∧
              c.venv.TeleDefEq c.lparams.length (Δf ++ Mp.vlctx).toCtx ps (params.drop i) ∧
              (∀ nidx, stats.nindices[idx]? = some nidx → ix.length = nidx) ∧
              ix.all (!·.mentions d.names) ∧
              FieldsChecked c.venv d (ps.reverse ++ Δc.toCtx) Δf.length Ds := by
        refine AddInductive.WF.bind consumeTypeAnnotations.WF fun _ ⟨hx, hok⟩ => ?_; subst hx
        have hΔkΓ := hΔk.toCtx
        obtain ⟨tys, hty', hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔk hok hdk (Lean.Expr.StripHeads.true _)
        have htyT : c.venv.IsType c.lparams.length (Δf ++ Mp.vlctx).toCtx tys :=
          ⟨_, hdu.defeqU_l henv hΔkΓ hdefty⟩
        have htyb := hty'.weakFV' henv.ordered W hΔb; simp only [Lift.consN] at htyb
        have htyTb := htyT.weak' henv.ordered hWc
        refine AddInductive.WF.withLocalDecl htyb htyTb ?_
        have W' : VLCtx.FVLift'
            (((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δf) ++
              Mp.vlctx)
            (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx.vlctx
            0 (ρ.consN 1) 0 :=
          W.cons_fvar _ (.vlam tys) hty'.fvarsList
        have hΔb' := (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb
          htyTb).mlctx_wf.tr.wf
        have hΔk' := W'.wf henv hΔb'
        have hAt : c.venv.IsDefEq c.lparams.length Δc.toCtx A tys (.sort u') := by
          have h1 := hdefty.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)
          exact (hdkA.trans henv hΔc.toCtx h1).of_l henv hΔc.toCtx hAu
        have hΔ' : VLCtx.IsDefEq c.venv c.lparams.length
            ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam A) :: Δc)
            (((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δf) ++
              Mp.vlctx) :=
          .cons hΔ (by rw [hΔ.fvars]; exact hΔk'.2.1) (.vlam hAt)
        have hR' : TrExprS c.venv c.lparams
            ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam A) :: Δc)
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) B := by
          rw [Lean.Expr.instantiate1_eq]; exact hB'.inst_fvar henv.ordered hΔ'.wf
        obtain ⟨m₁, hm₁, hMc'⟩ := hMc
        refine (ih _ (i + 1) (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb)
          _ _ (Δf.length + 1) B rfl hB ⟨m₁ + 1, by simpa [VContext.push] using hm₁, hMc'⟩
          (.inr ⟨Nat.le_succ_of_le hi, by rw [hk, Nat.sub_add_comm hi],
            (some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δf, rfl, rfl,
            ?_⟩) hΔ' ⟨_, W'⟩ hR').mono
          fun _ H d hd => ?_
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨rfl, _, rfl⟩
          · exact hΔfv x hx
        obtain ⟨ps, Ds, ix, hRe, har, htele, hix, hall, hfc⟩ := H d hd
        have hps : ps = [] := by
          have := htele.length_eq; rw [List.drop_eq_nil_of_le (by omega)] at this
          exact List.eq_nil_of_length_eq_zero this
        subst hps
        refine ⟨[], A :: Ds, ix, ?_, ?_, ?_, hix, hall, ?_⟩
        · rw [hRe]; simp [Nat.add_assoc, Nat.add_comm 1]
        · simp only [declareConstructors.arity, declareConstructors.arity_succ]
          rw [Lean.Expr.instantiate1_eq, declareConstructors.arity_instantiate1'] at har
          simp [har]
        · rw [List.drop_eq_nil_of_le hi]; exact .nil
        · simp only [List.reverse_nil, List.nil_append]
          have hdu' : d.uvars = c.lparams.length := hd.uvars
          refine .cons ⟨u', hdu' ▸ hAu, by rw [hd.level]; exact hlevel⟩ (fun hs => ?_) hfc
          have hpos := hposF (hd.isUnsafe ▸ hs) d hd (by rw [hd.params])
          have hΓ' : OnCtx Δc.toCtx (c.venv.IsType d.uvars) := hdu' ▸ hΔc.toCtx
          have hctx : c.venv.IsDefEqCtx d.uvars [] (Δf ++ Mp.vlctx).toCtx Δc.toCtx :=
            hdu' ▸ hΔ.defeqCtx.symm henv.ordered
          exact (hpos.defeqDFC henv.ordered hctx).defeq henv hΓ' (hdu' ▸ hdkA.symm)
      by_cases hlv : (stats.resultLevel.isAlwaysZero ||
          stats.resultLevel.geq' (Expr.sort u).sortLevel!) = true
      · simp only [hlv, ite_true]
        have hlevel : level ≈ .zero ∨ u' ≤ level := by
          simp only [Bool.or_eq_true] at hlv
          rcases hlv with h | h
          · exact .inl ((ofLevel_isAlwaysZero_iff hres).1 h)
          · exact .inr (Level.geq'_wf hres hu (by simpa [Expr.sortLevel!] using h))
        by_cases hsafe : (!isUnsafe) = true
        · simp only [hsafe, ite_true]
          refine WF.bind ?_ fun _ hpos => cont hlevel fun _ => hpos
          unfold checkPositivity
          refine WF.bind WF.read fun _ hr => ?_; subst hr
          exact checkPositivity.loop.WF hUs hMp hpar hlev hind _ dom c Δf dk rfl hB hΔfv
            ⟨ρ, W⟩ hdk
        · simp only [hsafe, Bool.false_eq_true, ite_false]
          exact cont hlevel fun h => by simp [h] at hsafe
      · simp only [hlv, Bool.false_eq_true, ite_false]
        exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
  · rw [checkConstructors.loop.eq_3 _ _ _ _ _ _ _ fun name dom body bi h =>
      hfa ⟨name, dom, body, bi, h⟩]
    split
    · exact .throw
    rename_i hval'
    simp only [Bool.not_eq_true, Bool.not_eq_false'] at hval'
    have hidx : idx < types.length := (List.getElem?_eq_some_iff.1 ht₀).1
    have ht₀' : types[idx] = t₀ := (List.getElem?_eq_some_iff.1 ht₀).2
    have hvlk : ∀ x ∈ Δk, x.1.isSome ∧ ∃ A, x.2 = .vlam A := by
      rcases hph with ⟨-, -, hk, rfl⟩ | ⟨-, -, Δf, rfl, -, hΔfv⟩
      · obtain ⟨_, h'⟩ := hMp.dropN' (params.length - i) (Nat.sub_le _ _)
        exact h'.vlam_entries
      · intro x hx; rcases List.mem_append.1 hx with hx | hx
        · exact hΔfv x hx
        · exact hMp.vlam_entries x hx
    have hvlc := hΔ.vlam_entries hvlk
    refine WF.pure fun d hd => ?_
    rcases hph with ⟨hi, -, hk, rfl⟩ | ⟨hi, hk, Δf, rfl, hΔfl, hΔfv⟩
    · exfalso
      obtain ⟨-, hsz, hpa, -⟩ := isValidIndAppIdx_true hval'
      have hip : i < pfvs.length := by omega
      have hpk : stats.params[i]! = .fvar pfvs[i] := by
        rw [getElem!_pos stats.params i (by rw [hlenp]; exact hi), ← Array.getElem_toList]
        simp [hpar]
      have h1 := hpa i (by rw [hlenp]; exact hi)
      rw [hpk] at h1
      replace h1 : (Expr.fvar pfvs[i] == t.getAppArgs[i]!) = true := by simpa [bne] using h1
      have hargs : t.getAppArgs = t.getAppArgsList.toArray := Expr.getAppArgs_eq
      have hka : i < t.getAppArgsList.length := by
        have : t.getAppArgs.size = t.getAppArgsList.length := by rw [hargs]; simp
        omega
      have h2 : t.getAppArgsList[i] = .fvar pfvs[i] := by
        have := Expr.eqv'_fvar (by rw [← Expr.eqv_eq]; exact h1)
        rw [hargs] at this; simpa [List.getElem?_eq_getElem hka] using this
      have hfv := hR.fvarsIn
      rw [← Expr.mkAppList_getAppArgsList t, FVarsIn.mkAppList] at hfv
      have := hfv.2 _ (List.getElem_mem hka)
      rw [h2] at this
      simp only [FVarsIn] at this
      rw [hΔ.fvars] at this
      obtain ⟨_, h'⟩ := hMp.dropN' (params.length - i) (Nat.sub_le _ _)
      rw [h'.fvars, show params.length - (params.length - i) = i by omega] at this
      obtain ⟨m₁, hm₁, hMc'⟩ := hMc
      have hnd : pfvs.Nodup := by
        have := (hMc' ▸ c.mlctx_wf.dropN m₁ hm₁).fvars_nodup
        rwa [hMp.fvars, List.nodup_reverse] at this
      rw [List.mem_reverse] at this
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem this
      simp only [List.getElem_take, List.length_take] at hj hjeq
      have := (List.getElem_inj (h₀ := by omega) (h₁ := hip) hnd).1 hjeq
      omega
    · subst hΔfl
      have hPA : ParamsAt Δc Δf.length pfvs := by
        have := ParamsAt.tele hMp hΔk.fvwf hΔfv
        exact ⟨hΔc.fvwf, hvlc, hΔ.fvars ▸ this.2.2⟩
      have hdp : d.params.length = pfvs.length := by rw [hd.params, hpl]
      obtain ⟨T, is, hT, hlen, hRe, hall⟩ := validIndApp_tr hUs hpar hlev hind hPA hval' hidx hR
        hd hdp fun a a' ha hno => by rw [hd.names]; exact hB.not_mentions hind hΔc hvlc ha hno
      have hTn : T.name = t₀.name := by
        have := congrArg (·[idx]?) hd.names
        simp [VInductDecl.names, hT, ht₀] at this; exact this
      refine ⟨[], [], is, ?_, ?_, ?_, ?_, hall, .nil⟩
      · rw [hRe, hTn, hd.uvars, hdp, hpl]; rfl
      · cases t with
        | forallE => exact (hfa ⟨_, _, _, _, rfl⟩).elim
        | _ => simp [declareConstructors.arity]
      · rw [List.drop_eq_nil_of_le hi]; exact .nil
      · intro nidx hn
        have := hd.indices idx T hT; rw [hn] at this; cases this; exact hlen

theorem WF.forIn_list {c : VContext} {α σ : Type} {l : List α} {f : α → σ → M (ForInStep σ)}
    {P : α → Prop}
    (H : ∀ a ∈ l, ∀ s, WF c (f a s) fun r => P a ∧ ∃ s', r = .yield s') :
    ∀ {init : σ}, WF c (forIn l init f) fun _ => ∀ a ∈ l, P a := by
  induction l with
  | nil => intro init; exact WF.pure nofun
  | cons a l ih =>
    intro init
    rw [List.forIn_cons]
    refine WF.bind (H a (.head _) init) fun r ⟨hp, s', hr⟩ => ?_
    subst hr
    refine (ih fun b hb s => H b (.tail _ hb) s).mono fun _ h b hb => ?_
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hp
    · exact h b hb

theorem WF.forIn'_list {c : VContext} {σ : Type} :
    ∀ {l : List Nat} {f : (a : Nat) → a ∈ l → σ → M (ForInStep σ)} {P : Nat → Prop},
    (∀ a (h : a ∈ l), ∀ s, WF c (f a h s) fun r => P a ∧ ∃ s', r = .yield s') →
    ∀ {init : σ}, WF c (forIn' l init f) fun _ => ∀ a ∈ l, P a
  | [], _, _, _, _ => WF.pure nofun
  | a :: l, f, P, H, init => by
    rw [List.forIn'_cons]
    refine WF.bind (H a (.head _) init) fun r ⟨hp, s', hr⟩ => ?_
    subst hr
    refine (WF.forIn'_list (l := l) (fun b hb s => H b (.tail _ hb) s)).mono fun _ h b hb => ?_
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hp
    · exact h b hb

theorem WF.forIn'_range {c : VContext} {σ : Type} {n : Nat}
    {f : (a : Nat) → a ∈ [:n] → σ → M (ForInStep σ)} {P : Nat → Prop}
    (H : ∀ a (h : a ∈ [:n]), ∀ s, WF c (f a h s) fun r => P a ∧ ∃ s', r = .yield s')
    {init : σ} : WF c (forIn' [:n] init f) fun _ => ∀ a < n, P a := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine (WF.forIn'_list fun a h s => H a _ s).mono fun _ h a ha => h a ?_
  simp [List.mem_range'_1, Std.Legacy.Range.size]; omega
/-- One constructor of the `idx`th type, as `checkConstructors` checks it. -/
theorem checkCtor.WF {c₀ c₁ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c₁ params level typeTr)
    (hc : c.mlctx = c₁.mlctx) (hU : c.lparams = c₁.lparams) (hle : c₀.venv ≤ c.venv)
    (hconst : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t →
      typeTr[j]? = some T' → c.venv.constants t.name = some ⟨c.lparams.length, T'⟩)
    (hB : BlockFresh c₀.venv c.venv types)
    (hUs : c.lparams.Nodup) {isUnsafe : Bool} {idx : Nat} {t : InductiveType}
    (ht : types[idx]? = some t) (ct : Constructor) {β : Type} {cont : M β} {Q : β → Prop}
    (Hk : (∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ nidx, stats.nindices[idx]? = some nidx → CtorChecked c.venv c.lparams d t nidx ct) →
      (∃ C', TrExprS c.venv c.lparams [] ct.type C') →
      AddInductive.WF c cont Q) :
    AddInductive.WF c (do
      liftM (c.env.checkNoMVarNoFVar ct.name ct.type)
      let _ ← liftM (TypeChecker.checkType ct.type)
      let ctx ← readThe Context
      checkConstructors.loop stats isUnsafe idx ct.name ct.type 0 ctx.fuel.inductiveFuel
      cont) Q := by
  refine WF.bind (WF.liftExcept (checkNoMVarNoFVar.WF _ _ _)) fun _ hcl => ?_
  refine WF.bind (WF.liftTC (TypeChecker.checkType.WF (c := c.tc) (s := {})
    (hcl.mono nofun))) fun _ hty => ?_
  have hCex : ∃ C', TrExprS c.venv c.lparams [] ct.type C' := by
    obtain ⟨e', -, -, he', -⟩ := hty
    obtain ⟨es, hs, -⟩ := TrExprS.strengthen hB.wf (VLCtx.FVLift'.from_nil (MLCtx.noBV c.mlctx))
      c.mlctx_wf.tr.wf (MLCtx.noBV _) he' (hcl.mono nofun)
    exact ⟨es, hs⟩
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  refine WF.bind (Q := fun _ => ∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ nidx, stats.nindices[idx]? = some nidx → CtorChecked c.venv c.lparams d t nidx ct) ?_
    fun _ h => Hk h hCex
  obtain ⟨k₁, hk₁, pfvs, hMp, hpar⟩ := hT.paramsCtx
  have hb := hT.base
  have henv := hB.wf
  have hlev : stats.levels = c.lparams.map .param := by rw [hT.levels, hU, hb.lparams]
  have hres : VLevel.ofLevel c.lparams stats.resultLevel = some level := by
    rw [hU, hb.lparams]; exact hT.resultLevel
  have hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels := by
    rw [hT.indConsts, List.take_of_length_le (by rw [hT.nindices.symm.trans hT.nindices]; omega)]
  have hpl := hMp.length_eq
  have W₀ := VLCtx.FVLift'.from_nil (MLCtx.noBV c.mlctx)
  intro r hr d hd nidx hnidx C' hC'
  have hstart := checkConstructors.loop.WF hUs hMp hpar hlev hind hres ht
    (n := ct.name) (isUnsafe := isUnsafe) _ ct.type 0 c [] [] 0 C' rfl hB
    ⟨k₁, hc ▸ hk₁, MLCtx.dropN_of_eq hc _ _⟩ ?_ .nil ⟨_, W₀⟩ hC' r hr d hd
  · obtain ⟨ps, Ds, ix, hR, har, htele, hix, hall, hfc⟩ := hstart
    simp only [VLCtx.toCtx, List.drop_zero, List.append_nil, Nat.zero_add] at htele hfc hR
    have hdp : d.params = params := hd.params
    refine ⟨?_, ps, Ds, ix, by rw [hdp]; exact hR, har, by rw [hdp]; exact htele,
      hix nidx hnidx, hall, hfc⟩
    by_cases hz : ps ++ Ds = []
    · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hz
      have hp0 : params = [] := List.eq_nil_of_length_eq_zero htele.length_eq.symm
      subst hp0
      have hjl : idx < typeTr.length := by
        rw [hT.typeTr_length]; exact (List.getElem?_eq_some_iff.1 ht).1
      obtain ⟨T', hT'⟩ : ∃ T', typeTr[idx]? = some T' := ⟨_, List.getElem?_eq_getElem hjl⟩
      obtain ⟨idxT, u, -, hTty, hTdef, -, hnT, -⟩ := hT.types idx t T' ht hT'
      have hU₀ : c.lparams = c₀.lparams := hU.trans hb.lparams
      have hci := hconst idx t T' ht hT'
      have hf := VEnv.HasType.const0 hci (by
        show c.venv.IsType c.lparams.length [] T'
        rw [hU₀]; exact hTty.mono hle)
      have hlen : ix.length = idxT.length := by
        rw [hix nidx hnidx]; rw [hnidx] at hnT; cases hnT; rfl
      rw [hR]
      simp only [List.nil_append, VExpr.foralls_nil, VExpr.bvars]
      refine VEnv.IsType.appN_of_endsInSort henv trivial ix hf (G := .foralls idxT (.sort u))
        ?_ (hlen ▸ VExpr.EndsInSort.foralls idxT) ?_
      · rw [hU₀]; simpa using hTdef.mono hle
      · have := TrExprS.wf henv.ordered (Δ := []) trivial hC'
        rw [hR] at this; simpa [VExpr.bvars, VLCtx.toCtx] using this
    · cases hct : ct.type with
      | forallE =>
        rw [hct] at hC'
        cases hC' with | forallE hAT hBT _ _ => exact VEnv.IsType.forallE hAT hBT
      | _ =>
        rw [hct] at har; simp [declareConstructors.arity] at har
        exact (hz (List.append_eq_nil_iff.2 ⟨List.eq_nil_of_length_eq_zero (by omega),
          List.eq_nil_of_length_eq_zero (by omega)⟩)).elim
  · obtain ⟨hk, hall⟩ := hMp.dropN_all
    by_cases hnp : 0 < params.length
    · refine .inl ⟨hnp, rfl, hk, ?_⟩
      rw [MLCtx.dropN_congr (Nat.sub_zero _) _ hk, hall]; rfl
    · have hp0 : params.length = 0 := by omega
      refine .inr ⟨Nat.le_of_eq hp0, by simp, [], ?_, rfl, nofun⟩
      have : c₁.mlctx.dropN k₁ hk₁ = .nil := by
        rw [← hall]; exact (MLCtx.dropN_congr hp0.symm (Nat.zero_le _) hk)
      rw [this]; rfl
theorem WF.getEnv {c : VContext} :
    AddInductive.WF c (liftM TypeChecker.getEnv : M Environment) (· = c.env) := by
  refine WF.liftTC ?_
  have := TypeChecker.M.WF.getEnv (c := c.tc) (s := {}) (f := fun e => (Pure.pure e : TypeChecker.M _))
    (Q := fun a _ => a = c.env) (TypeChecker.M.WF.pure rfl)
  simpa using this

/-- `checkConstructors`, in the checking environment. -/
theorem checkConstructors.WF {c₀ c₁ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c₁ params level typeTr)
    (hc : c.mlctx = c₁.mlctx) (hU : c.lparams = c₁.lparams) (hle : c₀.venv ≤ c.venv)
    (hconst : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t →
      typeTr[j]? = some T' → c.venv.constants t.name = some ⟨c.lparams.length, T'⟩)
    (hB : BlockFresh c₀.venv c.venv types)
    (hUs : c.lparams.Nodup) {isUnsafe : Bool} :
    AddInductive.WF c (checkConstructors types.toArray stats isUnsafe) fun _ =>
      (∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
        ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
          stats.nindices[j]? = some nidx →
          CtorChecked c.venv c.lparams d t nidx ct) ∧
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors,
        ∃ C', TrExprS c.venv c.lparams [] ct.type C' := by
  unfold checkConstructors
  refine WF.bind WF.getEnv fun env henv => ?_
  subst henv
  refine WF.bind (WF.forIn'_range (P := fun idx => ∀ (h : idx < types.length),
    ∀ ct ∈ types[idx].ctors, (∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ nidx, stats.nindices[idx]? = some nidx →
        CtorChecked c.venv c.lparams d types[idx] nidx ct) ∧
      ∃ C', TrExprS c.venv c.lparams [] ct.type C')
    fun idx hidx s => ?_) fun _ H => WF.pure ⟨fun d hd j t ht ct hct nidx hnidx => ?_,
      fun j t ht ct hct => ?_⟩
  · have hidx' : idx < types.length := by simpa [Membership.mem] using hidx.2.1
    have ht : types[idx]? = some types[idx] := List.getElem?_eq_getElem hidx'
    refine WF.bind (WF.forIn_list (P := fun ct => (∀ d, Compat c.lparams params level isUnsafe types
      stats.nindices d → ∀ nidx, stats.nindices[idx]? = some nidx →
        CtorChecked c.venv c.lparams d types[idx] nidx ct) ∧
      ∃ C', TrExprS c.venv c.lparams [] ct.type C') fun ct hct s => ?_)
      fun _ H => WF.pure ⟨fun _ ct hct => H ct (by simpa using hct), _, rfl⟩
    dsimp only
    split
    · exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
    · exact checkCtor.WF hT hc hU hle hconst hB hUs ht ct fun h h' => WF.pure ⟨⟨h, h'⟩, _, rfl⟩
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ht
    exact (H j (by simpa using hj) hj ct hct).1 d hd nidx hnidx
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ht
    exact (H j (by simpa using hj) hj ct hct).2

theorem declareConstructors.le_arity : ∀ (i : Nat) (e : Expr), i ≤ declareConstructors.arity i e
  | i, .forallE _ _ b _ => by
    simp only [declareConstructors.arity]; have := le_arity (i + 1) b; omega
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const .. | _, .app .. | _, .lam ..
  | _, .letE .. | _, .lit _ | _, .mdata .. | _, .proj .. => by simp [declareConstructors.arity]

theorem isKTarget.loop_iff (stats : InductiveStats) : ∀ (e : Expr) (i : Nat),
    i ≤ stats.params.size →
    (isKTarget.loop stats i e = true ↔ declareConstructors.arity i e ≤ stats.params.size)
  | .forallE _ _ b _, i, hi => by
    simp only [isKTarget.loop, declareConstructors.arity, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h : i < stats.params.size
    · rw [isKTarget.loop_iff stats b (i + 1) h]; simp [h]
    · have := declareConstructors.le_arity (i + 1) b
      simp [h]; omega
  | .bvar _, _, hi | .fvar _, _, hi | .mvar _, _, hi | .sort _, _, hi | .const .., _, hi
  | .app .., _, hi | .lam .., _, hi | .letE .., _, hi | .lit _, _, hi | .mdata .., _, hi
  | .proj .., _, hi => by simp [isKTarget.loop, declareConstructors.arity, hi]

/-- `isKTarget`: whether the block is a subsingleton in `Prop`. -/
theorem isKTarget.WF {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    {c' : VContext} (hc' : c'.lparams = c.lparams) (hle : c₀.venv ≤ c'.venv) (henv : c'.venv.WF)
    {isUnsafe : Bool}
    (hC : ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c'.venv c'.lparams d t nidx ct) :
    AddInductive.WF c' (isKTarget stats types.toArray) fun b =>
      ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
        Elaborates c'.venv c'.lparams nparams level types d → (b = true ↔ d.IsKTarget) := by
  intro b hb d hd hE
  have hU₀ : c'.lparams = c₀.lparams := hc'.trans hT.base.lparams
  have hlz : stats.resultLevel.isAlwaysZero = true ↔ d.level ≈ .zero := by
    rw [hd.level]; exact ofLevel_isAlwaysZero_iff hT.resultLevel
  have hlen := Lean4Lean.List.Forall₂.length_eq hE.types
  have hnot1 : (∀ t, types ≠ [t]) → b = false → (b = true ↔ d.IsKTarget) := by
    intro hne hb'
    subst hb'
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨-, T', c', h1, -⟩
    rw [h1] at hlen
    match types, hlen with
    | [t], _ => exact hne t rfl
  rcases types with _ | ⟨t, _ | ⟨t', ts⟩⟩
  · exact hnot1 (fun _ => nofun) (by cases hb; rfl)
  · obtain ⟨T, hT1⟩ : ∃ T, d.types = [T] := by
      match d.types, hlen with | [T], _ => exact ⟨T, rfl⟩
    have hE' := hE.types; rw [hT1] at hE'
    obtain ⟨⟨hTn, hcs⟩, -⟩ := List.forall₂_cons.1 hE'
    change (if stats.resultLevel.isAlwaysZero then
      match t.ctors with
      | [ctor] => pure (isKTarget.loop stats 0 ctor.type)
      | _ => pure false
    else pure false : M Bool) c'.toContext = .ok b at hb
    split at hb
    · rename_i hz
      have hnone : (∀ ct, t.ctors ≠ [ct]) → b = false → (b = true ↔ d.IsKTarget) := by
        intro hct hb'
        subst hb'
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨-, T', c', h1, -, h2, -⟩
        cases List.cons.inj (h1.symm.trans hT1) |>.1
        rw [h2] at hcs
        have := Lean4Lean.List.Forall₂.length_eq hcs
        match ht' : t.ctors, this with
        | [ct], _ => exact hct ct ht'
      rcases hct : t.ctors with _ | ⟨ct, _ | ⟨ct', cts⟩⟩ <;> rw [hct] at hb
      · exact hnone (fun _ h => by rw [hct] at h; cases h) (by cases hb; rfl)
      · rw [hct] at hcs
        obtain ⟨c, hc1⟩ : ∃ c, T.ctors = [c] := by
          have := Lean4Lean.List.Forall₂.length_eq hcs
          match T.ctors, this with | [c], _ => exact ⟨c, rfl⟩
        rw [hc1] at hcs
        obtain ⟨hrel, -⟩ := List.forall₂_cons.1 hcs
        cases hb
        have hpar : d.params.length = nparams := hd.params ▸ hT.nparams
        have hps : c'.venv.IsTele d.uvars [] d.params := by
          rw [hd.uvars, hd.params, hU₀]; exact hT.params_tele.mono hle
        obtain ⟨-, har⟩ := ctor_WF henv hd.uvars hpar hps hTn (hd.nested T (by simp [hT1])) rfl
          (hC d hd 0 t rfl ct (by simp [hct]) _ (hd.indices 0 T (by simp [hT1]))) hrel
        have hsize : stats.params.size = nparams := params_size hT
        rw [isKTarget.loop_iff stats _ 0 (Nat.zero_le _), har, hsize]
        constructor
        · intro h
          exact ⟨hlz.1 hz, T, c, hT1, hd.aux, hc1, List.eq_nil_of_length_eq_zero (by omega)⟩
        · rintro ⟨-, T', c', h1, -, h2, h3⟩
          cases List.cons.inj (h1.symm.trans hT1) |>.1
          cases List.cons.inj (h2.symm.trans hc1) |>.1
          simp [h3]
      · exact hnone (fun _ h => by rw [hct] at h; cases h) (by cases hb; rfl)
    · rename_i hz
      cases hb
      simp only [Bool.false_eq_true, false_iff]
      exact fun h => hz (hlz.2 h.1)
  · exact hnot1 (fun _ => nofun) (by cases hb; rfl)

theorem Expr.eqv'_fvar_r {a : Expr} {fv} (h : a.eqv' (.fvar fv) = true) : a = .fvar fv := by
  cases a <;> simp [Expr.eqv'] at h
  subst h; rfl

theorem isLargeEliminator.loop.WF {venv : VEnv} {Us : List Name} {stats : InductiveStats}
    {np : Nat} (hnp : stats.params.size = np) {ps Ds indices : List VExpr} {fields : List VField}
    {n : Name} (hps : ps.length = np) (hDs : Ds.length = fields.length)
    (hlvl : ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → fields[k]? = some f → ∀ u,
      venv.HasType Us.length ((Ds.take k).reverse ++ ps.reverse) D (.sort u) →
      (u ≈ .zero ↔ f.level ≈ .zero)) :
    ∀ fuel t i toCheck (c : VContext) (Δc Δk : VLCtx) (fvs : List FVarId),
      c.lparams = Us → c.venv = venv → c.venv.WF →
      fvs.length = i → Δc.fvars = fvs.reverse →
      (∀ x ∈ Δk, x.1.isSome ∧ ∃ A, x.2 = .vlam A) →
      VLCtx.IsDefEq c.venv Us.length Δc Δk →
      (∃ ρ, VLCtx.FVLift' Δk c.mlctx.vlctx 0 ρ 0) →
      Δc.toCtx = ((ps ++ Ds).take i).reverse →
      declareConstructors.arity i t = np + Ds.length →
      TrExprS c.venv Us Δc t (.foralls ((ps ++ Ds).drop i)
        (.appN (.const n (VLevel.params Us.length)) (VExpr.bvars np Ds.length ++ indices))) →
      (∀ k f fv, np + k < i → fields[k]? = some f → ¬f.level ≈ .zero → fvs[np + k]? = some fv →
        .fvar fv ∈ toCheck) →
      AddInductive.WF c (isLargeEliminator.loop stats t i toCheck fuel) fun b => b = true →
        ∀ k f, fields[k]? = some f → ¬f.level ≈ .zero →
          .bvar (fields.length - 1 - k) ∈ indices := by
  intro fuel
  induction fuel with
  | zero => intros; rw [isLargeEliminator.loop.eq_1]; exact .throw
  | succ fuel ih =>
  intro t i toCheck c Δc Δk fvs hU hV henv hfl hfv hvlk hΔ ⟨ρ, W⟩ hΔt har hR htc
  subst hU
  have hΔb := c.mlctx_wf.tr.wf
  have hΔk := W.wf henv hΔb
  have hΔc := hΔ.wf
  have hdl : (ps ++ Ds).length = np + Ds.length := by simp [hps]
  by_cases hfa : ∃ name dom body bi, t = .forallE name dom body bi
  · obtain ⟨name, dom, body, bi, rfl⟩ := hfa
    have hi : i < (ps ++ Ds).length := by
      simp only [declareConstructors.arity] at har
      have := declareConstructors.le_arity (i + 1) body; omega
    rw [List.drop_eq_getElem_cons hi, VExpr.foralls_cons] at hR
    cases hR with | forallE hAT hBT hA hB' => ?_
    rw [isLargeEliminator.loop.eq_2]
    obtain ⟨dk, hdk⟩ := hA.defeqDFC henv hΔ
    have hdkA := hA.uniq henv hΔ hdk
    refine AddInductive.WF.bind consumeTypeAnnotations.WF fun _ ⟨hx, hok⟩ => ?_; subst hx
    obtain ⟨tys, hty, hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔk hok hdk (Lean.Expr.StripHeads.true _)
    obtain ⟨u₀, hAS⟩ := hAT
    have hdkS : c.venv.HasType c.lparams.length Δk.toCtx dk (.sort u₀) :=
      (hAS.defeqDFC henv.ordered hΔ.defeqCtx).defeqU_l henv hΔk.toCtx
        (hdkA.defeqDFC henv.ordered hΔ.defeqCtx)
    have htyT : c.venv.IsType c.lparams.length Δk.toCtx tys :=
      ⟨_, hdkS.defeqU_l henv hΔk.toCtx hdefty⟩
    have hWc := W.toCtx; simp only [Lift.consN] at hWc
    have htyb := hty.weakFV' henv.ordered W hΔb; simp only [Lift.consN] at htyb
    have htyTb := htyT.weak' henv.ordered hWc
    refine AddInductive.WF.withLocalDecl htyb htyTb ?_
    have W' : VLCtx.FVLift'
        ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δk)
        (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx.vlctx
        0 (ρ.consN 1) 0 :=
      W.cons_fvar (⟨c.ngen.curr⟩, _) (.vlam tys) hty.fvarsList
    have hΔb' := (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb
      htyTb).mlctx_wf.tr.wf
    have hΔk' := W'.wf henv hΔb'
    have hAt : c.venv.IsDefEq c.lparams.length Δc.toCtx (ps ++ Ds)[i] tys (.sort u₀) := by
      have h1 := hdefty.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)
      exact (hdkA.trans henv hΔc.toCtx h1).of_l henv hΔc.toCtx hAS
    have hΔ' : VLCtx.IsDefEq c.venv c.lparams.length
        ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam (ps ++ Ds)[i]) :: Δc)
        ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δk) :=
      .cons hΔ (by rw [hΔ.fvars]; exact hΔk'.2.1) (.vlam hAt)
    have hR' : TrExprS c.venv c.lparams
        ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam (ps ++ Ds)[i]) :: Δc)
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        (.foralls ((ps ++ Ds).drop (i + 1)) (.appN (.const n (VLevel.params c.lparams.length))
          (VExpr.bvars np Ds.length ++ indices))) := by
      rw [Lean.Expr.instantiate1_eq]; exact hB'.inst_fvar henv.ordered hΔ'.wf
    have cont (toCheck' : Array Expr) (hsup : ∀ x ∈ toCheck, x ∈ toCheck')
        (hnew : np ≤ i → ∀ f, fields[i - np]? = some f → ¬f.level ≈ .zero →
          .fvar ⟨c.ngen.curr⟩ ∈ toCheck') :
        AddInductive.WF (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb)
          (isLargeEliminator.loop stats (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            toCheck' fuel) fun b => b = true →
          ∀ k f, fields[k]? = some f → ¬f.level ≈ .zero →
            .bvar (fields.length - 1 - k) ∈ indices := by
      refine ih _ (i + 1) toCheck' _ _ _ (fvs ++ [⟨c.ngen.curr⟩]) rfl hV henv
        (by simp [hfl]) (by rw [VLCtx.fvars_cons_some, hfv]; simp) ?_ hΔ' ⟨_, W'⟩ ?_ ?_ hR' ?_
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨rfl, _, rfl⟩
        · exact hvlk x hx
      · show (ps ++ Ds)[i] :: Δc.toCtx = _
        rw [hΔt, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
          List.reverse_append]; rfl
      · simp only [declareConstructors.arity] at har
        rw [Lean.Expr.instantiate1_eq, declareConstructors.arity_instantiate1']; exact har
      · intro k f fv hk hf hnz hfv'
        by_cases hki : np + k < i
        · rw [List.getElem?_append_left (by omega)] at hfv'
          exact hsup _ (htc k f fv hki hf hnz hfv')
        · have hki' : np + k = i := by omega
          rw [List.getElem?_append_right (by omega), hfl] at hfv'
          simp [hki'] at hfv'; subst hfv'
          exact hnew (by omega) f (by rw [← hki']; simpa using hf) hnz
    dsimp only
    by_cases hge : stats.params.size ≤ i
    · rw [if_pos hge]
      have W'' : VLCtx.FVLift' Δk
          (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx.vlctx
          0 (ρ.skipN 1) 0 :=
        W.skip_fvar (⟨c.ngen.curr⟩, _) (.vlam _)
      have h1 := hdk.weakFV' henv.ordered W'' hΔb'; simp only [Lift.consN] at h1
      refine WF.bind (WF.liftTC (TypeChecker.ensureType.WF h1))
        fun s ⟨e', he', u, u', hs, hu, hty'⟩ => ?_
      subst hs
      have hW''c := W''.toCtx; simp only [Lift.consN] at hW''c
      have hdu : c.venv.HasType c.lparams.length Δk.toCtx dk (.sort u') := by
        have h3 := he'.uniq henv (.refl henv.ordered hΔb') h1
        have h4 := hty'.defeqU_l henv hΔb'.toCtx h3
        exact (VEnv.HasType.weak'_iff (A := .sort u') henv hΔb'.toCtx hW''c).1 h4
      have hAu : c.venv.HasType c.lparams.length Δc.toCtx (ps ++ Ds)[i] (.sort u') :=
        (hdu.defeqDFC henv.ordered (hΔ.defeqCtx.symm henv.ordered)).defeqU_l henv hΔc.toCtx
          hdkA.symm
      have hk : i - np < Ds.length := by omega
      have hDk : Ds[i - np]? = some (ps ++ Ds)[i] := by
        rw [List.getElem_append_right (by omega)]; simp [hps]
      have hctx : Δc.toCtx = (Ds.take (i - np)).reverse ++ ps.reverse := by
        have : List.take i (ps ++ Ds) = ps ++ Ds.take (i - np) := by
          rw [List.take_append, List.take_of_length_le (by omega), hps]
        rw [hΔt, this, List.reverse_append]
      have hiff (f) (hf : fields[i - np]? = some f) : u' ≈ .zero ↔ f.level ≈ .zero :=
        hlvl _ _ f hDk hf u' (hV ▸ hctx ▸ hAu)
      by_cases hz : (!(Expr.sort u).sortLevel!.isAlwaysZero) = true
      · rw [if_pos hz]
        exact cont _ (fun x hx => Array.mem_push_of_mem _ hx) fun _ _ _ _ => Array.mem_push_self
      · rw [if_neg hz]
        refine cont toCheck (fun _ h => h) fun _ f hf hnz => absurd ((hiff f hf).1 ?_) hnz
        simp only [Expr.sortLevel!, Bool.not_eq_true', Bool.not_eq_false] at hz
        exact (ofLevel_isAlwaysZero_iff hu).1 hz
    · rw [if_neg hge]
      exact cont toCheck (fun _ h => h) fun h => absurd h (by omega)
  · rw [isLargeEliminator.loop.eq_3 _ _ _ _ _ fun name dom body bi h =>
      hfa ⟨name, dom, body, bi, h⟩]
    refine WF.pure fun hb k f hf hnz => ?_
    have hai : declareConstructors.arity i t = i := by
      cases t with
      | forallE => exact (hfa ⟨_, _, _, _, rfl⟩).elim
      | _ => simp [declareConstructors.arity]
    have hieq : i = np + Ds.length := hai.symm.trans har
    rw [List.drop_eq_nil_of_le (by omega), VExpr.foralls_nil] at hR
    have hk : k < Ds.length := by rw [hDs]; exact (List.getElem?_eq_some_iff.1 hf).1
    have hkf : np + k < fvs.length := by omega
    have hmem := htc k f fvs[np + k] (by omega) hf hnz (List.getElem?_eq_getElem hkf)
    rw [Array.all_eq_true'] at hb
    have hcont := hb _ hmem
    rw [Array.contains_eq_any_beq, Array.any_eq_true'] at hcont
    obtain ⟨arg, harg, heqv⟩ := hcont
    have harg' : arg = .fvar fvs[np + k] := Expr.eqv'_fvar (by rw [← Expr.eqv_eq]; exact heqv)
    subst harg'
    rw [← Expr.mkAppList_getAppArgsList t] at hR
    obtain ⟨F', as', heq, -, has⟩ := TrExprS.mkAppList_inv hR
    rw [Expr.getAppArgs_eq, List.mem_toArray] at harg
    obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem harg
    obtain ⟨a', ha', htr⟩ := List.Forall₂.getElem?_l has (List.getElem?_eq_getElem hm)
    rw [hmeq] at htr
    cases htr with | fvar hfd => ?_
    have hpos : Δc.fvars[Ds.length - 1 - k]? = some fvs[np + k] := by
      rw [hfv, List.getElem?_reverse (by omega),
        show fvs.length - 1 - (Ds.length - 1 - k) = np + k by omega]
      exact List.getElem?_eq_getElem hkf
    obtain ⟨_, hfd'⟩ := VLCtx.find?_fvar_index hΔc.fvwf (hΔ.vlam_entries hvlk) hpos
    rw [hfd'] at hfd; cases hfd
    have := congrArg VExpr.appArgs heq
    simp only [VExpr.appArgs_appN, VExpr.appArgs, List.nil_append] at this
    have hin : VExpr.bvar (Ds.length - 1 - k) ∈ VExpr.bvars np Ds.length ++ indices := by
      rw [this]; exact List.mem_append_right _ (List.mem_of_getElem? ha')
    rw [← hDs]
    rcases List.mem_append.1 hin with h | h
    · simp [VExpr.bvars] at h; omega
    · exact h

/-- `isLargeEliminator`: when it answers yes, the block may eliminate into every sort. -/
theorem isLargeEliminator.WF {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    {c' : VContext} (hc' : c'.lparams = c.lparams) (hle : c₀.venv ≤ c'.venv) (henv : c'.venv.WF)
    {isUnsafe : Bool}
    (hC : ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c'.venv c'.lparams d t nidx ct) :
    AddInductive.WF c' (isLargeEliminator stats types.toArray) fun b => b = true →
      ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
        Elaborates c'.venv c'.lparams nparams level types d → d.LargeElimOK := by
  have hU₀ : c'.lparams = c₀.lparams := hc'.trans hT.base.lparams
  cases hnz : stats.isNotZero
  case true =>
    intro b hb hbt d hd _
    have := (ofLevel_isNeverZero_iff hT.resultLevel).1 (hT.isNotZero ▸ hnz)
    exact .inl (hd.level ▸ this)
  intro b hb hbt d hd hE
  have hlen := Lean4Lean.List.Forall₂.length_eq hE.types
  rcases types with _ | ⟨t, _ | ⟨t', ts⟩⟩
  · have : isLargeEliminator stats [].toArray = pure false := by
      show (if stats.isNotZero then pure true else _) = _; rw [hnz]; rfl
    rw [this] at hb; cases hb; cases hbt
  · obtain ⟨T, hT1⟩ : ∃ T, d.types = [T] := by
      match d.types, hlen with | [T], _ => exact ⟨T, rfl⟩
    have hE' := hE.types; rw [hT1] at hE'
    obtain ⟨⟨hTn, hcs⟩, -⟩ := List.forall₂_cons.1 hE'
    have : isLargeEliminator stats [t].toArray = (match t.ctors with
        | [] => pure true
        | [ctor] => do
          isLargeEliminator.loop stats ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
        | _ => pure false) := by
      show (if stats.isNotZero then pure true else _) = _; rw [hnz]; rfl
    rw [this] at hb
    rcases hct : t.ctors with _ | ⟨ct, _ | ⟨ct', cts⟩⟩ <;> rw [hct] at hb hcs
    · have : T.ctors = [] := by
        have := Lean4Lean.List.Forall₂.length_eq hcs; exact List.eq_nil_of_length_eq_zero this.symm
      exact .inr ⟨T, hT1, hd.aux, .inl this⟩
    · obtain ⟨c, hc1⟩ : ∃ c, T.ctors = [c] := by
        have := Lean4Lean.List.Forall₂.length_eq hcs
        match T.ctors, this with | [c], _ => exact ⟨c, rfl⟩
      rw [hc1] at hcs
      obtain ⟨hrel, -⟩ := List.forall₂_cons.1 hcs
      have hpar : d.params.length = nparams := hd.params ▸ hT.nparams
      have hps : c'.venv.IsTele d.uvars [] d.params := by
        rw [hd.uvars, hd.params, hU₀]; exact hT.params_tele.mono hle
      obtain ⟨-, har⟩ := ctor_WF henv hd.uvars hpar hps hTn (hd.nested T (by simp [hT1])) rfl
        (hC d hd 0 t rfl ct (by simp [hct]) _ (hd.indices 0 T (by simp [hT1]))) hrel
      obtain ⟨-, htr, ps, Ds, hpsl, hDs, hty, -, -, hlvl⟩ := hrel
      refine .inr ⟨T, hT1, hd.aux, .inr ⟨c, hc1, ?_⟩⟩
      have hsize : stats.params.size = nparams := params_size hT
      have key : AddInductive.WF c' (do
          let x ← readThe Context
          isLargeEliminator.loop stats ct.type 0 #[] x.fuel.inductiveFuel) fun b => b = true →
            ∀ k f, c.fields[k]? = some f → ¬f.level ≈ .zero →
              .bvar (c.fields.length - 1 - k) ∈ c.indices := by
        refine WF.bind WF.read fun _ hr => ?_; subst hr
        exact isLargeEliminator.loop.WF hsize hpsl hDs hlvl _ ct.type 0 #[] c' [] [] [] rfl rfl
          henv rfl rfl nofun .nil ⟨_, VLCtx.FVLift'.from_nil (MLCtx.noBV c'.mlctx)⟩ rfl
          (by rw [har, hDs]) (n := t.name) (by rw [List.drop_zero, ← hty]; exact htr) nofun
      exact key b hb hbt
    · cases hb; cases hbt
  · have : isLargeEliminator stats (t :: t' :: ts).toArray = pure false := by
      show (if stats.isNotZero then pure true else _) = _; rw [hnz]; rfl
    rw [this] at hb; cases hb; cases hbt

theorem getElimLevel.loop_eq {lparams : List Name} :
    ∀ {fuel : Nat} {u : Name} {i : Nat} {l : Level},
      getElimLevel.loop lparams u i fuel = .ok l → ∃ u, l = .param u ∧ u ∉ lparams
  | fuel + 1, u, i, l, h => by
    unfold getElimLevel.loop at h
    split at h
    · exact getElimLevel.loop_eq h
    · rename_i hu; cases h; exact ⟨u, rfl, fun hm => hu (List.elem_eq_true_of_mem hm)⟩

/-- `getElimLevel`: the recursor's motive gets a fresh level parameter only when the block may
eliminate into every sort, searching `u`, `u_1`, `u_2`, … for a name not among the level
parameters. -/
theorem getElimLevel.WF {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    {c' : VContext} (hc' : c'.lparams = c.lparams) (hle : c₀.venv ≤ c'.venv) (henv : c'.venv.WF)
    {isUnsafe : Bool}
    (hC : ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c'.venv c'.lparams d t nidx ct) :
    WF c' (getElimLevel stats types.toArray) fun l =>
      (l ≠ .zero → ∀ d, Compat c'.lparams params level isUnsafe types stats.nindices d →
        Elaborates c'.venv c'.lparams nparams level types d → d.LargeElimOK) ∧
      (l = .zero ∨ ∃ u, l = .param u ∧ u ∉ c'.lparams) := by
  unfold getElimLevel
  refine WF.bind (isLargeEliminator.WF hT hc' hle henv hC) fun b hb => ?_
  cases b
  · exact WF.pure ⟨fun h => absurd rfl h, .inl rfl⟩
  · intro l h
    obtain ⟨u, rfl, hu⟩ := getElimLevel.loop_eq h
    exact ⟨fun _ => hb rfl, .inr ⟨u, rfl, hu⟩⟩

end AddInductive
end Lean4Lean

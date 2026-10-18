import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.InductiveLemmas

/-!
# Telescopes

Typing for telescopes of binders and for applications to a list of arguments. A list of
arguments `as` for a pi telescope `As` is the substitution `Subst.consList .id as`, typed by
`Ctx.SubstEq`: `HasType.appN_subst` types the application by it, and `HasType.appN_inv` recovers
it from a well-typed application.
-/

namespace Lean4Lean
namespace VExpr

theorem foralls_append :
    ∀ (As Bs : List VExpr) (e : VExpr), VExpr.foralls (As ++ Bs) e = .foralls As (.foralls Bs e)
  | [], _, _ => rfl
  | _ :: As, Bs, e => by simp [foralls_append As Bs e]

theorem lams_append :
    ∀ (As Bs : List VExpr) (e : VExpr), VExpr.lams (As ++ Bs) e = .lams As (.lams Bs e)
  | [], _, _ => rfl
  | _ :: As, Bs, e => by simp [lams_append As Bs e]

@[simp] theorem appN_cons (e a : VExpr) (as) : e.appN (a :: as) = (e.app a).appN as := rfl

theorem appN_append_singleton (e a : VExpr) (as) : e.appN (as ++ [a]) = (e.appN as).app a := by
  rw [appN_append]; rfl

@[simp] theorem length_bvars (n k : Nat) : (bvars n k).length = n := by simp [bvars]

@[simp] theorem Subst.ofLift_apply (ρ : Lift) (i : Nat) : Subst.ofLift ρ i = .bvar (ρ.liftVar i) :=
  rfl

theorem lift'_eq_subst {e : VExpr} {ρ : Lift} : e.lift' ρ = e.subst (.ofLift ρ) := by
  induction e generalizing ρ with
  | bvar | sort | const => rfl
  | app _ _ ih1 ih2 => simp [lift', subst, ih1, ih2]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp only [lift', subst, ih1, ih2]; congr 2; funext i
    cases i <;> simp [Subst.lift, lift, liftN, liftVar]; omega
  | proj _ _ _ ih => simp [lift', subst, ih]

theorem liftN_eq_subst {e : VExpr} : e.liftN n k = e.subst (.ofLift (.consN (.skipN .refl n) k)) := by
  rw [← lift'_consN_skipN, lift'_eq_subst]

@[simp] theorem Subst.consList_nil (σ : Subst) : σ.consList [] = σ := rfl

theorem Subst.consList_append (σ : Subst) :
    ∀ as bs, σ.consList (as ++ bs) = (σ.consList as).consList bs
  | [], _ => rfl
  | _ :: as, bs => Subst.consList_append _ as bs

theorem Subst.consList_concat (σ : Subst) (as a) :
    σ.consList (as ++ [a]) = (σ.consList as).cons a := Subst.consList_append ..

theorem Subst.consList_ge (σ : Subst) :
    ∀ (as : List VExpr) (i : Nat), σ.consList as (i + as.length) = σ i
  | [], _ => rfl
  | a :: as, i => by
    have := consList_ge (σ.cons a) as (i + 1)
    rwa [Nat.add_right_comm] at this

theorem Subst.consList_lt :
    ∀ (σ : Subst) (as : List VExpr) (i : Nat) (h : i < as.length),
      σ.consList as i = as.reverse[i]'(by simpa using h)
  | _, [], _, h => nomatch h
  | σ, a :: as, i, h => by
    show (σ.cons a).consList as i = _
    simp only [List.reverse_cons]
    by_cases hi : i < as.length
    · rw [consList_lt _ as i hi, List.getElem_append_left]
    · have : i = 0 + as.length := by simp at h; omega
      subst this
      rw [consList_ge]; simp [Subst.cons]

theorem subst_bvars_consList (σ : Subst) (as : List VExpr) :
    (bvars as.length 0).map (·.subst (σ.consList as)) = as := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [bvars, List.map_map, List.getElem_map, List.getElem_reverse, List.getElem_range,
    Function.comp_apply, Nat.add_zero, subst_bvar, List.length_range]
  simp at h1
  rw [Subst.consList_lt _ _ _ (by omega), List.getElem_reverse]
  congr 1; omega

theorem subst_bvars_consList_ge (σ : Subst) (as : List VExpr) (n j : Nat) :
    (bvars n (j + as.length)).map (·.subst (σ.consList as)) = (bvars n j).map (·.subst σ) := by
  simp [bvars, ← Nat.add_assoc, Subst.consList_ge]

theorem liftN_subst_consList (σ : Subst) (as : List VExpr) (e : VExpr) :
    (e.liftN as.length).subst (σ.consList as) = e.subst σ := by
  rw [liftN_eq_subst, subst_subst]; congr 1; funext i
  simp [Subst.comp, Lift.liftVar_skipN, Subst.consList_ge]

end VExpr

namespace VEnv
open VExpr

theorem IsTele.append {env : VEnv} {U : Nat} :
    ∀ {Γ As Bs}, env.IsTele U Γ As → env.IsTele U (As.reverse ++ Γ) Bs → env.IsTele U Γ (As ++ Bs)
  | _, [], _, .nil, h => h
  | _, _ :: _, _, .cons hA t, h => .cons hA (IsTele.append t (by simpa using h))

theorem IsTele.append_inv {env : VEnv} {U : Nat} :
    ∀ {Γ As Bs}, env.IsTele U Γ (As ++ Bs) → env.IsTele U Γ As ∧ env.IsTele U (As.reverse ++ Γ) Bs
  | _, [], _, h => ⟨.nil, by simpa using h⟩
  | _, _ :: _, _, .cons hA t =>
    let ⟨h1, h2⟩ := IsTele.append_inv t
    ⟨.cons hA h1, by simpa using h2⟩

theorem IsTele.onCtx {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    OnCtx Γ (env.IsType U) → OnCtx (As.reverse ++ Γ) (env.IsType U)
  | _, [], _, hΓ => hΓ
  | _, _ :: _, .cons hA h, hΓ => by simpa using h.onCtx ⟨hΓ, hA⟩

theorem IsTele.concat {env : VEnv} {U : Nat} {Γ As A} (h : env.IsTele U Γ As)
    (hA : env.IsType U (As.reverse ++ Γ) A) : env.IsTele U Γ (As ++ [A]) :=
  h.append (.cons hA .nil)

theorem IsTele.of_getElem {env : VEnv} {U : Nat} {Γ} : ∀ {As : List VExpr},
    (∀ i (h : i < As.length), env.IsType U ((As.take i).reverse ++ Γ) As[i]) → env.IsTele U Γ As
  | [], _ => .nil
  | A :: As, H => .cons (H 0 (by simp)) <| IsTele.of_getElem (Γ := A :: Γ) fun i h => by
      have := H (i + 1) (by simpa using h)
      simp only [List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.getElem_cons_succ] at this
      exact this

theorem IsTele.instL {env : VEnv} {U U'} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ As}, env.IsTele U Γ As →
      env.IsTele U' (Γ.map (VExpr.instL ls)) (As.map (VExpr.instL ls))
  | _, [], .nil => .nil
  | _, _ :: _, .cons hA t => .cons (hA.instL hls) (by simpa using IsTele.instL hls t)

variable! (henv : Ordered env) in
theorem IsType.foralls_inv : ∀ {Γ As B}, env.IsType U Γ (.foralls As B) →
    env.IsTele U Γ As ∧ env.IsType U (As.reverse ++ Γ) B
  | _, [], _, h => ⟨.nil, h⟩
  | _, _ :: _, _, h => by
    obtain ⟨h1, h2⟩ := h.forallE_inv henv
    obtain ⟨h3, h4⟩ := IsType.foralls_inv h2
    exact ⟨.cons h1 h3, by simpa using h4⟩

theorem IsTele.lams {env : VEnv} {U : Nat} : ∀ {Γ As e B}, env.IsTele U Γ As →
    env.HasType U (As.reverse ++ Γ) e B → env.HasType U Γ (.lams As e) (.foralls As B)
  | _, [], _, _, .nil, h => h
  | _, _ :: _, _, _, .cons ⟨_, hA⟩ t, h => .lam hA (IsTele.lams t (by simpa using h))

variable! (henv : Ordered env) in
theorem Ctx.SubstEq.weak' (W : Ctx.Lift' ρ Γ₀ Γ₀')
    (H : Ctx.SubstEq env U Γ₀ σ σ' Γ) :
    Ctx.SubstEq env U Γ₀' (σ.lift_r ρ) (σ'.lift_r ρ) Γ := by
  induction H with
  | nil => exact .nil
  | cons _ hA hhead ih =>
    refine .cons (Subst.lift_r_tail ▸ Subst.lift_r_tail ▸ ih) hA ?_
    rw [Subst.lift_r_tail]
    have := hhead.weak' henv W
    rwa [lift'_subst] at this

variable! (henv : Ordered env) in
theorem Ctx.SubstEq.ofLift' (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) :
    Ctx.SubstEq env U Γ' (.ofLift ρ) (.ofLift ρ) Γ :=
  (Ctx.SubstEq.id henv hΓ).weak' henv W

variable! (henv : Ordered env) in
/-- A term whose type is a pi telescope, applied to arguments that instantiate the telescope. -/
theorem HasType.appN_subst {Γ f As B as} (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f (.foralls As B)) (hlen : as.length = As.length)
    (W : Ctx.SubstEq env U Γ (Subst.consList .id as) (Subst.consList .id as) (As.reverse ++ Γ)) :
    env.HasType U Γ (f.appN as) (B.subst (Subst.consList .id as)) := by
  have := (hf.appN_bvars henv).subst henv W hΓ
  rwa [subst_appN, ← hlen, liftN_subst_consList, subst_id, subst_bvars_consList] at this

end VEnv
end Lean4Lean

namespace Lean4Lean
namespace VExpr

theorem Subst.consList_bvars (σ : Subst) (n k : Nat) :
    σ.consList (bvars n k) = fun i => if i < n then .bvar (i + k) else σ (i - n) := by
  funext i
  split <;> rename_i h
  · rw [consList_lt _ _ _ (by simpa using h)]
    simp [bvars]
  · have := consList_ge σ (bvars n k) (i - n)
    simp only [length_bvars] at this
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem Subst.consList_cons_tail (σ : Subst) (a : VExpr) (as : List VExpr) :
    (σ.cons a).consList as = σ.consList (a :: as) := rfl

/-- Lift the entries of a telescope in context `Γ` along a lift of `Γ`. -/
def liftTele' (ρ : Lift) : List VExpr → List VExpr
  | [] => []
  | A :: As => A.lift' ρ :: liftTele' ρ.cons As

@[simp] theorem length_liftTele' : ∀ (ρ : Lift) (As : List VExpr), (liftTele' ρ As).length = As.length
  | _, [] => rfl
  | _, _ :: As => congrArg (· + 1) (length_liftTele' _ As)

theorem liftTele_eq_liftTele' : ∀ (As : List VExpr) (n k : Nat),
    liftTele n As k = liftTele' (.consN (.skipN .refl n) k) As
  | [], _, _ => rfl
  | A :: As, n, k => by
    simp only [liftTele, liftTele', ← lift'_consN_skipN, liftTele_eq_liftTele' As n (k + 1)]; rfl

theorem appN_wf_prefix {env : VEnv} {U Γ} (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as bs : List VExpr} {f : VExpr}, (f.appN (as ++ bs)).WF env U Γ → (f.appN as).WF env U Γ
  | as, [], f, h => by simpa using h
  | as, b :: bs, f, h => by
    have h' := appN_wf_prefix henv hΓ (as := as ++ [b]) (bs := bs) (by simpa using h)
    rw [appN_append_singleton] at h'
    obtain ⟨_, _, h1, _⟩ := h'.app_inv henv hΓ
    exact ⟨_, h1⟩

end VExpr

open VExpr

theorem Lookup.append_left : ∀ (Δ : List VExpr) {Γ i A}, Lookup Γ i A →
    Lookup (Δ ++ Γ) (Δ.length + i) (A.liftN Δ.length)
  | [], _, _, _, h => by simpa using h
  | B :: Δ, Γ, i, A, h => by
    have := (Lookup.append_left Δ h).succ (A := B)
    simp only [List.length_cons, List.cons_append]
    rwa [liftN_succ, Nat.add_right_comm]

theorem Lookup.reverse_append : ∀ (As : List VExpr) {Γ} (i : Nat) (h : i < As.length),
    Lookup (As.reverse ++ Γ) (As.length - 1 - i) (As[i].liftN (As.length - i))
  | [], _, _, h => nomatch h
  | A :: As, Γ, 0, _ => by
    have := Lookup.append_left As.reverse (Lookup.zero (ty := A) (Γ := Γ))
    simp only [List.length_reverse, Nat.add_zero, lift, liftN_liftN] at this
    simpa [Nat.add_comm] using this
  | A :: As, Γ, i + 1, h => by
    have := Lookup.reverse_append As (Γ := A :: Γ) i (by simpa using h)
    have e1 : As.length + 1 - 1 - (i + 1) = As.length - 1 - i := by omega
    have e2 : As.length + 1 - (i + 1) = As.length - i := by omega
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      List.getElem_cons_succ, e1, e2]
    exact this

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem Ctx.SubstEq.tail (H : Ctx.SubstEq env U Γ₀ σ σ' (A :: Δ)) :
    Ctx.SubstEq env U Γ₀ σ.tail σ'.tail Δ := by cases H; assumption

theorem Ctx.SubstEq.dropList : ∀ {σ σ' : Subst} {as as' Bs : List VExpr} {Δ},
    as.length = Bs.length → as'.length = Bs.length →
    Ctx.SubstEq env U Γ₀ (σ.consList as) (σ'.consList as') (Bs.reverse ++ Δ) →
    Ctx.SubstEq env U Γ₀ σ σ' Δ
  | _, _, [], [], [], _, _, _, H => H
  | _, _, [], _, _ :: _, _, h1, _, _ | _, _, _ :: _, _, [], _, h1, _, _
  | _, _, _, [], _ :: _, _, _, h1, _ | _, _, _, _ :: _, [], _, _, h1, _ => nomatch h1
  | σ, σ', a :: as, a' :: as', B :: Bs, Δ, h1, h2, H => by
    rw [List.reverse_cons, List.append_assoc] at H
    exact (Ctx.SubstEq.dropList (σ := σ.cons a) (σ' := σ'.cons a') (Δ := B :: Δ)
      (Nat.succ.inj h1) (Nat.succ.inj h2) H).tail

/-- A term whose type is a pi telescope under a substitution `τ`, applied to arguments that
extend `τ` to the telescope. -/
theorem HasType.appN_substT {Γ : List VExpr} : ∀ {Δ As B τ f as},
    env.HasType U Γ f ((VExpr.foralls As B).subst τ) → as.length = As.length →
    Ctx.SubstEq env U Γ (τ.consList as) (τ.consList as) (As.reverse ++ Δ) →
    env.HasType U Γ (f.appN as) (B.subst (τ.consList as))
  | _, [], _, _, _, [], hf, _, _ => hf
  | Δ, A :: As, B, τ, f, a :: as, hf, hlen, W => by
    rw [List.reverse_cons, List.append_assoc] at W
    have W' := Ctx.SubstEq.dropList (as := as) (as' := as) (Bs := As) (Δ := A :: Δ)
      (Nat.succ.inj hlen) (Nat.succ.inj hlen) W
    have ha : env.HasType U Γ a (A.subst τ) := by
      cases W' with | cons _ _ h => exact h
    have hfa := hf.app ha
    rw [inst_lift_cons] at hfa
    exact HasType.appN_substT (Δ := A :: Δ) (As := As) (τ := τ.cons a) (f := f.app a) (as := as)
      hfa (Nat.succ.inj hlen) W

/-- Definitionally equal functions whose type is a pi telescope under `τ`, applied to pairs of
definitionally equal arguments for the telescope. -/
theorem IsDefEq.appN_substTDF {Γ : List VExpr} : ∀ {Δ As B} {τ τ' : Subst} {f g as bs},
    env.IsDefEq U Γ f g ((VExpr.foralls As B).subst τ) → as.length = As.length →
    bs.length = As.length →
    Ctx.SubstEq env U Γ (τ.consList as) (τ'.consList bs) (As.reverse ++ Δ) →
    env.IsDefEq U Γ (f.appN as) (g.appN bs) (B.subst (τ.consList as))
  | _, [], _, _, _, _, _, [], [], hf, _, _, _ => hf
  | Δ, A :: As, B, τ, τ', f, g, a :: as, b :: bs, hf, hlen, hlen', W => by
    rw [List.reverse_cons, List.append_assoc] at W
    have W' := Ctx.SubstEq.dropList (as := as) (as' := bs) (Bs := As) (Δ := A :: Δ)
      (Nat.succ.inj hlen) (Nat.succ.inj hlen') W
    have ha : env.IsDefEq U Γ a b (A.subst τ) := by
      cases W' with | cons _ _ h => exact h
    have hfa := hf.appDF ha
    rw [inst_lift_cons] at hfa
    exact IsDefEq.appN_substTDF (Δ := A :: Δ) (As := As) (τ := τ.cons a) (τ' := τ'.cons b)
      (f := f.app a) (g := g.app b) (as := as) (bs := bs) hfa (Nat.succ.inj hlen)
      (Nat.succ.inj hlen') W

/-- The arguments of a well-typed application extend the substitution its function's pi
telescope is typed under. -/
theorem IsTele.weak' (henv : Ordered env) : ∀ {ρ Γ Γ' As}, Ctx.Lift' ρ Γ Γ' →
    env.IsTele U Γ As → env.IsTele U Γ' (liftTele' ρ As)
  | _, _, _, [], _, .nil => .nil
  | _, _, _, _ :: _, W, .cons h t => .cons (h.weak' henv W) (IsTele.weak' henv (.cons W) t)

theorem _root_.Lean4Lean.Ctx.Lift'.tele : ∀ {ρ Γ Γ'} (As : List VExpr), Ctx.Lift' ρ Γ Γ' →
    Ctx.Lift' (.consN ρ As.length) (As.reverse ++ Γ) ((liftTele' ρ As).reverse ++ Γ')
  | _, _, _, [], W => W
  | ρ, Γ, Γ', A :: As, W => by
    have := Ctx.Lift'.tele (ρ := ρ.cons) As (.cons W (A := A))
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, liftTele',
      List.length_cons]
    rwa [show ρ.cons = ρ.consN 1 from rfl, Lift.consN_consN, Nat.add_comm] at this

theorem TeleDefEq.append : ∀ {Γ As Bs As' Bs'}, env.TeleDefEq U Γ As Bs →
    env.TeleDefEq U (Bs.reverse ++ Γ) As' Bs' → env.TeleDefEq U Γ (As ++ As') (Bs ++ Bs')
  | _, [], [], _, _, .nil, h => h
  | _, _ :: _, _ :: _, _, _, .cons h t, h' => .cons h (TeleDefEq.append t (by simpa using h'))

/-- Pi telescopes over agreeing domains are definitionally equal. -/
theorem _root_.Lean4Lean.VExpr.Subst.lift_l_cons (σ : Subst) (ρ : Lift) (a : VExpr) :
    (σ.cons a).lift_l ρ.cons = (σ.lift_l ρ).cons a := by
  funext i; cases i <;> rfl

/-- Arguments for a telescope over `Δ`, given where `Δ`'s variables go by a lift `ρ` of `Δ` and a
substitution `σ` on its target, are arguments for the lifted telescope under `σ`. -/
theorem Ctx.SubstEq.extendLift (henv : Ordered env) {Γ : List VExpr} :
    ∀ {ρ Δ Δ' σ As as}, Ctx.Lift' ρ Δ Δ' → env.IsTele U Δ As →
    Ctx.SubstEq env U Γ σ σ Δ' →
    Ctx.SubstEq env U Γ ((σ.lift_l ρ).consList as) ((σ.lift_l ρ).consList as) (As.reverse ++ Δ) →
    as.length = As.length →
    Ctx.SubstEq env U Γ (σ.consList as) (σ.consList as) ((liftTele' ρ As).reverse ++ Δ')
  | _, _, _, _, [], [], _, _, hσ, _, _ => hσ
  | ρ, Δ, Δ', σ, A :: As, a :: as, W, .cons ⟨_, hA⟩ hAs, hσ, H, hlen => by
    rw [List.reverse_cons, List.append_assoc] at H
    have H1 := Ctx.SubstEq.dropList (as := as) (as' := as) (Bs := As) (Δ := A :: Δ)
      (Nat.succ.inj hlen) (Nat.succ.inj hlen) H
    have ha : env.HasType U Γ a (A.subst (σ.lift_l ρ)) := by
      cases H1 with | cons _ _ h => exact h
    rw [← subst_lift'] at ha
    have hσ' : Ctx.SubstEq env U Γ (σ.cons a) (σ.cons a) (A.lift' ρ :: Δ') :=
      .cons hσ (by simpa using hA.weak' henv W) ha
    have := Ctx.SubstEq.extendLift henv (ρ := ρ.cons) (σ := σ.cons a) (As := As) (as := as)
      (.cons W) hAs hσ' (by rw [Subst.lift_l_cons]; exact H) (Nat.succ.inj hlen)
    simp only [liftTele', List.reverse_cons, List.append_assoc, List.singleton_append]
    exact this

/-- Arguments for a telescope, each typed against its entry instantiated by the ones before it. -/
theorem Ctx.SubstEq.ofGetElem {Γ Δ : List VExpr} {σ : Subst} (hσ : Ctx.SubstEq env U Γ σ σ Δ) :
    ∀ (n : Nat) {As as : List VExpr}, as.length = n → env.IsTele U Δ As → as.length = As.length →
    (∀ r (h : r < as.length) (h' : r < As.length),
      env.HasType U Γ as[r] (As[r].subst (σ.consList (as.take r)))) →
    Ctx.SubstEq env U Γ (σ.consList as) (σ.consList as) (As.reverse ++ Δ)
  | 0, As, as, hn, _, hlen, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero (hlen.symm.trans hn)
    exact hσ
  | n + 1, As, as, hn, hAs, hlen, H => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    obtain ⟨hAs', hA⟩ := IsTele.append_inv hAs
    have ⟨_, hA⟩ : env.IsType U (As.reverse ++ Δ) A := by cases hA with | cons h _ => exact h
    rw [Subst.consList_concat, List.reverse_append]
    refine .cons (Ctx.SubstEq.ofGetElem hσ n hn hAs' hlen fun r h h' => ?_) hA ?_
    · have := H r (by simp; omega) (by simp; omega)
      simp only [List.getElem_append_left h, List.getElem_append_left h',
        List.take_append_of_le_length (Nat.le_of_lt h)] at this
      exact this
    · have h1 := H as.length (by simp) (by simp; omega)
      have e1 : (as ++ [a])[as.length]'(by simp) = a := by simp
      have e2 : (As ++ [A])[as.length]'(by simp; omega) = A := by simp [hlen]
      have e3 : (as ++ [a]).take as.length = as := by simp
      rw [e1, e2, e3] at h1
      exact h1

/-- Pairs of arguments for a telescope, each pair defeq at its entry instantiated by the left
arguments before it. -/
theorem Ctx.SubstEq.ofGetElemDF {Γ Δ : List VExpr} {σ σ' : Subst}
    (hσ : Ctx.SubstEq env U Γ σ σ' Δ) :
    ∀ (n : Nat) {As as bs : List VExpr}, as.length = n → env.IsTele U Δ As →
    as.length = As.length → bs.length = As.length →
    (∀ r (h : r < as.length) (h' : r < bs.length) (h'' : r < As.length),
      env.IsDefEq U Γ as[r] bs[r] (As[r].subst (σ.consList (as.take r)))) →
    Ctx.SubstEq env U Γ (σ.consList as) (σ'.consList bs) (As.reverse ++ Δ)
  | 0, As, as, bs, hn, _, hlen, hlen', _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    obtain rfl := List.eq_nil_of_length_eq_zero hlen'
    exact hσ
  | n + 1, As, as, bs, hn, hAs, hlen, hlen', H => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    obtain ⟨bs, b, rfl⟩ : ∃ bs' b, bs = bs' ++ [b] := by
      simpa using (List.eq_nil_or_concat bs).resolve_left (by rintro rfl; simp at hlen')
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn hlen'
    obtain ⟨hAs', hA⟩ := IsTele.append_inv hAs
    have ⟨_, hA⟩ : env.IsType U (As.reverse ++ Δ) A := by cases hA with | cons h _ => exact h
    rw [Subst.consList_concat, Subst.consList_concat, List.reverse_append]
    refine .cons (Ctx.SubstEq.ofGetElemDF hσ n hn hAs' hlen hlen' fun r h h' h'' => ?_) hA ?_
    · have := H r (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [List.getElem_append_left h, List.getElem_append_left h',
        List.getElem_append_left h'', List.take_append_of_le_length (Nat.le_of_lt h)] at this
      exact this
    · have h1 := H as.length (by simp) (by simp; omega) (by simp; omega)
      have e1 : (as ++ [a])[as.length]'(by simp) = a := by simp
      have e2 : (As ++ [A])[as.length]'(by simp; omega) = A := by simp [hlen]
      have e2' : (bs ++ [b])[as.length]'(by simp; omega) = b := by simp [hlen, hlen']
      have e3 : (as ++ [a]).take as.length = as := by simp
      rw [e1, e2, e2', e3] at h1
      exact h1

end VEnv

namespace VExpr

theorem Subst.liftN_apply (σ : Subst) : ∀ (k i : Nat),
    σ.liftN k i = if i < k then .bvar i else (σ (i - k)).liftN k
  | 0, i => by simp [Subst.liftN]
  | k + 1, 0 => by simp [Subst.liftN, Subst.lift]
  | k + 1, i + 1 => by
    simp only [Subst.liftN, Subst.lift, Subst.liftN_apply σ k i]
    split <;> split <;> first
      | rfl | omega
      | (simp [VExpr.lift, VExpr.liftN, liftVar]; omega)
      | (rw [VExpr.lift, VExpr.liftN_liftN]; congr 2; omega)

theorem Subst.consList_apply (σ : Subst) (as : List VExpr) (i : Nat) :
    σ.consList as i = if h : i < as.length then as.reverse[i]'(by simpa using h)
      else σ (i - as.length) := by
  split <;> rename_i h
  · exact consList_lt σ as i h
  · have := consList_ge σ as (i - as.length)
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem Subst.lift_liftN (σ : Subst) : ∀ i, σ.lift.liftN i = σ.liftN (i + 1)
  | 0 => rfl
  | i + 1 => by
    show (σ.lift.liftN i).lift = (σ.liftN (i + 1)).lift
    rw [Subst.lift_liftN σ i]

theorem subst_foralls : ∀ (As : List VExpr) (B : VExpr) (σ : Subst),
    (VExpr.foralls As B).subst σ =
      .foralls (As.zipIdx.map fun (A, i) => A.subst (σ.liftN i)) (B.subst (σ.liftN As.length))
  | [], _, _ => rfl
  | A :: As, B, σ => by
    simp only [foralls_cons, subst, List.length_cons, List.zipIdx_cons, List.map_cons]
    rw [subst_foralls As B σ.lift, List.zipIdx_succ, List.map_map]
    congr 2
    · apply List.map_congr_left; rintro ⟨A', i⟩ _
      simp only [Function.comp_apply, Subst.lift_liftN]
    · rw [Subst.lift_liftN]

end VExpr
end Lean4Lean

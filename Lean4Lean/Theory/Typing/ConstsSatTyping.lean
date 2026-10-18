import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.ConstsSat

/-!
# The constants a judgment mentions
-/

namespace Lean4Lean
open VExpr

namespace VEnv
variable {env : VEnv}

theorem ConstsSat.inst {p : Name → Prop} {e a : VExpr} {k : Nat} (he : e.ConstsSat p)
    (ha : a.ConstsSat p) : (e.inst a k).ConstsSat p := by
  rw [instN_eq]
  refine he.subst fun i => ?_
  induction k generalizing i with
  | zero => cases i <;> simp [Subst.liftN, Subst.cons, Subst.id, VExpr.ConstsSat, ha]
  | succ k ih =>
    cases i with
    | zero => trivial
    | succ i => exact (ih i).liftN

variable! {p : Name → Prop} (henv : OnTypes env fun _ e A => e.ConstsSat p ∧ A.ConstsSat p)
  (hc : ∀ {c ci}, env.constants c = some ci → p c) in
/-- The constants of a judgment's terms, from those of the environment's types and rules. -/
theorem IsDefEq.constsSat' (H : env.IsDefEq U Γ e1 e2 A) (hΓ : OnCtx Γ fun _ A => A.ConstsSat p) :
    e1.ConstsSat p ∧ e2.ConstsSat p ∧ A.ConstsSat p := by
  induction H with
  | bvar h => exact ⟨trivial, trivial, hΓ.lookup h fun h => h.liftN⟩
  | constDF h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨hc h1, hc h1, h.instL⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, ConstsSat.inst hB ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 ⟨hΓ, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, ConstsSat.inst he he', ConstsSat.inst hB he'⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, he.liftN, trivial⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨hl.instL, hr.instL, hA.instL⟩
  | projDF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih2 ih3 =>
    exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih3 hΓ).1⟩
  | projIota _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ih3 =>
    exact ⟨(ih1 hΓ).1, (ih3 hΓ).1, (ih3 hΓ).2.2⟩
  | projEta _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact ⟨(ih1 hΓ).1, (ih2 hΓ).1, (ih1 hΓ).2.2⟩

/-- An ordered environment's types and rules mention only its constants. -/
theorem Ordered.constsSat (H : env.Ordered) :
    env.OnTypes fun _ e A => e.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome) := by
  refine H.induction (fun env _ e A => e.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome)) (fun {env₁ env₂ _ _ _} hle h => ?_)
    (fun _ ih h => ?_)
  · have hm : ∀ c, (env₁.constants c).isSome = true → (env₂.constants c).isSome = true := by
      intro c hc
      obtain ⟨ci, e⟩ := Option.isSome_iff_exists.1 hc
      rw [hle.constants e]; rfl
    exact ⟨h.1.mono hm, h.2.mono hm⟩
  · have := IsDefEq.constsSat' ih (fun h => by simp [h]) h trivial
    exact ⟨this.1, this.2.2⟩

/-- A judgment of an ordered environment mentions only its constants. -/
theorem IsDefEq.constsSat (henv : env.Ordered) (H : env.IsDefEq U Γ e1 e2 A)
    (hΓ : OnCtx Γ fun _ A => A.ConstsSat (env.constants · |>.isSome)) :
    e1.ConstsSat (env.constants · |>.isSome) ∧ e2.ConstsSat (env.constants · |>.isSome) ∧
      A.ConstsSat (env.constants · |>.isSome) :=
  IsDefEq.constsSat' henv.constsSat (fun h => by simp [h]) H hΓ

end VEnv
end Lean4Lean

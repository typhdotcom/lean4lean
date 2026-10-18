import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Typing.UniqueTyping

/-! Telescopes, inverted: the arguments of a well-typed application instantiate its function's
telescope, which takes uniqueness of typing. -/

namespace Lean4Lean
open VExpr
namespace VEnv
variable {env : VEnv} {U : Nat}

/-- The arguments of a well-typed application instantiate the function's pi telescope. -/
theorem HasType.appN_inv [VEnv.Injective] (henv : env.WF) {Γ f} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (n : Nat) {As B as}, as.length = n → env.HasType U Γ f (.foralls As B) →
    (f.appN as).WF env U Γ → as.length = As.length →
    Ctx.SubstEq env U Γ (Subst.consList .id as) (Subst.consList .id as) (As.reverse ++ Γ)
  | 0, As, B, as, hn, _, _, hlen => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero (hlen.symm.trans hn)
    exact Ctx.SubstEq.id henv.ordered hΓ
  | n+1, As, B, as, hn, hf, hwf, hlen => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] :=
      by simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] :=
      by simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hn hlen
    rw [foralls_append] at hf
    rw [appN_append_singleton] at hwf
    obtain ⟨A₁, B₁, h1, h2⟩ := hwf.app_inv henv.ordered hΓ
    have W := HasType.appN_inv henv hΓ n hn hf ⟨_, h1⟩ hlen
    have h3 := hf.appN_subst henv.ordered hΓ hlen W
    have ⟨⟨u, hA⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (h1.uniqU henv hΓ h3)
    have ⟨_, hAB⟩ := (IsType.foralls_inv henv.ordered (hf.isType henv.ordered hΓ)).2
    have ⟨⟨_, hA'⟩, _⟩ := IsType.forallE_inv henv.ordered ⟨_, hAB⟩
    rw [Subst.consList_concat, List.reverse_append]
    exact .cons W hA' (h2.defeqU_r henv hΓ ⟨_, hA⟩)

theorem HasType.appN_invT [VEnv.Injective] (henv : env.WF) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {Δ As B τ f as},
    env.HasType U Γ f ((VExpr.foralls As B).subst τ) → Ctx.SubstEq env U Γ τ τ Δ →
    env.IsTele U Δ As → (f.appN as).WF env U Γ → as.length = As.length →
    Ctx.SubstEq env U Γ (τ.consList as) (τ.consList as) (As.reverse ++ Δ)
  | _, [], _, _, _, [], _, hτ, _, _, _ => hτ
  | Δ, A :: As, B, τ, f, a :: as, hf, hτ, .cons ⟨_, hA⟩ hAs, hwf, hlen => by
    have hwf1 := appN_wf_prefix henv.ordered hΓ (as := [a]) (bs := as) hwf
    obtain ⟨A₁, B₁, h1, h2⟩ := hwf1.app_inv henv.ordered hΓ
    have ⟨⟨u, hA'⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ (h1.uniqU henv hΓ hf)
    have ha : env.HasType U Γ a (A.subst τ) := h2.defeqU_r henv hΓ ⟨_, hA'⟩
    have hτ' : Ctx.SubstEq env U Γ (τ.cons a) (τ.cons a) (A :: Δ) := .cons hτ hA ha
    have hfa := hf.app ha
    rw [inst_lift_cons] at hfa
    have := HasType.appN_invT henv hΓ (Δ := A :: Δ) hfa hτ' hAs hwf (Nat.succ.inj hlen)
    rw [List.reverse_cons, List.append_assoc]; exact this

theorem TeleDefEq.foralls [VEnv.Injective] (henv : env.WF) : ∀ {Γ As Bs R}, OnCtx Γ (env.IsType U) →
    env.TeleDefEq U Γ As Bs → env.IsTele U Γ Bs → env.IsType U (Bs.reverse ++ Γ) R →
    env.IsDefEqU U Γ (.foralls As R) (.foralls Bs R)
  | _, [], [], _, _, .nil, _, ⟨_, hR⟩ => ⟨_, hR⟩
  | Γ, A :: As, B :: Bs, R, hΓ, .cons hAB t, .cons ⟨_, hB⟩ tB, hR => by
    have h1 := hAB.of_r henv hΓ hB
    have ⟨_, h2⟩ := TeleDefEq.foralls henv (Γ := B :: Γ) (R := R) ⟨hΓ, _, hB⟩ t tB (by simpa using hR)
    have ⟨_, hY⟩ := tB.foralls (B := R) (by simpa using hR)
    have h3 := VEnv.IsDefEqU.of_r (Γ := B :: Γ) henv ⟨hΓ, _, hB⟩ ⟨_, h2⟩ hY
    have h4 := h3.defeqDFC henv.ordered (.succ .zero h1.symm)
    exact ⟨_, .forallEDF h1 h4⟩

/-- Telescopes that agree entry by entry give contexts that do. -/
theorem TeleDefEq.defeqCtx [VEnv.Injective] (henv : env.WF) :
    ∀ {Γ' Γ As Bs}, env.TeleDefEq U Γ As Bs → env.IsDefEqCtx U [] Γ' Γ →
      OnCtx Γ (env.IsType U) → env.IsTele U Γ Bs →
      env.IsDefEqCtx U [] (As.reverse ++ Γ') (Bs.reverse ++ Γ)
  | _, _, [], [], .nil, hΓ, _, _ => hΓ
  | _, _, _ :: _, _ :: _, .cons hAB t, hΓ, hwf, .cons ⟨u, hB⟩ tB => by
    have h1 := (hAB.of_r henv hwf hB).defeqDFC henv.ordered (hΓ.symm henv.ordered)
    simpa using t.defeqCtx henv (.succ hΓ h1) ⟨hwf, _, hB⟩ tB

end VEnv
end Lean4Lean

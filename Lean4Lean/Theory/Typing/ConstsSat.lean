import Lean4Lean.Theory.VExpr

/-!
# The constants a term mentions
-/

namespace Lean4Lean
namespace VExpr

/-- Every constant `e` mentions satisfies `p`. -/
def ConstsSat (p : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _ => p c
  | .app f a | .lam f a | .forallE f a => f.ConstsSat p ∧ a.ConstsSat p
  | .proj _ _ e => e.ConstsSat p

theorem ConstsSat.mono {p q : Name → Prop} (h : ∀ c, p c → q c) :
    ∀ {e : VExpr}, e.ConstsSat p → e.ConstsSat q
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, H => h c H
  | .app .., H | .lam .., H | .forallE .., H => ⟨H.1.mono h, H.2.mono h⟩
  | .proj _ _ _, H => ConstsSat.mono h (e := ‹_›) H

theorem ConstsSat.appN {p : Name → Prop} {f : VExpr} :
    ∀ {as : List VExpr}, (f.appN as).ConstsSat p ↔ f.ConstsSat p ∧ ∀ a ∈ as, a.ConstsSat p
  | [] => by simp [VExpr.appN]
  | a :: as => by
    rw [VExpr.appN, ConstsSat.appN]
    simp only [ConstsSat, List.mem_cons, forall_eq_or_imp]; exact and_assoc

theorem ConstsSat.liftN {p : Name → Prop} :
    ∀ {e : VExpr} {n k : Nat}, e.ConstsSat p → (e.liftN n k).ConstsSat p
  | .bvar _, _, _, _ | .sort _, _, _, _ => trivial
  | .const _ _, _, _, H => H
  | .app .., _, _, H | .lam .., _, _, H | .forallE .., _, _, H => ⟨H.1.liftN, H.2.liftN⟩
  | .proj _ _ e, _, _, H => ConstsSat.liftN (e := e) H

theorem ConstsSat.instL {p : Name → Prop} {ls : List VLevel} :
    ∀ {e : VExpr}, e.ConstsSat p → (e.instL ls).ConstsSat p
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, H => H
  | .app .., H | .lam .., H | .forallE .., H => ⟨H.1.instL, H.2.instL⟩
  | .proj _ _ e, H => ConstsSat.instL (e := e) H

theorem ConstsSat.subst {p : Name → Prop} :
    ∀ {e : VExpr} {σ : Subst}, e.ConstsSat p → (∀ i, (σ i).ConstsSat p) →
      (e.subst σ).ConstsSat p
  | .bvar _, _, _, h => h _
  | .sort _, _, _, _ => trivial
  | .const _ _, _, H, _ => H
  | .app .., _, H, h => ⟨H.1.subst h, H.2.subst h⟩
  | .lam .., _, H, h | .forallE .., _, H, h => ⟨H.1.subst h, H.2.subst fun i => by
      cases i with
      | zero => trivial
      | succ i => exact (h i).liftN⟩
  | .proj _ _ e, _, H, h => ConstsSat.subst (e := e) H h

end VExpr
end Lean4Lean

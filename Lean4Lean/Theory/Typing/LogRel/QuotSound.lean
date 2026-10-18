import Lean4Lean.Theory.Typing.LogRel.BlockSound

/-!
# Soundness of the quotient's computation rule in the model
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat}

/-- The quotient's rule forward, under its binders, at any valuation: an interpretation of
`Quot.lift α r β f h (Quot.mk α r a)` interprets `f a`. -/
theorem quot_body_le (hM : ModelEnv env) (hq : env.defeqs quotDefEq) {u v : VLevel}
    {σ : Valuation} {y : TShape}
    (H : LE_Interp env σ y ((VExpr.const ``Quot.lift [u, v]).appN
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
        (VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0]])) :
    LE_Interp env σ y (.app (.bvar 2) (.bvar 0)) := by
  have hA : ConstArity env ``Quot.lift .quotLift 6 := .quotLift hq rfl
  rw [← spine_eq_appN] at H
  obtain ⟨n0, H0⟩ := H.spine_inv hM.roles (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y', hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 6 := by rw [List.Forall₂.length_eq hra]; simp
  refine LE_Interp.mono hyy ?_
  cases hC with
  | bot => exact .bot
  | lam he hle => exact LE_Interp.mono (Const.lam_le_bot hM.roles he hle (hrl ▸ hA)) .bot
  | delta h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotK h1 h2 h3 h4 h5 =>
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
    cases hra with | cons _ hra =>
    cases hra with | cons _ hra =>
    cases hra with | cons hf _ =>
    let .cons (f := f') (x := x0) h6 h7 h8 := h5
    let .nil h9 := h8
    exact .app (hf.mono h6) (.mono h7 .bot) h9
  | quot h1 h2 h3 h4 h5 h6 =>
    rename_i a x hh f β r α
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
    cases hra with | cons hx hra =>
    cases hra with | cons _ hra =>
    cases hra with | cons hf _ =>
    let .cons (f := f') (x := x0) h7 h8 h9 := h5
    let .nil h10 := h9
    refine .app (hf.mono h7) (.bvar ?_) h10
    refine h8.trans ?_
    -- the major premise's interpretation is a `Quot.mk` shape above `a`
    by_cases hne : IsStruct ``Quot.mk → WShape.ListNonZero [a]
    · have hB : ConstArity env ``Quot.mk .quotMk 3 := .quotMk hq rfl
      rw [← spine_eq_appN] at hx
      obtain ⟨n1, H1⟩ := hx.spine_inv hM.roles (fun r n' h => by
        cases hM.roles h hB; have := hB.determ h; simp; omega)
      obtain ⟨rargs', y'', hra', hyy', hC'⟩ := H1 n1 (Nat.le_refl _)
      have hrl' : rargs'.length = 3 := by rw [List.Forall₂.length_eq hra']; simp
      have hxy := h6.trans hyy'
      cases hC' with
      | quotMk g1 g2 g3 g4 g5 =>
        rename_i a' r' α'
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
          at hra'
        cases hra' with | cons ha' _ =>
        obtain ⟨-, hl⟩ := TShape.ctor'_le_ctor' hne (hxy.trans g5)
        cases hl with | cons hl _ =>
        exact hl.trans (bvar_iff.1 ha')
      | bot =>
        obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1
          (WShape.LE.of_T ((hxy.trans TShape.bot_eqv.1).trans TShape.bot_eqv.2)) hne
        simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
      | lam he hle =>
        have := Const.lam_le_bot hM.roles he hle (hrl' ▸ hB)
        obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1
          (WShape.LE.of_T ((hxy.trans this).trans TShape.bot_eqv.2)) hne
        simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
      | delta g1 g2 => cases hM.roles (.delta g1 g2) hB
      | indTy g1 g2 => cases hM.roles (.indTy g1 g2) hB
      | ctor g1 g2 g3 g4 => cases hM.roles (.ctor g1 g2 g3 g4) hB
      | quotTy g1 g2 => cases hM.roles (.quotTy g1 g2) hB
      | quot g1 g2 => cases hM.roles (.quotLift g1 g2) hB
      | quotK g1 g2 => cases hM.roles (.quotLift g1 g2) hB
      | iota g1 g2 g3 g4 => cases hM.roles (.recursor g1 g2 g4) hB
      | kIota g1 g2 g3 g4 => cases hM.roles (.recursor g1 g2 g4) hB
    · have hz : a.1 ≤ .bot := Classical.byContradiction fun h' =>
        hne fun _ => ⟨a, .head _, h'⟩
      exact (WShape.LE.T (b := .bot) hz).trans TShape.bot_le'

end LogRel
end Lean4Lean

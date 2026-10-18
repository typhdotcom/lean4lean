import Lean4Lean.Theory.Typing.LogRel.IndStepOf
import Lean4Lean.Theory.Typing.LogRel.StructTyOf

/-!
# Stuck values of a block's structure types have typed projections

`IndHY`, from `structTy_spine` at both substitutions of a related pair.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

theorem indHY : IndHY := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d hX hXD hW hI hR hD hext hdom IH IHall
  letI := env.shapeEnv; letI := X
  intro T hTm ls ls₃ n rargs F σ σ' hls₃ e₃ hlen hF W hrl
  have hMX := henvW.modelEnv hX hXD
  have hEW : E.WF := ⟨_, hW⟩
  obtain ⟨hd, envT, envC, envR, h1, h2, h3, hTE', -, hs, -, hcC⟩ := induct_facts hD hext.le
  have hTle : envT ≤ env := hTE'.trans hext.le
  obtain ⟨dsT, hWT⟩ : envT.WF := VEnv.WF.addConstList hEW (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) h1
  have hTo : envT.Ordered := VEnv.WF.ordered ⟨_, hWT⟩
  have hIT := (hR envT envC envR h1 h2 h3).1
  obtain ⟨t, hs', hT'⟩ := hs T hTm
  have hc1 : ∀ cv ∈ T.ctors, IsStruct cv.name = true → T.ctors = [cv] := fun cv hcv hIS =>
    ctors_eq_single_of_eta henvW hs' hT' hcv (hMX.struct _ hIS)
  exact ⟨structTy_spine hMX henvW hΓ₀ hd h1 hTle hTo hIT hs' hT' (hcC T hTm) hc1 hls₃ e₃ hlen _ hF
      (W.left.toSubstEq hΓ₀),
    structTy_spine hMX henvW hΓ₀ hd h1 hTle hTo hIT hs' hT' (hcC T hTm) hc1 hls₃ e₃ hlen _ hF
      (W.symm.left.toSubstEq hΓ₀)⟩

end LogRel
end Lean4Lean

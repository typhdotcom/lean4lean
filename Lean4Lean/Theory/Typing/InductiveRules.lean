import Lean4Lean.Theory.Typing.Substitution
import Lean4Lean.Theory.Typing.RecursorInv

/-!
# What an inductive block generates is well typed

In a well-formed environment, which uniqueness of typing applies to.
-/

namespace Lean4Lean

/-! The typing of what `VEnv.addInduct` generates, in the environments it adds it to. -/

/-- The recursors are well-typed, given the types and constructors. -/
theorem VInductDecl.recConsts_WF {decl : VInductDecl} {env envT envC : VEnv} (henv : env.WF)
    (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC) :
    ∀ p ∈ decl.recConsts, p.2.WF envC := by
  intro p hp
  have hF := VInductDecl.recFacts henv hdecl hT hC VInductDecl.recLevels_WF
    VInductDecl.recLevels_length
  simp only [VInductDecl.recConsts, List.mem_map] at hp
  obtain ⟨⟨T, i⟩, hm, rfl⟩ := hp
  exact VInductDecl.recType_isType hF VInductDecl.motiveLevel_WF (List.mem_zipIdx_iff_getElem?.1 hm)

/-- The iota rules are well-typed, given the recursors. -/
theorem VInductDecl.iotaRules_WF {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.WF) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) :
    ∀ df ∈ decl.iotaRules, df.WF envR := by
  have hF := VInductDecl.recFacts henv hdecl hT hC VInductDecl.recLevels_WF
    VInductDecl.recLevels_length
  have hF' := hF.mono (VEnv.addConstList_le hR)
    (VEnv.WF.addConstList hF.wf (recConsts_WF henv hdecl hT hC) hR)
  have hrec : decl.RecTyped envR decl.recUVars decl.recLevels decl.motiveLevel
      (decl.recConst (VLevel.params decl.recUVars)) := fun {t T} ht => by
    have hc := VEnv.addConstList_constants_of_mem hR <| List.mem_map.2
      ⟨(T, t), List.mem_zipIdx_iff_getElem?.2 ht, rfl⟩
    have ⟨_, hty⟩ := VInductDecl.recType_isType hF' VInductDecl.motiveLevel_WF ht
    have := VEnv.HasType.const (Γ := []) (ls := VLevel.params decl.recUVars) hc VLevel.params_wf
      (by simp)
    simp only [VInductDecl.recConst, ht, Option.map_some, Option.getD_some]
    rwa [(hty.levelWF trivial).1.instL_id] at this
  intro df hdf
  simp only [VInductDecl.iotaRules, List.mem_map] at hdf
  obtain ⟨⟨⟨j, c⟩, q⟩, hm, rfl⟩ := hdf
  exact VInductDecl.iotaRule_WF hF' VInductDecl.motiveLevel_WF hrec
    (List.mem_zipIdx_iff_getElem?.1 hm) (by simp)

theorem VEnv.IsTele.ctxLevelWF {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    OnCtx Γ (fun _ A => A.LevelWF U) → OnCtx (As.reverse ++ Γ) (fun _ A => A.LevelWF U)
  | _, [], .nil, hΓ => hΓ
  | _, _ :: _, .cons ⟨_, hA⟩ t, hΓ => by
    simpa using VEnv.IsTele.ctxLevelWF t ⟨hΓ, (hA.levelWF hΓ).1⟩

theorem VExpr.lams_body_inj : ∀ {As : List VExpr} {e e' : VExpr},
    VExpr.lams As e = .lams As e' → e = e'
  | [], _, _, h => h
  | _ :: _, _, _, h => VExpr.lams_body_inj (VExpr.lam.inj h).2

theorem VExpr.foralls_body_inj : ∀ {As : List VExpr} {e e' : VExpr},
    VExpr.foralls As e = .foralls As e' → e = e'
  | [], _, _, h => h
  | _ :: _, _, _, h => VExpr.foralls_body_inj (VExpr.forallE.inj h).2

theorem VEnv.IsTele.levelWF {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    OnCtx Γ (fun _ A => A.LevelWF U) → ∀ A ∈ As, A.LevelWF U
  | _, [], .nil, _ => nofun
  | _, _ :: _, .cons ⟨_, hA⟩ t, hΓ => by
    have h := (hA.levelWF hΓ).1
    intro A hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact VEnv.IsTele.levelWF t ⟨hΓ, h⟩ A hm

theorem VInductDecl.FieldsWF.getElem {d : VInductDecl} {env : VEnv} {Γ k Ds fs}
    (H : d.FieldsWF env Γ k Ds fs) : ∀ i f, fs[i]? = some f →
      env.HasType d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) f.type (.sort f.level) ∧
      f.level.WF d.uvars := by
  induction H with
  | nil => simp
  | cons _ h2 h3 _ _ _ _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using ⟨h2, h3⟩
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons] using this

theorem VInductDecl.generatedWF {decl : VInductDecl} {env : VEnv} (henv : env.WF)
    (hdecl : decl.WF env) : decl.GeneratedWF env := fun _ _ _ hT hC hR =>
  ⟨recConsts_WF henv hdecl hT hC, iotaRules_WF henv hdecl hT hC hR⟩

end Lean4Lean

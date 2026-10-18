import Lean4Lean.Theory.Typing.Recursor

/-!
# Substitution lemmas for telescopes

Instantiating telescopes of binders with arguments, and lambda telescopes beta-reducing against
them; and the recursor's and iota rules' commuting with instantiating level parameters.
-/

namespace Lean4Lean
open VExpr

namespace VExpr

theorem subst_lams : ∀ (As : List VExpr) (B : VExpr) (σ : Subst),
    (VExpr.lams As B).subst σ =
      .lams (As.zipIdx.map fun (A, i) => A.subst (σ.liftN i)) (B.subst (σ.liftN As.length))
  | [], _, _ => rfl
  | A :: As, B, σ => by
    simp only [lams_cons, subst, List.length_cons, List.zipIdx_cons, List.map_cons]
    rw [subst_lams As B σ.lift, List.zipIdx_succ, List.map_map]
    congr 2
    · apply List.map_congr_left; rintro ⟨A', i⟩ _
      simp only [Function.comp_apply, Subst.lift_liftN]
    · rw [Subst.lift_liftN]

theorem instL_liftTele (ls : List VLevel) (n : Nat) : ∀ (As : List VExpr) (k : Nat),
    (liftTele n As k).map (·.instL ls) = liftTele n (As.map (·.instL ls)) k
  | [], _ => rfl
  | A :: As, k => by simp [liftTele, instL_liftTele ls n As (k + 1)]

theorem instL_lams (ls : List VLevel) : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.lams As B).instL ls = .lams (As.map (·.instL ls)) (B.instL ls)
  | [], _ => rfl
  | _ :: As, B => by simp [instL, instL_lams ls As B]

end VExpr

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem addDefEqList_defeqs_of_mem : ∀ {dfs : List VDefEq} {env : VEnv} {df : VDefEq},
    df ∈ dfs → (env.addDefEqList dfs).defeqs df
  | d :: dfs, env, df, h => by
    show ((env.addDefEq d).addDefEqList dfs).defeqs df
    rcases List.mem_cons.1 h with rfl | h
    · exact VEnv.addDefEqList_le.defeqs addDefEq_self
    · exact addDefEqList_defeqs_of_mem h

end VEnv
end Lean4Lean

namespace Lean4Lean
open VExpr

namespace VExpr

theorem Subst.comp_consList (σ' : Subst) : ∀ (σ : Subst) (as : List VExpr),
    (σ.consList as).comp σ' = (σ.comp σ').consList (as.map (·.subst σ'))
  | _, [] => rfl
  | σ, a :: as => by
    show ((σ.cons a).consList as).comp σ' = _
    rw [Subst.comp_consList σ' (σ.cons a) as]
    show _ = ((σ.comp σ').cons (a.subst σ')).consList _
    congr 1; funext i; cases i <;> rfl

theorem Subst.consList_congr {σ σ' : Subst} {N : Nat} (h : ∀ i < N, σ i = σ' i)
    (as : List VExpr) : ∀ i < N + as.length, σ.consList as i = σ'.consList as i := by
  intro i hi
  rw [Subst.consList_apply, Subst.consList_apply]
  split
  · rfl
  · exact h _ (by omega)

theorem Subst.ofLift_liftN (ρ : Lift) (i : Nat) :
    (Subst.ofLift ρ).liftN i = Subst.ofLift (ρ.consN i) := by
  funext x
  rw [Subst.liftN_apply]
  simp only [Subst.ofLift, Lift.liftVar_consN]
  split
  · rfl
  · simp only [VExpr.liftN, liftVar_base']

theorem ClosedN.lams : ∀ {As : List VExpr} {b : VExpr} {N : Nat},
    (∀ i (A : VExpr), As[i]? = some A → A.ClosedN (N + i)) → b.ClosedN (N + As.length) →
    (VExpr.lams As b).ClosedN N
  | [], _, _, _, hb => hb
  | A :: As, b, N, hA, hb =>
    ⟨by simpa using hA 0 A rfl, ClosedN.lams (N := N + 1) (fun i A h => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using hA (i + 1) A h)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)⟩

end VExpr

end Lean4Lean

namespace Lean4Lean
open VExpr
namespace VInductDecl
variable {d : VInductDecl}

/-! The recursor and the iota rules commute with instantiating their level parameters. -/

theorem _root_.Lean4Lean.VExpr.instL_reseat (ls : List VLevel) (e : VExpr) (a k m b l : Nat) :
    (e.reseat a k m b l).instL ls = (e.instL ls).reseat a k m b l := by
  simp [reseat]

theorem ctorAppAt_instL (j : Nat) (c : VConstructor) (ls ls' : List VLevel) (ps fs : List VExpr) :
    (d.ctorAppAt j c ls ps fs).instL ls' =
      d.ctorAppAt j c (ls.map (VLevel.inst ls')) (ps.map (·.instL ls')) (fs.map (·.instL ls')) := by
  simp [ctorAppAt, VInductiveType.ctorApp_instL]

theorem motiveType_instL (ls ls' : List VLevel) (v : VLevel) (j : Nat) (T : VInductiveType) :
    (d.motiveType ls v j T).instL ls' =
      d.motiveType (ls.map (VLevel.inst ls')) (v.inst ls') j T := by
  simp [motiveType, instL_foralls, instL_liftTele, List.map_map, Function.comp_def,
    instL_instL, instL, instL_bvars, VInductiveType.typeApp_instL]

theorem minorType_instL (ls ls' : List VLevel) (q j : Nat) (c : VConstructor) :
    (d.minorType ls q j c).instL ls' = d.minorType (ls.map (VLevel.inst ls')) q j c := by
  simp [minorType, instL_foralls, instL_appN, instL_liftTele, List.map_map, Function.comp_def,
    instL_instL, instL, instL_bvars, ctorAppAt_instL, instL_reseat]

theorem recType_instL (ls ls' : List VLevel) (v : VLevel) (i : Nat) (T : VInductiveType) :
    (d.recType ls v i T).instL ls' =
      d.recType (ls.map (VLevel.inst ls')) (v.inst ls') i T := by
  simp [recType, recBinders, motiveTypes, minorTypes, instL_foralls, instL_appN, instL_liftTele,
    List.map_map, Function.comp_def, instL_instL, instL, instL_bvars,
    VInductiveType.typeApp_instL, motiveType_instL, minorType_instL]

theorem recConst_instL (recLs ls' : List VLevel) (j : Nat) :
    (d.recConst recLs j).instL ls' = d.recConst (recLs.map (VLevel.inst ls')) j := by
  simp [recConst, instL]

theorem iotaRule_instL (ls ls' recLs : List VLevel) (v : VLevel) (q j : Nat) (c : VConstructor) :
    let r := d.iotaRule (ls.map (VLevel.inst ls')) (v.inst ls') (recLs.map (VLevel.inst ls')) q j c
    (d.iotaRule ls v recLs q j c).lhs.instL ls' = r.lhs ∧
    (d.iotaRule ls v recLs q j c).rhs.instL ls' = r.rhs ∧
    (d.iotaRule ls v recLs q j c).type.instL ls' = r.type := by
  simp [iotaRule, recBinders, motiveTypes, minorTypes, instL_foralls, instL_lams, instL_appN,
    instL_liftTele, List.map_map, Function.comp_def, instL_instL, instL, instL_bvars,
    ctorAppAt_instL, motiveType_instL, minorType_instL, recConst_instL, instL_reseat]

end VInductDecl
end Lean4Lean

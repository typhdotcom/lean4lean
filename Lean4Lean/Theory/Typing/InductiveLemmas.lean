import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
namespace VEnv

theorem addConstList_ordered : ∀ {env env' : VEnv} {cs : List (Name × VConstant)}, Ordered env →
    (∀ p ∈ cs, p.2.WF env) → env.addConstList cs = some env' → Ordered env'
  | _, _, [], h, _, e => by cases e; exact h
  | _, _, _ :: _, h, hw, e => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine addConstList_ordered (.const h (hw _ (.head _)) h1) (fun p hp => ?_) h2
    exact (hw p (.tail _ hp)).mono (addConst_le h1)

theorem addDefEqList_ordered : ∀ {env : VEnv} {dfs : List VDefEq}, Ordered env →
    (∀ df ∈ dfs, df.WF env) → Ordered (env.addDefEqList dfs)
  | _, [], h, _ => h
  | env, df :: dfs, h, hw =>
    show Ordered ((env.addDefEq df).addDefEqList dfs) from
      addDefEqList_ordered (.defeq h (hw _ (.head _))) fun d hd =>
        (hw d (.tail _ hd)).mono addDefEq_le

end VEnv

/-! ### Telescopes -/

@[simp] theorem VExpr.bvars_zero (k : Nat) : VExpr.bvars 0 k = [] := rfl

theorem VExpr.bvars_succ (n k : Nat) : VExpr.bvars (n + 1) k = .bvar (n + k) :: VExpr.bvars n k := by
  simp [VExpr.bvars, List.range_succ]

@[simp] theorem VExpr.liftN_appN (e : VExpr) : ∀ as, (e.appN as).liftN n k =
    (e.liftN n k).appN (as.map (·.liftN n k))
  | [] => rfl
  | a :: as => by simp [VExpr.appN, VExpr.liftN_appN _ as, VExpr.liftN]

@[simp] theorem VExpr.length_liftTele : ∀ (As : List VExpr) (k : Nat),
    (VExpr.liftTele n As k).length = As.length
  | [], _ => rfl
  | _ :: As, k => by simp [VExpr.liftTele, length_liftTele As]

namespace VEnv

variable! (henv : Ordered env) in
theorem IsTele.weakN : ∀ {k Γ Γ' As}, Ctx.LiftN n k Γ Γ' → env.IsTele U Γ As →
    env.IsTele U Γ' (VExpr.liftTele n As k)
  | _, _, _, [], _, .nil => .nil
  | _, _, _, _ :: _, W, .cons h t => .cons (h.weakN henv W) (IsTele.weakN (.succ W) t)

theorem IsTele.foralls {env : VEnv} {U B} : ∀ {Γ As}, env.IsTele U Γ As → env.IsType U (As.reverse ++ Γ) B →
    env.IsType U Γ (.foralls As B)
  | _, [], .nil, h => h
  | _, _ :: _, .cons hA t, h => hA.forallE (IsTele.foralls t (by simpa using h))

variable! (henv : Ordered env) in
/-- A term whose type is a pi telescope, applied to the telescope's own variables. -/
theorem HasType.appN_bvars : ∀ {Γ f As}, env.HasType U Γ f (.foralls As B) →
    env.HasType U (As.reverse ++ Γ) ((f.liftN As.length).appN (VExpr.bvars As.length 0)) B
  | _, _, [], h => by simpa using h
  | Γ, f, A :: As, h => by
    have h1 : env.HasType U (A :: Γ) (.app f.lift (.bvar 0)) (.foralls As B) := by
      have hw := h.weakN henv (.one (A := A))
      change env.HasType U (A :: Γ) f.lift (.forallE (A.liftN 1) ((VExpr.foralls As B).liftN 1 1)) at hw
      have := hw.app (.bvar .zero)
      rwa [VExpr.inst_liftN_bvar] at this
    have := HasType.appN_bvars h1
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    simpa [VExpr.bvars_succ, VExpr.appN, VExpr.liftN, VExpr.liftN_liftN, Nat.add_comm] using this

end VEnv

theorem VInductDecl.mem_ctors {decl : VInductDecl} {j c} (h : (j, c) ∈ decl.ctors) :
    ∃ T ∈ decl.types, c ∈ T.ctors := by
  simp only [VInductDecl.ctors, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨⟨T, i⟩, hT, rfl⟩, hc⟩ := h
  obtain ⟨c', hc', ⟨⟩⟩ := List.mem_map.1 hc
  exact ⟨T, List.fst_mem_of_mem_zipIdx hT, hc'⟩

/-! The typing of what `VEnv.addInduct` generates, in the environments it adds it to. -/

/-- The recursors are well-typed, given the types and constructors. -/
theorem VInductDecl.recConsts_WF {decl : VInductDecl} {env envT envC : VEnv} (henv : env.Ordered)
    (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC) :
    ∀ p ∈ decl.recConsts, p.2.WF envC :=
  sorry

/-- The iota rules are well-typed, given the recursors. -/
theorem VInductDecl.iotaRules_WF {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.Ordered) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) :
    ∀ df ∈ decl.iotaRules, df.WF envR :=
  sorry

/-- The eta rule is well-typed, given the iota rules: the projections it is stated with compute
on a constructor only by iota. -/
theorem VInductDecl.etaRules_WF {decl : VInductDecl} {env envT envC envR : VEnv}
    (henv : env.Ordered) (hdecl : decl.WF env) (hT : env.addConstList decl.typeConsts = some envT)
    (hC : envT.addConstList decl.ctorConsts = some envC)
    (hR : envC.addConstList decl.recConsts = some envR) :
    ∀ df ∈ decl.etaRules, df.WF (envR.addDefEqList decl.iotaRules) :=
  sorry

namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  simp [VEnv.addInduct, Option.bind_eq_some_iff] at henv'
  obtain ⟨envT, hT, envC, hC, envR, hR, rfl⟩ := henv'
  have oT := addConstList_ordered henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact hdecl.types T hT) hT
  have oC := addConstList_ordered oT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T, hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdecl.ctors envT hT T hT').2 c hc).type) hC
  have oR := addConstList_ordered oC (VInductDecl.recConsts_WF henv hdecl hT hC) hR
  exact addDefEqList_ordered (addDefEqList_ordered oR (VInductDecl.iotaRules_WF henv hdecl hT hC hR))
    (VInductDecl.etaRules_WF henv hdecl hT hC hR)

end VEnv

import Lean4Lean.Theory.Typing.Recursor

/-!
# Substitution lemmas for telescopes

Instantiating telescopes of binders with arguments, and lambda telescopes beta-reducing against
them; and the recursor's and iota rules' commuting with instantiating level parameters.
-/

namespace Lean4Lean
open VExpr

namespace VExpr

theorem ClosedN.subst_congr {e : VExpr} {k : Nat} {σ σ' : Subst} (self : ClosedN e k)
    (h : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with (simp [ClosedN] at self; simp [VExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    refine ⟨ih1 self.1 h, ih2 self.2 fun i hi => ?_⟩
    cases i with
    | zero => rfl
    | succ i => simp [Subst.lift, h i (by omega)]
  | proj _ _ _ ih => exact ih self h

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

/-- Defeq functions whose type is a pi telescope under `τ`, applied to the same arguments. -/
theorem IsDefEq.appN_substT {Γ : List VExpr} : ∀ {Δ As B τ f f' as},
    env.IsDefEq U Γ f f' ((VExpr.foralls As B).subst τ) → as.length = As.length →
    Ctx.SubstEq env U Γ (τ.consList as) (τ.consList as) (As.reverse ++ Δ) →
    env.IsDefEq U Γ (f.appN as) (f'.appN as) (B.subst (τ.consList as))
  | _, [], _, _, _, _, [], hf, _, _ => hf
  | Δ, A :: As, B, τ, f, f', a :: as, hf, hlen, W => by
    rw [List.reverse_cons, List.append_assoc] at W
    have W' := Ctx.SubstEq.dropList (as := as) (as' := as) (Bs := As) (Δ := A :: Δ)
      (Nat.succ.inj hlen) (Nat.succ.inj hlen) W
    have ha : env.HasType U Γ a (A.subst τ) := by
      cases W' with | cons _ _ h => exact h
    have hfa := IsDefEq.appDF hf ha
    rw [inst_lift_cons] at hfa
    exact IsDefEq.appN_substT (Δ := A :: Δ) (As := As) (τ := τ.cons a) hfa (Nat.succ.inj hlen) W

variable! (henv : Ordered env) in
/-- A lambda telescope under `τ` applied to arguments for its binders beta-reduces to its body
under the extended substitution. -/
theorem IsDefEq.lams_beta {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (env.IsType U)) :
    ∀ {Δ As L T τ as}, Ctx.SubstEq env U Γ₀ τ τ Δ → env.IsTele U Δ As →
    env.HasType U (As.reverse ++ Δ) L T → as.length = As.length →
    Ctx.SubstEq env U Γ₀ (τ.consList as) (τ.consList as) (As.reverse ++ Δ) →
    env.IsDefEq U Γ₀ (((VExpr.lams As L).subst τ).appN as) (L.subst (τ.consList as))
      (T.subst (τ.consList as))
  | _, [], _, _, _, [], hτ, _, hL, _, _ => hL.subst henv hτ hΓ₀
  | Δ, A :: As, L, T, τ, a :: as, hτ, .cons ⟨_, hA⟩ hAs, hL, hlen, W => by
    rw [List.reverse_cons, List.append_assoc] at W
    have W' := Ctx.SubstEq.dropList (as := as) (as' := as) (Bs := As) (Δ := A :: Δ)
      (Nat.succ.inj hlen) (Nat.succ.inj hlen) W
    have ha : env.HasType U Γ₀ a (A.subst τ) := by
      cases W' with | cons _ _ h => exact h
    have hX : env.HasType U (A :: Δ) (.lams As L) (.foralls As T) :=
      hAs.lams (by simpa using hL)
    have hX' := hX.subst henv (hτ.lift henv hA) ⟨hΓ₀, _, hA.subst henv hτ hΓ₀⟩
    have hb := IsDefEq.beta hX' ha
    rw [inst_lift_cons, inst_lift_cons] at hb
    have h1 := IsDefEq.appN_substT (Δ := A :: Δ) (As := As) (B := T) (τ := τ.cons a) (as := as)
      hb (Nat.succ.inj hlen) W
    have h2 := IsDefEq.lams_beta hΓ₀ (Δ := A :: Δ) (τ := τ.cons a) (as := as) W' hAs
      (by simpa using hL) (Nat.succ.inj hlen) W
    exact h1.trans h2

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

theorem motiveType_instL (ls ls' : List VLevel) (v : VLevel) (j : Nat) (T : VInductiveType) :
    (d.motiveType ls v j T).instL ls' =
      d.motiveType (ls.map (VLevel.inst ls')) (v.inst ls') j T := by
  simp [motiveType, instL_foralls, instL_appN, instL_liftTele, List.map_map, Function.comp_def,
    instL_instL, instL, instL_bvars]

theorem minorType_instL (ls ls' : List VLevel) (q j : Nat) (c : VConstructor) :
    (d.minorType ls q j c).instL ls' = d.minorType (ls.map (VLevel.inst ls')) q j c := by
  simp [minorType, instL_foralls, instL_appN, instL_liftTele, List.map_map, Function.comp_def,
    instL_instL, instL, instL_bvars, instL_reseat]

theorem recType_instL (ls ls' : List VLevel) (v : VLevel) (i : Nat) (T : VInductiveType) :
    (d.recType ls v i T).instL ls' =
      d.recType (ls.map (VLevel.inst ls')) (v.inst ls') i T := by
  simp [recType, recBinders, motiveTypes, minorTypes, instL_foralls, instL_appN, instL_liftTele,
    List.map_map, Function.comp_def, instL_instL, instL, instL_bvars, motiveType_instL,
    minorType_instL]

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
    motiveType_instL, minorType_instL, recConst_instL, instL_reseat]

end VInductDecl
end Lean4Lean

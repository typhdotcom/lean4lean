import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env

namespace Lean4Lean
theorem VInductDecl.mem_allCtors {decl : VInductDecl} {j c} (h : (j, c) ∈ decl.allCtors) :
    ∃ T ∈ decl.allTypes, c ∈ T.ctors := by
  simp only [VInductDecl.allCtors, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨⟨T, i⟩, hT, rfl⟩, hc⟩ := h
  obtain ⟨c', hc', ⟨⟩⟩ := List.mem_map.1 hc
  exact ⟨T, List.fst_mem_of_mem_zipIdx hT, hc'⟩

theorem VInductDecl.mem_allCtors_iff {decl : VInductDecl} {j : Nat} {c} :
    (j, c) ∈ decl.allCtors ↔ ∃ T, decl.allTypes[j]? = some T ∧ c ∈ T.ctors := by
  simp only [VInductDecl.allCtors, List.mem_flatten, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨_, ⟨⟨T, i⟩, hT, rfl⟩, hc⟩
    obtain ⟨c', hc', ⟨⟩⟩ := List.mem_map.1 hc
    exact ⟨T, by simpa using hT, hc'⟩
  · rintro ⟨T, hT, hc⟩
    exact ⟨_, ⟨⟨T, j⟩, by simpa using hT, rfl⟩, List.mem_map.2 ⟨c, hc, rfl⟩⟩

theorem VInductDecl.allTypes_getElem?_of_types {decl : VInductDecl} {t : Nat} {T}
    (h : decl.types[t]? = some T) : decl.allTypes[t]? = some T := by
  rw [VInductDecl.allTypes, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem VInductDecl.mem_allTypes_of_types {decl : VInductDecl} {T} (h : T ∈ decl.types) :
    T ∈ decl.allTypes := List.mem_append_left _ h

/-- The constructors of the block's own types come first among all its constructors. -/
theorem VInductDecl.allCtors_eq_append (decl : VInductDecl) :
    ∃ rest, decl.allCtors = decl.ctors ++ rest := by
  simp only [VInductDecl.allCtors, VInductDecl.allTypes, VInductDecl.ctors, List.zipIdx_append,
    List.map_append, List.flatten_append]
  exact ⟨_, rfl⟩

theorem VInductDecl.mem_allCtors_of_ctors {decl : VInductDecl} {j c} (h : (j, c) ∈ decl.ctors) :
    (j, c) ∈ decl.allCtors := by
  obtain ⟨rest, e⟩ := decl.allCtors_eq_append; rw [e]; exact List.mem_append_left _ h

theorem VInductDecl.allTypes_of_aux {decl : VInductDecl} (h : decl.aux = []) :
    decl.allTypes = decl.types := by simp [VInductDecl.allTypes, h]

theorem VInductDecl.allCtors_of_aux {decl : VInductDecl} (h : decl.aux = []) :
    decl.allCtors = decl.ctors := by
  simp [VInductDecl.allCtors, VInductDecl.ctors, VInductDecl.allTypes_of_aux h]

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

namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env) (hgen : decl.GeneratedWF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  simp [VEnv.addInduct, Option.bind_eq_some_iff] at henv'
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := henv'
  have oT := addConstList_ordered henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hdecl.types T hT).1) hT
  have oC := addConstList_ordered oT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T, hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdecl.ctors envT hT T (List.mem_append_left _ hT')).2 c hc).type) hC
  obtain ⟨hrec, hiota⟩ := hgen envT envC envR hT hC hR
  have oR := addConstList_ordered oC hrec hR
  exact .block (addDefEqList_ordered oR hiota) hB

end VEnv

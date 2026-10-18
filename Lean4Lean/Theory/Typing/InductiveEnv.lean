import Lean4Lean.Theory.Typing.TelescopeInv

/-!
# Environments with an inductive block

Adding lists of constants, and monotonicity of the specification in the environment.
-/

namespace Lean4Lean

/-! ### Adding lists of constants -/

theorem VEnv.addConstList_mono : ∀ {env₁ env₂ a b : VEnv} {cs}, env₁ ≤ env₂ →
    env₁.addConstList cs = some a → env₂.addConstList cs = some b → a ≤ b
  | _, _, _, _, [], H, h₁, h₂ => by cases h₁; cases h₂; exact H
  | _, _, _, _, _ :: _, H, h₁, h₂ => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at h₁ h₂
    obtain ⟨_, e₁, h₁⟩ := h₁; obtain ⟨_, e₂, h₂⟩ := h₂
    exact VEnv.addConstList_mono (VEnv.addConst_mono H e₁ e₂) h₁ h₂

theorem VEnv.addConstList_constants_none : ∀ {env e : VEnv} {cs : List (Name × VConstant)} {n},
    env.addConstList cs = some e → env.constants n = none → n ∉ cs.map (·.1) → e.constants n = none
  | _, _, [], _, h, hn, _ => by cases h; exact hn
  | env, _, (m, ci) :: cs, n, h, hn, hm => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at h hm
    obtain ⟨e₁, h1, h2⟩ := h
    refine VEnv.addConstList_constants_none h2 ?_ (by simpa using hm.2)
    rw [VEnv.addConst_constants_eq h1]; dsimp only; rw [if_neg (Ne.symm hm.1)]; exact hn

theorem VEnv.addConstList_constants_of_mem {env e : VEnv} :
    ∀ {cs : List (Name × VConstant)} {n ci}, env.addConstList cs = some e → (n, ci) ∈ cs →
    e.constants n = some ci
  | _ :: _, n, ci, h, hm => by
    simp only [VEnv.addConstList, List.foldlM_cons] at h
    obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases hm with
    | head =>
      refine (VEnv.addConstList_le h2).constants ?_
      rw [VEnv.addConst_constants_eq h1]; simp
    | tail _ hm => exact VEnv.addConstList_constants_of_mem h2 hm

theorem VEnv.exists_addConstList : ∀ {env : VEnv} {cs : List (Name × VConstant)},
    (∀ p ∈ cs, env.constants p.1 = none) → (cs.map (·.1)).Nodup →
    ∃ e, env.addConstList cs = some e
  | _, [], _, _ => ⟨_, rfl⟩
  | env, (n, ci) :: cs, hfr, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci) (hfr _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨e, h₂⟩ := VEnv.exists_addConstList (env := env₁) (cs := cs) (fun p hp => ?_) hnd.2
    · exact ⟨e, by simp [VEnv.addConstList, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]; dsimp only; rw [if_neg]; · exact hfr p (.tail _ hp)
      intro h; apply hnd.1; simp only at h ⊢; rw [h]; exact List.mem_map_of_mem hp

/-- If the bigger environment takes the constants, so does the smaller one. -/
theorem VEnv.addConstList_of_le : ∀ {env₁ env₂ b : VEnv} {cs : List (Name × VConstant)},
    env₁ ≤ env₂ → env₂.addConstList cs = some b → ∃ a, env₁.addConstList cs = some a ∧ a ≤ b
  | _, _, _, [], H, h => by cases h; exact ⟨_, rfl, H⟩
  | env₁, env₂, _, (n, ci) :: cs, H, h => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at h
    obtain ⟨e₂, h1, h2⟩ := h
    have hn : env₁.constants n = none := by
      unfold VEnv.addConst at h1; split at h1 <;> [cases h1; rename_i hn]
      cases h : env₁.constants n with
      | none => rfl
      | some _ => cases hn ▸ H.constants h
    obtain ⟨e₁, h1'⟩ := VEnv.addConst_eq_none (ci := ci) hn
    obtain ⟨a, ha, hle⟩ := VEnv.addConstList_of_le (VEnv.addConst_mono H h1' h1) h2
    exact ⟨a, by simp [VEnv.addConstList, h1']; exact ha, hle⟩

theorem VEnv.addDefEqList_mono : ∀ {dfs} {env₁ env₂ : VEnv}, env₁ ≤ env₂ →
    env₁.addDefEqList dfs ≤ env₂.addDefEqList dfs
  | [], _, _, H => H
  | df :: _, e₁, e₂, H =>
    show (e₁.addDefEq df).addDefEqList _ ≤ (e₂.addDefEq df).addDefEqList _ from
      VEnv.addDefEqList_mono (VEnv.addDefEq_mono H)

theorem VEnv.addInduct_mono {env₁ env₂ a b : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addInduct decl = some a) (h₂ : env₂.addInduct decl = some b) : a ≤ b := by
  simp [VEnv.addInduct, Option.bind_eq_some_iff] at h₁ h₂
  obtain ⟨_, t₁, _, c₁, _, r₁, b₁⟩ := h₁
  obtain ⟨_, t₂, _, c₂, _, r₂, b₂⟩ := h₂
  exact VEnv.addBlock_mono (VEnv.addDefEqList_mono <| VEnv.addConstList_mono
    (VEnv.addConstList_mono (VEnv.addConstList_mono H t₁ t₂) c₁ c₂) r₁ r₂) b₁ b₂

/-! ### The specification is monotone in the environment -/

section
variable {env env' : VEnv} (henv : env ≤ env') {decl : VInductDecl} {T : VInductiveType}
  {c : VConstructor} {f : VField} {Γ As Bs Ds : List VExpr} {fs : List VField} {U k : Nat}
include henv

theorem VEnv.TeleDefEq.mono (H : env.TeleDefEq U Γ As Bs) : env'.TeleDefEq U Γ As Bs := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.mono henv) ih

theorem VInductDecl.RecArgWF.mono (H : decl.RecArgWF env Γ k f) : decl.RecArgWF env' Γ k f := by
  unfold VInductDecl.RecArgWF at *
  cases h : f.recArg <;> simp only [h] at H ⊢
  obtain ⟨T, h1, h2, h3⟩ := H; exact ⟨T, h1, h2, h3.mono henv⟩

theorem VInductDecl.Positive.mono {t} (H : decl.Positive env Γ k t) : decl.Positive env' Γ k t := by
  induction H with
  | none h1 h2 => exact .none (h1.mono henv) h2
  | pi h1 h2 _ ih => exact .pi (h1.mono henv) h2 ih
  | app h1 h2 h3 h4 => exact .app h1 h2 (h3.mono henv) h4

theorem VInductDecl.FieldsWF.mono (H : decl.FieldsWF env Γ k Ds fs) :
    decl.FieldsWF env' Γ k Ds fs := by
  induction H with
  | nil => exact .nil
  | cons h1 h2 h3 h4 h5 h6 _ ih =>
    exact .cons (h1.mono henv) (h2.mono henv) h3
      (let ⟨u, a, b⟩ := h4; ⟨u, a.mono henv, b⟩) (fun h => (h5 h).mono henv) (h6.mono henv) ih

theorem VConstructor.WF.mono (H : c.WF env decl T) : c.WF env' decl T :=
  have ⟨ps, Ds, h1, h2, h3⟩ := H.shape
  ⟨H.type.mono henv, ⟨ps, Ds, h1, h2.mono henv, h3.mono henv⟩, H.indices,
    fun k f hf => (H.projFields k f hf).imp (·.mono henv) (·.mono henv)⟩

theorem VInductiveType.WF.mono (H : T.WF env decl) : T.WF env' decl :=
  ⟨H.indices.mono henv, H.defeq.mono henv⟩

theorem VInductDecl.WF.mono (H : decl.WF env) : decl.WF env' where
  nonempty := H.nonempty
  level := H.level
  params := H.params.mono henv
  types T hT := (H.types T hT).mono henv
  ctors _ hT' T hT :=
    let ⟨_, h, hle⟩ := VEnv.addConstList_of_le henv hT'
    ⟨(H.ctors _ h T hT).1.mono hle, fun c hc => ((H.ctors _ h T hT).2 c hc).mono hle⟩
  isRec := H.isRec
  largeElim := H.largeElim

end

theorem VEnv.WF.addConstList : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.WF → (∀ p ∈ cs, p.2.WF env) → env.addConstList cs = some env' → env'.WF
  | _, _, [], h, _, e => by cases e; exact h
  | env, _, (n, ci) :: cs, ⟨ds, h⟩, H, e => by
    simp only [VEnv.addConstList, List.foldlM_cons] at e
    obtain ⟨env₁, h1, h2⟩ := Option.bind_eq_some_iff.1 e
    have : env₁.WF := ⟨.axiom { ci with name := n } :: ds, .decl (.axiom (H _ (.head _)) h1) h⟩
    exact VEnv.WF.addConstList this
      (fun p hp => (H p (.tail _ hp)).mono (VEnv.addConst_le h1)) h2

end Lean4Lean

namespace Lean4Lean

/-- A type a well-formed environment records a block for is one of its constants. -/
theorem VEnv.WF.constants_of_inducts {env : VEnv} (henv : env.WF)
    (h : env.inducts n = some b) : ∃ ci, env.constants n = some ci := by
  obtain ⟨_, _, _, _, hT, hle, T, hT', rfl⟩ := henv.inducts h
  exact ⟨_, hle.constants <| VEnv.addConstList_constants_of_mem hT
    (List.mem_map.2 ⟨T, List.mem_of_getElem? hT', rfl⟩)⟩

/-- A block whose types have no block yet can be recorded. -/
theorem VEnv.exists_addBlock {env : VEnv} (h : ∀ T ∈ d.types, env.inducts T.name = none) :
    ∃ env', env.addBlock d = some env' := by
  unfold VEnv.addBlock; rw [if_pos (List.all_eq_true.2 fun T hT => by simp [h T hT])]; exact ⟨_, rfl⟩

end Lean4Lean

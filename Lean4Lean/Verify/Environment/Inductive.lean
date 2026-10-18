import Lean4Lean.Verify.Environment.AddInductive

/-!
# Adding an inductive block

`addInductive` is verified up to `addInductive.WF_flat`, which says that a run on a block
without nested occurrences takes an `AddInduct` step at the level the block is checked at. Here
that step is carried to every safety level, giving the `VEnvs` an `addDecl` needs.
-/

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

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
  obtain ⟨_, t₁, _, c₁, _, r₁, rfl⟩ := h₁
  obtain ⟨_, t₂, _, c₂, _, r₂, rfl⟩ := h₂
  exact VEnv.addDefEqList_mono <| VEnv.addDefEqList_mono <| VEnv.addConstList_mono
    (VEnv.addConstList_mono (VEnv.addConstList_mono H t₁ t₂) c₁ c₂) r₁ r₂

/-! ### The specification is monotone in the environment -/

section
variable {env env' : VEnv} (henv : env ≤ env') {decl : VInductDecl} {T : VInductiveType}
  {c : VConstructor} {f : VField} {Γ As Bs Ds : List VExpr} {fs : List VField} {U k : Nat}
include henv

theorem VEnv.IsTele.mono (H : env.IsTele U Γ As) : env'.IsTele U Γ As := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.mono henv) ih

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
  ⟨H.type.mono henv, ⟨ps, Ds, h1, h2.mono henv, h3.mono henv⟩, H.indices⟩

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

/-! ### Carrying the step to other safety levels -/

theorem List.Forall₂.map_eq {f : α → γ} {g : β → γ} :
    ∀ {l₁ l₂}, List.Forall₂ (fun a b => f a = g b) l₁ l₂ → l₁.map f = l₂.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by simp [h, map_eq t]

theorem List.Forall₂.append {R : α → β → Prop} :
    ∀ {l₁ l₂ l₃ l₄}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h t, h' => .cons h (append t h')

theorem TrRecVal.mono {env env' : VEnv} {decl : VInductDecl} {lparams : List Name} {i : Nat}
    {T : VInductiveType} {v : RecursorVal} (henv : env ≤ env')
    (H : TrRecVal decl lparams env i T v) : TrRecVal decl lparams env' i T v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := H
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    Lean4Lean.List.Forall₂.imp (fun _ _ ⟨a, b, c, d⟩ => ⟨a, b, c, d.mono henv⟩) h11⟩

/-- The names `AddInduct` inserts are those `VEnv.addInduct` adds constants under. -/
theorem AddInduct.names {decl : VInductDecl} (H : AddInduct safety C₁ env₁ decl C₂ env₂) :
    ∃ cis, C₂ = insertConsts C₁ cis ∧ (cis.map (·.name)).Nodup ∧
      (∀ ci ∈ cis, C₁.find? ci.name = none) ∧
      (∀ ci ∈ cis, ci.safety = if decl.isUnsafe then .unsafe else .safe) ∧
      cis.map (·.name) = (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1) := by
  obtain @⟨_, _, _, _, types, ctors, recs, -, hty, hct, hrc, hnd, hfr, rfl, -⟩ := H
  refine ⟨_, rfl, hnd, hfr, ?_, ?_⟩
  · intro ci hci
    simp only [inductConsts, List.mem_append, List.mem_map] at hci
    obtain (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩ := hci
    · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, h⟩, -⟩ := hty.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
    · obtain ⟨_, _, ⟨_, -, -, -, -, -, -, -, h⟩, -⟩ := hct.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
    · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, -, h, -⟩, -⟩ := hrc.forall_exists_l v hv
      simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
      cases decl.isUnsafe <;> rfl
  · refine List.Forall₂.map_eq (f := fun x : ConstantInfo => x.name)
      (g := fun x : Name × VConstant => x.1) ?_
    refine .append (.append ?_ ?_) ?_
    · simp only [VInductDecl.typeConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) hty
    · simp only [VInductDecl.ctorConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => h.1.choose_spec.2.2.1) hct
    · simp only [VInductDecl.recConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => h.1.1) hrc

/-- The step at a lower safety level, from a bigger environment that has room for the block. -/
theorem AddInduct.transport {decl : VInductDecl} (H : AddInduct sf C₁ env₁ decl C₂ env₂) (hsf : sf' ≤ sf)
    (hle : env₁ ≤ env₁') (hfr' : ∀ n, C₁.find? n = none → env₁'.constants n = none) :
    ∃ env₂', AddInduct sf' C₁ env₁' decl C₂ env₂' ∧ env₂ ≤ env₂' := by
  obtain ⟨cis, -, hnd, hfr, -, hnames⟩ := H.names
  rw [hnames, List.map_append, List.map_append] at hnd
  have hfresh : ∀ n ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1),
      env₁'.constants n = none := by
    rw [← hnames]; intro n hn
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    exact hfr' _ (hfr ci hci)
  simp only [List.map_append, List.mem_append] at hfresh
  obtain ⟨⟨hndT, hndC, hdTC⟩, hndR, hdR⟩ := List.nodup_append.1 hnd |>.imp_left List.nodup_append.1
  obtain @⟨lparams, envT, envC, envR, types, ctors, recs, hl, hty, hct, hrc, hnd₀, hfr₀, hm, hT, hC,
    hR, rfl⟩ := H
  obtain ⟨_, hT'⟩ := VEnv.exists_addConstList
    (fun p hp => hfresh _ (.inl (.inl (List.mem_map_of_mem hp)))) hndT
  obtain ⟨_, hC'⟩ := VEnv.exists_addConstList (fun p hp => VEnv.addConstList_constants_none hT'
      (hfresh _ (.inl (.inr (List.mem_map_of_mem hp))))
      fun h => hdTC _ h _ (List.mem_map_of_mem hp) rfl) hndC
  obtain ⟨_, hR'⟩ := VEnv.exists_addConstList (fun p hp => by
      have hp' := List.mem_map_of_mem (f := (·.1)) hp
      refine VEnv.addConstList_constants_none hC' (VEnv.addConstList_constants_none hT'
        (hfresh _ (.inr hp')) fun h => hdR _ (List.mem_append_left _ h) _ hp' rfl)
        fun h => hdR _ (List.mem_append_right _ h) _ hp' rfl) hndR
  have leT := VEnv.addConstList_mono hle hT hT'
  have leC := VEnv.addConstList_mono leT hC hC'
  have leR := VEnv.addConstList_mono leC hR hR'
  refine ⟨_, .mk hl ?_ ?_ ?_ hnd₀ hfr₀ hm hT' hC' hR' rfl,
    VEnv.addDefEqList_mono (VEnv.addDefEqList_mono leR)⟩
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, (h.2.sf_mono hsf).mono hle⟩) hty
  · exact Lean4Lean.List.Forall₂.imp (fun _ ⟨_, _⟩ h => ⟨h.1, (h.2.sf_mono hsf).mono leT⟩) hct
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ ⟨_, _⟩ h => ⟨h.1.mono leR, (h.2.sf_mono hsf).mono leC⟩) hrc

theorem TrEnv'.ignoreConsts : ∀ {cis : List ConstantInfo} {C},
    TrEnv' safety C Q venv → (cis.map (·.name)).Nodup → (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci ∈ cis, ¬safety ≤ ci.safety) → TrEnv' safety (insertConsts C cis) Q venv
  | [], _, H, _, _, _ => H
  | ci :: cis, C, H, hnd, hfr, hs => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine TrEnv'.ignoreConsts (cis := cis) (.ignore (hfr _ (.head _)) (hs _ (.head _)) H) hnd.2
      (fun c hc => ?_) (fun c hc => hs c (.tail _ hc))
    rw [H.map_wf.find?_insert, if_neg]; · exact hfr c (.tail _ hc)
    simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem hc)

theorem VEnv.HasPrimitives.addConstList {env e : VEnv} : ∀ {cs : List (Name × VConstant)},
    (∀ p ∈ cs, Environment.primitives.contains p.1 = false) →
    env.addConstList cs = some e → env.HasPrimitives → e.HasPrimitives
  | [], _, h, H => by cases h; exact H
  | _ :: _, hnp, h, H => by
    simp [VEnv.addConstList, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact addConstList (fun p hp => hnp p (.tail _ hp)) h2 (H.addConst (hnp _ (.head _)) h1)

theorem VEnv.HasPrimitives.addDefEqList : ∀ {dfs} {env : VEnv},
    env.HasPrimitives → (env.addDefEqList dfs).HasPrimitives
  | [], _, H => H
  | df :: _, env, H =>
    show ((env.addDefEq df).addDefEqList _).HasPrimitives from addDefEqList H.addDefEq

/-- A block none of whose names is a primitive keeps the primitive invariant. -/
theorem AddInduct.hasPrimitives {decl : VInductDecl}
    (hnp : ∀ n ∈ (decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts).map (·.1),
      Environment.primitives.contains n = false)
    (H : AddInduct safety C₁ env₁ decl C₂ env₂) (h : env₁.HasPrimitives) : env₂.HasPrimitives := by
  obtain ⟨-, -, -, -, -, -, -, hT, hC, hR, rfl⟩ := H
  have hnp' (cs : List (Name × VConstant)) (hcs : ∀ p ∈ cs, p ∈ decl.typeConsts ++ decl.ctorConsts ++ decl.recConsts) :
      ∀ p ∈ cs, Environment.primitives.contains p.1 = false :=
    fun p hp => hnp _ (List.mem_map_of_mem (hcs p hp))
  refine VEnv.HasPrimitives.addDefEqList <| VEnv.HasPrimitives.addDefEqList <|
    .addConstList (hnp' _ fun _ h => List.mem_append_right _ h) hR <|
    .addConstList (hnp' _ fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) hC <|
    .addConstList (hnp' _ fun _ h => List.mem_append_left _ (List.mem_append_left _ h)) hT h

/-- The level an inductive block is checked at, and the safety of every constant it adds. -/
abbrev inductSafety (isUnsafe : Bool) : DefinitionSafety := if isUnsafe then .unsafe else .safe

/-- An `AddInduct` step at the level the block is checked at gives one at every level. -/
theorem addInductBlock.WF {env env' : Environment} {ves : VEnvs} (wf : ves.WF env)
    {decl : VInductDecl} {venv' : VEnv}
    (hdecl : decl.WF (ves.venv (inductSafety decl.isUnsafe)))
    (H : AddInduct (inductSafety decl.isUnsafe) env.constants
      (ves.venv (inductSafety decl.isUnsafe)) decl env'.constants venv')
    (hq : env'.quotInit = env.quotInit)
    (hprim : ∀ safety venv₁ venv₂,
      AddInduct safety env.constants venv₁ decl env'.constants venv₂ →
      venv₁.HasPrimitives → venv₂.HasPrimitives)
    (hsafePrim : ∀ {n ci}, env'.find? n = some ci → Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hfr' (s) (n) (hn : env.constants.find? n = none) : (ves.venv s).constants n = none :=
    (wf.tr (safety := s)).constants_eq_none
      (by rwa [Kernel.Environment.find?, (wf.tr (safety := s)).map_wf.find?'_eq_find?])
  have hstep (s) : ∃ x, (s ≤ inductSafety decl.isUnsafe →
      AddInduct s env.constants (ves.venv s) decl env'.constants x) ∧
      (¬s ≤ inductSafety decl.isUnsafe → x = ves.venv s) := by
    by_cases hs : s ≤ inductSafety decl.isUnsafe
    · obtain ⟨x, h, -⟩ := H.transport hs (wf.mono hs) (hfr' s)
      exact ⟨x, fun _ => h, fun h => (h hs).elim⟩
    · exact ⟨_, fun h => (hs h).elim, fun _ => rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hstep
  obtain ⟨cis, hC', hnd, hfr, hsafe, -⟩ := H.names
  refine ⟨ves', {
    tr {s} := ?_
    hasPrimitives {s} := ?_
    safePrimitives := hsafePrim
    mono {s s'} hle := ?_ }, fun s => ?_⟩
  · show TrEnv' s env'.constants env'.quotInit _
    rw [hq]
    by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact .induct (hdecl.mono (wf.mono hs)) ((hves' s).1 hs) wf.tr
    · rw [(hves' s).2 hs, hC']
      exact (wf.tr (safety := s)).ignoreConsts hnd hfr fun ci hci h => hs (by rw [hsafe ci hci] at h; exact h)
  · by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact hprim s _ _ ((hves' s).1 hs) wf.hasPrimitives
    · rw [(hves' s).2 hs]; exact wf.hasPrimitives
  · by_cases hs' : s' ≤ inductSafety decl.isUnsafe
    · have hs := DefinitionSafety.le_trans hle hs'
      exact VEnv.addInduct_mono (wf.mono hle) ((hves' s').1 hs').to_addInduct
        ((hves' s).1 hs).to_addInduct
    · rw [(hves' s').2 hs']
      by_cases hs : s ≤ inductSafety decl.isUnsafe
      · exact (wf.mono hle).trans ((hves' s).1 hs).le
      · rw [(hves' s).2 hs]; exact wf.mono hle
  · by_cases hs : s ≤ inductSafety decl.isUnsafe
    · exact ((hves' s).1 hs).le
    · rw [(hves' s).2 hs]; exact VEnv.LE.rfl

/-- The block has no nested occurrences: eliminating them adds no auxiliary types. -/
def IsFlat (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (fuel : FuelConfig) : Prop :=
  ∀ res, (ElimNestedInductive.run fuel.inductiveFuel nparams types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
    res.aux2nested.size = 0

end Lean4Lean

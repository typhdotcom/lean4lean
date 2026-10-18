import Lean4Lean.Verify.Support.Monad
import Lean4Lean.Verify.Environment.Lemmas

/-!
# Declarations of a modelled environment mention no free variables

What `VEnvAt` records about the environment's own declarations, from its translation: their
expressions mention no free variables and only their own level parameters.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem Level.LParamsIn.of_ofLevel {Us : List Name} :
    ∀ {u : Level} {u'}, VLevel.ofLevel Us u = some u' → u.LParamsIn (· ∈ Us)
  | .zero, _, _ => trivial
  | .succ u, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h, -⟩ := h; exact Level.LParamsIn.of_ofLevel (u := u) h
  | .max a b, _, h | .imax a b, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, ha, _, hb, -⟩ := h
    exact ⟨Level.LParamsIn.of_ofLevel ha, Level.LParamsIn.of_ofLevel hb⟩
  | .param n, _, h => by
    simp only [VLevel.ofLevel] at h; split at h <;> cases h
    exact List.idxOf_lt_length_iff.1 ‹_›
  | .mvar _, _, h => by cases h

/-- The right-hand sides of a recursor's rules translate at its level parameters. -/
theorem TrEnv'.recRules {safety : DefinitionSafety} {C Q venv} (H : TrEnv' safety C Q venv)
    {name : Name} {v : RecursorVal} (h : C.find? name = some (.recInfo v))
    (hs : safety ≤ (ConstantInfo.recInfo v).safety) :
    ∀ r ∈ v.rules, ∃ e, TrExprS venv v.levelParams [] r.rhs e := by
  have {C : ConstMap} {n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some (ConstantInfo.recInfo v) →
      C.find? name = some (ConstantInfo.recInfo v) ∨ n = name ∧ ci' = ConstantInfo.recInfo v := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨-, h⟩ := this H.map_wf h
    · exact fun r hr => let ⟨e, he⟩ := ih h r hr; ⟨e, he.mono (VEnv.addConst_le h1)⟩
    · cases h
  | defn h2 h3 h4 h1 H ih =>
    obtain h | ⟨-, h⟩ := this H.map_wf h
    · exact fun r hr => let ⟨e, he⟩ := ih h r hr
        ⟨e, he.mono ((VEnv.addConst_le h1).trans VEnv.addDefEq_le)⟩
    · cases h
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, -, h⟩
    · exact fun r hr => let ⟨e, he⟩ := ih h r hr
        ⟨e, he.mono ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le)⟩
    · cases h
  | thm _ _ _ _ h1 H ih =>
    obtain h | ⟨-, h⟩ := this H.map_wf h
    · exact fun r hr => let ⟨e, he⟩ := ih h r hr; ⟨e, he.mono (VEnv.addConst_le h1)⟩
    · cases h
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨-, h⟩ := this H.map_wf h
    · exact fun r hr => let ⟨e, he⟩ := ih h r hr; ⟨e, he.mono (VEnv.addConst_le h1)⟩
    · cases h
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ (C : ConstMap) env, Aligned safety C env → P C env →
        C.find? name = some (ConstantInfo.recInfo v)) →
        ∀ (C : ConstMap) env, Aligned safety C env → AddQuot1 n k ci' P C env →
          C.find? name = some (ConstantInfo.recInfo v) by
      refine fun r hr => ?_
      obtain ⟨e, he⟩ := ih (this (this <| this <| this fun _ _ _ ⟨hC, _⟩ => hC ▸ h)
        _ _ H.aligned h1) r hr
      exact ⟨e, he.mono h1.le⟩
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨-, h⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · cases h
  | induct _ h1 H ih =>
    have hle := h1.le
    obtain ⟨-, -, -, hrecs, hnd, hfr, ⟨_, hp, rfl⟩, -, -, hR, hB⟩ := h1
    rcases insertConsts_find?_perm H.map_wf hfr hnd hp h with h' | ⟨hm, -⟩
    · exact fun r hr => let ⟨e, he⟩ := ih h' r hr; ⟨e, he.mono hle⟩
    · simp only [inductConsts, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨_, -, he⟩ | ⟨_, -, he⟩) | ⟨w, hw, he⟩
      · cases he
      · cases he
      cases he
      obtain ⟨⟨T, i⟩, -, htr, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrecs _ hw
      intro r hr
      obtain ⟨⟨T', j⟩, -, ⟨-, -, -, h3⟩⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_l htr.2.2.2.2.2.2.2.2.2.2.2 r hr
      exact ⟨_, h3.mono ((VEnv.addDefEqList_le).trans (VEnv.addBlock_le hB))⟩

theorem Literal.suppIn_true (l : Literal) : l.SuppIn fun _ => True := by
  cases l <;> simp [Literal.SuppIn]

/-- A translated expression mentions only the free variables of its context and the level
parameters it is translated at. -/
theorem TrExprS.suppIn_true {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') :
    e.SuppIn ⟨(· ∈ Δ.fvars), (· ∈ Us), fun _ => True⟩ := by
  induction H with
  | bvar => trivial
  | fvar h => exact VLCtx.find?_eq_some.1 ⟨_, h⟩
  | sort h => exact Level.LParamsIn.of_ofLevel h
  | const _ h =>
    refine ⟨trivial, fun u hu => ?_⟩
    obtain ⟨_, -, h'⟩ := Lean4Lean.List.Forall₂.forall_exists_l (List.mapM_eq_some.1 h) u hu
    exact Level.LParamsIn.of_ofLevel h'
  | app _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    exact ⟨ih1, Expr.SuppIn.mono ⟨fun _ h => by simpa using h, fun _ => id, fun _ => id⟩ ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    exact ⟨ih1, ih2, Expr.SuppIn.mono ⟨fun _ h => by simpa using h, fun _ => id, fun _ => id⟩ ih3⟩
  | lit => exact Literal.suppIn_true _
  | mdata _ ih => exact ih
  | proj _ _ ih => exact ih

theorem TrExprS.suppIn_nil {env : VEnv} {Us : List Name} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us [] e e') : e.SuppIn ⟨fun _ => False, (· ∈ Us), fun _ => True⟩ :=
  @Expr.SuppIn.mono ⟨(· ∈ VLCtx.fvars []), (· ∈ Us), fun _ => True⟩
    ⟨fun _ => False, (· ∈ Us), fun _ => True⟩
    ⟨fun _ h => by simp at h, fun _ => id, fun _ => id⟩ e H.suppIn_true

/-- The declarations of a translated environment mention no free variables, and only their own
level parameters. -/
theorem TrEnv'.suppIn_true {C Q venv} (H : TrEnv' .unsafe C Q venv) :
    ∀ n ci, C.find? n = some ci → ci.SuppIn fun _ => True := by
  have hS {Us e e'} (h : TrExprS venv Us [] e e') :
      e.SuppIn ⟨fun _ => False, (· ∈ Us), fun _ => True⟩ := h.suppIn_nil
  intro n ci h
  obtain ⟨_, -, htr⟩ := H.aligned.find? h DefinitionSafety.unsafe_le
  refine ⟨hS htr.2.2, ?_⟩
  cases ci with
  | defnInfo v | thmInfo v =>
    obtain ⟨_, he, -⟩ := H.of_value h DefinitionSafety.unsafe_le rfl
    exact hS he
  | inductInfo v => exact fun _ _ => trivial
  | ctorInfo v => trivial
  | recInfo v =>
    refine ⟨trivial, fun r hr => ?_⟩
    obtain ⟨e, he⟩ := H.recRules h DefinitionSafety.unsafe_le r hr
    exact hS he
  | _ => trivial

theorem TrEnv.suppIn_true {env : Environment} {venv : VEnv} (H : TrEnv .unsafe env venv) :
    ∀ n ci, env.find? n = some ci → ci.SuppIn fun _ => True := by
  intro n ci h
  rw [Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at h
  exact TrEnv'.suppIn_true H n ci h

end Lean4Lean

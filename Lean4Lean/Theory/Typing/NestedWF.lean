import Lean4Lean.Theory.Typing.NestedEnv

/-!
# The restored nested block is well formed

`RestoreSpec.wf`: the block a translated nested block restores to satisfies `VInductDecl.WF`,
given the translation's. Each clause about the translation carries over by `RestoreEnv`, from the
environment with the auxiliary types as constants to the one with the block's own types; what the
translation's terms are, syntactically, is the Verify side's to supply: where their auxiliary
constants sit (`VExpr.AuxAt`), and how a field's view relates to its declared domain.
-/

namespace Lean4Lean
open VExpr

namespace VExpr
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {ls₀ : List VLevel}

theorem AuxAt.foralls : ∀ {As : List VExpr} {B : VExpr} {k : Nat},
    (VExpr.foralls As B).AuxAt R ls₀ k →
    (∀ i (A : VExpr), As[i]? = some A → A.AuxAt R ls₀ (k + i)) ∧ B.AuxAt R ls₀ (k + As.length)
  | [], _, _, h => ⟨nofun, h⟩
  | A :: As, B, k, h => by
    obtain ⟨h1, h2⟩ := AuxAt.foralls (As := As) (B := B) (k := k + 1) h.2
    refine ⟨fun i A' hA' => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    cases i with
    | zero => cases hA'; exact h.1
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using h1 i A' hA'

theorem skips'_liftN_between : ∀ {e : VExpr} {k c j : Nat}, c ≤ j → j < c + k →
    (e.liftN k c).Skips' 1 j
  | .bvar i, k, c, j, h1, h2 => by
    simp only [liftN, Skips', liftVar]
    split <;> omega
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ => trivial
  | .app f a, _, _, _, h1, h2 => ⟨skips'_liftN_between (e := f) h1 h2, skips'_liftN_between (e := a) h1 h2⟩
  | .lam A b, _, _, _, h1, h2 | .forallE A b, _, _, _, h1, h2 =>
    ⟨skips'_liftN_between (e := A) h1 h2, skips'_liftN_between (e := b) (by omega) (by omega)⟩
  | .proj _ _ e, _, _, _, h1, h2 => skips'_liftN_between (e := e) h1 h2

theorem skips'_appN {f : VExpr} {j : Nat} : ∀ {xs : List VExpr},
    (VExpr.appN f xs).Skips' 1 j ↔ f.Skips' 1 j ∧ ∀ x ∈ xs, x.Skips' 1 j
  | [] => by simp [VExpr.appN]
  | x :: xs => by
    rw [VExpr.appN, skips'_appN]
    simp only [Skips', List.mem_cons, forall_eq_or_imp, and_assoc]

theorem bvars_skips' {n k j : Nat} (h : j < k) : ∀ x ∈ bvars n k, x.Skips' 1 j := by
  intro x hx
  simp only [bvars, List.mem_map, List.mem_reverse, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  simp only [Skips']; omega

/-- An auxiliary constant's occurrence at the parameters mentions only variables from `k` on. -/
theorem VAuxHead.inst_bvars_skips' {h : VAuxHead} (hcl : ∀ a ∈ h.args, a.ClosedN h.n)
    (ls : List VLevel) {k j : Nat} (hj : j < k) : (h.inst ls (bvars h.n k)).Skips' 1 j := by
  rw [VAuxHead.inst, skips'_appN]
  refine ⟨trivial, fun x hx => ?_⟩
  simp only [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have hcl' := (hcl a ha).instL (ls := ls)
  rw [hcl'.subst_congr (σ' := .ofLift (.consN (.skipN .refl k) 0)) fun i hi => by
    simp only [Subst.consList_bvars, if_pos hi]
    simp [Subst.ofLift, Lift.liftVar_skipN, Nat.add_comm]]
  rw [← liftN_eq_subst]
  exact skips'_liftN_between (Nat.zero_le _) (by omega)

/-- Restoring a term whose auxiliary constants sit at the parameters, `k` binders below, changes
none of its occurrences of the variables bound in between. -/
theorem AuxAt.restore_skips' (hcl : ∀ c h, R c = some h → ∀ a ∈ h.args, a.ClosedN h.n) :
    ∀ {e : VExpr} {k j : Nat}, e.AuxAt R ls₀ k → j < k →
      ((e.restore R ren).Skips' 1 j ↔ e.Skips' 1 j)
  | .bvar _, _, _, _, _ | .sort _, _, _, _, _ => .rfl
  | .const c ls, k, j, hA, hj => by
    simp only [restore]
    split
    · exact .rfl
    · unfold restoreAux
      simp only [constSpine?, Option.bind_some]
      cases hc : R c with
      | none => exact .rfl
      | some h =>
        simp only [AuxAt, hc] at hA
        simp only [Option.bind_some, List.length_nil, hA.1, if_true, Option.getD_some]
        have := VAuxHead.inst_bvars_skips' (hcl c h hc) ls (k := k) hj
        rw [show bvars h.n k = [] by simp [bvars, hA.1]] at this
        exact ⟨fun _ => trivial, fun _ => this⟩
  | .app f a, k, j, hA, hj => by
    have desc (hf : f.AuxAt R ls₀ k) (ha : a.AuxAt R ls₀ k)
        (hr : restoreAux R (.app f a) = none) :
        ((VExpr.app f a).restore R ren).Skips' 1 j ↔ (VExpr.app f a).Skips' 1 j := by
      simp only [restore, hr, Option.getD_none, Skips']
      rw [AuxAt.restore_skips' hcl hf hj, AuxAt.restore_skips' hcl ha hj]
    unfold AuxAt at hA
    cases hs : (VExpr.app f a).constSpine? with
    | none =>
      rw [hs] at hA
      exact desc hA.1 hA.2 (by simp [restoreAux, hs])
    | some p =>
      obtain ⟨c, ls, xs⟩ := p
      rw [hs] at hA
      cases hc : R c with
      | none =>
        simp only [hc] at hA
        exact desc hA.1 hA.2 (by simp [restoreAux, hs, hc])
      | some h =>
        simp only [hc] at hA
        split at hA
        · rename_i hl
          obtain ⟨rfl, -⟩ := hA
          have hr : restoreAux R (.app f a) = some (h.inst ls (bvars h.n k)) := by
            simp [restoreAux, hs, hc]
          simp only [restore, hr, Option.getD_some]
          refine ⟨fun _ => ?_, fun _ => VAuxHead.inst_bvars_skips' (hcl c h hc) ls hj⟩
          rw [eq_of_constSpine? hs, skips'_appN]
          exact ⟨trivial, bvars_skips' hj⟩
        · rename_i hl
          exact desc hA.1 hA.2 (by simp [restoreAux, hs, hc, hl])
  | .lam A b, k, j, hA, hj | .forallE A b, k, j, hA, hj => by
    simp only [restore, Skips']
    rw [AuxAt.restore_skips' hcl hA.1 hj, AuxAt.restore_skips' hcl hA.2 (by omega)]
  | .proj _ _ e, k, j, hA, hj => by
    simp only [restore, Skips']
    exact AuxAt.restore_skips' (e := e) hcl hA hj

theorem AuxAt.restore_skips (hcl : ∀ c h, R c = some h → ∀ a ∈ h.args, a.ClosedN h.n)
    {e : VExpr} {k j : Nat} (hA : e.AuxAt R ls₀ k) (hj : j < k) :
    (e.restore R ren).Skips 1 j ↔ e.Skips 1 j := by
  rw [skips_iff, skips_iff]; exact AuxAt.restore_skips' hcl hA hj

/-- A substitution that keeps the parameters, `np` variables from `k` on, at `k'` and puts no
auxiliary constant anywhere keeps the auxiliary constants at the parameters. -/
theorem AuxAt.subst {np : Nat} (hnp : ∀ c h, R c = some h → h.n = np) :
    ∀ {e : VExpr} {σ : Subst} {k k' : Nat}, (∀ i, (σ i).ConstsSat (R · = none)) →
      (∀ i < np, σ (i + k) = .bvar (i + k')) → e.AuxAt R ls₀ k → (e.subst σ).AuxAt R ls₀ k'
  | .bvar i, σ, _, _, hσ, _, _ => AuxAt.of_constsSat (hσ i)
  | .sort _, _, _, _, _, _, _ => trivial
  | .const .., _, _, _, _, _, h => h
  | .app f a, σ, k, k', hσ, hp, hA => by
    have desc (hf : f.AuxAt R ls₀ k) (ha : a.AuxAt R ls₀ k) :
        ((VExpr.app f a).subst σ).AuxAt R ls₀ k' :=
      AuxAt.app' (AuxAt.subst hnp hσ hp hf) (AuxAt.subst hnp hσ hp ha)
    unfold AuxAt at hA
    cases hs : (VExpr.app f a).constSpine? with
    | none =>
      rw [hs] at hA
      exact desc hA.1 hA.2
    | some p =>
      obtain ⟨c, ls, xs⟩ := p
      rw [hs] at hA
      cases hc : R c with
      | none =>
        simp only [hc] at hA
        exact desc hA.1 hA.2
      | some h =>
        simp only [hc] at hA
        split at hA
        · rename_i hl
          obtain ⟨rfl, hls⟩ := hA
          subst hls
          have hs' := constSpine?_subst_some (σ := σ) hs
          have hb : (bvars h.n k).map (·.subst σ) = bvars h.n k' := by
            simp only [bvars, List.map_map, Function.comp_def, VExpr.subst_bvar]
            refine List.map_congr_left fun i hi => ?_
            simp only [List.mem_reverse, List.mem_range] at hi
            exact hp i (hnp c h hc ▸ hi)
          rw [hb] at hs'
          rw [eq_of_constSpine? hs'] at ⊢
          have := AuxAt.appN_aux (ls₀ := ls) (k := k') hc (ys := []) nofun
          simpa using this
        · exact desc hA.1 hA.2
  | .lam A b, σ, k, k', hσ, hp, hA | .forallE A b, σ, k, k', hσ, hp, hA => by
    have hσ' : ∀ i, (σ.lift i).ConstsSat (R · = none) := by
      intro i; cases i with
      | zero => trivial
      | succ i => exact (hσ i).liftN
    have hp' : ∀ i < np, σ.lift (i + (k + 1)) = .bvar (i + (k' + 1)) := by
      intro i hi
      rw [show i + (k + 1) = (i + k) + 1 by omega]
      simp [Subst.lift, hp i hi, VExpr.lift, liftN, liftVar]; omega
    exact ⟨AuxAt.subst hnp hσ hp hA.1, AuxAt.subst hnp hσ' hp' hA.2⟩
  | .proj _ _ e, σ, _, _, hσ, hp, hA => AuxAt.subst (e := e) hnp hσ hp hA

end VExpr

theorem Lift.inv_constsSat {p : Name → Prop} : ∀ (ρ : Lift) (i : Nat), (ρ.inv i).ConstsSat p
  | .refl, _ => trivial
  | .skip _, 0 => trivial
  | .skip ρ, i + 1 => Lift.inv_constsSat ρ i
  | .cons _, 0 => trivial
  | .cons ρ, i + 1 => (Lift.inv_constsSat ρ i).liftN

namespace VConstructor
open Classical
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {ls₀ : List VLevel}
  {cname : Name → Name} (c : VConstructor)

theorem restore_fields_getElem? (i : Nat) :
    (c.restore R ren cname).fields[i]? = c.fields[i]?.map (·.restore R ren) := by
  simp [VConstructor.restore]

theorem strippedTypeBy_restore (P : Nat → Prop) (i : Nat) (A : VExpr) :
    (strippedTypeBy P i A).restore R ren = strippedTypeBy P i (A.restore R ren) :=
  VExpr.restore_subst fun _ => Lift.inv_constsSat _ _

theorem keptFieldsBy_restore (P : Nat → Prop) (k : Nat) :
    (c.restore R ren cname).keptFieldsBy P k = (c.keptFieldsBy P k).map (·.restore R ren) := by
  simp only [keptFieldsBy_eq, List.map_map, Function.comp_def, restore_fields_getElem?]
  refine List.map_congr_left fun j _ => ?_
  rw [strippedTypeBy_restore]
  cases c.fields[j]? <;> rfl

variable (hF : ∀ i (f : VField), c.fields[i]? = some f → f.type.AuxAt R ls₀ i)
  (hcl : ∀ c h, R c = some h → ∀ a ∈ h.args, a.ClosedN h.n)
include hF hcl

theorem restore_unused (k j : Nat) : (c.restore R ren cname).Unused k j ↔ c.Unused k j := by
  simp only [Unused, restore_fields_getElem?]
  refine forall_congr' fun i => ⟨fun H f hj hi hf => ?_, fun H f' hj hi hf' => ?_⟩
  · have := H (f.restore R ren) hj hi (by rw [hf]; rfl)
    exact (VExpr.AuxAt.restore_skips hcl (hF i f hf) (by omega)).1 this
  · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hf'
    exact (VExpr.AuxAt.restore_skips hcl (hF i f hf) (by omega)).2 (H f hj hi hf)

theorem restore_skipped (k : Nat) : (c.restore R ren cname).Skipped k = c.Skipped k := by
  funext j; simp only [Skipped, restore_unused c hF hcl]

theorem restore_keptFields (k : Nat) :
    (c.restore R ren cname).keptFields k = (c.keptFields k).map (·.restore R ren) := by
  rw [keptFields, keptFields, restore_skipped c hF hcl, keptFieldsBy_restore]

theorem restore_strippedType (k i : Nat) (A : VExpr) :
    (c.restore R ren cname).strippedType k i (A.restore R ren) =
      (c.strippedType k i A).restore R ren := by
  rw [strippedType, strippedType, restore_skipped c hF hcl, strippedTypeBy_restore]

end VConstructor

namespace VConstructor
open Classical
variable {R : Name → Option VAuxHead} {ls₀ : List VLevel}

/-- The lift that keeps the fields that are not `P` sends the parameters, above the fields before
the `i`th, to the parameters above the kept ones. -/
theorem keptLiftBy_inv_params (P : Nat → Prop) : ∀ (i p : Nat),
    (keptLiftBy P i).inv (p + i) = .bvar (p + (keptIdxBy P i).length)
  | 0, p => by simp [keptLiftBy, keptIdxBy, Lift.inv, Subst.id]
  | i + 1, p => by
    rw [keptLiftBy_succ, keptIdxBy_succ, show p + (i + 1) = (p + i) + 1 by omega]
    by_cases hP : P i
    · simp only [if_pos hP, Lift.inv, Subst.cons, List.append_nil]
      exact keptLiftBy_inv_params P i p
    · simp only [if_neg hP, Lift.inv, Subst.lift, List.length_append, List.length_singleton]
      rw [keptLiftBy_inv_params P i p]
      simp only [VExpr.lift, liftN, liftVar, Nat.not_lt_zero, if_false]
      congr 1; omega

theorem strippedTypeBy_auxAt {np : Nat} (hnp : ∀ c h, R c = some h → h.n = np) (P : Nat → Prop)
    {i : Nat} {A : VExpr} (hA : A.AuxAt R ls₀ i) :
    (strippedTypeBy P i A).AuxAt R ls₀ (keptIdxBy P i).length :=
  VExpr.AuxAt.subst hnp (fun _ => Lift.inv_constsSat _ _)
    (fun p _ => keptLiftBy_inv_params P i p) hA

/-- The kept fields, as a context above the parameters, have their auxiliary constants at the
parameters. -/
theorem keptFieldsBy_ctxAuxAt (c : VConstructor) {np : Nat}
    (hnp : ∀ c h, R c = some h → h.n = np) (P : Nat → Prop)
    (hF : ∀ i (f : VField), c.fields[i]? = some f → f.type.AuxAt R ls₀ i) :
    ∀ k, VExpr.CtxAuxAt R ls₀ (c.keptFieldsBy P k).reverse ∧
      (c.keptFieldsBy P k).length = (keptIdxBy P k).length
  | 0 => by simp [keptFieldsBy_eq, keptIdxBy, VExpr.CtxAuxAt]
  | k + 1 => by
    obtain ⟨ih, hl⟩ := keptFieldsBy_ctxAuxAt c hnp P hF k
    rw [keptFieldsBy_eq] at ih hl ⊢
    rw [keptIdxBy_succ]
    by_cases hP : P k
    · rw [if_pos hP, List.append_nil]; exact ⟨ih, hl⟩
    · simp only [if_neg hP, List.map_append, List.map_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.length_append,
        List.length_singleton, VExpr.CtxAuxAt]
      refine ⟨⟨?_, ih⟩, by rw [hl]⟩
      rw [List.length_reverse, hl]
      cases hf : c.fields[k]? with
      | none => trivial
      | some f => exact strippedTypeBy_auxAt hnp P (hF k f hf)

end VConstructor

namespace VExpr
variable {R : Name → Option VAuxHead} {ls₀ : List VLevel}

theorem AuxAt.foralls_intro : ∀ {As : List VExpr} {B : VExpr} {k : Nat},
    (∀ i (A : VExpr), As[i]? = some A → A.AuxAt R ls₀ (k + i)) →
    B.AuxAt R ls₀ (k + As.length) → (VExpr.foralls As B).AuxAt R ls₀ k
  | [], _, _, _, h => h
  | A :: As, B, k, hA, hB =>
    ⟨by simpa using hA 0 A rfl, AuxAt.foralls_intro (k := k + 1)
      (fun i A' h => by simpa [Nat.add_assoc, Nat.add_comm 1] using hA (i + 1) A' h)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hB)⟩

end VExpr

/-- Where a field's terms have their auxiliary constants, `k` fields above the parameters: its
type at `k`, and its recursive view's binders and indices above it. -/
def VField.AuxAt (R : Name → Option VAuxHead) (ls₀ : List VLevel) (k : Nat) (f : VField) : Prop :=
  f.type.AuxAt R ls₀ k ∧ ∀ ra, f.recArg = some ra →
    (∀ i (b : VExpr), ra.binders[i]? = some b → b.AuxAt R ls₀ (k + i)) ∧
    ∀ x ∈ ra.indices, x.AuxAt R ls₀ (k + ra.binders.length)

theorem VExpr.ConstsSat.foralls {p : Name → Prop} : ∀ {As : List VExpr} {B : VExpr},
    (VExpr.foralls As B).ConstsSat p ↔ (∀ A ∈ As, A.ConstsSat p) ∧ B.ConstsSat p
  | [], _ => by simp
  | A :: As, B => by
    simp only [VExpr.foralls, VExpr.ConstsSat, List.mem_cons, forall_eq_or_imp]
    rw [VExpr.ConstsSat.foralls, and_assoc]

/-- A recursive field's view has no auxiliary constant at all, where the auxiliary types are among
the block's own and the auxiliary constructors are not constants of the environment: the view
mentions none of the block's types, and is typed. -/
theorem VInductDecl.RecArgWF.auxAt {R : Name → Option VAuxHead} {d : VInductDecl} {E₁ : VEnv}
    (hE : E₁.Ordered) {Γ : List VExpr} {k : Nat} {f : VField}
    (hΓ : OnCtx Γ (E₁.IsType d.uvars))
    (hdom : ∀ c h, R c = some h → c ∈ d.names ∨ E₁.constants c = none)
    (hnone : ∀ T ∈ d.allTypes, T.nested = none) (H : d.RecArgWF E₁ Γ k f) (ls₀ : List VLevel) :
    ∀ ra, f.recArg = some ra →
      (∀ i (b : VExpr), ra.binders[i]? = some b → b.AuxAt R ls₀ (k + i)) ∧
      ∀ x ∈ ra.indices, x.AuxAt R ls₀ (k + ra.binders.length) := by
  intro ra hra
  unfold VInductDecl.RecArgWF at H
  rw [hra] at H
  obtain ⟨T, hT, -, ⟨_, hdef⟩, hbm, him⟩ := H
  have hcs := (VEnv.IsDefEq.constsSat hE hdef (VEnv.OnCtx.constsSat hE hΓ)).2.1
  rw [VExpr.ConstsSat.foralls, VInductiveType.typeApp_of_none
    (hnone T (List.mem_of_getElem? hT)), ConstsSat.appN] at hcs
  obtain ⟨hcb, -, hcis⟩ := hcs
  have hfree {b : VExpr} (h1 : b.ConstsSat (E₁.constants · |>.isSome))
      (h2 : b.mentions d.names = false) : b.ConstsSat (R · = none) :=
    (h1.and (VExpr.constsSat_of_mentions h2)).mono fun c ⟨h1, h2⟩ => by
      cases hR : R c with
      | none => rfl
      | some h =>
        rcases hdom c h hR with h' | h'
        · exact absurd h' h2
        · simp [h'] at h1
  refine ⟨fun i b hb => VExpr.AuxAt.of_constsSat (hfree (hcb b (List.mem_of_getElem? hb))
    (by simpa using List.all_eq_true.1 hbm b (List.mem_of_getElem? hb))), fun x hx =>
    VExpr.AuxAt.of_constsSat (hfree (hcis x (List.mem_append_right _ hx))
      (by simpa using List.all_eq_true.1 him x hx))⟩

namespace VInductDecl
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name} {E₁ E₀ : VEnv} {F : Name → Option VExpr}

/-- A type of the translation, at the parameters, has its auxiliary constant there. -/
theorem RestoreSpec.typeApp_auxAt (H : d.RestoreSpec R ren n ns cname) {j : Nat} {T}
    (hj : d.types[j]? = some T) {ls : List VLevel} {k : Nat} {idx : List VExpr}
    (hidx : ∀ x ∈ idx, x.AuxAt R ls k) :
    (T.typeApp ls (bvars d.params.length k) idx).AuxAt R ls k := by
  rw [VInductiveType.typeApp_of_none (H.nested T (List.mem_of_getElem? hj))]
  by_cases hn : j < n
  · obtain ⟨hR, -, -⟩ := H.own j T hn hj
    have hc : (VExpr.const T.name ls).AuxAt R ls k := by simp [VExpr.AuxAt, hR]
    refine VExpr.AuxAt.appN' hc fun y hy => ?_
    rcases List.mem_append.1 hy with hy | hy
    · simp [bvars] at hy; obtain ⟨_, _, rfl⟩ := hy; trivial
    · exact hidx y hy
  · obtain ⟨o, -, -, hR, -, -⟩ := H.nestedAt_aux hj (by omega)
    exact VExpr.AuxAt.appN_aux hR hidx

variable (hE₁ : E₁.WF) (hrenE₁ : ∀ c c', ren c = some c' → E₁.constants c = none)
include hE₁ hrenE₁

/-- What a judgment of `E₁` mentions is not renamed. -/
theorem renFree {U : Nat} {Γ : List VExpr} {e e' A : VExpr} (hΓ : OnCtx Γ (E₁.IsType U))
    (h : E₁.IsDefEq U Γ e e' A) :
    e.ConstsSat (ren · = none) ∧ e'.ConstsSat (ren · = none) ∧ A.ConstsSat (ren · = none) := by
  have := VEnv.IsDefEq.constsSat hE₁.ordered h (VEnv.OnCtx.constsSat hE₁.ordered hΓ)
  have hm : ∀ c, (E₁.constants c).isSome = true → ren c = none := by
    intro c hc
    cases hr : ren c with
    | none => rfl
    | some _ => rw [hrenE₁ c _ hr] at hc; cases hc
  exact ⟨this.1.mono hm, this.2.1.mono hm, this.2.2.mono hm⟩

theorem restore_ren_ctx {U : Nat} {Γ₀ : List VExpr} :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₀) (E₁.IsType U) →
      Δ.map (·.restore R ren) = Δ.map (·.restore R fun _ => none)
  | [], _ => rfl
  | A :: Δ, ⟨hΓ, _, hA⟩ => by
    simp only [List.map_cons, restore_ren_ctx (Δ := Δ) hΓ,
      VExpr.restore_ren_none (renFree hE₁ hrenE₁ hΓ hA).1]

variable (H : d.RestoreSpec R ren n ns cname)
  (HE : RestoreEnv E₁ E₀ d.uvars F R (VLevel.params d.uvars) d.params.reverse)
include H HE

/-- The conditions on a constructor's fields carry over to the restored block. -/
theorem RestoreSpec.fieldsWF (hdom : ∀ c, F c ≠ none ∨ R c ≠ none ∨ ren c ≠ none →
      c ∈ d.names ∨ E₁.constants c = none) :
    ∀ {Δ : List VExpr} {k : Nat} {Ds : List VExpr} {fs : List VField}, k = Δ.length →
      d.FieldsWF E₁ (Δ ++ d.params.reverse) k Ds fs →
      OnCtx (Δ ++ d.params.reverse) (E₁.IsType d.uvars) →
      VExpr.CtxAuxAt R (VLevel.params d.uvars) Δ →
      (∀ i (D : VExpr), Ds[i]? = some D → D.AuxAt R (VLevel.params d.uvars) (k + i)) →
      (∀ i (f : VField), fs[i]? = some f → f.AuxAt R (VLevel.params d.uvars) (k + i)) →
      (d.restoreNested R ren n ns cname).FieldsWF E₀
        (Δ.map (·.restore R ren) ++ d.params.reverse) k (Ds.map (·.restore R ren))
        (fs.map (·.restore R ren)) := by
  intro Δ k Ds fs hk hW hΓ hΔ hD hf
  generalize hG : Δ ++ d.params.reverse = G at hW
  induction hW generalizing Δ with
  | nil => exact .nil
  | @cons Γ' D k' f Ds' fs' h1 h2 h3 h4 h5 h6 _ ih =>
    subst hk hG
    have hO := hE₁.ordered
    have hD0 : D.AuxAt R (VLevel.params d.uvars) Δ.length := by simpa using hD 0 D rfl
    obtain ⟨hf0, hfra⟩ : f.AuxAt R (VLevel.params d.uvars) Δ.length := by simpa using hf 0 f rfl
    have hctx := restore_ren_ctx (R := R) hE₁ hrenE₁ hΓ
    have rf {e A : VExpr} (h : E₁.HasType d.uvars (Δ ++ d.params.reverse) e A) :
        e.restore R ren = e.restore R fun _ => none :=
      VExpr.restore_ren_none (renFree hE₁ hrenE₁ hΓ h).1
    have hfr := rf h2
    have hDr : D.restore R ren = D.restore R fun _ => none := by
      obtain ⟨_, h1'⟩ := h1; exact VExpr.restore_ren_none (renFree hE₁ hrenE₁ hΓ h1').1
    refine .cons ?_ ?_ h3 ?_ ?_ ?_ ?_
    · have := HE.isDefEqU hΓ hΔ hD0 hf0 h1
      rwa [← hctx, ← hDr, ← hfr] at this
    · have := HE.hasType (A := .sort f.level) hΓ hΔ hf0 trivial h2
      rwa [← hctx, ← hfr] at this
    · obtain ⟨u, hu, hle⟩ := h4
      have := HE.hasType (A := .sort u) hΓ hΔ hf0 trivial hu
      exact ⟨u, by rwa [← hctx, ← hfr] at this, hle⟩
    · intro hun
      have hP := H.positive HE hO hdom rfl (h5 hun) hΓ
      have hΓ0 := HE.onCtx hΓ
      have hW : VExpr.WF E₀ d.uvars (Δ.map (·.replaceConst F) ++ d.params.reverse)
          (f.type.replaceConst F) := by
        have := h2.replaceConst HE.wf.ordered HE.subst
        rw [HE.replaceConst_ctx] at this
        exact ⟨_, this⟩
      have hd := HE.defeq hΓ0 (by simpa using hf0) hW
      have hP' := Positive.defeqU (d := d.restoreNested R ren n ns cname) HE.wf hΓ0 hd hP
      have hP'' := Positive.defeqDFC (d := d.restoreNested R ren n ns cname) HE.wf.ordered
        (HE.ctx_defeq hΓ hΔ).2 hP'
      rwa [← hctx, ← hfr] at hP''
    · unfold RecArgWF at h6 ⊢
      simp only [VField.restore_recArg]
      cases hra : f.recArg with
      | none => trivial
      | some ra =>
        rw [hra] at h6
        obtain ⟨hb, hi⟩ := hfra ra hra
        obtain ⟨T, hT, hTl, hdef, hbm, him⟩ := h6
        rw [allTypes_of_aux H.flat] at hT
        -- the view's binders and indices mention no constant restoring changes
        have hfree : ∀ b : VExpr, b.ConstsSat (E₁.constants · |>.isSome) →
            b.mentions d.names = false →
            (b.restore R ren).mentions (d.restoreNested R ren n ns cname).names = false := by
          intro b hb' hm
          rw [VExpr.restore_of_constsSat ((hb'.and (VExpr.constsSat_of_mentions hm)).mono
            fun c ⟨h1, h2⟩ => ⟨?_, ?_⟩)]
          · exact VExpr.mentions_mono restoreNested_names_sub hm
          · cases hR : R c with
            | none => rfl
            | some _ =>
              rcases hdom c (.inr (.inl (by simp [hR]))) with h | h
              · exact absurd h h2
              · simp [h] at h1
          · cases hr : ren c with
            | none => rfl
            | some _ =>
              rcases hdom c (.inr (.inr (by simp [hr]))) with h | h
              · exact absurd h h2
              · simp [h] at h1
        obtain ⟨_, hdef₀⟩ := id hdef
        have hcs := (VEnv.IsDefEq.constsSat hO hdef₀ (VEnv.OnCtx.constsSat hO hΓ)).2.1
        rw [VExpr.ConstsSat.foralls, VInductiveType.typeApp_of_none
          (H.nested T (List.mem_of_getElem? hT)), ConstsSat.appN] at hcs
        obtain ⟨hcb, -, hcis⟩ := hcs
        refine ⟨T.restore R ren cname (nestedAt n ns ra.typeIdx), ?_, ?_, ?_, ?_, ?_⟩
        · rw [restoreNested_allTypes_getElem? H]
          simp only [VRecArg.restore, allTypes_of_aux H.flat, hT, Option.map_some]
        · simp [VRecArg.restore, VInductiveType.restore, hTl]
        · have hX : (VExpr.foralls ra.binders (T.typeApp (VLevel.params d.uvars)
              (bvars d.params.length (Δ.length + ra.binders.length)) ra.indices)).AuxAt R
              (VLevel.params d.uvars) Δ.length :=
            VExpr.AuxAt.foralls_intro hb (H.typeApp_auxAt hT hi)
          have := HE.isDefEqU hΓ hΔ hf0 hX hdef
          obtain ⟨_, hdef'⟩ := hdef
          rw [← hctx, ← hfr, ← VExpr.restore_ren_none (renFree hE₁ hrenE₁ hΓ hdef').2.1,
            VExpr.restore_foralls, H.restore_typeApp hT _ (by simp) (VExpr.restore_bvars ..)]
            at this
          rw [restoreNested_params_length]
          dsimp only [VRecArg.restore, VField.restore]
          rw [List.length_map]
          exact this
        · simp only [VRecArg.restore, List.all_map, List.all_eq_true, Function.comp_apply,
            Bool.not_eq_eq_eq_not, Bool.not_true]
          intro b hb'
          exact hfree b (hcb b hb') (by simpa using List.all_eq_true.1 hbm b hb')
        · simp only [VRecArg.restore, List.all_map, List.all_eq_true, Function.comp_apply,
            Bool.not_eq_eq_eq_not, Bool.not_true]
          intro b hb'
          exact hfree b (hcis b (List.mem_append_right _ hb'))
            (by simpa using List.all_eq_true.1 him b hb')
    · have := ih (Δ := f.type :: Δ) rfl ⟨hΓ, _, h2⟩ ⟨by simpa using hf0, hΔ⟩
        (fun i D' h => by simpa [Nat.add_assoc, Nat.add_comm 1] using hD (i + 1) D' h)
        (fun i f' h => by simpa [Nat.add_assoc, Nat.add_comm 1] using hf (i + 1) f' h) rfl
      exact this

end VInductDecl

theorem VEnv.IsTele.teleDefEq_self {env : VEnv} {U : Nat} :
    ∀ {Γ As : List VExpr}, env.IsTele U Γ As → env.TeleDefEq U Γ As As
  | _, [], .nil => .nil
  | _, _ :: _, .cons ⟨_, hA⟩ t => .cons ⟨_, hA⟩ t.teleDefEq_self

/-- Restoring keeps a declared domain's relation to the type the kernel reads off it, where the
annotations are neither auxiliary nor renamed. -/
theorem VExpr.StripsToBy.restore {R : Name → Option VAuxHead} {ren : Name → Option Name}
    {e e' : VExpr} (H : e.StripsToBy (fun c => R c = none ∧ ren c = none) e') :
    (e.restore R ren).StripsTo (e'.restore R ren) := by
  induction H with
  | refl => exact .refl
  | @app2 A _ ls v c hc hR _ ih =>
    obtain ⟨h1, h2⟩ := hR
    have : (VExpr.app (.app (.const c ls) A) v).restore R ren =
        .app (.app (.const c ls) (A.restore R ren)) (v.restore R ren) := by
      simp [VExpr.restore, VExpr.restoreAux, VExpr.constSpine?, h1, h2]
    rw [this]; exact .app2 hc ih
  | @app1 A _ ls c hc hR _ ih =>
    obtain ⟨h1, h2⟩ := hR
    have : (VExpr.app (.const c ls) A).restore R ren = .app (.const c ls) (A.restore R ren) := by
      simp [VExpr.restore, VExpr.restoreAux, VExpr.constSpine?, h1, h2]
    rw [this]; exact .app1 hc ih

/-- What the restoration needs to know of a constructor of the translated block `d`, beyond its
check: its declared type's parameter binders mention no auxiliary or renamed constant and its body
has its auxiliary constants at the parameters; so do its fields; its indices mention no auxiliary
constant other than the block's types; and each field's view is its declared domain with
annotations stripped that are neither auxiliary nor renamed, so it mentions no parameter the
domain does not, once both are restored. -/
structure VConstructor.RestoreFacts (R : Name → Option VAuxHead) (ren : Name → Option Name)
    (d : VInductDecl) (c : VConstructor) : Prop where
  shape : ∃ ps B, c.type = .foralls ps B ∧ ps.length = d.params.length ∧
    (∀ p ∈ ps, p.ConstsSat fun x => R x = none ∧ ren x = none) ∧
    B.AuxAt R (VLevel.params d.uvars) 0
  fields : ∀ k (f : VField), c.fields[k]? = some f → f.AuxAt R (VLevel.params d.uvars) k
  indices : ∀ x ∈ c.indices, x.ConstsSat fun y => R y ≠ none ∨ ren y ≠ none → y ∈ d.names
  strips : ∀ ps Ds B, c.type = .foralls (ps ++ Ds) B → ps.length = d.params.length →
    ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      D.StripsToBy (fun c => R c = none ∧ ren c = none) f.type

namespace VInductDecl
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name} {venv E₁ : VEnv}

/-- The block a translated nested block restores to is well formed, given the translation's check
and what the restoration needs to know of its terms. -/
theorem RestoreSpec.wf (henv : venv.WF) (H : d.RestoreSpec R ren n ns cname) (hd : d.WF venv)
    (hn : 0 < n)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none)
    (hRdom : ∀ c h, R c = some h → ∃ k T, d.types[n + k]? = some T ∧
      (c = T.name ∨ ∃ c' ∈ T.ctors, c = c'.name))
    (hrenNames : ∀ c c', ren c = some c' → c ∉ d.names)
    (hctorNames : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.name ∉ d.names)
    (hE₁ : venv.addConstList d.typeConsts = some E₁)
    (hIdx : ∀ T ∈ d.types, ∀ x ∈ T.indices, x.mentions d.names = false)
    (hAux : ∀ T ∈ (d.restoreNested R ren n ns cname).aux, ∃ o, T.nested = some o ∧
      ∀ env', venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some env' →
        T.AuxWF env' (d.restoreNested R ren n ns cname) o)
    (hCtor : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.RestoreFacts R ren d) :
    (d.restoreNested R ren n ns cname).WF venv := by
  have hO := henv.ordered
  have hfr {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) :
      e.ConstsSat fun c => R c = none ∧ ren c = none :=
    he.mono fun c hc => by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      refine ⟨?_, ?_⟩
      · cases h : R c with
        | none => rfl
        | some _ => rw [hRfresh c _ h] at hci; cases hci
      · cases h : ren c with
        | none => rfl
        | some _ => rw [hrenfresh c _ h] at hci; cases hci
  have hPC := VEnv.IsTele.constsSat hO hd.params trivial
  have hparams : (d.restoreNested R ren n ns cname).params = d.params := by
    simp only [restoreNested]
    exact (List.map_congr_left fun P hP' => restore_of_constsSat (hfr (hPC P hP'))).trans
      (List.map_id' _)
  have hTC {T} (hT : T ∈ d.types) : T.type.ConstsSat (venv.constants · |>.isSome) := by
    obtain ⟨_, h⟩ := (hd.types T hT).1; exact (h.constsSat hO trivial).1
  have hTrestore {T : VInductiveType} (hT : T ∈ d.types) : T.type.restore R ren = T.type :=
    restore_of_constsSat (hfr (hTC hT))
  have hE₁wf : E₁.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hd.types T hT).1) hE₁
  have hle₁ := VEnv.addConstList_le hE₁
  have hdeclT := hd.ctors E₁ hE₁
  -- `E₁`'s constants that the restoration replaces or renames
  have hE₁names : ∀ c, (E₁.constants c).isSome → venv.constants c ≠ none ∨ c ∈ d.names := by
    intro c hc
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    rcases VEnv.addConstList_constants_cases hE₁ hci with h | h
    · exact .inl (by rw [h]; nofun)
    · obtain ⟨T, hT, he⟩ := List.mem_map.1 h
      cases he
      exact .inr (List.mem_map_of_mem hT)
  have hrenE₁ : ∀ c c', ren c = some c' → E₁.constants c = none := by
    intro c c' hr
    cases h : E₁.constants c with
    | none => rfl
    | some _ =>
      rcases hE₁names c (by simp [h]) with h' | h'
      · exact (h' (hrenfresh c c' hr)).elim
      · exact (hrenNames c c' hr h').elim
  have hdom : ∀ c, nestedF R d.params c ≠ none ∨ R c ≠ none ∨ ren c ≠ none →
      c ∈ d.names ∨ E₁.constants c = none := by
    intro c hc
    have hc' : R c ≠ none ∨ ren c ≠ none := by
      rcases hc with hc | hc | hc
      · left; intro hR; simp [nestedF, hR] at hc
      · exact .inl hc
      · exact .inr hc
    rcases hc' with hR | hr
    · obtain ⟨h, hR⟩ := Option.ne_none_iff_exists'.1 hR
      obtain ⟨k, T, hT, hc⟩ := hRdom c h hR
      rcases hc with rfl | ⟨c', hc', rfl⟩
      · exact .inl (List.mem_map_of_mem (List.mem_of_getElem? hT))
      · right
        cases h' : E₁.constants c'.name with
        | none => rfl
        | some _ =>
          rcases hE₁names c'.name (by simp [h']) with h'' | h''
          · exact (h'' (hRfresh _ _ hR)).elim
          · exact (hctorNames T (List.mem_of_getElem? hT) c' hc' h'').elim
    · obtain ⟨c', hr⟩ := Option.ne_none_iff_exists'.1 hr
      exact .inr (hrenE₁ c c' hr)
  -- the restored block's environment, and the restoration over a parameter context
  have mkHE (E₀ : VEnv) (hE₀ : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts =
      some E₀) {Qs : List VExpr} (hQ : E₀.IsTele d.uvars [] Qs)
      (hQP : E₀.TeleDefEq d.uvars [] Qs d.params) :=
    H.restoreEnv henv hRfresh hrenfresh hRdom hd.params (fun T hT => (hd.types T hT).1) hE₁ hE₀
      (fun T hT => let ⟨o, h1, h2⟩ := hAux T hT; ⟨o, h1, h2 E₀ hE₀⟩) hQ hQP
  -- terms of `venv` are left alone by the substitution too
  have hFfree {e : VExpr} (he : e.ConstsSat fun c => R c = none ∧ ren c = none) :
      e.ConstsSat (nestedF R d.params · = none) :=
    he.mono fun c hc => by simp [nestedF, hc.1]
  have hE₁ren {U : Nat} {Γ : List VExpr} {e e' A : VExpr} (hΓ : OnCtx Γ (E₁.IsType U))
      (h : E₁.IsDefEq U Γ e e' A) :
      e.ConstsSat (ren · = none) ∧ e'.ConstsSat (ren · = none) ∧ A.ConstsSat (ren · = none) :=
    renFree hE₁wf hrenE₁ hΓ h
  have hPP₁ : OnCtx d.params.reverse (E₁.IsType d.uvars) := by
    simpa using (hd.params.mono hle₁).onCtx trivial
  refine {
    nonempty := ?_
    level := hd.level
    params := by rw [hparams]; exact hd.params
    types := ?_
    aux := hAux
    ctors := ?_
    isRec := ?_
    largeElim := ?_ }
  · intro h
    have hl := H.len
    have := congrArg List.length h
    simp only [restoreNested, List.length_map, List.length_take, List.length_zipIdx,
      List.length_nil] at this
    omega
  · intro T' hT'
    obtain ⟨j, T, -, hT, rfl⟩ := mem_restoreNested_types.1 hT'
    have hTm := List.mem_of_getElem? hT
    refine ⟨?_, rfl⟩
    show venv.IsType d.uvars [] (T.type.restore R ren)
    rw [hTrestore hTm]; exact (hd.types T hTm).1
  · intro E₀ hE₀ T' hT'
    rw [restoreNested_allTypes] at hT'
    obtain ⟨⟨T, j⟩, hm, rfl⟩ := List.mem_map.1 hT'
    have hj : d.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hm
    have hTm := List.mem_of_getElem? hj
    have hle₀ := VEnv.addConstList_le hE₀
    have hP₀ : E₀.IsTele d.uvars [] d.params := hd.params.mono hle₀
    have HE := mkHE E₀ hE₀ hP₀ hP₀.teleDefEq_self
    have hflat := hdeclT T (by rw [allTypes_of_aux H.flat]; exact hTm)
    have hcl : ∀ c h, R c = some h → ∀ a ∈ h.args, a.ClosedN h.n := fun c h hc =>
      let ⟨_, _, _, hcl, _⟩ := HE.hR c h hc; hcl
    have hnp : ∀ c h, R c = some h → h.n = d.params.length := by
      intro c h hc
      obtain ⟨k, T₂, hT₂, hc'⟩ := hRdom c h hc
      obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.1 hT₂).1; have := H.len; omega)⟩
      obtain ⟨hR₁, -, hR₂⟩ := H.aux k T₂ o hT₂ ho
      rcases hc' with rfl | ⟨c', hc', rfl⟩
      · rw [hR₁] at hc; cases hc; rfl
      · rw [(hR₂ c' hc').1] at hc; cases hc; rfl
    refine ⟨?_, fun c' hc' => ?_⟩
    · -- the indices, typed with the block's types only, mention none of them
      have hIC₁ := VEnv.IsTele.constsSat hE₁wf.ordered hflat.1.indices hPP₁
      have hIC : ∀ x ∈ T.indices, x.ConstsSat fun c => R c = none ∧ ren c = none :=
        fun x hx => ((hIC₁ x hx).and (constsSat_of_mentions (hIdx T hTm x hx))).mono
          fun c ⟨h1, h2⟩ => by
            rcases hE₁names c h1 with h | h
            · refine ⟨?_, ?_⟩
              · cases hR : R c with
                | none => rfl
                | some _ => exact (h (hRfresh c _ hR)).elim
              · cases hr : ren c with
                | none => rfl
                | some _ => exact (h (hrenfresh c _ hr)).elim
            · exact (h2 h).elim
      have hidx : T.indices.map (·.restore R ren) = T.indices :=
        (List.map_congr_left fun x hx => restore_of_constsSat (hIC x hx)).trans
          (List.map_id' _)
      have hidxF : T.indices.map (·.replaceConst (nestedF R d.params)) = T.indices :=
        (List.map_congr_left fun x hx => VExpr.replaceConst_of_constsSat (hFfree (hIC x hx))).trans
          (List.map_id' _)
      have hparF : d.params.reverse.map (·.replaceConst (nestedF R d.params)) = d.params.reverse :=
        (List.map_congr_left fun x hx => VExpr.replaceConst_of_constsSat
          (hFfree (hfr (hPC x (List.mem_reverse.1 hx))))).trans (List.map_id' _)
      refine ⟨?_, ?_⟩
      · show E₀.IsTele d.uvars (d.restoreNested R ren n ns cname).params.reverse
          (T.indices.map (·.restore R ren))
        rw [hparams, hidx]
        have := hflat.1.indices.replaceConst HE.wf.ordered HE.subst
        rwa [hparF, hidxF] at this
      · show E₀.IsDefEqU d.uvars [] (T.type.restore R ren)
          (.foralls ((d.restoreNested R ren n ns cname).params ++ T.indices.map (·.restore R ren))
            (.sort d.level))
        rw [hparams, hidx, hTrestore hTm]
        have := hflat.1.defeq.replaceConst HE.wf.ordered HE.subst
        rwa [VExpr.replaceConst_of_constsSat (hFfree (hfr (hTC hTm))),
          VExpr.replaceConst_of_constsSat (hFfree ((VExpr.ConstsSat.foralls
            (As := d.params ++ T.indices) (B := .sort d.level)).2
            ⟨fun A hA => by
              rcases List.mem_append.1 hA with hA | hA
              · exact hfr (hPC A hA)
              · exact hIC A hA, trivial⟩))] at this
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    have hcW := hflat.2 c hc
    have hF := hCtor T hTm c hc
    obtain ⟨ps, B, hty, hpsl, hpsC, hBA⟩ := hF.shape
    obtain ⟨ps₀, Ds, hty₀, hTD, hFW, hSk⟩ := hcW.shape
    have hl₀ := hTD.length_eq
    obtain ⟨rfl, rfl⟩ := VExpr.foralls_inj (hty.symm.trans (hty₀.trans
      (VExpr.foralls_append ..))) (by rw [hpsl, hl₀])
    obtain ⟨hDA, hXA⟩ := VExpr.AuxAt.foralls hBA
    -- the parameters' binders, which nothing replaces
    have hpsF : ∀ p ∈ ps, p.ConstsSat (nestedF R d.params · = none) := fun p hp => hFfree (hpsC p hp)
    have hpsR : ps.map (·.restore R ren) = ps :=
      (List.map_congr_left fun p hp => restore_of_constsSat (hpsC p hp)).trans (List.map_id' _)
    have hPF : ∀ p ∈ d.params, p.ConstsSat (nestedF R d.params · = none) :=
      fun p hp => hFfree (hfr (hPC p hp))
    have hmapF {L : List VExpr} (hL : ∀ p ∈ L, p.ConstsSat (nestedF R d.params · = none)) :
        L.map (·.replaceConst (nestedF R d.params)) = L :=
      (List.map_congr_left fun p hp => VExpr.replaceConst_of_constsSat (hL p hp)).trans
        (List.map_id' _)
    have hcT := hcW.type
    rw [hty] at hcT
    obtain ⟨hpsT, hBT⟩ := VEnv.IsType.foralls_inv hE₁wf.ordered hcT
    have hQ : E₀.IsTele d.uvars [] ps := by
      have := hpsT.replaceConst HE.wf.ordered HE.subst
      rwa [hmapF hpsF] at this
    have hQP : E₀.TeleDefEq d.uvars [] ps d.params := by
      have := hTD.replaceConst HE.wf.ordered HE.subst
      rwa [hmapF hpsF, hmapF hPF] at this
    have hcren : c.type.ConstsSat (ren · = none) := by
      obtain ⟨_, h⟩ := hcW.type
      exact (hE₁ren (Γ := []) trivial h).1
    rw [hty, VExpr.ConstsSat.foralls] at hcren
    have hBren := hcren.2
    -- the conclusion, restored
    have hX : (T.typeApp (VLevel.params d.uvars) (bvars d.params.length c.fields.length)
        c.indices).restore R ren = (T.restore R ren cname (nestedAt n ns j)).typeApp
          (VLevel.params d.uvars) (bvars d.params.length c.fields.length)
          (c.indices.map (·.restore R ren)) :=
      H.restore_typeApp hj _ (by simp) (VExpr.restore_bvars ..) _
    have hcty : (c.restore R ren cname).type = .foralls (ps ++ Ds.map (·.restore R ren))
        ((T.restore R ren cname (nestedAt n ns j)).typeApp (VLevel.params d.uvars)
          (bvars d.params.length c.fields.length) (c.indices.map (·.restore R ren))) := by
      show c.type.restore R ren = _
      rw [hty, VExpr.restore_foralls, hpsR, VExpr.restore_foralls, hX, VExpr.foralls_append]
    refine ⟨?_, ⟨ps, Ds.map (·.restore R ren), ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · -- the type
      have HEps := mkHE E₀ hE₀ hQ hQP
      have := HEps.isType (Δ := []) (by simpa using hpsT.onCtx trivial) trivial hBA
        (by simpa using hBT)
      have hB' := VExpr.restore_ren_none (R := R) hBren
      show E₀.IsType d.uvars [] (c.type.restore R ren)
      rw [hty, VExpr.restore_foralls, hpsR, hB']
      exact VEnv.IsTele.foralls hQ (by simpa using this)
    · rw [hcty, restoreNested_params_length]
      simp only [VConstructor.restore, List.length_map]
      rfl
    · rw [hparams]; exact hQP
    · have := H.fieldsWF hE₁wf hrenE₁ HE hdom (Δ := []) rfl hFW (by simpa using hPP₁) trivial
        (fun i D hD => by simpa using hDA i D hD) (fun i f hf => by simpa using hF.fields i f hf)
      rw [hparams]; simpa [VConstructor.restore] using this
    · intro k D' f' hD' hf' j hSk'
      rw [List.getElem?_map] at hD'
      obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.1 hD'
      rw [VConstructor.restore_fields_getElem?] at hf'
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hf'
      exact (hF.strips ps Ds _ hty₀ hpsl k D f hD hf).restore.skips hSk'
    · simp [VConstructor.restore, VInductiveType.restore, hcW.indices.1]
    · simp only [VConstructor.restore, List.all_map, List.all_eq_true, Function.comp_apply]
      intro x hx
      have hm := List.all_eq_true.1 hcW.indices.2 x hx
      have hxc : x.ConstsSat fun y => R y = none ∧ ren y = none := by
        have hmx : x.mentions d.names = false := by simpa using hm
        refine ((hF.indices x hx).and (VExpr.constsSat_of_mentions hmx)).mono
          fun y ⟨h1, h2⟩ => ?_
        by_cases hRy : R y = none
        · refine ⟨hRy, ?_⟩
          cases hr : ren y with
          | none => rfl
          | some _ => exact (h2 (h1 (.inr (by simp [hr])))).elim
        · exact (h2 (h1 (.inl hRy))).elim
      rw [restore_of_constsSat hxc]
      have hmx : x.mentions d.names = false := by simpa using hm
      simpa using VExpr.mentions_mono restoreNested_names_sub hmx
    · intro k f' hf'
      rw [VConstructor.restore_fields_getElem?] at hf'
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hf'
      obtain ⟨hT1, hT2⟩ := hcW.projFields k f hf
      have hFA : ∀ i (f : VField), c.fields[i]? = some f →
          f.type.AuxAt R (VLevel.params d.uvars) i := fun i f hf => (hF.fields i f hf).1
      have hrk := c.restore_keptFields (ren := ren) (cname := cname) hFA hcl k
      obtain ⟨hctx, hklen⟩ := c.keptFieldsBy_ctxAuxAt hnp (c.Skipped k) hFA k
      have hctx' : VExpr.CtxAuxAt R (VLevel.params d.uvars) ((c.keptFields k).reverse ++ []) := by
        rw [List.append_nil]; exact hctx
      have hΓk := hT1.onCtx hPP₁
      have hkren : (c.keptFields k).map (·.restore R ren) =
          (c.keptFields k).map (·.restore R fun _ => none) := by
        have := restore_ren_ctx (R := R) hE₁wf hrenE₁ hΓk
        simpa [List.map_reverse] using congrArg List.reverse this
      have hsA : (c.strippedType k k f.type).AuxAt R (VLevel.params d.uvars)
          (c.keptFields k).reverse.length := by
        rw [List.length_reverse]
        show (VConstructor.strippedTypeBy (c.Skipped k) k f.type).AuxAt _ _
          (c.keptFieldsBy (c.Skipped k) k).length
        rw [hklen]
        exact VConstructor.strippedTypeBy_auxAt hnp _ (hF.fields k f hf).1
      constructor
      · have := HE.isTele (Δ := []) (by simpa using hPP₁) hctx' hT1
        show E₀.IsTele d.uvars _ _
        rw [hparams, hrk, hkren]; simpa using this
      · have := HE.hasType (A := .sort f.level) hΓk hctx hsA trivial hT2
        have hsren := VExpr.restore_ren_none (R := R) (hE₁ren hΓk hT2).1
        rw [← hsren, ← c.restore_strippedType (ren := ren) (cname := cname) hFA hcl] at this
        rw [hparams, hrk]
        have hk' : ((c.keptFields k).map (·.restore R ren)).reverse =
            (c.keptFields k).reverse.map (·.restore R fun _ => none) := by
          rw [hkren, List.map_reverse]
        rw [hk']
        exact this
  · intro hr T' hT' c' hc' f' hf'
    rw [restoreNested_allTypes] at hT'
    obtain ⟨⟨T, j⟩, hm, rfl⟩ := List.mem_map.1 hT'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hf'
    have := hd.isRec hr T (by rw [allTypes_of_aux H.flat]; exact List.fst_mem_of_mem_zipIdx hm)
      c hc f hf
    simp [VField.restore, this]
  · intro hL
    rcases hd.largeElim hL with h | ⟨T, hT, -, hc⟩
    · exact .inl h
    · right
      have hl := H.len
      rw [hT] at hl
      simp only [List.length_singleton] at hl
      have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨T.restore R ren cname none, ?_, ?_, ?_⟩
      · simp [restoreNested, hT, nestedAt]
      · simp [restoreNested, hT]
      · rcases hc with hc | ⟨c, hc, hf⟩
        · left; simp [VInductiveType.restore, hc]
        · right
          refine ⟨c.restore R ren cname, by simp [VInductiveType.restore, hc], fun k f' hf' hz => ?_⟩
          rw [VConstructor.restore_fields_getElem?] at hf'
          obtain ⟨f, hfk, rfl⟩ := Option.map_eq_some_iff.1 hf'
          have := hf k f hfk hz
          simp only [VConstructor.restore, List.length_map, List.mem_map]
          exact ⟨_, this, by simp [VExpr.restore]⟩

end VInductDecl

end Lean4Lean

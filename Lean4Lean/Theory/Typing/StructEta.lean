import Lean4Lean.Theory.Typing.Recursor

/-!
# Structure eta is well typed

`EtaFacts` collects what the eta rule of a non-recursive structure is typed from: the
parameters and fields, the constructor, the recursor at every motive level, and the iota rule as
a definitional equation. From it, `projs_typed` types the projections and computes them on a
constructor together, by strong induction on the field: the `k`th projection's motive substitutes
the earlier projections for the earlier fields, so its minor premise is typed only once the
earlier projections compute to their fields by iota. `etaRule_WF` then types the constructor
applied to the projections.

The projections are stated under any binders below the parameters, and commute with
substitutions that move the parameters (`proj_subst`), which is how beta-reducing a motive at a
term turns into the field's type at that term's projections.
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

/-- Pairs of arguments for a telescope, each pair defeq at its entry instantiated by the left
arguments before it. -/
theorem Ctx.SubstEq.ofGetElemDF {Γ Δ : List VExpr} {σ σ' : Subst}
    (hσ : Ctx.SubstEq env U Γ σ σ' Δ) :
    ∀ (n : Nat) {As as bs : List VExpr}, as.length = n → env.IsTele U Δ As →
    as.length = As.length → bs.length = As.length →
    (∀ r (h : r < as.length) (h' : r < bs.length) (h'' : r < As.length),
      env.IsDefEq U Γ as[r] bs[r] (As[r].subst (σ.consList (as.take r)))) →
    Ctx.SubstEq env U Γ (σ.consList as) (σ'.consList bs) (As.reverse ++ Δ)
  | 0, As, as, bs, hn, _, hlen, hlen', _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    obtain rfl := List.eq_nil_of_length_eq_zero hlen'
    exact hσ
  | n + 1, As, as, bs, hn, hAs, hlen, hlen', H => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    obtain ⟨bs, b, rfl⟩ : ∃ bs' b, bs = bs' ++ [b] := by
      simpa using (List.eq_nil_or_concat bs).resolve_left (by rintro rfl; simp at hlen')
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn hlen'
    obtain ⟨hAs', hA⟩ := IsTele.append_inv hAs
    have ⟨_, hA⟩ : env.IsType U (As.reverse ++ Δ) A := by cases hA with | cons h _ => exact h
    rw [Subst.consList_concat, Subst.consList_concat, List.reverse_append]
    refine .cons (Ctx.SubstEq.ofGetElemDF hσ n hn hAs' hlen hlen' fun r h h' h'' => ?_) hA ?_
    · have := H r (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [List.getElem_append_left h, List.getElem_append_left h',
        List.getElem_append_left h'', List.take_append_of_le_length (Nat.le_of_lt h)] at this
      exact this
    · have h1 := H as.length (by simp) (by simp; omega) (by simp; omega)
      have e1 : (as ++ [a])[as.length]'(by simp) = a := by simp
      have e2 : (As ++ [A])[as.length]'(by simp; omega) = A := by simp [hlen]
      have e2' : (bs ++ [b])[as.length]'(by simp; omega) = b := by simp [hlen, hlen']
      have e3 : (as ++ [a]).take as.length = as := by simp
      rw [e1, e2, e2', e3] at h1
      exact h1

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

namespace VInductDecl
variable (d : VInductDecl) (S : VInductiveType) (c : VConstructor)

/-! Structure eta: the projections of `VInductDecl.proj`, typed by strong induction on the field.
The `k`th projection's motive substitutes the earlier projections of its bound variable; on a
constructor, the iota rule computes each earlier projection to its field. -/

/-- The first `k` projections of `y`, under `D` binders below the parameters. -/
def projs (D k : Nat) (y : VExpr) : List VExpr := (List.range k).map fun i => d.proj S c D i y

/-- The body of the `k`th projection's motive. -/
def projBody (D k : Nat) (f : VField) : VExpr :=
  f.type.subst ((Subst.ofLift (.skipN .refl (D + 1))).consList (d.projs S c (D + 1) k (.bvar 0)))

/-- The structure applied to the parameters, under `D` binders. -/
def structApp (D : Nat) : VExpr :=
  .appN (.const S.name (VLevel.params d.uvars)) (bvars d.params.length D)

def projMotive (D k : Nat) (f : VField) : VExpr := .lam (d.structApp S D) (d.projBody S c D k f)

def projMinor (D k : Nat) : VExpr :=
  .lams (liftTele D (c.fields.map (·.type))) (.bvar (c.fields.length - 1 - k))

/-- Each field's type mentions only the parameters and the fields before it. -/
def FieldsClosed : Prop :=
  ∀ k (f : VField), c.fields[k]? = some f → f.type.ClosedN (d.params.length + k)

variable {d S c}

theorem proj_eq {D k : Nat} {f : VField} {y : VExpr} (hf : c.fields[k]? = some f) :
    d.proj S c D k y = .appN (.const (Lean.mkRecName S.name) (f.level :: VLevel.params d.uvars))
      (bvars d.params.length D ++ [d.projMotive S c D k f, projMinor c D k, y]) := by
  rw [proj]
  simp [hf, projMotive, projBody, projs, projMinor, structApp]

theorem proj_none {D k : Nat} {y : VExpr} (hf : c.fields[k]? = none) :
    d.proj S c D k y = default := by
  rw [proj]; simp [hf]

theorem projMinor_eq_subst {D k : Nat} (hk : k < c.fields.length) :
    projMinor c D k =
      (VExpr.lams (c.fields.map (·.type)) (.bvar (c.fields.length - 1 - k))).subst
        (.ofLift (.skipN .refl D)) := by
  simp only [projMinor, subst_lams, List.length_map, subst_bvar, Subst.ofLift_liftN]
  congr 1
  · rw [liftTele_eq_liftTele', liftTele'_eq_zipIdx]
    apply List.map_congr_left; rintro ⟨A, i⟩ _
    simp [lift'_eq_subst]
  · simp [Subst.ofLift, Lift.liftVar_consN]; intro; omega

theorem structApp_subst {D D' : Nat} {σ : Subst}
    (hσ : ∀ j < d.params.length, σ (j + D) = .bvar (j + D')) :
    (d.structApp S D).subst σ = d.structApp S D' := by
  simp only [structApp, subst_appN, subst_const, bvars, List.map_map, Function.comp_def,
    subst_bvar]
  congr 1; apply List.map_congr_left; intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  exact hσ i hi

theorem lams_fields_closed (hcl : FieldsClosed d c)
    {k : Nat} (hk : k < c.fields.length) :
    (VExpr.lams (c.fields.map (·.type)) (.bvar (c.fields.length - 1 - k))).ClosedN
      d.params.length := by
  refine ClosedN.lams (fun i A h => ?_) (by simp [ClosedN]; omega)
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨f, hf, rfl⟩ := h
  exact hcl i f hf

theorem projMinor_subst (hcl : FieldsClosed d c)
    {D D' k : Nat} {σ : Subst} (hk : k < c.fields.length)
    (hσ : ∀ j < d.params.length, σ (j + D) = .bvar (j + D')) :
    (projMinor c D k).subst σ = projMinor c D' k := by
  rw [projMinor_eq_subst hk, projMinor_eq_subst hk, subst_subst]
  apply (lams_fields_closed hcl hk).subst_congr
  intro i hi
  simp only [Subst.comp, Subst.ofLift, subst_bvar, Lift.liftVar_skipN, Lift.liftVar]
  exact hσ i hi

theorem lift_moves {D D' : Nat} {σ : Subst}
    (hσ : ∀ j < d.params.length, σ (j + D) = .bvar (j + D')) :
    ∀ j < d.params.length, σ.lift (j + (D + 1)) = .bvar (j + (D' + 1)) := by
  intro j hj
  rw [show j + (D + 1) = (j + D) + 1 by omega]
  simp [Subst.lift, hσ j hj, VExpr.lift, VExpr.liftN]; omega

theorem projBody_subst_of (hcl : FieldsClosed d c) {D D' k : Nat} {f : VField} {σ : Subst}
    (hf : c.fields[k]? = some f)
    (hσ : ∀ j < d.params.length, σ (j + D) = .bvar (j + D'))
    (ih : ∀ i < k, (d.proj S c (D + 1) i (.bvar 0)).subst σ.lift =
      d.proj S c (D' + 1) i (.bvar 0)) :
    (d.projBody S c D k f).subst σ.lift = d.projBody S c D' k f := by
  simp only [projBody, subst_subst, Subst.comp_consList]
  have hps : (d.projs S c (D + 1) k (.bvar 0)).map (·.subst σ.lift) =
      d.projs S c (D' + 1) k (.bvar 0) := by
    simp only [projs, List.map_map, Function.comp_def]
    apply List.map_congr_left; intro i hi
    exact ih i (List.mem_range.1 hi)
  rw [hps]
  apply (hcl k f hf).subst_congr
  intro i hi
  refine Subst.consList_congr (N := d.params.length) (fun j hj => ?_) _ i
    (by simp [projs]; omega)
  simp only [Subst.comp, Subst.ofLift, subst_bvar, Lift.liftVar_skipN, Lift.liftVar]
  rw [lift_moves hσ j hj]

/-- A projection commutes with a substitution that moves the parameters. -/
theorem proj_subst (hcl : FieldsClosed d c) :
    ∀ k {D D' : Nat} {σ : Subst} (y : VExpr),
    (∀ j < d.params.length, σ (j + D) = .bvar (j + D')) →
    (d.proj S c D k y).subst σ = d.proj S c D' k (y.subst σ) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro D D' σ y hσ
  cases hf : c.fields[k]? with
  | none => rw [proj_none hf, proj_none hf]; rfl
  | some f =>
  have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  have hb : (bvars d.params.length D).map (·.subst σ) = bvars d.params.length D' := by
    simp only [bvars, List.map_map, Function.comp_def, subst_bvar]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    exact hσ i hi
  have hM : (d.projMotive S c D k f).subst σ = d.projMotive S c D' k f := by
    simp only [projMotive, subst, structApp_subst hσ]
    rw [projBody_subst_of hcl hf hσ fun i hi => (ih i hi _ (lift_moves hσ)).trans rfl]
  rw [proj_eq hf, proj_eq hf]
  simp only [subst_appN, subst_const, List.map_append, List.map_cons, List.map_nil, hb, hM,
    projMinor_subst hcl hk hσ]

theorem projMotive_subst (hcl : FieldsClosed d c) {D D' k : Nat} {f : VField} {σ : Subst}
    (hf : c.fields[k]? = some f)
    (hσ : ∀ j < d.params.length, σ (j + D) = .bvar (j + D')) :
    (d.projMotive S c D k f).subst σ = d.projMotive S c D' k f := by
  simp only [projMotive, subst, structApp_subst hσ]
  rw [projBody_subst_of hcl hf hσ fun i _ => (proj_subst hcl i _ (lift_moves hσ)).trans rfl]

theorem projMotive_liftN (hcl : FieldsClosed d c) {D k : Nat} {f : VField}
    (hf : c.fields[k]? = some f) (m : Nat) :
    (d.projMotive S c D k f).liftN m = d.projMotive S c (D + m) k f := by
  rw [liftN_eq_subst]
  exact projMotive_subst hcl hf fun j _ => by
    simp [Subst.ofLift, Lift.liftVar_skipN]; omega

theorem projBody_inst (hcl : FieldsClosed d c) {D k : Nat} {f : VField} {y : VExpr}
    (hf : c.fields[k]? = some f) :
    (d.projBody S c D k f).inst y =
      f.type.subst ((Subst.ofLift (.skipN .refl D)).consList (d.projs S c D k y)) := by
  have hσ : ∀ j < d.params.length, Subst.one y (j + (D + 1)) = .bvar (j + D) := by
    intro j _; rw [show j + (D + 1) = (j + D) + 1 by omega]; rfl
  rw [inst_eq, projBody, subst_subst, Subst.comp_consList]
  have hps : (d.projs S c (D + 1) k (.bvar 0)).map (·.subst (Subst.one y)) =
      d.projs S c D k y := by
    simp only [projs, List.map_map, Function.comp_def]
    apply List.map_congr_left; intro i _
    exact (proj_subst hcl i _ hσ).trans rfl
  rw [hps]
  apply (hcl k f hf).subst_congr
  intro i hi
  refine Subst.consList_congr (N := d.params.length) (fun j hj => ?_) _ i
    (by simp [projs]; omega)
  simp only [Subst.comp, Subst.ofLift, subst_bvar, Lift.liftVar_skipN, Lift.liftVar]
  exact hσ j hj

variable (d S c) in
/-- The constructor applied to the parameters and to the fields, which are the innermost
binders, `D` further binders separating the two. -/
def ctorApp (D : Nat) : VExpr :=
  .appN (.const c.name (VLevel.params d.uvars))
    (bvars d.params.length (D + c.fields.length) ++ bvars c.fields.length 0)

variable (d S c) in
/-- The recursor's motive type, for a structure. -/
def structMotiveType (v : VLevel) : VExpr := .forallE (d.structApp S 0) (.sort v)

variable (d S c) in
/-- The recursor's minor premise type, for a non-recursive structure. -/
def structMinorType : VExpr :=
  .foralls (liftTele 1 (c.fields.map (·.type)))
    (.app (.bvar c.fields.length) (d.ctorApp c 1))

variable (d S c) in
/-- The recursor's binders and the fields: the iota rule's binders, for a structure. -/
def iotaBinders (v : VLevel) : List VExpr :=
  d.params ++ [d.structMotiveType S v, d.structMinorType c] ++ liftTele 2 (c.fields.map (·.type))

set_option hygiene false
local notation "𝐔" => d.uvars
local notation "𝐥" => VLevel.params d.uvars
local notation "𝐏" => d.params
local notation "𝐧" => d.params.length
local notation "𝐅" => (c.fields.map (·.type))
local notation "𝐦" => c.fields.length
local notation "τ" D => Subst.ofLift (Lift.skipN Lift.refl D)

/-- What structure eta is typed from, in the environment with the iota rule. -/
structure EtaFacts (d : VInductDecl) (S : VInductiveType) (c : VConstructor) (E : VEnv) :
    Prop where
  henv : E.Ordered
  closed : FieldsClosed d c
  params : E.IsTele 𝐔 [] 𝐏
  fields : E.IsTele 𝐔 𝐏.reverse 𝐅
  level : ∀ {k : Nat} {f : VField}, c.fields[k]? = some f →
    E.HasType 𝐔 (((c.fields.take k).map (·.type)).reverse ++ 𝐏.reverse) f.type (.sort f.level) ∧
    f.level.WF 𝐔
  sort : ∃ u, E.HasType 𝐔 𝐏.reverse (d.structApp S 0) (.sort u)
  ctor : E.HasType 𝐔 (𝐅.reverse ++ 𝐏.reverse) (d.ctorApp c 0) (d.structApp S 𝐦)
  recTyping : ∀ {v : VLevel}, v.WF 𝐔 →
    E.HasType 𝐔 [] (.const (Lean.mkRecName S.name) (v :: 𝐥))
      (.foralls (𝐏 ++ [d.structMotiveType S v, d.structMinorType c, d.structApp S 2])
        (.app (.bvar 2) (.bvar 0)))
  iota : ∀ {v : VLevel}, v.WF 𝐔 →
    E.IsTele 𝐔 [] (d.iotaBinders S c v) ∧
    E.HasType 𝐔 (d.iotaBinders S c v).reverse
      (.appN (.const (Lean.mkRecName S.name) (v :: 𝐥))
        (bvars 𝐧 (𝐦 + 2) ++ [.bvar (𝐦 + 1), .bvar 𝐦, d.ctorApp c 2]))
      (.app (.bvar (𝐦 + 1)) (d.ctorApp c 2)) ∧
    E.HasType 𝐔 (d.iotaBinders S c v).reverse (.appN (.bvar 𝐦) (bvars 𝐦 0))
      (.app (.bvar (𝐦 + 1)) (d.ctorApp c 2)) ∧
    E.IsDefEq 𝐔 []
      (.lams (d.iotaBinders S c v) (.appN (.const (Lean.mkRecName S.name) (v :: 𝐥))
        (bvars 𝐧 (𝐦 + 2) ++ [.bvar (𝐦 + 1), .bvar 𝐦, d.ctorApp c 2])))
      (.lams (d.iotaBinders S c v) (.appN (.bvar 𝐦) (bvars 𝐦 0)))
      (.foralls (d.iotaBinders S c v) (.app (.bvar (𝐦 + 1)) (d.ctorApp c 2)))

theorem liftParams (Δ : List VExpr) :
    Ctx.Lift' (.skipN .refl Δ.length) 𝐏.reverse (Δ ++ 𝐏.reverse) :=
  Ctx.Lift'.skipN_append .refl Δ

theorem liftFields (Δ : List VExpr) :
    Ctx.Lift' (.consN (.skipN .refl Δ.length) 𝐦) (𝐅.reverse ++ 𝐏.reverse)
      ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse) := by
  have := Ctx.Lift'.tele 𝐅 (liftParams (d := d) Δ)
  simp only [List.length_map] at this
  rwa [liftTele_eq_liftTele' 𝐅 Δ.length 0, List.append_assoc]

theorem ctorApp_lift (D : Nat) :
    (d.ctorApp c 0).subst (.ofLift (.consN (.skipN .refl D) 𝐦)) = d.ctorApp c D := by
  simp only [ctorApp, subst_appN, subst_const, List.map_append, bvars, List.map_map,
    Function.comp_def, subst_bvar, Subst.ofLift, Lift.liftVar_consN, Lift.liftVar_skipN]
  congr 2
  · apply List.map_congr_left; intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    simp; split <;> omega
  · apply List.map_congr_left; intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    simp; omega

theorem structApp_liftN (D k : Nat) : (d.structApp S D).liftN k = d.structApp S (D + k) := by
  rw [liftN_eq_subst]
  exact structApp_subst fun j _ => by simp [Subst.ofLift, Lift.liftVar_skipN]; omega

theorem projs_take {D k r : Nat} {y : VExpr} (h : r ≤ k) :
    (d.projs S c D k y).take r = d.projs S c D r y := by
  rw [projs, projs, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem length_projs {D k : Nat} {y : VExpr} : (d.projs S c D k y).length = k := by
  simp [projs]

/-- The first `k` fields, as variables below all `m` of them. -/
def fieldVars (m k : Nat) : List VExpr := (List.range k).map fun i => .bvar (m - 1 - i)

theorem _root_.Lean4Lean.VExpr.getElem_liftTele (n : Nat) : ∀ (As : List VExpr) (k i : Nat)
    (h : i < (liftTele n As k).length),
    (liftTele n As k)[i] = (As[i]'(by simpa using h)).liftN n (k + i)
  | A :: As, k, 0, _ => by simp [liftTele]
  | A :: As, k, i + 1, h => by
    simp only [liftTele, List.getElem_cons_succ]
    rw [getElem_liftTele n As (k + 1) i]; congr 1; omega

theorem fieldVars_eq₁ (hcl : FieldsClosed d c) {D k : Nat} {f : VField}
    (hf : c.fields[k]? = some f) :
    (f.type.liftN D k).liftN (𝐦 - k) =
      f.type.subst ((τ (D + 𝐦)).consList (fieldVars 𝐦 k)) := by
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  rw [liftN_eq_subst, liftN_eq_subst, subst_subst]
  apply (hcl k f hf).subst_congr
  intro i hi
  simp only [Subst.comp, Subst.ofLift, subst_bvar, Subst.consList_apply, fieldVars,
    List.length_map, List.length_range, Lift.liftVar_consN, Lift.liftVar_skipN]
  split
  · simp [List.getElem_reverse]; omega
  · simp; omega

theorem fieldVars_eq₂ (hcl : FieldsClosed d c) {D k : Nat} {f : VField}
    (hf : c.fields[k]? = some f) :
    (f.type.liftN (𝐦 - k)).subst ((τ (D + 𝐦)).consList (bvars 𝐦 0)) =
      f.type.subst ((τ (D + 𝐦)).consList (fieldVars 𝐦 k)) := by
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  rw [liftN_eq_subst, subst_subst]
  apply (hcl k f hf).subst_congr
  intro i hi
  simp only [Subst.comp, Subst.ofLift, subst_bvar, Subst.consList_apply, fieldVars,
    List.length_map, List.length_range, Lift.liftVar_consN, Lift.liftVar_skipN,
    Lift.liftVar, Nat.not_lt_zero, if_false, Nat.sub_zero, Nat.add_zero, length_bvars]
  split <;> split <;> simp [bvars, List.getElem_reverse] <;> omega

theorem liftN_one_subst_cons (e : VExpr) (σ : Subst) (a : VExpr) (i : Nat) :
    (e.liftN 1 i).subst ((σ.cons a).liftN i) = e.subst (σ.liftN i) := by
  rw [liftN_subst]; congr 1; funext x
  simp only [Subst.lift_l, Lift.liftVar_consN, Lift.liftVar_skipN, Lift.liftVar]
  rw [Subst.liftN_apply, Subst.liftN_apply]
  split
  · simp [*]
  · rw [if_neg (by omega), show x - i + 1 + i - i = (x - i) + 1 by omega]; rfl

theorem foralls_liftTele_subst (D : Nat) (a : VExpr) : ∀ (As : List VExpr) (k : Nat) (B : VExpr),
    (VExpr.foralls (liftTele 1 As k) B).subst (((τ D).cons a).liftN k) =
      .foralls (liftTele D As k) (B.subst (((τ D).cons a).liftN (k + As.length)))
  | [], _, _ => rfl
  | A :: As, k, B => by
    simp only [liftTele, foralls_cons, subst, List.length_cons]
    rw [show (((τ D).cons a).liftN k).lift = ((τ D).cons a).liftN (k + 1) from rfl,
      foralls_liftTele_subst D a As (k + 1) B, liftN_one_subst_cons, Subst.ofLift_liftN,
      ← lift'_eq_subst, lift'_consN_skipN, Nat.add_right_comm, Nat.add_assoc]

theorem structMotive_subst (v : VLevel) (D : Nat) :
    (d.structMotiveType S v).subst (τ D) = .forallE (d.structApp S D) (.sort v) := by
  simp only [structMotiveType, subst]
  rw [structApp_subst (D' := D) fun j _ => by simp [Subst.ofLift, Lift.liftVar_skipN]]

theorem structMinor_subst (D : Nat) (mo : VExpr) :
    (d.structMinorType c).subst ((τ D).cons mo) =
      .foralls (liftTele D 𝐅) (.app (mo.liftN 𝐦) (d.ctorApp c D)) := by
  have := foralls_liftTele_subst D mo 𝐅 0 (.app (.bvar 𝐦) (d.ctorApp c 1))
  simp only [Subst.liftN, Nat.zero_add, List.length_map] at this
  rw [structMinorType, this]
  congr 1
  simp only [subst, Subst.liftN_apply, Nat.lt_irrefl, if_false, Nat.sub_self]
  congr 1
  simp only [ctorApp, subst_appN, subst_const, List.map_append, bvars, List.map_map,
    Function.comp_def, subst_bvar, Subst.liftN_apply]
  congr 2
  · apply List.map_congr_left; intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    rw [if_neg (by omega), show i + (1 + 𝐦) - 𝐦 = i + 1 by omega]
    simp [Subst.cons, Subst.ofLift, Lift.liftVar_skipN, VExpr.liftN]; omega
  · apply List.map_congr_left; intro i hi
    simp only [List.mem_reverse, List.mem_range] at hi
    rw [if_pos (by omega)]

variable (d S c) in
/-- The `k`th projection of a term of the structure has the `k`th field's type, at the earlier
projections. -/
def ProjTyped (E : VEnv) (k : Nat) : Prop :=
  ∀ {f : VField}, c.fields[k]? = some f → ∀ {Δ : List VExpr} {y : VExpr},
    OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔) →
    E.HasType 𝐔 (Δ ++ 𝐏.reverse) y (d.structApp S Δ.length) →
    E.HasType 𝐔 (Δ ++ 𝐏.reverse) (d.proj S c Δ.length k y)
      (f.type.subst ((τ Δ.length).consList (d.projs S c Δ.length k y)))

variable (d S c) in
/-- The `k`th projection of the constructor applied to fields is the `k`th field. -/
def ProjComputes (E : VEnv) (k : Nat) : Prop :=
  ∀ {f : VField}, c.fields[k]? = some f → ∀ {Δ : List VExpr},
    OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔) →
    E.IsDefEq 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      (d.proj S c (Δ.length + 𝐦) k (d.ctorApp c Δ.length)) (.bvar (𝐦 - 1 - k))
      (f.type.subst ((τ (Δ.length + 𝐦)).consList
        (d.projs S c (Δ.length + 𝐦) k (d.ctorApp c Δ.length))))

namespace EtaFacts
variable {E : VEnv} (H : EtaFacts d S c E)
include H

theorem paramsCtx : OnCtx 𝐏.reverse (E.IsType 𝐔) := by
  simpa using H.params.onCtx trivial

theorem tau (Δ : List VExpr) :
    VEnv.Ctx.SubstEq E 𝐔 (Δ ++ 𝐏.reverse) (τ Δ.length) (τ Δ.length) 𝐏.reverse :=
  VEnv.Ctx.SubstEq.ofLift' H.henv (liftParams Δ) H.paramsCtx

theorem structApp_type (Δ : List VExpr) :
    ∃ u, E.HasType 𝐔 (Δ ++ 𝐏.reverse) (d.structApp S Δ.length) (.sort u) := by
  obtain ⟨u, h⟩ := H.sort
  refine ⟨u, ?_⟩
  have := h.weak' H.henv (liftParams Δ)
  rwa [lift'_eq_subst, lift'_eq_subst, structApp_subst (D' := Δ.length) fun j _ => by
    simp [Subst.ofLift, Lift.liftVar_skipN]] at this

theorem fieldsTele (Δ : List VExpr) : E.IsTele 𝐔 (Δ ++ 𝐏.reverse) (liftTele Δ.length 𝐅) :=
  H.fields.weakN H.henv (.zero Δ rfl)

theorem fieldsCtx {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    OnCtx ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse) (E.IsType 𝐔) := by
  simpa using (H.fieldsTele Δ).onCtx hΓ

theorem ctorApp_type (Δ : List VExpr) :
    E.HasType 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse) (d.ctorApp c Δ.length)
      (d.structApp S (Δ.length + 𝐦)) := by
  have := H.ctor.weak' H.henv (liftFields Δ)
  rwa [lift'_eq_subst, lift'_eq_subst, ctorApp_lift, structApp_subst (D' := Δ.length + 𝐦)
    fun j _ => by
      simp only [Subst.ofLift, Lift.liftVar_consN, Lift.liftVar_skipN]
      split <;> simp <;> omega] at this

theorem fieldsTake (k : Nat) : E.IsTele 𝐔 𝐏.reverse ((c.fields.take k).map (·.type)) := by
  have := H.fields
  rw [← List.take_append_drop k c.fields, List.map_append] at this
  exact (VEnv.IsTele.append_inv this).1

/-- The body of the `k`th projection's motive is a type, given the earlier projections' types. -/
theorem motive_body {k : Nat} (ih : ∀ i < k, ProjTyped d S c E i) {f : VField}
    (hf : c.fields[k]? = some f) {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    E.HasType 𝐔 (d.structApp S Δ.length :: Δ ++ 𝐏.reverse) (d.projBody S c Δ.length k f)
      (.sort f.level) := by
  obtain ⟨u, hS⟩ := H.structApp_type Δ
  have hΓ' : OnCtx (d.structApp S Δ.length :: Δ ++ 𝐏.reverse) (E.IsType 𝐔) := ⟨hΓ, u, hS⟩
  have hy : E.HasType 𝐔 (d.structApp S Δ.length :: Δ ++ 𝐏.reverse) (.bvar 0)
      (d.structApp S (Δ.length + 1)) := by
    rw [← structApp_liftN]; exact .bvar .zero
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  have W := VEnv.Ctx.SubstEq.ofGetElem (H.tau (d.structApp S Δ.length :: Δ)) k
    (as := d.projs S c (Δ.length + 1) k (.bvar 0)) length_projs (H.fieldsTake k)
    (by simp [length_projs]; omega) fun r h h' => by
      have hr : r < k := by simpa [length_projs] using h
      have hfr : c.fields[r]? = some c.fields[r] := List.getElem?_eq_getElem (by omega)
      have := ih r hr hfr (Δ := d.structApp S Δ.length :: Δ) hΓ' hy
      simp only [List.length_cons] at this
      rw [projs_take (Nat.le_of_lt hr)]
      simpa [projs] using this
  have := (H.level hf).1.subst H.henv W hΓ'
  simpa [projBody] using this

theorem motive_type {k : Nat} (ih : ∀ i < k, ProjTyped d S c E i) {f : VField}
    (hf : c.fields[k]? = some f) {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    E.HasType 𝐔 (Δ ++ 𝐏.reverse) (d.projMotive S c Δ.length k f)
      (.forallE (d.structApp S Δ.length) (.sort f.level)) :=
  let ⟨_, hS⟩ := H.structApp_type Δ
  .lam hS (H.motive_body ih hf hΓ)

theorem fieldsCtx' {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    OnCtx (((liftTele Δ.length 𝐅).reverse ++ Δ) ++ 𝐏.reverse) (E.IsType 𝐔) :=
  H.fieldsCtx hΓ

omit H in
theorem length_fieldsCtx (Δ : List VExpr) :
    ((liftTele Δ.length 𝐅).reverse ++ Δ).length = Δ.length + 𝐦 := by
  simp [Nat.add_comm]

/-- On a constructor, the `k`th projection's motive computes by beta to the `k`th field's type
at the earlier projections. -/
theorem motive_beta {k : Nat} (ih : ∀ i < k, ProjTyped d S c E i) {f : VField}
    (hf : c.fields[k]? = some f) {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    E.IsDefEq 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      (.app (d.projMotive S c (Δ.length + 𝐦) k f) (d.ctorApp c Δ.length))
      (f.type.subst ((τ (Δ.length + 𝐦)).consList
        (d.projs S c (Δ.length + 𝐦) k (d.ctorApp c Δ.length))))
      (.sort f.level) := by
  have hb := H.motive_body ih hf (H.fieldsCtx' hΓ)
  rw [length_fieldsCtx] at hb
  have := VEnv.IsDefEq.beta hb (H.ctorApp_type Δ)
  rwa [projBody_inst H.closed hf] at this

/-- The earlier projections on a constructor compute to the earlier fields, so the `k`th field's
type at them is its type at the fields. -/
theorem projs_fields {k : Nat} (ihc : ∀ i < k, ProjComputes d S c E i) {f : VField}
    (hf : c.fields[k]? = some f) {Δ : List VExpr} (hΓ : OnCtx (Δ ++ 𝐏.reverse) (E.IsType 𝐔)) :
    E.IsDefEq 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      (f.type.subst ((τ (Δ.length + 𝐦)).consList
        (d.projs S c (Δ.length + 𝐦) k (d.ctorApp c Δ.length))))
      (f.type.subst ((τ (Δ.length + 𝐦)).consList (fieldVars 𝐦 k)))
      (.sort f.level) := by
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  have hτ := H.tau ((liftTele Δ.length 𝐅).reverse ++ Δ)
  rw [length_fieldsCtx] at hτ
  have W := VEnv.Ctx.SubstEq.ofGetElemDF hτ k
    (as := d.projs S c (Δ.length + 𝐦) k (d.ctorApp c Δ.length)) (bs := fieldVars 𝐦 k)
    length_projs (H.fieldsTake k) (by simp [length_projs]; omega) (by simp [fieldVars]; omega)
    fun r h h' h'' => by
      have hr : r < k := by simpa [length_projs] using h
      have hfr : c.fields[r]? = some c.fields[r] := List.getElem?_eq_getElem (by omega)
      have := ihc r hr hfr hΓ
      rw [projs_take (Nat.le_of_lt hr)]
      simpa [projs, fieldVars] using this
  have hsrc : OnCtx (((c.fields.take k).map (·.type)).reverse ++ 𝐏.reverse) (E.IsType 𝐔) := by
    simpa using (H.fieldsTake k).onCtx H.paramsCtx
  exact (H.level hf).1.substDF H.henv hsrc (H.fieldsCtx' hΓ) W

theorem fieldVar_type {k : Nat} {f : VField} (hf : c.fields[k]? = some f) (Δ : List VExpr) :
    E.HasType 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse) (.bvar (𝐦 - 1 - k))
      (f.type.subst ((τ (Δ.length + 𝐦)).consList (fieldVars 𝐦 k))) := by
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  have := Lookup.reverse_append (liftTele Δ.length 𝐅) (Γ := Δ ++ 𝐏.reverse) k (by simpa using hk)
  rw [getElem_liftTele] at this
  simp only [length_liftTele, List.length_map, Nat.zero_add, List.getElem_map,
    (List.getElem?_eq_some_iff.1 hf).2, ← List.append_assoc] at this
  rw [fieldVars_eq₁ H.closed hf] at this
  exact .bvar this

/-- The `k`th projection's minor premise, given that its motive at a constructor is the `k`th
field's type. -/
theorem minor_type {k : Nat} {f : VField} (hf : c.fields[k]? = some f) {Δ : List VExpr}
    (hBR : E.IsDefEq 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      (.app (d.projMotive S c (Δ.length + 𝐦) k f) (d.ctorApp c Δ.length))
      (f.type.subst ((τ (Δ.length + 𝐦)).consList (fieldVars 𝐦 k))) (.sort f.level)) :
    E.HasType 𝐔 (Δ ++ 𝐏.reverse) (projMinor c Δ.length k)
      (.foralls (liftTele Δ.length 𝐅)
        (.app (d.projMotive S c (Δ.length + 𝐦) k f) (d.ctorApp c Δ.length))) :=
  (H.fieldsTele Δ).lams (by
    have := VEnv.IsDefEq.defeqDF hBR.symm (H.fieldVar_type hf Δ)
    simp only [List.append_assoc] at this
    exact this)

theorem binderTypes {v : VLevel} (hv : v.WF 𝐔) :
    E.IsType 𝐔 𝐏.reverse (d.structMotiveType S v) ∧
    E.IsType 𝐔 (d.structMotiveType S v :: 𝐏.reverse) (d.structMinorType c) := by
  have h : E.IsTele 𝐔 [] (𝐏 ++ [d.structMotiveType S v, d.structMinorType c] ++
      liftTele 2 𝐅) := (H.iota hv).1
  have h1 := (VEnv.IsTele.append_inv (VEnv.IsTele.append_inv h).1).2
  obtain ⟨hM, hm⟩ : _ ∧ _ := by cases h1 with | cons h t => exact ⟨h, t⟩
  refine ⟨by simpa using hM, ?_⟩
  cases hm with | cons h _ => simpa using h

/-- A motive and a minor premise for a projection, as arguments for the recursor's binders. -/
theorem recArgs {v : VLevel} (hv : v.WF 𝐔) {Δ : List VExpr} {mo mi : VExpr}
    (hmo : E.HasType 𝐔 (Δ ++ 𝐏.reverse) mo (.forallE (d.structApp S Δ.length) (.sort v)))
    (hmi : E.HasType 𝐔 (Δ ++ 𝐏.reverse) mi
      (.foralls (liftTele Δ.length 𝐅) (.app (mo.liftN 𝐦) (d.ctorApp c Δ.length)))) :
    VEnv.Ctx.SubstEq E 𝐔 (Δ ++ 𝐏.reverse) (((τ Δ.length).cons mo).cons mi)
      (((τ Δ.length).cons mo).cons mi)
      (d.structMinorType c :: d.structMotiveType S v :: 𝐏.reverse) := by
  obtain ⟨⟨_, hM⟩, ⟨_, hm⟩⟩ := H.binderTypes hv
  refine .cons (.cons (H.tau Δ) hM ?_) hm ?_
  · show E.HasType 𝐔 _ mo ((d.structMotiveType S v).subst (τ Δ.length))
    rwa [structMotive_subst]
  · show E.HasType 𝐔 _ mi ((d.structMinorType c).subst ((τ Δ.length).cons mo))
    rwa [structMinor_subst]

theorem recTypeBinders {v : VLevel} (hv : v.WF 𝐔) :
    E.IsType 𝐔 (d.structMinorType c :: d.structMotiveType S v :: 𝐏.reverse) (d.structApp S 2) := by
  have hRT := VEnv.IsDefEq.isType H.henv (Γ := []) trivial (H.recTyping hv)
  have h := (VEnv.IsTele.append_inv (VEnv.IsType.foralls_inv H.henv hRT).1).2
  cases h with | cons _ t => cases t with | cons _ t => cases t with | cons h _ => simpa using h

/-- The `k`th projection is typed, given the earlier ones and that they compute. -/
theorem proj_type {k : Nat} (ih : ∀ i < k, ProjTyped d S c E i)
    (ihc : ∀ i < k, ProjComputes d S c E i) : ProjTyped d S c E k := by
  intro f hf Δ y hΓ hy
  have hv := (H.level hf).2
  have hmo := H.motive_type ih hf hΓ
  have hmi := H.minor_type hf ((H.motive_beta ih hf hΓ).trans (H.projs_fields ihc hf hΓ))
  rw [← projMotive_liftN H.closed hf] at hmi
  have W0 := H.recArgs hv hmo hmi
  obtain ⟨_, hS2⟩ := H.recTypeBinders hv
  have hy' : E.HasType 𝐔 (Δ ++ 𝐏.reverse) y ((d.structApp S 2).subst
      ((((τ Δ.length).cons (d.projMotive S c Δ.length k f)).cons (projMinor c Δ.length k)))) := by
    rwa [structApp_subst (D' := Δ.length) fun j _ => by
      simp [Subst.cons, Subst.ofLift, Lift.liftVar_skipN]]
  have W := VEnv.Ctx.SubstEq.cons
    (σ := (((τ Δ.length).cons (d.projMotive S c Δ.length k f)).cons
      (projMinor c Δ.length k)).cons y)
    (σ' := (((τ Δ.length).cons (d.projMotive S c Δ.length k f)).cons
      (projMinor c Δ.length k)).cons y)
    W0 hS2 hy'
  have hrec := H.recTyping hv
  have hrec0 := hrec.weak0 H.henv (Γ := Δ ++ 𝐏.reverse)
  rw [← closed_subst H.henv hrec (.ofLift (.skipN .refl (𝐧 + Δ.length)))] at hrec0
  have hτ : (Subst.ofLift (.skipN .refl (𝐧 + Δ.length))).consList (bvars 𝐧 Δ.length) =
      τ Δ.length := by subst_ext
  have h := VEnv.HasType.appN_substT (Δ := []) (B := .app (.bvar 2) (.bvar 0))
    (as := bvars 𝐧 Δ.length ++ [d.projMotive S c Δ.length k f, projMinor c Δ.length k, y]) hrec0
    (by simp) (by rw [Subst.consList_append, hτ]; simpa [Subst.consList] using W)
  rw [Subst.consList_append, hτ] at h
  have hb := VEnv.IsDefEq.beta (H.motive_body ih hf hΓ) hy
  rw [projBody_inst H.closed hf] at hb
  rw [proj_eq hf]
  exact VEnv.IsDefEq.defeqDF hb h

omit H in
theorem bvars_map_subst_eq {σ : Subst} {n j j' : Nat} (h : ∀ i < n, σ (i + j) = .bvar (i + j')) :
    (bvars n j).map (·.subst σ) = bvars n j' := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar]
  apply List.map_congr_left; intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  exact h i hi

omit H in
/-- The iota rule's substitution, for a motive `a` and a minor premise `b` over fields below
`D'` binders. -/
theorem iotaSubst_apply (D' : Nat) (a b : VExpr) (i : Nat) :
    (((τ D').cons a).cons b).consList (bvars 𝐦 0) i =
      if i < 𝐦 then .bvar i else if i = 𝐦 then b else if i = 𝐦 + 1 then a
      else .bvar (i - 𝐦 - 2 + D') := by
  rw [Subst.consList_bvars_apply]
  by_cases h1 : i < 𝐦; · simp [h1]
  by_cases h2 : i = 𝐦; · subst h2; simp [Subst.cons]
  by_cases h3 : i = 𝐦 + 1; · subst h3; simp [Subst.cons]
  obtain ⟨j, rfl⟩ : ∃ j, i = 𝐦 + 2 + j := ⟨i - 𝐦 - 2, by omega⟩
  rw [if_neg h1, if_neg h1, if_neg h2, if_neg h3, show 𝐦 + 2 + j - 𝐦 = j + 1 + 1 by omega]
  simp [Subst.cons, Subst.ofLift, Lift.liftVar_skipN]

omit H in
theorem iota_lhs_subst {D : Nat} {k : Nat} {f : VField} (hf : c.fields[k]? = some f) :
    (VExpr.appN (.const (Lean.mkRecName S.name) (f.level :: 𝐥))
        (bvars 𝐧 (𝐦 + 2) ++ [.bvar (𝐦 + 1), .bvar 𝐦, d.ctorApp c 2])).subst
      ((((τ (D + 𝐦)).cons (d.projMotive S c (D + 𝐦) k f)).cons
        (projMinor c (D + 𝐦) k)).consList (bvars 𝐦 0)) =
    d.proj S c (D + 𝐦) k (d.ctorApp c D) := by
  rw [proj_eq hf]
  simp only [ctorApp, subst_appN, subst_const, List.map_append, List.map_cons, List.map_nil,
    subst_bvar]
  have e : ∀ i, i + (𝐦 + 2) - 𝐦 - 2 = i := by omega
  rw [bvars_map_subst_eq (j' := D + 𝐦) fun i _ => by
      rw [iotaSubst_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), e],
    bvars_map_subst_eq (j' := D + 𝐦) fun i _ => by
      rw [iotaSubst_apply, Nat.add_comm 2 𝐦, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), e],
    bvars_map_subst_eq (j' := 0) fun i _ => by rw [iotaSubst_apply]; simp; omega,
    iotaSubst_apply, iotaSubst_apply, if_neg (by omega)]
  simp

omit H in
theorem iota_rhs_subst {D' : Nat} {a b : VExpr} :
    (VExpr.appN (.bvar 𝐦) (bvars 𝐦 0)).subst (((τ D').cons a).cons b |>.consList (bvars 𝐦 0)) =
      .appN b (bvars 𝐦 0) := by
  simp only [subst_appN, subst_bvar]
  rw [bvars_map_subst_eq (j' := 0) fun i _ => by rw [iotaSubst_apply]; simp; omega,
    iotaSubst_apply]
  simp

omit H in
theorem iota_type_subst {D : Nat} {a b : VExpr} :
    (VExpr.app (.bvar (𝐦 + 1)) (d.ctorApp c 2)).subst
      (((τ (D + 𝐦)).cons a).cons b |>.consList (bvars 𝐦 0)) = .app a (d.ctorApp c D) := by
  have e : ∀ i, i + (2 + 𝐦) - 𝐦 - 2 = i := by omega
  simp only [ctorApp, subst_appN, subst_const, List.map_append, subst_app, subst_bvar]
  rw [bvars_map_subst_eq (j' := D + 𝐦) fun i _ => by
      rw [iotaSubst_apply, if_neg (by omega), if_neg (by omega), if_neg (by omega), e],
    bvars_map_subst_eq (j' := 0) fun i _ => by rw [iotaSubst_apply]; simp; omega,
    iotaSubst_apply, if_neg (by omega), if_neg (by omega)]
  simp

/-- The `k`th projection computes on a constructor, given that the earlier ones are typed and
compute. -/
theorem proj_computes {k : Nat} (ih : ∀ i < k, ProjTyped d S c E i)
    (ihc : ∀ i < k, ProjComputes d S c E i) : ProjComputes d S c E k := by
  intro f hf Δ hΓ
  have hv := (H.level hf).2
  have hk : k < 𝐦 := (List.getElem?_eq_some_iff.1 hf).1
  have hΓ' := H.fieldsCtx' hΓ
  have hΓF : OnCtx ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse) (E.IsType 𝐔) := hΓ'
  -- the motive and minor premise at the constructor's depth
  have hmo := H.motive_type ih hf hΓ'
  have hmi := H.minor_type hf ((H.motive_beta ih hf hΓ').trans (H.projs_fields ihc hf hΓ'))
  rw [← projMotive_liftN H.closed hf] at hmi
  have W0 := H.recArgs hv hmo hmi
  rw [length_fieldsCtx] at W0
  obtain ⟨hB, hL, hR, hdf⟩ := H.iota hv
  have W2 : VEnv.Ctx.SubstEq E 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      ((τ (Δ.length + 𝐦)).consList (bvars 𝐦 0)) ((τ (Δ.length + 𝐦)).consList (bvars 𝐦 0))
      (𝐅.reverse ++ 𝐏.reverse) := by
    rw [show (τ (Δ.length + 𝐦)).consList (bvars 𝐦 0) =
      .ofLift (.consN (.skipN .refl Δ.length) 𝐦) by subst_ext]
    exact VEnv.Ctx.SubstEq.ofLift' H.henv (liftFields Δ) (by
      simpa using H.fields.onCtx H.paramsCtx)
  have Wf := VEnv.Ctx.SubstEq.extendLift H.henv (ρ := .skipN .refl 2) (Δ := 𝐏.reverse)
    (.skip (.skip .refl)) H.fields W0 (by exact W2) (by simp)
  rw [show liftTele' (.skipN .refl 2) 𝐅 = liftTele 2 𝐅 by
    rw [liftTele_eq_liftTele']; rfl] at Wf
  have hτ : (Subst.ofLift (.skipN .refl (𝐧 + (Δ.length + 𝐦)))).consList
      (bvars 𝐧 (Δ.length + 𝐦) ++ [d.projMotive S c (Δ.length + 𝐦) k f,
        projMinor c (Δ.length + 𝐦) k] ++ bvars 𝐦 0) =
      (((τ (Δ.length + 𝐦)).cons (d.projMotive S c (Δ.length + 𝐦) k f)).cons
        (projMinor c (Δ.length + 𝐦) k)).consList (bvars 𝐦 0) := by
    rw [Subst.consList_append, Subst.consList_append]
    congr 1
    rw [show (Subst.ofLift (.skipN .refl (𝐧 + (Δ.length + 𝐦)))).consList
      (bvars 𝐧 (Δ.length + 𝐦)) = τ (Δ.length + 𝐦) by subst_ext]
    rfl
  have W : VEnv.Ctx.SubstEq E 𝐔 ((liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (𝐧 + (Δ.length + 𝐦)))).consList
        (bvars 𝐧 (Δ.length + 𝐦) ++ [d.projMotive S c (Δ.length + 𝐦) k f,
          projMinor c (Δ.length + 𝐦) k] ++ bvars 𝐦 0))
      ((Subst.ofLift (.skipN .refl (𝐧 + (Δ.length + 𝐦)))).consList
        (bvars 𝐧 (Δ.length + 𝐦) ++ [d.projMotive S c (Δ.length + 𝐦) k f,
          projMinor c (Δ.length + 𝐦) k] ++ bvars 𝐦 0))
      ((d.iotaBinders S c f.level).reverse ++ []) := by
    rw [hτ]; simpa [iotaBinders] using Wf
  have hlen : (bvars 𝐧 (Δ.length + 𝐦) ++ [d.projMotive S c (Δ.length + 𝐦) k f,
      projMinor c (Δ.length + 𝐦) k] ++ bvars 𝐦 0).length =
      (d.iotaBinders S c f.level).length := by
    simp [iotaBinders]
  have hl := hdf.hasType.1
  have hr := hdf.hasType.2
  have hdf0 := hdf.weak0 H.henv (Γ := (liftTele Δ.length 𝐅).reverse ++ Δ ++ 𝐏.reverse)
  rw [← closed_subst H.henv hl (.ofLift (.skipN .refl (𝐧 + (Δ.length + 𝐦))))] at hdf0
  have h1 := VEnv.IsDefEq.appN_substT (Δ := []) hdf0 hlen W
  have h2 := VEnv.IsDefEq.lams_beta H.henv hΓF (Δ := []) .nil hB (by simpa using hL) hlen W
  have h3 := VEnv.IsDefEq.lams_beta H.henv hΓF (Δ := []) .nil hB (by simpa using hR) hlen W
  rw [(hl.closedN H.henv trivial).subst_eq Subst.Fixes.zero] at h2
  rw [(hr.closedN H.henv trivial).subst_eq Subst.Fixes.zero] at h3
  have hLR := (h2.symm.trans h1).trans h3
  rw [hτ, iota_lhs_subst hf, iota_rhs_subst, iota_type_subst] at hLR
  -- the minor premise applied to the fields is the `k`th field
  have hτD := H.tau ((liftTele Δ.length 𝐅).reverse ++ Δ)
  rw [length_fieldsCtx] at hτD
  have hbody : E.HasType 𝐔 (𝐅.reverse ++ 𝐏.reverse) (.bvar (𝐦 - 1 - k)) (f.type.liftN (𝐦 - k)) := by
    have := Lookup.reverse_append 𝐅 (Γ := 𝐏.reverse) k (by simpa using hk)
    simp only [List.length_map, List.getElem_map, (List.getElem?_eq_some_iff.1 hf).2] at this
    exact .bvar this
  have hmin := VEnv.IsDefEq.lams_beta H.henv hΓF (Δ := 𝐏.reverse) hτD H.fields hbody (by simp) W2
  rw [← projMinor_eq_subst hk, fieldVars_eq₂ H.closed hf, subst_bvar,
    Subst.consList_bvars_apply, if_pos (by omega)] at hmin
  exact (VEnv.IsDefEq.defeqDF (H.motive_beta ih hf hΓ) hLR).trans
    (VEnv.IsDefEq.defeqDF (H.projs_fields ihc hf hΓ).symm (by simpa using hmin))

theorem projs_typed : ∀ k, ProjTyped d S c E k ∧ ProjComputes d S c E k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  have ih1 : ∀ i < k, ProjTyped d S c E i := fun i hi => (ih i hi).1
  have ih2 : ∀ i < k, ProjComputes d S c E i := fun i hi => (ih i hi).2
  exact ⟨H.proj_type ih1 ih2, H.proj_computes ih1 ih2⟩

/-- Structure eta is well typed: the constructor applied to the projections has the structure's
type. -/
theorem etaRule_WF : (d.etaRule S c).WF E := by
  obtain ⟨u, hS⟩ := H.sort
  have hbind : E.IsTele 𝐔 [] (𝐏 ++ [d.structApp S 0]) :=
    H.params.append (.cons ⟨u, by simpa using hS⟩ .nil)
  have hΓ : OnCtx ([d.structApp S 0] ++ 𝐏.reverse) (E.IsType 𝐔) := ⟨H.paramsCtx, u, hS⟩
  have hy : E.HasType 𝐔 ([d.structApp S 0] ++ 𝐏.reverse) (.bvar 0) (d.structApp S 1) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, ← structApp_liftN]; exact .bvar .zero
  have W := VEnv.Ctx.SubstEq.ofGetElem (H.tau [d.structApp S 0]) 𝐦
    (as := d.projs S c 1 𝐦 (.bvar 0)) length_projs H.fields (by simp [length_projs])
    fun r h h' => by
      have hr : r < 𝐦 := by simpa [length_projs] using h
      have hfr : c.fields[r]? = some c.fields[r] := List.getElem?_eq_getElem hr
      have := (H.projs_typed r).1 hfr (Δ := [d.structApp S 0]) hΓ hy
      rw [projs_take (Nat.le_of_lt hr)]
      simpa [projs] using this
  have hc := H.ctor.subst H.henv W hΓ
  rw [structApp_subst (D' := 1) fun j _ => by
    rw [Subst.consList_apply, dif_neg (by simp [length_projs])]
    simp [length_projs, Subst.ofLift]] at hc
  have e : (d.ctorApp c 0).subst
      ((τ ([d.structApp S 0].length)).consList (d.projs S c 1 𝐦 (.bvar 0))) =
      .appN (.const c.name 𝐥) (bvars 𝐧 1 ++ d.projs S c 1 𝐦 (.bvar 0)) := by
    have := subst_bvars_consList (τ 1) (d.projs S c 1 𝐦 (.bvar 0))
    rw [length_projs] at this
    simp only [ctorApp, subst_appN, subst_const, List.map_append, Nat.zero_add, this,
      List.length_singleton]
    rw [bvars_map_subst_eq (j' := 1) fun i _ => by
      rw [Subst.consList_apply, dif_neg (by simp [length_projs])]
      simp [length_projs, Subst.ofLift]]
  rw [e] at hc
  refine ⟨hbind.lams ?_, hbind.lams ?_⟩
  · simpa [structApp] using hy
  · simpa [projs, structApp] using hc

end EtaFacts
end VInductDecl
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

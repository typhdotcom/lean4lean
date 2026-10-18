import Lean4Lean.Theory.Typing.InductiveEnv

/-!
# The recursor's type is well typed

`RecFacts` collects what the recursor is built from, typed in the environment with the block's
types and constructors at the recursor's levels; `recFacts` derives it from `VInductDecl.WF`.
From it, `recType_isType` types each recursor binder by binder: the motives
(`motives_isTele`), the minor premises (`minors_isTele`, from `minor_ih` and `minor_concl`), the
indices and major premise, and the conclusion.

Each piece is typed by moving a judgment from the context it was stated in (the parameters, the
fields before it, a recursive field's binders) to the context the recursor uses, by a lift
(`Ctx.SubstEq.ofLift'`), and by instantiating a telescope with arguments
(`HasType.appN_substT`, `HasType.appN_invT`); the remaining work is equalities of substitutions,
which `subst_ext` decides by cases on the variable.
-/

namespace Lean4Lean
open VExpr

theorem VLevel.params_inst {ls : List VLevel} {n} (h : ls.length = n) :
    (VLevel.params n).map (VLevel.inst ls) = ls := by
  subst h; apply List.ext_getElem (by simp)
  intro i h1 h2; simp [VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD, h2]

namespace VExpr

theorem liftN_foralls (n : Nat) : ∀ (As : List VExpr) (B : VExpr) (k : Nat),
    (VExpr.foralls As B).liftN n k = .foralls (liftTele n As k) (B.liftN n (k + As.length))
  | [], B, k => by simp [liftTele]
  | A :: As, B, k => by
    simp only [foralls_cons, liftN, liftTele, liftN_foralls n As B (k + 1), List.length_cons]
    rw [Nat.add_right_comm k 1, Nat.add_assoc]

theorem instL_foralls (ls : List VLevel) : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.foralls As B).instL ls = .foralls (As.map (·.instL ls)) (B.instL ls)
  | [], _ => rfl
  | _ :: As, B => by simp [instL, instL_foralls ls As B]

theorem instL_bvars (ls : List VLevel) (n j : Nat) : (bvars n j).map (·.instL ls) = bvars n j := by
  simp [bvars, instL]

theorem bvars_liftN (n j k : Nat) : (bvars n j).map (·.liftN k) = bvars n (j + k) := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  congr 1; funext a; simp; omega

theorem bvars_liftN_hi (n j k c : Nat) (h : c ≤ j) :
    (bvars n j).map (·.liftN k c) = bvars n (j + k) := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  congr 1; funext a; simp; split <;> omega

theorem bvars_subst_ofLift (n j : Nat) (ρ : Lift) :
    (bvars n j).map (·.subst (.ofLift ρ)) = (List.range n).reverse.map fun i => .bvar (ρ.liftVar (i + j)) := by
  simp [bvars]

theorem bvars_map_subst (σ : Subst) (n j : Nat) :
    (bvars n j).map (·.subst σ) = (List.range n).reverse.map fun i => σ (i + j) := by
  simp [bvars]

theorem bvars_subst_skipN (n j a : Nat) :
    (bvars n j).map (·.subst (.ofLift (.skipN .refl a))) = bvars n (j + a) := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, Subst.ofLift_apply,
    Lift.liftVar_skipN, Lift.liftVar]
  apply List.map_congr_left; intro i _; congr 1; omega

end VExpr

namespace VInductDecl
variable {d : VInductDecl}

theorem recLevels_length : d.recLevels.length = d.uvars := by
  unfold recLevels; split <;> simp [VLevel.params]

theorem recLevels_WF : ∀ l ∈ d.recLevels, l.WF d.recUVars := by
  unfold recLevels recUVars
  split
  · simp [VLevel.WF]
  · exact VLevel.params_wf

theorem motiveLevel_WF : d.motiveLevel.WF d.recUVars := by
  unfold motiveLevel recUVars; split <;> simp [VLevel.WF]

theorem params_instL_recLevels : (VLevel.params d.uvars).map (VLevel.inst d.recLevels) = d.recLevels :=
  VLevel.params_inst recLevels_length

theorem mem_ctors_iff {j c} : (j, c) ∈ d.ctors ↔ ∃ T, d.types[j]? = some T ∧ c ∈ T.ctors := by
  simp only [ctors, List.mem_flatten, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨_, ⟨⟨T, i⟩, hT, rfl⟩, hc⟩
    obtain ⟨c', hc', ⟨⟩⟩ := List.mem_map.1 hc
    exact ⟨T, by simpa using hT, hc'⟩
  · rintro ⟨T, hT, hc⟩
    exact ⟨_, ⟨⟨T, j⟩, by simpa using hT, rfl⟩, List.mem_map.2 ⟨c, hc, rfl⟩⟩

theorem FieldsWF.tele {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    env.IsTele d.uvars Γ (fs.map (·.type)) ∧ env.TeleDefEq d.uvars Γ Ds (fs.map (·.type)) := by
  induction H with
  | nil => exact ⟨.nil, .nil⟩
  | cons h1 h2 _ _ _ _ _ ih => exact ⟨.cons ⟨_, h2⟩ ih.1, .cons h1 ih.2⟩

theorem FieldsWF.recArg {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i f, fs[i]? = some f →
      d.RecArgWF env (((fs.take i).map (·.type)).reverse ++ Γ) (k + i) f := by
  induction H with
  | nil => simp
  | cons _ _ _ _ _ h6 _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using h6
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons, Nat.add_right_comm, Nat.add_assoc] using this

theorem FieldsWF.length {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    Ds.length = fs.length := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

theorem FieldsWF.defeq {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i D f, Ds[i]? = some D → fs[i]? = some f →
      env.IsDefEqU d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) D f.type := by
  induction H with
  | nil => simp
  | cons h1 _ _ _ _ _ _ ih =>
    intro i D f hD hf
    cases i with
    | zero => simp at hD hf; subst hD hf; simpa using h1
    | succ i =>
      have := ih i D f (by simpa using hD) (by simpa using hf)
      simpa [List.take_succ_cons] using this

theorem FieldsWF.level {env : VEnv} {Γ k Ds fs} (H : d.FieldsWF env Γ k Ds fs) :
    ∀ i f, fs[i]? = some f →
      env.HasType d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) f.type (.sort f.level) := by
  induction H with
  | nil => simp
  | cons _ h2 _ _ _ _ _ ih =>
    intro i f hf
    cases i with
    | zero => simp at hf; subst hf; simpa using h2
    | succ i =>
      have := ih i f (by simpa using hf)
      simpa [List.take_succ_cons] using this

end VInductDecl
end Lean4Lean

namespace Lean4Lean
namespace VInductDecl
open VExpr
variable {d : VInductDecl}

/-- The pieces of a well-formed declaration the recursor is built from, typed in the environment
with its types and constructors, at the recursor's levels. `type` and `ctor` state the block's own
types and constructors as constants; `typeHead` and `ctorHead` state every type the recursors
range over, auxiliary ones included, at the parameters as variables. -/
structure RecFacts (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) : Prop where
  wf : env.WF
  params : env.IsTele U [] (d.params.map (·.instL ls))
  indices : ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (T.indices.map (·.instL ls))
  type : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.HasType U [] (.const T.name ls)
      (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
        (.sort (d.level.inst ls)))
  fields : ∀ {j : Nat} {c : VConstructor}, (j, c) ∈ d.allCtors →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (c.fields.map (·.type.instL ls))
  ctor : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.ctors →
    d.types[j]? = some T →
    c.indices.length = T.indices.length ∧
    env.HasType U [] (.const c.name ls)
      (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
        (.appN (.const T.name ls)
          (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls))))
  recArg : ∀ {j : Nat} {c : VConstructor} {k : Nat} {f : VField} {ra : VRecArg},
    (j, c) ∈ d.allCtors → c.fields[k]? = some f → f.recArg = some ra →
    ∃ T, d.allTypes[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
        (d.params.map (·.instL ls)).reverse)
      (f.type.instL ls)
      (.foralls (ra.binders.map (·.instL ls)) (T.typeApp ls
        (bvars d.params.length (k + ra.binders.length)) (ra.indices.map (·.instL ls))))
  typeHead : ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.HasType U (d.params.map (·.instL ls)).reverse (T.typeHead ls (bvars d.params.length 0))
      (.foralls (T.indices.map (·.instL ls)) (.sort (d.level.inst ls)))
  ctorHead : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.allCtors →
    d.allTypes[j]? = some T →
    c.indices.length = T.indices.length ∧
    env.HasType U (d.params.map (·.instL ls)).reverse (T.ctorHead c ls (bvars d.params.length 0))
      (.foralls (c.fields.map (·.type.instL ls))
        (T.typeApp ls (bvars d.params.length c.fields.length) (c.indices.map (·.instL ls))))

theorem _root_.Lean4Lean.VExpr.bvars_liftN_lo (n j k c : Nat) (h : n + j ≤ c) :
    (bvars n j).map (·.liftN k c) = bvars n j := by
  simp only [bvars, List.map_map, Function.comp_def, liftN, liftVar]
  apply List.map_congr_left; intro a ha
  simp only [List.mem_reverse, List.mem_range] at ha
  simp; omega

variable (d) in
/-- `T`'s motive type under the parameters alone: `motiveType` lifts it past the motives before
it. -/
def genMotive (ls : List VLevel) (v : VLevel) (T : VInductiveType) : VExpr :=
  .foralls (T.indices.map (·.instL ls)) <| .forallE
    (T.typeApp ls (bvars d.params.length T.indices.length) (bvars T.indices.length 0)) (.sort v)

theorem _root_.Lean4Lean.VInductiveType.typeApp_liftN (T : VInductiveType) (ls : List VLevel)
    (ps idx : List VExpr) (n k : Nat) :
    (T.typeApp ls ps idx).liftN n k = T.typeApp ls (ps.map (·.liftN n k)) (idx.map (·.liftN n k)) := by
  simp only [liftN_eq_subst, VInductiveType.typeApp_subst]

theorem _root_.Lean4Lean.VInductiveType.typeApp_lift' (T : VInductiveType) (ls : List VLevel)
    (ps idx : List VExpr) (ρ : Lift) :
    (T.typeApp ls ps idx).lift' ρ = T.typeApp ls (ps.map (·.lift' ρ)) (idx.map (·.lift' ρ)) := by
  simp only [lift'_eq_subst, VInductiveType.typeApp_subst]

theorem _root_.Lean4Lean.VInductiveType.ctorApp_liftN (T : VInductiveType) (c : VConstructor)
    (ls : List VLevel) (ps fs : List VExpr) (n k : Nat) :
    (T.ctorApp c ls ps fs).liftN n k =
      T.ctorApp c ls (ps.map (·.liftN n k)) (fs.map (·.liftN n k)) := by
  simp only [liftN_eq_subst, VInductiveType.ctorApp_subst]

theorem motiveType_eq {ls v j T} : d.motiveType ls v j T = (d.genMotive ls v T).liftN j := by
  simp only [motiveType, genMotive, liftN_foralls, Nat.zero_add, List.length_map, liftN,
    VInductiveType.typeApp_liftN, bvars_liftN_hi _ _ _ _ (Nat.le_refl _), Nat.add_comm j]
  rw [bvars_liftN_lo _ _ _ _ (by simp)]

/-- A motive applied to indices and to a major premise of its type at them is a type. -/
theorem motiveApp {env : VEnv} {U ls v T Γ Δ M τ idx x}
    (hM : env.HasType U Γ M ((d.genMotive ls v T).subst τ))
    (hidx : VEnv.Ctx.SubstEq env U Γ (τ.consList idx) (τ.consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ Δ))
    (hlen : idx.length = T.indices.length)
    (hx : env.HasType U Γ x (T.typeApp ls ((bvars d.params.length 0).map (·.subst τ)) idx)) :
    env.HasType U Γ (.app (.appN M idx) x) (.sort v) := by
  have h1 := VEnv.HasType.appN_substT (As := T.indices.map (·.instL ls)) hM (by simp [hlen]) hidx
  simp only [subst, VInductiveType.typeApp_subst] at h1
  rw [← hlen, subst_bvars_consList, show bvars d.params.length idx.length =
    bvars d.params.length (0 + idx.length) by rw [Nat.zero_add], subst_bvars_consList_ge] at h1
  exact h1.app hx

theorem _root_.Lean4Lean.Ctx.Lift'.skipN_append {ρ : Lift} {Γ Γ' : List VExpr} (W : Ctx.Lift' ρ Γ Γ') :
    ∀ As : List VExpr, Ctx.Lift' (ρ.skipN As.length) Γ (As ++ Γ')
  | [] => W
  | _ :: As => .skip (Ctx.Lift'.skipN_append W As)

theorem getElem_motiveTypes {ls v} {j : Nat} {T : VInductiveType} (hj : d.allTypes[j]? = some T) :
    ∃ h, (d.motiveTypes ls v)[j]'h = d.motiveType ls v j T := by
  have hlt : j < d.allTypes.length := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨by simp [motiveTypes, hlt], ?_⟩
  simp only [motiveTypes, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.1 hj).2]

@[simp] theorem length_motiveTypes {ls v} : (d.motiveTypes ls v).length = d.allTypes.length := by
  simp [motiveTypes]

theorem _root_.Lean4Lean.Lift.liftVar_consN {ρ : Lift} :
    ∀ {k i : Nat}, (ρ.consN k).liftVar i = if i < k then i else ρ.liftVar (i - k) + k
  | 0, i => by simp
  | k + 1, 0 => by simp
  | k + 1, i + 1 => by
    simp only [Lift.consN, Lift.liftVar, Lift.liftVar_consN (k := k) (i := i)]
    split <;> split <;> first | omega | (simp; omega)

theorem _root_.Lean4Lean.VExpr.Subst.consList_bvars_apply (σ : Subst) (n k i : Nat) :
    σ.consList (bvars n k) i = if i < n then .bvar (i + k) else σ (i - n) := by
  rw [Subst.consList_bvars]

theorem _root_.Lean4Lean.VExpr.Subst.consList_lift_r (ρ : Lift) :
    ∀ (σ : Subst) (as : List VExpr),
      (σ.consList as).lift_r ρ = (σ.lift_r ρ).consList (as.map (·.lift' ρ))
  | σ, [] => rfl
  | σ, a :: as => by
    show ((σ.cons a).consList as).lift_r ρ = _
    rw [VExpr.Subst.consList_lift_r ρ (σ.cons a) as]
    show _ = ((σ.lift_r ρ).cons (a.lift' ρ)).consList _
    congr 1; funext i; cases i <;> rfl

/-- Two substitutions agree, by cases on the variable. -/
macro "subst_ext" : tactic => `(tactic| (
  funext i
  simp [Subst.consList_append, Subst.consList_bvars_apply, Lift.liftVar_skipN,
    Lift.liftVar_consN, Lift.liftVar_comp, Subst.lift_r, Subst.lift_l, Subst.comp, liftVar]
  (repeat' split) <;> (try simp only [VExpr.bvar.injEq]) <;> omega))

theorem _root_.Lean4Lean.VExpr.closed_subst {env : VEnv} {U e A} (henv : env.Ordered)
    (h : env.HasType U [] e A) (σ : Subst) : A.subst σ = A := by
  have ⟨_, hA⟩ := VEnv.IsDefEq.isType henv (Γ := []) trivial h
  exact (hA.closedN henv trivial).subst_eq Subst.Fixes.zero

theorem reseat_eq_subst (e : VExpr) (a k m b l : Nat) (h : k ≤ m) :
    e.reseat a k m b l =
      e.subst (.ofLift (.consN (.skipN (.consN (.skipN .refl a) k) (m - k + b)) l)) := by
  simp only [reseat]
  rw [liftN_eq_subst, liftN_eq_subst, subst_subst]; congr 1; funext i
  simp [Subst.comp, Lift.liftVar_skipN, Lift.liftVar_consN]
  (repeat' split) <;> omega

theorem _root_.Lean4Lean.VExpr.liftTele_append (n : Nat) : ∀ (As Bs : List VExpr) (k : Nat),
    liftTele n (As ++ Bs) k = liftTele n As k ++ liftTele n Bs (k + As.length)
  | [], _, _ => rfl
  | A :: As, Bs, k => by
    simp only [List.cons_append, liftTele, liftTele_append n As Bs (k + 1), List.length_cons]
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem _root_.Lean4Lean.VExpr.liftTele'_eq_zipIdx : ∀ (ρ : Lift) (As : List VExpr),
    liftTele' ρ As = As.zipIdx.map fun (A, i) => A.lift' (ρ.consN i)
  | _, [] => rfl
  | ρ, A :: As => by
    simp only [liftTele', List.zipIdx_cons, List.map_cons, Lift.consN, Nat.zero_add]
    rw [liftTele'_eq_zipIdx ρ.cons As, List.zipIdx_succ, List.map_map]
    congr 1; apply List.map_congr_left; rintro ⟨B, i⟩ _
    simp only [Function.comp_apply]
    rw [show ρ.cons = ρ.consN 1 from rfl, Lift.consN_consN, Nat.add_comm]

theorem _root_.Lean4Lean.VEnv.IsTele.getElem {env : VEnv} {U : Nat} : ∀ {Γ As}, env.IsTele U Γ As →
    ∀ i (h : i < As.length), env.IsType U ((As.take i).reverse ++ Γ) As[i]
  | _, _ :: _, .cons hA _, 0, _ => hA
  | _, _ :: _, .cons _ t, i + 1, h => by
    simpa [List.take_succ_cons] using VEnv.IsTele.getElem t i (by simpa using h)

/-- A type the recursors range over, at parameters given by a substitution and at indices
instantiating its index telescope. -/
theorem RecFacts.typeApp_typing {env : VEnv} {U : Nat} {ls : List VLevel} (hF : d.RecFacts env U ls)
    {t : Nat} {T : VInductiveType} (ht : d.allTypes[t]? = some T) {Γ : List VExpr} {ρ : Lift}
    {idx : List VExpr} (Wl : Ctx.Lift' ρ (d.params.map (·.instL ls)).reverse Γ)
    (W : VEnv.Ctx.SubstEq env U Γ ((Subst.ofLift ρ).consList idx) ((Subst.ofLift ρ).consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    (hlen : idx.length = T.indices.length) :
    env.HasType U Γ (T.typeApp ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ))) idx)
      (.sort (d.level.inst ls)) := by
  have h1 := (hF.typeHead ht).weak' hF.wf.ordered Wl
  rw [lift'_eq_subst, lift'_eq_subst, VInductiveType.typeHead_subst] at h1
  have h2 := VEnv.HasType.appN_substT (Δ := (d.params.map (·.instL ls)).reverse) h1
    (by simp [hlen]) W
  rw [VInductiveType.typeApp_eq]; exact h2

/-- A constructor the recursors' minor premises range over, at parameters given by a substitution
and at fields instantiating its field telescope. -/
theorem RecFacts.ctorApp_typing {env : VEnv} {U : Nat} {ls : List VLevel} (hF : d.RecFacts env U ls)
    {j : Nat} {c : VConstructor} {T : VInductiveType} (hc : (j, c) ∈ d.allCtors)
    (hj : d.allTypes[j]? = some T) {Γ : List VExpr} {ρ : Lift} {fs : List VExpr}
    (Wl : Ctx.Lift' ρ (d.params.map (·.instL ls)).reverse Γ)
    (W : VEnv.Ctx.SubstEq env U Γ ((Subst.ofLift ρ).consList fs) ((Subst.ofLift ρ).consList fs)
      ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    (hlen : fs.length = c.fields.length) :
    env.HasType U Γ (T.ctorApp c ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ))) fs)
      (T.typeApp ls ((bvars d.params.length 0).map (·.subst (.ofLift ρ)))
        ((c.indices.map (·.instL ls)).map (·.subst ((Subst.ofLift ρ).consList fs)))) := by
  have h1 := (hF.ctorHead hc hj).2.weak' hF.wf.ordered Wl
  rw [lift'_eq_subst, lift'_eq_subst, VInductiveType.ctorHead_subst] at h1
  have h2 := VEnv.HasType.appN_substT (Δ := (d.params.map (·.instL ls)).reverse) h1
    (by simp [hlen]) W
  rw [VInductiveType.typeApp_subst, ← hlen, show bvars d.params.length fs.length =
    bvars d.params.length (0 + fs.length) by rw [Nat.zero_add], subst_bvars_consList_ge] at h2
  rw [VInductiveType.ctorApp_eq]; exact h2

theorem ctorAppAt_eq {j : Nat} {T : VInductiveType} (hj : d.allTypes[j]? = some T)
    (c : VConstructor) (ls : List VLevel) (ps fs : List VExpr) :
    d.ctorAppAt j c ls ps fs = T.ctorApp c ls ps fs := by
  simp [ctorAppAt, hj]

section
variable {U : Nat} {ls : List VLevel} {v : VLevel}
set_option hygiene false
local notation "𝐔" => U
local notation "𝐥" => ls
local notation "𝐯" => v
local notation "𝐏" => (d.params.map (·.instL ls))
local notation "𝐌" => (d.motiveTypes ls v)
local notation "𝐧" => d.params.length
local notation "𝐓" => d.allTypes.length
local notation "𝐂" => d.allCtors.length
local notation "𝐅" => (c.fields.map (·.type.instL ls))
local notation "𝐦" => c.fields.length
local notation "𝐮" => c.recFields.length

/-- A motive, as a variable below the binders `Δ`. -/
theorem motive_var {env : VEnv} {t : Nat} {T : VInductiveType} (ht : d.allTypes[t]? = some T)
    (Δ : List VExpr) :
    env.HasType 𝐔 (Δ ++ 𝐌.reverse ++ 𝐏.reverse) (.bvar (Δ.length + (𝐓 - 1 - t)))
      ((d.genMotive 𝐥 𝐯 T).subst (.ofLift (.skipN .refl (Δ.length + 𝐓)))) := by
  obtain ⟨htlt', hMt⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) ht
  have htlt : t < 𝐓 := (List.getElem?_eq_some_iff.1 ht).1
  have h2 := Lookup.append_left Δ (Lookup.reverse_append 𝐌 (Γ := 𝐏.reverse) t htlt')
  rw [hMt, motiveType_eq, liftN_liftN, liftN_liftN, length_motiveTypes] at h2
  rw [show t + (𝐓 - t + Δ.length) = Δ.length + 𝐓 by omega, liftN_eq_subst] at h2
  simpa using VEnv.HasType.bvar (env := env) (U := 𝐔) h2

/-- The context of a minor premise's body, as a lift of the context of its first `k'` fields. -/
theorem fieldsLift {c : VConstructor} {q k' : Nat} (Qs' Extra : List VExpr) (hq : Qs'.length = q)
    (hk' : k' ≤ 𝐦) :
    Ctx.Lift' (.skipN (.consN (.skipN .refl (𝐓 + q)) k') (𝐦 - k' + Extra.length))
      (((c.fields.take k').map (·.type.instL 𝐥)).reverse ++ 𝐏.reverse)
      (Extra.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
  have h1 : Ctx.Lift' (.skipN .refl (𝐓 + q)) 𝐏.reverse (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) (Qs'.reverse ++ 𝐌.reverse)
    simpa [hq, Nat.add_comm] using this
  have h2 := Ctx.Lift'.tele ((c.fields.take k').map (·.type.instL 𝐥)) h1
  have h3 := Ctx.Lift'.skipN_append h2
    (Extra.reverse ++ (liftTele (𝐓 + q) ((c.fields.drop k').map (·.type.instL 𝐥)) k').reverse)
  have hF : 𝐅 = (c.fields.take k').map (·.type.instL 𝐥) ++ (c.fields.drop k').map (·.type.instL 𝐥) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hF, liftTele_append]
  simp only [List.length_append, List.length_reverse, List.length_map, Nat.zero_add,
    List.length_drop, List.length_take, Nat.min_eq_left hk', liftTele_eq_liftTele',
    List.reverse_append, List.append_assoc, Lift.consN, length_liftTele'] at h3 ⊢
  rwa [Nat.add_comm Extra.length] at h3

local notation "𝐁" => (ra.binders.map (·.instL ls))
local notation "𝐛" => ra.binders.length
local notation "𝐊" => (((c.fields.take k).map (·.type.instL ls)).reverse ++ 𝐏.reverse)
local notation "𝐱𝐬" => (ra.binders.zipIdx.map fun (A, i) =>
  (A.instL ls).reseat (d.allTypes.length + q) k c.fields.length r i)
local notation "𝐢𝐝𝐱" => (ra.indices.map fun e =>
  (e.instL ls).reseat (d.allTypes.length + q) k c.fields.length r ra.binders.length)
local notation "ρk" => (Lift.skipN (.consN (.skipN .refl (d.allTypes.length + q)) k)
  (c.fields.length - k + r))

theorem mem_recFields {c : VConstructor} {k : Nat} {ra : VRecArg} (h : (k, ra) ∈ c.recFields) :
    ∃ f, c.fields[k]? = some f ∧ f.recArg = some ra := by
  simp only [VConstructor.recFields, List.mem_filterMap] at h
  obtain ⟨⟨f, k'⟩, hm, he⟩ := h
  cases hr : f.recArg <;> simp [hr] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨f, (List.mem_zipIdx_iff_getElem?.1 hm), hr⟩

theorem genMotive_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {t : Nat}
    {T : VInductiveType} (ht : d.allTypes[t]? = some T) : env.IsType 𝐔 𝐏.reverse (d.genMotive 𝐥 𝐯 T) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hI := hF.indices ht
  have hIP : OnCtx ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) := hI.onCtx hPP
  refine hI.foralls (.forallE ?_ ⟨_, .sort hv⟩)
  have hWI : Ctx.Lift' (.skipN .refl T.indices.length) 𝐏.reverse
      ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    simpa using Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      (T.indices.map (·.instL 𝐥)).reverse
  have heq : (Subst.ofLift (.skipN .refl T.indices.length)).consList
      (bvars T.indices.length 0) = .ofLift .refl := by subst_ext
  have h := hF.typeApp_typing ht hWI (idx := bvars T.indices.length 0)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv .refl hIP) (by simp)
  rw [bvars_subst_skipN, Nat.zero_add] at h
  exact ⟨_, h⟩

theorem motives_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) :
    env.IsTele 𝐔 𝐏.reverse 𝐌 := by
  have henv := hF.wf.ordered
  apply VEnv.IsTele.of_getElem
  intro i hi
  have hi' : i < 𝐓 := by simpa using hi
  obtain ⟨_, hMi⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) (List.getElem?_eq_getElem hi')
  rw [hMi, motiveType_eq]
  exact (genMotive_isType hF hv (List.getElem?_eq_getElem hi')).weakN henv
    (.zero _ (by simp [Nat.min_eq_left (Nat.le_of_lt hi')]))

@[simp] theorem length_minorTypes {ls} : (d.minorTypes ls).length = 𝐂 := by simp [minorTypes]

/-- The recursor's indices, over its binders, lift the type's index telescope. -/
theorem recIndicesLift {i : Nat} {Ti : VInductiveType} (_hi : d.allTypes[i]? = some Ti) :
    Ctx.Lift' (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)
      ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hWI := Ctx.Lift'.tele (Ti.indices.map (·.instL 𝐥)) hW0
  simp only [List.length_map] at hWI
  simpa only [List.append_assoc] using hWI

/-- The recursor's major premise, the type applied to the parameters and indices, over the
recursor's binders and the indices. -/
theorem major_type {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {i : Nat} {Ti : VInductiveType}
    (hi : d.allTypes[i]? = some Ti) :
    env.HasType 𝐔 ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (Ti.typeApp 𝐥 (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length)) (bvars Ti.indices.length 0))
      (.sort (d.level.inst 𝐥)) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hIP : OnCtx ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    (hF.indices hi).onCtx hPP
  have hWP : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂 + Ti.indices.length)) 𝐏.reverse
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have heq : (Subst.ofLift (.skipN .refl (𝐓 + 𝐂 + Ti.indices.length))).consList
      (bvars Ti.indices.length 0) =
      .ofLift (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length) := by subst_ext
  have h := hF.typeApp_typing hi hWP (idx := bvars Ti.indices.length 0)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv (recIndicesLift (d := d) hi) hIP)
    (by simp)
  rwa [bvars_subst_skipN, Nat.zero_add] at h

theorem bvars_subst_cons (σ : Subst) (x : VExpr) (n k : Nat) :
    (bvars n (k + 1)).map (·.subst (σ.cons x)) = (bvars n k).map (·.subst σ) := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, ← Nat.add_assoc]; rfl

/-- The recursors, as terms `rc t` of their types. -/
def RecTyped (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) (v : VLevel)
    (rc : Nat → VExpr) : Prop :=
  ∀ {t : Nat} {T : VInductiveType}, d.allTypes[t]? = some T →
    env.HasType U [] (rc t) (d.recType ls v t T)

theorem _root_.Lean4Lean.VExpr.bvars_append (a b k : Nat) :
    bvars a (b + k) ++ bvars b k = bvars (a + b) k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [bvars, List.getElem_append, List.length_map, List.length_reverse, List.length_range,
    List.getElem_map, List.getElem_reverse, List.getElem_range]
  split <;> (congr 1; omega)

theorem _root_.Lean4Lean.VExpr.liftTele'_liftTele' : ∀ (ρ ρ' : Lift) (As : List VExpr),
    liftTele' ρ (liftTele' ρ' As) = liftTele' (ρ'.comp ρ) As
  | _, _, [] => rfl
  | ρ, ρ', A :: As => by
    simp only [liftTele', ← lift'_comp, liftTele'_liftTele' ρ.cons ρ'.cons As]; rfl

/-- Instantiating the inductive hypotheses before a minor premise's `r`th one, and lifting its
fields past the minor premises after it, moves a term reseated for the minor premise to one
reseated for the iota rule. -/
theorem reseat_subst_iota (e : VExpr) {a k m r i C q : Nat} (L : List VExpr) (hL : L.length = r)
    (hk : k ≤ m) (hqC : q ≤ C) :
    (e.reseat (a + q) k m r i).subst
      ((((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i) =
      e.reseat (a + C) k m 0 i := by
  rw [show (Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0) =
    .ofLift (.consN (.skipN .refl (C - q)) m) by subst_ext]
  rw [reseat_eq_subst _ _ _ _ _ _ hk, reseat_eq_subst _ _ _ _ _ _ hk, subst_subst]
  congr 1; funext p
  simp only [Subst.comp, Subst.ofLift_apply, subst_bvar, Subst.liftN_apply,
    Subst.consList_apply, Lift.liftVar_consN, Lift.liftVar_skipN, Lift.liftVar, hL]
  (repeat' split) <;> (try simp only [VExpr.liftN, liftVar, VExpr.bvar.injEq]) <;>
    (repeat' split) <;> omega

theorem bvar_subst_iota {m r i C q x : Nat} (L : List VExpr) (hL : L.length = r) (hqC : q ≤ C)
    (hx : i + r ≤ x) :
    (((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i x =
      .bvar (if x < i + r + m then x - r else x - r + (C - q)) := by
  rw [show (Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0) =
    .ofLift (.consN (.skipN .refl (C - q)) m) by subst_ext]
  simp only [Subst.liftN_apply, Subst.consList_apply, Subst.ofLift_apply,
    Lift.liftVar_consN, Lift.liftVar_skipN, Lift.liftVar, hL]
  (repeat' split) <;> (try simp only [VExpr.liftN, liftVar, VExpr.bvar.injEq]) <;>
    (repeat' split) <;> omega

theorem bvars_subst_iota {m i C q : Nat} (L : List VExpr) :
    (bvars i 0).map (·.subst
      ((((Subst.ofLift (.skipN .refl (C - q + m))).consList (bvars m 0)).consList L).liftN i)) =
      bvars i 0 := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, Subst.liftN_apply, Nat.add_zero]
  apply List.map_congr_left; intro x hx
  simp only [List.mem_reverse, List.mem_range] at hx
  simp [hx]

end

theorem RecFacts.mono {env env' : VEnv} {U ls} (H : d.RecFacts env U ls) (hle : env ≤ env')
    (hwf : env'.WF) : d.RecFacts env' U ls where
  wf := hwf
  params := H.params.mono hle
  indices h := (H.indices h).mono hle
  type h := (H.type h).mono hle
  fields h := (H.fields h).mono hle
  ctor h1 h2 := let ⟨a, b⟩ := H.ctor h1 h2; ⟨a, b.mono hle⟩
  recArg h1 h2 h3 := let ⟨T, a, b, c⟩ := H.recArg h1 h2 h3; ⟨T, a, b, c.mono hle⟩
  typeHead h := (H.typeHead h).mono hle
  ctorHead h1 h2 := let ⟨a, b⟩ := H.ctorHead h1 h2; ⟨a, b.mono hle⟩

end VInductDecl
end Lean4Lean

namespace Lean4Lean
open VExpr

/-- The constant a recorded block's constructor is declared as. -/
theorem VEnv.WF.ctor_constant {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    (hs : env.inducts s = some (d, t)) {j : Nat} {c : VConstructor} (hjc : (j, c) ∈ d.ctors) :
    env.constants c.name = some ⟨d.uvars, c.type⟩ := by
  obtain ⟨env₀, env₂, -, -, hadd, hle, -⟩ := henv.inducts_block hs
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := hadd
  exact ((VEnv.addConstList_le hR).trans <| VEnv.addDefEqList_le.trans <|
    (VEnv.addBlock_le hB).trans hle).constants
    (VEnv.addConstList_constants_of_mem hC (List.mem_map.2 ⟨(j, c), hjc, rfl⟩))

theorem VExpr.foralls_inj : ∀ {As As' : List VExpr} {B B' : VExpr},
    VExpr.foralls As B = .foralls As' B' → As.length = As'.length → As = As' ∧ B = B'
  | [], [], _, _, h, _ => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, h, hl => by
    simp only [foralls_cons, forallE.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := VExpr.foralls_inj h (by simpa using hl)
    exact ⟨rfl, rfl⟩

theorem VExpr.subst_dflt_bvars_of_closed {e : VExpr} {n : Nat} (h : e.ClosedN n) :
    e.subst (Subst.dflt.consList (bvars n 0)) = e := by
  rw [h.subst_congr (σ' := Subst.id) fun i hi => by
    simp [Subst.consList_bvars_apply, hi, Subst.id], subst_id]

namespace VInductDecl
variable {d : VInductDecl}

theorem _root_.Lean4Lean.VEnv.TeleDefEq.length_eq {env : VEnv} {U : Nat} :
    ∀ {Γ As Bs : List VExpr}, env.TeleDefEq U Γ As Bs → As.length = Bs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => congrArg (· + 1) h.length_eq

/-- A closed term over a telescope of parameters, applied to them as variables. -/
theorem _root_.Lean4Lean.VEnv.HasType.appN_params {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Ps Is : List VExpr} {e S : VExpr} (hP : env.IsTele U [] Ps)
    (h : env.HasType U [] e (.foralls (Ps ++ Is) S)) :
    env.HasType U Ps.reverse (.appN e (bvars Ps.length 0)) (.foralls Is S) := by
  have hPP : OnCtx Ps.reverse (env.IsType U) := by simpa using hP.onCtx trivial
  have hf0 := h.weak0 henv (Γ := Ps.reverse)
  rw [← closed_subst henv h (.ofLift (.skipN .refl Ps.length)), foralls_append] at hf0
  have heq : (Subst.ofLift (.skipN .refl Ps.length)).consList (bvars Ps.length 0) =
      .ofLift .refl := by subst_ext
  have := VEnv.HasType.appN_substT (Δ := []) (As := Ps) (as := bvars Ps.length 0) hf0 (by simp)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv .refl hPP)
  rwa [heq, ← lift'_eq_subst, lift'_refl] at this

theorem allTypes_cases {t : Nat} {T : VInductiveType} (h : d.allTypes[t]? = some T) :
    d.types[t]? = some T ∨ T ∈ d.aux := by
  by_cases ht : t < d.types.length
  · rw [allTypes, List.getElem?_append_left ht] at h; exact .inl h
  · rw [allTypes, List.getElem?_append_right (by omega)] at h; exact .inr (List.mem_of_getElem? h)

end VInductDecl
end Lean4Lean

namespace Lean4Lean
open VExpr

/-- Each argument of a telescope's substitution, typed against its entry instantiated by the
arguments before it. -/
theorem VEnv.Ctx.SubstEq.getElem {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {σ : Subst} :
    ∀ (n : Nat) {As as : List VExpr}, as.length = n →
    VEnv.Ctx.SubstEq env U Γ (σ.consList as) (σ.consList as) (As.reverse ++ Δ) →
    as.length = As.length → ∀ r (h : r < as.length) (h' : r < As.length),
      env.HasType U Γ as[r] (As[r].subst (σ.consList (as.take r)))
  | 0, _, as, hn, _, _, r, h, _ => by simp [List.eq_nil_of_length_eq_zero hn] at h
  | n + 1, As, as, hn, W, hlen, r, h, h' => by
    obtain ⟨as, a, rfl⟩ : ∃ as' a, as = as' ++ [a] := by
      simpa using (List.eq_nil_or_concat as).resolve_left (by rintro rfl; simp at hn)
    obtain ⟨As, A, rfl⟩ : ∃ As' A, As = As' ++ [A] := by
      simpa using (List.eq_nil_or_concat As).resolve_left (by rintro rfl; simp at hlen)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [Subst.consList_concat, List.reverse_append] at W
    cases W with | cons W' _ ha =>
    simp only [List.length_append, List.length_singleton] at h h'
    rcases Nat.lt_or_ge r as.length with hr | hr
    · have := VEnv.Ctx.SubstEq.getElem n hn W' hlen r hr (by omega)
      simp only [List.getElem_append_left hr, List.getElem_append_left (show r < As.length by omega),
        List.take_append_of_le_length (Nat.le_of_lt hr)]
      exact this
    · obtain rfl : r = as.length := by omega
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_append_right (show As.length ≤ as.length by omega), List.take_left']
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
      exact ha

/-- Each field of a constructor application, at the type of its sort. -/
theorem VEnv.WF.ctorApp_fieldType {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) {As fs : List VExpr}
    (hfs : fs.length = c.fields.length)
    (W : Ctx.SubstEq env U Γ ((Subst.dflt.consList As).consList fs)
      ((Subst.dflt.consList As).consList fs)
      ((c.fields.map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse))
    {j : Nat} {f : VField} (hf : c.fields[j]? = some f) :
    env.HasType U Γ ((f.type.instL ls).subst (Subst.dflt.consList (As ++ fs.take j)))
      (.sort (f.level.inst ls)) := by
  have hF := henv.projFacts hs ht hc
  have hj : j < fs.length := hfs ▸ (List.getElem?_eq_some_iff.1 hf).1
  have WA := VEnv.Ctx.SubstEq.dropList (as := fs) (as' := fs)
    (Bs := c.fields.map (·.type.instL ls)) (by simp [hfs]) (by simp [hfs]) W
  obtain ⟨hFt, hFk⟩ := hF.fields j f hf
  have hFt := hFt.instL hls
  simp only [List.map_reverse] at hFt
  -- the kept fields, as arguments for the kept telescope
  have WK := Ctx.SubstEq.ofGetElem WA (c.keptIdx j j).length
    (as := (c.keptIdx j j).map (fs[·]?.getD default)) (by simp) hFt
    (by simp [VConstructor.keptFields_eq]) fun r h h' => ?_
  · have hFk := hFk.instL hls
    simp only [List.map_append, List.map_reverse] at hFk
    have := hFk.subst henv.ordered WK hΓ
    rwa [← Subst.consList_append, ← c.field_subst_stripped hf (Nat.le_refl _),
      List.map_range_getD_eq_take _ (Nat.le_of_lt hj)] at this
  · simp only [List.length_map] at h
    have hm := List.getElem_mem h
    obtain ⟨hjk, -⟩ := (c.mem_keptIdx).1 hm
    generalize hi : (c.keptIdx j j)[r] = i at hjk
    have hi' : i < fs.length := by omega
    obtain ⟨fi, hfi⟩ : ∃ fi, c.fields[i]? = some fi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have := VEnv.Ctx.SubstEq.getElem fs.length rfl W (by simp [hfs]) i hi' (by simp; omega)
    simp only [List.getElem_map, hi, List.getElem?_eq_getElem hi', Option.getD_some,
      VConstructor.keptFields_eq, hfi, Option.map_some, ← List.map_take,
      VConstructor.keptIdx_take _ _ _ _ h, ← Subst.consList_append]
    rw [← c.field_subst_stripped hfi (Nat.le_of_lt hjk),
      List.map_range_getD_eq_take _ (Nat.le_of_lt hi')]
    simpa [(List.getElem?_eq_some_iff.1 hfi).2, Subst.consList_append] using this

theorem VExpr.projs_take (s : Name) (e : VExpr) {r k : Nat} (h : r ≤ k) :
    (VExpr.projs s k e).take r = VExpr.projs s r e := by
  simp [VExpr.projs, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem List.forall₂_of_getElem? {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ (j : Nat) a b, l₁[j]? = some a → l₂[j]? = some b → R a b) →
    List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, H =>
    .cons (H 0 a b rfl rfl) (List.forall₂_of_getElem? (by simpa using hl)
      fun j a b h₁ h₂ => H (j + 1) a b h₁ h₂)

/-- Both halves of an application are well formed. `app_inv` gives the typings, which is more
than a caller peeling a spine apart wants to name: this is the form that chains. -/
theorem VExpr.WF.app_inv₂ (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) {f a : VExpr}
    (H : VExpr.WF env U Γ (f.app a)) : VExpr.WF env U Γ f ∧ VExpr.WF env U Γ a :=
  let ⟨_, _, hf, ha⟩ := H.app_inv henv hΓ; ⟨⟨_, hf⟩, ⟨_, ha⟩⟩

variable! (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem VExpr.WF.appN_inv : ∀ {vs : List VExpr} {e},
    VExpr.WF env U Γ (e.appN vs) → VExpr.WF env U Γ e
  | [], _, h => h
  | v :: vs, e, h =>
    let ⟨_, _, h, _⟩ := (VExpr.WF.appN_inv (vs := vs) (e := e.app v) h).app_inv henv hΓ
    ⟨_, h⟩

end Lean4Lean

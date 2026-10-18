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

theorem instL_appN (ls : List VLevel) : ∀ (f : VExpr) (as : List VExpr),
    (f.appN as).instL ls = (f.instL ls).appN (as.map (·.instL ls))
  | _, [] => rfl
  | f, a :: as => by simp [instL_appN ls (.app f a) as, instL]

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

end VInductDecl
end Lean4Lean

namespace Lean4Lean
namespace VInductDecl
open VExpr
variable {d : VInductDecl}

/-- The pieces of a well-formed declaration the recursor is built from, typed in the environment
with its types and constructors, at the recursor's levels. -/
structure RecFacts (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) : Prop where
  wf : env.WF
  params : env.IsTele U [] (d.params.map (·.instL ls))
  indices : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (T.indices.map (·.instL ls))
  type : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.HasType U [] (.const T.name ls)
      (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
        (.sort (d.level.inst ls)))
  fields : ∀ {j : Nat} {c : VConstructor}, (j, c) ∈ d.ctors →
    env.IsTele U (d.params.map (·.instL ls)).reverse
      (c.fields.map (·.type.instL ls))
  ctor : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.ctors →
    d.types[j]? = some T →
    c.indices.length = T.indices.length ∧
    env.HasType U [] (.const c.name ls)
      (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
        (.appN (.const T.name ls)
          (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls))))
  recArg : ∀ {j : Nat} {c : VConstructor} {k : Nat} {f : VField} {ra : VRecArg}, (j, c) ∈ d.ctors →
    c.fields[k]? = some f → f.recArg = some ra →
    ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
        (d.params.map (·.instL ls)).reverse)
      (f.type.instL ls)
      (.foralls (ra.binders.map (·.instL ls)) (.appN (.const T.name ls)
        (bvars d.params.length (k + ra.binders.length) ++ ra.indices.map (·.instL ls))))

theorem recFacts {env envT envC : VEnv} (henv : env.WF) (hdecl : d.WF env)
    (hT : env.addConstList d.typeConsts = some envT)
    (hC : envT.addConstList d.ctorConsts = some envC) {U : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars) : d.RecFacts envC U ls := by
  have henvT : envT.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact hdecl.types T hT) hT
  have henvC : envC.WF := VEnv.WF.addConstList henvT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T, hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdecl.ctors envT hT T hT').2 c hc).type) hC
  have hle₁ : env ≤ envT := VEnv.addConstList_le hT
  have hle : envT ≤ envC := VEnv.addConstList_le hC
  have hTW {t : Nat} {T : VInductiveType} (h : d.types[t]? = some T) := hdecl.ctors envT hT T (List.mem_of_getElem? h)
  have hcT {t : Nat} {T : VInductiveType} (h : d.types[t]? = some T) : envC.constants T.name = some ⟨d.uvars, T.type⟩ :=
    hle.constants <| VEnv.addConstList_constants_of_mem hT
      (List.mem_map.2 ⟨T, List.mem_of_getElem? h, rfl⟩)
  have hcC {j : Nat} {c : VConstructor} (h : (j, c) ∈ d.ctors) : envC.constants c.name = some ⟨d.uvars, c.type⟩ :=
    VEnv.addConstList_constants_of_mem hC (List.mem_map.2 ⟨(j, c), h, rfl⟩)
  -- the shape of a constructor's type, in `envT` at the block's own levels
  have hshape {j : Nat} {c : VConstructor} {T : VInductiveType} (hc : (j, c) ∈ d.ctors) (hj : d.types[j]? = some T) :
      envT.IsTele d.uvars d.params.reverse (c.fields.map (·.type)) ∧
      envT.IsDefEqU d.uvars [] c.type (.foralls (d.params ++ c.fields.map (·.type))
        (.appN (.const T.name (VLevel.params d.uvars))
          (bvars d.params.length c.fields.length ++ c.indices))) := by
    obtain ⟨T', hT', hcm⟩ := mem_ctors_iff.1 hc
    cases hj.symm.trans hT'
    have hcW := (hTW hj).2 c hcm
    obtain ⟨ps, Ds, hty, hps, hfs⟩ := hcW.shape
    have ⟨htele, hdeq⟩ := FieldsWF.tele hfs
    refine ⟨htele, ?_⟩
    have hP : envT.IsTele d.uvars [] d.params := hdecl.params.mono hle₁
    have hTD := hps.append (by simpa using hdeq)
    have hcty := hcW.type
    rw [hty] at hcty ⊢
    have ⟨_, hR⟩ := VEnv.IsType.foralls_inv henvT.ordered hcty
    refine hTD.foralls henvT trivial (hP.append (by simpa using htele)) ?_
    have hctx := hTD.defeqCtx henvT (Γ' := []) .zero trivial (hP.append (by simpa using htele))
    simpa using hR.defeqDFC henvT.ordered (by simpa using hctx)
  refine {
    wf := henvC
    params := by simpa using (hdecl.params.instL hls).mono (hle₁.trans hle)
    indices := fun h => by
      simpa [List.map_reverse] using ((hTW h).1.indices.instL hls).mono hle
    type := fun {t T} h => by
      have hc : envC.HasType U [] (.const T.name ls) (T.type.instL ls) :=
        .const (hcT h) hls (by rw [hlen])
      have hdef := ((hTW h).1.defeq.instL hls).mono hle
      simp only [List.map_nil, instL_foralls, List.map_append, instL] at hdef
      exact hc.defeqU_r henvC trivial hdef
    fields := fun {j c} hc => by
      obtain ⟨T, hT', _⟩ := mem_ctors_iff.1 hc
      simpa [List.map_reverse, Function.comp_def] using
        ((hshape hc hT').1.instL hls).mono hle
    ctor := fun {j c T} hc hj => by
      obtain ⟨T', hT', hcm⟩ := mem_ctors_iff.1 hc
      cases hj.symm.trans hT'
      refine ⟨((hTW hj).2 c hcm).indices.1, ?_⟩
      have hcc : envC.HasType U [] (.const c.name ls) (c.type.instL ls) :=
        .const (hcC hc) hls (by rw [hlen])
      have hdef := ((hshape hc hj).2.instL hls).mono hle
      simp only [List.map_nil, instL_foralls, List.map_append, instL_appN, instL,
        VLevel.params_inst hlen, instL_bvars, List.map_map, Function.comp_def] at hdef
      exact hcc.defeqU_r henvC trivial hdef
    recArg := fun {j c k f ra} hc hf hra => by
      obtain ⟨T', hT', hcm⟩ := mem_ctors_iff.1 hc
      obtain ⟨ps, Ds, hty, hps, hfs⟩ := ((hTW hT').2 c hcm).shape
      have := FieldsWF.recArg hfs k f hf
      unfold RecArgWF at this
      rw [hra] at this
      obtain ⟨T, h1, h2, h3⟩ := this
      refine ⟨T, h1, h2, ?_⟩
      have := (h3.instL hls).mono hle
      simp only [List.map_append, List.map_reverse, List.map_map, Function.comp_def, List.map_take,
        instL_foralls, instL_appN, instL, VLevel.params_inst hlen, instL_bvars, Nat.zero_add] at this
      simpa [List.map_take, Function.comp_def] using this }

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
    (.appN (.const T.name ls) (bvars d.params.length T.indices.length ++
      bvars T.indices.length 0)) (.sort v)

theorem motiveType_eq {ls v j T} : d.motiveType ls v j T = (d.genMotive ls v T).liftN j := by
  simp only [motiveType, genMotive, liftN_foralls, Nat.zero_add, List.length_map, liftN,
    liftN_appN, List.map_append, bvars_liftN_hi _ _ _ _ (Nat.le_refl _), Nat.add_comm j]
  rw [bvars_liftN_lo _ _ _ _ (by simp)]

/-- A motive applied to indices and to a major premise of its type at them is a type. -/
theorem motiveApp {env : VEnv} {U ls v T Γ Δ M τ idx x}
    (hM : env.HasType U Γ M ((d.genMotive ls v T).subst τ))
    (hidx : VEnv.Ctx.SubstEq env U Γ (τ.consList idx) (τ.consList idx)
      ((T.indices.map (·.instL ls)).reverse ++ Δ))
    (hlen : idx.length = T.indices.length)
    (hx : env.HasType U Γ x (.appN (.const T.name ls)
      ((bvars d.params.length 0).map (·.subst τ) ++ idx))) :
    env.HasType U Γ (.app (.appN M idx) x) (.sort v) := by
  have h1 := VEnv.HasType.appN_substT (As := T.indices.map (·.instL ls)) hM (by simp [hlen]) hidx
  simp only [subst, subst_appN, List.map_append] at h1
  rw [← hlen, subst_bvars_consList, show bvars d.params.length idx.length =
    bvars d.params.length (0 + idx.length) by rw [Nat.zero_add], subst_bvars_consList_ge] at h1
  exact h1.app hx


theorem _root_.Lean4Lean.Ctx.Lift'.skipN_append {ρ : Lift} {Γ Γ' : List VExpr} (W : Ctx.Lift' ρ Γ Γ') :
    ∀ As : List VExpr, Ctx.Lift' (ρ.skipN As.length) Γ (As ++ Γ')
  | [] => W
  | _ :: As => .skip (Ctx.Lift'.skipN_append W As)

theorem getElem_motiveTypes {ls v} {j : Nat} {T : VInductiveType} (hj : d.types[j]? = some T) :
    ∃ h, (d.motiveTypes ls v)[j]'h = d.motiveType ls v j T := by
  have hlt : j < d.types.length := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨by simp [motiveTypes, hlt], ?_⟩
  simp only [motiveTypes, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.1 hj).2]

@[simp] theorem length_motiveTypes {ls v} : (d.motiveTypes ls v).length = d.types.length := by
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

section
variable {U : Nat} {ls : List VLevel} {v : VLevel}
set_option hygiene false
local notation "𝐔" => U
local notation "𝐥" => ls
local notation "𝐯" => v
local notation "𝐏" => (d.params.map (·.instL ls))
local notation "𝐌" => (d.motiveTypes ls v)
local notation "𝐧" => d.params.length
local notation "𝐓" => d.types.length
local notation "𝐂" => d.ctors.length
local notation "𝐅" => (c.fields.map (·.type.instL ls))
local notation "𝐦" => c.fields.length
local notation "𝐮" => c.recFields.length

/-- A motive, as a variable below the binders `Δ`. -/
theorem motive_var {env : VEnv} {t : Nat} {T : VInductiveType} (ht : d.types[t]? = some T)
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

/-- A constructor applied to the parameters and its fields, as variables below `IHs`: its type at
its indices, which instantiate the index telescope of its type. -/
theorem ctor_typing {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.ctors) (hj : d.types[j]? = some Tj) {q : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) :
    c.indices.length = Tj.indices.length ∧
    env.HasType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse) (.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length) ++ bvars 𝐦 IHs.length))
      (.appN (.const Tj.name 𝐥) ((bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)))) ++
        c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0)) ∧
    VEnv.Ctx.SubstEq env 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
        𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Tj.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
  have henv := hF.wf.ordered
  obtain ⟨hidxlen, hcty⟩ := hF.ctor hc hj
  have hjlt : j < 𝐓 := (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨hjlt', hMj⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) hj
  have hPc : OnCtx (𝐅.reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    (hF.fields hc).onCtx (by simpa using hF.params.onCtx trivial)
  have hWc : Ctx.Lift' (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) (𝐅.reverse ++ 𝐏.reverse)
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have h1 : Ctx.Lift' (.skipN .refl (𝐓 + q)) 𝐏.reverse (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
      have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) (Qs'.reverse ++ 𝐌.reverse)
      simpa [hq, Nat.add_comm] using this
    have h3 := Ctx.Lift'.skipN_append (Ctx.Lift'.tele 𝐅 h1) IHs.reverse
    simpa [liftTele_eq_liftTele'] using h3
  have hρc : (Subst.ofLift (.skipN .refl (𝐧 + (𝐓 + q + 𝐦 + IHs.length)))).consList
      (bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length) ++ bvars 𝐦 IHs.length) =
      .ofLift (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) := by subst_ext
  have hidx_eq : c.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0) =
      (c.indices.map (·.instL 𝐥)).map (·.subst (.ofLift (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length))) := by
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_refl _)]
  have hx : env.HasType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse) (.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length) ++ bvars 𝐦 IHs.length))
      (.appN (.const Tj.name 𝐥) ((bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)))) ++
        c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0)) := by
    have h0 := hcty.weak0 henv (Γ := IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse)
    rw [← closed_subst henv hcty (.ofLift (.skipN .refl (𝐧 + (𝐓 + q + 𝐦 + IHs.length))))] at h0
    have h1 := VEnv.HasType.appN_substT (Δ := []) (As := 𝐏 ++ 𝐅)
      (as := bvars 𝐧 (𝐓 + q + 𝐦 + IHs.length) ++ bvars 𝐦 IHs.length) h0 (by simp)
      (by rw [hρc]; simpa using VEnv.Ctx.SubstEq.ofLift' henv hWc hPc)
    rw [hρc] at h1
    simp only [subst_appN, subst, List.map_append] at h1
    rw [hidx_eq, show (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)))) =
      (bvars 𝐧 𝐦).map (·.subst (.ofLift (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length))) by
        simp only [bvars_subst_ofLift]; congr 1; funext i
        simp [Lift.liftVar_skipN, Lift.liftVar_consN]; (repeat' split) <;> omega]
    exact h1
  have hidx : VEnv.Ctx.SubstEq env 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Subst.ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓))).consList
        (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 IHs.length 0))
      ((Tj.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    have hcT := VEnv.IsDefEq.isType henv (Γ := []) trivial hcty
    have ⟨w, hR0⟩ := (VEnv.IsType.foralls_inv henv hcT).2
    have hTj := hF.type hj
    have hf0 := hTj.weak0 henv (Γ := 𝐅.reverse ++ 𝐏.reverse)
    rw [← closed_subst henv hTj (.ofLift (.skipN .refl (𝐧 + 𝐦))), foralls_append] at hf0
    have hWm : Ctx.Lift' (.skipN .refl 𝐦) 𝐏.reverse (𝐅.reverse ++ 𝐏.reverse) := by
      simpa using Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse)) 𝐅.reverse
    have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
    have hτm := VEnv.Ctx.SubstEq.ofLift' henv hWm hPP
    have heq : (Subst.ofLift (.skipN .refl (𝐧 + 𝐦))).consList (bvars 𝐧 𝐦) =
        .ofLift (.skipN .refl 𝐦) := by subst_ext
    have hf := VEnv.HasType.appN_substT (Δ := []) (As := 𝐏) (as := bvars 𝐧 𝐦) hf0 (by simp)
      (by rw [heq]; simpa using hτm)
    rw [heq] at hf
    have hinv := VEnv.HasType.appN_invT hF.wf hPc (Δ := 𝐏.reverse) hf hτm (hF.indices hj)
      (as := c.indices.map (·.instL 𝐥)) (by
        rw [← appN_append]
        have hR0' : env.HasType 𝐔 (𝐅.reverse ++ 𝐏.reverse) (.appN (.const Tj.name 𝐥)
            (bvars 𝐧 𝐦 ++ c.indices.map (·.instL 𝐥))) (.sort w) := by simpa using hR0
        exact ⟨_, hR0'⟩)
      (by simp [hidxlen])
    have := VEnv.Ctx.SubstEq.weak' henv hWc hinv
    rw [Subst.consList_lift_r, show (Subst.ofLift (.skipN .refl 𝐦)).lift_r
      (.skipN (.consN (.skipN .refl (𝐓 + q)) 𝐦) IHs.length) = .ofLift (.skipN .refl (IHs.length + 𝐦 + q + 𝐓)) by
        subst_ext] at this
    simp only [lift'_eq_subst] at this
    rwa [hidx_eq]
  exact ⟨hidxlen, hx, hidx⟩

/-- The conclusion of a minor premise: the motive at the constructor applied to its fields. -/
theorem minor_concl {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.ctors) (hj : d.types[j]? = some Tj) {q : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hu : IHs.length = 𝐮) :
    env.HasType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (.app (.appN (.bvar (𝐮 + 𝐦 + q + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 𝐮 0))
        (.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + q + 𝐦 + 𝐮) ++ bvars 𝐦 𝐮)))
      (.sort 𝐯) := by
  obtain ⟨hidxlen, hx, hidx⟩ := ctor_typing (v := 𝐯) hF hc hj Qs' IHs hq
  rw [hu] at hx hidx
  have := motive_var (env := env) (U := 𝐔) (ls := 𝐥) (v := 𝐯) hj (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse)
  simp only [List.length_append, List.length_reverse, hu, length_liftTele, List.length_map,
    hq] at this
  exact motiveApp this hidx (by simp [hidxlen]) hx

local notation "𝐁" => (ra.binders.map (·.instL ls))
local notation "𝐛" => ra.binders.length
local notation "𝐊" => (((c.fields.take k).map (·.type.instL ls)).reverse ++ 𝐏.reverse)
local notation "𝐱𝐬" => (ra.binders.zipIdx.map fun (A, i) =>
  (A.instL ls).reseat (d.types.length + q) k c.fields.length r i)
local notation "𝐢𝐝𝐱" => (ra.indices.map fun e =>
  (e.instL ls).reseat (d.types.length + q) k c.fields.length r ra.binders.length)
local notation "ρk" => (Lift.skipN (.consN (.skipN .refl (d.types.length + q)) k)
  (c.fields.length - k + r))

/-- A recursive field, over its own binders in the context of a minor premise's inductive
hypotheses: its binders form a telescope, the field applied to them has the type of its view, and
that view's indices instantiate the index telescope of its type. -/
theorem recField_typing {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    (hc : (j, c) ∈ d.ctors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) {q r : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hr : IHs.length = r) :
    ∃ T', d.types[ra.typeIdx]? = some T' ∧ ra.indices.length = T'.indices.length ∧
    env.IsTele 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse) 𝐱𝐬 ∧
    env.HasType 𝐔 (𝐱𝐬.reverse ++ (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
        𝐌.reverse ++ 𝐏.reverse)) (.appN (.bvar (𝐛 + r + (𝐦 - 1 - k))) (bvars 𝐛 0))
      (.appN (.const T'.name 𝐥) ((bvars 𝐧 0).map
        (·.subst (.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))))  ++ 𝐢𝐝𝐱)) ∧
    VEnv.Ctx.SubstEq env 𝐔 (𝐱𝐬.reverse ++ (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++
        Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList 𝐢𝐝𝐱)
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList 𝐢𝐝𝐱)
      ((T'.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
  have henv := hF.wf.ordered
  obtain ⟨T', hT', hidxlen, hdef⟩ := hF.recArg hc hk hra
  have hkm : k < 𝐦 := (List.getElem?_eq_some_iff.1 hk).1
  have hfk : c.fields[k] = f := (List.getElem?_eq_some_iff.1 hk).2
  obtain ⟨htlt', hMt⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) hT'
  have htlt : ra.typeIdx < 𝐓 := (List.getElem?_eq_some_iff.1 hT').1
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hFt := hF.fields hc
  rw [show 𝐅 = (c.fields.take (k + 1)).map (·.type.instL 𝐥) ++
    (c.fields.drop (k + 1)).map (·.type.instL 𝐥) by rw [← List.map_append, List.take_append_drop]]
    at hFt
  obtain ⟨hFk1, -⟩ := VEnv.IsTele.append_inv hFt
  rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hkm] at hFk1
  obtain ⟨hFk, hfty⟩ := VEnv.IsTele.append_inv hFk1
  simp only [Option.toList_some, List.map_cons, List.map_nil, hfk] at hfty
  have hOK : OnCtx 𝐊 (env.IsType 𝐔) := hFk.onCtx hPP
  have ⟨w, hfty⟩ : env.IsType 𝐔 𝐊 (f.type.instL 𝐥) := by
    cases hfty with | cons h _ => exact h
  have hRty := VEnv.IsType.defeqU_l hF.wf hOK hdef ⟨_, hfty⟩
  obtain ⟨hBt, hRt⟩ := VEnv.IsType.foralls_inv henv hRty
  have hxs : (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + q) k 𝐦 r i) =
      liftTele' ρk 𝐁 := by
    rw [liftTele'_eq_zipIdx, List.zipIdx_map, List.map_map]
    apply List.map_congr_left; rintro ⟨A, i⟩ _
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_of_lt hkm), lift'_eq_subst]
  rw [hxs]
  have hWk : Ctx.Lift' ρk 𝐊 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++
      𝐌.reverse ++ 𝐏.reverse) := by
    simpa [hr] using fieldsLift (d := d) (ls := 𝐥) (v := 𝐯) (c := c) (k' := k) Qs' IHs hq (Nat.le_of_lt hkm)
  have hWx : Ctx.Lift' (.consN ρk 𝐛) (𝐁.reverse ++ 𝐊) ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse)) := by
    simpa using Ctx.Lift'.tele 𝐁 hWk
  have hOB : OnCtx (𝐁.reverse ++ 𝐊) (env.IsType 𝐔) := hBt.onCtx hOK
  have hfield : env.HasType 𝐔 ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      (.bvar (𝐛 + r + (𝐦 - 1 - k)))
      ((VExpr.foralls 𝐁 (.appN (.const T'.name 𝐥)
        (bvars 𝐧 (k + 𝐛) ++ ra.indices.map (·.instL 𝐥)))).subst (.ofLift (.skipN ρk 𝐛))) := by
    have h0 : env.HasType 𝐔 (f.type.instL 𝐥 :: 𝐊) (.bvar 0) (f.type.instL 𝐥).lift :=
      VEnv.HasType.bvar .zero
    have h1 := VEnv.HasType.defeqU_r (Γ := f.type.instL 𝐥 :: 𝐊) hF.wf ⟨hOK, w, hfty⟩
      (hdef.weakN henv .one) h0
    have W' := fieldsLift (d := d) (ls := 𝐥) (v := 𝐯) (c := c) (k' := k + 1) Qs' (IHs ++ liftTele' ρk 𝐁) hq hkm
    rw [List.take_add_one, List.getElem?_eq_getElem hkm, hfk] at W'
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_assoc, List.length_append,
      length_liftTele', List.length_map, hr] at W'
    have h2 := h1.weak' henv W'
    have e1 : (VExpr.bvar 0).lift'
        ((Lift.consN (.skipN .refl (𝐓 + q)) (k + 1)).skipN (𝐦 - (k + 1) + (r + 𝐛)))
        = .bvar (𝐛 + r + (𝐦 - 1 - k)) := by simp [Lift.liftVar_skipN]; omega
    have e2 : ((VExpr.foralls 𝐁 (.appN (.const T'.name 𝐥)
        (bvars 𝐧 (k + 𝐛) ++ ra.indices.map (·.instL 𝐥)))).liftN 1).lift'
        ((Lift.consN (.skipN .refl (𝐓 + q)) (k + 1)).skipN (𝐦 - (k + 1) + (r + 𝐛))) =
        (VExpr.foralls 𝐁 (.appN (.const T'.name 𝐥)
        (bvars 𝐧 (k + 𝐛) ++ ra.indices.map (·.instL 𝐥)))).subst (.ofLift (.skipN ρk 𝐛)) := by
      rw [← lift'_consN_skipN, ← lift'_comp, lift'_eq_subst]; congr 1; subst_ext
    rw [e1, e2] at h2
    simpa only [List.append_assoc] using h2
  have heqx : (Subst.ofLift (.skipN ρk 𝐛)).consList (bvars 𝐛 0) = .ofLift (.consN ρk 𝐛) := by
    subst_ext
  have hx := VEnv.HasType.appN_substT (Δ := 𝐊) (As := 𝐁) (as := bvars 𝐛 0) hfield (by simp)
    (by rw [heqx]; exact VEnv.Ctx.SubstEq.ofLift' henv hWx hOB)
  rw [heqx] at hx
  simp only [subst_appN, subst, List.map_append] at hx
  have hidx_eq : ra.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛) =
      (ra.indices.map (·.instL 𝐥)).map (·.subst (.ofLift (.consN ρk 𝐛))) := by
    simp [reseat_eq_subst _ _ _ _ _ _ (Nat.le_of_lt hkm)]
  have hb_eq : (bvars 𝐧 (k + 𝐛)).map (·.subst (.ofLift (.consN ρk 𝐛))) =
      (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓)))) := by
    simp only [bvars_subst_ofLift]; congr 1; funext i
    simp [Lift.liftVar_skipN, Lift.liftVar_consN]; (repeat' split) <;> omega
  rw [hb_eq, ← hidx_eq] at hx
  have hidx : VEnv.Ctx.SubstEq env 𝐔 ((liftTele' ρk 𝐁).reverse ++
      (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList
        (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛))
      ((Subst.ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓))).consList
        (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r 𝐛))
      ((T'.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) := by
    have ⟨w', hR0⟩ := hRt
    have hTj := hF.type hT'
    have hf0 := hTj.weak0 henv (Γ := 𝐁.reverse ++ 𝐊)
    rw [← closed_subst henv hTj (.ofLift (.skipN .refl (𝐧 + (k + 𝐛)))), foralls_append] at hf0
    have hWm : Ctx.Lift' (.skipN .refl (k + 𝐛)) 𝐏.reverse (𝐁.reverse ++ 𝐊) := by
      have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
        (𝐁.reverse ++ ((c.fields.take k).map (·.type.instL 𝐥)).reverse)
      simpa [Nat.min_eq_left (Nat.le_of_lt hkm), Nat.add_comm] using this
    have hτm := VEnv.Ctx.SubstEq.ofLift' henv hWm hPP
    have heq : (Subst.ofLift (.skipN .refl (𝐧 + (k + 𝐛)))).consList (bvars 𝐧 (k + 𝐛)) =
        .ofLift (.skipN .refl (k + 𝐛)) := by subst_ext
    have hf := VEnv.HasType.appN_substT (Δ := []) (As := 𝐏) (as := bvars 𝐧 (k + 𝐛)) hf0
      (by simp) (by rw [heq]; simpa using hτm)
    rw [heq] at hf
    have hinv := VEnv.HasType.appN_invT hF.wf hOB (Δ := 𝐏.reverse) hf hτm (hF.indices hT')
      (as := ra.indices.map (·.instL 𝐥)) (by rw [← appN_append]; exact ⟨_, hR0⟩)
      (by simp [hidxlen])
    have := VEnv.Ctx.SubstEq.weak' henv hWx hinv
    rw [Subst.consList_lift_r, show (Subst.ofLift (.skipN .refl (k + 𝐛))).lift_r (.consN ρk 𝐛) =
      .ofLift (.skipN .refl (𝐛 + r + 𝐦 + q + 𝐓)) by subst_ext] at this
    simp only [lift'_eq_subst] at this
    rwa [hidx_eq]
  exact ⟨T', hT', hidxlen, hBt.weak' henv hWk, hx, hidx⟩

/-- An inductive hypothesis of a minor premise: over the recursive field's own binders, the motive
at its type, applied to its indices and to the field applied to the binders. -/
theorem minor_ih {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    (hc : (j, c) ∈ d.ctors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) {q r : Nat}
    (Qs' IHs : List VExpr) (hq : Qs'.length = q) (hr : IHs.length = r) :
    env.IsType 𝐔 (IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++ Qs'.reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.foralls 𝐱𝐬 <| .app (.appN (.bvar (𝐛 + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx))) 𝐢𝐝𝐱)
        (.appN (.bvar (𝐛 + r + (𝐦 - 1 - k))) (bvars 𝐛 0))) := by
  obtain ⟨T', hT', hidxlen, hxs, hx, hidx⟩ := recField_typing (v := 𝐯) hF hc hk hra Qs' IHs hq hr
  refine hxs.foralls ⟨𝐯, motiveApp (v := 𝐯) ?_ hidx (by simp [hidxlen]) hx⟩
  have := motive_var (env := env) (U := 𝐔) (ls := 𝐥) (v := 𝐯) hT' (𝐱𝐬.reverse ++ IHs.reverse ++ (liftTele (𝐓 + q) 𝐅).reverse ++
    Qs'.reverse)
  simp only [List.length_append, List.length_reverse, List.length_map, List.length_zipIdx, hr,
    length_liftTele, hq, List.append_assoc] at this
  rw [show 𝐛 + (r + (𝐦 + q)) = 𝐛 + r + 𝐦 + q by omega] at this
  simpa only [List.append_assoc] using this

theorem mem_recFields {c : VConstructor} {k : Nat} {ra : VRecArg} (h : (k, ra) ∈ c.recFields) :
    ∃ f, c.fields[k]? = some f ∧ f.recArg = some ra := by
  simp only [VConstructor.recFields, List.mem_filterMap] at h
  obtain ⟨⟨f, k'⟩, hm, he⟩ := h
  cases hr : f.recArg <;> simp [hr] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨f, (List.mem_zipIdx_iff_getElem?.1 hm), hr⟩

theorem minorType_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) {j : Nat} {c : VConstructor}
    {Tj : VInductiveType} (hc : (j, c) ∈ d.ctors) (hj : d.types[j]? = some Tj) {q : Nat}
    (Qs' : List VExpr) (hq : Qs'.length = q) :
    env.IsType 𝐔 (Qs'.reverse ++ 𝐌.reverse ++ 𝐏.reverse) (d.minorType 𝐥 q j c) := by
  have henv := hF.wf.ordered
  dsimp only [minorType]
  refine VEnv.IsTele.foralls (VEnv.IsTele.append ?_ ?_) ?_
  · exact (hF.fields hc).weakN henv (.zero (Qs'.reverse ++ 𝐌.reverse) (by simp [hq, Nat.add_comm]))
  · apply VEnv.IsTele.of_getElem
    intro r hr
    have hr' : r < c.recFields.length := by simpa using hr
    have hmem := List.getElem_mem hr'
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    generalize c.recFields[r] = p at hmem ⊢
    obtain ⟨k, ra⟩ := p
    obtain ⟨f, hk, hra⟩ := mem_recFields hmem
    have := minor_ih (v := 𝐯) hF hc hk hra Qs' _ hq (List.length_take_of_le (Nat.le_of_lt hr))
    simpa only [List.append_assoc] using this
  · refine ⟨v, ?_⟩
    simp only [List.reverse_append, ← List.append_assoc]
    refine minor_concl (v := 𝐯) hF hc hj Qs' _ hq ?_
    simp

theorem genMotive_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {t : Nat}
    {T : VInductiveType} (ht : d.types[t]? = some T) : env.IsType 𝐔 𝐏.reverse (d.genMotive 𝐥 𝐯 T) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hI := hF.indices ht
  have hIP : OnCtx ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) := hI.onCtx hPP
  refine hI.foralls (.forallE ?_ ⟨_, .sort hv⟩)
  have hTt := hF.type ht
  have hf0 := hTt.weak0 henv (Γ := (T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse)
  rw [← closed_subst henv hTt (.ofLift (.skipN .refl (𝐧 + T.indices.length)))] at hf0
  have heq : (Subst.ofLift (.skipN .refl (𝐧 + T.indices.length))).consList
      (bvars 𝐧 T.indices.length ++ bvars T.indices.length 0) = .ofLift .refl := by subst_ext
  have h := VEnv.HasType.appN_substT (Δ := []) (As := 𝐏 ++ T.indices.map (·.instL 𝐥))
    (as := bvars 𝐧 T.indices.length ++ bvars T.indices.length 0) hf0 (by simp)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv .refl hIP)
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

theorem minors_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) :
    env.IsTele 𝐔 (𝐌.reverse ++ 𝐏.reverse) (d.minorTypes 𝐥) := by
  apply VEnv.IsTele.of_getElem
  intro q hq
  have hq' : q < 𝐂 := by simpa [minorTypes] using hq
  have hmem := List.getElem_mem hq'
  simp only [minorTypes, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  generalize d.ctors[q] = p at hmem ⊢
  obtain ⟨j, c⟩ := p
  obtain ⟨Tj, hj, -⟩ := mem_ctors_iff.1 hmem
  have := minorType_isType (v := 𝐯) hF hmem hj ((d.minorTypes 𝐥).take q)
    (List.length_take_of_le (Nat.le_of_lt hq))
  simpa only [List.append_assoc, minorTypes] using this

@[simp] theorem length_minorTypes {ls} : (d.minorTypes ls).length = 𝐂 := by simp [minorTypes]

/-- The recursor's indices, over its binders, lift the type's index telescope. -/
theorem recIndicesLift {i : Nat} {Ti : VInductiveType} (_hi : d.types[i]? = some Ti) :
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
    (hi : d.types[i]? = some Ti) :
    env.HasType 𝐔 ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (.appN (.const Ti.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0))
      (.sort (d.level.inst 𝐥)) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hIP : OnCtx ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    (hF.indices hi).onCtx hPP
  have hTt := hF.type hi
  have hf0 := hTt.weak0 henv (Γ := (liftTele' (.skipN .refl (𝐓 + 𝐂))
    (Ti.indices.map (·.instL 𝐥))).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
  rw [← closed_subst henv hTt
    (.ofLift (.skipN .refl (𝐧 + (𝐓 + 𝐂 + Ti.indices.length))))] at hf0
  have heq : (Subst.ofLift (.skipN .refl (𝐧 + (𝐓 + 𝐂 + Ti.indices.length)))).consList
      (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0) =
      .ofLift (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length) := by subst_ext
  exact VEnv.HasType.appN_substT (Δ := []) (As := 𝐏 ++ Ti.indices.map (·.instL 𝐥))
    (as := bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0) hf0 (by simp)
    (by rw [heq]; simpa using VEnv.Ctx.SubstEq.ofLift' henv (recIndicesLift (d := d) hi) hIP)

theorem recType_isType {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {i : Nat}
    {Ti : VInductiveType} (hi : d.types[i]? = some Ti) : env.IsType 𝐔 [] (d.recType 𝐥 𝐯 i Ti) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hMs := motives_isTele hF hv
  have hQs := minors_isTele (v := 𝐯) hF
  have hI := hF.indices hi
  have hilt : i < 𝐓 := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hilt', hMi⟩ := getElem_motiveTypes (ls := 𝐥) (v := 𝐯) hi
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hWI := Ctx.Lift'.tele (Ti.indices.map (·.instL 𝐥)) hW0
  simp only [List.length_map] at hWI
  have hIP : OnCtx ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse) (env.IsType 𝐔) :=
    hI.onCtx hPP
  dsimp only [recType, recBinders]
  rw [liftTele_eq_liftTele']
  simp only [Lift.consN]
  have hTele : env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥 ++
      liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))) :=
    ((hF.params.append (by simpa using hMs)).append (by simpa using hQs)).append
      (by simpa using hI.weak' henv hW0)
  have hWI' : Ctx.Lift' (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)
      ((Ti.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    simpa only [List.append_assoc] using hWI
  have hX := major_type (v := 𝐯) hF hi
  refine hTele.foralls (.forallE ?_ ?_)
  · simp only [List.reverse_append, List.append_nil, ← List.append_assoc]
    exact ⟨_, hX⟩
  · simp only [List.reverse_append, List.append_nil, ← List.append_assoc]
    have hM : env.HasType 𝐔 (.appN (.const Ti.name 𝐥)
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
        (.bvar (1 + Ti.indices.length + 𝐂 + (𝐓 - 1 - i)))
        ((d.genMotive 𝐥 𝐯 Ti).subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))) := by
      have h1 := Lookup.reverse_append 𝐌 (Γ := 𝐏.reverse) i hilt'
      have h2 := Lookup.append_left (.appN (.const Ti.name 𝐥)
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse)) h1
      rw [hMi, motiveType_eq, liftN_liftN, liftN_liftN, length_motiveTypes] at h2
      simp only [List.append_assoc, List.length_append, List.length_reverse, List.length_cons,
        length_liftTele', List.length_map, length_minorTypes, List.cons_append] at h2
      rw [show i + (𝐓 - i + (Ti.indices.length + 𝐂 + 1)) = 1 + Ti.indices.length + 𝐂 + 𝐓 by omega,
        show Ti.indices.length + 𝐂 + 1 + (𝐓 - 1 - i) = 1 + Ti.indices.length + 𝐂 + (𝐓 - 1 - i) by
          omega, liftN_eq_subst] at h2
      simpa using VEnv.HasType.bvar (env := env) (U := 𝐔) h2
    have heq2 : (Subst.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓))).consList
        (bvars Ti.indices.length 1) =
        .ofLift (.skip (.consN (.skipN .refl (𝐓 + 𝐂)) Ti.indices.length)) := by subst_ext
    have hidx := VEnv.Ctx.SubstEq.ofLift' henv (.skip hWI' (A := .appN (.const Ti.name 𝐥)
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0))) hIP
    rw [← heq2] at hidx
    have hx : env.HasType 𝐔 (.appN (.const Ti.name 𝐥)
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0) ::
        ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) (.bvar 0)
        (.appN (.const Ti.name 𝐥) ((bvars 𝐧 0).map
          (·.subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))) ++
          bvars Ti.indices.length 1)) := by
      have := VEnv.HasType.bvar (env := env) (U := 𝐔) (Lookup.zero (ty := .appN (.const Ti.name 𝐥)
        (bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length) ++ bvars Ti.indices.length 0))
        (Γ := (liftTele' (.skipN .refl (𝐓 + 𝐂)) (Ti.indices.map (·.instL 𝐥))).reverse ++
        (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      simp only [lift, liftN_appN, List.map_append, bvars_liftN, liftN] at this
      rw [show (bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (1 + Ti.indices.length + 𝐂 + 𝐓)))) =
        bvars 𝐧 (𝐓 + 𝐂 + Ti.indices.length + 1) by
          rw [bvars_subst_skipN]; congr 1; omega]
      exact this
    exact ⟨_, motiveApp hM hidx (by simp) hx⟩

theorem bvars_subst_cons (σ : Subst) (x : VExpr) (n k : Nat) :
    (bvars n (k + 1)).map (·.subst (σ.cons x)) = (bvars n k).map (·.subst σ) := by
  simp only [bvars, List.map_map, Function.comp_def, subst_bvar, ← Nat.add_assoc]; rfl

/-- The recursors, as terms `rc t` of their types. -/
def RecTyped (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) (v : VLevel)
    (rc : Nat → VExpr) : Prop :=
  ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.HasType U [] (rc t) (d.recType ls v t T)

/-- A recursor applied to the parameters, motives and minor premises as variables below `Δ`, to
indices, and to a major premise at those indices: the motive at them. -/
theorem rec_app {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {rc : Nat → VExpr}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 rc) {t : Nat}
    {T : VInductiveType} (ht : d.types[t]? = some T) (Δ : List VExpr) {idx : List VExpr}
    {x : VExpr}
    (hidx : VEnv.Ctx.SubstEq env 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂))).consList idx)
      ((Subst.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂))).consList idx)
      ((T.indices.map (·.instL 𝐥)).reverse ++ 𝐏.reverse))
    (hlen : idx.length = T.indices.length)
    (hx : env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) x
      (.appN (.const T.name 𝐥)
        ((bvars 𝐧 0).map (·.subst (.ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂)))) ++ idx))) :
    env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (.appN (rc t) (bvars (𝐧 + 𝐓 + 𝐂) Δ.length ++ idx ++ [x]))
      (.app (.appN (.bvar (Δ.length + 𝐂 + (𝐓 - 1 - t))) idx) x) := by
  have henv := hF.wf.ordered
  have hPP : OnCtx 𝐏.reverse (env.IsType 𝐔) := by simpa using hF.params.onCtx trivial
  have hc := hrec ht
  have hRt : env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥) :=
    (hF.params.append (by simpa using motives_isTele hF hv)).append
      (by simpa using minors_isTele (v := 𝐯) hF)
  have hRc : OnCtx ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) (env.IsType 𝐔) := by
    simpa using hRt.onCtx trivial
  have hc0 := hc.weak0 henv (Γ := Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
  rw [← closed_subst henv hc (.ofLift (.skipN .refl (𝐧 + 𝐓 + 𝐂 + Δ.length)))] at hc0
  dsimp only [recType, recBinders] at hc0
  rw [liftTele_eq_liftTele',
    show ∀ (As : List VExpr) X B, VExpr.foralls As (.forallE X B) = .foralls (As ++ [X]) B by
      intro As X B; rw [foralls_append]; rfl] at hc0
  simp only [Lift.consN] at hc0
  have hσ : (Subst.ofLift (.skipN .refl (𝐧 + 𝐓 + 𝐂 + Δ.length))).consList
      (bvars (𝐧 + 𝐓 + 𝐂) Δ.length) = .ofLift (.skipN .refl Δ.length) := by subst_ext
  have hW : Ctx.Lift' (.skipN .refl Δ.length) ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    simpa only [List.append_assoc] using Ctx.Lift'.skipN_append (Ctx.Lift'.refl
      (Γ := (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) Δ
  have hW0 : Ctx.Lift' (.skipN .refl (𝐓 + 𝐂)) 𝐏.reverse
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := 𝐏.reverse))
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
    simpa [Nat.add_comm] using this
  have hI : VEnv.Ctx.SubstEq env 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)
      ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)
      ((liftTele' (.skipN .refl (𝐓 + 𝐂)) (T.indices.map (·.instL 𝐥))).reverse ++
        ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse)) := by
    refine VEnv.Ctx.SubstEq.extendLift henv hW0 (hF.indices ht)
      (VEnv.Ctx.SubstEq.ofLift' henv hW hRc) ?_ (by simp [hlen])
    rw [show (Subst.ofLift (.skipN .refl Δ.length)).lift_l (.skipN .refl (𝐓 + 𝐂)) =
      .ofLift (.skipN .refl (Δ.length + 𝐓 + 𝐂)) by subst_ext]
    exact hidx
  have hX := major_type (v := 𝐯) hF ht
  have hx' : env.HasType 𝐔 (Δ ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) x
      ((VExpr.appN (.const T.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + T.indices.length) ++
        bvars T.indices.length 0)).subst ((Subst.ofLift (.skipN .refl Δ.length)).consList idx)) := by
    simp only [subst_appN, subst, List.map_append]
    rw [← hlen, subst_bvars_consList, show 𝐓 + 𝐂 + idx.length = (𝐓 + 𝐂) + idx.length from rfl,
      subst_bvars_consList_ge, bvars_subst_skipN]
    rwa [bvars_subst_skipN, show 0 + (Δ.length + 𝐓 + 𝐂) = 𝐓 + 𝐂 + Δ.length by omega] at hx
  have h := VEnv.HasType.appN_substT (Δ := [])
    (As := 𝐏 ++ 𝐌 ++ d.minorTypes 𝐥 ++ liftTele' (.skipN .refl (𝐓 + 𝐂)) (T.indices.map (·.instL 𝐥)) ++
      [.appN (.const T.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + T.indices.length) ++ bvars T.indices.length 0)])
    (as := bvars (𝐧 + 𝐓 + 𝐂) Δ.length ++ idx ++ [x]) hc0 (by simp [hlen]; omega) (by
      rw [Subst.consList_concat, Subst.consList_append, hσ]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, List.append_nil]
      refine .cons ?_ (by simpa only [List.append_assoc] using hX) ?_
      · simpa only [List.append_assoc, Subst.cons_tail] using hI
      · have := hx'
        simp only [List.append_assoc] at this
        simp only [Subst.cons_tail, Subst.cons_head]
        exact this)
  rw [Subst.consList_concat, Subst.consList_append, hσ] at h
  simp only [subst, subst_appN] at h
  have e1 : ((Subst.ofLift (.skipN .refl Δ.length)).consList idx).cons x
      (1 + T.indices.length + 𝐂 + (𝐓 - 1 - t)) = .bvar (Δ.length + 𝐂 + (𝐓 - 1 - t)) := by
    rw [show 1 + T.indices.length + 𝐂 + (𝐓 - 1 - t) = (𝐂 + (𝐓 - 1 - t) + idx.length) + 1 by
      omega]
    show (Subst.ofLift (.skipN .refl Δ.length)).consList idx (𝐂 + (𝐓 - 1 - t) + idx.length) = _
    rw [Subst.consList_ge]; simp [Lift.liftVar_skipN]; omega
  rw [e1, bvars_subst_cons, ← hlen, subst_bvars_consList] at h
  exact h

theorem _root_.Lean4Lean.VExpr.bvars_append (a b k : Nat) :
    bvars a (b + k) ++ bvars b k = bvars (a + b) k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [bvars, List.getElem_append, List.length_map, List.length_reverse, List.length_range,
    List.getElem_map, List.getElem_reverse, List.getElem_range]
  split <;> (congr 1; omega)

theorem recBinders_isTele {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) :
    env.IsTele 𝐔 [] (𝐏 ++ 𝐌 ++ d.minorTypes 𝐥) :=
  (hF.params.append (by simpa using motives_isTele hF hv)).append
    (by simpa using minors_isTele (v := 𝐯) hF)

/-- The left side of an iota rule: the recursor at a constructor, over the recursor's binders and
the constructor's fields. -/
theorem iota_lhs {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {j : Nat}
    {c : VConstructor} {Tj : VInductiveType} (hc : (j, c) ∈ d.ctors) (hj : d.types[j]? = some Tj) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.appN (d.recConst recLs j) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐓 (𝐂 + 𝐦) ++
        bvars 𝐂 𝐦 ++ c.indices.map (fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0) ++
        [.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐦 0)]))
      (.app (.appN (.bvar (𝐦 + 𝐂 + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0))
        (.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐦 0))) := by
  obtain ⟨hidxlen, hx, hidx⟩ := ctor_typing (v := 𝐯) hF hc hj (d.minorTypes 𝐥) [] (q := 𝐂) (by simp)
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at hx hidx
  have := rec_app hF hv hrec hj (liftTele (𝐓 + 𝐂) 𝐅).reverse
    (idx := c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0)
    (x := .appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐦 0))
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hidx) (by simp [hidxlen])
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx)
  simp only [List.length_reverse, length_liftTele, List.length_map] at this
  have hb : bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐓 (𝐂 + 𝐦) ++ bvars 𝐂 𝐦 = bvars (𝐧 + 𝐓 + 𝐂) 𝐦 := by
    rw [show 𝐓 + 𝐂 + 𝐦 = 𝐓 + (𝐂 + 𝐦) by omega, bvars_append, bvars_append]
  rw [hb]
  exact this

/-- The argument an iota rule gives a minor premise for a recursive field: the recursor at the
field, over the field's own binders. -/
theorem iota_ih {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {j : Nat}
    {c : VConstructor} (hc : (j, c) ∈ d.ctors) {k : Nat} {f : VField} {ra : VRecArg}
    (hk : c.fields[k]? = some f) (hra : f.recArg = some ra) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
        (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + 𝐛) ++
          bvars 𝐓 (𝐂 + 𝐦 + 𝐛) ++ bvars 𝐂 (𝐦 + 𝐛) ++
          ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛))
        (.appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0)))
      (.foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
        (.appN (.bvar (𝐛 + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx)))
          (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛))
        (.appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0))) := by
  obtain ⟨T', hT', hidxlen, hxs, hx, hidx⟩ :=
    recField_typing (v := 𝐯) hF hc hk hra (d.minorTypes 𝐥) [] (q := 𝐂) (r := 0) (by simp) rfl
  simp only [List.reverse_nil, List.nil_append, Nat.add_zero] at hxs hx hidx
  refine hxs.lams ?_
  have := rec_app hF hv hrec hT'
    ((ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i).reverse ++
      (liftTele (𝐓 + 𝐂) 𝐅).reverse)
    (idx := ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 𝐛)
    (x := .appN (.bvar (𝐛 + (𝐦 - 1 - k))) (bvars 𝐛 0))
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hidx) (by simp [hidxlen])
    (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx)
  simp only [List.length_append, List.length_reverse, List.length_map, List.length_zipIdx,
    length_liftTele] at this
  have hb : bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + 𝐛) ++ bvars 𝐓 (𝐂 + 𝐦 + 𝐛) ++ bvars 𝐂 (𝐦 + 𝐛) =
      bvars (𝐧 + 𝐓 + 𝐂) (𝐛 + 𝐦) := by
    rw [show 𝐓 + 𝐂 + 𝐦 + 𝐛 = 𝐓 + (𝐂 + 𝐦 + 𝐛) by omega, bvars_append,
      show 𝐂 + 𝐦 + 𝐛 = 𝐂 + (𝐦 + 𝐛) by omega, bvars_append, Nat.add_comm 𝐦]
  rw [hb, ← appN_append_singleton]
  simpa only [List.append_assoc] using this

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

@[simp] theorem getElem_minorTypes {ls} {q : Nat} (h : q < (d.minorTypes ls).length) :
    (d.minorTypes ls)[q] = d.minorType ls q (d.ctors[q]'(by simpa using h)).1
      (d.ctors[q]'(by simpa using h)).2 := by
  simp [minorTypes]

/-- The right side of an iota rule: the minor premise applied to the fields and to the recursor
at each recursive field. -/
theorem iota_rhs {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.ctors[q]? = some (j, c)) :
    env.HasType 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++ (d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++
        𝐏.reverse)
      (.appN (.bvar (𝐦 + (𝐂 - 1 - q))) (bvars 𝐦 0 ++ c.recFields.map fun (k, ra) =>
        .lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
          (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + ra.binders.length) ++
            bvars 𝐓 (𝐂 + 𝐦 + ra.binders.length) ++ bvars 𝐂 (𝐦 + ra.binders.length) ++
            ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
          (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0))))
      (.app (.appN (.bvar (𝐦 + 𝐂 + (𝐓 - 1 - j)))
          (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0))
        (.appN (.const c.name 𝐥) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦) ++ bvars 𝐦 0))) := by
  have henv := hF.wf.ordered
  have hqC : q < 𝐂 := (List.getElem?_eq_some_iff.1 hq).1
  have hc : (j, c) ∈ d.ctors := List.mem_of_getElem? hq
  have hqlt : q < (d.minorTypes 𝐥).length := by simpa using hqC
  have hQq : (d.minorTypes 𝐥)[q] = d.minorType 𝐥 q j c := by
    rw [getElem_minorTypes, (List.getElem?_eq_some_iff.1 hq).2]
  -- the minor premise, as a variable
  have hmin := VEnv.HasType.bvar (env := env) (U := 𝐔) <|
    Lookup.append_left (liftTele (𝐓 + 𝐂) 𝐅).reverse
      (Lookup.reverse_append (d.minorTypes 𝐥) (Γ := 𝐌.reverse ++ 𝐏.reverse) q hqlt)
  rw [hQq, liftN_liftN, liftN_eq_subst] at hmin
  simp only [List.length_reverse, length_liftTele, List.length_map, length_minorTypes,
    Lift.consN] at hmin
  dsimp only [minorType] at hmin
  simp only [List.append_assoc]
  have hWq0 : Ctx.Lift' (.skipN .refl (𝐂 - q))
      (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse ++ 𝐏.reverse) := by
    have := Ctx.Lift'.skipN_append (Ctx.Lift'.refl
      (Γ := ((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse))
      ((d.minorTypes 𝐥).drop q).reverse
    rw [show (d.minorTypes 𝐥).reverse = ((d.minorTypes 𝐥).drop q).reverse ++
      ((d.minorTypes 𝐥).take q).reverse by rw [← List.reverse_append, List.take_append_drop]]
    simpa only [List.length_reverse, List.length_drop, length_minorTypes,
      List.append_assoc] using this
  have hWq := Ctx.Lift'.tele (liftTele (𝐓 + q) 𝐅) hWq0
  have hFF : liftTele' (.skipN .refl (𝐂 - q)) (liftTele (𝐓 + q) 𝐅) = liftTele (𝐓 + 𝐂) 𝐅 := by
    rw [liftTele_eq_liftTele', liftTele_eq_liftTele', liftTele'_liftTele']
    simp only [Lift.consN]
    rw [Lift.comp_skipN]
    show liftTele' (Lift.skipN (Lift.skipN .refl (𝐓 + q)) (𝐂 - q)) _ = _
    rw [Lift.skipN_skipN, show 𝐓 + q + (𝐂 - q) = 𝐓 + 𝐂 by omega]
  rw [hFF] at hWq
  simp only [length_liftTele, List.length_map] at hWq
  have hQt : env.IsTele 𝐔 (𝐌.reverse ++ 𝐏.reverse) ((d.minorTypes 𝐥).take q) := by
    have := minors_isTele (v := 𝐯) hF
    rw [← List.take_append_drop q (d.minorTypes 𝐥)] at this
    exact (VEnv.IsTele.append_inv this).1
  have hΔq : OnCtx (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (env.IsType 𝐔) := by
    have := ((hF.params.append (by simpa using motives_isTele hF hv)).append
      (by simpa using hQt)).onCtx trivial
    simpa only [List.reverse_append, List.append_nil, List.append_assoc] using this
  have hFq : env.IsTele 𝐔 (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++ 𝐏.reverse)
      (liftTele (𝐓 + q) 𝐅) :=
    (hF.fields hc).weakN henv (.zero (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse)
      (by simp; omega))
  have hσ : VEnv.Ctx.SubstEq env 𝐔 ((liftTele (𝐓 + 𝐂) 𝐅).reverse ++
      ((d.minorTypes 𝐥).reverse ++ (𝐌.reverse ++ 𝐏.reverse)))
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0))
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0))
      ((liftTele (𝐓 + q) 𝐅).reverse ++ (((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++
        𝐏.reverse)) := by
    rw [show (Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0) =
      .ofLift (.consN (.skipN .refl (𝐂 - q)) 𝐦) by subst_ext]
    exact VEnv.Ctx.SubstEq.ofLift' henv (by simpa only [List.append_assoc] using hWq)
      (hFq.onCtx hΔq)
  have h := VEnv.HasType.appN_substT (Δ := ((d.minorTypes 𝐥).take q).reverse ++ 𝐌.reverse ++
    𝐏.reverse) hmin (as := bvars 𝐦 0 ++ c.recFields.map fun (k, ra) =>
        .lams (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i) <| .app
          (.appN (d.recConst recLs ra.typeIdx) (bvars 𝐧 (𝐓 + 𝐂 + 𝐦 + ra.binders.length) ++
            bvars 𝐓 (𝐂 + 𝐦 + ra.binders.length) ++ bvars 𝐂 (𝐦 + ra.binders.length) ++
            ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
          (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0)))
    (by simp) ?W
  case W =>
    rw [Subst.consList_append, List.reverse_append, List.append_assoc]
    refine VEnv.Ctx.SubstEq.ofGetElem hσ _ rfl ?_ (by simp) ?_
    · apply VEnv.IsTele.of_getElem
      intro r hr
      have hr' : r < c.recFields.length := by simpa using hr
      have hmem := List.getElem_mem hr'
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      generalize c.recFields[r] = p at hmem ⊢
      obtain ⟨k, ra⟩ := p
      obtain ⟨f, hk, hra⟩ := mem_recFields hmem
      have := minor_ih (v := 𝐯) hF hc hk hra ((d.minorTypes 𝐥).take q) _
        (List.length_take_of_le (Nat.le_of_lt hqlt)) (List.length_take_of_le (Nat.le_of_lt hr))
      simpa only [List.append_assoc] using this
    · intro r hr hr2
      have hr' : r < c.recFields.length := by simpa using hr
      have hmem := List.getElem_mem hr'
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      generalize c.recFields[r] = p at hmem ⊢
      obtain ⟨k, ra⟩ := p
      obtain ⟨f, hk, hra⟩ := mem_recFields hmem
      have hkm : k < 𝐦 := (List.getElem?_eq_some_iff.1 hk).1
      have key : ∀ L : List VExpr, L.length = r →
          (VExpr.foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + q) k 𝐦 r i)
            (.app (.appN (.bvar (ra.binders.length + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx)))
              (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) k 𝐦 r ra.binders.length))
            (.appN (.bvar (ra.binders.length + r + (𝐦 - 1 - k))) (bvars ra.binders.length 0)))).subst
            (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L) =
          .foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 i)
            (.app (.appN (.bvar (ra.binders.length + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx)))
              (ra.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) k 𝐦 0 ra.binders.length))
            (.appN (.bvar (ra.binders.length + (𝐦 - 1 - k))) (bvars ra.binders.length 0))) := by
        intro L hL
        rw [subst_foralls]; congr 1
        · apply List.ext_getElem (by simp)
          intro i h1 h2
          simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
          exact reseat_subst_iota _ L hL (Nat.le_of_lt hkm) (Nat.le_of_lt hqC)
        · simp only [subst, subst_appN, List.map_map, List.length_map, List.length_zipIdx]
          rw [bvar_subst_iota L hL (Nat.le_of_lt hqC) (by omega),
            bvar_subst_iota L hL (Nat.le_of_lt hqC) (by omega), bvars_subst_iota,
            if_neg (by omega), if_pos (by omega),
            show ra.binders.length + r + 𝐦 + q + (𝐓 - 1 - ra.typeIdx) - r + (𝐂 - q) =
              ra.binders.length + 𝐦 + 𝐂 + (𝐓 - 1 - ra.typeIdx) by omega,
            show ra.binders.length + r + (𝐦 - 1 - k) - r = ra.binders.length + (𝐦 - 1 - k) by
              omega]
          congr 2
          apply List.map_congr_left; intro e _
          exact reseat_subst_iota _ L hL (Nat.le_of_lt hkm) (Nat.le_of_lt hqC)
      rw [key _ (by simp; omega)]
      simpa only [List.append_assoc] using iota_ih hF hv hrec hc hk hra
  have hb : ∀ (L : List VExpr), L.length = 𝐮 → ∀ x, 𝐮 ≤ x →
      ((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L x =
        .bvar (if x < 𝐮 + 𝐦 then x - 𝐮 else x - 𝐮 + (𝐂 - q)) := by
    intro L hL x hx
    simpa only [Subst.liftN, Nat.zero_add] using
      bvar_subst_iota (i := 0) (m := 𝐦) (C := 𝐂) (q := q) (x := x) L hL (Nat.le_of_lt hqC)
        (by omega)
  have e1 : ∀ (L : List VExpr), L.length = 𝐮 →
      (c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + q) 𝐦 𝐦 𝐮 0).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      c.indices.map fun e => (e.instL 𝐥).reseat (𝐓 + 𝐂) 𝐦 𝐦 0 0 := by
    intro L hL
    rw [List.map_map]; apply List.map_congr_left; intro e _
    have := reseat_subst_iota (e.instL 𝐥) (a := 𝐓) (i := 0) L hL (Nat.le_refl 𝐦)
      (Nat.le_of_lt hqC)
    simp only [Subst.liftN] at this
    exact this
  rw [Subst.consList_append] at h
  simp only [subst, subst_appN, List.map_append] at h
  rw [hb _ (by simp) _ (by omega), if_neg (by omega),
    show 𝐮 + 𝐦 + q + (𝐓 - 1 - j) - 𝐮 + (𝐂 - q) = 𝐦 + 𝐂 + (𝐓 - 1 - j) by omega,
    e1 _ (by simp)] at h
  have e2 : ∀ (L : List VExpr), L.length = 𝐮 →
      (bvars 𝐧 (𝐓 + q + 𝐦 + 𝐮)).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      bvars 𝐧 (𝐓 + 𝐂 + 𝐦) := by
    intro L hL
    rw [bvars_map_subst]; conv => rhs; rw [bvars]
    apply List.map_congr_left; intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    rw [hb L hL _ (by omega), if_neg (by omega)]; congr 1; omega
  have e3 : ∀ (L : List VExpr), L.length = 𝐮 →
      (bvars 𝐦 𝐮).map
        (·.subst (((Subst.ofLift (.skipN .refl (𝐂 - q + 𝐦))).consList (bvars 𝐦 0)).consList L)) =
      bvars 𝐦 0 := by
    intro L hL
    rw [bvars_map_subst]; conv => rhs; rw [bvars]
    apply List.map_congr_left; intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    rw [hb L hL _ (by omega), if_pos (by omega)]; congr 1; omega
  rw [e2 _ (by simp), e3 _ (by simp)] at h
  simpa only [List.append_assoc] using h

/-- An iota rule's two sides and type, as bodies over the recursor's binders and the
constructor's fields: each side is typed there. -/
theorem iotaRule_bodies {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔)
    {recLs : List VLevel} (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.ctors[q]? = some (j, c)) :
    ∃ L R T, (d.iotaRule 𝐥 𝐯 recLs q j c).lhs = .lams (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) L ∧
      (d.iotaRule 𝐥 𝐯 recLs q j c).rhs = .lams (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) R ∧
      (d.iotaRule 𝐥 𝐯 recLs q j c).type =
        .foralls (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) T ∧
      env.IsTele 𝐔 [] (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) ∧
      env.HasType 𝐔 (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅).reverse L T ∧
      env.HasType 𝐔 (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅).reverse R T := by
  have henv := hF.wf.ordered
  have hc : (j, c) ∈ d.ctors := List.mem_of_getElem? hq
  obtain ⟨Tj, hj, -⟩ := mem_ctors_iff.1 hc
  have hbind : env.IsTele 𝐔 [] (d.recBinders 𝐥 𝐯 ++ liftTele (𝐓 + 𝐂) 𝐅) :=
    (recBinders_isTele hF hv).append (by
      simpa using (hF.fields hc).weakN henv (.zero ((d.minorTypes 𝐥).reverse ++ 𝐌.reverse)
        (by simp; omega)))
  refine ⟨_, _, _, rfl, rfl, rfl, hbind, ?_, ?_⟩
  · simpa only [recBinders, List.reverse_append, List.append_nil, List.append_assoc] using
      iota_lhs hF hv hrec hc hj
  · simpa only [recBinders, List.reverse_append, List.append_nil, List.append_assoc] using
      iota_rhs hF hv hrec hq

theorem iotaRule_WF {env : VEnv} (hF : d.RecFacts env 𝐔 𝐥) (hv : 𝐯.WF 𝐔) {recLs : List VLevel}
    (hrec : d.RecTyped env 𝐔 𝐥 𝐯 (d.recConst recLs)) {q j : Nat}
    {c : VConstructor} (hq : d.ctors[q]? = some (j, c)) (hrl : recLs.length = 𝐔) :
    (d.iotaRule 𝐥 𝐯 recLs q j c).WF env := by
  obtain ⟨L, R, T, hl, hr, ht, hbind, hL, hR⟩ := iotaRule_bodies hF hv hrec hq
  dsimp only [VDefEq.WF]
  rw [hl, hr, ht, show (d.iotaRule 𝐥 𝐯 recLs q j c).uvars = 𝐔 from hrl]
  exact ⟨hbind.lams (by simpa using hL), hbind.lams (by simpa using hR)⟩

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

end VInductDecl
end Lean4Lean

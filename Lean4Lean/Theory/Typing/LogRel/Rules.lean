import Lean4Lean.Theory.Typing.Projection

/-!
# The rules of a well-formed environment

Every defining equation of a well-formed environment comes from one of three sources: a
definition's unfolding, the quotient's computation rule, or an iota rule of a block the
environment records. Each is a closed equation `lams Bs L ≡ lams Bs R` over binders `Bs`, and its
left-hand side's body `L` is a constant applied to arguments: a definition's constant at its own
level parameters (`Bs = []`), `Quot.lift` with `Quot.mk` at the major premise, or a recursor with
a constructor application at the major premise. This is what replaces upstream's `extra_pat`
assumption: the rules head reduction fires are read off these.
-/

namespace Lean4Lean
open VExpr

/-- Where a defining equation of an environment comes from. -/
inductive VEnv.RuleKind (env : VEnv) : VDefEq → Prop
  /-- A definition unfolds: `c.{us} ≡ value`, at the definition's own level parameters. -/
  | defn (ci : VDefVal) : env.constants ci.name = some ci.toVConstant → env.RuleKind ci.toDefEq
  /-- The quotient's computation rule, `Quot.lift f h (Quot.mk r a) ≡ f a`. -/
  | quot : env.constants ``Quot.lift = some quotLiftConst →
    env.constants ``Quot.mk = some quotMkConst → env.constants ``Eq = some eqConst →
    env.constants ``Quot = some quotConst → env.RuleKind quotDefEq
  /-- An iota rule of a recorded block. -/
  | iota {s d t df} : env.inducts s = some (d, t) → df ∈ d.iotaRules → env.RuleKind df

theorem VEnv.RuleKind.mono {env env' : VEnv} (H : env ≤ env') {df} :
    env.RuleKind df → env'.RuleKind df
  | .defn ci h => .defn ci (H.constants h)
  | .quot h1 h2 h3 h4 =>
    .quot (H.constants h1) (H.constants h2) (H.constants h3) (H.constants h4)
  | .iota h1 h2 => .iota (H.inducts h1) h2

namespace VEnv

theorem addConsts_defeqs : ∀ {env env' : VEnv} {cis : List VDefVal},
    env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | _, _, [], h => by cases h; rfl
  | _, _, _ :: _, h => by
    simp only [addConsts, List.foldlM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConsts_defeqs h2).trans (addConst_defeqs h1)

theorem addDefEqs_defeqs : ∀ {env : VEnv} {cis : List VDefVal} {df},
    (env.addDefEqs cis).defeqs df → (∃ ci ∈ cis, df = ci.toDefEq) ∨ env.defeqs df
  | _, [], _, h => .inr h
  | _, ci :: _, _, h => by
    rcases addDefEqs_defeqs (env := addDefEq _ ci.toDefEq) h with ⟨ci', h1, h2⟩ | h | h
    · exact .inl ⟨ci', .tail _ h1, h2⟩
    · exact .inl ⟨ci, .head _, h⟩
    · exact .inr h

theorem addDefEqList_defeqs' : ∀ {env : VEnv} {dfs : List VDefEq} {df},
    (env.addDefEqList dfs).defeqs df → df ∈ dfs ∨ env.defeqs df
  | _, [], _, h => .inr h
  | _, d :: _, _, h => by
    rcases addDefEqList_defeqs' (env := addDefEq _ d) h with h | h | h
    · exact .inl (.tail _ h)
    · exact .inl (h ▸ .head _)
    · exact .inr h

theorem addQuot_defeqs {env env' : VEnv} (h : env.addQuot = some env') {df}
    (h' : env'.defeqs df) : df = quotDefEq ∨ env.defeqs df := by
  simp only [addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, h5⟩ := h
  cases h5
  rcases h' with h' | h'
  · exact .inl h'
  · rw [addConst_defeqs h4, addConst_defeqs h3, addConst_defeqs h2, addConst_defeqs h1] at h'
    exact .inr h'

/-- Every defining equation of a well-formed environment is a definition's unfolding, the
quotient's computation rule, or an iota rule of a block the environment records. -/
theorem WF.ruleKind {env : VEnv} (henv : env.WF) {df : VDefEq} (h : env.defeqs df) :
    env.RuleKind df := by
  obtain ⟨ds, H⟩ := henv
  induction H generalizing df with
  | empty => cases h
  | @decl _ env₂ _ env₁ hD hW ih =>
    have IH {df} (h : env₁.defeqs df) : env₂.RuleKind df := (ih h).mono hD.le
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 => exact IH (addConst_defeqs h1 ▸ h)
    | «def» _ h1 =>
      rcases h with rfl | h
      · exact .defn _ (addDefEq_le.constants (addConst_self h1))
      · exact IH (addConst_defeqs h1 ▸ h)
    | mutualDef _ h1 _ =>
      rcases addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
      · exact .defn _ (addDefEqs_le.constants (addConsts_constants h1 ci hci))
      · exact IH (addConsts_defeqs h1 ▸ h)
    | «example» => exact IH h
    | quot hq h1 =>
      rcases addQuot_defeqs h1 h with rfl | h
      · exact .quot (addQuot_quotLift h1) (addQuot_quotMk h1)
          ((VDecl.WF.quot hq h1).le.constants hq) (addQuot_quot h1)
      · exact IH h
    | induct hd _ h1 =>
      rename_i d _
      have h1' := h1
      simp only [addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
      obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := h1
      rw [addBlock_defeqs hB] at h
      rcases addDefEqList_defeqs' h with h | h
      · obtain ⟨T, hT'⟩ : ∃ T, d.types[0]? = some T := by
          cases e : d.types with
          | nil => exact (hd.nonempty e).elim
          | cons T _ => exact ⟨T, rfl⟩
        refine .iota (s := T.name) (t := 0) ?_ h
        unfold addBlock at hB; split at hB <;> cases hB
        simp only
        rw [List.findIdx?_eq_some_iff_getElem.2 ⟨?_, ?_, ?_⟩]
        · exact (List.getElem?_eq_some_iff.1 hT').1
        · have := (List.getElem?_eq_some_iff.1 hT').2; simp [this]
        · intro j hj; omega
      · rw [addConstList_defeqs' hR, addConstList_defeqs' hC, addConstList_defeqs' hT] at h
        exact IH h

/-- The first `n` binders of a lambda and its body. -/
def peelLams : Nat → VExpr → List VExpr × VExpr
  | n + 1, .lam A e => let (Bs, b) := peelLams n e; (A :: Bs, b)
  | _, e => ([], e)

/-- The first `n` binders of a pi and its body. -/
def peelForalls : Nat → VExpr → List VExpr × VExpr
  | n + 1, .forallE A e => let (Bs, b) := peelForalls n e; (A :: Bs, b)
  | _, e => ([], e)

theorem lams_instL' (ls : List VLevel) : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.lams As B).instL ls = .lams (As.map (·.instL ls)) (B.instL ls)
  | [], _ => rfl
  | _ :: As, B => by simp [VExpr.instL, lams_instL' ls As B]

theorem foralls_instL' (ls : List VLevel) : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.foralls As B).instL ls = .foralls (As.map (·.instL ls)) (B.instL ls)
  | [], _ => rfl
  | _ :: As, B => by simp [VExpr.instL, foralls_instL' ls As B]

theorem _root_.Lean4Lean.VInductiveType.ctorApp_const (T : VInductiveType) (c : VConstructor)
    (ls : List VLevel) (ps fs : List VExpr) :
    ∃ lsC psC, T.ctorApp c ls ps fs = .appN (.const c.name lsC) (psC ++ fs) := by
  unfold VInductiveType.ctorApp; split <;> exact ⟨_, _, rfl⟩

/-- The shape of a rule of a well-formed environment, at levels `ls`: a closed equation over
binders `Bs` whose left-hand side's body is a definition's constant (without binders), or a
constant applied to arguments with a constant application last: a
recursor at a constructor, or `Quot.lift` at `Quot.mk`. -/
theorem WF.rule_shape {env : VEnv} (henv : env.WF) {df : VDefEq} (h : env.defeqs df)
    {ls : List VLevel} (hls : ls.length = df.uvars) :
    ∃ Bs L R A, df.lhs.instL ls = .lams Bs L ∧ df.rhs.instL ls = .lams Bs R ∧
      df.type.instL ls = .foralls Bs A ∧
      ((Bs = [] ∧ ∃ c, L = .const c ls) ∨
        ∃ (r c : Name) (as bs : List VExpr) (ls' : List VLevel), L = .app ((VExpr.const r ls).appN as) ((VExpr.const c ls').appN bs)) := by
  cases henv.ruleKind h with
  | defn ci _ =>
    refine ⟨[], _, _, _, rfl, rfl, rfl, .inl ⟨rfl, ci.name, ?_⟩⟩
    exact congrArg _ (VLevel.inst_map_id (n := ci.uvars) hls)
  | quot =>
    match ls, hls with
    | [u, v], _ =>
    exact ⟨(peelLams 6 (quotDefEq.lhs.instL [u, v])).1, _, (peelLams 6 (quotDefEq.rhs.instL [u, v])).2,
      (peelForalls 6 (quotDefEq.type.instL [u, v])).2, rfl, rfl, rfl,
      .inr ⟨``Quot.lift, ``Quot.mk, [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1],
        [.bvar 5, .bvar 4, .bvar 0], [u], rfl⟩⟩
  | @iota s d t _ _ hdf =>
    simp only [VInductDecl.iotaRules, List.mem_map] at hdf
    obtain ⟨⟨⟨j, c⟩, q⟩, -, rfl⟩ := hdf
    simp only [VInductDecl.iotaRule, VInductDecl.recConst, VInductDecl.ctorAppAt] at hls ⊢
    obtain ⟨lsC, psC, hC⟩ := ((d.allTypes[j]?).getD default).ctorApp_const c d.recLevels
      (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length))
      (VExpr.bvars c.fields.length 0)
    rw [hC]
    refine ⟨_, _, _, _, lams_instL' _ _ _, lams_instL' _ _ _, foralls_instL' _ _ _,
      .inr ⟨d.recName j, c.name,
        (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) ++
          VExpr.bvars d.allTypes.length (d.allCtors.length + c.fields.length) ++
          VExpr.bvars d.allCtors.length c.fields.length ++
          c.indices.map (fun e => (e.instL d.recLevels).reseat (d.allTypes.length + d.allCtors.length)
            c.fields.length c.fields.length 0 0)).map (·.instL ls),
        (psC ++ VExpr.bvars c.fields.length 0).map (·.instL ls), lsC.map (·.inst ls), ?_⟩⟩
    rw [VExpr.instL_appN, List.map_append, VExpr.appN_append]
    simp only [VExpr.instL_appN, VExpr.instL, List.map_cons, List.map_nil, VExpr.appN]
    rw [VLevel.inst_map_id (by simpa using hls)]

end VEnv
end Lean4Lean

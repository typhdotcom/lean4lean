import Lean4Lean.Theory.Typing.LogRel.Sound

/-!
# Soundness of the model, declaration by declaration

The cases of `strongSound_of` that need an environment's rules (`ExtraSound`, `ProjSound`,
`ProjIotaSound`, `ProjEtaSound`) are about one rule or one recorded block each. They hold of a
well-formed environment if they hold of each declaration's new rules and blocks, given that they
hold of the environment before it: the facts a block's rules need are derivations in the
environment the block was declared in, which the model is already sound for.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {E env : VEnv} {U : Nat}

variable (env U) in
/-- The two sides of an instance of the rule `df` have the same interpretations. -/
def RuleSound (df : VDefEq) : Prop := ∀ (Γ : List VExpr) (ls : List VLevel), (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
  StrongSound env U [] (df.lhs.instL ls) (df.type.instL ls) →
  StrongSound env U [] (df.rhs.instL ls) (df.type.instL ls) →
  StrongSound env U Γ (df.lhs.instL ls) (df.type.instL ls) →
  StrongSound env U Γ (df.rhs.instL ls) (df.type.instL ls) →
  SoundEq env Γ (df.lhs.instL ls) (df.rhs.instL ls)

variable (env U) in
/-- `ProjSound`, `ProjIotaSound` and `ProjEtaSound` for the type `t` of the block `d` recorded at
`s`. -/
def ProjSoundAt (s : Name) (d : VInductDecl) (t : Nat) : Prop :=
  (∀ {Γ T c k f ls As I e u}, d.types[t]? = some T → T.ctors = [c] → c.fields[k]? = some f →
    (∀ l ∈ ls, l.WF U) → ls.length = d.uvars → As.length = d.params.length →
    I.length = T.indices.length → d.ProjAllowed c ls k →
    StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u) →
    StrongSound env U Γ e (.appN (.const s ls) (As ++ I)) →
    StrongSound env U Γ (c.projType ls s k As e) (.sort (f.level.inst ls)) →
    SoundTy env Γ (.proj s k e) (c.projType ls s k As e)) ∧
  (∀ {Γ T c k f fs a ls As I u}, d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → fs[k]? = some a →
    (∀ l ∈ ls, l.WF U) → ls.length = d.uvars → As.length = d.params.length →
    fs.length = c.fields.length → I.length = T.indices.length → d.ProjAllowed c ls k →
    StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u) →
    StrongSound env U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)) →
    StrongSound env U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (.sort (f.level.inst ls)) →
    StrongSound env U Γ a (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) →
    SoundEq env Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a) ∧
  (∀ {Γ T c ls As e u}, d.types[t]? = some T → T.ctors = [c] → T.indices = [] →
    d.isRec = false → (∀ l ∈ ls, l.WF U) → ls.length = d.uvars →
    As.length = d.params.length →
    StrongSound env U Γ (.appN (.const s ls) As) (.sort u) →
    StrongSound env U Γ e (.appN (.const s ls) As) →
    StrongSound env U Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As) →
    SoundEq env Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e)))

variable (E env) in
/-- What soundness of the model of `env` needs of the rules and blocks of `E`. -/
def SoundHyps : Prop :=
  (∀ U df, E.defeqs df → RuleSound env U df) ∧
  ∀ U s d t, E.inducts s = some (d, t) → ProjSoundAt env U s d t

theorem SoundHyps.extra (H : SoundHyps E env) : ExtraSound E env U :=
  fun hdf hls hlen h1 h2 h3 h4 => H.1 _ _ hdf _ _ hls hlen h1 h2 h3 h4

theorem SoundHyps.proj (H : SoundHyps E env) : ProjSound E env U :=
  fun hs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =>
    (H.2 _ _ _ _ hs).1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11

theorem SoundHyps.projIota (H : SoundHyps E env) : ProjIotaSound E env U :=
  fun hs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 =>
    (H.2 _ _ _ _ hs).2.1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14

theorem SoundHyps.projEta (H : SoundHyps E env) : ProjEtaSound E env U :=
  fun hs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
    (H.2 _ _ _ _ hs).2.2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10

/-- The model of `env` is sound for the derivations of any `E ≤ env` whose rules and blocks it is
sound for. -/
theorem SoundHyps.strongSound (hM : ModelEnv env) (hE : E ≤ env) (H : SoundHyps E env)
    (h : E.IsDefEqStrong U Γ M N A) : StrongSoundEq env U Γ M N A :=
  strongSound_of hM hE LevelInv.of H.extra H.proj H.projIota H.projEta h

/-- `strongSound` for a derivation of `IsDefEq`, in a well-formed context of an ordered `E`. -/
theorem SoundHyps.strongSound' (hM : ModelEnv env) (hE : E ≤ env) (H : SoundHyps E env)
    (hO : E.Ordered) (hΓ : OnCtx Γ (E.IsType U)) (h : E.IsDefEq U Γ M N A) :
    StrongSoundEq env U Γ M N A :=
  H.strongSound hM hE (h.strong hO hΓ)

theorem SoundHyps.mono {E₁ E₂ : VEnv} (H : SoundHyps E₂ env)
    (hd : ∀ {df}, E₁.defeqs df → E₂.defeqs df)
    (hi : ∀ {s b}, E₁.inducts s = some b → E₂.inducts s = some b) : SoundHyps E₁ env :=
  ⟨fun U _ h => H.1 U _ (hd h), fun U _ _ _ h => H.2 U _ _ _ (hi h)⟩

theorem SoundHyps.empty : SoundHyps .empty env :=
  ⟨fun _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩

/-- A definition's rule. -/
theorem ruleSound_defn (hM : ModelEnv env) {ci : VDefVal}
    (hc : env.constants ci.name = some ci.toVConstant) (hdf : env.defeqs ci.toDefEq) :
    RuleSound env U ci.toDefEq := by
  intro Γ ls _ hlen _ _ _ h4
  have : ci.toDefEq.lhs.instL ls = .const ci.name ls :=
    congrArg _ (VLevel.inst_map_id (n := ci.uvars) hlen)
  rw [this]
  exact extraSound_defn hM hc hdf hlen h4

variable (env) in
/-- The quotient's computation rule is sound, where `env` has it. -/
def QuotRuleSound : Prop := env.defeqs quotDefEq → ∀ U, RuleSound env U quotDefEq

variable (env) in
/-- A block's iota rules and projections are sound, given that the environment it was declared in
is. -/
def BlockSound : Prop := ∀ {E₁ d E₂}, VDecl.WF E₁ (.induct d) E₂ → E₂ ≤ env → SoundHyps E₁ env →
  (∀ U, ∀ df ∈ d.iotaRules, RuleSound env U df) ∧
  ∀ U s t, E₂.inducts s = some (d, t) → ProjSoundAt env U s d t

/-- The cases of the model's soundness that need the rules hold of a well-formed environment,
given that the quotient's rule and each block's rules and projections are sound. -/
theorem _root_.Lean4Lean.VEnv.WF.soundHyps (henv : env.WF) (hM : ModelEnv env)
    (hQ : QuotRuleSound env) (hB : BlockSound env) : SoundHyps env env := by
  obtain ⟨ds, H₀⟩ := henv
  suffices ∀ {ds' E}, VEnv.WF' ds' E → E ≤ env → SoundHyps E env from this H₀ .rfl
  intro ds' E H hle
  induction H with
  | empty => exact .empty
  | @decl _ E₂ _ E₁ hD hW ih =>
    have IH := ih (hD.le.trans hle)
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 =>
      exact IH.mono (fun h => VEnv.addConst_defeqs h1 ▸ h) (fun h => VEnv.addConst_inducts h1 ▸ h)
    | «example» => exact IH
    | «def» _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addConst_inducts h1 ▸ h)⟩
      rcases h with rfl | h
      · exact ruleSound_defn hM (hle.constants (VEnv.addDefEq_le.constants (VEnv.addConst_self h1)))
          (hle.defeqs (.inl rfl))
      · exact IH.1 U df (VEnv.addConst_defeqs h1 ▸ h)
    | mutualDef _ h1 _ =>
      refine ⟨fun U df h => ?_, fun U s d t h =>
        IH.2 U s d t (VEnv.addConsts_inducts h1 ▸ VEnv.addDefEqs_inducts ▸ h)⟩
      have h' := h
      rcases VEnv.addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
      · exact ruleSound_defn hM
          (hle.constants (VEnv.addDefEqs_le.constants (VEnv.addConsts_constants h1 ci hci)))
          (hle.defeqs h')
      · exact IH.1 U df (VEnv.addConsts_defeqs h1 ▸ h)
    | quot _ h1 =>
      refine ⟨fun U df h => ?_, fun U s d t h => IH.2 U s d t (VEnv.addQuot_inducts h1 ▸ h)⟩
      rcases VEnv.addQuot_defeqs h1 h with rfl | h
      · exact hQ (hle.defeqs h) U
      · exact IH.1 U df h
    | induct hd hg h1 =>
      have ⟨hR, hP⟩ := hB (.induct hd hg h1) hle IH
      refine ⟨fun U df h => ?_, fun U s d' t h => ?_⟩
      · simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
        obtain ⟨envT, hT, envC, hC, envR, hR', hB'⟩ := h1
        rw [VEnv.addBlock_defeqs hB'] at h
        rcases VEnv.addDefEqList_defeqs' h with h | h
        · exact hR U df h
        · rw [VEnv.addConstList_defeqs' hR', VEnv.addConstList_defeqs' hC,
            VEnv.addConstList_defeqs' hT] at h
          exact IH.1 U df h
      · have h1' := h1
        simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
        obtain ⟨envT, hT, envC, hC, envR, hR', hB'⟩ := h1
        rcases VEnv.addBlock_inducts hB' h with h' | ⟨rfl, -⟩
        · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR',
            VEnv.addConstList_inducts hC, VEnv.addConstList_inducts hT] at h'
          exact IH.2 U s d' t h'
        · exact hP U s t h

/-- The model of a well-formed environment, with its own structures, is sound for its typing
rules, given that the quotient's rule and each block's rules and projections are. -/
theorem _root_.Lean4Lean.VEnv.WF.strongSound {env : VEnv} (henv : env.WF)
    (hQ : @QuotRuleSound env.shapeEnv env) (hB : @BlockSound env.shapeEnv env)
    (H : env.IsDefEqStrong U Γ M N A) : @StrongSoundEq env.shapeEnv env U Γ M N A :=
  letI := env.shapeEnv
  (henv.soundHyps henv.modelEnv hQ hB).strongSound henv.modelEnv .rfl H

end LogRel
end Lean4Lean

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

variable [ShapeEnv] [AxInterp] {E env : VEnv} {U : Nat}

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
theorem ruleSound_defn (hM : ModelEnv env) {ci : VDefVal} (hnd : ¬AxInterp.dom ci.name)
    (hc : env.constants ci.name = some ci.toVConstant) (hdf : env.defeqs ci.toDefEq) :
    RuleSound env U ci.toDefEq := by
  intro Γ ls _ hlen _ _ _ h4
  have : ci.toDefEq.lhs.instL ls = .const ci.name ls :=
    congrArg _ (VLevel.inst_map_id (n := ci.uvars) hlen)
  rw [this]
  exact extraSound_defn hM hnd hc hdf hlen h4

variable (E) in
/-- No rule of `E` defines a constant the model interprets by given shapes. -/
def NoDom : Prop := ∀ {df c us}, E.defeqs df → df.lhs = .const c us → ¬AxInterp.dom c

theorem NoDom.mono {E₁ E₂ : VEnv} (H : NoDom E₂) (hd : ∀ {df}, E₁.defeqs df → E₂.defeqs df) :
    NoDom E₁ := fun h => H (hd h)

omit [ShapeEnv] in
theorem NoDom.none {E : VEnv} [ShapeEnv] : @NoDom _ AxInterp.none E := fun _ _ => nofun

variable (env) in
/-- The quotient's computation rule is sound, where `env` has it. -/
def QuotRuleSound : Prop := env.defeqs quotDefEq → ∀ U, RuleSound env U quotDefEq

end LogRel
end Lean4Lean

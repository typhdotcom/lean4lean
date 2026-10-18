import Lean4Lean.Verify.Environment.Assemble

/-!
# The primitive blocks

`Bool` and `Nat` are checked with their constructors already in the environment, as axioms: the
type checker's model of an environment with either type has their constructors
(`VEnv.HasPrimitives`). The specification states what a block means with its types only. Their
constructors' types mention only the type, so what the kernel finds about them holds there too;
the lemmas here establish that for these two shapes, and that the step adding the block keeps the
primitive invariant.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace Primitive

theorem AddsConsts.addConstList : ∀ {env env₁ env₂ : VEnv} {l : List (Name × VExpr)}
    {l' : List (Name × VExpr)},
    env.addConstList (l.map fun p => (p.1, ⟨0, p.2⟩)) = some env₁ → AddsConsts env₁ l' env₂ →
    AddsConsts env (l ++ l') env₂
  | _, _, _, [], _, h, H => by cases h; exact H
  | env, env₁, env₂, (n, ty) :: l, l', h, H => by
    simp only [List.map_cons, VEnv.addConstList, List.foldlM_cons] at h
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact .const h1 (AddsConsts.addConstList h2 H)

theorem AddsConsts.addConstList_other : ∀ {env env₁ env₂ : VEnv} {ps : List (Name × VConstant)}
    {l : List (Name × VExpr)},
    env.addConstList ps = some env₁ → (∀ p ∈ ps, Environment.primitives.contains p.1 = false) →
    AddsConsts env₁ l env₂ → AddsConsts env l env₂
  | _, _, _, [], _, h, _, H => by cases h; exact H
  | env, env₁, env₂, (n, ci) :: ps, l, h, hp, H => by
    simp only [VEnv.addConstList, List.foldlM_cons] at h
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact .other h1 (hp _ (.head _))
      (AddsConsts.addConstList_other h2 (fun p hp' => hp p (.tail _ hp')) H)

theorem AddsConsts.addDefEqList : ∀ {dfs : List VDefEq} {env env₂ : VEnv}
    {l : List (Name × VExpr)},
    AddsConsts (env.addDefEqList dfs) l env₂ → AddsConsts env l env₂
  | [], _, _, _, H => H
  | _ :: dfs, _, _, _, H => .defeq (AddsConsts.addDefEqList (dfs := dfs) H)

/-- An `AddInduct` step whose types and constructors are the constants `cs`, at no level
parameters, and whose recursors are no primitives, adds `cs`. -/
theorem AddsConsts.of_addInduct {safety : DefinitionSafety} {m₁ m₂ : ConstMap} {venv₁ venv₂ : VEnv}
    {d : VInductDecl} (H : AddInduct safety m₁ venv₁ d m₂ venv₂) {cs : List (Name × VExpr)}
    (hcs : d.typeConsts ++ d.ctorConsts = cs.map fun p => (p.1, ⟨0, p.2⟩))
    (hrec : ∀ p ∈ d.recConsts, Environment.primitives.contains p.1 = false) :
    AddsConsts venv₁ cs venv₂ := by
  obtain @⟨-, envT, envC, envR, -, -, -, -, -, -, -, -, -, -, hT, hC, hR, hB⟩ := H
  have hTC : venv₁.addConstList (d.typeConsts ++ d.ctorConsts) = some envC := by
    simp only [VEnv.addConstList, List.foldlM_append] at hT hC ⊢
    rw [hT]; exact hC
  rw [hcs] at hTC
  simpa using AddsConsts.addConstList hTC (AddsConsts.addConstList_other hR hrec
    (AddsConsts.addDefEqList (.block hB .id)))

end Primitive

namespace AddInductive

/-- A constructor type of a primitive block of type `I`: `I`, or a function from `I` to `I`. -/
def PrimCtorType (I : Name) (e : Expr) : Prop :=
  e = .const I [] ∨ ∃ nm bi, e = .forallE nm (.const I []) (.const I []) bi

/-- Its translation. -/
def primCtorTr (I : Name) : Expr → VExpr
  | .forallE .. => .forallE (.const I []) (.const I [])
  | _ => .const I []

theorem primConst_isType {venv : VEnv} {I : Name} {Γ : List VExpr}
    (hI : venv.constants I = some ⟨0, .sort (.succ .zero)⟩) :
    venv.HasType 0 Γ (.const I []) (.sort (.succ .zero)) := by
  have := VEnv.HasType.const (env := venv) (U := 0) (Γ := Γ) (ls := []) hI (by simp) rfl
  simpa [VExpr.instL, VLevel.inst] using this

theorem primCtor_tr {venv : VEnv} {I : Name} {e : Expr}
    (hI : venv.constants I = some ⟨0, .sort (.succ .zero)⟩) (h : PrimCtorType I e) :
    TrExprS venv [] [] e (primCtorTr I e) ∧ venv.IsType 0 [] (primCtorTr I e) ∧
      ∀ C', TrExprS venv [] [] e C' → C' = primCtorTr I e := by
  have hc : ∀ Δ, TrExprS venv [] Δ (.const I []) (.const I []) := fun _ =>
    .const hI rfl rfl
  have htr : TrExprS venv [] [] e (primCtorTr I e) := by
    rcases h with rfl | ⟨nm, bi, rfl⟩
    · exact hc _
    · exact .forallE ⟨_, primConst_isType hI⟩ ⟨_, primConst_isType hI⟩ (hc _) (hc _)
  refine ⟨htr, ?_, fun C' h' => TrExprS.unique (TrExprS.IsUnique.all _) h' htr⟩
  rcases h with rfl | ⟨nm, bi, rfl⟩
  · exact ⟨_, primConst_isType hI⟩
  · exact ⟨_, .forallE (primConst_isType hI) (primConst_isType hI)⟩

/-- What `checkConstructors` establishes of a primitive constructor holds in any environment with
the type. -/
theorem primCtor_checked {venv : VEnv} {I : Name}
    (hI : venv.constants I = some ⟨0, .sort (.succ .zero)⟩) {d : VInductDecl} (hdu : d.uvars = 0)
    (hdp : d.params = []) {T : VInductiveType} (hdT : d.types[0]? = some T) (hTn : T.name = I)
    (hTno : T.nested = none)
    (hTi : T.indices = []) (hlev : d.level ≈ .succ .zero) {t : InductiveType} (htn : t.name = I)
    {ct : Constructor} (hct : PrimCtorType I ct.type) : CtorChecked venv [] d t 0 ct := by
  intro C' htr
  obtain ⟨-, hCT, hu⟩ := primCtor_tr hI hct
  obtain rfl := hu C' htr
  refine ⟨hCT, ?_⟩
  have hII : venv.IsDefEqU d.uvars [] (.const I []) (.const I []) := by
    rw [hdu]; exact ⟨_, primConst_isType hI⟩
  rcases hct with he | ⟨nm, bi, he⟩ <;> rw [he] <;> rw [he] at htr
  · refine ⟨[], [], [], by simp [primCtorTr, htn, hdp, VExpr.bvars, VLevel.params],
      rfl, by rw [hdp]; exact .nil, rfl, rfl, .nil, fun _ _ h => by simp at h, fun m hm => ?_⟩
    obtain rfl : m = 0 := by simpa using hm
    exact .nil nofun nofun nofun
  · refine ⟨[], [.const I []], [], by simp [primCtorTr, htn, hdp, VExpr.bvars, VLevel.params],
      rfl, by rw [hdp]; exact .nil, rfl, rfl, ?_, fun k D h => ?_, fun m hm => ?_⟩
    rotate_left
    · obtain ⟨rfl, rfl⟩ : k = 0 ∧ D = .const I [] := by cases k <;> simp_all
      intro P _
      simp only [Expr.domStrips, Expr.annStrips, List.drop_zero, List.length_nil, List.zip_cons_cons,
        List.zip_nil_right, List.map_cons, List.map_nil, VExpr.stripN, keptTysBy,
        VConstructor.keptIdxBy, List.range_zero, List.filter_nil, List.reverse_nil, hdp,
        List.nil_append, List.getElem?_cons_zero, Option.getD_some, VConstructor.strippedTypeBy,
        VExpr.subst]
      exact ⟨⟨_, primConst_isType hI⟩, fun _ => ⟨_, primConst_isType hI⟩⟩
    · have hc : TrExprS venv [] [] (.const I []) (.const I []) := .const hI rfl rfl
      rcases (show m = 0 ∨ m = 1 by simp at hm; omega) with rfl | rfl
      · exact .cons hc ⟨_, primConst_isType hI⟩ (.nil nofun nofun nofun)
      · simp [Expr.dropU_forallE, Expr.hasLooseBVar', Expr.lowerLooseBVars']
        exact .nil nofun nofun nofun
    refine .cons ⟨.succ .zero, by rw [hdu]; exact primConst_isType hI,
      .inr fun ls => by rw [show d.level.eval ls = (VLevel.succ .zero).eval ls from
        congrFun hlev ls]; exact Nat.le_refl _⟩ (fun _ => ?_) .nil
    refine .app (j := 0) (is := []) (VInductDecl.allTypes_getElem?_of_types hdT) (by simp [hTi]) ?_
      (by simp)
    simpa [VInductiveType.typeApp_of_none hTno, hTn, hdp, hdu, VExpr.bvars, VLevel.params,
      VExpr.appN] using hII

/-- Axioms added one after another, each of a type of the environment before them, model the
constants added to the environment's model. -/
theorem trEnv_addAxiomList {env : Environment} {venv : VEnv} {safety : DefinitionSafety} :
    ∀ (axs : List AxiomVal) (cs : List (Name × VConstant)) {venv' : VEnv},
    TrEnv safety env venv →
    List.Forall₂ (fun (ax : AxiomVal) (p : Name × VConstant) => ax.name = p.1 ∧
      TrConstant safety venv (.axiomInfo ax) p.2 ∧ p.2.WF venv) axs cs →
    (axs.map (·.name)).Nodup → (∀ ax ∈ axs, env.find? ax.name = none) →
    venv.addConstList cs = some venv' →
    TrEnv safety (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env) venv'
  | [], [], _, wf, .nil, _, _, e => by cases e; exact wf
  | ax :: axs, p :: cs, venv', wf, .cons ⟨hn, htr, hwf⟩ tl, hnd, hfr, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [VEnv.addConstList, List.foldlM_cons] at e
    obtain ⟨venv₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 e
    have h₁' : venv.addConst ax.name p.2 = some venv₁ := hn ▸ h₁
    have hle := VEnv.addConst_le h₁'
    have hax : (ConstantInfo.axiomInfo ax).name = ax.name := rfl
    have wf₁ : TrEnv safety (env.add (.axiomInfo ax)) venv₁ :=
      TrEnv'.axiom (ci := ax) htr
        (by rw [← wf.map_wf.find?'_eq_find?]; exact hfr _ (.head _)) hwf h₁' wf
    refine trEnv_addAxiomList axs cs wf₁ ?_ hnd.2 (fun a ha => ?_) h₂
    · exact Lean4Lean.List.Forall₂.imp (fun _ _ h =>
        ⟨h.1, h.2.1.mono hle, h.2.2.mono hle⟩) tl
    · have hne : ax.name ≠ a.name := fun hh => hnd.1 (List.mem_map.2 ⟨a, ha, hh.symm⟩)
      exact Environment.find?_add_of_ne wf.map_wf _ (hax ▸ hfr _ (.head _)) (hax ▸ hne)
        (hfr a (.tail _ ha))

/-- Axioms added one after another keep every primitive name safe and without level parameters,
when the primitive ones among them are. -/
theorem safePrimitives_addAxiomList {env : Environment} (mapWF : env.constants.WF)
    (old : ∀ {n : Name} {ci}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []) :
    ∀ (axs : List AxiomVal), (axs.map (·.name)).Nodup → (∀ ax ∈ axs, env.find? ax.name = none) →
    (∀ ax ∈ axs, Environment.primitives.contains ax.name →
      ax.isUnsafe = false ∧ ax.levelParams = []) →
    ∀ {n : Name} {ci}, (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  | [], _, _, _ => old
  | ax :: axs, hnd, hfr, hok => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hnone : env.constants.find? ax.name = none := by
      rw [← mapWF.find?'_eq_find?]; exact hfr _ (.head _)
    refine safePrimitives_addAxiomList (mapWF.insert _ _ hnone)
      (fun h hp => safePrimitives_add' mapWF old (.axiomInfo ax) (hfr _ (.head _))
        (fun hp' => ?_) h hp) axs hnd.2 (fun a ha => ?_) (fun a ha => hok a (.tail _ ha))
    · obtain ⟨h1, h2⟩ := hok ax (.head _) hp'
      exact ⟨by simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h1], h2⟩
    · have hax : (ConstantInfo.axiomInfo ax).name = ax.name := rfl
      have hne : ax.name ≠ a.name := fun hh => hnd.1 (List.mem_map.2 ⟨a, ha, hh.symm⟩)
      exact Environment.find?_add_of_ne mapWF _ (hax ▸ hfr _ (.head _)) (hax ▸ hne)
        (hfr a (.tail _ ha))

/-- The axioms `declareTypeAxioms` adds for a primitive block: its type, then its constructors. -/
def primAxioms (type : InductiveType) : List AxiomVal :=
  { name := type.name, levelParams := [], type := type.type, isUnsafe := false } ::
    type.ctors.map fun ct => { name := ct.name, levelParams := [], type := ct.type, isUnsafe := false }

/-- `declareTypeAxioms` on a primitive block: its type and constructors as axioms, which model the
constants `cs`, keeping the primitive invariant. -/
theorem declareTypeAxioms.WF_prim {c : VContext} {type : InductiveType}
    {cs : List (Name × VExpr)} (hap : c.allowPrimitive = true) (hU : c.lparams = [])
    (hsafety : c.safety = .safe) (htype : type.type = .sort (.succ .zero))
    (hct : ∀ ct ∈ type.ctors, PrimCtorType type.name ct.type)
    (hcs : cs = (type.name, .sort (.succ .zero)) ::
      type.ctors.map fun ct => (ct.name, primCtorTr type.name ct.type))
    (hfresh : c.env.find? type.name = none)
    (hprim : ∀ {venv env' : VEnv}, venv.HasPrimitives → Primitive.AddsConsts venv cs env' →
      env'.HasPrimitives) :
    AddInductive.WF c (declareTypeAxioms #[type] false) fun envAx => ∃ venvT venvAx,
      c.venv.addConstList [(type.name, ⟨0, .sort (.succ .zero)⟩)] = some venvT ∧
      venvT.addConstList (type.ctors.map fun ct => (ct.name, ⟨0, primCtorTr type.name ct.type⟩)) =
        some venvAx ∧
      VEnvAt envAx .safe venvAx ∧
      envAx = (primAxioms type).foldl (fun e ax => e.add (.axiomInfo ax)) c.env ∧
      ((primAxioms type).map (·.name)).Nodup ∧
      ∀ ax ∈ primAxioms type, c.env.find? ax.name = none := by
  intro envAx h
  let typeAx : AxiomVal :=
    { name := type.name, levelParams := [], type := type.type, isUnsafe := false }
  let f (ct : Constructor) : ConstantInfo :=
    .axiomInfo { name := ct.name, levelParams := [], type := ct.type, isUnsafe := false }
  let env₁ := c.env.add (.axiomInfo typeAx)
  have h' : (type.ctors.foldlM (m := Except Exception) (init := env₁)
      fun (env : Environment) ct => do env.checkName (f ct).name true; return env.add (f ct)) =
      .ok envAx := by
    simp only [declareTypeAxioms, hap, if_true, hU] at h
    rw [show #[type] = [type].toArray from rfl, List.foldlM_toArray] at h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    exact h
  have mapWF := c.envAt.tr.map_wf
  have hnone : c.env.constants.find? type.name = none := by
    rw [← mapWF.find?'_eq_find?]; exact hfresh
  have mapWF₁ : env₁.constants.WF := mapWF.insert _ _ hnone
  obtain ⟨-, -, hnd, hfr, -⟩ := addChecked.WF mapWF₁ true f type.ctors _ h'
  have henv := addChecked.eq_foldl true type.ctors h'
  have hnd' : (type.ctors.map (·.name)).Nodup := by
    simpa [List.map_map, Function.comp_def, f, ConstantInfo.name, ConstantInfo.toConstantVal]
      using hnd
  have hfr₁ (ct) (hct : ct ∈ type.ctors) : env₁.find? ct.name = none := by
    have := hfr (f ct) (List.mem_map_of_mem hct)
    rwa [Kernel.Environment.find?, mapWF₁.find?'_eq_find?]
  have hne (ct) (hct : ct ∈ type.ctors) : ct.name ≠ type.name := by
    intro he
    have := hfr₁ ct hct
    rw [he] at this
    change SMap.find?' (c.env.constants.insert type.name (.axiomInfo typeAx)) type.name = none at this
    rw [(mapWF.insert _ _ hnone).find?'_eq_find?, mapWF.find?_insert, if_pos (by simp)] at this
    cases this
  have hfr₀ (ct) (hct : ct ∈ type.ctors) : c.env.find? ct.name = none := by
    have := hfr₁ ct hct
    change SMap.find?' (c.env.constants.insert type.name (.axiomInfo typeAx)) ct.name = none at this
    rw [(mapWF.insert _ _ hnone).find?'_eq_find?, mapWF.find?_insert,
      if_neg (by simpa using (hne ct hct).symm)] at this
    rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]
  -- the models
  have hvT : c.venv.constants type.name = none := c.envAt.tr.constants_eq_none hfresh
  obtain ⟨venvT, hT⟩ : ∃ venvT, c.venv.addConstList [(type.name, ⟨0, .sort (.succ .zero)⟩)] =
      some venvT := VEnv.exists_addConstList (by simpa using hvT) (by simp)
  have hT' : c.venv.addConst type.name ⟨0, .sort (.succ .zero)⟩ = some venvT := by
    simpa [VEnv.addConstList] using hT
  have hleT := VEnv.addConst_le hT'
  have hIT : venvT.constants type.name = some ⟨0, .sort (.succ .zero)⟩ :=
    VEnv.addConstList_constants_of_mem hT (.head _)
  have hcsfr : ∀ p ∈ type.ctors.map (fun ct => (ct.name,
      (⟨0, primCtorTr type.name ct.type⟩ : VConstant))), venvT.constants p.1 = none := by
    intro p hp
    obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hp
    exact VEnv.addConstList_constants_none hT (c.envAt.tr.constants_eq_none (hfr₀ ct hct))
      (by simpa using hne ct hct)
  obtain ⟨venvAx, hAx⟩ := VEnv.exists_addConstList hcsfr (by
    simpa [List.map_map, Function.comp_def] using hnd')
  have hsafe (ax : AxiomVal) (h : ax.isUnsafe = false) :
      DefinitionSafety.safe ≤ (ConstantInfo.axiomInfo ax).safety := by
    simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h]
    exact DefinitionSafety.le_rfl
  have hwf1 : VConstant.WF c.venv ⟨0, .sort (.succ .zero)⟩ := ⟨_, .sort (by simp [VLevel.WF])⟩
  have htrT : TrEnv .safe env₁ venvT := by
    refine TrEnv'.axiom (ci := typeAx) ⟨hsafe _ rfl, rfl, ?_⟩ hnone hwf1 hT'
      (hsafety ▸ c.envAt.tr)
    show TrExprS c.venv [] [] type.type _
    rw [htype]; exact .sort rfl
  -- the constructors, as axioms of their types in the model with the type
  have hctr : ∀ l : List Constructor, (∀ ct ∈ l, PrimCtorType type.name ct.type) →
      List.Forall₂ (fun (ax : AxiomVal) (p : Name × VConstant) => ax.name = p.1 ∧
        TrConstant .safe venvT (.axiomInfo ax) p.2 ∧ p.2.WF venvT)
      (l.map fun ct => { name := ct.name, levelParams := [], type := ct.type, isUnsafe := false })
      (l.map fun ct => (ct.name, ⟨0, primCtorTr type.name ct.type⟩)) := by
    intro l hl
    induction l with
    | nil => exact .nil
    | cons ct l ih =>
      obtain ⟨h1, h2, -⟩ := primCtor_tr hIT (hl ct (.head _))
      exact .cons ⟨rfl, ⟨hsafe _ rfl, rfl, h1⟩, h2⟩ (ih fun ct' h => hl ct' (.tail _ h))
  have hpnd : ((primAxioms type).map (·.name)).Nodup := by
    simp only [primAxioms, List.map_cons, List.map_map, List.nodup_cons]
    refine ⟨fun hm => ?_, by simpa [Function.comp_def] using hnd'⟩
    obtain ⟨ct, hct, he⟩ := List.mem_map.1 hm
    exact hne ct hct he
  have hpfr : ∀ ax ∈ primAxioms type, c.env.find? ax.name = none := by
    intro ax hax
    simp only [primAxioms, List.mem_cons, List.mem_map] at hax
    rcases hax with rfl | ⟨ct, hct, rfl⟩
    · exact hfresh
    · exact hfr₀ ct hct
  have henv' : envAx = (primAxioms type).foldl (fun e ax => e.add (.axiomInfo ax)) c.env := by
    rw [henv]; simp [primAxioms, List.foldl_map, f, env₁, typeAx]
  have htrAx : TrEnv .safe envAx venvAx := by
    have := trEnv_addAxiomList _ _ htrT (hctr _ hct) (by
      simpa [List.map_map, Function.comp_def] using hnd') (fun ax hax => by
        obtain ⟨ct, hct', rfl⟩ := List.mem_map.1 hax; exact hfr₁ ct hct') hAx
    rw [henv]; simpa [List.foldl_map, f] using this
  have hall : c.venv.addConstList (cs.map fun p => (p.1, ⟨0, p.2⟩)) = some venvAx := by
    rw [hcs]
    simp only [List.map_cons, List.map_map, VEnv.addConstList, List.foldlM_cons]
    simp only [VEnv.addConstList] at hT hAx
    simp only [List.foldlM_cons, List.foldlM_nil] at hT
    rw [show c.venv.addConst type.name ⟨0, .sort (.succ .zero)⟩ = some venvT from hT'];
    simpa [Function.comp_def] using hAx
  refine ⟨venvT, venvAx, hT, hAx, ⟨htrAx, hprim c.envAt.hasPrimitives
      (by simpa using Primitive.AddsConsts.addConstList (l' := []) hall .id), ?_⟩,
    henv', hpnd, hpfr⟩
  intro n ci hn hp
  rw [henv'] at hn
  refine safePrimitives_addAxiomList mapWF c.envAt.safePrimitives _ hpnd hpfr
    (fun ax hax _ => ?_) hn hp
  simp only [primAxioms, List.mem_cons, List.mem_map] at hax
  rcases hax with rfl | ⟨ct, -, rfl⟩ <;> exact ⟨rfl, rfl⟩

theorem appN_ne_forallE {A B : VExpr} : ∀ (is : List VExpr) (f : VExpr),
    (∀ A' B', f ≠ .forallE A' B') → f.appN is ≠ .forallE A B
  | [], _, h => h _ _
  | _ :: is, _, _ => appN_ne_forallE is _ nofun

theorem primField_level {venv : VEnv} {I : Name} (henv : venv.WF)
    (hI : venv.constants I = some ⟨0, .sort (.succ .zero)⟩) {l : VLevel}
    (h : venv.HasType 0 [] (.const I []) (.sort l)) : l ≈ .succ .zero :=
  (VEnv.IsDefEq.uniqU henv trivial h (primConst_isType hI)).sort_inv henv trivial

/-- A primitive block elaborated in the environment with its constructors as axioms is elaborated
in the one with its type only: the fields' types and their inductive hypotheses' views are the
type itself. -/
theorem elaborates_prim {venvT venvAx : VEnv} {I : Name} (hle : venvT ≤ venvAx)
    (henvAx : venvAx.WF)
    (hIT : venvT.constants I = some ⟨0, .sort (.succ .zero)⟩) {envAx : Environment}
    (hax : ∃ ax, envAx.find? I = some (.axiomInfo ax)) {type : InductiveType}
    (htn : type.name = I) (hct : ∀ ct ∈ type.ctors, PrimCtorType I ct.type)
    {level : VLevel} {d : VInductDecl} (hEl : Elaborates venvAx [] 0 level [type] d)
    (hdu : d.uvars = 0) (hdp : d.params = []) (hdi : ∀ T ∈ d.types, T.indices = [])
    (hda : d.aux = []) (hdn : ∀ T ∈ d.types, T.nested = none)
    (hfirst : List.Forall₂ (fun (t : InductiveType) (T : VInductiveType) =>
      List.Forall₂ (fun (ct : Constructor) (cv : VConstructor) => ∀ nm D b bi,
        ct.type = .forallE nm D b bi → D.consumeTypeAnnotations' = D → ∀ f, cv.fields[0]? = some f →
          TrExprS venvAx [] [] D f.type ∧
          ∀ n us ax ra, D = .const n us → envAx.find? n = some (.axiomInfo ax) →
            f.recArg = some ra → ra.binders = []) t.ctors T.ctors) [type] d.types) :
    Elaborates venvT [] 0 level [type] d := by
  have hIAx := hle.1 hIT
  obtain ⟨T, hT⟩ : ∃ T, d.types = [T] :=
    List.length_eq_one_iff.1 (Lean4Lean.List.Forall₂.length_eq hEl.types).symm
  refine ⟨hEl.level, ?_⟩
  obtain ⟨hTn, hcs⟩ : T.name = type.name ∧ _ := by
    have := hEl.types; rw [hT] at this; cases this with | cons h _ => exact h
  have hf := hfirst; rw [hT] at hf
  cases hf with | cons hf _ => ?_
  rw [hT]
  refine .cons ⟨hTn, ?_⟩ .nil
  have hTi : T.indices = [] := hdi T (by rw [hT]; exact .head _)
  have : ∀ (cts : List Constructor) (cvs : List VConstructor), (∀ ct ∈ cts, PrimCtorType I ct.type) →
      List.Forall₂ (fun (ct : Constructor) (c : VConstructor) => c.name = ct.name ∧
        TrExprS venvAx [] [] ct.type c.type ∧ ∃ ps Ds, ps.length = 0 ∧ Ds.length = c.fields.length ∧
          c.type = .foralls (ps ++ Ds) (.appN (.const type.name (VLevel.params ([] : List Name).length))
            (VExpr.bvars 0 Ds.length ++ c.indices)) ∧
          FieldsElab venvAx d d.params.reverse 0 Ds c.fields ∧
          (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
            D.StripsToBy (· ∉ [type].map (·.name)) f.type) ∧
          (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f → ∀ u,
            venvAx.HasType ([] : List Name).length ((Ds.take k).reverse ++ ps.reverse) D (.sort u) →
            (u ≈ .zero ↔ f.level ≈ .zero)) ∧
          ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
            f.type = D.stripN ((ct.type.domStrips.drop 0)[k]?.getD 0)) cts cvs →
      List.Forall₂ (fun (ct : Constructor) (cv : VConstructor) => ∀ nm D b bi,
        ct.type = .forallE nm D b bi → D.consumeTypeAnnotations' = D → ∀ f, cv.fields[0]? = some f →
          TrExprS venvAx [] [] D f.type ∧
          ∀ n us ax ra, D = .const n us → envAx.find? n = some (.axiomInfo ax) →
            f.recArg = some ra → ra.binders = []) cts cvs →
      List.Forall₂ (fun (ct : Constructor) (c : VConstructor) => c.name = ct.name ∧
        TrExprS venvT [] [] ct.type c.type ∧ ∃ ps Ds, ps.length = 0 ∧ Ds.length = c.fields.length ∧
          c.type = .foralls (ps ++ Ds) (.appN (.const type.name (VLevel.params ([] : List Name).length))
            (VExpr.bvars 0 Ds.length ++ c.indices)) ∧
          FieldsElab venvT d d.params.reverse 0 Ds c.fields ∧
          (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
            D.StripsToBy (· ∉ [type].map (·.name)) f.type) ∧
          (∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f → ∀ u,
            venvT.HasType ([] : List Name).length ((Ds.take k).reverse ++ ps.reverse) D (.sort u) →
            (u ≈ .zero ↔ f.level ≈ .zero)) ∧
          ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
            f.type = D.stripN ((ct.type.domStrips.drop 0)[k]?.getD 0)) cts cvs := by
    intro cts cvs hp h1 h2
    induction h1 with
    | nil => exact .nil
    | @cons ct cv cts cvs h ht ih =>
      cases h2 with | cons hf2 ht2 => ?_
      refine .cons ?_ (ih (fun c hc => hp c (.tail _ hc)) ht2)
      obtain ⟨hn, htrA, ps, Ds, hps, hDs, hsh, hFE, hstr, hlv, hviews⟩ := h
      have hpc := hp ct (.head _)
      obtain ⟨htrT, -, -⟩ := primCtor_tr hIT hpc
      obtain ⟨-, -, huA⟩ := primCtor_tr hIAx hpc
      have hcv := huA _ htrA
      obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hps
      refine ⟨hn, hcv ▸ htrT, [], Ds, rfl, hDs, hsh, ?_, hstr,
        fun k D f h1 h2 u h3 => hlv k D f h1 h2 u (h3.mono hle), hviews⟩
      rcases hpc with he | ⟨nm, bi, he⟩
      · -- no field
        rw [he] at hcv
        obtain rfl : Ds = [] := by
          rcases Ds with _ | ⟨D, Ds⟩
          · rfl
          · rw [hcv] at hsh; simp [primCtorTr] at hsh
        obtain h0 : cv.fields = [] := List.eq_nil_of_length_eq_zero (by simpa using hDs.symm)
        rw [h0]; exact .nil
      · -- one field, the type itself
        rw [he] at hcv
        rcases Ds with _ | ⟨D, _ | ⟨D', Ds⟩⟩
        · rw [hcv] at hsh; simp [primCtorTr, VExpr.bvars] at hsh
          exact absurd hsh.symm (appN_ne_forallE _ _ nofun)
        · obtain ⟨f, hf0⟩ : ∃ f, cv.fields = [f] := by
            match cv.fields, hDs with
            | [f], _ => exact ⟨f, rfl⟩
          have hD : D = .const I [] := by
            rw [hcv] at hsh; simp [primCtorTr, VExpr.foralls] at hsh; exact hsh.1.symm
          subst hD
          obtain ⟨hftr, hrab⟩ := hf2 nm (.const I []) (.const I []) bi he rfl f (by simp [hf0])
          have hfty : f.type = .const I [] :=
            TrExprS.unique (TrExprS.IsUnique.all _) hftr (.const hIAx rfl rfl)
          rw [hf0] at hFE ⊢
          cases hFE with | cons hdefA hwA hsA hlwf hraA hrest => ?_
          rw [hdu, hdp] at hsA
          have hlv1 := primField_level henvAx hIAx (hfty ▸ hsA)
          refine .cons ?_ hwA ?_ hlwf ?_ (by cases hrest; exact .nil)
          · rw [hfty, hdu]; exact ⟨_, primConst_isType hIT⟩
          · rw [hfty, hdu]
            exact .defeqDF (.sortDF (by simp [VLevel.WF]) (by simpa [hdu] using hlwf)
              (show VLevel.succ .zero ≈ f.level from hlv1.symm)) (primConst_isType hIT)
          · unfold VInductDecl.RecArgWF at hraA ⊢
            split at hraA
            · rename_i ra hra
              obtain ⟨T', hT', hil, -⟩ := hraA
              have hb := hrab I [] hax.choose ra rfl hax.choose_spec hra
              obtain rfl : T' = T := by
                rw [VInductDecl.allTypes_of_aux hda, hT] at hT'
                simpa using (List.getElem?_eq_some_iff.1 hT').2.symm
              have hri : ra.indices = [] := List.eq_nil_of_length_eq_zero (by rw [hil, hTi]; rfl)
              refine ⟨T', hT', hil, ?_, by rw [hb]; rfl, by rw [hri]; rfl⟩
              rw [VInductiveType.typeApp_of_none (hdn T' (by rw [hT]; exact .head _)), hfty, hb, hri,
                hdu, hTn, htn, hdp]
              exact ⟨_, primConst_isType hIT⟩
            · trivial
        · rw [hcv] at hsh; simp [primCtorTr, VExpr.foralls] at hsh
  exact this type.ctors T.ctors hct hcs hf

end AddInductive

/-- `AddInductive.run` on a primitive block, `Bool` or `Nat` as the prelude declares them. The block
is checked with its constructors as axioms too, so `checkConstructors` establishes what it does in
an environment that already has them, while `AddInduct` asks for the constructors' types in the
one with only the types. What closes the gap is that these types mention only the block's type,
which for `Bool` and `Nat` is a computation; the primitive clauses of `FlatResult` are what
`PrimitiveInductiveResult` supplies. -/
theorem AddInductive.run.WF_primitive {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (hallow : Primitive.PrimitiveInductiveResult lparams nparams types isUnsafe) :
    (AddInductive.run nparams types 0
      { env, allowPrimitive := true, lparams, fuel, safety := inductSafety isUnsafe }).WF
      (FlatResult ves env lparams nparams types isUnsafe true 0) := by
  obtain ⟨rfl, rfl, rfl, type, cs, rfl, htype, hshape, hpres⟩ := hallow
  -- the block: `Bool` or `Nat`
  obtain ⟨hI, hct, hcs⟩ : (type.name = ``Bool ∨ type.name = ``Nat) ∧
      (∀ ct ∈ type.ctors, AddInductive.PrimCtorType type.name ct.type) ∧
      cs = (type.name, .sort (.succ .zero)) ::
        type.ctors.map fun ct => (ct.name, AddInductive.primCtorTr type.name ct.type) := by
    rcases hshape with ⟨hn, rfl, hc⟩ | ⟨hn, rfl, nm, bi, hc⟩ <;> rw [hc] <;>
      refine ⟨by simp [hn], ?_, by simp [hn, AddInductive.primCtorTr]; rfl⟩ <;>
      simp [AddInductive.PrimCtorType, hn]
  have hdum : type.name ≠ `_inhabitedExprDummy := by rcases hI with h | h <;> rw [h] <;> decide
  have hrecnp : Environment.primitives.contains (Lean.mkRecName type.name) = false := by
    rcases hI with h | h <;> rw [h] <;>
      simp +decide [Environment.primitives, NameSet.ofList, NameSet.contains]
  have htype' : type.type = .sort (.succ .zero) := htype
  let c₀ := AddInductive.VContext.top (wf.toVEnvAt (inductSafety false)) [] true fuel
  change AddInductive.WF c₀ (AddInductive.run 0 [type] 0) _
  unfold AddInductive.run
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind AddInductive.WF.read fun _ hr => ?_; subst hr
  refine AddInductive.WF.bind (AddInductive.WF.liftExcept (checkDuplicatedUnivParams.WF _))
    fun _ _ => ?_
  have hsafe : (c₀.safety != .safe) = false := rfl
  simp only [hsafe]
  have henv₀ := (wf.tr (safety := inductSafety false)).wf
  refine AddInductive.checkInductiveTypes.WF rfl henv₀
    (show ConstMap.Closed env.constants from TrEnv'.closed (wf.tr (safety := .unsafe)) wf.hasPrimitives) (List.cons_ne_nil _ _)
    fun stats c params level typeTr hT => ?_
  have hb := hT.base
  have hcl : c.lparams = [] := hb.lparams
  have hcs₀ : c.safety = .safe := hb.safety
  have hcp : c.allowPrimitive = true := hb.allowPrimitive
  have hcenv : c.env = env := hb.env
  have hcvenv : c.venv = ves.venv .safe := hb.venv
  obtain rfl : params = [] := List.eq_nil_of_length_eq_zero hT.nparams
  obtain ⟨T', rfl⟩ : ∃ T', typeTr = [T'] :=
    List.length_eq_one_iff.1 (by rw [hT.typeTr_length]; rfl)
  obtain ⟨idx, u, htrT', -, hdefT, hul, hni, -⟩ := hT.types 0 type T' rfl rfl
  have hT'eq : T' = .sort (.succ .zero) := by
    rw [htype'] at htrT'
    cases htrT' with | sort h => simp [VLevel.ofLevel] at h; rw [h]
  subst hT'eq
  have henvc₀ : c₀.venv.WF := henv₀
  obtain rfl : idx = [] := by
    rcases idx with _ | ⟨A, idx⟩
    · rfl
    · exact absurd hdefT (VEnv.IsDefEqU.sort_forallE_inv henvc₀ trivial)
  have hlev : level ≈ .succ .zero := by
    have h1 : VLevel.succ .zero ≈ u := VEnv.IsDefEqU.sort_inv henvc₀ trivial hdefT
    exact (show level.eval = u.eval from hul.symm).trans h1.symm
  refine AddInductive.WF.bind (AddInductive.WF.and AddInductive.declareInductiveTypes.WF
    AddInductive.declareInductiveTypes.ne_dummy)
    fun envTypes ⟨⟨hDc, hDq, hDnd, hDfr, _⟩, _⟩ => ?_
  have hnames' := AddInductive.inductVals_names (lparams := c.lparams) (numParams := 0)
    (numNested := 0) (isUnsafe := false) hT.nindices
  have hfrI : c.env.find? type.name = none := by
    obtain ⟨ci, h1, h2⟩ : ∃ ci ∈ (AddInductive.inductVals c.lparams stats 0 [type].toArray 0
        false).map ConstantInfo.inductInfo, ci.name = type.name := by
      have : type.name ∈ [type].map (·.name) := by simp
      rw [← hnames'] at this
      obtain ⟨ci, h1, h2⟩ := List.mem_map.1 this
      exact ⟨ci, h1, h2⟩
    have := hDfr ci h1
    rwa [h2, ← c.envAt.tr.map_wf.find?'_eq_find?] at this
  refine AddInductive.WF.bind (AddInductive.declareTypeAxioms.WF_prim (cs := cs) hcp hcl hcs₀
    htype' hct hcs hfrI hpres) fun envAx hAx => ?_
  obtain ⟨venvT, venvAx, hT₁, hAx₁, wfAx₀, hAxe, hpnd, hpfr⟩ := hAx
  have wfAx : VEnvAt envAx c.safety venvAx := hcs₀ ▸ wfAx₀
  have hleT : c.venv ≤ venvT := VEnv.addConstList_le hT₁
  have hleTA : venvT ≤ venvAx := VEnv.addConstList_le hAx₁
  have hleAx : c.venv ≤ venvAx := hleT.trans hleTA
  refine AddInductive.WF.withEnv wfAx hleAx ?_
  have hle₀ : c₀.venv ≤ venvAx := hb.venv ▸ hleAx
  refine AddInductive.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  have mapWFT : envTypes.constants.WF := by
    rw [hDc]; exact insertConsts_wf c.envAt.tr.map_wf hDfr hDnd
  refine AddInductive.WF.bind (AddInductive.WF.withEnvRaw
    (AddInductive.declareConstructors.WF (c := { (c.withEnv envAx venvAx wfAx hleAx).toContext with
      env := envTypes }) mapWFT)) fun envCtors hDC => ?_
  have hDC' : envCtors.constants = insertConsts envTypes.constants
        ((AddInductive.ctorVals c.lparams stats.params.size [type] false).map .ctorInfo) ∧
      envCtors.quotInit = envTypes.quotInit ∧
      (((AddInductive.ctorVals c.lparams stats.params.size [type] false).map
        ConstantInfo.ctorInfo).map (·.name)).Nodup ∧
      ∀ ci ∈ (AddInductive.ctorVals c.lparams stats.params.size [type] false).map
        ConstantInfo.ctorInfo, envTypes.constants.find? ci.name = none :=
    ⟨hDC.1, hDC.2.1, hDC.2.2.1, hDC.2.2.2.1⟩
  clear hDC
  -- what `checkConstructors` establishes, in any environment with the type
  have hIT : venvT.constants type.name = some ⟨0, .sort (.succ .zero)⟩ :=
    VEnv.addConstList_constants_of_mem hT₁ (.head _)
  have hIAx : venvAx.constants type.name = some ⟨0, .sort (.succ .zero)⟩ := hleTA.1 hIT
  have hdT : ∀ d, AddInductive.Compat c.lparams [] level false [type] stats.nindices d →
      ∃ T, d.types = [T] ∧ T.name = type.name ∧ T.indices = [] := by
    intro d hd
    have hn := hd.names
    simp only [VInductDecl.names, List.map_cons, List.map_nil] at hn
    obtain ⟨T, hT⟩ : ∃ T, d.types = [T] := List.length_eq_one_iff.1 (by
      simpa using congrArg List.length hn)
    rw [hT] at hn; simp at hn
    have hi := hd.indices 0 T (by rw [hT]; rfl)
    rw [hni] at hi
    exact ⟨T, hT, hn, List.eq_nil_of_length_eq_zero (Option.some.inj hi).symm⟩
  have hchk : ∀ venv : VEnv, venv.constants type.name = some ⟨0, .sort (.succ .zero)⟩ →
      ∀ d, AddInductive.Compat c.lparams [] level false [type] stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), [type][j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → AddInductive.CtorChecked venv c.lparams d t nidx ct := by
    intro venv hIv d hd j t hj ct hct' nidx hn
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ t = type := by
      rcases j with _ | j
      · exact ⟨rfl, (Option.some.inj hj).symm⟩
      · simp at hj
    rw [hni] at hn; obtain rfl := Option.some.inj hn
    obtain ⟨T, hT, hTn, hTi⟩ := hdT d hd
    rw [hcl]
    exact AddInductive.primCtor_checked hIv (by rw [hd.uvars, hcl]; rfl) hd.params
      (by rw [hT]; rfl) hTn (hd.nested T (by rw [hT]; exact .head _)) hTi
      (by rw [hd.level]; exact hlev) rfl (hct ct hct')
  -- the checking environment: the type and constructors as axioms, closed
  have hcl₀ : ConstMap.Closed c.env.constants := by
    rw [hcenv]; exact TrEnv'.closed (wf.tr (safety := .unsafe)) wf.hasPrimitives
  have mapWF := c.envAt.tr.map_wf
  have hAxc : envAx.constants = insertConsts c.env.constants
      ((AddInductive.primAxioms type).map .axiomInfo) := by
    rw [hAxe, AddInductive.foldl_addAxiom_constants]
  have hpfr' : ∀ ax ∈ AddInductive.primAxioms type, c.env.constants.find? ax.name = none := by
    intro ax hax; rw [← mapWF.find?'_eq_find?]; exact hpfr ax hax
  have hclosed : ConstMap.Closed envAx.constants := by
    have hnone : c.env.constants.find? type.name = none := by
      rw [← mapWF.find?'_eq_find?]; exact hfrI
    simp only [AddInductive.primAxioms, List.map_cons] at hAxc hpnd hpfr'
    rw [hAxc]
    rw [List.nodup_cons] at hpnd
    have hC₁ := AddInductive.ConstMap.Closed.insertAxioms
      [{ name := type.name, levelParams := [], type := type.type, isUnsafe := false }] mapWF hcl₀
      (fun ax hax => by
        simp only [List.mem_singleton] at hax; subst hax
        rw [htype']; exact Level.LParamsIn.of_ofLevel (Us := []) rfl)
      (by simp) (fun ax hax => by simp only [List.mem_singleton] at hax; subst hax; exact hnone)
    have mapWF₁ := mapWF.insert _ (.axiomInfo
      { name := type.name, levelParams := [], type := type.type, isUnsafe := false }) hnone
    refine AddInductive.ConstMap.Closed.insertAxioms _ mapWF₁ hC₁ (fun ax hax => ?_)
      (by simpa using hpnd.2) (fun ax hax => ?_)
    · obtain ⟨ct, hct', rfl⟩ := List.mem_map.1 hax
      rcases hct ct hct' with he | ⟨nm, bi, he⟩ <;> rw [he] <;>
        simp [Expr.SuppIn, ConstantInfo.name, ConstantInfo.toConstantVal, mapWF.find?_insert]
    · rw [mapWF.find?_insert, if_neg]
      · exact hpfr' ax (.tail _ hax)
      · obtain ⟨ct, hct', rfl⟩ := List.mem_map.1 hax
        simp only [beq_iff_eq]; intro he
        exact hpnd.1 (List.mem_map.2 ⟨_, hax, he.symm⟩)
  refine AddInductive.WF.bind (AddInductive.getElimLevel.WF hT
    (c' := c.withEnv envAx venvAx wfAx hleAx) rfl hle₀ wfAx.tr.wf hclosed (hchk venvAx hIAx))
    fun elimLevel hE => ?_
  refine AddInductive.WF.bind (AddInductive.isKTarget.WF hT (c' := c.withEnv envAx venvAx wfAx hleAx)
    rfl hle₀ wfAx.tr.wf (hchk venvAx hIAx)) fun kflag hK => ?_
  have hlp : c₀.toContext.lparams = (c.withEnv envAx venvAx wfAx hleAx).lparams := hb.lparams.symm
  conv => arg 2; arg 2; intro; arg 2; rw [hlp]
  -- the constructors are axioms already
  generalize hcAx : c.withEnv envAx venvAx wfAx hleAx = cAx at *
  have hcAxenv : cAx.env = envAx := by rw [← hcAx]; rfl
  have hcAxap : cAx.allowPrimitive = true := by rw [← hcAx]; exact hcp
  refine AddInductive.WF.bind (Q := (· = cAx.env)) (fun e h => by
    simp only [AddInductive.declareCtorAxioms, hcAxap, if_true] at h; cases h; rfl)
    fun envCA henvCA => ?_
  subst henvCA
  refine AddInductive.WF.withEnv cAx.envAt VEnv.LE.rfl ?_
  have hcAxv : cAx.venv = venvAx := by rw [← hcAx]; rfl
  have hcAxl : cAx.lparams = c.lparams := by rw [← hcAx]; rfl
  have hcAxm : cAx.mlctx = c.mlctx := by rw [← hcAx]; rfl
  have hfresh₀ : ∀ t ∈ [type], c₀.venv.constants t.name = none := by
    intro t ht; simp only [List.mem_singleton] at ht; subst ht
    exact c₀.envAt.tr.constants_eq_none (by rw [← hb.env]; exact hfrI)
  have hCt : ∀ (j : Nat) (t : InductiveType), [type][j]? = some t → ∀ ct ∈ t.ctors,
      ∃ C', TrExprS cAx.venv cAx.lparams [] ct.type C' := by
    intro j t hj ct hct'
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ t = type := by
      rcases j with _ | j
      · exact ⟨rfl, (Option.some.inj hj).symm⟩
      · simp at hj
    rw [hcAxv, hcAxl, hcl]
    exact ⟨_, (AddInductive.primCtor_tr hIAx (hct ct hct')).1⟩
  have hconst : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), [type][j]? = some t →
      [VExpr.sort (.succ .zero)][j]? = some T' →
      cAx.venv.constants t.name = some ⟨cAx.lparams.length, T'⟩ := by
    intro j t T' hj hT'
    obtain ⟨rfl, rfl, rfl⟩ : j = 0 ∧ t = type ∧ T' = .sort (.succ .zero) := by
      rcases j with _ | j
      · exact ⟨rfl, (Option.some.inj hj).symm, (Option.some.inj hT').symm⟩
      · simp at hj
    rw [hcAxv, hcAxl, hcl]; exact hIAx
  have hnoguard : ∀ ct ∈ type.ctors,
      ¬(AddInductive.spineIn (AddInductive.BFree (· ∈ [type].map (·.name))) ct.type ∧
        ([] : List VExpr).length < declareConstructors.arity 0 ct.type) := by
    intro ct hct' ⟨hsp, har⟩
    rcases hct ct hct' with he | ⟨nm, bi, he⟩ <;> rw [he] at hsp har
    · simp [declareConstructors.arity] at har
    · simp [AddInductive.spineIn, AddInductive.BFree, Expr.SuppIn] at hsp
  have hnotDefn : ∀ t ∈ [type], ∀ v, cAx.env.find? t.name ≠ some (.defnInfo v) := by
    intro t ht v hv
    simp only [List.mem_singleton] at ht; subst ht
    rw [hcAxenv] at hv
    change envAx.constants.find?' _ = _ at hv
    rw [wfAx.tr.map_wf.find?'_eq_find?, hAxc] at hv
    rcases insertConsts_find? mapWF (fun ci hci => by
        obtain ⟨ax, hax, rfl⟩ := List.mem_map.1 hci; exact hpfr' ax hax)
      (by simpa [List.map_map, Function.comp_def, ConstantInfo.name,
        ConstantInfo.toConstantVal] using hpnd) hv with h | ⟨h, -⟩
    · have h' : c.env.find? t.name = some (.defnInfo v) := by
        rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]; exact h
      rw [h'] at hfrI; cases hfrI
    · obtain ⟨ax, -, hax⟩ := List.mem_map.1 h; cases hax
  have hCtorC : ∀ (j : Nat) (t : InductiveType) ct C', [type][j]? = some t → ct ∈ t.ctors →
      TrExprS cAx.venv cAx.lparams [] ct.type C' →
      cAx.venv.constants ct.name = some ⟨cAx.lparams.length, C'⟩ := by
    intro j t ct C' hj hct' htr
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ t = type := by
      rcases j with _ | j
      · exact ⟨rfl, (Option.some.inj hj).symm⟩
      · simp at hj
    rw [hcAxv, hcAxl, hcl] at htr ⊢
    obtain rfl := (AddInductive.primCtor_tr hIAx (hct ct hct')).2.2 C' htr
    exact VEnv.addConstList_constants_of_mem hAx₁ (List.mem_map.2 ⟨ct, hct', rfl⟩)
  have hlit : isRec [type].toArray stats.indConsts = false →
      ∀ l, cAx.venv.ContainsLits l → l.SuppIn fun n => n ∉ [type].map (·.name) := by
    intro hrec l _
    rcases hshape with ⟨hn, -, -⟩ | ⟨hn, -, nm, bi, hc⟩
    · cases l <;> simp [Literal.SuppIn, hn]
    · have hind : stats.indConsts = #[.const type.name []] := by
        apply Array.toList_inj.1
        rw [hT.indConsts, hT.levels]; rfl
      rw [hind] at hrec
      simp [isRec, isRec.loop, hc, AddInductive.hasIndOcc_eq, Expr.anySub, AddInductive.indOccP,
        Expr.constName!] at hrec
      exact absurd hn hrec
  -- a translation mentions the type only where the term does: literals are of other types
  have hNM : AddInductive.NotMentionsOK cAx.venv cAx.lparams stats [type] := by
    have hind' : stats.indConsts.toList = [type].map fun T => .const T.name stats.levels := by
      have := hT.indConsts; rwa [List.take_length] at this
    obtain ⟨hp, hns⟩ := AddInductive.indOccP_spec hind'
    intro Δ a a' hΔ hvl ha hocc
    rw [AddInductive.hasIndOcc_eq] at hocc
    refine TrExprS.not_mentions (hcAxv ▸ wfAx.tr.wf) hns (fun l _ => ?_) (fun n b hbi hn => ?_)
      ha hΔ (fun x hx => ?_) hocc
    · refine l.toConstructor_anySub fun e he => ?_
      obtain ⟨c', us, rfl, hc'⟩ := hp e he
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc'
      subst hc'
      rcases hI with h | h <;> rw [h] <;> exact ⟨_, _, rfl, by decide, fun _ => by decide⟩
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
      subst hn
      rw [hcAxv, VEnv.addConstList_inducts hAx₁, VEnv.addConstList_inducts hT₁, hb.venv] at hbi
      obtain ⟨_, h⟩ := henv₀.constants_of_inducts hbi
      cases h.symm.trans (hfresh₀ type (.head _))
    · obtain ⟨-, A, hA⟩ := hvl x hx
      rw [hA]; rfl
  refine AddInductive.mkRecInfos.WF_core (c := cAx) hT hcAxm hcAxl (hcAxv ▸ hle₀)
    (hcAxv ▸ wfAx.tr.wf) hNM (by rw [hcAxv, hcAxl]; exact hchk venvAx hIAx) hCt hconst henv₀
    c₀.envAt.hasPrimitives hfresh₀ (by simp) (by rw [hcAxenv]; exact hclosed)
    (by rw [hcAxl, hcl]; exact .nil) (by simpa using hdum)
    (fun t ht ct hct' hsp har => ((hnoguard ct (by simpa using hct')) ⟨hsp, har⟩).elim)
    (fun t ht ct hct' hsp har => ((hnoguard ct (by simpa using hct')) ⟨hsp, har⟩).elim)
    hlit cAx.envAt VEnv.LE.rfl (X := fun _ => False) (fun _ _ => rfl) (fun _ _ _ => id)
    (fun _ h => h.elim) (by rw [hcAxenv]; exact hclosed) rfl hnotDefn hCtorC (fun _ h _ => h)
    hE.2 ?H
  case H =>
  intro recInfos c₃ d hR
  have mapWFT : envTypes.constants.WF := by
    rw [hDc]; exact insertConsts_wf c.envAt.tr.map_wf hDfr hDnd
  have mapWFC : envCtors.constants.WF := by
    rw [hDC'.1]; exact insertConsts_wf mapWFT hDC'.2.2.2 hDC'.2.2.1
  have hcAxs : cAx.safety = inductSafety false := by rw [← hcAx]; exact hcs₀
  refine AddInductive.WF.mono (AddInductive.declareRecursors.WF hR hR.largeElim hE.2 hcAxs
    (hK d hR.compat hR.elaborates) mapWFC) fun env' hRecs => ?_
  obtain ⟨recs, hRc, hRq, hRnd, hRfr, -, hRnames, hRmaj, hRtr⟩ := hRecs
  -- the declaration, elaborated with the type only
  have hdu : d.uvars = 0 := by rw [hR.uvars, hcAxl, hcl]; rfl
  have hdp : d.params = [] := hR.params
  have hdi : ∀ T ∈ d.types, T.indices = [] := by
    intro T hT'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
    have h1 := hR.nindices j T hj
    have hj0 : j = 0 := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      have hl := Lean4Lean.List.Forall₂.length_eq hR.elaborates.types
      simp at hl; omega
    subst hj0
    rw [hni] at h1
    exact List.eq_nil_of_length_eq_zero (Option.some.inj h1).symm
  have hax : ∃ ax, envAx.find? type.name = some (.axiomInfo ax) := by
    obtain ⟨ci, hci, -⟩ := wfAx.tr.find?_iff.2 ⟨_, hIAx⟩
    have hci' := hci
    change envAx.constants.find?' _ = _ at hci'
    rw [wfAx.tr.map_wf.find?'_eq_find?, hAxc] at hci'
    rcases insertConsts_find? mapWF (fun ci hci => by
        obtain ⟨ax, hax, rfl⟩ := List.mem_map.1 hci; exact hpfr' ax hax)
      (by simpa [List.map_map, Function.comp_def, ConstantInfo.name,
        ConstantInfo.toConstantVal] using hpnd) hci' with h | ⟨h, -⟩
    · have h' : c.env.find? type.name = some ci := by
        rw [Kernel.Environment.find?, mapWF.find?'_eq_find?]; exact h
      rw [h'] at hfrI; cases hfrI
    · obtain ⟨ax, -, rfl⟩ := List.mem_map.1 h; exact ⟨ax, hci⟩
  have hEl₂ := hR.elaborates
  rw [hcAxv, hcAxl, hcl] at hEl₂
  have hfirst := hR.first hdp
  rw [hcAxv, hcAxl, hcl, hcAxenv] at hfirst
  have hEl : AddInductive.Elaborates venvT [] 0 level [type] d :=
    AddInductive.elaborates_prim hleTA wfAx.tr.wf hIT hax rfl hct hEl₂ hdu hdp hdi hR.aux hR.nested
      hfirst
  have hlevwf : level.WF 0 := .of_ofLevel hT.resultLevel
  have hInd : ∀ T ∈ d.types, T.WF venvT d := by
    intro T hT'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT'
    obtain ⟨T'', hT'', hty⟩ := List.Forall₂.getElem?_l hR.typeTr hj
    have hj0 : j = 0 := by have := (List.getElem?_eq_some_iff.1 hT'').1; simp at this; omega
    subst hj0
    obtain rfl : T'' = .sort (.succ .zero) := (Option.some.inj hT'').symm
    refine ⟨by rw [hdi T hT', hdp]; exact .nil, ?_⟩
    rw [hty, hdi T hT', hdp, hR.level, hdu]
    exact ⟨_, .sortDF (by simp [VLevel.WF]) hlevwf (show VLevel.succ .zero ≈ level from hlev.symm)⟩
  -- each constructor's constant, as the declaration has it
  have hctorC : ∀ ct ∈ type.ctors, ∃ cv, (0, cv) ∈ d.ctors ∧ cv.name = ct.name ∧
      cv.type = AddInductive.primCtorTr type.name ct.type := by
    intro ct hct'
    obtain ⟨T, hTd⟩ : ∃ T, d.types = [T] :=
      List.length_eq_one_iff.1 (Lean4Lean.List.Forall₂.length_eq hEl₂.types).symm
    obtain ⟨T, hT', hTn, hcs'⟩ : ∃ T', d.types[0]? = some T' ∧ T'.name = type.name ∧
        List.Forall₂ _ type.ctors T'.ctors := by
      have := hEl₂.types
      rw [hTd] at this
      cases this with | cons h _ => exact ⟨_, by rw [hTd]; rfl, h.1, h.2⟩
    obtain ⟨cv, hcv, hn, htr, -⟩ := Lean4Lean.List.Forall₂.forall_exists_l hcs' ct hct'
    exact ⟨cv, VInductDecl.mem_ctors_iff.2 ⟨T, hT', hcv⟩, hn,
      (AddInductive.primCtor_tr hIAx (hct ct hct')).2.2 _ htr⟩
  have hRtr' : ∀ (envC envR : VEnv), venvT ≤ envC → envC.WF →
      (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
      envC.addConstList d.recConsts = some envR → envR.WF →
      List.Forall₂ (fun v (p : VInductiveType × Nat) =>
        TrRecVal d c.lparams envR p.2 p.1 v ∧
        TrConstant c.safety envC (.recInfo v)
          ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩)
        recs d.types.zipIdx := by
    intro envC envR hle' hwfC hcc hRadd hwfR
    have hleC : venvAx ≤ envC := VEnv.addConstList_le_of hAx₁ hle' fun p hp => by
      obtain ⟨ct, hct', rfl⟩ := List.mem_map.1 hp
      obtain ⟨cv, hcv, hn, hty⟩ := hctorC ct hct'
      have := hcc _ (List.mem_map_of_mem (f := fun p : Nat × VConstructor =>
        (p.2.name, (⟨d.uvars, p.2.type⟩ : VConstant))) hcv)
      simpa [hn, hty, hdu] using this
    have := hRtr envC envR (hcAxv ▸ hleC) hwfC hcc hRadd hwfR
    rw [hcAxl, hR.safety, show cAx.safety = c.safety by rw [← hcAx]; rfl] at this
    exact this
  obtain ⟨hdecl, hAxd, ⟨env₂, hstep⟩, -⟩ :=
    AddInductive.assemble_step wf (List.cons_ne_nil _ _) hT
    hDc hDnd hDfr hleT (VEnv.WF.addConstList c.envAt.tr.wf (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨_, .sort (by simp [VLevel.WF])⟩) hT₁)
    (by rw [hcl]; exact hT₁) (hchk venvT hIT d) hDC'.1 hDC'.2.2.1 hDC'.2.2.2 hcAxl hR (hcl ▸ hEl) hInd
    (fun h => hE.1 h d hR.compat hR.elaborates) hRc hRnd hRfr hRnames hRtr'
  -- the constants the step adds are the recognizer's, plus the recursor
  obtain ⟨T, hTd⟩ : ∃ T, d.types = [T] :=
    List.length_eq_one_iff.1 (Lean4Lean.List.Forall₂.length_eq hEl₂.types).symm
  have hTmem : T ∈ d.types := by rw [hTd]; exact .head _
  obtain ⟨T'', hT'', hty⟩ := List.Forall₂.getElem?_l hR.typeTr
    (show d.types[0]? = some T by rw [hTd]; rfl)
  obtain rfl : T'' = .sort (.succ .zero) := (Option.some.inj hT'').symm
  have hTty : T.type = .sort (.succ .zero) := by rw [hty]
  have hEt := hEl₂.types
  rw [hTd] at hEt
  obtain ⟨⟨hTn, hcsF⟩, -⟩ := List.forall₂_cons.1 hEt
  have hcs' : d.typeConsts ++ d.ctorConsts = cs.map fun p => (p.1, (⟨0, p.2⟩ : VConstant)) := by
    rw [hcs, VInductDecl.typeConsts, VInductDecl.ctorConsts, VInductDecl.ctors, hTd, hdu]
    simp only [List.map_cons, List.map_nil, List.zipIdx_cons, List.zipIdx_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.map_map, hTn, hTty, List.cons_append, List.nil_append]
    congr 1
    refine (List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun ct cv h => ?_) (Lean4Lean.List.Forall₂.and_mem hcsF))).symm
    obtain ⟨⟨hn, htr, -⟩, hct', -⟩ := h
    simp [hn, (AddInductive.primCtor_tr hIAx (hct ct hct')).2.2 _ htr]
  have hrecs' : ∀ p ∈ d.recConsts, Environment.primitives.contains p.1 = false := by
    simp [VInductDecl.recConsts, VInductDecl.allTypes_of_aux hR.aux, VInductDecl.recName, hTd, hTn,
      hrecnp]
  have mapWF' : env'.constants.WF := by rw [hRc]; exact insertConsts_wf mapWFC hRfr hRnd
  have hsafe : ∀ {n ci}, env'.find? n = some ci → Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci hf hp
    change env'.constants.find?' n = some ci at hf
    rw [mapWF'.find?'_eq_find?, hRc] at hf
    rcases insertConsts_find? mapWFC hRfr hRnd hf with hf | ⟨hci, rfl⟩
    rotate_left
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci
      rw [hTd] at hRnames
      obtain ⟨r₀, rfl, hr₀⟩ : ∃ r₀, recs = [r₀] ∧ r₀.name = Lean.mkRecName type.name := by
        cases hRnames with | cons h t => cases t; exact ⟨_, rfl, h.trans (by rw [hTn])⟩
      obtain rfl := List.mem_singleton.1 hr
      simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hp
      rw [hr₀, hrecnp] at hp; cases hp
    rw [hDC'.1] at hf
    rcases insertConsts_find? mapWFT hDC'.2.2.2 hDC'.2.2.1 hf with hf | ⟨hci, -⟩
    rotate_left
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hci
      simp [AddInductive.ctorVals, AddInductive.ctorVal] at hv
      obtain ⟨a, b, -, rfl⟩ := hv
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal, hcl]
    rw [hDc] at hf
    rcases insertConsts_find? c.envAt.tr.map_wf hDfr hDnd hf with hf | ⟨hci, -⟩
    rotate_left
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hci
      simp only [AddInductive.inductVals, Array.toList_zipWith] at hv
      generalize stats.nindices.toList = l at hv
      cases l with
      | nil => simp at hv
      | cons k l =>
        simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_singleton] at hv
        subst hv
        simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
          ConstantInfo.levelParams, ConstantInfo.toConstantVal, hcl]
    refine wf.safePrimitives ?_ hp
    rw [Kernel.Environment.find?, ← hcenv, c.envAt.tr.map_wf.find?'_eq_find?]; exact hf
  refine ⟨d, env₂, hR.isUnsafe, hdecl, hR.aux, hstep, by rw [hRq, hDC'.2.1, hDq, hcenv], nofun,
    fun _ => ⟨fun safety venv₁ venv₂ H hp =>
      hpres hp (Primitive.AddsConsts.of_addInduct H hcs' hrecs'), hsafe⟩,
    ⟨venvT, level, hAxd, hEl⟩, fun T hT x hx => by simp [hdi T hT] at hx,
    AddInductive.majorAt_of_recs mapWFC hRc hRnd hRfr hRnames hRmaj, nofun,
    hR.elaborates.stripsTo (by rw [hR.params]; exact hT.nparams)⟩

end Lean4Lean

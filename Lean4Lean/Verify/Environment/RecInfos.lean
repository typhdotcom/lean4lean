import Lean4Lean.Verify.Environment.Constructors
import Lean4Lean.Verify.Support.Bridge

/-!
# Verifying `mkRecInfos`

`mkRecInfos` opens the recursor's binders as local variables: each type's indices and major
premise and its motive, then each constructor's fields, inductive hypotheses and minor premise. It
runs in the environment with the block's constructors as axioms, at the recursor's universe
parameters, and normalizes types in a local context holding every variable opened so far. Each
normalization is verified by running it again in the smallest context it needs, the parameters
and the telescope being read, with the block's types only (`AddInductive.whnf.WF_sim`): there the
type checker's results are typed where the specification states them.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Substituting the variable `n` below a lift by `n + 1` above it: a variable bound outside the
lift is reached by both. -/
theorem VExpr.inst_liftN_bvar' : ∀ (F : VExpr) (n j : Nat),
    (F.liftN (n+1) (j+1)).inst (.bvar n) j = F.liftN n j
  | .bvar i, n, j => by
    simp only [VExpr.liftN, VExpr.inst, VExpr.instVar, liftVar]
    by_cases h : i < j + 1 <;> simp only [h, if_true, if_false]
    · by_cases h' : i < j <;> simp only [h', if_true, if_false]
      have : i = j := by omega
      subst this
      simp; omega
    · have h1 : ¬(n + 1 + i < j) := by omega
      have h2 : ¬(n + 1 + i = j) := by omega
      have h3 : ¬(i < j) := by omega
      simp only [h1, h2, h3, if_false]; congr 1; omega
  | .sort .., _, _ | .const .., _, _ => rfl
  | .app .., n, j => by simp only [VExpr.liftN, VExpr.inst, inst_liftN_bvar']
  | .lam .., n, j | .forallE .., n, j => by simp only [VExpr.liftN, VExpr.inst, inst_liftN_bvar']
  | .proj .., n, j => by simp only [VExpr.liftN, VExpr.inst, inst_liftN_bvar']

theorem VEnv.TeleDefEq.snoc {env : VEnv} {U : Nat} {A B : VExpr} :
    ∀ {Γ As Bs}, env.TeleDefEq U Γ As Bs → env.IsDefEqU U (Bs.reverse ++ Γ) A B →
      env.TeleDefEq U Γ (As ++ [A]) (Bs ++ [B])
  | _, [], [], .nil, h => .cons (by simpa using h) .nil
  | _, _ :: _, _ :: _, .cons hAB t, h => .cons hAB (VEnv.TeleDefEq.snoc t (by simpa using h))

theorem TypeChecker.MLCtx.IsTele.find?_fvar {m : TypeChecker.MLCtx} {fvs tys}
    (h : m.IsTele fvs tys) (hnd : fvs.Nodup) {j : Nat} (hj : j < fvs.length) :
    m.vlctx.find? (.inr fvs[j]) =
      some (.bvar (fvs.length - 1 - j), tys[j]'(h.length_eq ▸ hj) |>.liftN (fvs.length - j)) := by
  induction h generalizing j with
  | nil => cases hj
  | @vlam m fvs tys fv name ty ty' bi h ih =>
    have hl := h.length_eq
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    rw [List.nodup_append] at hnd
    by_cases hjl : j = fvs.length
    · subst hjl
      simp [TypeChecker.MLCtx.vlctx, hl, VExpr.lift]
    · have hj' : j < fvs.length := by omega
      have hne : fv ≠ fvs[j] := fun e => hnd.2.2 _ (List.getElem_mem hj') _ (.head _) e.symm
      simp only [List.getElem_append_left hj', TypeChecker.MLCtx.vlctx, VLCtx.find?, VLCtx.next]
      rw [if_neg (by simpa using hne)]
      simp only [ih hnd.1 hj']
      simp [VLocalDecl.depth, VExpr.liftN, liftVar, VExpr.liftN_liftN,
        List.getElem_append_left (hl ▸ hj')]
      exact ⟨by omega, by congr 1; omega⟩

namespace AddInductive

theorem foldlM_flatMap {m} [Monad m] [LawfulMonad m] {α β γ} (g : γ → β → m γ) (f : α → List β) :
    ∀ (l : List α) (init : γ),
    l.foldlM (fun acc a => (f a).foldlM g acc) init = (l.flatMap f).foldlM g init
  | [], _ => by simp
  | a :: l, init => by
    simp only [List.foldlM_cons, List.flatMap_cons, List.foldlM_append]
    congr 1; funext acc; exact foldlM_flatMap g f l acc

/-- The axioms `declareCtorAxioms` adds: the block's constructors, in order. -/
def ctorAxioms (lparams : List Name) (isUnsafe : Bool) (types : List InductiveType) :
    List AxiomVal :=
  (types.flatMap (·.ctors)).map fun ct =>
    { name := ct.name, levelParams := lparams, type := ct.type, isUnsafe }

theorem addChecked.ne_dummy {f : α → ConstantInfo} (allow : Bool) :
    ∀ (xs : List α) {env env' : Environment},
    (xs.foldlM (m := Except Exception) (init := env) fun (env : Environment) x => do
      env.checkName (f x).name allow; return env.add (f x)) = .ok env' →
    ∀ x ∈ xs, (f x).name ≠ `_inhabitedExprDummy
  | [], _, _, _ => nofun
  | x :: xs, env, env', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h; · cases h
    rename_i u hn
    split at hn; · cases hn
    rename_i hck
    cases hn
    rintro y (_ | ⟨_, hy⟩)
    · exact checkName.ne_dummy hck
    · exact addChecked.ne_dummy allow xs h y hy

theorem addChecked.eq_foldl {f : α → ConstantInfo} (allow : Bool) :
    ∀ (xs : List α) {env env' : Environment},
    (xs.foldlM (m := Except Exception) (init := env) fun (env : Environment) x => do
      env.checkName (f x).name allow; return env.add (f x)) = .ok env' →
    env' = xs.foldl (fun e x => e.add (f x)) env
  | [], _, _, h => by cases h; rfl
  | x :: xs, env, env', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h; · cases h
    rename_i u hn
    split at hn; · cases hn
    cases hn
    exact addChecked.eq_foldl allow xs h

/-- The constants the model adds for the block's constructors, at translations `ctorTr` of their
declared types. -/
def ctorConstsOf (U : Nat) (cts : List Constructor) (ctorTr : List VExpr) :
    List (Name × VConstant) :=
  List.zipWith (fun ct C' => (ct.name, ⟨U, C'⟩)) cts ctorTr

theorem ctorConstsOf_names {U : Nat} : ∀ {cts : List Constructor} {ctorTr : List VExpr},
    cts.length = ctorTr.length → (ctorConstsOf U cts ctorTr).map (·.1) = cts.map (·.name)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [ctorConstsOf, List.zipWith_cons_cons, List.map_cons] at h ⊢
    exact congrArg _ (ctorConstsOf_names (by simpa using h))

/-- What `declareCtorAxioms` establishes, for a block without primitive names: the environment the
recursors are built in adds the block's constructors to `c.env` as axioms, under fresh names
other than the kernel's panic constant, and has a model at the block's level for any translation
of their types. -/
theorem declareCtorAxioms.WF {c : VContext} {types : List InductiveType} {isUnsafe : Bool}
    (hsafety : c.safety = inductSafety isUnsafe) (hp : c.allowPrimitive = false)
    (hCt : ∀ ct ∈ types.flatMap (·.ctors), ∀ C', TrExprS c.venv c.lparams [] ct.type C' →
      c.venv.IsType c.lparams.length [] C') :
    WF c (declareCtorAxioms types.toArray isUnsafe) fun envCA =>
      envCA.constants = insertConsts c.env.constants
        ((ctorAxioms c.lparams isUnsafe types).map .axiomInfo) ∧
      envCA.quotInit = c.env.quotInit ∧
      ((types.flatMap (·.ctors)).map (·.name)).Nodup ∧
      (∀ ct ∈ types.flatMap (·.ctors), c.env.find? ct.name = none ∧
        ct.name ≠ `_inhabitedExprDummy ∧ Environment.primitives.contains ct.name = false) ∧
      ∀ ctorTr : List VExpr,
        List.Forall₂ (fun ct C' => TrExprS c.venv c.lparams [] ct.type C')
          (types.flatMap (·.ctors)) ctorTr →
        ∃ venvC, c.venv.addConstList (ctorConstsOf c.lparams.length
          (types.flatMap (·.ctors)) ctorTr) = some venvC ∧ VEnvAt envCA c.safety venvC := by
  intro envCA h
  let cts := types.flatMap (·.ctors)
  let f (ct : Constructor) : ConstantInfo :=
    .axiomInfo { name := ct.name, levelParams := c.lparams, type := ct.type, isUnsafe }
  have h' : (cts.foldlM (m := Except Exception) (init := c.env) fun (env : Environment) ct => do
      env.checkName (f ct).name false; return env.add (f ct)) = .ok envCA := by
    simp only [declareCtorAxioms, hp, Bool.false_eq_true, if_false, List.foldlM_toArray] at h
    rw [foldlM_flatMap] at h; exact h
  have mapWF := c.envAt.tr.map_wf
  obtain ⟨hC, hq, hnd, hfr, hprim⟩ := addChecked.WF mapWF false f cts _ h'
  have hdum := addChecked.ne_dummy false cts h'
  have hnd' : (cts.map (·.name)).Nodup := by
    simpa [List.map_map, Function.comp_def, f, ConstantInfo.name, ConstantInfo.toConstantVal]
      using hnd
  have hfind (ct) (hct : ct ∈ cts) : c.env.find? ct.name = none := by
    have := hfr (f ct) (List.mem_map_of_mem hct)
    rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]
  have hnp (ct) (hct : ct ∈ cts) : Environment.primitives.contains ct.name = false :=
    Bool.eq_false_iff.2 fun h => by simpa using hprim (f ct) (List.mem_map_of_mem hct) h
  refine ⟨by rw [hC]; simp [ctorAxioms, cts, f, List.map_map, Function.comp_def], hq, hnd',
    fun ct hct => ⟨hfind ct hct, hdum ct hct, hnp ct hct⟩, fun ctorTr htr => ?_⟩
  have hlen : cts.length = ctorTr.length := Lean4Lean.List.Forall₂.length_eq htr
  have hfr' : ∀ p ∈ ctorConstsOf c.lparams.length cts ctorTr, c.venv.constants p.1 = none := by
    intro p hp
    have : p.1 ∈ cts.map (·.name) := ctorConstsOf_names hlen ▸ List.mem_map_of_mem hp
    obtain ⟨ct, hct, e⟩ := List.mem_map.1 this
    exact e ▸ c.envAt.tr.constants_eq_none (hfind ct hct)
  obtain ⟨venvC, hadd⟩ := VEnv.exists_addConstList hfr' (ctorConstsOf_names hlen ▸ hnd')
  refine ⟨venvC, hadd, ?_⟩
  have henvCA : envCA = (ctorAxioms c.lparams isUnsafe types).foldl
      (fun e ax => e.add (.axiomInfo ax)) c.env := by
    rw [addChecked.eq_foldl false cts h']; simp [ctorAxioms, cts, f, List.foldl_map]
  rw [henvCA]
  refine VEnvAt.addAxiomList _ _ c.envAt ?_ (by simpa [ctorAxioms, List.map_map, Function.comp_def])
    (fun ax hax => ?_) (fun ax hax => ?_) hadd
  · have hs : c.safety ≤ (ConstantInfo.axiomInfo
        { name := .anonymous, levelParams := c.lparams, type := default, isUnsafe }).safety := by
      rw [hsafety]; cases isUnsafe <;> exact DefinitionSafety.le_rfl
    have : ∀ (l : List Constructor) (tr : List VExpr),
        (∀ ct ∈ l, ∀ C', TrExprS c.venv c.lparams [] ct.type C' →
          c.venv.IsType c.lparams.length [] C') →
        List.Forall₂ (fun ct C' => TrExprS c.venv c.lparams [] ct.type C') l tr →
        List.Forall₂ (fun (ax : AxiomVal) (p : Name × VConstant) => ax.name = p.1 ∧
          TrConstant c.safety c.venv (.axiomInfo ax) p.2 ∧ p.2.WF c.venv)
          (l.map fun ct => { name := ct.name, levelParams := c.lparams, type := ct.type, isUnsafe })
          (ctorConstsOf c.lparams.length l tr) := by
      intro l tr hl h
      induction h with
      | nil => exact .nil
      | cons h1 _ ih =>
        exact .cons ⟨rfl, ⟨hs, rfl, h1⟩, hl _ (.head _) _ h1⟩ (ih fun ct hct => hl ct (.tail _ hct))
    exact this _ _ hCt htr
  · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hax; exact hfind ct hct
  · obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hax; exact hnp ct hct

/-- The type checker's context with local context `m` over `c`'s environment: the kernel's
context with the variables a call does not read removed. -/
def VContext.small (c : VContext) (m : TypeChecker.MLCtx) (hm : m.WF c.venv c.lparams) :
    TypeChecker.VContext :=
  @TypeChecker.VContext.withMLC c.tc m ⟨hm⟩

@[simp] theorem VContext.small_mlctx {c : VContext} {m hm} : (c.small m hm).mlctx = m := rfl

/-- What `loopArgs1` keeps, having passed `i` parameters of a type declared at
`Π params idx₀, Sort u` and opened its indices `fvs` at translations `idx`: the small context `m`
is the parameters `Mp` and those indices; the type left translates to `V`, defeq to the rest of
the declared type; the indices so far agree with the declared ones. -/
structure ArgsInv (c₂ : VContext) (X : Name → Prop) (pre : List Name) (Mp : TypeChecker.MLCtx)
    (hMp : Mp.WF c₂.venv c₂.lparams) (pfvs : List FVarId) (params idx₀ : List VExpr) (u : VLevel)
    (i : Nat) (fvs : List FVarId) (idx : List VExpr) (m : TypeChecker.MLCtx)
    (hm : m.WF c₂.venv c₂.lparams) (type : Expr) (V : VExpr) (cb : VContext) (ρ ρp : Lift)
    (F₀ : List FVarId) (P : VContext → Prop) : Prop where
  tele : m.IsTele (pfvs ++ fvs) (params ++ idx)
  fvars : cb.mlctx.vlctx.fvars = fvs.reverse ++ F₀
  pred : P cb
  base : ∃ hk, m.dropN fvs.length hk = Mp
  sub : Sub X pre ρ (c₂.small m hm) cb
  subP : Sub X pre ρp (c₂.small Mp hMp) cb
  tr : (c₂.small m hm).TrExpr type V
  le : i ≤ params.length
  nil : i < params.length → fvs = []
  rel : idx.length ≤ idx₀.length →
    c₂.venv.TeleDefEq c₂.lparams.length params.reverse (idx₀.take idx.length) idx ∧
    c₂.venv.IsDefEqU c₂.lparams.length (idx.reverse ++ params.reverse) V
      ((VExpr.foralls (params.drop i ++ idx₀.drop idx.length) (.sort u)).liftN (params.length - i))

theorem loopArgs1.WF {c₂ : VContext} {X : Name → Prop} {pre : List Name} {Mp : TypeChecker.MLCtx}
    {hMp : Mp.WF c₂.venv c₂.lparams} {pfvs : List FVarId} {params idx₀ : List VExpr} {u : VLevel}
    (hMpT : Mp.IsTele pfvs params) {stats : InductiveStats}
    (hpar : stats.params.toList = pfvs.map .fvar) {F₀ : List FVarId} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {k : Expr → Nat → Array Expr → M α} {Q}
    (H : ∀ type i fvs idx m hm V cb ρ ρp,
      ArgsInv c₂ X pre Mp hMp pfvs params idx₀ u i fvs idx m hm type V cb ρ ρp F₀ P →
      WF cb (k type i (fvs.map .fvar).toArray) Q) :
    ∀ fuel type i fvs idx m hm V cb ρ ρp,
      ArgsInv c₂ X pre Mp hMp pfvs params idx₀ u i fvs idx m hm type V cb ρ ρp F₀ P →
      WF cb (mkRecInfos.loopArgs1 stats type i (fvs.map .fvar).toArray fuel k) Q := by
  intro fuel
  induction fuel with
  | zero => intros; exact .throw
  | succ fuel ih =>
  intro type i fvs idx m hm V cb ρ ρp hI
  simp only [mkRecInfos.loopArgs1]
  split
  · rename_i name dom body bi
    obtain ⟨V₀, hS, hdef⟩ := hI.tr
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i dom' body'
    have hlenp : pfvs.length = params.length := hMpT.length_eq
    have hsize : stats.params.size = params.length := by
      rw [← Array.length_toList, hpar, List.length_map, hlenp]
    have cs := c₂.small m hm
    have henv : c₂.venv.WF := c₂.envAt.tr.wf
    have hΔ : (c₂.small m hm).vlctx.WF c₂.venv c₂.lparams.length := (c₂.small m hm).Δwf
    have hΓ := hΔ.toCtx
    have hctx : (c₂.small m hm).vlctx.toCtx = idx.reverse ++ params.reverse := by
      show m.vlctx.toCtx = _; simpa using hI.tele.toCtx
    split
    · rename_i hlt
      rw [hsize] at hlt
      obtain rfl := hI.nil hlt
      have hidx : idx = [] := by
        have := hI.tele.length_eq; simp [hlenp] at this; exact this
      subst hidx
      obtain ⟨_, hm0⟩ := hI.base
      simp only [List.length_nil, TypeChecker.MLCtx.dropN] at hm0
      subst hm0
      have hpi : stats.params[i]! = .fvar pfvs[i] := by
        rw [getElem!_pos stats.params i (by rw [hsize]; exact hlt)]
        simp [← Array.getElem_toList, hpar]
      rw [hpi]
      obtain ⟨-, hrel⟩ := hI.rel (Nat.zero_le _)
      simp only [List.length_nil, List.drop_zero, List.reverse_nil, List.nil_append,
        List.drop_eq_getElem_cons hlt, List.cons_append, VExpr.foralls, VExpr.liftN] at hrel hctx
      rw [← hctx] at hrel
      obtain ⟨⟨u₁, hdd⟩, ⟨u₂, hbb⟩⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ (hdef.trans henv hΓ hrel)
      have hnd : pfvs.Nodup := by
        have := hMp.fvars_nodup; rw [hMpT.fvars] at this; exact List.nodup_reverse.1 this
      have hfind := hMpT.find?_fvar hnd (j := i) (by omega)
      simp only [hlenp] at hfind
      have t₀ := hΔ.find?_wf henv.ordered hfind
      have hΔeq : VLCtx.IsDefEq c₂.venv c₂.lparams.length
          ((none, .vlam dom') :: (c₂.small m hm).vlctx)
          ((none, .vlam ((params[i]'hlt).liftN (params.length - i))) :: (c₂.small m hm).vlctx) :=
        .cons (VLCtx.IsDefEq.refl henv.ordered hΔ) nofun (.vlam hdd)
      obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv hΔeq
      have hbodyeq := hbody.uniq henv hΔeq hbody''
      have hinst := hbody''.inst henv.ordered t₀ (.fvar hfind)
      rw [← Lean.Expr.instantiate1_eq] at hinst
      refine WF.bind (hI.sub.whnf hinst) fun e₁ h₁ => ?_
      obtain ⟨-, -, htr₁⟩ := h₁
      refine ih e₁ (i + 1) [] [] m hm _ cb ρ ρp ⟨hI.tele, hI.fvars, hI.pred, hI.base, hI.sub,
        hI.subP, htr₁, hlt, fun _ => rfl, fun _ => ⟨.nil, ?_⟩⟩
      have hΓ' : OnCtx (dom' :: (c₂.small m hm).vlctx.toCtx) (c₂.venv.IsType c₂.lparams.length) :=
        ⟨hΓ, hdomT⟩
      obtain ⟨_, hbe⟩ := hbodyeq.symm.trans henv hΓ' ⟨_, hbb⟩
      have hbe' := hbe.defeqDFC henv.ordered (.succ .zero hdd)
      have := hbe'.instN henv.ordered t₀ .zero
      have e1 : params.length - i = (params.length - 1 - i) + 1 := by omega
      have e2 : params.length - (i + 1) = params.length - 1 - i := by omega
      rw [e1, VExpr.inst_liftN_bvar'] at this
      simp only [List.length_nil, List.drop_zero, List.reverse_nil, List.nil_append]
      rw [e2, ← hctx]; exact ⟨_, this⟩
    · rename_i hge
      rw [hsize] at hge
      have hin : i = params.length := Nat.le_antisymm hI.le (Nat.not_lt.1 hge)
      subst hin
      refine WF.bind hI.sub.consumeTypeAnnotations fun dom_s hds => ?_
      obtain ⟨rfl, hok⟩ := hds
      obtain ⟨ty', hty, hdefty⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom
      have htyT : (c₂.small m hm).IsType ty' := hdomT.defeqU_l henv hΓ hdefty
      obtain ⟨wf, hsub⟩ := hI.sub.push (name := name) (bi := bi) hty htyT
      refine WF.withLocalDecl (hI.sub.trExprS hty) (hI.sub.isType htyT) ?_
      have hsubP := hI.subP.skip (name := name) (bi := bi) (hI.sub.trExprS hty) (hI.sub.isType htyT)
      obtain ⟨u₀, hdomS⟩ := hdomT
      have hdomty := hdefty.of_l henv hΓ hdomS
      have hΔeq : VLCtx.IsDefEq c₂.venv c₂.lparams.length
          ((none, .vlam dom') :: (c₂.small m hm).vlctx) ((none, .vlam ty') :: (c₂.small m hm).vlctx) :=
        .cons (VLCtx.IsDefEq.refl henv.ordered hΔ) nofun (.vlam hdomty)
      obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv hΔeq
      have hbodyeq := hbody.uniq henv hΔeq hbody''
      have hinst : (Sub.pushS (c₂.small m hm) ⟨cb.ngen.curr⟩ name dom.consumeTypeAnnotations' ty' bi
          wf).TrExprS (body.instantiate1 (.fvar ⟨cb.ngen.curr⟩)) body'' := by
        rw [Lean.Expr.instantiate1_eq]
        exact hbody''.inst_fvar henv.ordered (Sub.pushS (c₂.small m hm) _ _ _ _ _ wf).Δwf
      refine WF.bind (hsub.whnf hinst) fun e₁ h₁ => ?_
      obtain ⟨-, -, htr₁⟩ := h₁
      have harr : (List.map Expr.fvar fvs).toArray.push (.fvar ⟨cb.ngen.curr⟩) =
          (List.map Expr.fvar (fvs ++ [⟨cb.ngen.curr⟩])).toArray := by simp
      rw [harr]
      obtain ⟨hk, hbase⟩ := hI.base
      refine ih e₁ params.length (fvs ++ [⟨cb.ngen.curr⟩]) (idx ++ [ty']) _ wf body'' _ _ _
        ⟨?_, ?_, hP _ _ _ _ _ _ _ hI.pred, ⟨by simpa using hk, by simpa using hbase⟩, hsub,
          hsubP, htr₁, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _), fun hlen => ?_⟩
      · simpa using hI.tele.vlam
      · show VLCtx.fvars (_ :: cb.mlctx.vlctx) = _
        simp [VLCtx.fvars_cons_some, hI.fvars]
      · simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        obtain ⟨htd, hrel⟩ := hI.rel (by omega)
        have hj : idx.length < idx₀.length := by omega
        simp only [List.drop_length, List.nil_append, Nat.sub_self, VExpr.liftN_zero,
          List.drop_eq_getElem_cons hj, VExpr.foralls] at hrel
        rw [← hctx] at hrel
        obtain ⟨⟨_, hdd⟩, ⟨_, hbb⟩⟩ :=
          VEnv.IsDefEqU.forallE_inv henv hΓ (hdef.trans henv hΓ hrel)
        have hΓ' : OnCtx (dom' :: (c₂.small m hm).vlctx.toCtx) (c₂.venv.IsType c₂.lparams.length) :=
          ⟨hΓ, _, hdomS⟩
        refine ⟨?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil,
            List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
          refine htd.snoc ?_
          rw [← hctx]
          exact VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm ⟨_, hdd⟩) hdefty
        · obtain ⟨_, hbe⟩ := hbodyeq.symm.trans henv hΓ' ⟨_, hbb⟩
          have hbe' := hbe.defeqDFC henv.ordered (.succ .zero hdomty)
          simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, List.drop_length, Nat.sub_self, VExpr.liftN_zero,
            List.length_append, List.length_cons, List.length_nil]
          rw [← hctx]
          exact ⟨_, hbe'⟩
  · exact H _ _ _ _ _ _ _ _ _ _ hI

/-- The type of the major premise of a type of the block, under its parameters and `k` indices. -/
def majorTy (name : Name) (U n k : Nat) : VExpr :=
  .appN (.const name (VLevel.params U)) (VExpr.bvars n k ++ VExpr.bvars k 0)

/-- A motive's type, under the parameters, at the recursor's universe parameters: over the
indices `idx` and the major premise, into the sort `ml`. -/
def motiveTy (name : Name) (U n : Nat) (sh : List VLevel) (idx : List VExpr) (ml : VLevel) :
    VExpr :=
  .foralls (idx.map (·.instL sh)) (.forallE ((majorTy name U n idx.length).instL sh) (.sort ml))

/-- What `loopInd1` opened for a type `t` declared at `T'`, as the record `info` holds them: its
indices `fvs`, at translations `idx`, its major premise and its motive. The small context `m`
holds the parameters, the indices and the major premise, declared as in the kernel's context
`cb`; the motive's type translates over the parameters. -/
structure TypeVarsAt (cT : VContext) (pre : List Name) (Mp : TypeChecker.MLCtx)
    (pfvs : List FVarId) (params : List VExpr) (level ml : VLevel) (t : InductiveType)
    (T' : VExpr) (nidx : Nat) (info : RecInfo) (idx : List VExpr) (cb : VContext)
    (fvs : List FVarId) (majorFv motiveFv : FVarId) (m : TypeChecker.MLCtx) : Prop where
  info_eq : info = ⟨.fvar motiveFv, #[], #[], (fvs.map .fvar).toArray, .fvar majorFv⟩
  wf : m.WF cT.venv cT.lparams
  tele : m.IsTele (pfvs ++ fvs ++ [majorFv])
    (params ++ idx ++ [majorTy t.name cT.lparams.length params.length idx.length])
  base : ∃ hk, m.dropN (fvs.length + 1) hk = Mp
  nidx : idx.length = nidx
  defeq : cT.venv.IsDefEqU cT.lparams.length [] T' (.foralls (params ++ idx) (.sort level))
  agree : ∀ fv ∈ m.vlctx.fvars,
    (cb.lctx.find? fv).map LocalDecl.erase = (m.lctx.find? fv).map LocalDecl.erase
  motive_fresh : motiveFv ∉ m.vlctx.fvars
  motive : ∃ name mty, (cb.lctx.find? motiveFv).map LocalDecl.erase =
      some (.cdecl 0 motiveFv name mty .default .default) ∧
    TrExprS cb.venv cb.lparams (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx mty
      (motiveTy t.name cT.lparams.length params.length
        (VLevel.shift pre.length cT.lparams.length) idx ml) ∧
    cb.venv.IsType cb.lparams.length
      (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx.toCtx
      (motiveTy t.name cT.lparams.length params.length
        (VLevel.shift pre.length cT.lparams.length) idx ml)

def TypeVars (cT : VContext) (pre : List Name) (Mp : TypeChecker.MLCtx)
    (pfvs : List FVarId) (params : List VExpr) (level ml : VLevel) (t : InductiveType)
    (T' : VExpr) (nidx : Nat) (info : RecInfo) (idx : List VExpr) (cb : VContext) : Prop :=
  ∃ fvs majorFv motiveFv m,
    TypeVarsAt cT pre Mp pfvs params level ml t T' nidx info idx cb fvs majorFv motiveFv m

theorem VContext.push_find? {c : VContext} {name ty ty' bi h1 h2} {fv : FVarId}
    (h : c.lctx.Dom fv) : (c.push name ty ty' bi h1 h2).lctx.find? fv = c.lctx.find? fv := by
  have hb := (c.lctx_eq ▸ c.mlctx_wf.tr).1
  have fb : c.lctx.find? ⟨c.ngen.curr⟩ = none := by
    cases h : c.lctx.find? ⟨c.ngen.curr⟩; · rfl
    have := (c.lctx_eq ▸ c.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (c.reserved _ this) c.ngen.not_reserves_self
  show (c.lctx.mkLocalDecl _ name ty bi).find? fv = _
  rw [LocalContext.find?_mkLocalDecl hb fb, if_neg]
  rintro e; simp only [beq_iff_eq] at e; subst e
  simp [LocalContext.Dom, fb] at h

theorem VContext.push_erase {c : VContext} {name ty ty' bi h1 h2} {fv : FVarId} {d}
    (h : (c.lctx.find? fv).map LocalDecl.erase = some d) :
    ((c.push name ty ty' bi h1 h2).lctx.find? fv).map LocalDecl.erase = some d := by
  rw [VContext.push_find?]; · exact h
  cases e : c.lctx.find? fv <;> simp_all [LocalContext.Dom]

theorem TypeVarsAt.push {cT pre Mp pfvs params level ml t T' nidx info idx cb fvs majorFv motiveFv m}
    (H : TypeVarsAt cT pre Mp pfvs params level ml t T' nidx info idx cb fvs majorFv motiveFv m)
    {name ty ty' bi h1 h2} :
    TypeVarsAt cT pre Mp pfvs params level ml t T' nidx info idx
      (cb.push name ty ty' bi h1 h2) fvs majorFv motiveFv m := by
  refine { H with agree := fun fv hfv => ?_, motive := ?_ }
  · have := H.agree fv hfv
    obtain ⟨d, hd⟩ := H.wf.tr.find?_eq_some.2 hfv
    rw [hd] at this
    exact (VContext.push_erase this).trans (by rw [hd]; rfl)
  · obtain ⟨n, mty, h, h'⟩ := H.motive
    exact ⟨n, mty, VContext.push_erase h, h'⟩

theorem checkTypeAnnotation.defn {env : Environment} {n : Name} {k : Nat} {u : Unit}
    (h : checkTypeAnnotation env n k = .ok u) : ∃ v, env.find? n = some (.defnInfo v) := by
  unfold checkTypeAnnotation at h
  split at h <;> [exact ⟨_, ‹_›⟩; cases h]

/-- Stripping leaves an application of a constant that is not a definition alone. -/
theorem stripAnnotations_const_head {env : Environment} {n : Name} {ls : List Level}
    {args : Array Expr} {r : Expr} (hn : ∀ v, env.find? n ≠ some (.defnInfo v))
    (h : stripAnnotations env (mkAppN (.const n ls) args) = .ok r) :
    r = mkAppN (.const n ls) args := by
  have hfn : (mkAppN (.const n ls) args).getAppFn = .const n ls := by
    rw [mkAppN, ← Array.foldl_toList]
    have : ∀ (as : List Expr) (f : Expr), (as.foldl mkApp f).getAppFn = f.getAppFn := by
      intro as; induction as with
      | nil => intro; rfl
      | cons a as ih => intro f; rw [List.foldl_cons, ih]; rfl
    rw [this]; rfl
  generalize mkAppN (.const n ls) args = e at h hfn ⊢
  have bad {a : Name} {k : Nat} {x : Except Exception Expr} (ha : a = n)
      (h : (do checkTypeAnnotation env a k; x) = .ok r) : False := by
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i u hu
    obtain ⟨v, hv⟩ := checkTypeAnnotation.defn hu
    exact hn v (ha ▸ hv)
  unfold stripAnnotations at h
  split at h
  · exact (bad (by simpa [Expr.getAppFn] using hfn : _ ∧ _).1 h).elim
  · exact (bad (by simpa [Expr.getAppFn] using hfn : _ ∧ _).1 h).elim
  · exact (bad (by simpa [Expr.getAppFn] using hfn : _ ∧ _).1 h).elim
  · exact (bad (by simpa [Expr.getAppFn] using hfn : _ ∧ _).1 h).elim
  · cases h; rfl

theorem stripAnnotations_forallE {env : Environment} {name dom body bi} :
    stripAnnotations env (.forallE name dom body bi) = .ok (.forallE name dom body bi) := by
  rw [stripAnnotations.eq_5]
  · rfl
  all_goals intros; contradiction

theorem VContext.push_find?_self {c : VContext} {name ty ty' bi h1 h2} :
    ((c.push name ty ty' bi h1 h2).lctx.find? ⟨c.ngen.curr⟩).map LocalDecl.erase =
      some (.cdecl 0 ⟨c.ngen.curr⟩ name ty bi .default) := by
  have hb := (c.lctx_eq ▸ c.mlctx_wf.tr).1
  have fb : c.lctx.find? ⟨c.ngen.curr⟩ = none := by
    cases h : c.lctx.find? ⟨c.ngen.curr⟩; · rfl
    have := (c.lctx_eq ▸ c.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (c.reserved _ this) c.ngen.not_reserves_self
  show ((c.lctx.mkLocalDecl _ name ty bi).find? _).map _ = _
  rw [LocalContext.find?_mkLocalDecl hb fb]; simp [LocalDecl.erase]

/-- An application of translated terms translates when the translated application is typed. -/
theorem TrExprS.mkAppN_of_wf {env : VEnv} {Us : List Name} {Δ : VLCtx} (henv : env.Ordered)
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length)) :
    ∀ {args : List Expr} {args' : List VExpr} {f : Expr} {f' : VExpr}, TrExprS env Us Δ f f' →
    List.Forall₂ (TrExprS env Us Δ) args args' →
    (f'.appN args').WF env Us.length Δ.toCtx →
    TrExprS env Us Δ (mkAppN f args.toArray) (f'.appN args')
  | [], [], _, _, hf, .nil, _ => by simpa [mkAppN] using hf
  | a :: args, a' :: args', f, f', hf, .cons ha hargs, hwf => by
    have hwf1 : ((f'.app a').appN args').WF env Us.length Δ.toCtx := hwf
    have h1 := VExpr.appN_wf_prefix henv hΔ (as := [a']) (bs := args') (f := f') (by simpa using hwf)
    obtain ⟨_, _, h2, h3⟩ := h1.app_inv henv hΔ
    have := TrExprS.mkAppN_of_wf henv hΔ (f := .app f a) (.app h2 h3 hf ha) hargs hwf1
    simpa [mkAppN, Array.foldl_toList] using this

theorem _root_.Lean4Lean.VEnv.IsTele.teleDefEq_refl {env : VEnv} {U : Nat} :
    ∀ {Γ As}, env.IsTele U Γ As → env.TeleDefEq U Γ As As
  | _, [], .nil => .nil
  | _, _ :: _, .cons ⟨_, hA⟩ t => .cons ⟨_, hA⟩ (VEnv.IsTele.teleDefEq_refl t)

theorem mapM_ofLevel_params : ∀ {Us : List Name} (pre : List Name), (pre ++ Us).Nodup →
    (Us.map Level.param).mapM (VLevel.ofLevel (pre ++ Us)) =
      some ((List.range Us.length).map fun i => .param (i + pre.length))
  | [], _, _ => rfl
  | u :: Us, pre, hnd => by
    have h1 : VLevel.ofLevel (pre ++ u :: Us) (.param u) = some (.param pre.length) := by
      have : (pre ++ u :: Us).idxOf u = pre.length := by
        have hu : u ∉ pre := fun h => (List.nodup_append.1 hnd).2.2 u h u (.head _) rfl
        rw [List.idxOf_append, if_neg hu]; simp
      simp [VLevel.ofLevel, this]
    have h2 := mapM_ofLevel_params (Us := Us) (pre ++ [u]) (by simpa using hnd)
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
      at h2
    simp only [List.map_cons, List.mapM_cons, h1, h2, bind, Option.bind_some, pure,
      List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def, Nat.add_comm, Nat.add_left_comm]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.mkForall'_isTele : ∀ (n : Nat) {m : TypeChecker.MLCtx}
    {fvs₂ : List FVarId} {tys₂ : List VExpr} {fvs₁ tys₁}, fvs₂.length = n →
    m.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂) → fvs₂.length = tys₂.length → ∀ X hk,
    m.mkForall' fvs₂.length hk X = .foralls tys₂ X
  | 0, _, fvs₂, tys₂, _, _, hn, _, hlen, _, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm; rfl
  | n + 1, m, fvs₂, tys₂, fvs₁, tys₁, hn, h, hlen, X, hk => by
    obtain ⟨tys₂, ty, rfl⟩ : ∃ a b, tys₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys₂).resolve_left (by rintro rfl; simp_all)
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [← List.append_assoc, ← List.append_assoc] at h
    obtain ⟨name, ty', bi, m', rfl, h'⟩ := h.snoc_inv
    simp only [List.length_append, List.length_singleton, TypeChecker.MLCtx.mkForall']
    rw [TypeChecker.MLCtx.mkForall'_isTele n hn h' hlen, VExpr.foralls_append]; rfl

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.length {m : TypeChecker.MLCtx} {fvs tys}
    (h : m.IsTele fvs tys) : m.length = fvs.length := by
  induction h with
  | nil => rfl
  | vlam _ ih => simp [TypeChecker.MLCtx.length, ih]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.find?_dropN {env : VEnv} {Us : List Name} :
    ∀ {m : TypeChecker.MLCtx}, m.WF env Us → ∀ n hn {x : FVarId},
    x ∈ (m.dropN n hn).vlctx.fvars → m.lctx.find? x = (m.dropN n hn).lctx.find? x
  | _, _, 0, _, _, _ => rfl
  | .vlam fv _ _ _ _ m', wf, n+1, hn, x, hx
  | .vlet fv _ _ _ _ _ m', wf, n+1, hn, x, hx => by
    have hx' : x ∈ m'.vlctx.fvars := TypeChecker.MLCtx.dropN_fvars_subset n _ hx
    have hne : fv ≠ x := fun e => by subst e; exact (wf.1.tr.find?_eq_none.1 wf.2.1) hx'
    simp only [TypeChecker.MLCtx.lctx, TypeChecker.MLCtx.dropN]
    first
    | rw [LocalContext.find?_mkLocalDecl wf.1.tr.1 wf.2.1, if_neg (by simpa using hne)]
    | rw [LocalContext.find?_mkLetDecl wf.1.tr.1 wf.2.1, if_neg (by simpa using hne)]
    exact TypeChecker.MLCtx.WF.find?_dropN wf.1 n _ hx

theorem _root_.Lean4Lean.TypeChecker.MLCtx.mkForall_forallE : ∀ (n : Nat) {m : TypeChecker.MLCtx}
    {fvs : List FVarId} {tys : List VExpr}, m.IsTele fvs tys → ∀ hn name dom body bi,
    ∃ name' dom' body' bi', m.mkForall n hn (.forallE name dom body bi) =
      .forallE name' dom' body' bi'
  | 0, _, _, _, _, _, _, _, _, _ => ⟨_, _, _, _, rfl⟩
  | n + 1, m, fvs, tys, h, hn, name, dom, body, bi => by
    cases h with
    | nil => simp at hn
    | vlam h => exact TypeChecker.MLCtx.mkForall_forallE n h _ _ _ _ _

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.fvars_tr {env : VEnv} {Us : List Name}
    {m : TypeChecker.MLCtx} {fvs : List FVarId} {tys : List VExpr} (h : m.IsTele fvs tys)
    (hnd : fvs.Nodup) :
    List.Forall₂ (TrExprS env Us m.vlctx) (fvs.map .fvar) (VExpr.bvars fvs.length 0) := by
  refine List.forall₂_of_getElem? (by simp [VExpr.bvars]) fun j a b ha hb => ?_
  simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
  obtain ⟨fv, hfv, rfl⟩ := ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hfv
  have hb' : b = .bvar (fvs.length - 1 - j) := by
    have hj' : j < (List.range fvs.length).reverse.length := by simpa using hj
    simp only [VExpr.bvars, List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some,
      Option.some.injEq, List.getElem_reverse, List.getElem_range] at hb
    rw [← hb]; congr 1; simp
  subst hb'
  exact .fvar (h.find?_fvar hnd hj)

theorem mkAppN_append (f : Expr) (as bs : Array Expr) :
    mkAppN (mkAppN f as) bs = mkAppN f (as ++ bs) := by
  simp [mkAppN]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.dropN_instL (ls : List VLevel) :
    ∀ (m : TypeChecker.MLCtx) n hn hn',
    (m.instL ls).dropN n hn' = (m.dropN n hn).instL ls
  | _, 0, _, _ => rfl
  | .vlam .., n+1, h, h' | .vlet .., n+1, h, h' => by
    simp only [TypeChecker.MLCtx.instL, TypeChecker.MLCtx.dropN]
    exact TypeChecker.MLCtx.dropN_instL ls _ n _ _

theorem _root_.Lean4Lean.TypeChecker.MLCtx.length_instL (ls : List VLevel) :
    ∀ (m : TypeChecker.MLCtx), (m.instL ls).length = m.length
  | .nil => rfl
  | .vlam .. | .vlet .. => by
    simp [TypeChecker.MLCtx.instL, TypeChecker.MLCtx.length, TypeChecker.MLCtx.length_instL]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.instL (ls : List VLevel)
    {m : TypeChecker.MLCtx} {fvs tys} (h : m.IsTele fvs tys) :
    (m.instL ls).IsTele fvs (tys.map (·.instL ls)) := by
  induction h with
  | nil => exact .nil
  | vlam _ ih => simpa [TypeChecker.MLCtx.instL] using ih.vlam

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.fvarRevList : ∀ (n : Nat)
    {m : TypeChecker.MLCtx} {fvs₂ : List FVarId} {tys} {fvs₁ : List FVarId},
    fvs₂.length = n → m.IsTele (fvs₁ ++ fvs₂) tys → ∀ hk, m.fvarRevList n hk = fvs₂.reverse
  | 0, _, fvs₂, _, _, hn, _, _ => by obtain rfl := List.eq_nil_of_length_eq_zero hn; rfl
  | n + 1, m, fvs₂, tys, fvs₁, hn, h, hk => by
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hn
    rw [← List.append_assoc] at h
    obtain ⟨tys', ty, rfl⟩ : ∃ a b, tys = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys).resolve_left (by rintro rfl; have := h.length_eq; simp at this)
    obtain ⟨name, ty', bi, m', rfl, h'⟩ := h.snoc_inv
    simp only [TypeChecker.MLCtx.fvarRevList, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append]
    rw [TypeChecker.MLCtx.IsTele.fvarRevList n hn h']

/-- Closing over the top variables of a telescope context, through any local context that
declares them alike. -/
theorem mkForall_tele {lctx : LocalContext} {env : VEnv} {Us : List Name} {E : TypeChecker.MLCtx}
    (henv : env.WF) (hwf : E.WF env Us)
    {fvs₁ fvs₂ : List FVarId} {tys₁ tys₂ : List VExpr} (hT : E.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂))
    (hlen : fvs₂.length = tys₂.length)
    (hag : ∀ x ∈ fvs₂, (lctx.find? x).map LocalDecl.erase = (E.lctx.find? x).map LocalDecl.erase)
    {e : Expr} {e' : VExpr} (he : TrExprS env Us E.vlctx e e')
    (heT : env.IsType Us.length E.vlctx.toCtx e') :
    ∃ hk, lctx.mkForall (fvs₂.map .fvar).toArray e = E.mkForall fvs₂.length hk e ∧
      TrExprS env Us (E.dropN fvs₂.length hk).vlctx (E.mkForall fvs₂.length hk e)
        (.foralls tys₂ e') ∧
      env.IsType Us.length (E.dropN fvs₂.length hk).vlctx.toCtx (.foralls tys₂ e') := by
  have hk : fvs₂.length ≤ E.length := by rw [hT.length]; simp
  refine ⟨hk, ?_, ?_⟩
  · have h1 := TypeChecker.mkForall_agree (b := e) hag
    have h2 := hwf.mkForall_eq (arr := (fvs₂.map .fvar).toArray) (e := e) fvs₂.length hk (by
      rw [hT.fvarRevList fvs₂.length rfl hk]; simp [List.map_reverse])
    exact h1.trans h2
  · have := hwf.mkForall_trS henv he heT fvs₂.length hk
    rwa [TypeChecker.MLCtx.mkForall'_isTele fvs₂.length rfl hT hlen] at this

@[simp] theorem _root_.Lean4Lean.VLCtx.fvars_instL (ls : List VLevel) (Δ : VLCtx) :
    (Δ.instL ls).fvars = Δ.fvars := by
  rw [VLCtx.instL_eq_map, VLCtx.fvars, VLCtx.fvars, List.filterMap_map]; rfl

theorem VContext.curr_not_dom (c : VContext) : ¬c.lctx.Dom ⟨c.ngen.curr⟩ := fun h => by
  have htr := c.lctx_eq ▸ c.mlctx_wf.tr
  exact c.ngen.not_reserves_self (c.reserved _ (htr.find?_eq_some.1 (Option.isSome_iff_exists.1 h)))

/-- The facts `mkRecInfos` starts from, about the block and the small context `Mp` of its
parameters, in the environment `cT` the block was checked in. -/
structure RecSetup (cT : VContext) (pre : List Name) (Mp : TypeChecker.MLCtx)
    (pfvs : List FVarId) (params : List VExpr) (level ml : VLevel) (types : List InductiveType)
    (typeTr : List VExpr) (stats : InductiveStats) (elimLevel : Level) (env : Environment) :
    Prop where
  MpT : Mp.IsTele pfvs params
  par : stats.params.toList = pfvs.map .fvar
  levels : stats.levels = cT.lparams.map .param
  indConsts : stats.indConsts.toList = types.map fun T => .const T.name stats.levels
  nindices : stats.nindices.size = types.length
  typeTr_len : typeTr.length = types.length
  decl : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t → typeTr[j]? = some T' →
    ∃ idx₀ u,
    TrExprS cT.venv cT.lparams [] t.type T' ∧ cT.venv.IsType cT.lparams.length [] T' ∧
    cT.venv.IsDefEqU cT.lparams.length [] T' (.foralls (params ++ idx₀) (.sort u)) ∧
    u ≈ level ∧ stats.nindices[j]? = some idx₀.length
  const : ∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t → typeTr[j]? = some T' →
    cT.venv.constants t.name = some ⟨cT.lparams.length, T'⟩
  notDefn : ∀ t ∈ types, ∀ v, env.find? t.name ≠ some (.defnInfo v)
  ml : VLevel.ofLevel (pre ++ cT.lparams) elimLevel = some ml
  lpnd : (pre ++ cT.lparams).Nodup
  levelWF : level.WF cT.lparams.length

/-- What `loopInd1` opened for a type. -/
structure TyData where
  fvs : List FVarId
  major : FVarId
  motive : FVarId
  m : TypeChecker.MLCtx
  idx : List VExpr
  /-- The motive's declaration, and the translation of its type over the parameters. -/
  motName : Name
  mty : Expr
  mtr : VExpr

def TyData.block (td : TyData) : List FVarId := td.motive :: td.major :: td.fvs.reverse

def TyData.info (td : TyData) : RecInfo :=
  ⟨.fvar td.motive, #[], #[], (td.fvs.map .fvar).toArray, .fvar td.major⟩

/-- The parameters `base`, then the motives of `tds`, each over the parameters and the motives
before it. -/
def motivesCtx (base : TypeChecker.MLCtx) (tds : List TyData) : TypeChecker.MLCtx :=
  tds.zipIdx.foldl (fun B (td, j) => .vlam td.motive td.motName td.mty (td.mtr.liftN j) .default B)
    base

theorem motivesCtx_append (base : TypeChecker.MLCtx) (tds : List TyData) (td : TyData) :
    motivesCtx base (tds ++ [td]) =
      .vlam td.motive td.motName td.mty (td.mtr.liftN tds.length) .default (motivesCtx base tds) := by
  simp [motivesCtx, List.zipIdx_append]

theorem motivesCtx_lift (base : TypeChecker.MLCtx) : ∀ (n : Nat) (tds : List TyData),
    tds.length = n → VLCtx.FVLift' base.vlctx (motivesCtx base tds).vlctx 0
      (Lift.skipN .refl tds.length) 0
  | 0, tds, h => by obtain rfl := List.eq_nil_of_length_eq_zero h; exact .refl
  | n + 1, tds, h => by
    obtain ⟨tds, td, rfl⟩ : ∃ a b, tds = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tds).resolve_left (by rintro rfl; simp at h)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h
    rw [motivesCtx_append]
    have := VLCtx.FVLift'.skip_fvar (td.motive, td.mty.fvarsList)
      (.vlam (td.mtr.liftN tds.length)) (motivesCtx_lift base n tds h)
    simpa [VLocalDecl.depth, Lift.skipN_skipN] using this

/-- What `loopInd1` keeps, having opened the variables `tds` of the first types: the kernel's
context `cb` is `base` with their blocks pushed, and each is as `TypeVarsAt` says. -/
structure Ind1Inv (cT : VContext) (X : Name → Prop) (pre : List Name) (Mp : TypeChecker.MLCtx)
    (hMp : Mp.WF cT.venv cT.lparams) (pfvs : List FVarId) (params : List VExpr) (level ml : VLevel)
    (types : List InductiveType) (typeTr : List VExpr) (stats : InductiveStats)
    (env : Environment) (base : List FVarId) (tds : List TyData) (cb : VContext) : Prop where
  sub : ∃ ρp, Sub X pre ρp (cT.small Mp hMp) cb
  bext : ∃ ρB, Ext (motivesCtx (Mp.instL (VLevel.shift pre.length cT.lparams.length)) tds) cb ρB
  env : cb.env = env
  fvars : cb.mlctx.vlctx.fvars = (tds.reverse.map TyData.block).flatten ++ base
  recs : ∀ (j : Nat) (td : TyData), tds[j]? = some td → ∃ t T' nidx, types[j]? = some t ∧
    typeTr[j]? = some T' ∧
    stats.nindices[j]? = some nidx ∧
    TypeVarsAt cT pre Mp pfvs params level ml t T' nidx td.info td.idx cb td.fvs td.major
      td.motive td.m

theorem loopInd1.WF {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {hMp : Mp.WF cT.venv cT.lparams} {pfvs : List FVarId}
    {params : List VExpr} {level ml : VLevel} {types : List InductiveType} {typeTr : List VExpr}
    {stats : InductiveStats} {elimLevel : Level} {env : Environment} {base : List FVarId}
    (hS : RecSetup cT pre Mp pfvs params level ml types typeTr stats elimLevel env)
    {k : Array RecInfo → M α} {Q}
    (H : ∀ tds cb, tds.length = types.length →
      Ind1Inv cT X pre Mp hMp pfvs params level ml types typeTr stats env base tds cb →
      WF cb (k (tds.map TyData.info).toArray) Q) :
    ∀ n tds cb, tds.length + n = types.length →
      Ind1Inv cT X pre Mp hMp pfvs params level ml types typeTr stats env base tds cb →
      WF cb (mkRecInfos.loopInd1 stats types.toArray elimLevel tds.length
        (tds.map TyData.info).toArray k) Q := by
  intro n
  induction n with
  | zero =>
    intro tds cb hn hI
    rw [mkRecInfos.loopInd1, dif_neg (by simp; omega)]
    exact H tds cb (by omega) hI
  | succ n ih =>
    intro tds cb hn hI
    rw [mkRecInfos.loopInd1, dif_pos (by simp; omega)]
    have hlt : tds.length < types.length := by omega
    obtain ⟨t, ht⟩ : ∃ t, types[tds.length]? = some t := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨T', hT'⟩ : ∃ T', typeTr[tds.length]? = some T' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hS.typeTr_len]; exact hlt)⟩
    obtain ⟨idx₀, u, htr, hTT, hdef, hu, hnidx⟩ := hS.decl _ _ _ ht hT'
    have htype : types.toArray[tds.length].type = t.type := by
      simp [List.getElem?_eq_getElem hlt] at ht; simp [← ht]
    rw [htype]
    refine WF.bind (Q := (· = cb.toContext)) (fun _ h => by cases h; rfl) fun ctx hctx => ?_
    subst hctx
    obtain ⟨ρp, hsubP⟩ := hI.sub
    have henv : cT.venv.WF := cT.envAt.tr.wf
    have hΔ := (cT.small Mp hMp).Δwf
    have hTr : (cT.small Mp hMp).TrExprS t.type T' := by
      have := hTT; obtain ⟨_, hT⟩ := this
      exact TrExprS.of_nil henv (TypeChecker.MLCtx.noBV _) hΔ
        (hT.closedN' henv.ordered.closed trivial).1 htr
    refine WF.bind (hsubP.whnf hTr) fun e₁ h₁ => ?_
    obtain ⟨-, -, htr₁⟩ := h₁
    let P (cb' : VContext) : Prop := cb'.env = env ∧
      (∀ (j : Nat) (td : TyData), tds[j]? = some td → ∃ t T' nidx, types[j]? = some t ∧
        typeTr[j]? = some T' ∧ stats.nindices[j]? = some nidx ∧
        TypeVarsAt cT pre Mp pfvs params level ml t T' nidx td.info td.idx cb' td.fvs td.major
          td.motive td.m) ∧
      ∃ ρB, Ext (motivesCtx (Mp.instL (VLevel.shift pre.length cT.lparams.length)) tds) cb' ρB
    have hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2) := by
      intro cb name ty ty' bi h1 h2 ⟨he, hr, ρB, hB⟩
      refine ⟨he, fun j td hj => ?_, _, hB.skip h1 h2⟩
      obtain ⟨t, T', nidx, a, b, c, d⟩ := hr j td hj
      exact ⟨t, T', nidx, a, b, c, d.push⟩
    have hdefT : cT.venv.IsDefEqU cT.lparams.length (params.reverse) T'
        ((VExpr.foralls (params ++ idx₀) (.sort u)).liftN params.length) := by
      obtain ⟨_, hT⟩ := hTT
      have hc := (hdef.of_l henv trivial hT).closedN' henv.ordered.closed trivial
      rw [hc.2.1.liftN_eq (Nat.zero_le _)]
      exact hdef.weak0 henv.ordered
    refine loopArgs1.WF (hMp := hMp) (idx₀ := idx₀) (u := u) hS.MpT hS.par (F₀ := cb.mlctx.vlctx.fvars)
      (P := P) hP ?_ _ e₁ 0 [] [] Mp hMp T' cb ρp ρp
      ⟨by simpa using hS.MpT, by simp, ⟨hI.env, hI.recs, hI.bext⟩, ⟨Nat.zero_le _, rfl⟩, hsubP, hsubP,
        htr₁, Nat.zero_le _, fun _ => rfl, fun _ => ⟨.nil, ?_⟩⟩
    · intro r i fvs idx m hm V cb' ρ ρp' hA
      dsimp only
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨⟨hsort, hi⟩, hn⟩ := hcond
        have hlenp : pfvs.length = params.length := hS.MpT.length_eq
        have hsize : stats.params.size = params.length := by
          rw [← Array.length_toList, hS.par, List.length_map, hlenp]
        rw [hsize] at hi; subst hi
        have hfi : fvs.length = idx₀.length := by
          simp [hnidx] at hn; exact hn
        have hidxlen : idx.length = fvs.length := by
          have := hA.tele.length_eq; simp [hlenp] at this; omega
        obtain ⟨htd, -⟩ := hA.rel (by omega)
        rw [List.take_of_length_le (by omega)] at htd
        have hmwf := hm
        have hmT : cT.venv.IsTele cT.lparams.length [] (params ++ idx) := hA.tele.isTele hm
        obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ht
        have hic : stats.indConsts[tds.length]! = .const types[tds.length].name stats.levels := by
          have h1 : tds.length < stats.indConsts.size := by
            rw [← Array.length_toList, hS.indConsts]; simp; omega
          rw [getElem!_pos stats.indConsts _ h1, ← Array.getElem_toList]
          simp [hS.indConsts]
        have hpar' : stats.params = (pfvs.map .fvar).toArray := by rw [← hS.par]
        have htTy : mkAppN (mkAppN stats.indConsts[tds.length]! stats.params)
            (fvs.map .fvar).toArray =
            mkAppN (.const types[tds.length].name stats.levels) ((pfvs ++ fvs).map .fvar).toArray := by
          rw [hic, hpar', mkAppN_append]; simp
        rw [htTy]
        refine WF.bind (Q := (· = mkAppN (.const types[tds.length].name stats.levels)
          ((pfvs ++ fvs).map .fvar).toArray))
          (fun r hr => stripAnnotations_const_head
            (hA.pred.1 ▸ hS.notDefn _ (List.getElem_mem hj)) hr) fun tTy htTy' => ?_
        subst htTy'
        -- the declared type, at the indices read off
        have hU0 : cT.venv.IsType cT.lparams.length [] (.foralls (params ++ idx₀) (.sort u)) :=
          hTT.defeqU_l henv trivial hdef
        have huWF : u.WF cT.lparams.length := by
          obtain ⟨-, _, h⟩ := VEnv.IsType.foralls_inv henv.ordered hU0
          exact VEnv.IsDefEq.sort_inv' henv.ordered h (.inl rfl)
        have hPT : cT.venv.IsTele cT.lparams.length [] params := (VEnv.IsTele.append_inv hmT).1
        have hTD : cT.venv.TeleDefEq cT.lparams.length [] (params ++ idx₀) (params ++ idx) :=
          .append (VEnv.IsTele.teleDefEq_refl hPT) (by simpa using htd)
        have hdefI : cT.venv.IsDefEqU cT.lparams.length [] T'
            (.foralls (params ++ idx) (.sort level)) := by
          have h1 := hTD.foralls henv trivial hmT (R := .sort u) ⟨_, .sort huWF⟩
          obtain ⟨_, h2⟩ := VEnv.IsDefEq.foralls_congr hmT (u := .succ u)
            (e₁ := .sort u) (e₂ := .sort level) (.sortDF huWF hS.levelWF hu)
          exact (hdef.trans henv trivial h1).trans henv trivial ⟨_, h2⟩
        -- the major premise
        have hnd : (pfvs ++ fvs).Nodup := by
          have := hm.fvars_nodup; rw [hA.tele.fvars] at this; exact List.nodup_reverse.1 this
        have hargs := hA.tele.fvars_tr (env := cT.venv) (Us := cT.lparams) hnd
        rw [List.length_append, hlenp, ← hidxlen, ← VExpr.bvars_append] at hargs
        simp only [Nat.add_zero] at hargs
        have hc0 := VEnv.HasType.const0 (hS.const _ _ _ (List.getElem?_eq_getElem hj) hT') hTT
        have hc1 := hc0.defeqU_r henv trivial hdefI
        have hc2 := VEnv.HasType.appN_bvars henv.ordered hc1
        have hctxm : (cT.small m hm).vlctx.toCtx = (params ++ idx).reverse := hA.tele.toCtx
        have hc3 : cT.venv.HasType cT.lparams.length (cT.small m hm).vlctx.toCtx
            (majorTy types[tds.length].name cT.lparams.length params.length idx.length)
            (.sort level) := by
          rw [hctxm]
          simpa [majorTy, VExpr.liftN, ← VExpr.bvars_append] using hc2
        have hmaj : (cT.small m hm).TrExprS
            (mkAppN (.const types[tds.length].name stats.levels) ((pfvs ++ fvs).map .fvar).toArray)
            (majorTy types[tds.length].name cT.lparams.length params.length idx.length) := by
          refine TrExprS.mkAppN_of_wf henv.ordered (cT.small m hm).Δwf.toCtx ?_ hargs ⟨_, hc3⟩
          refine .const (hS.const _ _ _ (List.getElem?_eq_getElem hj) hT') ?_ (by simp [hS.levels])
          have hnd' : ([] ++ cT.lparams).Nodup :=
            List.Nodup.sublist (List.sublist_append_right _ _) hS.lpnd
          have := mapM_ofLevel_params (Us := cT.lparams) [] hnd'
          show (stats.levels).mapM (VLevel.ofLevel cT.lparams) = _
          simpa [hS.levels, VLevel.params] using this
        obtain ⟨wfM, hsubM⟩ := hA.sub.push (name := `t) (bi := .default) hmaj ⟨_, hc3⟩
        have hsubPM := hA.subP.skip (name := `t) (bi := .default) (hA.sub.trExprS hmaj)
          (hA.sub.isType ⟨_, hc3⟩)
        obtain ⟨ρB, hB⟩ := hA.pred.2.2
        have hBM := hB.skip (name := `t) (bi := .default) (hA.sub.trExprS hmaj)
          (hA.sub.isType ⟨_, hc3⟩)
        refine WF.withLocalDecl (hA.sub.trExprS hmaj) (hA.sub.isType ⟨_, hc3⟩) ?_
        refine WF.bind (Q := (· = (cb'.push `t _ _ .default (hA.sub.trExprS hmaj)
          (hA.sub.isType ⟨_, hc3⟩)).lctx)) (fun _ h => by cases h; rfl) fun lctx hl => ?_
        subst hl
        generalize hcb₂ : cb'.push `t _ _ .default (hA.sub.trExprS hmaj) (hA.sub.isType ⟨_, hc3⟩) = cb₂
          at hsubM hsubPM hBM ⊢
        have hE := hsubM.ext
        have hET := (hA.tele.vlam (fv := ⟨cb'.ngen.curr⟩) (name := `t) (bi := .default)
          (ty := mkAppN (.const types[tds.length].name stats.levels) ((pfvs ++ fvs).map .fvar).toArray)
          (ty' := majorTy types[tds.length].name cT.lparams.length params.length idx.length)).instL
          (VLevel.shift pre.length cT.lparams.length)
        rw [List.map_append (l₁ := params ++ idx)] at hET
        have hlp : cb₂.lparams = pre ++ cT.lparams := hsubM.lparams
        have hmlWF : ml.WF cb₂.lparams.length := by rw [hlp]; exact .of_ofLevel hS.ml
        have hsort (Δ) : TrExprS cb₂.venv cb₂.lparams Δ (.sort elimLevel) (.sort ml) :=
          .sort (by rw [hlp]; exact hS.ml)
        have hsortT (Γ) : cb₂.venv.IsType cb₂.lparams.length Γ (.sort ml) := ⟨_, .sort hmlWF⟩
        -- the inner closure, over the major premise
        obtain ⟨hk₁, eq₁, trS₁, isT₁⟩ := mkForall_tele (lctx := cb₂.lctx) cb₂.tc.Ewf hE.wf
          (fvs₁ := pfvs ++ fvs) (fvs₂ := [⟨cb'.ngen.curr⟩]) hET (by simp)
          (fun x hx => hE.lctx x (by
            simp at hx; subst hx
            simp [TypeChecker.MLCtx.vlctx_instL, VLCtx.instL_eq_map, Sub.pushS,
              TypeChecker.VContext.withMLC]))
          (hsort _) (hsortT _)
        -- the outer closure, over the indices
        have hmT' := hA.tele.instL (VLevel.shift pre.length cT.lparams.length)
        rw [List.map_append (l₁ := params)] at hmT'
        have hEwf := hE.wf
        obtain ⟨hk₂, eq₂, trS₂, isT₂⟩ := mkForall_tele (lctx := cb₂.lctx) cb₂.tc.Ewf hEwf.1
          (fvs₁ := pfvs) (fvs₂ := fvs) hmT' (by simp [hidxlen])
          (fun x hx => by
            have hx' : x ∈ (m.instL (VLevel.shift pre.length cT.lparams.length)).vlctx.fvars := by
              rw [TypeChecker.MLCtx.vlctx_instL, VLCtx.fvars_instL, hA.tele.fvars]
              simp [hx]
            refine (hE.lctx x ?_).trans ?_
            · simp only [Sub.pushS, TypeChecker.VContext.withMLC, TypeChecker.MLCtx.instL,
                TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons]
              exact .inr hx'
            · rw [TypeChecker.MLCtx.WF.find?_dropN hEwf 1 hk₁ hx']; rfl)
          trS₁ isT₁
        rw [show #[Expr.fvar ⟨cb'.ngen.curr⟩] = ([(⟨cb'.ngen.curr⟩ : FVarId)].map Expr.fvar).toArray
          from rfl, eq₁, eq₂]
        generalize hmot : TypeChecker.MLCtx.mkForall _ fvs.length hk₂ _ = motE at trS₂ ⊢
        have hfe : ∃ a b c d, motE = .forallE a b c d := by
          subst hmot
          exact TypeChecker.MLCtx.mkForall_forallE fvs.length hmT' hk₂ _ _ _ _
        refine WF.bind (Q := (motE = ·)) (fun r hr => by
          obtain ⟨a, b, c, d, rfl⟩ := hfe
          change stripAnnotations _ _ = _ at hr
          rw [stripAnnotations_forallE] at hr; cases hr; rfl) fun motE' he => ?_
        subst he
        obtain ⟨hkb, hbase⟩ := hA.base
        have hdrop := TypeChecker.MLCtx.dropN_instL (VLevel.shift pre.length cT.lparams.length) m
          fvs.length hkb hk₂
        rw [hbase] at hdrop
        have hmTr : TrExprS cb₂.venv cb₂.lparams
            (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx motE
            (motiveTy types[tds.length].name cT.lparams.length params.length
              (VLevel.shift pre.length cT.lparams.length) idx ml) := by
          rw [← hdrop]; exact trS₂
        have hmIT : cb₂.venv.IsType cb₂.lparams.length
            (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx.toCtx
            (motiveTy types[tds.length].name cT.lparams.length params.length
              (VLevel.shift pre.length cT.lparams.length) idx ml) := by
          rw [← hdrop]; exact isT₂
        -- the motive, over the parameters and the motives before it
        have hW := motivesCtx_lift (Mp.instL (VLevel.shift pre.length cT.lparams.length)) _ tds rfl
        have hBTr := hmTr.weakFV' cb₂.tc.Ewf.ordered hW hBM.wf.tr.wf
        have hBIT := hmIT.weak' cb₂.tc.Ewf.ordered hW.toCtx
        have hl : ∀ e : VExpr, e.lift' (Lift.refl.skipN tds.length) = e.liftN tds.length :=
          fun e => by simpa using VExpr.lift'_consN_skipN (e := e) (n := tds.length) (k := 0)
        simp only [Lift.consN] at hBTr hBIT
        rw [hl] at hBTr hBIT
        refine WF.withLocalDecl (hBM.trExprS hBTr) (hBM.isType hBIT) ?_
        let motName : Name :=
          if types.toArray.size > 1 then (`motive).appendIndexAfter (tds.length + 1) else `motive
        let td : TyData := ⟨fvs, ⟨cb'.ngen.curr⟩, ⟨cb₂.ngen.curr⟩,
          .vlam ⟨cb'.ngen.curr⟩ `t
            (mkAppN (.const types[tds.length].name stats.levels) ((pfvs ++ fvs).map .fvar).toArray)
            (majorTy types[tds.length].name cT.lparams.length params.length idx.length) .default m,
          idx, motName, motE, motiveTy types[tds.length].name cT.lparams.length params.length
              (VLevel.shift pre.length cT.lparams.length) idx ml⟩
        have hcb₂env : cb₂.env = env := by rw [← hcb₂]; exact hA.pred.1
        have hnew : TypeVarsAt cT pre Mp pfvs params level ml types[tds.length] T' idx₀.length
            td.info td.idx (cb₂.push motName motE _ .default (hBM.trExprS hBTr) (hBM.isType hBIT))
            td.fvs td.major td.motive td.m := by
          refine ⟨rfl, wfM, hA.tele.vlam, ⟨show fvs.length + 1 ≤ m.length + 1 by omega, hbase⟩,
            by simp [td]; omega, hdefI, fun fv hfv => ?_, fun hfv => ?_,
            ⟨_, motE, VContext.push_find?_self, hmTr, hmIT⟩⟩
          · have := hsubM.lctx fv hfv
            obtain ⟨d, hd⟩ := Sub.find?_cs
              (cs := Sub.pushS (cT.small m hm) ⟨cb'.ngen.curr⟩ `t _ _ .default wfM) hfv
            rw [hd] at this
            exact (VContext.push_erase this).trans (congrArg (Option.map LocalDecl.erase) hd).symm
          · exact cb₂.curr_not_dom (hsubM.dom hfv)
        have := ih (tds ++ [td])
          (cb₂.push motName motE _ .default (hBM.trExprS hBTr) (hBM.isType hBIT)) (by simp; omega) {
          sub := ⟨_, hsubPM.skip (hBM.trExprS hBTr) (hBM.isType hBIT)⟩
          bext := ⟨_, by rw [motivesCtx_append]; exact hBM.push hBTr hBIT⟩
          env := hcb₂env
          fvars := ?_
          recs := ?_ }
        · simpa [TyData.info, td, motName] using this
        · show VLCtx.fvars (_ :: cb₂.mlctx.vlctx) = _
          have hcf : cb₂.mlctx.vlctx.fvars = ⟨cb'.ngen.curr⟩ :: cb'.mlctx.vlctx.fvars := by
            rw [← hcb₂]; rfl
          simp [hcf, hA.fvars, hI.fvars, TyData.block, td]
        · intro j td' hj'
          rcases Nat.lt_or_ge j tds.length with hlt' | hge'
          · rw [List.getElem?_append_left hlt'] at hj'
            obtain ⟨t, T'', nidx, a, b, c, d⟩ := hA.pred.2.1 j td' hj'
            refine ⟨t, T'', nidx, a, b, c, ?_⟩
            have d' := (d.push (name := `t) (bi := .default) (h1 := hA.sub.trExprS hmaj)
              (h2 := hA.sub.isType ⟨_, hc3⟩))
            rw [hcb₂] at d'
            exact d'.push
          · rw [List.getElem?_append_right hge'] at hj'
            obtain ⟨hj0, rfl⟩ : j - tds.length = 0 ∧ td = td' := by
              cases h : j - tds.length <;> simp_all
            obtain rfl : j = tds.length := by omega
            exact ⟨_, T', idx₀.length, List.getElem?_eq_getElem hj, hT', hnidx, hnew⟩
      · exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
    · have := hS.MpT.toCtx
      simp only [List.length_nil, List.drop_zero, List.reverse_nil, List.nil_append,
        Nat.sub_zero]
      exact hdefT

end AddInductive
end Lean4Lean

import Lean4Lean.Verify.Environment.NestedAux
import Lean4Lean.Verify.Environment.NestedFinal
import Lean4Lean.Verify.TypeChecker

/-!
# The nested occurrences' arguments, typed by the kernel's check

`addInductive` checks each nested occurrence `J Ls Ds` the elimination recorded, in the
environment with the block's types as axioms and the block's parameters as local variables
(`res.lctx`). The check walks `J`'s literal binders (`LitApp.argTypes`), so each argument is typed
at its binder. Here that is read back over the parameters as bound variables, for
`VInductiveType.AuxWF.of_created`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

/-- A variable looked up past local declarations of other variables is lifted past them. -/
theorem VLCtx.find?_append_fvars {x : FVarId} : ∀ {E : VLCtx} {Δ : VLCtx},
    (∀ e ∈ E, ∃ y deps A, e = (some (y, deps), .vlam A) ∧ y ≠ x) →
    (E ++ Δ).find? (.inr x) =
      (Δ.find? (.inr x)).map fun (e, A) => (e.liftN E.length, A.liftN E.length)
  | [], Δ, _ => by cases h : Δ.find? (.inr x) <;> simp [h]
  | e :: E, Δ, hE => by
    obtain ⟨y, deps, A, rfl, hy⟩ := hE e (.head _)
    have ih := VLCtx.find?_append_fvars (E := E) (Δ := Δ) fun e he => hE e (.tail _ he)
    simp only [List.cons_append, VLCtx.find?, VLCtx.next, beq_iff_eq, hy, if_false, ih]
    cases h : Δ.find? (.inr x) <;>
      simp [VLocalDecl.depth, VExpr.liftN_liftN]

/-- Opening the leading binders of a translated telescope at fresh variables models the local
context it builds: each variable is the bound variable of its binder. -/
theorem ElimNestedInductive.Opens.mlctx {env : VEnv} (henv : env.Ordered) {Us : List Name} :
    ∀ {lctx₀ ty xs lctx body}, ElimNestedInductive.Opens lctx₀ ty xs lctx body →
    ∀ {M₀ : MLCtx}, M₀.WF env Us → M₀.lctx = lctx₀ → (∀ x ∈ xs, x ∉ M₀.vlctx.fvars) → xs.Nodup →
    ∀ {Qs B}, Qs.length = xs.length → TrExprS env Us M₀.vlctx ty (.foralls Qs B) →
    ∃ (M : MLCtx) (E : VLCtx), M.WF env Us ∧ M.lctx = lctx ∧ M.vlctx = E ++ M₀.vlctx ∧
      E.length = xs.length ∧ (∀ e ∈ E, ∃ y deps A, e = (some (y, deps), .vlam A) ∧ y ∈ xs) ∧
      M.vlctx.toCtx = Qs.reverse ++ M₀.vlctx.toCtx ∧
      M.vlctx.fvars = xs.reverse ++ M₀.vlctx.fvars ∧
      (∀ j (hj : j < xs.length), ∃ A,
        M.vlctx.find? (.inr xs[j]) = some (.bvar (xs.length - 1 - j), A)) ∧
      TrExprS env Us M.vlctx body B
  | _, _, _, _, _, .nil, M₀, hM, hl, _, _, Qs, B, hQ, hT => by
    cases Qs with
    | nil => exact ⟨M₀, [], hM, hl, rfl, rfl, nofun, by simp, by simp, nofun, by simpa using hT⟩
    | cons => simp at hQ
  | lctx₀, _, _, _, _, @ElimNestedInductive.Opens.cons _ x nm dom bi bd xs lctx' ty' ho,
      M₀, hM, hl, hfr, hnd, Qs, B, hQ, hT => by
    obtain ⟨q, Qs', rfl⟩ : ∃ q Qs', Qs = q :: Qs' := by
      cases Qs with
      | nil => simp at hQ
      | cons q Qs' => exact ⟨q, Qs', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hQ
    rw [VExpr.foralls_cons] at hT
    cases hT with | forallE h1 _ hq hbd =>
    obtain ⟨hxn, hnd'⟩ := List.nodup_cons.1 hnd
    have hx0 : x ∉ M₀.vlctx.fvars := hfr x (.head _)
    have hM₁ : (MLCtx.vlam x nm dom q bi M₀).WF env Us :=
      ⟨hM, hM.tr.find?_eq_none.2 hx0, hq, h1⟩
    have hbd' := TrExprS.inst_fvar henv hM₁.tr.wf hbd
    obtain ⟨M, E, hMw, hMl, hMv, hEl, hE, hMc, hMfv, hMf, hMb⟩ :=
      ElimNestedInductive.Opens.mlctx henv ho hM₁ (by simp [MLCtx.lctx, hl])
        (fun y hy hy' => by
          simp only [MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons] at hy'
          rcases hy' with rfl | hy'
          · exact hxn hy
          · exact hfr y (.tail _ hy) hy')
        hnd' hQ (by simpa using hbd')
    refine ⟨M, E ++ [(some (x, dom.fvarsList), .vlam q)], hMw, hMl, by simp [hMv], by simp [hEl],
      ?_, ?_, by simp [hMfv, MLCtx.vlctx], ?_, hMb⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨y, deps, A, rfl, hy⟩ := hE e he; exact ⟨y, deps, A, rfl, .tail _ hy⟩
      · simp at he; subst he; exact ⟨x, _, q, rfl, .head _⟩
    · simp [hMc, MLCtx.vlctx, VLCtx.toCtx]
    · intro j hj
      cases j with
      | zero =>
        refine ⟨(VLocalDecl.vlam q).type.liftN E.length, ?_⟩
        rw [hMv, VLCtx.find?_append_fvars (fun e he => ?_)]
        · simp [MLCtx.vlctx, VLocalDecl.type, VExpr.liftN, liftVar, hEl]
        · obtain ⟨y, deps, A, rfl, hy⟩ := hE e he
          exact ⟨y, deps, A, rfl, fun h => hxn (by simp at h; exact h ▸ hy)⟩
      | succ j =>
        obtain ⟨A, hA⟩ := hMf j (by simpa using hj)
        exact ⟨A, by simpa [Nat.sub_sub, Nat.add_comm] using hA⟩

/-- A context whose `let` values are closed below their declarations. -/
def VLCtx.ClosedVals : VLCtx → Prop
  | [] => True
  | (_, .vlam _) :: Δ => ClosedVals Δ
  | (_, .vlet _ e) :: Δ => e.ClosedN (VLCtx.toCtx Δ).length ∧ ClosedVals Δ

theorem VLCtx.ClosedVals.find? : ∀ {Δ : VLCtx} {v x A}, Δ.ClosedVals →
    Δ.find? v = some (x, A) → x.ClosedN Δ.toCtx.length
  | [], _, _, _, _, h => by cases h
  | (ofv, d) :: Δ, v, x, A, hΔ, h => by
    simp only [VLCtx.find?] at h
    split at h
    · cases h
      cases d with
      | vlam => exact Nat.zero_lt_succ _
      | vlet _ e => exact hΔ.1
    · obtain ⟨⟨e', A'⟩, h', he⟩ := Option.bind_eq_some_iff.1 h
      cases he
      cases d with
      | vlam => exact (VLCtx.ClosedVals.find? (Δ := Δ) hΔ h').liftN
      | vlet _ e => exact (VLCtx.ClosedVals.find? hΔ.2 h').liftN

/-- A plain translation is closed below its context's variables. -/
theorem PTr.closedN {CL : Literal → Prop} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : PTr Us CL Δ e e') (hΔ : Δ.ClosedVals) : e'.ClosedN Δ.toCtx.length := by
  induction H with
  | bvar h | fvar h => exact hΔ.find? h
  | sort | const => trivial
  | app _ _ ih1 ih2 => exact ⟨ih1 hΔ, ih2 hΔ⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 hΔ, ih2 hΔ⟩
  | letE _ _ _ _ ih2 ih3 => exact ih3 ⟨ih2 hΔ, hΔ⟩
  | lit _ _ ih | mdata _ ih | proj _ ih => exact ih hΔ

theorem paramCtx_closedVals : ∀ {As : List VExpr}, (paramCtx As).ClosedVals
  | [] => trivial
  | _ :: As => paramCtx_closedVals (As := As)

theorem paramCtx_toCtx : ∀ {As : List VExpr}, (paramCtx As).toCtx = As
  | [] => rfl
  | _ :: As => congrArg _ (paramCtx_toCtx (As := As))

theorem _root_.Lean.Expr.abstract'_mkAppList (xs : List FVarId) (d : Nat) (f : Expr)
    (as : List Expr) :
    (f.mkAppList as).abstract' xs d = (f.abstract' xs d).mkAppList (as.map (·.abstract' xs d)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [Expr.mkAppList, List.map_cons, ih]; rfl

theorem _root_.Lean.Expr.instantiate'_mkAppList (subst : List Expr) (d : Nat) (f : Expr)
    (as : List Expr) :
    (f.mkAppList as).instantiate' subst d =
      (f.instantiate' subst d).mkAppList (as.map (·.instantiate' subst d)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [Expr.mkAppList, List.map_cons, ih]; rfl

/-- A nested occurrence's key: the earlier constant applied to the occurrence's arguments, taken
from the constructor's parameters `xs` to the block's `xsP`. -/
theorem ElimNestedInductive.replaceParamsVal_mkAppRange {xsP xs : List FVarId} {J : Name}
    {Ls : List Level} {nI : Nat} {args : Array Expr} (hle : nI ≤ args.size) :
    ElimNestedInductive.replaceParamsVal (xsP.map .fvar).toArray
        (mkAppRange (.const J Ls) 0 nI args) (xs.map .fvar).toArray =
      mkAppN (.const J Ls) ((args.extract 0 nI).toList.map fun a =>
        (a.abstract' xs).instantiate' (xsP.map .fvar).reverse).toArray := by
  rw [Expr.mkAppRange_eq (i := 0) (j := nI) (l₁ := []) (l₂ := (args.extract 0 nI).toList)
      (l₃ := (args.extract nI args.size).toList) (by
        simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero,
          List.nil_append]
        rw [List.take_of_length_le (l := List.drop nI args.toList) (by simp),
          List.take_append_drop]) rfl
      (by simp; omega),
    ElimNestedInductive.mkAppN_eq_mkAppList]
  simp only [ElimNestedInductive.replaceParamsVal, List.toArray, Expr.abstract_eq',
    Expr.instantiateRev_eq, Expr.instantiate_eq', Expr.abstract'_mkAppList,
    Expr.instantiate'_mkAppList, List.map_map, Function.comp_def, Array.toList_reverse]
  rfl

/-- A context for running the type checker in `env`, in the local context `M` models. -/
def TypeChecker.VContext.ofMLCtx {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) (lparams : List Name) (fuel : FuelConfig) (M : MLCtx)
    (hM : M.WF venv lparams) : VContext where
  env; safety; lparams; fuel; venv
  lctx := M.lctx
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr
  mlctx := M
  mlctx_wf := hM
  lctx_eq := rfl

theorem TypeChecker.VState.WF.ofMLCtx {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    {wf : VEnvAt env safety venv} {lparams : List Name} {fuel : FuelConfig} {M : MLCtx}
    {hM : M.WF venv lparams}
    (hres : ∀ fv ∈ M.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv) :
    VState.WF (.ofMLCtx wf lparams fuel M hM) {} where
  trctx := hM.tr
  ngen_wf := hres
  ectx := ⟨M.vlctx, _, hM.tr.wf, .refl, .empty, hres⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  inferTypeC_lit := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- Running the type checker in a local context it models: what holds of the result, holds at
the final state. -/
theorem TypeChecker.M.WF.runMLCtx {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) {lparams : List Name} {fuel : FuelConfig} {M : MLCtx}
    (hM : M.WF venv lparams)
    (hres : ∀ fv ∈ M.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv)
    {x : TypeChecker.M α} {Q} (H : x.WF (.ofMLCtx wf lparams fuel M hM) {} Q) {a : α}
    (h : TypeChecker.M.run env safety M.lctx lparams fuel x = .ok a) :
    ∃ s : VState, s.WF (.ofMLCtx wf lparams fuel M hM) ∧ Q a s := by
  simp only [TypeChecker.M.run, StateT.run', Functor.map, Except.map] at h
  split at h <;> cases h; rename_i eq
  obtain ⟨s, -, -, hs, hQ⟩ := H (.ofMLCtx hres) _ _ eq
  exact ⟨s, hs, hQ⟩

theorem List.Forall₂.unique_r {R S : α → β → Prop} (h : ∀ a b b', R a b → S a b' → b = b') :
    ∀ {l : List α} {l₁ l₂ : List β}, List.Forall₂ R l l₁ → List.Forall₂ S l l₂ → l₁ = l₂
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => by
    rw [h _ _ _ h1 h2, List.Forall₂.unique_r h t1 t2]

theorem foldl_insert_getElem? {pairs : List (Expr × Name)} :
    ∀ (m : Std.TreeMap Name Expr Name.quickCmp) {n : Name}, n ∉ pairs.map (·.2) →
      (pairs.foldl (fun m p => m.insert p.2 p.1) m)[n]? = m[n]? := by
  induction pairs with
  | nil => intros; rfl
  | cons p pairs ih =>
    intro m n hn
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [List.foldl_cons, ih _ hn.2, Std.TreeMap.getElem?_insert, if_neg]
    rw [Std.LawfulEqCmp.compare_eq_iff_eq]; exact fun h => hn.1 h.symm

/-- The map of recorded occurrences has each record, when their names are distinct. -/
theorem foldl_insert_mem_toList {pairs : List (Expr × Name)} (hnd : (pairs.map (·.2)).Nodup)
    {e : Expr} {n : Name} (h : (e, n) ∈ pairs) :
    (n, e) ∈ Std.TreeMap.toList
      ((pairs.foldl (fun m (e, n) => m.insert n e) {} : NameMap Expr) :
        Std.TreeMap Name Expr Name.quickCmp) := by
  show (n, e) ∈ Std.TreeMap.toList (pairs.foldl (fun m p => m.insert p.2 p.1)
    (∅ : Std.TreeMap Name Expr Name.quickCmp))
  rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some]
  generalize (∅ : Std.TreeMap Name Expr Name.quickCmp) = m
  induction pairs generalizing m with
  | nil => cases h
  | cons p pairs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [foldl_insert_getElem? _ hnd.1]
      exact Std.TreeMap.getElem?_insert_self
    · exact ih hnd.2 h _

/-- The elimination's fresh variables are not the type checker's. -/
theorem freshIds_kernel_reserves : ∀ {g : NameGenerator} {n : Nat} {x : FVarId},
    g.namePrefix = `_nested_fresh → x ∈ ElimNestedInductive.freshIds g n →
    ({} : TypeChecker.State).ngen.Reserves x
  | g, n + 1, x, hg, h => by
    simp only [ElimNestedInductive.freshIds, List.mem_cons] at h
    rcases h with rfl | h
    · intro i hi
      simp only [NameGenerator.curr, FVarId.mk.injEq, hg] at hi
      have h := congrArg Name.getPrefix hi
      simp only [Name.getPrefix] at h
      exact absurd h (by decide)
    · exact freshIds_kernel_reserves (g := g.next) hg h

theorem ElimNestedInductive.run.loop_params {env : Environment} {nparams : Nat}
    {lctx : LocalContext} {params : Array Expr} :
    ∀ (fuel i : Nat) (s : State) (res : Result) (s' : State),
      run.loop nparams lctx params i fuel env s = .ok (res, s') → res.params = params
  | 0, i, s, res, s', h => by rw [run.loop] at h; cases h
  | fuel + 1, i, s, res, s', h => by
    rw [run.loop, bind_apply] at h
    rw [show (MonadState.get : M State) env s = .ok (s, s) from rfl] at h
    dsimp only at h
    split at h
    · obtain ⟨_, s₁, -, h⟩ := bind_ok h
      obtain ⟨_, s₂, hm, h⟩ := bind_ok h
      cases hm
      exact run.loop_params fuel (i + 1) _ res s' h
    · cases h; rfl

/-- The parameters the elimination opens are fresh variables of its own. -/
theorem ElimNestedInductive.run_params {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : Result}
    (h : (run fuel nparams types env).run' { lvls := lparams.map .param, newTypes := types.toArray }
      = .ok res) :
    ∀ x, .fvar x ∈ res.params → ({} : TypeChecker.State).ngen.Reserves x := by
  obtain ⟨⟨res', s'⟩, h1, h2⟩ : ∃ p, run fuel nparams types env
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok p ∧ p.1 = res := by
    revert h; unfold StateT.run'
    cases run fuel nparams types env _ <;> simp [Functor.map, Except.map]
  subst h2
  unfold run at h1
  split at h1
  · obtain ⟨lctx, ty, -, hk⟩ := withParams.loop_open _ _ _ _ _ _ _ h1
    have := run.loop_params _ _ _ _ _ hk
    intro x hx
    rw [this] at hx
    simp only [Array.empty_append, List.mem_toArray, List.mem_map, Expr.fvar.injEq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact freshIds_kernel_reserves rfl hy
  · cases h1

/-- The arguments of a nested occurrence, typed at the earlier constant's literal binders over the
block's parameters, from the kernel's check of the occurrences (`hargTy` of
`VInductiveType.AuxWF.of_created`). The check runs in `envT`, modelled by `venvT`, in the local
context `res.lctx` that opens the first type's leading binders `xsP`, whose translations are `Qs`.
The occurrence `K` was recorded for the earlier constant `J` at the levels `Ls` and the arguments
`args`, over the constructor's parameters `xs`; `ys` translates those arguments over the
parameters as bound variables. -/
theorem occ_argTypes {envT : Environment} {safety : DefinitionSafety} {venvT : VEnv}
    (wfT : VEnvAt envT safety venvT) {lparams : List Name} {fuel : FuelConfig}
    {res : ElimNestedInductive.Result}
    (hocc : TypeChecker.M.run envT safety res.lctx lparams fuel
      ((Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp)).forM fun p =>
        do _ ← TypeChecker.checkType p.2) = .ok ())
    {Ity bodyI : Expr} {xsP : List FVarId}
    (hoI : ElimNestedInductive.Opens {} Ity xsP res.lctx bodyI) (hndP : xsP.Nodup)
    (hres : ∀ x ∈ xsP, ({} : TypeChecker.State).ngen.Reserves x)
    {Qs : List VExpr} {B : VExpr} (hQl : Qs.length = xsP.length)
    (hI : TrExprS venvT lparams [] Ity (.foralls Qs B))
    (hfvK : ∀ p ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp),
      p.2.FVarsIn (· ∈ xsP))
    {aux : Name} {K : Expr}
    (hmem : (aux, K) ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp))
    {xs : List FVarId} {J : Name} {Ls : List Level} {nI : Nat} {args : Array Expr}
    (hK : K = ElimNestedInductive.replaceParamsVal (xsP.map .fvar).toArray
      (mkAppRange (.const J Ls) 0 nI args) (xs.map .fvar).toArray)
    (hle' : nI ≤ args.size) (hlb : ∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0)
    (hnd : xs.Nodup) (hxs : xs.length = xsP.length)
    {Jv : InductiveVal} (hJ : envT.find? J = some (.inductInfo Jv)) {JT : VExpr}
    (hJty : TrExprS venvT Jv.levelParams [] Jv.type JT) (hsz : nI ≤ Jv.type.leadingForalls)
    {lvls : List VLevel} (hls : Ls.mapM (VLevel.ofLevel lparams) = some lvls)
    (hLs : Jv.levelParams.length = Ls.length)
    {CL : Literal → Prop} {Ps ys : List VExpr} (hPs : Ps.length = xs.length)
    (hys : List.Forall₂ (PTr lparams CL (paramCtx Ps))
      ((args.extract 0 nI).toList.map (·.abstractList xs)) ys)
    {E : VEnv} (hle : venvT ≤ E) {U : Nat} (hU : lparams.length = U) :
    ∀ L R, PTr Jv.levelParams CL [] Jv.type (.foralls L R) → L.length = nI →
      ∀ i (a A : VExpr), ys[i]? = some a → L[i]? = some A →
        E.HasType U Qs.reverse a
          ((A.instL lvls).subst (VExpr.Subst.dflt.consList (ys.take i))) := by
  intro L R hJL hLl i a A ha hA
  have henv := wfT.tr.wf
  -- the local context of the check, modelled
  obtain ⟨M, Ectx, hMw, hMl, -, -, -, hMc, hMfv, hMf, -⟩ :=
    ElimNestedInductive.Opens.mlctx henv.ordered hoI (M₀ := .nil) trivial rfl (by simp) hndP hQl
      (by simpa using hI)
  simp only [MLCtx.vlctx, VLCtx.toCtx, VLCtx.fvars_nil, List.append_nil] at hMc hMfv
  have hresM : ∀ fv ∈ M.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv := by
    rw [hMfv]; exact fun fv h => hres fv (List.mem_reverse.1 h)
  let c := TypeChecker.VContext.ofMLCtx wfT lparams fuel M hMw
  have hfvc : ∀ p ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp),
      p.2.FVarsIn (· ∈ c.vlctx.fvars) := fun p hp =>
    (hfvK p hp).mono fun x hx => by
      show x ∈ M.vlctx.fvars; rw [hMfv]; exact List.mem_reverse.2 hx
  obtain ⟨s, hs, hQ⟩ := TypeChecker.M.WF.runMLCtx wfT hMw hresM
    (checkType.forM_lit (c := c) _ (fun p : Name × Expr => p.2) hfvc) (hMl ▸ hocc)
  obtain ⟨⟨eK, hKtr⟩, ty, hlit⟩ := hQ _ hmem
  -- the occurrence: `J` applied to its arguments over the parameters
  generalize hDl : (args.extract 0 nI).toList.map
    (fun a => (a.abstract' xs).instantiate' (xsP.map .fvar).reverse) = Dl
  have hKe : K = mkAppN (.const J Ls) Dl.toArray := by
    rw [hK, ElimNestedInductive.replaceParamsVal_mkAppRange hle', hDl]
  simp only at hKtr hlit
  rw [hKe] at hKtr hlit
  rw [ElimNestedInductive.mkAppN_eq_mkAppList] at hKtr
  obtain ⟨-, Ds', -, -, hDs⟩ := TrExprS.mkAppList_inv hKtr
  have hDll : Dl.length = nI := by rw [← hDl]; simp; omega
  -- its translations are `ys`
  have hargsC : ∀ a ∈ (args.extract 0 nI).toList, a.looseBVarRange' = 0 := by
    intro a ha
    rw [Array.toList_extract] at ha
    simp [List.extract] at ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    exact hlb j (by simp at hj; omega) _ (by simp [List.getElem_take])
  have hpar : List.Forall₂ (PTr lparams CL M.vlctx) (xsP.map .fvar) (VExpr.bvars xsP.length 0) := by
    refine Lean4Lean.List.forall₂_of_getElem? (by simp) fun j x y hx hy => ?_
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    simp only [List.length_map] at hj
    obtain ⟨A', hA'⟩ := hMf j hj
    have : y = .bvar (xsP.length - 1 - j) := by
      simp [VExpr.bvars, hj] at hy
      rw [← hy]
    subst this
    simpa using PTr.fvar (Us := lparams) (CL := CL) hA'
  have hPys : List.Forall₂ (PTr lparams CL M.vlctx) Dl ys := by
    rw [← hDl, List.forall₂_map_left_iff]
    rw [List.forall₂_map_left_iff] at hys
    refine forall₂_imp_mem (fun a y ha hy => ?_) hys
    rw [Expr.abstract'_eq_abstractList (Nat.le_of_eq (hargsC a ha)) hnd]
    have := PTr.inst' (Δ := M.vlctx) (As := Ps) hpar (by simp [hPs, hxs]) .base hy
    rwa [show (VExpr.Subst.dflt.consList (VExpr.bvars xsP.length 0)).liftN 0 =
        VExpr.Subst.dflt.consList (VExpr.bvars xsP.length 0) from rfl,
      VExpr.subst_dflt_bvars_of_closed (by
        have := hy.closedN paramCtx_closedVals
        rwa [paramCtx_toCtx, hPs, hxs] at this)] at this
  have hDsy : Ds' = ys := by
    refine List.Forall₂.unique_r (fun a b b' h1 h2 => ?_) (by simpa using hDs) hPys
    exact h1.toPTr.unique h2
  subst hDsy
  -- the check of the occurrence types each argument at its binder
  have hJL' : JT = .foralls L R := hJty.toPTr.unique hJL
  subst hJL'
  have := LitApp.argTypes (c := c) hs hlit hJ hJty hls hLs (by simp [hLl, hDll])
    (by simp only [List.size_toArray, hDll]; exact hsz) (fun a ha => by
      obtain ⟨_, -, h⟩ := (List.Forall₂.forall_exists_l (by simpa using hDs) a (by simpa using ha))
      exact h.fvarsIn) (by simpa using hDs) i a A ha hA
  have hc : c.vlctx.toCtx = Qs.reverse := hMc
  have h' := this.mono hle
  simp only [hc] at h'
  exact hU ▸ h'

end Lean4Lean

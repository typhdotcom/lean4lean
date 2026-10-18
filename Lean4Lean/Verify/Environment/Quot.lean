import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Support.Monad
import Lean4Lean.Quot

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

/-- The translation of an expression built from bound variables, sorts, constants, applications
and pi types, which is syntactic. -/
def _root_.Lean.Expr.plainTr (Us : List Name) : Expr → Option VExpr
  | .bvar i => some (.bvar i)
  | .sort u => (VLevel.ofLevel Us u).map .sort
  | .const c us => (us.mapM (VLevel.ofLevel Us)).map (.const c)
  | .app f a => return .app (← f.plainTr Us) (← a.plainTr Us)
  | .forallE _ A B _ => return .forallE (← A.plainTr Us) (← B.plainTr Us)
  | _ => none

/-- A local context of bound variables only, as under the binders of a closed term. -/
def _root_.Lean4Lean.VLCtx.AllBV : VLCtx → Prop
  | [] => True
  | (ofv, d) :: Δ => ofv = none ∧ (∃ A, d = .vlam A) ∧ VLCtx.AllBV Δ

theorem VLCtx.AllBV.find?_bvar : ∀ {Δ : VLCtx}, Δ.AllBV → ∀ {i}, i < Δ.toCtx.length →
    ∃ A, Δ.find? (.inl i) = some (.bvar i, A)
  | (_, _) :: Δ, ⟨rfl, ⟨A, rfl⟩, hΔ⟩, i, hi => by
    cases i with
    | zero => exact ⟨_, rfl⟩
    | succ i =>
      obtain ⟨B, hB⟩ := hΔ.find?_bvar (i := i) (by simpa [VLCtx.toCtx] using hi)
      exact ⟨B.liftN 1, by simp [VLCtx.find?, VLCtx.next, hB, VLocalDecl.depth, VExpr.liftN]⟩

theorem _root_.Lean.Expr.plainTr_eqv' {Us : List Name} {e₁ : Expr} :
    ∀ {e₂ : Expr}, e₁.eqv' e₂ = true → e₁.plainTr Us = e₂.plainTr Us := by
  induction e₁ with
  | app f a ihf iha =>
    intro e₂ h; cases e₂ <;> simp [Expr.eqv'] at h
    simp [Expr.plainTr, ihf h.1, iha h.2]
  | forallE _ A B _ ihA ihB =>
    intro e₂ h; cases e₂ <;> simp [Expr.eqv'] at h
    simp [Expr.plainTr, ihA h.1, ihB h.2]
  | _ => intro e₂ h; cases e₂ <;> simp [Expr.eqv'] at h; simp_all [Expr.plainTr]

/-- A plain expression translates to its plain translation wherever that is well formed. -/
theorem TrExprS.of_plainTr {env : VEnv} (henv : env.Ordered) {Us : List Name} :
    ∀ {e : Expr} {e' : VExpr} {Δ : VLCtx}, Δ.AllBV → OnCtx Δ.toCtx (env.IsType Us.length) →
    e.plainTr Us = some e' → e'.WF env Us.length Δ.toCtx → TrExprS env Us Δ e e'
  | .bvar i, e', Δ, hΔ, _, h, hwf => by
    cases h
    obtain ⟨_, hA⟩ := hwf
    obtain ⟨A, hL⟩ := VEnv.HasType.bvar_inv henv ‹_› hA
    obtain ⟨B, hB⟩ := hΔ.find?_bvar hL.lt
    exact .bvar hB
  | .sort u, e', Δ, _, _, h, _ => by
    simp only [Expr.plainTr, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl⟩ := h
    exact .sort hu
  | .const c us, e', Δ, _, hΓ, h, hwf => by
    simp only [Expr.plainTr, Option.map_eq_some_iff] at h
    obtain ⟨us', hus, rfl⟩ := h
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΓ
    exact .const hci hus (by rw [← hlen, Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hus)])
  | .app f a, e', Δ, hΔ, hΓ, h, hwf => by
    simp only [Expr.plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    obtain ⟨A, B, hf', ha'⟩ := hwf.app_inv henv hΓ
    exact .app hf' ha' (of_plainTr henv hΔ hΓ hf ⟨_, hf'⟩) (of_plainTr henv hΔ hΓ ha ⟨_, ha'⟩)
  | .forallE _ A B _, e', Δ, hΔ, hΓ, h, hwf => by
    simp only [Expr.plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨A', hA, B', hB, rfl⟩ := h
    obtain ⟨_, hT⟩ := hwf
    obtain ⟨hA', hB'⟩ := VEnv.HasType.forallE_inv henv hT
    have hΔ' : VLCtx.AllBV ((none, .vlam A') :: Δ) := ⟨rfl, ⟨_, rfl⟩, hΔ⟩
    exact .forallE hA' hB' (of_plainTr henv hΔ hΓ hA (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (of_plainTr henv hΔ' ⟨hΓ, hA'⟩ hB (let ⟨_, h⟩ := hB'; ⟨_, h⟩))
  | .lam .., _, _, _, _, h, _ | .letE .., _, _, _, _, h, _ | .lit _, _, _, _, _, h, _
  | .mvar _, _, _, _, _, h, _ | .fvar _, _, _, _, _, h, _ | .mdata .., _, _, _, _, h, _
  | .proj .., _, _, _, _, h, _ => nomatch h

/-! `addQuot` and `checkEqType` build their types in a fresh local context; these lemmas compute
them. -/
namespace QuotInit

def L₀ : LocalContext := {}
def G₀ : NameGenerator := {}

theorem wf₀ : L₀.WF := .nil
theorem find?₀ : L₀.find? x = none := by rw [wf₀.find?_eq_find?_toList]; rfl

theorem run_eq {m} [Monad m] {α} (x : ExprBuildT m α) : ExprBuildT.run x = x L₀ G₀ := rfl

theorem withLocalDecl_eq {m} [Monad m] {α} (n : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → ExprBuildT m α) :
    withLocalDecl n bi ty k = fun lctx ngen =>
      k (.fvar ⟨ngen.curr⟩) (lctx.mkLocalDecl ⟨ngen.curr⟩ n ty bi) ngen.next := rfl

theorem read_eq {m} [Monad m] : (read : ExprBuildT m LocalContext) = fun lctx _ => pure lctx :=
  rfl

theorem find?_self {L : LocalContext} (H : L.WF) (h : L.find? fv = none) :
    (L.mkLocalDecl fv n ty bi).find? fv = some (.cdecl L.decls.size fv n ty bi .default) := by
  rw [LocalContext.find?_mkLocalDecl H h]; simp

theorem find?_ne {L : LocalContext} (H : L.WF) (h : L.find? fv = none) (hne : fv ≠ x) :
    (L.mkLocalDecl fv n ty bi).find? x = L.find? x := by
  rw [LocalContext.find?_mkLocalDecl H h]; simp [hne]

theorem wf_mk {L : LocalContext} (H : L.WF) (h : L.find? fv = none) :
    (L.mkLocalDecl fv n ty bi).WF = True := eq_true (H.mkLocalDecl h)

theorem mkForall1 {L : LocalContext} :
    L.mkForall #[.fvar a] b = LocalContext.mkBindingList false L [a] b :=
  LocalContext.mkBinding_eq (xs := [a])

theorem mkForall2 {L : LocalContext} :
    L.mkForall #[.fvar a₁, .fvar a₂] b = LocalContext.mkBindingList false L [a₁, a₂] b :=
  LocalContext.mkBinding_eq (xs := [a₁, a₂])

theorem mkForall3 {L : LocalContext} :
    L.mkForall #[.fvar a₁, .fvar a₂, .fvar a₃] b =
      LocalContext.mkBindingList false L [a₁, a₂, a₃] b :=
  LocalContext.mkBinding_eq (xs := [a₁, a₂, a₃])

theorem mkForall4 {L : LocalContext} :
    L.mkForall #[.fvar a₁, .fvar a₂, .fvar a₃, .fvar a₄] b =
      LocalContext.mkBindingList false L [a₁, a₂, a₃, a₄] b :=
  LocalContext.mkBinding_eq (xs := [a₁, a₂, a₃, a₄])

theorem g1 : G₀.curr = .num `_uniq 1 := rfl
theorem g2 : G₀.next.curr = .num `_uniq 2 := rfl
theorem g3 : G₀.next.next.curr = .num `_uniq 3 := rfl
theorem g4 : G₀.next.next.next.curr = .num `_uniq 4 := rfl
theorem g5 : G₀.next.next.next.next.curr = .num `_uniq 5 := rfl
theorem g6 : G₀.next.next.next.next.next.curr = .num `_uniq 6 := rfl

/-- The types `addQuot` declares. -/
def quotType : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.sort (.param `u)) .default) .implicit

def quotMkType : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `a (.bvar 1) (.app (.app (.const ``Quot [.param `u]) (.bvar 2)) (.bvar 1)) .default)
      .default) .implicit

def quotLiftType : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `β (.sort (.param `v))
        (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
          (.forallE `a
            (.forallE `a (.bvar 3)
              (.forallE `b (.bvar 4)
                (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const ``Eq [.param `v]) (.bvar 4))
                    (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1))) .default) .default)
              .default)
            (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 4)) (.bvar 3)) (.bvar 3)
              .default) .default) .default) .implicit) .implicit) .implicit

def quotIndType : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default)
      (.forallE `β
        (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 1)) (.bvar 0)) (.sort .zero)
          .default)
        (.forallE `mk
          (.forallE `a (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app (.const ``Quot.mk [.param `u]) (.bvar 3)) (.bvar 2))
              (.bvar 0))) .default)
          (.forallE `q (.app (.app (.const ``Quot [.param `u]) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit) .implicit

def quotInfo : ConstantInfo :=
  .quotInfo { name := ``Quot, levelParams := [`u], type := quotType, kind := .type }
def quotMkInfo : ConstantInfo :=
  .quotInfo { name := ``Quot.mk, levelParams := [`u], type := quotMkType, kind := .ctor }
def quotLiftInfo : ConstantInfo :=
  .quotInfo { name := ``Quot.lift, levelParams := [`u, `v], type := quotLiftType, kind := .lift }
def quotIndInfo : ConstantInfo :=
  .quotInfo { name := ``Quot.ind, levelParams := [`u], type := quotIndType, kind := .ind }

end QuotInit
open QuotInit

theorem addQuot_eq {env : Environment} (h : env.quotInit = false) :
    Environment.addQuot env = (do
      checkEqType env
      env.checkName ``Quot
      env.checkName ``Quot.mk
      env.checkName ``Quot.lift
      env.checkName ``Quot.ind
      pure (markQuotInit ((((env.add quotInfo).add quotMkInfo).add quotLiftInfo).add quotIndInfo))) := by
  unfold Environment.addQuot
  simp only [h, run_eq, withLocalDecl_eq, read_eq]
  simp only [bind, ReaderT.bind, pure, ReaderT.pure, Except.pure, Except.bind]
  simp (config := {decide := true, maxDischargeDepth := 30}) only [mkForall1, mkForall2,
    mkForall3, mkForall4, find?_self, find?_ne, wf_mk, wf₀, find?₀, g1, g2, g3, g4, g5, g6, ne_eq,
    not_false_eq_true, and_true, List.not_mem_nil, or_false, List.nodup_nil, exists_eq',
    forall_eq_or_imp, forall_eq, FVarId.mk.injEq, List.mem_cons, List.nodup_cons,
    Option.some.injEq, LocalContext.mkBindingList1, List.foldr, Expr.abstract1, Expr.abstractList,
    LocalContext.mkBindingList, LocalContext.mkBindingList.core, LocalContext.mkBindingList.go,
    Expr.abstract', List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.idxOf?_cons, List.idxOf?_nil, beq_iff_eq,
    if_false, if_true, Expr.arrow, Expr.prop, mkApp2, mkApp3]
  rfl

theorem checkEqType.WF {env : Environment} :
    (checkEqType env).WF fun _ => ∃ info, env.find? ``Eq = some (.inductInfo info) ∧
      info.isUnsafe = false ∧ ∃ u, info.levelParams = [u] ∧
      info.type.eqv' (.forallE `α (.sort (.param u)) (.forallE `a (.bvar 0)
        (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .implicit) = true := by
  intro _ h
  unfold checkEqType at h
  simp only [run_eq, withLocalDecl_eq, read_eq, Environment.get, bind, ReaderT.bind, pure,
    Except.pure, Except.bind] at h
  cases hf : env.find? ``Eq with
  | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
  simp only [hf] at h
  cases ci with
  | inductInfo info => ?_
  | _ => cases h
  refine ⟨info, rfl, ?_⟩
  cases hu : info.isUnsafe
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> [rename_i u hlp; cases h]
    split at h <;> [skip; cases h]
    refine ⟨rfl, u, hlp, ?_⟩
    split at h
    · cases h
    rename_i hEq
    split at hEq
    · simp [liftM, monadLift, MonadLift.monadLift, throw, throwThe, MonadExceptOf.throw] at hEq
    rename_i hne
    simp (config := {decide := true, maxDischargeDepth := 30}) only [mkForall1, find?_self,
      wf₀, find?₀, g1, List.not_mem_nil, or_false, exists_eq', forall_eq,
      List.mem_cons, Option.some.injEq, LocalContext.mkBindingList1, Expr.abstract1,
      Expr.abstractList, LocalContext.mkBindingList, LocalContext.mkBindingList.core,
      LocalContext.mkBindingList.go, Expr.abstract', List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.idxOf?_cons, List.idxOf?_nil, beq_iff_eq, if_false, if_true, Expr.arrow, Expr.prop, bne,
      Bool.not_eq_true'] at hne
    rw [← Expr.eqv_eq]
    exact Bool.of_not_eq_false hne
  · simp [hu, throw, throwThe, MonadExceptOf.throw] at h

section
open VEnv
variable {env : VEnv}

theorem eqConst_wf : eqConst.WF env := ⟨_, by type_tac⟩
theorem quotConst_wf : quotConst.WF env := ⟨_, by type_tac⟩
theorem quotMkConst_wf (quot : env.constants ``Quot = some quotConst) :
    quotMkConst.WF env := ⟨_, by type_tac⟩
theorem quotLiftConst_wf (quot : env.constants ``Quot = some quotConst)
    (eq : env.constants ``Eq = some eqConst) : quotLiftConst.WF env := ⟨_, by type_tac⟩
theorem quotIndConst_wf (quot : env.constants ``Quot = some quotConst)
    (mk : env.constants ``Quot.mk = some quotMkConst) : quotIndConst.WF env := ⟨_, by type_tac⟩

end

theorem plainTr_eqType (u : Name) :
    (Expr.forallE `α (.sort (.param u)) (.forallE `a (.bvar 0)
      (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .implicit).plainTr [u] =
    some eqConst.type := by
  simp [Expr.plainTr, VLevel.ofLevel, eqConst]

theorem plainTr_quotType : quotType.plainTr [`u] = some quotConst.type := by
  simp [Expr.plainTr, VLevel.ofLevel, quotType, quotConst]
theorem plainTr_quotMkType : quotMkType.plainTr [`u] = some quotMkConst.type := by
  simp [Expr.plainTr, VLevel.ofLevel, quotMkType, quotMkConst]
theorem plainTr_quotLiftType : quotLiftType.plainTr [`u, `v] = some quotLiftConst.type := by
  simp +decide [Expr.plainTr, VLevel.ofLevel, quotLiftType, quotLiftConst]
theorem plainTr_quotIndType : quotIndType.plainTr [`u] = some quotIndConst.type := by
  simp [Expr.plainTr, VLevel.ofLevel, quotIndType, quotIndConst]

/-- `VEnv.addConst` once the name is known to be fresh. -/
def _root_.Lean4Lean.VEnv.insertConst (env : VEnv) (n : Name) (ci : VConstant) : VEnv :=
  { env with constants := fun m => if n = m then some ci else env.constants m }

theorem VEnv.addConst_of_none {env : VEnv} {n ci} (h : env.constants n = none) :
    env.addConst n ci = some (env.insertConst n ci) := by
  simp [VEnv.addConst, h, VEnv.insertConst]

namespace QuotInit

def quotNames : List Name := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- The model after quotient initialization. -/
def quotVEnv (venv : VEnv) : VEnv :=
  ((((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk quotMkConst).insertConst
    ``Quot.lift quotLiftConst).insertConst ``Quot.ind quotIndConst).addDefEq quotDefEq

/-- The constant map after quotient initialization. -/
def quotConsts (C : ConstMap) : ConstMap :=
  (((C.insert ``Quot quotInfo).insert ``Quot.mk quotMkInfo).insert ``Quot.lift quotLiftInfo).insert
    ``Quot.ind quotIndInfo

theorem quotVEnv_steps {venv : VEnv} (hv : ∀ n ∈ quotNames, venv.constants n = none) :
    ∃ v₁ v₂ v₃ v₄, venv.addConst ``Quot quotConst = some v₁ ∧
      v₁.addConst ``Quot.mk quotMkConst = some v₂ ∧ v₂.addConst ``Quot.lift quotLiftConst = some v₃ ∧
      v₃.addConst ``Quot.ind quotIndConst = some v₄ ∧ quotVEnv venv = v₄.addDefEq quotDefEq := by
  simp only [quotNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hv
  obtain ⟨h1, h2, h3, h4⟩ := hv
  refine ⟨_, _, _, _, VEnv.addConst_of_none h1, VEnv.addConst_of_none ?_,
    VEnv.addConst_of_none ?_, VEnv.addConst_of_none ?_, rfl⟩ <;>
    simp [VEnv.insertConst, h2, h3, h4]

theorem quotVEnv_mono {venv₁ venv₂ : VEnv} (H : venv₁ ≤ venv₂)
    (hv₁ : ∀ n ∈ quotNames, venv₁.constants n = none)
    (hv₂ : ∀ n ∈ quotNames, venv₂.constants n = none) : quotVEnv venv₁ ≤ quotVEnv venv₂ := by
  obtain ⟨_, _, _, _, a1, a2, a3, a4, ha⟩ := quotVEnv_steps hv₁
  obtain ⟨_, _, _, _, b1, b2, b3, b4, hb⟩ := quotVEnv_steps hv₂
  rw [ha, hb]
  exact VEnv.addDefEq_mono <| VEnv.addConst_mono (VEnv.addConst_mono
    (VEnv.addConst_mono (VEnv.addConst_mono H a1 b1) a2 b2) a3 b3) a4 b4

theorem trConstant {venv : VEnv} (henv : venv.Ordered) {ci : ConstantInfo} {ci' : VConstant}
    (hs : ci.safety = .safe) (hl : ci.levelParams.length = ci'.uvars)
    (htr : ci.type.plainTr ci.levelParams = some ci'.type) (hwf : ci'.WF venv) :
    TrConstant .safe venv ci ci' :=
  ⟨hs ▸ DefinitionSafety.le_rfl, hl,
    TrExprS.of_plainTr henv trivial trivial htr (let ⟨_, h⟩ := hwf; ⟨_, hl ▸ h⟩)⟩

/-- Each model takes the `AddQuot` step. -/
theorem addQuot_of {C : ConstMap} {venv : VEnv} (mapWF : C.WF) (henv : venv.Ordered)
    (hq : venv.QuotReady) (hC : ∀ n ∈ quotNames, C.find? n = none)
    (hv : ∀ n ∈ quotNames, venv.constants n = none) :
    AddQuot C (quotConsts C) venv (quotVEnv venv) := by
  obtain ⟨v₁, v₂, v₃, v₄, e1, e2, e3, e4, he⟩ := quotVEnv_steps hv
  have o1 := henv.const quotConst_wf e1
  have q1 : v₁.constants ``Quot = some quotConst := by
    rw [VEnv.addConst_constants_eq e1]; simp
  have o2 := o1.const (quotMkConst_wf q1) e2
  have q2 := (VEnv.addConst_le e2).constants q1
  have m2 : v₂.constants ``Quot.mk = some quotMkConst := by
    rw [VEnv.addConst_constants_eq e2]; simp
  have eq2 : v₂.constants ``Eq = some eqConst := (VEnv.addConst_le e2).constants
    ((VEnv.addConst_le e1).constants hq)
  have o3 := o2.const (quotLiftConst_wf q2 eq2) e3
  have q3 := (VEnv.addConst_le e3).constants q2
  have m3 := (VEnv.addConst_le e3).constants m2
  simp only [quotNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hC
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have w1 := mapWF.insert ``Quot quotInfo c1
  have f3 : ((C.insert ``Quot quotInfo).insert ``Quot.mk quotMkInfo).find? ``Quot.lift = none := by
    rw [w1.find?_insert, mapWF.find?_insert]; simpa using c3
  have f4 : (((C.insert ``Quot quotInfo).insert ``Quot.mk quotMkInfo).insert ``Quot.lift
      quotLiftInfo).find? ``Quot.ind = none := by
    rw [(w1.insert _ _ (by rw [mapWF.find?_insert]; simpa using c2)).find?_insert, w1.find?_insert,
      mapWF.find?_insert]
    simpa using c4
  refine ⟨[`u], quotType, v₁, trConstant henv rfl rfl plainTr_quotType quotConst_wf, c1, e1, ?_⟩
  refine ⟨[`u], quotMkType, v₂, trConstant o1 rfl rfl plainTr_quotMkType (quotMkConst_wf q1),
    by rw [mapWF.find?_insert]; simpa using c2, e2, ?_⟩
  refine ⟨[`u, `v], quotLiftType, v₃,
    trConstant o2 rfl rfl plainTr_quotLiftType (quotLiftConst_wf q2 eq2),
    f3, e3, ?_⟩
  refine ⟨[`u], quotIndType, v₄, trConstant o3 rfl rfl plainTr_quotIndType (quotIndConst_wf q3 m3),
    f4, e4, ?_⟩
  exact ⟨rfl, he.symm⟩

theorem quotConsts_wf {C : ConstMap} (mapWF : C.WF) (hC : ∀ n ∈ quotNames, C.find? n = none) :
    (quotConsts C).WF ∧ ∀ n, n ∉ quotNames → (quotConsts C).find? n = C.find? n := by
  simp only [quotNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hC ⊢
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have w1 := mapWF.insert ``Quot quotInfo c1
  have w2 := w1.insert ``Quot.mk quotMkInfo (by rw [mapWF.find?_insert]; simpa using c2)
  have w3 := w2.insert ``Quot.lift quotLiftInfo (by
    rw [w1.find?_insert, mapWF.find?_insert]; simpa using c3)
  refine ⟨w3.insert ``Quot.ind quotIndInfo (by
    rw [w2.find?_insert, w1.find?_insert, mapWF.find?_insert]; simpa using c4), fun n hn => ?_⟩
  simp only [not_or] at hn
  simp only [quotConsts, w3.find?_insert, w2.find?_insert, w1.find?_insert, mapWF.find?_insert,
    beq_iff_eq, Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2.1, Ne.symm hn.2.2.2, if_false]

theorem quotNames_nonprim : ∀ n ∈ quotNames, Environment.primitives.contains n = false := by
  simp +decide [quotNames, Environment.primitives, NameSet.ofList, NameSet.contains]

end QuotInit

/-- Initializing quotients: `checkEqType` finds a safe `Eq` of the expected type, which each
model has as `eqConst`, and the four constants `addQuot` adds translate to theirs. -/
theorem addQuot.WF_uninit [VEnv.Injective] {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (h : env.quotInit = false) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rw [addQuot_eq h]
  have mapWF := (wf.tr (safety := .safe)).map_wf
  refine checkEqType.WF.bind fun _ ⟨info, hEq, hu, u, hlp, htype⟩ => ?_
  refine (checkName.WF mapWF _ _).bind fun _ ⟨c1, _⟩ => ?_
  refine (checkName.WF mapWF _ _).bind fun _ ⟨c2, _⟩ => ?_
  refine (checkName.WF mapWF _ _).bind fun _ ⟨c3, _⟩ => ?_
  refine (checkName.WF mapWF _ _).bind fun _ ⟨c4, _⟩ => ?_
  refine .pure ?_
  have hE : ∀ n ∈ quotNames, env.find? n = none := by
    simp only [quotNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨c1, c2, c3, c4⟩
  have hC : ∀ n ∈ quotNames, env.constants.find? n = none := fun n hn => by
    rw [← mapWF.find?'_eq_find?]; exact hE n hn
  have hv (s) : ∀ n ∈ quotNames, (ves.venv s).constants n = none := by
    intro n hn
    cases hc : (ves.venv s).constants n with
    | none => rfl
    | some ci =>
      obtain ⟨ci, hci, -⟩ := (wf.tr (safety := s)).find?_iff.2 ⟨_, hc⟩
      cases (hE n hn).symm.trans hci
  have hq (s) : (ves.venv s).QuotReady := by
    have henv := (wf.tr (safety := s)).wf.ordered
    have hsafe : (ConstantInfo.inductInfo info).safety = .safe := by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hu]
    obtain ⟨ci', hci', -, hlen, htr⟩ :=
      (wf.tr (safety := s)).find? hEq (hsafe ▸ DefinitionSafety.le_safe)
    have htr' : TrExprS (ves.venv s) info.levelParams [] info.type eqConst.type := by
      refine TrExprS.of_plainTr henv trivial trivial ?_ ?_
      · rw [Expr.plainTr_eqv' htype, hlp]; exact plainTr_eqType u
      · rw [hlp]; exact let ⟨_, h⟩ := eqConst_wf (env := ves.venv s); ⟨_, h⟩
    have hty := TrExprS.unique (TrExprS.IsUnique.all _) htr htr'
    have hU : ci'.uvars = eqConst.uvars := by
      rw [← hlen]; simp [ConstantInfo.levelParams, ConstantInfo.toConstantVal, hlp]; rfl
    show (ves.venv s).constants ``Eq = some eqConst
    rw [hci']; cases ci'; simp_all
  have ⟨mapWF', hfind⟩ := quotConsts_wf mapWF hC
  refine ⟨⟨fun s => quotVEnv (ves.venv s)⟩, ?_,
    fun s => (addQuot_of mapWF (wf.tr (safety := s)).wf.ordered (hq s) hC (hv s)).le⟩
  exact {
    tr {s} := .quot (hq s) (addQuot_of mapWF (wf.tr (safety := s)).wf.ordered (hq s) hC (hv s))
      (h ▸ wf.tr)
    hasPrimitives {s} := by
      obtain ⟨_, _, _, _, e1, e2, e3, e4, he⟩ := quotVEnv_steps (hv s)
      have hp := quotNames_nonprim
      simp only [quotNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hp
      show (quotVEnv _).HasPrimitives
      rw [he]
      exact ((((wf.hasPrimitives.addConst hp.1 e1).addConst hp.2.1 e2).addConst hp.2.2.1 e3).addConst
        hp.2.2.2 e4).addDefEq
    safePrimitives {n ci} hf hp := by
      change (quotConsts env.constants).find?' n = some ci at hf
      rw [mapWF'.find?'_eq_find?] at hf
      by_cases hn : n ∈ quotNames
      · rw [quotNames_nonprim n hn] at hp; cases hp
      rw [hfind n hn, ← mapWF.find?'_eq_find?] at hf
      exact wf.safePrimitives hf hp
    mono {s s'} hle := quotVEnv_mono (wf.mono hle) (hv s') (hv s) }

end Lean4Lean

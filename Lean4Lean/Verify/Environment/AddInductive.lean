import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Inductive.Add

/-!
# Verification framework for `AddInductive.M`

`AddInductive.M` reads a context holding the environment and the local context the kernel has
opened, and lifts each type checker call into a fresh run of `TypeChecker.M` over that local
context. A model of the context is a type checker model of the environment, plus a model of the
local context whose free variables the kernel's name generator has already handed out and the
type checker's never will.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel TypeChecker

/-! ### The kernel's level tests are exact

`isNeverZero` and `isAlwaysZero` are syntactic, but on levels without metavariables they decide
the semantic properties the spec states: levels are monotone, so a level is never zero iff it is
nonzero when every parameter is `0`, and always zero iff it is zero when every parameter is `1`. -/

theorem eval_zero_of_not_isNeverZero (h : VLevel.ofLevel Us u = some u')
    (H : u.isNeverZero = false) : u'.eval [] = 0 := by
  induction u generalizing u' with
    simp [Level.isNeverZero, VLevel.ofLevel] at H h
  | zero => subst h; rfl
  | param => obtain ⟨-, rfl⟩ := h; simp [VLevel.eval]
  | max _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp [VLevel.eval, ih1 h1 H.1, ih2 h2 H.2]
  | imax _ _ _ ih2 =>
    obtain ⟨_, _, _, h2, rfl⟩ := h
    simp [VLevel.eval, Lean.Nat.imax, ih2 h2 H]

theorem ofLevel_isNeverZero_iff (h : VLevel.ofLevel Us u = some u') :
    u.isNeverZero ↔ u'.IsNeverZero := by
  refine ⟨ofLevel_isNeverZero h, fun H => ?_⟩
  cases e : u.isNeverZero; · exact (H [] (eval_zero_of_not_isNeverZero h e)).elim
  rfl

theorem eval_ones_of_not_isAlwaysZero (h : VLevel.ofLevel Us u = some u')
    (H : u.isAlwaysZero = false) : u'.eval (List.replicate Us.length 1) ≠ 0 := by
  induction u generalizing u' with
    simp [Level.isAlwaysZero, VLevel.ofLevel] at H h
  | succ => obtain ⟨_, -, rfl⟩ := h; simp [VLevel.eval]
  | param => obtain ⟨hi, rfl⟩ := h; simp [VLevel.eval, hi]
  | max a b ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp only [VLevel.eval, Nat.max_def]
    by_cases ea : a.isAlwaysZero = true
    · have := ih2 h2 (H ea); split <;> omega
    · have := ih1 h1 (by simpa using ea); split <;> omega
  | imax _ _ _ ih2 =>
    obtain ⟨_, _, _, h2, rfl⟩ := h
    have := ih2 h2 H
    simp only [VLevel.eval, Lean.Nat.imax, Nat.max_def]; split <;> [omega; split <;> omega]

theorem ofLevel_isAlwaysZero_iff (h : VLevel.ofLevel Us u = some u') :
    u.isAlwaysZero ↔ u' ≈ .zero := by
  refine ⟨ofLevel_isAlwaysZero h, fun H => ?_⟩
  cases e : u.isAlwaysZero; · exact (eval_ones_of_not_isAlwaysZero h e (VLevel.equiv_def.1 H _)).elim
  rfl

theorem VEnv.HasType.lams_ctx {env : VEnv} (henv : env.Ordered) :
    ∀ {Γ As e T}, OnCtx Γ (env.IsType U) → env.HasType U Γ (.lams As e) T →
      OnCtx (As.reverse ++ Γ) (env.IsType U)
  | _, [], _, _, hΓ, _ => hΓ
  | Γ, A :: As, _, _, hΓ, h => by
    obtain ⟨hA, _, hb⟩ := h.lam_inv henv hΓ
    simpa using VEnv.HasType.lams_ctx henv (Γ := A :: Γ) ⟨hΓ, hA⟩ hb

/-- `n` returns the `i`th of its `k` arguments wherever it is applied well typed. -/
def VEnv.Erases (env : VEnv) (n : Name) (k i : Nat) : Prop :=
  ∀ U Γ ls args, OnCtx Γ (env.IsType U) → args.length = k →
    VExpr.WF env U Γ (.appN (.const n ls) args) →
    env.IsDefEqU U Γ (.appN (.const n ls) args) (args.getD i default)

/-- `n` is, up to definitional equality, the function of its `k` arguments returning the first:
what `AddInductive.checkTypeAnnotation` checks of a type annotation's definition. -/
def VEnv.ReturnsFirst (env : VEnv) (n : Name) (k : Nat) : Prop :=
  ∀ ci, env.constants n = some ci → ∃ As T, As.length = k ∧
    env.IsDefEq ci.uvars [] (.const n (VLevel.params ci.uvars)) (.lams As (.bvar (k - 1))) T

theorem VEnv.ReturnsFirst.erases {env : VEnv} (henv : env.WF) (hk : 0 < k)
    (H : env.ReturnsFirst n k) :
    env.Erases n k 0 := by
  intro U Γ ls args hΓ hlen hwf
  have ⟨_, hc⟩ := VExpr.WF.appN_inv henv.ordered hΓ hwf
  obtain ⟨ci, hci, hls, hlen'⟩ := VEnv.HasType.const_inv henv.ordered hΓ hc
  obtain ⟨As, T, hAs, hdf⟩ := H ci hci
  have hrule := (hdf.instL hls).weak0 henv.ordered (Γ := Γ)
  simp only [VExpr.instL, VLevel.inst_map_id hlen', VExpr.instL_lams] at hrule
  have h1 := VEnv.IsDefEqU.appN henv hΓ ⟨_, hrule⟩ hwf
  have hwf2 : VExpr.WF env U Γ ((VExpr.lams (As.map (·.instL ls)) (.bvar (k - 1))).appN args) :=
    let ⟨_, h⟩ := h1; ⟨_, h.hasType.2⟩
  have hctx := (VEnv.HasType.lams_ctx henv.ordered trivial hdf.hasType.2).instL hls
  obtain ⟨-, h2, -⟩ := VExpr.lams_appN henv hΓ (As := As.map (·.instL ls)) (Γ := [])
    (by simpa [List.map_reverse] using hctx) (σ := .id) .nil (vs := args) (by simp [hlen, hAs])
    (by simpa using hwf2)
  have h3 := h1.trans henv hΓ (by simpa using h2)
  obtain _ | ⟨a, rest⟩ := args
  · subst hlen; cases hk
  · subst hlen
    have : VExpr.Subst.consN .id (a :: rest) rest.length = a := by
      simpa [VExpr.Subst.cons] using VExpr.Subst.consN_add rest (VExpr.Subst.id.cons a) 0
    simpa [VExpr.subst, this] using h3

/-- What the kernel checked of the type annotations it stripped from `e`'s head: each returns the
type it annotates. -/
def VEnv.StripOK (env : VEnv) : Expr → Prop
  | .app (.app (.const ``optParam _) A) _ => env.Erases ``optParam 2 0 ∧ env.StripOK A
  | .app (.app (.const ``autoParam _) A) _ => env.Erases ``autoParam 2 0 ∧ env.StripOK A
  | .app (.const ``outParam _) A => env.Erases ``outParam 1 0 ∧ env.StripOK A
  | .app (.const ``semiOutParam _) A => env.Erases ``semiOutParam 1 0 ∧ env.StripOK A
  | _ => True

/-- A local context of `d` lambda-bound variables without free variables, as a closed term's
binders translate to. -/
def VLCtx.Lams (Δ : VLCtx) : Prop := ∀ p ∈ Δ, p.1 = none ∧ ∃ A, p.2 = .vlam A

theorem VLCtx.Lams.find?_bvar : ∀ {Δ : VLCtx}, Δ.Lams → ∀ i, i < Δ.length →
    ∃ A, Δ.find? (.inl i) = some (.bvar i, A)
  | [], _, _, h => nomatch h
  | (o, d) :: Δ, H, i, hi => by
    obtain ⟨rfl, A, rfl⟩ := H _ (.head _)
    cases i with
    | zero => exact ⟨_, rfl⟩
    | succ i =>
      obtain ⟨B, hB⟩ := find?_bvar (fun p hp => H p (.tail _ hp)) i (by simpa using hi)
      refine ⟨B.liftN 1, ?_⟩
      simp [VLCtx.find?, VLCtx.next, hB, VLocalDecl.depth, VExpr.liftN]

/-- A closed term the kernel checked returns its first argument translates to a function that
does. -/
theorem TrExprS.returnsFirstArg {env : VEnv} {Us : List Name} :
    ∀ {k d : Nat} {Δ : VLCtx} {v : Expr} {e : VExpr}, Δ.Lams → Δ.length = d →
    AddInductive.returnsFirstArg d k v = true → TrExprS env Us Δ v e →
    ∃ As, As.length = k ∧ e = .lams As (.bvar (d + k - 1))
  | k + 1, d, Δ, .lam _ ty b _, e, hΔ, hd, hv, H => by
    let .lam (ty' := ty') (body' := b') _ _ hb := H
    obtain ⟨As, hAs, rfl⟩ := TrExprS.returnsFirstArg (k := k) (d := d + 1)
      (fun p hp => by
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨rfl, _, rfl⟩
        · exact hΔ p hp) (by simp [hd]) (by simpa [AddInductive.returnsFirstArg] using hv) hb
    exact ⟨ty' :: As, by simp [hAs], by simp [VExpr.lams]⟩
  | 0, d, Δ, .bvar i, e, hΔ, hd, hv, H => by
    simp [AddInductive.returnsFirstArg] at hv
    let .bvar h := H
    obtain ⟨A, hA⟩ := hΔ.find?_bvar i (by omega)
    rw [hA] at h; cases h
    exact ⟨[], rfl, by simp [VExpr.lams]; omega⟩
  | 0, _, _, .lam .., _, _, _, hv, _ | k + 1, _, _, .bvar _, _, _, _, hv, _ => by
    simp [AddInductive.returnsFirstArg] at hv
  | _, _, _, .fvar _, _, _, _, hv, _ | _, _, _, .mvar _, _, _, _, hv, _
  | _, _, _, .sort _, _, _, _, hv, _ | _, _, _, .const .., _, _, _, hv, _
  | _, _, _, .app .., _, _, _, hv, _ | _, _, _, .forallE .., _, _, _, hv, _
  | _, _, _, .letE .., _, _, _, hv, _ | _, _, _, .lit _, _, _, _, hv, _
  | _, _, _, .mdata .., _, _, _, hv, _ | _, _, _, .proj .., _, _, _, hv, _ => by
    simp [AddInductive.returnsFirstArg] at hv

theorem AddInductive.checkTypeAnnotation.WF {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) :
    (checkTypeAnnotation env n k).WF fun _ => venv.ReturnsFirst n k := by
  unfold checkTypeAnnotation
  split <;> [skip; exact .throw]
  rename_i hv
  split <;> [skip; exact .throw]
  rename_i hr
  refine .pure fun ci hci => ?_
  have hC : env.constants.find? n = _ := (H.map_wf.find?'_eq_find? _).symm.trans hv
  obtain ⟨hname, hTr⟩ := H.find?_uniq hv hci
  have := TrEnv'.of_value H hC DefinitionSafety.le_safe rfl
  obtain ⟨e₂, he₂, hdf⟩ := this
  obtain ⟨As, hAs, rfl⟩ := TrExprS.returnsFirstArg (Δ := []) (fun _ h => nomatch h) rfl hr he₂
  obtain ⟨T, hdf⟩ := hdf
  refine ⟨As, T, hAs, ?_⟩
  rw [← hTr.2.1, ← hname]
  simpa [VLCtx.toCtx] using hdf.symm

/-- Stripping succeeds only with each annotation it strips checked, and then strips as
`consumeTypeAnnotations'` does. -/
theorem AddInductive.stripAnnotations.WF {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) (henv : venv.WF) {e : Expr} :
    (stripAnnotations env e).WF fun e' => e' = e.consumeTypeAnnotations' ∧ venv.StripOK e := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    simp only [stripAnnotations]
    refine (checkTypeAnnotation.WF H).bind fun _ h => ih.mono fun e' ⟨h1, h2⟩ => ?_
    exact ⟨by simp [h1, Lean.Expr.consumeTypeAnnotations'], h.erases henv (by decide), h2⟩
  | case5 e h1 h2 h3 h4 =>
    rw [stripAnnotations.eq_5 env e h1 h2 h3 h4]
    refine .pure ⟨(Lean.Expr.consumeTypeAnnotations'.eq_5 e h1 h2 h3 h4).symm, ?_⟩
    rw [VEnv.StripOK.eq_5 venv e h1 h2 h3 h4]; trivial

/-- The annotations `consumeTypeAnnotations'` strips from the head of `e` are named by `P`. -/
def _root_.Lean.Expr.StripHeads (P : Name → Prop) : Expr → Prop
  | .app (.app (.const ``optParam _) A) _ => P ``optParam ∧ A.StripHeads P
  | .app (.app (.const ``autoParam _) A) _ => P ``autoParam ∧ A.StripHeads P
  | .app (.const ``outParam _) A => P ``outParam ∧ A.StripHeads P
  | .app (.const ``semiOutParam _) A => P ``semiOutParam ∧ A.StripHeads P
  | _ => True

theorem _root_.Lean.Expr.StripHeads.true (e : Expr) : e.StripHeads fun _ => True := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    simp only [Lean.Expr.StripHeads]; exact ⟨trivial, ih⟩
  | case5 e h1 h2 h3 h4 => rw [Lean.Expr.StripHeads.eq_5 _ e h1 h2 h3 h4]; trivial

theorem _root_.Lean.Expr.StripHeads.mono {P Q : Name → Prop} (h : ∀ n, P n → Q n) {e : Expr}
    (H : e.StripHeads P) : e.StripHeads Q := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    simp only [Lean.Expr.StripHeads] at H ⊢; exact ⟨h _ H.1, ih H.2⟩
  | case5 e h1 h2 h3 h4 => rw [Lean.Expr.StripHeads.eq_5 _ e h1 h2 h3 h4]; trivial

theorem _root_.Lean.Expr.StripHeads.and {P Q : Name → Prop} {e : Expr}
    (H1 : e.StripHeads P) (H2 : e.StripHeads Q) : e.StripHeads fun n => P n ∧ Q n := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    simp only [Lean.Expr.StripHeads] at H1 H2 ⊢; exact ⟨⟨H1.1, H2.1⟩, ih H1.2 H2.2⟩
  | case5 e h1 h2 h3 h4 => rw [Lean.Expr.StripHeads.eq_5 _ e h1 h2 h3 h4]; trivial

/-- Stripping succeeds only where the environment defines each annotation it strips. -/
theorem AddInductive.stripAnnotations_heads {env : Environment} :
    ∀ {e r : Expr}, stripAnnotations env e = .ok r →
      e.StripHeads fun n => ∃ v, env.find? n = some (.defnInfo v) := by
  have hc {n k} (h : checkTypeAnnotation env n k = .ok ()) :
      ∃ v, env.find? n = some (.defnInfo v) := by
    unfold checkTypeAnnotation at h
    split at h <;> [skip; cases h]
    rename_i v _ hv
    exact ⟨_, hv⟩
  intro e
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    intro r h
    simp only [stripAnnotations, bind, Except.bind] at h
    split at h <;> [cases h; skip]
    rename_i u hu
    simp only [Lean.Expr.StripHeads]
    exact ⟨hc hu, ih h⟩
  | case5 e h1 h2 h3 h4 => intros; rw [Lean.Expr.StripHeads.eq_5 _ e h1 h2 h3 h4]; trivial

/-- What `AddInductive.checkTypeAnnotation` checks is a defining rule of the model: the
annotation is defined as returning its first argument. -/
theorem AddInductive.checkTypeAnnotation.rule {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) :
    (checkTypeAnnotation env n k).WF fun _ => venv.ReturnsFirstRule n k := by
  unfold checkTypeAnnotation
  split <;> [skip; exact .throw]
  rename_i hv
  split <;> [skip; exact .throw]
  rename_i hr
  refine .pure ?_
  have hC : env.constants.find? n = _ := (H.map_wf.find?'_eq_find? _).symm.trans hv
  obtain ⟨df, venv₀, h1, h2, -, h4⟩ := TrEnv'.defn_rule H hC DefinitionSafety.le_safe
  obtain ⟨As, hAs, e⟩ := TrExprS.returnsFirstArg (Δ := []) (fun _ h => nomatch h) rfl hr h4
  exact ⟨df, As, h1, h2, hAs, by simpa using e⟩

/-- Stripping succeeds only with each annotation it strips defined, in the model, as returning
the type it annotates. -/
theorem AddInductive.stripAnnotations_rules {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) :
    ∀ {e r : Expr}, stripAnnotations env e = .ok r → e.StripHeads venv.AnnotDef := by
  have hc {n k} (h : checkTypeAnnotation env n k = .ok ()) : venv.ReturnsFirstRule n k :=
    checkTypeAnnotation.rule H _ h
  intro e
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    intro r h
    simp only [stripAnnotations, bind, Except.bind] at h
    split at h <;> [cases h; skip]
    rename_i u hu
    simp only [Lean.Expr.StripHeads]
    exact ⟨by simpa [VEnv.AnnotDef] using hc hu, ih h⟩
  | case5 e h1 h2 h3 h4 => intros; rw [Lean.Expr.StripHeads.eq_5 _ e h1 h2 h3 h4]; trivial

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Adding constants one by one, each after `checkName`: the names are fresh and distinct, and
primitive only where allowed. -/
theorem addChecked.WF {env : Environment} (mapWF : env.constants.WF) (allow : Bool)
    (f : α → ConstantInfo) :
    ∀ (xs : List α), (xs.foldlM (m := Except Exception) (init := env) fun (env : Environment) x => do
        env.checkName (f x).name allow; return env.add (f x)).WF fun env' =>
      env'.constants = insertConsts env.constants (xs.map f) ∧ env'.quotInit = env.quotInit ∧
      ((xs.map f).map (·.name)).Nodup ∧ (∀ ci ∈ xs.map f, env.constants.find? ci.name = none) ∧
      (∀ ci ∈ xs.map f, Environment.primitives.contains ci.name → allow)
  | [] => .pure ⟨rfl, rfl, .nil, nofun, nofun⟩
  | x :: xs => by
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (checkName.WF mapWF (f x).name allow).bind fun _ ⟨hn, hp⟩ => ?_
    have hn' : env.constants.find? (f x).name = none := by
      rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at hn
    have mapWF' := mapWF.insert (f x).name (f x) hn'
    refine (addChecked.WF (env := env.add (f x)) mapWF' allow f xs).mono
      fun env' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hm => ?_, h3⟩
      obtain ⟨ci, hci, he⟩ := List.mem_map.1 hm
      have := h4 ci hci
      change (env.constants.insert (f x).name (f x)).find? ci.name = none at this
      rw [mapWF.find?_insert, if_pos (by simp [he])] at this; cases this
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨hn', fun ci hci => ?_⟩
      have := h4 ci hci
      change (env.constants.insert (f x).name (f x)).find? ci.name = none at this
      rw [mapWF.find?_insert] at this; split at this; · cases this
      exact this
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]; exact ⟨hp, h5⟩

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
/-- Stripping type annotations the kernel checked does not change a translation, up to defeq. -/
theorem TrExprS.consumeTypeAnnotations' {e e'} (hok : env.StripOK e) (H : TrExprS env Us Δ e e')
    {P : Name → Prop} (hP : e.StripHeads P) :
    ∃ e'', TrExprS env Us Δ e.consumeTypeAnnotations' e'' ∧
      env.IsDefEqU Us.length Δ.toCtx e' e'' ∧ e'.StripsToBy P e'' := by
  have hΓ := hΔ.toCtx
  induction e using Lean.Expr.consumeTypeAnnotations'.induct generalizing e' with
  | case1 _ A _ ih | case2 _ A _ ih =>
    cases H with | app h1 h2 hf _ => cases hf with | app _ _ hc hA => cases hc with | const =>
    have := hok.1 _ _ _ [_, _] hΓ rfl ⟨_, h1.app h2⟩
    simp only [Lean.Expr.StripHeads] at hP
    obtain ⟨A'', h3, h4, h5⟩ := ih hok.2 hA hP.2
    refine ⟨A'', by simpa [Lean.Expr.consumeTypeAnnotations'] using h3,
      this.trans henv hΓ (by simpa using h4), .app2 (by simp) hP.1 h5⟩
  | case3 _ A ih | case4 _ A ih =>
    cases H with | app h1 h2 hc hA => cases hc with | const =>
    have := hok.1 _ _ _ [_] hΓ rfl ⟨_, h1.app h2⟩
    simp only [Lean.Expr.StripHeads] at hP
    obtain ⟨A'', h3, h4, h5⟩ := ih hok.2 hA hP.2
    refine ⟨A'', by simpa [Lean.Expr.consumeTypeAnnotations'] using h3,
      this.trans henv hΓ (by simpa using h4), .app1 (by simp) hP.1 h5⟩
  | case5 e h1 h2 h3 h4 =>
    refine ⟨e', ?_, H.wf henv.ordered hΔ, .refl⟩
    unfold Lean.Expr.consumeTypeAnnotations'
    split <;> first | exact H | (exfalso; simp_all)

namespace AddInductive

structure VContext extends Context where
  venv : VEnv
  envAt : VEnvAt env safety venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx
  reserved : ∀ fv ∈ mlctx.vlctx.fvars, ngen.Reserves fv
  notKernel : ∀ fv ∈ mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv
  pfx : ngen.namePrefix ≠ `_kernel_fresh

/-- The type checker's view of the context. -/
def VContext.tc (c : VContext) : TypeChecker.VContext where
  env := c.env
  safety := c.safety
  lparams := c.lparams
  fuel := c.fuel
  lctx := c.lctx
  venv := c.venv
  hasPrimitives := c.envAt.hasPrimitives
  safePrimitives := c.envAt.safePrimitives
  trenv := c.envAt.tr
  mlctx := c.mlctx
  mlctx_wf := c.mlctx_wf
  lctx_eq := c.lctx_eq

def WF (c : VContext) (x : M α) (Q : α → Prop) : Prop := ∀ a, x c.toContext = .ok a → Q a

theorem WF.bind {c : VContext} {x : M α} {f : α → M β} {Q R}
    (h1 : WF c x Q) (h2 : ∀ a, Q a → WF c (f a) R) : WF c (x >>= f) R := by
  intro b
  simp only [WF, (· >>= ·), ReaderT.bind, Except.bind] at *
  split; · simp
  exact h2 _ (h1 _ ‹_›) _

theorem WF.pure {c : VContext} {Q} (H : Q a) : WF c (pure a : M α) Q := by
  rintro _ ⟨⟩; exact H

theorem WF.mono {c : VContext} {x : M α} {Q R} (h1 : WF c x Q) (h2 : ∀ a, Q a → R a) :
    WF c x R := fun _ e => h2 _ (h1 _ e)

theorem WF.throw {c : VContext} {Q} : WF c (throw e : M α) Q := nofun

theorem WF.liftExcept {c : VContext} {x : Except Exception α} {Q} (h : x.WF Q) :
    WF c (liftM x : M α) Q := fun _ e => h _ e

theorem VState.WF.emptyM (c : VContext) : TypeChecker.VState.WF c.tc {} :=
  .emptyOf _ c.envAt.envClosed rfl

/-- Stripping a binder type's annotations, each checked to return the type it annotates. -/
theorem consumeTypeAnnotations.WF {c : VContext} {e : Expr} :
    WF c (consumeTypeAnnotations e) fun e' =>
      e' = e.consumeTypeAnnotations' ∧ c.venv.StripOK e :=
  stripAnnotations.WF c.envAt.tr c.envAt.tr.wf

/-- A type checker call, run over the kernel's local context. -/
theorem WF.liftTC {c : VContext} {x : TypeChecker.M α} {Q}
    (H : x.WF c.tc {} fun a _ => Q a) : WF c (monadLift x : M α) Q := by
  intro a eq
  change TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x = .ok a at eq
  simp only [TypeChecker.M.run, StateT.run', Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  obtain ⟨_, _, _, _, h⟩ := H (VState.WF.emptyM c) _ _ eq
  exact h

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.mono {env env' : VEnv} (henv : env ≤ env') :
    ∀ {m : MLCtx}, m.WF env Us → m.WF env' Us
  | .nil, h => h
  | .vlam .., ⟨h1, h2, h3, h4⟩ => ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv⟩
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv, h5.mono henv⟩

/-- The context with the environment replaced by one modelled by `venv'` at the same level, into
which the local context carries over. -/
def VContext.withEnv (c : VContext) (env' : Environment) (venv' : VEnv)
    (wf : VEnvAt env' c.safety venv') (hle : c.venv ≤ venv') : VContext :=
  { c with
    env := env'
    venv := venv'
    envAt := wf
    mlctx_wf := c.mlctx_wf.mono hle }

/-- A computation under `withEnv` that does not use the type checker, verified directly. -/
theorem WF.withEnvRaw {c : VContext} {x : M α} {Q} {env'}
    (H : (x { c.toContext with env := env' }).WF Q) : WF c (AddInductive.withEnv env' x) Q := H

theorem WF.withEnv {c : VContext} {x : M α} {Q} {env' venv'} (wf hle)
    (H : WF (c.withEnv env' venv' wf hle) x Q) : WF c (AddInductive.withEnv env' x) Q := H

/-- The context `withLocalDecl` opens: a fresh variable of type `ty`, modelled by `ty'`. -/
def VContext.push (c : VContext) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (hty : TrExprS c.venv c.lparams c.mlctx.vlctx ty ty')
    (hty' : c.venv.IsType c.lparams.length c.mlctx.vlctx.toCtx ty') : VContext :=
  { c with
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    ngen := c.ngen.next
    mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi c.mlctx
    mlctx_wf := ⟨c.mlctx_wf,
      c.mlctx_wf.tr.find?_eq_none.2 fun h => c.ngen.not_reserves_self (c.reserved _ h), hty, hty'⟩
    lctx_eq := by simp [MLCtx.lctx, c.lctx_eq]
    reserved := by
      simp only [MLCtx.vlctx]; simp
      exact ⟨c.ngen.next_reserves_self, fun _ h => (c.reserved _ h).mono .next⟩
    notKernel := by
      simp only [MLCtx.vlctx]; simp
      refine ⟨fun i h => ?_, c.notKernel⟩
      injection h with h; injection h with h; exact absurd h c.pfx }

theorem WF.withLocalDecl {c : VContext} {f : Expr → M α} {Q name ty ty' bi} (hty hty')
    (H : WF (c.push name ty ty' bi hty hty') (f (.fvar ⟨c.ngen.curr⟩)) Q) :
    WF c (Lean4Lean.withLocalDecl name bi ty f) Q := H

end AddInductive
end Lean4Lean

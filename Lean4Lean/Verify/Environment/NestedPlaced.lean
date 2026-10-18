import Lean4Lean.Verify.Environment.NestedAuxWF

/-!
# Where restoring a nested block replaces

The kernel's restoration replaces an auxiliary constant applied to the parameters by the
occurrence it stands for, a constant applied to terms over the parameters, and replaces nothing
else (`PlacedFn`). The occurrences are typed over the parameters, from the final phase's check of
them.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace ElimNestedInductive

theorem constSpine?_eq_spineNM : ∀ (t : Expr),
    Result.constSpine? t = (spineNM t).map fun x => (x.1, x.2.1, x.2.2.toArray)
  | .const .. => rfl
  | .app f a => by
    simp only [Result.constSpine?, spineNM, constSpine?_eq_spineNM f, Option.map_map]
    congr 1; funext x; simp
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

theorem looseBVarRange'_mkAppList {m : Nat} : ∀ {f : Expr} {xs : List Expr},
    f.looseBVarRange' ≤ m → (∀ x ∈ xs, x.looseBVarRange' ≤ m) →
    (Expr.mkAppList f xs).looseBVarRange' ≤ m
  | _, [], hf, _ => hf
  | f, x :: xs, hf, hx => by
    simp only [Expr.mkAppList]
    exact looseBVarRange'_mkAppList (by
      simp only [Expr.looseBVarRange', Nat.max_le]; exact ⟨hf, hx x (.head _)⟩)
      fun y hy => hx y (.tail _ hy)

theorem liftLooseBVars'_mkAppList {s k : Nat} : ∀ {f : Expr} {xs : List Expr},
    (Expr.mkAppList f xs).liftLooseBVars' s k =
      Expr.mkAppList (f.liftLooseBVars' s k) (xs.map (·.liftLooseBVars' s k))
  | _, [] => rfl
  | f, x :: xs => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [liftLooseBVars'_mkAppList (f := .app f x)]; rfl

theorem not_binder_mkAppList_const {c : Name} {ls : List Level} {xs : List Expr} :
    (∀ nm d b bi, Expr.mkAppList (.const c ls) xs ≠ .forallE nm d b bi) ∧
    (∀ i, Expr.mkAppList (.const c ls) xs ≠ .bvar i) ∧
    (∀ x, Expr.mkAppList (.const c ls) xs ≠ .fvar x) := by
  have h := Expr.getAppFn_mkAppList_const (c := c) (ls := ls) (xs := xs)
  refine ⟨fun nm d b bi e => ?_, fun i e => ?_, fun x e => ?_⟩ <;> rw [e] at h <;> cases h

/-- A constructor type the elimination translated, `setBody` of the input's at a body whose
auxiliary constants sit at the parameters, has them placed after its parameters, given the input
names none. -/
theorem placedAfter_setBody {isAux : Name → Bool} {lvls : List Level} {m : Nat} {B : Expr}
    (hB : AuxPlaced isAux lvls m 0 B) :
    ∀ {n e}, (peel n e).isSome → e.anySub (constP isAux) = false →
      PlacedAfter isAux lvls m n (setBody n e B)
  | 0, _, _, _ => hB
  | n + 1, .forallE .., h, he => by
    simp only [Expr.anySub, constP, Bool.or_eq_false_iff] at he
    exact ⟨he.1.2, placedAfter_setBody hB (n := n) h he.2⟩
  | _ + 1, .bvar .., h, _ | _ + 1, .fvar .., h, _ | _ + 1, .mvar .., h, _
  | _ + 1, .sort .., h, _ | _ + 1, .const .., h, _ | _ + 1, .app .., h, _
  | _ + 1, .lam .., h, _ | _ + 1, .letE .., h, _ | _ + 1, .lit .., h, _
  | _ + 1, .mdata .., h, _ | _ + 1, .proj .., h, _ => by simp [peel] at h

end ElimNestedInductive

theorem abstract'_ground {xs : List FVarId} {k : Nat} : ∀ {e : Expr}, e.Ground →
    e.abstract' xs k = e
  | .app f a, ⟨hf, ha⟩ => by simp [Expr.abstract', abstract'_ground hf, abstract'_ground ha]
  | .mdata _ e, he => by simp [Expr.abstract', abstract'_ground (e := e) he]
  | .proj _ _ e, he => by simp [Expr.abstract', abstract'_ground (e := e) he]
  | .const .., _ | .sort _, _ | .lit _, _ => by simp [Expr.abstract']

/-- A translated term names only constants of its environment. -/
theorem TrExprS.anySub_constP {env : VEnv} {Us : List Name} {f : Name → Bool}
    (hf : ∀ c, f c = true → env.constants c = none) {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : e.anySub (constP f) = false := by
  induction H with
  | bvar | fvar | sort | lit => rfl
  | @const c _ _ _ _ h1 =>
    cases hc : f c
    · simp [Expr.anySub, constP, hc]
    · rw [hf c hc] at h1; cases h1
  | app _ _ _ _ ih1 ih2 => simp [Expr.anySub, constP, ih1, ih2]
  | lam _ _ _ ih1 ih2 => simp [Expr.anySub, constP, ih1, ih2]
  | forallE _ _ _ _ ih1 ih2 => simp [Expr.anySub, constP, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => simp [Expr.anySub, constP, ih1, ih2, ih3]
  | mdata _ ih => simp [Expr.anySub, constP, ih]
  | proj _ _ ih => simp [Expr.anySub, constP, ih]

/-- A plain translation's loose bound variables are below its context's. -/
theorem PTr.looseBVarRange_le {Us : List Name} {CL : Literal → Prop} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, PTr Us CL Δ e e' → ∀ {m : Nat},
      (∀ i p, Δ.find? (.inl i) = some p → i < m) → e.looseBVarRange' ≤ m := by
  have hcons {Δ : VLCtx} {d : VLocalDecl} {m : Nat}
      (h : ∀ i p, Δ.find? (.inl i) = some p → i < m) :
      ∀ i p, VLCtx.find? ((none, d) :: Δ) (.inl i) = some p → i < m + 1 := by
    intro i p hp
    cases i with
    | zero => omega
    | succ i =>
      simp only [VLCtx.find?, VLCtx.next] at hp
      obtain ⟨q, hq, -⟩ := Option.bind_eq_some_iff.1 hp
      have := h i q hq; omega
  intro Δ e e' H
  induction H with
  | bvar h => intro m hm; exact hm _ _ h
  | fvar | sort | const => intros; simp [Expr.looseBVarRange']
  | lit => intros; simp [Expr.looseBVarRange']
  | app _ _ ih1 ih2 =>
    intro m hm; simp only [Expr.looseBVarRange', Nat.max_le]; exact ⟨ih1 hm, ih2 hm⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    intro m hm
    have := ih2 (hcons hm)
    simp only [Expr.looseBVarRange', Nat.max_le]; exact ⟨ih1 hm, by omega⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    intro m hm
    have := ih3 (hcons hm)
    simp only [Expr.looseBVarRange', Nat.max_le]; exact ⟨⟨ih1 hm, ih2 hm⟩, by omega⟩
  | mdata _ ih | proj _ ih => intro m hm; exact ih hm

theorem VLCtx.toCtx_append' : ∀ (Δ Δ' : VLCtx), (Δ ++ Δ').toCtx = Δ.toCtx ++ Δ'.toCtx
  | [], _ => rfl
  | (_, .vlam _) :: Δ, Δ' => congrArg _ (VLCtx.toCtx_append' Δ Δ')
  | (_, .vlet ..) :: Δ, Δ' => VLCtx.toCtx_append' Δ Δ'

/-- Abstracting the free variables of a context `Δ` of them, below binders `Γ`: the term translates
over parameters of the same types in their place as it did over `Δ`. -/
theorem TrExprS.abstract'_params {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {xs : List FVarId} {As : List VExpr} (hAs : As = Δ.toCtx)
    (hΔb : ∀ j, Δ.find? (.inl j) = none)
    (hΔf : ∀ fv e A, Δ.find? (.inr fv) = some (e, A) →
      ∃ j, j < As.length ∧ xs.reverse.idxOf? fv = some j ∧ e = .bvar j) :
    ∀ {Γ : VLCtx} {e : Expr} {e' : VExpr}, (∀ x ∈ Γ, x.1 = none) → TrExprS env Us (Γ ++ Δ) e e' →
      TrExprS env Us (Γ ++ paramCtx As) (e.abstract' xs Γ.length) e' := by
  have hctx (Γ : VLCtx) : (Γ ++ paramCtx As).toCtx = (Γ ++ Δ).toCtx := by
    rw [VLCtx.toCtx_append', VLCtx.toCtx_append', paramCtx_toCtx, hAs]
  have hcons {Γ : VLCtx} {d : VLocalDecl} (hΓ : ∀ x ∈ Γ, x.1 = none) :
      ∀ x ∈ ((none, d) :: Γ : VLCtx), x.1 = none := by
    rintro x (_ | ⟨_, hx⟩); · rfl
    · exact hΓ x hx
  intro Γ e e' hΓ H
  generalize hc : Γ ++ Δ = Δ₀ at H
  induction H generalizing Γ with
  | @bvar _ _ _ i h =>
    subst hc
    obtain ⟨g, k, HΓ⟩ := VLCtx.find?_append_binders Γ hΓ
    simp only [Expr.abstract']
    by_cases hi : i < Γ.length
    · rw [(HΓ Δ).2.2 i hi (paramCtx As)] at h; exact .bvar h
    · obtain ⟨j, rfl⟩ : ∃ j, i = Γ.length + j := ⟨i - Γ.length, by omega⟩
      rw [(HΓ Δ).1 j, hΔb j] at h; cases h
  | @fvar _ _ _ fv h =>
    subst hc
    obtain ⟨g, k, HΓ⟩ := VLCtx.find?_append_binders Γ hΓ
    rw [(HΓ Δ).2.1 fv] at h
    obtain ⟨⟨e₀, A₀⟩, h₀, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    obtain ⟨j, hj, hidx, rfl⟩ := hΔf fv e₀ A₀ h₀
    simp only [Expr.abstract', hidx]
    obtain ⟨B, hB⟩ := paramCtx_find?_bvar hj
    exact .bvar (by rw [(HΓ (paramCtx As)).1 j, hB]; rfl)
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    subst hc
    exact .app (hctx Γ ▸ h1) (hctx Γ ▸ h2) (ih1 hΓ rfl) (ih2 hΓ rfl)
  | lam h1 _ _ ih1 ih2 =>
    subst hc
    exact .lam (hctx Γ ▸ h1) (ih1 hΓ rfl) (ih2 (Γ := (none, _) :: Γ) (hcons hΓ) rfl)
  | forallE h1 h2 _ _ ih1 ih2 =>
    subst hc
    have h2' := hctx Γ ▸ h2
    exact .forallE (hctx Γ ▸ h1) h2' (ih1 hΓ rfl) (ih2 (Γ := (none, _) :: Γ) (hcons hΓ) rfl)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    subst hc
    exact .letE (hctx Γ ▸ h1) (ih1 hΓ rfl) (ih2 hΓ rfl) (ih3 (Γ := (none, _) :: Γ) (hcons hΓ) rfl)
  | lit h _ ih =>
    subst hc
    have := ih hΓ rfl
    rw [abstract'_ground Literal.toConstructor_ground] at this
    exact .lit h this
  | mdata _ ih => exact .mdata (ih hΓ hc)
  | proj _ h2 ih =>
    subst hc
    exact .proj (ih hΓ rfl) (hctx Γ ▸ h2)

/-- Telescopes that agree entry by entry give parameter contexts that do. -/
theorem paramVLCtx_isDefEq [VEnv.Injective] {E : VEnv} {U : Nat} (henv : E.WF) :
    ∀ {Γ As Bs}, E.TeleDefEq U Γ As Bs → E.IsTele U Γ Bs → OnCtx Γ (E.IsType U) →
      ∀ {Δ₁ Δ₂ : VLCtx}, Δ₁.toCtx = Γ → VLCtx.IsDefEq E U Δ₁ Δ₂ →
      VLCtx.IsDefEq E U (paramVLCtx Bs ++ Δ₁) (paramVLCtx As ++ Δ₂)
  | _, [], [], .nil, _, _, _, _, _, h => h
  | Γ, A :: As, B :: Bs, .cons hAB t, .cons ⟨u, hB⟩ tB, hΓ, Δ₁, Δ₂, hc, h => by
    have h1 : E.IsDefEq U Γ B A (.sort u) := (hAB.of_r henv hΓ hB).symm
    have h2 : VLCtx.IsDefEq E U ((none, .vlam B) :: Δ₁) ((none, .vlam A) :: Δ₂) :=
      .cons h (by nofun) (.vlam (hc ▸ h1))
    have := paramVLCtx_isDefEq henv t tB ⟨hΓ, _, hB⟩ (Δ₁ := (none, .vlam B) :: Δ₁)
      (by simp [VLCtx.toCtx, hc]) h2
    simpa [paramVLCtx] using this

section
open ElimNestedInductive
variable {r : ElimNestedInductive.Result} {env' : Environment} {lparams : List Name}
  {auxRec : NameMap Name} {Us : List Name} {CL : Literal → Prop}
  {R : Name → Option VAuxHead} {ren : Name → Option Name}

theorem getNestedIfAuxCtor_some {c : Name} {K : Expr} {auxI : Name}
    (h : r.getNestedIfAuxCtor env' c = some (K, auxI)) : r.aux2nested.find? auxI = some K := by
  unfold ElimNestedInductive.Result.getNestedIfAuxCtor at h
  cases hc : env'.find? c with
  | none => simp [hc] at h
  | some ci =>
    cases ci <;> simp [hc] at h
    rename_i v
    cases e : r.aux2nested.find? v.induct with
    | none => simp [e] at h
    | some K' => simp [e] at h; obtain ⟨rfl, rfl⟩ := h; exact e

theorem tm_contains_of_get?_none {m : TM} {c : Name} (h : m.get? c = none) :
    m.contains c = false := by
  rw [Std.TreeMap.contains_eq_isSome_getElem?, ← Std.TreeMap.get?_eq_getElem?, h]; rfl

theorem aux2nested_find?_none {c : Name} (h : r.aux2nested.find? c = none) :
    r.aux2nested.contains c = false :=
  tm_contains_of_get?_none (m := r.aux2nested) h

theorem restoreFn_eq_auxFn {t : Expr}
    (h : ∀ c ls, t = .const c ls → auxRec.find? c = none) :
    Result.restoreFn r env' lparams auxRec t = Result.auxFn r env' lparams t := by
  unfold Result.restoreFn
  split
  · rename_i c ls; simp [h c ls rfl]
  · rfl

theorem constSpine?_mkAppList_const {c : Name} {ls : List Level} {xs : List Expr} :
    Result.constSpine? (Expr.mkAppList (.const c ls) xs) = some (c, ls, xs.toArray) := by
  rw [constSpine?_eq_spineNM, spineNM_mkAppList (acc := []) rfl]; rfl

theorem restoreFn_mkAppList_const {c : Name} {ls : List Level} {xs : List Expr}
    (hc : auxRec.find? c = none) :
    Result.restoreFn r env' lparams auxRec (Expr.mkAppList (.const c ls) xs) =
      Result.auxFn r env' lparams (Expr.mkAppList (.const c ls) xs) := by
  refine restoreFn_eq_auxFn fun c' ls' e => ?_
  have := Expr.getAppFn_mkAppList_const (c := c) (ls := ls) (xs := xs)
  rw [e] at this; cases this; exact hc

/-- At an auxiliary constant applied to as many arguments as there are parameters, the
replacement is the kernel's `kRepl`. -/
theorem RestoreSpec.restoreFn_eq_kRepl (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    {n : Nat} (hnp : r.nparams = n) {c : Name} (hc : (R c).isSome) {ls : List Level}
    {xs : List Expr} (hxs : xs.length = n) :
    Result.restoreFn r env' lparams auxRec (Expr.mkAppList (.const c ls) xs) =
      Result.kRepl r env' lparams c ls xs.toArray := by
  rw [restoreFn_mkAppList_const (S.ren_aux c hc)]
  unfold Result.auxFn
  rw [constSpine?_mkAppList_const]
  simp only [Option.bind_some, List.size_toArray, hxs, hnp, ← S.aux c, hc, and_self, if_true]

/-- The replacement of an auxiliary constant at the parameters, `k` binders below them: the
occurrence's head, or its constructor's, at the occurrence's arguments over the parameters. -/
theorem RestoreSpec.restoreFn_bvs (S : RestoreSpec r env' lparams auxRec Us CL R ren) {n : Nat}
    (hnp : r.nparams = n)
    (hK : ∀ c K, r.aux2nested.find? c = some K → ∃ J Ls Ds,
      K.abstract r.params = Expr.mkAppList (.const J Ls) Ds ∧ ∀ D ∈ Ds, D.looseBVarRange' ≤ n)
    {c : Name} (hc : (R c).isSome) :
    ∃ a K J h Ls Ds, r.aux2nested.find? a = some K ∧
      K.abstract r.params = Expr.mkAppList (.const J Ls) Ds ∧ (∀ D ∈ Ds, D.looseBVarRange' ≤ n) ∧
      ∀ k, Result.restoreFn r env' lparams auxRec
        (Expr.mkAppList (.const c (lparams.map .param)) (bvs n k)) =
        some ((Expr.mkAppList (.const h Ls) Ds).liftLooseBVars' 0 k) := by
  have hren := S.ren_aux c hc
  have haux := S.aux c
  rw [hc] at haux
  have hlvl := instantiateLevelParamsRaw_self (ps := lparams)
  cases hf : r.aux2nested.find? c with
  | some K =>
    obtain ⟨J, Ls, Ds, hD, hDs⟩ := hK c K hf
    have hN : (Expr.mkAppList (.const J Ls) Ds).looseBVarRange' ≤ n :=
      looseBVarRange'_mkAppList (by simp [Expr.looseBVarRange']) hDs
    refine ⟨c, K, J, J, Ls, Ds, hf, hD, hDs, fun k => ?_⟩
    rw [restoreFn_mkAppList_const hren]
    unfold Result.auxFn
    rw [constSpine?_mkAppList_const]
    have hcont : r.aux2nested.contains c = true := tm_contains_of_get? (m := r.aux2nested) hf
    simp only [Option.bind_some, List.size_toArray, bvs_length, hnp, hcont, Bool.true_or,
      and_self, if_true, Result.kRepl, hf, hlvl]
    rw [instantiateBVars _ _ _ (hD ▸ hN), hD]
  | none =>
    have hc0 := aux2nested_find?_none hf
    rw [hc0, Bool.false_or] at haux
    obtain ⟨⟨K, auxI⟩, hg⟩ := Option.isSome_iff_exists.1 haux.symm
    have hfK := getNestedIfAuxCtor_some hg
    obtain ⟨J, Ls, Ds, hD, hDs⟩ := hK auxI K hfK
    have hM : (Expr.mkAppList (.const J Ls) Ds).looseBVarRange' ≤ n :=
      looseBVarRange'_mkAppList (by simp [Expr.looseBVarRange']) hDs
    refine ⟨auxI, K, J, c.replacePrefix auxI J, Ls, Ds, hfK, hD, hDs, fun k => ?_⟩
    rw [restoreFn_mkAppList_const hren]
    unfold Result.auxFn
    rw [constSpine?_mkAppList_const]
    simp only [Option.bind_some, List.size_toArray, bvs_length, hnp, hc0, Bool.false_or, hg,
      Option.isSome_some, and_self, if_true, Result.kRepl, hf, hlvl]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hcl : (Expr.const J Ls).liftLooseBVars' 0 k = .const J Ls := by
      simp [Expr.liftLooseBVars']
    have hcl' : (Expr.const (c.replacePrefix auxI J) Ls).liftLooseBVars' 0 k =
        .const (c.replacePrefix auxI J) Ls := by simp [Expr.liftLooseBVars']
    rw [instantiateBVars _ _ _ (hD ▸ hM), hD, liftLooseBVars'_mkAppList, hcl,
      Expr.getAppFn_mkAppList_const, Expr.getAppArgs_mkAppList_const, liftLooseBVars'_mkAppList,
      hcl']
    show some (mkAppN _ _) = _
    rw [Expr.mkAppN_eq_mkAppList]

/-- The kernel's replacement is placed: at an auxiliary constant applied to the parameters it gives
the occurrence, over the parameters, and nowhere else does it replace anything but a recursor. -/
theorem RestoreSpec.placedFn (S : RestoreSpec r env' lparams auxRec Us CL R ren) {n : Nat}
    (hnp : r.nparams = n)
    (hK : ∀ c K, r.aux2nested.find? c = some K → ∃ J Ls Ds,
      K.abstract r.params = Expr.mkAppList (.const J Ls) Ds ∧ ∀ D ∈ Ds, D.looseBVarRange' ≤ n) :
    PlacedFn (Result.restoreFn r env' lparams auxRec) (fun c => (R c).isSome)
      (fun c => (auxRec.find? c).isSome) (lparams.map .param) n := by
  refine ⟨fun c hc => ?_, fun t c ls xs ht hn hr => ?_, fun t ht => ?_⟩
  · obtain ⟨-, -, -, h, Ls, Ds, -, -, hDs, hF⟩ := S.restoreFn_bvs hnp hK hc
    exact ⟨_, looseBVarRange'_mkAppList (by simp [Expr.looseBVarRange']) hDs,
      not_binder_mkAppList_const, hF⟩
  · have hr' : auxRec.find? c = none := by simpa using hr
    rw [spineNM_eq ht, restoreFn_mkAppList_const hr']
    unfold Result.auxFn
    rw [constSpine?_mkAppList_const]
    have haux := S.aux c
    simp only [Option.bind_some, List.size_toArray, hnp, ← haux]
    rw [if_neg (fun h => hn ⟨h.2, h.1⟩)]
  · refine restoreFn_of_spine_none (fun c ls e => ?_) ?_
    · subst e; cases ht
    · rw [constSpine?_eq_spineNM, ht]; rfl

end

/-- An occurrence restoring puts back, at the parameters, is well formed over them. -/
theorem RestoreEnv.inst_wf {E₁ E₀ : VEnv} {U : Nat} {F : Name → Option VExpr}
    {R : Name → Option VAuxHead} {ls₀ : List VLevel} {Γ₀ : List VExpr}
    (H : RestoreEnv E₁ E₀ U F R ls₀ Γ₀) {c : Name} {h : VAuxHead} (hc : R c = some h) :
    VExpr.WF E₀ U Γ₀ (h.inst ls₀ (VExpr.bvars h.n 0)) := by
  obtain ⟨Ps, -, -, hcl, hwf, W⟩ := H.hR c h hc
  rw [VAuxHead.lam, VExpr.instL_lams] at hwf
  obtain ⟨-, T, hb⟩ := hwf.lams_inv H.wf.ordered trivial
  have hb' := hb.subst H.wf.ordered (by simpa using W) H.ctx
  simp only [VExpr.subst_id] at hb'
  have heq : h.inst ls₀ (VExpr.bvars h.n 0) =
      VExpr.instL ls₀ ((VExpr.const h.name h.lvls).appN h.args) := by
    rw [VAuxHead.inst, VExpr.instL_appN]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    rw [((hcl a ha).instL (ls := ls₀)).subst_congr (σ' := .id) fun i hi => by
      simp [VExpr.Subst.consList_bvars, hi]; rfl]
    simp
  rw [heq]; exact ⟨_, hb'⟩

theorem letsOK_mkAppList {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {f : Expr} {xs : List Expr}, LetsOK env Us Δ f → (∀ x ∈ xs, LetsOK env Us Δ x) →
      LetsOK env Us Δ (Expr.mkAppList f xs)
  | _, [], hf, _ => hf
  | f, x :: xs, hf, hx => by
    simp only [Expr.mkAppList]
    exact letsOK_mkAppList (f := .app f x) ⟨hf, hx x (.head _)⟩ fun y hy => hx y (.tail _ hy)

theorem ptr_bvs {Us : List Name} {CL : Literal → Prop} {Δ : VLCtx} :
    ∀ {n : Nat}, (∀ i < n, ∃ A, Δ.find? (.inl i) = some (.bvar i, A)) →
      List.Forall₂ (PTr Us CL Δ) (ElimNestedInductive.bvs n 0) (VExpr.bvars n 0)
  | 0, _ => .nil
  | n + 1, h => by
    have e : VExpr.bvars (n + 1) 0 = .bvar n :: VExpr.bvars n 0 := by
      simp [VExpr.bvars, List.range_succ]
    rw [e]
    obtain ⟨A, hA⟩ := h n (by omega)
    exact .cons (.bvar (by simpa using hA)) (ptr_bvs fun i hi => h i (by omega))

/-- The arguments of the occurrences the final phase checks translate over the first type's
leading binders as parameters, in a model of the environment it checks them in. -/
theorem nested_occs_tr [VEnv.Injective] {env : Environment} {ves : VEnvs} (wf : ves.WF env) {lparams : List Name}
    {nparams : Nat} {isUnsafe ap : Bool} {fuel : FuelConfig} {I : InductiveType}
    {rest : List InductiveType} (hcl : ∀ T ∈ I :: rest, ElimNestedInductive.TypeClosed T)
    {res : ElimNestedInductive.Result}
    (hrun : (ElimNestedInductive.run fuel.inductiveFuel nparams (I :: rest) env).run'
      { lvls := lparams.map .param, newTypes := (I :: rest).toArray } = .ok res)
    {xs : List FVarId} {body : Expr}
    (hoI : ElimNestedInductive.Opens {} I.type xs res.lctx body) (hxnd : xs.Nodup)
    (hparams : res.params = (xs.map .fvar).toArray)
    {auxs : List InductiveType} {pairs : List (Expr × Name)}
    (hA : List.Forall₂ (fun e T => ElimNestedInductive.AuxMade env res.params nparams (e, T))
      pairs auxs)
    (haux2 : res.aux2nested = pairs.foldl (fun m (e, n) => m.insert n e) {})
    (hpnd : (pairs.map (·.2)).Nodup)
    {env' envT envF : Environment} {inds : List (InductiveVal × List ConstructorVal)}
    {recs : List RecursorVal}
    (hF : NestedFinalOK env env' lparams (I :: rest) res isUnsafe ap fuel inds recs envT envF)
    {E₀ : VEnv} (hVT : VEnvAt envT (inductSafety isUnsafe) E₀)
    {Qs₀ : List VExpr} {B₀ : VExpr} (hQl : Qs₀.length = xs.length)
    (hIT : TrExprS E₀ lparams [] I.type (.foralls Qs₀ B₀)) :
    ∀ p ∈ pairs, ∃ J Ls Ks, p.1 = mkAppN (.const J Ls) Ks ∧
      ∀ k ∈ Ks.toList, ∃ k', TrExprS E₀ lparams (paramVLCtx Qs₀) (k.abstract' xs) k' := by
  have henv := hVT.tr.wf
  have hfvK := ElimNestedInductive.aux2nested_fvarsIn
    (ElimNestedInductive.EnvClosed.of_tr (wf.tr (safety := .unsafe))) hcl hrun hparams
  obtain ⟨M, E, hMw, hMl, hME, -, hEent, hMc, hMfv, hMf, -⟩ :=
    ElimNestedInductive.Opens.mlctx henv.ordered hoI (M₀ := .nil) trivial rfl (by simp) hxnd hQl
      (by simpa using hIT)
  simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_nil, List.append_nil] at hME hMfv hMc
  let c := TypeChecker.VContext.ofMLCtx hVT lparams fuel M hMw
  have hfvc : ∀ p ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp),
      p.2.FVarsIn (· ∈ c.vlctx.fvars) := fun p hp =>
    (hfvK p hp).mono fun x hx => by
      show x ∈ M.vlctx.fvars; rw [hMfv]; exact List.mem_reverse.2 hx
  obtain ⟨s, -, hQ⟩ := TypeChecker.M.WF.runMLCtx hVT hMw
    (TypeChecker.checkType.forM_lit (c := c) _ (fun p : Name × Expr => p.2) hfvc) (hMl ▸ hF.occList)
  have hEsome : ∀ x ∈ M.vlctx, x.1.isSome := by
    rw [hME]; intro x hx
    obtain ⟨y, ds, A, rfl, -⟩ := hEent x hx
    rfl
  have hΔf : ∀ fv e A, M.vlctx.find? (.inr fv) = some (e, A) →
      ∃ j, j < M.vlctx.toCtx.length ∧ xs.reverse.idxOf? fv = some j ∧ e = .bvar j := by
    intro fv e A h
    have hm := VLCtx.find?_inr_mem h
    rw [hMfv, List.mem_reverse] at hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨A', hA'⟩ := hMf k hk
    rw [hA'] at h
    cases h
    refine ⟨xs.length - 1 - k, by rw [hMc]; simp [hQl]; omega, ?_, rfl⟩
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp; omega, by rw [List.getElem_reverse]; congr 1; omega, fun j hj e => ?_⟩
    rw [List.getElem_reverse] at e
    have := (List.getElem_inj hxnd).1 e
    omega
  intro p hp
  obtain ⟨K, n⟩ := p
  have hmem : (n, K) ∈ Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp) := by
    rw [haux2]; exact foldl_insert_mem_toList hpnd hp
  obtain ⟨⟨K', hKtr⟩, -⟩ := hQ _ hmem
  change TrExprS E₀ lparams M.vlctx K K' at hKtr
  obtain ⟨T, -, hAM⟩ := Lean4Lean.List.Forall₂.forall_exists_l hA _ hp
  obtain ⟨-, cty, xs', lctx, body', -, -, -, -, -, -, -, hC⟩ := hAM
  obtain ⟨J, Ls, args, nI, Jv, v, hK, -, hnI, -⟩ := hC
  simp only at hK
  rw [hparams, ElimNestedInductive.replaceParamsVal_mkAppRange hnI] at hK
  generalize (List.map _ (args.extract 0 nI).toList).toArray = Ks at hK
  subst hK
  refine ⟨J, Ls, Ks, rfl, fun k hk => ?_⟩
  rw [Expr.mkAppN_eq_mkAppList] at hKtr
  obtain ⟨f', as', -, -, has⟩ := TrExprS.mkAppList_inv hKtr
  obtain ⟨k', -, hk'⟩ := Lean4Lean.List.Forall₂.forall_exists_l has k hk
  have := TrExprS.abstract'_params (As := M.vlctx.toCtx) rfl
    (VLCtx.find?_inl_of_fvars hEsome) hΔf (Γ := []) (by simp) (by simpa using hk')
  rw [hMc] at this
  refine ⟨k', ?_⟩
  show TrExprS E₀ lparams (paramCtx Qs₀.reverse) _ _
  simpa [VLCtx.toCtx] using this

section
open ElimNestedInductive
variable {r : ElimNestedInductive.Result} {env' : Environment} {lparams : List Name}
  {auxRec : NameMap Name} {R : Name → Option VAuxHead} {ren : Name → Option Name}

/-- The occurrence restoring puts back for an auxiliary constant translates over parameters `Qs`,
given that its arguments do and that what it stands for is well formed there. -/
theorem RestoreSpec.occ_tr {CL : Literal → Prop}
    (S : RestoreSpec r env' lparams auxRec lparams CL R ren) {n : Nat} (hnp : r.nparams = n)
    (hK : ∀ c K, r.aux2nested.find? c = some K → ∃ J Ls Ds,
      K.abstract r.params = Expr.mkAppList (.const J Ls) Ds ∧ ∀ D ∈ Ds, D.looseBVarRange' ≤ n)
    (hUs : lparams.Nodup) {E₀ : VEnv} (henv₀ : E₀.Ordered) (hlit : ∀ l, CL l → E₀.ContainsLits l)
    {Qs : List VExpr} (hQs : Qs.length = n) (hon : OnCtx Qs.reverse (E₀.IsType lparams.length))
    (hn : ∀ c h, R c = some h → h.n = n)
    (hwf : ∀ c h, R c = some h → VExpr.WF E₀ lparams.length Qs.reverse
      (h.inst (VLevel.params lparams.length) (VExpr.bvars h.n 0)))
    (hDs : ∀ a K J Ls Ds, r.aux2nested.find? a = some K →
      K.abstract r.params = Expr.mkAppList (.const J Ls) Ds →
      ∀ D ∈ Ds, ∃ D', TrExprS E₀ lparams (paramVLCtx Qs) D D')
    {c : Name} (hc : (R c).isSome) :
    ∃ Y, TrExprS E₀ lparams (paramVLCtx Qs)
      ((Expr.mkAppList (.const c (lparams.map .param)) (bvs n 0)).replaceNoCache
        (Result.restoreFn r env' lparams auxRec)) Y := by
  obtain ⟨h, hR⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨a, K, J, h', Ls, Ds, hfa, hD, -, hF⟩ := S.restoreFn_bvs hnp hK hc
  have hlv := VLevel.mapM_ofLevel_params hUs
  have hargs : List.Forall₂ (PTr lparams CL (paramVLCtx Qs)) (bvs n 0).toArray.toList
      (VExpr.bvars n 0) := by
    simpa using ptr_bvs (Us := lparams) (CL := CL) (Δ := paramVLCtx Qs) (n := n) fun i hi =>
      paramCtx_find?_bvar (As := Qs.reverse) (by simp [hQs]; omega)
  obtain ⟨out, hout, hP⟩ := S.repl c h (lparams.map .param) _ (bvs n 0).toArray (paramVLCtx Qs) _
    hR hlv (by simp) (by simp [hnp, bvs_length]) hargs
  rw [← S.restoreFn_eq_kRepl hnp hc bvs_length, hF 0, Expr.liftLooseBVars_zero] at hout
  cases hout
  rw [Expr.replaceNoCache.eq_def, hF 0, Expr.liftLooseBVars_zero]
  refine ⟨_, (hP.mono_lit hlit).toTrExprS' henv₀ ?_ (by simpa using hon) ?_⟩
  · exact letsOK_mkAppList trivial fun D hD' =>
      let ⟨_, hD''⟩ := hDs a K J Ls Ds hfa hD D hD'; hD''.letsOK
  · have := hwf c h hR
    rw [hn c h hR] at this
    simpa using this

end
end Lean4Lean

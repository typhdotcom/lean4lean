import Lean4Lean.Verify.Environment.RestoreDrop
import Lean4Lean.Theory.Typing.NestedDecl

/-!
# Restoring translations in a context

A translation is its plain translation (`PTr`) together with the typing of what that does not
determine: the values of the term's `let`s (`LetsOK`), the rest coming from the translation's own
typing (`PTr.toTrExprS'`). Restoring a nested block's translated term in a context of binders over
the parameters keeps the `let`s typed (`TrExprS.restoreLets`), carried by `RestoreEnv`, except in
the occurrences it puts back, whose typing comes from elsewhere.
-/

namespace Lean4Lean
open Lean

/-- Each `let` of `e`, in context `Δ`, has its value's translation typed at its type's. -/
def LetsOK (env : VEnv) (Us : List Name) : VLCtx → Expr → Prop
  | Δ, .app f a => LetsOK env Us Δ f ∧ LetsOK env Us Δ a
  | Δ, .lam _ t b _ | Δ, .forallE _ t b _ => LetsOK env Us Δ t ∧
    ∀ (CL : Literal → Prop) t', PTr Us CL Δ t t' → LetsOK env Us ((none, .vlam t') :: Δ) b
  | Δ, .letE _ t v b _ => LetsOK env Us Δ t ∧ LetsOK env Us Δ v ∧
    ∀ (CL : Literal → Prop) t' v', PTr Us CL Δ t t' → PTr Us CL Δ v v' →
      env.HasType Us.length Δ.toCtx v' t' ∧ LetsOK env Us ((none, .vlet t' v') :: Δ) b
  | Δ, .mdata _ e | Δ, .proj _ _ e => LetsOK env Us Δ e
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const .. | _, .lit _ => True

/-- Where its translation is typed, a term whose `let`s are typed translates. -/
theorem PTr.toTrExprS' {env : VEnv} (henv : env.Ordered) {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, PTr Us env.ContainsLits Δ e e' → LetsOK env Us Δ e →
      OnCtx Δ.toCtx (env.IsType Us.length) → e'.WF env Us.length Δ.toCtx →
      TrExprS env Us Δ e e'
  | _, _, _, .bvar h, _, _, _ => .bvar h
  | _, _, _, .fvar h, _, _, _ => .fvar h
  | _, _, _, .sort h, _, _, _ => .sort h
  | _, _, _, .const h, _, hΓ, hwf => by
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΓ
    exact .const hci h (by rw [← hlen, Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 h)])
  | _, _, _, .app hf ha, hl, hΓ, hwf => by
    obtain ⟨A, B, hf', ha'⟩ := hwf.app_inv henv hΓ
    exact .app hf' ha' (hf.toTrExprS' henv hl.1 hΓ ⟨_, hf'⟩) (ha.toTrExprS' henv hl.2 hΓ ⟨_, ha'⟩)
  | _, _, _, .lam hA hb, hl, hΓ, hwf => by
    obtain ⟨hA', hb'⟩ := hwf.lam_inv henv hΓ
    exact .lam hA' (hA.toTrExprS' henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hb.toTrExprS' henv (hl.2 _ _ hA) ⟨hΓ, hA'⟩ hb')
  | _, _, _, .forallE hA hB, hl, hΓ, ⟨_, hT⟩ => by
    obtain ⟨hA', hB'⟩ := VEnv.HasType.forallE_inv henv hT
    exact .forallE hA' hB' (hA.toTrExprS' henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hB.toTrExprS' henv (hl.2 _ _ hA) ⟨hΓ, hA'⟩ (let ⟨_, h⟩ := hB'; ⟨_, h⟩))
  | _, _, _, .letE ht hv hb, hl, hΓ, hwf => by
    obtain ⟨hvt, hlb⟩ := hl.2.2 _ _ _ ht hv
    have hT := hvt.isType henv hΓ
    exact .letE hvt (ht.toTrExprS' henv hl.1 hΓ (let ⟨_, h⟩ := hT; ⟨_, h⟩))
      (hv.toTrExprS' henv hl.2.1 hΓ ⟨_, hvt⟩) (hb.toTrExprS' henv hlb hΓ hwf)
  | _, .lit l, _, .lit hc h, _, hΓ, hwf =>
    .lit hc (h.toTrExprS henv Literal.toConstructor_letFree hΓ hwf)
  | _, _, _, .mdata h, hl, hΓ, hwf => .mdata (h.toTrExprS' henv hl hΓ hwf)
  | _, _, _, .proj h, hl, hΓ, hwf => by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hT, -⟩ := hwf.proj_inv henv hΓ
    exact .proj (h.toTrExprS' henv hl hΓ ⟨_, hT⟩) hwf

/-- A translation's `let`s are typed. -/
theorem TrExprS.letsOK {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : LetsOK env Us Δ e := by
  induction H with
  | bvar | fvar | sort | const | lit => trivial
  | app _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ hA _ ih1 ih2 | forallE _ _ hA _ ih1 ih2 =>
    refine ⟨ih1, fun CL t' h => ?_⟩
    cases hA.toPTr.unique h; exact ih2
  | letE hvt ht hv _ ih1 ih2 ih3 =>
    refine ⟨ih1, ih2, fun CL t' v' h1 h2 => ?_⟩
    cases ht.toPTr.unique h1; cases hv.toPTr.unique h2
    exact ⟨hvt, ih3⟩
  | mdata _ ih | proj _ _ ih => exact ih

section
open ElimNestedInductive
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {auxRec : NameMap Name} {Us : List Name} {R : Name → Option VAuxHead}
  {ren : Name → Option Name} {lvls : List Level} {n : Nat} {ls₀ : List VLevel}
  {Γ₀ : List VExpr} {Θ : VLCtx} {E₁ E₀ : VEnv}

local notation "ρ" => Expr.replaceNoCache (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)

/-- How a context of the translation, `Δ₁`, and of the restored terms, `Δ₂`, sit over the
parameters `Γ₀`: their binders are `Δ`, restored in `Δ₂`, and their parameters are at depth `k`. -/
structure RCtx (E₁ : VEnv) (U : Nat) (R : Name → Option VAuxHead) (ren : Name → Option Name)
    (ls₀ : List VLevel) (Γ₀ : List VExpr) (Θ : VLCtx) (n : Nat) (Δ₁ Δ₂ : VLCtx) (Δ : List VExpr)
    (k : Nat) : Prop where
  ctx₁ : Δ₁.toCtx = Δ ++ Γ₀
  ctx₂ : Δ₂.toCtx = Δ.map (·.restore R fun _ => none) ++ Γ₀
  wf : OnCtx (Δ ++ Γ₀) (E₁.IsType U)
  aux : VExpr.CtxAuxAt R ls₀ Δ
  np : CtxNP R Δ₁
  rel : CtxRel R ren Δ₁ Δ₂
  some : CtxSome Δ₁ Δ₂
  params : ParamsAt n Δ₁ k Δ.length
  caux : CtxAux R ls₀ Δ₁ Δ.length
  base : ∃ L : VLCtx, Δ₂ = L ++ Θ ∧ L.length = k ∧ ∀ x ∈ L, x.1 = none

theorem VLCtx.bvLift_append {Θ : VLCtx} : ∀ (L : VLCtx), (∀ x ∈ L, x.1 = none) →
    ∃ m, VLCtx.BVLift Θ (L ++ Θ) L.length 0 m 0
  | [], _ => ⟨0, .refl⟩
  | (o, d) :: L, h => by
    obtain ⟨m, W⟩ := VLCtx.bvLift_append L fun x hx => h x (.tail _ hx)
    obtain rfl : o = none := h _ (.head _)
    exact ⟨_, .skip d W⟩

/-- An occurrence put back, typed over the parameters `Θ`, keeps its `let`s typed under the
binders above them. -/
theorem RCtx.lets_lift {U : Nat} {Δ₁ Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}
    (C : RCtx E₁ U R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k) (henv₀ : E₀.Ordered) {N : Expr} {Y : VExpr}
    (hY : TrExprS E₀ Us Θ N Y) : LetsOK E₀ Us Δ₂ (N.liftLooseBVars' 0 k) := by
  obtain ⟨L, rfl, rfl, hL⟩ := C.base
  obtain ⟨m, W⟩ := VLCtx.bvLift_append L hL
  exact (hY.weakBV henv₀ W).letsOK

/-- A restored typing of the translation's, in contexts `RCtx` relates. -/
theorem RCtx.hasType {U : Nat} {F : Name → Option VExpr} (HE : RestoreEnv E₁ E₀ U F R ls₀ Γ₀)
    {Δ₁ Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat} (C : RCtx E₁ U R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k)
    {e A : VExpr} (he : e.AuxAt R ls₀ Δ.length) (hA : A.AuxAt R ls₀ Δ.length)
    (h : E₁.HasType U Δ₁.toCtx e A) :
    E₀.HasType U Δ₂.toCtx (e.restore R fun _ => none) (A.restore R fun _ => none) := by
  rw [C.ctx₂]; rw [C.ctx₁] at h
  exact HE.hasType C.wf C.aux he hA h

/-- A binder pushed on both contexts. -/
theorem RCtx.vlam {U : Nat} {Δ₁ Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}
    (C : RCtx E₁ U R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k) {A A' : VExpr}
    (hA : E₁.IsType U Δ₁.toCtx A) (hAa : A.AuxAt R ls₀ Δ.length)
    (hA' : A' = A.restore R fun _ => none) :
    RCtx E₁ U R ren ls₀ Γ₀ Θ n ((none, .vlam A) :: Δ₁) ((none, .vlam A') :: Δ₂) (A :: Δ) (k + 1) where
  ctx₁ := by simp [VLCtx.toCtx, C.ctx₁]
  ctx₂ := by simp [VLCtx.toCtx, C.ctx₂, hA']
  wf := ⟨C.wf, by show E₁.IsType U (Δ ++ Γ₀) A; rw [← C.ctx₁]; exact hA⟩
  aux := ⟨hAa, C.aux⟩
  np := C.np.cons noPartial_bvar
  rel := C.rel.cons (fun _ => rfl) rfl
  some := C.some.cons _ _
  params := by simpa using C.params.vlam
  caux := by simpa using C.caux.vlam
  base := let ⟨L, h1, h2, h3⟩ := C.base
    ⟨(none, .vlam A') :: L, by simp [h1], by simp [h2], by simpa using h3⟩

/-- A `let` pushed on both contexts. -/
theorem RCtx.vlet {U : Nat} {Δ₁ Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}
    (C : RCtx E₁ U R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k) {A V A' V' : VExpr}
    (hV : V.NoPartial R) (hVa : V.AuxAt R ls₀ Δ.length) (hV' : V' = V.restore R ren) :
    RCtx E₁ U R ren ls₀ Γ₀ Θ n ((none, .vlet A V) :: Δ₁) ((none, .vlet A' V') :: Δ₂) Δ (k + 1) where
  ctx₁ := by simp [VLCtx.toCtx, C.ctx₁]
  ctx₂ := by simp [VLCtx.toCtx, C.ctx₂]
  wf := C.wf
  aux := C.aux
  np := C.np.cons hV
  rel := C.rel.cons (fun _ => hV') rfl
  some := C.some.cons _ _
  params := C.params.vlet
  caux := C.caux.vlet hVa
  base := let ⟨L, h1, h2, h3⟩ := C.base
    ⟨(none, .vlet A' V') :: L, by simp [h1], by simp [h2], by simpa using h3⟩

/-- Restoring a translation's term in a context keeps its `let`s typed, given that the
occurrences it puts back are. -/
theorem TrExprS.restoreLets {F : Name → Option VExpr}
    (HE : RestoreEnv E₁ E₀ Us.length F R ls₀ Γ₀) (henv₁ : E₁.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    (hF : PlacedFn (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)
      (fun c => (R c).isSome) (fun c => (auxRec.find? c).isSome) lvls n)
    (hlv : lvls.mapM (VLevel.ofLevel Us) = some ls₀)
    (hR1 : ∀ c h, R c = some h → (R c).isSome ∧ h.n = n)
    (hlit : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP fun c => (R c).isSome) = false)
    (hren : ∀ c, ren c ≠ none → E₁.constants c = none)
    (hrepl : ∀ c, (R c).isSome → ∀ {Δ₁ Δ₂ Δ k}, RCtx E₁ Us.length R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k →
      LetsOK E₀ Us Δ₂ (ρ (Expr.mkAppList (.const c lvls) (bvs n k))))
    {Δ₁ : VLCtx} {e : Expr} {e' : VExpr} (H : TrExprS E₁ Us Δ₁ e e') :
    ∀ {Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}, RCtx E₁ Us.length R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k →
      AuxPlaced (fun c => (R c).isSome) lvls n k e →
      e.anySub (constP fun c => (auxRec.find? c).isSome) = false →
      e.ConstsOK (fun c ls => (R c).isSome → ls.length = lparams.length) →
      (ρ e).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none) →
      LetsOK E₀ Us Δ₂ (ρ e) := by
  have hR2 : ∀ c, (R c).isSome → ∃ h, R c = some h := fun c h => Option.isSome_iff_exists.1 h
  -- what restoring a subterm gives
  have rest {Δ₁ Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}
      (C : RCtx E₁ Us.length R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k) {t : Expr} {t' : VExpr}
      (ht : TrExprS E₁ Us Δ₁ t t') (hA : AuxPlaced (fun c => (R c).isSome) lvls n k t)
      (har : t.ConstsOK (fun c ls => (R c).isSome → ls.length = lparams.length))
      (hc : (ρ t).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none))
      (hcs : t'.ConstsSat (ren · = none)) {CL : Literal → Prop} {t'' : VExpr}
      (h2 : PTr Us CL Δ₂ (ρ t) t'') :
      t'.AuxAt R ls₀ Δ.length ∧ t'' = t'.restore R fun _ => none := by
    have hAt := ElimNestedInductive.TrExprS.auxAt hlv hR1 hR2 hlit ht C.params C.caux hA
    obtain ⟨y, hy, hy'⟩ := ht.toPTr.restore S C.np C.rel C.some har hc
    refine ⟨hAt, ?_⟩
    rw [h2.unique hy, hy' hAt.leadFree, VExpr.restore_ren_none hcs]
  have csat {Δ₁ : VLCtx} {Δ : List VExpr} {e A : VExpr} (hΓ : Δ₁.toCtx = Δ ++ Γ₀)
      (hon : OnCtx (Δ ++ Γ₀) (E₁.IsType Us.length)) (h : E₁.HasType Us.length Δ₁.toCtx e A) :
      e.ConstsSat (ren · = none) ∧ A.ConstsSat (ren · = none) := by
    rw [hΓ] at h
    have := VEnv.IsDefEq.constsSat henv₁ h (VEnv.OnCtx.constsSat henv₁ hon)
    have hm {x : VExpr} (hx : x.ConstsSat (E₁.constants · |>.isSome)) : x.ConstsSat (ren · = none) :=
      hx.mono fun c hc => by
        by_contra h'; rw [hren c h'] at hc; cases hc
    exact ⟨hm this.1, hm this.2.2⟩
  induction H with
  | bvar h =>
    intros
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; trivial
  | fvar h =>
    intros
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; trivial
  | sort h =>
    intros
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; trivial
  | lit _ _ _ =>
    intros
    rw [Expr.replaceNoCache.eq_def, hF.noSpine _ rfl]; trivial
  | @const c ci us' Δ₁ us _ _ _ =>
    intro Δ₂ Δ k C hA hr _ _
    by_cases hc : (R c).isSome
    · obtain ⟨-, rfl⟩ := hA hc
      have := hrepl c hc C
      have hn : n = 0 := (hA hc).1
      subst hn
      simpa [bvs, Expr.mkAppList] using this
    · rw [Expr.replaceNoCache.eq_def, hF.spine _ c us [] rfl (by simp [hc])
        (by simpa [Expr.anySub, constP] using hr)]
      trivial
  | @app Δ₁ f' A B a' f a _ _ hf ha ih1 ih2 =>
    intro Δ₂ Δ k C hA hr har hc
    have hr' := anySub_constP_app.1 hr
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      by_cases hcx : (R c).isSome = true ∧ xs.length = n
      · rw [if_pos hcx] at hA
        obtain ⟨rfl, rfl⟩ := hA
        rw [spineNM_eq hs]
        exact hrepl c hcx.1 C
      · rw [if_neg hcx] at hA
        rw [Expr.replaceNoCache_app (hF.spine _ c ls xs hs hcx (spineNM_anySub hs hr))] at hc ⊢
        exact ⟨ih1 C hA.1 hr'.1 har.1 hc.1, ih2 C hA.2 hr'.2 har.2 hc.2⟩
    · rename_i hs
      rw [Expr.replaceNoCache_app (hF.noSpine _ hs)] at hc ⊢
      exact ⟨ih1 C hA.1 hr'.1 har.1 hc.1, ih2 C hA.2 hr'.2 har.2 hc.2⟩
  | @lam Δ₁ ty' ty body body' nm bi hty _ _ ih1 ih2 =>
    intro Δ₂ Δ k C hA hr har hc
    have hr' := anySub_constP_lam.1 hr
    rw [Expr.replaceNoCache_lam (hF.noSpine _ rfl)] at hc ⊢
    refine ⟨ih1 C hA.1 hr'.1 har.1 hc.1, fun CL t'' h2 => ?_⟩
    obtain ⟨u, hu⟩ := hty
    obtain ⟨hAt, rfl⟩ := rest C ‹_› hA.1 har.1 hc.1 (csat C.ctx₁ C.wf hu).1 h2
    exact ih2 (C.vlam ⟨u, hu⟩ hAt rfl) hA.2 hr'.2 har.2 hc.2
  | @forallE Δ₁ ty' body' ty body nm bi hty _ _ _ ih1 ih2 =>
    intro Δ₂ Δ k C hA hr har hc
    have hr' := anySub_constP_forallE.1 hr
    rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl)] at hc ⊢
    refine ⟨ih1 C hA.1 hr'.1 har.1 hc.1, fun CL t'' h2 => ?_⟩
    obtain ⟨u, hu⟩ := hty
    obtain ⟨hAt, rfl⟩ := rest C ‹_› hA.1 har.1 hc.1 (csat C.ctx₁ C.wf hu).1 h2
    exact ih2 (C.vlam ⟨u, hu⟩ hAt rfl) hA.2 hr'.2 har.2 hc.2
  | @letE Δ₁ val' ty' ty val body body' nm nd hvt ht hv _ ih1 ih2 ih3 =>
    intro Δ₂ Δ k C hA hr har hc
    have hr' := anySub_constP_letE.1 hr
    rw [Expr.replaceNoCache_letE (hF.noSpine _ rfl)] at hc ⊢
    refine ⟨ih1 C hA.1 hr'.1 har.1 hc.1, ih2 C hA.2.1 hr'.2.1 har.2.1 hc.2.1,
      fun CL t'' v'' h2 h3 => ?_⟩
    obtain ⟨hcv, hct⟩ := csat C.ctx₁ C.wf hvt
    obtain ⟨hAt, rfl⟩ := rest C ht hA.1 har.1 hc.1 hct h2
    obtain ⟨hAv, rfl⟩ := rest C hv hA.2.1 har.2.1 hc.2.1 hcv h3
    refine ⟨C.hasType HE hAv hAt hvt, ?_⟩
    have hNP := hv.toPTr.noPartial S C.np hc.2.1
    exact ih3 (C.vlet hNP hAv (VExpr.restore_ren_none hcv).symm) hA.2.2 hr'.2.2 har.2.2 hc.2.2
  | mdata _ ih =>
    intro Δ₂ Δ k C hA hr har hc
    rw [Expr.replaceNoCache_mdata (hF.noSpine _ rfl)] at hc ⊢
    exact ih C hA (anySub_constP_mdata.1 hr) har hc
  | proj _ _ ih =>
    intro Δ₂ Δ k C hA hr har hc
    rw [Expr.replaceNoCache_proj (hF.noSpine _ rfl)] at hc ⊢
    exact ih C hA (anySub_constP_proj.1 hr) har hc

/-- A telescope of the translation whose domains translate to types, restored, in contexts
`RCtx` relates: the restored domains translate to the restored types. The occurrences restoring
puts back are typed over the parameters `Θ`. -/
theorem TeleDoms.restore {F : Name → Option VExpr}
    (HE : RestoreEnv E₁ E₀ Us.length F R ls₀ Γ₀) (henv₁ : E₁.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    (hF : PlacedFn (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)
      (fun c => (R c).isSome) (fun c => (auxRec.find? c).isSome) lvls n)
    (hlv : lvls.mapM (VLevel.ofLevel Us) = some ls₀)
    (hR1 : ∀ c h, R c = some h → (R c).isSome ∧ h.n = n)
    (hlit : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP fun c => (R c).isSome) = false)
    (hren : ∀ c, ren c ≠ none → E₁.constants c = none)
    (hlitE : ∀ l, E₁.ContainsLits l → E₀.ContainsLits l)
    (hocc : ∀ c, (R c).isSome → ∃ Y, TrExprS E₀ Us Θ (ρ (Expr.mkAppList (.const c lvls) (bvs n 0))) Y)
    {Δ₁ : VLCtx} {e : Expr} (H : TeleDoms E₁ Us Δ₁ e) :
    ∀ {Δ₂ : VLCtx} {Δ : List VExpr} {k : Nat}, RCtx E₁ Us.length R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k →
      OnCtx Δ₂.toCtx (E₀.IsType Us.length) →
      AuxPlaced (fun c => (R c).isSome) lvls n k e →
      e.anySub (constP fun c => (auxRec.find? c).isSome) = false →
      e.ConstsOK (fun c ls => (R c).isSome → ls.length = lparams.length) →
      (ρ e).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none) →
      TeleDoms E₀ Us Δ₂ (ρ e) := by
  have henv₀ := HE.wf.ordered
  have hrepl : ∀ c, (R c).isSome → ∀ {Δ₁ Δ₂ Δ k},
      RCtx E₁ Us.length R ren ls₀ Γ₀ Θ n Δ₁ Δ₂ Δ k →
      LetsOK E₀ Us Δ₂ (ρ (Expr.mkAppList (.const c lvls) (bvs n k))) := by
    intro c hc Δ₁ Δ₂ Δ k C
    obtain ⟨N, -, -, hFN⟩ := hF.aux c hc
    obtain ⟨Y, hY⟩ := hocc c hc
    rw [Expr.replaceNoCache.eq_def, hFN 0, Expr.liftLooseBVars_zero] at hY
    rw [Expr.replaceNoCache.eq_def, hFN k]
    exact C.lets_lift henv₀ hY
  induction H with
  | nil h1 h2 h3 =>
    intro Δ₂ Δ k C _ hA hr _ _
    obtain ⟨h2', h3'⟩ := hF.not_var hA hr h2 h3
    exact .nil (hF.not_forallE hA hr h1) h2' h3'
  | @cons Δ₁ dom b A nm bi hdom hAT _ ih =>
    intro Δ₂ Δ k C hon hA hr har hc
    have hr' := anySub_constP_forallE.1 hr
    rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl)] at hc ⊢
    have hR2 : ∀ c, (R c).isSome → ∃ h, R c = some h := fun c h => Option.isSome_iff_exists.1 h
    have hAt := ElimNestedInductive.TrExprS.auxAt hlv hR1 hR2 hlit hdom C.params C.caux hA.1
    obtain ⟨u, hu⟩ := hAT
    have hcs : A.ConstsSat (ren · = none) := by
      have h := hu; rw [C.ctx₁] at h
      exact ((VEnv.IsDefEq.constsSat henv₁ h (VEnv.OnCtx.constsSat henv₁ C.wf)).1).mono
        fun c hc => by by_contra h'; rw [hren c h'] at hc; cases hc
    obtain ⟨y, hy, hy'⟩ := hdom.toPTr.restore S C.np C.rel C.some har.1 hc.1
    rw [hy' hAt.leadFree, VExpr.restore_ren_none hcs] at hy
    have hAT₀ : E₀.IsType Us.length Δ₂.toCtx (A.restore R fun _ => none) :=
      ⟨_, C.hasType HE (A := .sort u) hAt trivial hu⟩
    have hL := hdom.restoreLets HE henv₁ S hF hlv hR1 hlit hren hrepl C hA.1 hr'.1 har.1 hc.1
    have htr := (hy.mono_lit hlitE).toTrExprS' henv₀ hL hon (let ⟨_, h⟩ := hAT₀; ⟨_, h⟩)
    exact .cons htr hAT₀ (ih (C.vlam ⟨u, hu⟩ hAt rfl) ⟨hon, hAT₀⟩ hA.2 hr'.2 har.2 hc.2)

/-- The context of parameters `Qs`, outermost first. -/
def paramVLCtx (Qs : List VExpr) : VLCtx := Qs.reverse.map fun Q => (none, .vlam Q)

@[simp] theorem paramVLCtx_toCtx (Qs : List VExpr) : (paramVLCtx Qs).toCtx = Qs.reverse := by
  simp only [paramVLCtx]
  induction Qs.reverse <;> simp_all [VLCtx.toCtx]

theorem paramVLCtx_snoc (Qs : List VExpr) (Q : VExpr) :
    paramVLCtx (Qs ++ [Q]) = (none, .vlam Q) :: paramVLCtx Qs := by
  simp [paramVLCtx]

/-- A nested block's translated constructor type whose dropped telescopes have typed domains,
restored, still does: its parameters are those of the restored type's translation `Ps`, over
which `RestoreEnv` carries the rest. -/
theorem CtorDoms.restore {F : Name → Option VExpr} (henv₁ : E₁.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    (hF : PlacedFn (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)
      (fun c => (R c).isSome) (fun c => (auxRec.find? c).isSome) lvls n)
    (hlv : lvls.mapM (VLevel.ofLevel Us) = some ls₀)
    (hR1 : ∀ c h, R c = some h → (R c).isSome ∧ h.n = n)
    (hlit : ∀ l, E₁.ContainsLits l → l.toConstructor.anySub (constP fun c => (R c).isSome) = false)
    (hren : ∀ c, ren c ≠ none → E₁.constants c = none)
    (hlitE : ∀ l, E₁.ContainsLits l → E₀.ContainsLits l)
    {t₀ : Expr} {nf : Nat} (hCD : CtorDoms E₁ Us n nf t₀)
    {Ps : List VExpr} {B : VExpr} (htr : TrExprS E₀ Us [] (ρ t₀) (VExpr.foralls Ps B))
    (hPs : Ps.length = n) (HE : RestoreEnv E₁ E₀ Us.length F R ls₀ Ps.reverse)
    (hocc : ∀ c, (R c).isSome → ∃ Y, TrExprS E₀ Us (paramVLCtx Ps)
      (ρ (Expr.mkAppList (.const c lvls) (bvs n 0))) Y)
    (hpl : PlacedAfter (fun c => (R c).isSome) lvls n n t₀)
    (hr : t₀.anySub (constP fun c => (auxRec.find? c).isSome) = false)
    (har : t₀.ConstsOK (fun c ls => (R c).isSome → ls.length = lparams.length))
    (hc : (ρ t₀).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none)) :
    CtorDoms E₀ Us n nf (ρ t₀) := by
  have henv₀ := HE.wf.ordered
  intro m hm
  rw [hF.dropAfter n m hpl hr]
  have go : ∀ p (t : Expr) (Qs Ps' : List VExpr), Qs ++ Ps' = Ps → Ps'.length = p →
      TeleDoms E₁ Us (paramVLCtx Qs) (Expr.dropAfter p m t) →
      TrExprS E₀ Us (paramVLCtx Qs) (ρ t) (VExpr.foralls Ps' B) →
      OnCtx Qs.reverse (E₁.IsType Us.length) → OnCtx Qs.reverse (E₀.IsType Us.length) →
      PlacedAfter (fun c => (R c).isSome) lvls n p t →
      t.anySub (constP fun c => (auxRec.find? c).isSome) = false →
      t.ConstsOK (fun c ls => (R c).isSome → ls.length = lparams.length) →
      (ρ t).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none) →
      TeleDoms E₀ Us (paramVLCtx Qs) (ρ (Expr.dropAfter p m t)) := by
    intro p
    induction p with
    | zero =>
      intro t Qs Ps' hQ hl hT₁ _ hon₁ hon₀ hA hr har hc
      obtain rfl : Ps' = [] := List.eq_nil_of_length_eq_zero hl
      simp only [List.append_nil] at hQ; subst hQ
      simp only [Expr.dropAfter_zero] at hT₁ ⊢
      have hA' := hF.dropU_placed m hA hr
      have C : RCtx E₁ Us.length R ren ls₀ Qs.reverse (paramVLCtx Qs) n (paramVLCtx Qs)
          (paramVLCtx Qs) [] 0 := by
        obtain ⟨hP, hCA⟩ := ElimNestedInductive.paramsCtx R ls₀ Qs.reverse
        have hbv : ∀ v e A, (paramVLCtx Qs).find? v = some (e, A) → ∃ i, e = .bvar i :=
          fun v e A h => ElimNestedInductive.paramsCtx_bvar Qs.reverse h
        refine {
          ctx₁ := by simp
          ctx₂ := by simp
          wf := by simpa using hon₁
          aux := trivial
          np := fun v e A h => by obtain ⟨i, rfl⟩ := hbv v e A h; exact noPartial_bvar
          rel := fun v y A h _ => by
            obtain ⟨i, rfl⟩ := hbv v y A h; exact ⟨A, by simpa [VExpr.restore] using h⟩
          some := fun v h => h
          params := by simpa [paramVLCtx, hPs] using hP
          caux := by simpa [paramVLCtx] using hCA
          base := ⟨[], rfl, rfl, by simp⟩ }
      have hc' : (ρ (Expr.dropU m t)).ConstsOK (fun c _ => R c = none ∧ auxRec.find? c = none) := by
        rw [← hF.dropU m hA hr]; exact constsOK_dropU m hc
      exact hT₁.restore HE henv₁ S hF hlv hR1 hlit hren hlitE hocc C (by simpa using hon₀)
        hA'.1 hA'.2 (constsOK_dropU m har) hc'
    | succ p ih =>
      intro t Qs Ps' hQ hl hT₁ hT₀ hon₁ hon₀ hA hr har hc
      cases t with
      | forallE nm d b bi =>
        have hr' := anySub_constP_forallE.1 hr
        have hd : ρ d = d := hF.id_of_free hA.1 hr'.1
        rw [Expr.dropAfter_forallE] at hT₁ ⊢
        rw [Expr.replaceNoCache_forallE (hF.noSpine _ rfl), hd] at hT₀ hc ⊢
        obtain ⟨P', Ps'', rfl⟩ : ∃ P' Ps'', Ps' = P' :: Ps'' := by
          cases Ps' with
          | nil => simp at hl
          | cons P' Ps'' => exact ⟨_, _, rfl⟩
        cases hT₁ with
        | nil h1 _ _ => exact (h1 _ _ _ _ rfl).elim
        | cons h1 h2 h3 =>
        cases hT₀ with
        | forallE h4 _ h6 h7 =>
        cases h1.toPTr.unique h6.toPTr
        have hQ' : (Qs ++ [P']) ++ Ps'' = Ps := by simpa using hQ
        have := ih b (Qs ++ [P']) Ps'' hQ' (by simpa using hl)
          (by rw [paramVLCtx_snoc]; exact h3) (by rw [paramVLCtx_snoc]; exact h7)
          (by simpa using ⟨hon₁, by simpa using h2⟩) (by simpa using ⟨hon₀, by simpa using h4⟩)
          hA.2 hr'.2 har.2 hc.2
        rw [paramVLCtx_snoc] at this
        exact .cons h6 h4 this
      | _ => exact hA.elim
  exact go n t₀ [] Ps (by simp) hPs (by simpa [paramVLCtx] using hCD m hm)
    (by simpa [paramVLCtx] using htr) trivial trivial hpl hr har hc

end
end Lean4Lean

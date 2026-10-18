import Batteries.Data.UnionFind.Lemmas
import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.EquivManager
import Lean4Lean.Verify.TypeChecker.Rerun

namespace Lean4Lean.EquivManager
open Lean hiding Environment Exception
open Batteries Kernel

inductive RelevantEq : Expr → Expr → Prop
  | bvar : RelevantEq (.bvar i) (.bvar i)
  | fvar : RelevantEq (.fvar i) (.fvar i)
  | mvar : RelevantEq (.mvar i) (.mvar i)
  | sort : RelevantEq (.sort u) (.sort u)
  | const : RelevantEq (.const n ls) (.const n ls)
  | app : RelevantEq f₁ f₂ → RelevantEq a₁ a₂ → RelevantEq (.app f₁ a₁) (.app f₂ a₂)
  | lam : RelevantEq d₁ d₂ → RelevantEq b₁ b₂ → RelevantEq (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : RelevantEq d₁ d₂ → RelevantEq b₁ b₂ →
    RelevantEq (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : RelevantEq t₁ t₂ → RelevantEq v₁ v₂ → RelevantEq b₁ b₂ →
    RelevantEq (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | lit : RelevantEq (.lit l) (.lit l)
  | mdata : RelevantEq e₁ e₂ → RelevantEq (.mdata _ e₁) (.mdata _ e₂)
  | proj : RelevantEq e₁ e₂ → RelevantEq (.proj s i e₁) (.proj s i e₂)

theorem RelevantEq.rfl : RelevantEq e e := by
  induction e with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | mvar => exact .mvar
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ _ ih => exact .mdata ih
  | proj _ _ _ ih => exact .proj ih

theorem RelevantEq.symm (H1 : RelevantEq e₁ e₂) : RelevantEq e₂ e₁ := by
  induction H1 with
  | bvar | fvar | mvar | sort | const | lit => exact .rfl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

theorem RelevantEq.of_eqv : e₁ == e₂ → RelevantEq e₁ e₂ := by
  simp [(· == ·)]; induction e₁ generalizing e₂
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [Expr.eqv']; intros; subst_vars; try simp [rfl, *]
  all_goals grind [RelevantEq]

theorem RelevantEq.trans (H1 : RelevantEq e₁ e₂) (H2 : RelevantEq e₂ e₃) : RelevantEq e₁ e₃ := by
  induction H1 generalizing e₃ with
  | bvar | fvar | mvar | sort | const | lit => exact H2
  | app h1 h2 ih1 ih2 => let .app r1 r2 := H2; exact .app (ih1 r1) (ih2 r2)
  | lam h1 h2 ih1 ih2 => let .lam r1 r2 := H2; exact .lam (ih1 r1) (ih2 r2)
  | forallE h1 h2 ih1 ih2 => let .forallE r1 r2 := H2; exact .forallE (ih1 r1) (ih2 r2)
  | letE h1 h2 h3 ih1 ih2 ih3 => let .letE r1 r2 r3 := H2; exact .letE (ih1 r1) (ih2 r2) (ih3 r3)
  | mdata h1 ih => let .mdata r1 := H2; exact .mdata (ih r1)
  | proj h1 ih => let .proj r1 := H2; exact .proj (ih r1)

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}

theorem IsDefEqE.relevant (H : RelevantEq e₁ e₂) : IsDefEqE env us Δ e₁ e₂ := by
  induction H with
  | bvar | fvar | mvar | sort | const | lit => exact .rfl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : VEnv.WF env) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem RelevantEq.uniq [VEnv.Injective] (eq : RelevantEq e₁ e₂)
    (H1 : TrExprS env Us Δ₁ e₁ e₁') (H2 : TrExprS env Us Δ₂ e₂ e₂') :
    env.IsDefEqU Us.length Δ₁.toCtx e₁' e₂' := by
  induction H1 generalizing e₂ Δ₂ e₂' with
  | bvar l1 => cases eq; let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => cases eq; let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 =>
    cases eq; let .sort r1 := H2; cases l1.symm.trans r1
    exact ⟨_, VEnv.HasType.sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    cases eq; let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrExprS.const l1 l2 l3).wf henv hΔ.wf
  | app l1 l2 _ _ ih3 ih4 =>
    let .app eq1 eq2 := eq; let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ eq1 r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ eq2 r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    let .lam eq1 eq2 := eq; let ⟨_, l1⟩ := l1; let .lam _ r2 r3 := H2
    have hA := ih2 hΔ eq1 r2 |>.of_l henv hΔ.wf.toCtx l1
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) eq2 r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let .forallE eq1 eq2 := eq; let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ eq1 r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) eq2 r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    let .letE eq1 eq2 eq3 := eq; have hΓ := hΔ.wf.toCtx; let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) eq3 r4
    exact .vlet (ih3 hΔ eq2 r3 |>.of_l henv hΓ l1) (ih2 hΔ eq1 r2 |>.of_l henv hΓ hb)
  | lit _ _ ih1 => cases eq; let .lit _ r2 := H2; exact ih1 hΔ .rfl r2
  | mdata _ ih1 => let .mdata eq := eq; let .mdata r1 := H2; exact ih1 hΔ eq r1
  | proj _ l2 ih1 =>
    let .proj eq := eq; let .proj r1 _ := H2
    exact l2.proj_congr henv hΔ.wf.toCtx (ih1 hΔ eq r1)

theorem IsDefEqE.trExpr [VEnv.Injective]
    (henv : env.WF) (noBV : Δ.NoBV) (H1 : IsDefEqE env Us Δ r₁ r₂) (hΔ : Δ'.WF env Us.length)
    (W : Δ.BVLift Δ' dn 0 n 0) (hr : RelevantEq r₁ e₁) (he : TrExprS env Us Δ' e₁ e') :
    ∃ e₂, RelevantEq r₂ e₂ ∧ TrExpr env Us Δ' e₂ e' := by
  induction H1 generalizing e₁ Δ' e' dn n with
  | rfl => exact ⟨_, hr, he.trExpr henv hΔ⟩
  | trans _ _ ih1 ih2 =>
    let ⟨em, a1, _, a2, a3⟩ := ih1 hΔ W hr he
    have ⟨_, b1, b2⟩ := ih2 hΔ W a1 a2
    exact ⟨_, b1, b2.defeq henv hΔ a3⟩
  | defeq h1 h2 =>
    have h1' := h1.weakBV henv W; have h2' := h2.weakBV henv W
    rw [Expr.liftLooseBVars_eq_self (noBV ▸ h1.closed.looseBVarRange_le)] at h1'
    rw [Expr.liftLooseBVars_eq_self (noBV ▸ h2.closed.looseBVarRange_le)] at h2'
    exact ⟨_, .rfl, h2'.defeq henv hΔ (hr.uniq henv (.refl henv hΔ) h1' he)⟩
  | app _ _ ih1 ih2 =>
    let .app hr1 hr2 := hr; let .app a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a3
    let ⟨_, c1, c2⟩ := ih2 hΔ W hr2 a4
    exact ⟨_, .app b1 c1, .app henv hΔ.toCtx a1 a2 b2 c2⟩
  | lam _ _ ih1 ih2 =>
    let .lam hr1 hr2 := hr; let .lam a1 a2 a3 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a2
    let ⟨_, c1, c2⟩ := ih2 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr2 a3
    exact ⟨_, .lam b1 c1, .lam (name := default) (bi := default) henv hΔ a1 b2 c2⟩
  | forallE _ _ ih1 ih2 =>
    let .forallE hr1 hr2 := hr; let .forallE a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a3
    let ⟨_, c1, c2⟩ := ih2 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr2 a4
    exact ⟨_, .forallE b1 c1, .forallE (name := default) (bi := default) henv hΔ a1 a2 b2 c2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    let .letE hr1 hr2 hr3 := hr; let .letE a1 a2 a3 a4 := he
    let ⟨_, b1, b2⟩ := ih1 hΔ W hr1 a2
    let ⟨_, c1, c2⟩ := ih2 hΔ W hr2 a3
    let ⟨_, d1, d2⟩ := ih3 (by exact ⟨hΔ, nofun, a1⟩) (.skip _ W) hr3 a4
    exact ⟨_, .letE b1 c1 d1, .letE (name := default) (nd := default) henv hΔ a1 b2 c2 d2⟩
  | mdata _ ih =>
    let .mdata hr := hr; let .mdata a1 := he; let ⟨_, b1, b2⟩ := ih hΔ W hr a1
    exact ⟨_, .mdata b1, .mdata (d := default) b2⟩
  | proj _ ih =>
    let .proj hr := hr; let .proj a1 a2 := he
    have ⟨_, b1, b2⟩ := ih hΔ W hr a1
    exact ⟨_, .proj b1, .proj henv hΔ b2 a2⟩

theorem IsDefEqE.uniq [VEnv.Injective] (henv : env.WF) (noBV : Δ.NoBV) (hΔ : Δ.WF env Us.length)
    (he₁ : TrExprS env Us Δ e₁ e₁') (he₂ : TrExprS env Us Δ e₂ e₂')
    (eq : IsDefEqE env Us Δ e₁ e₂) : env.IsDefEqU Us.length Δ.toCtx e₁' e₂' := by
  have ⟨_, a1, _, a2, a3⟩ := eq.trExpr henv noBV hΔ .refl .rfl he₁
  exact .symm <| a1.uniq henv (.refl henv hΔ) he₂ a2 |>.trans henv hΔ a3

end EquivManager

namespace ScopedEquivManager

variable {env : VEnv} {Us : List Name}

/-- The equivalences of a chain of contexts are a relation the scoped union-find can answer
queries by. -/
theorem Chain.erel (henv : env.WF) (H : Chain env Us Γ c) : ERel (ChainE env Us Γ c) where
  beq h _ := .relevant (.of_eqv h)
  symm h hc := (h hc).symm
  trans h1 h2 := fun hc => by
    have a1 := ChainE.mono henv H (Nat.le_max_left ..) h1 hc
    have a2 := ChainE.mono henv H (Nat.le_max_right ..) h2 hc
    exact a1.trans a2
  mono h h1 := ChainE.mono henv H h h1
  app h1 h2 := fun hc =>
    .app (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  lam h1 h2 := fun hc =>
    .lam (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  forallE h1 h2 := fun hc =>
    .forallE (ChainE.mono henv H (Nat.le_max_left ..) h1 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h2 hc)
  letE h1 h2 h3 := fun hc =>
    .letE (ChainE.mono henv H (by omega) h1 hc) (ChainE.mono henv H (by omega) h2 hc)
      (ChainE.mono henv H (Nat.le_max_right ..) h3 hc)
  mdata h := fun hc => .mdata (h hc)
  proj h := fun hc => .proj (h hc)

end ScopedEquivManager

namespace TypeChecker.Inner

/-- The equivalences of one context, at every level. -/
theorem IsDefEqE.erel (env : VEnv) (Us : List Name) (Δ : VLCtx) :
    ScopedEquivManager.ERel fun _ => EquivManager.IsDefEqE env Us Δ where
  beq h := .relevant (.of_eqv h)
  symm h := h.symm
  trans h1 h2 := h1.trans h2
  mono _ h := h
  app h1 h2 := .app h1 h2
  lam h1 h2 := .lam h1 h2
  forallE h1 h2 := .forallE h1 h2
  letE h1 h2 h3 := .letE h1 h2 h3
  mdata h := .mdata h
  proj h := .proj h

theorem RecM.WF.withTaint {c : VContext} {s : VState} {x : RecM α} {Q : α → VState → Prop}
    (h : x.WF c ⟨{ s.toState with taint := 0 }⟩ Q)
    (hQ : ∀ a (s₁ s₂ : VState), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    (TypeChecker.withTaint x).WF c s fun p s' => Q p.1 s' := by
  intro m mwf wf a s' e
  unfold TypeChecker.withTaint at e
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure, Except.pure,
    StateT.pure, ReaderT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at e
  split at e <;> [cases e; skip]
  rename_i v e₁
  obtain ⟨b, s₁⟩ := v
  cases e
  obtain ⟨vs₁, h1, h2, h3, h4⟩ := h m mwf (wf.setTaint 0) _ _ e₁
  subst h1
  exact ⟨⟨{ vs₁.toState with taint := max s.taint vs₁.taint }⟩, rfl, h2,
    h3.setTaint _, hQ b vs₁ _ rfl h4⟩

/-- What a recorded equivalence of `e₁` and `e₂` asserts in a context, as a fact learned. -/
def PairFact (env : VEnv) (Us : List Name) (e₁ e₂ : Lean.Expr) (m : MLCtx) : Prop :=
  ∀ t' u', TrExprS env Us m.vlctx e₁ t' → TrExprS env Us m.vlctx e₂ u' →
    EquivManager.IsDefEqE env Us m.vlctx e₁ e₂

theorem PairFact.eqv {e₁ e₂ k₁ k₂ : Lean.Expr} (H : PairFact env Us e₁ e₂ m)
    (h₁ : (e₁ == k₁) = true) (h₂ : (e₂ == k₂) = true) :
    PairClaim env Us (k₁, k₂) v m := fun t' u' ht hu => by
  have ht' := ht.eqv (by rwa [BEq.comm] at h₁)
  have hu' := hu.eqv (by rwa [BEq.comm] at h₂)
  exact (EquivManager.IsDefEqE.relevant (.of_eqv h₁)).symm.trans (H t' u' ht' hu') |>.trans
    (.relevant (.of_eqv h₂))

theorem _root_.Lean4Lean.TypeChecker.VState.WF.labelId_le {c : VContext} {s : VState}
    (wf : s.WF c) (l : Nat) : s.scopeIds.labelId l ≤ s.ngen.idx := by
  rcases ScopedEquivManager.Scopes.labelId_mem s.scopeIds l with h | h
  · rw [h]; exact Nat.zero_le _
  · exact (wf.ids_wf _ h).2

theorem _root_.Lean4Lean.TypeChecker.State.recordEquiv_eq (st : State) (t u : Lean.Expr)
    (l : Nat) : ∃ lab, l ≤ lab ∧ st.recordEquiv t u l =
      { st with
        eqvPairs := st.eqvPairs.insert (t, u) (lab, st.scopeIds.labelId lab)
        eqvManager := ((ScopedEquivManager.addEquiv st.scopeIds (fun _ => 0) t u
          st.scopeIds.size).run st.eqvManager).2 } := ⟨l, Nat.le_refl _, rfl⟩

theorem recordEquiv.WF [VEnv.Injective] {c : VContext} {s : VState} (he₁ : c.TrExprS e₁ e') (he₂ : c.TrExpr e₂ e')
    (hL : ∀ lab, l ≤ lab → lab ≤ s.scopeIds.size → c.ceiling.all (lab ≤ ·) →
      Learned c.venv c.lparams (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab) c.lctx s.ngen
        (PairFact c.venv c.lparams e₁ e₂)) :
    RecM.WF c s (modify (·.recordEquiv e₁ e₂ l)) fun _ _ => True := by
  rintro _ mwf wf _ _ ⟨⟩
  obtain ⟨lab, hlab, hr⟩ := State.recordEquiv_eq s.toState e₁ e₂ l
  dsimp only; rw [hr]
  have hE := ScopedEquivManager.Chain.erel c.Ewf (ScopeShape.chain wf.shape)
  have hd : EquivManager.IsDefEqE c.venv c.lparams c.vlctx e₁ e₂ := .defeq he₁ he₂
  have hd' : s.LinkE c s.scopeIds.size e₁ e₂ := fun hc' => by
    cases hce : c.ceiling with
    | some lab => rw [hce] at hc'; have := wf.ceil_lt lab hce; simp at hc'; omega
    | none =>
      show EquivManager.IsDefEqE _ _
        (levelCtx c.mlctx s.scopeFV none c.top s.scopeIds.size).vlctx e₁ e₂
      rw [← wf.fv_size, levelCtx_size]; exact hd
  refine ⟨⟨_⟩, rfl, .rfl,
    { wf with supp := wf.supp.setAux rfl rfl rfl rfl rfl rfl, ectx := ?_, pairs_wf := ?_,
              ids_made := ⟨wf.ids_made.1.insert (wf.labelId_le _), wf.ids_made.2⟩ }, trivial⟩
  · generalize hr : (ScopedEquivManager.addEquiv s.scopeIds (fun _ => 0) e₁ e₂
      s.scopeIds.size).run s.eqvManager = r
    obtain ⟨⟨⟩, m'⟩ := r
    exact (ScopedEquivManager.addEquiv.SWF hE hd' wf.ectx _ _ hr).1
  · refine wf.pairs_wf.insert fun k' hk hval hc => ?_
    refine ⟨c.lctx, s.ngen, Lean.NameGenerator.LE.rfl, Keeps.refl _ _, Admits.refl _ _, ?_⟩
    have H := hL _ hlab (le_of_valid hval) hc
    simp only [BEq.beq, Bool.and_eq_true] at hk
    exact fun m wfm hb ha => (H m wfm hb ha).eqv hk.1 hk.2

theorem isDefEq.WF [VEnv.Injective] {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  have hd₁ := c.mlctx_wf.dom_of_tr he₁; have hd₂ := c.mlctx_wf.dom_of_tr he₂
  rw [c.lctx_eq] at hd₁ hd₂
  refine (RecM.WF.withTaintLearn (D := fun fv => fv ∈ e₁.fvarsList ∨ fv ∈ e₂.fvarsList)
    (Pre := fun m => (∃ t', TrExprS c.venv c.lparams m.vlctx e₁ t') ∧
      ∃ u', TrExprS c.venv c.lparams m.vlctx e₂ u')
    (P := fun b m => b = true → EquivManager.IsDefEqE c.venv c.lparams m.vlctx e₁ e₂)
    (fun fv h => h.elim (hd₁ fv) (hd₂ fv))
    (fun m hm S c₂ hA hS hD hl hc => isDefEqCore.SS hA hS hd₁ hd₂
      (Lean.Expr.suppIn_of_fvars (fun fv h => hD fv (.inl h)) hl hc)
      (Lean.Expr.suppIn_of_fvars (fun fv h => hD fv (.inr h)) hl hc) m hm |>.mono
        fun _ _ _ _ => (trivial : True))
    (fun c₂ hv _ hl ⟨⟨t', ht⟩, ⟨u', hu⟩⟩ _ => by
      rw [← hv, ← hl] at ht hu ⊢
      exact (isDefEqCore.WF ht hu).mono fun b _ _ h hb => .defeq ht ⟨_, hu, (h hb).symm⟩)
    (isDefEqCore.WF he₁ he₂)).bind fun p s' le ⟨hb, _, hL⟩ => ?_
  obtain ⟨b, l⟩ := p
  simp; split
  · refine (recordEquiv.WF he₁ ⟨_, he₂, (hb ‹_›).symm⟩ fun lab h1 h2 h3 => ?_).map
      fun _ _ _ _ => hb
    rw [le.2.1] at h2; rw [le.2.2]
    have H := hL lab h1 h2 h3
    exact fun m wfm hbm ha t' u' ht hu =>
      H m wfm hbm ha (fun fv h => h.elim (wfm.dom_of_tr ht fv) (wfm.dom_of_tr hu fv))
        ⟨⟨_, ht⟩, ⟨_, hu⟩⟩ ‹_›
  · exact .pure hb

import Lean4Lean.Verify.TypeChecker.Scoped

/-!
# Learning by running again

A computation's result is cached at the level of the facts it used. To show the cached fact holds
in every context extending that level's context, the computation is run again there, with the
facts of the deeper scopes set aside: it runs the same way (`M.Sim`), and its own correctness
proof applies in the new context.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- What the support proofs keep of the state carries over to a context admitting `c`. -/
theorem _root_.Lean4Lean.SuppState.transfer {c c₂ : Context} {s : State} {g : NameGenerator}
    (wf : SuppState c s) (ha : Admits c.lctx g c₂.lctx) (hg : s.ngen ≤ g)
    (hk : Keeps c.lctx s.ngen g) (hwf₂ : c₂.lctx.WF) (hws₂ : c₂.lctx.WellScoped)
    (henv : c₂.env = c.env) : SuppState c₂ s := by
  have tr {e r} (h : CondSupp c s.ngen e r) : CondSupp c₂ s.ngen e r := by
    refine ⟨fun x hx => ?_, fun S hS hd he => ?_⟩
    · rcases h.1 x hx with h' | h'
      · exact .inl h'
      · by_cases hr : s.ngen.Reserves x
        · exact .inl hr
        · exact .inr (ha.keep x h' (hk x h' hr))
    · have hdc : ∀ x ∈ e.fvarsList, c.lctx.Dom x := fun x hx => by
        rcases h.1 x hx with h' | h'
        · obtain ⟨d, hd'⟩ := Option.isSome_iff_exists.1 (hd x hx)
          obtain ⟨d', h1, -⟩ := ha.find? hd' (.inl (h'.mono hg))
          simp [LocalContext.Dom, h1]
        · exact h'
      let D : FVarId → Prop := fun x => c₂.lctx.Dom x ∧ (g.Reserves x ∨ c.lctx.Dom x)
      have hS' : Supp.Closed ⟨fun x => S.fv x ∧ D x, S.lvl, S.const⟩ c := by
        refine ⟨fun x d ⟨h1, h2, h3⟩ hx => ?_, ?_⟩
        · obtain ⟨d₂, hd₂⟩ := Option.isSome_iff_exists.1 h2
          have e := ha.agree x d₂ hd₂ h3
          rw [hx] at e
          obtain ⟨et, ev⟩ := LocalDecl.erase_type (Option.some.inj e)
          obtain ⟨a1, a2⟩ := hS.1 x d₂ h1 hd₂
          obtain ⟨s1, s2⟩ := wf.wellScoped x d hx
          obtain ⟨t1, t2⟩ := hws₂ x d₂ hd₂
          rw [← et] at a1 t1; rw [← ev] at a2 t2
          exact ⟨a1.restrict fun y hy => ⟨t1 y hy, .inr (s1 y hy)⟩,
            a2.restrict fun y hy => ⟨t2 y hy, .inr (s2 y hy)⟩⟩
        · rw [← henv]; exact ⟨fun n ci h1 h2 => hS.2.find n ci h1 h2, hS.2.nat, hS.2.bool, hS.2.dummy⟩
      have he' : e.SuppIn ⟨fun x => S.fv x ∧ D x, S.lvl, S.const⟩ :=
        he.restrict fun x hx => ⟨hd x hx, .inr (hdc x hx)⟩
      exact (h.2 _ hS' hdc he').mono restrict_le
  exact ⟨hwf₂, hws₂, henv ▸ wf.envClosed, fun e r h => tr (wf.inferTypeI e r h),
    fun e r h => tr (wf.inferTypeC e r h), fun e r h => tr (wf.whnfCore e r h),
    fun e r h => tr (wf.whnf e r h), fun e r h S hS => wf.unfold e r h S (henv ▸ hS)⟩

theorem _root_.Lean.Expr.suppIn_of_fvars {T : Supp} {e : Expr}
    (hfv : ∀ fv ∈ e.fvarsList, T.fv fv) (hl : ∀ n, T.lvl n) (hc : ∀ n, T.const n) :
    e.SuppIn T :=
  Expr.SuppIn.mono (S := ⟨T.fv, fun _ => True, fun _ => True⟩) (S' := T)
    ⟨fun _ h => h, fun n _ => hl n, fun n _ => hc n⟩ (Expr.suppIn_fvars.2 hfv)

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.dom_of_tr {m : MLCtx} (wf : m.WF env Us)
    {e : Expr} {e' : VExpr} (h : TrExprS env Us m.vlctx e e') : ∀ fv ∈ e.fvarsList, m.lctx.Dom fv := by
  intro y hy
  have := (fvarsIn_iff.1 h.fvarsIn).1 y hy
  simpa [LocalContext.Dom, Option.isSome_iff_exists] using wf.tr.find?_eq_some.2 this

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.mem_of_dom {m : MLCtx} (wf : m.WF env Us)
    {fv : FVarId} (h : m.lctx.Dom fv) : fv ∈ m.vlctx.fvars :=
  wf.tr.find?_eq_some.1 (Option.isSome_iff_exists.1 h)

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.dom_of_mem {m : MLCtx} (wf : m.WF env Us)
    {fv : FVarId} (h : fv ∈ m.vlctx.fvars) : m.lctx.Dom fv := by
  simpa [LocalContext.Dom, Option.isSome_iff_exists] using wf.tr.find?_eq_some.2 h

/-- The context a computation run in `c` is run again in: `m`, with the ceiling `ceil`. -/
def VContext.rerun (c : VContext) (m : MLCtx) (wf : m.WF c.venv c.lparams) (ceil : Option Nat) :
    VContext :=
  { c with mlctx := m, mlctx_wf := wf, lctx := m.lctx, lctx_eq := rfl, ceiling := ceil, top := m }

/-- The ceiling of a run again for a fact at level `lab`, with `size` scopes open: the levels
above `lab`, unless `lab` is the current one. -/
def rerunCeil (lab size : Nat) : Option Nat := if lab < size then some lab else none

/-- A well-formed state stays so in a context a computation is run again in, for a fact at level
`lab`: one extending the level-`lab` context, admitting `c`, with the levels above `lab` set
aside. -/
theorem VState.WF.transfer [VEnv.Injective] {c : VContext} {s : VState} {g : NameGenerator} {lab : Nat}
    {m : MLCtx} (wf : s.WF c) (wf₂ : m.WF c.venv c.lparams)
    (hvis : c.ceiling.all (lab ≤ ·)) (hlab : lab ≤ s.scopeIds.size)
    (hb : (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab).Below m)
    (ha : Admits c.lctx g m.lctx) (hg : s.ngen ≤ g) (hk : Keeps c.lctx s.ngen g) :
    s.WF (c.rerun m wf₂ (rerunCeil lab s.scopeIds.size)) := by
  obtain ⟨hS₂, htop, hvis₂, hcut, hc₂, hcl⟩ :
      ScopeShape m s.scopeFV (rerunCeil lab s.scopeIds.size) m ∧
      (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab).Below
        (levelCtx m s.scopeFV (rerunCeil lab s.scopeIds.size) m lab) ∧
      (∀ l, l < lab → (rerunCeil lab s.scopeIds.size).all (l < ·)) ∧
      (∀ l, l ≤ s.scopeIds.size → lab < l → (rerunCeil lab s.scopeIds.size).all (l ≤ ·) = false) ∧
      (rerunCeil lab s.scopeIds.size = some lab ∨
        rerunCeil lab s.scopeIds.size = none ∧ c.ceiling = none ∧ lab = s.scopeIds.size) ∧
      (∀ lab', rerunCeil lab s.scopeIds.size = some lab' → lab' < s.scopeIds.size) := by
    by_cases hlt : lab < s.scopeIds.size
    · have e : rerunCeil lab s.scopeIds.size = some lab := if_pos hlt
      rw [e]
      have hl : levelCtx m s.scopeFV (some lab) m lab = m := levelCtx_top (by simp)
      refine ⟨ScopeShape.rerun wf.shape c.mlctx_wf wf₂ (wf.fv_size ▸ hlt) hvis hb, by rw [hl]; exact hb,
        fun l h => by simpa using h, fun l _ h => by simp; omega, .inl rfl,
        fun _ h => by cases h; exact hlt⟩
    · have e : rerunCeil lab s.scopeIds.size = none := if_neg hlt
      have hl : lab = s.scopeIds.size := by omega
      have hcn : c.ceiling = none := by
        cases h : c.ceiling with
        | none => rfl
        | some cl => have := wf.ceil_lt cl h; rw [h] at hvis; simp at hvis; omega
      rw [e]; subst hl
      have a3 : levelCtx c.mlctx s.scopeFV c.ceiling c.top s.scopeIds.size = c.mlctx := by
        rw [hcn, ← wf.fv_size, levelCtx_size]
      have hS := wf.shape; rw [hcn] at hS
      refine ⟨ScopeShape.above hS wf₂ (a3 ▸ hb), ?_, fun _ _ => rfl, fun l h1 h2 => by omega,
        .inr ⟨rfl, hcn, rfl⟩, nofun⟩
      rw [a3, ← wf.fv_size, levelCtx_size]; exact a3 ▸ hb
  have tr {κ ν : Type} [BEq κ] [Hashable κ] {cache : Std.HashMap κ ν} {lab' P}
      (H : LabHolds c s.toState cache lab' P) :
      LabHolds (c.rerun m wf₂ (rerunCeil lab s.scopeIds.size)) s.toState cache lab' P :=
    H.transfer wf.shape hvis rfl rfl hb htop hvis₂ hcut ha hg hk
  exact {
    trctx := (c.rerun m wf₂ _).trlctx
    supp := wf.supp.transfer (c₂ := (c.rerun m wf₂ _).toContext) ha hg hk wf₂.tr.1
      (wf₂.wellScoped c.Ewf) rfl
    ectx := wf.ectx_transfer hS₂ hvis rfl rfl hb htop hvis₂ hc₂
    ids_wf := wf.ids_wf
    pairs_wf := tr wf.pairs_wf
    inferTypeI_wf := tr wf.inferTypeI_wf
    inferTypeC_wf := tr wf.inferTypeC_wf
    whnfCore_wf := tr wf.whnfCore_wf
    whnf_wf := tr wf.whnf_wf
    ids_made := wf.ids_made
    unfold_wf := wf.unfold_wf
    shape := hS₂
    fv_size := wf.fv_size
    ceil_lt := hcl }

/-- A ceiling for a fact at level `lab` sets aside no more than `c` does, if `c` keeps `lab`. -/
theorem rerunCeil_le {c : VContext} {s : VState} (wf : s.WF c) {lab : Nat}
    (hvis : c.ceiling.all (lab ≤ ·)) (l : Nat)
    (h : (rerunCeil lab s.scopeIds.size).all (l ≤ ·)) : c.ceiling.all (l ≤ ·) := by
  unfold rerunCeil at h
  split at h
  · simp at h
    cases e : c.ceiling with
    | none => rfl
    | some cl => rw [e] at hvis; simp at hvis ⊢; omega
  · cases e : c.ceiling with
    | none => rfl
    | some cl => have := wf.ceil_lt cl e; rw [e] at hvis; simp at hvis; omega

/-- `withTaint x` learns what `x` establishes of its result: at every level from the level of the
facts it used up, in every context extending that level's context that admits the current one,
where `x`'s input lives (`D`) and its precondition holds (`Pre`). -/
theorem RecM.WF.withTaintLearn [VEnv.Injective] {c : VContext} {s : VState} {x : RecM α} {Q : α → VState → Prop}
    {D : FVarId → Prop} {Pre : MLCtx → Prop} {P : α → MLCtx → Prop} {R : α → Prop}
    (hDc : ∀ fv, D fv → c.lctx.Dom fv)
    (hss : ∀ m : Methods, m.SS → ∀ (S : Supp) (c₂ : Context), Agree S c.toContext c₂ →
      S.Closed c.toContext → (∀ fv, D fv → S.fv fv) → (∀ n, S.lvl n) → (∀ n, S.const n) →
      M.SS c.toContext c₂ { s.toState with taint := 0 } (x m) (x m) fun a _ => R a)
    (hwf : ∀ c₂ : VContext, c₂.venv = c.venv → c₂.env = c.env → c₂.lparams = c.lparams →
      Pre c₂.mlctx → (∀ fv, D fv → c₂.lctx.Dom fv) →
      RecM.WF c₂ ⟨{ s.toState with taint := 0 }⟩ x fun a _ => P a c₂.mlctx)
    (h : x.WF c ⟨{ s.toState with taint := 0 }⟩ Q)
    (hQ : ∀ a (s₁ s₂ : VState), s₁.ngen = s₂.ngen → Q a s₁ → Q a s₂ := by
      intro _ _ _ _ h; exact h) :
    (withTaint x).WF c s fun p s' => Q p.1 s' ∧ R p.1 ∧
      ∀ lab, p.2 ≤ lab → lab ≤ s.scopeIds.size → c.ceiling.all (lab ≤ ·) →
        Learned c.venv c.lparams (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab) c.lctx s'.ngen
          fun m => (∀ fv, D fv → m.lctx.Dom fv) → Pre m → P p.1 m := by
  intro m mwf wf a s' e
  obtain ⟨b, s₁, e₁, rfl, rfl⟩ := withTaint_run e
  have wf₀ := wf.setTaint 0
  obtain ⟨vs₁, h1, h2, h3, h4⟩ := h m mwf wf₀ _ _ e₁
  subst h1
  have hS₀ := hss m mwf.ss (Supp.dom c.toContext) c.toContext
    (Agree.refl wf.supp.lctxWF) wf.supp.closedDom hDc (fun _ => trivial) (fun _ => trivial)
  obtain ⟨-, hgle, hmo, hR⟩ := hS₀.1 wf₀.supp _ _ e₁
  refine ⟨⟨{ vs₁.toState with taint := max s.taint vs₁.taint }⟩, rfl, h2,
    h3.setTaint _, hQ b vs₁ _ rfl h4, hR, ?_⟩
  intro lab hlab hle hvis
  refine Learned.of_rerun (s₀ := ⟨{ s.toState with taint := 0 }⟩)
    (s₁ := vs₁.toState) (a := b) e₁ wf₀.supp hDc
    (fun S c₂ hA hS hD hl hc => (hss m mwf.ss S c₂ hA hS hD hl hc).2)
    fun m₂ wfm hb ha hD hpre => ?_
  refine ⟨c.rerun m₂ wfm (rerunCeil lab s.scopeIds.size), rfl, rfl, rfl, rfl, rfl, rfl,
    rerunCeil_le wf hvis, fun lab' hl => ?_,
    wf₀.transfer wfm hvis hle hb ha hgle hmo.keeps,
    hwf (c.rerun m₂ wfm (rerunCeil lab s.scopeIds.size)) rfl rfl rfl hpre hD m mwf⟩
  unfold rerunCeil at hl
  split at hl
  · cases hl; exact ⟨hlab, by assumption⟩
  · cases hl

theorem _root_.Lean4Lean.TypeChecker.State.cached?_spec {s : State} {ceil : Option Nat}
    {o : Option Cached} {r : Expr} {l : Nat} (h : s.cached? ceil o = some (r, l)) :
    ∃ id, o = some ⟨r, l, id⟩ ∧ s.scopeIds.valid l id = true ∧ ceil.all (l ≤ ·) := by
  unfold State.cached? at h
  split at h
  · split at h
    · rename_i hc; cases h; simp only [Bool.and_eq_true] at hc; exact ⟨_, rfl, hc.1, hc.2⟩
    · cases h
  · cases h

theorem _root_.Lean4Lean.TypeChecker.State.keyLabel_eq (s : State) (t : Nat) :
    ∃ l, t ≤ l ∧ s.keyLabel t = (l, s.scopeIds.labelId l) := ⟨t, Nat.le_refl _, rfl⟩

end Lean4Lean.TypeChecker

import Lean4Lean.Verify.Environment.Inductive

/-!
# Verifying `addInductive` on a block without nested occurrences

`Environment.addInductive` on a flat block is `AddInductive.run`, whose phases are verified one at
a time against the model of `Lean4Lean.Verify.Environment.AddInductive`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace TypeChecker

/-- `m` is a telescope of local declarations over the empty context: the variables `fvs` of types
`tys`, outermost first. -/
inductive MLCtx.IsTele : MLCtx → List FVarId → List VExpr → Prop
  | nil : MLCtx.IsTele .nil [] []
  | vlam {m fvs tys fv name ty ty' bi} : MLCtx.IsTele m fvs tys →
    MLCtx.IsTele (.vlam fv name ty ty' bi m) (fvs ++ [fv]) (tys ++ [ty'])

theorem _root_.Lean4Lean.VEnv.IsTele.snoc {env : VEnv} {U : Nat} {A : VExpr} :
    ∀ {Γ As}, env.IsTele U Γ As → env.IsType U (As.reverse ++ Γ) A → env.IsTele U Γ (As ++ [A])
  | _, [], .nil, h => .cons (by simpa using h) .nil
  | _, _ :: _, .cons hB t, h => .cons hB (VEnv.IsTele.snoc t (by simpa using h))

theorem MLCtx.IsTele.toCtx {m : MLCtx} : m.IsTele fvs tys → m.vlctx.toCtx = tys.reverse
  | .nil => rfl
  | .vlam h => by simp [MLCtx.vlctx, VLCtx.toCtx, h.toCtx]

theorem MLCtx.IsTele.fvars {m : MLCtx} : m.IsTele fvs tys → m.vlctx.fvars = fvs.reverse
  | .nil => rfl
  | .vlam h => by simp [MLCtx.vlctx, h.fvars]

theorem MLCtx.IsTele.isTele {env : VEnv} {Us : List Name} {m : MLCtx} :
    m.IsTele fvs tys → m.WF env Us → env.IsTele Us.length [] tys
  | .nil, _ => .nil
  | .vlam h, ⟨h1, _, _, h4⟩ => (h.isTele h1).snoc (by simpa [h.toCtx] using h4)

theorem MLCtx.IsTele.length_eq {m : MLCtx} : m.IsTele fvs tys → fvs.length = tys.length
  | .nil => rfl
  | .vlam h => by simp [h.length_eq]

theorem MLCtx.IsTele.dropN' {m : MLCtx} (h : m.IsTele fvs tys) :
    ∀ k (hk : k ≤ tys.length), ∃ hk', (m.dropN k hk').IsTele
      (fvs.take (tys.length - k)) (tys.take (tys.length - k)) := by
  induction h with
  | nil => intro k hk; cases Nat.le_zero.1 hk; exact ⟨Nat.le_refl _, by simpa using IsTele.nil⟩
  | @vlam m fvs tys fv name ty ty' bi h ih =>
    have hl := h.length_eq
    intro k hk
    cases k with
    | zero =>
      refine ⟨Nat.zero_le _, ?_⟩
      rw [List.take_of_length_le (by simp [hl]), List.take_of_length_le (by simp)]
      exact h.vlam
    | succ k =>
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      obtain ⟨hk', h'⟩ := ih k (by omega)
      refine ⟨by simp [MLCtx.length] at hk' ⊢; omega, ?_⟩
      simp only [MLCtx.dropN, List.length_append, List.length_cons, List.length_nil]
      rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
      simpa [Nat.add_sub_add_right] using h'

theorem MLCtx.IsTele.dropN {m : MLCtx} {As Bs} (h : m.IsTele fvs (As ++ Bs)) :
    ∃ hk, (m.dropN Bs.length hk).IsTele (fvs.take As.length) As := by
  obtain ⟨hk, h'⟩ := h.dropN' Bs.length (by simp)
  exact ⟨hk, by simpa using h'⟩

end TypeChecker

/-! ### Strengthening past local variables an expression does not mention -/

theorem VLCtx.FVLift'.isFVarUpSet {Δs Δb : VLCtx} {dk : Nat} {ρ : Lift} {k : Nat}
    (W : VLCtx.FVLift' Δs Δb dk ρ k) (hdk : dk = 0) (hfv : Δb.FVWF) :
    IsFVarUpSet (· ∈ Δs.fvars) Δb := by
  induction W with
  | refl => exact .fvars hfv
  | skip_fvar fv d W ih =>
    obtain ⟨fv, deps⟩ := fv
    exact ⟨ih hdk hfv.1, fun h => absurd (W.fvars_sublist.subset h) (hfv.2 _ _ rfl).1⟩
  | cons_fvar fv d hd W ih =>
    obtain ⟨fv, deps⟩ := fv
    refine ⟨?_, fun _ x hx => List.mem_cons_of_mem _ (hd hx)⟩
    refine (IsFVarUpSet.congr hfv.1 fun x hx => ?_).1 (ih hdk hfv.1)
    simp only [VLCtx.fvars_cons_some, List.mem_cons]
    refine ⟨.inr, fun h => h.resolve_left fun e => ?_⟩
    subst e; exact (hfv.2 _ _ rfl).1 hx
  | cons_bvar => cases hdk

theorem TrExprS.strengthen {env : VEnv} {Us : List Name} {Δs Δb : VLCtx} {ρ : Lift}
    (henv : VEnv.WF env) (W : VLCtx.FVLift' Δs Δb 0 ρ 0) (hΔb : Δb.WF env Us.length)
    (hbv : Δb.NoBV) {e eb} (H : TrExprS env Us Δb e eb) (hv : FVarsIn (· ∈ Δs.fvars) e) :
    ∃ es, TrExprS env Us Δs e es ∧ env.IsDefEqU Us.length Δb.toCtx eb (es.lift' ρ) := by
  have hc : Closed e 0 := by have := H.closed; rwa [hbv] at this
  obtain ⟨es, hs⟩ := H.weakFV'_inv henv W (.refl henv.ordered hΔb) hc hv
  have hs' := hs.weakFV' henv W hΔb
  simp only [Lift.consN] at hs'
  exact ⟨es, hs, H.uniq henv (.refl henv.ordered hΔb) hs'⟩

theorem TrExpr.strengthen {env : VEnv} {Us : List Name} {Δs Δb : VLCtx} {ρ : Lift}
    (henv : VEnv.WF env) (W : VLCtx.FVLift' Δs Δb 0 ρ 0) (hΔb : Δb.WF env Us.length)
    (hbv : Δb.NoBV) {e V} (H : TrExpr env Us Δb e (V.lift' ρ)) (hv : FVarsIn (· ∈ Δs.fvars) e) :
    TrExpr env Us Δs e V := by
  obtain ⟨eb, H1, H2⟩ := H
  obtain ⟨es, hs, h⟩ := TrExprS.strengthen henv W hΔb hbv H1 hv
  have hW := W.toCtx; simp only [Lift.consN] at hW
  exact ⟨es, hs, (VEnv.IsDefEqU.weak'_iff henv hΔb.toCtx hW).1 (h.symm.trans henv hΔb.toCtx H2)⟩

theorem TypeChecker.MLCtx.fvlift_dropN : ∀ (m : TypeChecker.MLCtx) n hn,
    ∃ ρ, VLCtx.FVLift' (m.dropN n hn).vlctx m.vlctx 0 ρ 0
  | _, 0, _ => ⟨_, .refl⟩
  | .vlam .., n+1, h | .vlet .., n+1, h => by
    obtain ⟨_, W⟩ := fvlift_dropN _ n (Nat.le_of_succ_le_succ h)
    exact ⟨_, .skip_fvar _ _ W⟩

theorem TypeChecker.MLCtx.WF.find?_dropN_vlam {env : VEnv} {Us : List Name} :
    ∀ {m : TypeChecker.MLCtx} (_ : m.WF env Us) (n hn) {fv name ty ty' bi m'},
    m.dropN n hn = .vlam fv name ty ty' bi m' → ∃ d, m.lctx.find? fv = some d ∧ d.type = ty
  | .nil, _, 0, _, _, _, _, _, _, _, e => nomatch e
  | .vlet .., _, 0, _, _, _, _, _, _, _, e => nomatch e
  | .vlam .., wf, 0, _, _, _, _, _, _, _, rfl => by
    rw [wf.find?_eq]; simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, LocalDecl.type]
  | .vlam x _ _ _ _ m₁, wf, n+1, h, fv, _, _, _, _, _, e
  | .vlet x _ _ _ _ _ m₁, wf, n+1, h, fv, _, _, _, _, _, e => by
    obtain ⟨d, h1, h2⟩ := find?_dropN_vlam wf.1 n (Nat.le_of_succ_le_succ h) e
    have hfv : fv ∈ m₁.vlctx.fvars := by
      have := TypeChecker.MLCtx.dropN_fvars_subset (c := m₁) n (Nat.le_of_succ_le_succ h)
      have e' : m₁.dropN n (Nat.le_of_succ_le_succ h) = _ := e
      rw [e'] at this; exact this (by simp)
    have hx : x ≠ fv := fun h' => by
      subst h'; exact (wf.1.tr.find?_eq_none.1 wf.2.1) hfv
    refine ⟨d, ?_, h2⟩
    rw [wf.find?_eq, ← h1, wf.1.find?_eq]
    simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, Ne.symm hx]

theorem TypeChecker.MLCtx.dropN_congr {m : TypeChecker.MLCtx} {n n'} (e : n = n') (h h') :
    m.dropN n h = m.dropN n' h' := by subst e; rfl

theorem TypeChecker.MLCtx.dropN_of_eq {m m' : TypeChecker.MLCtx} (e : m = m') {n} (h h') :
    m.dropN n h = m'.dropN n h' := by subst e; rfl

theorem TypeChecker.MLCtx.length_dropN : ∀ (m : TypeChecker.MLCtx) n hn,
    (m.dropN n hn).length = m.length - n
  | _, 0, _ => rfl
  | .vlam .., n+1, h | .vlet .., n+1, h => by
    simp only [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.length]
    rw [length_dropN _ n]; omega

theorem TypeChecker.MLCtx.dropN_dropN : ∀ (m : TypeChecker.MLCtx) a b ha hb hab,
    (m.dropN a ha).dropN b hb = m.dropN (a + b) hab
  | _, 0, _, _, _, _ => by simp
  | .vlam .., a+1, b, _, hb, hab | .vlet .., a+1, b, _, hb, hab => by
    simp only [TypeChecker.MLCtx.dropN]
    rw [dropN_dropN _ a b _ hb (by simp only [TypeChecker.MLCtx.length] at hab; omega),
      dropN_congr (show a + 1 + b = (a + b) + 1 by omega) _ (by simpa [Nat.add_right_comm] using hab)]
    rfl

theorem TypeChecker.MLCtx.IsTele.snoc_inv {m : TypeChecker.MLCtx} {fvs fv tys ty'}
    (h : m.IsTele (fvs ++ [fv]) (tys ++ [ty'])) :
    ∃ name ty bi m', m = .vlam fv name ty ty' bi m' ∧ m'.IsTele fvs tys := by
  generalize hf : fvs ++ [fv] = F at h
  generalize ht : tys ++ [ty'] = T at h
  cases h with
  | nil => simp at hf
  | vlam h =>
    obtain ⟨rfl, h1⟩ := List.append_inj' hf rfl
    obtain ⟨rfl, h2⟩ := List.append_inj' ht rfl
    cases h1; cases h2
    exact ⟨_, _, _, _, rfl, h⟩

theorem TypeChecker.MLCtx.IsTele.dropN_all {m : TypeChecker.MLCtx} {fvs tys}
    (h : m.IsTele fvs tys) : ∃ hk, m.dropN tys.length hk = .nil := by
  obtain ⟨hk, h'⟩ := h.dropN' tys.length (Nat.le_refl _)
  refine ⟨hk, ?_⟩
  simp only [Nat.sub_self, List.take_zero] at h'
  generalize m.dropN tys.length hk = m' at h'
  generalize hF : ([] : List FVarId) = F at h'
  generalize hT : ([] : List VExpr) = T at h'
  cases h' with
  | nil => rfl
  | vlam => simp at hF


theorem VEnv.IsDefEq.foralls_congr {env : VEnv} {U : Nat} {e₁ e₂ : VExpr} :
    ∀ {Γ As u}, env.IsTele U Γ As → env.IsDefEq U (As.reverse ++ Γ) e₁ e₂ (.sort u) →
      ∃ v, env.IsDefEq U Γ (.foralls As e₁) (.foralls As e₂) (.sort v)
  | _, [], _, .nil, h => ⟨_, h⟩
  | _, _ :: _, _, .cons ⟨_, hA⟩ t, h =>
    let ⟨_, ih⟩ := VEnv.IsDefEq.foralls_congr t (by simpa using h)
    ⟨_, .forallEDF hA ih⟩

theorem List.Forall₂.getElem?_r {R : α → β → Prop} : ∀ {l₁ l₂} {j : Nat} {b : β},
    List.Forall₂ R l₁ l₂ → l₂[j]? = some b → ∃ a, l₁[j]? = some a ∧ R a b
  | _, _, _, _, .nil, e => by simp at e
  | _, _, 0, _, .cons h _, e => by cases e; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, j + 1, _, .cons _ t, e => List.Forall₂.getElem?_r (j := j) t (by simpa using e)

theorem List.Forall₂.getElem?_l {R : α → β → Prop} : ∀ {l₁ l₂} {j : Nat} {a : α},
    List.Forall₂ R l₁ l₂ → l₁[j]? = some a → ∃ b, l₂[j]? = some b ∧ R a b
  | _, _, _, _, .nil, e => by simp at e
  | _, _, 0, _, .cons h _, e => by cases e; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, j + 1, _, .cons _ t, e => List.Forall₂.getElem?_l (j := j) t (by simpa using e)

namespace VExpr

/-- The arguments of an application spine. -/
def appArgs : VExpr → List VExpr
  | .app f a => f.appArgs ++ [a]
  | _ => []

theorem appArgs_appN : ∀ (e : VExpr) (as : List VExpr), (e.appN as).appArgs = e.appArgs ++ as
  | _, [] => by simp
  | e, a :: as => by simp [appN, appArgs_appN (.app e a) as, appArgs]

theorem appN_const_inj {n n' : Name} {ls ls' : List VLevel} {as bs : List VExpr}
    (h : (VExpr.const n ls).appN as = (VExpr.const n' ls').appN bs) : as = bs := by
  simpa [appArgs_appN, appArgs] using congrArg appArgs h

/-- Not a pi. -/
def NotPi : VExpr → Prop
  | .forallE .. => False
  | _ => True

theorem appN_notPi : ∀ {e : VExpr} (as : List VExpr), e.NotPi → (e.appN as).NotPi
  | _, [], h => h
  | e, a :: as, _ => appN_notPi (e := .app e a) as trivial

theorem foralls_inj : ∀ {xs ys : List VExpr} {X Y : VExpr}, X.NotPi → Y.NotPi →
    foralls xs X = foralls ys Y → xs = ys ∧ X = Y
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hX, _, h => by simp at h; subst h; exact hX.elim
  | _ :: _, [], _, _, _, hY, h => by simp at h; subst h; exact hY.elim
  | _ :: _, _ :: _, _, _, hX, hY, h => by
    simp only [foralls_cons, forallE.injEq] at h
    have := foralls_inj hX hY h.2
    exact ⟨by rw [h.1, this.1], this.2⟩

end VExpr

theorem VEnv.TeleDefEq.length_eq {env : VEnv} {U : Nat} : ∀ {Γ As Bs},
    env.TeleDefEq U Γ As Bs → As.length = Bs.length
  | _, [], [], .nil => rfl
  | _, _ :: _, _ :: _, .cons _ h => congrArg (· + 1) h.length_eq

namespace VInductDecl
variable {d : VInductDecl} {venv : VEnv}

theorem Positive.defeqDFC (henv : venv.Ordered) {Γ₀ Γ₁ Γ₂}
    (hΓ : VEnv.IsDefEqCtx venv d.uvars Γ₀ Γ₁ Γ₂) {k t} (H : d.Positive venv Γ₁ k t) :
    d.Positive venv Γ₂ k t := by
  induction H generalizing Γ₂ with
  | none h hA => exact .none (h.defeqDFC henv hΓ) hA
  | pi h hA _ ih =>
    obtain ⟨_, h'⟩ := h
    obtain ⟨⟨_, hAu⟩, -⟩ := h'.hasType.2.forallE_inv henv
    exact .pi (VEnv.IsDefEqU.defeqDFC henv hΓ ⟨_, h'⟩) hA (ih (.succ hΓ hAu))
  | app hT hlen h his => exact .app hT hlen (h.defeqDFC henv hΓ) his

theorem Positive.defeq (henv : venv.WF) {Γ} (hΓ : OnCtx Γ (venv.IsType d.uvars)) {k t t'}
    (H : d.Positive venv Γ k t) (h : venv.IsDefEqU d.uvars Γ t t') : d.Positive venv Γ k t' := by
  cases H with
  | none h1 hA => exact .none (h.symm.trans henv hΓ h1) hA
  | pi h1 hA hB => exact .pi (h.symm.trans henv hΓ h1) hA hB
  | app hT hlen h1 his => exact .app hT hlen (h.symm.trans henv hΓ h1) his

end VInductDecl

theorem List.forall₂_of_getElem? {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ (j : Nat) a b, l₁[j]? = some a → l₂[j]? = some b → R a b) →
    List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, H =>
    .cons (H 0 a b rfl rfl) (List.forall₂_of_getElem? (by simpa using hl)
      fun j a b h₁ h₂ => H (j + 1) a b h₁ h₂)

theorem insertConsts_find?_none {cis : List ConstantInfo} {C : ConstMap} {name : Name}
    (hC : C.WF) (hfr : ∀ ci ∈ cis, C.find? ci.name = none) (hnd : (cis.map (·.name)).Nodup)
    (h : (insertConsts C cis).find? name = none) :
    C.find? name = none ∧ name ∉ cis.map (·.name) := by
  have hn : name ∉ cis.map (·.name) := by
    intro hm
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hci
    rw [insertConsts_append] at h
    simp only [List.map_append, List.map_cons] at hnd
    have hnd₁ := (List.nodup_append.1 hnd)
    have hC₁ := insertConsts_wf hC (fun c hc => hfr c (List.mem_append_left _ hc)) hnd₁.1
    have hfr₁ : (insertConsts C l₁).find? ci.name = none := by
      rw [insertConsts_find?_of_not_mem hC (fun c hc => hfr c (List.mem_append_left _ hc)) hnd₁.1
        fun hh => hnd₁.2.2 _ hh _ (.head _) rfl]
      exact hfr ci (List.mem_append_right _ (.head _))
    have hnd₂ := List.nodup_cons.1 hnd₁.2.1
    rw [show insertConsts (insertConsts C l₁) (ci :: l₂) =
      insertConsts ((insertConsts C l₁).insert ci.name ci) l₂ from rfl] at h
    have hC₂ := hC₁.insert ci.name ci hfr₁
    rw [insertConsts_find?_of_not_mem hC₂ (fun c hc => ?_) hnd₂.2 hnd₂.1, hC₁.find?_insert] at h
    · simp at h
    · rw [hC₁.find?_insert, if_neg]
      · rw [insertConsts_find?_of_not_mem hC (fun c hc => hfr c (List.mem_append_left _ hc)) hnd₁.1
          fun hh => hnd₁.2.2 _ hh _ (.tail _ (List.mem_map_of_mem hc)) rfl]
        exact hfr c (List.mem_append_right _ (.tail _ hc))
      · simp only [beq_iff_eq]; intro hh
        exact hnd₂.1 (by rw [hh]; exact List.mem_map_of_mem hc)
  exact ⟨by rwa [insertConsts_find?_of_not_mem hC hfr hnd hn] at h, hn⟩

namespace AddInductive
open TypeChecker

/-- The context `run` starts in: the environment, at the block's level, and no local context. -/
def VContext.top {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) (lparams : List Name) (allowPrimitive : Bool)
    (fuel : FuelConfig) : VContext where
  env; safety; lparams; allowPrimitive; fuel; venv
  envAt := wf
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl
  reserved := nofun
  notKernel := nofun
  pfx := by decide

/-- The parts of the context `checkInductiveTypes` keeps fixed. -/
structure SameBase (c₀ c : VContext) : Prop where
  env : c.env = c₀.env
  venv : c.venv = c₀.venv
  lparams : c.lparams = c₀.lparams
  safety : c.safety = c₀.safety
  allowPrimitive : c.allowPrimitive = c₀.allowPrimitive
  fuel : c.fuel = c₀.fuel
  pfx : c.ngen.namePrefix = c₀.ngen.namePrefix

protected theorem SameBase.refl {c : VContext} : SameBase c c :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem SameBase.push {c₀ c : VContext} (h : SameBase c₀ c) {name ty ty' bi h1 h2} :
    SameBase c₀ (c.push name ty ty' bi h1 h2) :=
  ⟨h.env, h.venv, h.lparams, h.safety, h.allowPrimitive, h.fuel, h.pfx⟩

/-- What `checkInductiveTypes` has established after its first `n` types, with `stats` in `c`:
the parameters are local variables of the types `params`, at the bottom of the local context;
each type so far is, up to defeq, a pi over the parameters and its indices into a sort that agrees
with `level`. -/
structure TypesSoFar (c₀ : VContext) (nparams : Nat) (types : List InductiveType) (n : Nat)
    (stats : InductiveStats) (c : VContext) (params : List VExpr) (level : VLevel)
    (typeTr : List VExpr) : Prop where
  base : SameBase c₀ c
  paramsCtx : ∃ k hk fvs, (c.mlctx.dropN k hk).IsTele fvs params ∧
    stats.params.toList = fvs.map .fvar
  nparams : params.length = nparams
  params_tele : c₀.venv.IsTele c₀.lparams.length [] params
  levels : stats.levels = c₀.lparams.map .param
  resultLevel : VLevel.ofLevel c₀.lparams stats.resultLevel = some level
  isNotZero : stats.isNotZero = stats.resultLevel.isNeverZero
  nindices : stats.nindices.size = n
  indConsts : stats.indConsts.toList = (types.take n).map fun T => .const T.name stats.levels
  typeTr_length : typeTr.length = n
  types : ∀ (j : Nat) (T : InductiveType) (T' : VExpr), types[j]? = some T → typeTr[j]? = some T' →
    ∃ idx u,
    TrExprS c₀.venv c₀.lparams [] T.type T' ∧ c₀.venv.IsType c₀.lparams.length [] T' ∧
    c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) (.sort u)) ∧
    u ≈ level ∧ stats.nindices[j]? = some idx.length ∧
    c₀.venv.IsTele c₀.lparams.length params.reverse idx

/-- What `checkInductiveTypes` establishes, for the continuation it calls. -/
abbrev TypesData (c₀ : VContext) (nparams : Nat) (types : List InductiveType) :=
  TypesSoFar c₀ nparams types types.length

/-- The first type's loop: each parameter and index becomes a local variable, of the type the
binder normalizes to with annotations stripped, and the type of the block is, up to defeq, a pi over
them into the remaining type. -/
theorem loopFirst.WF {c₀ : VContext} (henv : c₀.venv.WF) (hann : c₀.venv.AnnotationsErase)
    {nparams : Nat} {stats₀ : InductiveStats} (h₀ : stats₀.indConsts = #[]) {T' : VExpr}
    {k : Expr → InductiveStats → Nat → M α} {Q}
    (H : ∀ type V (c : VContext) fvs params idx, SameBase c₀ c →
      c.mlctx.IsTele fvs (params ++ idx) → params.length = nparams →
      TrExpr c.venv c.lparams c.mlctx.vlctx type V →
      c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) V) →
      WF c (k type { stats₀ with params := ((fvs.take nparams).map .fvar).toArray } idx.length) Q) :
    ∀ fuel type i nidx (c : VContext) fvs params idx V,
      SameBase c₀ c → c.mlctx.IsTele fvs (params ++ idx) →
      params.length = i → idx.length = nidx → (nidx ≠ 0 → i = nparams) → i ≤ nparams →
      TrExpr c.venv c.lparams c.mlctx.vlctx type V →
      c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) V) →
      WF c (checkInductiveTypes.loopInd.loop nparams
        { stats₀ with params := ((fvs.take i).map .fvar).toArray } type i nidx fuel k) Q := by
  intro fuel
  induction fuel with
  | zero => intros; rw [checkInductiveTypes.loopInd.loop.eq_1]; exact .throw
  | succ fuel ih =>
  intro type i nidx c fvs params idx V hc htele hi hn hni hle htr hT
  cases type with
  | forallE name dom body bi =>
    rw [checkInductiveTypes.loopInd.loop.eq_2]
    have henv' : c.venv.WF := hc.venv ▸ henv
    have hann' : c.venv.AnnotationsErase := hc.venv ▸ hann
    have hΔ := c.tc.Δwf
    have hΓ := hΔ.toCtx
    obtain ⟨V₀, hS, hdef⟩ := htr
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i dom' body'
    rw [Lean.Expr.consumeTypeAnnotations_eq]
    obtain ⟨ty', hty, hdefty⟩ := TrExprS.consumeTypeAnnotations' henv' hann' hΔ hdom
    have htyT : c.venv.IsType c.lparams.length c.mlctx.vlctx.toCtx ty' :=
      hdomT.defeqU_l henv' hΓ hdefty
    obtain ⟨u, hdomS⟩ := hdomT
    have hdomty := hdefty.of_l henv' hΓ hdomS
    have hΔeq : VLCtx.IsDefEq c.venv c.lparams.length
        ((none, .vlam dom') :: c.mlctx.vlctx) ((none, .vlam ty') :: c.mlctx.vlctx) :=
      .cons (VLCtx.IsDefEq.refl henv'.ordered hΔ) nofun (.vlam hdomty)
    obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv' hΔeq
    have hbodyeq := hbody.uniq henv' hΔeq hbody''
    -- the step both binder kinds take: open the binder, then normalize the body
    have step {stats' : InductiveStats} {i' nidx' : Nat} {params' idx' : List VExpr}
        (hstats : stats' = { stats₀ with
          params := (((fvs ++ [(⟨c.ngen.curr⟩ : FVarId)]).take i').map Expr.fvar).toArray })
        (hpi : params' ++ idx' = params ++ idx ++ [ty']) (hi' : params'.length = i')
        (hn' : idx'.length = nidx') (hni' : nidx' ≠ 0 → i' = nparams) (hle' : i' ≤ nparams) :
        AddInductive.WF (c.push name dom.consumeTypeAnnotations' ty' bi hty htyT)
          (do
            let e ← liftM (TypeChecker.whnf (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)))
            checkInductiveTypes.loopInd.loop nparams stats' e i' nidx' fuel k) Q := by
      let c' := c.push name dom.consumeTypeAnnotations' ty' bi hty htyT
      have hinst : c'.tc.TrExprS (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' := by
        rw [Lean.Expr.instantiate1_eq]
        exact hbody''.inst_fvar henv'.ordered c'.tc.Δwf
      refine AddInductive.WF.bind (AddInductive.WF.liftTC (TypeChecker.whnf.WF hinst))
        fun e ⟨_, he⟩ => ?_
      subst hstats
      refine ih e i' nidx' c' (fvs ++ [⟨c.ngen.curr⟩]) params' idx' body'' hc.push ?_ hi' hn' hni'
        hle' he ?_
      · rw [hpi]; exact htele.vlam
      · obtain ⟨v, hbodyS⟩ := hbodyT
        have h1 : c.venv.IsDefEq c.lparams.length c.mlctx.vlctx.toCtx
            (.forallE dom' body') (.forallE ty' body'') (.sort (.imax u v)) :=
          .forallEDF hdomty (hbodyeq.of_l henv' ⟨hΓ, _, hdomS⟩ hbodyS)
        have h2 := (hdef.of_l henv' hΓ h1.hasType.1).symm.trans h1
        change c.venv.IsDefEq c.lparams.length c.mlctx.vlctx.toCtx _ _ _ at h2
        rw [htele.toCtx] at h2
        obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr (htele.isTele c.mlctx_wf)
          (by simpa using h2)
        have h4 : c.venv.IsDefEqU c.lparams.length [] T'
            (.foralls (params ++ idx) (.forallE ty' body'')) :=
          (hc.venv ▸ hc.lparams ▸ hT).trans henv' trivial ⟨_, h3⟩
        rw [hpi, VExpr.foralls_append]
        simpa [hc.venv, hc.lparams] using h4
    have hlen : fvs.length = i + nidx := by simp [htele.length_eq, hi, hn]
    split
    · rename_i hlt
      have hn0 : nidx = 0 := Decidable.byContradiction fun h => absurd (hni h) (Nat.ne_of_lt hlt)
      subst hn0
      have hidx : idx = [] := List.eq_nil_of_length_eq_zero hn
      subst hidx
      rw [if_pos (by simp [h₀])]
      refine AddInductive.WF.withLocalDecl hty htyT ?_
      refine step (params' := params ++ [ty']) (idx' := []) ?_ (by simp) (by simp [hi]) rfl
        nofun hlt
      simp only [Nat.add_zero] at hlen
      simp [← hlen, List.take_of_length_le]
    · rename_i hlt
      have hi' : i = nparams := Nat.le_antisymm hle (Nat.not_lt.1 hlt)
      refine AddInductive.WF.withLocalDecl hty htyT ?_
      refine step (params' := params) (idx' := idx ++ [ty']) ?_ (by simp) hi (by simp [hn])
        (fun _ => hi') hle
      rw [List.take_append_of_le_length (by omega)]
  | _ =>
    rw [checkInductiveTypes.loopInd.loop.eq_3 _ _ _ _ _ _ _ fun _ _ _ _ h => by cases h]
    split
    · exact AddInductive.WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
    · rename_i hi'
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi'
      have hnp : params.length = nparams := hi.trans hi'
      have := H _ V c fvs params idx hc htele hnp htr hT
      rw [← hn]; subst hi; rwa [hnp]

theorem WF.read {c : VContext} : WF c (read : M Context) (· = c.toContext) := by
  rintro _ ⟨⟩; rfl

/-- The initial statistics. -/
abbrev initStats (c : VContext) : InductiveStats :=
  { (default : InductiveStats) with levels := c.lparams.map .param }

/-- The first type of the block. -/
theorem loopInd0.WF {c₀ : VContext} (h₀ : c₀.mlctx = .nil) (henv : c₀.venv.WF)
    (hann : c₀.venv.AnnotationsErase) {nparams : Nat} {types : List InductiveType}
    (hne : types ≠ []) {k : InductiveStats → M α} {Q}
    (H : ∀ stats c params level typeTr, TypesSoFar c₀ nparams types 1 stats c params level typeTr →
      WF c (checkInductiveTypes.loopInd nparams types.toArray k 1 stats) Q) :
    WF c₀ (checkInductiveTypes.loopInd nparams types.toArray k 0 (initStats c₀)) Q := by
  obtain ⟨T, types', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [checkInductiveTypes.loopInd.eq_1, dif_pos (by simp)]
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  refine WF.bind (WF.liftExcept (checkNoMVarNoFVar.WF _ _ _)) fun _ hcl => ?_
  have hcl' : T.type.FVarsIn (· ∈ c₀.tc.vlctx.fvars) := hcl.mono nofun
  refine WF.bind (WF.liftTC (TypeChecker.checkType.WF hcl')) fun _ hty => ?_
  obtain ⟨T', _, -, hT', -, -⟩ := hty
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  refine WF.bind (WF.liftTC (TypeChecker.whnf.WF hT')) fun e₁ ⟨_, he₁⟩ => ?_
  have hT'0 : TrExprS c₀.venv c₀.lparams [] T.type T' := by
    change TrExprS c₀.venv c₀.lparams c₀.mlctx.vlctx _ _ at hT'
    rw [h₀] at hT'; exact hT'
  have hnil : VLCtx.WF c₀.venv c₀.lparams.length ([] : VLCtx) := trivial
  refine loopFirst.WF henv hann (stats₀ := initStats c₀) rfl (T' := T') ?_ _ e₁ 0 0 c₀ [] [] []
    T' .refl (by rw [h₀]; exact .nil) rfl rfl nofun (Nat.zero_le _) he₁
    (by have := TrExprS.wf henv.ordered hnil hT'0; exact this)
  intro type V c fvs params idx hc htele hnp htr hT
  have henv' : c.venv.WF := hc.venv ▸ henv
  have hΓ : OnCtx c.mlctx.vlctx.toCtx (c.venv.IsType c.lparams.length) := c.tc.Δwf.toCtx
  obtain ⟨V₁, hS, hV⟩ := htr
  dsimp only
  refine WF.bind (WF.liftTC (TypeChecker.ensureSort.WF hS)) fun e ⟨⟨s', hs', hs'V⟩, u, he⟩ => ?_
  subst he
  cases hs' with | sort hu => ?_
  rename_i u'
  change VLevel.ofLevel c.lparams u = some u' at hu
  change c.venv.IsDefEqU c.lparams.length c.mlctx.vlctx.toCtx (.sort u') V₁ at hs'V
  rw [if_pos (show (default : InductiveStats).indConsts.isEmpty = true from rfl)]
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  refine H _ c params u' [T'] ⟨hc, ?_, hnp, ?_, rfl, ?_, rfl, rfl, ?_, rfl, ?_⟩
  · obtain ⟨hk, h⟩ := htele.dropN
    exact ⟨_, hk, _, h, by simp [hnp]⟩
  · have := (htele.isTele c.mlctx_wf).append_inv.1
    rwa [hc.venv, hc.lparams] at this
  · rw [hc.lparams] at hu; simpa [Expr.sortLevel!] using hu
  · simp; rfl
  · intro j T₀ T'₀ hT₀ hT'₀
    obtain ⟨rfl, hT'eq⟩ : j = 0 ∧ T'₀ = T' := by
      cases j <;> simp_all
    rw [hT'eq]
    obtain rfl : T₀ = T := by simpa using hT₀.symm
    have hsort : c.venv.IsDefEq c.lparams.length c.mlctx.vlctx.toCtx V (.sort u')
        (.sort (.succ u')) := by
      have h1 := hs'V.trans henv' hΓ hV
      have hu' : u'.WF c.lparams.length := .of_ofLevel hu
      exact (h1.of_l henv' hΓ (.sort hu')).symm
    rw [htele.toCtx] at hsort
    obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr (htele.isTele c.mlctx_wf) (by simpa using hsort)
    have hpi := (htele.isTele c.mlctx_wf).append_inv
    rw [hc.venv, hc.lparams] at h3
    have hdef : c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) (.sort u')) :=
      hT.trans henv trivial ⟨_, h3⟩
    refine ⟨idx, u', hT'0, ?_, hdef, VLevel.equiv_def.2 fun _ => rfl, ?_, ?_⟩
    · have htel : c₀.venv.IsTele c₀.lparams.length [] (params ++ idx) := by
        have := htele.isTele c.mlctx_wf; rwa [hc.venv, hc.lparams] at this
      have hu' : u'.WF c₀.lparams.length := .of_ofLevel (hc.lparams ▸ hu)
      exact (htel.foralls ⟨_, .sort hu'⟩).defeqU_l henv trivial hdef.symm
    · show (#[].push idx.length)[0]? = _; simp
    · simpa [hc.venv, hc.lparams] using hpi.2

theorem getType.WF {c : VContext} {fv : FVarId} {d : LocalDecl}
    (h : c.lctx.find? fv = some d) : WF c (getType (.fvar fv)) (· = d.type) := by
  rintro _ e
  simp only [getType, getLCtx, bind, ReaderT.bind, read, readThe, MonadReaderOf.read,
    ReaderT.read, pure, ReaderT.pure, Except.bind, Except.pure, LocalContext.get!, Expr.fvarId!,
    h] at e
  cases e; rfl

theorem loopLater.WF {c₀ : VContext} (henv : c₀.venv.WF) (hann : c₀.venv.AnnotationsErase)
    {nparams : Nat} {stats : InductiveStats} (hne : stats.indConsts.isEmpty = false)
    {Mp : MLCtx} {pfvs : List FVarId} {params : List VExpr} (hMp : Mp.IsTele pfvs params)
    (hpar : stats.params.toList = pfvs.map .fvar) (hnp : params.length = nparams)
    (hptele : c₀.venv.IsTele c₀.lparams.length [] params)
    {T' : VExpr} {k : Expr → InductiveStats → Nat → M α} {Q} {M₁ : MLCtx}
    (hM₁ : ∃ n hn, M₁.dropN n hn = Mp)
    (H : ∀ type V (c : VContext) (Δs : VLCtx) idx, SameBase c₀ c →
      (∃ hk, c.mlctx.dropN idx.length hk = M₁) →
      (∃ ρ, VLCtx.FVLift' Δs c.mlctx.vlctx 0 ρ 0) →
      Δs.toCtx = idx.reverse ++ params.reverse →
      c₀.venv.IsTele c₀.lparams.length [] (params ++ idx) →
      TrExpr c.venv c.lparams Δs type V →
      c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) V) →
      WF c (k type stats idx.length) Q) :
    ∀ fuel type i nidx (c : VContext) (Δs : VLCtx) idx V,
      SameBase c₀ c → (∃ hk, c.mlctx.dropN nidx hk = M₁) →
      (∃ ρ, VLCtx.FVLift' Δs c.mlctx.vlctx 0 ρ 0) →
      Δs.toCtx = idx.reverse ++ (params.take i).reverse →
      (nidx = 0 → ∃ hk, Δs = (Mp.dropN (nparams - i) hk).vlctx) →
      i ≤ nparams → idx.length = nidx → (nidx ≠ 0 → i = nparams) →
      c₀.venv.IsTele c₀.lparams.length [] (params.take i ++ idx) →
      TrExpr c.venv c.lparams Δs type V →
      c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params.take i ++ idx) V) →
      WF c (checkInductiveTypes.loopInd.loop nparams stats type i nidx fuel k) Q := by
  subst hnp
  intro fuel
  induction fuel with
  | zero => intros; rw [checkInductiveTypes.loopInd.loop.eq_1]; exact .throw
  | succ fuel ih =>
  intro type i nidx c Δs idx V hc hM hW hΔ hparam hle hn hni htele htr hT
  have henv' : c.venv.WF := hc.venv ▸ henv
  have hΔb := c.mlctx_wf.tr.wf
  obtain ⟨ρ, W⟩ := hW
  have hΔs : Δs.WF c.venv c.lparams.length := W.wf henv' hΔb
  have hΓ := hΔs.toCtx
  cases type with
  | forallE name dom body bi =>
    rw [checkInductiveTypes.loopInd.loop.eq_2]
    obtain ⟨V₀, hS, hdef⟩ := htr
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i dom' body'
    split
    · rename_i hlt
      have hn0 : nidx = 0 := Decidable.byContradiction fun h => absurd (hni h) (Nat.ne_of_lt hlt)
      subst hn0
      have hidx : idx = [] := List.eq_nil_of_length_eq_zero hn
      subst hidx
      rw [if_neg (by simp [hne])]
      have hlen := hMp.length_eq
      have hip : i < pfvs.length := by omega
      have hpi : stats.params[i]! = .fvar pfvs[i] := by
        rw [getElem!_pos stats.params i (by rw [← Array.length_toList, hpar]; simpa)]
        simp [← Array.getElem_toList, hpar]
      rw [hpi]
      obtain ⟨n₁, hn₁, hMp'⟩ := hM₁
      obtain ⟨_, rfl⟩ := hM
      obtain ⟨hk, rfl⟩ := hparam rfl
      have hpi' : params.take (i + 1) = params.take i ++ [params[i]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (show i < params.length by omega)]; rfl
      have hfi' : pfvs.take (i + 1) = pfvs.take i ++ [pfvs[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hip]; rfl
      obtain ⟨hk', hT1⟩ := hMp.dropN' (params.length - (i + 1)) (by omega)
      rw [show params.length - (params.length - (i + 1)) = i + 1 by omega, hpi'] at hT1
      rw [hfi'] at hT1
      obtain ⟨name_i, ty_i, bi_i, m', hm', -⟩ := hT1.snoc_inv
      have hm'eq : Mp.dropN (params.length - i) hk = m' := by
        rw [← MLCtx.dropN_congr (show params.length - (i + 1) + 1 = params.length - i by omega)
          (by omega) hk, ← MLCtx.dropN_dropN Mp _ 1 hk' (by simp [hm'])]
        simp [hm']
      rw [hm'eq] at W hΔs hdomT hbodyT hdom hbody hdef hΔ
      simp only [MLCtx.dropN] at hMp'
      have hn₁' : n₁ + (params.length - (i + 1)) ≤ c.mlctx.length := by
        have := MLCtx.length_dropN c.mlctx n₁ hn₁; rw [hMp'] at this; omega
      have hcm : c.mlctx.dropN (n₁ + (params.length - (i + 1))) hn₁' =
          .vlam pfvs[i] name_i ty_i params[i] bi_i m' := by
        rw [← MLCtx.dropN_dropN c.mlctx n₁ _ hn₁ (by rw [hMp']; exact hk'),
          MLCtx.dropN_of_eq hMp' _ hk', hm']
      have hwf := MLCtx.WF.dropN _ hn₁' c.mlctx_wf
      rw [hcm] at hwf
      obtain ⟨-, -, hty_i, -⟩ := hwf
      obtain ⟨d, hd, hdty⟩ := c.mlctx_wf.find?_dropN_vlam _ _ hcm
      rw [c.lctx_eq] at hd
      refine WF.bind (getType.WF hd) fun t ht => ?_
      subst ht; rw [hdty]
      have h1 := hdom.weakFV' henv' W hΔb
      have h2 := hty_i.weakFV' henv' W hΔb
      simp only [Lift.consN] at h1 h2
      refine WF.bind (WF.liftTC (TypeChecker.isDefEq.WF h1 h2)) fun b hb => ?_
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
      | true =>
      simp only [if_true]
      have hΓ := hΔs.toCtx
      have hWc := W.toCtx; simp only [Lift.consN] at hWc
      have hdd : c.venv.IsDefEqU c.lparams.length m'.vlctx.toCtx dom' params[i] :=
        (VEnv.IsDefEqU.weak'_iff henv' hΔb.toCtx hWc).1 (hb rfl)
      obtain ⟨u, hdomS⟩ := hdomT
      have hdomty := hdd.of_l henv' hΓ hdomS
      have hΔeq : VLCtx.IsDefEq c.venv c.lparams.length
          ((none, .vlam dom') :: m'.vlctx) ((none, .vlam params[i]) :: m'.vlctx) :=
        .cons (VLCtx.IsDefEq.refl henv'.ordered hΔs) nofun (.vlam hdomty)
      obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv' hΔeq
      have hbodyeq := hbody.uniq henv' hΔeq hbody''
      obtain ⟨ρ', W'⟩ := MLCtx.fvlift_dropN c.mlctx _ hn₁'
      rw [hcm] at W'
      have hΔs' := W'.wf henv' hΔb
      have hinst : TrExprS c.venv c.lparams (MLCtx.vlam pfvs[i] name_i ty_i params[i] bi_i m').vlctx
          (body.instantiate1 (.fvar pfvs[i])) body'' := by
        rw [Lean.Expr.instantiate1_eq]; exact hbody''.inst_fvar henv'.ordered hΔs'
      have h3 := hinst.weakFV' henv' W' hΔb; simp only [Lift.consN] at h3
      refine WF.bind (WF.liftTC (TypeChecker.whnf.WF h3)) fun e₁ ⟨hbelow, htr₁⟩ => ?_
      have hfv₁ := hbelow _ (W'.isFVarUpSet rfl hΔb.fvwf) hinst.fvarsIn
      have htr' := TrExpr.strengthen henv' W' hΔb (MLCtx.noBV _) htr₁ hfv₁
      have hptake : c₀.venv.IsTele c₀.lparams.length [] (params.take (i + 1)) := by
        have := hptele; rw [← List.take_append_drop (i + 1) params] at this
        exact this.append_inv.1
      refine ih e₁ (i + 1) 0 c _ [] body'' hc ⟨Nat.zero_le _, rfl⟩ ⟨ρ', W'⟩ ?_
        (fun _ => ⟨hk', by rw [hm']⟩) (by omega) rfl nofun (by simpa using hptake) htr' ?_
      · simp only [MLCtx.vlctx, VLCtx.toCtx, hpi']
        rw [List.reverse_append]
        simpa using hΔ
      · obtain ⟨v, hbodyS⟩ := hbodyT
        have h1 : c.venv.IsDefEq c.lparams.length m'.vlctx.toCtx
            (.forallE dom' body') (.forallE params[i] body'') (.sort (.imax u v)) :=
          .forallEDF hdomty (hbodyeq.of_l henv' ⟨hΓ, _, hdomS⟩ hbodyS)
        have h2 := (hdef.of_l henv' hΓ h1.hasType.1).symm.trans h1
        rw [hΔ] at h2
        have htele' : c.venv.IsTele c.lparams.length [] (params.take i) := by
          rw [hc.venv, hc.lparams]; simpa using htele
        obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr htele' (by simpa using h2)
        have hT0 : c.venv.IsDefEqU c.lparams.length [] T' (.foralls (params.take i) V) := by
          rw [hc.venv, hc.lparams]; simpa using hT
        have h4 : c.venv.IsDefEqU c.lparams.length [] T'
            (.foralls (params.take i) (.forallE params[i] body'')) :=
          hT0.trans henv' trivial ⟨_, h3⟩
        rw [hpi', List.append_nil, VExpr.foralls_append]
        simpa [hc.venv, hc.lparams] using h4
    · rename_i hlt
      have hi' : i = params.length := Nat.le_antisymm hle (Nat.not_lt.1 hlt)
      subst hi'
      rw [List.take_of_length_le (Nat.le_refl _)] at hΔ htele hT
      rw [Lean.Expr.consumeTypeAnnotations_eq]
      have hΓ := hΔs.toCtx
      obtain ⟨tys, hty, hdefty⟩ :=
        TrExprS.consumeTypeAnnotations' henv' (hc.venv ▸ hann) hΔs hdom
      have htyT : c.venv.IsType c.lparams.length Δs.toCtx tys := hdomT.defeqU_l henv' hΓ hdefty
      obtain ⟨u, hdomS⟩ := hdomT
      have hdomty := hdefty.of_l henv' hΓ hdomS
      have hΔeq : VLCtx.IsDefEq c.venv c.lparams.length
          ((none, .vlam dom') :: Δs) ((none, .vlam tys) :: Δs) :=
        .cons (VLCtx.IsDefEq.refl henv'.ordered hΔs) nofun (.vlam hdomty)
      obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv' hΔeq
      have hbodyeq := hbody.uniq henv' hΔeq hbody''
      have hWc := W.toCtx; simp only [Lift.consN] at hWc
      have htyb := hty.weakFV' henv' W hΔb; simp only [Lift.consN] at htyb
      have htyTb : c.venv.IsType c.lparams.length c.mlctx.vlctx.toCtx (tys.lift' ρ) :=
        htyT.weak' henv'.ordered hWc
      refine AddInductive.WF.withLocalDecl htyb htyTb ?_
      have W' : VLCtx.FVLift'
          ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δs)
          (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx.vlctx
          0 (ρ.consN 1) 0 :=
        W.cons_fvar (⟨c.ngen.curr⟩, _) (.vlam tys) hty.fvarsList
      have hΔb' := (c.push name dom.consumeTypeAnnotations' (tys.lift' ρ) bi htyb htyTb).mlctx_wf.tr.wf
      have hΔs' := W'.wf henv' hΔb'
      have hinst : TrExprS c.venv c.lparams
          ((some (⟨c.ngen.curr⟩, dom.consumeTypeAnnotations'.fvarsList), .vlam tys) :: Δs)
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' := by
        rw [Lean.Expr.instantiate1_eq]; exact hbody''.inst_fvar henv'.ordered hΔs'
      have h3 := hinst.weakFV' henv'.ordered W' hΔb'; simp only [Lift.consN] at h3
      refine AddInductive.WF.bind (AddInductive.WF.liftTC (TypeChecker.whnf.WF h3))
        fun e₁ ⟨hbelow, htr₁⟩ => ?_
      have hfv₁ := hbelow _ (W'.isFVarUpSet rfl hΔb'.fvwf) hinst.fvarsIn
      have htr' := TrExpr.strengthen henv' W' hΔb' (MLCtx.noBV _) htr₁ hfv₁
      obtain ⟨hk, hM⟩ := hM
      refine ih e₁ params.length (nidx + 1) _ _ (idx ++ [tys]) body'' hc.push
        ⟨by simp [VContext.push, MLCtx.length]; exact hk, hM⟩ ⟨_, W'⟩ ?_ nofun (Nat.le_refl _) (by simp [hn]) (fun _ => rfl)
        ?_ htr' ?_
      · simp only [VLCtx.toCtx, List.reverse_append]
        rw [List.take_of_length_le (Nat.le_refl _)]
        simpa using hΔ
      · rw [List.take_of_length_le (Nat.le_refl _), ← List.append_assoc]
        refine htele.snoc ?_
        rw [hc.venv, hc.lparams] at htyT
        simpa [hΔ] using htyT
      · obtain ⟨v, hbodyS⟩ := hbodyT
        have h1 : c.venv.IsDefEq c.lparams.length Δs.toCtx
            (.forallE dom' body') (.forallE tys body'') (.sort (.imax u v)) :=
          .forallEDF hdomty (hbodyeq.of_l henv' ⟨hΓ, _, hdomS⟩ hbodyS)
        have h2 := (hdef.of_l henv' hΓ h1.hasType.1).symm.trans h1
        rw [hΔ] at h2
        have htele' : c.venv.IsTele c.lparams.length [] (params ++ idx) := by
          rw [hc.venv, hc.lparams]; exact htele
        obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr htele' (by simpa using h2)
        have hT0 : c.venv.IsDefEqU c.lparams.length [] T' (.foralls (params ++ idx) V) := by
          rw [hc.venv, hc.lparams]; exact hT
        have h4 : c.venv.IsDefEqU c.lparams.length [] T'
            (.foralls (params ++ idx) (.forallE tys body'')) :=
          hT0.trans henv' trivial ⟨_, h3⟩
        rw [List.take_of_length_le (Nat.le_refl _), ← List.append_assoc, VExpr.foralls_append]
        simpa [hc.venv, hc.lparams] using h4
  | _ =>
    rw [checkInductiveTypes.loopInd.loop.eq_3 _ _ _ _ _ _ _ fun _ _ _ _ h => by cases h]
    split
    · exact AddInductive.WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
    · rename_i hi'
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi'
      subst hi'
      rw [List.take_of_length_le (by omega)] at hΔ htele hT
      rw [← hn]
      exact H _ V c Δs idx hc (hn ▸ hM) ⟨ρ, W⟩ hΔ htele htr hT

/-- Each later type of a mutual block: its parameters agree with the first type's, and it lives
in the same universe. Its loop runs in a local context holding the earlier types' indices too, which
the type does not mention, so each step is read in the context of the parameters and its own
indices. -/
theorem loopIndLater.WF {c₀ : VContext} (henv : c₀.venv.WF) (hann : c₀.venv.AnnotationsErase)
    {nparams : Nat} {types : List InductiveType} {k : InductiveStats → M α} {Q}
    {dIdx : Nat} (hd : 1 ≤ dIdx) (hlt : dIdx < types.length) {stats c params level typeTr}
    (hT : TypesSoFar c₀ nparams types dIdx stats c params level typeTr)
    (H : ∀ stats c typeTr, TypesSoFar c₀ nparams types (dIdx + 1) stats c params level typeTr →
      AddInductive.WF c (checkInductiveTypes.loopInd nparams types.toArray k (dIdx + 1) stats) Q) :
    AddInductive.WF c (checkInductiveTypes.loopInd nparams types.toArray k dIdx stats) Q := by
  obtain ⟨k₁, hk₁, pfvs, hMp, hpar⟩ := hT.paramsCtx
  have hne : stats.indConsts.isEmpty = false := by
    have h := hT.indConsts
    rw [Bool.eq_false_iff]; intro he
    rw [Array.isEmpty_iff] at he; rw [he] at h
    have : (types.take dIdx).length = 0 := by simpa using (congrArg List.length h).symm
    simp at this
    rcases this with h | h
    · omega
    · subst h; simp at hlt
  rw [checkInductiveTypes.loopInd.eq_1, dif_pos (by simpa using hlt)]
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  have hc := hT.base
  have henv' : c.venv.WF := hc.venv ▸ henv
  have hΔb := c.mlctx_wf.tr.wf
  refine WF.bind (WF.liftExcept (checkNoMVarNoFVar.WF _ _ _)) fun _ hcl => ?_
  have hcl' : types.toArray[dIdx].type.FVarsIn (· ∈ c.tc.vlctx.fvars) := hcl.mono nofun
  refine WF.bind (WF.liftTC (TypeChecker.checkType.WF hcl')) fun _ hty => ?_
  obtain ⟨Tb, _, -, hTb, -, -⟩ := hty
  have W₀ := VLCtx.FVLift'.from_nil (MLCtx.noBV c.mlctx)
  obtain ⟨T', hT'0, -⟩ := TrExprS.strengthen henv' W₀ hΔb (MLCtx.noBV _) hTb (hcl.mono nofun)
  have hTl := hT'0.weakFV' henv'.ordered W₀ hΔb; simp only [Lift.consN] at hTl
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  refine WF.bind (WF.liftTC (TypeChecker.whnf.WF hTl)) fun e₁ ⟨hbelow, he₁⟩ => ?_
  have hfv₁ := hbelow _ (W₀.isFVarUpSet rfl hΔb.fvwf) hT'0.fvarsIn
  have htr₁ := TrExpr.strengthen henv' W₀ hΔb (MLCtx.noBV _) he₁ hfv₁
  have hnil : VLCtx.WF c.venv c.lparams.length ([] : VLCtx) := trivial
  have hT'wf := TrExprS.wf henv'.ordered hnil hT'0
  obtain ⟨hkall, hall⟩ := hMp.dropN_all
  refine loopLater.WF henv hann hne hMp hpar hT.nparams hT.params_tele (T' := T') (M₁ := c.mlctx)
    ⟨k₁, hk₁, rfl⟩ ?_ _ e₁ 0 0 c [] [] T' hc ⟨Nat.zero_le _, rfl⟩ ⟨_, W₀⟩ rfl
    (fun _ => ⟨by simpa [hT.nparams] using hkall, by simp [← hT.nparams, hall]⟩)
    (Nat.zero_le _) rfl nofun (by simpa using VEnv.IsTele.nil) htr₁
    (by rw [← hc.venv, ← hc.lparams]; exact hT'wf)
  intro type V c' Δs idx hc' hM hW hΔ htele htr hT₁
  dsimp only
  have henv'' : c'.venv.WF := hc'.venv ▸ henv
  have hΔb' := c'.mlctx_wf.tr.wf
  obtain ⟨ρ, W⟩ := hW
  have hΔs := W.wf henv'' hΔb'
  have hΓ := hΔs.toCtx
  obtain ⟨V₁, hS, hV⟩ := htr
  have hSb := hS.weakFV' henv''.ordered W hΔb'; simp only [Lift.consN] at hSb
  refine WF.bind (WF.liftTC (TypeChecker.ensureSort.WF hSb)) fun e ⟨⟨s', hs', hs'V⟩, u, he⟩ => ?_
  subst he
  cases hs' with | sort hu => ?_
  rename_i u'
  change VLevel.ofLevel c'.lparams u = some u' at hu
  have hWc := W.toCtx; simp only [Lift.consN] at hWc
  have hs'V' : c'.venv.IsDefEqU c'.lparams.length Δs.toCtx (.sort u') V₁ :=
    (VEnv.IsDefEqU.weak'_iff (e1 := .sort u') henv'' hΔb'.toCtx hWc).1 hs'V
  rw [if_neg (by simp [hne])]
  split
  · exact WF.bind (Q := fun _ => False) .throw fun _ h => h.elim
  rename_i heq
  have heqv : u.isEquiv stats.resultLevel = true := by simpa [Expr.sortLevel!] using heq
  have hu₀ : VLevel.ofLevel c₀.lparams u = some u' := by rwa [← hc'.lparams]
  have hlev : u' ≈ level := Level.isEquiv_wf heqv hu₀ hT.resultLevel
  have hsize := hT.nindices
  refine H _ c' (typeTr ++ [T']) ⟨hc', ?_, hT.nparams, hT.params_tele, hT.levels, hT.resultLevel,
    hT.isNotZero, by simp [hsize], ?_, by simp [hT.typeTr_length], ?_⟩
  · obtain ⟨hk, hM⟩ := hM
    have hk' : idx.length + k₁ ≤ c'.mlctx.length := by
      have := MLCtx.length_dropN c'.mlctx idx.length hk; rw [hM] at this; omega
    refine ⟨_, hk', pfvs, ?_, hpar⟩
    rw [← MLCtx.dropN_dropN c'.mlctx idx.length k₁ hk (by rw [hM]; exact hk₁),
      MLCtx.dropN_of_eq hM _ hk₁]
    exact hMp
  · simp only [Array.toList_push, hT.indConsts, List.take_add_one, List.map_append]
    simp [List.getElem?_eq_getElem hlt]
  · intro j t T'' ht hT''
    have hj : j ≤ dIdx := by
      have := (List.getElem?_eq_some_iff.1 hT'').1; simp [hT.typeTr_length] at this; omega
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · rw [List.getElem?_append_left (by rw [hT.typeTr_length]; exact hj)] at hT''
      obtain ⟨i', u'', a, b, c, d, e, f⟩ := hT.types j t T'' ht hT''
      refine ⟨i', u'', a, b, c, d, ?_, f⟩
      rw [Array.getElem?_push_lt (by rw [hsize]; exact hj), ← Array.getElem?_eq_getElem]
      exact e
    · rw [List.getElem?_append_right (Nat.le_of_eq hT.typeTr_length)] at hT''
      simp [hT.typeTr_length] at hT''; subst hT''
      obtain rfl : t = types[j] := by simpa [List.getElem?_eq_getElem hlt] using ht.symm
      have hsort : c'.venv.IsDefEq c'.lparams.length Δs.toCtx V (.sort u') (.sort (.succ u')) := by
        have h1 := hs'V'.trans henv'' hΓ hV
        have hu' : u'.WF c'.lparams.length := .of_ofLevel hu
        exact (h1.of_l henv'' hΓ (.sort hu')).symm
      rw [hΔ] at hsort
      have htele' : c'.venv.IsTele c'.lparams.length [] (params ++ idx) := by
        rw [hc'.venv, hc'.lparams]; exact htele
      obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr htele' (by simpa using hsort)
      rw [hc'.venv, hc'.lparams] at h3
      have hdef : c₀.venv.IsDefEqU c₀.lparams.length [] T' (.foralls (params ++ idx) (.sort u')) :=
        hT₁.trans henv trivial ⟨_, h3⟩
      have hT'0' : TrExprS c₀.venv c₀.lparams [] types[j].type T' := by
        rw [← hT.base.venv, ← hT.base.lparams]; simpa using hT'0
      refine ⟨idx, u', hT'0', ?_, hdef, hlev, ?_, ?_⟩
      · have hu' : u'.WF c₀.lparams.length := .of_ofLevel hu₀
        exact (htele.foralls ⟨_, .sort hu'⟩).defeqU_l henv trivial hdef.symm
      · simp only [Array.getElem?_push, hsize, ite_true]
      · simpa using htele.append_inv.2


/-- Once every type is through, the continuation gets the statistics. -/
theorem loopIndEnd.WF {c₀ : VContext} {nparams : Nat} {types : List InductiveType}
    {k : InductiveStats → M α} {Q} {stats c params level typeTr}
    (hT : TypesData c₀ nparams types stats c params level typeTr)
    (H : ∀ stats c params level typeTr, TypesData c₀ nparams types stats c params level typeTr →
      WF c (k stats) Q) :
    WF c (checkInductiveTypes.loopInd nparams types.toArray k types.length stats) Q := by
  rw [checkInductiveTypes.loopInd.eq_1, dif_neg (by simp)]
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  obtain ⟨_, _, fvs, htele, hps⟩ := hT.paramsCtx
  have h1 : stats.levels.length = c.lparams.length := by simp [hT.levels, hT.base.lparams]
  have h2 : stats.nindices.size = types.toArray.size := by simp [hT.nindices]
  have h3 : stats.indConsts.size = types.toArray.size := by
    rw [← Array.length_toList, hT.indConsts]; simp
  have h4 : stats.params.size = nparams := by
    rw [← Array.length_toList, hps, List.length_map, htele.length_eq, hT.nparams]
  simp only [h1, h2, h3, h4, beq_self_eq_true, ↓reduceIte]
  exact H _ _ _ _ _ hT

theorem loopIndFrom.WF {c₀ : VContext} (henv : c₀.venv.WF) (hann : c₀.venv.AnnotationsErase)
    {nparams : Nat} {types : List InductiveType} {k : InductiveStats → M α} {Q}
    (H : ∀ stats c params level typeTr, TypesData c₀ nparams types stats c params level typeTr →
      WF c (k stats) Q) :
    ∀ m dIdx, types.length - dIdx = m → 1 ≤ dIdx → dIdx ≤ types.length →
      ∀ stats c params level typeTr,
        TypesSoFar c₀ nparams types dIdx stats c params level typeTr →
      WF c (checkInductiveTypes.loopInd nparams types.toArray k dIdx stats) Q
  | 0, dIdx, hm, _, hle, _, _, _, _, _, hT => by
    obtain rfl : dIdx = types.length := by omega
    exact loopIndEnd.WF hT H
  | m + 1, dIdx, hm, hd, _, _, _, _, _, _, hT =>
    loopIndLater.WF henv hann hd (by omega) hT fun _ _ _ hT' =>
      loopIndFrom.WF henv hann H m (dIdx + 1) (by omega) (by omega) (by omega) _ _ _ _ _ hT'

/-- `checkInductiveTypes` from the empty local context. -/
theorem checkInductiveTypes.WF {c₀ : VContext} (h₀ : c₀.mlctx = .nil) (henv : c₀.venv.WF)
    (hann : c₀.venv.AnnotationsErase) {nparams : Nat} {types : List InductiveType}
    (hne : types ≠ []) {k : InductiveStats → M α} {Q}
    (H : ∀ stats c params level typeTr, TypesData c₀ nparams types stats c params level typeTr →
      WF c (k stats) Q) :
    WF c₀ (checkInductiveTypes nparams types.toArray k) Q := by
  unfold checkInductiveTypes
  refine WF.bind WF.read fun _ hr => ?_; subst hr
  exact loopInd0.WF h₀ henv hann hne fun _ _ _ _ _ hT =>
    loopIndFrom.WF henv hann H _ 1 rfl (Nat.le_refl _)
      (List.length_pos_iff.2 hne) _ _ _ _ _ hT

/-- The records `declareInductiveTypes` adds. -/
def inductVals (lparams : List Name) (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : List InductiveVal :=
  let all := indTypes.map (·.name) |>.toList
  (indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts : InductiveVal }).toList

theorem declareInductiveTypes.WF {c : VContext} {stats : InductiveStats}
    {numParams numNested : Nat} {indTypes : Array InductiveType} {isUnsafe : Bool} :
    WF c (declareInductiveTypes stats numParams indTypes numNested isUnsafe) fun env' =>
      let cis := (inductVals c.lparams stats numParams indTypes numNested isUnsafe).map .inductInfo
      env'.constants = insertConsts c.env.constants cis ∧ env'.quotInit = c.env.quotInit ∧
      (cis.map (·.name)).Nodup ∧ (∀ ci ∈ cis, c.env.constants.find? ci.name = none) ∧
      (∀ ci ∈ cis, Environment.primitives.contains ci.name → c.allowPrimitive) := by
  intro env' h
  simp only [declareInductiveTypes, ← Array.foldlM_toList] at h
  exact Lean4Lean.addChecked.WF c.envAt.tr.map_wf c.allowPrimitive ConstantInfo.inductInfo _ _ h

theorem inductVals_names {lparams : List Name} {stats : InductiveStats} {numParams numNested : Nat}
    {types : List InductiveType} {isUnsafe : Bool} (h : stats.nindices.size = types.length) :
    ((inductVals lparams stats numParams types.toArray numNested isUnsafe).map
      ConstantInfo.inductInfo).map (·.name) = types.map (·.name) := by
  have key : ∀ (F : InductiveType → Nat → InductiveVal), (∀ a b, (F a b).name = a.name) →
      ∀ (ts : List InductiveType) (ns : List Nat), ts.length = ns.length →
      ((List.zipWith F ts ns).map ConstantInfo.inductInfo).map (·.name) = ts.map (·.name) := by
    intro F hF ts
    induction ts with
    | nil => intro _ _; rfl
    | cons t ts ih =>
      intro ns h; cases ns with
      | nil => cases h
      | cons n ns =>
        simp only [List.zipWith_cons_cons, List.map_cons]
        congr 1
        exacts [hF t n, ih ns (by simpa using h)]
  simp only [inductVals, Array.toList_zipWith]
  exact key _ (fun _ _ => rfl) _ _ (by simp [h])

/-- Adding a list of axioms, each translated against the environment before them all, to an
environment with a model. -/
theorem _root_.Lean4Lean.VEnvAt.addAxiomList {env : Environment} {venv : VEnv}
    {safety : DefinitionSafety} :
    ∀ (axs : List AxiomVal) (cs : List (Name × VConstant)) {venv' : VEnv},
    VEnvAt env safety venv →
    List.Forall₂ (fun (ax : AxiomVal) (p : Name × VConstant) => ax.name = p.1 ∧
      TrConstant safety venv (.axiomInfo ax) p.2 ∧ p.2.WF venv) axs cs →
    (axs.map (·.name)).Nodup → (∀ ax ∈ axs, env.find? ax.name = none) →
    (∀ ax ∈ axs, Environment.primitives.contains ax.name = false) →
    venv.addConstList cs = some venv' →
    VEnvAt (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env) safety venv'
  | [], [], _, wf, .nil, _, _, _, e => by cases e; exact wf
  | ax :: axs, p :: cs, venv', wf, .cons ⟨hn, htr, hwf⟩ tl, hnd, hfr, hnp, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [VEnv.addConstList, List.foldlM_cons] at e
    obtain ⟨venv₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 e
    have h₁' : venv.addConst ax.name p.2 = some venv₁ := hn ▸ h₁
    have hle := VEnv.addConst_le h₁'
    have hax : (ConstantInfo.axiomInfo ax).name = ax.name := rfl
    have wf₁ : VEnvAt (env.add (.axiomInfo ax)) safety venv₁ :=
      { tr := TrEnv'.axiom (ci := ax) htr
          (by rw [← wf.tr.map_wf.find?'_eq_find?]; exact hfr _ (.head _)) hwf h₁' wf.tr
        hasPrimitives := wf.hasPrimitives.addConst (hnp _ (.head _)) h₁'
        safePrimitives := wf.safePrimitives_add _ (hax ▸ hfr _ (.head _))
          (by rw [hax, hnp _ (.head _)]; nofun) }
    refine VEnvAt.addAxiomList axs cs wf₁ ?_ hnd.2 (fun a ha => ?_) (fun a ha => hnp a (.tail _ ha))
      h₂
    · exact Lean4Lean.List.Forall₂.imp (fun _ _ h =>
        ⟨h.1, h.2.1.mono hle, h.2.2.mono hle⟩) tl
    · have hne : ax.name ≠ a.name := fun hh => hnd.1 (List.mem_map.2 ⟨a, ha, hh.symm⟩)
      exact Environment.find?_add_of_ne wf.tr.map_wf _ (hax ▸ hfr _ (.head _)) (hax ▸ hne)
        (hfr a (.tail _ ha))

theorem foldlM_except_pure {α β ε} (f : β → α → β) : ∀ (l : List α) (b : β),
    l.foldlM (m := Except ε) (fun b a => pure (f b a)) b = pure (l.foldl f b)
  | [], _ => rfl
  | a :: l, b => foldlM_except_pure f l (f b a)

theorem forall₂_map_zipWith {g : α → γ} {f : α → β → δ} {R : γ → δ → Prop} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    (∀ (j : Nat) a b, l₁[j]? = some a → l₂[j]? = some b → R (g a) (f a b)) →
    List.Forall₂ R (l₁.map g) (List.zipWith f l₁ l₂)
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, H =>
    .cons (H 0 a b rfl rfl) (forall₂_map_zipWith l₁ l₂ (by simpa using hl)
      fun j a b h₁ h₂ => H (j + 1) a b h₁ h₂)

/-- The axioms `declareTypeAxioms` adds: each type, followed, in a primitive block, by its
constructors. -/
def typeAxioms (lparams : List Name) (allowPrimitive isUnsafe : Bool)
    (types : List InductiveType) : List AxiomVal :=
  types.flatMap fun t => { name := t.name, levelParams := lparams, type := t.type, isUnsafe } ::
    if allowPrimitive then
      t.ctors.map fun ct => { name := ct.name, levelParams := lparams, type := ct.type, isUnsafe }
    else []

/-- The constants the checking environment's model adds for the block's types. -/
def typeConstsOf (U : Nat) (types : List InductiveType) (typeTr : List VExpr) :
    List (Name × VConstant) :=
  List.zipWith (fun t T' => (t.name, ⟨U, T'⟩)) types typeTr

theorem typeConstsOf_names {U : Nat} : ∀ {types : List InductiveType} {typeTr : List VExpr},
    types.length = typeTr.length →
    (typeConstsOf U types typeTr).map (·.1) = types.map (·.name)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [typeConstsOf, List.zipWith_cons_cons, List.map_cons] at h ⊢
    exact congrArg _ (typeConstsOf_names (by simpa using h))

/-- What `declareTypeAxioms` establishes about the environment `envAx` the block is checked in:
it adds the block's types, and for a primitive block its constructors, as axioms, and has a model
at the block's level extending the environment's. -/
def TypeAxiomsAdded (c : VContext) (types : List InductiveType) (typeTr : List VExpr)
    (isUnsafe : Bool) (envAx : Environment) : Prop :=
  envAx = (typeAxioms c.lparams c.allowPrimitive isUnsafe types).foldl
    (fun e ax => e.add (.axiomInfo ax)) c.env ∧
  ∃ venvAx, VEnvAt envAx c.safety venvAx ∧ c.venv ≤ venvAx ∧
    (c.allowPrimitive = false →
      c.venv.addConstList (typeConstsOf c.lparams.length types typeTr) = some venvAx) ∧
    (∀ (j : Nat) (t : InductiveType) (T' : VExpr), types[j]? = some t → typeTr[j]? = some T' →
      venvAx.constants t.name = some ⟨c.lparams.length, T'⟩) ∧
    (∀ n, c.venv.constants n = none → venvAx.constants n ≠ none →
      n ∈ types.map (·.name) ∨
        c.allowPrimitive ∧ ∃ t ∈ types, n ∈ t.ctors.map (·.name))

/-- The environment a block without primitive names is checked in has a model at the block's level,
extending the environment's: the block's types as axioms. -/
theorem declareTypeAxioms.WF {c₀ c : VContext} {nparams : Nat}
    {types : List InductiveType} {stats params level typeTr}
    (hT : TypesData c₀ nparams types stats c params level typeTr)
    {isUnsafe : Bool} (hsafety : c.safety = inductSafety isUnsafe)
    (hfresh : ∀ t ∈ types, c.env.constants.find? t.name = none)
    (hnd : (types.map (·.name)).Nodup)
    (hprim : ∀ t ∈ types, Environment.primitives.contains t.name → c.allowPrimitive)
    (hp : c.allowPrimitive = false) :
    AddInductive.WF c (declareTypeAxioms types.toArray isUnsafe)
      (TypeAxiomsAdded c types typeTr isUnsafe) := by
  intro envAx h
  let axs := types.map fun t =>
    ({ name := t.name, levelParams := c.lparams, type := t.type, isUnsafe } : AxiomVal)
  have hax : typeAxioms c.lparams c.allowPrimitive isUnsafe types = axs := by
    simp [typeAxioms, hp, axs, List.map_eq_flatMap]
  have henv : envAx = axs.foldl (fun e ax => e.add (.axiomInfo ax)) c.env := by
    simp only [declareTypeAxioms, hp, List.foldlM_toArray, Bool.false_eq_true, if_false,
      foldlM_except_pure] at h
    cases h; simp [axs, List.foldl_map]
  unfold TypeAxiomsAdded; rw [hax]; refine ⟨henv, ?_⟩
  have hlen : types.length = typeTr.length := hT.typeTr_length.symm
  have hfind (n) (hn : c.env.constants.find? n = none) : c.env.find? n = none := by
    rwa [Kernel.Environment.find?, c.envAt.tr.map_wf.find?'_eq_find?]
  have hfr' : ∀ p ∈ typeConstsOf c.lparams.length types typeTr, c.venv.constants p.1 = none := by
    intro p hp
    have : p.1 ∈ types.map (·.name) := typeConstsOf_names hlen ▸ List.mem_map_of_mem hp
    obtain ⟨t, ht, e⟩ := List.mem_map.1 this
    exact e ▸ c.envAt.tr.constants_eq_none (hfind _ (hfresh t ht))
  obtain ⟨venvAx, hadd⟩ := VEnv.exists_addConstList hfr' (typeConstsOf_names hlen ▸ hnd)
  refine ⟨venvAx, ?_, VEnv.addConstList_le hadd, fun _ => hadd, ?_, ?_⟩
  · rw [henv]
    refine VEnvAt.addAxiomList axs _ c.envAt ?_ (by simpa [axs, List.map_map, Function.comp_def])
      (fun ax hax => ?_) (fun ax hax => ?_) hadd
    · refine forall₂_map_zipWith _ _ hlen fun j t T' h₁ h₂ => ⟨rfl, ⟨?_, rfl, ?_⟩, ?_⟩
      · rw [hsafety]; cases isUnsafe <;> exact DefinitionSafety.le_rfl
      · obtain ⟨_, _, htr, -⟩ := hT.types j t T' h₁ h₂
        rw [hT.base.venv, hT.base.lparams]; exact htr
      · obtain ⟨_, _, -, hty, -⟩ := hT.types j t T' h₁ h₂
        show c.venv.IsType _ [] T'
        rw [hT.base.venv, hT.base.lparams]; exact hty
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hax
      exact hfind _ (hfresh t ht)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hax
      exact Bool.eq_false_iff.2 fun h => by simpa [hp] using hprim t ht h
  · intro j t T' h₁ h₂
    refine VEnv.addConstList_constants_of_mem hadd (List.mem_iff_getElem?.2 ⟨j, ?_⟩)
    simp [typeConstsOf, List.getElem?_zipWith, h₁, h₂]
  · intro n hn hne
    left
    by_contra hm
    exact hne (VEnv.addConstList_constants_none hadd hn (typeConstsOf_names hlen ▸ hm))

/-- What `checkConstructors` establishes about a constructor's fields `Ds`, declared under the
parameters and `k` earlier fields `Γ`: each is a type whose sort is bounded by the block's, and
in a safe block it is positive. -/
inductive FieldsChecked (venv : VEnv) (d : VInductDecl) : List VExpr → Nat → List VExpr → Prop
  | nil : FieldsChecked venv d Γ k []
  | cons :
    (∃ u, venv.HasType d.uvars Γ D (.sort u) ∧ (d.level ≈ .zero ∨ u ≤ d.level)) →
    (d.isUnsafe = false → d.Positive venv Γ k D) →
    FieldsChecked venv d (D :: Γ) (k + 1) Ds → FieldsChecked venv d Γ k (D :: Ds)

/-- What `checkConstructors` establishes about constructor `ct` of type `t`, for any translation
of its type in `venv`: it is a type, and a telescope of parameters agreeing with the block's
followed by fields, ending in `t` at the parameters and at indices that do not mention the
block. The declared type has a binder for each, which is what `declareConstructors` counts. -/
def CtorChecked (venv : VEnv) (U : List Name) (d : VInductDecl) (t : InductiveType) (nidx : Nat)
    (ct : Constructor) : Prop :=
  ∀ C', TrExprS venv U [] ct.type C' → venv.IsType U.length [] C' ∧ ∃ ps Ds idx,
    C' = .foralls (ps ++ Ds) (.appN (.const t.name (VLevel.params U.length))
      (VExpr.bvars d.params.length Ds.length ++ idx)) ∧
    declareConstructors.arity 0 ct.type = ps.length + Ds.length ∧
    venv.TeleDefEq U.length [] ps d.params ∧ idx.length = nidx ∧
    idx.all (!·.mentions d.names) ∧ FieldsChecked venv d ps.reverse 0 Ds

/-- A declaration that agrees with what the checks so far have seen of the block. -/
structure Compat (U : List Name) (params : List VExpr) (level : VLevel) (isUnsafe : Bool)
    (types : List InductiveType) (nindices : Array Nat) (d : VInductDecl) : Prop where
  uvars : d.uvars = U.length
  params : d.params = params
  level : d.level = level
  isUnsafe : d.isUnsafe = isUnsafe
  names : d.names = types.map (·.name)
  indices : ∀ (j : Nat) (T : VInductiveType), d.types[j]? = some T →
    nindices[j]? = some T.indices.length

/-- The record `declareConstructors` adds for the `cidx`th constructor `ct` of type `t`. -/
def ctorVal (lparams : List Name) (nparams : Nat) (isUnsafe : Bool) (t : InductiveType)
    (ct : Constructor) (cidx : Nat) : ConstructorVal :=
  { name := ct.name, levelParams := lparams, type := ct.type, induct := t.name, cidx,
    numParams := nparams, numFields := declareConstructors.arity 0 ct.type - nparams, isUnsafe }

/-- The records `declareConstructors` adds. -/
def ctorVals (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) : List ConstructorVal :=
  types.flatMap fun t => (t.ctors.zipIdx).map fun p => ctorVal lparams nparams isUnsafe t p.1 p.2

theorem declareConstructors_eq {c : Context} {stats : InductiveStats}
    {types : List InductiveType} {isUnsafe : Bool} :
    declareConstructors stats types.toArray isUnsafe c =
      (ctorVals c.lparams stats.params.size types isUnsafe).foldlM (m := Except Exception)
        (fun (env : Environment) v => do
          env.checkName v.name c.allowPrimitive; return env.add (.ctorInfo v)) c.env := by
  have inner : ∀ (t : InductiveType)
      (F : Nat × Environment → Constructor → Except Exception (Nat × Environment))
      (G : Environment → ConstructorVal → Except Exception Environment),
      (∀ n env ct, F (n, env) ct =
        (G env (ctorVal c.lparams stats.params.size isUnsafe t ct n) >>= fun e => pure (n + 1, e))) →
      ∀ (cts : List Constructor) (n : Nat) (env : Environment), cts.foldlM F (n, env) =
        (do
          let e ← ((cts.zipIdx n).map fun p => ctorVal c.lparams stats.params.size isUnsafe t p.1 p.2)
            |>.foldlM G env
          pure (n + cts.length, e)) := by
    intro t F G hF cts
    induction cts with
    | nil => intro n env; simp
    | cons ct cts ih =>
      intro n env
      simp only [List.foldlM_cons, List.zipIdx_cons, List.map_cons, hF, bind_assoc, pure_bind, ih]
      simp [Nat.add_assoc, Nat.add_comm 1]
  unfold declareConstructors
  rw [← Array.foldlM_toList, List.toList_toArray]
  unfold ctorVals
  generalize c.env = env
  induction types generalizing env with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldlM_cons, List.flatMap_cons, List.foldlM_append]
    rw [inner t _ (fun (env : Environment) v => do
      env.checkName v.name c.allowPrimitive; return env.add (.ctorInfo v)) (fun _ _ _ => by
        have h (a n : Nat) : (if n ≤ a then a - n else 0) = a - n := by split <;> omega
        simp [ctorVal, h])]
    simp only [bind_assoc, pure_bind]
    congr 1; funext e; exact ih e

theorem declareConstructors.WF {c : Context} {stats : InductiveStats}
    {types : List InductiveType} {isUnsafe : Bool} (mapWF : c.env.constants.WF) :
    (declareConstructors stats types.toArray isUnsafe c).WF fun env' =>
      let cis := (ctorVals c.lparams stats.params.size types isUnsafe).map .ctorInfo
      env'.constants = insertConsts c.env.constants cis ∧ env'.quotInit = c.env.quotInit ∧
      (cis.map (·.name)).Nodup ∧ (∀ ci ∈ cis, c.env.constants.find? ci.name = none) ∧
      (∀ ci ∈ cis, Environment.primitives.contains ci.name → c.allowPrimitive) := by
  rw [declareConstructors_eq]
  exact Lean4Lean.addChecked.WF mapWF c.allowPrimitive ConstantInfo.ctorInfo _

/-- How a constructor's fields `fs` elaborate its declared field domains `Ds`, under the
parameters and `k` earlier fields `Γ`: each field's type is its domain with annotations stripped,
in the sort `f.level`. -/
inductive FieldsElab (venv : VEnv) (d : VInductDecl) : List VExpr → Nat → List VExpr →
    List VField → Prop
  | nil : FieldsElab venv d Γ k [] []
  | cons :
    venv.IsDefEqU d.uvars Γ D f.type →
    venv.HasType d.uvars Γ f.type (.sort f.level) →
    f.level.WF d.uvars →
    FieldsElab venv d (f.type :: Γ) (k + 1) Ds fs →
    FieldsElab venv d Γ k (D :: Ds) (f :: fs)

/-- `d` elaborates the block: its sort agrees with the block's, and each constructor's type is a
translation of its declared type, a telescope of parameters and fields ending in its type at its
indices, whose fields `d` elaborates and each of whose fields' levels is zero exactly when a sort of
its declared domain is. -/
structure Elaborates (venv : VEnv) (U : List Name) (nparams : Nat) (level : VLevel)
    (types : List InductiveType) (d : VInductDecl) : Prop where
  level : d.level ≈ level
  types : List.Forall₂ (fun (t : InductiveType) (T : VInductiveType) =>
    T.name = t.name ∧ List.Forall₂ (fun (ct : Constructor) (c : VConstructor) =>
      c.name = ct.name ∧ TrExprS venv U [] ct.type c.type ∧ ∃ ps Ds, ps.length = nparams ∧
        Ds.length = c.fields.length ∧
        c.type = .foralls (ps ++ Ds) (.appN (.const t.name (VLevel.params U.length))
          (VExpr.bvars nparams Ds.length ++ c.indices)) ∧
        FieldsElab venv d d.params.reverse 0 Ds c.fields ∧
        ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f → ∀ u,
          venv.HasType U.length ((Ds.take k).reverse ++ ps.reverse) D (.sort u) →
          (u ≈ .zero ↔ f.level ≈ .zero)) t.ctors T.ctors) types d.types

theorem FieldsChecked.defeqDFC {venv : VEnv} {d : VInductDecl} (henv : venv.Ordered) {Γ₀ Γ₁ Γ₂}
    (hΓ : VEnv.IsDefEqCtx venv d.uvars Γ₀ Γ₁ Γ₂) {k Ds} (H : FieldsChecked venv d Γ₁ k Ds) :
    FieldsChecked venv d Γ₂ k Ds := by
  induction H generalizing Γ₂ with
  | nil => exact .nil
  | cons hu hpos _ ih =>
    obtain ⟨u, hD, hb⟩ := hu
    exact .cons ⟨u, hD.defeqDFC henv hΓ, hb⟩ (fun h => (hpos h).defeqDFC henv hΓ)
      (ih (.succ hΓ hD))

theorem FieldsWF.of_checked {venv : VEnv} {d : VInductDecl} (henv : venv.WF) {Γ k Ds fs}
    (hΓ : OnCtx Γ (venv.IsType d.uvars)) (H1 : FieldsChecked venv d Γ k Ds)
    (H2 : FieldsElab venv d Γ k Ds fs) : d.FieldsWF venv Γ k Ds fs := by
  induction H2 with
  | nil => exact .nil
  | cons hD hf hl _ ih =>
    cases H1 with
    | cons hu hpos hrest =>
    obtain ⟨u, hDu, hb⟩ := hu
    have hDf := hD.of_l henv hΓ hDu
    exact .cons hD hf hl ⟨u, hDf.hasType.2, hb⟩ (fun h => (hpos h).defeq henv hΓ hD)
      (ih ⟨hΓ, _, hf⟩ (hrest.defeqDFC henv.ordered (.succ .zero hDf)))

/-- A constructor that `checkConstructors` checked, as `mkRecInfos` elaborated it. -/
theorem ctor_WF {venv : VEnv} (henv : venv.WF) {U : List Name} {nparams : Nat} {d : VInductDecl}
    (hU : d.uvars = U.length) (hnp : d.params.length = nparams)
    (hparams : venv.IsTele d.uvars [] d.params)
    {t : InductiveType} {T : VInductiveType} {nidx : Nat} (hname : T.name = t.name)
    (hnidx : nidx = T.indices.length) {ct : Constructor} {c : VConstructor}
    {X : List VExpr → List VExpr → Prop}
    (hC : CtorChecked venv U d t nidx ct)
    (hE : c.name = ct.name ∧ TrExprS venv U [] ct.type c.type ∧ ∃ ps Ds, ps.length = nparams ∧
        Ds.length = c.fields.length ∧
        c.type = .foralls (ps ++ Ds) (.appN (.const t.name (VLevel.params U.length))
          (VExpr.bvars nparams Ds.length ++ c.indices)) ∧
        FieldsElab venv d d.params.reverse 0 Ds c.fields ∧ X ps Ds) :
    c.WF venv d T ∧ declareConstructors.arity 0 ct.type = nparams + c.fields.length := by
  obtain ⟨-, htr, ps, Ds, hps, hDs, hty, hfe, -⟩ := hE
  obtain ⟨hT, ps', Ds', idx, hty', har, htele, hidx, hmen, hfc⟩ := hC _ htr
  rw [hty] at hty'
  have ⟨h1, h2⟩ := VExpr.foralls_inj (VExpr.appN_notPi (e := .const ..) _ trivial)
    (VExpr.appN_notPi (e := .const ..) _ trivial) hty'
  have hlen : ps.length = ps'.length := by rw [hps, ← hnp, htele.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj h1 hlen
  have h3 := VExpr.appN_const_inj h2
  rw [hnp] at h3
  obtain rfl := List.append_cancel_left h3
  rw [← hU] at hT htele
  have hctx := htele.defeqCtx henv .zero trivial hparams
  simp only [List.append_nil] at hctx
  refine ⟨⟨hT, ⟨ps, Ds, ?_, htele, FieldsWF.of_checked henv (by simpa using hparams.onCtx trivial)
    (hfc.defeqDFC henv.ordered hctx) hfe⟩, hidx.trans hnidx, hmen⟩, by rw [har, hps, hDs]⟩
  rw [hty, hname, hU, hnp, hDs]

/-- The type `run` gives the `i`th recursor, from the local variables `mkRecInfos` opened. -/
def recTypeExpr (lctx : LocalContext) (stats : InductiveStats) (recInfos : Array RecInfo)
    (info : RecInfo) : Expr :=
  lctx.mkForall stats.params <|
  lctx.mkForall (recInfos.map (·.motive)) <|
  lctx.mkForall (recInfos.flatMap (·.minors)) <|
  recTypeTail info.motive info.motiveType

/-- What `mkRecInfos` establishes, for the continuation it calls with `recInfos` in `c`: the
block elaborates to a declaration `d`, whose recursors' types are what the local variables
`mkRecInfos` opened abstract to. -/
structure RecInfosData (c₂ : VContext) (nparams : Nat) (types : List InductiveType)
    (stats : InductiveStats) (params : List VExpr) (level : VLevel) (typeTr : List VExpr)
    (isUnsafe : Bool) (elimLevel : Level) (recInfos : Array RecInfo) (c : VContext)
    (d : VInductDecl) : Prop where
  venv : c₂.venv ≤ c.venv
  /-- The motives may be at a universe that is not the block's, so the continuation runs with it
  added to the block's level parameters. -/
  lparams : c.lparams = mkRecInfosLevelParams elimLevel c₂.lparams
  allowPrimitive : c.allowPrimitive = c₂.allowPrimitive
  safety : c.safety = c₂.safety
  size : recInfos.size = types.length
  elaborates : Elaborates c₂.venv c₂.lparams nparams level types d
  uvars : d.uvars = c₂.lparams.length
  params : d.params = params
  level : d.level = level
  isUnsafe : d.isUnsafe = isUnsafe
  isRec : d.isRec = isRec types.toArray stats.indConsts
  /-- A field `isRecArg` sees as recursive has an occurrence of the block in its declared domain,
  which is what `isRec` looks for: reduction does not introduce the block's names. -/
  isRecArgs : d.isRec = false → ∀ T ∈ d.types, ∀ c ∈ T.ctors, ∀ f ∈ c.fields, f.recArg = none
  largeElim : d.LargeElim ↔ elimLevel ≠ .zero
  typeTr : List.Forall₂ (fun (T : VInductiveType) T' => T.type = T') d.types typeTr
  /-- The index telescopes and recursive views `mkRecInfos` normalizes, in the environment it
  runs in, with the constructors. -/
  normalized : ∀ envC, c₂.venv.addConstList d.ctorConsts = some envC →
    ∀ T ∈ d.types, T.WF envC d ∧ ∀ c ∈ T.ctors, d.RecArgsWF envC c
  nindices : ∀ (i : Nat) (T : VInductiveType), d.types[i]? = some T →
    stats.nindices[i]? = some T.indices.length
  /-- The recursor's type mentions the constructors, which the checking environment does not
  have yet, so it translates in any extension that has them. -/
  recType : ∀ (i : Nat) (T : VInductiveType) info, d.types[i]? = some T → recInfos[i]? = some info →
    ∀ envC : VEnv, c₂.venv ≤ envC → envC.WF →
      (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
      TrExprS envC (getRecLevelParams elimLevel c₂.lparams) []
        (recTypeExpr c.lctx stats recInfos info) (d.recType d.recLevels d.motiveLevel i T)

/-- `mkRecInfos`, in the checking environment with the constructors added as axioms. Its
constructors' fields are read as `d`'s fields, which `run` then builds the recursors from. -/
theorem mkRecInfos.WF {c₀ c₁ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c₁ params level typeTr)
    (hc : c.mlctx = c₁.mlctx) (hU : c.lparams = c₁.lparams) (hle : c₀.venv ≤ c.venv)
    (henv : c.venv.WF) (hann : c.venv.AnnotationsErase) {isUnsafe : Bool}
    (hp : c.allowPrimitive = false)
    (hC : ∀ d, Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked c.venv c.lparams d t nidx ct)
    (hCt : ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors,
      ∃ C', TrExprS c.venv c.lparams [] ct.type C')
    {elimLevel : Level} {k : Array RecInfo → M α} {Q}
    (H : ∀ recInfos c' d,
      RecInfosData c nparams types stats params level typeTr isUnsafe elimLevel recInfos c' d →
      WF c' (k recInfos) Q) :
    WF c (do withEnv (← declareCtorAxioms types.toArray isUnsafe) <|
      withReader (fun ctx => { ctx with lparams := mkRecInfosLevelParams elimLevel ctx.lparams }) <|
      mkRecInfos stats types.toArray elimLevel k) Q :=
  sorry

/-- `declareRecursors`: it adds one recursor per type, each translating, in any model of the
environment with the block's types and constructors, to the spec's recursor, with its rules
translating to the iota rules in any model that also has the recursors. -/
theorem declareRecursors.WF {c₂ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr isUnsafe elimLevel recInfos d}
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c d)
    (hE : d.LargeElim ↔ elimLevel ≠ .zero)
    (hEu : elimLevel = .zero ∨ ∃ u, elimLevel = .param u ∧ u ∉ c₂.lparams)
    {kflag : Bool} (hK : kflag = true ↔ d.IsKTarget) {envCtors : Environment}
    (mapWF : envCtors.constants.WF) :
    WF c (declareRecursors envCtors c₂.lparams stats types.toArray elimLevel kflag recInfos)
      fun env' =>
      ∃ recs : List RecursorVal,
        env'.constants = insertConsts envCtors.constants (recs.map .recInfo) ∧
        env'.quotInit = envCtors.quotInit ∧
        ((recs.map ConstantInfo.recInfo).map (·.name)).Nodup ∧
        (∀ ci ∈ recs.map ConstantInfo.recInfo, envCtors.constants.find? ci.name = none) ∧
        (∀ ci ∈ recs.map ConstantInfo.recInfo,
          Environment.primitives.contains ci.name → c.allowPrimitive) ∧
        List.Forall₂ (fun v (p : VInductiveType × Nat) => v.name = Lean.mkRecName p.1.name)
          recs d.types.zipIdx ∧
        ∀ (envC envR : VEnv), c₂.venv ≤ envC → envC.WF →
          (∀ p ∈ d.ctorConsts, envC.constants p.1 = some p.2) →
          envC.addConstList d.recConsts = some envR → envR.WF →
          List.Forall₂ (fun v (p : VInductiveType × Nat) =>
            TrRecVal d c₂.lparams envR p.2 p.1 v ∧
            TrConstant c.safety envC (.recInfo v)
              ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩)
            recs d.types.zipIdx :=
  sorry

theorem typeConsts_eq {U : Nat} {X : InductiveType → VInductiveType → Prop} :
    ∀ {types : List InductiveType} {Ts : List VInductiveType} {typeTr : List VExpr},
    List.Forall₂ (fun t T => T.name = t.name ∧ X t T) types Ts →
    List.Forall₂ (fun (T : VInductiveType) T' => T.type = T') Ts typeTr →
    Ts.map (fun T => (T.name, (⟨U, T.type⟩ : VConstant))) = typeConstsOf U types typeTr
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    simp only [List.map_cons, typeConstsOf, List.zipWith_cons_cons, h₁.1, h₂]
    exact congrArg _ (typeConsts_eq t₁ t₂)

/-- What the phases established about the elaborated `d` makes it a well-formed declaration. -/
theorem decl_WF {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    (hne : types ≠ []) {venvAx : VEnv}
    (hAx : c.venv.addConstList (typeConstsOf c.lparams.length types typeTr) = some venvAx)
    (henvAx : venvAx.WF) {isUnsafe : Bool} {d : VInductDecl}
    (hC : Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked venvAx c.lparams d t nidx ct)
    {c₂ c₃ : VContext} {elimLevel recInfos} (hc₂ : c₂.venv = venvAx) (hc₂U : c₂.lparams = c.lparams)
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c₃ d)
    (hLE : elimLevel ≠ .zero → d.LargeElimOK) :
    d.WF c.venv := by
  have hEl : Elaborates venvAx c.lparams nparams level types d := hc₂ ▸ hc₂U ▸ hR.elaborates
  have hU : d.uvars = c.lparams.length := hR.uvars.trans (by rw [hc₂U])
  have hlen : d.params.length = nparams := hR.params ▸ hT.nparams
  have hle := VEnv.addConstList_le hAx
  have hU₀ : c.lparams = c₀.lparams := hT.base.lparams
  have hV₀ : c.venv = c₀.venv := hT.base.venv
  have hcompat : Compat c.lparams params level isUnsafe types stats.nindices d :=
    ⟨hU, hR.params, hR.level, hR.isUnsafe,
      (List.Forall₂.map_eq (f := fun t : InductiveType => t.name) (g := fun T : VInductiveType => T.name)
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.symm) hEl.types)).symm,
      hR.nindices⟩
  have htypes (T) (hTm : T ∈ d.types) : ∃ (j : Nat) (t : InductiveType), d.types[j]? = some T ∧ types[j]? = some t ∧
      typeTr[j]? = some T.type := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hTm
    obtain ⟨t, ht, -⟩ := List.Forall₂.getElem?_r hEl.types hj
    obtain ⟨T', hT', e⟩ := List.Forall₂.getElem?_l hR.typeTr hj
    exact ⟨j, t, hj, ht, e ▸ hT'⟩
  have hd : d.typeConsts = typeConstsOf c.lparams.length types typeTr := by
    rw [VInductDecl.typeConsts, hU]
    exact typeConsts_eq (X := fun _ _ => _) hEl.types hR.typeTr
  refine ⟨fun h => hne ?_, ?_, ?_, fun T hTm => ?_, fun env' h T hTm => ?_,
    fun env' envC h hCC => ?_, hR.isRecArgs, fun h => hLE (hR.largeElim.1 h)⟩
  · exact List.eq_nil_of_length_eq_zero ((Lean4Lean.List.Forall₂.length_eq hEl.types).trans (by rw [h]; rfl))
  · rw [hR.level, hU, hU₀]; exact .of_ofLevel hT.resultLevel
  · rw [hR.params, hU, hU₀, hV₀]; exact hT.params_tele
  · obtain ⟨j, t, -, ht, hT'⟩ := htypes T hTm
    obtain ⟨_, _, -, h, -⟩ := hT.types j t _ ht hT'
    rw [hU, hU₀, hV₀]; exact h
  · obtain rfl : env' = venvAx := Option.some.inj (h.symm.trans (hd ▸ hAx))
    obtain ⟨j, t, hj, ht, -⟩ := htypes T hTm
    obtain ⟨t', ht', hname, hcs⟩ := List.Forall₂.getElem?_r hEl.types hj
    obtain rfl : t = t' := Option.some.inj (ht.symm.trans ht')
    intro c hc
    obtain ⟨ct, hct, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcs c hc
    have hps : env'.IsTele d.uvars [] d.params := by
      rw [hR.params, hU, hU₀]; exact (hV₀ ▸ hT.params_tele).mono hle
    exact (ctor_WF henvAx hU hlen hps hname rfl
      (hC hcompat j t ht ct hct _ (hR.nindices j T hj)) hrel).1
  · obtain rfl : env' = venvAx := Option.some.inj (h.symm.trans (hd ▸ hAx))
    exact hR.normalized envC (hc₂ ▸ hCC)

theorem inductVals_length {lparams : List Name} {stats : InductiveStats} {np nn : Nat}
    {types : List InductiveType} {isUnsafe : Bool} (h : stats.nindices.size = types.length) :
    (inductVals lparams stats np types.toArray nn isUnsafe).length = types.length := by
  simp [inductVals, h]

theorem inductVals_getElem? {lparams : List Name} {stats : InductiveStats} {np nn : Nat}
    {types : List InductiveType} {isUnsafe : Bool} {j : Nat} {t : InductiveType} {ni : Nat}
    (ht : types[j]? = some t) (hn : stats.nindices[j]? = some ni) :
    ∃ v, (inductVals lparams stats np types.toArray nn isUnsafe)[j]? = some v ∧
      v.name = t.name ∧ v.levelParams = lparams ∧ v.type = t.type ∧ v.numParams = np ∧
      v.numIndices = ni ∧ v.all = types.map (·.name) ∧ v.ctors = t.ctors.map (·.name) ∧
      v.numNested = nn ∧ v.isRec = isRec types.toArray stats.indConsts ∧ v.isUnsafe = isUnsafe := by
  refine ⟨{ t with
    numParams := np, numIndices := ni, all := types.toArray.map (·.name) |>.toList, numNested := nn
    isUnsafe, levelParams := lparams, ctors := t.ctors.map (·.name)
    isRec := isRec types.toArray stats.indConsts
    isReflexive := isReflexive types.toArray stats.indConsts }, ?_, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl⟩
  · simp [inductVals, List.getElem?_zipWith, ht, Array.getElem?_toList, hn]
  · simp

theorem names_eq {venv U nparams level types} {d : VInductDecl}
    (hEl : Elaborates venv U nparams level types d) : types.map (·.name) = d.names :=
  List.Forall₂.map_eq (f := fun t : InductiveType => t.name) (g := fun T : VInductiveType => T.name)
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.symm) hEl.types)

theorem RecInfosData.compat {c₂ : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr isUnsafe elimLevel recInfos c d}
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c d) :
    Compat c₂.lparams params level isUnsafe types stats.nindices d :=
  ⟨hR.uvars, hR.params, hR.level, hR.isUnsafe, (names_eq hR.elaborates).symm, hR.nindices⟩

theorem inductVals_tr {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    {isUnsafe : Bool} (hsafety : c₀.safety = inductSafety isUnsafe)
    {c₂ c₃ : VContext} {elimLevel recInfos d} (hc₂U : c₂.lparams = c.lparams)
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c₃ d) :
    List.Forall₂ (fun v T => TrInductVal d c.lparams T v ∧
      TrConstant c₀.safety c₀.venv (.inductInfo v) ⟨d.uvars, T.type⟩)
      (inductVals c.lparams stats nparams types.toArray 0 isUnsafe) d.types := by
  have hEl := hR.elaborates
  refine List.forall₂_of_getElem? ((inductVals_length hT.nindices).trans
    (Lean4Lean.List.Forall₂.length_eq hEl.types)) fun j v T hv hTj => ?_
  obtain ⟨t, ht, hname, hcs⟩ := List.Forall₂.getElem?_r hEl.types hTj
  obtain ⟨v', hv', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    inductVals_getElem? (lparams := c.lparams) (np := nparams) (nn := 0) (isUnsafe := isUnsafe)
      ht (hR.nindices j T hTj)
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain ⟨T', hT', e⟩ := List.Forall₂.getElem?_l hR.typeTr hTj
  obtain ⟨-, -, htr, -⟩ := hT.types j t T' ht hT'
  refine ⟨⟨h1.trans hname.symm, h2, h4.trans (hR.params ▸ hT.nparams).symm, h5,
    h6.trans (names_eq hEl), h7.trans ?_, h8, h9.trans hR.isRec.symm, h10.trans hR.isUnsafe.symm⟩,
    ?_, ?_, ?_⟩
  · exact List.Forall₂.map_eq (f := fun ct : Constructor => ct.name)
      (g := fun c : VConstructor => c.name) (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.symm) hcs)
  · rw [hsafety]
    simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h10]
    cases isUnsafe <;> exact DefinitionSafety.le_rfl
  · show v.levelParams.length = d.uvars
    rw [h2, hR.uvars, hc₂U]
  · show TrExprS c₀.venv v.levelParams [] v.type T.type
    rw [h2, h3, e, hT.base.lparams]; exact htr

theorem forall₂_flatMap_ctors {β : Type} {g : InductiveType → Constructor → Nat → β}
    {Q : Nat → VConstructor → β → Prop} :
    ∀ (ts : List InductiveType) (Ts : List VInductiveType) (j0 : Nat), ts.length = Ts.length →
    (∀ (j : Nat) t T, ts[j]? = some t → Ts[j]? = some T →
      List.Forall₂ (fun v c => Q (j0 + j) c v) (t.ctors.zipIdx.map fun p => g t p.1 p.2) T.ctors) →
    List.Forall₂ (fun v (p : Nat × VConstructor) => Q p.1 p.2 v)
      (ts.flatMap fun t => t.ctors.zipIdx.map fun p => g t p.1 p.2)
      ((Ts.zipIdx j0).map fun (T, j) => T.ctors.map (j, ·)).flatten
  | [], [], _, _, _ => .nil
  | t :: ts, T :: Ts, j0, hl, H => by
    simp only [List.flatMap_cons, List.zipIdx_cons, List.map_cons, List.flatten_cons]
    refine List.Forall₂.append ?_ (forall₂_flatMap_ctors ts Ts (j0 + 1) (by simpa using hl)
      fun j t T h₁ h₂ => ?_)
    · have := H 0 t T rfl rfl
      simp only [Nat.add_zero] at this
      simpa [List.forall₂_map_right_iff] using this
    · have := H (j + 1) t T h₁ h₂
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this

theorem params_size {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr) :
    stats.params.size = nparams := by
  obtain ⟨_, _, fvs, h1, h2⟩ := hT.paramsCtx
  rw [← Array.length_toList, h2, List.length_map, h1.length_eq, hT.nparams]

theorem ctorVals_tr {c₀ c : VContext} {nparams : Nat} {types : List InductiveType}
    {stats params level typeTr} (hT : TypesData c₀ nparams types stats c params level typeTr)
    {isUnsafe : Bool} (hsafety : c.safety = inductSafety isUnsafe)
    {venvAx : VEnv} (henvAx : venvAx.WF) (hle : c.venv ≤ venvAx) {d : VInductDecl}
    (hC : Compat c.lparams params level isUnsafe types stats.nindices d →
      ∀ (j : Nat) (t : InductiveType), types[j]? = some t → ∀ ct ∈ t.ctors, ∀ nidx,
        stats.nindices[j]? = some nidx → CtorChecked venvAx c.lparams d t nidx ct)
    {c₂ c₃ : VContext} {elimLevel recInfos} (hc₂ : c₂.venv = venvAx) (hc₂U : c₂.lparams = c.lparams)
    (hR : RecInfosData c₂ nparams types stats params level typeTr isUnsafe elimLevel recInfos c₃ d) :
    List.Forall₂ (fun v (j, c') => TrCtorVal d c.lparams j c' v ∧
      TrConstant c.safety venvAx (.ctorInfo v) ⟨d.uvars, c'.type⟩)
      (ctorVals c.lparams stats.params.size types isUnsafe) d.ctors := by
  have hEl : Elaborates venvAx c.lparams nparams level types d := hc₂ ▸ hc₂U ▸ hR.elaborates
  have hU : d.uvars = c.lparams.length := hR.uvars.trans (by rw [hc₂U])
  have hlen : d.params.length = nparams := hR.params ▸ hT.nparams
  have hcompat : Compat c.lparams params level isUnsafe types stats.nindices d :=
    ⟨hU, hR.params, hR.level, hR.isUnsafe, (names_eq hEl).symm, hR.nindices⟩
  have hps : venvAx.IsTele d.uvars [] d.params := by
    rw [hR.params, hU, hT.base.lparams]; exact (hT.base.venv ▸ hT.params_tele).mono hle
  rw [params_size hT]
  refine forall₂_flatMap_ctors (g := ctorVal c.lparams nparams isUnsafe)
    (Q := fun j c' v => TrCtorVal d c.lparams j c' v ∧
      TrConstant c.safety venvAx (.ctorInfo v) ⟨d.uvars, c'.type⟩) _ _ 0
    (Lean4Lean.List.Forall₂.length_eq hEl.types) fun j t T ht hTj => ?_
  rw [Nat.zero_add]
  obtain ⟨t', ht', hname, hcs⟩ := List.Forall₂.getElem?_r hEl.types hTj
  obtain rfl : t = t' := Option.some.inj (ht.symm.trans ht')
  refine List.forall₂_of_getElem? (by simp [Lean4Lean.List.Forall₂.length_eq hcs])
    fun q v c' hv hc' => ?_
  obtain ⟨ct, hct, hrel⟩ := List.Forall₂.getElem?_r hcs hc'
  have hv' : v = ctorVal c.lparams nparams isUnsafe t ct q := by
    simp [List.getElem?_zipIdx, hct] at hv; exact hv.symm
  subst hv'
  obtain ⟨-, har⟩ := ctor_WF henvAx hU hlen hps hname rfl
    (hC hcompat j t ht ct (List.mem_of_getElem? hct) _ (hR.nindices j T hTj)) hrel
  refine ⟨⟨T, hTj, hc', hrel.1.symm, rfl, hname.symm, hlen.symm, ?_, hR.isUnsafe.symm⟩, ?_, ?_, ?_⟩
  · show declareConstructors.arity 0 ct.type - nparams = c'.fields.length
    omega
  · rw [hsafety]
    simp only [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, ctorVal]
    cases isUnsafe <;> exact DefinitionSafety.le_rfl
  · exact hU.symm
  · exact hrel.2.1

end AddInductive

end Lean4Lean

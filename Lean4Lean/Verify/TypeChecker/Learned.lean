import Lean4Lean.Verify.TypeChecker.Levels
import Lean4Lean.Verify.NameGenerator

/-!
# Facts learned at a level

A fact the type checker learns (a cached result, or a recorded equivalence) is labelled with the
deepest level of the facts it rests on. It holds in the context of that level, and in every
context extending it that declares as the context it was learned in did both the variables that
context declared and those the name generator had made by then (`Admits`): a computation that used
nothing deeper runs the same way there. So it survives leaving the deeper scopes, and stays true in
the scopes opened later. The context it was learned in may itself be one a computation is run again
in, with variables the name generator makes only later; `Admits` keeps those as they are, and a run
never makes a variable its context declares (`Keeps`).
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- The free variables `lctx` declares. -/
def _root_.Lean.LocalContext.Dom (lctx : LocalContext) (fv : FVarId) : Prop :=
  (lctx.find? fv).isSome

/-- The name generator `g'` made none of the variables `L` declares that `g` had not: a run from
`g` to `g'` declares each variable it makes afresh (`withFreshId`). -/
def Keeps (L : LocalContext) (g g' : NameGenerator) : Prop :=
  ∀ fv, L.Dom fv → ¬g.Reserves fv → ¬g'.Reserves fv

theorem Keeps.refl (L : LocalContext) (g : NameGenerator) : Keeps L g g := fun _ _ h => h

theorem Keeps.trans {L : LocalContext} {g₁ g₂ g₃ : NameGenerator} (h₁ : Keeps L g₁ g₂)
    (h₂ : Keeps L g₂ g₃) : Keeps L g₁ g₃ := fun fv h1 h2 => h₂ fv h1 (h₁ fv h1 h2)

/-- Making a variable the context does not declare keeps it. -/
theorem Keeps.next {L : LocalContext} {g : NameGenerator} (h : L.find? ⟨g.curr⟩ = none) :
    Keeps L g g.next := by
  intro fv hd hr hr'
  rcases NameGenerator.reserves_next.1 hr' with hr' | rfl
  · exact hr hr'
  · simp [LocalContext.Dom, h] at hd

theorem Keeps.of_dom {L L' : LocalContext} {g g' : NameGenerator} (h : Keeps L' g g')
    (hL : ∀ fv, L.Dom fv → L'.Dom fv) : Keeps L g g' := fun fv h1 h2 => h fv (hL fv h1) h2

/-- Each declaration mentions only variables declared before it. -/
def _root_.Lean.LocalContext.WellScoped (L : LocalContext) : Prop :=
  ∀ fv d, L.find? fv = some d →
    (∀ x ∈ d.type.fvarsList, L.Dom x) ∧ ∀ x ∈ d.value'.fvarsList, L.Dom x

/-- `L₂` declares as `L` does every variable that `L` declares or that the name generator `g`
had made, and keeps the variables `L` declares that `g` had not made: a context a computation run
in `L`, with the name generator ending at `g`, runs the same way in. The variables of `L` that `g`
had not made are ones a computation run again from `L` was given (a context a fact learned
earlier is used in): the facts learned in `L` may mention them. -/
structure Admits (L : LocalContext) (g : NameGenerator) (L₂ : LocalContext) : Prop where
  agree : ∀ fv d, L₂.find? fv = some d → g.Reserves fv ∨ L.Dom fv →
    (L.find? fv).map LocalDecl.erase = some d.erase
  keep : ∀ fv, L.Dom fv → ¬g.Reserves fv → L₂.Dom fv

theorem Admits.refl (L : LocalContext) (g : NameGenerator) : Admits L g L :=
  ⟨fun _ _ h _ => by rw [h]; rfl, fun _ h _ => h⟩

theorem Admits.find? {L L₂ : LocalContext} {g : NameGenerator} (H : Admits L g L₂) {fv d}
    (h : L₂.find? fv = some d) (hd : g.Reserves fv ∨ L.Dom fv) :
    ∃ d', L.find? fv = some d' ∧ d'.erase = d.erase := by
  have e := H.agree fv d h hd
  cases h' : L.find? fv with
  | none => rw [h'] at e; cases e
  | some d' => rw [h'] at e; exact ⟨d', rfl, Option.some.inj e⟩

theorem Keeps.of_admits {L L₂ : LocalContext} {g g₁ g₂ : NameGenerator} (H : Admits L g L₂)
    (hk : Keeps L g g₁) (h : Keeps L₂ g₁ g₂) : Keeps L g g₂ :=
  fun fv h1 h2 => h fv (H.keep fv h1 h2) (hk fv h1 h2)

/-- Admitting composes, as long as the variables `L` declares that `g` had not made were not
made by `g'`. -/
theorem Admits.trans {L L₁ L₂ : LocalContext} {g g' : NameGenerator} (H₁ : Admits L g L₁)
    (H₂ : Admits L₁ g' L₂) (hg : g ≤ g') (hk : Keeps L g g') : Admits L g L₂ := by
  refine ⟨fun fv d h1 h2 => ?_, fun fv h1 h2 => H₂.keep fv (H₁.keep fv h1 h2) (hk fv h1 h2)⟩
  have h2' : g'.Reserves fv ∨ L₁.Dom fv := by
    by_cases hr : g.Reserves fv
    · exact .inl (hr.mono hg)
    · exact .inr (H₁.keep fv (h2.resolve_left hr) hr)
  obtain ⟨d₁, hd₁, e₁⟩ := H₂.find? h1 h2'
  rw [← e₁]
  exact H₁.agree fv d₁ hd₁ h2

/-- A smaller context keeps admitting, if it keeps the variables `L` declares that `g` had not
made. -/
theorem Admits.below {L : LocalContext} {g : NameGenerator} {m m' : MLCtx} (H : Admits L g m'.lctx)
    (hb : m.Below m') (wf : m'.WF env Us) (hk : ∀ fv, L.Dom fv → ¬g.Reserves fv → m.lctx.Dom fv) :
    Admits L g m.lctx := by
  refine ⟨fun fv d h1 h2 => ?_, hk⟩
  have hx : fv ∈ m.vlctx.fvars := (hb.wf wf).tr.find?_eq_some.1 ⟨_, h1⟩
  exact H.agree fv d (by rw [hb.find? hx wf, h1]) h2

/-- Declaring variables that `L` does not declare and the name generator has not made keeps
admitting. -/
theorem Admits.above {L : LocalContext} {g : NameGenerator} {m m' : MLCtx} (H : Admits L g m.lctx)
    (hb : m.Below m') (wf : m'.WF env Us)
    (hnew : ∀ fv ∈ m'.vlctx.fvars, fv ∉ m.vlctx.fvars → ¬g.Reserves fv ∧ ¬L.Dom fv) :
    Admits L g m'.lctx := by
  refine ⟨fun fv d h1 h2 => ?_, fun fv h1 h2 => ?_⟩
  · have hx' : fv ∈ m'.vlctx.fvars := wf.tr.find?_eq_some.1 ⟨_, h1⟩
    by_cases hx : fv ∈ m.vlctx.fvars
    · exact H.agree fv d (by rw [← hb.find? hx wf, h1]) h2
    · obtain ⟨n1, n2⟩ := hnew fv hx' hx
      exact (h2.elim n1 n2).elim
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (H.keep fv h1 h2)
    have hx : fv ∈ m.vlctx.fvars := (hb.wf wf).tr.find?_eq_some.1 ⟨_, hd⟩
    rw [LocalContext.Dom, hb.find? hx wf, hd]; rfl

/-- A fact `P` about contexts, learned with base `base`, in the context `L`, with the name
generator at `g`: it holds in every well-formed context extending `base` that admits `L`. -/
def Learned (env : VEnv) (Us : List Name) (base : MLCtx) (L : LocalContext) (g : NameGenerator)
    (P : MLCtx → Prop) : Prop :=
  ∀ m, m.WF env Us → base.Below m → Admits L g m.lctx → P m

theorem Learned.base {base base' : MLCtx} (H : Learned env Us base L g P) (h : base.Below base') :
    Learned env Us base' L g P :=
  fun m wf hb ha => H m wf (h.trans hb) ha

/-- What the state's record of a fact learned at level `l` asserts in the context `c`, whose open
scopes declare `fvs`, with the name generator at `g₀`: unless the level is above the ceiling, the
fact was learned in a context `c` admits, and holds as `Learned` says from the level's context.
`top` is the context a computation run again with a ceiling started from. -/
def Holds (c : VContext) (fvs : Array FVarId) (top : MLCtx) (g₀ : NameGenerator) (l : Nat)
    (P : MLCtx → Prop) : Prop :=
  c.ceiling.all (l ≤ ·) → ∃ L g, g ≤ g₀ ∧ Keeps L g g₀ ∧ Admits L g c.lctx ∧
    Learned c.venv c.lparams (levelCtx c.mlctx fvs c.ceiling top l) L g P

/-- A fact holds in the context it is recorded in. -/
theorem Holds.now {c : VContext} (H : Holds c fvs top g₀ l P)
    (hS : ScopeShape c.mlctx fvs c.ceiling top) (hc : c.ceiling.all (l ≤ ·)) : P c.mlctx := by
  obtain ⟨L, g, -, -, ha, H⟩ := H hc
  exact H _ c.mlctx_wf (hS.levelCtx_below _) (c.lctx_eq ▸ ha)

/-- A run that made none of the context's variables keeps what holds. -/
theorem Holds.mono {c : VContext} (H : Holds c fvs top g₀ l P) (h : g₀ ≤ g₁)
    (hk : Keeps c.lctx g₀ g₁) : Holds c fvs top g₁ l P :=
  fun hc => let ⟨L, g, h1, k, h2, h3⟩ := H hc; ⟨L, g, h1.trans h, k.of_admits h2 hk, h2, h3⟩

theorem Holds.imp {c : VContext} (H : Holds c fvs top g₀ l P) (h : ∀ m, P m → Q m) :
    Holds c fvs top g₀ l Q :=
  fun hc => let ⟨L, g, h1, k, h2, h3⟩ := H hc; ⟨L, g, h1, k, h2, fun m a b d => h m (h3 m a b d)⟩

/-- The level contexts of a context declaring one more variable `x` on top, as a new scope,
extend those of the context. -/
theorem levelCtx_below_push {m m' top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {l : Nat}
    (H : ScopeShape m fvs ceil top) (hb : m.Below m') (wf' : m'.WF env Us) {x : FVarId}
    (hx : m'.under x = m) :
    (levelCtx m fvs ceil top l).Below (levelCtx m' (fvs.push x) ceil top l) := by
  rcases Nat.lt_or_ge l fvs.size with hl | hl
  · rw [levelCtx_push H hl x hb wf']; exact .refl
  · by_cases hc : ceil.all (l < ·)
    · rw [levelCtx_none (Array.getElem?_eq_none_iff.2 hl) hc]
      rcases Nat.lt_or_ge l (fvs.push x).size with hl' | hl'
      · obtain rfl : l = fvs.size := by simp at hl'; omega
        rw [levelCtx_push_top hc hx]; exact .refl
      · rw [levelCtx_none (Array.getElem?_eq_none_iff.2 hl') hc]; exact hb
    · rw [levelCtx_top hc, levelCtx_top hc]; exact .refl

/-- Opening a scope for a variable the name generator has not made keeps what holds. -/
theorem Holds.push {c c' : VContext} (H : Holds c fvs top g₀ l P)
    (hS : ScopeShape c.mlctx fvs c.ceiling top)
    (hb : c.mlctx.Below c'.mlctx) {x : FVarId} (hx : c'.mlctx.under x = c.mlctx)
    (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (hnew : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → ¬g₀.Reserves fv) (h : g₀ ≤ g₁)
    (hk : Keeps c.lctx g₀ g₁) :
    Holds c' (fvs.push x) top g₁ l P := by
  intro hc'
  obtain ⟨L, g, h1, k, h2, h3⟩ := H (hc ▸ hc')
  refine ⟨L, g, h1.trans h, k.of_admits h2 hk, ?_, ?_⟩
  · rw [← c'.lctx_eq]
    refine (c.lctx_eq ▸ h2).above hb c'.mlctx_wf fun fv a b => ?_
    have hr : ¬g.Reserves fv := mt (·.mono h1) (hnew fv a b)
    refine ⟨hr, fun hL => b ?_⟩
    have := (c.lctx_eq ▸ h2).keep fv hL hr
    exact c.mlctx_wf.tr.find?_eq_some.1 (Option.isSome_iff_exists.1 this)
  · rw [hv, hl, hc]
    exact h3.base (levelCtx_below_push hS hb (hv ▸ hl ▸ c'.mlctx_wf) hx)

/-- Closing the scope of the variable `x` keeps what holds at the levels up to the enclosing
one. -/
theorem Holds.pop {c c' : VContext} (H : Holds c' (fvs.push x) top g₁ l P)
    (hS : ScopeShape c.mlctx fvs c.ceiling top) (hl : l ≤ fvs.size)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under x = c.mlctx)
    (hv : c'.venv = c.venv) (hlp : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (hmade : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → g₁.Reserves fv) :
    Holds c fvs top g₁ l P := by
  intro hc'
  obtain ⟨L, g, h1, k, h2, h3⟩ := H (hc ▸ hc')
  refine ⟨L, g, h1, k, ?_, ?_⟩
  · rw [← c.lctx_eq]; rw [← c'.lctx_eq] at h2
    refine h2.below hb c'.mlctx_wf fun fv hL hr => ?_
    have hd' := h2.keep fv hL hr
    have hx' : fv ∈ c'.vlctx.fvars :=
      c'.mlctx_wf.tr.find?_eq_some.1 (Option.isSome_iff_exists.1 hd')
    by_cases hin : fv ∈ c.vlctx.fvars
    · exact Option.isSome_iff_exists.2 (c.mlctx_wf.tr.find?_eq_some.2 hin)
    · exact (k fv hL hr (hmade fv hx' hin)).elim
  · rw [hv, hlp, hc] at h3
    have e : levelCtx c'.mlctx (fvs.push x) c.ceiling top l =
        levelCtx c.mlctx fvs c.ceiling top l := by
      rcases Nat.lt_or_ge l fvs.size with hl' | hl'
      · exact levelCtx_push hS hl' x hb (hv ▸ hlp ▸ c'.mlctx_wf)
      · obtain rfl : l = fvs.size := by omega
        by_cases hvis : c.ceiling.all (fvs.size < ·)
        · rw [levelCtx_push_top hvis hx, levelCtx_none (by simp) hvis]
        · rw [levelCtx_top hvis, levelCtx_top hvis]
    exact e ▸ h3

/-- A visible scope's variable is declared in the context of the next level. -/
theorem ScopeShape.mem_levelCtx_succ {m top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat}
    (H : ScopeShape m fvs ceil top) {l : Nat} {fv : FVarId} (e : fvs[l]? = some fv)
    (hc : ceil.all (l < ·)) : fv ∈ (levelCtx m fvs ceil top (l + 1)).vlctx.fvars := by
  by_cases hc' : ceil.all (l + 1 < ·)
  · cases e' : fvs[l + 1]? with
    | none => rw [levelCtx_none e' hc']; exact H.mem l fv e hc
    | some fv' => rw [levelCtx_some e' hc']; exact H.order l fv fv' e e' hc'
  · rw [levelCtx_top hc']
    obtain ⟨lab, rfl⟩ : ∃ lab, ceil = some lab := by cases ceil <;> simp_all
    have : lab = l + 1 := by simp at hc hc'; omega
    subst this
    exact (H.top _ rfl).2.2 fv (by simpa using e) (by omega)

/-- A context `m₂` extending the level-`lab` context of `m`, below its open scopes, has the open
scopes up to `lab` declared in order, with the levels from `lab` up set aside and standing for
`m₂` itself: the shape of a context a computation is run again in with a ceiling. -/
theorem ScopeShape.rerun {m m₂ top : MLCtx} {fvs : Array FVarId} {ceil : Option Nat} {lab : Nat}
    (hS : ScopeShape m fvs ceil top) (wf : m.WF env Us) (wf₂ : m₂.WF env Us)
    (hlab : lab < fvs.size) (hvis : ceil.all (lab ≤ ·))
    (hb : (levelCtx m fvs ceil top lab).Below m₂) : ScopeShape m₂ fvs (some lab) m₂ := by
  have hin : ∀ l fv, fvs[l]? = some fv → l < lab →
      fv ∈ (levelCtx m fvs ceil top lab).vlctx.fvars := fun l fv e hl => by
    have hcl : ceil.all (l < ·) := by cases e' : ceil <;> simp_all; omega
    exact (hS.levelCtx_mono wf hl).fvars (hS.mem_levelCtx_succ e hcl)
  refine ⟨fun l fv e hc => hb.fvars (hin l fv e (by simpa using hc)),
    fun l fv fv' e e' hc => ?_, fun lab' e => ?_⟩
  · have hc' : l + 1 < lab := by simpa using hc
    have hcl : ceil.all (l + 1 < ·) := by cases e'' : ceil <;> simp_all; omega
    have h1 := hS.order l fv fv' e e' hcl
    have hfv' := hin _ fv' e' hc'
    rw [MLCtx.Below.under_eq hfv' hb wf₂,
      ← MLCtx.Below.under_eq hfv' (hS.levelCtx_below lab) wf]
    exact h1
  · cases e
    refine ⟨.refl, Nat.le_of_lt hlab, fun fv e h0 => hb.fvars (hin _ fv e (by omega))⟩

/-- With no ceiling, a context extending `m` has its open scopes declared as `m` does: the shape of
a context a computation is run again in at the current depth. -/
theorem ScopeShape.above {m m₂ top top₂ : MLCtx} {fvs : Array FVarId}
    (hS : ScopeShape m fvs none top) (wf₂ : m₂.WF env Us) (hb : m.Below m₂) :
    ScopeShape m₂ fvs none top₂ where
  mem l fv e hc := hb.fvars (hS.mem l fv e hc)
  order l fv fv' e e' hc := by
    rw [MLCtx.Below.under_eq (hS.mem _ fv' e' (by simp)) hb wf₂]
    exact hS.order l fv fv' e e' hc
  top _ e := by cases e

/-- The contexts of the levels up to `lab` of a context `c` extend into those of a context `m₂` a
computation is run again in: one extending the level-`lab` context of `c`, whose own level `lab`
extends that of `c`, and which sees the levels below `lab`. -/
theorem levelCtx_transfer {m m₂ top top₂ : MLCtx} {fvs : Array FVarId} {ceil ceil₂ : Option Nat}
    {l lab : Nat} (hS : ScopeShape m fvs ceil top) (wf : m.WF env Us) (wf₂ : m₂.WF env Us)
    (hl : l ≤ lab) (hvis : ceil.all (lab ≤ ·))
    (hb : (levelCtx m fvs ceil top lab).Below m₂)
    (htop : (levelCtx m fvs ceil top lab).Below (levelCtx m₂ fvs ceil₂ top₂ lab))
    (hvis₂ : ∀ l, l < lab → ceil₂.all (l < ·)) :
    (levelCtx m fvs ceil top l).Below (levelCtx m₂ fvs ceil₂ top₂ l) := by
  rcases Nat.lt_or_ge l lab with hlt | hge
  · have hcl : ceil.all (l < ·) := by cases e : ceil <;> simp_all; omega
    have hcl₂ := hvis₂ l hlt
    cases e : fvs[l]? with
    | none =>
      have hsz : fvs.size ≤ l := Array.getElem?_eq_none_iff.1 e
      rw [levelCtx_none e hcl, levelCtx_none e hcl₂]
      cases e' : ceil with
      | some lab' =>
        have := (hS.top lab' e').2.1; rw [e'] at hvis; simp at hvis; omega
      | none =>
        rw [levelCtx_none (by simp; omega) (by simp [e'])] at hb
        exact hb
    | some fv =>
      rw [levelCtx_some e hcl, levelCtx_some e hcl₂]
      have hin : fv ∈ (levelCtx m fvs ceil top lab).vlctx.fvars :=
        (hS.levelCtx_mono wf hlt).fvars (hS.mem_levelCtx_succ e hcl)
      rw [MLCtx.Below.under_eq hin hb wf₂,
        MLCtx.Below.under_eq hin (hS.levelCtx_below lab) wf]
      exact .refl
  · obtain rfl : l = lab := by omega
    exact htop

/-- A fact recorded at a level up to `lab` in `c` holds in a context `c₂` a computation is run
again in: one extending the level-`lab` context of `c`, that admits `c` with the name generator
past the computation, and whose own level `lab` extends that of `c`. -/
theorem Holds.transfer {c c₂ : VContext} {top top₂ : MLCtx} (H : Holds c fvs top g₀ l P)
    (hS : ScopeShape c.mlctx fvs c.ceiling top) (hl : l ≤ lab) (hvis : c.ceiling.all (lab ≤ ·))
    (hv : c₂.venv = c.venv) (hlp : c₂.lparams = c.lparams)
    (hb : (levelCtx c.mlctx fvs c.ceiling top lab).Below c₂.mlctx)
    (htop : (levelCtx c.mlctx fvs c.ceiling top lab).Below
      (levelCtx c₂.mlctx fvs c₂.ceiling top₂ lab))
    (hvis₂ : ∀ l, l < lab → c₂.ceiling.all (l < ·))
    (ha : Admits c.lctx g c₂.lctx) (hg : g₀ ≤ g) (hk : Keeps c.lctx g₀ g) :
    Holds c₂ fvs top₂ g₀ l P := by
  intro hc₂
  have hc : c.ceiling.all (l ≤ ·) := by cases e : c.ceiling <;> simp_all; omega
  obtain ⟨L, g', h1, k, h2, h3⟩ := H hc
  refine ⟨L, g', h1, k, ?_, ?_⟩
  · rw [← c₂.lctx_eq]; rw [← c.lctx_eq] at h2 hk; rw [← c.lctx_eq, ← c₂.lctx_eq] at ha
    exact h2.trans ha (h1.trans hg) (k.of_admits h2 hk)
  · rw [hv, hlp]
    exact h3.base (levelCtx_transfer hS c.mlctx_wf (hv ▸ hlp ▸ c₂.mlctx_wf) hl hvis hb htop
      hvis₂)

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.wellScoped {m : MLCtx} (henv : env.WF)
    (wf : m.WF env Us) : m.lctx.WellScoped := by
  intro fv d h
  have htr := wf.tr
  have hm : d ∈ m.lctx.toList := by
    rw [htr.1.find?_eq_find?_toList] at h; exact List.mem_of_find?_eq_some h
  obtain ⟨_, _, -, -, -, h1, h2⟩ := htr.find?_of_mem henv hm
  have hdom {e e'} (he : TrExprS env Us m.vlctx e e') : ∀ x ∈ e.fvarsList, m.lctx.Dom x :=
    fun x hx => by
      have := (fvarsIn_iff.1 he.fvarsIn).1 x hx
      simpa [LocalContext.Dom, Option.isSome_iff_exists] using htr.find?_eq_some.2 this
  exact ⟨hdom h2, hdom h1⟩

@[simp] theorem _root_.Lean.NameGenerator.next_idx (g : NameGenerator) : g.next.idx = g.idx + 1 :=
  rfl

theorem _root_.Lean.NameGenerator.LE.idx_le {g g' : NameGenerator} (h : g ≤ g') : g.idx ≤ g'.idx := by
  cases h; assumption

/-- The state a fresh variable's scope starts in: the name generator past the variable, and the
scope opened. -/
def _root_.Lean4Lean.TypeChecker.State.enter (st : State) : State :=
  ({ st with ngen := st.ngen.next } : State).pushScope ⟨st.ngen.curr⟩

/-- `s₁`, at the end of a variable's scope entered from `s₀`, with the scope closed. -/
def _root_.Lean4Lean.TypeChecker.State.restore (s₀ s₁ : State) : State := s₀.popScope s₁

theorem withFreshId_run {x : Name → M α} {ctx : Context} {st : State} {a s'}
    (h : (MonadLocalNameGenerator.withFreshId x : M α) ctx st = .ok (a, s')) :
    ctx.lctx.find? ⟨st.ngen.curr⟩ = none ∧
    ∃ s₁, x st.ngen.curr ctx st.enter = .ok (a, s₁) ∧ s' = st.restore s₁ := by
  simp only [MonadLocalNameGenerator.withFreshId, bind, ReaderT.bind, StateT.bind, Except.bind,
    get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
    Except.pure, StateT.pure, ReaderT.pure, mkFreshId, getNGen, setNGen, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, read, readThe, MonadReaderOf.read,
    ReaderT.read] at h
  split at h
  · cases h
  rename_i hf
  simp only [Bind.bind, Pure.pure, ReaderT.bind, StateT.bind, Except.bind, StateT.get,
    StateT.modifyGet, ReaderT.pure, StateT.pure, Except.pure] at h
  split at h <;> [cases h; skip]
  rename_i v eq
  cases h
  exact ⟨by simpa using hf, _, eq, rfl⟩

theorem withFreshId_ok {x : Name → M α} {ctx : Context} {st : State} {a s₁}
    (hf : ctx.lctx.find? ⟨st.ngen.curr⟩ = none)
    (h : x st.ngen.curr ctx st.enter = .ok (a, s₁)) :
    (MonadLocalNameGenerator.withFreshId x : M α) ctx st = .ok (a, st.restore s₁) := by
  simp only [MonadLocalNameGenerator.withFreshId, bind, ReaderT.bind, StateT.bind, Except.bind,
    get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
    Except.pure, StateT.pure, ReaderT.pure, mkFreshId, getNGen, setNGen, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, State.enter, read, readThe, MonadReaderOf.read,
    ReaderT.read] at h ⊢
  rw [hf]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
    ReaderT.bind, StateT.bind, Except.bind, StateT.get, StateT.modifyGet, ReaderT.pure, StateT.pure,
    Except.pure]
  rw [h]; rfl


end Lean4Lean.TypeChecker

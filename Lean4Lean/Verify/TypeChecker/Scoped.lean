import Lean4Lean.Verify.Support.Sim
import Lean4Lean.Verify.TypeChecker.Basic

/-!
# Running a computation again

A fact learned in a context (`Learned`) is established by running the computation again in each
context it is learned for: one that agrees with the context it ran in on what it read.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

/-- A context admitting the context a computation ran in, with the name generator past it, is
fresh for it. -/
theorem Admits.freshFor {c₁ c₂ : Context} {g : NameGenerator} (H : Admits c₁.lctx g c₂.lctx) :
    FreshFor c₁ c₂ g := by
  intro fv hd
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hd
  by_cases h : g.Reserves fv
  · obtain ⟨d', hd', -⟩ := H.find? hd (.inl h)
    exact .inl (by simp [LocalContext.Dom, hd'])
  · exact .inr h

/-- The variables both contexts declare, of those `L` declares or `g` had made: what a computation
in `L` that read only them reads alike in `L₂`. -/
def Admits.supp (L L₂ : LocalContext) (g : NameGenerator) : Supp :=
  ⟨fun fv => L₂.Dom fv ∧ (g.Reserves fv ∨ L.Dom fv), fun _ => True, fun _ => True⟩

theorem Admits.supp_lctx {L L₂ : LocalContext} {g : NameGenerator} (H : Admits L g L₂) :
    ∀ fv, (Admits.supp L L₂ g).fv fv → (L₂.find? fv).map LocalDecl.erase =
      (L.find? fv).map LocalDecl.erase := by
  rintro fv ⟨hd, h2⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hd
  rw [hd, H.agree fv d hd h2]; rfl

/-- What a computation in `L` reads alike in `L₂` is closed under `L`'s declarations. -/
theorem Admits.supp_closed {L L₂ : LocalContext} {g : NameGenerator} (H : Admits L g L₂)
    (hL : L.WellScoped) (hL₂ : L₂.WellScoped) : (Admits.supp L L₂ g).CtxClosed L := by
  intro fv d ⟨hd₂, h2⟩ hd
  obtain ⟨d₂, hd₂'⟩ := Option.isSome_iff_exists.1 hd₂
  have e := H.agree fv d₂ hd₂' h2
  rw [hd] at e
  obtain ⟨et, ev⟩ := LocalDecl.erase_type (Option.some.inj e)
  obtain ⟨s1, s2⟩ := hL fv d hd
  obtain ⟨t1, t2⟩ := hL₂ fv d₂ hd₂'
  rw [← et] at t1; rw [← ev] at t2
  exact ⟨Expr.suppIn_fvars.2 fun x hx => ⟨t1 x hx, .inr (s1 x hx)⟩,
    Expr.suppIn_fvars.2 fun x hx => ⟨t2 x hx, .inr (s2 x hx)⟩⟩

/-- A context admitting `c` agrees with it on what a computation in `c` reads of the variables
both declare, whichever variables `c` declares that the name generator had not made. -/
theorem Admits.agreeCtx {c c₂ : Context} {g : NameGenerator} (H : Admits c.lctx g c₂.lctx)
    (wf : c₂.lctx.WF) (henv : c₂.env = c.env) (hs : c₂.safety = c.safety)
    (he : c₂.eagerReduce = c.eagerReduce) (hl : c₂.lparams = c.lparams) (hf : c₂.fuel = c.fuel)
    (hc : ∀ l, c₂.ceiling.all (l ≤ ·) → c.ceiling.all (l ≤ ·)) :
    Agree (Admits.supp c.lctx c₂.lctx g) c c₂ where
  env _ _ := by rw [henv]
  lctx := H.supp_lctx
  wf := wf
  quotInit := by rw [henv]
  safety := hs
  eagerReduce := he
  lparams _ _ h := hl ▸ h
  fuel := hf
  ceiling := hc

/-- What a computation learns. A computation ran in `c` from `s₀` to `s₁` with result `a`, on an
input mentioning the variables `D`; it reads only what its input mentions (`hsim`). For each
context extending `base` that admits `c` with the name generator at `s₁`, and in which its
precondition `Pre` holds, it can be run again (`mk`: a context of the type checker over it, in
which `s₀` is well formed, which sets aside no fact the run used, and where the computation
establishes `P` of its result). Then `P` of `a` is learned in `c` over `base`. No context it is
learned for needs to declare only variables the name generator had made: those `c` declares are
kept as they are. -/
theorem Learned.of_rerun {c : VContext} {s₀ : VState} {x : M α} {a s₁} {base : MLCtx}
    {D : FVarId → Prop} {Pre : MLCtx → Prop} {P : α → MLCtx → Prop}
    (run : x c.toContext s₀.toState = .ok (a, s₁)) (hss : SuppState c.toContext s₀.toState)
    (hDc : ∀ fv, D fv → c.lctx.Dom fv)
    (hsim : ∀ (S : Supp) (c₂ : Context), Agree S c.toContext c₂ → S.Closed c.toContext →
      (∀ fv, D fv → S.fv fv) → (∀ n, S.lvl n) → (∀ n, S.const n) →
      M.Sim c.toContext c₂ s₀.toState x x)
    (mk : ∀ m : MLCtx, m.WF c.venv c.lparams → base.Below m → Admits c.lctx s₁.ngen m.lctx →
      (∀ fv, D fv → m.lctx.Dom fv) → Pre m → ∃ c₂ : VContext, c₂.mlctx = m ∧
        c₂.env = c.env ∧ c₂.safety = c.safety ∧ c₂.eagerReduce = c.eagerReduce ∧
        c₂.lparams = c.lparams ∧ c₂.fuel = c.fuel ∧
        (∀ l, c₂.ceiling.all (l ≤ ·) → c.ceiling.all (l ≤ ·)) ∧
        CeilFits c₂.toContext s₀.toState s₁ ∧ s₀.WF c₂ ∧ M.WF c₂ s₀ x fun a' _ => P a' m) :
    Learned c.venv c.lparams base c.lctx s₁.ngen
      fun m => (∀ fv, D fv → m.lctx.Dom fv) → Pre m → P a m := by
  intro m wf hb ha hD hpre
  obtain ⟨c₂, rfl, henv, hs, he, hl, hf, hc, hC, wf₂, hwf⟩ := mk m wf hb ha hD hpre
  have ha' : Admits c.toContext.lctx s₁.ngen c₂.toContext.lctx := c₂.lctx_eq ▸ ha
  have hS : (Admits.supp c.lctx c₂.lctx s₁.ngen).Closed c.toContext := by
    refine ⟨ha'.supp_closed (c.lctx_eq ▸ c.mlctx_wf.wellScoped c.Ewf)
      (c₂.lctx_eq ▸ c₂.mlctx_wf.wellScoped c₂.Ewf),
      ⟨fun n ci h _ => hss.envClosed n ci h,
        fun _ _ _ => ⟨trivial, trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial⟩, trivial⟩⟩
  have hag := ha'.agreeCtx (c₂.lctx_eq ▸ c₂.mlctx_wf.tr.1) henv hs he hl hf hc
  have run₂ := hsim _ _ hag hS (fun fv h => ⟨c₂.lctx_eq ▸ hD fv h, .inr (hDc fv h)⟩)
    (fun _ => trivial) (fun _ => trivial) hss _ _ run ha'.freshFor hC
  obtain ⟨_, -, -, -, h⟩ := hwf wf₂ _ _ run₂
  exact h

/-- A run in `c` that used no fact a context `c₂` sets aside runs the same way in `c₂`, so what the
computation establishes in every context holds of its result in `c₂` too. -/
theorem RecM.rerun {c c₂ : VContext} {s : VState} {x : RecM α} {m : Methods} {Q a s'}
    (hm : m.WF) (hsim : M.Sim c.toContext c₂.toContext s.toState (x m) (x m))
    (hss : SuppState c.toContext s.toState)
    (run : x m c.toContext s.toState = .ok (a, s'))
    (hF : FreshFor c.toContext c₂.toContext s'.ngen) (hC : CeilFits c₂.toContext s.toState s')
    (wf₂ : s.WF c₂) (hx : RecM.WF c₂ s x Q) : ∃ vs' : VState, vs'.toState = s' ∧ Q a vs' :=
  by obtain ⟨vs', h1, -, -, h2⟩ := hx m hm wf₂ _ _ (hsim hss _ _ run hF hC); exact ⟨vs', h1, h2⟩

end Lean4Lean.TypeChecker

import Lean4Lean.Verify.Support.SimIsDefEq
import Lean4Lean.Verify.Support.EnvSupp
import Lean4Lean.Verify.Environment.AddInductive

/-!
# What a translated expression mentions

An expression with a translation mentions only the free variables of its context and the level
parameters it is translated at.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- The constants a literal expands into are declared, once the constants its translation
needs are. -/
theorem VEnv.HasPrimitives.lit {env : VEnv} (henv : env.WF) (hp : env.HasPrimitives)
    {l : Literal} (h : env.ContainsLits l) : l.SuppIn env.contains := by
  have hc {Γ U A c ls} (hΓ : OnCtx Γ (env.IsType U)) (h : env.HasType U Γ (.const c ls) A) :
      env.contains c :=
    let ⟨_, h, _⟩ := VEnv.HasType.const_inv henv.ordered hΓ h; ⟨_, h⟩
  cases l with
  | natVal => exact ⟨h, hp.nat h⟩
  | strVal =>
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := h
    obtain ⟨⟨_, hN⟩, hC⟩ := (hp.charOfNat h1 ▸ henv.ordered.constWF h1).forallE_inv henv.ordered
    obtain ⟨e2, hnil, hcons⟩ := hp.stringOfList h2
    obtain ⟨hL, ⟨_, hS⟩⟩ := (e2 ▸ henv.ordered.constWF h2).forallE_inv henv.ordered
    obtain ⟨_, _, hnil', hchar⟩ := VEnv.HasType.app_inv henv.ordered trivial hnil
    obtain ⟨_, _, hcons', -⟩ := VEnv.HasType.app_inv henv.ordered trivial hcons
    have hNat : env.contains ``Nat := hc trivial hN
    exact ⟨hc (Γ := [VExpr.listChar]) ⟨trivial, hL⟩ hS, ⟨_, h2⟩, hc trivial hchar, ⟨_, h1⟩, hc trivial hnil',
      hc trivial hcons', hNat, hp.nat hNat⟩

/-- A translated expression mentions only the free variables of its context, the level
parameters it is translated at, and declared constants. -/
theorem TrExprS.suppIn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (henv : env.WF) (hp : env.HasPrimitives) (H : TrExprS env Us Δ e e') :
    e.SuppIn ⟨(· ∈ Δ.fvars), (· ∈ Us), env.contains⟩ := by
  induction H with
  | bvar => trivial
  | fvar h => exact VLCtx.find?_eq_some.1 ⟨_, h⟩
  | sort h => exact Level.LParamsIn.of_ofLevel h
  | const h1 h =>
    refine ⟨⟨_, h1⟩, fun u hu => ?_⟩
    obtain ⟨_, -, h'⟩ := Lean4Lean.List.Forall₂.forall_exists_l (List.mapM_eq_some.1 h) u hu
    exact Level.LParamsIn.of_ofLevel h'
  | app _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    exact ⟨ih1, Expr.SuppIn.mono ⟨fun _ h => by simpa using h, fun _ => id, fun _ => id⟩ ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    exact ⟨ih1, ih2, Expr.SuppIn.mono ⟨fun _ h => by simpa using h, fun _ => id, fun _ => id⟩ ih3⟩
  | lit h => exact hp.lit henv h
  | mdata _ ih => exact ih
  | proj _ _ ih => exact ih

theorem VInductDecl.mem_ctors_of_mem {d : VInductDecl} {T : VInductiveType} {c : VConstructor}
    (hT : T ∈ d.types) (hc : c ∈ T.ctors) : ∃ j, (j, c) ∈ d.ctors := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
  exact ⟨i, VInductDecl.mem_ctors_iff.2 ⟨_, by simp [hi], hc⟩⟩

theorem insertConsts_isSome : ∀ {cis : List ConstantInfo} {C : ConstMap} {name : Name}, C.WF →
    (∀ ci ∈ cis, C.find? ci.name = none) → (cis.map (·.name)).Nodup →
    (C.find? name).isSome ∨ name ∈ cis.map (·.name) → ((insertConsts C cis).find? name).isSome
  | [], _, _, _, _, _, h => h.resolve_right nofun
  | ci :: cis, C, name, hC, hfr, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hC' := hC.insert ci.name ci (hfr ci (.head _))
    refine insertConsts_isSome (cis := cis) hC' (fun c hc => ?_) hnd.2 ?_
    · rw [hC.find?_insert, if_neg]; · exact hfr c (.tail _ hc)
      simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem hc)
    · rw [hC.find?_insert]
      rcases h with h | h
      · split <;> simp [h]
      · rw [List.map_cons, List.mem_cons] at h
        rcases h with rfl | h
        · simp
        · exact .inr h

/-- What an inductive block's declarations name besides their expressions is declared with
them. -/
theorem TrEnv'.namesDeclared {C Q venv} (H : TrEnv' .unsafe C Q venv) :
    (∀ n v, C.find? n = some (.inductInfo v) → ∀ c ∈ v.ctors, (C.find? c).isSome) ∧
    (∀ n v, C.find? n = some (.ctorInfo v) → (C.find? v.induct).isSome) ∧
    (∀ n v, C.find? n = some (.recInfo v) → (C.find? v.getMajorInduct).isSome) := by
  let P (C : ConstMap) : Prop :=
    (∀ n v, C.find? n = some (.inductInfo v) → ∀ c ∈ v.ctors, (C.find? c).isSome) ∧
    (∀ n v, C.find? n = some (.ctorInfo v) → (C.find? v.induct).isSome) ∧
    (∀ n v, C.find? n = some (.recInfo v) → (C.find? v.getMajorInduct).isSome)
  have mono {C : ConstMap} {n ci} (hC : C.WF) (hn : C.find? n = none) {m}
      (h : (C.find? m).isSome) : ((C.insert n ci).find? m).isSome := by
    rw [hC.find?_insert]; split <;> simp [h]
  -- inserting a constant that names nothing keeps `P`
  have plain {C : ConstMap} {n ci} (hC : C.WF) (hn : C.find? n = none) (ih : P C)
      (h1 : ∀ v, ci ≠ .inductInfo v) (h2 : ∀ v, ci ≠ .ctorInfo v) (h3 : ∀ v, ci ≠ .recInfo v) :
      P (C.insert n ci) := by
    refine ⟨fun m v h => ?_, fun m v h => ?_, fun m v h => ?_⟩ <;> rw [hC.find?_insert] at h <;>
      split at h
    · cases h; exact (h1 _ rfl).elim
    · exact fun c hc => mono hC hn (ih.1 m v h c hc)
    · cases h; exact (h2 _ rfl).elim
    · exact mono hC hn (ih.2.1 m v h)
    · cases h; exact (h3 _ rfl).elim
    · exact mono hC hn (ih.2.2 m v h)
  change P C
  induction H with
  | empty => refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [SMap.find?]
  | ignore _ h2 => exact (h2 DefinitionSafety.unsafe_le).elim
  | «axiom» _ h1 _ _ H ih | thm _ h1 _ _ _ H ih | «opaque» _ h1 _ _ H ih =>
    exact plain H.map_wf h1 ih nofun nofun nofun
  | defn _ h1 _ _ H ih => exact plain H.map_wf h1 ih nofun nofun nofun
  | mutualDef _ hnd hfr _ _ _ H ih =>
    have : ∀ (ds : List DefinitionVal) (C : ConstMap), C.WF → P C →
        (∀ d ∈ ds, C.find? d.name = none) → (ds.map (·.name)).Nodup → P (insertDefs C ds) := by
      intro ds
      induction ds with
      | nil => exact fun _ _ h _ _ => h
      | cons d ds ih' =>
        intro C hC hP hfr hnd
        rw [List.map_cons, List.nodup_cons] at hnd
        have hfr₀ := hfr d (.head _)
        refine ih' _ (hC.insert _ _ hfr₀) (plain hC hfr₀ hP nofun nofun nofun) (fun e he => ?_) hnd.2
        rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
        simp only [beq_iff_eq]; intro hh; exact hnd.1 (by rw [hh]; exact List.mem_map_of_mem he)
    exact this _ _ H.map_wf ih hfr hnd
  | @quot C C' _ _ _ h1 H ih =>
    suffices ∀ {n k ci' Q'}, (∀ (C : ConstMap) env, Aligned .unsafe C env → P C → Q' C env → P C') →
        ∀ (C : ConstMap) env, Aligned .unsafe C env → P C → AddQuot1 n k ci' Q' C env → P C' from
      this (this (this (this fun _ _ _ hP ⟨hC, _⟩ => hC ▸ hP))) _ _ H.aligned ih h1
    rintro n k ci' Q' hQ C env wf hP ⟨_, _, _, h1, h2, h3, h4⟩
    exact hQ _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.unsafe_le) h3 rfl)
      (plain wf.map_wf h2 hP nofun nofun nofun) h4
  | @induct C _ decl _ _ _ hd h1 H ih =>
    obtain @⟨_, envT, _, _, types, ctors, recs, -, htys, hcts, hrecs, hnd, hfr, ⟨cis, hp, rfl⟩, hTenv,
      -, -, -⟩ := h1
    have hC := H.map_wf
    have hfind := insertConsts_perm_find? hC hfr hnd hp
    refine (show P (insertConsts C (inductConsts types ctors recs)) → P (insertConsts C cis) from
      fun h => by simp only [P, hfind]; exact h) ?_
    have hins {m} (h : m ∈ (inductConsts types ctors recs).map (·.name)) :=
      insertConsts_isSome (name := m) hC hfr hnd (.inr h)
    have hold {m} (h : (C.find? m).isSome) := insertConsts_isSome (name := m) hC hfr hnd (.inl h)
    have htype {T} (hT : T ∈ decl.types) : ((insertConsts C (inductConsts types ctors recs)).find? T.name).isSome := by
      obtain ⟨w, hw, ⟨hname, -⟩, -⟩ := List.Forall₂.forall_exists_r htys _ hT
      refine hins ?_
      simp only [inductConsts, List.map_append, List.mem_append, List.map_map, List.mem_map]
      exact .inl (.inl ⟨w, hw, hname⟩)
    refine ⟨fun n v h => ?_, fun n v h => ?_, fun n v h => ?_⟩ <;>
      rcases insertConsts_find? hC hfr hnd h with h | ⟨hm, -⟩
    · exact fun c hc => hold (ih.1 n v h c hc)
    · simp only [inductConsts, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨w, hw, he⟩ | ⟨_, -, he⟩) | ⟨_, -, he⟩ <;> cases he
      obtain ⟨T, hT, ⟨⟨-, -, -, -, -, hctors, -⟩, -⟩⟩ := List.Forall₂.forall_exists_l htys _ hw
      intro c hc; rw [hctors] at hc; obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      obtain ⟨j, hj⟩ := VInductDecl.mem_ctors_of_mem hT hc'
      obtain ⟨v', hv', ⟨⟨_, _, _, hname, -⟩, -⟩⟩ := List.Forall₂.forall_exists_r hcts _ hj
      refine hins ?_
      simp only [inductConsts, List.map_append, List.mem_append, List.map_map, List.mem_map]
      exact .inl (.inr ⟨v', hv', hname⟩)
    · exact hold (ih.2.1 n v h)
    · simp only [inductConsts, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨_, -, he⟩ | ⟨w, hw, he⟩) | ⟨_, -, he⟩ <;> cases he
      obtain ⟨⟨j, c⟩, -, ⟨T, hT, -, -, -, hind, -⟩, -⟩ := List.Forall₂.forall_exists_l hcts _ hw
      rw [hind]; exact htype (List.mem_of_getElem? hT)
    · exact hold (ih.2.2 n v h)
    · simp only [inductConsts, List.mem_append, List.mem_map] at hm
      rcases hm with (⟨_, -, he⟩ | ⟨_, -, he⟩) | ⟨w, hw, he⟩ <;> cases he
      obtain ⟨⟨T, i⟩, hTi, ⟨-, hmaj, -⟩, -⟩ := List.Forall₂.forall_exists_l hrecs _ hw
      rw [hmaj]
      rcases List.mem_append.1 (List.fst_mem_of_mem_zipIdx hTi) with hT | hT
      · rw [(hd.types T hT).2]; exact htype hT
      · -- an auxiliary type's recursor eliminates the earlier type it stands for
        obtain ⟨o, hno, hAux⟩ := hd.aux T hT
        obtain ⟨⟨dI, tI, TI, hind, -⟩⟩ := hAux _ hTenv
        rw [VEnv.addConstList_inducts hTenv] at hind
        obtain ⟨-, -, -, -, -, -, TI', hTI', hname⟩ := H.wf.inducts hind
        obtain ⟨lp, -, hTs, -⟩ := H.blockConsts hind
        obtain ⟨v, hv, -⟩ := hTs tI TI' hTI'
        rw [hno, Option.map_some, Option.getD_some, ← hname]; exact hold (by simp [hv])

/-- Every name the declarations of `C` mention is declared in `C`. -/
def ConstMap.Closed (C : ConstMap) : Prop :=
  ∀ n ci, C.find? n = some ci → ci.SuppIn fun m => (C.find? m).isSome

theorem TrEnv'.closed {C Q venv} (H : TrEnv' .unsafe C Q venv) (hp : venv.HasPrimitives) :
    ConstMap.Closed C := by
  have henv := H.wf
  have hdecl {m} (h : venv.contains m) : (C.find? m).isSome := by
    obtain ⟨ci, h1, -⟩ := H.aligned.find?_iff.2 h; simp [h1]
  have hS {Us e e'} (h : TrExprS venv Us [] e e') :
      e.SuppIn ⟨fun _ => False, (· ∈ Us), fun m => (C.find? m).isSome⟩ := by
    have h' := TrExprS.suppIn henv hp h
    exact @Expr.SuppIn.mono ⟨(· ∈ VLCtx.fvars []), (· ∈ Us), venv.contains⟩
      ⟨fun _ => False, (· ∈ Us), fun m => (C.find? m).isSome⟩
      ⟨fun _ h => by simp at h, fun _ => id, fun _ hc => hdecl hc⟩ e h'
  have hnames := H.namesDeclared
  intro n ci h
  obtain ⟨_, -, htr⟩ := H.aligned.find? h DefinitionSafety.unsafe_le
  refine ⟨hS htr.2.2, ?_⟩
  cases ci with
  | defnInfo v | thmInfo v =>
    obtain ⟨_, he, -⟩ := H.of_value h DefinitionSafety.unsafe_le rfl
    exact hS he
  | inductInfo v => exact hnames.1 n v h
  | ctorInfo v => exact hnames.2.1 n v h
  | recInfo v =>
    refine ⟨hnames.2.2 n v h, fun r hr => ?_⟩
    obtain ⟨e, he⟩ := H.recRules h DefinitionSafety.unsafe_le r hr
    exact hS he
  | _ => trivial

/-- The levels that move a term to a context with `k` more universe parameters, put first. -/
def VLevel.shift (k n : Nat) : List VLevel := (List.range n).map fun i => .param (i + k)

theorem VLevel.shift_wf {k n : Nat} : ∀ l ∈ VLevel.shift k n, l.WF (k + n) := by
  simp [VLevel.shift, VLevel.WF]; omega

theorem VLevel.ofLevel_append {Us pre : List Name} (hu : ∀ u ∈ pre, u ∉ Us) :
    ∀ {l : Level} {l'}, VLevel.ofLevel Us l = some l' →
      VLevel.ofLevel (pre ++ Us) l = some (l'.inst (VLevel.shift pre.length Us.length))
  | .zero, _, h => by cases h; rfl
  | .succ l, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨_, h, rfl⟩ := h; exact ⟨_, VLevel.ofLevel_append hu h, rfl⟩
  | .max a b, _, h | .imax a b, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    exact ⟨_, VLevel.ofLevel_append hu ha, _, VLevel.ofLevel_append hu hb, rfl⟩
  | .param n, _, h => by
    simp only [VLevel.ofLevel] at h; split at h <;> cases h
    rename_i hi
    have hn : n ∉ pre := fun h => hu n h (List.idxOf_lt_length_iff.1 hi)
    have : (pre ++ Us).idxOf n = pre.length + Us.idxOf n := by
      induction pre with
      | nil => simp
      | cons a pre ih =>
        have hne : a ≠ n := fun e => hn (e ▸ List.mem_cons_self ..)
        have : (a == n) = false := by simpa using hne
        simp [List.idxOf_cons, this, ih (fun u h => hu u (.tail _ h)) (fun h => hn (.tail _ h))]
        omega
    simp [VLevel.ofLevel, this, hi, VLevel.inst, VLevel.shift]; omega
  | .mvar _, _, h => by cases h

theorem VLevel.ofLevel_append_mapM {Us pre : List Name} (hu : ∀ u ∈ pre, u ∉ Us) :
    ∀ {ls : List Level} {ls'}, ls.mapM (VLevel.ofLevel Us) = some ls' →
      ls.mapM (VLevel.ofLevel (pre ++ Us)) =
        some (ls'.map (·.inst (VLevel.shift pre.length Us.length)))
  | [], _, h => by cases h; rfl
  | l :: ls, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    exact ⟨_, VLevel.ofLevel_append hu h1, _, VLevel.ofLevel_append_mapM hu h2, rfl⟩

/-- Translating with more universe parameters, put first, shifts the translation's. -/
theorem TrExprS.lparams_append {env : VEnv} {Us pre : List Name} (hu : ∀ u ∈ pre, u ∉ Us)
    {Δ : VLCtx} {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env (pre ++ Us) (Δ.instL (VLevel.shift pre.length Us.length)) e
      (e'.instL (VLevel.shift pre.length Us.length)) := by
  have hls : ∀ l ∈ VLevel.shift pre.length Us.length, l.WF (pre ++ Us).length := by
    simpa using VLevel.shift_wf
  induction H with
  | bvar h => exact .bvar (VLCtx.find?_instL h)
  | fvar h => exact .fvar (VLCtx.find?_instL h)
  | sort h => exact .sort (VLevel.ofLevel_append hu h)
  | const h1 h2 h3 =>
    refine .const h1 (VLevel.ofLevel_append_mapM hu h2) ?_
    simp [h3]
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (VLCtx.instL_toCtx _ ▸ h1.instL hls) (VLCtx.instL_toCtx _ ▸ h2.instL hls) ih1 ih2
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (VLCtx.instL_toCtx _ ▸ h1.instL hls) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 =>
    refine .forallE (VLCtx.instL_toCtx _ ▸ h1.instL hls) ?_ ih1 ih2
    simpa using h2.instL hls
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (VLCtx.instL_toCtx _ ▸ h1.instL hls) ih1 ih2 ih3
  | lit h1 _ ih => exact .lit h1 ih
  | mdata _ ih => exact .mdata ih
  | proj _ h2 ih => exact .proj ih (VLCtx.instL_toCtx _ ▸ h2.instL hls)

/-- The local context with its translations' universe levels instantiated. -/
def TypeChecker.MLCtx.instL (ls : List VLevel) : TypeChecker.MLCtx → TypeChecker.MLCtx
  | .nil => .nil
  | .vlam id name ty ty' bi c => .vlam id name ty (ty'.instL ls) bi (c.instL ls)
  | .vlet id name ty v ty' v' c => .vlet id name ty v (ty'.instL ls) (v'.instL ls) (c.instL ls)

theorem TypeChecker.MLCtx.lctx_instL (ls : List VLevel) :
    ∀ c : TypeChecker.MLCtx, (c.instL ls).lctx = c.lctx
  | .nil => rfl
  | .vlam .. | .vlet .. => by simp [instL, MLCtx.lctx, lctx_instL]

theorem TypeChecker.MLCtx.vlctx_instL (ls : List VLevel) :
    ∀ c : TypeChecker.MLCtx, (c.instL ls).vlctx = c.vlctx.instL ls
  | .nil => rfl
  | .vlam .. | .vlet .. => by
    simp [instL, vlctx_instL, VLCtx.instL_eq_map, VLocalDecl.instL]

/-- A local context, at more universe parameters put first. -/
theorem TypeChecker.MLCtx.WF.lparams_append {env : VEnv} {Us pre : List Name}
    (hu : ∀ u ∈ pre, u ∉ Us) : ∀ {c : TypeChecker.MLCtx}, c.WF env Us →
      (c.instL (VLevel.shift pre.length Us.length)).WF env (pre ++ Us)
  | .nil, _ => trivial
  | .vlam .., ⟨h1, h2, h3, h4⟩ => by
    have hls : ∀ l ∈ VLevel.shift pre.length Us.length, l.WF (pre ++ Us).length := by
      simpa using VLevel.shift_wf
    refine ⟨h1.lparams_append hu, by rwa [MLCtx.lctx_instL], ?_, ?_⟩
    · rw [MLCtx.vlctx_instL]; exact h3.lparams_append hu
    · rw [MLCtx.vlctx_instL, VLCtx.instL_toCtx]; exact h4.instL hls
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => by
    have hls : ∀ l ∈ VLevel.shift pre.length Us.length, l.WF (pre ++ Us).length := by
      simpa using VLevel.shift_wf
    refine ⟨h1.lparams_append hu, by rwa [MLCtx.lctx_instL], ?_, ?_, ?_⟩
    · rw [MLCtx.vlctx_instL]; exact h3.lparams_append hu
    · rw [MLCtx.vlctx_instL]; exact h4.lparams_append hu
    · rw [MLCtx.vlctx_instL, VLCtx.instL_toCtx]; exact h5.instL hls

namespace AddInductive

theorem _root_.Lean.ConstantInfo.SuppIn.mono {C C' : Name → Prop} (H : ∀ x, C x → C' x)
    {ci : ConstantInfo} (h : ci.SuppIn C) : ci.SuppIn C' := by
  have hS {e : Expr} : e.SuppIn ⟨fun _ => False, (· ∈ ci.levelParams), C⟩ →
      e.SuppIn ⟨fun _ => False, (· ∈ ci.levelParams), C'⟩ :=
    @Expr.SuppIn.mono ⟨fun _ => False, (· ∈ ci.levelParams), C⟩
      ⟨fun _ => False, (· ∈ ci.levelParams), C'⟩ ⟨fun _ => id, fun _ => id, H⟩ e
  obtain ⟨h1, h2⟩ := h
  refine ⟨hS h1, ?_⟩
  cases ci with
  | defnInfo | thmInfo => exact hS h2
  | inductInfo => exact fun c hc => H _ (h2 c hc)
  | ctorInfo => exact H _ h2
  | recInfo => exact ⟨H _ h2.1, fun r hr => hS (h2.2 r hr)⟩
  | _ => trivial

theorem _root_.Lean4Lean.TypeChecker.VState.WF.emptyAt (c : TypeChecker.VContext)
    (hcl : ConstMap.Closed c.env.constants) (hc : c.ceiling = none) :
    TypeChecker.VState.WF c {} :=
  .emptyOf c (fun n ci h => by
    rw [Kernel.Environment.find?, c.trenv.map_wf.find?'_eq_find?] at h
    exact (hcl n ci h).mono fun _ _ => trivial) hc

/-- A closed expression with a translation mentions only names its environment declares. -/
theorem TrExprS.suppIn_env {env : Environment} {venv : VEnv} {safety}
    (H : TrEnv safety env venv) (hp : venv.HasPrimitives) {Us : List Name} {e : Expr} {e' : VExpr}
    (h : TrExprS venv Us [] e e') :
    e.SuppIn ⟨fun _ => False, (· ∈ Us), fun m => (env.constants.find? m).isSome⟩ := by
  have h' := TrExprS.suppIn H.wf hp h
  refine @Expr.SuppIn.mono ⟨(· ∈ VLCtx.fvars []), (· ∈ Us), venv.contains⟩
    ⟨fun _ => False, (· ∈ Us), fun m => (env.constants.find? m).isSome⟩
    ⟨fun _ h => by simp at h, fun _ => id, fun m hm => ?_⟩ e h'
  obtain ⟨ci, h1, -⟩ := H.find?_iff.2 hm
  rw [Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at h1
  simp [h1]

theorem ConstMap.Closed.insert_axiom {C : ConstMap} (hC : C.WF) (hcl : ConstMap.Closed C)
    {n : Name} {v : AxiomVal}
    (hv : v.type.SuppIn ⟨fun _ => False, (· ∈ v.levelParams), fun m => (C.find? m).isSome⟩) :
    ConstMap.Closed (C.insert n (.axiomInfo v)) := by
  have mono {m} (h : (C.find? m).isSome) : ((C.insert n (.axiomInfo v)).find? m).isSome := by
    rw [hC.find?_insert]; split <;> simp [h]
  intro m ci h
  rw [hC.find?_insert] at h; split at h
  · cases h
    exact ⟨@Expr.SuppIn.mono ⟨fun _ => False, (· ∈ v.levelParams), fun m => (C.find? m).isSome⟩
      ⟨fun _ => False, (· ∈ v.levelParams), fun m => ((C.insert n (.axiomInfo v)).find? m).isSome⟩
      ⟨fun _ => id, fun _ => id, fun _ => mono⟩ _ hv, trivial⟩
  · exact ConstantInfo.SuppIn.mono (fun _ => mono) (hcl m ci h)

/-- Axioms added to a closed environment, each of whose types mentions only its names. -/
theorem ConstMap.Closed.addAxioms : ∀ (axs : List AxiomVal) {env : Environment},
    env.constants.WF → ConstMap.Closed env.constants →
    (∀ ax ∈ axs, ax.type.SuppIn
      ⟨fun _ => False, (· ∈ ax.levelParams), fun m => (env.constants.find? m).isSome⟩) →
    (axs.map (·.name)).Nodup → (∀ ax ∈ axs, env.constants.find? ax.name = none) →
    ConstMap.Closed (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).constants ∧
      (axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).constants.WF ∧
      ∀ m, (env.constants.find? m).isSome →
        ((axs.foldl (fun e ax => e.add (.axiomInfo ax)) env).constants.find? m).isSome
  | [], _, hC, hcl, _, _, _ => ⟨hcl, hC, fun _ => id⟩
  | ax :: axs, env, hC, hcl, hty, hnd, hfr => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfr₀ := hfr ax (.head _)
    have hC' : (env.add (.axiomInfo ax)).constants.WF := hC.insert _ _ hfr₀
    have mono {m} (h : (env.constants.find? m).isSome) :
        ((env.add (.axiomInfo ax)).constants.find? m).isSome := by
      show ((env.constants.insert _ _).find? m).isSome
      rw [hC.find?_insert]; split <;> simp [h]
    have hcl' := ConstMap.Closed.insert_axiom (n := ax.name) hC hcl (hty ax (.head _))
    obtain ⟨h1, h2, h3⟩ := ConstMap.Closed.addAxioms axs (env := env.add (.axiomInfo ax)) hC' hcl'
      (fun a ha => @Expr.SuppIn.mono
        ⟨fun _ => False, (· ∈ a.levelParams), fun m => (env.constants.find? m).isSome⟩
        ⟨fun _ => False, (· ∈ a.levelParams),
          fun m => ((env.add (.axiomInfo ax)).constants.find? m).isSome⟩
        ⟨fun _ => id, fun _ => id, fun _ => mono⟩ _ (hty a (.tail _ ha))) hnd.2
      (fun a ha => by
        show (env.constants.insert _ _).find? _ = none
        rw [hC.find?_insert, if_neg]; · exact hfr a (.tail _ ha)
        simp only [beq_iff_eq]; intro hh
        exact hnd.1 (by rw [show ax.name = a.name from hh]; exact List.mem_map_of_mem ha))
    exact ⟨h1, h2, fun m h => h3 m (mono h)⟩

/-- The state a lifted type checker call starts in, when the environment declares every name it
mentions. -/
theorem VContext.suppState {c : VContext} (hcl : ConstMap.Closed c.env.constants) :
    SuppState c.tc.toContext {} where
  lctxWF := show c.lctx.WF from c.lctx_eq ▸ c.mlctx_wf.tr.1
  wellScoped fv d h := by
    change c.lctx.find? fv = some d at h
    have htr := c.lctx_eq ▸ c.mlctx_wf.tr
    have hm : d ∈ c.lctx.toList := by
      rw [htr.1.find?_eq_find?_toList] at h; exact List.mem_of_find?_eq_some h
    obtain ⟨_, _, -, -, -, h1, h2⟩ := htr.find?_of_mem c.envAt.tr.wf hm
    have hdom {e e'} (he : TrExprS c.venv c.lparams c.mlctx.vlctx e e') :
        ∀ x ∈ e.fvarsList, c.lctx.Dom x := fun x hx => by
      have := (fvarsIn_iff.1 he.fvarsIn).1 x hx
      simpa [LocalContext.Dom, Option.isSome_iff_exists] using htr.find?_eq_some.2 this
    exact ⟨hdom h2, hdom h1⟩
  envClosed n ci h := by
    change c.env.find? n = some ci at h
    rw [Kernel.Environment.find?, c.envAt.tr.map_wf.find?'_eq_find?] at h
    exact (hcl n ci h).mono fun _ _ => trivial
  inferTypeI := by simp
  inferTypeC := by simp
  whnfCore := by simp
  whnf := by simp
  unfold := by simp

/-- A type checker call, run over the kernel's local context, verified by running it in a context
that agrees with it on what the call mentions. -/
theorem WF.liftTC_sim {c : VContext} {c₂ : TypeChecker.VContext} {x : TypeChecker.M α}
    {Q P : α → Prop} (hcl₂ : ConstMap.Closed c₂.env.constants)
    (hss : SuppState c.tc.toContext {})
    (hsim : TypeChecker.M.SS c.tc.toContext c₂.toContext {} x x fun a _ => P a)
    (hF : ∀ g, TypeChecker.FreshFor c.tc.toContext c₂.toContext g) (hc : c₂.ceiling = none)
    (H : TypeChecker.M.WF c₂ {} x fun a _ => Q a) :
    WF c (monadLift x : M α) fun a => P a ∧ Q a := by
  intro a eq
  change TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x = .ok a at eq
  simp only [TypeChecker.M.run, StateT.run', Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  obtain ⟨_, _, _, h1⟩ := hsim.1 hss _ _ eq
  obtain ⟨_, _, _, _, h2⟩ := H (TypeChecker.VState.WF.emptyAt c₂ hcl₂ hc) _ _ (hsim.2 hss _ _ eq (hF _)
    (TypeChecker.CeilFits.none hc))
  exact ⟨h1, h2⟩

/-- `whnf`, run over the kernel's local context and verified in a context that agrees with it on
what its input mentions. -/
theorem whnf.WF_sim {c : VContext} {c₂ : TypeChecker.VContext} {S : Supp} {e : Expr} {e' : VExpr}
    (hcl : ConstMap.Closed c.env.constants) (hcl₂ : ConstMap.Closed c₂.env.constants)
    (hA : TypeChecker.Agree S c.tc.toContext c₂.toContext)
    (hF : ∀ g, TypeChecker.FreshFor c.tc.toContext c₂.toContext g) (hc : c₂.ceiling = none)
    (hS : S.Closed c.tc.toContext) (hd : TypeChecker.Dom c.tc.toContext e) (hs : e.SuppIn S) (he : c₂.TrExprS e e') :
    WF c (monadLift (TypeChecker.whnf e) : M Expr) fun e₁ =>
      e₁.SuppIn S ∧ c₂.FVarsBelow e e₁ ∧ c₂.TrExpr e₁ e' := by
  have hsim : TypeChecker.M.SS c.tc.toContext c₂.toContext {} (TypeChecker.whnf e)
      (TypeChecker.whnf e) fun e₁ _ => TypeChecker.SuppBelow c.tc.toContext e e₁ :=
    TypeChecker.RecM.SS.run (fun m hm => hm.whnf hA hS hd hs) hA.fuel
  exact (WF.liftTC_sim hcl₂ (VContext.suppState hcl) hsim hF hc (TypeChecker.whnf.WF he)).mono
    fun _ ⟨h1, h2⟩ => ⟨h1 S hS hs, h2⟩

/-- `cs` is the part of the kernel's context `cb` a computation reads: some of its variables,
declared alike, at universe parameters `cb`'s has after `pre`, in an environment that `cb`'s
extends only by fresh names `X`. A variable of `cs` translates in `cb` lifted past the others by
`ρ`. -/
structure Sub (X : Name → Prop) (pre : List Name) (ρ : Lift) (cs : TypeChecker.VContext)
    (cb : VContext) : Prop where
  lparams : cb.lparams = pre ++ cs.lparams
  pre_fresh : ∀ u ∈ pre, u ∉ cs.lparams
  lift : VLCtx.FVLift' (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)).vlctx
    cb.mlctx.vlctx 0 ρ 0
  lctx : ∀ fv ∈ cs.mlctx.vlctx.fvars,
    (cb.lctx.find? fv).map LocalDecl.erase = (cs.lctx.find? fv).map LocalDecl.erase
  venv : cs.venv ≤ cb.venv
  env : ∀ n, ¬X n → cb.env.find? n = cs.env.find? n
  /-- The names `cb`'s environment adds are not definitions. -/
  defn : ∀ n v, cb.env.find? n = some (.defnInfo v) → ¬X n
  fresh : ∀ n, X n → cs.env.find? n = none ∧ n ≠ `_inhabitedExprDummy ∧
    Environment.primitives.contains n = false
  closed : ConstMap.Closed cs.env.constants
  closedB : ConstMap.Closed cb.env.constants
  quotInit : cb.env.quotInit = cs.env.quotInit
  safety : cb.safety = cs.safety
  fuel : cb.fuel = cs.fuel
  eagerReduce : cs.eagerReduce = false
  ceiling : cb.tc.ceiling = cs.ceiling := by rfl
  notKernel : ∀ fv ∈ cs.mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv

/-- What a computation over `cs` may mention. -/
def Sub.supp (X : Name → Prop) (cs : TypeChecker.VContext) : Supp :=
  ⟨(· ∈ cs.mlctx.vlctx.fvars), (· ∈ cs.lparams), fun n => ¬X n⟩

theorem Sub.declared {cs : TypeChecker.VContext} {n : Name} (h : cs.venv.contains n) :
    (cs.env.find? n).isSome := by
  obtain ⟨ci, h1, -⟩ := cs.trenv.find?_iff.2 h; simp [h1]

theorem Sub.suppIn {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} {E : VExpr}
    (he : cs.TrExprS e E) : e.SuppIn (Sub.supp X cs) := by
  have h := TrExprS.suppIn cs.Ewf cs.hasPrimitives he
  refine @Expr.SuppIn.mono ⟨(· ∈ cs.vlctx.fvars), (· ∈ cs.lparams), cs.venv.contains⟩
    (Sub.supp X cs) ⟨fun _ => id, fun _ => id, fun n hn hX => ?_⟩ e h
  have h1 := (H.fresh n hX).1
  have h2 := Sub.declared hn
  simp_all

theorem Sub.find?_cs {cs : TypeChecker.VContext} {fv : FVarId}
    (h : fv ∈ cs.mlctx.vlctx.fvars) : ∃ d, cs.lctx.find? fv = some d := by
  have := cs.mlctx_wf.tr.find?_eq_some.2 h
  rwa [cs.lctx_eq] at this

theorem Sub.dom {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {fv : FVarId}
    (h : fv ∈ cs.mlctx.vlctx.fvars) : cb.lctx.Dom fv := by
  obtain ⟨d, hd⟩ := Sub.find?_cs h
  have := H.lctx fv h
  rw [hd] at this
  cases e : cb.lctx.find? fv <;> rw [e] at this <;> simp_all [LocalContext.Dom]

theorem Sub.agree {X pre ρ cs cb} (H : Sub X pre ρ cs cb) :
    TypeChecker.Agree (Sub.supp X cs) cb.tc.toContext cs.toContext where
  env n hn := (H.env n hn).symm
  lctx fv hfv := (H.lctx fv hfv).symm
  wf := cs.lctx_eq ▸ cs.mlctx_wf.tr.1
  quotInit := H.quotInit.symm
  safety := H.safety.symm
  eagerReduce := H.eagerReduce
  lparams _ h _ := h
  fuel := H.fuel.symm
  ceiling _ h := H.ceiling ▸ h

theorem Sub.freshFor {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {g} :
    TypeChecker.FreshFor cb.tc.toContext cs.toContext g :=
  .of_dom fun fv h => by
    have h' : fv ∈ cs.mlctx.vlctx.fvars := by
      have := cs.mlctx_wf.tr.find?_eq_some (fv := fv)
      rw [cs.lctx_eq] at this
      exact this.1 (Option.isSome_iff_exists.1 h)
    exact H.dom h'

theorem Sub.suppClosed {X pre ρ cs cb} (H : Sub X pre ρ cs cb) :
    (Sub.supp X cs).Closed cb.tc.toContext := by
  refine ⟨fun fv d hfv hd => ?_, ⟨fun n ci h hn => ?_, fun op hop hn => ?_, fun op hop hn => ?_,
    fun h => (H.fresh _ h).2.1 rfl⟩⟩
  · have e := H.lctx fv hfv
    change cb.lctx.find? fv = some d at hd
    rw [hd] at e
    obtain ⟨d', hd', he⟩ : ∃ d', cs.lctx.find? fv = some d' ∧ d.erase = d'.erase := by
      cases h : cs.lctx.find? fv <;> rw [h] at e <;> simp_all
    obtain ⟨h1, h2⟩ := LocalDecl.erase_type he
    have htr := cs.lctx_eq ▸ cs.mlctx_wf.tr
    have hm : d' ∈ cs.lctx.toList := by
      rw [htr.1.find?_eq_find?_toList] at hd'; exact List.mem_of_find?_eq_some hd'
    obtain ⟨_, _, -, -, -, h3, h4⟩ := htr.find?_of_mem cs.Ewf hm
    rw [h1, h2]; exact ⟨H.suppIn h4, H.suppIn h3⟩
  · change cb.env.find? n = some ci at h
    rw [H.env n hn, Kernel.Environment.find?, cs.trenv.map_wf.find?'_eq_find?] at h
    refine (H.closed n ci h).mono fun m hm hX => ?_
    have := (H.fresh m hX).1
    rw [Kernel.Environment.find?, cs.trenv.map_wf.find?'_eq_find?] at this
    simp [this] at hm
  · have prim (n) (h : Environment.primitives.contains n = true) : ¬X n := fun hX => by
      simp [(H.fresh n hX).2.2] at h
    refine ⟨prim _ ?_, prim _ ?_, prim _ ?_⟩ <;>
      simp +decide [Environment.primitives, NameSet.ofList, NameSet.contains]
  · have prim (n) (h : Environment.primitives.contains n = true) : ¬X n := fun hX => by
      simp [(H.fresh n hX).2.2] at h
    refine ⟨prim _ ?_, prim _ ?_⟩ <;>
      simp +decide [Environment.primitives, NameSet.ofList, NameSet.contains]

/-- `whnf` in the kernel's context, verified in the part of it its input mentions. -/
theorem Sub.whnf {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} {E : VExpr}
    (he : cs.TrExprS e E) :
    WF cb (monadLift (TypeChecker.whnf e) : M Expr) fun e₁ =>
      e₁.SuppIn (Sub.supp X cs) ∧ cs.FVarsBelow e e₁ ∧ cs.TrExpr e₁ E :=
  whnf.WF_sim H.closedB H.closed H.agree (fun _ => H.freshFor) H.ceiling.symm H.suppClosed
    (fun fv hfv => H.dom ((fvarsIn_iff.1 he.fvarsIn).1 fv hfv)) (H.suppIn he) he

/-- The translation of an expression of `cs`, in `cb`. -/
def Sub.up (pre : List Name) (ρ : Lift) (cs : TypeChecker.VContext) (E : VExpr) : VExpr :=
  (E.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ

theorem Sub.trExprS {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} {E : VExpr}
    (he : cs.TrExprS e E) : cb.tc.TrExprS e (Sub.up pre ρ cs E) := by
  have h1 := he.lparams_append H.pre_fresh
  rw [← TypeChecker.MLCtx.vlctx_instL, ← H.lparams] at h1
  have := (h1.mono H.venv).weakFV' cb.tc.Ewf.ordered H.lift cb.tc.Δwf
  exact this

theorem Sub.isDefEq {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e₁ e₂ A : VExpr}
    (h : cs.venv.IsDefEq cs.lparams.length cs.vlctx.toCtx e₁ e₂ A) :
    cb.venv.IsDefEq cb.lparams.length cb.tc.vlctx.toCtx
      (Sub.up pre ρ cs e₁) (Sub.up pre ρ cs e₂) (Sub.up pre ρ cs A) := by
  have hls : ∀ l ∈ VLevel.shift pre.length cs.lparams.length, l.WF cb.lparams.length := by
    rw [H.lparams]; simpa using VLevel.shift_wf
  have h1 := (h.instL hls).mono H.venv
  have W := H.lift.toCtx
  rw [TypeChecker.MLCtx.vlctx_instL, VLCtx.instL_toCtx] at W
  exact h1.weak' cb.tc.Ewf.ordered W

theorem Sub.isType {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {A : VExpr}
    (h : cs.IsType A) : cb.tc.IsType (Sub.up pre ρ cs A) :=
  let ⟨_, h⟩ := h; ⟨_, H.isDefEq h⟩

theorem Sub.trExpr {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} {E : VExpr}
    (he : cs.TrExpr e E) : cb.tc.TrExpr e (Sub.up pre ρ cs E) :=
  let ⟨_, h1, _, h2⟩ := he; ⟨_, H.trExprS h1, _, H.isDefEq h2⟩

theorem Sub.fresh_cs {X pre ρ cs cb} (H : Sub X pre ρ cs cb) :
    cs.lctx.find? ⟨cb.ngen.curr⟩ = none := by
  cases h : cs.lctx.find? ⟨cb.ngen.curr⟩ with
  | none => rfl
  | some d =>
    have hm : (⟨cb.ngen.curr⟩ : FVarId) ∈ cs.mlctx.vlctx.fvars := by
      have := cs.mlctx_wf.tr.find?_eq_some (fv := ⟨cb.ngen.curr⟩)
      rw [cs.lctx_eq] at this; exact this.1 ⟨_, h⟩
    have hd := H.dom hm
    have htr := cb.lctx_eq ▸ cb.mlctx_wf.tr
    have := htr.find?_eq_some.1 (Option.isSome_iff_exists.1 hd)
    exact absurd (cb.reserved _ this) cb.ngen.not_reserves_self

/-- The small context with a variable pushed, as `withLocalDecl` pushes it onto the kernel's. -/
def Sub.pushS (cs : TypeChecker.VContext) (fv : FVarId) (name : Name) (ty : Expr) (Ty : VExpr)
    (bi : BinderInfo) (wf : (TypeChecker.MLCtx.vlam fv name ty Ty bi cs.mlctx).WF cs.venv cs.lparams) :
    TypeChecker.VContext :=
  @TypeChecker.VContext.withMLC cs (.vlam fv name ty Ty bi cs.mlctx) ⟨wf⟩

theorem Sub.push_lctx {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {name ty bi}
    (_ : (cs.lctx.mkLocalDecl ⟨cb.ngen.curr⟩ name ty bi).WF) :
    ∀ fv, ((cb.lctx.mkLocalDecl ⟨cb.ngen.curr⟩ name ty bi).find? fv).map LocalDecl.erase =
      ((cs.lctx.mkLocalDecl ⟨cb.ngen.curr⟩ name ty bi).find? fv).map LocalDecl.erase ∨
      fv ∉ (⟨cb.ngen.curr⟩ : FVarId) :: cs.mlctx.vlctx.fvars := by
  have hb := (cb.lctx_eq ▸ cb.mlctx_wf.tr).1
  have hs := (cs.lctx_eq ▸ cs.mlctx_wf.tr).1
  have fb : cb.lctx.find? ⟨cb.ngen.curr⟩ = none := by
    cases h : cb.lctx.find? ⟨cb.ngen.curr⟩; · rfl
    have := (cb.lctx_eq ▸ cb.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (cb.reserved _ this) cb.ngen.not_reserves_self
  intro fv
  by_cases hfv : fv ∈ (⟨cb.ngen.curr⟩ : FVarId) :: cs.mlctx.vlctx.fvars
  · left
    rw [LocalContext.find?_mkLocalDecl hb fb, LocalContext.find?_mkLocalDecl hs H.fresh_cs]
    split
    · simp [LocalDecl.erase]
    · rename_i h
      exact H.lctx fv ((List.mem_cons.1 hfv).resolve_left fun e => h (by simp [e]))
  · exact .inr hfv

/-- Pushing a variable onto both contexts. -/
theorem Sub.push {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {name : Name} {ty : Expr} {Ty : VExpr}
    {bi : BinderInfo} (hty : cs.TrExprS ty Ty) (hT : cs.IsType Ty) :
    ∃ wf, Sub X pre ρ.cons (Sub.pushS cs ⟨cb.ngen.curr⟩ name ty Ty bi wf)
      (cb.push name ty (Sub.up pre ρ cs Ty) bi (H.trExprS hty) (H.isType hT)) := by
  have wf : (TypeChecker.MLCtx.vlam ⟨cb.ngen.curr⟩ name ty Ty bi cs.mlctx).WF cs.venv cs.lparams :=
    ⟨cs.mlctx_wf, cs.lctx_eq ▸ H.fresh_cs, hty, hT⟩
  refine ⟨wf, {
    lparams := H.lparams
    pre_fresh := H.pre_fresh
    lift := ?_
    lctx := ?_
    venv := H.venv
    env := H.env
    defn := H.defn
    fresh := H.fresh
    closed := H.closed
    closedB := H.closedB
    quotInit := H.quotInit
    safety := H.safety
    fuel := H.fuel
    eagerReduce := H.eagerReduce
    ceiling := H.ceiling
    notKernel := ?_ }⟩
  · refine .cons_fvar (_, _) (.vlam _) (fun x hx => ?_) H.lift
    have := (fvarsIn_iff.1 hty.fvarsIn).1 x hx
    rw [TypeChecker.MLCtx.vlctx_instL]
    simpa [VLCtx.instL_eq_map, VLCtx.fvars] using this
  · intro fv hfv
    have := (H.push_lctx (name := name) (ty := ty) (bi := bi) (cs.lctx_eq ▸ wf.tr.1) fv)
    simp only [Sub.pushS, TypeChecker.VContext.withMLC, TypeChecker.MLCtx.vlctx,
      VLCtx.fvars_cons_some] at hfv
    show _ = Option.map _ ((cs.mlctx.lctx.mkLocalDecl _ name ty bi).find? fv)
    rw [cs.lctx_eq]
    exact this.resolve_right fun h => h hfv
  · intro fv hfv
    simp only [Sub.pushS, TypeChecker.VContext.withMLC, TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hfv
    rcases hfv with rfl | hfv
    · intro i h; injection h with h; injection h with h; exact absurd h cb.pfx
    · exact H.notKernel fv hfv

/-- Pushing a variable onto the kernel's context only. -/
theorem Sub.skip {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {name : Name} {ty : Expr} {Ty : VExpr}
    {bi : BinderInfo} (hty : TrExprS cb.venv cb.lparams cb.mlctx.vlctx ty Ty)
    (hT : cb.venv.IsType cb.lparams.length cb.mlctx.vlctx.toCtx Ty) :
    Sub X pre (ρ.skipN 1) cs (cb.push name ty Ty bi hty hT) := by
  have hb := (cb.lctx_eq ▸ cb.mlctx_wf.tr).1
  have fb : cb.lctx.find? ⟨cb.ngen.curr⟩ = none := by
    cases h : cb.lctx.find? ⟨cb.ngen.curr⟩; · rfl
    have := (cb.lctx_eq ▸ cb.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (cb.reserved _ this) cb.ngen.not_reserves_self
  refine { H with lift := .skip_fvar (_, _) (.vlam _) H.lift, lctx := fun fv hfv => ?_ }
  show Option.map _ ((cb.lctx.mkLocalDecl _ name ty bi).find? fv) = _
  rw [LocalContext.find?_mkLocalDecl hb fb, if_neg]; · exact H.lctx fv hfv
  rintro h; simp only [beq_iff_eq] at h; subst h
  have hd := H.dom hfv
  simp [LocalContext.Dom, fb] at hd

theorem stripAnnotations_mono {env₁ env₂ : Environment}
    (H : ∀ n v, env₁.find? n = some (.defnInfo v) → env₂.find? n = some (.defnInfo v)) :
    ∀ {e r : Expr}, stripAnnotations env₁ e = .ok r → stripAnnotations env₂ e = .ok r := by
  have hc {n k} (h : checkTypeAnnotation env₁ n k = .ok ()) : checkTypeAnnotation env₂ n k = .ok () := by
    unfold checkTypeAnnotation at h ⊢
    split at h <;> [skip; cases h]
    rename_i v _ hv
    rw [H n _ hv]; exact h
  intro e
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    intro r h
    simp only [stripAnnotations, bind, Except.bind] at h ⊢
    split at h <;> [cases h; skip]
    rename_i u hu
    rw [hc hu]; exact ih h
  | case5 e h1 h2 h3 h4 =>
    intro r h
    rw [stripAnnotations.eq_5 env₁ e h1 h2 h3 h4] at h
    rw [stripAnnotations.eq_5 env₂ e h1 h2 h3 h4]; exact h

theorem Sub.consumeTypeAnnotations {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} :
    WF cb (consumeTypeAnnotations e) fun e' =>
      e' = e.consumeTypeAnnotations' ∧ cs.venv.StripOK e := by
  intro r h
  have h' := stripAnnotations_mono (fun n v hv => (H.env n (H.defn n v hv)) ▸ hv) h
  exact stripAnnotations.WF cs.trenv cs.trenv.wf r h'

/-- Stripping in the kernel's context strips only annotations the small context's environment
defines. -/
theorem Sub.consumeTypeAnnotations_heads {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {e : Expr} :
    WF cb (AddInductive.consumeTypeAnnotations e) fun e' =>
      e' = e.consumeTypeAnnotations' ∧ cs.venv.StripOK e ∧
        e.StripHeads fun n => ∃ v, cs.env.find? n = some (.defnInfo v) := by
  intro r h
  obtain ⟨h1, h2⟩ := H.consumeTypeAnnotations r h
  exact ⟨h1, h2, (AddInductive.stripAnnotations_heads (env := cb.env) h).mono fun n ⟨v, hv⟩ =>
    ⟨v, (H.env n (H.defn n v hv)) ▸ hv⟩⟩

/-- `m` holds some of the kernel's variables, declared alike, in its environment and at its
universe parameters, the kernel's context lifting it by `ρ`: a specification's view of the
variables a construction is about. -/
structure Ext (m : TypeChecker.MLCtx) (cb : VContext) (ρ : Lift) : Prop where
  wf : m.WF cb.venv cb.lparams
  lift : VLCtx.FVLift' m.vlctx cb.mlctx.vlctx 0 ρ 0
  lctx : ∀ fv ∈ m.vlctx.fvars,
    (cb.lctx.find? fv).map LocalDecl.erase = (m.lctx.find? fv).map LocalDecl.erase

theorem Ext.trExprS {m cb ρ} (H : Ext m cb ρ) {e : Expr} {E : VExpr}
    (he : TrExprS cb.venv cb.lparams m.vlctx e E) : cb.tc.TrExprS e (E.lift' ρ) := by
  have := he.weakFV' cb.tc.Ewf.ordered H.lift cb.tc.Δwf
  exact this

theorem Ext.isDefEq {m cb ρ} (H : Ext m cb ρ) {e₁ e₂ A : VExpr}
    (h : cb.venv.IsDefEq cb.lparams.length m.vlctx.toCtx e₁ e₂ A) :
    cb.venv.IsDefEq cb.lparams.length cb.tc.vlctx.toCtx (e₁.lift' ρ) (e₂.lift' ρ) (A.lift' ρ) := by
  have W := H.lift.toCtx
  exact h.weak' cb.tc.Ewf.ordered W

theorem Ext.isType {m cb ρ} (H : Ext m cb ρ) {A : VExpr}
    (h : cb.venv.IsType cb.lparams.length m.vlctx.toCtx A) : cb.tc.IsType (A.lift' ρ) :=
  let ⟨_, h⟩ := h; ⟨_, H.isDefEq h⟩

theorem Ext.fresh {m cb ρ} (H : Ext m cb ρ) : m.lctx.find? ⟨cb.ngen.curr⟩ = none := by
  cases h : m.lctx.find? ⟨cb.ngen.curr⟩ with
  | none => rfl
  | some d =>
    have hm : (⟨cb.ngen.curr⟩ : FVarId) ∈ m.vlctx.fvars := H.wf.tr.find?_eq_some.1 ⟨_, h⟩
    have e := H.lctx _ hm
    rw [h] at e
    have htr := cb.lctx_eq ▸ cb.mlctx_wf.tr
    cases h' : cb.lctx.find? ⟨cb.ngen.curr⟩ <;> rw [h'] at e
    · cases e
    · exact absurd (cb.reserved _ (htr.find?_eq_some.1 ⟨_, h'⟩)) cb.ngen.not_reserves_self

/-- Pushing a variable onto both. -/
theorem Ext.push {m cb ρ} (H : Ext m cb ρ) {name : Name} {ty : Expr} {Ty : VExpr}
    {bi : BinderInfo} (hty : TrExprS cb.venv cb.lparams m.vlctx ty Ty)
    (hT : cb.venv.IsType cb.lparams.length m.vlctx.toCtx Ty) :
    Ext (.vlam ⟨cb.ngen.curr⟩ name ty Ty bi m)
      (cb.push name ty (Ty.lift' ρ) bi (H.trExprS hty) (H.isType hT)) ρ.cons := by
  have hb := (cb.lctx_eq ▸ cb.mlctx_wf.tr).1
  have fb : cb.lctx.find? ⟨cb.ngen.curr⟩ = none := by
    cases h : cb.lctx.find? ⟨cb.ngen.curr⟩; · rfl
    have := (cb.lctx_eq ▸ cb.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (cb.reserved _ this) cb.ngen.not_reserves_self
  have hm := H.wf.tr.1
  refine ⟨⟨H.wf, H.fresh, hty, hT⟩, .cons_fvar (_, _) (.vlam _) (fun x hx => ?_) H.lift,
    fun fv hfv => ?_⟩
  · exact (fvarsIn_iff.1 hty.fvarsIn).1 x hx
  · show Option.map _ ((cb.lctx.mkLocalDecl _ name ty bi).find? fv) =
      Option.map _ ((m.lctx.mkLocalDecl _ name ty bi).find? fv)
    rw [LocalContext.find?_mkLocalDecl hb fb, LocalContext.find?_mkLocalDecl hm H.fresh]
    split
    · simp [LocalDecl.erase]
    · rename_i h
      simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons] at hfv
      exact H.lctx fv (hfv.resolve_left fun e => h (by simp [e]))

/-- Pushing a variable onto the kernel's context only. -/
theorem Ext.skip {m cb ρ} (H : Ext m cb ρ) {name : Name} {ty : Expr} {Ty : VExpr}
    {bi : BinderInfo} (hty : TrExprS cb.venv cb.lparams cb.mlctx.vlctx ty Ty)
    (hT : cb.venv.IsType cb.lparams.length cb.mlctx.vlctx.toCtx Ty) :
    Ext m (cb.push name ty Ty bi hty hT) (ρ.skipN 1) := by
  have hb := (cb.lctx_eq ▸ cb.mlctx_wf.tr).1
  have fb : cb.lctx.find? ⟨cb.ngen.curr⟩ = none := by
    cases h : cb.lctx.find? ⟨cb.ngen.curr⟩; · rfl
    have := (cb.lctx_eq ▸ cb.mlctx_wf.tr).find?_eq_some.1 ⟨_, h⟩
    exact absurd (cb.reserved _ this) cb.ngen.not_reserves_self
  refine ⟨H.wf.mono (VEnv.LE.rfl), .skip_fvar (_, _) (.vlam _) H.lift, fun fv hfv => ?_⟩
  show Option.map _ ((cb.lctx.mkLocalDecl _ name ty bi).find? fv) = _
  rw [LocalContext.find?_mkLocalDecl hb fb, if_neg]; · exact H.lctx fv hfv
  rintro h; simp only [beq_iff_eq] at h; subst h
  have := H.lctx _ hfv
  rw [fb] at this
  obtain ⟨_, h⟩ := H.wf.tr.find?_eq_some.2 hfv
  rw [h] at this; cases this

/-- The small context, at the kernel's universe parameters, as a specification's view. -/
theorem Sub.ext {X pre ρ cs cb} (H : Sub X pre ρ cs cb) :
    Ext (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)) cb ρ := by
  refine ⟨?_, H.lift, fun fv hfv => ?_⟩
  · rw [H.lparams]
    exact (cs.mlctx_wf.lparams_append H.pre_fresh).mono H.venv
  · rw [TypeChecker.MLCtx.lctx_instL, cs.lctx_eq]
    rw [TypeChecker.MLCtx.vlctx_instL] at hfv
    exact H.lctx fv (by simpa [VLCtx.instL_eq_map, VLCtx.fvars] using hfv)

/-- The context at more universe parameters, put first, as `withReader` sets them. -/
def VContext.withLParams (c : VContext) (pre : List Name) (hpre : ∀ u ∈ pre, u ∉ c.lparams) :
    VContext :=
  { c with
    lparams := pre ++ c.lparams
    mlctx := c.mlctx.instL (VLevel.shift pre.length c.lparams.length)
    mlctx_wf := c.mlctx_wf.lparams_append hpre
    lctx_eq := by rw [TypeChecker.MLCtx.lctx_instL]; exact c.lctx_eq
    reserved := by rw [TypeChecker.MLCtx.vlctx_instL]; simpa [VLCtx.instL_eq_map, VLCtx.fvars]
      using c.reserved
    notKernel := by rw [TypeChecker.MLCtx.vlctx_instL]; simpa [VLCtx.instL_eq_map, VLCtx.fvars]
      using c.notKernel }

theorem WF.withLParams {c : VContext} {pre : List Name} (hpre : ∀ u ∈ pre, u ∉ c.lparams)
    {x : M α} {Q} (H : WF (c.withLParams pre hpre) x Q) :
    WF c (withReader (fun ctx => { ctx with lparams := pre ++ ctx.lparams }) x) Q := H

/-! ### Kernel calls verified in a smaller context

A call the kernel makes in its local context, on an input that mentions only the variables of `m`
(`Ext`), runs the same way in `m` alone, and is verified there. -/

/-- The type checker's context with local context `m` over `c`'s environment: the kernel's
context with the variables a call does not read removed. -/
def VContext.small (c : VContext) (m : TypeChecker.MLCtx) (hm : m.WF c.venv c.lparams) :
    TypeChecker.VContext :=
  @TypeChecker.VContext.withMLC c.tc m ⟨hm⟩

@[simp] theorem VContext.small_mlctx {c : VContext} {m hm} : (c.small m hm).mlctx = m := rfl
@[simp] theorem VContext.small_venv {c : VContext} {m hm} : (c.small m hm).venv = c.venv := rfl
@[simp] theorem VContext.small_lparams {c : VContext} {m hm} :
    (c.small m hm).lparams = c.lparams := rfl
@[simp] theorem VContext.small_env {c : VContext} {m hm} : (c.small m hm).env = c.env := rfl

/-- What a call over the variables of `m` may mention: any constant and universe parameter. -/
def Ext.supp (m : TypeChecker.MLCtx) : Supp := ⟨(· ∈ m.vlctx.fvars), fun _ => True, fun _ => True⟩

theorem Ext.suppIn_iff {m : TypeChecker.MLCtx} {e : Expr} :
    e.SuppIn (Ext.supp m) ↔ ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := Expr.suppIn_fvars

theorem Ext.mem_fvars {m cb ρ} (H : Ext m cb ρ) {fv : FVarId} (h : fv ∈ m.vlctx.fvars) :
    fv ∈ cb.mlctx.vlctx.fvars := H.lift.fvars_sublist.subset h

theorem Ext.dom {m cb ρ} (H : Ext m cb ρ) {fv : FVarId} (h : fv ∈ m.vlctx.fvars) :
    cb.lctx.Dom fv := by
  have := (cb.lctx_eq ▸ cb.mlctx_wf.tr).find?_eq_some.2 (H.mem_fvars h)
  exact Option.isSome_iff_exists.2 this

theorem Ext.agree {m cb ρ} (H : Ext m cb ρ) :
    TypeChecker.Agree (Ext.supp m) cb.tc.toContext (cb.small m H.wf).toContext where
  env _ _ := rfl
  lctx fv hfv := (H.lctx fv hfv).symm
  wf := H.wf.tr.1
  quotInit := rfl
  safety := rfl
  eagerReduce := rfl
  lparams _ _ h := h
  fuel := rfl

theorem Ext.freshFor {m cb ρ} (H : Ext m cb ρ) {g} :
    TypeChecker.FreshFor cb.tc.toContext (cb.small m H.wf).toContext g :=
  .of_dom fun _ h => H.dom (H.wf.tr.find?_eq_some.1 (Option.isSome_iff_exists.1 h))

theorem Ext.suppClosed {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants) :
    (Ext.supp m).Closed cb.tc.toContext := by
  refine ⟨fun fv d hfv hd => ?_, ⟨fun n ci h _ => ?_, fun _ _ _ => ⟨trivial, trivial, trivial⟩,
    fun _ _ _ => ⟨trivial, trivial⟩, trivial⟩⟩
  · have e := H.lctx fv hfv
    change cb.lctx.find? fv = some d at hd
    rw [hd] at e
    obtain ⟨d', hd', he⟩ : ∃ d', m.lctx.find? fv = some d' ∧ d.erase = d'.erase := by
      cases h : m.lctx.find? fv <;> rw [h] at e <;> simp_all
    obtain ⟨h1, h2⟩ := LocalDecl.erase_type he
    have htr := H.wf.tr
    have hm : d' ∈ m.lctx.toList := by
      rw [htr.1.find?_eq_find?_toList] at hd'; exact List.mem_of_find?_eq_some hd'
    obtain ⟨_, _, -, -, -, h3, h4⟩ := htr.find?_of_mem cb.tc.Ewf hm
    rw [h1, h2]
    exact ⟨Ext.suppIn_iff.2 (fvarsIn_iff.1 h4.fvarsIn).1, Ext.suppIn_iff.2 (fvarsIn_iff.1 h3.fvarsIn).1⟩
  · exact (VContext.suppState (c := cb) hcl).envClosed n ci h

theorem Ext.notKernel {m cb ρ} (H : Ext m cb ρ) :
    ∀ fv ∈ (cb.small m H.wf).mlctx.vlctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv :=
  fun fv h => cb.notKernel fv (H.mem_fvars h)

theorem Ext.tdom {m cb ρ} (H : Ext m cb ρ) {e : Expr} (h : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars) :
    TypeChecker.Dom cb.tc.toContext e := fun fv hfv => H.dom (h fv hfv)

theorem Ext.liftTC {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {x : TypeChecker.M α} {Q P : α → Prop}
    (hsim : TypeChecker.M.SS cb.tc.toContext (cb.small m H.wf).toContext {} x x fun a _ => P a)
    (W : TypeChecker.M.WF (cb.small m H.wf) {} x fun a _ => Q a) :
    WF cb (monadLift x : M α) fun a => Q a :=
  (WF.liftTC_sim hcl (VContext.suppState hcl) hsim (fun _ => H.freshFor) rfl W).mono
    fun _ h => h.2

/-- `whnf` in the kernel's context, verified in `m`. -/
theorem Ext.whnf {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e : Expr} {E : VExpr} (he : (cb.small m H.wf).TrExprS e E) :
    WF cb (monadLift (TypeChecker.whnf e) : M Expr) fun e₁ =>
      (cb.small m H.wf).FVarsBelow e e₁ ∧ (cb.small m H.wf).TrExpr e₁ E := by
  have hs : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 he.fvarsIn).1
  exact H.liftTC hcl (P := fun _ => True) (TypeChecker.RecM.SS.run
    (fun _ hm => (hm.whnf H.agree (H.suppClosed hcl) (H.tdom hs) (Ext.suppIn_iff.2 hs)).mono
      fun _ _ _ _ => trivial) rfl)
    (TypeChecker.whnf.WF he)

/-- `isDefEq` in the kernel's context, verified in `m`. -/
theorem Ext.isDefEq' {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e₁ e₂ : Expr} {E₁ E₂ : VExpr} (h₁ : (cb.small m H.wf).TrExprS e₁ E₁)
    (h₂ : (cb.small m H.wf).TrExprS e₂ E₂) :
    WF cb (monadLift (TypeChecker.isDefEq e₁ e₂) : M Bool) fun b =>
      b → (cb.small m H.wf).IsDefEqU E₁ E₂ := by
  have hs₁ : ∀ fv ∈ e₁.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 h₁.fvarsIn).1
  have hs₂ : ∀ fv ∈ e₂.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 h₂.fvarsIn).1
  exact H.liftTC hcl (P := fun _ => True) (TypeChecker.RecM.SS.run
    (TypeChecker.Inner.isDefEq.SS H.agree (H.suppClosed hcl) (H.tdom hs₁) (H.tdom hs₂)
      (Ext.suppIn_iff.2 hs₁) (Ext.suppIn_iff.2 hs₂)) rfl)
    (TypeChecker.isDefEq.WF h₁ h₂)

/-- `ensureSort` in the kernel's context, verified in `m`. -/
theorem Ext.ensureSort {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e e₀ : Expr} {E : VExpr} (he : (cb.small m H.wf).TrExprS e E) :
    WF cb (monadLift (TypeChecker.ensureSort e e₀) : M Expr) fun e1 =>
      (cb.small m H.wf).TrExpr e1 E ∧ ∃ u, e1 = .sort u := by
  have hs : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 he.fvarsIn).1
  exact H.liftTC hcl (P := fun _ => True) (TypeChecker.RecM.SS.run
    ((TypeChecker.Inner.ensureSortCore.SS H.agree (H.suppClosed hcl) (H.tdom hs)
      (Ext.suppIn_iff.2 hs)).mono fun _ _ _ _ => trivial) rfl)
    (TypeChecker.ensureSort.WF he)

/-- `checkType` in the kernel's context, verified in `m`. -/
theorem Ext.checkType {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e : Expr} (hfv : e.FVarsIn (· ∈ m.vlctx.fvars)) :
    WF cb (monadLift (TypeChecker.checkType e) : M Expr) fun ty =>
      ∃ e' ty', (cb.small m H.wf).TrTyping e ty e' ty' := by
  have hs : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 hfv).1
  exact H.liftTC hcl (P := fun _ => True) (TypeChecker.RecM.SS.run
    ((TypeChecker.Inner.inferType.SS H.agree (H.suppClosed hcl) (H.tdom hs)
      (Ext.suppIn_iff.2 hs)).mono fun _ _ _ _ => trivial) rfl)
    (TypeChecker.checkType.WF hfv)

/-- `ensureType` in the kernel's context, verified in `m`. -/
theorem Ext.ensureType {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e : Expr} {E : VExpr} (he : (cb.small m H.wf).TrExprS e E) {inferOnly : Bool} :
    WF cb (monadLift (TypeChecker.ensureType e inferOnly) : M Expr) fun e1 =>
      ∃ e', (cb.small m H.wf).TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
        VLevel.ofLevel cb.lparams u = some u' ∧ (cb.small m H.wf).HasType e' (.sort u') := by
  have hs : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 he.fvarsIn).1
  refine H.liftTC hcl (P := fun _ => True) ?_ (TypeChecker.ensureType.WF he)
  refine TypeChecker.M.SS.bind (TypeChecker.RecM.SS.run
    (TypeChecker.Inner.inferType.SS H.agree (H.suppClosed hcl) (H.tdom hs)
      (Ext.suppIn_iff.2 hs)) rfl) fun ty _ _ hQ => ?_
  have hty : ty.SuppIn (Ext.supp m) := hQ _ (H.suppClosed hcl) (Ext.suppIn_iff.2 hs)
  exact TypeChecker.RecM.SS.run ((TypeChecker.Inner.ensureSortCore.SS H.agree (H.suppClosed hcl)
    (H.tdom (Ext.suppIn_iff.1 hty)) hty).mono fun _ _ _ _ => trivial) rfl

/-- `ensureType` in check mode in the kernel's context, verified in `m` from the variables it
mentions alone: a check translates its input. -/
theorem Ext.ensureType' {m cb ρ} (H : Ext m cb ρ) (hcl : ConstMap.Closed cb.env.constants)
    {e : Expr} (hfv : e.FVarsIn (· ∈ m.vlctx.fvars)) :
    WF cb (monadLift (TypeChecker.ensureType e false) : M Expr) fun e1 =>
      ∃ e', (cb.small m H.wf).TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
        VLevel.ofLevel cb.lparams u = some u' ∧ (cb.small m H.wf).HasType e' (.sort u') := by
  have hs : ∀ fv ∈ e.fvarsList, fv ∈ m.vlctx.fvars := (fvarsIn_iff.1 hfv).1
  refine H.liftTC hcl (P := fun _ => True) ?_ (TypeChecker.ensureType.WF' hfv nofun)
  refine TypeChecker.M.SS.bind (TypeChecker.RecM.SS.run
    (TypeChecker.Inner.inferType.SS H.agree (H.suppClosed hcl) (H.tdom hs)
      (Ext.suppIn_iff.2 hs)) rfl) fun ty _ _ hQ => ?_
  have hty : ty.SuppIn (Ext.supp m) := hQ _ (H.suppClosed hcl) (Ext.suppIn_iff.2 hs)
  exact TypeChecker.RecM.SS.run ((TypeChecker.Inner.ensureSortCore.SS H.agree (H.suppClosed hcl)
    (H.tdom (Ext.suppIn_iff.1 hty)) hty).mono fun _ _ _ _ => trivial) rfl

end AddInductive

end Lean4Lean

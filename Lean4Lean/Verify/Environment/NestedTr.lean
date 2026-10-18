import Lean4Lean.Verify.Environment.NestedFinal
import Lean4Lean.Verify.Environment.Recursors
import Lean4Lean.Theory.Typing.NestedWF

/-!
# The restored block's constants translate to the restored block's

The final phase of a nested block adds the translated block's constructors and recursors with
their terms restored (`NestedFinalOK`). Each restored term translates to the restored block's
(`VInductDecl.restoreNested`) corresponding term: its constructor types, recursor types and iota
rules' right-hand sides, by `TrExprS.restoreNested` where the restored term has no `let`, and by
`TrExprS.restoreNested_unique` from the check the final phase makes where it has one.

The restoration needs the translated terms' auxiliary applications to keep their leading
arguments free of auxiliary constants (`VExpr.LeadFree`). The recursors' types and rules are built
from the constructors' fields, the types' indices and applications at variables, so they inherit
it (`VInductDecl.recType_leadFree`, `iotaRule_rhs_leadFree`).
-/

namespace Lean4Lean
open Lean

namespace VExpr
variable {R : Name → Option VAuxHead} {ren : Name → Option Name}

theorem AuxFree.subst {e : VExpr} {σ : Subst} (H : e.AuxFree R ren)
    (hσ : ∀ i, (σ i).AuxFree R ren) : (e.subst σ).AuxFree R ren := ConstsSat.subst H hσ

theorem LeadFree.subst : ∀ {e : VExpr} {σ : Subst}, (∀ i, (σ i).AuxFree R ren) →
    e.LeadFree R ren → (e.subst σ).LeadFree R ren
  | .bvar i, _, hσ, _ => AuxFree.leadFree (hσ i)
  | .sort _, _, _, _ | .const .., _, _, _ => trivial
  | .app f a, σ, hσ, H => by
    unfold LeadFree at H ⊢
    have e1 := restoreAux_subst (R := R) (fun i => (hσ i).mono fun _ h => h.1) (.app f a)
    simp only [VExpr.subst_app] at e1 ⊢
    rw [e1]
    cases h : restoreAux R (.app f a) with
    | some r =>
      rw [h] at H
      simp only [Option.map_some]
      intro c ls xs hs x hx
      unfold restoreAux at h
      cases hs0 : (VExpr.app f a).constSpine? with
      | none => rw [hs0] at h; cases h
      | some p =>
        obtain ⟨c0, ls0, xs0⟩ := p
        have := constSpine?_subst_some (σ := σ) hs0
        simp only [VExpr.subst_app] at this
        rw [this] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨-, -, rfl⟩ := hs
        obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
        exact AuxFree.subst (H c0 ls0 xs0 hs0 x0 hx0) hσ
    | none =>
      rw [h] at H
      exact ⟨LeadFree.subst hσ H.1, LeadFree.subst hσ H.2⟩
  | .lam A b, σ, hσ, H | .forallE A b, σ, hσ, H => by
    have hσ' : ∀ i, (σ.lift i).AuxFree R ren := by
      intro i; cases i with
      | zero => trivial
      | succ i => exact ConstsSat.liftN (hσ i)
    exact ⟨LeadFree.subst hσ H.1, LeadFree.subst hσ' H.2⟩
  | .proj _ _ e, σ, hσ, H => LeadFree.subst (e := e) hσ H

theorem LeadFree.liftN {e : VExpr} {n k : Nat} (H : e.LeadFree R ren) :
    (e.liftN n k).LeadFree R ren := by
  rw [liftN_eq_subst]; exact LeadFree.subst (fun _ => trivial) H

theorem LeadFree.instL {ls : List VLevel} : ∀ {e : VExpr}, e.LeadFree R ren →
    (e.instL ls).LeadFree R ren
  | .bvar _, _ | .sort _, _ | .const .., _ => trivial
  | .app f a, H => by
    unfold LeadFree at H ⊢
    have e1 := restoreAux_instL (R := R) ls (.app f a)
    simp only [VExpr.instL] at e1 ⊢
    rw [e1]
    cases h : restoreAux R (.app f a) with
    | some r =>
      rw [h] at H
      simp only [Option.map_some]
      intro c ls' xs hs x hx
      have := constSpine?_instL (ls' := ls) (e := .app f a)
      simp only [VExpr.instL] at this
      rw [hs] at this
      obtain ⟨⟨c0, ls0, xs0⟩, hs0, he⟩ := Option.map_eq_some_iff.1 this.symm
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
      exact ConstsSat.instL (H c0 ls0 xs0 hs0 x0 hx0)
    | none =>
      rw [h] at H
      exact ⟨LeadFree.instL H.1, LeadFree.instL H.2⟩
  | .lam .., H | .forallE .., H => ⟨LeadFree.instL H.1, LeadFree.instL H.2⟩
  | .proj _ _ e, H => LeadFree.instL (e := e) H

theorem LeadFree.reseat {e : VExpr} (H : e.LeadFree R ren) (a k m b l : Nat) :
    (e.reseat a k m b l).LeadFree R ren := H.liftN.liftN

theorem LeadFree.foralls : ∀ {As : List VExpr} {B : VExpr}, (∀ A ∈ As, A.LeadFree R ren) →
    B.LeadFree R ren → (VExpr.foralls As B).LeadFree R ren
  | [], _, _, hB => hB
  | _ :: _, _, hA, hB => ⟨hA _ (.head _), LeadFree.foralls (fun A h => hA A (.tail _ h)) hB⟩

theorem LeadFree.lams : ∀ {As : List VExpr} {B : VExpr}, (∀ A ∈ As, A.LeadFree R ren) →
    B.LeadFree R ren → (VExpr.lams As B).LeadFree R ren
  | [], _, _, hB => hB
  | _ :: _, _, hA, hB => ⟨hA _ (.head _), LeadFree.lams (fun A h => hA A (.tail _ h)) hB⟩

theorem LeadFree.liftTele (n : Nat) : ∀ {As : List VExpr} {k : Nat},
    (∀ A ∈ As, A.LeadFree R ren) → ∀ A ∈ liftTele n As k, A.LeadFree R ren
  | [], _, _ => nofun
  | _ :: _, _, h => by
    simp only [VExpr.liftTele, List.mem_cons, forall_eq_or_imp]
    exact ⟨(h _ (.head _)).liftN, LeadFree.liftTele n fun A hA => h A (.tail _ hA)⟩

/-- An application whose head, after any prefix of its arguments, is not replaced restores
argument by argument. -/
theorem LeadFree.appN_of_head : ∀ {f : VExpr} {xs : List VExpr},
    (∀ c ls ys, f.constSpine? = some (c, ls, ys) → R c = none) → f.LeadFree R ren →
    (∀ x ∈ xs, x.LeadFree R ren) → (VExpr.appN f xs).LeadFree R ren
  | _, [], _, hf, _ => hf
  | f, x :: xs, hh, hf, hx => by
    refine LeadFree.appN_of_head (f := .app f x) (fun c ls ys h => ?_) ?_
      (fun y hy => hx y (.tail _ hy))
    · simp only [constSpine?, Option.map_eq_some_iff] at h
      obtain ⟨⟨c', ls', ys'⟩, h1, h2⟩ := h
      cases h2; exact hh _ _ _ h1
    · unfold LeadFree
      have : restoreAux R (.app f x) = none := by
        unfold restoreAux
        cases h : (VExpr.app f x).constSpine? with
        | none => rfl
        | some p =>
          obtain ⟨c, ls, ys⟩ := p
          simp only [constSpine?, Option.map_eq_some_iff] at h
          obtain ⟨⟨c', ls', ys'⟩, h1, h2⟩ := h
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp [hh _ _ _ h1]
      rw [this]
      exact ⟨hf, hx x (.head _)⟩

theorem LeadFree.appN_bvar {i : Nat} {xs : List VExpr} (hx : ∀ x ∈ xs, x.LeadFree R ren) :
    (VExpr.appN (.bvar i) xs).LeadFree R ren :=
  LeadFree.appN_of_head (fun _ _ _ h => by cases h) trivial hx

/-- A constant applied to arguments without auxiliary constants keeps its leading arguments free
of them, whatever is replaced. -/
theorem LeadFree.of_spine_auxFree {c : Name} {ls : List VLevel} : ∀ {e : VExpr} {xs : List VExpr},
    e.constSpine? = some (c, ls, xs) → (∀ x ∈ xs, x.AuxFree R ren) → e.LeadFree R ren
  | .const .., _, _, _ => trivial
  | .app f a, xs, h, hx => by
    unfold LeadFree
    cases hr : restoreAux R (.app f a) with
    | some r =>
      intro c' ls' xs' hs x hxs
      rw [h] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, -, rfl⟩ := hs
      exact hx x hxs
    | none =>
      simp only [constSpine?, Option.map_eq_some_iff] at h
      obtain ⟨⟨c', ls', ys⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact ⟨LeadFree.of_spine_auxFree h1 (fun x hx' => hx x (List.mem_append_left _ hx')),
        AuxFree.leadFree (hx a (by simp))⟩
  | .bvar _, _, h, _ | .sort _, _, h, _ | .lam .., _, h, _ | .forallE .., _, h, _
  | .proj .., _, h, _ => by cases h

theorem LeadFree.appN_const {c : Name} {ls : List VLevel} {xs : List VExpr}
    (hx : ∀ x ∈ xs, x.AuxFree R ren) : (VExpr.appN (.const c ls) xs).LeadFree R ren :=
  LeadFree.of_spine_auxFree (constSpine?_appN c ls xs) hx

theorem auxFree_bvars (n k : Nat) : ∀ x ∈ bvars n k, x.AuxFree R ren := by
  intro x hx
  simp only [bvars, List.mem_map] at hx
  obtain ⟨_, -, rfl⟩ := hx
  trivial

theorem LeadFree.app_appN_bvar {i : Nat} {xs : List VExpr} {a : VExpr}
    (hx : ∀ x ∈ xs, x.LeadFree R ren) (ha : a.LeadFree R ren) :
    (VExpr.app (.appN (.bvar i) xs) a).LeadFree R ren := by
  rw [← VExpr.appN_append_singleton]
  exact LeadFree.appN_bvar fun x h => (List.mem_append.1 h).elim (hx x) fun h => by
    cases List.mem_singleton.1 h; exact ha

end VExpr

namespace VInductDecl
open VExpr
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl}

/-- The pieces the recursor's terms are built from keep the leading arguments of their auxiliary
applications free of auxiliary constants: the parameters, the types' indices, and the
constructors' fields, recursive views and indices. -/
structure LeadFreeParts (R : Name → Option VAuxHead) (ren : Name → Option Name)
    (d : VInductDecl) : Prop where
  params : ∀ A ∈ d.params, A.LeadFree R ren
  indices : ∀ T ∈ d.allTypes, ∀ e ∈ T.indices, e.LeadFree R ren
  fields : ∀ T ∈ d.allTypes, ∀ c ∈ T.ctors, ∀ f ∈ c.fields, f.type.LeadFree R ren ∧
    ∀ ra, f.recArg = some ra → (∀ A ∈ ra.binders, A.LeadFree R ren) ∧
      ∀ e ∈ ra.indices, e.LeadFree R ren
  ctorIndices : ∀ T ∈ d.allTypes, ∀ c ∈ T.ctors, ∀ e ∈ c.indices, e.LeadFree R ren
  nested : ∀ T ∈ d.allTypes, T.nested = none
  recNames : ∀ j, j < d.allTypes.length → R (d.recName j) = none

section
variable (P : d.LeadFreeParts R ren) (ls : List VLevel) (v : VLevel)
include P

theorem LeadFreeParts.typeApp {T : VInductiveType} (hT : T ∈ d.allTypes) (ps idx : List VExpr)
    (hps : ∀ x ∈ ps, x.AuxFree R ren) (hidx : ∀ x ∈ idx, x.AuxFree R ren) :
    (T.typeApp ls ps idx).LeadFree R ren := by
  rw [VInductiveType.typeApp_of_none (P.nested T hT)]
  exact LeadFree.appN_const fun x hx => (List.mem_append.1 hx).elim (hps x) (hidx x)

theorem LeadFreeParts.ctorAppAt {j : Nat} (c : VConstructor) (ps fs : List VExpr)
    (hps : ∀ x ∈ ps, x.AuxFree R ren) (hfs : ∀ x ∈ fs, x.AuxFree R ren) :
    (d.ctorAppAt j c ls ps fs).LeadFree R ren := by
  unfold VInductDecl.ctorAppAt
  have : ((d.allTypes[j]?).getD default).nested = none := by
    cases h : d.allTypes[j]? with
    | none => rfl
    | some T => exact P.nested T (List.mem_of_getElem? h)
  rw [VInductiveType.ctorApp_of_none this]
  exact LeadFree.appN_const fun x hx => (List.mem_append.1 hx).elim (hps x) (hfs x)

theorem LeadFreeParts.motiveType {j : Nat} {T : VInductiveType} (hT : T ∈ d.allTypes) :
    (d.motiveType ls v j T).LeadFree R ren := by
  refine LeadFree.foralls (LeadFree.liftTele _ fun A hA => ?_) ⟨P.typeApp ls hT _ _
    (auxFree_bvars _ _) (auxFree_bvars _ _), trivial⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hA
  exact (P.indices T hT e he).instL

theorem LeadFreeParts.minorType {q j : Nat} {T : VInductiveType} (hT : T ∈ d.allTypes)
    {c : VConstructor} (hc : c ∈ T.ctors) : (d.minorType ls q j c).LeadFree R ren := by
  simp only [VInductDecl.minorType]
  refine LeadFree.foralls (fun A hA => ?_) (LeadFree.app_appN_bvar (fun e he => ?_)
    (P.ctorAppAt ls c _ _ (auxFree_bvars _ _) (auxFree_bvars _ _)))
  · rcases List.mem_append.1 hA with hA | hA
    · refine LeadFree.liftTele _ (fun A hA => ?_) A hA
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hA
      exact (P.fields T hT c hc f hf).1.instL
    · obtain ⟨⟨⟨k, ra⟩, r⟩, hp, rfl⟩ := List.mem_map.1 hA
      have hkr := List.fst_mem_of_mem_zipIdx hp
      obtain ⟨f, hf, hra⟩ : ∃ f ∈ c.fields, f.recArg = some ra := by
        obtain ⟨f, h1, h2⟩ := mem_recFields hkr
        exact ⟨f, List.mem_of_getElem? h1, h2⟩
      obtain ⟨hb, hi⟩ := (P.fields T hT c hc f hf).2 ra hra
      refine LeadFree.foralls (fun A hA => ?_) (LeadFree.app_appN_bvar (fun e he => ?_)
        (LeadFree.appN_bvar fun x hx => AuxFree.leadFree (auxFree_bvars _ _ x hx)))
      · obtain ⟨⟨B, i⟩, hB, rfl⟩ := List.mem_map.1 hA
        exact (hb B (List.fst_mem_of_mem_zipIdx hB)).instL.reseat ..
      · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact (hi e' he').instL.reseat ..
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact (P.ctorIndices T hT c hc e' he').instL.reseat ..

theorem LeadFreeParts.recBinders : ∀ A ∈ d.recBinders ls v, A.LeadFree R ren := by
  intro A hA
  unfold VInductDecl.recBinders at hA
  rcases List.mem_append.1 hA with hA | hA
  rcases List.mem_append.1 hA with hA | hA
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hA
    exact (P.params e he).instL
  · obtain ⟨⟨T, j⟩, hp, rfl⟩ := List.mem_map.1 hA
    exact P.motiveType ls v (List.fst_mem_of_mem_zipIdx hp)
  · obtain ⟨⟨⟨j, c⟩, q⟩, hp, rfl⟩ := List.mem_map.1 hA
    obtain ⟨T, hT, hc⟩ := mem_allCtors (List.fst_mem_of_mem_zipIdx hp)
    exact P.minorType ls hT hc

/-- The recursor's type keeps auxiliary applications' leading arguments free of them. -/
theorem LeadFreeParts.recType {i : Nat} {Ti : VInductiveType} (hi : Ti ∈ d.allTypes) :
    (d.recType ls v i Ti).LeadFree R ren := by
  simp only [VInductDecl.recType]
  refine LeadFree.foralls (fun A hA => ?_) ⟨P.typeApp ls hi _ _ (auxFree_bvars _ _)
    (auxFree_bvars _ _), LeadFree.app_appN_bvar
      (fun x hx => AuxFree.leadFree (auxFree_bvars _ _ x hx)) trivial⟩
  rcases List.mem_append.1 hA with hA | hA
  · exact P.recBinders ls v A hA
  · refine LeadFree.liftTele _ (fun A hA => ?_) A hA
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hA
    exact (P.indices Ti hi e he).instL

/-- An iota rule's right-hand side keeps auxiliary applications' leading arguments free of
them. -/
theorem LeadFreeParts.iotaRule_rhs (recLs : List VLevel) {q j : Nat} {T : VInductiveType}
    (hT : T ∈ d.allTypes) {c : VConstructor} (hc : c ∈ T.ctors)
    (hra : ∀ p ∈ c.recFields, p.2.typeIdx < d.allTypes.length) :
    (d.iotaRule ls v recLs q j c).rhs.LeadFree R ren := by
  simp only [VInductDecl.iotaRule]
  refine LeadFree.lams (fun A hA => ?_) (LeadFree.appN_bvar fun x hx => ?_)
  · rcases List.mem_append.1 hA with hA | hA
    · exact P.recBinders ls v A hA
    · refine LeadFree.liftTele _ (fun A hA => ?_) A hA
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hA
      exact (P.fields T hT c hc f hf).1.instL
  · rcases List.mem_append.1 hx with hx | hx
    · exact AuxFree.leadFree (auxFree_bvars _ _ x hx)
    · obtain ⟨⟨k, ra⟩, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨f, hf, hra'⟩ : ∃ f ∈ c.fields, f.recArg = some ra := by
        obtain ⟨f, h1, h2⟩ := mem_recFields hp
        exact ⟨f, List.mem_of_getElem? h1, h2⟩
      obtain ⟨hb, hi⟩ := (P.fields T hT c hc f hf).2 ra hra'
      refine LeadFree.lams (fun A hA => ?_) ?_
      · obtain ⟨⟨B, i⟩, hB, rfl⟩ := List.mem_map.1 hA
        exact (hb B (List.fst_mem_of_mem_zipIdx hB)).instL.reseat ..
      rw [← VExpr.appN_append_singleton]
      refine LeadFree.appN_of_head (fun c' ls' ys h => ?_) trivial (fun e he => ?_)
      · simp only [recConst, constSpine?, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        exact P.recNames _ (hra _ hp)
      · simp only [List.mem_append, List.mem_singleton] at he
        rcases he with (((he | he) | he) | he) | rfl
        · exact AuxFree.leadFree (auxFree_bvars _ _ e he)
        · exact AuxFree.leadFree (auxFree_bvars _ _ e he)
        · exact AuxFree.leadFree (auxFree_bvars _ _ e he)
        · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
          exact (hi e' he').instL.reseat ..
        · exact LeadFree.appN_bvar fun x hx => AuxFree.leadFree (auxFree_bvars _ _ x hx)

end
end VInductDecl

/-! ### A restored term translates to the restored translation -/

theorem PTr.hasExprMVar' {CL : Literal → Prop} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : PTr Us CL Δ e e') : e.hasExprMVar' = false := by
  induction H with
  | bvar | fvar | sort | const | lit => rfl
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp [Expr.hasExprMVar', ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 => simp [Expr.hasExprMVar', ih1, ih2, ih3]
  | mdata _ ih | proj _ ih => simpa [Expr.hasExprMVar'] using ih

theorem PTr.fvarsIn {CL : Literal → Prop} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : PTr Us CL Δ e e') : FVarsIn (· ∈ Δ.fvars) e := by
  induction H with
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort h => exact ofLevel_hasMVar h
  | const h =>
    rw [List.mapM_eq_some] at h
    intro _ hl
    have ⟨_, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_l h _ hl
    exact ofLevel_hasMVar h
  | bvar | lit | mdata => trivial
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ ih => exact ih

theorem _root_.Lean.Expr.ConstsOK.mono {p q : Name → List Level → Prop}
    (h : ∀ c ls, p c ls → q c ls) {e : Expr} (H : e.ConstsOK p) : e.ConstsOK q := by
  induction e with
  | const c ls => exact h c ls H
  | app _ _ ih1 ih2 | lam _ _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1 H.1, ih2 H.2⟩
  | letE _ _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1 H.1, ih2 H.2.1, ih3 H.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih H
  | bvar | fvar | mvar | sort | lit => trivial

section
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {auxRec : NameMap Name} {Us : List Name} {R : Name → Option VAuxHead}
  {ren : Name → Option Name}

/-- A restored term translates to the restored translation, where that is typed: by its plain
translation when it has no `let`, and from the translation the final phase's check gives it when
it has one. -/
theorem TrExprS.restored {E₁ E₀ : VEnv} (henv : E₀.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    {e : Expr} {e' : VExpr} (H : TrExprS E₁ Us [] e e')
    (hR : ∀ c ci, E₁.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    (hc : (r.restoreNested env' lparams e auxRec).ConstsOK
      fun c _ => R c = none ∧ auxRec.find? c = none)
    (hL : e'.LeadFree R ren) (hlit : ∀ l, E₁.ContainsLits l → E₀.ContainsLits l)
    (hwf : (e'.restore R ren).WF E₀ Us.length [])
    (hchk : (r.restoreNested env' lparams e auxRec).anySub (·.isLet) = true →
      ∃ X, TrExprS E₀ Us [] (r.restoreNested env' lparams e auxRec) X) :
    TrExprS E₀ Us [] (r.restoreNested env' lparams e auxRec) (e'.restore R ren) := by
  cases hl : (r.restoreNested env' lparams e auxRec).anySub (·.isLet) with
  | true =>
    obtain ⟨X, hX⟩ := hchk hl
    rwa [← TrExprS.restoreNested_unique S H hR hc hL hX]
  | false =>
    have hP := H.toPTr.restoreNested S (H.auxArity hR) hc hL
    exact TrExprS.restoreNested henv S H hR hc hL
      (Expr.letFree_of_anySub hl hP.hasExprMVar') hlit hwf

/-- A restored term the final phase checked translates to the restored translation: the final
phase found no auxiliary name in it (`NestedFinalOK.clean`), and checked it, against an
environment modelled by `E₀`, if it has a `let` (`NestedFinalOK.lets`). -/
theorem TrExprS.restored_of_final {E₁ E₀ : VEnv} (henv : E₀.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    {e : Expr} {e' : VExpr} (H : TrExprS E₁ Us [] e e')
    (hR : ∀ c ci, E₁.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    {SN : NameSet} (hSN : ∀ c, (R c).isSome ∨ (auxRec.find? c).isSome → SN.contains c)
    (hclean : (r.restoreNested env' lparams e auxRec).anySub (auxP SN) = false)
    (hL : e'.LeadFree R ren) (hlit : ∀ l, E₁.ContainsLits l → E₀.ContainsLits l)
    (hwf : (e'.restore R ren).WF E₀ Us.length []) {safety : DefinitionSafety}
    {fuel : FuelConfig} {b : Bool}
    (hchk : (r.restoreNested env' lparams e auxRec).anySubterm (·.isLet) → ∃ envk,
      VEnvAt envk safety E₀ ∧
      checkRestored envk safety Us fuel (r.restoreNested env' lparams e auxRec) b = .ok ()) :
    TrExprS E₀ Us [] (r.restoreNested env' lparams e auxRec) (e'.restore R ren) := by
  have hc : (r.restoreNested env' lparams e auxRec).ConstsOK
      fun c _ => R c = none ∧ auxRec.find? c = none :=
    (anySub_auxP_false (p := fun c => (R c).isSome ∨ (auxRec.find? c).isSome) hSN hclean).1.mono
      fun c _ h => by
        simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
          at h
        exact h
  refine TrExprS.restored henv S H hR hc hL hlit hwf fun hl => ?_
  have hP := H.toPTr.restoreNested S (H.auxArity hR) hc hL
  rw [← anySubterm_isLet] at hl
  obtain ⟨envk, wf, hk⟩ := hchk hl
  obtain ⟨X, -, hX, -⟩ := checkRestored.WF wf (hP.fvarsIn.mono fun _ h => by cases h) hl hk
  exact ⟨X, hX⟩

end

/-! ### Leading binders survive restoring -/

/-- The number of leading pi binders of a term. -/
def VExpr.forallsCount : VExpr → Nat
  | .forallE _ b => b.forallsCount + 1
  | _ => 0

theorem VExpr.forallsCount_foralls : ∀ (As : List VExpr) (B : VExpr),
    (VExpr.foralls As B).forallsCount = As.length + B.forallsCount
  | [], _ => by simp [VExpr.foralls]
  | _ :: As, B => by
    simp only [VExpr.foralls, VExpr.forallsCount, VExpr.forallsCount_foralls As B, List.length_cons]
    omega

theorem VExpr.forallsCount_appN : ∀ {xs : List VExpr} {f : VExpr},
    (∀ A B, f ≠ .forallE A B) → (VExpr.appN f xs).forallsCount = 0
  | [], f, h => by
    cases f <;> first | rfl | exact absurd rfl (h _ _)
  | x :: xs, f, _ => VExpr.forallsCount_appN (xs := xs) (f := .app f x) fun _ _ h => by cases h

theorem VExpr.forallsCount_appN_const {c : Name} {ls : List VLevel} {xs : List VExpr} :
    (VExpr.appN (.const c ls) xs).forallsCount = 0 := VExpr.forallsCount_appN nofun

/-- A translation has at least as many leading pi binders as the term. -/
theorem TrExprS.leadingForalls_le {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (H : TrExprS env Us Δ e e') : e.leadingForalls ≤ e'.forallsCount := by
  induction H with
  | forallE _ _ _ _ _ ih => simp only [Expr.leadingForalls, VExpr.forallsCount]; omega
  | bvar | fvar | sort | const | app | lam | letE | lit | mdata | proj =>
    simp [Expr.leadingForalls]

theorem restoreNested_leadingForalls {r : ElimNestedInductive.Result}
    {env' : Kernel.Environment} {lparams : List Name} {auxRec : NameMap Name} (e : Expr) :
    e.leadingForalls ≤ (r.restoreNested env' lparams e auxRec).leadingForalls := by
  rw [ElimNestedInductive.Result.restoreNested_eq]
  induction e with
  | forallE n t b bi _ ih =>
    rw [Expr.replaceNoCache_forallE (by
      simp [ElimNestedInductive.Result.restoreFn, ElimNestedInductive.Result.auxFn,
        ElimNestedInductive.Result.constSpine?])]
    simp only [Expr.leadingForalls]; omega
  | _ => simp [Expr.leadingForalls]

/-! ### The head of a restored application -/

section
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {auxRec : NameMap Name}

local notation "ρ" => Expr.replaceNoCache (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)

/-- An application of a constant restoring leaves alone keeps its head. -/
theorem restore_constSpine?_of_not_aux {c : Name} {ls : List Level} :
    ∀ {t : Expr} {args : Array Expr}, ElimNestedInductive.Result.constSpine? t = some (c, ls, args) →
    (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = false →
    auxRec.find? c = none →
    ElimNestedInductive.Result.constSpine? (ρ t) = some (c, ls, args.map ρ)
  | .const c' ls', args, h, haux, hren => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3
    simp only [Bool.or_eq_false_iff] at haux
    have : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.const c' ls') = none := by
      simp [ElimNestedInductive.Result.restoreFn, hren, ElimNestedInductive.Result.auxFn,
        ElimNestedInductive.Result.constSpine?, haux.1, haux.2]
    rw [Expr.replaceNoCache.eq_def, this]
    simp [ElimNestedInductive.Result.constSpine?]
  | .app f a, args, h, haux, hren => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', args'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
    have hn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.app f a) = none := by
      rw [restoreFn_of_not_const fun _ _ h => by cases h]
      simp only [Bool.or_eq_false_iff] at haux
      simp [ElimNestedInductive.Result.auxFn, ElimNestedInductive.Result.constSpine?, h1, haux.1,
        haux.2]
    rw [Expr.replaceNoCache_app hn]
    simp [ElimNestedInductive.Result.constSpine?,
      restore_constSpine?_of_not_aux h1 haux hren]
  | .bvar _, _, h, _, _ | .fvar _, _, h, _, _ | .mvar _, _, h, _, _ | .sort _, _, h, _, _
  | .lam .., _, h, _, _ | .forallE .., _, h, _, _ | .letE .., _, h, _, _ | .lit _, _, h, _, _
  | .proj .., _, h, _, _ | .mdata .., _, h, _, _ => by cases h

/-- An auxiliary constant applied to at least the block's parameters restores to an application of
its replacement. -/
theorem restore_getAppFn_of_aux {c : Name} {ls : List Level} :
    ∀ {t : Expr} {args : Array Expr}, ElimNestedInductive.Result.constSpine? t = some (c, ls, args) →
    (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true →
    auxRec.find? c = none → r.nparams ≤ args.size → ∀ {out : Expr},
    r.kRepl env' lparams c ls (args.extract 0 r.nparams) = some out →
    (ρ t).getAppFn = out.getAppFn
  | t, args, h, haux, hren, hle, out, hout => by
    by_cases hs : args.size = r.nparams
    · have : args.extract 0 r.nparams = args := by
        rw [← hs]; simp
      rw [this] at hout
      have hf := restoreFn_of_repl (r := r) (env' := env') (lparams := lparams) (auxRec := auxRec)
        (fun c' ls' ht => by
          subst ht
          simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, -, -⟩ := h; exact hren) h ⟨hs, haux⟩
      rw [Expr.replaceNoCache.eq_def, hf, hout]
    · cases t with
      | app f a =>
        simp only [ElimNestedInductive.Result.constSpine?, Option.map_eq_some_iff] at h
        obtain ⟨⟨c', ls', args'⟩, h1, h2⟩ := h
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
        have hn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.app f a) = none := by
          rw [restoreFn_of_not_const fun _ _ h => by cases h]
          simp only [ElimNestedInductive.Result.auxFn, ElimNestedInductive.Result.constSpine?, h1,
            Option.map_some, Option.bind_some]
          rw [if_neg fun h => hs h.1]
        rw [Expr.replaceNoCache_app hn]
        simp only [Expr.getAppFn]
        refine restore_getAppFn_of_aux h1 haux hren (by simp at hle hs; omega) ?_
        rwa [Array.extract_push_of_le (by simp at hle hs; omega)] at hout
      | const =>
        simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        have h0 : r.nparams = 0 := by simpa using hle
        exact absurd (by simp [h0]) hs
      | _ => cases h

/-- The `k`th binder domain of `e` satisfies `P`. -/
def MajorAtP (P : Expr → Prop) : Nat → Expr → Prop
  | 0, .forallE _ dom _ _ => P dom
  | k + 1, .forallE _ _ b _ => MajorAtP P k b
  | _, _ => False

theorem majorAt_iff {I : Name} : ∀ {k : Nat} {e : Expr},
    AddInductive.MajorAt I k e ↔ MajorAtP (fun dom => ∃ us, dom.getAppFn = .const I us) k e
  | 0, .forallE .. => by simp [AddInductive.MajorAt, MajorAtP]
  | k + 1, .forallE .. => by simp [AddInductive.MajorAt, MajorAtP, majorAt_iff (k := k)]
  | 0, .bvar _ | 0, .fvar _ | 0, .mvar _ | 0, .sort _ | 0, .const .. | 0, .app .. | 0, .lam ..
  | 0, .letE .. | 0, .lit _ | 0, .mdata .. | 0, .proj .. | _ + 1, .bvar _ | _ + 1, .fvar _
  | _ + 1, .mvar _ | _ + 1, .sort _ | _ + 1, .const .. | _ + 1, .app .. | _ + 1, .lam ..
  | _ + 1, .letE .. | _ + 1, .lit _ | _ + 1, .mdata .. | _ + 1, .proj .. => by
    simp [AddInductive.MajorAt, MajorAtP]

theorem MajorAtP.mono {P Q : Expr → Prop} (h : ∀ dom, P dom → Q dom) :
    ∀ {k : Nat} {e : Expr}, MajorAtP P k e → MajorAtP Q k e
  | 0, .forallE .., H => h _ H
  | _ + 1, .forallE .., H => MajorAtP.mono h (e := ‹_›) H

theorem MajorAtP.restore {P Q : Expr → Prop} (h : ∀ dom, P dom → Q (ρ dom)) :
    ∀ {k : Nat} {e : Expr}, MajorAtP P k e → MajorAtP Q k (ρ e)
  | 0, .forallE .., H => by
    rw [Expr.replaceNoCache_forallE restoreFn_forallE]; exact h _ H
  | _ + 1, .forallE .., H => by
    rw [Expr.replaceNoCache_forallE restoreFn_forallE]; exact MajorAtP.restore h (e := ‹_›) H

/-- The `k`th binder domain of a pi telescope. -/
def _root_.Lean4Lean.VExpr.domAt : Nat → VExpr → Option VExpr
  | 0, .forallE A _ => some A
  | k + 1, .forallE _ B => B.domAt k
  | _, _ => none

theorem _root_.Lean4Lean.VExpr.domAt_foralls : ∀ (As : List VExpr) (A B : VExpr),
    (VExpr.foralls As (.forallE A B)).domAt As.length = some A
  | [], _, _ => rfl
  | _ :: As, A, B => VExpr.domAt_foralls As A B

/-- A binder domain, with a plain translation in its context of the translation's domain. -/
theorem MajorAtP.ptr {P : Expr → Prop} {Us : List Name} {CL : Literal → Prop} :
    ∀ {k : Nat} {Δ : VLCtx} {e : Expr} {e' : VExpr}, MajorAtP P k e → PTr Us CL Δ e e' →
      MajorAtP (fun dom => P dom ∧ ∃ Δ' D, PTr Us CL Δ' dom D ∧ e'.domAt k = some D) k e
  | 0, _, .forallE .., _, H, .forallE h1 _ => ⟨H, _, _, h1, rfl⟩
  | k + 1, _, .forallE _ _ b _, _, H, .forallE _ h2 => MajorAtP.ptr (P := P) (k := k) (e := b) H h2

theorem forall₂_take {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (n : Nat), List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.take n) (l₂.take n)
  | _, _, 0, _ => by simp
  | [], [], _ + 1, .nil => .nil
  | _ :: _, _ :: _, n + 1, .cons h t => .cons h (forall₂_take n t)

theorem constSpine?_of_getAppFn {c : Name} {ls : List Level} : ∀ {t : Expr},
    t.getAppFn = .const c ls → ∃ args, ElimNestedInductive.Result.constSpine? t = some (c, ls, args)
  | .const .., h => by
    simp only [Expr.getAppFn, Expr.const.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, rfl⟩
  | .app f a, h => by
    obtain ⟨args, h1⟩ := constSpine?_of_getAppFn (t := f) h
    exact ⟨args.push a, by simp [ElimNestedInductive.Result.constSpine?, h1]⟩
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h | .letE .., h
  | .lit _, h | .proj .., h | .mdata .., h => by cases h

theorem getAppFn_of_constSpine? {c : Name} {ls : List Level} : ∀ {t : Expr} {args : Array Expr},
    ElimNestedInductive.Result.constSpine? t = some (c, ls, args) → t.getAppFn = .const c ls
  | .const .., _, h => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h; rfl
  | .app f _, _, h => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', a'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, -⟩ := h2
    exact getAppFn_of_constSpine? (t := f) h1
  | .bvar _, _, h | .fvar _, _, h | .mvar _, _, h | .sort _, _, h | .lam .., _, h
  | .forallE .., _, h | .letE .., _, h | .lit _, _, h | .proj .., _, h | .mdata .., _, h => by
    cases h

/-- The major premise's domain restores to an application of the type it stands for: its own
type, or for an auxiliary type, the earlier type its replacement applies. -/
theorem MajorAt.restore {Us : List Name} {CL : Literal → Prop} {R : Name → Option VAuxHead}
    {ren : Name → Option Name} (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    (hout : ∀ c h ls args out, R c = some h → r.kRepl env' lparams c ls args = some out →
      ∃ us, out.getAppFn = .const h.name us)
    {I : Name} {k : Nat} {e : Expr} {e' : VExpr} (hM : AddInductive.MajorAt I k e)
    (H : PTr Us CL [] e e') {ls : List VLevel} {xs : List VExpr}
    (hD : e'.domAt k = some (.appN (.const I ls) xs)) (hlsl : ls.length = lparams.length)
    (hxs : (R I).isSome → r.nparams ≤ xs.length) (hren : auxRec.find? I = none) :
    AddInductive.MajorAt (((R I).map (·.name)).getD I) k (ρ e) := by
  rw [majorAt_iff] at hM ⊢
  refine MajorAtP.restore (fun dom ⟨⟨us, hf⟩, Δ', D', hp, hd⟩ => ?_) (hM.ptr H)
  rw [hD, Option.some.injEq] at hd; subst hd
  obtain ⟨args, hsp⟩ := constSpine?_of_getAppFn hf
  obtain ⟨ls', xs', hls, hsp', hxs'⟩ := hp.constSpine? hsp
  rw [VExpr.constSpine?_appN, Option.some.injEq, Prod.mk.injEq] at hsp'
  obtain ⟨-, rfl, rfl⟩ := hsp'
  have hal : args.size = xs.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hxs']; simp
  cases hR : R I with
  | none =>
    have haux : (r.aux2nested.contains I || (r.getNestedIfAuxCtor env' I).isSome) = false := by
      have := S.aux I; rw [hR] at this; simpa using this.symm
    exact ⟨_, getAppFn_of_constSpine? (restore_constSpine?_of_not_aux hsp haux hren)⟩
  | some h =>
    have haux : (r.aux2nested.contains I || (r.getNestedIfAuxCtor env' I).isSome) = true := by
      have := S.aux I; rw [hR] at this; simpa using this.symm
    have hle : r.nparams ≤ args.size := hal ▸ hxs (by simp [hR])
    have hus : us.length = lparams.length := by
      rw [← hlsl, ← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls)]
    have hys : List.Forall₂ (PTr Us CL Δ') (args.extract 0 r.nparams).toList
        (xs.take r.nparams) := by
      have := forall₂_take r.nparams hxs'
      simpa [Array.toList_extract, List.extract] using this
    obtain ⟨out, hout', -⟩ := S.repl I h us ls (args.extract 0 r.nparams) Δ' _ hR hls hus
      (by simp; omega) hys
    obtain ⟨us', hus'⟩ := hout I h us _ out hR hout'
    exact ⟨us', (restore_getAppFn_of_aux hsp haux hren hle hout').trans hus'⟩

end

/-! ### The restored constructors -/

namespace VInductDecl
variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name}

theorem restoreNested_types_getElem?_of {j : Nat} {T : VInductiveType} (hj : j < n)
    (hT : d.types[j]? = some T) :
    (d.restoreNested R ren n ns cname).types[j]? = some (T.restore R ren cname none) := by
  have hl := (List.getElem?_eq_some_iff.1 hT).1
  simp only [restoreNested, List.getElem?_map, List.getElem?_take, if_pos hj,
    List.getElem?_zipIdx, hT, Option.map_some]
  simp [nestedAt, hj]

end VInductDecl

section
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {auxRec : NameMap Name} {R : Name → Option VAuxHead} {ren : Name → Option Name}
  {d : VInductDecl} {n : Nat} {ns : List VNested} {cname : Name → Name}

/-- A constructor of one of the block's own types, as the final phase restores it, is the
restored block's. -/
theorem restoredCtor {safety : DefinitionSafety} {venv envT envT' : VEnv} (henv : venv.WF)
    (H : d.RestoreSpec R ren n ns cname) (hdN : (d.restoreNested R ren n ns cname).WF venv)
    (hTN : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some envT)
    (S : RestoreSpec r env' lparams auxRec lparams envT'.ContainsLits R ren)
    (hR : ∀ c ci, envT'.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    {SN : NameSet} (hSN : ∀ c, (R c).isSome ∨ (auxRec.find? c).isSome → SN.contains c)
    (hlit : ∀ l, envT'.ContainsLits l → envT.ContainsLits l) {fuel : FuelConfig}
    {j : Nat} (hj : j < n) {c : VConstructor} {c₀ : ConstructorVal}
    (hc₀ : TrCtorVal d lparams j c c₀ ∧ TrConstant safety envT' (.ctorInfo c₀) ⟨d.uvars, c.type⟩)
    (hL : c.type.LeadFree R ren)
    (hclean : (r.restoreNested env' lparams c₀.type auxRec).anySub (auxP SN) = false)
    (hchk : (r.restoreNested env' lparams c₀.type auxRec).anySubterm (·.isLet) → ∃ envk,
      VEnvAt envk safety envT ∧
      checkRestored envk safety lparams fuel (r.restoreNested env' lparams c₀.type auxRec) true =
        .ok ()) :
    let c₁ := { c₀ with type := r.restoreNested env' lparams c₀.type auxRec }
    TrCtorVal (d.restoreNested R ren n ns cname) lparams j (c.restore R ren cname) c₁ ∧
      TrConstant safety envT (.ctorInfo c₁)
        ⟨(d.restoreNested R ren n ns cname).uvars, (c.restore R ren cname).type⟩ := by
  intro c₁
  obtain ⟨⟨T, hT, hcT, hname, hlp, hind, hnp, hnf, hunsafe, hlf⟩, hsafe, hlen, htr⟩ := hc₀
  have hcm : c ∈ T.ctors := List.mem_of_getElem? hcT
  obtain ⟨-, -, hown⟩ := H.own j T hj hT
  obtain ⟨-, -, hcn⟩ := hown c hcm
  have hTj := VInductDecl.restoreNested_types_getElem?_of (R := R) (ren := ren) (ns := ns)
    (cname := cname) hj hT
  have hTm : T.restore R ren cname none ∈ (d.restoreNested R ren n ns cname).allTypes :=
    List.mem_append_left _ (List.mem_of_getElem? hTj)
  have hcN : c.restore R ren cname ∈ (T.restore R ren cname none).ctors :=
    List.mem_map_of_mem hcm
  have hcW := (hdN.ctors envT hTN _ hTm).2 _ hcN
  have henvT : envT.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
    exact (hdN.types T' hT').1) hTN
  change TrExprS envT' c₀.levelParams [] c₀.type c.type at htr
  change c₀.levelParams.length = d.uvars at hlen
  rw [hlp] at htr hlen
  have htrN : TrExprS envT lparams [] c₁.type (c.type.restore R ren) := by
    refine TrExprS.restored_of_final henvT.ordered S htr hR hSN hclean hL hlit ?_ hchk
    obtain ⟨_, h⟩ := hcW.type
    rw [hlen]; exact ⟨_, h⟩
  have hcnt : (c.type.restore R ren).forallsCount =
      (d.restoreNested R ren n ns cname).params.length + (c.restore R ren cname).fields.length := by
    obtain ⟨ps, Ds, hty, hps, hfs, -⟩ := hcW.shape
    have hfl := VInductDecl.FieldsWF.length hfs
    change (c.restore R ren cname).type.forallsCount = _
    rw [hty, VExpr.forallsCount_foralls, List.length_append, hps.length_eq, hfl,
      VInductiveType.typeApp_of_none rfl, VExpr.forallsCount_appN_const]
    rfl
  refine ⟨⟨T.restore R ren cname none, hTj, ?_, ?_, hlp, hind, ?_, ?_, hunsafe, ?_⟩,
    hsafe, by change c₀.levelParams.length = d.uvars; rw [hlp, hlen],
    by change TrExprS envT c₀.levelParams [] c₁.type _; rw [hlp]; exact htrN⟩
  · show (T.ctors.map _)[c₀.cidx]? = _
    rw [List.getElem?_map, hcT]; rfl
  · show c₀.name = cname c.name
    rw [hcn, hname]
  · rw [VInductDecl.restoreNested_params_length]; exact hnp
  · simpa [VConstructor.restore] using hnf
  · refine Nat.le_antisymm (hcnt ▸ htrN.leadingForalls_le) ?_
    have := restoreNested_leadingForalls (r := r) (env' := env') (lparams := lparams)
      (auxRec := auxRec) c₀.type
    rw [hlf] at this
    simpa [VInductDecl.restoreNested_params_length, VConstructor.restore] using this

/-- A recursor type's major premise, and how far into its binders it is. -/
theorem _root_.Lean4Lean.VInductDecl.recType_domAt {d : VInductDecl} {ls : List VLevel}
    {v : VLevel} {i : Nat} {T : VInductiveType} :
    (d.recType ls v i T).domAt
        (d.params.length + d.allTypes.length + d.allCtors.length + T.indices.length) =
      some (T.typeApp ls (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + T.indices.length))
        (VExpr.bvars T.indices.length 0)) := by
  have := VExpr.domAt_foralls (d.recBinders ls v ++ VExpr.liftTele
      (d.allTypes.length + d.allCtors.length) (T.indices.map (·.instL ls)))
    (T.typeApp ls (VExpr.bvars d.params.length
      (d.allTypes.length + d.allCtors.length + T.indices.length)) (VExpr.bvars T.indices.length 0))
    (.app (.appN (.bvar (1 + T.indices.length + d.allCtors.length +
      (d.allTypes.length - 1 - i))) (VExpr.bvars T.indices.length 1)) (.bvar 0))
  simp only [List.length_append, VInductDecl.recBinders, List.length_map, VInductDecl.motiveTypes,
    VInductDecl.minorTypes, List.length_zipIdx, VExpr.length_liftTele] at this
  simpa [VInductDecl.recType, VInductDecl.recBinders, VInductDecl.motiveTypes,
    VInductDecl.minorTypes, Nat.add_assoc] using this

theorem forall₂_imp_mem₂ {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, (∀ a b, a ∈ l₁ → b ∈ l₂ → R a b → S a b) →
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, h, .cons h1 t =>
    .cons (h _ _ (.head _) (.head _) h1)
      (forall₂_imp_mem₂ (fun a b ha hb => h a b (.tail _ ha) (.tail _ hb)) t)

/-- The block's own types, as the final phase adds them, are the restored block's: restoring
leaves their types and the parameters alone, as they mention nothing restoring replaces. -/
theorem restoredType {safety : DefinitionSafety} {venv : VEnv} {types : List InductiveType}
    {nn : Nat} (henv : venv.WF) (H : d.RestoreSpec R ren n ns cname) (hd : d.WF venv)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none)
    (hnn : nn = ns.length) (hnames : types.map (·.name) = (d.restoreNested R ren n ns cname).names)
    {i : Nat} {T : VInductiveType} (hin : i < n) (hi : d.types[i]? = some T) {v : InductiveVal}
    (hv : TrInductValN d lparams nn T v ∧ TrConstant safety venv (.inductInfo v) ⟨d.uvars, T.type⟩ ∧
      (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
        ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params)) :
    let v₁ := { v with all := types.map (·.name) }
    TrInductValN (d.restoreNested R ren n ns cname) lparams
        (d.restoreNested R ren n ns cname).aux.length (T.restore R ren cname none) v₁ ∧
      TrConstant safety venv (.inductInfo v₁)
        ⟨(d.restoreNested R ren n ns cname).uvars, (T.restore R ren cname none).type⟩ ∧
      ((d.restoreNested R ren n ns cname).params.length ≤ v₁.type.leadingForalls →
        ∀ ps B, (T.restore R ren cname none).type = .foralls ps B →
        ps.length = (d.restoreNested R ren n ns cname).params.length →
        venv.TeleDefEq (d.restoreNested R ren n ns cname).uvars [] ps
          (d.restoreNested R ren n ns cname).params) := by
  intro v₁
  obtain ⟨⟨hname, hlp, hnp, hni, -, hctors, hnest, hrec, hunsafe⟩, hc, hagree⟩ := hv
  have hO := henv.ordered
  have hfr {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) :
      e.ConstsSat fun c => R c = none ∧ ren c = none := by
    refine he.mono fun c hc => ?_
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    refine ⟨?_, ?_⟩
    · cases h : R c with
      | none => rfl
      | some _ => rw [hRfresh c _ h] at hci; cases hci
    · cases h : ren c with
      | none => rfl
      | some _ => rw [hrenfresh c _ h] at hci; cases hci
  have hparams : (d.restoreNested R ren n ns cname).params = d.params := by
    simp only [VInductDecl.restoreNested]
    exact (List.map_congr_left fun P hP' => VExpr.restore_of_constsSat
      (hfr (VEnv.IsTele.constsSat hO hd.params trivial P hP'))).trans (List.map_id' _)
  have hT : (T.restore R ren cname none).type = T.type := by
    obtain ⟨_, h⟩ := (hd.types T (List.mem_of_getElem? hi)).1
    exact VExpr.restore_of_constsSat (hfr (h.constsSat hO trivial).1)
  obtain ⟨-, -, hcn⟩ := H.own i T hin hi
  have hlen := H.len
  refine ⟨⟨hname, hlp, ?_, ?_, hnames.symm ▸ rfl, ?_, ?_, hrec, hunsafe⟩, ?_, ?_⟩
  · show v.numParams = _; rw [hparams]; exact hnp
  · show v.numIndices = _; simpa [VInductiveType.restore] using hni
  · show v.ctors = _
    rw [hctors]; simp only [VInductiveType.restore, List.map_map]
    exact List.map_congr_left fun c hc => (hcn c hc).2.2.symm
  · show v.numNested = _
    simp only [VInductDecl.restoreNested, List.length_map, List.length_drop, List.length_zipIdx]
    omega
  · rw [hT]; exact hc
  · intro hle ps B hpB hps
    rw [hparams] at hle hps ⊢
    exact hagree hle ps B (hT ▸ hpB) hps

/-- A recursor's type, as the final phase restores it, is the restored block's. -/
theorem restoredRecType {safety : DefinitionSafety} {venv envT envC envC' : VEnv}
    {types : List InductiveType} (henv : venv.WF)
    (H : d.RestoreSpec R ren n ns cname) (hdN : (d.restoreNested R ren n ns cname).WF venv)
    (hTN : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some envT)
    (hCN : envT.addConstList (d.restoreNested R ren n ns cname).ctorConsts = some envC)
    (hP : d.LeadFreeParts R ren) {r₀ : RecursorVal}
    (SC : RestoreSpec r env' lparams (mkAuxRecNameMap env' types).2 r₀.levelParams
      envC'.ContainsLits R ren)
    (hRC : ∀ c ci, envC'.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    {SN : NameSet}
    (hSN : ∀ c, (R c).isSome ∨ ((mkAuxRecNameMap env' types).2.find? c).isSome → SN.contains c)
    (hlitC : ∀ l, envC'.ContainsLits l → envC.ContainsLits l) {fuel : FuelConfig} {i : Nat}
    {T : VInductiveType} (hi : d.types[i]? = some T)
    (hr₀ : TrConstant safety envC' (.recInfo r₀)
      ⟨d.recUVars, d.recType d.recLevels d.motiveLevel i T⟩)
    (hcleanT : (r.restoreNested env' lparams r₀.type (mkAuxRecNameMap env' types).2).anySub
      (auxP SN) = false)
    (hchkT : (r.restoreNested env' lparams r₀.type (mkAuxRecNameMap env' types).2).anySubterm
        (·.isLet) → ∃ envk, VEnvAt envk safety envC ∧
      checkRestored envk safety r₀.levelParams fuel
        (r.restoreNested env' lparams r₀.type (mkAuxRecNameMap env' types).2) true = .ok ()) :
    TrConstant safety envC (.recInfo (restoreRec env' lparams types r r₀.name r₀))
      ⟨(d.restoreNested R ren n ns cname).recUVars,
        (d.restoreNested R ren n ns cname).recType (d.restoreNested R ren n ns cname).recLevels
          (d.restoreNested R ren n ns cname).motiveLevel i
          (T.restore R ren cname (nestedAt n ns i))⟩ := by
  obtain ⟨hsafe, hlen, htr⟩ := hr₀
  change TrExprS envC' r₀.levelParams [] r₀.type (d.recType d.recLevels d.motiveLevel i T) at htr
  change r₀.levelParams.length = d.recUVars at hlen
  have hTm : T ∈ d.allTypes := by
    rw [VInductDecl.allTypes_of_aux H.flat]; exact List.mem_of_getElem? hi
  have hTN' : (d.restoreNested R ren n ns cname).allTypes[i]? =
      some (T.restore R ren cname (nestedAt n ns i)) := by
    rw [VInductDecl.restoreNested_allTypes_getElem? H, VInductDecl.allTypes_of_aux H.flat, hi]; rfl
  have henvT : envT.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
    exact (hdN.types T' hT').1) hTN
  have henvC : envC.WF := VEnv.WF.addConstList henvT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdN.ctors envT hTN T' (List.mem_append_left _ hT')).2 c hc).type) hCN
  refine ⟨hsafe, hlen, ?_⟩
  show TrExprS envC r₀.levelParams [] (r.restoreNested env' lparams r₀.type _)
    ((d.restoreNested R ren n ns cname).recType d.recLevels d.motiveLevel i
      (T.restore R ren cname (nestedAt n ns i)))
  rw [← H.restore_recType d.recLevels d.motiveLevel hi]
  refine TrExprS.restored_of_final henvC.ordered SC htr hRC hSN hcleanT
    (hP.recType d.recLevels d.motiveLevel hTm) hlitC ?_ hchkT
  rw [H.restore_recType d.recLevels d.motiveLevel hi, hlen]
  obtain ⟨_, h⟩ := VInductDecl.recConsts_WF henv hdN hTN hCN _ (List.mem_map.2
    ⟨(T.restore R ren cname (nestedAt n ns i), i), List.mk_mem_zipIdx_iff_getElem?.2 hTN', rfl⟩)
  exact ⟨_, h⟩

/-- A recursor of the translated block, as the final phase restores it, is the restored block's. -/
theorem restoredRec {safety : DefinitionSafety} {venv envT envC envR envC' envR' : VEnv}
    {types : List InductiveType} (henv : venv.WF)
    (H : d.RestoreSpec R ren n ns cname) (hdN : (d.restoreNested R ren n ns cname).WF venv)
    (hn : 0 < n) (hns : ns ≠ [])
    (hTN : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some envT)
    (hCN : envT.addConstList (d.restoreNested R ren n ns cname).ctorConsts = some envC)
    (hRN : envC.addConstList (d.restoreNested R ren n ns cname).recConsts = some envR)
    (hP : d.LeadFreeParts R ren) {r₀ : RecursorVal}
    (SR : RestoreSpec r env' lparams (mkAuxRecNameMap env' types).2 r₀.levelParams
      envR'.ContainsLits R ren)
    (hRR : ∀ c ci, envR'.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    {SN : NameSet}
    (hSN : ∀ c, (R c).isSome ∨ ((mkAuxRecNameMap env' types).2.find? c).isSome → SN.contains c)
    (hlitR : ∀ l, envR'.ContainsLits l → envR.ContainsLits l)
    (hlitCR : ∀ l, envC'.ContainsLits l → envR'.ContainsLits l)
    (hout : ∀ c h ls args out, R c = some h → r.kRepl env' lparams c ls args = some out →
      ∃ us, out.getAppFn = .const h.name us)
    (hcn : ∀ (j : Nat) T, d.types[j]? = some T → ∀ c ∈ T.ctors,
      r.restoreCtorName env' c.name = cname c.name)
    (hnames : types.map (·.name) = (d.restoreNested R ren n ns cname).names)
    (hlp : lparams.length = d.uvars) {fuel : FuelConfig} {i : Nat} {T : VInductiveType}
    (hi : d.types[i]? = some T)
    (hra : ∀ c ∈ T.ctors, ∀ p ∈ c.recFields, p.2.typeIdx < d.types.length)
    (hr₀ : TrRecVal d lparams envR' i T r₀ ∧
      TrConstant safety envC' (.recInfo r₀) ⟨d.recUVars, d.recType d.recLevels d.motiveLevel i T⟩)
    (hrT : TrConstant safety envC (.recInfo (restoreRec env' lparams types r r₀.name r₀))
      ⟨(d.restoreNested R ren n ns cname).recUVars,
        (d.restoreNested R ren n ns cname).recType (d.restoreNested R ren n ns cname).recLevels
          (d.restoreNested R ren n ns cname).motiveLevel i
          (T.restore R ren cname (nestedAt n ns i))⟩)
    (hM : AddInductive.MajorAt T.name r₀.getMajorIdx r₀.type)
    (hcleanR : ∀ rule ∈ r₀.rules,
      (r.restoreNested env' lparams rule.rhs (mkAuxRecNameMap env' types).2).anySub
        (auxP SN) = false)
    (hchkR : ∀ rule ∈ r₀.rules,
      (r.restoreNested env' lparams rule.rhs (mkAuxRecNameMap env' types).2).anySubterm
        (·.isLet) → ∃ envk, VEnvAt envk safety envR ∧
      checkRestored envk safety r₀.levelParams fuel
        (r.restoreNested env' lparams rule.rhs (mkAuxRecNameMap env' types).2) false = .ok ()) :
    let r₁ := restoreRec env' lparams types r r₀.name r₀
    TrRecVal (d.restoreNested R ren n ns cname) lparams envR i
        (T.restore R ren cname (nestedAt n ns i)) r₁ ∧
      TrConstant safety envC (.recInfo r₁)
        ⟨(d.restoreNested R ren n ns cname).recUVars,
          (d.restoreNested R ren n ns cname).recType (d.restoreNested R ren n ns cname).recLevels
            (d.restoreNested R ren n ns cname).motiveLevel i
            (T.restore R ren cname (nestedAt n ns i))⟩ := by
  intro r₁
  obtain ⟨⟨hname, -, hle1, hle2, hnp, hni, hnm, hnmin, -, hk, hunsafe, hrules⟩, hsafe, hlen, htr⟩ :=
    hr₀
  change TrExprS envC' r₀.levelParams [] r₀.type (d.recType d.recLevels d.motiveLevel i T) at htr
  change r₀.levelParams.length = d.recUVars at hlen
  have hil : i < d.types.length := (List.getElem?_eq_some_iff.1 hi).1
  have hTm : T ∈ d.allTypes := by rw [VInductDecl.allTypes_of_aux H.flat]; exact List.mem_of_getElem? hi
  have hTN' : (d.restoreNested R ren n ns cname).allTypes[i]? =
      some (T.restore R ren cname (nestedAt n ns i)) := by
    rw [VInductDecl.restoreNested_allTypes_getElem? H, VInductDecl.allTypes_of_aux H.flat, hi]; rfl
  -- the restored block's environments and what they type
  have henvT : envT.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
    exact (hdN.types T' hT').1) hTN
  obtain ⟨hGC, hGR⟩ := VInductDecl.generatedWF henv hdN envT envC envR hTN hCN hRN
  have henvC : envC.WF := VEnv.WF.addConstList henvT (fun p hp => by
    obtain ⟨⟨j, c⟩, hc, rfl⟩ := List.mem_map.1 hp
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_ctors hc
    exact ((hdN.ctors envT hTN T' (List.mem_append_left _ hT')).2 c hc).type) hCN
  have henvR : envR.WF := VEnv.WF.addConstList henvC hGC hRN
  -- the recursor's name
  have hfind : (mkAuxRecNameMap env' types).2.find? (d.recName i) = ren (d.recName i) :=
    (SR.ren_eq _).symm
  have hgetD : (mkAuxRecNameMap env' types).2.getD (d.recName i) (d.recName i) =
      (d.restoreNested R ren n ns cname).recName i := by
    have e : ∀ (m : NameMap Name) (k f : Name), m.getD k f = (m.find? k).getD f := fun m k f =>
      Std.TreeMap.getD_eq_getD_getElem? (t := (m : NM))
    rw [e, hfind]
    by_cases hin : i < n
    · rw [(H.recOwn i hin).2, H.recName_own hin]; rfl
    · rw [(H.recAux i (by omega) hil).2]; rfl
  -- the major premise
  have hmajor : r₁.getMajorInduct =
      (((T.restore R ren cname (nestedAt n ns i)).nested).map (·.ind)).getD
        (T.restore R ren cname (nestedAt n ns i)).name := by
    have hidx : r₀.getMajorIdx =
        d.params.length + d.allTypes.length + d.allCtors.length + T.indices.length := by
      simp only [RecursorVal.getMajorIdx, hnp, hnm, hnmin, hni]
    have hD := VInductDecl.recType_domAt (d := d) (ls := d.recLevels) (v := d.motiveLevel) (i := i)
      (T := T)
    rw [← hidx, VInductiveType.typeApp_of_none (H.nested T (List.mem_of_getElem? hi))] at hD
    have hren0 : (mkAuxRecNameMap env' types).2.find? T.name = none := by
      rw [← SR.ren_eq]
      by_cases hin : i < n
      · exact (H.own i T hin hi).2.1
      · obtain ⟨o, -, -, -, hr, -⟩ := H.nestedAt_aux hi (by omega); exact hr
    have hM' := MajorAt.restore SR hout hM (htr.toPTr.mono_lit hlitCR) hD
      (by rw [VInductDecl.recLevels_length, hlp])
      (fun hR => by
        obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 hR
        rw [← SR.n_eq _ _ hh]
        by_cases hin : i < n
        · rw [(H.own i T hin hi).1] at hh; cases hh
        · obtain ⟨o, -, -, hR', -⟩ := H.nestedAt_aux hi (by omega)
          rw [hR'] at hh; cases hh
          simp)
      hren0
    rw [AddInductive.getMajorInduct_eq]
    have hg := AddInductive.MajorAt.go hM'
    rw [← ElimNestedInductive.Result.restoreNested_eq] at hg
    refine hg.trans ?_
    by_cases hin : i < n
    · simp [(H.own i T hin hi).1, VInductiveType.restore, nestedAt, hin]
    · obtain ⟨o, -, hna, hR', -⟩ := H.nestedAt_aux hi (by omega)
      simp [hR', VInductiveType.restore, hna]
  -- the K flag: neither block is a K target, having more than one type
  have hK : ¬d.IsKTarget ∧ ¬(d.restoreNested R ren n ns cname).IsKTarget := by
    have hl := H.len
    refine ⟨fun ⟨_, T', c, hT', _⟩ => ?_, fun ⟨_, T', c, _, haux, _⟩ => ?_⟩
    · have := congrArg List.length hT'
      simp at this
      cases ns with
      | nil => exact hns rfl
      | cons => simp at hl; omega
    · have := congrArg List.length haux
      simp only [VInductDecl.restoreNested, List.length_map, List.length_drop,
        List.length_zipIdx, List.length_nil] at this
      cases ns with
      | nil => exact hns rfl
      | cons => simp at hl; omega
  refine ⟨⟨?_, hmajor, hle1, hle2, ?_, ?_, ?_, ?_, hnames ▸ rfl, ?_, hunsafe, ?_⟩, hrT⟩
  · show (mkAuxRecNameMap env' types).2.getD r₀.name r₀.name = _
    rw [hname, hgetD]
  · show r₀.numParams = _
    rw [VInductDecl.restoreNested_params_length]; exact hnp
  · show r₀.numIndices = _
    simpa [VInductiveType.restore] using hni
  · show r₀.numMotives = _
    rw [VInductDecl.restoreNested_allTypes_length, hnm, VInductDecl.allTypes_of_aux H.flat]
  · show r₀.numMinors = _
    rw [VInductDecl.restoreNested_allCtors_length H]; exact hnmin
  · show r₀.k = true ↔ _
    rw [hk]; exact ⟨fun h => absurd h hK.1, fun h => absurd h hK.2⟩
  · have hz : (d.restoreNested R ren n ns cname).allCtors.zipIdx.filter (·.1.1 = i) =
        (d.allCtors.zipIdx.filter (·.1.1 = i)).map
          fun p : (Nat × VConstructor) × Nat => ((p.1.1, p.1.2.restore R ren cname), p.2) := by
      rw [VInductDecl.restoreNested_allCtors H, List.zipIdx_map, List.filter_map]
      rfl
    show List.Forall₂ _ (r₀.rules.map _) _
    rw [hz, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine forall₂_imp_mem₂ (fun rule ⟨⟨j, c⟩, q⟩ hrule hp ⟨hj, hctor, hnf, hrhs⟩ => ?_) hrules
    subst hj
    obtain ⟨hp, -⟩ := List.mem_filter.1 hp
    have hjc : (j, c) ∈ d.allCtors := List.fst_mem_of_mem_zipIdx hp
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_allCtors_iff.1 hjc
    rw [VInductDecl.allTypes_of_aux H.flat, hi] at hT'; cases hT'
    refine ⟨rfl, ?_, by simpa [VConstructor.restore] using hnf, ?_⟩
    · show r.restoreCtorName env' rule.ctor = cname c.name
      rw [hctor]; exact hcn j T hi c hc
    · have hra' : ∀ p ∈ c.recFields, p.2.typeIdx < d.allTypes.length := by
        rw [VInductDecl.allTypes_of_aux H.flat]; exact hra c hc
      have hrw := H.restore_iotaRule_rhs d.recLevels d.motiveLevel (VLevel.params d.recUVars)
        (q := q) (j := j) (c := c) (by rw [← VInductDecl.allTypes_of_aux H.flat]; exact hra')
      show TrExprS envR r₀.levelParams [] (r.restoreNested env' lparams rule.rhs _)
        ((d.restoreNested R ren n ns cname).iotaRule d.recLevels d.motiveLevel
          (VLevel.params d.recUVars) q j (c.restore R ren cname)).rhs
      rw [← hrw]
      refine TrExprS.restored_of_final henvR.ordered SR hrhs hRR hSN (hcleanR rule hrule)
        (hP.iotaRule_rhs d.recLevels d.motiveLevel _ hTm hc hra') hlitR ?_ (hchkR rule hrule)
      rw [hrw, hlen]
      have hmem : ((j, c.restore R ren cname), q) ∈
          (d.restoreNested R ren n ns cname).allCtors.zipIdx := by
        rw [VInductDecl.restoreNested_allCtors H, List.zipIdx_map]
        exact List.mem_map.2 ⟨_, hp, rfl⟩
      obtain ⟨-, h⟩ := hGR _ (List.mem_map.2 ⟨_, hmem, rfl⟩)
      have hu : ((d.restoreNested R ren n ns cname).iotaRule d.recLevels d.motiveLevel
          (VLevel.params d.recUVars) q j (c.restore R ren cname)).uvars = d.recUVars := by
        simp [VInductDecl.iotaRule]
      exact ⟨_, hu ▸ h⟩

end

/-! ### The translated block's constants, by name -/

theorem forall₂_swap {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ (fun b a => R a b) l₂ l₁
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (forall₂_swap t)

theorem forall₂_getElem?_l {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α}, l₁[i]? = some a →
      ∃ b, l₂[i]? = some b ∧ R a b
  | [], [], .nil, _, _, e => by cases e
  | _ :: _, _ :: _, .cons h _, 0, _, e => by cases e; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, .cons _ t, _ + 1, _, e => forall₂_getElem?_l t e

theorem forall₂_getElem?_r {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b : β}, l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b
  | [], [], .nil, _, _, e => by cases e
  | _ :: _, _ :: _, .cons h _, 0, _, e => by cases e; exact ⟨_, rfl, h⟩
  | _ :: _, _ :: _, .cons _ t, _ + 1, _, e => forall₂_getElem?_r t e

/-- What the check of the translated block added, looked up by name in the environment it
made. -/
theorem AddInductN.flatFind {nn : Nat} {safety : DefinitionSafety} {C : ConstMap}
    {venv venv' : VEnv} {d : VInductDecl} {env' : Kernel.Environment} (hC : C.WF)
    (hflat : AddInductN nn safety C venv d env'.constants venv') (hdaux : d.aux = []) :
    ∃ lps envT envC envR, lps.length = d.uvars ∧ venv.addConstList d.typeConsts = some envT ∧
      envT.addConstList d.ctorConsts = some envC ∧ envC.addConstList d.recConsts = some envR ∧
      envR ≤ venv' ∧
      (∀ (i : Nat) T, d.types[i]? = some T → ∃ v, env'.find? T.name = some (.inductInfo v) ∧
        TrInductValN d lps nn T v ∧ TrConstant safety venv (.inductInfo v) ⟨d.uvars, T.type⟩ ∧
        (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
          ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params)) ∧
      (∀ (i : Nat) T, d.types[i]? = some T → ∀ c ∈ T.ctors, ∃ c₀,
        env'.find? c.name = some (.ctorInfo c₀) ∧ TrCtorVal d lps i c c₀ ∧
        TrConstant safety envT (.ctorInfo c₀) ⟨d.uvars, c.type⟩) ∧
      (∀ (i : Nat) T, d.types[i]? = some T → ∃ r₀, env'.find? (d.recName i) = some (.recInfo r₀) ∧
        TrRecVal d lps envR i T r₀ ∧
        TrConstant safety envC (.recInfo r₀) ⟨d.recUVars, d.recType d.recLevels d.motiveLevel i T⟩) := by
  obtain @⟨lps, envT, envC, envR, types, ctors, recs, hl, hty, hct, hrc, hnd, hfr, ⟨cis, hp, he⟩,
    hT, hC', hR, hB⟩ := hflat
  have hfind : ∀ ci ∈ inductConsts types ctors recs, env'.find? ci.name = some ci := by
    intro ci hci
    have hwf : env'.constants.WF := by
      rw [he]; exact insertConsts_wf hC (fun c hc => hfr c (hp.mem_iff.1 hc))
        ((hp.map _).nodup_iff.2 hnd)
    rw [Kernel.Environment.find?, hwf.find?'_eq_find?, he, insertConsts_perm_find? hC hfr hnd hp]
    exact insertConsts_find?_of_mem hC hfr hnd hci
  refine ⟨lps, envT, envC, envR, hl, hT, hC', hR,
    VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB), fun i T hi => ?_, fun i T hi c hc => ?_,
    fun i T hi => ?_⟩
  · obtain ⟨v, hv0, hv⟩ := forall₂_getElem?_r hty hi
    refine ⟨v, ?_, hv⟩
    rw [← hv.1.1]
    exact hfind _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_of_getElem? hv0))))
  · obtain ⟨c₀, hc₀, hR₀⟩ := Lean4Lean.List.Forall₂.forall_exists_r hct (i, c)
      (VInductDecl.mem_ctors_iff.2 ⟨T, hi, hc⟩)
    refine ⟨c₀, ?_, hR₀⟩
    obtain ⟨_, _, _, hname, -⟩ := hR₀.1
    rw [← hname]
    exact hfind _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hc₀)))
  · obtain ⟨r₀, hr₀, hR₀⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrc (T, i) (by
      rw [VInductDecl.allTypes_of_aux hdaux]; exact List.mk_mem_zipIdx_iff_getElem?.2 hi)
    refine ⟨r₀, ?_, hR₀⟩
    rw [← hR₀.1.1]
    exact hfind _ (List.mem_append_right _ (List.mem_map_of_mem hr₀))

/-- A well-formed block's recursive fields are at its types. -/
theorem VInductDecl.WF.recFields_lt {venv : VEnv} {d : VInductDecl} (hd : d.WF venv)
    {envT : VEnv} (hT : venv.addConstList d.typeConsts = some envT) :
    ∀ T ∈ d.allTypes, ∀ c ∈ T.ctors, ∀ p ∈ c.recFields, p.2.typeIdx < d.allTypes.length := by
  intro T hT' c hc ⟨k, ra⟩ hp
  obtain ⟨ps, Ds, -, -, hfs, -⟩ := ((hd.ctors _ hT T hT').2 c hc).shape
  obtain ⟨f, hf, hra⟩ := VInductDecl.mem_recFields hp
  have := hfs.recArg k f hf
  unfold VInductDecl.RecArgWF at this
  rw [hra] at this
  obtain ⟨_, h, -⟩ := this
  exact (List.getElem?_eq_some_iff.1 h).1

/-- Constructors, type by type, related to a block's constructors. -/
theorem forall₂_ctors {β : Type _} {Q : Nat → VConstructor → β → Prop} :
    ∀ {L : List (α × List β)} {Ts : List (VInductiveType × Nat)},
    List.Forall₂ (fun p (Tj : VInductiveType × Nat) =>
      List.Forall₂ (fun v c => Q Tj.2 c v) p.2 Tj.1.ctors) L Ts →
    List.Forall₂ (fun v (jc : Nat × VConstructor) => Q jc.1 jc.2 v) (L.flatMap (·.2))
      (Ts.map fun (T, j) => T.ctors.map (j, ·)).flatten
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
    refine Lean4Lean.List.Forall₂.append ?_ (forall₂_ctors t)
    simpa [List.forall₂_map_right_iff] using h

/-! ### The restored block's step -/

section
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {R : Name → Option VAuxHead} {ren : Name → Option Name}
  {d : VInductDecl} {n : Nat} {ns : List VNested} {cname : Name → Name}

theorem restoreRec_name {types : List InductiveType} (H : d.RestoreSpec R ren n ns cname)
    (hren : ∀ c, ren c = (mkAuxRecNameMap env' types).2.find? c) {i : Nat}
    (hil : i < d.types.length) (r₀ : RecursorVal) :
    (restoreRec env' lparams types r (d.recName i) r₀).name =
      (d.restoreNested R ren n ns cname).recName i := by
  have e : ∀ (m : NameMap Name) (k f : Name), m.getD k f = (m.find? k).getD f := fun m k f =>
    Std.TreeMap.getD_eq_getD_getElem? (t := (m : NM))
  show (mkAuxRecNameMap env' types).2.getD _ _ = _
  rw [e, ← hren]
  by_cases hin : i < n
  · rw [(H.recOwn i hin).2, H.recName_own hin]; rfl
  · rw [(H.recAux i (by omega) hil).2]; rfl

/-- The restored block's own types are its translation's, so they are types. -/
theorem restoreNested_types_isType {venv : VEnv} (henv : venv.WF) (hd : d.WF venv)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none) :
    ∀ T ∈ (d.restoreNested R ren n ns cname).types,
      venv.IsType (d.restoreNested R ren n ns cname).uvars [] T.type := by
  intro T' hT'
  obtain ⟨j, T, -, hT, rfl⟩ := VInductDecl.mem_restoreNested_types.1 hT'
  obtain ⟨hIT, -⟩ := hd.types T (List.mem_of_getElem? hT)
  have hc := hIT
  obtain ⟨_, h⟩ := hc
  have hC := (h.constsSat henv.ordered trivial).1
  show venv.IsType d.uvars [] (T.type.restore R ren)
  rw [VExpr.restore_of_constsSat (hC.mono fun c hc => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    refine ⟨?_, ?_⟩
    · cases h : R c with
      | none => rfl
      | some _ => rw [hRfresh c _ h] at hci; cases hci
    · cases h : ren c with
      | none => rfl
      | some _ => rw [hrenfresh c _ h] at hci; cases hci)]
  exact hIT

/-- The restored block's parameters are its translation's. -/
theorem restoreNested_params_eq {venv : VEnv} (henv : venv.WF) (hd : d.WF venv)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none) :
    (d.restoreNested R ren n ns cname).params = d.params := by
  have hPC := VEnv.IsTele.constsSat henv.ordered hd.params trivial
  simp only [VInductDecl.restoreNested]
  refine (List.map_congr_left fun P hP => VExpr.restore_of_constsSat ((hPC P hP).mono
    fun c hc => ?_)).trans (List.map_id' _)
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
  refine ⟨?_, ?_⟩
  · cases h : R c with
    | none => rfl
    | some _ => rw [hRfresh c _ h] at hci; cases hci
  · cases h : ren c with
    | none => rfl
    | some _ => rw [hrenfresh c _ h] at hci; cases hci

/-- The final phase's environment with the block's types as axioms is modelled by the
environment with the restored block's types. -/
theorem typeAx_venvAt {env envTk envF : Kernel.Environment} {types : List InductiveType}
    {isUnsafe ap : Bool} {fuel : FuelConfig} {inds : List (InductiveVal × List ConstructorVal)}
    {recs : List RecursorVal}
    (hF : NestedFinalOK env env' lparams types r isUnsafe ap fuel inds recs envTk envF)
    {venv : VEnv} (wf : VEnvAt env (inductSafety isUnsafe) venv) {nn : Nat} {venv' : VEnv}
    (hflat : AddInductN nn (inductSafety isUnsafe) env.constants venv d env'.constants venv')
    (hd : d.WF venv) (H : d.RestoreSpec R ren n ns cname)
    (hn : types.length = n) (hn0 : 0 < n) (hnn : nn = ns.length)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none)
    (hnames : types.map (·.name) = (d.restoreNested R ren n ns cname).names)
    (hap : ap = false)
    (hlpk : ∀ t ∈ types, ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      ind.levelParams = lparams)
    {envT : VEnv} (hTN : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some envT) :
    VEnvAt envTk (inductSafety isUnsafe) envT := by
  have henv := wf.tr.wf
  have hO := henv.ordered
  have hCwf : env.constants.WF := wf.tr.map_wf
  obtain ⟨lps, envT', envC', envR', hl, hT', hC', hR', hRle, hfT, hfC, hfR⟩ :=
    hflat.flatFind hCwf H.flat
  have hlen := H.len
  have hnm (i : Nat) (hi : i < n) (t : InductiveType) (T : VInductiveType)
      (ht : types[i]? = some t) (hT : d.types[i]? = some T) : t.name = T.name := by
    have := congrArg (·[i]?) hnames
    simp only [List.getElem?_map, ht, Option.map_some, VInductDecl.names] at this
    rw [VInductDecl.restoreNested_types_getElem?_of hi hT] at this
    simpa [VInductiveType.restore] using this
  have hTi (i : Nat) (hi : i < n) : ∃ T, d.types[i]? = some T :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hti (i : Nat) (hi : i < n) : ∃ t, types[i]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hlps : lps = lparams := by
    obtain ⟨t, ht⟩ := hti 0 hn0
    obtain ⟨T, hT⟩ := hTi 0 hn0
    obtain ⟨v, hv, ⟨-, hvl, -⟩, -⟩ := hfT 0 T hT
    rw [← hvl]
    exact hlpk t (List.mem_of_getElem? ht) v (hnm 0 hn0 t T ht hT ▸ hv)
  rw [hlps] at hl hfT hfC hfR
  obtain ⟨cisN, hpN, heN, hndN, hfrN, hprimN, -⟩ := hF.addConsts hCwf
  have hindsLen : inds.length = n := by
    rw [← hn, Lean4Lean.List.Forall₂.length_eq hF.indsSpec]
  have hinds (i : Nat) (hi : i < n) : ∃ p T v, inds[i]? = some p ∧ d.types[i]? = some T ∧
      env'.find? T.name = some (.inductInfo v) ∧ p.1 = { v with all := types.map (·.name) } ∧
      (TrInductValN d lparams nn T v ∧
        TrConstant (inductSafety isUnsafe) venv (.inductInfo v) ⟨d.uvars, T.type⟩ ∧
        (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
          ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params)) := by
    obtain ⟨t, ht⟩ := hti i hi
    obtain ⟨T, hT⟩ := hTi i hi
    obtain ⟨p, hp, hPp⟩ := forall₂_getElem?_l hF.indsSpec ht
    obtain ⟨v, hv, hvT⟩ := hfT i T hT
    obtain ⟨h1, -⟩ := hPp v (hnm i hi t T ht hT ▸ hv)
    exact ⟨p, T, v, hp, hT, hv, h1, hvT⟩
  have hdNlen : (d.restoreNested R ren n ns cname).types.length = n := by
    simp [VInductDecl.restoreNested]; omega
  have tyF : List.Forall₂ (fun v T =>
      TrInductValN (d.restoreNested R ren n ns cname) lparams
        (d.restoreNested R ren n ns cname).aux.length T v ∧
      TrConstant (inductSafety isUnsafe) venv (.inductInfo v)
        ⟨(d.restoreNested R ren n ns cname).uvars, T.type⟩ ∧
      ((d.restoreNested R ren n ns cname).params.length ≤ v.type.leadingForalls →
        ∀ ps B, T.type = .foralls ps B → ps.length = (d.restoreNested R ren n ns cname).params.length →
        venv.TeleDefEq (d.restoreNested R ren n ns cname).uvars [] ps
          (d.restoreNested R ren n ns cname).params))
      (inds.map (·.1)) (d.restoreNested R ren n ns cname).types := by
    refine Lean4Lean.List.forall₂_of_getElem? (by simp [hindsLen, hdNlen]) fun j a b ha hb => ?_
    have hj : j < n := by
      have := (List.getElem?_eq_some_iff.1 ha).1; simpa [hindsLen] using this
    obtain ⟨p, T, v, hp, hT, -, hpv, hvT⟩ := hinds j hj
    rw [List.getElem?_map, hp, Option.map_some, Option.some.injEq] at ha
    rw [VInductDecl.restoreNested_types_getElem?_of hj hT, Option.some.injEq] at hb
    subst ha hb
    rw [hpv]
    exact restoredType henv H hd hRfresh hrenfresh hnn hnames hj hT hvT
  have hTyp := restoreNested_types_isType (n := n) (ns := ns) (cname := cname) henv hd hRfresh
    hrenfresh
  have hcsNames : (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs).map (·.name) =
      (inds.map (·.1)).map (·.name) ++ (inds.flatMap (·.2)).map (·.name) ++
        recs.map (·.name) := by
    simp [inductConsts, List.map_map, Function.comp_def, ConstantInfo.name,
      ConstantInfo.toConstantVal]
  have hnoprim (nm : Name) (h : nm ∈ (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs).map
      (·.name)) : Kernel.Environment.primitives.contains nm = false := by
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 h
    cases hc : Kernel.Environment.primitives.contains ci.name
    · rfl
    · exact absurd (hprimN ci hci hc) (by simp [hap])
  rw [hcsNames] at hnoprim
  have hax := hF.typeAx
  have e : typeAxiomsN inds lparams isUnsafe =
      (inds.map fun p => AxiomVal.mk ⟨p.1.name, lparams, p.1.type⟩ isUnsafe).map .axiomInfo := by
    simp [typeAxiomsN, List.map_map, Function.comp_def]
  rw [e] at hax
  refine CheckedAdds.venvAt wf hax ?_ (fun ax hax' => ?_) hTN
  · simp only [VInductDecl.typeConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    have := List.forall₂_map_left_iff.1 tyF
    refine forall₂_imp_mem₂ (fun p T _ hT ⟨⟨hname, hlp, _, _, _, _, _, _, hpu⟩,
      ⟨hsafe, hlen, htr⟩, _⟩ => ?_) this
    refine ⟨hname, ⟨?_, ?_, ?_⟩, hTyp T hT⟩
    · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
    · change lparams.length = _; rw [← hlp]; exact hlen
    · change TrExprS venv lparams [] p.1.type T.type; rw [← hlp]; exact htr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hax'
    exact hnoprim _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_map_of_mem hp))))

/-- **The restored block's step.** What the final phase of a nested block adds is the restored
block's `AddInduct` step, given what the check of the translated block established
(`AddInductN`) and how the restoration relates to the translation. -/
theorem nestedAddInduct {env envTk envF : Kernel.Environment} {types : List InductiveType}
    {isUnsafe ap : Bool} {fuel : FuelConfig} {inds : List (InductiveVal × List ConstructorVal)}
    {recs : List RecursorVal}
    (hF : NestedFinalOK env env' lparams types r isUnsafe ap fuel inds recs envTk envF)
    {venv : VEnv} (wf : VEnvAt env (inductSafety isUnsafe) venv) {nn : Nat} {venv' : VEnv}
    (hflat : AddInductN nn (inductSafety isUnsafe) env.constants venv d env'.constants venv')
    (hd : d.WF venv)
    (H : d.RestoreSpec R ren n ns cname) (hdN : (d.restoreNested R ren n ns cname).WF venv)
    (hn : types.length = n) (hn0 : 0 < n) (hns : ns ≠ []) (hnn : nn = ns.length)
    (hS : ∀ Us (E : VEnv), venv ≤ E → (∀ l, E.ContainsLits l → venv.ContainsLits l) →
      RestoreSpec r env' lparams (mkAuxRecNameMap env' types).2 Us E.ContainsLits R ren)
    (hP : d.LeadFreeParts R ren) (hcL : ∀ T ∈ d.types, ∀ c ∈ T.ctors, c.type.LeadFree R ren)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none)
    (hout : ∀ c h ls args out, R c = some h → r.kRepl env' lparams c ls args = some out →
      ∃ us, out.getAppFn = .const h.name us)
    (hcn : ∀ (j : Nat) T, d.types[j]? = some T → ∀ c ∈ T.ctors,
      r.restoreCtorName env' c.name = cname c.name)
    (hnames : types.map (·.name) = (d.restoreNested R ren n ns cname).names)
    (hSN : ∀ c, (R c).isSome ∨ ((mkAuxRecNameMap env' types).2.find? c).isSome →
      (auxNameSet r types (mkAuxRecNameMap env' types).1).contains c)
    (hM : ∀ i T r₀, d.types[i]? = some T → env'.find? (d.recName i) = some (.recInfo r₀) →
      AddInductive.MajorAt T.name r₀.getMajorIdx r₀.type)
    (hap : ap = false) (hlit : ∀ l, venv'.ContainsLits l → venv.ContainsLits l)
    (hlpk : ∀ t ∈ types, ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      ind.levelParams = lparams) :
    ∃ venvF, AddInductN (d.restoreNested R ren n ns cname).aux.length (inductSafety isUnsafe)
      env.constants venv (d.restoreNested R ren n ns cname) envF.constants venvF := by
  have henv := wf.tr.wf
  have hCwf : env.constants.WF := wf.tr.map_wf
  obtain ⟨lps, envT', envC', envR', hl, hT', hC', hR', hRle, hfT, hfC, hfR⟩ :=
    hflat.flatFind hCwf H.flat
  have hfresh (nm : Name) (h : env.constants.find? nm = none) : venv.constants nm = none :=
    wf.tr.constants_eq_none (by rwa [Kernel.Environment.find?, hCwf.find?'_eq_find?])
  have hlen := H.len
  have hdl : n ≤ d.types.length := by omega
  -- the input types are the translated block's first, by name
  have hnm (i : Nat) (hi : i < n) (t : InductiveType) (T : VInductiveType)
      (ht : types[i]? = some t) (hT : d.types[i]? = some T) : t.name = T.name := by
    have := congrArg (·[i]?) hnames
    simp only [List.getElem?_map, ht, Option.map_some, VInductDecl.names] at this
    rw [VInductDecl.restoreNested_types_getElem?_of hi hT] at this
    simpa [VInductiveType.restore] using this
  have hTi (i : Nat) (hi : i < n) : ∃ T, d.types[i]? = some T :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hti (i : Nat) (hi : i < n) : ∃ t, types[i]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  -- the translated block's level parameters are the kernel's
  have hlps : lps = lparams := by
    obtain ⟨t, ht⟩ := hti 0 hn0
    obtain ⟨T, hT⟩ := hTi 0 hn0
    obtain ⟨v, hv, ⟨-, hvl, -⟩, -⟩ := hfT 0 T hT
    rw [← hvl]
    exact hlpk t (List.mem_of_getElem? ht) v (hnm 0 hn0 t T ht hT ▸ hv)
  rw [hlps] at hl hfT hfC hfR
  obtain ⟨cisN, hpN, heN, hndN, hfrN, hprimN, -⟩ := hF.addConsts hCwf
  have hindsLen : inds.length = n := by
    rw [← hn, Lean4Lean.List.Forall₂.length_eq hF.indsSpec]
  -- each kernel type, with its constructors, is a translated block's own type restored
  have hinds (i : Nat) (hi : i < n) : ∃ p T v, inds[i]? = some p ∧ d.types[i]? = some T ∧
      env'.find? T.name = some (.inductInfo v) ∧ p.1 = { v with all := types.map (·.name) } ∧
      (TrInductValN d lparams nn T v ∧
        TrConstant (inductSafety isUnsafe) venv (.inductInfo v) ⟨d.uvars, T.type⟩ ∧
        (d.params.length ≤ v.type.leadingForalls → ∀ ps B, T.type = .foralls ps B →
          ps.length = d.params.length → venv.TeleDefEq d.uvars [] ps d.params)) ∧
      List.Forall₂ (fun nm (c₁ : ConstructorVal) => ∀ c₀, env'.find? nm = some (.ctorInfo c₀) →
        c₁ = { c₀ with
          type := (r.restoreNested env' lparams c₀.type (mkAuxRecNameMap env' types).2) })
        (T.ctors.map (·.name)) p.2 := by
    obtain ⟨t, ht⟩ := hti i hi
    obtain ⟨T, hT⟩ := hTi i hi
    obtain ⟨p, hp, hPp⟩ := forall₂_getElem?_l hF.indsSpec ht
    obtain ⟨v, hv, hvT⟩ := hfT i T hT
    obtain ⟨h1, h2⟩ := hPp v (hnm i hi t T ht hT ▸ hv)
    have hvc := hvT.1.2.2.2.2.2.1
    exact ⟨p, T, v, hp, hT, hv, h1, hvT, hvc ▸ h2⟩
  have hdNlen : (d.restoreNested R ren n ns cname).types.length = n := by
    simp [VInductDecl.restoreNested]; omega
  -- the types
  have tyF : List.Forall₂ (fun v T =>
      TrInductValN (d.restoreNested R ren n ns cname) lparams
        (d.restoreNested R ren n ns cname).aux.length T v ∧
      TrConstant (inductSafety isUnsafe) venv (.inductInfo v)
        ⟨(d.restoreNested R ren n ns cname).uvars, T.type⟩ ∧
      ((d.restoreNested R ren n ns cname).params.length ≤ v.type.leadingForalls →
        ∀ ps B, T.type = .foralls ps B → ps.length = (d.restoreNested R ren n ns cname).params.length →
        venv.TeleDefEq (d.restoreNested R ren n ns cname).uvars [] ps
          (d.restoreNested R ren n ns cname).params))
      (inds.map (·.1)) (d.restoreNested R ren n ns cname).types := by
    refine Lean4Lean.List.forall₂_of_getElem? (by simp [hindsLen, hdNlen]) fun j a b ha hb => ?_
    have hj : j < n := by
      have := (List.getElem?_eq_some_iff.1 ha).1; simpa [hindsLen] using this
    obtain ⟨p, T, v, hp, hT, -, hpv, hvT, -⟩ := hinds j hj
    rw [List.getElem?_map, hp, Option.map_some, Option.some.injEq] at ha
    rw [VInductDecl.restoreNested_types_getElem?_of hj hT, Option.some.injEq] at hb
    subst ha hb
    rw [hpv]
    exact restoredType henv H hd hRfresh hrenfresh hnn hnames hj hT hvT
  have tyNames : (inds.map (·.1)).map (·.name) =
      (d.restoreNested R ren n ns cname).types.map (·.name) :=
    Lean4Lean.List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1.1) tyF)
  -- the names the final phase adds
  have hcsNames : (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs).map (·.name) =
      (inds.map (·.1)).map (·.name) ++ (inds.flatMap (·.2)).map (·.name) ++
        recs.map (·.name) := by
    simp [inductConsts, List.map_map, Function.comp_def, ConstantInfo.name,
      ConstantInfo.toConstantVal]
  rw [hcsNames] at hndN
  have hfrK (nm : Name) (h : nm ∈ (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs).map
      (·.name)) : venv.constants nm = none := by
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 h
    exact hfresh _ (hfrN ci hci)
  rw [hcsNames] at hfrK
  obtain ⟨⟨hndT, hndC, hdTC⟩, hndR, hdR⟩ :=
    (List.nodup_append.1 hndN).imp_left List.nodup_append.1
  obtain ⟨envT, hTN⟩ : ∃ envT,
      venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some envT := by
    refine VEnv.exists_addConstList (fun p hp => hfrK _ ?_) ?_
    · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
      exact List.mem_append_left _ (List.mem_append_left _ (tyNames ▸ List.mem_map_of_mem hT))
    · simpa [VInductDecl.typeConsts, List.map_map, Function.comp_def, ← tyNames] using hndT
  have hTle : venv ≤ envT := VEnv.addConstList_le hTN
  have hT'le : envT' ≤ venv' :=
    (VEnv.addConstList_le hC').trans ((VEnv.addConstList_le hR').trans hRle)
  have hC'le : envC' ≤ venv' := (VEnv.addConstList_le hR').trans hRle
  have hnoprim (nm : Name) (h : nm ∈ (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs).map
      (·.name)) : Kernel.Environment.primitives.contains nm = false := by
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 h
    cases hc : Kernel.Environment.primitives.contains ci.name
    · rfl
    · exact absurd (hprimN ci hci hc) (by simp [hap])
  rw [hcsNames] at hnoprim
  -- the types as axioms model the environment the final phase checks against
  have hVT : VEnvAt envTk (inductSafety isUnsafe) envT := by
    have hax := hF.typeAx
    have e : typeAxiomsN inds lparams isUnsafe =
        (inds.map fun p => AxiomVal.mk ⟨p.1.name, lparams, p.1.type⟩ isUnsafe).map .axiomInfo := by
      simp [typeAxiomsN, List.map_map, Function.comp_def]
    rw [e] at hax
    refine CheckedAdds.venvAt wf hax ?_ (fun ax hax' => ?_) hTN
    · simp only [VInductDecl.typeConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      have := List.forall₂_map_left_iff.1 tyF
      refine forall₂_imp_mem₂ (fun p T _ hT ⟨⟨hname, hlp, _, _, _, _, _, _, hpu⟩,
        ⟨hsafe, hlen, htr⟩, _⟩ => ?_) this
      refine ⟨hname, ⟨?_, ?_, ?_⟩, (hdN.types T hT).1⟩
      · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
      · change lparams.length = _; rw [← hlp]; exact hlen
      · change TrExprS venv lparams [] p.1.type T.type; rw [← hlp]; exact htr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hax'
      exact hnoprim _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_map_of_mem hp))))
  -- the auxiliary constants of the translated block's environments are at the block's levels
  have hRar (E : VEnv) (hE : ∀ c ci, E.constants c = some ci → venv.constants c = some ci ∨
      (c, ci) ∈ d.typeConsts ∨ (c, ci) ∈ d.ctorConsts ∨ (c, ci) ∈ d.recConsts) :
      ∀ c ci, E.constants c = some ci → (R c).isSome → ci.uvars = lparams.length := by
    intro c ci hc hRc
    obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 hRc
    rcases hE c ci hc with h1 | h1 | h1 | h1
    · rw [hRfresh c h hh] at h1; cases h1
    · obtain ⟨T, -, he⟩ := List.mem_map.1 h1; cases he; exact hl.symm
    · obtain ⟨_, -, he⟩ := List.mem_map.1 h1; cases he; exact hl.symm
    · obtain ⟨⟨T, j⟩, hj, he⟩ := List.mem_map.1 h1
      cases he
      have hjl := (List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hj)).1
      rw [VInductDecl.allTypes_of_aux H.flat] at hjl
      have : R (d.recName j) = none := by
        by_cases hjn : j < n
        · exact (H.recOwn j hjn).1
        · exact (H.recAux j (by omega) hjl).1
      rw [this] at hh; cases hh
  have hRT := hRar envT' fun c ci h => by
    rcases VEnv.addConstList_constants_cases hT' h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have hRC := hRar envC' fun c ci h => by
    rcases VEnv.addConstList_constants_cases hC' h with h | h
    · rcases VEnv.addConstList_constants_cases hT' h with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  have hRR := hRar envR' fun c ci h => by
    rcases VEnv.addConstList_constants_cases hR' h with h | h
    · rcases VEnv.addConstList_constants_cases hC' h with h | h
      · rcases VEnv.addConstList_constants_cases hT' h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  have hcleanAll := hF.clean
  -- the constructors
  have ctF : List.Forall₂ (fun v (jc : Nat × VConstructor) =>
      TrCtorVal (d.restoreNested R ren n ns cname) lparams jc.1 jc.2 v ∧
      TrConstant (inductSafety isUnsafe) envT (.ctorInfo v)
        ⟨(d.restoreNested R ren n ns cname).uvars, jc.2.type⟩)
      (inds.flatMap (·.2)) (d.restoreNested R ren n ns cname).ctors := by
    refine forall₂_ctors (Q := fun j c v =>
      TrCtorVal (d.restoreNested R ren n ns cname) lparams j c v ∧
      TrConstant (inductSafety isUnsafe) envT (.ctorInfo v)
        ⟨(d.restoreNested R ren n ns cname).uvars, c.type⟩) ?_
    refine Lean4Lean.List.forall₂_of_getElem? (by simp [hindsLen, hdNlen]) fun j p Tj hp hTj => ?_
    have hj : j < n := by
      have := (List.getElem?_eq_some_iff.1 hp).1; simpa [hindsLen] using this
    obtain ⟨p', T, v, hp', hT, -, -, -, hctors⟩ := hinds j hj
    rw [hp] at hp'; cases hp'
    rw [List.getElem?_zipIdx, VInductDecl.restoreNested_types_getElem?_of hj hT] at hTj
    cases hTj
    have hpm : p ∈ inds := List.mem_of_getElem? hp
    have hTm : T ∈ d.types := List.mem_of_getElem? hT
    show List.Forall₂ _ p.2 (T.ctors.map (·.restore R ren cname))
    rw [List.forall₂_map_right_iff]
    rw [List.forall₂_map_left_iff] at hctors
    have hflip : List.Forall₂ (fun c₁ c => ∀ c₀, env'.find? c.name = some (.ctorInfo c₀) →
        c₁ = { c₀ with
          type := (r.restoreNested env' lparams c₀.type (mkAuxRecNameMap env' types).2) })
        p.2 T.ctors := forall₂_swap hctors
    refine forall₂_imp_mem₂ (fun c₁ c hc₁ hc hce => ?_) hflip
    obtain ⟨c₀, hc₀f, hc₀⟩ := hfC j T hT c hc
    have e := hce c₀ hc₀f
    subst e
    simp only [Nat.zero_add]
    refine restoredCtor (fuel := fuel) henv H hdN hTN (hS lparams envT' (VEnv.addConstList_le hT')
      fun l h => hlit l (VEnv.ContainsLits.mono hT'le h))
      hRT hSN
      (fun l h => VEnv.ContainsLits.mono hTle (hlit l (VEnv.ContainsLits.mono hT'le h)))
      hj hc₀ (hcL T hTm c hc) (hcleanAll _ ?_) (fun hlet => ?_)
    · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hpm, List.mem_map_of_mem hc₁⟩)
    · have hany : (restoredTerms inds recs).any (·.anySubterm (·.isLet)) :=
        List.any_eq_true.2 ⟨_, List.mem_append_left _
          (List.mem_flatMap.2 ⟨p, hpm, List.mem_map_of_mem hc₁⟩), hlet⟩
      obtain ⟨_, _, -, -, hck, -, -⟩ := hF.lets hany
      exact ⟨envTk, hVT, hck p hpm _ hc₁⟩
  have ctNames : (inds.flatMap (·.2)).map (·.name) =
      (d.restoreNested R ren n ns cname).ctors.map (·.2.name) :=
    Lean4Lean.List.Forall₂.map_eq (Lean4Lean.List.Forall₂.imp
      (fun _ _ h => by obtain ⟨_, -, -, h, -⟩ := h.1; exact h) ctF)
  obtain ⟨envC, hCN⟩ : ∃ envC,
      envT.addConstList (d.restoreNested R ren n ns cname).ctorConsts = some envC := by
    refine VEnv.exists_addConstList (fun p hp => ?_) ?_
    · obtain ⟨jc, hjc, rfl⟩ := List.mem_map.1 hp
      have hm : jc.2.name ∈ (inds.flatMap (·.2)).map (·.name) :=
        ctNames ▸ List.mem_map_of_mem hjc
      refine VEnv.addConstList_constants_none hTN
        (hfrK _ (List.mem_append_left _ (List.mem_append_right _ hm))) fun h => ?_
      simp only [VInductDecl.typeConsts, List.map_map, Function.comp_def] at h
      exact hdTC _ (tyNames ▸ h) _ hm rfl
    · simpa [VInductDecl.ctorConsts, List.map_map, Function.comp_def, ← ctNames] using hndC
  have hCle : envT ≤ envC := VEnv.addConstList_le hCN
  -- the recursors, by name
  obtain ⟨t0, ts, hts⟩ : ∃ t0 ts, types = t0 :: ts := by
    cases types with
    | nil => simp at hn; omega
    | cons t0 ts => exact ⟨t0, ts, rfl⟩
  obtain ⟨T0, hT0⟩ := hTi 0 hn0
  obtain ⟨v0, hv0, ⟨-, -, -, -, hall0, -⟩, -⟩ := hfT 0 T0 hT0
  have ht0 : t0.name = T0.name := hnm 0 hn0 t0 T0 (by simp [hts]) hT0
  have hRecNames : types.map (fun t => mkRecName t.name) ++ (mkAuxRecNameMap env' types).1 =
      d.types.zipIdx.map fun p => d.recName p.2 := by
    have hnsl : 0 < ns.length := List.length_pos_iff.2 hns
    have hsp := (mkAuxRecNameMap_spec (env' := env') (T := t0) (Ts := ts) (info := v0)
      (by rw [ht0]; exact hv0)
      (by rw [hall0, VInductDecl.names, List.length_map, ← hts, hn]; omega)).1
    rw [← hts] at hsp
    rw [hsp, hall0, VInductDecl.names]
    refine List.ext_getElem (by simp [hn]; omega) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hi2 : i < d.types.length := by simpa using h2
    rw [VInductDecl.recName, dif_pos hi2]
    by_cases hin : i < n
    · rw [List.getElem_append_left (by simpa [hn] using hin), List.getElem_map]
      have := hnm i hin types[i] d.types[i] (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem hi2)
      rw [this]
    · rw [List.getElem_append_right (by simp [hn]; omega)]
      simp [hn, List.getElem_drop, show n + (i - n) = i by omega]
  have hrecs (i : Nat) (hi : i < d.types.length) : ∃ T r₀ r₁, d.types[i]? = some T ∧
      recs[i]? = some r₁ ∧ env'.find? (d.recName i) = some (.recInfo r₀) ∧
      r₁ = restoreRec env' lparams types r (d.recName i) r₀ ∧
      TrRecVal d lparams envR' i T r₀ ∧ TrConstant (inductSafety isUnsafe) envC' (.recInfo r₀)
        ⟨d.recUVars, d.recType d.recLevels d.motiveLevel i T⟩ := by
    obtain ⟨T, hT⟩ : ∃ T, d.types[i]? = some T := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨r₀, hr₀f, hr₀⟩ := hfR i T hT
    have hL : (types.map (fun t => mkRecName t.name) ++ (mkAuxRecNameMap env' types).1)[i]? =
        some (d.recName i) := by
      rw [hRecNames, List.getElem?_map, List.getElem?_zipIdx, hT]; simp
    obtain ⟨r₁, hr₁, hP⟩ := forall₂_getElem?_l hF.recsSpec hL
    exact ⟨T, r₀, r₁, hT, hr₁, hr₀f, hP r₀ hr₀f, hr₀⟩
  have hrecsLen : recs.length = d.types.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hF.recsSpec, hRecNames]; simp
  have hC'le' : venv ≤ envC' := (VEnv.addConstList_le hT').trans (VEnv.addConstList_le hC')
  have hR'le : venv ≤ envR' := hC'le'.trans (VEnv.addConstList_le hR')
  have hrecMem (i : Nat) (r₁ : RecursorVal) (h : recs[i]? = some r₁) : ∀ e ∈ r₁.type ::
      r₁.rules.map (·.rhs), e ∈ restoredTerms inds recs := fun e he =>
    List.mem_append_right _ (List.mem_flatMap.2 ⟨r₁, List.mem_of_getElem? h, he⟩)
  -- the constructors as axioms model the environment the recursors' types are checked against
  have hVC (envCk : Kernel.Environment)
      (hck : CheckedAdds ap envTk (ctorAxiomsN inds lparams isUnsafe) envCk) :
      VEnvAt envCk (inductSafety isUnsafe) envC := by
    have e : ctorAxiomsN inds lparams isUnsafe = ((inds.flatMap (·.2)).map fun c =>
        AxiomVal.mk ⟨c.name, lparams, c.type⟩ isUnsafe).map .axiomInfo := by
      simp [ctorAxiomsN, List.map_flatMap, Function.comp_def]
    rw [e] at hck
    refine CheckedAdds.venvAt hVT hck ?_ (fun ax hax' => ?_) hCN
    · simp only [VInductDecl.ctorConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine forall₂_imp_mem₂ (fun c jc _ hjc ⟨⟨_, _, _, hname, hlp, _⟩, ⟨hsafe, hlen, htr⟩⟩ =>
        ?_) ctF
      obtain ⟨T, hT, hcT⟩ := VInductDecl.mem_ctors hjc
      refine ⟨hname, ⟨?_, ?_, ?_⟩,
        ((hdN.ctors envT hTN T (VInductDecl.mem_allTypes_of_types hT)).2 _ hcT).type⟩
      · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
      · change lparams.length = _; rw [← hlp]; exact hlen
      · change TrExprS envT lparams [] c.type jc.2.type; rw [← hlp]; exact htr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hax'
      exact hnoprim _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hc)))
  -- the recursors' types
  have rtF (i : Nat) (hi : i < d.types.length) : ∃ T r₁, d.types[i]? = some T ∧
      recs[i]? = some r₁ ∧
      TrConstant (inductSafety isUnsafe) envC (.recInfo r₁)
        ⟨(d.restoreNested R ren n ns cname).recUVars,
          (d.restoreNested R ren n ns cname).recType (d.restoreNested R ren n ns cname).recLevels
            (d.restoreNested R ren n ns cname).motiveLevel i
            (T.restore R ren cname (nestedAt n ns i))⟩ := by
    obtain ⟨T, r₀, r₁, hT, hr₁, -, rfl, hr₀, hr₀c⟩ := hrecs i hi
    refine ⟨T, _, hT, hr₁, ?_⟩
    have hname : r₀.name = d.recName i := hr₀.1
    rw [← hname]
    refine restoredRecType (fuel := fuel) henv H hdN hTN hCN hP (hS _ envC' hC'le' fun l h => hlit l (VEnv.ContainsLits.mono hC'le h)) hRC hSN
      (fun l h => VEnv.ContainsLits.mono (hTle.trans hCle) (hlit l (VEnv.ContainsLits.mono hC'le h)))
      hT hr₀c (hcleanAll _ ?_) (fun hlet => ?_)
    · exact hrecMem i _ (hname ▸ hr₁) _ (.head _)
    · have hany : (restoredTerms inds recs).any (·.anySubterm (·.isLet)) :=
        List.any_eq_true.2 ⟨_, hrecMem i _ (hname ▸ hr₁) _ (.head _), hlet⟩
      obtain ⟨envCk, _, h1, -, -, hck, -⟩ := hF.lets hany
      exact ⟨envCk, hVC envCk h1, hck _ (List.mem_of_getElem? (hname ▸ hr₁))⟩
  -- the recursors' names
  have hdNTl : (d.restoreNested R ren n ns cname).allTypes.length = d.types.length :=
    VInductDecl.restoreNested_allTypes_length
  have rcNames : recs.map (·.name) = (d.restoreNested R ren n ns cname).recConsts.map (·.1) := by
    refine List.ext_getElem (by simp [VInductDecl.recConsts, hrecsLen, hdNTl]) fun i h1 h2 => ?_
    have hi : i < d.types.length := by simpa [hrecsLen] using h1
    obtain ⟨T, r₀, r₁, -, hr₁, -, rfl, -, -⟩ := hrecs i hi
    simp only [List.getElem_map, VInductDecl.recConsts, List.getElem_zipIdx, Nat.zero_add]
    rw [List.getElem?_eq_getElem (by simpa using h1 : i < recs.length), Option.some.injEq] at hr₁
    rw [hr₁]
    exact restoreRec_name H ((hS lparams venv VEnv.LE.rfl fun _ h => h).ren_eq) hi r₀
  obtain ⟨envR, hRN⟩ : ∃ envR,
      envC.addConstList (d.restoreNested R ren n ns cname).recConsts = some envR := by
    refine VEnv.exists_addConstList (fun p hp => ?_) ?_
    · have hm : p.1 ∈ recs.map (·.name) := rcNames ▸ List.mem_map_of_mem hp
      refine VEnv.addConstList_constants_none hCN (VEnv.addConstList_constants_none hTN
        (hfrK _ (List.mem_append_right _ hm)) fun h => ?_) fun h => ?_
      · simp only [VInductDecl.typeConsts, List.map_map, Function.comp_def] at h
        exact hdR _ (List.mem_append_left _ (tyNames ▸ h)) _ hm rfl
      · simp only [VInductDecl.ctorConsts, List.map_map, Function.comp_def] at h
        exact hdR _ (List.mem_append_right _ (ctNames ▸ h)) _ hm rfl
    · rw [← rcNames]; exact hndR
  -- the recursors as axioms model the environment the rules are checked against
  have hVR (envCk envRk : Kernel.Environment)
      (h1 : CheckedAdds ap envTk (ctorAxiomsN inds lparams isUnsafe) envCk)
      (h2 : CheckedAdds ap envCk (recAxiomsN recs isUnsafe) envRk) :
      VEnvAt envRk (inductSafety isUnsafe) envR := by
    have e : recAxiomsN recs isUnsafe = (recs.map fun r =>
        AxiomVal.mk ⟨r.name, r.levelParams, r.type⟩ isUnsafe).map .axiomInfo := by
      simp [recAxiomsN, Function.comp_def]
    rw [e] at h2
    refine CheckedAdds.venvAt (hVC envCk h1) h2 ?_ (fun ax hax' => ?_) hRN
    · simp only [VInductDecl.recConsts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine Lean4Lean.List.forall₂_of_getElem? (by simp [hrecsLen, hdNTl])
        fun i r₁ p hr₁ hp => ?_
      have hi : i < d.types.length := by
        have := (List.getElem?_eq_some_iff.1 hr₁).1; omega
      obtain ⟨T, r₁', hT, hr₁', hrT⟩ := rtF i hi
      rw [hr₁] at hr₁'; cases hr₁'
      rw [List.getElem?_zipIdx, VInductDecl.restoreNested_allTypes_getElem? H,
        VInductDecl.allTypes_of_aux H.flat, hT] at hp
      simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
      subst hp
      obtain ⟨hsafe, hlen, htr⟩ := hrT
      have hname : r₁.name = (d.restoreNested R ren n ns cname).recName i := by
        obtain ⟨_, r₀, _, -, hr₁'', -, e, -, -⟩ := hrecs i hi
        rw [hr₁] at hr₁''; cases hr₁''
        rw [e]; exact restoreRec_name H ((hS lparams venv VEnv.LE.rfl fun _ h => h).ren_eq) hi r₀
      refine ⟨hname, ⟨?_, hlen, htr⟩, ?_⟩
      · simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial]
      · exact VInductDecl.recConsts_WF henv hdN hTN hCN _ (List.mem_map.2 ⟨_,
          List.mk_mem_zipIdx_iff_getElem?.2 (by
            rw [VInductDecl.restoreNested_allTypes_getElem? H, VInductDecl.allTypes_of_aux H.flat,
              hT]; rfl), rfl⟩)
    · obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.1 hax'
      exact hnoprim _ (List.mem_append_right _ (List.mem_map_of_mem hr₁))
  have hRNle : envC ≤ envR := VEnv.addConstList_le hRN
  have hra := VInductDecl.WF.recFields_lt hd hT'
  rw [VInductDecl.allTypes_of_aux H.flat] at hra
  -- the recursors
  have rcF : List.Forall₂ (fun v (Ti : VInductiveType × Nat) =>
      TrRecVal (d.restoreNested R ren n ns cname) lparams envR Ti.2 Ti.1 v ∧
      TrConstant (inductSafety isUnsafe) envC (.recInfo v)
        ⟨(d.restoreNested R ren n ns cname).recUVars,
          (d.restoreNested R ren n ns cname).recType (d.restoreNested R ren n ns cname).recLevels
            (d.restoreNested R ren n ns cname).motiveLevel Ti.2 Ti.1⟩)
      recs (d.restoreNested R ren n ns cname).allTypes.zipIdx := by
    refine Lean4Lean.List.forall₂_of_getElem? (by simp [hrecsLen, hdNTl]) fun i r₁ p hr₁ hp => ?_
    have hi : i < d.types.length := by
      have := (List.getElem?_eq_some_iff.1 hr₁).1; omega
    obtain ⟨T, r₀, r₁', hT, hr₁', hr₀f, e, hr₀, hr₀c⟩ := hrecs i hi
    rw [hr₁] at hr₁'; cases hr₁'
    rw [List.getElem?_zipIdx, VInductDecl.restoreNested_allTypes_getElem? H,
      VInductDecl.allTypes_of_aux H.flat, hT] at hp
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hp
    subst hp
    obtain ⟨T', r₁'', hT', hr₁'', hrT⟩ := rtF i hi
    rw [hT] at hT'; cases hT'
    rw [hr₁] at hr₁''; cases hr₁''
    have hname : r₀.name = d.recName i := hr₀.1
    subst e
    rw [← hname] at hrT ⊢
    have hrm := hrecMem i _ (hname ▸ hr₁)
    refine restoredRec (fuel := fuel) henv H hdN hn0 hns hTN hCN hRN hP (hS _ envR' hR'le fun l h => hlit l (VEnv.ContainsLits.mono hRle h)) hRR hSN
      (fun l h => VEnv.ContainsLits.mono ((hTle.trans hCle).trans hRNle)
        (hlit l (VEnv.ContainsLits.mono hRle h)))
      (fun l h => VEnv.ContainsLits.mono (VEnv.addConstList_le hR') h)
      hout hcn hnames hl hT (hra T (List.mem_of_getElem? hT)) ⟨hr₀, hr₀c⟩ hrT
      (hM i T r₀ hT hr₀f) (fun rule hrule => hcleanAll _ (hrm _ (.tail _ (List.mem_map.2
        ⟨_, List.mem_map.2 ⟨rule, hrule, rfl⟩, rfl⟩)))) (fun rule hrule hlet => ?_)
    have hmem := hrm _ (.tail _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨rule, hrule, rfl⟩, rfl⟩))
    have hany : (restoredTerms inds recs).any (·.anySubterm (·.isLet)) :=
      List.any_eq_true.2 ⟨_, hmem, hlet⟩
    obtain ⟨envCk, envRk, h1, h2, -, -, hck⟩ := hF.lets hany
    exact ⟨envRk, hVR envCk envRk h1 h2, hck _ (List.mem_of_getElem? (hname ▸ hr₁)) _
      (List.mem_map.2 ⟨rule, hrule, rfl⟩)⟩
  -- the block is recorded
  obtain ⟨venvF, hBN⟩ := VEnv.exists_addBlock (d := d.restoreNested R ren n ns cname)
    (env := envR.addDefEqList (d.restoreNested R ren n ns cname).iotaRules) fun T hT => by
      rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hRN, VEnv.addConstList_inducts hCN,
        VEnv.addConstList_inducts hTN]
      cases h : venv.inducts T.name with
      | none => rfl
      | some b =>
        obtain ⟨_, hc⟩ := henv.constants_of_inducts h
        rw [hfrK _ (List.mem_append_left _ (List.mem_append_left _
          (tyNames ▸ List.mem_map_of_mem hT)))] at hc
        cases hc
  refine ⟨venvF, .mk hl tyF ctF rcF ?_ hfrN ⟨cisN, hpN, heN⟩ hTN hCN hRN hBN⟩
  rw [hcsNames]; exact hndN

end

end Lean4Lean

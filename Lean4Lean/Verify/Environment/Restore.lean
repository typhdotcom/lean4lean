import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Nested

/-!
# Restoring a nested block's translation

`ElimNestedInductive.Result.restoreNested` replaces, in a term the flat check of a nested block's
translation produced, each auxiliary type or constructor applied to as many arguments as the block
has parameters by the occurrence it stands for. `VExpr.restore` is that replacement on the
translation. A translation of the term gives one of the restored term, and it is the restored
translation (`PTr.restore`), when the restored term mentions no auxiliary constant, which the
kernel checks, and the auxiliary constants' leading arguments in the translation mention none
either.

`PTr` is the translation `TrExprS` computes without its typing side conditions. Where the
restored term has no `let` its typing comes back from that of its translation
(`PTr.toTrExprS`), and where it has one the kernel checks it, and translations are unique
(`PTr.unique`).
-/

namespace Lean4Lean
open Lean

/-- The translation `TrExprS` computes, without its typing side conditions; `CL` says which
literals translate. -/
inductive PTr (Us : List Name) (CL : Literal → Prop) : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → PTr Us CL Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → PTr Us CL Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → PTr Us CL Δ (.sort u) (.sort u')
  | const : us.mapM (VLevel.ofLevel Us) = some us' → PTr Us CL Δ (.const c us) (.const c us')
  | app : PTr Us CL Δ f f' → PTr Us CL Δ a a' → PTr Us CL Δ (.app f a) (.app f' a')
  | lam : PTr Us CL Δ ty ty' → PTr Us CL ((none, .vlam ty') :: Δ) body body' →
    PTr Us CL Δ (.lam name ty body bi) (.lam ty' body')
  | forallE : PTr Us CL Δ ty ty' → PTr Us CL ((none, .vlam ty') :: Δ) body body' →
    PTr Us CL Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE : PTr Us CL Δ ty ty' → PTr Us CL Δ val val' →
    PTr Us CL ((none, .vlet ty' val') :: Δ) body body' →
    PTr Us CL Δ (.letE name ty val body nd) body'
  | lit : CL l → PTr Us CL Δ l.toConstructor e → PTr Us CL Δ (.lit l) e
  | mdata : PTr Us CL Δ e e' → PTr Us CL Δ (.mdata d e) e'
  | proj : PTr Us CL Δ e e' → PTr Us CL Δ (.proj s i e) (.proj s i e')

theorem TrExprS.toPTr {env : VEnv} (H : TrExprS env Us Δ e e') :
    PTr Us env.ContainsLits Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const _ h => exact .const h
  | app _ _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit h _ ih => exact .lit h ih
  | mdata _ ih => exact .mdata ih
  | proj _ _ ih => exact .proj ih

theorem PTr.mono_lit {CL CL' : Literal → Prop} (h : ∀ l, CL l → CL' l)
    (H : PTr Us CL Δ e e') : PTr Us CL' Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit hl _ ih => exact .lit (h _ hl) ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- A term has at most one translation in a context. -/
theorem PTr.unique {CL CL' : Literal → Prop} (H1 : PTr Us CL Δ e e₁) (H2 : PTr Us CL' Δ e e₂) :
    e₁ = e₂ := by
  induction H1 generalizing e₂ with cases H2
  | bvar h1 | fvar h1 => cases h1.symm.trans ‹_›; rfl
  | sort h1 => cases h1.symm.trans ‹_›; rfl
  | const h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ ih1 ih2 => cases ih1 ‹_›; cases ih2 ‹_›; rfl
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => cases ih1 ‹_›; cases ih2 ‹_›; rfl
  | letE _ _ _ ih1 ih2 ih3 => cases ih1 ‹_›; cases ih2 ‹_›; exact ih3 ‹_›
  | lit _ _ ih => exact ih ‹_›
  | mdata _ ih => exact ih ‹_›
  | proj _ ih => cases ih ‹_›; rfl

/-- `e` has no `let`. -/
def _root_.Lean.Expr.LetFree : Expr → Prop
  | .letE .. | .mvar _ => False
  | .app f a | .lam _ f a _ | .forallE _ f a _ => f.LetFree ∧ a.LetFree
  | .mdata _ e | .proj _ _ e => e.LetFree
  | .bvar _ | .fvar _ | .sort _ | .const .. | .lit _ => True

theorem _root_.Lean.Literal.toConstructor_letFree {l : Literal} : l.toConstructor.LetFree := by
  cases l with
  | natVal n => cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.LetFree,
      Expr.natZero, Expr.natSucc]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor, Expr.LetFree, true_and]
    induction s.toList <;> simp_all [Expr.LetFree]

/-- Where its translation is typed, a `let`-free term's plain translation is its translation. -/
theorem PTr.toTrExprS {env : VEnv} (henv : env.Ordered) {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, PTr Us env.ContainsLits Δ e e' → e.LetFree →
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
    exact .app hf' ha' (hf.toTrExprS henv hl.1 hΓ ⟨_, hf'⟩) (ha.toTrExprS henv hl.2 hΓ ⟨_, ha'⟩)
  | _, _, _, .lam hA hb, hl, hΓ, hwf => by
    obtain ⟨hA', hb'⟩ := hwf.lam_inv henv hΓ
    exact .lam hA' (hA.toTrExprS henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hb.toTrExprS henv hl.2 ⟨hΓ, hA'⟩ hb')
  | _, _, _, .forallE hA hB, hl, hΓ, ⟨_, hT⟩ => by
    obtain ⟨hA', hB'⟩ := VEnv.HasType.forallE_inv henv hT
    exact .forallE hA' hB' (hA.toTrExprS henv hl.1 hΓ (let ⟨_, h⟩ := hA'; ⟨_, h⟩))
      (hB.toTrExprS henv hl.2 ⟨hΓ, hA'⟩ (let ⟨_, h⟩ := hB'; ⟨_, h⟩))
  | _, _, _, .letE .., hl, _, _ => hl.elim
  | _, .lit l, _, .lit hc h, _, hΓ, hwf =>
    .lit hc (h.toTrExprS henv Literal.toConstructor_letFree hΓ hwf)
  | _, _, _, .mdata h, hl, hΓ, hwf => .mdata (h.toTrExprS henv hl hΓ hwf)
  | _, _, _, .proj h, hl, hΓ, hwf => by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hT, -⟩ := hwf.proj_inv henv hΓ
    exact .proj (h.toTrExprS henv hl hΓ ⟨_, hT⟩) hwf

/-! ### Weakening and instantiating plain translations -/

theorem PTr.weakBV (W : VLCtx.BVLift Δ Δ' dn dk n k) (H : PTr Us CL Δ e e') :
    PTr Us CL Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.cons _))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.cons _))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.cons _))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

/-- A context of `n` bound variables, as the parameters a nested occurrence is stated over. -/
def paramCtx (As : List VExpr) : VLCtx := As.map fun A => (none, .vlam A)

theorem paramCtx_find? : ∀ {As : List VExpr} {v : Nat ⊕ FVarId} {e A : VExpr},
    (paramCtx As).find? v = some (e, A) → ∃ j < As.length, v = .inl j ∧ e = .bvar j
  | [], _, _, _, h => by cases h
  | B :: As, v, e, A, h => by
    obtain (_ | j) | fv := v <;>
      simp [paramCtx, VLCtx.find?, VLCtx.next, VLocalDecl.value] at h
    · exact ⟨0, by simp, rfl, h.1.symm⟩
    · obtain ⟨e', A', h', rfl, rfl⟩ := h
      obtain ⟨j', hj', hv, rfl⟩ := paramCtx_find? h'
      cases hv
      exact ⟨j + 1, by simp; omega, rfl, by simp [VLocalDecl.depth, VExpr.liftN, liftVar]; omega⟩
    · obtain ⟨e', A', h', -⟩ := h
      obtain ⟨_, _, ⟨⟩, -⟩ := paramCtx_find? h'

theorem paramCtx_find?_lt : ∀ {As : List VExpr} {j : Nat}, j < As.length →
    ∃ A, (paramCtx As).find? (.inl j) = some (.bvar j, A)
  | B :: As, 0, _ => ⟨_, rfl⟩
  | B :: As, j + 1, h => by
    obtain ⟨A, hA⟩ := paramCtx_find?_lt (As := As) (j := j) (by simpa using h)
    exact ⟨A.liftN 1, by
      simp [paramCtx, VLCtx.find?, VLCtx.next] at hA ⊢
      exact ⟨_, _, hA, by simp [VLocalDecl.depth, VExpr.liftN, liftVar]; omega, rfl⟩⟩

def _root_.Lean4Lean.VLocalDecl.subst : VLocalDecl → VExpr.Subst → VLocalDecl
  | .vlam A, σ => .vlam (A.subst σ)
  | .vlet A e, σ => .vlet (A.subst σ) (e.subst σ)

@[simp] theorem _root_.Lean4Lean.VLocalDecl.depth_subst {d : VLocalDecl} {σ} :
    (d.subst σ).depth = d.depth := by cases d <;> rfl

theorem _root_.Lean4Lean.VExpr.liftN_subst_liftN {e : VExpr} {σ : VExpr.Subst} {n k : Nat} :
    (e.liftN n).subst (σ.liftN (k + n)) = (e.subst (σ.liftN k)).liftN n := by
  rw [← VExpr.lift'_consN_skipN, VExpr.subst_lift', ← VExpr.lift'_consN_skipN, VExpr.lift'_subst]
  congr 1; funext i
  simp only [VExpr.Subst.lift_l, VExpr.Subst.lift_r, Lift.liftVar_consN_skipN, liftVar,
    Nat.not_lt_zero, if_false, VExpr.lift'_consN_skipN, VExpr.Subst.liftN_apply]
  by_cases h : i < k
  · rw [if_pos (by omega), if_pos h]; simp [VExpr.liftN, liftVar]
  · rw [if_neg (by omega), if_neg h, VExpr.liftN_liftN, show n + i - (k + n) = i - k by omega,
      Nat.add_comm]

/-- Instantiating the `n` variables of a nested occurrence's context, below the binders a term
crossed since: the Expr side substitutes the arguments `L` from depth `dk`, the translation the
values `σ` from depth `k`. -/
inductive InstCtx (σ : VExpr.Subst) (Θ Δ : VLCtx) : Nat → Nat → VLCtx → VLCtx → Prop
  | base : InstCtx σ Θ Δ 0 0 Θ Δ
  | succ : InstCtx σ Θ Δ dk k Γ Γ' →
    InstCtx σ Θ Δ (dk + 1) (k + d.depth) ((none, d) :: Γ) ((none, d.subst (σ.liftN k)) :: Γ')

theorem InstCtx.find? {σ : VExpr.Subst} {As : List VExpr} {Δ : VLCtx}
    (W : InstCtx σ (paramCtx As) Δ dk k Γ Γ') (h : Γ.find? v = some (e, A)) :
    (∃ i < dk, v = .inl i ∧ ∃ A', Γ'.find? (.inl i) = some (e.subst (σ.liftN k), A')) ∨
    (∃ j < As.length, v = .inl (dk + j) ∧ e = .bvar (k + j)) := by
  induction W generalizing v e A with
  | base =>
    obtain ⟨j, hj, rfl, rfl⟩ := paramCtx_find? h
    exact .inr ⟨j, hj, by simp, by simp⟩
  | @succ dk k Γ Γ' d W ih =>
    obtain (_ | i) | fv := v
    · simp [VLCtx.find?, VLCtx.next] at h
      obtain ⟨rfl, rfl⟩ := h
      refine .inl ⟨0, by omega, rfl, (d.subst (σ.liftN k)).type, ?_⟩
      cases d <;> simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.subst,
        VLocalDecl.depth, VExpr.Subst.liftN, VExpr.Subst.lift]
    · simp [VLCtx.find?, VLCtx.next] at h
      obtain ⟨e₀, A₀, h, rfl, rfl⟩ := h
      rcases ih h with ⟨i', hi, ⟨⟩, A', h'⟩ | ⟨j, hj, ⟨⟩, rfl⟩
      · refine .inl ⟨i + 1, by omega, rfl, A'.liftN d.depth, ?_⟩
        simp [VLCtx.find?, VLCtx.next, h', VExpr.liftN_subst_liftN]
      · refine .inr ⟨j, hj, by simp; omega, ?_⟩
        simp [VExpr.liftN, liftVar]; omega
    · simp [VLCtx.find?, VLCtx.next] at h
      obtain ⟨e₀, A₀, h, -⟩ := h
      rcases ih h with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> cases h

theorem InstCtx.bvLift {σ : VExpr.Subst} (W : InstCtx σ Θ Δ dk k Γ Γ') :
    VLCtx.BVLift Δ Γ' dk 0 k 0 := by
  induction W with
  | base => exact .refl
  | @succ _ _ _ _ d _ ih => simpa using ih.skip (d.subst _)

theorem forall₂_getElem?_rev {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ j, j < l₁.length →
      ∃ x y, l₁.reverse[j]? = some x ∧ l₂.reverse[j]? = some y ∧ R x y
  | _ :: l₁, _ :: l₂, .cons h t, j, hj => by
    simp only [List.reverse_cons]
    by_cases hj' : j < l₁.length
    · obtain ⟨x, y, h1, h2, h3⟩ := forall₂_getElem?_rev t j hj'
      exact ⟨x, y, by rw [List.getElem?_append_left (by simpa using hj'), h1],
        by rw [List.getElem?_append_left (by rw [List.length_reverse,
          ← Lean4Lean.List.Forall₂.length_eq t]; exact hj'), h2], h3⟩
    · have e1 : j = l₁.length := by simp at hj; omega
      refine ⟨_, _, ?_, ?_, h⟩
      · rw [List.getElem?_append_right (by simp; omega)]; simp [e1]
      · rw [List.getElem?_append_right (by simp [← Lean4Lean.List.Forall₂.length_eq t]; omega)]
        simp [e1, Lean4Lean.List.Forall₂.length_eq t]

/-- Instantiating a nested occurrence's parameters by arguments, below binders. -/
theorem PTr.inst' {As : List VExpr} {args : List Expr} {ys : List VExpr}
    (hys : List.Forall₂ (PTr Us CL Δ) args ys) (hlen : As.length = ys.length)
    (W : InstCtx (VExpr.Subst.dflt.consList ys) (paramCtx As) Δ dk k Γ Γ')
    (H : PTr Us CL Γ M b) :
    PTr Us CL Γ' (M.instantiate' args.reverse dk)
      (b.subst ((VExpr.Subst.dflt.consList ys).liftN k)) := by
  have hal : args.length = ys.length := Lean4Lean.List.Forall₂.length_eq hys
  induction H generalizing dk k Γ' with
  | @bvar Γ i e A h =>
    rcases W.find? h with ⟨i', hi, ⟨⟩, A', h'⟩ | ⟨j, hj, ⟨⟩, rfl⟩
    · simp only [Expr.instantiate', if_pos hi]; exact .bvar h'
    · simp only [Expr.instantiate', show ¬dk + j < dk by omega, if_false,
        show dk + j - dk = j by omega]
      have hj' : j < args.reverse.length := by simp; omega
      rw [dif_pos hj']
      rw [VExpr.subst, VExpr.Subst.liftN_apply, if_neg (by omega),
        show k + j - k = j by omega, VExpr.Subst.consList_apply, dif_pos (by omega)]
      obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, args.reverse[j]? = some x ∧ ys.reverse[j]? = some y ∧
          PTr Us CL Δ x y := forall₂_getElem?_rev hys j (by omega)
      rw [List.getElem?_eq_some_iff] at hx hy
      obtain ⟨_, rfl⟩ := hx; obtain ⟨_, rfl⟩ := hy
      exact hxy.weakBV W.bvLift
  | fvar h =>
    rcases W.find? h with ⟨_, _, h, -⟩ | ⟨_, _, h, -⟩ <;> cases h
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 =>
    exact .lam (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE _ _ ih1 ih2 =>
    exact .forallE (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE _ _ _ ih1 ih2 ih3 =>
    exact .letE (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet _ _)))
  | lit h1 _ ih =>
    refine .lit h1 (Expr.instantiate'_eq_self ?_ ▸ ih W :)
    exact Nat.le_trans Closed.toConstructor.looseBVarRange_le (Nat.zero_le _)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

/-! ### Instantiating level parameters without simplifying -/

theorem forall₂_getElem {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length)
      (h₂ : i < l₂.length), R l₁[i] l₂[i]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ t, i + 1, h₁, h₂ =>
    forall₂_getElem t i (by simpa using h₁) (by simpa using h₂)

theorem lookup_zip_idxOf : ∀ {ps : List Name} {ls : List Level} {p : Name},
    ps.idxOf p < ps.length → ls.length = ps.length →
    ∃ h : ps.idxOf p < ls.length, List.lookup p (ps.zip ls) = some ls[ps.idxOf p]
  | [], _, _, h, _ => by simp at h
  | q :: ps, [], _, _, hl => by simp at hl
  | q :: ps, l :: ls, p, h, hl => by
    by_cases hq : p = q
    · subst hq; simp
    · have hq' : (q == p) = false := by simpa using Ne.symm hq
      have hq'' : (p == q) = false := by simpa using hq
      simp only [List.idxOf_cons, hq', cond_false, List.length_cons] at h ⊢
      obtain ⟨h1, h2⟩ := lookup_zip_idxOf (ps := ps) (ls := ls) (p := p) (by omega)
        (by simpa using hl)
      refine ⟨by simp; omega, ?_⟩
      simp only [List.zip_cons_cons, List.lookup, hq'', h2]
      simp

theorem ofLevel_substLevelParams {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (hls : ls.mapM (VLevel.ofLevel Us) = some ls') (hlen : ls.length = ps.length) :
    ∀ {L : Level} {l : VLevel}, VLevel.ofLevel ps L = some l →
      VLevel.ofLevel Us (ElimNestedInductive.Result.substLevelParams
        (fun n => List.lookup n (ps.zip ls)) L) = some (l.inst ls')
  | .zero, _, h => by cases h; rfl
  | .succ L, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨l, h, rfl⟩ := h
    simp [ElimNestedInductive.Result.substLevelParams, VLevel.ofLevel,
      ofLevel_substLevelParams hls hlen h, VLevel.inst]
  | .max L₁ L₂, _, h | .imax L₁ L₂, _, h => by
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := h
    simp [ElimNestedInductive.Result.substLevelParams, VLevel.ofLevel,
      ofLevel_substLevelParams hls hlen h₁, ofLevel_substLevelParams hls hlen h₂, VLevel.inst]
  | .param p, _, h => by
    simp only [VLevel.ofLevel] at h
    split at h <;> cases h
    rename_i hp
    obtain ⟨h1, h2⟩ := lookup_zip_idxOf hp hlen
    simp only [ElimNestedInductive.Result.substLevelParams, h2, Option.getD_some, VLevel.inst]
    have hF := List.mapM_eq_some.1 hls
    have hl' : ps.idxOf p < ls'.length := by
      rw [← Lean4Lean.List.Forall₂.length_eq hF]; exact h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some]
    exact forall₂_getElem hF _ h1 hl'
  | .mvar _, _, h => by cases h

section
open ElimNestedInductive.Result

/-- `instantiateLevelParamsRaw`'s replacement at a node. -/
def rawFn (ps : List Name) (ls : List Level) : Expr → Option Expr
  | .const c us => some (.const c (us.map (substLevelParams fun n => List.lookup n (ps.zip ls))))
  | .sort u => some (.sort (substLevelParams (fun n => List.lookup n (ps.zip ls)) u))
  | _ => none

theorem instantiateLevelParamsRaw_eq {e : Expr} {ps : List Name} {ls : List Level} :
    instantiateLevelParamsRaw e ps ls = e.replaceNoCache (rawFn ps ls) := by
  simp only [instantiateLevelParamsRaw, Expr.replace_eq]; congr 1

theorem rawFn_toConstructor {ps : List Name} {ls : List Level} {l : Literal} :
    l.toConstructor.replaceNoCache (rawFn ps ls) = l.toConstructor := by
  cases l with
  | natVal n =>
    cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero,
      Expr.natSucc, Expr.replaceNoCache, rawFn]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor]
    simp [Expr.replaceNoCache, rawFn, substLevelParams]
    induction s.toList <;> simp_all [Expr.replaceNoCache, rawFn, substLevelParams]

/-- Instantiating level parameters keeps a plain translation, at the instantiated levels. -/
theorem PTr.instantiateLevelParamsRaw {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (hls : ls.mapM (VLevel.ofLevel Us) = some ls') (hlen : ls.length = ps.length)
    (H : PTr ps CL Δ e e') :
    PTr Us CL (Δ.instL ls') (ElimNestedInductive.Result.instantiateLevelParamsRaw e ps ls)
      (e'.instL ls') := by
  rw [instantiateLevelParamsRaw_eq]
  induction H with
  | bvar h => exact .bvar (VLCtx.find?_instL h)
  | fvar h => exact .fvar (VLCtx.find?_instL h)
  | sort h =>
    simp only [Expr.replaceNoCache, rawFn, VExpr.instL]
    exact .sort (ofLevel_substLevelParams hls hlen h)
  | const h =>
    simp only [Expr.replaceNoCache, rawFn, VExpr.instL]
    refine .const (List.mapM_eq_some.2 ?_)
    have := List.mapM_eq_some.1 h
    simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ofLevel_substLevelParams hls hlen h) this
  | app _ _ ih1 ih2 => simpa [Expr.replaceNoCache, rawFn, VExpr.instL] using PTr.app ih1 ih2
  | lam _ _ ih1 ih2 =>
    simpa [Expr.replaceNoCache, rawFn, VExpr.instL, VLCtx.instL, VLocalDecl.instL] using PTr.lam ih1 ih2
  | forallE _ _ ih1 ih2 =>
    simpa [Expr.replaceNoCache, rawFn, VExpr.instL, VLCtx.instL, VLocalDecl.instL] using PTr.forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 =>
    simpa [Expr.replaceNoCache, rawFn, VExpr.instL, VLCtx.instL, VLocalDecl.instL] using PTr.letE ih1 ih2 ih3
  | lit h _ ih =>
    simp only [Expr.replaceNoCache, rawFn]
    exact .lit h (rawFn_toConstructor ▸ ih)
  | mdata _ ih => simpa [Expr.replaceNoCache, rawFn] using PTr.mdata ih
  | proj _ ih => simpa [Expr.replaceNoCache, rawFn, VExpr.instL] using PTr.proj ih

end

theorem paramCtx_instL {As : List VExpr} {ls : List VLevel} :
    (paramCtx As).instL ls = paramCtx (As.map (·.instL ls)) := by
  induction As <;> simp_all [paramCtx, VLCtx.instL, VLocalDecl.instL]

/-- The kernel's replacement: a nested occurrence, stated over the parameters, at the auxiliary
constant's levels and arguments. -/
theorem PTr.instNested {N : Expr} {a : VExpr} {As : List VExpr} {Us ps : List Name}
    {ls : List Level} {ls' : List VLevel} {args : Array Expr} {ys : List VExpr}
    (hN : PTr ps CL (paramCtx As) N a) (hls : ls.mapM (VLevel.ofLevel Us) = some ls')
    (hlen : ls.length = ps.length) (hys : List.Forall₂ (PTr Us CL Δ) args.toList ys)
    (hAy : As.length = ys.length) :
    PTr Us CL Δ ((ElimNestedInductive.Result.instantiateLevelParamsRaw N ps ls).instantiateRev args)
      ((a.instL ls').subst (VExpr.Subst.dflt.consList ys)) := by
  have h1 := hN.instantiateLevelParamsRaw hls hlen
  rw [paramCtx_instL] at h1
  rw [Expr.instantiateRev_eq_instantiate']
  exact PTr.inst' hys (by simpa using hAy) .base h1

/-! ### The kernel's replacement -/

namespace ElimNestedInductive.Result

variable (r : Result) (env' : Kernel.Environment) (lparams : List Name) (auxRec : NameMap Name)

/-- The replacement `restoreNested` makes for an auxiliary constant `c` at levels `ls` applied
to `args`. -/
def kRepl (c : Name) (ls : List Level) (args : Array Expr) : Option Expr :=
  let inst (nested : Expr) :=
    (instantiateLevelParamsRaw (nested.abstract r.params) lparams ls).instantiateRev args
  match r.aux2nested.find? c with
  | some nested => some (inst nested)
  | none => do
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let .const I_c I_ls := (inst nested).getAppFn | none
    return mkAppN (.const (c.replacePrefix auxI_name I_c) I_ls) (inst nested).getAppArgs

/-- `restoreNested`'s replacement at a node, other than renaming a recursor. -/
def auxFn (t : Expr) : Option Expr :=
  (constSpine? t).bind fun x =>
    if x.2.2.size = r.nparams ∧ (r.aux2nested.contains x.1 || (r.getNestedIfAuxCtor env' x.1).isSome) = true
    then kRepl r env' lparams x.1 x.2.1 x.2.2 else none

/-- `restoreNested`'s replacement at a node. -/
def restoreFn (t : Expr) : Option Expr :=
  match t with
  | .const c ls => match auxRec.find? c with
    | some c' => some (.const c' ls)
    | none => auxFn r env' lparams t
  | _ => auxFn r env' lparams t

theorem spineHead?_eq : ∀ {t : Expr},
    spineHead? t = (constSpine? t).map fun x => (x.1, x.2.2.size)
  | .const .. => rfl
  | .app f _ => by
    simp only [spineHead?, constSpine?, spineHead?_eq (t := f), Option.map_map]
    congr 1; funext x; simp
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. | .mdata .. => rfl

/-- The kernel's replacement after the renaming test. -/
theorem rest_eq (t : Expr) : (do
    let (c, n) ← spineHead? t
    if n != r.nparams || !(r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) then
      none
    let (_, ls, args) ← constSpine? t
    let inst (nested : Expr) :=
      (instantiateLevelParamsRaw (nested.abstract r.params) lparams ls).instantiateRev args
    if let some nested := r.aux2nested.find? c then
      return inst nested
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let .const I_c I_ls := (inst nested).getAppFn | none
    return mkAppN (.const (c.replacePrefix auxI_name I_c) I_ls) (inst nested).getAppArgs : Option Expr) =
    auxFn r env' lparams t := by
  rw [spineHead?_eq]
  unfold auxFn
  cases h : constSpine? t with
  | none => rfl
  | some x =>
    obtain ⟨c, ls, args⟩ := x
    simp only [Option.map_some, Option.bind_some]
    by_cases h1 : args.size = r.nparams
    · by_cases h2 : (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true
      · have h2' : ¬(r.aux2nested.contains c = false ∧ r.getNestedIfAuxCtor env' c = none) := by
          simp only [Bool.or_eq_true] at h2
          rintro ⟨h3, h4⟩; rcases h2 with h2 | h2
          · simp [h3] at h2
          · simp [h4] at h2
        have h2n : r.aux2nested.contains c = true ∨ (r.getNestedIfAuxCtor env' c).isSome = true := by
          simpa using h2
        simp [h1, h2', h2n, kRepl]
        cases r.aux2nested.find? c <;> rfl
      · have : r.aux2nested.contains c = false ∧ r.getNestedIfAuxCtor env' c = none := by
          simp at h2; exact ⟨h2.1, h2.2⟩
        simp [h1, this]
    · simp [h1]

theorem restoreNested_eq (e : Expr) :
    r.restoreNested env' lparams e auxRec = e.replaceNoCache (restoreFn r env' lparams auxRec) := by
  unfold restoreNested; rw [Expr.replace_eq]
  congr 1; funext t
  simp only [restoreFn]
  split
  · rename_i c ls
    cases h : auxRec.find? c with
    | some c' => simp [h]
    | none =>
      simp only [h]
      rw [← rest_eq]; rfl
  · rename_i ht
    split
    · rename_i c ls; exact absurd rfl (ht c ls)
    · rw [← rest_eq]; rfl

end ElimNestedInductive.Result

/-! ### Conditions on the translation -/

namespace VExpr
variable (R : Name → Option VAuxHead) (ren : Name → Option Name)

/-- `e` mentions no auxiliary constant and no recursor to rename. -/
abbrev AuxFree (e : VExpr) : Prop := e.ConstsSat fun c => R c = none ∧ ren c = none

/-- The auxiliary constant at the head of `e`, if any, has its leading arguments. -/
def NoPartial (e : VExpr) : Prop :=
  ∀ c ls xs h, e.constSpine? = some (c, ls, xs) → R c = some h → h.n ≤ xs.length

/-- Wherever `restore` replaces an auxiliary constant, its leading arguments, which the
replacement keeps as they are, mention no auxiliary constant. -/
def LeadFree : VExpr → Prop
  | .app f a => match restoreAux R (.app f a) with
    | some _ => ∀ c ls xs, (VExpr.app f a).constSpine? = some (c, ls, xs) → ∀ x ∈ xs,
      x.ConstsSat fun c => R c = none ∧ ren c = none
    | none => LeadFree f ∧ LeadFree a
  | .lam A b | .forallE A b => LeadFree A ∧ LeadFree b
  | .proj _ _ e => LeadFree e
  | .bvar _ | .sort _ | .const .. => True

variable {R ren}

/-- Auxiliary constants at the parameters leave the leading arguments of every replaced
application free of them: what the translation of a processed constructor satisfies
(`TrExprS.auxAt`) gives what the restoration needs. -/
theorem _root_.Lean4Lean.VExpr.AuxAt.leadFree {ls₀ : List VLevel} {e : VExpr} :
    ∀ {k}, e.AuxAt R ls₀ k → e.LeadFree R ren := by
  induction e with
  | bvar | sort | const => intros; trivial
  | lam A b ihA ihb | forallE A b ihA ihb => exact fun H => ⟨ihA H.1, ihb H.2⟩
  | proj _ _ e ih => exact fun H => ih H
  | app f a ihf iha =>
    intro k H
    unfold VExpr.AuxAt at H
    unfold LeadFree
    have hfa : f.AuxAt R ls₀ k ∧ a.AuxAt R ls₀ k → f.LeadFree R ren ∧ a.LeadFree R ren :=
      fun h => ⟨ihf h.1, iha h.2⟩
    cases hs : (VExpr.app f a).constSpine? with
    | none =>
      have : restoreAux R (.app f a) = none := by simp [restoreAux, hs]
      rw [hs] at H; rw [this]; exact hfa H
    | some x =>
      obtain ⟨c, ls, xs⟩ := x
      rw [hs] at H
      cases hR : R c with
      | none =>
        have : restoreAux R (.app f a) = none := by simp [restoreAux, hs, hR]
        simp only [hR] at H; rw [this]; exact hfa H
      | some h =>
        simp only [hR] at H
        by_cases hl : xs.length = h.n
        · have : restoreAux R (.app f a) = some (h.inst ls xs) := by
            simp [restoreAux, hs, hR, hl]
          rw [if_pos hl] at H; rw [this]
          intro c' ls' xs' hs' x hx
          simp only [Option.some.injEq, Prod.mk.injEq] at hs'
          obtain ⟨-, -, rfl⟩ := hs'
          rw [H.1] at hx
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
          trivial
        · have : restoreAux R (.app f a) = none := by simp [restoreAux, hs, hR, hl]
          rw [if_neg hl] at H; rw [this]; exact hfa H

theorem constSpine?_liftN : ∀ {e : VExpr} {n k : Nat},
    (e.liftN n k).constSpine? = e.constSpine?.map fun x => (x.1, x.2.1, x.2.2.map (·.liftN n k))
  | .const .., _, _ => rfl
  | .app f a, n, k => by
    simp only [VExpr.liftN, constSpine?, constSpine?_liftN (e := f), Option.map_map]
    congr 1; funext x; simp
  | .bvar _, _, _ | .sort _, _, _ | .lam .., _, _ | .forallE .., _, _ | .proj .., _, _ => rfl

theorem ConstsSat.of_liftN {p : Name → Prop} :
    ∀ {e : VExpr} {n k : Nat}, (e.liftN n k).ConstsSat p → e.ConstsSat p
  | .bvar _, _, _, _ | .sort _, _, _, _ => trivial
  | .const _ _, _, _, H => H
  | .app .., _, _, H | .lam .., _, _, H | .forallE .., _, _, H => ⟨H.1.of_liftN, H.2.of_liftN⟩
  | .proj _ _ e, _, _, H => ConstsSat.of_liftN (e := e) H

theorem NoPartial.liftN {e : VExpr} (H : e.NoPartial R) : (e.liftN n k).NoPartial R := by
  intro c ls xs h he hR
  rw [constSpine?_liftN] at he
  obtain ⟨⟨c', ls', xs'⟩, he', hx⟩ := Option.map_eq_some_iff.1 he
  cases hx
  simpa using H _ _ _ _ he' hR

theorem restoreAux_liftN {e : VExpr} :
    restoreAux R (e.liftN n k) = (restoreAux R e).map (·.liftN n k) := by
  rw [liftN_eq_subst, restoreAux_subst (σ := Subst.ofLift _) (fun _ => show (VExpr.bvar _).ConstsSat _ from trivial)]
  cases restoreAux R e <;> simp [liftN_eq_subst]

theorem LeadFree.of_liftN : ∀ {e : VExpr} {n k : Nat}, (e.liftN n k).LeadFree R ren → e.LeadFree R ren
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _ => trivial
  | .app f a, n, k, H => by
    unfold LeadFree at H ⊢
    have := restoreAux_liftN (R := R) (e := .app f a) (n := n) (k := k)
    simp only [VExpr.liftN] at this H
    rw [this] at H
    cases h : restoreAux R (.app f a) with
    | some _ =>
      rw [h] at H
      intro c ls xs hs x hx
      have hs' := constSpine?_liftN (e := .app f a) (n := n) (k := k)
      rw [hs] at hs'
      simp only [VExpr.liftN, Option.map_some] at hs'
      exact (H c ls (xs.map (·.liftN n k)) hs' _ (List.mem_map_of_mem hx)).of_liftN
    | none => rw [h] at H; exact ⟨H.1.of_liftN, H.2.of_liftN⟩
  | .lam .., _, _, H | .forallE .., _, _, H => ⟨H.1.of_liftN, H.2.of_liftN⟩
  | .proj _ _ e, _, _, H => LeadFree.of_liftN (e := e) H

theorem AuxFree.leadFree : ∀ {e : VExpr}, e.AuxFree R ren → e.LeadFree R ren
  | .bvar _, _ | .sort _, _ | .const .., _ => trivial
  | .app f a, H => by
    unfold LeadFree
    rw [restoreAux_eq_none (e := .app f a) (H.mono fun _ h => h.1)]
    exact ⟨AuxFree.leadFree H.1, AuxFree.leadFree H.2⟩
  | .lam .., H | .forallE .., H => ⟨AuxFree.leadFree H.1, AuxFree.leadFree H.2⟩
  | .proj _ _ e, H => AuxFree.leadFree (e := e) H

end VExpr

/-! ### Constants and spines of plain translations -/

/-- Every constant `e` mentions satisfies `p`, at its levels; literals count as mentioning none. -/
def _root_.Lean.Expr.ConstsOK (p : Name → List Level → Prop) : Expr → Prop
  | .const c ls => p c ls
  | .app f a | .lam _ f a _ | .forallE _ f a _ => f.ConstsOK p ∧ a.ConstsOK p
  | .letE _ t v b _ => t.ConstsOK p ∧ v.ConstsOK p ∧ b.ConstsOK p
  | .mdata _ e | .proj _ _ e => e.ConstsOK p
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True

/-- The constants a literal stands for. -/
def _root_.Lean.Literal.constNames : Literal → List Name
  | .natVal _ => [``Nat.zero, ``Nat.succ]
  | .strVal _ => [``Char, ``List.nil, ``List.cons, ``String.ofList, ``Char.ofNat]

/-- Built from constants, sorts and literals by applications, without variables or binders. -/
def _root_.Lean.Expr.Ground : Expr → Prop
  | .app f a => f.Ground ∧ a.Ground
  | .mdata _ e | .proj _ _ e => e.Ground
  | .const .. | .sort _ | .lit _ => True
  | _ => False

theorem _root_.Lean.Literal.toConstructor_ground {l : Literal} : l.toConstructor.Ground := by
  cases l with
  | natVal n => cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.Ground,
      Expr.natZero, Expr.natSucc]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor, Expr.Ground, true_and]
    induction s.toList <;> simp_all [Expr.Ground]

theorem _root_.Lean.Literal.toConstructor_constsOK {p : Name → List Level → Prop}
    {l : Literal} (h : ∀ c ∈ l.constNames, ∀ ls, p c ls) : l.toConstructor.ConstsOK p := by
  cases l with
  | natVal n =>
    have h' := fun c (hc : c ∈ (Literal.natVal n).constNames) => h c hc
    cases n <;> simp_all [Literal.toConstructor, Expr.natLitToConstructor,
      Expr.ConstsOK, Expr.natZero, Expr.natSucc, Literal.constNames]
  | strVal s =>
    have h' := fun c (hc : c ∈ (Literal.strVal s).constNames) => h c hc
    simp only [Literal.toConstructor, Expr.strLitToConstructor, Expr.ConstsOK]
    refine ⟨h _ (by simp [Literal.constNames]) _, ?_⟩
    induction s.toList <;> simp_all [Expr.ConstsOK, Literal.constNames]

/-- A ground term translates the same way in every context. -/
theorem PTr.ground (H : PTr Us CL Δ e e') (he : e.Ground) : PTr Us CL Δ' e e' := by
  induction H generalizing Δ' with
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 he.1) (ih2 he.2)
  | lit h _ ih => exact .lit h (ih Literal.toConstructor_ground)
  | mdata _ ih => exact .mdata (ih he)
  | proj _ ih => exact .proj (ih he)
  | bvar | fvar | lam | forallE | letE => exact he.elim

theorem PTr.ground_constsSat {p : Name → Prop} (H : PTr Us CL Δ e e') (he : e.Ground)
    (hc : e.ConstsOK fun c _ => p c) (hl : ∀ l, CL l → ∀ c ∈ l.constNames, p c) :
    e'.ConstsSat p := by
  induction H with
  | sort => trivial
  | const => exact hc
  | app _ _ ih1 ih2 => exact ⟨ih1 he.1 hc.1, ih2 he.2 hc.2⟩
  | lit hl' _ ih =>
    exact ih Literal.toConstructor_ground
      (Literal.toConstructor_constsOK (p := fun c _ => p c) fun c h _ => hl _ hl' c h)
  | mdata _ ih => exact ih he hc
  | proj _ ih => exact ih he hc
  | bvar | fvar | lam | forallE | letE => exact he.elim

/-- An application spine the kernel sees translates to one with the same head and as many
arguments. -/
theorem PTr.constSpine? (H : PTr Us CL Δ t t')
    (h : ElimNestedInductive.Result.constSpine? t = some (c, ls, args)) :
    ∃ ls' xs', ls.mapM (VLevel.ofLevel Us) = some ls' ∧ t'.constSpine? = some (c, ls', xs') ∧
      List.Forall₂ (PTr Us CL Δ) args.toList xs' := by
  induction H generalizing c ls args with
  | const h' =>
    simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, [], h', rfl, .nil⟩
  | app _ ha ih _ =>
    simp only [ElimNestedInductive.Result.constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c₁, ls₁, args₁⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
    obtain ⟨ls', xs', h3, h4, h5⟩ := ih h1
    refine ⟨ls', xs' ++ [_], h3, by simp [VExpr.constSpine?, h4]; rfl, ?_⟩
    simpa using forall₂_append h5 (.cons ha .nil)
  | bvar | fvar | sort | lam | forallE | letE | lit | proj | mdata =>
    simp [ElimNestedInductive.Result.constSpine?] at h

/-! ### The restoration and its translation -/

section
variable {F : Expr → Option Expr}

theorem _root_.Lean.Expr.replaceNoCache_app (h : F (.app f a) = none) :
    (Expr.app f a).replaceNoCache F = .app (f.replaceNoCache F) (a.replaceNoCache F) := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

theorem _root_.Lean.Expr.replaceNoCache_mdata (h : F (.mdata d e) = none) :
    (Expr.mdata d e).replaceNoCache F = .mdata d (e.replaceNoCache F) := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

theorem _root_.Lean.Expr.replaceNoCache_lam (h : F (.lam n t b bi) = none) :
    (Expr.lam n t b bi).replaceNoCache F = .lam n (t.replaceNoCache F) (b.replaceNoCache F) bi := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

theorem _root_.Lean.Expr.replaceNoCache_forallE (h : F (.forallE n t b bi) = none) :
    (Expr.forallE n t b bi).replaceNoCache F =
      .forallE n (t.replaceNoCache F) (b.replaceNoCache F) bi := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

theorem _root_.Lean.Expr.replaceNoCache_letE (h : F (.letE n t v b nd) = none) :
    (Expr.letE n t v b nd).replaceNoCache F =
      .letE n (t.replaceNoCache F) (v.replaceNoCache F) (b.replaceNoCache F) nd := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

theorem _root_.Lean.Expr.replaceNoCache_proj (h : F (.proj s i e) = none) :
    (Expr.proj s i e).replaceNoCache F = .proj s i (e.replaceNoCache F) := by
  rw [Expr.replaceNoCache.eq_def, h]; simp

end

/-- What relates the kernel's restoration data to `VExpr.restore`'s: the auxiliary constants and
the recursors to rename are the same, and each auxiliary constant's replacement translates to the
occurrence `R` gives, at the constant's levels and arguments. `RestoreSpec.of_nested` gives
`repl` from the translations of the nested occurrences the kernel recorded. -/
structure RestoreSpec (r : ElimNestedInductive.Result) (env' : Kernel.Environment)
    (lparams : List Name) (auxRec : NameMap Name) (Us : List Name) (CL : Literal → Prop)
    (R : Name → Option VAuxHead) (ren : Name → Option Name) : Prop where
  ren_eq : ∀ c, ren c = auxRec.find? c
  aux : ∀ c, (R c).isSome = (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome)
  ren_aux : ∀ c, (R c).isSome → auxRec.find? c = none
  n_eq : ∀ c h, R c = some h → h.n = r.nparams
  lit : ∀ l, CL l → ∀ c ∈ l.constNames, R c = none ∧ auxRec.find? c = none
  repl : ∀ c h (ls : List Level) ls' (args : Array Expr) Δ ys, R c = some h →
    ls.mapM (VLevel.ofLevel Us) = some ls' → ls.length = lparams.length →
    args.size = r.nparams → List.Forall₂ (PTr Us CL Δ) args.toList ys →
    ∃ out, r.kRepl env' lparams c ls args = some out ∧ PTr Us CL Δ out (h.inst ls' ys)

section
variable {r : ElimNestedInductive.Result} {env' : Kernel.Environment} {lparams : List Name}
  {auxRec : NameMap Name} {Us : List Name} {CL : Literal → Prop}
  {R : Name → Option VAuxHead} {ren : Name → Option Name}

local notation "ρ" => Expr.replaceNoCache (ElimNestedInductive.Result.restoreFn r env' lparams auxRec)

/-- The context's values are not partial auxiliary applications. -/
def CtxNP (R : Name → Option VAuxHead) (Δ : VLCtx) : Prop :=
  ∀ v x A, Δ.find? v = some (x, A) → x.NoPartial R

theorem CtxNP.cons {Δ : VLCtx} {d : VLocalDecl} (hΔ : CtxNP R Δ) (hd : d.value.NoPartial R) :
    CtxNP R ((none, d) :: Δ) := by
  rintro ((_ | i) | fv) x A h <;> simp [VLCtx.find?, VLCtx.next] at h
  · obtain ⟨rfl, -⟩ := h; exact hd
  · obtain ⟨x, A, h, rfl, -⟩ := h; exact (hΔ _ _ _ h).liftN
  · obtain ⟨x, A, h, rfl, -⟩ := h; exact (hΔ _ _ _ h).liftN

theorem noPartial_bvar : (VExpr.bvar i).NoPartial R := by
  intro _ _ _ _ h; cases h

theorem restoreFn_of_spine_none {t : Expr} (ht : ∀ c ls, t ≠ .const c ls)
    (h : ElimNestedInductive.Result.constSpine? t = none) :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec t = none := by
  unfold ElimNestedInductive.Result.restoreFn ElimNestedInductive.Result.auxFn
  split
  · exact absurd rfl (ht _ _)
  · simp [h]

theorem restoreFn_of_not_const {t : Expr} (ht : ∀ c ls, t ≠ .const c ls) :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec t =
      ElimNestedInductive.Result.auxFn r env' lparams t := by
  unfold ElimNestedInductive.Result.restoreFn
  split
  · exact absurd rfl (ht _ _)
  · rfl

@[simp] theorem restoreFn_letE :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.letE n t v b nd) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_lam :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.lam n t b bi) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_forallE :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.forallE n t b bi) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_bvar :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.bvar i) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_fvar :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.fvar fv) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_sort :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.sort u) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_lit :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.lit l) = none :=
  restoreFn_of_spine_none nofun rfl
@[simp] theorem restoreFn_proj :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.proj s i e) = none :=
  restoreFn_of_spine_none nofun rfl

/-- What the kernel restores is aux-free only if no translated head is a partial auxiliary
application. -/
theorem PTr.noPartial (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    (H : PTr Us CL Δ f f') (hΔ : CtxNP R Δ)
    (hc : (ρ f).ConstsOK fun c _ => R c = none ∧ auxRec.find? c = none) : f'.NoPartial R := by
  induction H with
  | bvar h | fvar h => exact hΔ _ _ _ h
  | sort | lam | forallE | proj => intro _ _ _ _ h; cases h
  | lit hl H _ =>
    have := H.ground_constsSat (p := (R · = none)) Literal.toConstructor_ground
      (Literal.toConstructor_constsOK (p := fun c _ => R c = none) fun c h _ => (S.lit _ hl c h).1)
      fun l hl c h => (S.lit l hl c h).1
    intro c ls xs h' he hR
    rw [VExpr.eq_of_constSpine? he, VExpr.ConstsSat.appN] at this
    rw [this.1] at hR; cases hR
  | @const us' _ c us h =>
    intro c' ls xs hh he hR
    cases he
    by_contra hn
    have hz : hh.n ≠ 0 := by simp at hn; omega
    have hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.const c us) = none := by
      unfold ElimNestedInductive.Result.restoreFn ElimNestedInductive.Result.auxFn
      simp [S.ren_aux c (by simp [hR]), ElimNestedInductive.Result.constSpine?,
        ← S.n_eq c hh hR, Ne.symm hz]
    simp [Expr.replaceNoCache, hfn, Expr.ConstsOK, hR] at hc
  | @app _ g g' a a' Hg Ha ihg _ =>
    intro c ls xs hh he hR
    have hne : ∀ c ls, Expr.app g a ≠ .const c ls := nofun
    have descend (hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.app g a) = none) :
        hh.n ≤ xs.length := by
      simp only [Expr.replaceNoCache, hfn, Expr.updateApp!, Expr.ConstsOK] at hc
      simp only [VExpr.constSpine?, Option.map_eq_some_iff] at he
      obtain ⟨⟨c₁, ls₁, xs₁⟩, he₁, he₂⟩ := he
      simp only [Prod.mk.injEq] at he₂; obtain ⟨rfl, rfl, rfl⟩ := he₂
      have := ihg hΔ hc.1 _ _ _ _ he₁ hR
      simp; omega
    cases hs : ElimNestedInductive.Result.constSpine? (.app g a) with
    | some x =>
      obtain ⟨c₀, ls₀, args₀⟩ := x
      obtain ⟨_, xs₀, -, h₀, hxs⟩ := (PTr.app Hg Ha).constSpine? hs
      rw [he] at h₀; cases h₀
      by_cases hr : args₀.size = r.nparams ∧ (r.aux2nested.contains c ||
          (r.getNestedIfAuxCtor env' c).isSome) = true
      · rw [S.n_eq c hh hR, ← hr.1, ← Lean4Lean.List.Forall₂.length_eq hxs]; simp
      · refine descend ?_
        rw [restoreFn_of_not_const hne]
        simp only [ElimNestedInductive.Result.auxFn, hs, Option.bind_some]
        exact if_neg hr
    | none => exact descend (restoreFn_of_spine_none hne hs)
  | @letE _ _ _ _ _ _ _ _ _ _ _ _ _ ihv ihb =>
    simp only [Expr.replaceNoCache, restoreFn_letE, Expr.updateLetE!, Expr.ConstsOK] at hc
    exact ihb (hΔ.cons (ihv hΔ hc.2.1)) hc.2.2
  | @mdata _ g g' d Hg ih =>
    intro c ls xs hh he hR
    have hne : ∀ c ls, Expr.mdata d g ≠ .const c ls := nofun
    have descend (hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.mdata d g) = none) :
        hh.n ≤ xs.length := by
      simp only [Expr.replaceNoCache, hfn, Expr.updateMData!, Expr.ConstsOK] at hc
      exact ih hΔ hc _ _ _ _ he hR
    cases hs : ElimNestedInductive.Result.constSpine? (.mdata d g) with
    | some x =>
      obtain ⟨c₀, ls₀, args₀⟩ := x
      obtain ⟨_, xs₀, -, h₀, hxs⟩ := (PTr.mdata (d := d) Hg).constSpine? hs
      rw [he] at h₀; cases h₀
      by_cases hr : args₀.size = r.nparams ∧ (r.aux2nested.contains c ||
          (r.getNestedIfAuxCtor env' c).isSome) = true
      · rw [S.n_eq c hh hR, ← hr.1, ← Lean4Lean.List.Forall₂.length_eq hxs]; simp
      · refine descend ?_
        rw [restoreFn_of_not_const hne]
        simp only [ElimNestedInductive.Result.auxFn, hs, Option.bind_some]
        exact if_neg hr
    | none => exact descend (restoreFn_of_spine_none hne hs)

/-! ### Changing the context -/

/-- Every variable the first context binds, the second does. -/
def CtxSome (Δ₁ Δ₂ : VLCtx) : Prop := ∀ v, (Δ₁.find? v).isSome → (Δ₂.find? v).isSome

theorem CtxSome.cons {Δ₁ Δ₂ : VLCtx} (H : CtxSome Δ₁ Δ₂) (d₁ d₂ : VLocalDecl) :
    CtxSome ((none, d₁) :: Δ₁) ((none, d₂) :: Δ₂) := by
  have key (w) (h : (Δ₁.find? w).isSome) : ∃ q, Δ₂.find? w = some q :=
    Option.isSome_iff_exists.1 (H w h)
  rintro ((_ | i) | v) h
  · simp [VLCtx.find?, VLCtx.next]
  · have : (Δ₁.find? (.inl i)).isSome := by
      cases h1 : Δ₁.find? (.inl i) <;> simp_all [VLCtx.find?, VLCtx.next]
    obtain ⟨q, h'⟩ := key _ this
    simp [VLCtx.find?, VLCtx.next, h']
  · have : (Δ₁.find? (.inr v)).isSome := by
      cases h1 : Δ₁.find? (.inr v) <;> simp_all [VLCtx.find?, VLCtx.next]
    obtain ⟨q, h'⟩ := key _ this
    simp [VLCtx.find?, VLCtx.next, h']

/-- A term that translates in one context translates in another binding the same variables. -/
theorem PTr.ctxSome (H : PTr Us CL Δ₁ e x) (hΔ : CtxSome Δ₁ Δ₂) : ∃ y, PTr Us CL Δ₂ e y := by
  induction H generalizing Δ₂ with
  | bvar h =>
    obtain ⟨⟨y, B⟩, h'⟩ := Option.isSome_iff_exists.1 (hΔ _ (by rw [h]; rfl))
    exact ⟨_, .bvar h'⟩
  | fvar h =>
    obtain ⟨⟨y, B⟩, h'⟩ := Option.isSome_iff_exists.1 (hΔ _ (by rw [h]; rfl))
    exact ⟨_, .fvar h'⟩
  | sort h => exact ⟨_, .sort h⟩
  | const h => exact ⟨_, .const h⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1 hΔ; obtain ⟨_, h2⟩ := ih2 hΔ; exact ⟨_, .app h1 h2⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1 hΔ; obtain ⟨_, h2⟩ := ih2 (hΔ.cons _ (.vlam _))
    exact ⟨_, .lam h1 h2⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1 hΔ; obtain ⟨_, h2⟩ := ih2 (hΔ.cons _ (.vlam _))
    exact ⟨_, .forallE h1 h2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    obtain ⟨_, h1⟩ := ih1 hΔ; obtain ⟨_, h2⟩ := ih2 hΔ
    obtain ⟨_, h3⟩ := ih3 (hΔ.cons _ (.vlet _ _))
    exact ⟨_, .letE h1 h2 h3⟩
  | lit hl h _ => exact ⟨_, .lit hl (h.ground Literal.toConstructor_ground)⟩
  | mdata _ ih => obtain ⟨_, h⟩ := ih hΔ; exact ⟨_, .mdata h⟩
  | proj _ ih => obtain ⟨_, h⟩ := ih hΔ; exact ⟨_, .proj h⟩

/-- The second context agrees with the first wherever its value is aux-free. -/
def CtxAuxFree (R : Name → Option VAuxHead) (ren : Name → Option Name) (Δ₁ Δ₂ : VLCtx) : Prop :=
  ∀ v y A, Δ₁.find? v = some (y, A) → y.AuxFree R ren → ∃ A', Δ₂.find? v = some (y, A')

theorem CtxAuxFree.cons {Δ₁ Δ₂ : VLCtx} (H : CtxAuxFree R ren Δ₁ Δ₂) {d₁ d₂ : VLocalDecl}
    (hv : d₁.value.AuxFree R ren → d₂.value = d₁.value) (hd : d₂.depth = d₁.depth) :
    CtxAuxFree R ren ((none, d₁) :: Δ₁) ((none, d₂) :: Δ₂) := by
  rintro ((_ | i) | v) y A h hy
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨d₂.type, by simp [VLCtx.find?, VLCtx.next, hv hy]⟩
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨x, B, h, rfl, -⟩ := h
    obtain ⟨B', h'⟩ := H _ _ _ h (VExpr.ConstsSat.of_liftN hy)
    exact ⟨B'.liftN d₂.depth, by simp [VLCtx.find?, VLCtx.next, h', hd]⟩
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨x, B, h, rfl, -⟩ := h
    obtain ⟨B', h'⟩ := H _ _ _ h (VExpr.ConstsSat.of_liftN hy)
    exact ⟨B'.liftN d₂.depth, by simp [VLCtx.find?, VLCtx.next, h', hd]⟩

/-- An aux-free translation is kept in a context that agrees wherever it is aux-free: whatever
the term uses of the context shows up in its translation. -/
theorem PTr.ctxAuxFree (H : PTr Us CL Δ₁ e x) (hx : x.AuxFree R ren)
    (hΔ : CtxAuxFree R ren Δ₁ Δ₂) (hs : CtxSome Δ₁ Δ₂) : PTr Us CL Δ₂ e x := by
  induction H generalizing Δ₂ with
  | bvar h => obtain ⟨_, h'⟩ := hΔ _ _ _ h hx; exact .bvar h'
  | fvar h => obtain ⟨_, h'⟩ := hΔ _ _ _ h hx; exact .fvar h'
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 hx.1 hΔ hs) (ih2 hx.2 hΔ hs)
  | lam _ _ ih1 ih2 =>
    exact .lam (ih1 hx.1 hΔ hs)
      (ih2 hx.2 (hΔ.cons (fun _ => rfl) rfl) (hs.cons _ _))
  | forallE _ _ ih1 ih2 =>
    exact .forallE (ih1 hx.1 hΔ hs)
      (ih2 hx.2 (hΔ.cons (fun _ => rfl) rfl) (hs.cons _ _))
  | @letE _ _ ty' _ val' _ body' _ _ Hty Hval _ _ ihv ihb =>
    obtain ⟨ty'', hty⟩ := Hty.ctxSome hs
    by_cases hv : val'.AuxFree R ren
    · exact .letE hty (ihv hv hΔ hs)
        (ihb hx (hΔ.cons (fun _ => rfl) rfl) (hs.cons _ _))
    · obtain ⟨val'', hval⟩ := Hval.ctxSome hs
      exact .letE hty hval
        (ihb hx (hΔ.cons (d₂ := .vlet ty'' val'') (fun h => absurd h hv) rfl) (hs.cons _ _))
  | lit hl h _ => exact .lit hl (h.ground Literal.toConstructor_ground)
  | mdata _ ih => exact .mdata (ih hx hΔ hs)
  | proj _ ih => exact .proj (ih hx hΔ hs)


/-- The second context holds the restored values of the first's, wherever the leading arguments
`restore` keeps are aux-free. -/
def CtxRel (R : Name → Option VAuxHead) (ren : Name → Option Name) (Δ₁ Δ₂ : VLCtx) : Prop :=
  ∀ v y A, Δ₁.find? v = some (y, A) → y.LeadFree R ren →
    ∃ A', Δ₂.find? v = some (y.restore R ren, A')

theorem CtxRel.cons {Δ₁ Δ₂ : VLCtx} (H : CtxRel R ren Δ₁ Δ₂) {d₁ d₂ : VLocalDecl}
    (hv : d₁.value.LeadFree R ren → d₂.value = d₁.value.restore R ren)
    (hd : d₂.depth = d₁.depth) :
    CtxRel R ren ((none, d₁) :: Δ₁) ((none, d₂) :: Δ₂) := by
  rintro ((_ | i) | v) y A h hy
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨d₂.type, by simp [VLCtx.find?, VLCtx.next, hv hy]⟩
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨x, B, h, rfl, -⟩ := h
    obtain ⟨B', h'⟩ := H _ _ _ h (VExpr.LeadFree.of_liftN hy)
    exact ⟨B'.liftN d₂.depth, by simp [VLCtx.find?, VLCtx.next, h', hd, VExpr.restore_liftN]⟩
  · simp [VLCtx.find?, VLCtx.next] at h
    obtain ⟨x, B, h, rfl, -⟩ := h
    obtain ⟨B', h'⟩ := H _ _ _ h (VExpr.LeadFree.of_liftN hy)
    exact ⟨B'.liftN d₂.depth, by simp [VLCtx.find?, VLCtx.next, h', hd, VExpr.restore_liftN]⟩

theorem CtxRel.auxFree {Δ₁ Δ₂ : VLCtx} (H : CtxRel R ren Δ₁ Δ₂) : CtxAuxFree R ren Δ₁ Δ₂ :=
  fun v y A h hy => by
    obtain ⟨A', h'⟩ := H v y A h hy.leadFree
    exact ⟨A', by rwa [VExpr.restore_of_constsSat hy] at h'⟩

theorem forall₂_exists {R : α → β → Prop} {S : α → γ → Prop} (H : ∀ a b, R a b → ∃ c, S a c) :
    ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ → ∃ l₃, List.Forall₂ S l₁ l₃
  | [], [], .nil => ⟨[], .nil⟩
  | _ :: _, _ :: _, .cons h t =>
    let ⟨c, hc⟩ := H _ _ h; let ⟨l, hl⟩ := forall₂_exists H t; ⟨c :: l, .cons hc hl⟩

theorem constsOK_of_constSpine? {p : Name → List Level → Prop} : ∀ {t : Expr},
    ElimNestedInductive.Result.constSpine? t = some (c, ls, args) → t.ConstsOK p → p c ls
  | .const .., h, H => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h; exact H
  | .app f _, h, H => by
    simp only [ElimNestedInductive.Result.constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', a'⟩, h, he⟩ := h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, -⟩ := he
    exact constsOK_of_constSpine? h H.1
  | .bvar _, h, _ | .fvar _, h, _ | .mvar _, h, _ | .sort _, h, _ | .lam .., h, _
  | .forallE .., h, _ | .letE .., h, _ | .lit _, h, _ | .proj .., h, _ | .mdata .., h, _ => by
    cases h

theorem VExpr.restore_of_constSpine? {t : VExpr} {h : VAuxHead}
    (hs : t.constSpine? = some (c, ls, xs)) (hR : R c = some h) (hn : xs.length = h.n)
    (hren : ren c = none) : t.restore R ren = h.inst ls xs := by
  have hra : VExpr.restoreAux R t = some (h.inst ls xs) := by
    simp [VExpr.restoreAux, hs, hR, hn]
  cases t with
  | const => simp only [VExpr.constSpine?, Option.some.injEq, Prod.mk.injEq] at hs
             obtain ⟨rfl, rfl, rfl⟩ := hs; simp [VExpr.restore, hren, hra]
  | app => simp [VExpr.restore, hra]
  | _ => cases hs

theorem VExpr.LeadFree.of_constSpine? {t : VExpr} (H : t.LeadFree R ren)
    (hs : t.constSpine? = some (c, ls, xs)) (hR : R c = some h) (hn : xs.length = h.n) :
    ∀ x ∈ xs, x.AuxFree R ren := by
  cases t with
  | const => simp only [VExpr.constSpine?, Option.some.injEq, Prod.mk.injEq] at hs
             obtain ⟨-, -, rfl⟩ := hs; nofun
  | app f a =>
    have hra : VExpr.restoreAux R (.app f a) = some (h.inst ls xs) := by
      simp [VExpr.restoreAux, hs, hR, hn]
    unfold LeadFree at H; rw [hra] at H
    exact H c ls xs hs
  | _ => cases hs

/-- Where the kernel replaces an auxiliary constant's spine, the replacement translates, and to
the restored translation when its leading arguments are aux-free. -/
theorem PTr.restore_repl (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    (H : PTr Us CL Δ₁ t t') (hΔ : CtxRel R ren Δ₁ Δ₂) (hs : CtxSome Δ₁ Δ₂)
    (hsp : ElimNestedInductive.Result.constSpine? t = some (c, ls, args))
    (hn : args.size = r.nparams)
    (haux : (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true)
    (har : ls.length = lparams.length) :
    ∃ out y, r.kRepl env' lparams c ls args = some out ∧ PTr Us CL Δ₂ out y ∧
      (t'.LeadFree R ren → y = t'.restore R ren) := by
  obtain ⟨ls', xs', hls, hsp', hxs⟩ := H.constSpine? hsp
  obtain ⟨h, hR⟩ : ∃ h, R c = some h := Option.isSome_iff_exists.1 (by rw [S.aux]; exact haux)
  have hxn : xs'.length = h.n := by
    rw [S.n_eq c h hR, ← hn, ← Lean4Lean.List.Forall₂.length_eq hxs]; simp
  have hren : ren c = none := by rw [S.ren_eq]; exact S.ren_aux c (by simp [hR])
  by_cases hL : t'.LeadFree R ren
  · have hfree := hL.of_constSpine? hsp' hR hxn
    have hys : List.Forall₂ (PTr Us CL Δ₂) args.toList xs' := by
      clear hsp' hxn hL
      generalize args.toList = l at hxs ⊢
      induction hxs with
      | nil => exact .nil
      | cons h1 _ ih =>
        exact .cons (h1.ctxAuxFree (hfree _ (.head _)) hΔ.auxFree hs)
          (ih fun x hx => hfree x (.tail _ hx))
    obtain ⟨out, h1, h2⟩ := S.repl c h ls ls' args Δ₂ xs' hR hls har hn hys
    exact ⟨out, _, h1, h2, fun _ => (VExpr.restore_of_constSpine? hsp' hR hxn hren).symm⟩
  · obtain ⟨ys, hys⟩ := forall₂_exists (fun _ _ h => h.ctxSome hs) hxs
    obtain ⟨out, h1, h2⟩ := S.repl c h ls ls' args Δ₂ ys hR hls har hn hys
    exact ⟨out, _, h1, h2, fun h => absurd h hL⟩


theorem restoreFn_const_ren {c c' : Name} {ls : List Level} (h : auxRec.find? c = some c') :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.const c ls) = some (.const c' ls) := by
  simp [ElimNestedInductive.Result.restoreFn, h]

theorem restoreFn_of_repl {t : Expr} (ht : ∀ c' ls', t = .const c' ls' → auxRec.find? c' = none)
    (hsp : ElimNestedInductive.Result.constSpine? t = some (c, ls, args))
    (hcond : args.size = r.nparams ∧
      (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true) :
    ElimNestedInductive.Result.restoreFn r env' lparams auxRec t = r.kRepl env' lparams c ls args := by
  have : ElimNestedInductive.Result.restoreFn r env' lparams auxRec t =
      ElimNestedInductive.Result.auxFn r env' lparams t := by
    unfold ElimNestedInductive.Result.restoreFn
    split
    · rename_i c' ls'; simp [ht c' ls' rfl]
    · rfl
  rw [this]; simp only [ElimNestedInductive.Result.auxFn, hsp, Option.bind_some]
  exact if_pos hcond

/-- **The restoration on translations.** A plain translation of a term gives one of what
`restoreNested` makes of it, which is the restored translation where the leading arguments
`restore` keeps are aux-free; given that the restored term mentions no auxiliary constant, which
the kernel checks, and that the auxiliary constants occur at the block's number of levels. -/
theorem PTr.restore (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    (H : PTr Us CL Δ₁ e e') (hNP : CtxNP R Δ₁) (hΔ : CtxRel R ren Δ₁ Δ₂) (hs : CtxSome Δ₁ Δ₂)
    (har : e.ConstsOK fun c ls => (R c).isSome → ls.length = lparams.length)
    (hc : (ρ e).ConstsOK fun c _ => R c = none ∧ auxRec.find? c = none) :
    ∃ y, PTr Us CL Δ₂ (ρ e) y ∧ (e'.LeadFree R ren → y = e'.restore R ren) := by
  -- the case where the kernel replaces the node itself
  have repl {Δ₁ Δ₂ t t' c ls} {args : Array Expr} (H : PTr Us CL Δ₁ t t')
      (hΔ : CtxRel R ren Δ₁ Δ₂) (hs : CtxSome Δ₁ Δ₂)
      (har : t.ConstsOK fun c ls => (R c).isSome → ls.length = lparams.length)
      (ht : ∀ c' ls', t = .const c' ls' → auxRec.find? c' = none)
      (hsp : ElimNestedInductive.Result.constSpine? t = some (c, ls, args))
      (hcond : args.size = r.nparams ∧
        (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true) :
      ∃ y, PTr Us CL Δ₂ (ρ t) y ∧ (t'.LeadFree R ren → y = t'.restore R ren) := by
    have harc := constsOK_of_constSpine?
      (p := fun c ls => (R c).isSome = true → ls.length = lparams.length) hsp har
      (by rw [S.aux]; exact hcond.2)
    obtain ⟨out, y, h1, h2, h3⟩ := H.restore_repl S hΔ hs hsp hcond.1 hcond.2 harc
    refine ⟨y, ?_, h3⟩
    have hf := restoreFn_of_repl (lparams := lparams) ht hsp hcond
    rw [h1] at hf
    unfold Expr.replaceNoCache; rw [hf]; exact h2
  induction H generalizing Δ₂ with
  | @bvar x _ _ _ h =>
    simp only [Expr.replaceNoCache, restoreFn_bvar]
    obtain ⟨⟨y, B⟩, h'⟩ := Option.isSome_iff_exists.1 (hs _ (by rw [h]; rfl))
    by_cases hL : VExpr.LeadFree R ren x
    · obtain ⟨A', h''⟩ := hΔ _ _ _ h hL
      exact ⟨_, .bvar h'', fun _ => rfl⟩
    · exact ⟨_, .bvar h', fun h => absurd h hL⟩
  | @fvar x _ _ _ h =>
    simp only [Expr.replaceNoCache, restoreFn_fvar]
    obtain ⟨⟨y, B⟩, h'⟩ := Option.isSome_iff_exists.1 (hs _ (by rw [h]; rfl))
    by_cases hL : VExpr.LeadFree R ren x
    · obtain ⟨A', h''⟩ := hΔ _ _ _ h hL
      exact ⟨_, .fvar h'', fun _ => rfl⟩
    · exact ⟨_, .fvar h', fun h => absurd h hL⟩
  | sort h =>
    simp only [Expr.replaceNoCache, restoreFn_sort]
    exact ⟨_, .sort h, fun _ => rfl⟩
  | @const us' _ c us h =>
    cases hren : auxRec.find? c with
    | some c' =>
      simp only [Expr.replaceNoCache, restoreFn_const_ren (r := r) (env' := env')
        (lparams := lparams) hren]
      exact ⟨_, .const h, fun _ => by simp [VExpr.restore, S.ren_eq, hren]⟩
    | none =>
      by_cases hcond : (#[] : Array Expr).size = r.nparams ∧
          (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true
      · exact repl (.const h) hΔ hs har (by rintro _ _ ⟨⟩; exact hren) rfl hcond
      · have hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.const c us) =
            none := by
          unfold ElimNestedInductive.Result.restoreFn
          simp [hren, ElimNestedInductive.Result.auxFn, ElimNestedInductive.Result.constSpine?]
          exact fun h1 h2 => absurd ⟨h1, by simpa using h2⟩ hcond
        simp only [Expr.replaceNoCache, hfn]
        refine ⟨_, .const h, fun _ => ?_⟩
        have hra : VExpr.restoreAux R (.const c us') = none := by
          cases hR : R c with
          | none => simp [VExpr.restoreAux, VExpr.constSpine?, hR]
          | some hh =>
            have hn := S.n_eq c hh hR
            have ha := S.aux c; rw [hR] at ha
            simp [VExpr.restoreAux, VExpr.constSpine?, hR]
            intro h0; exact hcond ⟨by simp [← hn, ← h0], by simpa using ha.symm⟩
        simp [VExpr.restore, S.ren_eq, hren, hra]
  | @app _ f f' a a' Hf Ha ihf iha =>
    have hne : ∀ c ls, Expr.app f a ≠ .const c ls := nofun
    have descend (hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.app f a) = none) :
        ∃ y, PTr Us CL Δ₂ (ρ (.app f a)) y ∧
          ((VExpr.app f' a').LeadFree R ren → y = (VExpr.app f' a').restore R ren) := by
      have e1 : ρ (.app f a) = .app (ρ f) (ρ a) := Expr.replaceNoCache_app hfn
      rw [e1] at hc ⊢
      obtain ⟨yf, h1, e2⟩ := ihf hNP hΔ hs har.1 hc.1
      obtain ⟨ya, h2, e3⟩ := iha hNP hΔ hs har.2 hc.2
      refine ⟨_, .app h1 h2, fun hL => ?_⟩
      unfold VExpr.LeadFree at hL
      cases hra : VExpr.restoreAux R (.app f' a') with
      | some _ =>
        exfalso
        simp only [VExpr.restoreAux, Option.bind_eq_some_iff] at hra
        obtain ⟨⟨c, ls, xs⟩, hsp, hh, hR, hra⟩ := hra
        split at hra <;> [rename_i hn; cases hra]
        simp only [VExpr.constSpine?, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨c₀, ls₀, xs₀⟩, hsp, he⟩ := hsp
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
        have := Hf.noPartial S hNP hc.1 _ _ _ _ hsp hR
        simp at hn; omega
      | none =>
        rw [hra] at hL
        simp [VExpr.restore, hra, e2 hL.1, e3 hL.2]
    cases hsp : ElimNestedInductive.Result.constSpine? (.app f a) with
    | some x =>
      obtain ⟨c, ls, args⟩ := x
      by_cases hcond : args.size = r.nparams ∧
          (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true
      · exact repl (.app Hf Ha) hΔ hs har (by rintro _ _ ⟨⟩) hsp hcond
      · refine descend ?_
        rw [restoreFn_of_not_const hne]
        simp only [ElimNestedInductive.Result.auxFn, hsp, Option.bind_some]
        exact if_neg hcond
    | none => exact descend (restoreFn_of_spine_none hne hsp)
  | lam _ _ ih1 ih2 =>
    have e1 : ∀ {n t b bi}, ρ (.lam n t b bi) = .lam n (ρ t) (ρ b) bi := by
      exact Expr.replaceNoCache_lam restoreFn_lam
    rw [e1] at hc ⊢
    obtain ⟨yt, h1, e2⟩ := ih1 hNP hΔ hs har.1 hc.1
    obtain ⟨yb, h2, e3⟩ := ih2 (hNP.cons noPartial_bvar) (hΔ.cons (d₂ := .vlam yt)
      (fun _ => rfl) rfl) (hs.cons _ _) har.2 hc.2
    exact ⟨_, .lam h1 h2, fun hL => by simp [VExpr.restore, e2 hL.1, e3 hL.2]⟩
  | forallE _ _ ih1 ih2 =>
    have e1 : ∀ {n t b bi}, ρ (.forallE n t b bi) = .forallE n (ρ t) (ρ b) bi := by
      exact Expr.replaceNoCache_forallE restoreFn_forallE
    rw [e1] at hc ⊢
    obtain ⟨yt, h1, e2⟩ := ih1 hNP hΔ hs har.1 hc.1
    obtain ⟨yb, h2, e3⟩ := ih2 (hNP.cons noPartial_bvar) (hΔ.cons (d₂ := .vlam yt)
      (fun _ => rfl) rfl) (hs.cons _ _) har.2 hc.2
    exact ⟨_, .forallE h1 h2, fun hL => by simp [VExpr.restore, e2 hL.1, e3 hL.2]⟩
  | letE _ Hval _ ih1 ih2 ih3 =>
    have e1 : ∀ {n t v b nd}, ρ (.letE n t v b nd) = .letE n (ρ t) (ρ v) (ρ b) nd := by
      exact Expr.replaceNoCache_letE restoreFn_letE
    rw [e1] at hc ⊢
    obtain ⟨yt, h1, -⟩ := ih1 hNP hΔ hs har.1 hc.1
    obtain ⟨yv, h2, e2⟩ := ih2 hNP hΔ hs har.2.1 hc.2.1
    obtain ⟨yb, h3, e3⟩ := ih3 (hNP.cons (Hval.noPartial S hNP hc.2.1))
      (hΔ.cons (d₂ := .vlet yt yv) e2 rfl) (hs.cons _ _) har.2.2 hc.2.2
    exact ⟨_, .letE h1 h2 h3, e3⟩
  | @lit l _ _ hl h _ =>
    have e1 : ρ (.lit l) = .lit l := by
      rw [Expr.replaceNoCache.eq_def, restoreFn_lit]
    rw [e1]
    refine ⟨_, .lit hl (h.ground Literal.toConstructor_ground), fun _ => ?_⟩
    refine (VExpr.restore_of_constsSat ?_).symm
    refine h.ground_constsSat Literal.toConstructor_ground ?_ ?_
    · exact Literal.toConstructor_constsOK fun c hc _ => ⟨(S.lit _ hl c hc).1, by
        rw [S.ren_eq]; exact (S.lit _ hl c hc).2⟩
    · exact fun l hl c hc => ⟨(S.lit l hl c hc).1, by rw [S.ren_eq]; exact (S.lit l hl c hc).2⟩
  | @mdata _ g g' d Hg ih =>
    have hne : ∀ c ls, Expr.mdata d g ≠ .const c ls := nofun
    have descend (hfn : ElimNestedInductive.Result.restoreFn r env' lparams auxRec (.mdata d g) = none) :
        ∃ y, PTr Us CL Δ₂ (ρ (.mdata d g)) y ∧ (g'.LeadFree R ren → y = g'.restore R ren) := by
      have e1 : ρ (.mdata d g) = .mdata d (ρ g) := Expr.replaceNoCache_mdata hfn
      rw [e1] at hc ⊢
      obtain ⟨y, h1, e2⟩ := ih hNP hΔ hs har hc
      exact ⟨_, .mdata h1, e2⟩
    cases hsp : ElimNestedInductive.Result.constSpine? (.mdata d g) with
    | some x =>
      obtain ⟨c, ls, args⟩ := x
      by_cases hcond : args.size = r.nparams ∧
          (r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) = true
      · exact repl (.mdata Hg) hΔ hs har (by rintro _ _ ⟨⟩) hsp hcond
      · refine descend ?_
        rw [restoreFn_of_not_const hne]
        simp only [ElimNestedInductive.Result.auxFn, hsp, Option.bind_some]
        exact if_neg hcond
    | none => exact descend (restoreFn_of_spine_none hne hsp)
  | proj _ ih =>
    have e1 : ∀ {s i e}, ρ (.proj s i e) = .proj s i (ρ e) := by
      exact Expr.replaceNoCache_proj restoreFn_proj
    rw [e1] at hc ⊢
    obtain ⟨y, h1, e2⟩ := ih hNP hΔ hs har hc
    exact ⟨_, .proj h1, fun hL => by simp [VExpr.restore, e2 hL]⟩


/-- A rule's constructor name, as `restoreNested`'s caller restores it: an auxiliary constructor
becomes the earlier constructor it copies. -/
theorem restoreCtorName_eq {c auxI I_c : Name} {nested : Expr} {I_ls : List Level}
    (hg : r.getNestedIfAuxCtor env' c = some (nested, auxI))
    (hI : nested.getAppFn = .const I_c I_ls) :
    r.restoreCtorName env' c = c.replacePrefix auxI I_c := by
  simp [ElimNestedInductive.Result.restoreCtorName, hg, hI]

/-! ### Applications of the restoration -/

theorem _root_.Lean.Expr.mkAppN_eq_mkAppList {f : Expr} {xs : Array Expr} :
    mkAppN f xs = Expr.mkAppList f xs.toList := by
  rw [Expr.mkAppList_eq_foldl, mkAppN, Array.foldl_toList]; rfl

theorem _root_.Lean.Expr.getAppFn_mkAppList_const :
    ∀ {xs : List Expr}, (Expr.mkAppList (.const c ls) xs).getAppFn = .const c ls := by
  intro xs
  rw [← Expr.mkAppRevList_reverse]
  generalize xs.reverse = ys
  induction ys <;> simp_all [Expr.mkAppRevList, Expr.getAppFn]

theorem _root_.Lean.Expr.getAppArgs_mkAppList_const {xs : List Expr} :
    (Expr.mkAppList (.const c ls) xs).getAppArgs = xs.toArray := by
  rw [Expr.getAppArgs_eq_rev]
  suffices (Expr.mkAppList (.const c ls) xs).getAppArgsRevList = xs.reverse by simp [this]
  rw [← Expr.mkAppRevList_reverse]
  generalize hy : xs.reverse = ys
  clear hy
  induction ys <;> simp_all [Expr.mkAppRevList, Expr.getAppArgsRevList]

theorem replaceNoCache_rawFn_mkAppList {ps : List Name} {ls : List Level} :
    ∀ {f : Expr} {xs : List Expr}, (Expr.mkAppList f xs).replaceNoCache (rawFn ps ls) =
      Expr.mkAppList (f.replaceNoCache (rawFn ps ls)) (xs.map (·.replaceNoCache (rawFn ps ls)))
  | _, [] => rfl
  | f, x :: xs => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [replaceNoCache_rawFn_mkAppList, Expr.replaceNoCache_app rfl]

theorem instantiate'_mkAppList {L : List Expr} {k : Nat} :
    ∀ {f : Expr} {xs : List Expr}, (Expr.mkAppList f xs).instantiate' L k =
      Expr.mkAppList (f.instantiate' L k) (xs.map (·.instantiate' L k))
  | _, [] => rfl
  | f, x :: xs => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [instantiate'_mkAppList]; rfl

/-- `RestoreSpec.repl` from the translations of the occurrences the kernel recorded: an
auxiliary type's, over the parameters, is its `VAuxHead`'s constant applied to its arguments; an
auxiliary constructor's is the earlier constructor's, the occurrence's head renamed. -/
theorem RestoreSpec.repl_of_nested
    (haux : ∀ c h, R c = some h → (r.aux2nested.find? c).isSome ∨
      (r.getNestedIfAuxCtor env' c).isSome)
    (htype : ∀ c nested h, r.aux2nested.find? c = some nested → R c = some h → ∃ As,
      As.length = r.nparams ∧ PTr lparams CL (paramCtx As) (nested.abstract r.params)
        (.appN (.const h.name h.lvls) h.args))
    (hctor : ∀ c nested auxI h, r.aux2nested.find? c = none →
      r.getNestedIfAuxCtor env' c = some (nested, auxI) → R c = some h →
      ∃ I_c I_ls Ds As, nested.abstract r.params = mkAppN (.const I_c I_ls) Ds ∧
        h.name = c.replacePrefix auxI I_c ∧ As.length = r.nparams ∧
        PTr lparams CL (paramCtx As) (mkAppN (.const h.name I_ls) Ds)
          (.appN (.const h.name h.lvls) h.args)) :
    ∀ c h (ls : List Level) ls' (args : Array Expr) Δ ys, R c = some h →
      ls.mapM (VLevel.ofLevel Us) = some ls' → ls.length = lparams.length →
      args.size = r.nparams → List.Forall₂ (PTr Us CL Δ) args.toList ys →
      ∃ out, r.kRepl env' lparams c ls args = some out ∧ PTr Us CL Δ out (h.inst ls' ys) := by
  intro c h ls ls' args Δ ys hR hls hlen hn hys
  have hyl : ys.length = r.nparams := by
    rw [← Lean4Lean.List.Forall₂.length_eq hys]; simpa using hn
  have hinst : ∀ a : VExpr, a = .appN (.const h.name h.lvls) h.args →
      (a.instL ls').subst (VExpr.Subst.dflt.consList ys) = h.inst ls' ys := by
    rintro _ rfl
    simp [VAuxHead.inst, VExpr.instL_appN, VExpr.subst_appN, VExpr.instL, Function.comp_def]
  cases hn' : r.aux2nested.find? c with
  | some nested =>
    obtain ⟨As, hAs, hN⟩ := htype c nested h hn' hR
    refine ⟨(ElimNestedInductive.Result.instantiateLevelParamsRaw (nested.abstract r.params)
      lparams ls).instantiateRev args, by simp [ElimNestedInductive.Result.kRepl, hn'], ?_⟩
    rw [← hinst _ rfl]
    exact hN.instNested hls hlen hys (by omega)
  | none =>
    have hc := haux c h hR
    rw [hn'] at hc
    obtain ⟨⟨nested, auxI⟩, hg⟩ := Option.isSome_iff_exists.1 (hc.resolve_left (by simp))
    obtain ⟨I_c, I_ls, Ds, As, hN, hname, hAs, hP⟩ := hctor c nested auxI h hn' hg hR
    have hinstN : ∀ n : Name,
        (ElimNestedInductive.Result.instantiateLevelParamsRaw (mkAppN (.const n I_ls) Ds) lparams
          ls).instantiateRev args = Expr.mkAppList
          (.const n (I_ls.map (ElimNestedInductive.Result.substLevelParams
            fun x => List.lookup x (lparams.zip ls))))
          (Ds.toList.map fun d => (ElimNestedInductive.Result.instantiateLevelParamsRaw d lparams
            ls).instantiateRev args) := by
      intro n
      rw [instantiateLevelParamsRaw_eq, Expr.mkAppN_eq_mkAppList, replaceNoCache_rawFn_mkAppList,
        Expr.instantiateRev_eq_instantiate', instantiate'_mkAppList]
      simp [Expr.replaceNoCache, rawFn, Expr.instantiate', instantiateLevelParamsRaw_eq,
        Expr.instantiateRev_eq_instantiate', Function.comp_def]
    refine ⟨Expr.mkAppList (.const (c.replacePrefix auxI I_c)
      (I_ls.map (ElimNestedInductive.Result.substLevelParams fun x => List.lookup x (lparams.zip ls))))
      (Ds.toList.map fun d => (ElimNestedInductive.Result.instantiateLevelParamsRaw d lparams
        ls).instantiateRev args), ?_, ?_⟩
    · simp only [ElimNestedInductive.Result.kRepl, hn', hg, Option.bind_eq_bind, Option.bind_some]
      rw [hN, hinstN]
      simp [Expr.getAppFn_mkAppList_const, Expr.getAppArgs_mkAppList_const,
        Expr.mkAppN_eq_mkAppList]
    · have := hP.instNested hls hlen hys (by omega)
      rw [hinst _ rfl, hinstN, hname] at this
      exact this


/-- The auxiliary constants a translated term mentions occur at their declared number of levels. -/
theorem TrExprS.auxArity {env : VEnv} (H : TrExprS env Us Δ e e')
    (hR : ∀ c ci, env.constants c = some ci → (R c).isSome → ci.uvars = lparams.length) :
    e.ConstsOK fun c ls => (R c).isSome → ls.length = lparams.length := by
  induction H with
  | const h1 _ h3 => exact fun h => h3.trans (hR _ _ h1 h)
  | app _ _ _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | mdata _ ih | proj _ _ ih => exact ih
  | bvar | fvar | sort | lit => trivial

/-- **(a)** for a closed term: the kernel's restoration of a term translates to the restored
translation. -/
theorem PTr.restoreNested (S : RestoreSpec r env' lparams auxRec Us CL R ren)
    (H : PTr Us CL [] e e')
    (har : e.ConstsOK fun c ls => (R c).isSome → ls.length = lparams.length)
    (hc : (r.restoreNested env' lparams e auxRec).ConstsOK
      fun c _ => R c = none ∧ auxRec.find? c = none)
    (hL : e'.LeadFree R ren) :
    PTr Us CL [] (r.restoreNested env' lparams e auxRec) (e'.restore R ren) := by
  rw [ElimNestedInductive.Result.restoreNested_eq] at hc ⊢
  obtain ⟨y, h1, h2⟩ := H.restore S (Δ₂ := []) (fun _ _ _ h => by cases h)
    (fun _ _ _ h => by cases h) (fun _ h => by cases h) har hc
  exact h2 hL ▸ h1

/-- **(b)** Where the restored term has no `let`, its translation is typed from that of the
restored translation. -/
theorem TrExprS.restoreNested {E₁ E₀ : VEnv} (henv : E₀.Ordered)
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    (H : TrExprS E₁ Us [] e e')
    (hR : ∀ c ci, E₁.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    (hc : (r.restoreNested env' lparams e auxRec).ConstsOK
      fun c _ => R c = none ∧ auxRec.find? c = none)
    (hL : e'.LeadFree R ren) (hlf : (r.restoreNested env' lparams e auxRec).LetFree)
    (hlit : ∀ l, E₁.ContainsLits l → E₀.ContainsLits l)
    (hwf : (e'.restore R ren).WF E₀ Us.length []) :
    TrExprS E₀ Us [] (r.restoreNested env' lparams e auxRec) (e'.restore R ren) :=
  ((H.toPTr.restoreNested S (H.auxArity hR) hc hL).mono_lit hlit).toTrExprS henv hlf
    (by simp [VLCtx.toCtx]; trivial) hwf

/-- **(c)** Whatever the restored term translates to, it is the restored translation. -/
theorem TrExprS.restoreNested_unique {E₁ E₀ : VEnv}
    (S : RestoreSpec r env' lparams auxRec Us E₁.ContainsLits R ren)
    (H : TrExprS E₁ Us [] e e')
    (hR : ∀ c ci, E₁.constants c = some ci → (R c).isSome → ci.uvars = lparams.length)
    (hc : (r.restoreNested env' lparams e auxRec).ConstsOK
      fun c _ => R c = none ∧ auxRec.find? c = none)
    (hL : e'.LeadFree R ren)
    (hX : TrExprS E₀ Us [] (r.restoreNested env' lparams e auxRec) X) :
    X = e'.restore R ren :=
  hX.toPTr.unique (H.toPTr.restoreNested S (H.auxArity hR) hc hL)

end

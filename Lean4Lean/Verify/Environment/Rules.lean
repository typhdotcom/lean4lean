import Lean4Lean.Verify.Environment.Minors

/-!
# The recursor rules' right-hand sides

`mkRecRules` builds each rule's right-hand side by abstracting the parameters, motives, minor
premises and the constructor's fields over the minor premise applied to the fields and to the
inductive hypotheses' values, each a lambda over the pieces `mkRecInfos` recorded. These lemmas
translate such terms under bound variables, the binders the pieces were abstracted over.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive

theorem bvCtx_append_cons (xs : List VExpr) (x : VExpr) (Δ : VLCtx) :
    bvCtx (x :: xs) ++ Δ = bvCtx xs ++ (none, .vlam x) :: Δ := by
  simp [bvCtx]

theorem bvCtx_toCtx (xs : List VExpr) (Δ : VLCtx) :
    (bvCtx xs ++ Δ).toCtx = xs.reverse ++ Δ.toCtx := by
  induction xs generalizing Δ with
  | nil => rfl
  | cons x xs ih => rw [bvCtx_append_cons, ih]; simp [VLCtx.toCtx]

theorem find?_bvCtx_fvar {fv : FVarId} :
    ∀ (xs : List VExpr) {Δ : VLCtx} {p : Nat} {A : VExpr}, Δ.find? (.inr fv) = some (.bvar p, A) →
      ∃ A', (bvCtx xs ++ Δ).find? (.inr fv) = some (.bvar (p + xs.length), A')
  | [], _, _, _, h => ⟨_, h⟩
  | x :: xs, Δ, p, A, h => by
    rw [bvCtx_append_cons]
    have h' : VLCtx.find? ((none, .vlam x) :: Δ) (.inr fv) =
        some (.bvar (p + 1), A.liftN 1) := by
      simp [VLCtx.find?, VLCtx.next, h, VLocalDecl.depth, VExpr.liftN, liftVar]; omega
    obtain ⟨A', hA'⟩ := find?_bvCtx_fvar xs h'
    exact ⟨A', by rw [hA']; simp; omega⟩

theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.fvars_tr_bv {env : VEnv} {Us : List Name}
    {m : TypeChecker.MLCtx} {fvs : List FVarId} {tys : List VExpr} (h : m.IsTele fvs tys)
    (hnd : fvs.Nodup) (xs : List VExpr) :
    List.Forall₂ (TrExprS env Us (bvCtx xs ++ m.vlctx)) (fvs.map .fvar)
      (VExpr.bvars fvs.length xs.length) := by
  refine List.forall₂_of_getElem? (by simp [VExpr.bvars]) fun j a b ha hb => ?_
  simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
  obtain ⟨fv, hfv, rfl⟩ := ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hfv
  have hb' : b = .bvar (fvs.length - 1 - j + xs.length) := by
    have hj' : j < (List.range fvs.length).reverse.length := by simpa using hj
    simp only [VExpr.bvars, List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some,
      Option.some.injEq, List.getElem_reverse, List.getElem_range] at hb
    rw [← hb]; congr 1; simp
  subst hb'
  obtain ⟨A', hA'⟩ := find?_bvCtx_fvar xs (h.find?_fvar hnd hj)
  exact .fvar hA'

/-- A lift of a context into another, under the same bound variables, each lifted past what the
lift inserts. -/
theorem _root_.Lean4Lean.VLCtx.FVLift'.bvCtx {Δ Δ' : VLCtx} {ρ : Lift}
    (W : VLCtx.FVLift' Δ Δ' 0 ρ 0) : ∀ xs : List VExpr,
    VLCtx.FVLift' (AddInductive.bvCtx xs ++ Δ)
      (AddInductive.bvCtx (xs.zipIdx.map fun (A, i) => A.lift' (ρ.consN i)) ++ Δ')
      xs.length ρ xs.length := by
  intro xs
  obtain ⟨L, rfl⟩ : ∃ L, xs = L.reverse := ⟨xs.reverse, by simp⟩
  induction L with
  | nil => simpa using W
  | cons x L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = xs at ih ⊢
    have := ih.cons_bvar (.vlam x)
    simpa [bvCtx_snoc, List.zipIdx_append, VLocalDecl.lift', VLocalDecl.depth] using this

/-- Bound variables whose types a typed `lams` opens extend a well-formed context. -/
theorem bvCtx_wf_of_lams {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ (xs : List VExpr) {Δ : VLCtx} {e : VExpr}, Δ.WF env U →
      (VExpr.lams xs e).WF env U Δ.toCtx →
      (bvCtx xs ++ Δ).WF env U ∧ e.WF env U (bvCtx xs ++ Δ).toCtx
  | [], _, _, hΔ, he => ⟨hΔ, he⟩
  | x :: xs, Δ, e, hΔ, he => by
    obtain ⟨hx, hb⟩ := VExpr.WF.lam_inv henv hΔ.toCtx he
    rw [bvCtx_append_cons]
    exact bvCtx_wf_of_lams henv xs (Δ := (none, .vlam x) :: Δ) ⟨hΔ, nofun, hx⟩ hb

/-- Nested lambdas over binders whose types translate, each over the ones before it as bound
variables. -/
theorem lams_foldr_tr {env : VEnv} {Us : List Name} (henv : env.Ordered) :
    ∀ (bs : List (Name × Expr × BinderInfo)) (xs : List VExpr) {Δ : VLCtx} {b : Expr}
    {b' : VExpr} (hl : bs.length = xs.length),
    (∀ i (h : i < bs.length), TrExprS env Us (bvCtx (xs.take i) ++ Δ) bs[i].2.1
      (xs[i]'(hl ▸ h))) →
    TrExprS env Us (bvCtx xs ++ Δ) b b' → Δ.WF env Us.length →
    (VExpr.lams xs b').WF env Us.length Δ.toCtx →
    TrExprS env Us Δ (bs.foldr (fun (name, ty, bi) b => .lam name ty b bi) b) (.lams xs b')
  | [], [], _, _, _, _, _, hb, _, _ => by simpa using hb
  | (name, ty, bi) :: bs, x :: xs, Δ, b, b', hl, hbs, hb, hΔ, hwf => by
    obtain ⟨hx, hwf'⟩ := VExpr.WF.lam_inv henv hΔ.toCtx hwf
    have h0 := hbs 0 (by simp)
    simp only [List.take_zero, bvCtx_nil, List.nil_append, List.getElem_cons_zero] at h0
    refine .lam hx h0 (lams_foldr_tr henv bs xs (by simpa using hl) (fun i h => ?_)
      (by rw [← bvCtx_append_cons]; exact hb) ⟨hΔ, nofun, hx⟩ hwf')
    have := hbs (i + 1) (by simp; omega)
    simpa [List.take_succ_cons, bvCtx_append_cons] using this

/-- Each argument of a typed application is typed. -/
theorem appN_arg_wf {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) {f : VExpr} {as : List VExpr} (h : (f.appN as).WF env U Γ) :
    ∀ a ∈ as, a.WF env U Γ := by
  intro a ha
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have := VExpr.appN_wf_prefix henv hΓ (as := s ++ [a]) (bs := t) (by simpa using h)
  rw [VExpr.appN_append_singleton] at this
  obtain ⟨_, _, -, h2⟩ := this.app_inv henv hΓ
  exact ⟨_, h2⟩

theorem _root_.List.zipIdx_take' {α} : ∀ (l : List α) (i k : Nat),
    (l.take i).zipIdx k = (l.zipIdx k).take i
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | a :: l, i + 1, k => by simp [List.zipIdx_take' l i (k + 1)]

theorem bvCtx_append (xs ys : List VExpr) : bvCtx (xs ++ ys) = bvCtx ys ++ bvCtx xs := by
  simp [bvCtx]

theorem bvCtx_instL (xs : List VExpr) (ls : List VLevel) (Δ : VLCtx) :
    (bvCtx xs ++ Δ).instL ls = bvCtx (xs.map (·.instL ls)) ++ Δ.instL ls := by
  simp [VLCtx.instL_eq_map, bvCtx, VLocalDecl.instL, Function.comp_def]

theorem _root_.Lean4Lean.VLCtx.WF.append_right {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : VLCtx}, (Δ₁ ++ Δ₂).WF env U → Δ₂.WF env U
  | [], _, h => h
  | _ :: Δ₁, _, h => VLCtx.WF.append_right (Δ₁ := Δ₁) h.1

theorem find?_bvCtx_bvar {Δ : VLCtx} : ∀ (xs : List VExpr) {i : Nat}, i < xs.length →
    ∃ A, (bvCtx xs ++ Δ).find? (.inl i) = some (.bvar i, A) := by
  intro xs
  obtain ⟨L, rfl⟩ : ∃ L, xs = L.reverse := ⟨xs.reverse, by simp⟩
  induction L with
  | nil => intro i h; simp at h
  | cons x L ih =>
    intro i hi
    rw [List.reverse_cons] at hi ⊢
    generalize L.reverse = xs at ih hi ⊢
    rw [bvCtx_snoc]
    cases i with
    | zero =>
      exact ⟨(VLocalDecl.vlam x).type, by simp [VLCtx.find?, VLCtx.next, VLocalDecl.value]⟩
    | succ i =>
      obtain ⟨A, hA⟩ := ih (i := i) (by simp at hi; omega)
      exact ⟨A.liftN 1, by
        simp [VLCtx.find?, VLCtx.next, hA, VLocalDecl.depth, VExpr.liftN, liftVar]; omega⟩

/-- A translation in the small context `Mk`, under bound variables, in a view `V` of the kernel's
context that `Mk` lifts into, at the recursor's level parameters. -/
theorem trExprS_reseat {env : VEnv} {Us : List Name} (henv : env.WF) {V : TypeChecker.MLCtx}
    {cT : VContext} {pre : List Name} (hpre : ∀ u ∈ pre, u ∉ cT.lparams)
    (hUs : Us = pre ++ cT.lparams) (hle : cT.venv ≤ env) {Mk : TypeChecker.MLCtx} {ρ : Lift}
    (W : VLCtx.FVLift' (Mk.instL (VLevel.shift pre.length cT.lparams.length)).vlctx V.vlctx 0 ρ 0)
    (ys : List VExpr)
    (hΔ : (bvCtx (ys.zipIdx.map fun (B, i) =>
      (B.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN i)) ++ V.vlctx).WF
        env Us.length)
    {e : Expr} {e' : VExpr} (he : TrExprS cT.venv cT.lparams (bvCtx ys ++ Mk.vlctx) e e') :
    TrExprS env Us (bvCtx (ys.zipIdx.map fun (B, i) =>
      (B.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN i)) ++ V.vlctx) e
      ((e'.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN ys.length)) := by
  have h1 := he.lparams_append hpre
  rw [bvCtx_instL, ← TypeChecker.MLCtx.vlctx_instL] at h1
  have W' := W.bvCtx (ys.map (·.instL (VLevel.shift pre.length cT.lparams.length)))
  rw [List.zipIdx_map, List.map_map, List.length_map] at W'
  subst hUs
  exact (h1.mono hle).weakFV' henv.ordered W' (by simpa [Function.comp_def] using hΔ)

/-- An inductive hypothesis' value, built from the pieces `mkRecInfos` recorded, translates over a
view `V` of the kernel's context that the small context `Mk` of the parameters and the fields
before the recursive one lifts into, when the recursor applied to the parameters, motives and
minor premises `rec` translates under its binders. -/
theorem ihValue_tr {env : VEnv} {Us : List Name} (henv : env.WF) {V : TypeChecker.MLCtx}
    (hV : V.WF env Us) {cT : VContext} {pre : List Name} (hpre : ∀ u ∈ pre, u ∉ cT.lparams)
    (hUs : Us = pre ++ cT.lparams) (hle : cT.venv ≤ env)
    {Mk : TypeChecker.MLCtx} {fvk : FVarId} {ih : IHInfo} {ra : VRecArg}
    (hP : IHPieces cT.venv cT.lparams Mk fvk ih ra) {ρ : Lift}
    (W : VLCtx.FVLift' (Mk.instL (VLevel.shift pre.length cT.lparams.length)).vlctx V.vlctx 0 ρ 0)
    {p : Nat} {A : VExpr} (hk : V.vlctx.find? (.inr fvk) = some (.bvar p, A))
    {rec : Expr} {R : VExpr}
    (hrec : TrExprS env Us (bvCtx (ra.binders.zipIdx.map fun (B, i) =>
      (B.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN i)) ++ V.vlctx) rec R)
    (hwf : (VExpr.lams (ra.binders.zipIdx.map fun (B, i) =>
        (B.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN i))
      (.app (.appN R (ra.indices.map fun e =>
          (e.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN ra.binders.length)))
        (.appN (.bvar (ra.binders.length + p)) (VExpr.bvars ra.binders.length 0)))).WF
      env Us.length V.vlctx.toCtx) :
    TrExprS env Us V.vlctx (ih.value rec) (VExpr.lams (ra.binders.zipIdx.map fun (B, i) =>
        (B.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN i))
      (.app (.appN R (ra.indices.map fun e =>
          (e.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ.consN ra.binders.length)))
        (.appN (.bvar (ra.binders.length + p)) (VExpr.bvars ra.binders.length 0)))) := by
  generalize hsh : VLevel.shift pre.length cT.lparams.length = sh at *
  generalize hxs : (ra.binders.zipIdx.map fun (B, i) => (B.instL sh).lift' (ρ.consN i)) = xs at *
  have hxl : xs.length = ra.binders.length := by rw [← hxs]; simp
  have hΓ := hV.tr.wf
  obtain ⟨hΔ, hbwf⟩ := bvCtx_wf_of_lams henv.ordered xs hΓ hwf
  have hΔt : OnCtx (bvCtx xs ++ V.vlctx).toCtx (env.IsType Us.length) := hΔ.toCtx
  obtain ⟨F, B, hF, ha⟩ := hbwf.app_inv henv.ordered hΔt
  have hΔ' : ∀ i ≤ ra.binders.length,
      (bvCtx ((ra.binders.take i).zipIdx.map fun (B, i) => (B.instL sh).lift' (ρ.consN i)) ++
        V.vlctx).WF env Us.length := by
    intro i hi
    have e : xs = ((ra.binders.take i).zipIdx.map fun (B, i) => (B.instL sh).lift' (ρ.consN i)) ++
        xs.drop i := by
      rw [List.zipIdx_take', List.map_take, hxs]; exact (List.take_append_drop i xs).symm
    rw [e, bvCtx_append, List.append_assoc] at hΔ
    exact hΔ.append_right
  have hind : List.Forall₂ (TrExprS env Us (bvCtx xs ++ V.vlctx)) ih.indices.toList
      (ra.indices.map fun e => (e.instL sh).lift' (ρ.consN ra.binders.length)) := by
    rw [List.forall₂_map_right_iff]
    refine Lean4Lean.List.Forall₂.imp (fun a b h => ?_) hP.indices
    have := trExprS_reseat henv hpre hUs hle (hsh ▸ W) ra.binders
      (by rw [hsh, hxs]; exact hΔ) h
    rwa [hsh, hxs] at this
  have hfun : TrExprS env Us (bvCtx xs ++ V.vlctx) (mkAppN rec ih.indices)
      (.appN R (ra.indices.map fun e => (e.instL sh).lift' (ρ.consN ra.binders.length))) := by
    have := TrExprS.mkAppN_of_wf henv.ordered hΔt hrec hind ⟨_, hF⟩
    simpa using this
  have harg : TrExprS env Us (bvCtx xs ++ V.vlctx)
      (mkAppN ih.field ((Array.range ih.binders.size).reverse.map .bvar))
      (.appN (.bvar (ra.binders.length + p)) (VExpr.bvars ra.binders.length 0)) := by
    obtain ⟨A', hA'⟩ := find?_bvCtx_fvar xs hk
    rw [hxl, Nat.add_comm] at hA'
    have hargs : List.Forall₂ (TrExprS env Us (bvCtx xs ++ V.vlctx))
        ((List.range ra.binders.length).reverse.map Expr.bvar) (VExpr.bvars ra.binders.length 0) := by
      simp only [VExpr.bvars, Nat.add_zero, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      have : ∀ L : List Nat, (∀ i ∈ L, i < ra.binders.length) → List.Forall₂
          (fun a b => TrExprS env Us (bvCtx xs ++ V.vlctx) (.bvar a) (.bvar b)) L L := by
        intro L hL
        induction L with
        | nil => exact .nil
        | cons i L ih =>
          obtain ⟨B, hB⟩ := find?_bvCtx_bvar (Δ := V.vlctx) xs (i := i)
            (by rw [hxl]; exact hL i (.head _))
          exact .cons (.bvar hB) (ih fun j hj => hL j (.tail _ hj))
      exact this _ (by simp)
    have := TrExprS.mkAppN_of_wf henv.ordered hΔt (.fvar hA') hargs ⟨_, ha⟩
    have e : (Array.range ih.binders.size).reverse.map Expr.bvar =
        ((List.range ra.binders.length).reverse.map Expr.bvar).toArray :=
      Array.toList_inj.1 (by simp [Array.toList_range, hP.size])
    rw [hP.field, e]; exact this
  have hbs : ∀ i (h : i < ih.binders.toList.length), TrExprS env Us
      (bvCtx (xs.take i) ++ V.vlctx) ih.binders.toList[i].2.1 (xs[i]'(by
        rw [hxl, ← hP.size]; simpa using h)) := by
    intro i hi
    have hi' : i < ih.binders.size := by simpa using hi
    have hib : i < ra.binders.length := hP.size ▸ hi'
    have := trExprS_reseat henv hpre hUs hle (hsh ▸ W) (ra.binders.take i)
      (by rw [hsh]; exact hΔ' i (Nat.le_of_lt hib)) (hP.binders i hi')
    have e1 : xs.take i = ((ra.binders.take i).zipIdx.map fun (B, i) =>
        (B.instL sh).lift' (ρ.consN i)) := by
      rw [List.zipIdx_take', List.map_take, hxs]
    have e2 : xs[i]'(by rw [hxl]; exact hib) = (ra.binders[i].instL sh).lift' (ρ.consN i) := by
      simp [← hxs]
    rw [hsh, List.length_take, Nat.min_eq_left (Nat.le_of_lt hib), ← e1] at this
    simpa [e2] using this
  have := lams_foldr_tr henv.ordered ih.binders.toList xs (by rw [hxl, ← hP.size]; simp) hbs
    (.app hF ha hfun harg) hΓ hwf
  simpa [IHInfo.value, Array.foldr_toList] using this

/-- The iota rule's value of the inductive hypothesis for the `k`th field, of view `ra`, the
recursor being `rc`: below the `n` parameters, `T` motives, `C` minor premises and `m` fields. -/
def ihRhs (ls : List VLevel) (n T C m k : Nat) (rc : VExpr) (ra : VRecArg) : VExpr :=
  .lams (ra.binders.zipIdx.map fun (A, i) => (A.instL ls).reseat (T + C) k m 0 i) <| .app
    (.appN rc (VExpr.bvars n (T + C + m + ra.binders.length) ++
      VExpr.bvars T (C + m + ra.binders.length) ++ VExpr.bvars C (m + ra.binders.length) ++
      ra.indices.map fun e => (e.instL ls).reseat (T + C) k m 0 ra.binders.length))
    (.appN (.bvar (ra.binders.length + (m - 1 - k))) (VExpr.bvars ra.binders.length 0))

/-- `ihValue_tr` for the recursor applied to the parameters, motives and minor premises, in a view
`V` of the kernel's context holding them and the fields, into which the small context `Mf` of the
parameters and fields lifts past the motives and minor premises. -/
theorem ihRhs_tr {env : VEnv} {Us : List Name} (henv : env.WF) {V : TypeChecker.MLCtx}
    (hV : V.WF env Us) {cT : VContext} {pre : List Name} (hpre : ∀ u ∈ pre, u ∉ cT.lparams)
    (hUs : Us = pre ++ cT.lparams) (hle : cT.venv ≤ env)
    {pfvs motfvs minfvs fvs : List FVarId} {tys : List VExpr}
    (hVT : V.IsTele (pfvs ++ motfvs ++ minfvs ++ fvs) tys)
    {Mf : TypeChecker.MLCtx} {ptys ftys : List VExpr}
    (hMfT : Mf.IsTele (pfvs ++ fvs) (ptys ++ ftys)) (hfl : ftys.length = fvs.length)
    (W : VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx V.vlctx 0
      ((Lift.skipN .refl (motfvs.length + minfvs.length)).consN fvs.length) 0)
    {k : Nat} (hk : k < fvs.length) (hk' : fvs.length - k ≤ Mf.length)
    {ih : IHInfo} {ra : VRecArg}
    (hP : IHPieces cT.venv cT.lparams (Mf.dropN (fvs.length - k) hk') fvs[k] ih ra)
    {name : Name} {lvls : List Level} {rc : VExpr}
    (hc : ∀ Δ, TrExprS env Us Δ (.const name lvls) rc)
    (hwf : (ihRhs (VLevel.shift pre.length cT.lparams.length) pfvs.length motfvs.length
      minfvs.length fvs.length k rc ra).WF env Us.length V.vlctx.toCtx) :
    TrExprS env Us V.vlctx (ih.value (mkAppN (mkAppN (mkAppN (.const name lvls)
        (pfvs.map .fvar).toArray) (motfvs.map .fvar).toArray) (minfvs.map .fvar).toArray))
      (ihRhs (VLevel.shift pre.length cT.lparams.length) pfvs.length motfvs.length
        minfvs.length fvs.length k rc ra) := by
  generalize hsh : VLevel.shift pre.length cT.lparams.length = sh at *
  have hnd : (pfvs ++ motfvs ++ minfvs ++ fvs).Nodup := by
    have := hV.tr.wf.fvars_nodup; rw [hVT.fvars] at this; exact List.nodup_reverse.1 this
  -- the small context of the parameters and the fields before the `k`th
  have hMfT' := hMfT.instL sh
  rw [show pfvs ++ fvs = (pfvs ++ fvs.take k) ++ fvs.drop k by simp,
    show (ptys ++ ftys).map (·.instL sh) =
      (ptys.map (·.instL sh) ++ (ftys.map (·.instL sh)).take k) ++
        (ftys.map (·.instL sh)).drop k by simp] at hMfT'
  have W1 := hMfT'.fvlift_top (fvs.length - k) (by simp) (by simp [hfl])
    (by rw [TypeChecker.MLCtx.length_instL]; exact hk')
  rw [TypeChecker.MLCtx.dropN_instL _ _ _ hk'] at W1
  have W₀ : VLCtx.FVLift' ((Mf.dropN (fvs.length - k) hk').instL sh).vlctx V.vlctx 0
      (reseatLift (motfvs.length + minfvs.length) k fvs.length 0) 0 := W1.comp W
  -- the field
  have hj : pfvs.length + motfvs.length + minfvs.length + k <
      (pfvs ++ motfvs ++ minfvs ++ fvs).length := by simp; omega
  have hfk := hVT.find?_fvar hnd hj
  have hget : (pfvs ++ motfvs ++ minfvs ++ fvs)[pfvs.length + motfvs.length + minfvs.length + k]'hj
      = fvs[k] := by
    rw [List.getElem_append_right (by simp; omega)]; congr 1; simp; omega
  have hpos : (pfvs ++ motfvs ++ minfvs ++ fvs).length - 1 -
      (pfvs.length + motfvs.length + minfvs.length + k) = fvs.length - 1 - k := by simp; omega
  rw [hget, hpos] at hfk
  -- the recursor applied to the parameters, motives and minor premises
  generalize hxs : (ra.binders.zipIdx.map fun (B, i) =>
    (B.instL sh).lift' ((reseatLift (motfvs.length + minfvs.length) k fvs.length 0).consN i)) = xs
  have hxl : xs.length = ra.binders.length := by rw [← hxs]; simp
  have hall := hVT.fvars_tr_bv (env := env) (Us := Us) hnd xs
  have hb : VExpr.bvars (pfvs ++ motfvs ++ minfvs ++ fvs).length xs.length =
      VExpr.bvars pfvs.length (motfvs.length + minfvs.length + fvs.length + xs.length) ++
        VExpr.bvars motfvs.length (minfvs.length + fvs.length + xs.length) ++
        VExpr.bvars minfvs.length (fvs.length + xs.length) ++
        VExpr.bvars fvs.length xs.length := by
    rw [show (pfvs ++ motfvs ++ minfvs ++ fvs).length =
      pfvs.length + (motfvs.length + (minfvs.length + fvs.length)) by
        simp only [List.length_append]; omega]
    rw [← VExpr.bvars_append pfvs.length, ← VExpr.bvars_append motfvs.length,
      ← VExpr.bvars_append minfvs.length]
    simp only [List.append_assoc, Nat.add_assoc]
  rw [hb, List.map_append, List.map_append, List.map_append] at hall
  have hargs := List.Forall₂.take_append (by simp [VExpr.bvars]) hall
  rw [← List.map_append, ← List.map_append] at hargs
  have hspec : ihRhs sh pfvs.length motfvs.length minfvs.length fvs.length k rc ra =
      VExpr.lams xs (.app (.appN (.appN rc
        (VExpr.bvars pfvs.length (motfvs.length + minfvs.length + fvs.length + xs.length) ++
          VExpr.bvars motfvs.length (minfvs.length + fvs.length + xs.length) ++
          VExpr.bvars minfvs.length (fvs.length + xs.length)))
        (ra.indices.map fun e => (e.instL sh).lift'
          ((reseatLift (motfvs.length + minfvs.length) k fvs.length 0).consN ra.binders.length)))
        (.appN (.bvar (ra.binders.length + (fvs.length - 1 - k))) (VExpr.bvars ra.binders.length 0)))
      := by
    simp only [ihRhs, ← hxs, lift'_reseatLift, VExpr.appN_append, List.length_map,
      List.length_zipIdx]
  rw [hspec] at hwf ⊢
  -- the recursor's application is typed under the binders
  have hΓ := hV.tr.wf
  obtain ⟨hΔ, hbwf⟩ := bvCtx_wf_of_lams henv.ordered xs hΓ hwf
  obtain ⟨_, _, hF, -⟩ := hbwf.app_inv henv.ordered hΔ.toCtx
  rw [← VExpr.appN_append] at hF
  have hRwf := VExpr.appN_wf_prefix henv.ordered hΔ.toCtx ⟨_, hF⟩
  have hrec := TrExprS.mkAppN_of_wf henv.ordered hΔ.toCtx (hc _) hargs hRwf
  simp only [List.map_append] at hrec
  have hrecE : mkAppN (mkAppN (mkAppN (.const name lvls) (pfvs.map .fvar).toArray)
      (motfvs.map .fvar).toArray) (minfvs.map .fvar).toArray =
      mkAppN (.const name lvls)
        (pfvs.map Expr.fvar ++ motfvs.map Expr.fvar ++ minfvs.map Expr.fvar).toArray := by
    simp [mkAppN_append]
  rw [hrecE]
  subst hsh
  rw [← hxs] at hrec ⊢
  exact ihValue_tr henv hV hpre hUs hle hP W₀ hfk hrec (by rw [← hxs] at hwf; exact hwf)

theorem _root_.List.Forall₂.length_flatten {R : List α → List β → Prop}
    (hR : ∀ a b, R a b → a.length = b.length) :
    ∀ {l₁ : List (List α)} {l₂ : List (List β)}, List.Forall₂ R l₁ l₂ →
      l₁.flatten.length = l₂.flatten.length
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp [hR _ _ h, List.Forall₂.length_flatten hR t]

theorem mkLambda_agree {lctx₁ lctx₂ : LocalContext} {xs : List FVarId} {b : Expr}
    (H : ∀ x ∈ xs, (lctx₂.find? x).map LocalDecl.erase = (lctx₁.find? x).map LocalDecl.erase) :
    lctx₂.mkLambda ⟨xs.map .fvar⟩ b = lctx₁.mkLambda ⟨xs.map .fvar⟩ b := by
  rw [LocalContext.mkLambda, LocalContext.mkLambda, LocalContext.mkBinding_eq,
    LocalContext.mkBinding_eq, TypeChecker.mkBindingList_agree H]

theorem _root_.Lean4Lean.TypeChecker.MLCtx.mkLambda'_isTele : ∀ (n : Nat) {m : TypeChecker.MLCtx}
    {fvs₂ : List FVarId} {tys₂ : List VExpr} {fvs₁ tys₁}, fvs₂.length = n →
    m.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂) → fvs₂.length = tys₂.length → ∀ X hk,
    m.mkLambda' fvs₂.length hk X = .lams tys₂ X
  | 0, _, fvs₂, tys₂, _, _, hn, _, hlen, _, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm; rfl
  | n + 1, m, fvs₂, tys₂, fvs₁, tys₁, hn, h, hlen, X, hk => by
    obtain ⟨tys₂, ty, rfl⟩ : ∃ a b, tys₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys₂).resolve_left (by rintro rfl; simp_all)
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [← List.append_assoc, ← List.append_assoc] at h
    obtain ⟨name, ty', bi, m', rfl, h'⟩ := h.snoc_inv
    simp only [List.length_append, List.length_singleton, TypeChecker.MLCtx.mkLambda']
    rw [TypeChecker.MLCtx.mkLambda'_isTele n hn h' hlen, VExpr.lams_append]; rfl

/-- `mkLambda` over the top variables of a telescope context, the kernel's local context
declaring them as the view does. -/
theorem mkLambda_tele {lctx : LocalContext} {env : VEnv} {Us : List Name} {E : TypeChecker.MLCtx}
    (henv : env.WF) (hwf : E.WF env Us)
    {fvs₁ fvs₂ : List FVarId} {tys₁ tys₂ : List VExpr} (hT : E.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂))
    (hlen : fvs₂.length = tys₂.length)
    (hag : ∀ x ∈ fvs₂, (lctx.find? x).map LocalDecl.erase = (E.lctx.find? x).map LocalDecl.erase)
    {e : Expr} {e' ty : VExpr} (he : TrExprS env Us E.vlctx e e')
    (hety : env.HasType Us.length E.vlctx.toCtx e' ty) :
    ∃ hk, lctx.mkLambda (fvs₂.map .fvar).toArray e = E.mkLambda fvs₂.length hk e ∧
      TrExprS env Us (E.dropN fvs₂.length hk).vlctx (E.mkLambda fvs₂.length hk e)
        (.lams tys₂ e') ∧
      env.HasType Us.length (E.dropN fvs₂.length hk).vlctx.toCtx (.lams tys₂ e')
        (.foralls tys₂ ty) := by
  have hk : fvs₂.length ≤ E.length := by rw [hT.length]; simp
  refine ⟨hk, ?_, ?_⟩
  · have h1 := mkLambda_agree (b := e) hag
    have h2 := hwf.mkLambda_eq (arr := (fvs₂.map .fvar).toArray) (e := e) fvs₂.length hk (by
      rw [hT.fvarRevList fvs₂.length rfl hk]; simp [List.map_reverse])
    exact h1.trans h2
  · have := hwf.mkLambda_trS henv he hety fvs₂.length hk
    rwa [TypeChecker.MLCtx.mkLambda'_isTele fvs₂.length rfl hT hlen,
      TypeChecker.MLCtx.mkForall'_isTele fvs₂.length rfl hT hlen] at this

/-- Nested `mkLambda`s over consecutive segments of the top of a telescope context. -/
theorem mkLambda_nest {env : VEnv} {Us : List Name} (henv : env.WF) {lctx : LocalContext} :
    ∀ (segs : List (List FVarId)) (tyss : List (List VExpr)) {E : TypeChecker.MLCtx}
    {Bfvs : List FVarId} {Btys : List VExpr}, E.WF env Us →
    E.IsTele (Bfvs ++ segs.flatten) (Btys ++ tyss.flatten) →
    List.Forall₂ (fun (s : List FVarId) (t : List VExpr) => s.length = t.length) segs tyss →
    (∀ x ∈ segs.flatten, (lctx.find? x).map LocalDecl.erase =
      (E.lctx.find? x).map LocalDecl.erase) →
    ∀ {e : Expr} {e' ty : VExpr}, TrExprS env Us E.vlctx e e' →
      env.HasType Us.length E.vlctx.toCtx e' ty →
    ∃ hk : segs.flatten.length ≤ E.length,
      TrExprS env Us (E.dropN segs.flatten.length hk).vlctx
        (segs.foldr (fun s acc => lctx.mkLambda (s.map .fvar).toArray acc) e)
        (.lams tyss.flatten e') ∧
      env.HasType Us.length (E.dropN segs.flatten.length hk).vlctx.toCtx (.lams tyss.flatten e')
        (.foralls tyss.flatten ty)
  | [], [], _, _, _, _, _, _, _, _, _, _, he, hety => ⟨Nat.zero_le _, he, hety⟩
  | s :: segs, t :: tyss, E, Bfvs, Btys, hE, hT, .cons hl hrest, hag, e, e', ty, he, hety => by
    have hT' : E.IsTele ((Bfvs ++ s) ++ segs.flatten) ((Btys ++ t) ++ tyss.flatten) := by
      simpa using hT
    obtain ⟨hk₁, tr₁, ty₁⟩ := mkLambda_nest henv (lctx := lctx) segs tyss hE hT' hrest
      (fun x hx => hag x (by simp only [List.flatten_cons]; exact List.mem_append_right _ hx))
      he hety
    have hrl : segs.flatten.length = tyss.flatten.length :=
      List.Forall₂.length_flatten (fun _ _ h => h) hrest
    obtain ⟨-, -, -, -, hT₁⟩ := hT'.vlctx_split segs.flatten.length rfl hrl hk₁
    have hE₁ := hE.dropN _ hk₁
    obtain ⟨hk₂, eq₂, tr₂, ty₂⟩ := mkLambda_tele (lctx := lctx) henv hE₁ hT₁ hl
      (fun x hx => by
        rw [hag x (by simp only [List.flatten_cons]; exact List.mem_append_left _ hx)]
        rw [hE.find?_dropN _ hk₁ (by rw [hT₁.fvars]; simp [hx])]) tr₁ ty₁
    have hlen : (s :: segs).flatten.length = segs.flatten.length + s.length := by
      rw [List.flatten_cons, List.length_append, Nat.add_comm]
    have hk' : segs.flatten.length + s.length ≤ E.length := by
      have := TypeChecker.MLCtx.length_dropN E _ hk₁; omega
    have hk : (s :: segs).flatten.length ≤ E.length := hlen ▸ hk'
    have e₂ : (E.dropN segs.flatten.length hk₁).dropN s.length hk₂ =
        E.dropN (s :: segs).flatten.length hk := by
      rw [TypeChecker.MLCtx.dropN_dropN E _ _ hk₁ hk₂ hk']
      exact TypeChecker.MLCtx.dropN_congr hlen.symm _ _
    refine ⟨hk, ?_, ?_⟩
    · rw [← e₂]
      simp only [List.foldr_cons, List.flatten_cons, VExpr.lams_append]
      rw [eq₂]; exact tr₂
    · rw [← e₂]
      simp only [List.flatten_cons, VExpr.lams_append, VExpr.foralls_append]
      exact ty₂

/-- The fields the kernel opened for a minor premise are none of the minor premises, nor among the
variables opened before the first. -/
theorem MinorKD.fvs_fresh {kds : List MinorKD} {F : List FVarId}
    (h : ((kds.reverse.map MinorKD.seg).flatten ++ F).Nodup) {q : Nat} (hq : q < kds.length)
    {x : FVarId} (hx : x ∈ kds[q].fvs) : x ∉ F ∧ x ∉ kds.map (·.minor) := by
  have hseg : x ∈ kds[q].seg := by simp [MinorKD.seg, hx]
  have hmemL : kds[q].seg ∈ kds.reverse.map MinorKD.seg :=
    List.mem_map.2 ⟨_, List.mem_reverse.2 (List.getElem_mem hq), rfl⟩
  have hxf : x ∈ (kds.reverse.map MinorKD.seg).flatten := List.mem_flatten.2 ⟨_, hmemL, hseg⟩
  obtain ⟨hnd, -, hdisj⟩ := List.nodup_append.1 h
  refine ⟨fun hF => hdisj x hxf x hF rfl, fun hm => ?_⟩
  obtain ⟨kd', hkd', hxe⟩ := List.mem_map.1 hm
  obtain ⟨q', hq', rfl⟩ := List.getElem_of_mem hkd'
  obtain ⟨hnds, hpw⟩ := (List.pairwise_flatten (R := (· ≠ ·))).1 hnd
  rw [List.map_reverse, List.pairwise_reverse, List.pairwise_map] at hpw
  have hmin : kds[q'].minor ∈ kds[q'].seg := by simp [MinorKD.seg]
  rcases Nat.lt_trichotomy q q' with hlt | rfl | hlt
  · exact List.pairwise_iff_getElem.1 hpw q q' hq hq' hlt _ hmin _ hseg hxe
  · have := hnds _ hmemL
    simp only [MinorKD.seg, List.pairwise_cons] at this
    exact this.1 x (by simp [hx]) hxe
  · exact List.pairwise_iff_getElem.1 hpw q' q hq' hq hlt _ hseg _ hmin hxe.symm

theorem _root_.List.Forall₂.and_mem_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ (fun a b => R a b ∧ b ∈ l₂) l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons ⟨h, .head _⟩
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.1, .tail _ h.2⟩) t.and_mem_right)

/-- An iota rule's right-hand side: the minor premise applied to the fields and to each inductive
hypothesis' value. -/
theorem iotaRule_rhs (d : VInductDecl) (ls : List VLevel) (v : VLevel) (recLs : List VLevel)
    (q j : Nat) (c : VConstructor) :
    (d.iotaRule ls v recLs q j c).rhs =
      .lams (d.recBinders ls v ++
          VExpr.liftTele (d.types.length + d.ctors.length) (c.fields.map (·.type.instL ls)))
        (.appN (.bvar (c.fields.length + (d.ctors.length - 1 - q)))
          (VExpr.bvars c.fields.length 0 ++ c.recFields.map fun (k, ra) =>
            ihRhs ls d.params.length d.types.length d.ctors.length c.fields.length k
              (d.recConst recLs ra.typeIdx) ra)) := rfl

/-- The recursor's universe levels, as the kernel writes them, are its level parameters. -/
theorem getRecLevels_tr {Us pre : List Name} {elimLevel : Level} {levels : List Level}
    (hlev : levels = Us.map .param) (hpnd : (pre ++ Us).Nodup)
    (h : (elimLevel = .zero ∧ pre = []) ∨ ∃ u, elimLevel = .param u ∧ pre = [u]) :
    (getRecLevels elimLevel levels).mapM (VLevel.ofLevel (pre ++ Us)) =
      some (VLevel.params (pre ++ Us).length) := by
  subst hlev
  rcases h with ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩
  · have := mapM_ofLevel_params (Us := Us) [] hpnd
    simp only [getRecLevels, Level.isParam, Bool.false_eq_true, ↓reduceIte] at this ⊢
    rw [this]; simp [VLevel.params]
  · have h1 : VLevel.ofLevel ([u] ++ Us) (.param u) = some (.param 0) := by
      simp [VLevel.ofLevel]
    have := mapM_ofLevel_params (Us := Us) [u] hpnd
    simp only [getRecLevels, Level.isParam, ↓reduceIte, List.mapM_cons, h1, this]
    simp [VLevel.params, List.range_succ_eq_map, Function.comp_def]

end AddInductive
end Lean4Lean

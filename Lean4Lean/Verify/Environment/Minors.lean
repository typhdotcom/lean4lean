import Lean4Lean.Verify.Environment.RecInfos

/-!
# Verifying `mkRecInfos`' minor premises

`mkRecInfos.loopInd2` opens, for each constructor of the block, its fields, an inductive hypothesis
per field `isRecArg` sees as recursive, and the minor premise over them. The fields are read off
the constructor's declared type syntactically, with the parameters instantiated; the inductive
hypotheses are read off each recursive field's type normalized again, which is verified in the
smallest context it needs, as `loopInd1`'s normalizations are.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive

theorem isRecArg.loop.WF {X : Name → Prop} {pre : List Name} {stats : InductiveStats} :
    ∀ fuel (cs : TypeChecker.VContext) (cb : VContext) ρ (t : Expr) (T : VExpr),
      Sub X pre ρ cs cb → cs.TrExprS t T →
      WF cb (isRecArg.loop stats t fuel) fun _ => True := by
  intro fuel
  induction fuel with
  | zero => intros; exact .throw
  | succ fuel ih =>
  intro cs cb ρ t T hsub ht
  simp only [isRecArg.loop]
  refine WF.bind (hsub.whnf ht) fun e₁ h₁ => ?_
  obtain ⟨-, -, V₀, hS, -⟩ := h₁
  split
  · rename_i name dom body bi
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i dom' body'
    have henv := cs.Ewf
    have hΔ := cs.Δwf
    have hΓ := hΔ.toCtx
    refine WF.bind hsub.consumeTypeAnnotations fun dom_s hds => ?_
    obtain ⟨rfl, hok⟩ := hds
    obtain ⟨ty', hty, hdefty⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom
    have htyT : cs.IsType ty' := hdomT.defeqU_l henv hΓ hdefty
    obtain ⟨wf, hsub'⟩ := hsub.push (name := name) (bi := bi) hty htyT
    refine WF.withLocalDecl (hsub.trExprS hty) (hsub.isType htyT) ?_
    obtain ⟨u₀, hdomS⟩ := hdomT
    have hΔeq : VLCtx.IsDefEq cs.venv cs.lparams.length
        ((none, .vlam dom') :: cs.vlctx) ((none, .vlam ty') :: cs.vlctx) :=
      .cons (VLCtx.IsDefEq.refl henv.ordered hΔ) nofun (.vlam (hdefty.of_l henv hΓ hdomS))
    obtain ⟨body'', hbody''⟩ := hbody.defeqDFC henv hΔeq
    have hinst : (Sub.pushS cs ⟨cb.ngen.curr⟩ name dom.consumeTypeAnnotations' ty' bi
        wf).TrExprS (body.instantiate1 (.fvar ⟨cb.ngen.curr⟩)) body'' := by
      rw [Lean.Expr.instantiate1_eq]
      exact hbody''.inst_fvar henv.ordered (Sub.pushS cs _ _ _ _ _ wf).Δwf
    exact ih _ _ _ _ _ hsub' hinst
  · exact .pure trivial

/-- Instantiating a binder with a variable declared at a definitionally equal type. -/
theorem TrExprS.inst_fvar_defeq {env : VEnv} {Us : List Name} {Δ : VLCtx} {a : FVarId}
    {deps : List FVarId} {A A' : VExpr} {e : Expr} {e' : VExpr} {u : VLevel} (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length ((some (a, deps), .vlam A') :: Δ))
    (hAA : env.IsDefEq Us.length Δ.toCtx A A' (.sort u))
    (H : TrExprS env Us ((none, .vlam A) :: Δ) e e') :
    TrExprS env Us ((some (a, deps), .vlam A') :: Δ) (e.instantiate1' (.fvar a)) e' := by
  have hd : VLCtx.IsDefEq env Us.length ((none, .vlam A) :: Δ) ((none, .vlam A') :: Δ) :=
    .cons (.refl henv.ordered hΔ.1) nofun (.vlam hAA)
  obtain ⟨e'', h⟩ := H.defeqDFC henv hd
  obtain rfl := H.unique' (.cons .base .vlam) (TrExprS.IsUnique.all _) h
  exact h.inst_fvar henv.ordered hΔ

/-- The variables among `fvs` flagged in `rs`. -/
def recFvs (fvs : List FVarId) (rs : List Bool) : List FVarId :=
  (fvs.zip rs).filterMap fun (fv, r) => if r then some fv else none

theorem recFvs_snoc {fvs : List FVarId} {rs : List Bool} (h : rs.length = fvs.length)
    (fv : FVarId) (r : Bool) :
    recFvs (fvs ++ [fv]) (rs ++ [r]) = recFvs fvs rs ++ if r then [fv] else [] := by
  simp only [recFvs, List.zip_append h.symm, List.filterMap_append]
  cases r <;> simp

/-- What `loopCtorArgs` keeps, having read `i` binders of a constructor type that translates to
`.foralls (ps ++ Ds) R`, its parameters `ps` agreeing with the block's `params`. While reading the
parameters it instantiates them with the block's, and the rest of the type translates in the
parameters read so far. Then it opens each field `fvs` at the translation `ftys` of its declared
domain stripped of annotations, flagging in `rs` those `isRecArg` sees as recursive: the small
context `Mf` is the parameters and those fields, and the rest of the type translates there. -/
structure CtorArgsInv (cT : VContext) (X : Name → Prop) (pre : List Name)
    (Mp : TypeChecker.MLCtx) (pfvs : List FVarId) (params ps Ds : List VExpr) (R : VExpr)
    (P : VContext → Prop) (F₀ : List FVarId) (t : Expr) (i : Nat) (fvs : List FVarId)
    (ftys : List VExpr) (rs : List Bool) (Mf : TypeChecker.MLCtx)
    (hMf : Mf.WF cT.venv cT.lparams) (cb : VContext) (ρ : Lift) : Prop where
  tele : Mf.IsTele (pfvs ++ fvs) (params ++ ftys)
  base : ∃ hk, Mf.dropN fvs.length hk = Mp
  sub : Sub X pre ρ (cT.small Mf hMf) cb
  pred : P cb
  fvars : cb.mlctx.vlctx.fvars = fvs.reverse ++ F₀
  rs : rs.length = fvs.length
  le : fvs.length ≤ Ds.length
  arity : declareConstructors.arity 0 t + i = ps.length + Ds.length
  tr : (i < params.length ∧ fvs = [] ∧ ∃ (Mi : TypeChecker.MLCtx), ∃ hk,
      Mp.dropN (params.length - i) hk = Mi ∧ Mi.IsTele (pfvs.take i) (params.take i) ∧
      TrExprS cT.venv cT.lparams Mi.vlctx t (.foralls (ps.drop i ++ Ds) R) ∧
      cT.venv.TeleDefEq cT.lparams.length Mi.vlctx.toCtx (ps.drop i) (params.drop i)) ∨
    (i = params.length + fvs.length ∧
      TrExprS cT.venv cT.lparams Mf.vlctx t (.foralls (Ds.drop fvs.length) R))
  fields : ∀ j D fty, Ds[j]? = some D → ftys[j]? = some fty →
    cT.venv.IsDefEqU cT.lparams.length ((ftys.take j).reverse ++ params.reverse) D fty

theorem loopCtorArgs.loop.WF {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {pfvs : List FVarId} {params : List VExpr}
    (hMpT : Mp.IsTele pfvs params) {stats : InductiveStats}
    (hpar : stats.params.toList = pfvs.map .fvar) {ps Ds : List VExpr} {R : VExpr}
    (hps : ps.length = params.length) {F₀ : List FVarId} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {k : Expr → Array Expr → Array Expr → M α} {Q}
    (H : ∀ t fvs ftys rs Mf hMf cb ρ,
      CtorArgsInv cT X pre Mp pfvs params ps Ds R P F₀ t (params.length + fvs.length) fvs ftys rs
        Mf hMf cb ρ →
      fvs.length = Ds.length →
      WF cb (k t (fvs.map .fvar).toArray ((recFvs fvs rs).map .fvar).toArray) Q) :
    ∀ fuel t i fvs ftys rs Mf hMf cb ρ,
      CtorArgsInv cT X pre Mp pfvs params ps Ds R P F₀ t i fvs ftys rs Mf hMf cb ρ →
      WF cb (mkRecInfos.loopCtorArgs.loop stats k t i (fvs.map .fvar).toArray
        ((recFvs fvs rs).map .fvar).toArray fuel) Q := by
  intro fuel
  induction fuel with
  | zero => intros; exact .throw
  | succ fuel ih =>
  intro t i fvs ftys rs Mf hMf cb ρ hI
  have henv : cT.venv.WF := cT.envAt.tr.wf
  have hlenp : pfvs.length = params.length := hMpT.length_eq
  have hsize : stats.params.size = params.length := by
    rw [← Array.length_toList, hpar, List.length_map, hlenp]
  simp only [mkRecInfos.loopCtorArgs.loop]
  split
  · rename_i name dom body bi
    have har := hI.arity
    simp only [declareConstructors.arity, declareConstructors.arity_succ] at har
    split
    · -- a parameter
      rename_i param hparam
      have hi : i < params.length := by
        have := (Array.getElem?_eq_some_iff.1 hparam).1; omega
      have hip : i < pfvs.length := by omega
      have hpv : param = .fvar pfvs[i] := by
        have := Array.getElem?_eq_some_iff.1 hparam; rw [← this.2]
        simp [← Array.getElem_toList, hpar]
      subst hpv
      obtain ⟨-, rfl, Mi, hk, hMi, hMiT, htr, htele⟩ := hI.tr.resolve_right (by omega)
      have hft : ftys = [] := by
        have := hI.tele.length_eq; simpa [hlenp] using this
      have hrs : rs = [] := List.eq_nil_of_length_eq_zero hI.rs
      subst hft hrs
      have hpsi : i < ps.length := by omega
      rw [List.drop_eq_getElem_cons hpsi, List.drop_eq_getElem_cons hi] at htele
      simp only [List.drop_eq_getElem_cons hpsi, List.cons_append, VExpr.foralls] at htr
      cases htr with | forallE hdomT hbodyT hdom hbody => ?_
      cases htele with | cons hAB htele' => ?_
      -- the parameters up to the `i`th
      obtain ⟨hk', hT1⟩ := hMpT.dropN' (params.length - (i + 1)) (by omega)
      have hpi' : params.take (i + 1) = params.take i ++ [params[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      have hfi' : pfvs.take (i + 1) = pfvs.take i ++ [pfvs[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hip]; rfl
      rw [show params.length - (params.length - (i + 1)) = i + 1 by omega] at hT1
      have hT1₀ := hT1
      rw [hpi', hfi'] at hT1
      obtain ⟨name_i, ty_i, bi_i, m', hm', hm'T⟩ := hT1.snoc_inv
      have hm'eq : Mi = m' := by
        rw [← hMi, ← TypeChecker.MLCtx.dropN_congr
          (show params.length - (i + 1) + 1 = params.length - i by omega) (by omega) hk,
          ← TypeChecker.MLCtx.dropN_dropN Mp _ 1 hk' (by simp [hm', TypeChecker.MLCtx.length])]
        simp [hm', TypeChecker.MLCtx.dropN]
      subst hm'eq
      have hMfp : Mp = Mf := by
        obtain ⟨_, h⟩ := hI.base; simpa [TypeChecker.MLCtx.dropN] using h.symm
      subst hMfp
      have hwf' := TypeChecker.MLCtx.WF.dropN _ hk' hMf
      rw [hm'] at hwf'
      have hΔ' := hwf'.tr.wf
      have hΓ := hΔ'.1.toCtx
      obtain ⟨u, hpsS⟩ := hdomT
      have hbody' := TrExprS.inst_fvar_defeq henv hΔ' (hAB.of_l henv hΓ hpsS) hbody
      rw [← Lean.Expr.instantiate1_eq] at hbody'
      refine ih _ (i + 1) [] [] [] Mp hMf cb ρ
        ⟨hI.tele, hI.base, hI.sub, hI.pred, hI.fvars, hI.rs, hI.le, ?_, ?_, hI.fields⟩
      · rw [Lean.Expr.instantiate1_eq, declareConstructors.arity_instantiate1']; omega
      have hvl : (Mp.dropN (params.length - (i + 1)) hk').vlctx =
          (some (pfvs[i], ty_i.fvarsList), .vlam params[i]) :: Mi.vlctx := by rw [hm']; rfl
      rw [← hvl] at hbody'
      by_cases hi1 : i + 1 < params.length
      · exact .inl ⟨hi1, rfl, _, hk', rfl, hT1₀, hbody', by rw [hm']; exact htele'⟩
      · refine .inr ⟨by simp; omega, ?_⟩
        have : Mp.dropN (params.length - (i + 1)) hk' = Mp.dropN 0 (Nat.zero_le _) :=
          TypeChecker.MLCtx.dropN_congr (by omega) _ _
        rw [this] at hbody'
        have hpsd : ps.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
        simpa [hpsd, TypeChecker.MLCtx.dropN] using hbody'
    · -- a field
      rename_i hnone
      have hi : params.length ≤ i := by
        rw [← hsize]
        exact Decidable.byContradiction fun h => hnone _ (Array.getElem?_eq_getElem (by omega))
      obtain ⟨rfl, htr⟩ := hI.tr.resolve_left (by omega)
      have hn : fvs.length < Ds.length := by omega
      simp only [List.drop_eq_getElem_cons hn, VExpr.foralls] at htr
      cases htr with | forallE hdomT hbodyT hdom hbody => ?_
      have cs := cT.small Mf hMf
      have hΔ : (cT.small Mf hMf).vlctx.WF cT.venv cT.lparams.length := (cT.small Mf hMf).Δwf
      have hΓ := hΔ.toCtx
      refine WF.bind hI.sub.consumeTypeAnnotations fun dom_s hds => ?_
      obtain ⟨rfl, hok⟩ := hds
      obtain ⟨ty', hty, hdefty⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom
      have htyT : (cT.small Mf hMf).IsType ty' := hdomT.defeqU_l henv hΓ hdefty
      obtain ⟨wf, hsub'⟩ := hI.sub.push (name := name) (bi := bi) hty htyT
      refine WF.withLocalDecl (hI.sub.trExprS hty) (hI.sub.isType htyT) ?_
      have hskip := hI.sub.skip (name := name) (bi := bi) (hI.sub.trExprS hty) (hI.sub.isType htyT)
      refine WF.bind (Q := fun _ => True) ?_ fun r _ => ?_
      · unfold isRecArg
        refine WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
        exact isRecArg.loop.WF _ _ _ _ _ _ hskip hdom
      obtain ⟨u₀, hdomS⟩ := hdomT
      have hbody' := TrExprS.inst_fvar_defeq henv
        (Sub.pushS (cT.small Mf hMf) _ _ _ _ _ wf).Δwf (hdefty.of_l henv hΓ hdomS) hbody
      rw [← Lean.Expr.instantiate1_eq] at hbody'
      have harr : (List.map Expr.fvar fvs).toArray.push (.fvar ⟨cb.ngen.curr⟩) =
          (List.map Expr.fvar (fvs ++ [⟨cb.ngen.curr⟩])).toArray := by simp
      have harr' : (if r.isSome = true then
          ((recFvs fvs rs).map Expr.fvar).toArray.push (.fvar ⟨cb.ngen.curr⟩)
          else ((recFvs fvs rs).map Expr.fvar).toArray) =
          ((recFvs (fvs ++ [⟨cb.ngen.curr⟩]) (rs ++ [r.isSome])).map Expr.fvar).toArray := by
        rw [recFvs_snoc hI.rs]; cases r.isSome <;> simp
      rw [harr, harr']
      obtain ⟨hk, hbase⟩ := hI.base
      have hmtele := hI.tele.toCtx
      have hbase' : ∃ hk', (TypeChecker.MLCtx.vlam (FVarId.mk cb.ngen.curr) name
          dom.consumeTypeAnnotations' ty' bi Mf).dropN (fvs ++ [(FVarId.mk cb.ngen.curr)]).length hk' =
          Mp := by
        refine ⟨by simp [TypeChecker.MLCtx.length]; omega, ?_⟩
        rw [TypeChecker.MLCtx.dropN_congr (show (fvs ++ [(FVarId.mk cb.ngen.curr)]).length = fvs.length + 1
          by simp) _ (by simp [TypeChecker.MLCtx.length]; omega)]
        exact hbase
      refine ih _ _ _ (ftys ++ [ty']) _ _ wf _ _
        ⟨?_, hbase', hsub',
          hP _ _ _ _ _ _ _ hI.pred, ?_, by simp [hI.rs], by simp; omega, ?_, .inr ⟨by simp; omega, ?_⟩,
          fun j D fty hD hf => ?_⟩
      · simpa using hI.tele.vlam
      · show VLCtx.fvars (_ :: cb.mlctx.vlctx) = _
        simp [VLCtx.fvars_cons_some, hI.fvars]
      · rw [Lean.Expr.instantiate1_eq, declareConstructors.arity_instantiate1']; omega
      · have hbody'' : TrExprS cT.venv cT.lparams _ _ _ := hbody'
        simpa using hbody''
      · rcases Nat.lt_or_ge j ftys.length with hj | hj
        · rw [List.getElem?_append_left hj] at hf
          rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
          exact hI.fields j D fty hD hf
        · rw [List.getElem?_append_right hj] at hf
          obtain ⟨hj0, rfl⟩ : j - ftys.length = 0 ∧ ty' = fty := by
            cases h : j - ftys.length <;> simp_all
          have hjf : j = ftys.length := by omega
          subst hjf
          have hfl : ftys.length = fvs.length := by
            have := hI.tele.length_eq; simp [hlenp] at this; omega
          rw [hfl, List.getElem?_eq_getElem hn] at hD; cases hD
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          have : (cT.small Mf hMf).vlctx.toCtx = ftys.reverse ++ params.reverse := by
            show Mf.vlctx.toCtx = _; simp [hmtele]
          rw [← this]; exact hdefty
  · rename_i hnf
    have har := hI.arity
    have h0 : declareConstructors.arity 0 t = 0 := by
      cases t with
      | forallE => exact (hnf _ _ _ _ rfl).elim
      | _ => simp [declareConstructors.arity]
    rw [h0] at har
    obtain ⟨rfl, htr⟩ := hI.tr.resolve_left (by omega)
    exact H _ _ _ _ _ _ _ _ hI (by omega)

end AddInductive
end Lean4Lean

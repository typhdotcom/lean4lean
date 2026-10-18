import Lean4Lean.Verify.Environment.Syntactic

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

/-- `inferType'` of a local variable that misses the cache is its declared type. -/
theorem TypeChecker.Inner.inferType'_fvar {m : TypeChecker.Methods} {ctx : TypeChecker.Context}
    {s : TypeChecker.State} {fv : FVarId} {d : LocalDecl} {io : Bool}
    (hs : (bif io then s.inferTypeI else s.inferTypeC)[Expr.fvar fv]? = none)
    (h : ctx.lctx.find? fv = some d) :
    ∃ s', TypeChecker.Inner.inferType' (.fvar fv) io m ctx s = .ok (d.type, s') := by
  unfold TypeChecker.Inner.inferType'
  simp only [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange']
  simp [bind, ReaderT.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift, StateT.lift, readThe, MonadReaderOf.read,
    hs, TypeChecker.Inner.inferFVar, pure, ReaderT.pure, StateT.pure, Except.pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, TypeChecker.State.cached?,
    TypeChecker.withTaint, TypeChecker.Inner.inferTypeCore]
  have hr (st : TypeChecker.State) : (read : ReaderT TypeChecker.Context
      (StateT TypeChecker.State (Except Exception)) TypeChecker.Context) ctx st = .ok (ctx, st) :=
    rfl
  simp only [hr, h]
  exact ⟨_, rfl⟩

namespace AddInductive

theorem isRecArg.loop.WF [VEnv.Injective] {X : Name → Prop} {pre : List Name} {stats : InductiveStats} :
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
    obtain ⟨ty', hty, hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom (Lean.Expr.StripHeads.true _)
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

/-- Bound variables of the types `As`, the last on top, as a context. -/
def bvCtx (As : List VExpr) : VLCtx := (As.map fun A => ((none : Option (FVarId × List FVarId)),
  VLocalDecl.vlam A)).reverse

@[simp] theorem bvCtx_nil : bvCtx [] = [] := rfl

theorem bvCtx_snoc (As : List VExpr) (A : VExpr) :
    bvCtx (As ++ [A]) = (none, .vlam A) :: bvCtx As := by simp [bvCtx]

@[simp] theorem bvCtx_length (As : List VExpr) : (bvCtx As).length = As.length := by
  simp [bvCtx]

theorem VLCtx.Abstract.ofBV {Δ₀ : VLCtx} {v₀ : FVarId} {deps : List FVarId} {d₀ : VLocalDecl} :
    ∀ (Δbv : VLCtx), (∀ x ∈ Δbv, x.1 = none ∧ ∃ A, x.2 = .vlam A) →
      VLCtx.Abstract Δ₀ v₀ d₀ Δbv.length Δbv.length (Δbv ++ (some (v₀, deps), d₀) :: Δ₀)
        (Δbv ++ (none, d₀) :: Δ₀)
  | [], _ => .zero
  | (o, d) :: Δbv, h => by
    obtain ⟨rfl, A, rfl⟩ := h _ (.head _)
    exact .succ (d := .vlam A) (VLCtx.Abstract.ofBV Δbv fun x hx => h x (.tail _ hx))

/-- Abstracting the variables on top of a telescope context, under bound variables. -/
theorem _root_.Lean4Lean.TrExprS.abstractTop {env : VEnv} {Us : List Name} :
    ∀ (n : Nat) {m : TypeChecker.MLCtx} {fvs₁ xs : List FVarId} {tys₁ xtys : List VExpr},
    m.IsTele (fvs₁ ++ xs) (tys₁ ++ xtys) → xs.length = n → xtys.length = n →
    (fvs₁ ++ xs).Nodup → (hn : n ≤ m.length) →
    ∀ (Δbv : VLCtx), (∀ x ∈ Δbv, x.1 = none ∧ ∃ A, x.2 = .vlam A) →
    ∀ {e : Expr} {e' : VExpr}, TrExprS env Us (Δbv ++ m.vlctx) e e' →
      TrExprS env Us (Δbv ++ bvCtx xtys ++ (m.dropN n hn).vlctx) (e.abstractList xs Δbv.length) e'
  | 0, _, _, xs, _, xtys, _, h1, h2, _, _, Δbv, _, e, e', H => by
    obtain rfl := List.eq_nil_of_length_eq_zero h1
    obtain rfl := List.eq_nil_of_length_eq_zero h2
    simpa [TypeChecker.MLCtx.dropN] using H
  | n + 1, m, fvs₁, xs, tys₁, xtys, hT, h1, h2, hnd, hn, Δbv, hbv, e, e', H => by
    obtain ⟨xs, x, rfl⟩ : ∃ a b, xs = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat xs).resolve_left (by rintro rfl; simp at h1)
    obtain ⟨xtys, A, rfl⟩ : ∃ a b, xtys = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat xtys).resolve_left (by rintro rfl; simp at h2)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h1 h2
    rw [← List.append_assoc, ← List.append_assoc] at hT
    obtain ⟨name, ty, bi, m', rfl, hT'⟩ := hT.snoc_inv
    have W := VLCtx.Abstract.ofBV (Δ₀ := m'.vlctx) (v₀ := x) (deps := ty.fvarsList)
      (d₀ := .vlam A) Δbv hbv
    have H1 := H.abstract W
    have hbv' : ∀ y ∈ Δbv ++ [((none : Option (FVarId × List FVarId)), VLocalDecl.vlam A)],
        y.1 = none ∧ ∃ A, y.2 = .vlam A := by
      intro y hy; rcases List.mem_append.1 hy with hy | hy
      · exact hbv y hy
      · simp at hy; subst hy; exact ⟨rfl, _, rfl⟩
    have hnd' : (fvs₁ ++ xs).Nodup := by
      rw [← List.append_assoc] at hnd; exact (List.nodup_append.1 hnd).1
    have H2 := TrExprS.abstractTop n hT' h1 h2 hnd' (by simp [TypeChecker.MLCtx.length] at hn; omega)
      (Δbv ++ [(none, .vlam A)]) hbv' (by simpa using H1)
    have hx : x ∉ xs := by
      intro h; rw [← List.append_assoc] at hnd
      exact (List.nodup_append.1 hnd).2.2 _ (List.mem_append_right _ h) _ (.head _) rfl
    rw [Expr.abstractList_append]
    simp only [Expr.abstractList]
    rw [Expr.abstract1_abstractList hx]
    simpa [bvCtx_snoc, TypeChecker.MLCtx.dropN] using H2

theorem _root_.Lean.Expr.abstractRange_fvars (xs : List FVarId) (e : Expr) (i : Nat) :
    e.abstractRange i (xs.map Expr.fvar).toArray = e.abstract' (xs.take i) := by
  simp only [Expr.abstractRange_eq, List.extract_toArray, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero, ← List.map_take]
  rw [show ((List.take i xs).map Expr.fvar).toArray = ⟨(List.take i xs).map Expr.fvar⟩ from rfl,
    Expr.abstract_eq']

theorem _root_.Lean.Expr.abstract_fvars (xs : List FVarId) (e : Expr) :
    e.abstract (xs.map Expr.fvar).toArray = e.abstract' xs := by
  rw [show (xs.map Expr.fvar).toArray = ⟨xs.map Expr.fvar⟩ from rfl, Expr.abstract_eq']

/-- Each variable on top of a telescope context is declared at a type that, abstracted over the
variables before it, translates over them as bound variables. -/
theorem tele_binder_tr {env : VEnv} {Us : List Name} {Mx : TypeChecker.MLCtx}
    {kfvs xfvs : List FVarId} {ktys xtys : List VExpr}
    (hT : Mx.IsTele (kfvs ++ xfvs) (ktys ++ xtys)) (hwf : Mx.WF env Us)
    (hlen : xfvs.length = xtys.length) (hk : xfvs.length ≤ Mx.length) :
    ∀ i (h : i < xfvs.length), ∃ d, Mx.lctx.find? xfvs[i] = some d ∧
      TrExprS env Us (bvCtx (xtys.take i) ++ (Mx.dropN xfvs.length hk).vlctx)
        (d.type.abstractList (xfvs.take i)) (xtys[i]'(hlen ▸ h)) := by
  intro i hi
  have hkl := hT.length_eq
  simp only [List.length_append] at hkl
  obtain ⟨hj, hTj⟩ := hT.dropN' (xfvs.length - 1 - i) (by simp; omega)
  have e1 : ((kfvs ++ xfvs).take ((ktys ++ xtys).length - (xfvs.length - 1 - i))) =
      (kfvs ++ xfvs.take i) ++ [xfvs[i]] := by
    rw [List.take_append, List.take_of_length_le (by simp; omega),
      show (ktys ++ xtys).length - (xfvs.length - 1 - i) - kfvs.length = i + 1 by simp; omega,
      List.take_add_one, List.getElem?_eq_getElem hi, List.append_assoc]; rfl
  have e2 : ((ktys ++ xtys).take ((ktys ++ xtys).length - (xfvs.length - 1 - i))) =
      (ktys ++ xtys.take i) ++ [xtys[i]'(hlen ▸ hi)] := by
    rw [List.take_append, List.take_of_length_le (by simp; omega),
      show (ktys ++ xtys).length - (xfvs.length - 1 - i) - ktys.length = i + 1 by simp; omega,
      List.take_add_one, List.getElem?_eq_getElem (hlen ▸ hi), List.append_assoc]; rfl
  rw [e1, e2] at hTj
  obtain ⟨name, ty, bi, m', hm', hT'⟩ := hTj.snoc_inv
  obtain ⟨d, hd, hdty⟩ := hwf.find?_dropN_vlam _ hj hm'
  have hwfj := hwf.dropN _ hj
  rw [hm'] at hwfj
  obtain ⟨hwf', -, htr, -⟩ := hwfj
  have hnd : (kfvs ++ xfvs.take i).Nodup := by
    have := hwf'.tr.wf.fvars_nodup; rw [hT'.fvars] at this; exact List.nodup_reverse.1 this
  have hil : i ≤ m'.length := by have := hT'.length; simp at this ⊢; omega
  have H := TrExprS.abstractTop i hT' (by simp; omega) (by simp; omega) hnd hil [] nofun
    (by simpa using htr)
  refine ⟨d, hd, ?_⟩
  rw [hdty]
  have key : ∀ (c : TypeChecker.MLCtx) (_ : c = .vlam xfvs[i] name ty (xtys[i]'(hlen ▸ hi)) bi m')
      (hb : i + 1 ≤ c.length), c.dropN (i + 1) hb = m'.dropN i hil := by
    rintro c rfl hb; rfl
  have hb : i + 1 ≤ (Mx.dropN (xfvs.length - 1 - i) hj).length := by
    rw [TypeChecker.MLCtx.length_dropN]; have := hT.length; simp at this; omega
  have e3 : m'.dropN i hil = Mx.dropN xfvs.length hk := by
    rw [← key _ hm' hb, TypeChecker.MLCtx.dropN_dropN Mx _ _ hj hb (by omega)]
    exact TypeChecker.MLCtx.dropN_congr (by omega) _ _
  rw [← e3]
  simpa using H

/-- Free of the names `B`. -/
def BFree (B : Name → Prop) : Supp := ⟨fun _ => True, fun _ => True, fun n => ¬B n⟩

/-- What a computation over `cs` may mention, without the names `B`. -/
def Sub.suppB (X : Name → Prop) (cs : TypeChecker.VContext) (B : Name → Prop) : Supp :=
  ⟨(· ∈ cs.mlctx.vlctx.fvars), (· ∈ cs.lparams), fun n => ¬X n ∧ ¬B n⟩

theorem _root_.Lean.Literal.SuppIn.and {C₁ C₂ : Name → Prop} {l : Literal}
    (h₁ : l.SuppIn C₁) (h₂ : l.SuppIn C₂) : l.SuppIn fun n => C₁ n ∧ C₂ n := by
  cases l <;> simp_all [Literal.SuppIn]

theorem _root_.Lean.Expr.SuppIn.inter {F F' : FVarId → Prop} {L L' C₁ C₂ : Name → Prop} :
    ∀ {e : Expr}, e.SuppIn ⟨F, L, C₁⟩ → e.SuppIn ⟨F', L', C₂⟩ →
      e.SuppIn ⟨F, L, fun n => C₁ n ∧ C₂ n⟩ := by
  intro e
  induction e with
  | lit l => exact fun h₁ h₂ => Literal.SuppIn.and h₁ h₂
  | const _ _ => exact fun h₁ h₂ => ⟨⟨h₁.1, h₂.1⟩, h₁.2⟩
  | app _ _ ih1 ih2 | lam _ _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    exact fun h₁ h₂ => ⟨ih1 h₁.1 h₂.1, ih2 h₁.2 h₂.2⟩
  | letE _ _ _ _ _ ih1 ih2 ih3 =>
    exact fun h₁ h₂ => ⟨ih1 h₁.1 h₂.1, ih2 h₁.2.1 h₂.2.1, ih3 h₁.2.2 h₂.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact fun h₁ h₂ => ih h₁ h₂
  | _ => exact fun h₁ _ => h₁

theorem _root_.Lean.Expr.SuppIn.and {S : Supp} {B : Name → Prop} {e : Expr}
    (h₁ : e.SuppIn S) (h₂ : e.SuppIn (BFree B)) :
    e.SuppIn ⟨S.fv, S.lvl, fun n => S.const n ∧ ¬B n⟩ :=
  Expr.SuppIn.inter (F := S.fv) (L := S.lvl) h₁ h₂

theorem _root_.Lean.ConstantInfo.SuppIn.and {C₁ C₂ : Name → Prop} {ci : ConstantInfo}
    (h₁ : ci.SuppIn C₁) (h₂ : ci.SuppIn C₂) : ci.SuppIn fun n => C₁ n ∧ C₂ n := by
  have hS {e : Expr} (e₁ : e.SuppIn ⟨fun _ => False, (· ∈ ci.levelParams), C₁⟩)
      (e₂ : e.SuppIn ⟨fun _ => False, (· ∈ ci.levelParams), C₂⟩) :
      e.SuppIn ⟨fun _ => False, (· ∈ ci.levelParams), fun n => C₁ n ∧ C₂ n⟩ :=
    Expr.SuppIn.inter e₁ e₂
  obtain ⟨t₁, r₁⟩ := h₁
  obtain ⟨t₂, r₂⟩ := h₂
  refine ⟨hS t₁ t₂, ?_⟩
  cases ci <;> simp_all
  all_goals first
    | exact hS r₁ r₂
    | exact fun c hc => ⟨r₁ c hc, r₂ c hc⟩
    | exact ⟨⟨r₁.1, r₂.1⟩, fun r hr => hS (r₁.2 r hr) (r₂.2 r hr)⟩
    | skip

theorem _root_.Lean.Expr.SuppIn.consumeTypeAnnotations' {S : Supp} {e : Expr} (h : e.SuppIn S) :
    e.consumeTypeAnnotations'.SuppIn S := by
  induction e using Lean.Expr.consumeTypeAnnotations'.induct with
  | case1 _ A _ ih | case2 _ A _ ih | case3 _ A ih | case4 _ A ih =>
    unfold Lean.Expr.consumeTypeAnnotations'
    exact ih (by simp_all [Expr.SuppIn])
  | case5 e h1 h2 h3 h4 =>
    unfold Lean.Expr.consumeTypeAnnotations'
    split <;> first | exact h | (exfalso; simp_all)

theorem Sub.suppB_closed [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {B : Name → Prop}
    (hctx : ∀ fv d, cs.lctx.find? fv = some d →
      d.type.SuppIn (BFree B) ∧ d.value'.SuppIn (BFree B))
    (henvB : ∀ n ci, cs.env.find? n = some ci → ¬B n → ci.SuppIn fun m => ¬B m)
    (hprim : ∀ n, B n → Environment.primitives.contains n = false)
    (hdummy : ¬B `_inhabitedExprDummy) :
    (Sub.suppB X cs B).Closed cb.tc.toContext := by
  obtain ⟨hC, hE⟩ := H.suppClosed
  have p (n) (h : Environment.primitives.contains n = true) : ¬B n := fun hb => by
    simp [hprim n hb] at h
  refine ⟨fun fv d hfv hd => ?_, ⟨fun n ci h hn => ?_, fun op hop hn => ?_, fun op hop hn => ?_,
    ⟨hE.dummy, hdummy⟩⟩⟩
  · obtain ⟨h1, h2⟩ := hC fv d hfv hd
    have e := H.lctx fv hfv
    change cb.lctx.find? fv = some d at hd
    rw [hd] at e
    obtain ⟨d', hd', he⟩ : ∃ d', cs.lctx.find? fv = some d' ∧ d.erase = d'.erase := by
      cases h : cs.lctx.find? fv <;> rw [h] at e <;> simp_all
    obtain ⟨e1, e2⟩ := LocalDecl.erase_type he
    obtain ⟨b1, b2⟩ := hctx fv d' hd'
    exact ⟨h1.and (e1 ▸ b1), h2.and (e2 ▸ b2)⟩
  · have h1 := hE.find n ci h hn.1
    change cb.env.find? n = some ci at h
    have h2 := henvB n ci (by rw [← H.env n hn.1]; exact h) hn.2
    exact h1.and h2
  · obtain ⟨a, b, c⟩ := hE.nat op hop hn.1
    refine ⟨⟨a, p _ ?_⟩, ⟨b, p _ ?_⟩, ⟨c, p _ ?_⟩⟩ <;>
      simp +decide [Environment.primitives, NameSet.ofList, NameSet.contains]
  · obtain ⟨a, b⟩ := hE.bool op hop hn.1
    refine ⟨⟨a, p _ ?_⟩, ⟨b, p _ ?_⟩⟩ <;>
      simp +decide [Environment.primitives, NameSet.ofList, NameSet.contains]

/-- `whnf` of an expression free of the names `B`, in a context whose declarations are too, is
free of them. -/
theorem Sub.whnfB [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {B : Name → Prop}
    (hcl : (Sub.suppB X cs B).Closed cb.tc.toContext) {e : Expr} {E : VExpr}
    (he : cs.TrExprS e E) (hB : e.SuppIn (BFree B)) :
    WF cb (monadLift (TypeChecker.whnf e) : M Expr) fun e₁ =>
      e₁.SuppIn (Sub.suppB X cs B) ∧ cs.FVarsBelow e e₁ ∧ cs.TrExpr e₁ E :=
  whnf.WF_sim H.closedB H.closed (H.agree.mono ⟨fun _ => id, fun _ => id, fun _ h => h.1⟩)
    (fun _ => H.freshFor) H.ceiling.symm hcl
    (fun fv hfv => H.dom ((fvarsIn_iff.1 he.fvarsIn).1 fv hfv)) ((H.suppIn he).and hB) he

/-- Each binder domain along `e`'s spine of pis is allowed by `S`: what `isRec` checks of a
constructor's type. -/
def spineIn (S : Supp) : Expr → Prop
  | .forallE _ dom body _ => dom.SuppIn S ∧ spineIn S body
  | _ => True

theorem spineIn_instantiate1 {S : Supp} {x : FVarId} (hx : S.fv x) :
    ∀ {e : Expr} {d : Nat}, spineIn S e → spineIn S (e.instantiate1' (.fvar x) d)
  | .forallE .., _, h =>
    ⟨Expr.SuppIn.instantiate1 (a := .fvar x) hx h.1, spineIn_instantiate1 hx h.2⟩
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1']
    split; · trivial
    split <;> simp [Expr.liftLooseBVars', spineIn]
  | .mdata .., _, _ | .proj .., _, _ | .app .., _, _ | .lam .., _, _ | .letE .., _, _
  | .const .., _, _ | .sort _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .lit _, _, _ => by
    simp [Expr.instantiate1', spineIn]

theorem spineIn_inst1 {S : Supp} {x : FVarId} (hx : S.fv x) {e : Expr} (h : spineIn S e) :
    spineIn S (e.instantiate1 (.fvar x)) := by
  rw [Lean.Expr.instantiate1_eq]; exact spineIn_instantiate1 hx h

/-- `isRecArg` finds no type of the block in a type that mentions none, in a context whose
declarations mention none either: normalization does not introduce them, since no declaration
that could unfold mentions them. -/
theorem isRecArg.loop.noOcc [VEnv.Injective] {X : Name → Prop} {pre : List Name} {stats : InductiveStats}
    {B : Name → Prop}
    (hB : ∀ j, j < stats.indConsts.size → ∃ n us, stats.indConsts[j]! = .const n us ∧ B n)
    (hprim : ∀ n, B n → Environment.primitives.contains n = false)
    (hdummy : ¬B `_inhabitedExprDummy) :
    ∀ fuel (cs : TypeChecker.VContext) (cb : VContext) ρ (t : Expr) (T : VExpr),
      Sub X pre ρ cs cb → cs.TrExprS t T →
      (∀ fv d, cs.lctx.find? fv = some d →
        d.type.SuppIn (BFree B) ∧ d.value'.SuppIn (BFree B)) →
      (∀ n ci, cs.env.find? n = some ci → ¬B n → ci.SuppIn fun m => ¬B m) →
      t.SuppIn (BFree B) →
      AddInductive.WF cb (isRecArg.loop stats t fuel) (· = none) := by
  intro fuel
  induction fuel with
  | zero => intros; exact .throw
  | succ fuel ih =>
  intro cs cb ρ t T hsub ht hctx henvB htB
  simp only [isRecArg.loop]
  have hcl := hsub.suppB_closed hctx henvB hprim hdummy
  refine WF.bind (hsub.whnfB hcl ht htB) fun e₁ h₁ => ?_
  obtain ⟨hsupp, -, V₀, hS, -⟩ := h₁
  have hlow : Sub.suppB X cs B ≤ BFree B := ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ h => h.2⟩
  split
  · rename_i name dom body bi
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i dom' body'
    have henv := cs.Ewf
    have hΔ := cs.Δwf
    have hΓ := hΔ.toCtx
    refine WF.bind hsub.consumeTypeAnnotations fun dom_s hds => ?_
    obtain ⟨rfl, hok⟩ := hds
    obtain ⟨ty', hty, hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom (Lean.Expr.StripHeads.true _)
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
    have hdomB : dom.consumeTypeAnnotations'.SuppIn (BFree B) :=
      (hsupp.1.mono hlow).consumeTypeAnnotations'
    refine ih _ _ _ _ _ hsub' hinst (fun fv d hd => ?_) henvB
      (Expr.SuppIn.inst1 (a := .fvar _) trivial (hsupp.2.mono hlow))
    have hm := (cs.lctx_eq ▸ cs.mlctx_wf.tr).1
    change (cs.mlctx.lctx.mkLocalDecl ⟨cb.ngen.curr⟩ name dom.consumeTypeAnnotations' bi).find? fv =
      some d at hd
    rw [LocalContext.find?_mkLocalDecl (cs.lctx_eq ▸ hm) wf.2.1] at hd
    split at hd
    · cases hd; exact ⟨hdomB, trivial⟩
    · exact hctx fv d (cs.lctx_eq ▸ hd)
  · refine .pure ?_
    cases h : isValidIndApp? stats e₁ with
    | none => rfl
    | some j =>
      exfalso
      obtain ⟨hj, hv⟩ := isValidIndApp?_some h
      obtain ⟨hfn, -⟩ := isValidIndAppIdx_true hv
      obtain ⟨n, us, hI, hBn⟩ := hB j hj
      rw [hI] at hfn
      have hf := hsupp.getAppFn
      cases hfe : e₁.getAppFn <;> rw [hfe] at hfn hf <;>
        simp only [(· == ·), Expr.eqv_eq, Expr.eqv', reduceCtorEq, Bool.false_eq_true] at hfn
      rename_i n' us'
      simp only [Bool.and_eq_true] at hfn
      obtain rfl : n' = n := beq_iff_eq.mp hfn.1
      exact hf.1.2 hBn

/-- Instantiating a binder with a variable declared at a definitionally equal type. -/
theorem TrExprS.inst_fvar_defeq [VEnv.Injective] {env : VEnv} {Us : List Name} {Δ : VLCtx} {a : FVarId}
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

/-- A translation in the small context, in a view of the kernel's context that extends it. -/
theorem Sub.trExprS_to [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {N : TypeChecker.MLCtx} {ρ' : Lift}
    (W : VLCtx.FVLift' (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)).vlctx
      N.vlctx 0 ρ' 0) (hN : N.vlctx.WF cb.venv cb.lparams.length) {e : Expr} {E : VExpr}
    (he : cs.TrExprS e E) :
    TrExprS cb.venv cb.lparams N.vlctx e
      ((E.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ') := by
  have h1 := he.lparams_append H.pre_fresh
  rw [← TypeChecker.MLCtx.vlctx_instL, ← H.lparams] at h1
  exact (h1.mono H.venv).weakFV' cb.tc.Ewf.ordered W hN

theorem Sub.isDefEq_to [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {N : TypeChecker.MLCtx} {ρ' : Lift}
    (W : VLCtx.FVLift' (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)).vlctx
      N.vlctx 0 ρ' 0) {e₁ e₂ A : VExpr}
    (h : cs.venv.IsDefEq cs.lparams.length cs.vlctx.toCtx e₁ e₂ A) :
    cb.venv.IsDefEq cb.lparams.length N.vlctx.toCtx
      ((e₁.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ')
      ((e₂.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ')
      ((A.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ') := by
  have hls : ∀ l ∈ VLevel.shift pre.length cs.lparams.length, l.WF cb.lparams.length := by
    rw [H.lparams]; simpa using VLevel.shift_wf
  have h1 := (h.instL hls).mono H.venv
  have W' := W.toCtx
  rw [TypeChecker.MLCtx.vlctx_instL, VLCtx.instL_toCtx] at W'
  exact h1.weak' cb.tc.Ewf.ordered W'

theorem Sub.isType_to [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {N : TypeChecker.MLCtx} {ρ' : Lift}
    (W : VLCtx.FVLift' (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)).vlctx
      N.vlctx 0 ρ' 0) {A : VExpr} (h : cs.IsType A) :
    cb.venv.IsType cb.lparams.length N.vlctx.toCtx
      ((A.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ') :=
  let ⟨_, h⟩ := h; ⟨_, H.isDefEq_to W h⟩

theorem VContext.push_congr {c : VContext} {name : Name} {ty : Expr} {ty₁ ty₂ : VExpr}
    {bi : BinderInfo} (e : ty₁ = ty₂) (h1 h2 h1' h2') :
    c.push name ty ty₁ bi h1 h2 = c.push name ty ty₂ bi h1' h2' := by subst e; rfl

/-- Pushing a variable onto the small context, the kernel's, and a view `N` of the kernel's that
extends the small one. -/
theorem Sub.push_ext [VEnv.Injective] {X pre ρ cs cb} (H : Sub X pre ρ cs cb) {N : TypeChecker.MLCtx}
    {ρN ρ' : Lift} (E : Ext N cb ρN)
    (W : VLCtx.FVLift' (cs.mlctx.instL (VLevel.shift pre.length cs.lparams.length)).vlctx
      N.vlctx 0 ρ' 0) {name : Name} {ty : Expr} {Ty : VExpr} {bi : BinderInfo}
    (hty : cs.TrExprS ty Ty) (hT : cs.IsType Ty) :
    ∃ wf, Sub X pre ρ.cons (Sub.pushS cs ⟨cb.ngen.curr⟩ name ty Ty bi wf)
      (cb.push name ty (Sub.up pre ρ cs Ty) bi (H.trExprS hty) (H.isType hT)) ∧
    Ext (.vlam ⟨cb.ngen.curr⟩ name ty
        ((Ty.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ') bi N)
      (cb.push name ty (Sub.up pre ρ cs Ty) bi (H.trExprS hty) (H.isType hT)) ρN.cons ∧
    VLCtx.FVLift' ((Sub.pushS cs ⟨cb.ngen.curr⟩ name ty Ty bi wf).mlctx.instL
        (VLevel.shift pre.length cs.lparams.length)).vlctx
      (TypeChecker.MLCtx.vlam ⟨cb.ngen.curr⟩ name ty
        ((Ty.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ') bi N).vlctx
      0 (ρ'.consN 1) 0 := by
  obtain ⟨wf, hsub⟩ := H.push (name := name) (bi := bi) hty hT
  have htyN := H.trExprS_to W E.wf.tr.wf hty
  have hTN := H.isType_to W hT
  have he : ((Ty.instL (VLevel.shift pre.length cs.lparams.length)).lift' ρ').lift' ρN =
      Sub.up pre ρ cs Ty :=
    TrExprS.unique (TrExprS.IsUnique.all _) (E.trExprS htyN) (H.trExprS hty)
  refine ⟨wf, hsub, ?_, ?_⟩
  · have := E.push (name := name) (bi := bi) htyN hTN
    rwa [VContext.push_congr he (E.trExprS htyN) (E.isType hTN) (H.trExprS hty) (H.isType hT)]
      at this
  · refine W.cons_fvar _ (.vlam _) (fun x hx => ?_)
    have := (fvarsIn_iff.1 hty.fvarsIn).1 x hx
    rw [TypeChecker.MLCtx.vlctx_instL]
    simpa [VLCtx.instL_eq_map, VLCtx.fvars] using this

/-- What `loopCtorArgs` keeps, having read `i` binders of a constructor type that translates to
`.foralls (ps ++ Ds) R`, its parameters `ps` agreeing with the block's `params`. While reading the
parameters it instantiates them with the block's, and the rest of the type translates in the
parameters read so far. Then it opens each field `fvs` at the translation `ftys` of its declared
domain stripped of annotations, flagging in `rs` those `isRecArg` sees as recursive: the small
context `Mf` is the parameters and those fields, and the rest of the type translates there. -/
structure CtorArgsInv (cT : VContext) (X : Name → Prop) (pre : List Name)
    (Mp : TypeChecker.MLCtx) (pfvs : List FVarId) (params ps Ds : List VExpr) (R : VExpr)
    (N₀ : TypeChecker.MLCtx) (N₀fvs : List FVarId) (N₀tys : List VExpr) (ρ₀ : Lift)
    (P : VContext → Prop) (F₀ : List FVarId) (B : Name → Prop) (Z : Prop) (t₀ t : Expr) (i : Nat)
    (fvs : List FVarId) (ftys : List VExpr) (rs : List Bool) (Mf : TypeChecker.MLCtx)
    (hMf : Mf.WF cT.venv cT.lparams) (cb : VContext) (ρ : Lift) : Prop where
  tele : Mf.IsTele (pfvs ++ fvs) (params ++ ftys)
  base : ∃ hk, Mf.dropN fvs.length hk = Mp
  sub : Sub X pre ρ (cT.small Mf hMf) cb
  pred : P cb
  fvars : cb.mlctx.vlctx.fvars = fvs.reverse ++ F₀
  rsLen : rs.length = fvs.length
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
  within : ∀ (j : Nat) (D fty : VExpr), Ds[j]? = some D → ftys[j]? = some fty →
    D.StripsToBy (fun n => (∃ v, cT.env.find? n = some (.defnInfo v)) ∧ cT.venv.AnnotDef n) fty
  /-- The view `N₀` of the kernel's context, with the fields pushed. -/
  comp : ∃ N ρN, Ext N cb ρN ∧
    VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx N.vlctx 0
      (ρ₀.consN fvs.length) 0 ∧
    N.IsTele (N₀fvs ++ fvs) (N₀tys ++ ftys.zipIdx.map fun (A, j) =>
      (A.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ₀.consN j)) ∧
    ∃ hk, N.dropN fvs.length hk = N₀
  /-- When the constructor's binder domains do not mention the names `B`, neither does the rest
  of its type nor any declaration of the small context, and no field is recursive. -/
  free : Z → spineIn (BFree B) t ∧ (∀ r ∈ rs, r = false) ∧
    ∀ fv d, Mf.lctx.find? fv = some d → d.type.SuppIn (BFree B) ∧ d.value'.SuppIn (BFree B)
  /-- The constructor's type, before anything is read. -/
  start : i = 0 → t = t₀
  /-- Without parameters, a first binder whose domain carries no annotation is the first field's
  declared type, and its translation the field's. -/
  first : params.length = 0 → ∀ nm D b bi, t₀ = .forallE nm D b bi →
    D.consumeTypeAnnotations' = D → ∀ h : 0 < fvs.length,
      (∃ dk, Mf.lctx.find? (fvs[0]'h) = some dk ∧ dk.type = D) ∧ ftys[0]? = Ds[0]?
  /-- The annotations on the binders read so far, counted. -/
  strips : t.domStrips = t₀.domStrips.drop i
  /-- Each field's view is its declared domain with as many annotations stripped as the
  constructor's type has on that binder. -/
  views : ∀ (j : Nat) (D fty : VExpr), Ds[j]? = some D → ftys[j]? = some fty →
    fty = D.stripN ((t₀.domStrips.drop params.length)[j]?.getD 0)

theorem loopCtorArgs.loop.WF [VEnv.Injective] {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {pfvs : List FVarId} {params : List VExpr}
    (hMpT : Mp.IsTele pfvs params) {stats : InductiveStats}
    (hpar : stats.params.toList = pfvs.map .fvar) {ps Ds : List VExpr} {R : VExpr}
    (hps : ps.length = params.length) {N₀ : TypeChecker.MLCtx} {N₀fvs : List FVarId}
    {N₀tys : List VExpr} {ρ₀ : Lift} {F₀ : List FVarId} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {B : Name → Prop} {Z : Prop} {t₀ : Expr}
    (hB : ∀ j, j < stats.indConsts.size → ∃ n us, stats.indConsts[j]! = .const n us ∧ B n)
    (hprim : Z → 0 < Ds.length → ∀ n, B n → Environment.primitives.contains n = false)
    (hdummy : ¬B `_inhabitedExprDummy)
    (henvB : Z → 0 < Ds.length →
      ∀ n ci, cT.env.find? n = some ci → ¬B n → ci.SuppIn fun m => ¬B m)
    {k : Expr → Array Expr → Array Expr → M α} {Q}
    (H : ∀ t fvs ftys rs Mf hMf cb ρ,
      CtorArgsInv cT X pre Mp pfvs params ps Ds R N₀ N₀fvs N₀tys ρ₀ P F₀ B Z t₀ t (params.length + fvs.length) fvs ftys rs
        Mf hMf cb ρ →
      fvs.length = Ds.length →
      WF cb (k t (fvs.map .fvar).toArray ((recFvs fvs rs).map .fvar).toArray) Q) :
    ∀ fuel t i fvs ftys rs Mf hMf cb ρ,
      CtorArgsInv cT X pre Mp pfvs params ps Ds R N₀ N₀fvs N₀tys ρ₀ P F₀ B Z t₀ t i fvs ftys rs Mf hMf cb ρ →
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
      have hrs : rs = [] := List.eq_nil_of_length_eq_zero hI.rsLen
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
        ⟨hI.tele, hI.base, hI.sub, hI.pred, hI.fvars, hI.rsLen, hI.le, ?_, ?_, hI.fields, hI.within,
          hI.comp,
          fun hz => let ⟨h1, h2, h3⟩ := hI.free hz; ⟨spineIn_inst1 trivial h1.2, h2, h3⟩,
          fun h => absurd h (by omega), fun hp0 => absurd hi (by omega), by
            have h := congrArg List.tail hI.strips
            simp only [Lean.Expr.domStrips, List.tail_cons, List.tail_drop] at h
            rw [Lean.Expr.instantiate1_eq, Lean.Expr.domStrips_instantiate1']; exact h,
          hI.views⟩
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
      refine WF.bind hI.sub.consumeTypeAnnotations_heads fun dom_s hds => ?_
      obtain ⟨rfl, hok, hheads⟩ := hds
      obtain ⟨ty', hty, hdefty, hwty⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom hheads
      have htyT : (cT.small Mf hMf).IsType ty' := hdomT.defeqU_l henv hΓ hdefty
      obtain ⟨N, ρN, hE, hW, hNT, hNk, hNb⟩ := hI.comp
      obtain ⟨wf, hsub', hE', hW'⟩ := hI.sub.push_ext (name := name) (bi := bi) hE hW hty htyT
      refine WF.withLocalDecl (hI.sub.trExprS hty) (hI.sub.isType htyT) ?_
      have hskip := hI.sub.skip (name := name) (bi := bi) (hI.sub.trExprS hty) (hI.sub.isType htyT)
      refine WF.bind (Q := fun r => Z → r = none) ?_ fun r hrZ => ?_
      · by_cases hz : Z
        · obtain ⟨hsp, -, hctx⟩ := hI.free hz
          unfold isRecArg
          refine WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
          exact (isRecArg.loop.noOcc hB (hprim hz (by omega)) hdummy _ _ _ _ _ _ hskip hdom
            (fun fv d hd => hctx fv d hd) (henvB hz (by omega)) hsp.1).mono fun r h _ => h
        · exact fun r _ h => (hz h).elim
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
        rw [recFvs_snoc hI.rsLen]; cases r.isSome <;> simp
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
          hP _ _ _ _ _ _ _ hI.pred, ?_, by simp [hI.rsLen], by simp; omega, ?_, .inr ⟨by simp; omega, ?_⟩,
          fun j D fty hD hf => ?_, fun j D fty hD hf => ?_,
          ⟨_, _, hE', by rw [List.length_append, List.length_singleton]; exact hW',
          ?_, by simp [TypeChecker.MLCtx.length]; omega, ?_⟩, ?_, fun h => absurd h (by omega), ?_,
          ?_, ?_⟩
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
      · rcases Nat.lt_or_ge j ftys.length with hj | hj
        · rw [List.getElem?_append_left hj] at hf
          exact hI.within j D fty hD hf
        · rw [List.getElem?_append_right hj] at hf
          obtain ⟨hj0, rfl⟩ : j - ftys.length = 0 ∧ ty' = fty := by
            cases h : j - ftys.length <;> simp_all
          have hjf : j = ftys.length := by omega
          subst hjf
          have hfl : ftys.length = fvs.length := by
            have := hI.tele.length_eq; simp [hlenp] at this; omega
          rw [hfl, List.getElem?_eq_getElem hn] at hD; cases hD
          exact hwty
      · have hfl : ftys.length = fvs.length := by
          have := hI.tele.length_eq; simp [hlenp] at this; omega
        have := hNT.vlam (fv := ⟨cb.ngen.curr⟩) (name := name) (ty := dom.consumeTypeAnnotations')
          (bi := bi) (ty' := (ty'.instL (VLevel.shift pre.length cT.lparams.length)).lift'
            (ρ₀.consN fvs.length))
        have e : (cT.small Mf hMf).lparams = cT.lparams := rfl
        rw [e]; simpa [List.zipIdx_append, hfl] using this
      · rw [TypeChecker.MLCtx.dropN_congr (show (fvs ++ [FVarId.mk cb.ngen.curr]).length =
          fvs.length + 1 by simp) _ (by simp [TypeChecker.MLCtx.length]; omega)]
        exact hNb
      · intro hz
        obtain ⟨hsp, hrs, hctx⟩ := hI.free hz
        refine ⟨spineIn_inst1 trivial hsp.2, fun x hx => ?_, fun fv d hd => ?_⟩
        · rcases List.mem_append.1 hx with hx | hx
          · exact hrs x hx
          · simp only [List.mem_singleton] at hx; subst hx; rw [hrZ hz]; rfl
        · change (Mf.lctx.mkLocalDecl _ name dom.consumeTypeAnnotations' bi).find? fv = some d at hd
          rw [LocalContext.find?_mkLocalDecl hMf.tr.1 wf.2.1] at hd
          split at hd
          · cases hd; exact ⟨hsp.1.consumeTypeAnnotations', trivial⟩
          · exact hctx fv d hd
      · intro hp0 nm D b bi' ht₀ hD h
        have hfl : ftys.length = fvs.length := by
          have := hI.tele.length_eq; simp [hlenp] at this; omega
        rcases Nat.eq_zero_or_pos fvs.length with hf0 | hf0
        · obtain rfl : fvs = [] := List.eq_nil_of_length_eq_zero hf0
          obtain rfl : ftys = [] := List.eq_nil_of_length_eq_zero (by omega)
          have ht := hI.start (by omega)
          rw [ht₀] at ht
          obtain ⟨rfl, rfl, rfl, rfl⟩ : name = nm ∧ dom = D ∧ body = b ∧ bi = bi' := by
            injection ht with h1 h2 h3 h4; exact ⟨h1, h2, h3, h4⟩
          refine ⟨⟨.cdecl Mf.lctx.decls.size ⟨cb.ngen.curr⟩ name dom.consumeTypeAnnotations' bi
            .default, ?_, hD⟩, ?_⟩
          · show (Mf.lctx.mkLocalDecl _ _ _ _).find? _ = _
            rw [LocalContext.find?_mkLocalDecl hMf.tr.1 wf.2.1, if_pos (by simp)]
          · rw [hD] at hty
            obtain rfl := TrExprS.unique (TrExprS.IsUnique.all _) hty hdom
            simp [List.getElem?_eq_getElem hn]
        · obtain ⟨⟨dk, hdk, hdkt⟩, hft⟩ := hI.first hp0 nm D b bi' ht₀ hD hf0
          refine ⟨⟨dk, ?_, hdkt⟩, ?_⟩
          · show (Mf.lctx.mkLocalDecl _ _ _ _).find? _ = _
            rw [LocalContext.find?_mkLocalDecl hMf.tr.1 wf.2.1, if_neg, List.getElem_append_left hf0]
            · exact hdk
            · simp only [beq_iff_eq]
              intro he
              have h2 : Mf.lctx.find? ⟨cb.ngen.curr⟩ = none := wf.2.1
              rw [he] at h2
              rw [List.getElem_append_left hf0, hdk] at h2; cases h2
          · rw [List.getElem?_append_left (by omega)]; exact hft
      · have h := congrArg List.tail hI.strips
        simp only [Lean.Expr.domStrips, List.tail_cons, List.tail_drop] at h
        rw [Lean.Expr.instantiate1_eq, Lean.Expr.domStrips_instantiate1']; exact h
      · intro j D fty hD hf
        rcases Nat.lt_or_ge j ftys.length with hj | hj
        · rw [List.getElem?_append_left hj] at hf
          exact hI.views j D fty hD hf
        · rw [List.getElem?_append_right hj] at hf
          obtain ⟨hj0, rfl⟩ : j - ftys.length = 0 ∧ ty' = fty := by
            cases h : j - ftys.length <;> simp_all
          have hfl : ftys.length = fvs.length := by
            have := hI.tele.length_eq; simp [hlenp] at this; omega
          have hjf : j = fvs.length := by omega
          subst hjf
          rw [List.getElem?_eq_getElem hn] at hD; cases hD
          have hn₀ : dom.annStrips = (t₀.domStrips.drop params.length)[fvs.length]?.getD 0 := by
            have h := congrArg List.head? hI.strips
            simp only [Lean.Expr.domStrips, List.head?_cons, List.head?_drop] at h
            rw [List.getElem?_drop, ← h]; rfl
          rw [← hn₀]
          exact TrExprS.unique (TrExprS.IsUnique.all _) hty hdom.consumeTypeAnnotations'_stripN
  · rename_i hnf
    have har := hI.arity
    have h0 : declareConstructors.arity 0 t = 0 := by
      cases t with
      | forallE => exact (hnf _ _ _ _ rfl).elim
      | _ => simp [declareConstructors.arity]
    rw [h0] at har
    obtain ⟨rfl, htr⟩ := hI.tr.resolve_left (by omega)
    exact H _ _ _ _ _ _ _ _ hI (by omega)

/-- `inferType` of a local variable, from a fresh state, is its declared type. -/
theorem inferType_fvar {c : VContext} {fv : FVarId} {d : LocalDecl} {io : Bool}
    (h : c.lctx.find? fv = some d) :
    WF c (monadLift (TypeChecker.inferType (.fvar fv) io) : M Expr) (· = d.type) := by
  intro a eq
  change ((TypeChecker.Methods.withFuel c.fuel.recDepth).inferType (.fvar fv) io
    { env := c.env, lctx := c.lctx, safety := c.safety, lparams := c.lparams, fuel := c.fuel }
    {}).map Prod.fst = .ok a at eq
  generalize c.fuel.recDepth = n at eq
  cases n with
  | zero => cases eq
  | succ n =>
    have hs0 : (bif io then ({} : TypeChecker.State).inferTypeI
        else ({} : TypeChecker.State).inferTypeC)[Expr.fvar fv]? = none := by cases io <;> simp
    let ctx₀ : TypeChecker.Context :=
      { env := c.env, lctx := c.lctx, safety := c.safety, lparams := c.lparams, fuel := c.fuel }
    obtain ⟨s', hs'⟩ := TypeChecker.Inner.inferType'_fvar (m := .withFuel n) (ctx := ctx₀) hs0 h
    change (TypeChecker.Inner.inferType' (.fvar fv) io (.withFuel n) _ {}).map Prod.fst = _ at eq
    rw [hs'] at eq; cases eq; rfl

/-- The part of a small context below its top `n` variables. -/
theorem Sub.dropN {X : Name → Prop} {pre : List Name} {ρ : Lift} {c : VContext}
    {M : TypeChecker.MLCtx} {hM : M.WF c.venv c.lparams} {cb : VContext}
    (H : Sub X pre ρ (c.small M hM) cb) (n : Nat) (hn : n ≤ M.length) :
    ∃ ρ', Sub X pre ρ' (c.small (M.dropN n hn) (hM.dropN n hn)) cb := by
  obtain ⟨ρ₁, W₁⟩ := TypeChecker.MLCtx.fvlift_dropN
    (M.instL (VLevel.shift pre.length c.lparams.length)) n
    (by rw [TypeChecker.MLCtx.length_instL]; exact hn)
  rw [TypeChecker.MLCtx.dropN_instL _ _ _ hn] at W₁
  refine ⟨ρ₁.comp ρ, { H with
    lift := W₁.comp H.lift
    lctx := (fun fv hfv => ?_)
    notKernel := (fun fv hfv => H.notKernel fv (TypeChecker.MLCtx.dropN_fvars_subset n hn hfv)) }⟩
  have hfv' := TypeChecker.MLCtx.dropN_fvars_subset n hn hfv
  refine (H.lctx fv hfv').trans ?_
  show ((M.lctx.find? fv).map _) = ((M.dropN n hn).lctx.find? fv).map _
  rw [hM.find?_dropN n hn hfv]

/-- The part of a small context below its top `n` variables, named. -/
theorem Sub.dropN' {X : Name → Prop} {pre : List Name} {ρ : Lift} {c : VContext}
    {M : TypeChecker.MLCtx} {hM : M.WF c.venv c.lparams} {cb : VContext}
    (H : Sub X pre ρ (c.small M hM) cb) (n : Nat) (hn : n ≤ M.length) {M' : TypeChecker.MLCtx}
    (hM' : M'.WF c.venv c.lparams) (e : M.dropN n hn = M') :
    ∃ ρ', Sub X pre ρ' (c.small M' hM') cb := by
  subst e; exact H.dropN n hn


theorem _root_.List.Forall₂.drop' {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (n : Nat), List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.drop n) (l₂.drop n)
  | _, _, 0, h => h
  | [], [], _ + 1, .nil => .nil
  | _ :: _, _ :: _, n + 1, .cons _ h => List.Forall₂.drop' n h

/-- The expression `isValidIndAppIdx` accepts translates to the `j`th type at the parameters, the
variables `k` binders up, and at the translations of its other arguments. -/
theorem validIndApp_shape {venv : VEnv} {Us : List Name} (hUs : Us.Nodup)
    {stats : InductiveStats} {types : List InductiveType} {pfvs : List FVarId}
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = Us.map .param)
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    {Δ : VLCtx} {k : Nat} (hΔ : ParamsAt Δ k pfvs)
    {e : Expr} {E : VExpr} {j : Nat} (hval : isValidIndAppIdx stats e j = true)
    (hj : j < types.length) (hS : TrExprS venv Us Δ e E) :
    ∃ is, is.length + pfvs.length = e.getAppArgsList.length ∧
      e.getAppArgsList.length = stats.params.size + stats.nindices[j]! ∧
      E = .appN (.const types[j].name (VLevel.params Us.length)) (VExpr.bvars pfvs.length k ++ is) ∧
      List.Forall₂ (TrExprS venv Us Δ) (e.getAppArgsList.drop pfvs.length) is := by
  obtain ⟨hfvwf, hentries, hposΔ⟩ := hΔ
  obtain ⟨hI, hsz, hpa, -⟩ := isValidIndAppIdx_true hval
  have hlenp : stats.params.size = pfvs.length := by
    rw [← Array.length_toList, hpar, List.length_map]
  have hjs : j < stats.indConsts.size := by rw [← Array.length_toList, hind]; simpa
  have hindj : stats.indConsts[j]! = .const types[j].name (Us.map .param) := by
    rw [getElem!_pos stats.indConsts j hjs, ← Array.getElem_toList]
    simp [hind, hlev]
  rw [hindj] at hI
  have hfn : e.getAppFn = .const types[j].name (Us.map .param) :=
    Expr.eqv'_const (by rw [← Expr.eqv_eq]; exact hI)
  have hargs : e.getAppArgs = e.getAppArgsList.toArray := Expr.getAppArgs_eq
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at hS
  obtain ⟨F', as', rfl, hF, has⟩ := TrExprS.mkAppList_inv hS
  cases hF with | const _ hus _ => ?_
  rw [VLevel.mapM_ofLevel_params hUs] at hus; cases hus
  have hlenA : e.getAppArgsList.length = stats.params.size + stats.nindices[j]! := by
    rw [← hsz, hargs]; simp
  have hlen' : as'.length = e.getAppArgsList.length := (Lean4Lean.List.Forall₂.length_eq has).symm
  have hparam : ∀ i (hi : i < pfvs.length), as'[i]? = some (.bvar (pfvs.length - 1 - i + k)) := by
    intro i hi
    have hka : i < e.getAppArgsList.length := by omega
    have hpk : stats.params[i]! = .fvar (pfvs[i]'hi) := by
      rw [getElem!_pos stats.params i (by rw [hlenp]; exact hi), ← Array.getElem_toList]
      simp [hpar]
    have h1 := hpa i (by rw [hlenp]; exact hi)
    rw [hpk] at h1
    replace h1 : (Expr.fvar (pfvs[i]'hi) == e.getAppArgs[i]!) = true := by simpa [bne] using h1
    have h2 : e.getAppArgsList[i] = .fvar (pfvs[i]'hi) := by
      have := Expr.eqv'_fvar (by rw [← Expr.eqv_eq]; exact h1)
      rw [hargs] at this; simpa [List.getElem?_eq_getElem hka] using this
    obtain ⟨a', ha', htr⟩ := List.Forall₂.getElem?_l has (List.getElem?_eq_getElem hka)
    rw [ha']
    rw [h2] at htr
    cases htr with | fvar hf => ?_
    have hpos : Δ.fvars[pfvs.length - 1 - i + k]? = some (pfvs[i]'hi) := by
      have := hposΔ i hi; rwa [Nat.add_comm] at this
    obtain ⟨_, hf'⟩ := VLCtx.find?_fvar_index hfvwf hentries hpos
    rw [hf'] at hf; cases hf; rfl
  refine ⟨as'.drop pfvs.length, by simp; omega, hlenA, ?_, List.Forall₂.drop' _ has⟩
  conv => lhs; rw [← List.take_append_drop pfvs.length as']
  congr 2
  refine List.ext_getElem? fun m => ?_
  by_cases hm : m < pfvs.length
  · rw [List.getElem?_take, if_pos hm, hparam m hm]
    simp [VExpr.bvars, hm]
  · rw [List.getElem?_take, if_neg hm]
    simp [VExpr.bvars]; omega

/-- What `loopUArgs` keeps about the type `uiTy` of a recursive field, declared at `fty` over the
parameters and the fields before it (`Mk`, a telescope of `ktys`), having opened its binders `xfvs`
at the translations `xtys` of their stripped domains: `uiTy` translates to `V` in the small context
`Mx` of `Mk` and those binders, and the field's type is the binders over `V`. -/
structure UArgsInv (cT : VContext) (X : Name → Prop) (pre : List Name) (Mk : TypeChecker.MLCtx)
    (kfvs : List FVarId) (ktys : List VExpr) (fty : VExpr)
    (N₀ : TypeChecker.MLCtx) (N₀fvs : List FVarId) (N₀tys : List VExpr) (ρ₀ : Lift)
    (P : VContext → Prop)
    (F₀ : List FVarId) (Z : Prop) (uiTy : Expr) (xfvs : List FVarId) (xtys : List VExpr)
    (V : VExpr) (Mx : TypeChecker.MLCtx) (hMx : Mx.WF cT.venv cT.lparams) (cb : VContext)
    (ρ : Lift) : Prop where
  tele : Mx.IsTele (kfvs ++ xfvs) (ktys ++ xtys)
  len : xtys.length = xfvs.length
  base : ∃ hk, Mx.dropN xfvs.length hk = Mk
  sub : Sub X pre ρ (cT.small Mx hMx) cb
  pred : P cb
  fvars : cb.mlctx.vlctx.fvars = xfvs.reverse ++ F₀
  tr : (cT.small Mx hMx).TrExpr uiTy V
  isType : (cT.small Mx hMx).IsType V
  rel : cT.venv.IsDefEqU cT.lparams.length ktys.reverse fty (.foralls xtys V)
  /-- The view `N₀` of the kernel's context, with the binders pushed. -/
  comp : ∃ N ρN, Ext N cb ρN ∧
    VLCtx.FVLift' (Mx.instL (VLevel.shift pre.length cT.lparams.length)).vlctx N.vlctx 0
      (ρ₀.consN xfvs.length) 0 ∧
    N.IsTele (N₀fvs ++ xfvs) (N₀tys ++ xtys.zipIdx.map fun (A, j) =>
      (A.instL (VLevel.shift pre.length cT.lparams.length)).lift' (ρ₀.consN j)) ∧
    ∃ hk, N.dropN xfvs.length hk = N₀
  /-- When `Z`, the normalized type opened no binder: it is not a pi. -/
  stop : Z → xfvs = [] ∧ ∀ name dom body bi, uiTy ≠ .forallE name dom body bi

theorem loopUArgs.loop.WF [VEnv.Injective] {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mk : TypeChecker.MLCtx} {kfvs : List FVarId} {ktys : List VExpr} {fty : VExpr}
    {N₀ : TypeChecker.MLCtx} {N₀fvs : List FVarId} {N₀tys : List VExpr} {ρ₀ : Lift}
    {F₀ : List FVarId} {P : VContext → Prop} {Z : Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {k : Expr → Array Expr → M α} {Q}
    (H : ∀ uiTy xfvs xtys V Mx hMx cb ρ,
      UArgsInv cT X pre Mk kfvs ktys fty N₀ N₀fvs N₀tys ρ₀ P F₀ Z uiTy xfvs xtys V Mx hMx cb ρ →
      (∀ name dom body bi, uiTy ≠ .forallE name dom body bi) →
      WF cb (k uiTy (xfvs.map .fvar).toArray) Q) :
    ∀ fuel uiTy xfvs xtys V Mx hMx cb ρ,
      UArgsInv cT X pre Mk kfvs ktys fty N₀ N₀fvs N₀tys ρ₀ P F₀ Z uiTy xfvs xtys V Mx hMx cb ρ →
      WF cb (mkRecInfos.loopUArgs.loop k uiTy (xfvs.map .fvar).toArray fuel) Q := by
  intro fuel
  induction fuel with
  | zero => intros; exact .throw
  | succ fuel ih =>
  intro uiTy xfvs xtys V Mx hMx cb ρ hI
  have henv : cT.venv.WF := cT.envAt.tr.wf
  simp only [mkRecInfos.loopUArgs.loop]
  split
  · rename_i name dom body bi
    obtain ⟨V₀, hS, hdef⟩ := hI.tr
    cases hS with | forallE hdomT hbodyT hdom hbody => ?_
    rename_i A B
    have hΔ : (cT.small Mx hMx).vlctx.WF cT.venv cT.lparams.length := (cT.small Mx hMx).Δwf
    have hΓ := hΔ.toCtx
    have hctx : (cT.small Mx hMx).vlctx.toCtx = xtys.reverse ++ ktys.reverse := by
      show Mx.vlctx.toCtx = _; simp [hI.tele.toCtx]
    refine WF.bind hI.sub.consumeTypeAnnotations fun dom_s hds => ?_
    obtain ⟨rfl, hok⟩ := hds
    obtain ⟨ty', hty, hdefty, -⟩ := TrExprS.consumeTypeAnnotations' henv hΔ hok hdom (Lean.Expr.StripHeads.true _)
    have htyT : (cT.small Mx hMx).IsType ty' := hdomT.defeqU_l henv hΓ hdefty
    obtain ⟨N, ρN, hE, hW, hNT, hNk, hNb⟩ := hI.comp
    obtain ⟨wf, hsub', hE', hW'⟩ := hI.sub.push_ext (name := name) (bi := bi) hE hW hty htyT
    refine WF.withLocalDecl (hI.sub.trExprS hty) (hI.sub.isType htyT) ?_
    obtain ⟨u₀, hdomS⟩ := hdomT
    have hAty := hdefty.of_l henv hΓ hdomS
    have hbody' := TrExprS.inst_fvar_defeq henv
      (Sub.pushS (cT.small Mx hMx) _ _ _ _ _ wf).Δwf hAty hbody
    rw [← Lean.Expr.instantiate1_eq] at hbody'
    refine WF.bind (hsub'.whnf hbody') fun e₁ h₁ => ?_
    obtain ⟨-, -, htr₁⟩ := h₁
    have harr : (List.map Expr.fvar xfvs).toArray.push (.fvar ⟨cb.ngen.curr⟩) =
        (List.map Expr.fvar (xfvs ++ [⟨cb.ngen.curr⟩])).toArray := by simp
    rw [harr]
    obtain ⟨hk, hbase⟩ := hI.base
    have hbase' : ∃ hk', (TypeChecker.MLCtx.vlam (FVarId.mk cb.ngen.curr) name
        dom.consumeTypeAnnotations' ty' bi Mx).dropN (xfvs ++ [FVarId.mk cb.ngen.curr]).length hk' =
        Mk := by
      refine ⟨by simp [TypeChecker.MLCtx.length]; omega, ?_⟩
      rw [TypeChecker.MLCtx.dropN_congr (show (xfvs ++ [FVarId.mk cb.ngen.curr]).length =
        xfvs.length + 1 by simp) _ (by simp [TypeChecker.MLCtx.length]; omega)]
      exact hbase
    obtain ⟨v₀, hBS⟩ := hbodyT
    have hctxd : VEnv.IsDefEqCtx cT.venv cT.lparams.length (cT.small Mx hMx).vlctx.toCtx
        (A :: (cT.small Mx hMx).vlctx.toCtx) (ty' :: (cT.small Mx hMx).vlctx.toCtx) :=
      .succ .zero hAty
    refine ih _ _ (xtys ++ [ty']) B _ wf _ _
      ⟨by simpa using hI.tele.vlam, by simp [hI.len], hbase', hsub', hP _ _ _ _ _ _ _ hI.pred, ?_, htr₁,
        ⟨_, hBS.defeqDFC henv.ordered hctxd⟩, ?_,
        ⟨_, _, hE', by rw [List.length_append, List.length_singleton]; exact hW', ?_,
          by simp [TypeChecker.MLCtx.length]; omega, ?_⟩,
        fun hz => absurd rfl ((hI.stop hz).2 name dom body bi)⟩
    · show VLCtx.fvars (_ :: cb.mlctx.vlctx) = _
      simp [VLCtx.fvars_cons_some, hI.fvars]
    · have hT := hI.tele.isTele hMx
      obtain ⟨-, hxT⟩ := VEnv.IsTele.append_inv hT
      obtain ⟨u, hVS⟩ := hI.isType
      have h1 : cT.venv.IsDefEqU cT.lparams.length (cT.small Mx hMx).vlctx.toCtx V
          (.forallE ty' B) :=
        hdef.symm.trans henv hΓ ⟨_, .forallEDF hAty hBS⟩
      have h2 := h1.of_l henv hΓ hVS
      rw [hctx] at h2
      obtain ⟨_, h3⟩ := VEnv.IsDefEq.foralls_congr (by simpa using hxT) h2
      rw [VExpr.foralls_append]
      exact hI.rel.trans henv (by simpa using hT.append_inv.1.onCtx trivial) ⟨_, h3⟩
    · have hfl := hI.len
      have := hNT.vlam (fv := ⟨cb.ngen.curr⟩) (name := name) (ty := dom.consumeTypeAnnotations')
        (bi := bi) (ty' := (ty'.instL (VLevel.shift pre.length cT.lparams.length)).lift'
          (ρ₀.consN xfvs.length))
      have e : (cT.small Mx hMx).lparams = cT.lparams := rfl
      rw [e]; simpa [List.zipIdx_append, hfl] using this
    · rw [TypeChecker.MLCtx.dropN_congr (show (xfvs ++ [FVarId.mk cb.ngen.curr]).length =
        xfvs.length + 1 by simp) _ (by simp [TypeChecker.MLCtx.length]; omega)]
      exact hNb
  · rename_i hnf
    exact H _ _ _ _ _ _ _ _ hI hnf


/-- The top `n` variables of a telescope context, skipped. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.fvlift_top : ∀ (n : Nat)
    {m : TypeChecker.MLCtx} {fvs₁ fvs₂ : List FVarId} {tys₁ tys₂ : List VExpr},
    fvs₂.length = n → m.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂) → fvs₂.length = tys₂.length →
    ∀ hk, VLCtx.FVLift' (m.dropN n hk).vlctx m.vlctx 0 (Lift.skipN .refl n) 0
  | 0, _, _, _, _, _, _, _, _, _ => .refl
  | n + 1, m, fvs₁, fvs₂, tys₁, tys₂, hn, h, hlen, hk => by
    obtain ⟨tys₂, ty, rfl⟩ : ∃ a b, tys₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys₂).resolve_left (by rintro rfl; simp_all)
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [← List.append_assoc, ← List.append_assoc] at h
    obtain ⟨name, ty', bi, m', rfl, h'⟩ := h.snoc_inv
    have := (fvlift_top n hn h' hlen (by simp [TypeChecker.MLCtx.length] at hk; omega)).skip_fvar
      (fv, ty'.fvarsList) (.vlam ty)
    simpa [TypeChecker.MLCtx.dropN, TypeChecker.MLCtx.vlctx, VLocalDecl.depth] using this

/-- The lift from the parameters and `k` fields to the parameters, `a` binders, all `m` fields
and `r` more binders: what `reseat` does. -/
def reseatLift (a k m r : Nat) : Lift :=
  (Lift.skipN .refl (m - k)).comp (((Lift.skipN .refl a).consN m).comp (Lift.skipN .refl r))

theorem lift'_reseatLift (e : VExpr) (a k m r l : Nat) :
    e.lift' ((reseatLift a k m r).consN l) = e.reseat a k m r l := by
  simp only [reseatLift, Lift.consN_comp, VExpr.lift'_comp, Lift.consN_consN,
    VExpr.lift'_consN_skipN, VExpr.reseat]
  rw [VExpr.liftN'_comm _ _ _ _ _ (by omega), VExpr.liftN'_liftN' (Nat.le_refl _) (by omega)]
  congr 1; omega

theorem lift'_reseatLift0 (e : VExpr) (a k m r : Nat) :
    e.lift' (reseatLift a k m r) = e.reseat a k m r 0 := lift'_reseatLift e a k m r 0

end AddInductive

namespace VInductDecl
open VExpr

/-- `d` with its `j`th type's constructors replaced by `c` alone, and the other types' by none:
what typing a single constructor's minor premise depends on. -/
def only (d : VInductDecl) (j : Nat) (c : VConstructor) : VInductDecl :=
  { d with types := d.types.zipIdx.map fun (T, i) => { T with ctors := if i = j then [c] else [] } }

@[simp] theorem only_params (d : VInductDecl) (j c) : (d.only j c).params = d.params := rfl
@[simp] theorem only_level (d : VInductDecl) (j c) : (d.only j c).level = d.level := rfl
@[simp] theorem only_uvars (d : VInductDecl) (j c) : (d.only j c).uvars = d.uvars := rfl
@[simp] theorem only_types_length (d : VInductDecl) (j c) :
    (d.only j c).types.length = d.types.length := by simp [only]

theorem only_types_getElem? (d : VInductDecl) (j c) (t : Nat) :
    (d.only j c).types[t]? =
      d.types[t]?.map fun T => { T with ctors := if t = j then [c] else [] } := by
  simp only [only, List.getElem?_map, List.getElem?_zipIdx]
  cases d.types[t]? <;> simp

@[simp] theorem only_allTypes_length (d : VInductDecl) (j c) :
    (d.only j c).allTypes.length = d.allTypes.length := by simp [allTypes, only]

/-- `only` changes a type's constructors and nothing else. -/
theorem only_allTypes_getElem? (d : VInductDecl) (j c) (t : Nat) :
    (d.only j c).allTypes[t]?.map (fun T => (T.name, T.indices, T.nested)) =
      d.allTypes[t]?.map (fun T => (T.name, T.indices, T.nested)) := by
  by_cases ht : t < d.types.length
  · rw [allTypes, allTypes, List.getElem?_append_left (by simpa using ht),
      List.getElem?_append_left ht, only_types_getElem?]
    cases d.types[t]? <;> simp
  · rw [allTypes, allTypes, List.getElem?_append_right (by simpa using ht),
      List.getElem?_append_right (by omega), only_types_length]
    rfl

theorem only_allTypes_getElem (d : VInductDecl) (j c) (t : Nat)
    (h : t < (d.only j c).allTypes.length) :
    ((d.only j c).allTypes[t].name, (d.only j c).allTypes[t].indices,
      (d.only j c).allTypes[t].nested) =
    ((d.allTypes[t]'(by simpa using h)).name, (d.allTypes[t]'(by simpa using h)).indices,
      (d.allTypes[t]'(by simpa using h)).nested) := by
  have := only_allTypes_getElem? d j c t
  rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by simpa using h)] at this
  simpa using this

theorem motiveType_congr {d d' : VInductDecl} (hp : d.params.length = d'.params.length)
    {ls v i} {T T' : VInductiveType} (e1 : T.name = T'.name) (e2 : T.indices = T'.indices)
    (e3 : T.nested = T'.nested) : d.motiveType ls v i T = d'.motiveType ls v i T' := by
  simp only [motiveType, VInductiveType.typeApp, e1, e2, e3, hp]

theorem only_motiveTypes (d : VInductDecl) (j c ls v) :
    (d.only j c).motiveTypes ls v = d.motiveTypes ls v := by
  apply List.ext_getElem (by simp [motiveTypes]) fun i h1 h2 => ?_
  simp only [motiveTypes, List.getElem_map, List.getElem_zipIdx]
  have := only_allTypes_getElem d j c i (by simpa [motiveTypes] using h1)
  simp only [Prod.mk.injEq] at this
  obtain ⟨e1, e2, e3⟩ := this
  exact motiveType_congr rfl e1 e2 e3

theorem only_ctorAppAt (d : VInductDecl) (j c) :
    (d.only j c).ctorAppAt = d.ctorAppAt := by
  funext j' c' ls ps fs
  have := only_allTypes_getElem? d j c j'
  simp only [ctorAppAt]
  cases h1 : (d.only j c).allTypes[j']? <;> cases h2 : d.allTypes[j']? <;>
    rw [h1, h2] at this <;> simp at this <;>
    first | rfl | (simp only [Option.getD_some]; unfold VInductiveType.ctorApp; rw [this.2.2])

theorem ctorAppAt_of_none {d : VInductDecl} {j : Nat} {T : VInductiveType}
    (h : d.allTypes[j]? = some T) (hno : T.nested = none) (c ls ps fs) :
    d.ctorAppAt j c ls ps fs = .appN (.const c.name ls) (ps ++ fs) := by
  simp [ctorAppAt, h, VInductiveType.ctorApp_of_none hno]

theorem recName_of_types {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (h : d.types[t]? = some T) : d.recName t = Lean.mkRecName T.name := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 h; simp [recName, hlt]

/-- In a block without nested occurrences, a constructor applied as `ctorAppAt` applies it is its
constant applied to the parameters and fields. -/
theorem ctorAppAt_flat {d : VInductDecl} (hno : ∀ T ∈ d.allTypes, T.nested = none) (j c ls ps fs) :
    d.ctorAppAt j c ls ps fs = .appN (.const c.name ls) (ps ++ fs) := by
  cases h : d.allTypes[j]? with
  | none => simp [ctorAppAt, h, VInductiveType.ctorApp]; rfl
  | some T => exact ctorAppAt_of_none h (hno T (List.mem_of_getElem? h)) c ls ps fs

/-- The facts the recursor is built from, for a block without nested occurrences, from their
statements for its own types and constructors as constants. -/
theorem RecFacts.of_flat {d : VInductDecl} {env : VEnv} {U : Nat} {ls : List VLevel}
    (haux : d.aux = []) (hnone : ∀ T ∈ d.types, T.nested = none)
    (henv : env.WF) (hP : env.IsTele U [] (d.params.map (·.instL ls)))
    (hI : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
      env.IsTele U (d.params.map (·.instL ls)).reverse (T.indices.map (·.instL ls)))
    (hT : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
      env.HasType U [] (.const T.name ls)
        (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
          (.sort (d.level.inst ls))))
    (hF : ∀ {j : Nat} {c : VConstructor}, (j, c) ∈ d.ctors →
      env.IsTele U (d.params.map (·.instL ls)).reverse (c.fields.map (·.type.instL ls)))
    (hC : ∀ {j : Nat} {c : VConstructor} {T : VInductiveType}, (j, c) ∈ d.ctors →
      d.types[j]? = some T → c.indices.length = T.indices.length ∧
      env.HasType U [] (.const c.name ls)
        (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
          (.appN (.const T.name ls)
            (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls)))))
    (hR : ∀ {j : Nat} {c : VConstructor} {k : Nat} {f : VField} {ra : VRecArg}, (j, c) ∈ d.ctors →
      c.fields[k]? = some f → f.recArg = some ra →
      ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
      env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
          (d.params.map (·.instL ls)).reverse)
        (f.type.instL ls)
        (.foralls (ra.binders.map (·.instL ls)) (.appN (.const T.name ls)
          (bvars d.params.length (k + ra.binders.length) ++ ra.indices.map (·.instL ls))))) :
    d.RecFacts env U ls :=
  have hall : d.allTypes = d.types := allTypes_of_aux haux
  have hallC : d.allCtors = d.ctors := allCtors_of_aux haux
  { wf := henv
    params := hP
    indices := fun h => hI (hall ▸ h)
    type := hT
    fields := fun h => hF (hallC ▸ h)
    ctor := hC
    recArg := fun {j c k f ra} h hk hra => by
      rw [hallC] at h
      obtain ⟨T', h1, h2, h3⟩ := hR h hk hra
      refine ⟨T', hall ▸ h1, h2, ?_⟩
      rw [VInductiveType.typeApp_of_none (hnone T' (List.mem_of_getElem? h1))]
      exact h3
    typeHead := fun {t T'} h => by
      rw [hall] at h
      rw [VInductiveType.typeHead_of_none (hnone T' (List.mem_of_getElem? h))]
      simpa using VEnv.HasType.appN_params henv.ordered hP (hT h)
    ctorHead := fun {j' c' T'} h hT' => by
      rw [hallC] at h; rw [hall] at hT'
      have hno := hnone T' (List.mem_of_getElem? hT')
      refine ⟨(hC h hT').1, ?_⟩
      rw [VInductiveType.ctorHead_of_none hno, VInductiveType.typeApp_of_none hno]
      simpa using VEnv.HasType.appN_params henv.ordered hP (hC h hT').2 }

theorem only_minorType (d : VInductDecl) (j c ls q j' c') :
    (d.only j c).minorType ls q j' c' = d.minorType ls q j' c' := by
  simp only [minorType, only_params, only_allTypes_length, only_ctorAppAt]

theorem mem_only_ctors {d : VInductDecl} {j : Nat} {c : VConstructor} {j' c'}
    (h : (j', c') ∈ (d.only j c).ctors) : j' = j ∧ c' = c := by
  rw [mem_ctors_iff, only_types_getElem?] at h
  obtain ⟨_, hT, hc⟩ := h
  obtain ⟨T, -, rfl⟩ := Option.map_eq_some_iff.1 hT
  dsimp only at hc
  split at hc
  · simp at hc; exact ⟨by assumption, hc⟩
  · simp at hc

theorem mem_only_ctors_self {d : VInductDecl} {j : Nat} {c : VConstructor} {T}
    (hj : d.types[j]? = some T) : (j, c) ∈ (d.only j c).ctors := by
  rw [mem_ctors_iff]
  exact ⟨_, by rw [only_types_getElem?, hj]; rfl, by simp⟩

@[simp] theorem only_aux (d : VInductDecl) (j c) : (d.only j c).aux = d.aux := rfl

theorem only_nested {d : VInductDecl} (hn : ∀ T ∈ d.types, T.nested = none) (j c) :
    ∀ T ∈ (d.only j c).types, T.nested = none := by
  intro T hT
  obtain ⟨⟨T', i⟩, hT', rfl⟩ := List.mem_map.1 hT
  exact hn T' (List.fst_mem_of_mem_zipIdx hT')

theorem only_recFacts {d : VInductDecl} {env : VEnv} {U : Nat} {ls : List VLevel}
    {j : Nat} {c : VConstructor} {T : VInductiveType} (hj : d.types[j]? = some T)
    (haux : d.aux = []) (hnone : ∀ T ∈ d.types, T.nested = none)
    (henv : env.WF) (hP : env.IsTele U [] (d.params.map (·.instL ls)))
    (hI : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
      env.IsTele U (d.params.map (·.instL ls)).reverse (T.indices.map (·.instL ls)))
    (hT : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
      env.HasType U [] (.const T.name ls)
        (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
          (.sort (d.level.inst ls))))
    (hF : env.IsTele U (d.params.map (·.instL ls)).reverse (c.fields.map (·.type.instL ls)))
    (hC : c.indices.length = T.indices.length ∧
      env.HasType U [] (.const c.name ls)
        (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
          (.appN (.const T.name ls)
            (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls)))))
    (hR : ∀ {k : Nat} {f : VField} {ra : VRecArg}, c.fields[k]? = some f → f.recArg = some ra →
      ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
      env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
          (d.params.map (·.instL ls)).reverse)
        (f.type.instL ls)
        (.foralls (ra.binders.map (·.instL ls)) (.appN (.const T.name ls)
          (bvars d.params.length (k + ra.binders.length) ++ ra.indices.map (·.instL ls))))) :
    (d.only j c).RecFacts env U ls :=
  have hall : (d.only j c).allTypes = (d.only j c).types := allTypes_of_aux haux
  have hallC : (d.only j c).allCtors = (d.only j c).ctors := allCtors_of_aux haux
  have hn' := only_nested hnone j c
  have hctor {j' : Nat} {c' : VConstructor} {T' : VInductiveType} (h : (j', c') ∈ (d.only j c).ctors)
      (hT' : (d.only j c).types[j']? = some T') :
      c'.indices.length = T'.indices.length ∧
      env.HasType U [] (.const c'.name ls)
        (.foralls (d.params.map (·.instL ls) ++ c'.fields.map (·.type.instL ls))
          (.appN (.const T'.name ls)
            (bvars d.params.length c'.fields.length ++ c'.indices.map (·.instL ls)))) := by
    obtain ⟨rfl, rfl⟩ := mem_only_ctors h
    rw [only_types_getElem?, hj] at hT'; cases hT'; exact hC
  have htype {t : Nat} {T' : VInductiveType} (h : (d.only j c).types[t]? = some T') :
      env.HasType U [] (.const T'.name ls)
        (.foralls (d.params.map (·.instL ls) ++ T'.indices.map (·.instL ls))
          (.sort (d.level.inst ls))) := by
    rw [only_types_getElem?] at h
    obtain ⟨T'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hT (T := T'') h1
  { wf := henv
    params := hP
    indices := fun {t T'} h => by
      rw [hall, only_types_getElem?] at h
      obtain ⟨T'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      exact hI (T := T'') h1
    type := htype
    fields := fun {j' c'} h => by
      rw [hallC] at h; obtain ⟨rfl, rfl⟩ := mem_only_ctors h; exact hF
    ctor := hctor
    recArg := fun {j' c' k f ra} h hk hra => by
      rw [hallC] at h
      obtain ⟨rfl, rfl⟩ := mem_only_ctors h
      obtain ⟨T', h1, h2, h3⟩ := hR hk hra
      refine ⟨{ T' with ctors := if ra.typeIdx = j' then [c'] else [] },
        by rw [hall, only_types_getElem?, h1]; rfl, h2, ?_⟩
      rw [VInductiveType.typeApp_of_none (by exact hnone T' (List.mem_of_getElem? h1))]
      exact h3
    typeHead := fun {t T'} h => by
      rw [hall] at h
      rw [VInductiveType.typeHead_of_none (hn' T' (List.mem_of_getElem? h))]
      simpa using VEnv.HasType.appN_params henv.ordered hP (htype h)
    ctorHead := fun {j' c' T'} h hT' => by
      rw [hallC] at h; rw [hall] at hT'
      have hno := hn' T' (List.mem_of_getElem? hT')
      refine ⟨(hctor h hT').1, ?_⟩
      rw [VInductiveType.ctorHead_of_none hno, VInductiveType.typeApp_of_none hno]
      simpa using VEnv.HasType.appN_params henv.ordered hP (hctor h hT').2 }

end VInductDecl

namespace AddInductive

end AddInductive

namespace VInductDecl
open VExpr

/-- What the recursor's binders before the minor premises are typed from: the parameters, and each
type at its index telescope. -/
structure BlockFacts (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) : Prop where
  wf : env.WF
  params : env.IsTele U [] (d.params.map (·.instL ls))
  indices : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.IsTele U (d.params.map (·.instL ls)).reverse (T.indices.map (·.instL ls))
  type : ∀ {t : Nat} {T : VInductiveType}, d.types[t]? = some T →
    env.HasType U [] (.const T.name ls)
      (.foralls (d.params.map (·.instL ls) ++ T.indices.map (·.instL ls))
        (.sort (d.level.inst ls)))
  aux : d.aux = []
  nested : ∀ T ∈ d.types, T.nested = none

/-- What a constructor's minor premise is typed from: its fields, its type, and the views of its
recursive fields. -/
structure CtorFacts (d : VInductDecl) (env : VEnv) (U : Nat) (ls : List VLevel) (j : Nat)
    (c : VConstructor) : Prop where
  fields : env.IsTele U (d.params.map (·.instL ls)).reverse (c.fields.map (·.type.instL ls))
  ctor : ∃ T, d.types[j]? = some T ∧ c.indices.length = T.indices.length ∧
    env.HasType U [] (.const c.name ls)
      (.foralls (d.params.map (·.instL ls) ++ c.fields.map (·.type.instL ls))
        (.appN (.const T.name ls)
          (bvars d.params.length c.fields.length ++ c.indices.map (·.instL ls))))
  recArg : ∀ {k : Nat} {f : VField} {ra : VRecArg}, c.fields[k]? = some f →
    f.recArg = some ra →
    ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
        (d.params.map (·.instL ls)).reverse)
      (f.type.instL ls)
      (.foralls (ra.binders.map (·.instL ls)) (.appN (.const T.name ls)
        (bvars d.params.length (k + ra.binders.length) ++ ra.indices.map (·.instL ls))))

theorem BlockFacts.only {d : VInductDecl} {env : VEnv} {U : Nat} {ls : List VLevel} {j : Nat}
    {c : VConstructor} (hB : d.BlockFacts env U ls) (hC : d.CtorFacts env U ls j c) :
    (d.only j c).RecFacts env U ls := by
  obtain ⟨T, hj, hC1, hC2⟩ := hC.ctor
  exact only_recFacts hj hB.aux hB.nested hB.wf hB.params hB.indices hB.type hC.fields ⟨hC1, hC2⟩
    hC.recArg

end VInductDecl

namespace AddInductive

theorem _root_.List.Forall₂.drop_append {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, l₁.length = m₁.length →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) → List.Forall₂ R l₂ m₂
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, hl, .cons _ h => List.Forall₂.drop_append (Nat.succ.inj hl) h

/-- The top variables of a telescope context translate to the variables they are. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.top_tr {env : VEnv} {Us : List Name}
    {m : TypeChecker.MLCtx} {fvs₁ fvs₂ : List FVarId} {tys : List VExpr}
    (h : m.IsTele (fvs₁ ++ fvs₂) tys) (hnd : (fvs₁ ++ fvs₂).Nodup) :
    List.Forall₂ (TrExprS env Us m.vlctx) (fvs₂.map .fvar) (VExpr.bvars fvs₂.length 0) := by
  have := h.fvars_tr (env := env) (Us := Us) hnd
  rw [List.map_append, List.length_append, ← VExpr.bvars_append] at this
  exact List.Forall₂.drop_append (by simp [VExpr.bvars]) this

/-- An inductive hypothesis' type, `Π xs, motive idx (u xs)` in the kernel's local context,
translates over a view `N` of it holding the binders `xs` on top, once the translated type is
known to be a type. -/
theorem ihType_tr {env : VEnv} {Us : List Name} (henv : env.WF) {lctx : LocalContext}
    {N : TypeChecker.MLCtx} (hN : N.WF env Us) {fvs₁ xfvs : List FVarId} {tys₁ xtys : List VExpr}
    (hT : N.IsTele (fvs₁ ++ xfvs) (tys₁ ++ xtys)) (hlen : xfvs.length = xtys.length)
    (hag : ∀ x ∈ xfvs, (lctx.find? x).map LocalDecl.erase = (N.lctx.find? x).map LocalDecl.erase)
    {mfv ufv : FVarId} {mp up : Nat} {mty uty : VExpr}
    (hm : N.vlctx.find? (.inr mfv) = some (.bvar (xfvs.length + mp), mty))
    (hu : N.vlctx.find? (.inr ufv) = some (.bvar (xfvs.length + up), uty))
    {idx : List Expr} {idx' : List VExpr} (hidx : List.Forall₂ (TrExprS env Us N.vlctx) idx idx')
    (hty : env.IsType Us.length (N.dropN xfvs.length (by rw [hT.length]; simp)).vlctx.toCtx
      (.foralls xtys (.app (.appN (.bvar (xfvs.length + mp)) idx')
        (.appN (.bvar (xfvs.length + up)) (VExpr.bvars xfvs.length 0))))) :
    ∃ hk, lctx.mkForall (xfvs.map .fvar).toArray
        (.app (mkAppN (.fvar mfv) idx.toArray) (mkAppN (.fvar ufv) (xfvs.map .fvar).toArray)) =
      N.mkForall xfvs.length hk
        (.app (mkAppN (.fvar mfv) idx.toArray) (mkAppN (.fvar ufv) (xfvs.map .fvar).toArray)) ∧
      TrExprS env Us (N.dropN xfvs.length hk).vlctx (N.mkForall xfvs.length hk
          (.app (mkAppN (.fvar mfv) idx.toArray) (mkAppN (.fvar ufv) (xfvs.map .fvar).toArray)))
        (.foralls xtys (.app (.appN (.bvar (xfvs.length + mp)) idx')
          (.appN (.bvar (xfvs.length + up)) (VExpr.bvars xfvs.length 0)))) ∧
      env.IsType Us.length (N.dropN xfvs.length hk).vlctx.toCtx
        (.foralls xtys (.app (.appN (.bvar (xfvs.length + mp)) idx')
          (.appN (.bvar (xfvs.length + up)) (VExpr.bvars xfvs.length 0)))) := by
  have hΔ := hN.tr.wf
  have hΓ := hΔ.toCtx
  have hk : xfvs.length ≤ N.length := by rw [hT.length]; simp
  have hctx : N.vlctx.toCtx = xtys.reverse ++ (N.dropN xfvs.length hk).vlctx.toCtx := by
    obtain ⟨hk', h'⟩ := hT.dropN
    rw [TypeChecker.MLCtx.dropN_congr hlen hk hk', h'.toCtx, hT.toCtx]; simp
  obtain ⟨-, hB⟩ := VEnv.IsType.foralls_inv henv.ordered hty
  rw [← hctx] at hB
  obtain ⟨_, hBS⟩ := hB
  obtain ⟨A₀, B₀, hF, hA⟩ := VExpr.WF.app_inv henv.ordered hΓ ⟨_, hBS⟩
  have hnd : (fvs₁ ++ xfvs).Nodup := by
    have := hN.fvars_nodup; rw [hT.fvars] at this; exact List.nodup_reverse.1 this
  have htrF := TrExprS.mkAppN_of_wf henv.ordered hΓ (.fvar hm) hidx ⟨_, hF⟩
  have htrA := TrExprS.mkAppN_of_wf henv.ordered hΓ (.fvar hu) (hT.top_tr hnd) ⟨_, hA⟩
  obtain ⟨hk₁, eq₁, trS₁, isT₁⟩ := mkForall_tele (lctx := lctx) henv hN hT hlen hag
    (.app hF hA htrF htrA) ⟨_, hBS⟩
  exact ⟨hk₁, eq₁, trS₁, isT₁⟩

/-- Stripping leaves an application of a variable alone. -/
theorem stripAnnotations_fvar_head {env : Environment} {e : Expr} {fv : FVarId}
    (hfn : e.getAppFn = .fvar fv) : stripAnnotations env e = .ok e := by
  unfold stripAnnotations
  split <;> first | (simp [Expr.getAppFn] at hfn) | rfl

theorem consumeTypeAnnotations_of_strip {c : VContext} {e : Expr}
    (h : stripAnnotations c.env e = .ok e) : WF c (consumeTypeAnnotations e) (· = e) := by
  intro a ha; change stripAnnotations _ _ = _ at ha; rw [h] at ha; cases ha; rfl

/-- Closing a telescope context's top variables over something stripping does not change leaves
something stripping does not change. -/
theorem stripAnnotations_mkForall {env : Environment} : ∀ (n : Nat) {m : TypeChecker.MLCtx}
    {fvs : List FVarId} {tys : List VExpr}, m.IsTele fvs tys → ∀ hk {e : Expr},
    stripAnnotations env e = .ok e → stripAnnotations env (m.mkForall n hk e) = .ok (m.mkForall n hk e)
  | 0, _, _, _, _, _, _, he => he
  | n + 1, m, fvs, tys, h, hk, e, _ => by
    cases h with
    | nil => simp [TypeChecker.MLCtx.length] at hk
    | vlam h =>
      obtain ⟨_, _, _, _, he⟩ := TypeChecker.MLCtx.mkForall_forallE n h
        (Nat.le_of_succ_le_succ hk) _ _ _ _
      simp only [TypeChecker.MLCtx.mkForall]
      rw [he]; exact stripAnnotations_forallE

theorem _root_.Array.toList_slice_from {α} (a : Array α) (n : Nat) :
    (a[n:] : Array α).toList = a.toList.drop n := by
  rw [Subarray.copy_eq_toArray, Subarray.toList_toArray, Subarray.toList_eq_drop_take]
  simp only [Array.array_toSubarray, Array.start_toSubarray, Array.stop_toSubarray]
  rw [Nat.min_self, ← Array.length_toList, List.take_length]
  by_cases h : n ≤ a.toList.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

theorem getIIndices.WF {c : VContext} {stats : InductiveStats} {t : Expr} :
    WF c (getIIndices stats t) fun r =>
      isValidIndApp? stats t = some r.1 ∧ r.2.toList = t.getAppArgsList.drop stats.params.size := by
  unfold getIIndices
  split
  · rename_i i hi
    refine WF.pure ⟨hi, ?_⟩
    rw [Array.toList_slice_from, Expr.getAppArgs_eq]
  · exact .throw

/-- A telescope context is its top variables over the rest. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.vlctx_split : ∀ (n : Nat)
    {m : TypeChecker.MLCtx} {fvs₁ fvs₂ : List FVarId} {tys₁ tys₂ : List VExpr},
    fvs₂.length = n → m.IsTele (fvs₁ ++ fvs₂) (tys₁ ++ tys₂) → fvs₂.length = tys₂.length →
    ∀ hk, ∃ Δtop : VLCtx, m.vlctx = Δtop ++ (m.dropN n hk).vlctx ∧ Δtop.length = n ∧
      (∀ x ∈ Δtop, x.1.isSome ∧ ∃ A, x.2 = .vlam A) ∧ (m.dropN n hk).IsTele fvs₁ tys₁
  | 0, m, fvs₁, fvs₂, tys₁, tys₂, hn, h, hlen, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨[], rfl, rfl, nofun, by simpa using h⟩
  | n + 1, m, fvs₁, fvs₂, tys₁, tys₂, hn, h, hlen, hk => by
    obtain ⟨tys₂, ty, rfl⟩ : ∃ a b, tys₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat tys₂).resolve_left (by rintro rfl; simp_all)
    obtain ⟨fvs₂, fv, rfl⟩ : ∃ a b, fvs₂ = a ++ [b] :=
      by simpa using (List.eq_nil_or_concat fvs₂).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen hn
    rw [← List.append_assoc, ← List.append_assoc] at h
    obtain ⟨name, ty', bi, m', rfl, h'⟩ := h.snoc_inv
    obtain ⟨Δtop, e, hl, hv, ht⟩ := vlctx_split n hn h' hlen
      (by simp [TypeChecker.MLCtx.length] at hk; omega)
    refine ⟨(some (fv, ty'.fvarsList), .vlam ty) :: Δtop, ?_, by simp [hl], ?_, ht⟩
    · simp only [TypeChecker.MLCtx.vlctx, TypeChecker.MLCtx.dropN]; rw [e]; rfl
    · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨rfl, _, rfl⟩
      · exact hv x hx

end AddInductive

/-- `c` with its `k`th field seen as recursive, through the view `ra`. -/
def VConstructor.setRecArg (c : VConstructor) (k : Nat) (ra : VRecArg) : VConstructor :=
  { c with fields := c.fields.modify k fun f => { f with recArg := some ra } }

theorem VConstructor.setRecArg_types (c : VConstructor) (k ra) :
    (c.setRecArg k ra).fields.map (·.type) = c.fields.map (·.type) := by
  apply List.ext_getElem? fun i => ?_
  simp only [setRecArg, List.getElem?_map, List.getElem?_modify]
  split <;> cases c.fields[i]? <;> rfl

theorem VConstructor.setRecArg_length (c : VConstructor) (k ra) :
    (c.setRecArg k ra).fields.length = c.fields.length := by simp [setRecArg]

theorem VConstructor.setRecArg_getElem? (c : VConstructor) (k ra) (i : Nat) :
    (c.setRecArg k ra).fields[i]? =
      if k = i then c.fields[i]?.map ({ · with recArg := some ra }) else c.fields[i]? := by
  simp only [setRecArg, List.getElem?_modify]
  split <;> cases c.fields[i]? <;> rfl

theorem VConstructor.map_type_instL_setRecArg (c : VConstructor) (k ra) (ls : List VLevel) :
    (c.setRecArg k ra).fields.map (·.type.instL ls) = c.fields.map (·.type.instL ls) := by
  have := congrArg (List.map (VExpr.instL ls)) (c.setRecArg_types k ra)
  simpa [List.map_map, Function.comp_def] using this

theorem VInductDecl.CtorFacts.setRecArg {d : VInductDecl} {env : VEnv} {U : Nat}
    {ls : List VLevel} {j : Nat} {c : VConstructor} (H : d.CtorFacts env U ls j c)
    {k : Nat} {f : VField} (hk : c.fields[k]? = some f) {ra : VRecArg}
    (hra : ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
      env.IsDefEqU U (((c.fields.take k).map (·.type.instL ls)).reverse ++
          (d.params.map (·.instL ls)).reverse)
        (f.type.instL ls)
        (.foralls (ra.binders.map (·.instL ls)) (.appN (.const T.name ls)
          (VExpr.bvars d.params.length (k + ra.binders.length) ++
            ra.indices.map (·.instL ls))))) :
    d.CtorFacts env U ls j (c.setRecArg k ra) where
  fields := by rw [c.map_type_instL_setRecArg]; exact H.fields
  ctor := by
    rw [c.map_type_instL_setRecArg, c.setRecArg_length]; exact H.ctor
  recArg {k' f' ra'} hk' hra' := by
    have htake : ((c.setRecArg k ra).fields.take k').map (·.type.instL ls) =
        (c.fields.take k').map (·.type.instL ls) := by
      have := congrArg (List.take k') (c.map_type_instL_setRecArg k ra ls)
      simpa [List.map_take] using this
    rw [htake]
    rw [VConstructor.setRecArg_getElem?] at hk'
    split at hk'
    · subst k'
      rw [hk] at hk'; cases hk'; cases hra'; exact hra
    · exact H.recArg hk' hra'

namespace AddInductive

/-- The `k`th field's view `ra`, as `VInductDecl.RecArgWF` states it, over parameters `params`
and fields `ftys`. -/
def _root_.Lean4Lean.VInductDecl.RecArgAt (d : VInductDecl) (env : VEnv) (U : Nat)
    (params ftys : List VExpr) (k : Nat) (fty : VExpr) (ra : VRecArg) : Prop :=
  ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU U ((ftys.take k).reverse ++ params.reverse) fty
      (.foralls ra.binders (.appN (.const T.name (VLevel.params U))
        (VExpr.bvars params.length (k + ra.binders.length) ++ ra.indices))) ∧
    ra.binders.all (!·.mentions d.names) ∧ ra.indices.all (!·.mentions d.names)

/-- An inductive hypothesis' type in a minor premise, as `minorType` states it: over the views of
the `k`th field's binders, the motive of its type applied to the view's indices and to the field
applied to the binders, with `r` inductive hypotheses before it, below the parameters, `T`
motives, `q` minor premises and `m` fields. -/
def ihSpec (ls : List VLevel) (T q m r k : Nat) (ra : VRecArg) : VExpr :=
  let b := ra.binders.length
  .foralls (ra.binders.zipIdx.map fun (A, i) => (A.instL ls).reseat (T + q) k m r i) <|
    .app (.appN (.bvar (b + r + m + q + (T - 1 - ra.typeIdx)))
        (ra.indices.map fun e => (e.instL ls).reseat (T + q) k m r b))
      (.appN (.bvar (b + r + (m - 1 - k))) (VExpr.bvars b 0))

/-- What `mkRecRules` builds an inductive hypothesis' value from: the binders, indices and field
`ih` records translate, over the parameters and the fields before the recursive one `Mk`, to the
view `ra`, with the binders as bound variables. -/
structure IHPieces (env : VEnv) (Us : List Name) (Mk : TypeChecker.MLCtx) (fvk : FVarId)
    (ih : IHInfo) (ra : VRecArg) : Prop where
  itIdx : ih.itIdx = ra.typeIdx
  field : ih.field = .fvar fvk
  size : ih.binders.size = ra.binders.length
  binders : ∀ i (h : i < ih.binders.size), TrExprS env Us (bvCtx (ra.binders.take i) ++ Mk.vlctx)
    (ih.binders[i]).2.1 (ra.binders[i]'(size ▸ h))
  indices : List.Forall₂ (TrExprS env Us (bvCtx ra.binders ++ Mk.vlctx)) ih.indices.toList
    ra.indices

/-- `loopUArgs` and the inductive hypothesis built from what it reads, for the `k`th field, the
`r`th recursive one, of a constructor `c` of the `j`th type, the `q`th of the block. The kernel's
context is viewed as `E`: the parameters, motives, earlier minor premises, the fields, and the
inductive hypotheses so far. It reads the field's type in the small context `Mf` of the
parameters and fields. -/
theorem ihInfo.WF [VEnv.Injective] {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {pfvs : List FVarId} {params : List VExpr}
    (hMpT : Mp.IsTele pfvs params) {stats : InductiveStats}
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = cT.lparams.map .param)
    {types : List InductiveType}
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    (hUs : cT.lparams.Nodup) {d₀ : VInductDecl} (hd₀p : d₀.params = params)
    (hd₀T : d₀.types.length = types.length)
    (hd₀t : ∀ t (ht : t < types.length), ∃ T', d₀.types[t]? = some T' ∧
      T'.name = types[t].name ∧ stats.nindices[t]? = some T'.indices.length)
    {cb : VContext} {ml : VLevel}
    (hB : d₀.BlockFacts cb.venv cb.lparams.length
      (VLevel.shift pre.length cT.lparams.length))
    {j : Nat} {c : VConstructor}
    (hC : d₀.CtorFacts cb.venv cb.lparams.length (VLevel.shift pre.length cT.lparams.length) j c)
    {Mf : TypeChecker.MLCtx} {hMf : Mf.WF cT.venv cT.lparams} {fvs : List FVarId}
    {ftys : List VExpr} (hMfT : Mf.IsTele (pfvs ++ fvs) (params ++ ftys))
    (hcf : c.fields.map (·.type) = ftys) {ρf : Lift}
    (hsub : Sub X pre ρf (cT.small Mf hMf) cb)
    {k : Nat} (hk : k < fvs.length) {f : VField} (hfk : c.fields[k]? = some f)
    {q r : Nat} {Qs' : List VExpr} (hq : Qs'.length = q) {motfvs minfvs vfvs : List FVarId}
    {ihtys : List VExpr} (hmot : motfvs.length = types.length) (hmin : minfvs.length = q)
    (hvfvs : vfvs.length = r) (hih : ihtys.length = r)
    {E : TypeChecker.MLCtx} {ρE : Lift} (hE : Ext E cb ρE)
    (hET : E.IsTele (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs)
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs' ++
        VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++ ihtys))
    (hWf : ∃ hk', VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx
      (E.dropN r hk').vlctx 0 ((Lift.skipN .refl (types.length + q)).consN fvs.length) 0)
    {recInfos : Array RecInfo} {blockNames : NameSet}
    (hrec : ∀ t (ht : t < types.length), recInfos[t]!.motive = .fvar (motfvs[t]'(hmot ▸ ht)))
    (hNM : NotMentionsOK cT.venv cT.lparams stats types)
    (hBN : ∀ t ∈ types, blockNames.contains t.name) :
    WF cb (mkRecInfos.loopUArgs (.fvar fvs[k]) fun uiTy xs => do
      let (itIdx, itIndices) ← getIIndices stats uiTy
      let lctx ← getLCtx
      for x in xs do
        if let some d := lctx.findFVar? x then
          if d.type.anySubterm fun | .const c _ => blockNames.contains c | _ => false then
            throw <| .other "invalid recursive argument, its binders mention the block"
      return (lctx.mkForall xs <| .app (mkAppN recInfos[itIdx]!.motive itIndices)
          (mkAppN (.fvar fvs[k]) xs),
        { itIdx, field := .fvar fvs[k]
          binders := xs.mapIdx fun i x => match lctx.findFVar? x with
            | some d => (d.userName, d.type.abstractRange i xs, d.binderInfo)
            | none => (.anonymous, x, .default)
          indices := itIndices.map (·.abstract xs) : IHInfo }))
      fun (viTy, ih) => ∃ ra, d₀.CtorFacts cb.venv cb.lparams.length
          (VLevel.shift pre.length cT.lparams.length) j (c.setRecArg k ra) ∧
        d₀.RecArgAt cT.venv cT.lparams.length params ftys k f.type ra ∧
        ih.itIdx = ra.typeIdx ∧
        TrExprS cb.venv cb.lparams E.vlctx viTy
          (ihSpec (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length r k ra) ∧
        cb.venv.IsType cb.lparams.length E.vlctx.toCtx
          (ihSpec (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length r k ra) ∧
        stripAnnotations cb.env viTy = .ok viTy ∧
        ∃ hk', IHPieces cT.venv cT.lparams (Mf.dropN (fvs.length - k) hk') fvs[k] ih ra ∧
          ∀ dk n us ax, Mf.lctx.find? fvs[k] = some dk → dk.type = .const n us →
            cT.env.find? n = some (.axiomInfo ax) → ra.binders = [] := by
  -- the field's place in the small context
  have hlenp : pfvs.length = params.length := hMpT.length_eq
  have hfl : ftys.length = fvs.length := by
    have := hMfT.length_eq; simp [hlenp] at this; omega
  obtain ⟨hk1, hT1⟩ := hMfT.dropN' (fvs.length - k - 1) (by simp; omega)
  have hlen1 : (params ++ ftys).length - (fvs.length - k - 1) = pfvs.length + k + 1 := by
    simp [hfl, hlenp]; omega
  have htk1 : (pfvs ++ fvs).take (pfvs.length + k + 1) = (pfvs ++ fvs.take k) ++ [fvs[k]] := by
    rw [List.take_append, List.take_of_length_le (by omega),
      show pfvs.length + k + 1 - pfvs.length = k + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hk, List.append_assoc]; rfl
  have htt1 : (params ++ ftys).take (pfvs.length + k + 1) =
      (params ++ ftys.take k) ++ [ftys[k]'(hfl ▸ hk)] := by
    rw [List.take_append, List.take_of_length_le (by omega),
      show pfvs.length + k + 1 - params.length = k + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (hfl ▸ hk), List.append_assoc]; rfl
  rw [hlen1, htk1, htt1] at hT1
  obtain ⟨name_k, dom_k, bi_k, Mk, hMk1, hMkT⟩ := hT1.snoc_inv
  have hk2 : fvs.length - k ≤ Mf.length := by
    have := hMfT.length; simp at this; omega
  have hMkdrop : Mf.dropN (fvs.length - k) hk2 = Mk := by
    rw [← TypeChecker.MLCtx.dropN_congr (show fvs.length - k - 1 + 1 = fvs.length - k by omega)
      (by omega) hk2, ← TypeChecker.MLCtx.dropN_dropN Mf _ 1 hk1
        (by simp [hMk1, TypeChecker.MLCtx.length])]
    simp [hMk1, TypeChecker.MLCtx.dropN]
  subst hMkdrop
  have hwf1 := TypeChecker.MLCtx.WF.dropN _ hk1 hMf
  rw [hMk1] at hwf1
  obtain ⟨hMkWF, -, htyk, hTk⟩ := hwf1
  -- the field's declaration in the kernel's context
  obtain ⟨dk, hdk, hdkty⟩ := hMf.find?_dropN_vlam _ hk1 hMk1
  have hmem : fvs[k] ∈ (cT.small Mf hMf).mlctx.vlctx.fvars := by
    show fvs[k] ∈ Mf.vlctx.fvars
    rw [hMfT.fvars]; simp
  have hcbk := hsub.lctx _ hmem
  have hcbk' : ∃ d', cb.lctx.find? fvs[k] = some d' ∧ d'.type = dom_k := by
    change _ = Option.map _ (Mf.lctx.find? fvs[k]) at hcbk
    rw [hdk] at hcbk
    cases e : cb.lctx.find? fvs[k] with
    | none => rw [e] at hcbk; cases hcbk
    | some d' =>
      rw [e] at hcbk; injection hcbk with hcbk
      exact ⟨d', rfl, (LocalDecl.erase_type hcbk).1.trans hdkty⟩
  obtain ⟨d', hd', hd'ty⟩ := hcbk'
  obtain ⟨ρk, hsubk⟩ := hsub.dropN (fvs.length - k) hk2
  unfold mkRecInfos.loopUArgs
  refine WF.bind (inferType_fvar hd') fun ty₀ hty₀ => ?_
  subst hty₀; rw [hd'ty]
  -- an axiom is its own normal form
  let Zax : Prop := ∃ n us ax, dom_k = .const n us ∧ cT.env.find? n = some (.axiomInfo ax)
  have hsyn : AddInductive.WF cb (monadLift (TypeChecker.whnf dom_k) : M Expr)
      fun e₁ => Zax → e₁ = dom_k := by
    by_cases hz : Zax
    · obtain ⟨n, us, ax, he, hax⟩ := hz
      have hX : ¬X n := fun hX => by
        have := (hsubk.fresh n hX).1
        change cT.env.find? n = none at this
        rw [hax] at this; cases this
      have hax' : cb.env.find? n = some (.axiomInfo ax) := by
        rw [hsubk.env n hX]; exact hax
      rw [he]; exact AddInductive.WF.mono (whnf_const_axiom.WF hax') fun e h _ => h
    · exact fun _ _ h => absurd h hz
  refine WF.bind (AddInductive.WF.and (hsubk.whnf htyk) hsyn) fun e₁ ⟨h₁, hZ⟩ => ?_
  obtain ⟨-, -, htr₁⟩ := h₁
  refine WF.bind (Q := (· = cb.toContext)) (fun _ h => by cases h; rfl) fun ctx hctx => ?_
  subst hctx
  -- the view of the kernel's context the inductive hypothesis is translated in
  have hEfl : (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs).length =
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs' ++
        VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++ ihtys).length :=
    hET.length_eq
  obtain ⟨hk', W2⟩ := hWf
  have W3 := hET.fvlift_top r (fvs₂ := vfvs) (tys₂ := ihtys) hvfvs (by omega) hk'
  have hMfT' := hMfT.instL (VLevel.shift pre.length cT.lparams.length)
  rw [show pfvs ++ fvs = (pfvs ++ fvs.take k) ++ fvs.drop k by simp,
    show params ++ ftys = (params ++ ftys.take k) ++ ftys.drop k by simp,
    List.map_append] at hMfT'
  have W1 := hMfT'.fvlift_top (fvs.length - k) (by simp) (by simp [hfl])
    (by rw [TypeChecker.MLCtx.length_instL]; exact hk2)
  rw [TypeChecker.MLCtx.dropN_instL _ _ _ hk2] at W1
  have W₀ := W1.comp (W2.comp W3)
  have hEtel : E.IsTele ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ [])
      ((params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs' ++
        VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++ ihtys) ++
        ([] : List VExpr).zipIdx.map fun (A, j) =>
          (A.instL (VLevel.shift pre.length cT.lparams.length)).lift'
            ((reseatLift (types.length + q) k fvs.length r).consN j)) := by simpa using hET
  obtain ⟨u₀, hfS⟩ := hTk
  have hMkctx : (Mf.dropN (fvs.length - k) hk2).vlctx.toCtx = (params ++ ftys.take k).reverse :=
    hMkT.toCtx
  refine loopUArgs.loop.WF (Mk := Mf.dropN (fvs.length - k) hk2) (F₀ := cb.mlctx.vlctx.fvars)
    (P := fun cb' => cb'.env = cb.env ∧ cb'.venv = cb.venv ∧ cb'.lparams = cb.lparams)
    (Z := Zax) (fun _ _ _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩) ?_ _ e₁ [] [] _ _ _ cb ρk
    ⟨by simpa using hMkT, rfl, ⟨Nat.zero_le _, rfl⟩, hsubk, ⟨rfl, rfl, rfl⟩, by simp, htr₁,
      ⟨_, hfS⟩, ⟨_, by rw [← hMkctx]; exact hfS⟩, ⟨E, ρE, hE, W₀, hEtel, ⟨Nat.zero_le _, rfl⟩⟩,
      fun hz => ⟨rfl, fun name dom body bi he => by
        rw [hZ hz] at he; obtain ⟨n, us, ax, rfl, -⟩ := hz; cases he⟩⟩
  intro uiTy xfvs xtys V Mx hMx cbx ρx hI hnf
  obtain ⟨henvx, hvenvx, hlpx⟩ := hI.pred
  refine WF.bind getIIndices.WF fun ⟨itIdx, itIndices⟩ ⟨hval, hidxL⟩ => ?_
  dsimp only
  obtain ⟨hits, hvalI⟩ := isValidIndApp?_some hval
  have hitT : itIdx < types.length := by
    rw [← Array.length_toList, hind] at hits; simpa using hits
  -- what the field's type ends in
  obtain ⟨V₀, hS, hdef⟩ := hI.tr
  have hxl := hI.len
  have hteleP : Mx.IsTele (pfvs ++ (fvs.take k ++ xfvs)) (params ++ (ftys.take k ++ xtys)) := by
    simpa using hI.tele
  obtain ⟨Δtop, hsplit, hΔl, hΔv, hbotT⟩ := hteleP.vlctx_split (k + xfvs.length)
    (by simp; omega) (by simp [hxl]; omega) (by
      have := hteleP.length; simp at this; simp; omega)
  have hPA : ParamsAt Mx.vlctx (k + xfvs.length) pfvs := by
    have hfv := hMx.tr.wf.fvwf
    rw [hsplit] at hfv ⊢
    have := ParamsAt.tele hbotT hfv hΔv
    rwa [hΔl] at this
  obtain ⟨is, hisl, hargl, hV₀, hisTr⟩ := validIndApp_shape hUs hpar hlev hind hPA hvalI hitT hS
  -- the field's view, at the checking environment's levels
  have henvT : cT.venv.WF := cT.envAt.tr.wf
  have hΓx : OnCtx (cT.small Mx hMx).vlctx.toCtx (cT.venv.IsType cT.lparams.length) :=
    (cT.small Mx hMx).Δwf.toCtx
  have hxctx : (cT.small Mx hMx).vlctx.toCtx =
      xtys.reverse ++ (params ++ ftys.take k).reverse := by
    show Mx.vlctx.toCtx = _; rw [hI.tele.toCtx]; simp
  have hkT : cT.venv.IsTele cT.lparams.length [] (params ++ ftys.take k) := by
    have := hI.tele.isTele hMx
    exact (VEnv.IsTele.append_inv this).1
  have hxT : cT.venv.IsTele cT.lparams.length (params ++ ftys.take k).reverse xtys := by
    have := hI.tele.isTele hMx
    simpa using (VEnv.IsTele.append_inv this).2
  obtain ⟨uV, hVS⟩ := hI.isType
  have hVV₀ := hdef.of_r henvT hΓx hVS
  rw [hxctx] at hVV₀
  obtain ⟨_, hfc⟩ := VEnv.IsDefEq.foralls_congr hxT hVV₀
  have hrel₀ : cT.venv.IsDefEqU cT.lparams.length (params ++ ftys.take k).reverse
      (ftys[k]'(hfl ▸ hk)) (.foralls xtys V₀) :=
    hI.rel.trans henvT (by simpa using hkT.onCtx trivial) ⟨_, hfc.symm⟩
  have hshl : (VLevel.shift pre.length cT.lparams.length).length = cT.lparams.length := by
    simp [VLevel.shift]
  have hls : ∀ l ∈ VLevel.shift pre.length cT.lparams.length, l.WF cb.lparams.length := by
    have e : (cT.small Mf hMf).lparams = cT.lparams := rfl
    rw [hsub.lparams, e]; simpa using VLevel.shift_wf
  have hrel₁ := (hrel₀.instL hls).mono hsub.venv
  obtain ⟨T', hT', hT'n, hT'i⟩ := hd₀t itIdx hitT
  have hfty : f.type = ftys[k]'(hfl ▸ hk) := by
    have := congrArg (·[k]?) hcf
    simp only [List.getElem?_map, hfk, Option.map_some, List.getElem?_eq_getElem (hfl ▸ hk)] at this
    exact Option.some.inj this
  have htake : (c.fields.take k).map (·.type.instL (VLevel.shift pre.length cT.lparams.length)) =
      (ftys.take k).map (·.instL (VLevel.shift pre.length cT.lparams.length)) := by
    rw [← hcf]; simp [List.map_take, Function.comp_def]
  have hisl' : is.length = T'.indices.length := by
    have h1 := hargl
    rw [getElem!_pos stats.nindices itIdx (Array.getElem?_eq_some_iff.1 hT'i).1,
      (Array.getElem?_eq_some_iff.1 hT'i).2] at h1
    have : stats.params.size = pfvs.length := by
      rw [← Array.length_toList, hpar, List.length_map]
    omega
  let ra : VRecArg := ⟨xtys, itIdx, is⟩
  have hra : ∃ T, d₀.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
      cb.venv.IsDefEqU cb.lparams.length (((c.fields.take k).map
          (·.type.instL (VLevel.shift pre.length cT.lparams.length))).reverse ++
          (d₀.params.map (·.instL (VLevel.shift pre.length cT.lparams.length))).reverse)
        (f.type.instL (VLevel.shift pre.length cT.lparams.length))
        (.foralls (ra.binders.map (·.instL (VLevel.shift pre.length cT.lparams.length)))
          (.appN (.const T.name (VLevel.shift pre.length cT.lparams.length))
          (VExpr.bvars d₀.params.length (k + ra.binders.length) ++
            ra.indices.map (·.instL (VLevel.shift pre.length cT.lparams.length))))) := by
    refine ⟨T', hT', hisl', ?_⟩
    rw [htake, hd₀p, hfty]
    rw [hV₀, VExpr.instL_foralls, VExpr.instL_appN, List.map_append, VExpr.instL_bvars] at hrel₁
    simp only [VExpr.instL, VLevel.params_inst hshl, List.map_reverse, List.map_append,
      List.reverse_append] at hrel₁
    rw [hT'n, ← hlenp, show ra.binders.length = xfvs.length from hxl]
    exact hrel₁
  have hC' := hC.setRecArg hfk hra
  -- the inductive hypothesis is a type
  obtain ⟨Tj, hTj, -, -⟩ := hC.ctor
  have hF := hB.only hC'
  have hcj := VInductDecl.mem_only_ctors_self (c := c.setRecArg k ra) hTj
  have hk'' : (c.setRecArg k ra).fields[k]? = some { f with recArg := some ra } := by
    rw [VConstructor.setRecArg_getElem?, if_pos rfl, hfk]; rfl
  have hty := VInductDecl.minor_ih (v := ml) hF (VInductDecl.mem_allCtors_of_ctors hcj) hk'' rfl
    Qs' ihtys hq hih
  simp only [VInductDecl.only_allTypes_length, VInductDecl.allTypes_of_aux hB.aux,
    VInductDecl.only_types_length, VInductDecl.only_motiveTypes, VInductDecl.only_params,
    VConstructor.map_type_instL_setRecArg, VConstructor.setRecArg_length, hd₀T, hd₀p] at hty
  have hEctx : E.vlctx.toCtx = ihtys.reverse ++
      (VExpr.liftTele (types.length + q)
        (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length)))).reverse ++
      Qs'.reverse ++ (d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml).reverse ++
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length))).reverse := by
    rw [hET.toCtx]; simp
  have hcfl : c.fields.length = fvs.length := by rw [← hfl, ← hcf, List.length_map]
  have hcfm : c.fields.map (·.type.instL (VLevel.shift pre.length cT.lparams.length)) =
      ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length)) := by
    rw [← hcf]; simp [Function.comp_def]
  rw [hcfm, hcfl, ← hEctx] at hty
  -- the view of the kernel's context with the binders
  obtain ⟨N, ρN, hEN, hWN, hNT, hNk, hNb⟩ := hI.comp
  have hNwf := hEN.wf
  rw [hvenvx, hlpx] at hNwf
  have hndN : ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ xfvs).Nodup := by
    have := hEN.wf.fvars_nodup; rw [hNT.fvars] at this; exact List.nodup_reverse.1 this
  have hNlen := hNT.length_eq
  simp only [List.length_append, List.length_map, List.length_zipIdx] at hNlen
  have hm := hNT.find?_fvar hndN (j := pfvs.length + itIdx) (by simp; omega)
  have hu := hNT.find?_fvar hndN (j := pfvs.length + types.length + q + k) (by simp; omega)
  have hmget : ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ xfvs)[pfvs.length + itIdx]'(by
      simp; omega) = motfvs[itIdx]'(hmot ▸ hitT) := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega), List.getElem_append_left (by simp; omega)]
    simp
  have hfget : ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ xfvs)[pfvs.length + types.length +
      q + k]'(by simp; omega) = fvs[k] := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    rw [List.getElem_append_right (by (try simp only [List.length_append]); omega)]
    rw [List.getElem_append_right (by (try simp only [List.length_append]); omega)]
    rw [List.getElem_append_left (by (try simp only [List.length_append]); omega)]
    congr 1; omega
  rw [hmget] at hm; rw [hfget] at hu
  have hpsz : stats.params.size = pfvs.length := by
    rw [← Array.length_toList, hpar, List.length_map]
  have hidx : List.Forall₂ (TrExprS cbx.venv cbx.lparams N.vlctx) itIndices.toList
      (is.map fun e => (e.instL (VLevel.shift pre.length cT.lparams.length)).lift'
        ((reseatLift (types.length + q) k fvs.length r).consN xfvs.length)) := by
    rw [hidxL, hpsz, List.forall₂_map_right_iff]
    exact Lean4Lean.List.Forall₂.imp (fun _ _ h => hI.sub.trExprS_to hWN hEN.wf.tr.wf h) hisTr
  have hag : ∀ x ∈ xfvs, (cbx.lctx.find? x).map LocalDecl.erase =
      (N.lctx.find? x).map LocalDecl.erase := fun x hx =>
    hEN.lctx x (by rw [hNT.fvars]; simp [hx])
  have hmi : ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ xfvs).length - 1 -
      (pfvs.length + itIdx) =
      xfvs.length + (r + fvs.length + q + (types.length - 1 - itIdx)) := by simp; omega
  have hui : ((pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs) ++ xfvs).length - 1 -
      (pfvs.length + types.length + q + k) = xfvs.length + (r + (fvs.length - 1 - k)) := by
    simp; omega
  rw [hmi] at hm; rw [hui] at hu
  have hNb' : N.dropN xfvs.length (by rw [hNT.length]; simp; omega) = E :=
    (TypeChecker.MLCtx.dropN_congr rfl _ _).trans hNb
  have e1 : xfvs.length + (r + fvs.length + q + (types.length - 1 - itIdx)) =
      xtys.length + r + fvs.length + q + (types.length - 1 - itIdx) := by omega
  have e2 : xfvs.length + (r + (fvs.length - 1 - k)) = xtys.length + r + (fvs.length - 1 - k) := by
    omega
  have hspec : ihSpec (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length r k ra =
      .foralls (xtys.zipIdx.map fun (A, j) =>
          (A.instL (VLevel.shift pre.length cT.lparams.length)).lift'
            ((reseatLift (types.length + q) k fvs.length r).consN j))
        (.app (.appN (.bvar (xfvs.length + (r + fvs.length + q + (types.length - 1 - itIdx))))
          (is.map fun e => (e.instL (VLevel.shift pre.length cT.lparams.length)).lift'
            ((reseatLift (types.length + q) k fvs.length r).consN xfvs.length)))
        (.appN (.bvar (xfvs.length + (r + (fvs.length - 1 - k)))) (VExpr.bvars xfvs.length 0))) := by
    simp only [ihSpec, lift'_reseatLift]
    rw [e1, e2, ← hxl]
  have hty2 : cb.venv.IsType cb.lparams.length E.vlctx.toCtx
      (ihSpec (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length r k ra) := hty
  have hty' := hty2
  rw [hspec, ← hNb', ← hvenvx, ← hlpx] at hty'
  have henvx' : cbx.venv.WF := hvenvx ▸ hB.wf
  obtain ⟨hk3, heq3, htr3, hisT3⟩ := ihType_tr (lctx := cbx.lctx) henvx' hEN.wf hNT
    (by simp [hxl]) hag hm hu hidx hty'
  refine WF.bind (Q := (· = cbx.lctx)) (fun _ h => by cases h; rfl) fun lctx hl => ?_
  subst hl
  rw [← Array.forIn_toList]
  refine WF.bind (WF.forIn_list (P := fun x => ∀ d, cbx.lctx.findFVar? x = some d →
      (d.type.anySubterm fun | .const c _ => blockNames.contains c | _ => false) = false)
    fun x _ _ => ?_) fun _ hfree => ?_
  · split
    · next d hd =>
      split
      · exact WF.throw
      · next hc =>
        refine WF.pure ⟨fun d' hd' => ?_, _, rfl⟩
        rw [hd] at hd'; cases hd'; simpa using hc
    · next hd => exact WF.pure ⟨fun d' hd' => (hd d' hd').elim, _, rfl⟩
  have hdnames : d₀.names = types.map (·.name) := by
    refine List.ext_getElem (by simp [VInductDecl.names, hd₀T]) fun i h1 h2 => ?_
    obtain ⟨T'', hT'', hn, -⟩ := hd₀t i (by simpa using h2)
    simp only [VInductDecl.names, List.getElem_map]
    rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hT''), hn]
  -- what the kernel checks of a term rules out the block's types in it
  have hocc_of {e : Expr} (h : e.anySub (blockP blockNames) = false) :
      hasIndOcc stats.indConsts e = false := by
    rw [hasIndOcc_eq]
    refine anySub_mono (fun x hx => ?_) h
    obtain ⟨c, us, rfl, hc⟩ := (indOccP_spec hind).1 x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    exact hBN t ht
  rw [hrec itIdx hitT, show itIndices = itIndices.toList.toArray by simp]
  refine WF.pure ⟨ra, hC', ⟨T', hT', hisl', ?_, ?_, ?_⟩, rfl, ?_, hty2, ?_, hk2, ?_, ?_⟩
  · rw [hfty, hT'n]
    rw [hV₀, ← hxl, List.reverse_append, hlenp] at hrel₀
    exact hrel₀
  · -- the binders: the kernel checked their declarations
    rw [hdnames]
    refine List.all_eq_true.2 fun b hb => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hix : i < xfvs.length := by have : i < xtys.length := hi; omega
    have hkf : k ≤ fvs.length := Nat.le_of_lt hk
    have e1 : (pfvs ++ fvs.take k ++ xfvs)[pfvs.length + (k + i)]'(by simp; omega) =
        xfvs[i] := by
      rw [List.getElem_append_right (by simp; omega)]
      congr 1; simp; omega
    have e2 : (params ++ ftys.take k ++ xtys)[pfvs.length + (k + i)]'(by simp; omega) =
        xtys[i] := by
      rw [List.getElem_append_right (by simp; omega)]
      congr 1; simp; omega
    have := hI.tele.not_mentions hNM hMx (pfvs.length + (k + i)) (by simp; omega)
      (by simp; omega) fun d hd => ?_
    · rw [e2] at this; simpa using this
    rw [e1] at hd
    have hag' := hI.sub.lctx xfvs[i] (by
      show xfvs[i] ∈ Mx.vlctx.fvars; rw [hI.tele.fvars]; simp)
    change (cbx.lctx.find? xfvs[i]).map LocalDecl.erase = (Mx.lctx.find? xfvs[i]).map _ at hag'
    rw [hd] at hag'
    obtain ⟨d', hd', he⟩ : ∃ d', cbx.lctx.find? xfvs[i] = some d' ∧ d'.erase = d.erase := by
      cases h : cbx.lctx.find? xfvs[i] <;> rw [h] at hag' <;> simp_all
    have hf := hfree (.fvar xfvs[i]) (by simp) d' (by
      simp only [LocalContext.findFVar?, Expr.fvarId!, hd'])
    have hf' := (anySubterm_blockP blockNames d'.type).symm.trans hf
    rw [(LocalDecl.erase_type he).1] at hf'
    exact hocc_of hf'
  · -- the indices: the kernel checked the type's arguments
    rw [hdnames]
    refine List.all_eq_true.2 fun b hb => ?_
    obtain ⟨a, ha, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_r hisTr b hb
    have hpsz : stats.params.size = pfvs.length := by
      rw [← Array.length_toList, hpar, List.length_map]
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [List.getElem_drop] at htr
    have hlt : pfvs.length + j < uiTy.getAppArgs.size := by
      rw [← Array.length_toList, Expr.getAppArgs_toList]; simp at hj; omega
    have := (isValidIndAppIdx_true hvalI).2.2.2 (pfvs.length + j) (by omega) hlt
    have harg : uiTy.getAppArgs[pfvs.length + j] = uiTy.getAppArgsList[pfvs.length + j]'(by
        rw [← Expr.getAppArgs_toList]; simpa using hlt) := by
      simp only [← Expr.getAppArgs_toList, Array.getElem_toList]
    rw [getElem!_pos uiTy.getAppArgs (pfvs.length + j) hlt, harg] at this
    simpa using hNM hMx.tr.wf hI.tele.vlam_entries htr this
  · rw [heq3, hspec]
    have := htr3
    rw [TypeChecker.MLCtx.dropN_congr rfl hk3 (by rw [hNT.length]; simp; omega), hNb', hvenvx,
      hlpx] at this
    exact this
  · rw [heq3, ← henvx]
    refine stripAnnotations_mkForall _ hNT hk3 (stripAnnotations_fvar_head
      (fv := motfvs[itIdx]'(hmot ▸ hitT)) ?_)
    simp [Expr.getAppFn, Expr.getAppFn_mkAppN']
  · -- the pieces of the hypothesis' value, in the small context
    obtain ⟨hkx, hbase⟩ := hI.base
    have hndx : (pfvs ++ fvs.take k ++ xfvs).Nodup := by
      have := hMx.tr.wf.fvars_nodup; rw [hI.tele.fvars] at this; exact List.nodup_reverse.1 this
    refine ⟨rfl, rfl, by simpa using hxl.symm, fun i hi => ?_, ?_⟩
    · have hi' : i < xfvs.length := by simpa using hi
      obtain ⟨d, hd, htrd⟩ := tele_binder_tr hI.tele hMx hxl.symm hkx i hi'
      have hag' := hI.sub.lctx xfvs[i] (by
        show xfvs[i] ∈ Mx.vlctx.fvars; rw [hI.tele.fvars]; simp)
      change (cbx.lctx.find? xfvs[i]).map LocalDecl.erase = (Mx.lctx.find? xfvs[i]).map _ at hag'
      rw [hd] at hag'
      obtain ⟨d', hd', he⟩ : ∃ d', cbx.lctx.find? xfvs[i] = some d' ∧ d'.erase = d.erase := by
        cases h : cbx.lctx.find? xfvs[i] <;> rw [h] at hag' <;> simp_all
      obtain ⟨hty, -⟩ := LocalDecl.erase_type he
      simp only [Array.getElem_mapIdx, List.getElem_toArray, List.getElem_map,
        LocalContext.findFVar?, Expr.fvarId!, hd']
      have hxnd : xfvs.Nodup := (List.nodup_append.1 hndx).2.1
      rw [hty, Expr.abstractRange_fvars, Expr.abstract'_eq_abstractList
        (Nat.le_of_eq (hMx.find?_closed hd).type) ((List.take_sublist ..).nodup hxnd), ← hbase]
      exact htrd
    · simp only [Array.toList_map, Expr.abstract_fvars]
      have hidxs : itIndices.toList = uiTy.getAppArgsList.drop pfvs.length := by
        rw [hidxL, ← Array.length_toList, hpar, List.length_map]
      rw [hidxs, List.forall₂_map_left_iff, ← hbase]
      refine Lean4Lean.List.Forall₂.imp (fun _ _ h => ?_) hisTr
      have h' : TrExprS cT.venv cT.lparams Mx.vlctx _ _ := h
      rw [Expr.abstract'_eq_abstractList (Mx.noBV ▸ h'.closed).looseBVarRange_le
        (List.nodup_append.1 hndx).2.1]
      simpa using TrExprS.abstractTop xfvs.length hI.tele rfl hxl hndx hkx [] nofun
        (by simpa using h')
  · intro dk n us ax hdk' hty hax
    rw [hdk] at hdk'; cases hdk'
    have := (hI.stop ⟨n, us, ax, hdkty.symm.trans hty, hax⟩).1
    subst this
    show xtys = []
    have h0 : xtys.length = 0 := hxl
    exact List.eq_nil_of_length_eq_zero h0

end AddInductive

theorem List.modify_append_cons {α} (A B : List α) (x : α) (g : α → α) :
    (A ++ x :: B).modify A.length g = A ++ g x :: B := by
  apply List.ext_getElem?; intro n
  rw [List.getElem?_modify]
  split
  · subst n; simp
  · rename_i h
    rcases Nat.lt_or_ge n A.length with h1 | h1
    · simp [List.getElem?_append_left h1]
    · rw [List.getElem?_append_right h1, List.getElem?_append_right h1]
      obtain ⟨m, hm⟩ : ∃ m, n - A.length = m + 1 := ⟨n - A.length - 1, by omega⟩
      rw [hm]; simp

theorem VConstructor.recFields_setRecArg {c : VConstructor} {k : Nat} (hk : k < c.fields.length)
    (hnone : c.fields[k].recArg = none) (hlt : ∀ p ∈ c.recFields, p.1 < k) (ra : VRecArg) :
    (c.setRecArg k ra).recFields = c.recFields ++ [(k, ra)] := by
  obtain ⟨A, f, B, hAB, hA⟩ : ∃ A f B, c.fields = A ++ f :: B ∧ A.length = k :=
    ⟨c.fields.take k, c.fields[k], c.fields.drop (k + 1), by simp, by simp; omega⟩
  have hf : c.fields[k] = f := by simp [hAB, ← hA]
  rw [hf] at hnone
  have hmod : (c.setRecArg k ra).fields = A ++ { f with recArg := some ra } :: B := by
    simp only [setRecArg, hAB, ← hA]
    exact List.modify_append_cons A B f _
  have hB : (B.zipIdx (k + 1)).filterMap
      (fun x => Option.map (fun y => (x.snd, y)) x.fst.recArg) = [] := by
    rw [List.filterMap_eq_nil_iff]
    rintro ⟨f', k'⟩ hm
    cases hr : f'.recArg with
    | none => simp
    | some ra' =>
      exfalso
      have hm' : ((k', ra') : Nat × VRecArg) ∈ c.recFields := by
        simp only [recFields, List.mem_filterMap, hAB, List.zipIdx_append, List.zipIdx_cons]
        refine ⟨(f', k'), ?_, by simp [hr]⟩
        simp only [List.mem_append, List.mem_cons, Nat.zero_add, hA]
        exact .inr (.inr hm)
      have := hlt _ hm'
      have := (List.mem_zipIdx hm).1
      omega
  simp only [recFields, hmod, hAB, List.zipIdx_append, List.zipIdx_cons, List.filterMap_append,
    List.filterMap_cons, hA, hnone, Option.map_none]
  simp only [Option.map_some, Nat.zero_add] at hB ⊢
  rw [hB]; simp

namespace AddInductive

theorem recFvs_cons (fv : FVarId) (fvs : List FVarId) (b : Bool) (rs : List Bool) :
    recFvs (fv :: fvs) (b :: rs) = (if b then [fv] else []) ++ recFvs fvs rs := by
  cases b <;> simp [recFvs]

/-- The fields `recFvs` picks, by their positions, in order. -/
theorem recFvs_positions : ∀ {fvs : List FVarId} {rs : List Bool}, rs.length = fvs.length →
    ∃ ks : List Nat, ks.length = (recFvs fvs rs).length ∧ ks.Pairwise (· < ·) ∧
      (∀ k ∈ ks, k < fvs.length) ∧
      ∀ i (h : i < ks.length), ∃ hk : ks[i] < fvs.length, (recFvs fvs rs)[i]? = some fvs[ks[i]]
  | [], [], _ => ⟨[], rfl, .nil, nofun, nofun⟩
  | fv :: fvs, b :: rs, h => by
    obtain ⟨ks, h1, h2, h3, h4⟩ := recFvs_positions (fvs := fvs) (rs := rs) (by simpa using h)
    refine ⟨(if b then [0] else []) ++ ks.map (· + 1), ?_, ?_, ?_, ?_⟩
    · rw [recFvs_cons]; cases b <;> simp [h1]
    · rw [List.pairwise_append]
      refine ⟨by split <;> simp, List.Pairwise.map _ (fun _ _ => by omega) h2, ?_⟩
      intro a ha b hb; split at ha <;> simp at ha hb
      obtain ⟨_, _, rfl⟩ := hb; omega
    · intro k hk
      simp only [List.mem_append, List.mem_map] at hk
      rcases hk with hk | ⟨k', hk', rfl⟩
      · split at hk <;> simp at hk; subst hk; simp
      · simp [h3 k' hk']
    · intro i hi
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, List.nil_append, List.length_map] at hi ⊢
        obtain ⟨hk, e⟩ := h4 i hi
        refine ⟨by simp; omega, ?_⟩
        simp only [recFvs_cons, Bool.false_eq_true, if_false, List.nil_append, List.getElem_map]
        rw [e]; rfl
      | true =>
        simp only [if_true, List.singleton_append, List.length_cons, List.length_map] at hi ⊢
        cases i with
        | zero => exact ⟨by simp, by simp [recFvs_cons]⟩
        | succ i =>
          obtain ⟨hk, e⟩ := h4 i (by omega)
          refine ⟨by simp; omega, ?_⟩
          simp only [recFvs_cons, if_true, List.singleton_append, List.getElem?_cons_succ,
            List.getElem_cons_succ, List.getElem_map]
          rw [e]

/-- A minor premise's inductive hypotheses, as `minorType` states them. -/
def ihsOf (ls : List VLevel) (T q m : Nat) (c : VConstructor) : List VExpr :=
  c.recFields.zipIdx.map fun ((k, ra), r) => ihSpec ls T q m r k ra

/-- What `loopU` keeps, having built the inductive hypotheses `vfvs` of the first `i` recursive
fields, whose positions `ks` lists: `c` sees those fields as recursive, and the view `E` of the
kernel's context holds the parameters, motives, earlier minor premises, the fields, and those
hypotheses, at their types in the minor premise. -/
structure UInv (cT : VContext) (X : Name → Prop) (pre : List Name) (pfvs : List FVarId)
    (params : List VExpr) (d₀ : VInductDecl) (ml : VLevel) (j : Nat) (Mf : TypeChecker.MLCtx)
    (hMf : Mf.WF cT.venv cT.lparams) (fvs : List FVarId) (ftys : List VExpr) (ks : List Nat)
    (q : Nat) (Qs' : List VExpr) (motfvs minfvs : List FVarId) (T : Nat) (P : VContext → Prop)
    (F₀ : List FVarId) (E₀ : TypeChecker.MLCtx) (c₀ : VConstructor) (i : Nat)
    (vfvs : List FVarId) (infos : List IHInfo) (c : VConstructor) (E : TypeChecker.MLCtx)
    (ρE : Lift) (cb : VContext) (ρf : Lift) : Prop where
  ctor : d₀.CtorFacts cb.venv cb.lparams.length (VLevel.shift pre.length cT.lparams.length) j c
  types : c.fields.map (·.type) = ftys
  recs : c.recFields.map (·.1) = ks.take i
  sub : Sub X pre ρf (cT.small Mf hMf) cb
  pred : P cb
  fvars : cb.mlctx.vlctx.fvars = vfvs.reverse ++ F₀
  len : vfvs.length = i
  ext : Ext E cb ρE
  tele : E.IsTele (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs)
    (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
      d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs' ++
      VExpr.liftTele (T + q)
        (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++
      ihsOf (VLevel.shift pre.length cT.lparams.length) T q fvs.length c)
  lift : ∃ hk', VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx
    (E.dropN i hk').vlctx 0 ((Lift.skipN .refl (T + q)).consN fvs.length) 0
  /-- What `mkRecRules` builds each hypothesis' value from. -/
  pieces : List.Forall₂ (fun (ih : IHInfo) (p : Nat × VRecArg) => ∃ (hp : p.1 < fvs.length)
    (hk' : fvs.length - p.1 ≤ Mf.length),
      IHPieces cT.venv cT.lparams (Mf.dropN (fvs.length - p.1) hk') (fvs[p.1]'hp) ih p.2 ∧
      ∀ dk n us ax, Mf.lctx.find? (fvs[p.1]'hp) = some dk → dk.type = .const n us →
        cT.env.find? n = some (.axiomInfo ax) → p.2.binders = [])
    infos c.recFields
  infos : infos.map (·.itIdx) = c.recFields.map (·.2.typeIdx)
  recArgs : ∀ k f ra, c.fields[k]? = some f → f.recArg = some ra →
    d₀.RecArgAt cT.venv cT.lparams.length params ftys k f.type ra
  base : ∃ hk, E.dropN i hk = E₀
  head : c.name = c₀.name ∧ c.type = c₀.type ∧ c.indices = c₀.indices ∧
    c.fields.map (·.level) = c₀.fields.map (·.level)

theorem loopU.WF [VEnv.Injective] {blockNames : NameSet} {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {pfvs : List FVarId} {params : List VExpr}
    (hMpT : Mp.IsTele pfvs params) {stats : InductiveStats}
    (hpar : stats.params.toList = pfvs.map .fvar) (hlev : stats.levels = cT.lparams.map .param)
    {types : List InductiveType}
    (hind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels)
    (hNM : NotMentionsOK cT.venv cT.lparams stats types)
    (hBN : ∀ t ∈ types, blockNames.contains t.name)
    (hUs : cT.lparams.Nodup) {d₀ : VInductDecl} (hd₀p : d₀.params = params)
    (hd₀T : d₀.types.length = types.length)
    (hd₀t : ∀ t (ht : t < types.length), ∃ T', d₀.types[t]? = some T' ∧
      T'.name = types[t].name ∧ stats.nindices[t]? = some T'.indices.length)
    {ml : VLevel} {j : Nat}
    {Mf : TypeChecker.MLCtx} {hMf : Mf.WF cT.venv cT.lparams} {fvs : List FVarId}
    {ftys : List VExpr} (hMfT : Mf.IsTele (pfvs ++ fvs) (params ++ ftys))
    {rs : List Bool} {ks : List Nat} (hks : ks.length = (recFvs fvs rs).length)
    (hksp : ks.Pairwise (· < ·))
    (hksu : ∀ i (h : i < ks.length), ∃ hk : ks[i] < fvs.length,
      (recFvs fvs rs)[i]? = some fvs[ks[i]])
    {q : Nat} {Qs' : List VExpr} (hq : Qs'.length = q) {motfvs minfvs : List FVarId}
    (hmot : motfvs.length = types.length) (hmin : minfvs.length = q)
    {recInfos : Array RecInfo}
    (hrec : ∀ t (ht : t < types.length), recInfos[t]!.motive = .fvar (motfvs[t]'(hmot ▸ ht)))
    {F₀ : List FVarId} {E₀ : TypeChecker.MLCtx} {c₀ : VConstructor} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    (hPB : ∀ cb, P cb → d₀.BlockFacts cb.venv cb.lparams.length
      (VLevel.shift pre.length cT.lparams.length))
    {k : Array Expr → Array IHInfo → M α} {Q}
    (H : ∀ vfvs infos c E ρE cb ρf,
      UInv cT X pre pfvs params d₀ ml j Mf hMf fvs ftys ks q Qs' motfvs minfvs types.length P F₀
        E₀ c₀ ks.length vfvs infos c E ρE cb ρf →
      WF cb (k (vfvs.map .fvar).toArray infos.toArray) Q) :
    ∀ n i vfvs infos c E ρE cb ρf, ks.length = i + n →
      UInv cT X pre pfvs params d₀ ml j Mf hMf fvs ftys ks q Qs' motfvs minfvs types.length P F₀
        E₀ c₀ i vfvs infos c E ρE cb ρf →
      WF cb (mkRecInfos.loopU stats blockNames ((recFvs fvs rs).map .fvar).toArray recInfos i
        (vfvs.map .fvar).toArray infos.toArray k) Q := by
  intro n
  induction n with
  | zero =>
    intro i vfvs infos c E ρE cb ρf hn hI
    rw [mkRecInfos.loopU, dif_neg (by simp; omega)]
    obtain rfl : i = ks.length := by omega
    exact H _ _ _ _ _ _ _ hI
  | succ n ih =>
    intro i vfvs infos c E ρE cb ρf hn hI
    rw [mkRecInfos.loopU, dif_pos (by simp; omega)]
    have hi : i < ks.length := by omega
    obtain ⟨hk, hu⟩ := hksu i hi
    have hui : ((recFvs fvs rs).map Expr.fvar).toArray[i]'(by simp; omega) = .fvar fvs[ks[i]] := by
      have hi' : i < (recFvs fvs rs).length := by omega
      rw [List.getElem?_eq_getElem hi'] at hu
      simp [Option.some.inj hu]
    simp only [hui]
    have hlenp : pfvs.length = params.length := hMpT.length_eq
    have hfl : ftys.length = fvs.length := by
      have := hMfT.length_eq; simp [hlenp] at this; omega
    have hcl : c.fields.length = fvs.length := by rw [← hfl, ← hI.types, List.length_map]
    obtain ⟨f, hfk⟩ : ∃ f, c.fields[ks[i]]? = some f :=
      ⟨_, List.getElem?_eq_getElem (l := c.fields) (hcl ▸ hk)⟩
    have hrl : c.recFields.length = i := by
      have := congrArg List.length hI.recs; simp at this; omega
    have hihl : (ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length
        c).length = i := by simp [ihsOf, hrl]
    refine WF.bind (ihInfo.WF hMpT hpar hlev hind hUs hd₀p hd₀T hd₀t (ml := ml)
      (hPB cb hI.pred) hI.ctor hMfT hI.types hI.sub hk hfk hq hmot hmin hI.len hihl hI.ext
      hI.tele hI.lift hrec hNM hBN) fun ⟨viTy, ihI⟩ ⟨ra, hC', hRA, hidx, htr, hisT, hstrip, hkI, hpcs⟩ => ?_
    dsimp only
    refine WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
    refine WF.bind (Q := (· = viTy)) (fun a h => by
      change stripAnnotations _ _ = _ at h; rw [hstrip] at h; cases h; rfl) fun _ he => ?_
    subst he
    refine WF.withLocalDecl (hI.ext.trExprS htr) (hI.ext.isType hisT) ?_
    -- the positions before are smaller
    have hbefore : ∀ x ∈ ks.take i, x < ks[i] := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_take] at hr
      simp only [List.getElem_take]
      exact List.pairwise_iff_getElem.1 hksp r i (by omega) hi (by omega)
    have hlt : ∀ p ∈ c.recFields, p.1 < ks[i] := fun p hp =>
      hbefore _ (hI.recs ▸ List.mem_map_of_mem hp)
    have hnone : (c.fields[ks[i]]'(hcl ▸ hk)).recArg = none := by
      cases h : (c.fields[ks[i]]'(hcl ▸ hk)).recArg with
      | none => rfl
      | some ra₀ =>
        exfalso
        have hm : ((ks[i], ra₀) : Nat × VRecArg) ∈ c.recFields := by
          simp only [VConstructor.recFields, List.mem_filterMap]
          exact ⟨(c.fields[ks[i]]'(hcl ▸ hk), ks[i]), List.mem_zipIdx_iff_getElem?.2
            (by simp), by simp [h]⟩
        exact Nat.lt_irrefl _ (hlt _ hm)
    have hrf' := VConstructor.recFields_setRecArg (hcl ▸ hk) hnone hlt ra
    have harr1 : (List.map Expr.fvar vfvs).toArray.push (.fvar ⟨cb.ngen.curr⟩) =
        (List.map Expr.fvar (vfvs ++ [⟨cb.ngen.curr⟩])).toArray := by simp
    have harr2 : infos.toArray.push ihI = (infos ++ [ihI]).toArray := by simp
    rw [harr1, harr2]
    have hihs : ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length
        (c.setRecArg ks[i] ra) =
        ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c ++
          [ihSpec (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length i ks[i]
            ra] := by
      simp [ihsOf, hrf', List.zipIdx_append, hrl]
    obtain ⟨hk', hlift⟩ := hI.lift
    refine ih (i + 1) _ _ (c.setRecArg ks[i] ra) _ _ _ _ (by omega) {
      ctor := hC'
      types := by rw [VConstructor.setRecArg_types, hI.types]
      recs := by
        rw [hrf', List.map_append, hI.recs, List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      sub := hI.sub.skip _ _
      pred := hP _ _ _ _ _ _ _ hI.pred
      fvars := ?_
      len := by simp [hI.len]
      ext := hI.ext.push htr hisT
      tele := ?_
      lift := ⟨by simp [TypeChecker.MLCtx.length]; omega, ?_⟩
      infos := by rw [hrf']; simp [hI.infos, hidx]
      pieces := by
        rw [hrf']
        exact (Lean4Lean.List.Forall₂.append_of_left
          (Lean4Lean.List.Forall₂.length_eq hI.pieces)).2 ⟨hI.pieces, .cons ⟨hk, hkI, hpcs⟩ .nil⟩
      recArgs := fun k' f' ra' hk' hra' => by
        rw [VConstructor.setRecArg_getElem?] at hk'
        split at hk'
        · subst k'
          rw [hfk] at hk'; cases hk'; cases hra'; exact hRA
        · exact hI.recArgs k' f' ra' hk' hra'
      base := ?_
      head := ?_ }
    · show VLCtx.fvars (_ :: cb.mlctx.vlctx) = _
      simp [VLCtx.fvars_cons_some, hI.fvars]
    · rw [hihs]; simpa using hI.tele.vlam
    · rw [TypeChecker.MLCtx.dropN_congr (show i + 1 = i + 1 from rfl) _ (by
        simp [TypeChecker.MLCtx.length]; omega)]
      exact hlift
    · obtain ⟨hkb, hb⟩ := hI.base
      exact ⟨by simp [TypeChecker.MLCtx.length]; omega, hb⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hI.head
      refine ⟨h1, h2, h3, ?_⟩
      rw [← h4]
      apply List.ext_getElem? fun n => ?_
      simp only [VConstructor.setRecArg, List.getElem?_map, List.getElem?_modify]
      split <;> cases c.fields[n]? <;> rfl

/-- A minor premise's type, `Π fields ihs, body` in the kernel's local context, translates over a
view `E` of it holding the fields and inductive hypotheses on top. -/
theorem minorTy_tr {env : VEnv} {Us : List Name} (henv : env.WF) {lctx : LocalContext}
    {E : TypeChecker.MLCtx} (hE : E.WF env Us) {Bfvs fvs vfvs : List FVarId}
    {Btys Ftys Itys : List VExpr} (hT : E.IsTele (Bfvs ++ fvs ++ vfvs) (Btys ++ Ftys ++ Itys))
    (hfl : fvs.length = Ftys.length) (hvl : vfvs.length = Itys.length)
    (hag : ∀ x ∈ fvs ++ vfvs, (lctx.find? x).map LocalDecl.erase =
      (E.lctx.find? x).map LocalDecl.erase)
    {e : Expr} {e' : VExpr} (he : TrExprS env Us E.vlctx e e')
    (heT : env.IsType Us.length E.vlctx.toCtx e') :
    ∃ hk : fvs.length + vfvs.length ≤ E.length,
      TrExprS env Us (E.dropN (fvs.length + vfvs.length) hk).vlctx
        (lctx.mkForall (fvs.map .fvar).toArray (lctx.mkForall (vfvs.map .fvar).toArray e))
        (.foralls (Ftys ++ Itys) e') ∧
      env.IsType Us.length (E.dropN (fvs.length + vfvs.length) hk).vlctx.toCtx
        (.foralls (Ftys ++ Itys) e') ∧
      ∃ E₁ hk₁ hk₂, E.dropN vfvs.length hk₁ = E₁ ∧
        lctx.mkForall (fvs.map .fvar).toArray (lctx.mkForall (vfvs.map .fvar).toArray e) =
          E₁.mkForall fvs.length hk₂ (E.mkForall vfvs.length hk₁ e) := by
  obtain ⟨hk₁, eq₁, trS₁, isT₁⟩ := mkForall_tele (lctx := lctx) henv hE
    (fvs₁ := Bfvs ++ fvs) (fvs₂ := vfvs) (tys₁ := Btys ++ Ftys) (tys₂ := Itys) hT hvl
    (fun x hx => hag x (List.mem_append_right _ hx)) he heT
  obtain ⟨-, -, -, -, hT₁⟩ := hT.vlctx_split vfvs.length rfl hvl hk₁
  have hE₁ := hE.dropN vfvs.length hk₁
  have hag₁ : ∀ x ∈ fvs, (lctx.find? x).map LocalDecl.erase =
      ((E.dropN vfvs.length hk₁).lctx.find? x).map LocalDecl.erase := by
    intro x hx
    rw [hag x (List.mem_append_left _ hx)]
    have hx' : x ∈ (E.dropN vfvs.length hk₁).vlctx.fvars := by
      rw [hT₁.fvars]; simp [hx]
    rw [hE.find?_dropN vfvs.length hk₁ hx']
  obtain ⟨hk₂, eq₂, trS₂, isT₂⟩ := mkForall_tele (lctx := lctx) henv hE₁
    (fvs₁ := Bfvs) (fvs₂ := fvs) (tys₁ := Btys) (tys₂ := Ftys) hT₁ hfl hag₁
    trS₁ isT₁
  have hk : fvs.length + vfvs.length ≤ E.length := by
    have := TypeChecker.MLCtx.length_dropN E vfvs.length hk₁; omega
  have e₂ : (E.dropN vfvs.length hk₁).dropN fvs.length hk₂ =
      E.dropN (fvs.length + vfvs.length) hk := by
    rw [TypeChecker.MLCtx.dropN_dropN E _ _ hk₁ hk₂ (by omega)]
    exact TypeChecker.MLCtx.dropN_congr (Nat.add_comm _ _) _ _
  refine ⟨hk, ?_, ?_, _, hk₁, hk₂, rfl, by rw [eq₁, eq₂]⟩
  · rw [eq₁, eq₂, ← e₂, VExpr.foralls_append]; exact trS₂
  · rw [← e₂, VExpr.foralls_append]; exact isT₂

theorem _root_.List.Forall₂.take_append {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, l₁.length = m₁.length →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) → List.Forall₂ R l₁ m₁
  | [], _, [], _, _, _ => .nil
  | _ :: _, _, _ :: _, _, hl, .cons h t => .cons h (List.Forall₂.take_append (Nat.succ.inj hl) t)

/-- A minor premise's body, the motive at the constructor's indices applied to the constructor at
the parameters and fields, translates over a view `E` of the kernel's context, once the
translation is typed. -/
theorem minorBody_tr {env : VEnv} {Us : List Name} (henv : env.WF) {E : TypeChecker.MLCtx}
    (hE : E.WF env Us) {pfvs Ofvs fvs vfvs : List FVarId} {Ptys Otys Ftys Itys : List VExpr}
    (hT : E.IsTele (pfvs ++ Ofvs ++ fvs ++ vfvs) (Ptys ++ Otys ++ Ftys ++ Itys))
    {mfv : FVarId} {mpos : Nat} {mty : VExpr}
    (hm : E.vlctx.find? (.inr mfv) = some (.bvar mpos, mty))
    {itIndices : List Expr} {idx' : List VExpr}
    (hidx : List.Forall₂ (TrExprS env Us E.vlctx) itIndices idx')
    {cn : Name} {ls : List Level} {ls' : List VLevel}
    (hc : TrExprS env Us E.vlctx (.const cn ls) (.const cn ls')) {v : VLevel}
    (hty : env.HasType Us.length E.vlctx.toCtx
      (.app (.appN (.bvar mpos) idx') (.appN (.const cn ls')
        (VExpr.bvars pfvs.length (Ofvs.length + fvs.length + vfvs.length) ++
          VExpr.bvars fvs.length vfvs.length))) (.sort v)) :
    TrExprS env Us E.vlctx
      (.app (mkAppN (.fvar mfv) itIndices.toArray)
        (mkAppN (mkAppN (.const cn ls) (pfvs.map .fvar).toArray) (fvs.map .fvar).toArray))
      (.app (.appN (.bvar mpos) idx') (.appN (.const cn ls')
        (VExpr.bvars pfvs.length (Ofvs.length + fvs.length + vfvs.length) ++
          VExpr.bvars fvs.length vfvs.length))) := by
  have hΓ := hE.tr.wf.toCtx
  obtain ⟨A, B, hF, hA⟩ := VExpr.WF.app_inv henv.ordered hΓ ⟨_, hty⟩
  have trF := TrExprS.mkAppN_of_wf henv.ordered hΓ (.fvar hm) hidx ⟨_, hF⟩
  have hnd : (pfvs ++ Ofvs ++ fvs ++ vfvs).Nodup := by
    have := hE.fvars_nodup; rw [hT.fvars] at this; exact List.nodup_reverse.1 this
  have hall := hT.fvars_tr (env := env) (Us := Us) hnd
  have hb : VExpr.bvars (pfvs ++ Ofvs ++ fvs ++ vfvs).length 0 =
      VExpr.bvars pfvs.length (Ofvs.length + fvs.length + vfvs.length) ++
        VExpr.bvars Ofvs.length (fvs.length + vfvs.length) ++
        VExpr.bvars fvs.length vfvs.length ++ VExpr.bvars vfvs.length 0 := by
    have e1 := VExpr.bvars_append pfvs.length (Ofvs.length + (fvs.length + vfvs.length)) 0
    have e2 := VExpr.bvars_append Ofvs.length (fvs.length + vfvs.length) 0
    have e3 := VExpr.bvars_append fvs.length vfvs.length 0
    simp only [Nat.add_zero] at e1 e2 e3
    simp only [List.append_assoc]
    rw [e3, e2, show Ofvs.length + fvs.length + vfvs.length =
      Ofvs.length + (fvs.length + vfvs.length) by omega, e1]
    simp
  rw [hb, List.map_append, List.map_append, List.map_append] at hall
  have h1 := List.Forall₂.take_append (by simp [VExpr.bvars]) hall
  have h2 := List.Forall₂.take_append (by simp [VExpr.bvars]) h1
  have hP := List.Forall₂.take_append (by simp [VExpr.bvars]) h2
  have hFv := List.Forall₂.drop_append (by simp [VExpr.bvars]) h1
  rw [mkAppN_append, show (pfvs.map Expr.fvar).toArray ++ (fvs.map Expr.fvar).toArray =
    ((pfvs ++ fvs).map Expr.fvar).toArray by simp]
  have trI := TrExprS.mkAppN_of_wf henv.ordered hΓ hc
    ((Lean4Lean.List.Forall₂.append_of_left (by simp [VExpr.bvars])).2 ⟨hP, hFv⟩) ⟨_, hA⟩
  rw [List.map_append]; exact .app hF hA trF trI

/-- The facts about the block `loopInd2` works from: the parameters `Mp`, the kernel's view of the
block, its specification head `d₀` (without constructors), and the motives `loopInd1` opened. -/
structure MinorsSetup (cT : VContext) (pre : List Name) (Mp : TypeChecker.MLCtx) (pfvs : List FVarId)
    (params : List VExpr) (stats : InductiveStats) (types : List InductiveType)
    (d₀ : VInductDecl) (motfvs : List FVarId) (heads : List (Array Expr × Expr))
    (recInfos : Array RecInfo) : Prop where
  MpT : Mp.IsTele pfvs params
  par : stats.params.toList = pfvs.map .fvar
  lev : stats.levels = cT.lparams.map .param
  ind : stats.indConsts.toList = types.map fun T => .const T.name stats.levels
  lpnd : cT.lparams.Nodup
  prend : (pre ++ cT.lparams).Nodup
  names : (types.map (·.name)).Nodup
  d₀params : d₀.params = params
  d₀len : d₀.types.length = types.length
  d₀types : ∀ t (ht : t < types.length), ∃ T', d₀.types[t]? = some T' ∧
    T'.name = types[t].name ∧ stats.nindices[t]? = some T'.indices.length
  motlen : motfvs.length = types.length
  motives : ∀ t (ht : t < types.length),
    recInfos[t]!.motive = .fvar (motfvs[t]'(motlen ▸ ht))
  /-- The indices and major premises `loopInd1` recorded, which `loopInd2` keeps. -/
  heads : ∀ t, t < types.length → (recInfos[t]!.indices, recInfos[t]!.major) = heads[t]!
  /-- The block's names are not the constant a panic returns, nor mentioned by the parameters.
  Where a constructor has a field and its binder domains do not mention the block, which is
  where `isRecArg` is shown to find nothing, they are no primitive and no other declaration
  mentions them. -/
  nonPrim : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors,
    spineIn (BFree (· ∈ d₀.types.map (·.name))) ct.type →
    params.length < declareConstructors.arity 0 ct.type →
    ∀ T ∈ d₀.types, Environment.primitives.contains T.name = false
  notDummy : ∀ T ∈ d₀.types, T.name ≠ `_inhabitedExprDummy
  envB : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors,
    spineIn (BFree (· ∈ d₀.types.map (·.name))) ct.type →
    params.length < declareConstructors.arity 0 ct.type →
    ∀ n ci, cT.env.find? n = some ci → n ∉ d₀.types.map (·.name) →
      ci.SuppIn fun m => m ∉ d₀.types.map (·.name)
  MpB : ∀ fv d, Mp.lctx.find? fv = some d →
    d.type.SuppIn (BFree (· ∈ d₀.types.map (·.name))) ∧
    d.value'.SuppIn (BFree (· ∈ d₀.types.map (·.name)))

theorem MinorsSetup.indB {cT : VContext} {pre : List Name} {Mp : TypeChecker.MLCtx}
    {pfvs : List FVarId} {params : List VExpr} {stats : InductiveStats}
    {types : List InductiveType} {d₀ : VInductDecl} {motfvs : List FVarId}
    {heads : List (Array Expr × Expr)} {recInfos : Array RecInfo}
    (hS : MinorsSetup cT pre Mp pfvs params stats types d₀ motfvs heads recInfos) :
    ∀ j, j < stats.indConsts.size →
      ∃ n us, stats.indConsts[j]! = .const n us ∧ n ∈ d₀.types.map (·.name) := by
  intro j hj
  have hjt : j < types.length := by
    rw [← Array.length_toList, hS.ind] at hj; simpa using hj
  obtain ⟨T', h1, h2, -⟩ := hS.d₀types j hjt
  refine ⟨types[j].name, stats.levels, ?_, List.mem_map.2 ⟨T', List.mem_of_getElem? h1, h2⟩⟩
  rw [getElem!_pos _ j hj, ← Array.getElem_toList]; simp [hS.ind]

/-- The head of an application spine. -/
def _root_.Lean4Lean.VExpr.appHead : VExpr → VExpr
  | .app f _ => f.appHead
  | e => e

theorem _root_.Lean4Lean.VExpr.appHead_appN : ∀ (e : VExpr) (as : List VExpr),
    (e.appN as).appHead = e.appHead
  | _, [] => rfl
  | e, a :: as => by simp [VExpr.appN, appHead_appN (.app e a) as, VExpr.appHead]

/-- Each entry of a telescope context is a type over the ones before it. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.IsTele.entry_isType {env : VEnv} {Us : List Name}
    {m : TypeChecker.MLCtx} {fvs : List FVarId} {tys : List VExpr} (h : m.IsTele fvs tys)
    (hm : m.WF env Us) : ∀ k (hk : k < tys.length),
      env.IsType Us.length (tys.take k).reverse tys[k] := by
  induction h with
  | nil => intro k hk; simp at hk
  | @vlam m fvs tys fv name ty ty' bi h ih =>
    obtain ⟨h1, -, -, h4⟩ := hm
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k tys.length with hk' | hk'
    · rw [List.getElem_append_left hk', List.take_append_of_le_length (Nat.le_of_lt hk')]
      exact ih h1 k hk'
    · obtain rfl : k = tys.length := by omega
      rw [List.getElem_append_right (Nat.le_refl _), List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
      simpa [h.toCtx] using h4

/-- Entries that agree one by one, each in the context of the second telescope's entries before
it. -/
theorem teleDefEq_of_getElem {env : VEnv} {U : Nat} : ∀ {Γ : List VExpr} {Ds Fs : List VExpr},
    Ds.length = Fs.length →
    (∀ k D F, Ds[k]? = some D → Fs[k]? = some F →
      env.IsDefEqU U ((Fs.take k).reverse ++ Γ) D F) →
    env.TeleDefEq U Γ Ds Fs
  | _, [], [], _, _ => .nil
  | Γ, D :: Ds, F :: Fs, hl, h =>
    .cons (by simpa using h 0 D F rfl rfl)
      (teleDefEq_of_getElem (Γ := F :: Γ) (by simpa using hl) fun k D' F' h1 h2 => by
        simpa using h (k + 1) D' F' h1 h2)

/-- What `loopCtors` establishes about a constructor `ct` of the `j`th type, declared at
`C' = Π ps Ds, I params idx`: the specification's constructor `c`, its fields read at the types
the kernel opens them at. -/
structure CtorOut (cT : VContext) (pre : List Name) (params : List VExpr) (d₀ : VInductDecl)
    (VB : VEnv) (UB : Nat) (j : Nat) (ct : Constructor) (C' : VExpr) (ps Ds idx : List VExpr)
    (c : VConstructor) : Prop where
  name : c.name = ct.name
  type : c.type = C'
  indices : c.indices = idx
  len : c.fields.length = Ds.length
  defeq : ∀ k D f, Ds[k]? = some D → c.fields[k]? = some f →
    cT.venv.IsDefEqU cT.lparams.length
      (((c.fields.take k).map (·.type)).reverse ++ params.reverse) D f.type
  /-- A field's view is its declared domain with annotations stripped, each defined in the
  environment. -/
  within : ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
    D.StripsToBy (fun n => (∃ v, cT.env.find? n = some (.defnInfo v)) ∧ cT.venv.AnnotDef n)
      f.type
  sort : ∀ k f, c.fields[k]? = some f →
    cT.venv.HasType cT.lparams.length
      (((c.fields.take k).map (·.type)).reverse ++ params.reverse) f.type (.sort f.level) ∧
    f.level.WF cT.lparams.length
  recArg : ∀ k f ra, c.fields[k]? = some f → f.recArg = some ra →
    d₀.RecArgAt cT.venv cT.lparams.length params ((c.fields).map (·.type)) k f.type ra
  facts : d₀.CtorFacts VB UB (VLevel.shift pre.length cT.lparams.length) j c
  /-- A constructor whose binder domains do not mention the block has no recursive field. -/
  recFree : spineIn (BFree (· ∈ d₀.types.map (·.name))) ct.type → ∀ f ∈ c.fields, f.recArg = none
  /-- Without parameters, a first binder whose domain carries no annotation is the first field's
  type, and an axiom there gives an inductive hypothesis without binders. -/
  first : params.length = 0 → ∀ nm D b bi, ct.type = .forallE nm D b bi →
    D.consumeTypeAnnotations' = D → ∀ f, c.fields[0]? = some f →
      TrExprS cT.venv cT.lparams [] D f.type ∧
      ∀ n us ax ra, D = .const n us → cT.env.find? n = some (.axiomInfo ax) →
        f.recArg = some ra → ra.binders = []
  /-- A field's view is its declared domain with as many annotations stripped as the constructor's
  type has on its binder. -/
  views : ∀ (k : Nat) (D : VExpr) (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
    f.type = D.stripN ((ct.type.domStrips.drop params.length)[k]?.getD 0)

/-- What the kernel opened for a constructor's minor premise: its fields `fvs`, inductive
hypotheses `vfvs` and the minor premise itself, the small context `Mf` of the parameters and the
fields, and the inductive hypotheses `mkRecRules` builds values from. -/
structure MinorKD where
  fvs : List FVarId
  vfvs : List FVarId
  minor : FVarId
  Mf : TypeChecker.MLCtx
  ihs : Array IHInfo

/-- The record `mkRecInfos` keeps for the minor premise. -/
def MinorKD.info (k : MinorKD) : MinorInfo := ⟨(k.fvs.map .fvar).toArray, k.ihs⟩

/-- The variables the minor premise added, the last on top. -/
def MinorKD.seg (k : MinorKD) : List FVarId := k.minor :: (k.vfvs.reverse ++ k.fvs.reverse)

/-- The facts about `k` for constructor `c`, the kernel's context being `cb`. -/
structure MinorKDOK (cT : VContext) (Mp : TypeChecker.MLCtx) (pfvs : List FVarId)
    (params : List VExpr) (cb : VContext) (k : MinorKD) (c : VConstructor) : Prop where
  wf : k.Mf.WF cT.venv cT.lparams
  tele : k.Mf.IsTele (pfvs ++ k.fvs) (params ++ c.fields.map (·.type))
  base : ∃ hk, k.Mf.dropN k.fvs.length hk = Mp
  agree : ∀ fv ∈ k.Mf.vlctx.fvars,
    (cb.lctx.find? fv).map LocalDecl.erase = (k.Mf.lctx.find? fv).map LocalDecl.erase
  pieces : List.Forall₂ (fun (ih : IHInfo) (p : Nat × VRecArg) => ∃ (hp : p.1 < k.fvs.length)
    (hk' : k.fvs.length - p.1 ≤ k.Mf.length),
      IHPieces cT.venv cT.lparams (k.Mf.dropN (k.fvs.length - p.1) hk') (k.fvs[p.1]'hp) ih p.2 ∧
      ∀ dk n us ax, k.Mf.lctx.find? (k.fvs[p.1]'hp) = some dk → dk.type = .const n us →
        cT.env.find? n = some (.axiomInfo ax) → p.2.binders = [])
    k.ihs.toList c.recFields

theorem MinorKDOK.extend {cT Mp pfvs params cb k c} (H : MinorKDOK cT Mp pfvs params cb k c)
    {cb' : VContext} (hext : ∀ fv d, cb.lctx.find? fv = some d → cb'.lctx.find? fv = some d) :
    MinorKDOK cT Mp pfvs params cb' k c := by
  refine { H with agree := fun fv hfv => ?_ }
  have := H.agree fv hfv
  obtain ⟨d, hd⟩ := H.wf.tr.find?_eq_some.2 hfv
  rw [hd] at this
  obtain ⟨d', hd', -⟩ : ∃ d', cb.lctx.find? fv = some d' ∧ d'.erase = d.erase := by
    cases h : cb.lctx.find? fv <;> rw [h] at this <;> simp_all
  rw [hext _ _ hd', hd]; rw [hd'] at this; exact this

theorem ctorMinor.WF [VEnv.Injective] {blockNames : NameSet} {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {hMp : Mp.WF cT.venv cT.lparams} {pfvs : List FVarId}
    {params : List VExpr} {stats : InductiveStats} {types : List InductiveType}
    (hNM : NotMentionsOK cT.venv cT.lparams stats types)
    (hBN : ∀ t ∈ types, blockNames.contains t.name)
    {d₀ : VInductDecl} {motfvs : List FVarId} {heads : List (Array Expr × Expr)} {recInfos : Array RecInfo}
    (hS : MinorsSetup cT pre Mp pfvs params stats types d₀ motfvs heads recInfos) {ml : VLevel}
    {j : Nat} (hj : j < types.length) {ct : Constructor} (hct : ct ∈ types[j].ctors)
    {C' : VExpr} {ps Ds idx : List VExpr}
    (hctr : TrExprS cT.venv cT.lparams [] ct.type C')
    (hC'T : cT.venv.IsType cT.lparams.length [] C')
    (hshape : C' = .foralls (ps ++ Ds) (.appN (.const types[j].name
      (VLevel.params cT.lparams.length)) (VExpr.bvars params.length Ds.length ++ idx)))
    (harity : declareConstructors.arity 0 ct.type = ps.length + Ds.length)
    (htele : cT.venv.TeleDefEq cT.lparams.length [] ps params)
    {q : Nat} {Qs' : List VExpr} (hq : Qs'.length = q) {minfvs : List FVarId}
    (hmin : minfvs.length = q) {Mmin : TypeChecker.MLCtx}
    (hMminT : Mmin.IsTele (pfvs ++ motfvs ++ minfvs)
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs'))
    (hWmin : VLCtx.FVLift' (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx
      Mmin.vlctx 0 (Lift.skipN .refl (types.length + q)) 0)
    {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    (hPB : ∀ cb, P cb → d₀.BlockFacts cb.venv cb.lparams.length
      (VLevel.shift pre.length cT.lparams.length))
    (hPC : ∀ cb, P cb → cb.venv.constants ct.name = some ⟨cT.lparams.length, C'⟩)
    {indTypeName : Name} {K : Expr → Array Expr → Array IHInfo → M α} {Q} {cb : VContext}
    (H : ∀ (minorFv : FVarId) (bu : Array Expr) (ihs : Array IHInfo) (c : VConstructor)
      (cb' : VContext) ρp' ρmin' name ty,
      CtorOut cT pre params d₀ cb'.venv cb'.lparams.length j ct C' ps Ds idx c →
      Sub X pre ρp' (cT.small Mp hMp) cb' →
      Ext (.vlam minorFv name ty
        (d₀.minorType (VLevel.shift pre.length cT.lparams.length) q j c) .default Mmin) cb'
        ρmin' →
      P cb' → (∃ cbX : VContext, P cbX ∧ minorFv = ⟨cbX.ngen.curr⟩) →
      (∃ kd : MinorKD, kd.minor = minorFv ∧ kd.info = ⟨bu, ihs⟩ ∧
        MinorKDOK cT Mp pfvs params cb' kd c ∧
        cb'.mlctx.vlctx.fvars = kd.seg ++ cb.mlctx.vlctx.fvars ∧
        ∀ fv d, cb.lctx.find? fv = some d → cb'.lctx.find? fv = some d) →
      WF cb' (K (.fvar minorFv) bu ihs) Q)
    {ρp ρmin : Lift} (hsub : Sub X pre ρp (cT.small Mp hMp) cb)
    (hEmin : Ext Mmin cb ρmin) (hPcb : P cb) :
    WF cb (mkRecInfos.loopCtorArgs stats ct.type fun t bu u => do
      let (itIdx, itIndices) ← getIIndices stats t
      let introApp := mkAppN (mkAppN (.const ct.name stats.levels) stats.params) bu
      let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
      mkRecInfos.loopU stats blockNames u recInfos 0 #[] #[] fun v ihs => do
      let lctx ← getLCtx
      let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
      let minorName := ct.name.replacePrefix indTypeName .anonymous
      withLocalDecl minorName .default (← consumeTypeAnnotations minorTy) fun minor =>
        K minor bu ihs) Q := by
  have hMpT := hS.MpT
  have hlenp : pfvs.length = params.length := hMpT.length_eq
  have hpsl : ps.length = params.length := htele.length_eq
  unfold mkRecInfos.loopCtorArgs
  refine WF.bind (Q := (· = cb.toContext)) (fun _ h => by cases h; rfl) fun ctx hctx => ?_
  subst hctx
  have hMp0 : ∃ hk, (Mp.dropN params.length hk).vlctx = [] := by
    obtain ⟨hk, h⟩ := hMpT.dropN' params.length (Nat.le_refl _)
    rw [Nat.sub_self, List.take_zero, List.take_zero] at h
    refine ⟨hk, ?_⟩
    generalize Mp.dropN params.length hk = m at h
    generalize hf : ([] : List FVarId) = fs at h
    generalize ht : ([] : List VExpr) = ts at h
    cases h with
    | nil => rfl
    | vlam _ => simp at hf
  obtain ⟨hk0, hMp0⟩ := hMp0
  have hctr' := hctr
  rw [hshape] at hctr'
  refine loopCtorArgs.loop.WF hMpT hS.par hpsl (N₀ := Mmin) (F₀ := cb.mlctx.vlctx.fvars)
    (R := .appN (.const types[j].name (VLevel.params cT.lparams.length))
      (VExpr.bvars params.length Ds.length ++ idx))
    (P := fun cb' => P cb' ∧ (∃ ρ, Ext Mmin cb' ρ) ∧
      ∀ fv d, cb.lctx.find? fv = some d → cb'.lctx.find? fv = some d)
    (fun cb' _ _ _ _ h1 h2 ⟨hP1, ⟨ρ', hE'⟩, hx⟩ => ⟨hP _ _ _ _ _ _ _ hP1, ⟨_, hE'.skip h1 h2⟩,
      fun fv d hd => by
        rw [VContext.push_find? (by simp [LocalContext.Dom, hx fv d hd])]; exact hx fv d hd⟩)
    (B := (· ∈ d₀.types.map (·.name)))
    (Z := spineIn (BFree (· ∈ d₀.types.map (·.name))) ct.type) hS.indB
    (fun hz (hDs : 0 < Ds.length) n hn => let ⟨T, hT, e⟩ := List.mem_map.1 hn;
      e ▸ hS.nonPrim j hj ct hct hz (by rw [harity, hpsl]; omega) T hT)
    (fun h => let ⟨T, hT, e⟩ := List.mem_map.1 h; hS.notDummy T hT e)
    (fun hz (hDs : 0 < Ds.length) n ci h hn => hS.envB j hj ct hct hz (by rw [harity, hpsl]; omega) n ci h hn)
    ?cont _ ct.type
    0 [] [] [] Mp hMp cb ρp
    { tele := by simpa using hMpT
      base := ⟨Nat.zero_le _, rfl⟩
      sub := hsub
      pred := ⟨hPcb, ⟨_, hEmin⟩, fun _ _ h => h⟩
      fvars := by simp
      rsLen := rfl
      le := Nat.zero_le _
      arity := by simpa using harity
      tr := ?tr
      fields := by simp
      within := by simp
      comp := ⟨Mmin, ρmin, hEmin, hWmin, by simpa using hMminT, ⟨Nat.zero_le _, rfl⟩⟩
      free := fun hz => ⟨hz, nofun, hS.MpB⟩
      start := fun _ => rfl
      first := fun _ _ _ _ _ _ _ h => absurd h (by simp)
      strips := by simp
      views := by simp }
  case tr =>
    rcases Nat.eq_zero_or_pos params.length with h0 | h0
    · refine .inr ⟨by simp [h0], ?_⟩
      obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero (hpsl.trans h0)
      have hMpnil : Mp.vlctx = [] := by
        have : Mp.dropN params.length hk0 = Mp.dropN 0 (Nat.zero_le _) :=
          TypeChecker.MLCtx.dropN_congr h0 _ _
        rw [this] at hMp0; exact hMp0
      rw [hMpnil]; simpa using hctr'
    · refine .inl ⟨h0, rfl, _, hk0, rfl, by simpa using
        (show (Mp.dropN params.length hk0).IsTele [] [] from by
          obtain ⟨hk', h⟩ := hMpT.dropN' params.length (Nat.le_refl _)
          rw [Nat.sub_self, List.take_zero, List.take_zero] at h
          exact h), ?_, ?_⟩
      · simp only [Nat.sub_zero, List.drop_zero]; rw [hMp0]; exact hctr'
      · simp only [Nat.sub_zero, List.drop_zero]; rw [hMp0]; exact htele
  case cont =>
  intro t fvs ftys rs Mf hMf cb₁ ρ₁ hI hfD
  obtain ⟨hP1, ⟨ρm1, hEm1⟩, hx1⟩ := hI.pred
  have hfl : ftys.length = fvs.length := by
    have := hI.tele.length_eq; simp [hlenp] at this; omega
  -- the constructor's result
  have htrR : TrExprS cT.venv cT.lparams Mf.vlctx t
      (.appN (.const types[j].name (VLevel.params cT.lparams.length))
        (VExpr.bvars params.length Ds.length ++ idx)) := by
    obtain ⟨-, h⟩ := hI.tr.resolve_left (by omega)
    rw [hfD, List.drop_length] at h; exact h
  refine WF.bind getIIndices.WF fun ⟨itIdx, itIndices⟩ ⟨hval, hidxL⟩ => ?_
  dsimp only
  obtain ⟨hits, hvalI⟩ := isValidIndApp?_some hval
  have hitT : itIdx < types.length := by
    rw [← Array.length_toList, hS.ind] at hits; simpa using hits
  obtain ⟨Δtop, hsplit, hΔl, hΔv, hbotT⟩ := hI.tele.vlctx_split fvs.length rfl (by omega)
    (by have := hI.tele.length; simp at this; omega)
  have hPA : ParamsAt Mf.vlctx fvs.length pfvs := by
    have hfv := hMf.tr.wf.fvwf
    rw [hsplit] at hfv ⊢
    have := ParamsAt.tele hbotT hfv hΔv
    rwa [hΔl] at this
  obtain ⟨is, hisl, hargl, hV₀, hisTr⟩ :=
    validIndApp_shape hS.lpnd hS.par hS.lev hS.ind hPA hvalI hitT htrR
  have hRE := hV₀
  rw [hlenp, hfD] at hRE
  have hname : types[itIdx].name = types[j].name := by
    have := congrArg VExpr.appHead hRE
    simp [VExpr.appHead_appN, VExpr.appHead] at this; exact this.symm
  obtain rfl : itIdx = j := (List.getElem_inj (xs := types.map (·.name)) (h₀ := by simpa)
    (h₁ := by simpa) hS.names).1 (by simpa using hname)
  have hisidx : is = idx := by
    have := VExpr.appN_const_inj hRE
    exact (List.append_cancel_left this).symm
  subst hisidx
  -- the fields' sorts
  have henvT : cT.venv.WF := cT.envAt.tr.wf
  have hMfT := hI.tele
  have hlv : ∀ k (hk : k < ftys.length), ∃ u, cT.venv.HasType cT.lparams.length
      ((ftys.take k).reverse ++ params.reverse) (ftys[k]'hk) (.sort u) := by
    intro k hk
    have := hMfT.entry_isType hMf (params.length + k) (by simp; omega)
    rw [List.take_append, List.take_of_length_le (by omega),
      show params.length + k - params.length = k by omega, List.reverse_append,
      List.getElem_append_right (by omega)] at this
    have h2 : cT.venv.IsType cT.lparams.length ((ftys.take k).reverse ++ params.reverse)
        (ftys[k]'hk) := by simpa using this
    exact h2
  let lv : Nat → VLevel := fun k =>
    if hk : k < ftys.length then Classical.choose (hlv k hk) else .zero
  have hlvS : ∀ k (hk : k < ftys.length), cT.venv.HasType cT.lparams.length
      ((ftys.take k).reverse ++ params.reverse) (ftys[k]'hk) (.sort (lv k)) := by
    intro k hk; simp only [lv, dif_pos hk]; exact Classical.choose_spec (hlv k hk)
  let c₀ : VConstructor :=
    ⟨ct.name, C', ftys.zipIdx.map fun (A, k) => ⟨A, lv k, none⟩, is⟩
  have hc₀t : c₀.fields.map (·.type) = ftys := by
    simp only [c₀, List.map_map]
    apply List.ext_getElem (by simp) fun i h1 h2 => by simp
  -- the constructor's type, over the fields' types
  have hls : ∀ l ∈ VLevel.shift pre.length cT.lparams.length, l.WF cb₁.lparams.length := by
    have e : (cT.small Mf hMf).lparams = cT.lparams := rfl
    rw [hI.sub.lparams, e]; simpa using VLevel.shift_wf
  have hshl : (VLevel.shift pre.length cT.lparams.length).length = cT.lparams.length := by
    simp [VLevel.shift]
  have hle : cT.venv ≤ cb₁.venv := hI.sub.venv
  have hPFT : cT.venv.IsTele cT.lparams.length [] (params ++ ftys) := hMfT.isTele hMf
  obtain ⟨hPT, hFT⟩ := VEnv.IsTele.append_inv hPFT
  have hTD : cT.venv.TeleDefEq cT.lparams.length [] (ps ++ Ds) (params ++ ftys) :=
    VEnv.TeleDefEq.append htele (teleDefEq_of_getElem (by omega) fun k D F hD hF => by
      simpa using hI.fields k D F hD hF)
  obtain ⟨-, hRps⟩ := VEnv.IsType.foralls_inv henvT.ordered (hshape ▸ hC'T)
  simp only [List.append_nil] at hRps
  have hctxD := VEnv.TeleDefEq.defeqCtx henvT (Γ' := []) hTD .zero trivial hPFT
  simp only [List.append_nil] at hctxD
  have hRpar := hRps.defeqDFC henvT.ordered hctxD
  have hC'eq : cT.venv.IsDefEqU cT.lparams.length [] C'
      (.foralls (params ++ ftys) (.appN (.const types[itIdx].name
        (VLevel.params cT.lparams.length)) (VExpr.bvars params.length Ds.length ++ is))) := by
    rw [hshape]; exact VEnv.TeleDefEq.foralls henvT trivial hTD hPFT (by simpa using hRpar)
  have hcT := VEnv.HasType.const (Γ := []) (hPC cb₁ hP1) hls (by simp [hshl])
  have hC'eq' := (hC'eq.instL hls).mono hle
  simp only [List.map_nil, VExpr.instL_foralls, VExpr.instL_appN, VExpr.instL, List.map_append,
    VExpr.instL_bvars, VLevel.params_inst hshl] at hC'eq'
  have hBF := hPB cb₁ hP1
  have hcT' := hcT.defeqU_r hBF.wf trivial hC'eq'
  obtain ⟨T', hT', hT'n, hT'i⟩ := hS.d₀types itIdx hitT
  have hc₀l : c₀.fields.length = Ds.length := by simp [c₀]; omega
  have hpsz : stats.params.size = pfvs.length := by
    rw [← Array.length_toList, hS.par, List.length_map]
  have hisl' : is.length = T'.indices.length := by
    rw [getElem!_pos stats.nindices itIdx (Array.getElem?_eq_some_iff.1 hT'i).1,
      (Array.getElem?_eq_some_iff.1 hT'i).2, hpsz] at hargl
    omega
  have hcf₀ : d₀.CtorFacts cb₁.venv cb₁.lparams.length (VLevel.shift pre.length cT.lparams.length)
      itIdx c₀ := by
    have hmapt : c₀.fields.map (·.type.instL (VLevel.shift pre.length cT.lparams.length)) =
        ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length)) := by
      rw [← hc₀t]; simp [Function.comp_def]
    refine ⟨?_, ⟨T', hT', hisl', ?_⟩, ?_⟩
    · rw [hmapt, hS.d₀params]
      have := (hFT.instL hls).mono hle
      simpa [List.map_reverse] using this
    · rw [hmapt, hS.d₀params, hc₀l, hT'n]
      exact hcT'
    · intro k f ra hk hra
      simp only [c₀, List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hk
      obtain ⟨_, -, rfl⟩ := hk
      cases hra
  -- the inductive hypotheses
  obtain ⟨ks, hks1, hks2, -, hks4⟩ := recFvs_positions hI.rsLen
  obtain ⟨N, ρN, hEN, hWN, hNT, hNk, hNb⟩ := hI.comp
  have hrec₀ : c₀.recFields = [] := by
    have hnone : ∀ f ∈ c₀.fields, f.recArg = none := by
      simp only [c₀, List.mem_map]
      rintro f ⟨⟨x, k⟩, _, rfl⟩; rfl
    simp only [VConstructor.recFields, List.filterMap_eq_nil_iff]
    rintro ⟨f, k⟩ hm
    have := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hm)
    simp [hnone f this]
  have hNT' : N.IsTele (pfvs ++ motfvs ++ minfvs ++ fvs ++ [])
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs' ++
        VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++
        ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c₀) := by
    rw [ihsOf, hrec₀, VExpr.liftTele_eq_liftTele', VExpr.liftTele'_eq_zipIdx]
    simpa [List.zipIdx_map, Function.comp_def] using hNT
  refine loopU.WF hMpT hS.par hS.lev hS.ind hNM hBN hS.lpnd hS.d₀params hS.d₀len hS.d₀types (ml := ml)
    (j := itIdx) hI.tele (rs := rs) hks1 hks2 hks4 hq hS.motlen hmin hS.motives
    (F₀ := cb₁.mlctx.vlctx.fvars) (E₀ := N) (c₀ := c₀) (P := fun cb' => P cb' ∧
      (∃ ρ, Ext Mmin cb' ρ) ∧ ∀ fv d, cb.lctx.find? fv = some d → cb'.lctx.find? fv = some d)
    (fun cb' _ _ _ _ h1 h2 ⟨hP1, ⟨ρ', hE'⟩, hx⟩ => ⟨hP _ _ _ _ _ _ _ hP1, ⟨_, hE'.skip h1 h2⟩,
      fun fv d hd => by
        rw [VContext.push_find? (by simp [LocalContext.Dom, hx fv d hd])]; exact hx fv d hd⟩)
    (fun cb' ⟨h, _⟩ => hPB cb' h) ?minor ks.length 0 [] [] c₀ N ρN cb₁ ρ₁ (by simp)
    { ctor := hcf₀
      types := hc₀t
      recs := by simp [hrec₀]
      sub := hI.sub
      pred := ⟨hP1, ⟨_, hEm1⟩, hx1⟩
      fvars := by simp
      len := rfl
      ext := hEN
      tele := by simpa using hNT'
      lift := ⟨Nat.zero_le _, hWN⟩
      infos := by simp [hrec₀]
      pieces := by rw [hrec₀]; exact .nil
      recArgs := fun k f ra hk hra => by
        simp only [c₀, List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hk
        obtain ⟨_, -, rfl⟩ := hk
        cases hra
      base := ⟨Nat.zero_le _, rfl⟩
      head := ⟨rfl, rfl, rfl, rfl⟩ }
  case minor =>
  intro vfvs infos c E ρE cb₂ ρf hU
  obtain ⟨hP2, ⟨ρm2, hEm2⟩, hx2⟩ := hU.pred
  obtain ⟨hcn, hcty, hcidx, hclv⟩ := hU.head
  refine WF.bind (Q := (· = cb₂.lctx)) (fun _ h => by cases h; rfl) fun lctx hl => ?_
  subst hl
  rw [hS.motives itIdx hitT]
  have hBF2 := hPB cb₂ hP2
  have henv2 := hBF2.wf
  have hET := hU.tele
  have hEwf := hU.ext.wf
  have hEΓ := hEwf.tr.wf.toCtx
  have hu : (ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length
      c).length = vfvs.length := by
    have h1 := congrArg List.length hU.recs
    simp only [List.length_map, List.length_take] at h1
    simp [ihsOf, h1, hU.len, hks1]
  have hcl : c.fields.length = fvs.length := by
    rw [← hfl, ← hU.types, List.length_map]
  have hrl : c.recFields.length = vfvs.length := by simpa [ihsOf] using hu
  have hcfm : c.fields.map (·.type.instL (VLevel.shift pre.length cT.lparams.length)) =
      ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length)) := by
    rw [← hU.types]; simp [Function.comp_def]
  have hconc := VInductDecl.minor_concl (v := ml) (hBF2.only hU.ctor)
    (VInductDecl.mem_allCtors_of_ctors (VInductDecl.mem_only_ctors_self hT'))
    (VInductDecl.allTypes_getElem?_of_types (by rw [VInductDecl.only_types_getElem?, hT']; rfl)) Qs'
    (ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c) hq
    (by simp [ihsOf])
  obtain ⟨T'', hT''⟩ : ∃ T'', (d₀.only itIdx c).types[itIdx]? = some T'' :=
    ⟨_, by rw [VInductDecl.only_types_getElem?, hT']; rfl⟩
  rw [VInductDecl.ctorAppAt_of_none (VInductDecl.allTypes_getElem?_of_types hT'')
    (VInductDecl.only_nested hBF2.nested _ _ _ (List.mem_of_getElem? hT''))] at hconc
  simp only [VInductDecl.only_allTypes_length, VInductDecl.allTypes_of_aux hBF2.aux,
    VInductDecl.only_types_length, VInductDecl.only_motiveTypes,
    VInductDecl.only_params, hS.d₀len, hS.d₀params, hcl, hrl, hcfm] at hconc
  have hEctx : E.vlctx.toCtx =
      (ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c).reverse ++
      (VExpr.liftTele (types.length + q)
        (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length)))).reverse ++
      Qs'.reverse ++ (d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml).reverse ++
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length))).reverse := by
    rw [hET.toCtx]; simp
  rw [← hEctx] at hconc
  -- the motive, the indices and the constructor, in the view
  have hEfl := hET.length_eq
  simp only [List.length_append, List.length_map, VInductDecl.length_motiveTypes,
    VInductDecl.allTypes_of_aux hBF2.aux, VExpr.length_liftTele, hS.d₀len, hq] at hEfl
  have hndE : (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs).Nodup := by
    have := hEwf.fvars_nodup; rw [hET.fvars] at this; exact List.nodup_reverse.1 this
  have hm := hET.find?_fvar hndE (j := pfvs.length + itIdx) (by simp; omega)
  have hmget : (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs)[pfvs.length + itIdx]'(by simp; omega) =
      motfvs[itIdx]'(hS.motlen ▸ hitT) := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega), List.getElem_append_left (by simp; omega)]
    simp
  have hmi : (pfvs ++ motfvs ++ minfvs ++ fvs ++ vfvs).length - 1 - (pfvs.length + itIdx) =
      vfvs.length + fvs.length + q + (types.length - 1 - itIdx) := by
    simp; omega
  rw [hmget, hmi] at hm
  obtain ⟨hk', W2⟩ := hU.lift
  have hk'' : vfvs.length ≤ E.length := hU.len ▸ hk'
  rw [TypeChecker.MLCtx.dropN_congr hU.len.symm hk' hk''] at W2
  have W3 := hET.fvlift_top vfvs.length (fvs₂ := vfvs)
    (tys₂ := ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c) rfl
    (by omega) hk''
  have W1 : VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx
      (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx 0
      (Lift.skipN .refl (fvs.length - fvs.length)) 0 := by rw [Nat.sub_self]; exact .refl
  have W : VLCtx.FVLift' (Mf.instL (VLevel.shift pre.length cT.lparams.length)).vlctx E.vlctx 0
      (reseatLift (types.length + q) fvs.length fvs.length vfvs.length) 0 :=
    W1.comp (W2.comp W3)
  have hidxE : List.Forall₂ (TrExprS cb₂.venv cb₂.lparams E.vlctx) itIndices.toList
      (c.indices.map fun e => (e.instL (VLevel.shift pre.length cT.lparams.length)).reseat
        (types.length + q) fvs.length fvs.length vfvs.length 0) := by
    rw [hidxL, hpsz, hcidx, List.forall₂_map_right_iff]
    refine Lean4Lean.List.Forall₂.imp (fun _ _ h => ?_) hisTr
    have := hU.sub.trExprS_to W hEwf.tr.wf h
    rwa [lift'_reseatLift0] at this
  have hlvl : (stats.levels).mapM (VLevel.ofLevel cb₂.lparams) =
      some (VLevel.shift pre.length cT.lparams.length) := by
    have e : (cT.small Mf hMf).lparams = cT.lparams := rfl
    rw [hU.sub.lparams, e, hS.lev]; exact mapM_ofLevel_params pre hS.prend
  have hcn' : c.name = ct.name := hcn
  have hconst : TrExprS cb₂.venv cb₂.lparams E.vlctx (.const c.name stats.levels)
      (.const c.name (VLevel.shift pre.length cT.lparams.length)) := by
    rw [hcn']
    exact .const (hPC cb₂ hP2) hlvl (by simp [hS.lev])
  have hETa : E.IsTele (pfvs ++ (motfvs ++ minfvs) ++ fvs ++ vfvs)
      (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
        (d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++ Qs') ++
        VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++
        ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c) := by
    simpa only [List.append_assoc] using hET
  have hbv : params.length = pfvs.length := hlenp.symm
  have hbv2 : types.length + q + fvs.length + vfvs.length =
      (motfvs ++ minfvs).length + fvs.length + vfvs.length := by
    simp [hS.motlen, hmin]
  rw [hbv, hbv2] at hconc
  have hbody := minorBody_tr henv2 hEwf hETa hm hidxE hconst hconc
  have hag : ∀ x ∈ fvs ++ vfvs, (cb₂.lctx.find? x).map LocalDecl.erase =
      (E.lctx.find? x).map LocalDecl.erase := fun x hx =>
    hU.ext.lctx x (by
      rw [hET.fvars, List.mem_reverse]; simp only [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact .inl (.inr hx)
      · exact .inr hx)
  obtain ⟨hkM, htrM, hTM, E₁, hk₁, hk₂, hE₁, heqM⟩ := minorTy_tr henv2 hEwf
    (Bfvs := pfvs ++ motfvs ++ minfvs) hET (by simp [hfl]) (by simp [hu]) hag hbody ⟨_, hconc⟩
  -- the view below the fields is the minor premises' context
  have hMmin : E.dropN (fvs.length + vfvs.length) hkM = Mmin := by
    obtain ⟨hkb, hb⟩ := hU.base
    have hkb' : vfvs.length ≤ E.length := hU.len ▸ hkb
    rw [TypeChecker.MLCtx.dropN_congr hU.len.symm hkb hkb'] at hb
    have hNk' : fvs.length ≤ (E.dropN vfvs.length hkb').length := by
      rw [TypeChecker.MLCtx.length_dropN]; omega
    rw [← TypeChecker.MLCtx.dropN_congr (Nat.add_comm vfvs.length fvs.length) (by omega) hkM,
      ← TypeChecker.MLCtx.dropN_dropN E _ _ hkb' hNk']
    rw [TypeChecker.MLCtx.dropN_of_eq hb hNk' hNk]
    exact hNb
  rw [hMmin] at htrM hTM
  have hmt : d₀.minorType (VLevel.shift pre.length cT.lparams.length) q itIdx c =
      .foralls (VExpr.liftTele (types.length + q)
          (ftys.map (·.instL (VLevel.shift pre.length cT.lparams.length))) ++
        ihsOf (VLevel.shift pre.length cT.lparams.length) types.length q fvs.length c)
      (.app (.appN (.bvar (vfvs.length + fvs.length + q + (types.length - 1 - itIdx)))
        (c.indices.map fun e => (e.instL (VLevel.shift pre.length cT.lparams.length)).reseat
          (types.length + q) fvs.length fvs.length vfvs.length 0))
        (.appN (.const c.name (VLevel.shift pre.length cT.lparams.length))
          (VExpr.bvars pfvs.length ((motfvs ++ minfvs).length + fvs.length + vfvs.length) ++
            VExpr.bvars fvs.length vfvs.length))) := by
    simp only [VInductDecl.minorType, VInductDecl.allTypes_of_aux hBF2.aux,
      VInductDecl.ctorAppAt_of_none (VInductDecl.allTypes_getElem?_of_types hT')
        (hBF2.nested _ (List.mem_of_getElem? hT')),
      ihsOf, ihSpec, hS.d₀params, hS.d₀len, hcl, hrl, hcfm]
    rw [← hbv2, ← hbv]
  rw [← hmt] at htrM hTM
  have hparams : stats.params = (pfvs.map Expr.fvar).toArray := by rw [← hS.par]
  rw [show itIndices = itIndices.toList.toArray by simp, hparams, ← hcn']
  -- stripping the minor premise's type leaves it alone
  have hstrip : ∀ X, X = cb₂.lctx.mkForall (fvs.map Expr.fvar).toArray
      (cb₂.lctx.mkForall (vfvs.map Expr.fvar).toArray
        (.app (mkAppN (.fvar (motfvs[itIdx]'(hS.motlen ▸ hitT))) itIndices.toList.toArray)
          (mkAppN (mkAppN (.const c.name stats.levels) (pfvs.map Expr.fvar).toArray)
            (fvs.map Expr.fvar).toArray))) → stripAnnotations cb₂.env X = .ok X := by
    rintro _ rfl
    rw [heqM]
    subst hE₁
    obtain ⟨-, -, -, -, hT₁⟩ := hET.vlctx_split vfvs.length rfl (by simp [hu]) hk₁
    refine stripAnnotations_mkForall _ hT₁ _ (stripAnnotations_mkForall _ hET _ ?_)
    exact stripAnnotations_fvar_head (fv := motfvs[itIdx]'(hS.motlen ▸ hitT))
      (by simp [Expr.getAppFn, Expr.getAppFn_mkAppN'])
  refine WF.bind (consumeTypeAnnotations_of_strip (hstrip _ rfl)) fun _ he => ?_
  subst he
  refine WF.withLocalDecl (hEm2.trExprS htrM) (hEm2.isType hTM) ?_
  obtain ⟨hbk, hbase⟩ := hI.base
  obtain ⟨ρp', hsubP⟩ := hU.sub.dropN' fvs.length hbk hMp hbase
  have hfget : ∀ k f, c.fields[k]? = some f → ∃ hk : k < ftys.length,
      f.type = ftys[k] ∧ f.level = lv k := by
    intro k f hk
    have hkl : k < ftys.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1; omega
    refine ⟨hkl, ?_, ?_⟩
    · have := congrArg (·[k]?) hU.types
      simp only [List.getElem?_map, hk, Option.map_some, List.getElem?_eq_getElem hkl] at this
      exact Option.some.inj this
    · have := congrArg (·[k]?) hclv
      simp only [List.getElem?_map, hk, Option.map_some] at this
      simp [c₀, List.getElem?_eq_getElem hkl] at this
      exact this
  have htake : ∀ k, (c.fields.take k).map (·.type) = ftys.take k := fun k => by
    rw [List.map_take, hU.types]
  refine H _ _ _ c _ _ _ _ _ ⟨hcn', hcty, hcidx, by rw [hcl, hfD], ?_, ?_, ?_, ?_, hU.ctor, ?_, ?_,
    fun k D f hD hk => by
      obtain ⟨hkl, hft, -⟩ := hfget k f hk
      rw [hft]; exact hI.views k D _ hD (List.getElem?_eq_getElem hkl)⟩
    (hsubP.skip _ _) (hEm2.push htrM hTM) (hP _ _ _ _ _ _ _ hP2) ⟨_, hP2, rfl⟩ ?kd
  · intro k D f hD hk
    obtain ⟨hkl, hft, -⟩ := hfget k f hk
    rw [htake, hft]
    exact hI.fields k D _ hD (List.getElem?_eq_getElem hkl)
  · intro k D f hD hk
    obtain ⟨hkl, hft, -⟩ := hfget k f hk
    rw [hft]
    exact hI.within k D _ hD (List.getElem?_eq_getElem hkl)
  · intro k f hk
    obtain ⟨hkl, hft, hfl'⟩ := hfget k f hk
    rw [htake, hft, hfl']
    have h1 := hlvS k hkl
    refine ⟨h1, ?_⟩
    have hPk : cT.venv.IsTele cT.lparams.length [] (params ++ ftys.take k) :=
      (VEnv.IsTele.append_inv (by rw [List.append_assoc, List.take_append_drop]; exact hPFT :
        cT.venv.IsTele cT.lparams.length [] ((params ++ ftys.take k) ++ ftys.drop k))).1
    have hΓ : OnCtx ((ftys.take k).reverse ++ params.reverse)
        (cT.venv.IsType cT.lparams.length) := by simpa using hPk.onCtx trivial
    exact (h1.isType henvT.ordered hΓ).sort_inv henvT.ordered
  · intro k f ra hk hra
    rw [hU.types]; exact hU.recArgs k f ra hk hra
  · intro hz f hf
    have hrs := (hI.free hz).2.1
    have hnil : recFvs fvs rs = [] := by
      simp only [recFvs, List.filterMap_eq_nil_iff]
      rintro ⟨fv, r⟩ hm
      simp [hrs r (List.of_mem_zip hm).2]
    have hks0 : ks = [] := List.eq_nil_of_length_eq_zero (by rw [hks1, hnil]; rfl)
    have hrf : c.recFields = [] := by
      have := hU.recs; rw [hks0] at this; simpa using this
    cases hra : f.recArg with
    | none => rfl
    | some ra =>
      exfalso
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hf
      have : (k, ra) ∈ c.recFields := by
        simp only [VConstructor.recFields, List.mem_filterMap]
        exact ⟨(f, k), List.mem_zipIdx_iff_getElem?.2 (by simpa using hk), by simp [hra]⟩
      rw [hrf] at this; cases this
  · intro hp0 nm D b bi hct hD f hf
    obtain ⟨hkl, hft, -⟩ := hfget 0 f hf
    have h0 : 0 < fvs.length := by rw [← hcl]; exact (List.getElem?_eq_some_iff.1 hf).1
    obtain ⟨⟨dk, hdk, hdkt⟩, hft0⟩ := hI.first hp0 nm D b bi hct hD h0
    have hps0 : ps = [] := List.eq_nil_of_length_eq_zero (hpsl.trans hp0)
    obtain ⟨D', Ds', rfl⟩ : ∃ D' Ds', Ds = D' :: Ds' :=
      match Ds, hfD with
      | D' :: Ds', _ => ⟨D', Ds', rfl⟩
      | [], h => absurd (h ▸ h0 : 0 < ([] : List VExpr).length) (by simp)
    have htr0 := hctr
    rw [hshape, hps0, hct] at htr0
    simp only [List.nil_append, VExpr.foralls] at htr0
    cases htr0 with | forallE _ _ hdomD _ => ?_
    refine ⟨?_, fun n us ax ra hDc hax hra => ?_⟩
    · rw [hft]
      have : ftys[0]? = some D' := by simpa using hft0
      rw [List.getElem?_eq_getElem hkl] at this; cases this; exact hdomD
    · have hmem : (0, ra) ∈ c.recFields := by
        simp only [VConstructor.recFields, List.mem_filterMap]
        exact ⟨(f, 0), List.mem_zipIdx_iff_getElem?.2 (by simpa using hf), by simp [hra]⟩
      obtain ⟨ih, -, ⟨hp, hk', -, hax'⟩⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_r hU.pieces _ hmem
      exact hax' dk n us ax hdk (hdkt.trans hDc) hax
  case kd =>
    refine ⟨⟨fvs, vfvs, ⟨cb₂.ngen.curr⟩, Mf, infos.toArray⟩, rfl, rfl, ?_, ?_, ?_⟩
    · refine ⟨hMf, by rw [hU.types]; exact hI.tele, hI.base, fun fv hfv => ?_,
        by simpa using hU.pieces⟩
      have h1 := hU.sub.lctx fv hfv
      obtain ⟨dd, hdd⟩ := hMf.tr.find?_eq_some.2 hfv
      change (cb₂.lctx.find? fv).map LocalDecl.erase = (Mf.lctx.find? fv).map _ at h1
      rw [hdd] at h1 ⊢
      exact VContext.push_erase h1
    · show VLCtx.fvars (_ :: cb₂.mlctx.vlctx) = _
      simp [hU.fvars, hI.fvars, MinorKD.seg]
    · intro fv d hd
      exact (VContext.push_find? (by simp [LocalContext.Dom, hx2 fv d hd])).trans (hx2 fv d hd)

theorem MinorsSetup.modify {cT : VContext} {pre : List Name} {Mp : TypeChecker.MLCtx}
    {pfvs : List FVarId} {params : List VExpr} {stats : InductiveStats}
    {types : List InductiveType} {d₀ : VInductDecl} {motfvs : List FVarId} {heads : List (Array Expr × Expr)}
    {recInfos : Array RecInfo} (H : MinorsSetup cT pre Mp pfvs params stats types d₀ motfvs heads recInfos)
    (hsz : recInfos.size = types.length) (d : Nat) {f : RecInfo → RecInfo}
    (hf : ∀ s, (f s).motive = s.motive ∧ (f s).indices = s.indices ∧ (f s).major = s.major) :
    MinorsSetup cT pre Mp pfvs params stats types d₀ motfvs heads (recInfos.modify d f) :=
  { H with
    motives := fun t ht => by
      have h1 : t < (recInfos.modify d f).size := by simp [hsz, ht]
      have h2 : t < recInfos.size := by simp [hsz, ht]
      rw [getElem!_pos _ t h1, Array.getElem_modify]
      split
      · rw [(hf _).1, ← getElem!_pos recInfos t h2]; exact H.motives t ht
      · rw [← getElem!_pos recInfos t h2]; exact H.motives t ht
    heads := fun t ht => by
      have h1 : t < (recInfos.modify d f).size := by simp [hsz, ht]
      have h2 : t < recInfos.size := by simp [hsz, ht]
      rw [getElem!_pos _ t h1, Array.getElem_modify]
      split
      · rw [(hf _).2.1, (hf _).2.2, ← getElem!_pos recInfos t h2]; exact H.heads t ht
      · rw [← getElem!_pos recInfos t h2]; exact H.heads t ht }

/-- A minor premise added to a type's record, as `loopCtors` adds it. -/
def RecInfo.addMinor (s : RecInfo) (x : Expr) (mi : MinorInfo) : RecInfo :=
  { s with minors := s.minors.push x, minorInfos := s.minorInfos.push mi }

/-- Appending a minor premise to the `d`th record keeps all the minor premises in order, when the
records after it have none. -/
theorem minors_modify (l : List RecInfo) (d : Nat) (hd : d < l.length) (x : Expr)
    (hlater : ∀ t (ht : t < l.length), d < t → l[t].minors = #[]) (mi : MinorInfo) :
    ((l.modify d (RecInfo.addMinor · x mi)).map (·.minors.toList)).flatten =
      (l.map (·.minors.toList)).flatten ++ [x] := by
  obtain ⟨A, s, B, hAB, hA⟩ : ∃ A s B, l = A ++ s :: B ∧ A.length = d :=
    ⟨l.take d, l[d], l.drop (d + 1), by simp, by simp; omega⟩
  subst hAB hA
  rw [List.modify_append_cons]
  have hB : (B.map (·.minors.toList)).flatten = [] := by
    rw [List.flatten_eq_nil_iff]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have := hlater (A.length + 1 + i) (by simp; omega) (by omega)
    simp only [List.getElem_append_right (show A.length ≤ A.length + 1 + i by omega),
      show A.length + 1 + i - A.length = i + 1 by omega, List.getElem_cons_succ] at this
    simp [this]
  simp [hB, RecInfo.addMinor]

theorem minorInfos_modify (l : List RecInfo) (d : Nat) (hd : d < l.length) (x : Expr)
    (hlater : ∀ t (ht : t < l.length), d < t → l[t].minorInfos = #[]) (mi : MinorInfo) :
    ((l.modify d (RecInfo.addMinor · x mi)).map (·.minorInfos.toList)).flatten =
      (l.map (·.minorInfos.toList)).flatten ++ [mi] := by
  obtain ⟨A, s, B, hAB, hA⟩ : ∃ A s B, l = A ++ s :: B ∧ A.length = d :=
    ⟨l.take d, l[d], l.drop (d + 1), by simp, by simp; omega⟩
  subst hAB hA
  rw [List.modify_append_cons]
  have hB : (B.map (·.minorInfos.toList)).flatten = [] := by
    rw [List.flatten_eq_nil_iff]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have := hlater (A.length + 1 + i) (by simp; omega) (by omega)
    simp only [List.getElem_append_right (show A.length ≤ A.length + 1 + i by omega),
      show A.length + 1 + i - A.length = i + 1 by omega, List.getElem_cons_succ] at this
    simp [this]
  simp [hB, RecInfo.addMinor]

/-- A constructor `ct` of the `j`th type, as `checkConstructors` leaves it: its declared type
translates to `C' = Π ps Ds, I params idx`, a type, over parameters agreeing with the block's. -/
def CtorShape (cT : VContext) (params : List VExpr) (types : List InductiveType) (j : Nat)
    (hj : j < types.length) (ct : Constructor) (C' : VExpr) (ps Ds idx : List VExpr) : Prop :=
  TrExprS cT.venv cT.lparams [] ct.type C' ∧ cT.venv.IsType cT.lparams.length [] C' ∧
  C' = .foralls (ps ++ Ds) (.appN (.const (types[j]'hj).name (VLevel.params cT.lparams.length))
    (VExpr.bvars params.length Ds.length ++ idx)) ∧
  declareConstructors.arity 0 ct.type = ps.length + Ds.length ∧
  cT.venv.TeleDefEq cT.lparams.length [] ps params

/-- What `loopCtors` leaves of a constructor: its shape and the specification's constructor. -/
def CtorDone (cT : VContext) (pre : List Name) (params : List VExpr)
    (types : List InductiveType) (d₀ : VInductDecl) (VB : VEnv) (UB : Nat) (j : Nat)
    (hj : j < types.length) (ct : Constructor) (c : VConstructor) : Prop :=
  ∃ C' ps Ds idx, CtorShape cT params types j hj ct C' ps Ds idx ∧
    CtorOut cT pre params d₀ VB UB j ct C' ps Ds idx c

/-- What `loopInd2` keeps, having opened the minor premises `minfvs` of the constructors `cds` of
the block, in order, each with the position of its type. -/
structure CtorsInv (cT : VContext) (X : Name → Prop) (pre : List Name)
    (Mp : TypeChecker.MLCtx) (hMp : Mp.WF cT.venv cT.lparams) (pfvs : List FVarId)
    (params : List VExpr) (stats : InductiveStats) (types : List InductiveType)
    (d₀ : VInductDecl) (motfvs : List FVarId) (heads : List (Array Expr × Expr)) (ml : VLevel) (P : VContext → Prop) (dIdx : Nat)
    (recInfos : Array RecInfo) (cds : List (Nat × VConstructor)) (minfvs : List FVarId)
    (kds : List MinorKD) (F₁ : List FVarId)
    (Mmin : TypeChecker.MLCtx) (cb : VContext) (ρp ρmin : Lift) : Prop where
  setup : MinorsSetup cT pre Mp pfvs params stats types d₀ motfvs heads recInfos
  size : recInfos.size = types.length
  minlen : minfvs.length = cds.length
  tele : Mmin.IsTele (pfvs ++ motfvs ++ minfvs)
    (params.map (·.instL (VLevel.shift pre.length cT.lparams.length)) ++
      d₀.motiveTypes (VLevel.shift pre.length cT.lparams.length) ml ++
      cds.zipIdx.map fun ((j, c), q) =>
        d₀.minorType (VLevel.shift pre.length cT.lparams.length) q j c)
  lift : VLCtx.FVLift' (Mp.instL (VLevel.shift pre.length cT.lparams.length)).vlctx
    Mmin.vlctx 0 (Lift.skipN .refl (types.length + cds.length)) 0
  sub : Sub X pre ρp (cT.small Mp hMp) cb
  ext : Ext Mmin cb ρmin
  pred : P cb
  minors : (recInfos.toList.map (·.minors.toList)).flatten = minfvs.map .fvar
  later : ∀ t (ht : t < recInfos.size), dIdx < t → recInfos[t].minors = #[]
  /-- Each minor premise was a fresh variable of a context satisfying `P`. -/
  minfresh : ∀ fv ∈ minfvs, ∃ cbX : VContext, P cbX ∧ fv = ⟨cbX.ngen.curr⟩
  /-- What the kernel opened for each minor premise, which `mkRecRules` builds the rules from. -/
  kdlen : kds.length = cds.length
  kdmin : kds.map (·.minor) = minfvs
  kdinfo : (recInfos.toList.map (·.minorInfos.toList)).flatten = kds.map (·.info)
  kdok : ∀ q (h1 : q < kds.length) (h2 : q < cds.length),
    MinorKDOK cT Mp pfvs params cb kds[q] cds[q].2
  kdfvars : cb.mlctx.vlctx.fvars = (kds.reverse.map (·.seg)).flatten ++ F₁
  laterInfos : ∀ t (ht : t < recInfos.size), dIdx < t → recInfos[t].minorInfos = #[]
  infoCount : ∀ t (ht : t < recInfos.size),
    recInfos[t].minorInfos.size = (cds.filter (·.1 = t)).length

theorem loopCtors.WF [VEnv.Injective] {blockNames : NameSet} {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {hMp : Mp.WF cT.venv cT.lparams} {pfvs : List FVarId}
    {params : List VExpr} {stats : InductiveStats} {types : List InductiveType}
    (hNM : NotMentionsOK cT.venv cT.lparams stats types)
    (hBN : ∀ t ∈ types, blockNames.contains t.name)
    {d₀ : VInductDecl} {motfvs : List FVarId} {heads : List (Array Expr × Expr)} {ml : VLevel} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {VB : VEnv} {UB : Nat} (hPV : ∀ cb, P cb → cb.venv = VB ∧ cb.lparams.length = UB)
    (hPB : d₀.BlockFacts VB UB (VLevel.shift pre.length cT.lparams.length))
    {dIdx : Nat} (hd : dIdx < types.length) {indTypeName : Name}
    (hshape : ∀ ct ∈ types[dIdx].ctors, ∃ C' ps Ds idx,
      CtorShape cT params types dIdx hd ct C' ps Ds idx ∧
      VB.constants ct.name = some ⟨cT.lparams.length, C'⟩)
    {cds₀ : List (Nat × VConstructor)} {F₁ : List FVarId} {k : Array RecInfo → M α} {Q}
    (H : ∀ recInfos cs minfvs kds Mmin cb ρp ρmin,
      CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos
        (cds₀ ++ cs.map (dIdx, ·)) minfvs kds F₁ Mmin cb ρp ρmin →
      List.Forall₂ (CtorDone cT pre params types d₀ VB UB dIdx hd) types[dIdx].ctors cs →
      WF cb (k recInfos) Q) :
    ∀ rest done cs recInfos minfvs kds Mmin cb ρp ρmin,
      types[dIdx].ctors = done ++ rest →
      List.Forall₂ (CtorDone cT pre params types d₀ VB UB dIdx hd) done cs →
      CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos
        (cds₀ ++ cs.map (dIdx, ·)) minfvs kds F₁ Mmin cb ρp ρmin →
      WF cb (mkRecInfos.loopCtors stats blockNames indTypeName dIdx recInfos rest k) Q := by
  intro rest
  induction rest with
  | nil =>
    intro done cs recInfos minfvs kds Mmin cb ρp ρmin hdone hcs hI
    simp only [List.append_nil] at hdone
    rw [mkRecInfos.loopCtors]
    exact H _ _ _ _ _ _ _ _ hI (hdone ▸ hcs)
  | cons ct rest ih =>
    intro done cs recInfos minfvs kds Mmin cb ρp ρmin hdone hcs hI
    rw [mkRecInfos.loopCtors]
    have hct : ct ∈ types[dIdx].ctors := by rw [hdone]; simp
    obtain ⟨C', ps, Ds, idx, ⟨hctr, hC'T, hsh, har, htele⟩, hcon⟩ := hshape ct hct
    refine ctorMinor.WF hNM hBN hI.setup hd hct hctr hC'T hsh har htele (by simp) hI.minlen hI.tele
      hI.lift
      hP (fun cb' h => (hPV cb' h).1 ▸ (hPV cb' h).2 ▸ hPB)
      (fun cb' h => (hPV cb' h).1 ▸ hcon) ?step hI.sub hI.ext hI.pred
    case step =>
    intro minorFv bu ihs c cb' ρp' ρmin' name ty hout hsub' hext' hP' hfr' hkd
    obtain ⟨kd, hkdm, hkdi, hkdok, hkdf, hkdx⟩ := hkd
    obtain ⟨hV', hU'⟩ := hPV cb' hP'
    have hsz := hI.size
    have hdlt : dIdx < recInfos.size := by omega
    refine ih (done ++ [ct]) (cs ++ [c])
      (recInfos.modify dIdx (RecInfo.addMinor · (.fvar minorFv) ⟨bu, ihs⟩)) (minfvs ++ [minorFv])
      (kds ++ [kd]) (.vlam minorFv name ty (d₀.minorType (VLevel.shift pre.length cT.lparams.length)
        (cds₀ ++ cs.map (dIdx, ·)).length dIdx c) .default Mmin) cb' ρp' ρmin'
      (by rw [hdone]; simp) ?_ ?_
    · refine (Lean4Lean.List.Forall₂.append_of_left (Lean4Lean.List.Forall₂.length_eq hcs)).2
        ⟨hcs, .cons ?_ .nil⟩
      refine ⟨C', ps, Ds, idx, ⟨hctr, hC'T, hsh, har, htele⟩, ?_⟩
      rw [← hV', ← hU']; exact hout
    · exact {
        setup := hI.setup.modify hsz dIdx fun _ => ⟨rfl, rfl, rfl⟩
        size := by simp [hsz]
        minlen := by simp [hI.minlen]; omega
        tele := by
          have := hI.tele.vlam (fv := minorFv) (name := name) (ty := ty) (bi := .default)
            (ty' := d₀.minorType (VLevel.shift pre.length cT.lparams.length)
              (cds₀ ++ cs.map (dIdx, ·)).length dIdx c)
          simpa [List.zipIdx_append] using this
        lift := by
          have := hI.lift.skip_fvar (minorFv, ty.fvarsList) (.vlam (d₀.minorType
            (VLevel.shift pre.length cT.lparams.length) (cds₀ ++ cs.map (dIdx, ·)).length dIdx c))
          simpa [Lift.skipN_skipN, VLocalDecl.depth, Nat.add_assoc] using this
        sub := hsub'
        ext := hext'
        pred := hP'
        minors := by
          rw [Array.toList_modify, minors_modify _ dIdx (by simp; omega) _
            (fun t ht h => by simpa using hI.later t (by simpa using ht) h), hI.minors]
          simp
        later := fun t ht h => by
          rw [Array.getElem_modify, if_neg (by omega)]
          exact hI.later t (by simpa using ht) h
        minfresh := fun fv hfv => by
          rcases List.mem_append.1 hfv with hfv | hfv
          · exact hI.minfresh fv hfv
          · obtain rfl := List.mem_singleton.1 hfv; exact hfr'
        kdlen := by simp [hI.kdlen]; omega
        kdmin := by simp [hI.kdmin, hkdm]
        kdinfo := by
          rw [Array.toList_modify, minorInfos_modify _ dIdx (by simp; omega) _
            (fun t ht h => by simpa using hI.laterInfos t (by simpa using ht) h), hI.kdinfo]
          simp [hkdi]
        kdok := fun q h1 h2 => by
          have e : cds₀ ++ (cs ++ [c]).map (dIdx, ·) = (cds₀ ++ cs.map (dIdx, ·)) ++ [(dIdx, c)] := by
            simp
          rcases Nat.lt_or_ge q kds.length with hq | hq
          · have hq' : q < (cds₀ ++ cs.map (dIdx, ·)).length := hI.kdlen ▸ hq
            have h3 : (cds₀ ++ (cs ++ [c]).map (dIdx, ·))[q]? = (cds₀ ++ cs.map (dIdx, ·))[q]? := by
              rw [e, List.getElem?_append_left hq']
            have h4 := (List.getElem?_eq_getElem h2).symm.trans (h3.trans (List.getElem?_eq_getElem hq'))
            have h5 : (kds ++ [kd])[q]? = kds[q]? := List.getElem?_append_left hq
            have h6 := (List.getElem?_eq_getElem h1).symm.trans (h5.trans (List.getElem?_eq_getElem hq))
            rw [Option.some.inj h4, Option.some.inj h6]
            exact (hI.kdok q hq hq').extend hkdx
          · obtain rfl : q = kds.length := by simp at h1; omega
            have h3 : (cds₀ ++ (cs ++ [c]).map (dIdx, ·))[kds.length]? = some (dIdx, c) := by
              rw [e, List.getElem?_append_right (Nat.le_of_eq hI.kdlen.symm)]; simp [hI.kdlen]
            have h4 := (List.getElem?_eq_getElem h2).symm.trans h3
            have h6 : (kds ++ [kd])[kds.length]'h1 = kd := by simp
            rw [Option.some.inj h4, h6]
            exact hkdok
        kdfvars := by rw [hkdf, hI.kdfvars]; simp
        laterInfos := fun t ht h => by
          rw [Array.getElem_modify, if_neg (by omega)]
          exact hI.laterInfos t (by simpa using ht) h
        infoCount := fun t ht => by
          have ht' : t < recInfos.size := by simpa using ht
          rw [Array.getElem_modify, show cds₀ ++ (cs ++ [c]).map (dIdx, ·) =
            (cds₀ ++ cs.map (dIdx, ·)) ++ [(dIdx, c)] by simp, List.filter_append,
            List.length_append, ← hI.infoCount t ht']
          split <;> simp [RecInfo.addMinor, *] }

/-- The block's constructors, with the positions of their types, from per-type lists. -/
def flatCtors (css : List (List VConstructor)) : List (Nat × VConstructor) :=
  (css.zipIdx.map fun (cs, t) => cs.map (t, ·)).flatten

theorem flatCtors_append (css : List (List VConstructor)) (cs : List VConstructor) :
    flatCtors (css ++ [cs]) = flatCtors css ++ cs.map (css.length, ·) := by
  simp [flatCtors, List.zipIdx_append]

theorem flatCtors_filter_length (t : Nat) : ∀ css : List (List VConstructor),
    ((flatCtors css).filter (·.1 = t)).length = (css[t]?.map List.length).getD 0 := by
  intro css
  obtain ⟨L, rfl⟩ : ∃ L, css = L.reverse := ⟨css.reverse, by simp⟩
  induction L with
  | nil => simp [flatCtors]
  | cons cs L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = css at ih ⊢
    rw [flatCtors_append, List.filter_append, List.length_append, ih]
    rcases Nat.lt_trichotomy t css.length with h | rfl | h
    · rw [List.getElem?_append_left h, List.filter_eq_nil_iff.2 (by simp; omega)]; simp
    · rw [List.getElem?_eq_none (Nat.le_refl _), List.getElem?_append_right (Nat.le_refl _)]
      simp [List.filter_map, Function.comp_def]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega),
        List.filter_eq_nil_iff.2 (by simp; omega)]; simp

theorem flatCtors_length : ∀ css : List (List VConstructor),
    (flatCtors css).length = (css.map List.length).sum := by
  intro css
  obtain ⟨L, rfl⟩ : ∃ L, css = L.reverse := ⟨css.reverse, by simp⟩
  induction L with
  | nil => simp [flatCtors]
  | cons cs L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = css at ih ⊢
    rw [flatCtors_append]; simp [ih]

theorem flatCtors_fst_lt : ∀ (css : List (List VConstructor)), ∀ x ∈ flatCtors css, x.1 < css.length := by
  intro css x hx
  simp only [flatCtors, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨⟨cs, t⟩, ht, rfl⟩, hx⟩ := hx
  obtain ⟨cv, -, rfl⟩ := List.mem_map.1 hx
  exact (List.mem_zipIdx' ht).1

theorem flatCtors_filter_lt (i : Nat) : ∀ css : List (List VConstructor),
    (flatCtors css).filter (·.1 < i) = flatCtors (css.take i) := by
  intro css
  obtain ⟨L, rfl⟩ : ∃ L, css = L.reverse := ⟨css.reverse, by simp⟩
  induction L with
  | nil => simp [flatCtors]
  | cons cs L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = css at ih ⊢
    rw [flatCtors_append, List.filter_append, ih]
    rcases Nat.lt_or_ge css.length i with h | h
    · rw [List.take_of_length_le (l := css) (by omega), List.take_of_length_le (by simp; omega),
        List.filter_eq_self.2 (by simp; omega), flatCtors_append]
    · rw [List.take_append_of_le_length h, List.filter_eq_nil_iff.2 (by simp; omega),
        List.append_nil]

theorem flatCtors_zipIdx_filter (i : Nat) : ∀ (css : List (List VConstructor)) (hi : i < css.length),
    (flatCtors css).zipIdx.filter (·.1.1 = i) =
      css[i].zipIdx.map fun (cv, p) => ((i, cv), (flatCtors (css.take i)).length + p) := by
  intro css
  obtain ⟨L, rfl⟩ : ∃ L, css = L.reverse := ⟨css.reverse, by simp⟩
  induction L with
  | nil => intro h; simp at h
  | cons cs L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = css at ih ⊢
    intro hi
    rw [flatCtors_append, List.zipIdx_append, List.filter_append]
    rcases Nat.lt_or_ge i css.length with h | h
    · rw [ih h, List.getElem_append_left h, List.take_append_of_le_length (Nat.le_of_lt h)]
      rw [List.filter_eq_nil_iff.2]; · simp
      intro x hx
      rw [List.zipIdx_eq_map_add, List.zipIdx_map] at hx
      simp only [List.mem_map] at hx
      obtain ⟨_, ⟨y, -, rfl⟩, rfl⟩ := hx
      simp; omega
    · obtain rfl : i = css.length := by simp at hi; omega
      rw [List.filter_eq_nil_iff.2, List.nil_append]
      · rw [List.getElem_append_right (Nat.le_refl _),
          List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _),
          List.filter_eq_self.2]
        · rw [List.zipIdx_eq_map_add, List.zipIdx_map, List.map_map]; simp
        · intro x hx
          rw [List.zipIdx_eq_map_add, List.zipIdx_map] at hx
          simp only [List.mem_map] at hx
          obtain ⟨_, ⟨y, -, rfl⟩, rfl⟩ := hx
          simp
      · intro x hx
        have := flatCtors_fst_lt css x.1 (List.fst_mem_of_mem_zipIdx hx)
        simp; omega

theorem CtorsInv.weaken {cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos cds
    minfvs kds F₁ Mmin cb ρp ρmin}
    (H : CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos cds minfvs
      kds F₁ Mmin cb ρp ρmin) {dIdx' : Nat} (h : dIdx ≤ dIdx') :
    CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx' recInfos cds minfvs
      kds F₁ Mmin cb ρp ρmin :=
  { H with
    later := fun t ht h' => H.later t ht (by omega)
    laterInfos := fun t ht h' => H.laterInfos t ht (by omega) }

theorem loopInd2.WF [VEnv.Injective] {blockNames : NameSet} {cT : VContext} {X : Name → Prop} {pre : List Name}
    {Mp : TypeChecker.MLCtx} {hMp : Mp.WF cT.venv cT.lparams} {pfvs : List FVarId}
    {params : List VExpr} {stats : InductiveStats} {types : List InductiveType}
    (hNM : NotMentionsOK cT.venv cT.lparams stats types)
    (hBN : ∀ t ∈ types, blockNames.contains t.name)
    {d₀ : VInductDecl} {motfvs : List FVarId} {heads : List (Array Expr × Expr)} {ml : VLevel} {P : VContext → Prop}
    (hP : ∀ cb name ty ty' bi h1 h2, P cb → P (cb.push name ty ty' bi h1 h2))
    {VB : VEnv} {UB : Nat} (hPV : ∀ cb, P cb → cb.venv = VB ∧ cb.lparams.length = UB)
    (hPB : d₀.BlockFacts VB UB (VLevel.shift pre.length cT.lparams.length))
    (hshape : ∀ t (ht : t < types.length), ∀ ct ∈ types[t].ctors, ∃ C' ps Ds idx,
      CtorShape cT params types t ht ct C' ps Ds idx ∧
      VB.constants ct.name = some ⟨cT.lparams.length, C'⟩)
    {F₁ : List FVarId} {k : Array RecInfo → M α} {Q}
    (H : ∀ recInfos css minfvs kds Mmin cb ρp ρmin,
      CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P types.length recInfos
        (flatCtors css) minfvs kds F₁ Mmin cb ρp ρmin →
      css.length = types.length →
      (∀ t (ht : t < types.length) (h' : t < css.length),
        List.Forall₂ (CtorDone cT pre params types d₀ VB UB t ht) types[t].ctors css[t]) →
      WF cb (k recInfos) Q) :
    ∀ n dIdx css recInfos minfvs kds Mmin cb ρp ρmin, dIdx + n = types.length →
      css.length = dIdx →
      (∀ t (ht : t < types.length) (h' : t < css.length),
        List.Forall₂ (CtorDone cT pre params types d₀ VB UB t ht) types[t].ctors css[t]) →
      CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos
        (flatCtors css) minfvs kds F₁ Mmin cb ρp ρmin →
      (∀ t (ht : t < recInfos.size), dIdx ≤ t → recInfos[t].minors = #[]) →
      WF cb (mkRecInfos.loopInd2 stats blockNames types.toArray dIdx recInfos k) Q := by
  intro n
  induction n with
  | zero =>
    intro dIdx css recInfos minfvs kds Mmin cb ρp ρmin hn hcl hcs hI _
    rw [mkRecInfos.loopInd2, dif_neg (by simp; omega)]
    exact H _ _ _ _ _ _ _ _ (hI.weaken (by omega)) (by omega) hcs
  | succ n ih =>
    intro dIdx css recInfos minfvs kds Mmin cb ρp ρmin hn hcl hcs hI hlater
    have hd : dIdx < types.length := by omega
    rw [mkRecInfos.loopInd2, dif_pos (by simp; omega)]
    simp only [List.getElem_toArray]
    have hI0 : CtorsInv cT X pre Mp hMp pfvs params stats types d₀ motfvs heads ml P dIdx recInfos
        (flatCtors css ++ ([] : List VConstructor).map (dIdx, ·)) minfvs kds F₁ Mmin cb ρp ρmin := by
      simpa using hI
    refine loopCtors.WF hNM hBN hP hPV hPB hd (hshape dIdx hd) ?_ types[dIdx].ctors [] [] recInfos minfvs
      kds Mmin cb ρp ρmin (by simp) .nil hI0
    intro recInfos' cs minfvs' kds' Mmin' cb' ρp' ρmin' hI' hcs'
    refine ih (dIdx + 1) (css ++ [cs]) recInfos' minfvs' kds' Mmin' cb' ρp' ρmin' (by omega)
      (by simp [hcl]) ?_ ?_ ?_
    · intro t ht h'
      rcases Nat.lt_or_ge t css.length with h1 | h1
      · rw [List.getElem_append_left h1]; exact hcs t ht h1
      · obtain rfl : t = css.length := by simp at h'; omega
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        subst hcl; exact hcs'
    · rw [flatCtors_append, hcl]; exact hI'.weaken (by omega)
    · intro t ht h
      exact hI'.later t ht (by omega)

end AddInductive
end Lean4Lean

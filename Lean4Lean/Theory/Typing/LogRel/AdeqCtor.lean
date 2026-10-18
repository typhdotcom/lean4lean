import Lean4Lean.Theory.Typing.LogRel.AdeqQuotLiftQ
import Lean4Lean.Theory.Typing.LogRel.IndTeleOf
import Lean4Lean.Theory.Typing.LogRel.AdeqStruct
import Lean4Lean.Theory.Typing.LogRel.StructProj

/-!
# A constructor's constant case

A constructor applied to related parameters and fields is related, at its type, to itself: at a
constructor shape it reduces to itself, its fields are related along its telescope at the type
shape's telescope, and its parameters and indices are the codomain's arguments.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp]

omit [AxInterp] in
theorem TShape.indTy_not_le_ctor' {l : List (WShape n)} {c : Name} {l' : List (WShape n')} :
    ¬(WShape.indTy r h l : WShape (n+1)).T ≤ (WShape.ctor' c l').T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_indTy le₁, WShape.lift_ctor' le₂]
  unfold WShape.ctor'; split <;>
    simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.indTy, WShape.ctor, WShape.bot]

omit [AxInterp] in
/-- A shape below a constructor shape is `bot` or a shape of that constructor with smaller
fields. -/
theorem WShape.le_ctor'_cases {m : WShape (n+1)} {c : Name} {l : List (WShape k)}
    (h : m.T ≤ (WShape.ctor' c l).T) :
    m = .bot ∨ ∃ fs hf, m = WShape.ctor c fs hf ∧ List.Forall₂ (fun x y => x.T ≤ y.T) fs l := by
  cases m using WShape.casesOn' with
  | bot => exact .inl rfl
  | sort r => exact (TShape.sort_not_le_ctor' h).elim
  | forallE a f => exact (TShape.forallE_not_le_ctor' h).elim
  | lam f hl => exact (TShape.lam_not_le_ctor' h).elim
  | ctor c' fs hf =>
    rw [WShape.ctor_eq_ctor'] at h
    obtain ⟨rfl, h2⟩ := TShape.ctor'_le_ctor' hf h
    exact .inr ⟨fs, hf, rfl, h2⟩
  | indTy r h' l' => exact (TShape.indTy_not_le_ctor' h).elim

omit [ShapeEnv] [AxInterp] in
/-- Instantiating a substitution's first variables by `q` and then substituting the next ones by
`qs` is substituting `q :: qs`. -/
theorem inst_subst_consList (X q : VExpr) (qs : List VExpr) :
    (X.inst q qs.length).subst (Subst.id.consList qs) = X.subst (Subst.id.consList (q :: qs)) := by
  rw [instN_eq, subst_subst]; congr 1; funext i
  show (Subst.liftN (Subst.one q) qs.length i).subst _ = (Subst.id.cons q).consList qs i
  rw [Subst.liftN_apply]
  split <;> rename_i h
  · show Subst.id.consList qs i = _
    rw [Subst.consList_lt _ _ _ h, Subst.consList_lt _ _ _ h]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + qs.length := ⟨i - qs.length, by omega⟩
    rw [Nat.add_sub_cancel, Subst.consList_ge]
    cases j with
    | zero =>
      show (q.liftN qs.length).subst _ = q
      rw [liftN_subst_consList, subst_id]
    | succ j =>
      show ((VExpr.bvar j).liftN qs.length).subst _ = .bvar j
      rw [liftN_subst_consList]; rfl

omit [ShapeEnv] [AxInterp] in
/-- Instantiating a telescope's first binders by `qs`, syntactically, substitutes them. -/
theorem piInst_foralls : ∀ (Ps : List VExpr) (X : VExpr) (qs : List VExpr),
    qs.length = Ps.length → piInst (.foralls Ps X) qs = X.subst (Subst.id.consList qs)
  | [], X, [], _ => by simp [piInst, VExpr.foralls]
  | P :: Ps, X, q :: qs, h => by
    simp only [VExpr.foralls, piInst]
    rw [inst_foralls_gen q Ps X 0]
    simp only [Nat.zero_add]
    rw [piInst_foralls _ _ qs (by simpa using h), show Ps.length = qs.length by simpa using h.symm,
      inst_subst_consList]

/-- Fields related along a telescope `T` from an interpretation of a model telescope `Tm` (the
same telescope, over the model's context): at each field both are pi types, the telescope shape's
domain interprets the model's domain at the valuation with the fields before it pushed, and what
each field needs, with what holds of the rest, is the invariant `P`. -/
theorem FieldsRel.of_interp (hM : ModelEnv env) {Γ : List VExpr} {n : Nat}
    {IH : LogRel env U Γ n}
    (P : VExpr → VExpr → Valuation → List VExpr → List VExpr → List (WShape n) → Prop)
    (H : ∀ {D B Dm Bm ρ m ms m' ms'} {x b : WShape n} {xs},
      P (.forallE D B) (.forallE Dm Bm) ρ (m :: ms) (m' :: ms') (x :: xs) →
      LE_Interp env ρ b.T Dm → x.HasType b →
      env.IsDefEq U Γ m m' D ∧ IH.DefEq m m' D x b ∧ P (B.inst m) Bm (ρ.push x.T) ms ms' xs)
    (Hpi : ∀ {T Tm ρ m ms m' ms' xs}, P T Tm ρ (m :: ms) (m' :: ms') xs →
      ∃ D B Dm Bm, T = .forallE D B ∧ Tm = .forallE Dm Bm) :
    ∀ {fs : List (WShape n)} {T Tm ρ} {tel : WShape n} {ms ms'}, P T Tm ρ ms ms' fs →
      LE_Interp env ρ tel.T Tm → TelFits tel fs → ms.length = fs.length →
      ms'.length = fs.length → FieldsRel IH T tel ms ms' fs
  | [], T, _, ρ, tel, ms, ms', _, _, _, h1, h2 => by
    rw [List.length_eq_zero_iff.1 h1, List.length_eq_zero_iff.1 h2]; trivial
  | _ :: _, _, _, _, _, [], _, _, _, _, h1, _ => nomatch h1
  | _ :: _, _, _, _, _, _ :: _, [], _, _, _, _, h2 => nomatch h2
  | x :: xs, T, Tm, ρ, tel, m :: ms, m' :: ms', hP, hT, hfit, h1, h2 => by
    obtain ⟨b, g, hv, hx, hfit⟩ := hfit
    obtain ⟨D, B, Dm, Bm, rfl, rfl⟩ := Hpi hP
    cases n with
    | zero => simp [WShape.piView] at hv
    | succ k =>
      obtain ⟨t, wf⟩ := tel
      cases t <;> simp [WShape.piView] at hv
      rename_i b0 f0
      obtain ⟨rfl, rfl⟩ := hv
      have hT' : LE_Interp env ρ (WShape.T (n := k+1) (.forallE ⟨b0, wf.1⟩ ⟨f0, wf.2⟩))
          (.forallE Dm Bm) := hT
      have hT2 := hT'.lift (m := WShape.T (n := k+1) (.forallE ⟨b0, wf.1⟩ ⟨f0, wf.2⟩))
        (Nat.le_succ (k+1))
      simp only [WShape.T] at hT2
      rw [WShape.lift_forallE (Nat.le_succ k)] at hT2
      obtain ⟨hb, hg⟩ := hT2.forallE_inv' hM
      obtain ⟨hmm, hrel, hP'⟩ := H hP hb hx
      exact ⟨D, B, _, _, rfl, .rfl, hx, hmm, hrel,
        FieldsRel.of_interp hM P H Hpi hP' (hg x) hfit (by simpa using h1) (by simpa using h2)⟩

/-- An inductive type shape interpreting an application of a recorded type former: its head is the
type former's, and each constructor's telescope shape is below the interpretation of the
constructor's type at the shapes of the parameters. -/
theorem blockTy_inv (hM : ModelEnv env) {s : Name} (hnd : ¬AxInterp.dom s) {d : VInductDecl}
    {t : Nat} {T : VInductiveType} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    {ρ : Valuation} {ls : List VLevel} {args : List VExpr}
    (hargs : args.length = d.params.length + T.indices.length)
    {K : Nat} {r : Bool} {h : IndHead} {l : List (WShape K)}
    (ha : LE_Interp env ρ (WShape.indTy r h l).T ((VExpr.const s ls).appN args)) :
    h = ⟨s, args.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩ ∧
    ∃ pp : List TShape,
      List.Forall₂ (fun x A => LE_Interp env ρ x A) pp (args.take d.params.length) ∧
      ∀ i c', T.ctors[i]? = some c' → ∃ (h' cty : TShape),
        LE_Interp env ρ h' (c'.type.instL ls) ∧ PiAppS h' pp cty ∧ (ctorTel h l i).T ≤ cty := by
  have hA : ConstArity env s (.indTy d t) (d.params.length + T.indices.length) := .indTy hs hT
  have ha' : LE_Interp env ρ (WShape.indTy r h l).T (spine s ls args.reverse) := by
    rw [spine_eq_appN]; exact ha
  obtain ⟨n0, H0⟩ := ha'.spine_inv hM.roles hnd (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y, hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = args.length := by rw [List.Forall₂.length_eq hra]; simp
  have hnb : ¬ y ≤ TShape.bot := fun hb => by
    have := WShape.LE.of_T ((hyy.trans hb).trans TShape.bot_eqv.2)
    simp [WShape.indTy, WShape.bot, WShape.LE.def, Shape.LE.def, Shape.bot] at this
  cases hC with
  | bot => exact (hnb TShape.bot_eqv.1).elim
  | lam he hle => exact (hnb (Const.lam_le_bot hM.roles he hle (hrl ▸ hargs ▸ hA))).elim
  | ext h0 => exact (hnd h0).elim
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | indTy h1 h2 h3 h4 h5 h6 =>
    rename_i ctys
    rw [hs] at h1; cases h1; rw [hT] at h2; cases h2
    have hle := hyy.trans h6
    let N := max K n0
    have hK : K ≤ N := Nat.le_max_left ..; have hn : n0 ≤ N := Nat.le_max_right ..
    have hle' := (TShape.LE.def (m := N+1) (Nat.succ_le_succ hK) (Nat.succ_le_succ hn)).1 hle
    simp only [WShape.lift_indTy hK, WShape.lift_indTy hn, WShape.indTy_le_indTy] at hle'
    obtain ⟨-, rfl, hl⟩ := hle'
    refine ⟨by rw [hrl], (rargs.reverse.take d.params.length).map (·.T), ?_, fun i c' hc' => ?_⟩
    · have := (List.Forall₂.reverse.2 hra)
      simp only [List.reverse_reverse] at this
      exact List.forall₂_map_left_iff.2 (List.forall₂_take' this)
    · obtain ⟨cty, hcty⟩ : ∃ cty, ctys[i]? = some cty := ⟨_, List.getElem?_eq_getElem (by
        rw [h4]; exact (List.getElem?_eq_some_iff.1 hc').1)⟩
      obtain ⟨h', hR, hP⟩ := h5 i c' cty hc' hcty
      refine ⟨h', cty.T, hR, hP, ?_⟩
      have htel := hl.getD' (d := WShape.bot) (d' := WShape.bot) WShape.LE.rfl (rargs.length + i)
      have e1 : (List.map (WShape.lift N) l).getD (rargs.length + i) WShape.bot =
          (ctorTel ⟨s, rargs.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩ l i).lift N := by
        simp only [ctorTel, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases l[rargs.length + i]? <;> simp
      have e2 : (List.map (WShape.lift N) (rargs.reverse ++ ctys)).getD (rargs.length + i)
          WShape.bot = cty.lift N := by
        simp only [List.getD_eq_getElem?_getD, List.map_append]
        rw [List.getElem?_append_right (by simp)]
        simp [hcty]
      rw [e1, e2] at htel
      exact (TShape.LE.def (m := N) hK hn).2 htel

omit [ShapeEnv] [AxInterp] in
theorem ctors_eq_of_name {cs : List VConstructor} (hnd : (cs.map (·.name)).Nodup) {c c' : VConstructor}
    (h1 : c ∈ cs) (h2 : c' ∈ cs) (e : c.name = c'.name) : c = c' := by
  induction cs with
  | nil => cases h1
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.mem_cons] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2]
    · exact (hnd.1 _ h2 (by subst h1; exact e.symm)).elim
    · exact (hnd.1 _ h1 (by subst h2; exact e)).elim
    · exact ih hnd.2 h1 h2

omit [ShapeEnv] [AxInterp] in
theorem ctors_getElem_of_idx {cs : List VConstructor} {c : VConstructor} {i : Nat}
    (hnd : (cs.map (·.name)).Nodup) (hc : c ∈ cs)
    (hi : (cs.map (·.name)).idxOf? c.name = some i) : cs[i]? = some c := by
  obtain ⟨hil, hie, -⟩ := List.idxOf?_eq_some_iff.1 hi
  have hil' : i < cs.length := by simpa using hil
  rw [List.getElem?_eq_getElem hil']
  congr 1
  exact ctors_eq_of_name hnd (List.getElem_mem hil') hc (by simpa using hie)

omit [ShapeEnv] [AxInterp] in
theorem ctors_find {cs : List VConstructor} {c : VConstructor} (hnd : (cs.map (·.name)).Nodup)
    (hc : c ∈ cs) : cs.find? (·.name == c.name) = some c := by
  obtain ⟨x, hx⟩ : ∃ x, cs.find? (·.name == c.name) = some x :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨c, hc, by simp⟩)
  rw [hx]; congr 1
  exact ctors_eq_of_name hnd (List.mem_of_find?_eq_some hx) hc (by simpa using List.find?_some hx)

omit [ShapeEnv] [AxInterp] in
/-- The values of the variables of a telescope of `k` binders under `σ`. -/
theorem consList_bvars_subst (σ : VExpr.Subst) (k : Nat) :
    ∀ i < k, VExpr.Subst.dflt.consList ((VExpr.bvars k 0).map (·.subst σ)) i = σ i := by
  intro i hi
  rw [VExpr.Subst.consList_lt _ _ _ (by simpa [VExpr.bvars] using hi)]
  simp [VExpr.bvars, VExpr.subst]

omit [ShapeEnv] [AxInterp] in
theorem piCount_foralls : ∀ (Xs : List VExpr) (Y : VExpr),
    piCount (.foralls Xs Y) = Xs.length + piCount Y
  | [], _ => by simp [VExpr.foralls]
  | _ :: Xs, Y => by simp [VExpr.foralls, piCount, piCount_foralls Xs Y]; omega

omit [ShapeEnv] [AxInterp] in
theorem piCount_appN_app : ∀ (as : List VExpr) (f a : VExpr), piCount ((VExpr.app f a).appN as) = 0
  | [], _, _ => rfl
  | b :: as, f, a => piCount_appN_app as _ b

omit [ShapeEnv] [AxInterp] in
theorem piCount_appN_const (as : List VExpr) (c : Name) (ls : List VLevel) :
    piCount ((VExpr.const c ls).appN as) = 0 := by
  cases as with
  | nil => rfl
  | cons a as => exact piCount_appN_app as _ a

omit [ShapeEnv] [AxInterp] in
theorem bvars_getElem {n k i : Nat} (h : i < (VExpr.bvars n k).length) :
    (VExpr.bvars n k)[i] = .bvar (n - 1 - i + k) := by
  simp [VExpr.bvars] at h ⊢

/-- The codomain of a constructor's type over its parameters and fields, at levels `l`. -/
def ctorCod (s : Name) (c : VConstructor) (np nf : Nat) (l : List VLevel) : VExpr :=
  (VExpr.const s l).appN (VExpr.bvars np nf ++ c.indices.map (·.instL l))

variable {henv : env.Ordered} {hU : StepUniq env} {Γ₀ : List VExpr}

omit [ShapeEnv] in
/-- A substitution along a closed context depends only on its values at the context's variables. -/
theorem substEq_congr_closed {Γ : List VExpr} :
    ∀ {Cs : List VExpr} {σ σ' τ τ' : VExpr.Subst}, CtxClosed Cs →
      (∀ i < Cs.length, σ i = τ i) → (∀ i < Cs.length, σ' i = τ' i) →
      VEnv.Ctx.SubstEq env U Γ σ σ' Cs → VEnv.Ctx.SubstEq env U Γ τ τ' Cs
  | [], _, _, _, _, _, _, _, _ => .nil
  | _ :: Cs, σ, σ', τ, τ', ⟨hC, hA⟩, h1, h2, .cons W hAt ha => by
    refine .cons (substEq_congr_closed hC (fun i hi => h1 (i+1) (by simp; omega))
      (fun i hi => h2 (i+1) (by simp; omega)) W) hAt ?_
    have e1 : σ.head = τ.head := h1 0 (by simp)
    have e2 : σ'.head = τ'.head := h2 0 (by simp)
    have e3 := hA.subst_congr (σ := σ.tail) (σ' := τ.tail) fun i hi => h1 (i+1) (by simp; omega)
    rw [← e1, ← e2, ← e3]; exact ha

omit [ShapeEnv] in
/-- Substitutions along a telescope `Ps ++ Ds` give each field of `Ds` its domain, instantiated
with the parameters' and earlier fields' values. -/
theorem fields_lookup {Ps Ds Γ : List VExpr} {σ σ' : VExpr.Subst}
    (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ' ((Ps ++ Ds).reverse ++ Γ))
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j)) :
    ∀ j (h : j < Ds.length), env.IsDefEq U Γ₀ (σ (Ds.length - 1 - j)) (σ' (Ds.length - 1 - j))
      (Ds[j].subst (Subst.dflt.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
        ((VExpr.bvars Ds.length 0).map (·.subst σ)).take j))) := by
  intro j hjD
  let qs := (VExpr.bvars Ps.length Ds.length).map (·.subst σ)
  let ms := (VExpr.bvars Ds.length 0).map (·.subst σ)
  have hqsl : qs.length = Ps.length := by simp [qs, VExpr.bvars]
  have hms_get : ∀ j (h : j < ms.length), ms[j] = σ (Ds.length - 1 - j) := by
    intro j h; simp [ms, VExpr.bvars, VExpr.subst]
  have hmsl : ms.length = Ds.length := by simp [ms, VExpr.bvars]
  have hjm : j < ms.length := by omega
  have L := Lookup.reverse_append (Ps ++ Ds) (Γ := Γ) (Ps.length + j) (by simp; omega)
  have e1 : (Ps ++ Ds).length - 1 - (Ps.length + j) = Ds.length - 1 - j := by simp; omega
  have e2 : (Ps ++ Ds)[Ps.length + j]'(by simp; omega) = Ds[j] := by
    rw [List.getElem_append_right (by omega)]; congr 1; omega
  have e3 : (Ps ++ Ds).length - (Ps.length + j) = Ds.length - j := by simp; omega
  rw [e1, e2, e3] at L
  have hcl := hDcl j Ds[j] (List.getElem?_eq_getElem hjD)
  have eT : (Ds[j].liftN (Ds.length - j)).subst σ =
      Ds[j].subst (Subst.dflt.consList (qs ++ ms.take j)) := by
    rw [← lift'_consN_skipN (n := Ds.length - j) (k := 0), subst_lift']
    refine hcl.subst_congr fun i hi => ?_
    have hl : (qs ++ ms.take j).length = Ps.length + j := by simp [hqsl]; omega
    rw [Subst.consList_lt _ _ _ (by omega), List.getElem_reverse]
    simp only [Subst.lift_l, Lift.consN, Lift.liftVar_skipN, Lift.liftVar]
    rw [List.getElem_append]
    split <;> rename_i h
    · simp [qs, VExpr.bvars, VExpr.subst]; congr 1; omega
    · rw [List.getElem_take, hms_get]; congr 1; simp [hqsl] at h ⊢; omega
  have hD := W.lookup L
  rwa [eT] at hD

/-- The fields of a telescope `Ps ++ Ds` under related substitutions are related along `Ds`,
instantiated with the parameters' values, at a telescope shape that interprets `Ds` at the
parameters' shapes, at field shapes below the fields' values. -/
theorem ctorFields_rel (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {Ps Ds : List VExpr} {cod : VExpr} {Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((Ps ++ Ds).reverse ++ Γ) ρ)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    {n0 : Nat} {tel : WShape n0} {fs : List (WShape n0)} {pp : List TShape}
    (hfl : fs.length = Ds.length) (hppl : pp.length = Ps.length)
    (hpp : ∀ p (h : p < pp.length), pp[p] ≤ ρ (Ps.length - 1 - p + Ds.length))
    (hfsle : ∀ j (h : j < fs.length), fs[j].T ≤ ρ (Ds.length - 1 - j))
    (hT : LE_Interp env (pushAll (fun i => ρ (i + (Ps.length + Ds.length))) pp) tel.T
      (.foralls Ds cod))
    (hfit : TelFits tel fs) :
    FieldsRel (LR (U := U) (Γ := Γ₀) henv hU n0)
      ((VExpr.foralls Ds cod).subst
        (Subst.id.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ)))) tel
      ((VExpr.bvars Ds.length 0).map (·.subst σ)) ((VExpr.bvars Ds.length 0).map (·.subst σ'))
      fs := by
  let qs := (VExpr.bvars Ps.length Ds.length).map (·.subst σ)
  let ms := (VExpr.bvars Ds.length 0).map (·.subst σ)
  let ms' := (VExpr.bvars Ds.length 0).map (·.subst σ')
  let ρΓ : Valuation := fun i => ρ (i + (Ps.length + Ds.length))
  have hmsl : ms.length = Ds.length := by simp [ms, VExpr.bvars]
  have hmsl' : ms'.length = Ds.length := by simp [ms', VExpr.bvars]
  have hqsl : qs.length = Ps.length := by simp [qs, VExpr.bvars]
  have hms_get : ∀ j (h : j < ms.length), ms[j] = σ (Ds.length - 1 - j) := by
    intro j h; simp [ms, VExpr.bvars, VExpr.subst]
  have hms_get' : ∀ j (h : j < ms'.length), ms'[j] = σ' (Ds.length - 1 - j) := by
    intro j h; simp [ms', VExpr.bvars, VExpr.subst]
  let P : VExpr → VExpr → Valuation → List VExpr → List VExpr → List (WShape n0) → Prop :=
    fun T Tm ρ' xs xs' ys => ∃ j, j ≤ Ds.length ∧ ys = fs.drop j ∧ xs = ms.drop j ∧
      xs' = ms'.drop j ∧ Tm = .foralls (Ds.drop j) cod ∧
      T = Tm.subst (Subst.id.consList (qs ++ ms.take j)) ∧
      ρ' = pushAll ρΓ (pp ++ (fs.take j).map (·.T))
  have Hpi : ∀ {T Tm ρ' m xs m' xs' ys}, P T Tm ρ' (m :: xs) (m' :: xs') ys →
      ∃ D B Dm Bm, T = .forallE D B ∧ Tm = .forallE Dm Bm := by
    rintro T Tm ρ' m xs m' xs' ys ⟨j, hj, -, hx, -, rfl, rfl, -⟩
    have hj' : j < ms.length := Classical.byContradiction fun h => by
      rw [List.drop_eq_nil_of_le (by omega)] at hx; cases hx
    obtain ⟨D, rest, hdrop⟩ : ∃ D rest, Ds.drop j = D :: rest :=
      ⟨_, _, List.drop_eq_getElem_cons (by omega)⟩
    rw [hdrop]; exact ⟨_, _, _, _, rfl, rfl⟩
  have H : ∀ {D B Dm Bm ρ' m xs m' xs'} {x b : WShape n0} {ys},
      P (.forallE D B) (.forallE Dm Bm) ρ' (m :: xs) (m' :: xs') (x :: ys) →
      LE_Interp env ρ' b.T Dm → x.HasType b →
      env.IsDefEq U Γ₀ m m' D ∧ (LR (U := U) (Γ := Γ₀) henv hU n0).DefEq m m' D x b ∧
        P (B.inst m) Bm (ρ'.push x.T) xs xs' ys := by
    rintro D B Dm Bm ρ' m xs m' xs' x b ys ⟨j, hj, hys, hx, hx', hTm, hT', hρ'⟩ hb hxb
    subst hρ'
    have hjm : j < ms.length := Classical.byContradiction fun h => by
      rw [List.drop_eq_nil_of_le (by omega)] at hx; cases hx
    have hjD : j < Ds.length := by omega
    have hjf : j < fs.length := by omega
    have hjm' : j < ms'.length := by omega
    rw [List.drop_eq_getElem_cons hjD] at hTm
    simp only [VExpr.foralls] at hTm
    cases hTm
    rw [List.drop_eq_getElem_cons hjm] at hx
    rw [List.drop_eq_getElem_cons hjm'] at hx'
    rw [List.drop_eq_getElem_cons hjf] at hys
    cases hx; cases hx'; cases hys
    simp only [VExpr.subst] at hT'
    cases hT'
    -- the lookup of the field's variable
    have L := Lookup.reverse_append (Ps ++ Ds) (Γ := Γ) (Ps.length + j) (by simp; omega)
    have e1 : (Ps ++ Ds).length - 1 - (Ps.length + j) = Ds.length - 1 - j := by simp; omega
    have e2 : (Ps ++ Ds)[Ps.length + j]'(by simp; omega) = Ds[j] := by
      rw [List.getElem_append_right (by omega)]; congr 1; omega
    have e3 : (Ps ++ Ds).length - (Ps.length + j) = Ds.length - j := by simp; omega
    rw [e1, e2, e3] at L
    -- the field's type, as the substitution sees it
    have hcl := hDcl j Ds[j] (List.getElem?_eq_getElem hjD)
    have eT : (Ds[j].liftN (Ds.length - j)).subst σ =
        Ds[j].subst (Subst.id.consList (qs ++ ms.take j)) := by
      rw [← lift'_consN_skipN (n := Ds.length - j) (k := 0), subst_lift']
      refine hcl.subst_congr fun i hi => ?_
      have hl : (qs ++ ms.take j).length = Ps.length + j := by simp [hqsl]; omega
      rw [Subst.consList_lt _ _ _ (by omega), List.getElem_reverse]
      simp only [Subst.lift_l, Lift.consN, Lift.liftVar_skipN, Lift.liftVar]
      rw [List.getElem_append]
      split <;> rename_i h
      · simp [qs, VExpr.bvars, VExpr.subst]; congr 1; omega
      · rw [List.getElem_take, hms_get]; congr 1; simp [hqsl] at h ⊢; omega
    -- the field's shape interprets its type in the context
    let ρd : Valuation := fun i => ρ (i + (Ds.length - j))
    have hρd : (pushAll ρΓ (pp ++ (fs.take j).map (·.T))).LE ρd := by
      intro i
      by_cases hi : i < Ps.length + j
      · have h1 : ∀ p (hp : p < pp.length), pp[p] ≤ ρd (Ps.length - 1 - p + j) := by
          intro p hp
          have := hpp p hp; simp only [ρd]
          rwa [show Ps.length - 1 - p + j + (Ds.length - j) = Ps.length - 1 - p + Ds.length by omega]
        have h2 : ∀ l (hl : l < ((fs.take j).map (·.T)).length),
            ((fs.take j).map (·.T))[l] ≤ ρd (j - 1 - l) := by
          intro l hl
          simp only [List.length_map, List.length_take] at hl
          simp only [List.getElem_map, List.getElem_take, ρd]
          have := hfsle l (by omega)
          rwa [show j - 1 - l + (Ds.length - j) = Ds.length - 1 - l by omega]
        have key := pushAll_le_of (σ := ρd) (N := Ps.length) (m := j) hppl
          (by simp only [List.length_map, List.length_take]; omega) h1 h2 i hi
        rw [pushAll_apply, dif_pos (by simp; omega)] at key ⊢; exact key
      · rw [pushAll_apply, dif_neg (by simp; omega)]
        simp only [ρd, ρΓ, List.length_append, List.length_map, List.length_take, hppl]
        rw [show i - (Ps.length + min j fs.length) + (Ps.length + Ds.length) =
          i + (Ds.length - j) by omega]
        exact .rfl
    have hbρ : LE_Interp env ρ b.T (Ds[j].liftN (Ds.length - j)) := by
      rw [← lift'_consN_skipN (n := Ds.length - j) (k := 0)]
      refine (weak'_iff hM.closed _ fun i => ?_).2 (hb.mono_l hρd)
      simp [ρd, Lift.consN, Lift.liftVar_skipN, Lift.liftVar]
    have hxle : fs[j].T ≤ ρ (Ds.length - 1 - j) := hfsle j hjf
    have R := LR.SubstWF.bvar hM W L hxle hbρ hxb
    have hD := (W.toSubstEq hΓ₀).lookup L
    simp only [VExpr.subst] at R
    rw [eT, ← hms_get j hjm, ← hms_get' j hjm'] at R hD
    refine ⟨hD, R, j + 1, by omega, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rw [inst_lift_cons, List.take_add_one, List.getElem?_eq_getElem hjm, Option.toList_some,
        ← List.append_assoc, Subst.consList_concat]
    · rw [List.take_add_one, List.getElem?_eq_getElem hjf, Option.toList_some, List.map_append,
        ← List.append_assoc]
      simp only [List.map_cons, List.map_nil]
      rw [pushAll_concat]
  exact FieldsRel.of_interp hM P H Hpi (fs := fs) (ρ := pushAll ρΓ pp)
    ⟨0, Nat.zero_le _, rfl, rfl, rfl, rfl, by simp only [List.take_zero, List.append_nil]; rfl,
      by simp⟩ hT hfit (by simp [hmsl, hfl]) (by simp [hmsl', hfl])

/-- What a structure constructor's case needs of its declaration, at its type's levels `ls`, for
the parameter binders `Ps` and field binders `Ds` of its type there: its declared domains `Ds₀`,
each a type equal to its field's view, and the parameter binders equal to the block's. -/
def StructHyps (env : VEnv) (U : Nat) (d : VInductDecl) (T : VInductiveType) (c : VConstructor)
    (ls : List VLevel) (Ps Ds : List VExpr) : Prop :=
  T.ctors = [c] ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = d.uvars ∧
  OnCtx (Ps ++ Ds).reverse (env.IsType U) ∧
  env.IsDefEqCtx U [] Ps.reverse (d.params.map (·.instL ls)).reverse ∧
  ∃ Ds₀ : List VExpr, Ds = Ds₀.map (·.instL ls) ∧ Ds₀.length = c.fields.length ∧
    (∀ k D (f : VField), Ds₀[k]? = some D → c.fields[k]? = some f →
      env.IsDefEq d.uvars (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse) D f.type
        (.sort f.level)) ∧
    env.IsTele d.uvars d.params.reverse (c.fields.map (·.type))

/-- A constructor, not a structure's, applied to its telescope's variables, under related
substitutions and at levels whose codomains are related: related at its codomain, at a
constructor shape, through its fields along its telescope. -/
theorem ctorSpine_core (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    {ci : VConstant} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    (hc : c ∈ T.ctors) (hnodup : (T.ctors.map (·.name)).Nodup)
    (hci : env.constants c.name = some ci) (hcity : ci.type = c.type)
    (hnd : ¬AxInterp.dom s)
    {ls : List VLevel} {Ps Ds : List VExpr}
    (hstr : IsStruct c.name = true → StructHyps env U d T c ls Ps Ds)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hDs : Ds.length = c.fields.length)
    (hnidx : c.indices.length = T.indices.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    (hicl : ∀ e ∈ c.indices, e.ClosedN (Ps.length + Ds.length))
    (hccl : (c.type.instL ls).ClosedN)
    {Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((Ps ++ Ds).reverse ++ Γ) ρ)
    {ls₁ ls₂ : List VLevel} {n : Nat} {m a : WShape n} (hma : m.HasType a)
    (hm : LE_Interp env ρ m.T
      ((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)))
    (ha : LE_Interp env ρ a.T (ctorCod s c Ps.length Ds.length ls))
    (hTA : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq
      ((ctorCod s c Ps.length Ds.length ls).subst σ) ((ctorCod s c Ps.length Ds.length ls).subst σ')
      a)
    (hT1 : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq
      ((ctorCod s c Ps.length Ds.length ls₁).subst σ) ((ctorCod s c Ps.length Ds.length ls).subst σ)
      a)
    (hT2 : (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq
      ((ctorCod s c Ps.length Ds.length ls₂).subst σ') ((ctorCod s c Ps.length Ds.length ls).subst σ)
      a)
    (ht1 : env.IsDefEq U Γ₀
      (((VExpr.const c.name ls₁).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      (((VExpr.const c.name ls₁).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      ((ctorCod s c Ps.length Ds.length ls).subst σ))
    (ht2 : env.IsDefEq U Γ₀
      (((VExpr.const c.name ls₂).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
      (((VExpr.const c.name ls₂).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
      ((ctorCod s c Ps.length Ds.length ls).subst σ))
    (hMN : env.IsDefEq U Γ₀
      (((VExpr.const c.name ls₁).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      (((VExpr.const c.name ls₂).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
      ((ctorCod s c Ps.length Ds.length ls).subst σ))
    (hM0 : env.IsDefEq U Γ₀
      (((VExpr.const c.name ls₁).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      (((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      ((ctorCod s c Ps.length Ds.length ls).subst σ)) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq
      (((VExpr.const c.name ls₁).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
      (((VExpr.const c.name ls₂).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
      ((ctorCod s c Ps.length Ds.length ls).subst σ) m a := by
  have hsplit : VExpr.bvars (Ps.length + Ds.length) 0 =
      VExpr.bvars Ps.length Ds.length ++ VExpr.bvars Ds.length 0 :=
    (VExpr.bvars_append Ps.length Ds.length 0).symm
  have hm' := hm; rw [hsplit] at hm'
  rcases ctorApp_inv hM hs hT hc (by simp [VExpr.bvars, hPs]) (by simp [VExpr.bvars, hDs]) hm'
    with hb | ⟨hnp, k', rf, hrf, hmle⟩
  · cases show m = .bot from TShape.le_bot.1 hb
    exact (LR _ _ _).bot hma.isType
  cases n with
  | zero =>
    obtain ⟨mv, wf⟩ := m
    cases mv with
    | bot => exact (LR _ _ _).bot hma.isType
    | sort r => exact (TShape.sort_not_le_ctor' (r := r) (n := 0) hmle).elim
  | succ n0 =>
  rcases WShape.le_ctor'_cases hmle with rfl | ⟨fs, hf, rfl, hfs⟩
  · exact (LR _ _ _).bot hma.isType
  obtain ⟨I, as, rfl⟩ := WShape.HasType.ctor_inv hma
  simp only [LR, LRS, LRS.DefEq.ctor_indTy]
  unfold LRS.IndVal
  refine .inl ?_
  -- the codomain's arguments
  have hcodσ : ∀ (l : List VLevel) (τ : VExpr.Subst), (ctorCod s c Ps.length Ds.length l).subst τ =
      (VExpr.const s l).appN ((VExpr.bvars Ps.length Ds.length).map (·.subst τ) ++
        c.indices.map (fun e => (e.instL l).subst τ)) := by
    intro l τ; simp [ctorCod, subst_appN, List.map_append, Function.comp_def, VExpr.subst]
  have hvals : ∀ (l : List VLevel) (τ : VExpr.Subst),
      ((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst τ =
      (VExpr.const c.name l).appN ((VExpr.bvars Ps.length Ds.length).map (·.subst τ) ++
        (VExpr.bvars Ds.length 0).map (·.subst τ)) := by
    intro l τ; rw [hsplit]; simp [subst_appN, List.map_append, VExpr.subst]
  obtain ⟨hI, pp, hpp, hpi⟩ := blockTy_inv hM hnd hs hT
    (args := VExpr.bvars Ps.length Ds.length ++ c.indices.map (·.instL ls))
    (by simp [VExpr.bvars, hPs, hnidx]) ha
  subst hI
  have hInS : Inert env s := Inert.of_role hM.roles (fun hdf e => henvW.rule_lhs_params hdf e)
    (.indTy hs hT) (fun _ h => nomatch h) (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hInC : Inert env c.name := Inert.of_role hM.roles
    (fun hdf e => henvW.rule_lhs_params hdf e) (.ctor hs hT hc rfl)
    (fun _ h => nomatch h) (fun _ _ h => nomatch h) (fun h => nomatch h)
  -- the type's telescopes, related to themselves
  have hTA' := hTA
  simp only [LR, LRS, LRS.TyDefEq.indTy_iff] at hTA'
  obtain ⟨hRA, hITA⟩ := hTA'.resolve_right fun ⟨hN, _⟩ =>
    NeRed.not_inert hU hInS hN (by rw [hcodσ]; exact .rfl)
  -- the constructor's index and arity in the type shape
  obtain ⟨i, hi, hfit⟩ := WShape.HasType.ctor_fits hma
  obtain ⟨i', hi', hk⟩ := WShape.HasType.ctor_arity hma
  rw [hi] at hi'; cases hi'
  have hci' : T.ctors[i]? = some c := ctors_getElem_of_idx hnodup hc hi
  -- the constructor's parameters
  have hCP : ∀ {l : List VLevel} {τ : VExpr.Subst},
      (LR (U := U) (Γ := Γ₀) henv hU (n0+1)).TyDefEq ((ctorCod s c Ps.length Ds.length l).subst τ)
        ((ctorCod s c Ps.length Ds.length ls).subst σ) (.indTy true ⟨s, (VExpr.bvars Ps.length Ds.length ++ c.indices.map (·.instL ls)).length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩ as) →
      CtorParams env U Γ₀ ⟨s, (VExpr.bvars Ps.length Ds.length ++ c.indices.map (·.instL ls)).length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩ c.name l ((VExpr.bvars Ps.length Ds.length).map (·.subst τ))
        ((VExpr.bvars Ds.length 0).map (·.subst τ)) ls
        ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
          c.indices.map (fun e => (e.instL ls).subst σ)) := by
    intro l τ H
    simp only [LR, LRS, LRS.TyDefEq.indTy_iff] at H
    obtain ⟨hR, -⟩ := H.resolve_right fun ⟨_, hN⟩ =>
      NeRed.not_inert hU hInS hN (by rw [hcodσ]; exact .rfl)
    rw [hcodσ, hcodσ] at hR
    have e1 : c.indices.map (fun e => (e.instL l).subst τ) = ctorIdx env s c.name l
        ((VExpr.bvars Ps.length Ds.length).map (·.subst τ) ++
          (VExpr.bvars Ds.length 0).map (·.subst τ)) := by
      simp only [ctorIdx, hs, hT, Option.bind_some, ctors_find hnodup hc]
      refine List.map_congr_left fun e he => ?_
      refine ((hicl e he).instL.subst_congr fun i hi => ?_)
      rw [← List.map_append, ← hsplit]
      exact (consList_bvars_subst τ _ i hi).symm
    rw [e1] at hR
    obtain ⟨lsA, AsA, hr, hP⟩ := CtorParams.of_indRel hR
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hr)
    exact hP
  -- the fields, along the constructor's telescope at the type's parameters
  have hfsl : fs.length = Ds.length := by
    simp [List.getElem?_map, hci'] at hk; omega
  have eTel : ctorTeleAt ci fs.length ls
      ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
        c.indices.map (fun e => (e.instL ls).subst σ)) =
      (VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst
        (Subst.id.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ))) := by
    rw [ctorTeleAt, hcity, ← piCount_instL c.type ls, hcty, piCount_foralls, ctorCod,
      piCount_appN_const, List.length_append, hfsl, Nat.add_zero, Nat.add_sub_cancel,
      List.take_left' (by simp [VExpr.bvars]), VExpr.foralls_append,
      piInst_foralls _ _ _ (by simp [VExpr.bvars])]
  have hFR : FieldsRel (LR (U := U) (Γ := Γ₀) henv hU n0)
      ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst
        (Subst.id.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ))))
      (ctorTel ⟨s, (VExpr.bvars Ps.length Ds.length ++ c.indices.map (·.instL ls)).length,
        T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩ as i)
      ((VExpr.bvars Ds.length 0).map (·.subst σ)) ((VExpr.bvars Ds.length 0).map (·.subst σ'))
      fs := by
    have hppl : pp.length = Ps.length := by
      rw [List.Forall₂.length_eq hpp]; simp [VExpr.bvars]; omega
    obtain ⟨h', cty, hh', hP', hle'⟩ := hpi i c hci'
    have hT0 := (closed_iff (ρ' := fun i => ρ (i + (Ps.length + Ds.length))) hM.closed hccl).1 hh'
    rw [hcty] at hT0
    have hT1 := LE_Interp.piAppS_foralls hM Ps hT0 hP' hppl
    refine ctorFields_rel hM hΓ₀ W hDcl hfsl hppl (fun p hp => ?_) (fun j hj => ?_)
      (hT1.mono hle') hfit
    · have hp2 : p < ((VExpr.bvars Ps.length Ds.length ++ c.indices.map (·.instL ls)).take
          d.params.length).length := by rw [← List.Forall₂.length_eq hpp]; exact hp
      have := List.Forall₂.getElem?' hpp (List.getElem?_eq_getElem hp) (List.getElem?_eq_getElem hp2)
      rw [List.getElem_take, List.getElem_append_left (by simp [VExpr.bvars]; omega),
        bvars_getElem] at this
      exact bvar_iff.1 this
    · have hj2 : j < rf.length := by rw [← List.Forall₂.length_eq hfs]; exact hj
      have hj3 : j < (VExpr.bvars Ds.length 0).length := by
        rw [← List.Forall₂.length_eq hrf]; exact hj2
      have h1 := List.Forall₂.getElem?' hfs (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj2)
      have h2 := List.Forall₂.getElem?' hrf (List.getElem?_eq_getElem hj2) (List.getElem?_eq_getElem hj3)
      rw [bvars_getElem] at h2
      simp only [Nat.add_zero] at h2
      exact h1.trans (bvar_iff.1 h2)
  split
  · rename_i hso
    obtain ⟨hone, hlsWF, hlslen, hPD, hPctx, Ds₀, hDs₀, hDs₀l, hV, hVT⟩ := hstr hso.1
    have hEo := henvW.ordered
    have hF := henvW.projFacts hs hT hone
    have hqsl : ((VExpr.bvars Ps.length Ds.length).map (·.subst σ)).length = d.params.length := by
      simp [VExpr.bvars, hPs]
    have hqsl' : ((VExpr.bvars Ps.length Ds.length).map (·.subst σ')).length = d.params.length := by
      simp [VExpr.bvars, hPs]
    have hmsl : ((VExpr.bvars Ds.length 0).map (·.subst σ)).length = c.fields.length := by
      simp [VExpr.bvars, hDs]
    have hmsl' : ((VExpr.bvars Ds.length 0).map (·.subst σ')).length = c.fields.length := by
      simp [VExpr.bvars, hDs]
    have hidxl : (c.indices.map (fun e => (e.instL ls).subst σ)).length = T.indices.length := by
      simp [hnidx]
    have hms_get : ∀ (τ : VExpr.Subst) j (h : j < ((VExpr.bvars Ds.length 0).map (·.subst τ)).length),
        ((VExpr.bvars Ds.length 0).map (·.subst τ))[j] = τ (Ds.length - 1 - j) := by
      intro τ j h; simp [VExpr.bvars, VExpr.subst]
    -- the parameters' values, along the block's parameters
    have WS := W.toSubstEq hΓ₀
    have Wv := Ctx.SubstEq.vals hEo hPD WS.left
    rw [List.length_reverse, List.length_append, hsplit, List.map_append, Subst.consList_append,
      List.reverse_append] at Wv
    have Wq := VEnv.Ctx.SubstEq.dropList (by simp [VExpr.bvars]) (by simp [VExpr.bvars]) Wv
    have Wq2 := VEnv.Ctx.SubstEq.defeqTele hEo hΓ₀ hPctx Wq
    have hpar : OnCtx (d.params.map (·.instL ls)).reverse (env.IsType U) := by
      simpa using (hF.params.instL hlsWF).onCtx (Γ := []) trivial
    have Wq3 : VEnv.Ctx.SubstEq env U Γ₀
        (Subst.dflt.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ)))
        (Subst.dflt.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ)))
        (d.params.map (·.instL ls)).reverse :=
      substEq_congr_closed (hpar.ctxClosed hEo)
        (fun i hi => by
          rw [Subst.consList_lt _ _ _ (by simpa [hqsl] using hi),
            Subst.consList_lt _ _ _ (by simpa [hqsl] using hi)])
        (fun i hi => by
          rw [Subst.consList_lt _ _ _ (by simpa [hqsl] using hi),
            Subst.consList_lt _ _ _ (by simpa [hqsl] using hi)]) Wq2
    -- the type, the values and the type's sort
    have eA := hcodσ ls σ
    have eM := hvals ls₁ σ
    have eN := hvals ls₂ σ'
    have eMl := hvals ls σ
    obtain ⟨u, hAu⟩ := ht1.isType hEo hΓ₀
    rw [eA] at hAu
    have hM0' := hM0; rw [eM, eMl, eA] at hM0'
    have hMN' := hMN; rw [eM, eN, eA] at hMN'
    -- the fields at their declared domains, and at their views
    have hDsget : ∀ j (h : j < Ds.length), Ds[j] = (Ds₀[j]'(by rw [hDs₀] at h; simpa using h)).instL ls := by
      intro j h; simp [hDs₀]
    have hfD : ∀ k (h : k < ((VExpr.bvars Ds.length 0).map (·.subst σ)).length) D, Ds₀[k]? = some D →
        env.HasType U Γ₀ ((VExpr.bvars Ds.length 0).map (·.subst σ))[k]
          ((D.instL ls).subst (Subst.dflt.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
            ((VExpr.bvars Ds.length 0).map (·.subst σ)).take k))) := by
      intro k h D hD
      have hkD : k < Ds.length := by simpa [VExpr.bvars] using h
      have := (fields_lookup WS hDcl k hkD).hasType.1
      rw [hms_get σ k h, ← (List.getElem?_eq_some_iff.1 hD).2, ← hDsget k hkD]
      exact this
    have hfsT := VEnv.fields_views hEo hΓ₀ hlsWF hV hVT Wq3 hDs₀l hfD
    have hPA : ∀ k < c.fields.length, d.ProjAllowed c ls k := fun k hk =>
      hso.2 ls _ (by rw [eA]; exact .rfl) hInS.whnf d t T c hs hT
        (by simp [hone]) rfl k hk
    -- each projection of the first value is its field, at its projection's type
    have hP : ∀ k (h : k < ((VExpr.bvars Ds.length 0).map (·.subst σ)).length),
        env.IsDefEq U Γ₀ (.proj s k ((VExpr.const c.name ls₁).appN
          ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
            (VExpr.bvars Ds.length 0).map (·.subst σ))))
          ((VExpr.bvars Ds.length 0).map (·.subst σ))[k]
          (c.projType ls s k ((VExpr.bvars Ps.length Ds.length).map (·.subst σ))
            ((VExpr.const c.name ls₁).appN ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++
              (VExpr.bvars Ds.length 0).map (·.subst σ)))) := by
      intro k h
      have hkf : k < c.fields.length := by omega
      obtain ⟨f, hf⟩ : ∃ f, c.fields[k]? = some f := ⟨_, List.getElem?_eq_getElem hkf⟩
      have pc := VEnv.projCongr hEo hΓ₀ hs hT hone hF hlsWF hlslen hqsl hidxl hqsl hidxl Wq3 hAu
        hM0' k f hf (hPA k hkf)
      have pi := VEnv.projIota_ctor hEo hΓ₀ hs hT hone hF hlsWF hlslen hqsl hidxl hmsl Wq3 hAu
        hM0'.hasType.2 hfsT k f _ hf (List.getElem?_eq_getElem h) (hPA k hkf)
      exact pc.2.trans (.defeqDF pc.1.symm pi)
    have DP := VEnv.declDom_projs hEo hΓ₀ hlsWF hV hVT Wq3 hmsl hP
    -- the type's arguments, and the type's telescopes
    have hRL := hRA.left
    obtain ⟨-, lsx, lsx', Asx, Asx', hx1, -, -, hx4, -, hx6⟩ := hRL
    rw [eA] at hx1
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hx1)
    have hTel := hITA.left' hU hRA ls _ ls _ (by rw [eA]; exact .rfl) (by rw [eA]; exact .rfl)
      c.name i fs.length ci hi hk hci
    rw [eM, eN]
    refine ⟨hInS, hITA.left' hU hRA, i, fs.length, ci, ls, _, _, _, hi, hk, hci,
      (by rw [eA]; exact .rfl), TRed.refl (by rw [← eM]; exact ht1), hInC.whnf,
      TRed.refl (by rw [← eN]; exact ht2), hInC.whnf, rfl, ?_, ⟨hx4, hx6.left⟩⟩
    rw [eTel] at hTel ⊢
    -- the domains instantiated by the parameters' values, by either base substitution
    have eD : ∀ j (h : j < Ds.length) (xs : List VExpr), xs.length = j →
        Ds[j].subst ((Subst.id.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ))).consList xs) =
        ((Ds₀[j]'(by rw [hDs₀] at h; simpa using h)).instL ls).subst
          (Subst.dflt.consList ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++ xs)) := by
      intro j h xs hxs
      rw [← hDsget j h, ← Subst.consList_append]
      refine (hDcl j _ (List.getElem?_eq_getElem h)).subst_congr fun i hi => ?_
      have hl : ((VExpr.bvars Ps.length Ds.length).map (·.subst σ) ++ xs).length = Ps.length + j := by
        simp [VExpr.bvars, hxs]
      rw [Subst.consList_lt _ _ _ (by omega), Subst.consList_lt _ _ _ (by omega)]
    refine FieldsRel.of_red hU (by simpa [hfsl] using hTel) hFR ?_ ?_
    · refine RedFields.of_foralls _ Ds _ _ _ _ (by simp [hfsl]) (by simp [hfsl]) (by simp [VExpr.bvars])
        fun j h1 h2 h3 => ?_
      have hjf : j < c.fields.length := by omega
      obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hjf⟩
      have hD0 : Ds₀[j]? = some (Ds₀[j]'(by omega)) := List.getElem?_eq_getElem _
      obtain ⟨-, hb, -⟩ := DP j h2 _ f hD0 hf
      rw [eD j h3 _ (by simp; omega), VEnv.projs_take' _ _ (by omega)]
      simp only [VExpr.projs, List.getElem_map, List.getElem_range] at hb ⊢
      exact ⟨.single (.projIota hs hT hone hqsl hmsl (by simp; exact ⟨_, List.getElem?_eq_getElem (by simpa [VExpr.bvars] using h3), rfl⟩)), hb⟩
    · refine RedFields.of_foralls _ Ds _ _ _ _ (by simp [hfsl]) (by simp [hfsl]) (by simp [VExpr.bvars])
        fun j h1 h2 h3 => ?_
      have hjf : j < c.fields.length := by omega
      have h2' : j < ((VExpr.bvars Ds.length 0).map (·.subst σ)).length := by simpa using h2
      obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hjf⟩
      have hD0 : Ds₀[j]? = some (Ds₀[j]'(by omega)) := List.getElem?_eq_getElem _
      obtain ⟨ha, hb, hc'⟩ := DP j h2' _ f hD0 hf
      rw [eD j h3 _ (by simp; omega), VEnv.projs_take' _ _ (by omega)]
      have pc := VEnv.projCongr hEo hΓ₀ hs hT hone hF hlsWF hlslen hqsl hidxl hqsl hidxl Wq3 hAu
        hMN' j f hf (hPA j hjf)
      have e3 := fields_lookup WS hDcl j h3
      rw [← hms_get σ j h2', ← hms_get σ' j h2, hDsget j h3] at e3
      have key := (VEnv.IsDefEq.defeqDF hc' pc.2.symm).trans (hb.trans (.defeqDF ha.symm e3))
      simp only [VExpr.projs, List.getElem_map, List.getElem_range] at key ⊢
      exact ⟨.single (.projIota hs hT hone hqsl' hmsl' (by simp; exact ⟨_, List.getElem?_eq_getElem (by simpa [VExpr.bvars] using h3), rfl⟩)), key⟩
  refine ⟨hInS, hInC, hITA.left' hU hRA, i, fs.length, ci, ls, _, ls₁,
    (VExpr.bvars Ps.length Ds.length).map (·.subst σ), (VExpr.bvars Ds.length 0).map (·.subst σ),
    ls₂, (VExpr.bvars Ps.length Ds.length).map (·.subst σ'),
    (VExpr.bvars Ds.length 0).map (·.subst σ'), hi, hk, hci, ?_, ?_, ?_, rfl, ?_, hCP hT1, hCP hT2⟩
  · rw [← hcodσ]; exact .rfl
  · rw [← hvals]; exact ⟨.rfl, ht1⟩
  · rw [← hvals]; exact ⟨.rfl, ht2⟩
  · rw [eTel]; exact hFR

/-- A constructor, not a structure's, applied to its telescope's variables at equivalent levels:
related at its codomain, given the codomains related and their soundness and the spines' typing. -/
theorem AdeqStmt.ctorSpine (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    {ci : VConstant} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    (hc : c ∈ T.ctors) (hnodup : (T.ctors.map (·.name)).Nodup)
    (hci : env.constants c.name = some ci) (hcity : ci.type = c.type)
    (hnd : ¬AxInterp.dom s)
    {ls ls' : List VLevel} {Ps Ds : List VExpr}
    (hstr : IsStruct c.name = true → StructHyps env U d T c ls Ps Ds)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hDs : Ds.length = c.fields.length)
    (hnidx : c.indices.length = T.indices.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    (hicl : ∀ e ∈ c.indices, e.ClosedN (Ps.length + Ds.length))
    (hccl : (c.type.instL ls).ClosedN)
    {Γ : List VExpr} (hΔ : OnCtx ((Ps ++ Ds).reverse ++ Γ) (env.IsType U)) {w : VLevel}
    (hsp : env.IsDefEq U ((Ps ++ Ds).reverse ++ Γ) ((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)) ((VExpr.const c.name ls').appN (VExpr.bvars (Ps.length + Ds.length) 0))
      (ctorCod s c Ps.length Ds.length ls))
    (hSB : StrongSoundEq env U ((Ps ++ Ds).reverse ++ Γ) (ctorCod s c Ps.length Ds.length ls)
      (ctorCod s c Ps.length Ds.length ls') (.sort w))
    (HB : AdeqStmt (U := U) henv hU Γ₀ ((Ps ++ Ds).reverse ++ Γ)
      (ctorCod s c Ps.length Ds.length ls) (ctorCod s c Ps.length Ds.length ls') (.sort w)) :
    AdeqStmt (U := U) henv hU Γ₀ ((Ps ++ Ds).reverse ++ Γ) ((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)) ((VExpr.const c.name ls').appN (VExpr.bvars (Ps.length + Ds.length) 0))
      (ctorCod s c Ps.length Ds.length ls) := by
  intro ρ n m a hm ha hma
  have hEo := henvW.ordered
  have tys : ∀ {σ σ'}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((Ps ++ Ds).reverse ++ Γ) ρ →
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((ctorCod s c Ps.length Ds.length ls).subst σ)
        ((ctorCod s c Ps.length Ds.length ls).subst σ') a ∧
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((ctorCod s c Ps.length Ds.length ls').subst σ)
        ((ctorCod s c Ps.length Ds.length ls').subst σ') a ∧
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq ((ctorCod s c Ps.length Ds.length ls).subst σ)
        ((ctorCod s c Ps.length Ds.length ls').subst σ) a := by
    intro σ σ' W
    have hA' := ha
    have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ := (hSB.left.sound W.fits hA').out
    have H := HB hA'' hSort hmem'
    exact ⟨LR.toValTy le_n le_a hma.isType hSort hmem' (H.1 W).1,
      LR.toValTy le_n le_a hma.isType hSort hmem' (H.1 W).2,
      LR.toValTy le_n le_a hma.isType hSort hmem' (H.2 W.left)⟩
  have typ : ∀ {σ σ'}, LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((Ps ++ Ds).reverse ++ Γ) ρ →
      ∀ (l : List VLevel), env.IsDefEq U ((Ps ++ Ds).reverse ++ Γ)
        ((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0))
        ((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0))
        (ctorCod s c Ps.length Ds.length ls) →
      env.IsDefEq U Γ₀ (((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
        (((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ)
        ((ctorCod s c Ps.length Ds.length ls).subst σ) ∧
      env.IsDefEq U Γ₀ (((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
        (((VExpr.const c.name l).appN (VExpr.bvars (Ps.length + Ds.length) 0)).subst σ')
        ((ctorCod s c Ps.length Ds.length ls).subst σ) := by
    intro σ σ' W l H
    have := H.substDF hEo hΔ hΓ₀ (W.toSubstEq hΓ₀)
    exact ⟨this.hasType.1, this.hasType.2⟩
  have core := @ctorSpine_core _ _ _ _ henv hU Γ₀ hM henvW hΓ₀ s d t T c ci hs hT hc hnodup hci hcity
    hnd ls Ps Ds hstr hcty hPs hDs hnidx hDcl hicl hccl Γ
  have hL := hsp.hasType.1
  have hR := hsp.hasType.2
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · obtain ⟨tA, -, -⟩ := tys W
    exact core W hma hm ha tA ((LR _ _ _).left_ty tA) ((LR _ _ _).symm_ty tA)
      (typ W ls hL).1 (typ W ls hL).2 (hL.substDF hEo hΔ hΓ₀ (W.toSubstEq hΓ₀)) (typ W ls hL).1
  · obtain ⟨tA, tB, -⟩ := tys W
    obtain ⟨-, -, tAB⟩ := tys W.left
    exact core W hma hm ha tA ((LR _ _ _).symm_ty tAB)
      ((LR _ _ _).trans_ty ((LR _ _ _).symm_ty tB) ((LR _ _ _).symm_ty tAB))
      (typ W ls' hR).1 (typ W ls' hR).2 (hR.substDF hEo hΔ hΓ₀ (W.toSubstEq hΓ₀))
      (hsp.symm.substDF hEo hΔ hΓ₀ (W.left.toSubstEq hΓ₀))
  · obtain ⟨tA, -, tAB⟩ := tys W
    exact core W hma hm ha tA ((LR _ _ _).left_ty tA) ((LR _ _ _).symm_ty tAB)
      (typ W ls hL).1 (typ W ls' hR).2 (hsp.substDF hEo hΔ hΓ₀ (W.left.toSubstEq hΓ₀))
      (typ W ls hL).1

/-- A constructor's constant case: given adequacy's cases for an environment `E₀` in which its
type's telescope and codomain are typed, model soundness for `E₀`, its spines at equivalent levels
equal, and in `E₀` their codomains equal. -/
theorem AdeqStmt.ctor (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₀ : VEnv} (hE₀le : E₀ ≤ env) (hE₀o : E₀.Ordered)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀)
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    {ci : VConstant} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    (hc : c ∈ T.ctors) (hnodup : (T.ctors.map (·.name)).Nodup)
    (hci : env.constants c.name = some ci) (hcity : ci.type = c.type)
    (hnd : ¬AxInterp.dom s)
    {ls ls' : List VLevel} {Ps Ds : List VExpr}
    (hstr : IsStruct c.name = true → StructHyps env U d T c ls Ps Ds)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hDs : Ds.length = c.fields.length)
    (hnidx : c.indices.length = T.indices.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    (hicl : ∀ e ∈ c.indices, e.ClosedN (Ps.length + Ds.length))
    (hccl : (c.type.instL ls).ClosedN)
    (hTe : E₀.IsTele U [] (Ps ++ Ds)) {w : VLevel}
    (hspE : env.IsDefEq U (Ps ++ Ds).reverse ((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)) ((VExpr.const c.name ls').appN (VExpr.bvars (Ps.length + Ds.length) 0))
      (ctorCod s c Ps.length Ds.length ls))
    (hBE : E₀.IsDefEq U (Ps ++ Ds).reverse (ctorCod s c Ps.length Ds.length ls)
      (ctorCod s c Ps.length Ds.length ls') (.sort w))
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    AdeqStmt (U := U) henv hU Γ₀ Γ (.const c.name ls) (.const c.name ls') (c.type.instL ls) := by
  have hEo := henvW.ordered
  have onBs : OnCtx (Ps ++ Ds).reverse (E₀.IsType U) := by simpa using hTe.onCtx (Γ := []) trivial
  have onBs' : OnCtx (Ps ++ Ds).reverse (env.IsType U) := onBs.mono fun h => h.mono hE₀le
  have hΔ : OnCtx ((Ps ++ Ds).reverse ++ Γ) (env.IsType U) :=
    OnCtx.append_closed hEo VEnv.LE.rfl hΓ onBs'
  have DB := IsDefEq.weak_closed hE₀o onBs hBE Γ
  have Dsp := IsDefEq.weak_closed hEo onBs' hspE Γ
  have HB : AdeqStmt (U := U) henv hU Γ₀ ((Ps ++ Ds).reverse ++ Γ)
      (ctorCod s c Ps.length Ds.length ls) (ctorCod s c Ps.length Ds.length ls') (.sort w) :=
    LR.adequacy_of hM hE₀le hS hΓ₀ IH DB hΔ
  have H : AdeqStmt (U := U) henv hU Γ₀ ((Ps ++ Ds).reverse ++ Γ) ((VExpr.const c.name ls).appN (VExpr.bvars (Ps.length + Ds.length) 0)) ((VExpr.const c.name ls').appN (VExpr.bvars (Ps.length + Ds.length) 0))
      (ctorCod s c Ps.length Ds.length ls) := by
    intro ρ n m a hm ha hma
    exact AdeqStmt.ctorSpine (U := U) (henv := henv) (hU := hU) (Γ₀ := Γ₀) hM henvW hΓ₀ hs hT hc
      hnodup hci hcity hnd hstr hcty hPs hDs hnidx hDcl hicl hccl hΔ Dsp.defeq (hS DB)
      @HB hm ha hma
  have hR : E₀.IsType U (Ps ++ Ds).reverse (ctorCod s c Ps.length Ds.length ls) :=
    ⟨_, hBE.hasType.1⟩
  have H' : AdeqStmt (U := U) henv hU Γ₀ ((Ps ++ Ds).reverse ++ Γ)
      (etaSpine (Ps ++ Ds) (.const c.name ls)) (etaSpine (Ps ++ Ds) (.const c.name ls'))
      (ctorCod s c Ps.length Ds.length ls) := by
    rw [etaSpine_eq, etaSpine_eq]
    simp only [VExpr.liftN, List.length_append]
    intro ρ n m a; exact H
  rw [hcty]
  have key : AdeqStmt (U := U) henv hU Γ₀ Γ (.const c.name ls) (.const c.name ls')
      (.foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls)) :=
    AdeqStmt.etaLams_closed hM hΓ₀ hE₀le hE₀o hS IH hTe hΓ hR @H'
  exact @key

end LogRel

import Lean4Lean.Theory.Typing.LogRel.ProjRed
import Lean4Lean.Theory.Typing.LogRel.AnnotStep

/-!
# The `projDF` and `projEta` cases at a block's own types

A projection of values related at a structure-like type of the block is related through the
fields the values' relation stores: their projections are related along the constructor's
telescope (`FieldsRel`), so the projected field is related at its telescope domain, and that
domain's shape interprets the projection's type (`indProjDFNew`).

A value is related to its structure eta expansion, whose projections the rule allows at the type's
levels (`indProjEtaNew`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr} [ShapeEnv] {n : Nat} {IH : LogRel env U Γ n}

theorem FieldsRel.take : ∀ {T} {tel : WShape n} {ms ns fs} (j : Nat), FieldsRel IH T tel ms ns fs →
    FieldsRel IH T tel (ms.take j) (ns.take j) (fs.take j)
  | _, _, [], [], [], _, _ => by simp [FieldsRel]
  | _, _, _ :: _, _ :: _, _ :: _, 0, _ => trivial
  | _, _, _ :: _, _ :: _, _ :: _, j+1, ⟨D, B, b, g, hv, r, hx, hd, hr, H⟩ =>
    ⟨D, B, b, g, hv, r, hx, hd, hr, FieldsRel.take j H⟩
  | _, _, [], [], _ :: _, _, H | _, _, [], _ :: _, _, _, H | _, _, _ :: _, [], _, _, H
  | _, _, _ :: _, _ :: _, [], _, H => by simp [FieldsRel] at H

/-- The `k`th field of fields related along a syntactic telescope: related at the telescope's
`k`th domain instantiated by the fields before it, at the telescope shape's domain there. -/
theorem FieldsRel.get_foralls : ∀ {fs : List (WShape n)} {Ds : List VExpr} {B : VExpr}
    {σ : VExpr.Subst} {tel : WShape n} {ms ns : List VExpr},
    FieldsRel IH ((VExpr.foralls Ds B).subst σ) tel ms ns fs →
    ∀ k x D, fs[k]? = some x → Ds[k]? = some D →
    ∃ b g m n', (tel.piApps (fs.take k)).piView = some (b, g) ∧ x.HasType b ∧
      ms[k]? = some m ∧ ns[k]? = some n' ∧
      env.IsDefEq U Γ m n' (D.subst (σ.consList (ms.take k))) ∧
      IH.DefEq m n' (D.subst (σ.consList (ms.take k))) x b
  | [], _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, h => by cases h
  | x0 :: fs, D0 :: Ds, B, σ, tel, ms, ns, H, k, x, D, hx, hD => by
    cases ms <;> cases ns <;> try simp [FieldsRel] at H
    rename_i m ms n' ns
    obtain ⟨D', B', b, g, hv, r, hxb, hd, hr, H'⟩ := H
    have e := StepS.of_whnf forallE_whnf' r
    simp only [VExpr.forallE.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    cases k with
    | zero =>
      cases hx; cases hD
      exact ⟨b, g, m, n', by simpa [WShape.piApps] using hv, hxb, rfl, rfl,
        by simpa using hd, by simpa using hr⟩
    | succ k =>
      rw [VExpr.subst_lift_inst] at H'
      obtain ⟨b', g', m', n'', hv', hx', hm, hn, hd', hr'⟩ :=
        FieldsRel.get_foralls H' k x D (by simpa using hx) (by simpa using hD)
      refine ⟨b', g', m', n'', ?_, hx', by simpa using hm, by simpa using hn, ?_, ?_⟩
      · simpa [WShape.piApps, hv] using hv'
      · simpa [VExpr.Subst.consList] using hd'
      · simpa [VExpr.Subst.consList] using hr'


omit [ShapeEnv] in
theorem piCount_subst_foralls : ∀ (Ds : List VExpr) (B : VExpr) (τ : VExpr.Subst),
    Ds.length ≤ piCount ((VExpr.foralls Ds B).subst τ)
  | [], _, _ => Nat.zero_le _
  | _ :: Ds, B, τ => by
    simp only [VExpr.foralls, VExpr.subst, piCount, List.length_cons]
    exact Nat.succ_le_succ (piCount_subst_foralls Ds B τ.lift)

omit [ShapeEnv] in
theorem piInst_subst_foralls : ∀ (ys Ds : List VExpr) (B : VExpr) (τ : VExpr.Subst),
    ys.length ≤ Ds.length →
    piInst ((VExpr.foralls Ds B).subst τ) ys = (VExpr.foralls (Ds.drop ys.length) B).subst (τ.consList ys)
  | [], _, _, _, _ => by simp [piInst, VExpr.Subst.consList]
  | _ :: _, [], _, _, h => by simp at h
  | y :: ys, D :: Ds, B, τ, h => by
    simp only [VExpr.foralls, VExpr.subst, piInst_forallE, VExpr.subst_lift_inst, List.length_cons,
      List.drop_succ_cons, VExpr.Subst.consList]
    exact piInst_subst_foralls ys Ds B (τ.cons y) (by simpa using h)

/-- The `k`th of fields `ms`, `ns` related along a syntactic telescope, related at a type `Q` the
telescope's domain there reduces to when instantiated by fields `xs` related to `ms`, and that
domain instantiated by `ms` is equal to. -/
theorem FieldsRel.field_conv (hU : StepUniq env) {Ds : List VExpr} {B : VExpr} {τ : VExpr.Subst}
    {tel : WShape n} {fs : List (WShape n)} {xs ms ns : List VExpr} {Q : VExpr}
    (hl : fs.length ≤ Ds.length)
    (TR : TeleRel IH fs.length ((VExpr.foralls Ds B).subst τ) ((VExpr.foralls Ds B).subst τ) tel)
    (FXM : FieldsRel IH ((VExpr.foralls Ds B).subst τ) tel xs ms fs)
    (FMN : FieldsRel IH ((VExpr.foralls Ds B).subst τ) tel ms ns fs)
    {k : Nat} {x : WShape n} {D : VExpr} {b : WShape n} {g : WShapeFun n}
    (hx : fs[k]? = some x) (hD : Ds[k]? = some D)
    (hv : (tel.piApps (fs.take k)).piView = some (b, g))
    (hQ : StepS env U Γ (D.subst (τ.consList (xs.take k))) Q)
    (hE : TyEq env U Γ (D.subst (τ.consList (ms.take k))) Q) :
    ∃ m n', ms[k]? = some m ∧ ns[k]? = some n' ∧ x.HasType b ∧ env.IsDefEq U Γ m n' Q ∧
      IH.DefEq m n' Q x b := by
  obtain ⟨b1, g1, m, n', hv1, hxb, hm, hn, hd, hr⟩ := FMN.get_foralls k x D hx hD
  rw [hv] at hv1; obtain ⟨rfl, rfl⟩ : b = b1 ∧ g = g1 := by simpa using hv1
  have hkf : k < fs.length := (List.getElem?_eq_some_iff.1 hx).1
  have hxl : xs.length = fs.length := FXM.length.1
  have hml : ms.length = fs.length := FMN.length.1
  have hxk : (xs.take k).length = k := by simp; omega
  have hmk : (ms.take k).length = k := by simp; omega
  have TR' : TeleRel IH ((xs.take k).length + (fs.length - k)) ((VExpr.foralls Ds B).subst τ)
      ((VExpr.foralls Ds B).subst τ) tel := by rw [hxk, Nat.add_sub_cancel' (Nat.le_of_lt hkf)]; exact TR
  have H := TeleRel.instArgs hU
    (Nat.le_trans (by omega) (piCount_subst_foralls Ds B τ))
    (Nat.le_trans (by omega) (piCount_subst_foralls Ds B τ)) TR' (FXM.take k)
  rw [piInst_subst_foralls _ _ _ _ (by omega), piInst_subst_foralls _ _ _ _ (by omega), hxk, hmk,
    show fs.length - k = (fs.length - k - 1) + 1 by omega] at H
  obtain ⟨D1, B1, D1', B1', r1, r1', -, hTy, -⟩ := H.of_piView hv
  have eD : Ds.drop k = D :: Ds.drop (k+1) := by
    rw [List.drop_eq_getElem_cons (by omega)]; congr; exact (List.getElem?_eq_some_iff.1 hD).2
  rw [eD] at r1 r1'
  simp only [VExpr.foralls, VExpr.subst] at r1 r1'
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa using StepS.of_whnf forallE_whnf' r1
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa using StepS.of_whnf forallE_whnf' r1'
  have hTy' := IH.symm_ty ((IH.whr_ty hQ .rfl).1 hTy)
  exact ⟨m, n', hm, hn, hxb, hE.defeqDF hd, IH.conv hE hTy' hr⟩

end

section
variable {env : VEnv} [ShapeEnv] [AxInterp]

omit [AxInterp] in
theorem WShape.piView_bot : (WShape.bot : WShape n).piView = none := by cases n <;> rfl

/-- A telescope shape interpreting a pi telescope: its domain after field shapes `fs` interprets
the telescope's domain there, at the valuation with them pushed. -/
theorem LE_Interp.piApps_dom (hM : ModelEnv env) : ∀ (k : Nat) {n : Nat} {tel : WShape n}
    {fs : List (WShape n)} {Ds : List VExpr} {B : VExpr} {ρ : Valuation} {b : WShape n} {g D},
    LE_Interp env ρ tel.T (.foralls Ds B) → k ≤ fs.length →
    (tel.piApps (fs.take k)).piView = some (b, g) → Ds[k]? = some D →
    LE_Interp env (pushAll ρ ((fs.take k).map (·.T))) b.T D
  | k, 0, _, _, _, _, _, _, _, _, _, _, hv, _ => by
    cases k <;> simp [WShape.piApps] at hv
  | k, n+1, tel, fs, Ds, B, ρ, b, g, D, hT, hk, hv, hD => by
    have fe {s : WShape n} {f : WShapeFun n} (hT : LE_Interp env ρ (WShape.forallE s f).T
        (.foralls Ds B)) : ∃ D0 Ds', Ds = D0 :: Ds' ∧
        LE_Interp env ρ (s.lift (n+1)).T D0 ∧
        ∀ x : WShape (n+1), LE_Interp env (ρ.push x.T) ((f.lift (n+1)).app x).T (.foralls Ds' B) := by
      have hT2 := hT.lift (m := (WShape.forallE s f).T) (Nat.le_succ (n+1))
      simp only [WShape.T] at hT2
      rw [WShape.lift_forallE (Nat.le_succ n)] at hT2
      obtain _ | ⟨D0, Ds'⟩ := Ds
      · simp at hD
      obtain ⟨hb, hg⟩ := hT2.forallE_inv' hM
      exact ⟨D0, Ds', rfl, hb, hg⟩
    cases k with
    | zero =>
      simp only [List.take_zero, WShape.piApps] at hv
      obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
      obtain ⟨D0, Ds', rfl, hb, -⟩ := fe hT
      cases hD; simpa [pushAll] using hb
    | succ k =>
      obtain _ | ⟨x, fs⟩ := fs; · simp at hk
      cases hpv : tel.piView with
      | none => simp [WShape.piApps, hpv, WShape.piView_bot] at hv
      | some bg =>
        obtain ⟨b0, g0⟩ := bg
        obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hpv
        obtain ⟨D0, Ds', rfl, -, hg⟩ := fe hT
        have := LE_Interp.piApps_dom hM k (hg x) (by simpa using hk)
          (by simpa [WShape.piApps] using hv) (by simpa using hD)
        simpa [pushAll] using this

end

section
variable {env : VEnv} [ShapeEnv] [AxInterp]

omit [AxInterp] in
/-- Field shapes fitting a telescope shape: each is typed at the telescope shape's domain after
the fields before it. -/
theorem TelFits.get : ∀ {tel : WShape n} {fs : List (WShape n)}, TelFits tel fs →
    ∀ j x, fs[j]? = some x → ∃ b g, (tel.piApps (fs.take j)).piView = some (b, g) ∧ x.HasType b
  | _, [], _, _, _, h => by cases h
  | _, _ :: _, ⟨b, g, hv, hx, H⟩, 0, _, h => by
    cases h; exact ⟨b, g, by simpa [WShape.piApps] using hv, hx⟩
  | _, _ :: _, ⟨_, _, hv, _, H⟩, j+1, x, h => by
    obtain ⟨b, g, hv', hx⟩ := TelFits.get H j x (by simpa using h)
    exact ⟨b, g, by simpa [WShape.piApps, hv] using hv', hx⟩

/-- `FieldsWF.view_interp` at a given shape: a shape interpreting a field's declared domain
interprets its view, at a valuation fitting the parameters and with fields typed at
interpretations of their declared domains before it. -/
theorem FieldsWF.view_interp_at (hM : ModelEnv env) {envX : VEnv} (hX : SoundHyps envX env)
    (hXe : envX ≤ env) (hO : envX.Ordered) {d : VInductDecl} {ls : List VLevel} {U : Nat}
    (hls : ∀ l ∈ ls, l.WF U) {Γc : List VExpr} {j : Nat} {Ds : List VExpr} {fs : List VField}
    (H : d.FieldsWF envX Γc j Ds fs) : OnCtx Γc (envX.IsType d.uvars) →
    ∀ {P : List TShape}, Valuation.Fits env [] (Γc.map (·.instL ls)) (pushAll .nil P) →
    ∀ {xs : List (WShape N)}, (∀ i x D, xs[i]? = some x → Ds[i]? = some D →
      ∃ b : WShape N, x.HasType b ∧
        LE_Interp env (pushAll .nil (P ++ (xs.take i).map (·.T))) b.T (D.instL ls)) →
    ∀ k (b : TShape) (D : VExpr) (f : VField), k ≤ xs.length → Ds[k]? = some D →
      fs[k]? = some f →
      LE_Interp env (pushAll .nil (P ++ (xs.take k).map (·.T))) b (D.instL ls) →
      LE_Interp env (pushAll .nil (P ++ (xs.take k).map (·.T))) b (f.type.instL ls) := by
  induction H with
  | nil => intro _ _ _ _ _ _ _ _ _ _ h; cases h
  | @cons Γc D j f Ds fs h1 h2 _ _ _ _ _ ih =>
    intro hΓ P W xs hxs k b D' f' hk hD hf' hb
    obtain ⟨u, hDf⟩ := h1
    have hS := hX.strongSound' hM hXe hO (hΓ.instL hls) (hDf.instL hls)
    cases k with
    | zero =>
      cases hD; cases hf'
      simp only [List.take_zero, List.map_nil, List.append_nil] at hb ⊢
      exact (hS.sound W).1 hb
    | succ k =>
      obtain _ | ⟨x0, xs⟩ := xs; · simp at hk
      obtain ⟨b0, hb0, hbD⟩ := hxs 0 x0 D rfl rfl
      simp only [List.take_zero, List.map_nil, List.append_nil] at hbD
      have hbf := (hS.sound W).1 hbD
      have hT := hX.strongSound' hM hXe hO (hΓ.instL hls) (h2.instL hls)
      have W' : Valuation.Fits env [] ((f.type :: Γc).map (·.instL ls))
          (pushAll .nil (P ++ [x0.T])) := by
        rw [pushAll_concat]
        exact .cons W (fun ha => InterpTyped.hsort (hT.left.sound W) ha) hbf
          (WShape.HasType.T hb0)
      have := ih ⟨hΓ, _, h2⟩ W' (xs := xs) (fun i x D hx hD => by
        obtain ⟨b, h1, h2⟩ := hxs (i + 1) x D hx hD
        refine ⟨b, h1, ?_⟩
        simpa [List.append_assoc] using h2) k b D' f' (by simpa using hk) hD hf'
        (by simpa [List.append_assoc] using hb)
      simpa [List.append_assoc] using this

end

section
variable {env : VEnv} [ShapeEnv] [AxInterp]

/-- The domain shape at the `k`th field of a constructor shape interpreting `e`, typed at an
inductive type shape interpreting `e`'s type, interprets the `k`th projection's type. -/
theorem projDom_interp (hM : ModelEnv env) {E₁ envT : VEnv} (hE₁ : E₁.WF) {d : VInductDecl}
    {s : Name} (hnd : ¬AxInterp.dom s)
    (hd : d.WF E₁) (hTs : E₁.addConstList d.typeConsts = some envT) (hle : envT ≤ env)
    (hX : SoundHyps envT env) {t : Nat} (hs : env.inducts s = some (d, t))
    {T : VInductiveType} (hT : d.types[t]? = some T) (hname : T.name = s)
    {Γ₀ Γ : List VExpr} {c : VConstructor} {k : Nat} {f : VField} {ls : List VLevel}
    {As I : List VExpr} {e : VExpr} {u : VLevel} {U : Nat}
    (hcs : T.ctors = [c]) (hf : c.fields[k]? = some f)
    (hls : ∀ l ∈ ls, l.WF U) (hAs : As.length = d.params.length)
    (hI : I.length = T.indices.length)
    (hS : StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u))
    {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ)
    {N : Nat} {l' : List (WShape N)} {hf'} {Ih : IndHead} {as : List (WShape N)}
    (hw : LE_Interp env ρ (WShape.ctor c.name l' hf').T e)
    (haI : LE_Interp env ρ (WShape.indTy true Ih as).T (.appN (.const s ls) (As ++ I)))
    (hwa : (WShape.ctor c.name l' hf').HasType (.indTy true Ih as))
    {b : WShape N} {g : WShapeFun N}
    (hv : ((ctorTel Ih as 0).piApps (l'.take k)).piView = some (b, g)) :
    LE_Interp env ρ b.T (c.projType ls s k As e) := by
  have hO : envT.Ordered := (VEnv.WF.addConstList hE₁ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hd.types T hT).1) hTs).ordered
  have hle₁ : E₁ ≤ envT := VEnv.addConstList_le hTs
  have hTm : T ∈ d.allTypes := List.mem_append_left _ (List.mem_of_getElem? hT)
  obtain ⟨hTW, hCW⟩ := hd.ctors envT hTs T hTm
  have hcW := hCW c (by simp [hcs])
  obtain ⟨Ps, Ds, hcty, hPD, hFW, -⟩ := hcW.shape
  have hPs : Ps.length = d.params.length := hPD.length_eq
  have hDl : Ds.length = c.fields.length := hFW.length
  have hPT : envT.IsTele d.uvars [] d.params := hd.params.mono hle₁
  have hΓP : OnCtx d.params.reverse (envT.IsType d.uvars) := by simpa using hPT.onCtx trivial
  -- the type shape's constructor telescope
  obtain ⟨hIh, pp, hpp, hpi⟩ := blockTy_inv hM hnd hs hT (args := As ++ I)
    (by simp [hAs, hI]) haI
  rw [List.take_left' hAs] at hpp
  obtain ⟨h', cty, hh', hPA, hle'⟩ := hpi 0 c (by simp [hcs])
  have hcty' : c.type.instL ls = .foralls (Ps.map (·.instL ls) ++ Ds.map (·.instL ls))
      ((T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length c.fields.length)
        c.indices).instL ls) := by
    rw [hcty, VEnv.foralls_instL', List.map_append]
  rw [hcty'] at hh'
  have hppl : pp.length = As.length := List.Forall₂.length_eq hpp
  have htel := (hh'.piAppS_foralls hM (Ps.map (·.instL ls)) hPA (by simp [hppl, hAs, hPs])).mono
    hle'
  -- the fields' shapes, and their count
  obtain ⟨i0, hi0, hfit⟩ := WShape.HasType.ctor_fits hwa
  obtain ⟨i1, hi1, hk1⟩ := WShape.HasType.ctor_arity hwa
  simp only [hIh, hcs, List.map_cons, List.map_nil] at hi0 hi1 hk1
  have e0 : ([c.name] : List Name).idxOf? c.name = some 0 := by simp [List.idxOf?]
  rw [e0] at hi0 hi1; cases hi0; cases hi1
  have hl'l : l'.length = c.fields.length := by simpa using hk1.symm
  -- the parameters, fitting the block's telescope
  have hQT : envT.IsTele U [] ((d.params ++ T.indices).map (·.instL ls)) := by
    simpa using ((hPT.append (by simpa using hTW.indices)).instL hls (Γ := []))
  obtain ⟨_, hdef⟩ := hTW.defeq
  have hdef' := hdef.instL hls (ls := ls)
  rw [VEnv.foralls_instL'] at hdef'
  have hRcl := (hdef'.closedN' hO.closed trivial).2.1
  have hcT : env.constants s = some ⟨d.uvars, T.type⟩ := hname ▸ hle.constants
    (VEnv.addConstList_constants_of_mem hTs (List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩))
  have hTcl : (T.type.instL ls).ClosedN := (hdef'.closedN' hO.closed trivial).1
  obtain ⟨hTS, -⟩ := StrongSound.spine hM
    (Qs := (d.params ++ T.indices).map (·.instL ls)) (R := .sort (d.level.inst ls))
    (fun i A hA => ⟨by simpa using VEnv.IsTele.closedN hO hQT trivial i A hA,
      by simpa using IsTele.soundAt hM hX hle hO hQT trivial i A hA⟩)
    hRcl (fun ci hci _ => by
      cases hcT.symm.trans hci
      exact SoundEq.closed hM hTcl hRcl
        (hX.strongSound' hM hle hO (Γ := []) trivial hdef').sound)
    (As ++ I).length (As ++ I) rfl (by simp [hAs, hI]) hS
  have hTS' := hTS.take d.params.length
  rw [List.take_take, Nat.min_eq_left (by simp [hAs]), List.take_left' hAs,
    ← List.map_take, List.take_left' rfl] at hTS'
  obtain ⟨P, hP1, hP2, hP3⟩ := hTS'.exists_fits hM W (pushAll_consList hpp)
  have hPl : P.length = As.length := List.Forall₂.length_eq hP1
  have hρLE : (pushAll .nil pp).LE (pushAll .nil P) := fun i => by
    by_cases hi : i < As.length
    · exact hP3 i hi
    · rw [pushAll_apply, pushAll_apply, dif_neg (by omega), dif_neg (by omega), hppl, hPl]
      exact .rfl
  -- each field's domain shape interprets its declared domain over `P`
  have hccl : (c.type.instL ls).ClosedN := by
    obtain ⟨_, h⟩ := hcW.type; exact (h.closedN hO trivial).instL
  rw [hcty'] at hccl
  have hdom : ∀ j (bj : WShape N) gj (D : VExpr), j ≤ l'.length →
      ((ctorTel Ih as 0).piApps (l'.take j)).piView = some (bj, gj) → Ds[j]? = some D →
      LE_Interp env (pushAll .nil (P ++ (l'.take j).map (·.T))) bj.T (D.instL ls) := by
    intro j bj gj D hj hvj hD
    have hD' : (Ds.map (·.instL ls))[j]? = some (D.instL ls) := by simp [hD]
    have h0 := LE_Interp.piApps_dom hM j htel hj hvj hD'
    rw [← pushAll_append] at h0
    have hcl : (D.instL ls).ClosedN (Ps.length + j) := by
      have := VExpr.ClosedN.foralls_getElem hccl (Ps.length + j) (D.instL ls)
        (by rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
          hD'])
      simpa using this
    have h1 := LE_Interp.closed hM.closed hcl (ρ' := pushAll .nil (pp ++ (l'.take j).map (·.T)))
      (fun i hi => by
        rw [pushAll_apply, pushAll_apply]
        have : i < (pp ++ (l'.take j).map (·.T)).length := by
          simp [hppl, hAs, ← hPs]; omega
        rw [dif_pos this, dif_pos this]) h0
    refine h1.mono_l ?_
    rw [pushAll_append, pushAll_append]
    exact pushAll_mono hρLE (List.forall₂_refl' fun _ => .rfl)
  have hxs : ∀ i x (D : VExpr), l'[i]? = some x → Ds[i]? = some D →
      ∃ b : WShape N, x.HasType b ∧
        LE_Interp env (pushAll .nil (P ++ (l'.take i).map (·.T))) b.T (D.instL ls) := by
    intro i x D hx hD
    obtain ⟨bi, gi, hvi, hxi⟩ := hfit.get i x hx
    exact ⟨bi, hxi, hdom i bi gi D (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hx).1) hvi hD⟩
  have hkf : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨D, hD⟩ : ∃ D, Ds[k]? = some D := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have W' : Valuation.Fits env [] (d.params.reverse.map (·.instL ls)) (pushAll .nil P) := by
    rw [List.map_reverse]; exact hP2
  have hbv := FieldsWF.view_interp_at hM hX hle hO hls hFW hΓP W' hxs k b.T D f (by omega) hD hf
    (hdom k b g D (by omega) hv hD)
  -- substituted by the parameters and the projections
  have hw' : LE_Interp env ρ (WShape.ctor' c.name l').T e := by
    rw [← WShape.ctor_eq_ctor' (h := hf')]; exact hw
  unfold VConstructor.projType
  rw [hf]
  refine TeleSubst.interp_subst hM (List.forall₂_append' hP1 ?_) hbv
  refine List.forall₂_of_getElem? (by simp [VExpr.projs]; omega) fun j y z hy hz => ?_
  have hj : j < k := by simpa [VExpr.projs] using (List.getElem?_eq_some_iff.1 hz).1
  simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at hz
  subst hz
  simp only [List.getElem?_map, List.getElem?_take_of_lt hj] at hy
  obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1 hy
  exact .proj hs hT hcs hw' hy' .rfl

end

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem _root_.Lean4Lean.VEnv.IsTele.of_onCtx : ∀ {As Γ : List VExpr},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.IsTele U Γ As
  | [], _, _ => .nil
  | A :: As, Γ, h => by
    have h' : OnCtx (As.reverse ++ (A :: Γ)) (env.IsType U) := by simpa using h
    exact .cons (OnCtx.of_append h').2 (VEnv.IsTele.of_onCtx h')

theorem subst_consList_id_dflt {D : VExpr} {n : Nat} (hD : D.ClosedN n) {xs : List VExpr}
    (hx : xs.length = n) : D.subst (Subst.id.consList xs) = D.subst (Subst.dflt.consList xs) :=
  hD.subst_congr fun i hi => by
    rw [Subst.consList_lt _ _ _ (by omega), Subst.consList_lt _ _ _ (by omega)]

/-- A projection's type, as the constructor's declared domain at the parameters and the earlier
projections. -/
theorem projType_declDom (henvW : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T)
    {ls : List VLevel} {Ps Ds : List VExpr} (hSH : StructHyps env U d T c ls Ps Ds)
    (hPs : Ps.length = d.params.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    {As I : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (WP : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    {u : VLevel}
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    (hPA : ∀ j < c.fields.length, d.ProjAllowed c ls j)
    {X : VExpr} (hX : env.IsDefEq U Γ X X (.appN (.const s ls) (As ++ I)))
    {j : Nat} {D : VExpr} {f : VField} (hD : Ds[j]? = some D) (hf : c.fields[j]? = some f) :
    env.IsDefEq U Γ (c.projType ls s j As X)
      (D.subst ((Subst.id.consList As).consList (VExpr.projs s j X))) (.sort (f.level.inst ls)) := by
  have henv := henvW.ordered
  obtain ⟨h3, hls, hlen, -, -, Ds₀, hDs₀, hDs₀l, hV, hVT⟩ := hSH
  have hF := henvW.projFacts h1 h2 h3
  have hjf : j < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨D₀, hD₀, rfl⟩ : ∃ D₀, Ds₀[j]? = some D₀ ∧ D₀.instL ls = D := by
    rw [hDs₀, List.getElem?_map] at hD
    obtain ⟨D₀, h, e⟩ := Option.map_eq_some_iff.1 hD; exact ⟨D₀, h, e⟩
  have := (VEnv.declDom_projs henv hΓ hls hV hVT WP (x := X) (ms := VExpr.projs s c.fields.length X)
    (by simp [VExpr.projs]) (fun k hk => by
      have hkf : k < c.fields.length := by simpa [VExpr.projs] using hk
      obtain ⟨fk, hfk⟩ : ∃ fk, c.fields[k]? = some fk := ⟨_, List.getElem?_eq_getElem hkf⟩
      simpa [VExpr.projs] using
        (VEnv.projCongr henv hΓ h1 h2 h3 hF hls hlen hA hI hA hI WP hS hX k fk hfk
          (hPA k hkf)).2) j (by simpa [VExpr.projs] using hjf) D₀ f hD₀ hf).2.2
  rw [← Subst.consList_append, subst_consList_id_dflt (hDcl j _ hD) (by simp [hA, hPs,
    VExpr.projs])]
  exact this

/-- A projection of a value that reduces, typed, to a constructor application whose parameters
and indices are related to the type's arguments (`CtorParams`), and whose fields are typed along
the constructor's declared telescope at the type's parameters: it reduces, typed at its
projection type, to the field. -/
theorem TRed.proj_ctorVal (henvW : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T)
    {ls ls₁ : List VLevel} {Ps Ds : List VExpr} (hSH : StructHyps env U d T c ls Ps Ds)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hnidx : c.indices.length = T.indices.length)
    {As I qs ms : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (WP : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    {u : VLevel}
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    {h : IndHead} (hh : h.name = s)
    (hCP : CtorParams env U Γ h c.name ls₁ qs ms ls (As ++ I))
    (hms : ms.length = c.fields.length)
    (hmsT : ∀ j (hj : j < ms.length) D, Ds[j]? = some D →
      env.HasType U Γ ms[j] (D.subst (Subst.dflt.consList (As ++ ms.take j))))
    {M : VExpr}
    (hM : TRed env U Γ M ((VExpr.const c.name ls₁).appN (qs ++ ms)) (.appN (.const s ls) (As ++ I)))
    {k : Nat} {f : VField} {a : VExpr} (hf : c.fields[k]? = some f) (ha : ms[k]? = some a)
    (hP : d.ProjAllowed c ls k) :
    TRed env U Γ (.proj s k M) a (c.projType ls s k As M) := by
  have henv := henvW.ordered
  obtain ⟨h3, hls, hlen, hPD, hPctx, Ds₀, hDs₀, hDs₀l, hV, hVT⟩ := hSH
  have hF := henvW.projFacts h1 h2 h3
  have hDl : Ds.length = c.fields.length := by rw [hDs₀]; simpa using hDs₀l
  obtain ⟨hl₁, hCl, -, hR⟩ := hCP
  subst hh
  simp only [typeTele_block h1 h2] at hR hCl
  have hidx : ctorIdx env h.name c.name ls₁ (qs ++ ms) =
      c.indices.map (fun e => (e.instL ls₁).subst (Subst.dflt.consList (qs ++ ms))) := by
    simp [ctorIdx, h1, h2, h3]
  rw [hidx] at hR hCl
  have hqs : qs.length = d.params.length := by simp at hCl; omega
  -- the constructor application's levels
  obtain ⟨_, hci, hls₁, -⟩ := (appN_wf_prefix henv hΓ (as := []) (bs := qs ++ ms)
    (by rw [List.nil_append]; exact ⟨_, hM.2.hasType.2⟩)).const_inv henv hΓ
  cases hcC.symm.trans hci
  -- the type's parameters, related to the constructor application's
  have hpar : OnCtx (d.params.map (·.instL ls)).reverse (env.IsType U) := by
    simpa using (hF.params.instL hls).onCtx (Γ := []) trivial
  have R1 := hR.symm.take d.params.length (by simp [hA, hI]) (by simp [hqs, hnidx])
  rw [List.take_left' hA, List.take_left' hqs, ← List.map_take, ← List.map_take,
    List.take_left' rfl] at R1
  have WAq := VEnv.Ctx.SubstEq.defeqTele henv hΓ (hPctx.symm henv) (R1.substEq hpar)
  -- the rebuilt application at the type's levels and parameters
  have hTe : env.IsTele U Ps.reverse Ds := VEnv.IsTele.of_onCtx (by simpa using hPD)
  have W2 := VEnv.Ctx.SubstEq.ofGetElemDF WAq ms.length (As := Ds) (as := ms) (bs := ms) rfl hTe
    (by omega) (by omega) fun r hr _ hr' => by
      have := hmsT r hr _ (List.getElem?_eq_getElem hr')
      rw [Subst.consList_append] at this
      exact this
  have hccl : (c.type.instL ls).ClosedN := (henv.closedC hcC).instL
  have hc : env.IsDefEq U Γ (.const c.name ls) (.const c.name ls₁)
      ((VExpr.foralls (Ps ++ Ds) (ctorCod h.name c Ps.length Ds.length ls)).subst Subst.dflt) := by
    rw [← hcty, hccl.subst_eq Subst.Fixes.zero]
    exact .constDF hcC hls hls₁ hlen (hl₁.swap' fun _ _ e => Eq.symm e)
  have hXX := VEnv.IsDefEq.appN_substTDF (Δ := []) (as := As ++ ms) (bs := qs ++ ms) hc
    (by simp [hA, hPs, hms, hDl]) (by simp [hqs, hPs, hms, hDl])
    (by rw [Subst.consList_append, Subst.consList_append, List.reverse_append, List.append_nil]
        exact W2)
  have hcod : (ctorCod h.name c Ps.length Ds.length ls).subst (Subst.dflt.consList (As ++ ms)) =
      (VExpr.const h.name ls).appN (As ++ c.indices.map fun e =>
        (e.instL ls).subst (Subst.dflt.consList (As ++ ms))) := by
    simp only [ctorCod, subst_appN, List.map_append, VExpr.subst, List.map_map]
    rw [Subst.consList_append, show Ds.length = 0 + ms.length by omega,
      subst_bvars_consList_ge, hPs, ← hA, subst_bvars_consList]
    rfl
  rw [hcod] at hXX
  obtain ⟨u₂, hS₂⟩ := hXX.hasType.1.isType henv hΓ
  have hidl : (c.indices.map fun e =>
      (e.instL ls).subst (Subst.dflt.consList (As ++ ms))).length = T.indices.length := by
    simp [hnidx]
  have hfsT := VEnv.fields_views henv hΓ hls hV hVT WP hDs₀l (vs := ms) fun j hj D hD =>
    hmsT j hj (D.instL ls) (by rw [hDs₀]; simp [hD])
  have hι := VEnv.projIota_ctor henv hΓ h1 h2 h3 hF hls hlen hA hidl hms WP hS₂ hXX.hasType.1
    hfsT k f a hf ha hP
  have pc := VEnv.projCongr henv hΓ h1 h2 h3 hF hls hlen hA hidl hA hidl WP hS₂ hXX.symm k f hf hP
  have hty := VEnv.projType_congr henv hΓ h1 h2 h3 hF hls hlen hls
    (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hA hI hA hI WP hS hM.2 hf hP
  have pM := TRed.proj h1 h2 h3 hf hls hlen hA hI hS.hasType.1 hM hP hty
  exact ⟨pM.1.trans (.single (.projIota h1 h2 h3 hqs hms ha)),
    pM.2.trans (.defeqDF hty.symm (pc.2.trans (.defeqDF pc.1.symm hι)))⟩

end

section
variable {env : VEnv} {U : Nat} [ShapeEnv] {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- Values related at a structure-like type's constructor shape: both stuck, or their projections
are related along the constructor's declared telescope at the type's parameters, which is related
to itself. -/
theorem indVal_fields (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T)
    {ls : List VLevel} {Ps Ds : List VExpr} (hSH : StructHyps env U d T c ls Ps Ds)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hDl : Ds.length = c.fields.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    (hnidx : c.indices.length = T.indices.length) (hInS : Inert env s)
    {As I : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (WP : VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    {u : VLevel}
    (hS : env.IsDefEq U Γ₀ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    (hPA : ∀ j < c.fields.length, d.ProjAllowed c ls j)
    {Ih : IndHead} (hIn : Ih.name = s) (hIc : Ih.ctors = [c.name])
    (hIa : Ih.arities = [c.fields.length])
    {N₀ : Nat} {l' : List (WShape N₀)} {hf'} {as : List (WShape N₀)} {M N : VExpr}
    (hMN : env.IsDefEq U Γ₀ M N (.appN (.const s ls) (As ++ I)))
    (H : (LR (U := U) (Γ := Γ₀) henv hU (N₀+1)).DefEq M N (.appN (.const s ls) (As ++ I))
      (.ctor c.name l' hf') (.indTy true Ih as)) :
    (¬StructOK env U Γ₀ Ih (.appN (.const s ls) (As ++ I)) c.name ∧
      TNeRed env U Γ₀ M (.appN (.const s ls) (As ++ I)) ∧
      TNeRed env U Γ₀ N (.appN (.const s ls) (As ++ I))) ∨
    (l'.length = c.fields.length ∧
      (TNeRed env U Γ₀ M (.appN (.const s ls) (As ++ I)) →
        StructOK env U Γ₀ Ih (.appN (.const s ls) (As ++ I)) c.name) ∧
      TeleRel (LR (U := U) (Γ := Γ₀) henv hU N₀) c.fields.length
        ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
        ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
        (ctorTel Ih as 0) ∧
      FieldsRel (LR (U := U) (Γ := Γ₀) henv hU N₀)
        ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
        (ctorTel Ih as 0) (VExpr.projs s c.fields.length M) (VExpr.projs s c.fields.length N) l') := by
  have henv' := henvW.ordered
  have hSH' := hSH
  obtain ⟨h3, hls, hlen, -, -, -⟩ := hSH'
  have hF := henvW.projFacts h1 h2 h3
  have hte : ctorTeleAt ⟨d.uvars, c.type⟩ c.fields.length ls (As ++ I) =
      (VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As) := by
    rw [ctorTeleAt, ← piCount_instL c.type ls, hcty, piCount_foralls, ctorCod,
      piCount_appN_const, List.length_append, hDl, Nat.add_zero, Nat.add_sub_cancel,
      List.take_left' (by omega), VExpr.foralls_append, piInst_foralls _ _ _ (by omega)]
  have hi : Ih.ctors.idxOf? c.name = some 0 := by rw [hIc]; simp [List.idxOf?]
  have hk : Ih.arities[0]? = some c.fields.length := by rw [hIa]; rfl
  -- a projection reduces, typed, at its declared domain
  have conv : ∀ {X Y p q : VExpr}, env.IsDefEq U Γ₀ X Y (.appN (.const s ls) (As ++ I)) →
      ∀ j (hj : j < c.fields.length) D, Ds[j]? = some D →
      TRed env U Γ₀ p q (c.projType ls s j As Y) →
      TRed env U Γ₀ p q (D.subst ((Subst.id.consList As).consList (VExpr.projs s j X))) := by
    intro X Y p q hXY j hj D hD tr
    obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
    have e1 := VEnv.projType_congr henv' hΓ₀ h1 h2 h3 hF hls hlen hls
      (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hA hI hA hI WP hS hXY hf (hPA j hj)
    have e2 := projType_declDom henvW hΓ₀ h1 h2 hSH hPs hDcl hA hI WP hS hPA hXY.hasType.1 hD hf
    exact tr.defeqDF (e1.symm.trans e2)
  have red : ∀ {X Y : VExpr} {qs : List VExpr}, env.IsDefEq U Γ₀ X Y (.appN (.const s ls) (As ++ I)) →
      qs.length = c.fields.length →
      (∀ j (hj : j < c.fields.length) (q : VExpr), qs[j]? = some q →
        TRed env U Γ₀ (.proj s j Y) q (c.projType ls s j As Y)) →
      RedFields env U Γ₀
        ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
        (VExpr.projs s c.fields.length X) (VExpr.projs s c.fields.length Y) qs := by
    intro X Y qs hXY hql H
    refine RedFields.of_foralls _ Ds _ _ _ _ (by simp [VExpr.projs, hDl])
      (by simp [VExpr.projs, hDl]) (by omega) fun j h1' h2' h3' => ?_
    have hj : j < c.fields.length := by omega
    rw [VEnv.projs_take' _ _ (by simp [VExpr.projs] at h1'; omega)]
    simp only [VExpr.projs, List.getElem_map, List.getElem_range]
    exact conv hXY j hj _ (List.getElem?_eq_getElem h3')
      (H j hj _ (List.getElem?_eq_getElem h2'))
  simp only [LR, LRS, LRS.DefEq.ctor_indTy] at H
  unfold LRS.IndVal at H
  rcases H with H | hNA | ⟨hSO, hM1, hN1⟩
  · right
    split at H
    · rename_i hSO
      obtain ⟨-, hIT, i, k', ci, lsA, AsA, M', N', hi', hk', hci', hA', tM, -, tN, -, hfl, hFR, -⟩ :=
        H
      rw [hi] at hi'; cases hi'
      rw [hk] at hk'; cases hk'
      rw [hcC] at hci'; cases hci'
      rw [hIn] at hA' hFR
      obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hA')
      have hTel := hIT ls (As ++ I) ls (As ++ I) (by rw [hIn]; exact .rfl) (by rw [hIn]; exact .rfl)
        c.name 0 c.fields.length ⟨d.uvars, c.type⟩ hi hk hcC
      rw [hte] at hTel hFR
      refine ⟨hfl, fun _ => hSO, hTel, FieldsRel.of_red hU (by rw [hfl]; exact hTel) hFR ?_ ?_⟩
      · refine red hMN.hasType.1 (by simp [VExpr.projs]) fun j hj q hq => ?_
        obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
        simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
          Option.some.injEq] at hq
        subst hq
        exact TRed.proj h1 h2 h3 hf hls hlen hA hI hS.hasType.1 tM (hPA j hj)
          (VEnv.projType_congr henv' hΓ₀ h1 h2 h3 hF hls hlen hls
            (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hA hI hA hI WP hS tM.2 hf
            (hPA j hj))
      · refine red hMN (by simp [VExpr.projs]) fun j hj q hq => ?_
        obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
        simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
          Option.some.injEq] at hq
        subst hq
        exact TRed.proj h1 h2 h3 hf hls hlen hA hI hS.hasType.1 tN (hPA j hj)
          (VEnv.projType_congr henv' hΓ₀ h1 h2 h3 hF hls hlen hls
            (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hA hI hA hI WP hS tN.2 hf
            (hPA j hj))
    · obtain ⟨-, hInC, hIT, i, k', ci, lsA, AsA, ls₁, qs, ms, ls₁', qs', ns, hi', hk', hci', hA', tM,
        tN, hfl, hFR, hCP, hCP'⟩ := H
      rw [hi] at hi'; cases hi'
      rw [hk] at hk'; cases hk'
      rw [hcC] at hci'; cases hci'
      rw [hIn] at hA'
      obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hA')
      have hTel := hIT ls (As ++ I) ls (As ++ I) (by rw [hIn]; exact .rfl) (by rw [hIn]; exact .rfl)
        c.name 0 c.fields.length ⟨d.uvars, c.type⟩ hi hk hcC
      rw [hte] at hTel hFR
      have hTel' : TeleRel (LR (U := U) (Γ := Γ₀) henv hU N₀) l'.length
          ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
          ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
          (ctorTel Ih as 0) := by
        rw [hfl]; exact hTel
      have hmsl : ms.length = c.fields.length := by rw [hFR.length.1, hfl]
      have hnsl : ns.length = c.fields.length := by rw [hFR.length.2, hfl]
      have typ : ∀ {xs ys : List VExpr}, FieldsRel (LR (U := U) (Γ := Γ₀) henv hU N₀)
          ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
          (ctorTel Ih as 0) xs ys l' →
          ∀ j (hj : j < xs.length) D, Ds[j]? = some D →
            env.HasType U Γ₀ xs[j] (D.subst (Subst.dflt.consList (As ++ xs.take j))) := by
        intro xs ys HF j hj D hD
        have hjl : j < l'.length := by rw [← HF.length.1]; exact hj
        obtain ⟨_, _, m, _, _, _, hm, _, hd, _⟩ :=
          HF.get_foralls j l'[j] D (List.getElem?_eq_getElem hjl) hD
        rw [List.getElem?_eq_getElem hj] at hm; cases hm
        rw [← Subst.consList_append, subst_consList_id_dflt (hDcl j D hD)
          (by simp [hA, hPs]; omega)] at hd
        exact hd.hasType.1
      refine ⟨hfl, fun ⟨M₁, t1, w1, n1⟩ => ?_, hTel, FieldsRel.of_red hU hTel' hFR ?_ ?_⟩
      · cases StepS.determ hU t1.1 w1 tM.1 hInC.whnf
        exact (hInC.not_neutral n1).elim
      · refine red hMN.hasType.1 hmsl fun j hj q hq => ?_
        obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
        exact TRed.proj_ctorVal henvW hΓ₀ h1 h2 hSH hcC hcty hPs hnidx hA hI WP hS hIn hCP hmsl
          (typ hFR) tM hf hq (hPA j hj)
      · refine red hMN hnsl fun j hj q hq => ?_
        obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
        exact TRed.proj_ctorVal henvW hΓ₀ h1 h2 hSH hcC hcty hPs hnidx hA hI WP hS hIn hCP' hnsl
          (typ (hFR.symm hU hTel')) tN hf hq (hPA j hj)
  · exact (NeRed.not_inert hU (hIn ▸ hInS) hNA .rfl).elim
  · exact .inl ⟨hSO, hM1, hN1⟩

end

section
variable {env : VEnv} {U : Nat} [ShapeEnv] [AxInterp] {henv : env.Ordered} {hU : StepUniq env}
  {Γ₀ : List VExpr}

/-- The `k`th projections of values `M`, `N` related at a structure-like type's constructor shape,
given a value `X` related to `M` there: related at `X`'s projection type `Q`, at any shapes below
the field's shape whose type shape interprets a type `P` that the domain's shape interprets too. -/
theorem projPair_rel (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {s : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T)
    {ls : List VLevel} {Ps Ds : List VExpr} (hSH : StructHyps env U d T c ls Ps Ds)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) (ctorCod s c Ps.length Ds.length ls))
    (hPs : Ps.length = d.params.length) (hDl : Ds.length = c.fields.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j))
    (hnidx : c.indices.length = T.indices.length) (hInS : Inert env s)
    (hview : ∀ (j : Nat) (D : VExpr) (f : VField) (σ : VExpr.Subst), Ds[j]? = some D → c.fields[j]? = some f →
      VExpr.WF env U Γ₀ (D.subst σ) → StepS env U Γ₀ (D.subst σ) ((f.type.instL ls).subst σ))
    {As I : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (WP : VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    {u : VLevel}
    (hS : env.IsDefEq U Γ₀ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    (hPA : ∀ j < c.fields.length, d.ProjAllowed c ls j)
    {Ih : IndHead} (hIn : Ih.name = s) (hIc : Ih.ctors = [c.name])
    (hIa : Ih.arities = [c.fields.length])
    {N₀ : Nat} {l' : List (WShape N₀)} {hf'} {as : List (WShape N₀)} {X M N : VExpr}
    (hXM : env.IsDefEq U Γ₀ X M (.appN (.const s ls) (As ++ I)))
    (hMN : env.IsDefEq U Γ₀ M N (.appN (.const s ls) (As ++ I)))
    (HXM : (LR (U := U) (Γ := Γ₀) henv hU (N₀+1)).DefEq X M (.appN (.const s ls) (As ++ I))
      (.ctor c.name l' hf') (.indTy true Ih as))
    (HMN : (LR (U := U) (Γ := Γ₀) henv hU (N₀+1)).DefEq M N (.appN (.const s ls) (As ++ I))
      (.ctor c.name l' hf') (.indTy true Ih as))
    {k : Nat} {f : VField} (hf : c.fields[k]? = some f)
    {n : Nat} {m a : WShape n} (hma : m.HasType a)
    (hinfo : TyInfo env U Γ₀ henv hU n (c.projType ls s k As X) a)
    (hPQ : env.IsDefEq U Γ₀ (.proj s k M) (.proj s k N) (c.projType ls s k As X))
    {ρ : Valuation} {P : VExpr} (ha : LE_Interp env ρ a.T P)
    (hTy : ∀ {j} {b : WShape j}, LE_Interp env ρ b.T P → b.HasType .type →
      (LR (U := U) (Γ := Γ₀) henv hU j).TyDefEq (c.projType ls s k As X)
        (c.projType ls s k As X) b)
    (hdomP : ∀ x (b : WShape N₀) g, l'[k]? = some x →
      ((ctorTel Ih as 0).piApps (l'.take k)).piView = some (b, g) →
      m.T ≤ x.T ∧ LE_Interp env ρ b.T P) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.proj s k M) (.proj s k N)
      (c.projType ls s k As X) m a := by
  have henv' := henvW.ordered
  have hSH' := hSH
  obtain ⟨h3, hls, hlen, -, -, -⟩ := hSH'
  have hF := henvW.projFacts h1 h2 h3
  have hkf : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨D, hD⟩ : ∃ D, Ds[k]? = some D := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have tyQ : ∀ {Y}, env.IsDefEq U Γ₀ X Y (.appN (.const s ls) (As ++ I)) →
      env.IsDefEq U Γ₀ (c.projType ls s k As Y) (c.projType ls s k As X)
        (.sort (f.level.inst ls)) := fun h =>
    (VEnv.projType_congr henv' hΓ₀ h1 h2 h3 hF hls hlen hls
      (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hA hI hA hI WP hS h hf
      (hPA k hkf)).symm
  rcases indVal_fields henvW hΓ₀ h1 h2 hSH hcC hcty hPs hDl hDcl hnidx hInS hA hI WP hS hPA hIn hIc
    hIa hMN HMN with ⟨-, hM1, hN1⟩ | ⟨hl, hnot, TR, FMN⟩
  · have pM := (TNeRed.proj henv' hU hΓ₀ h1 h2 h3 hF hf hls hlen hA hI WP hS (hPA k hkf) hM1).tyEq
      (.base (tyQ hXM))
    have pN := (TNeRed.proj henv' hU hΓ₀ h1 h2 h3 hF hf hls hlen hA hI WP hS (hPA k hkf) hN1).tyEq
      (.base (tyQ (hXM.trans hMN)))
    exact reflect henv hU n hma.isType hma hinfo pM pN hPQ
  obtain FXM : FieldsRel (LR (U := U) (Γ := Γ₀) henv hU N₀)
      ((VExpr.foralls Ds (ctorCod s c Ps.length Ds.length ls)).subst (Subst.id.consList As))
      (ctorTel Ih as 0) (VExpr.projs s c.fields.length X) (VExpr.projs s c.fields.length M) l' := by
    rcases indVal_fields henvW hΓ₀ h1 h2 hSH hcC hcty hPs hDl hDcl hnidx hInS hA hI WP hS hPA hIn
      hIc hIa hXM HXM with ⟨hSO, -, hM1⟩ | ⟨-, -, -, FXM⟩
    · exact absurd (hnot hM1) hSO
    · exact FXM
  obtain ⟨x, hx⟩ : ∃ x, l'[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b, g, -, -, hv, -⟩ := FMN.get_foralls k x D hx hD
  have eD := projType_declDom henvW hΓ₀ h1 h2 hSH hPs hDcl hA hI WP hS hPA hXM.hasType.1 hD hf
  have eDM := projType_declDom henvW hΓ₀ h1 h2 hSH hPs hDcl hA hI WP hS hPA hXM.hasType.2 hD hf
  have hlen' : (As ++ VExpr.projs s k X).length = Ps.length + k := by
    simp [hA, hPs, VExpr.projs]
  have hQ : StepS env U Γ₀
      (D.subst ((Subst.id.consList As).consList ((VExpr.projs s c.fields.length X).take k)))
      (c.projType ls s k As X) := by
    rw [VEnv.projs_take' _ _ (by omega)]
    have hW : VExpr.WF env U Γ₀ (D.subst ((Subst.id.consList As).consList (VExpr.projs s k X))) :=
      ⟨_, eD.hasType.2⟩
    rw [← Subst.consList_append, subst_consList_id_dflt (hDcl k D hD) hlen'] at hW ⊢
    have := hview k D f _ hD hf hW
    simpa [VConstructor.projType, hf] using this
  have hE : TyEq env U Γ₀
      (D.subst ((Subst.id.consList As).consList ((VExpr.projs s c.fields.length M).take k)))
      (c.projType ls s k As X) := by
    rw [VEnv.projs_take' _ _ (by omega)]
    exact .base (eDM.symm.trans (tyQ hXM))
  obtain ⟨m', n', hm', hn', hxb, -, hrel⟩ :=
    FieldsRel.field_conv hU (by omega) (by rwa [hl]) FXM FMN hx hD hv hQ hE
  simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hkf, Option.map_some,
    Option.some.injEq] at hm' hn'
  subst hm' hn'
  obtain ⟨hmx, hbP⟩ := hdomP x b g hx hv
  exact LR.retype hM hrel hxb hmx hma hbP ha hTy

end

section
variable {env : VEnv} [ShapeEnv] [AxInterp]

/-- An interpretation of a projection: `bot`, or below a field of a constructor shape
interpreting the projected term. -/
theorem LE_Interp.proj_inv' {ρ : Valuation} {m : TShape} {s : Name} {k : Nat} {e : VExpr}
    {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T) (hcs : T.ctors = [c])
    (H : LE_Interp env ρ m (.proj s k e)) :
    m ≤ TShape.bot ∨ ∃ n0, ∃ fs : List (WShape n0), ∃ x,
      LE_Interp env ρ (WShape.ctor' c.name fs).T e ∧ fs[k]? = some x ∧ m ≤ x.T := by
  cases H with
  | bot => exact .inl TShape.bot_eqv.1
  | proj hs' hT' hcs' hce hx hmx =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs'))
    obtain rfl : T = _ := Option.some.inj (hT.symm.trans hT')
    obtain rfl : c = _ := (List.cons.inj (hcs.symm.trans hcs')).1
    exact .inr ⟨_, _, _, hce, hx, hmx⟩

end

/-- `projDF` at the types a block adds. -/
theorem indProjDFNew : IndProjDFNew := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d0 hX hXD hW hEI hR hD hext hdom IH IHall
  letI := env.shapeEnv; letI := X
  intro Γ s d t T c k f ls As I As' I' e e' u hΓ h1 h2 h3 h4 hls hlen hA hIl hA' hIl' hu hfl hP
    HA He HP ihA ihe ihP hSA hSP hSe hSpr
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  have henv := henvW.ordered
  have hle : E' ≤ env := hext.le
  obtain ⟨hE's, hEs⟩ : E'.inducts s = some (d, t) ∧ E.inducts s = none := by
    simp only [newBlockEnv] at h1
    split at h1
    · exact ⟨h1, ‹_›⟩
    · cases h1
  obtain hold | ⟨rfl, T', hT', hname⟩ := induct_inducts_cases hD hE's
  · rw [hEs] at hold; cases hold
  rw [h2] at hT'; cases hT'
  subst hname
  have hs : env.inducts T.name = some (d, t) := hle.inducts hE's
  obtain ⟨hd, envT, envC, envR, hT1, hT2, hT3, hTE', -, -, -, hcCall⟩ := induct_facts hD hle
  have hTle : envT ≤ env := hTE'.trans hle
  have hEW : E.WF := ⟨_, hW⟩
  have hdomE : ∀ c, X.dom c → E.constants c = none :=
    fun c h => VEnv.constants_none_of_le hD.le (hdom c h)
  obtain ⟨dsT, hWT⟩ : envT.WF := VEnv.WF.addConstList hEW (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) hT1
  have hTo : envT.Ordered := VEnv.WF.ordered ⟨_, hWT⟩
  have hIT := (hR envT envC envR hT1 hT2 hT3).1
  have hXT : SoundHyps envT env := by
    have hndX : NoDom envT := fun hdf e hx => by
      rw [VEnv.addConstList_defeqs' hT1] at hdf
      exact VEnv.WF.rule_head hEW hdf e (hdomE _ hx)
    exact soundHyps_of hMX (quotRuleSound hMX henvW) (henvW.blockSound hMX) hWT hTle hndX
      (NoDomI.mono (VEnv.WF.noDomI hEW hdomE) fun h => (VEnv.addConstList_inducts hT1) ▸ h)
  have hTm : T ∈ d.types := List.mem_of_getElem? h2
  have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hTm
  have hcm : c ∈ T.ctors := by simp [h3]
  have hcC := hcCall T hTm c hcm
  have hnone : T.nested = none := (hd.types T hTm).2
  have hcW := (hd.ctors envT hT1 T hTA).2 c hcm
  obtain ⟨ps, Ds₀, hshape, hPD, hFW, -, -⟩ := hcW.shape
  have hpl : ps.length = d.params.length := hPD.length_eq
  have hDl : Ds₀.length = c.fields.length := hFW.length
  have hcty : c.type.instL ls = .foralls (ps.map (·.instL ls) ++ Ds₀.map (·.instL ls))
      (ctorCod T.name c (ps.map (·.instL ls)).length (Ds₀.map (·.instL ls)).length ls) := by
    rw [hshape, VEnv.foralls_instL', List.map_append, VInductiveType.typeApp_of_none hnone]
    simp only [ctorCod, instL_appN, VExpr.instL, VLevel.params_inst hlen, List.map_append,
      instL_bvars, List.length_map, hpl, hDl]
  generalize hPs : ps.map (·.instL ls) = Ps at hcty
  generalize hDs' : Ds₀.map (·.instL ls) = Ds at hcty
  have hPl : Ps.length = d.params.length := by rw [← hPs, List.length_map, hpl]
  have hDl' : Ds.length = c.fields.length := by rw [← hDs', List.length_map, hDl]
  have hty : envT.IsType U [] (c.type.instL ls) := by simpa using hcW.type.instL hls
  rw [hcty] at hty
  obtain ⟨hTe, -⟩ := VEnv.IsType.foralls_inv hTo hty
  have onT : OnCtx (Ps ++ Ds).reverse (envT.IsType U) := by
    simpa using hTe.onCtx (Γ := []) trivial
  have hcl := VEnv.IsTele.closedN hTo hTe trivial
  have hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j) := by
    intro j D hD
    have := hcl (Ps.length + j) D (by rw [List.getElem?_append_right (by omega)]; simpa using hD)
    simpa using this
  have hP₀ : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le hT1)
  have onP : OnCtx d.params.reverse (envT.IsType d.uvars) := by
    simpa using hP₀.onCtx (Γ := []) trivial
  have hPctx : env.IsDefEqCtx U [] Ps.reverse (d.params.map (·.instL ls)).reverse := by
    have hTD := VEnv.TeleDefEq.instL' hls hPD
    simp only [List.map_nil] at hTD
    rw [← hPs]
    have := VEnv.TeleDefEq.defeqCtx_of_inj hTo hIT hTD .zero trivial (by simpa using hP₀.instL hls)
    simpa using VEnv.IsDefEqCtx.mono' hTle this
  have hSH : StructHyps env U d T c ls Ps Ds :=
    ⟨h3, hls, hlen, onT.mono fun h => h.mono hTle, hPctx, Ds₀, hDs'.symm, hDl,
      fun k D f hD hf => ((VInductDecl.FieldsWF.atSort hIT hFW onP k D f hD hf).1.mono hTle),
      hFW.viewsTele.mono hTle⟩
  have hnidx : c.indices.length = T.indices.length := hcW.indices.1
  have hInS : Inert env T.name := Inert.of_role hMX.roles
    (fun hdf e => henvW.rule_lhs_params hdf e) (.indTy hs h2) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hnd : ¬X.dom T.name := fun hx => by
    have h := hdom _ hx
    rw [hTE'.constants (VEnv.addConstList_constants_of_mem hT1
      (List.mem_map_of_mem (f := fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))) hTm))] at h
    cases h
  have hview : ∀ (j : Nat) (D : VExpr) (f : VField) (σ : VExpr.Subst), Ds[j]? = some D →
      c.fields[j]? = some f → VExpr.WF env U Γ₀ (D.subst σ) →
      StepS env U Γ₀ (D.subst σ) ((f.type.instL ls).subst σ) := by
    intro j D f σ hD hf hWF
    rw [← hDs', List.getElem?_map] at hD
    obtain ⟨D₀, hD₀, rfl⟩ := Option.map_eq_some_iff.1 hD
    exact StepS.declDom_view henv hΓ₀ hcW hTle hshape hpl hD₀ hf ls σ hWF
  -- the projection's interpretations
  intro ρ n m a hm ha hma
  refine LR.Adequate.fits fun hW' => ?_
  have hbot : m.T ≤ TShape.bot → LR.Adequate (U := U) henvW.ordered henvW.stepUniq Γ₀ Γ ρ
      (.proj T.name k e) (.proj T.name k e') (c.projType ls T.name k As e) m a := fun hb => by
    cases show m = .bot from TShape.le_bot.1 hb
    exact .bot hma.isType
  by_cases hnz : (d.level.inst ls).IsNeverZero
  case neg =>
    have hf0 := (hP hnz).1 f h4
    exact hbot (hSpr.left.proof_le_bot' hSP.left (by rw [levelRel_congr hf0, levelRel_zero]) hW'
      hm)
  have hPA : ∀ j < c.fields.length, d.ProjAllowed c ls j := fun _ _ h => absurd hnz h
  rcases hm.proj_inv' hs h2 h3 with hb | ⟨n0, fs, x0, hce, hx0, hmx⟩
  · exact hbot hb
  by_cases hne : IsStruct c.name → WShape.ListNonZero fs
  case neg =>
    have hz : x0.1 ≤ .bot := Classical.byContradiction fun h =>
      hne fun _ => ⟨x0, List.mem_of_getElem? hx0, h⟩
    exact hbot (hmx.trans ((WShape.LE.T (b := .bot) hz).trans TShape.bot_eqv.1))
  -- the projected value's interpretation, at a constructor shape and the type's shape
  obtain ⟨n', w, aI, -, le_w, hw, haI, hwa⟩ := (hSe.left.sound hW' hce).out
  obtain ⟨N₀, l', hf', Ih, as, hIn, hfs, hw', haI', hwa', Htr⟩ :=
    proj_shape (U := U) (henv := henvW.ordered) (hU := henvW.stepUniq) hMX hnd hs h2
      (args := As ++ I) (by simp [hA, hIl]) hne le_w hwa haI hw
  have hIh := (blockTy_inv hMX hnd hs h2 (args := As ++ I) (by simp [hA, hIl]) haI').1
  have hIc : Ih.ctors = [c.name] := by rw [hIh, h3]; rfl
  have hIa : Ih.arities = [c.fields.length] := by rw [hIh, h3]; rfl
  have ad := ihe hw haI hwa
  have hF := henvW.projFacts hs h2 h3
  have hpar : OnCtx (d.params.map (·.instL ls)).reverse (env.IsType U) := by
    simpa using (hF.params.instL hls).onCtx (Γ := []) trivial
  have key : ∀ {σ : VExpr.Subst} {M' N' : VExpr},
      LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ₀ σ σ Γ ρ →
      env.IsDefEq U Γ₀ (e.subst σ) M' ((VExpr.appN (.const T.name ls) (As ++ I)).subst σ) →
      env.IsDefEq U Γ₀ M' N' ((VExpr.appN (.const T.name ls) (As ++ I)).subst σ) →
      (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq n').DefEq (e.subst σ) M'
        ((VExpr.appN (.const T.name ls) (As ++ I)).subst σ) w aI →
      (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq n').DefEq M' N'
        ((VExpr.appN (.const T.name ls) (As ++ I)).subst σ) w aI →
      env.IsDefEq U Γ₀ (.proj T.name k M') (.proj T.name k N')
        ((c.projType ls T.name k As e).subst σ) →
      (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq n).DefEq (.proj T.name k M')
        (.proj T.name k N') ((c.projType ls T.name k As e).subst σ) m a := by
    intro σ M' N' Wσ hXM hMN HXM HMN hPQ
    have eA : (VExpr.appN (.const T.name ls) (As ++ I)).subst σ =
        (VExpr.const T.name ls).appN (As.map (·.subst σ) ++ I.map (·.subst σ)) := by
      simp [subst_appN, VExpr.subst, List.map_append]
    have hinfo := AdeqStmt.tyInfo ihP hSP.left hfl Wσ ha hma.isType
    have hTy : ∀ {j} {b : WShape j}, LE_Interp env ρ b.T (c.projType ls T.name k As e) →
        b.HasType .type → (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq j).TyDefEq
          (c.projType ls T.name k (As.map (·.subst σ)) (e.subst σ))
          (c.projType ls T.name k (As.map (·.subst σ)) (e.subst σ)) b := fun hb ht => by
      have := (AdeqStmt.tyInfo ihP hSP.left hfl Wσ hb ht).1
      rwa [VConstructor.projType_subst] at this
    rw [VConstructor.projType_subst] at hPQ hinfo ⊢
    -- the type's parameters, related to themselves along the block's
    obtain ⟨_, aI'', s'', le_n, le_a, haI'', hs'', haIs⟩ := (hSA.left.sound hW' haI').out
    have tA := LR.toValTy le_n le_a hwa'.isType hs'' haIs ((ihA haI'' hs'' haIs).1 Wσ).1
    have hS : env.IsDefEq U Γ₀ ((VExpr.const T.name ls).appN (As.map (·.subst σ) ++ I.map (·.subst σ)))
        ((VExpr.const T.name ls).appN (As.map (·.subst σ) ++ I.map (·.subst σ))) (.sort u) := by
      have := HA.defeq.hasType.1.subst henv (Wσ.toSubstEq hΓ₀) hΓ₀
      rw [eA] at this; exact this
    rw [eA] at tA hXM hMN HXM HMN
    simp only [LR, LRS, LRS.TyDefEq.indTy_iff] at tA
    obtain ⟨⟨-, ls1, ls2, As1, As2, r1, -, -, -, -, hRR⟩, -⟩ := tA.resolve_right fun ⟨hN, _⟩ =>
      NeRed.not_inert henvW.stepUniq (hIn ▸ hInS) hN .rfl
    rw [hIn] at r1 hRR
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf r1)
    simp only [typeTele_block hs h2] at hRR
    have R1 := hRR.left.take d.params.length (by simp [hA, hIl]) (by simp [hA, hIl])
    rw [List.take_left' (by simp [hA]), ← List.map_take, List.take_left' rfl] at R1
    have WP := R1.substEq hpar
    exact projPair_rel hMX henvW hΓ₀ hs h2 hSH hcC hcty hPl hDl' hDcl hnidx hInS hview
      (by simp [hA]) (by simp [hIl]) WP hS hPA hIn hIc hIa hXM hMN (Htr HXM) (Htr HMN) h4 hma hinfo
      hPQ ha hTy fun x b g hx hv => ⟨hmx.trans (hfs.getElem?' hx0 hx),
        projDom_interp hMX hEW hnd hd hT1 hTle hXT hs h2 rfl h3 h4 hls hA hIl hSA.left hW' hw' haI'
          hwa' hv⟩
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · have H1 := (ad.1 W).1
    exact key W.left (He.defeq.hasType.1.subst henv (W.left.toSubstEq hΓ₀) hΓ₀)
      (He.defeq.hasType.1.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)) ((LR _ _ _).left H1) H1
      (hSpr.defeq.hasType.1.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀))
  · exact key W.left (He.defeq.subst henv (W.left.toSubstEq hΓ₀) hΓ₀)
      (He.defeq.hasType.2.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)) (ad.2 W.left) (ad.1 W).2
      (hSpr.defeq.hasType.2.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀))
  · have H := ad.2 W
    exact key W (He.defeq.hasType.1.subst henv (W.toSubstEq hΓ₀) hΓ₀)
      (He.defeq.subst henv (W.toSubstEq hΓ₀) hΓ₀) ((LR _ _ _).left H) H
      (hSpr.defeq.subst henv (W.toSubstEq hΓ₀) hΓ₀)

/-- `projEta` at the types a block adds. -/
theorem indProjEtaNew : IndProjEtaNew := by
  intro env henvW U Γ₀ hΓ₀ X ds E E' d0 hX hXD hW hEI hR hD hext hdom IH IHall
  letI := env.shapeEnv; letI := X
  intro Γ s d t T c ls As e u hΓ h1 h2 h3 hidx hrec hls hlen hA hPA hu HA He Hη ihA ihe ihη hSη
  have hMX : ModelEnv env := henvW.modelEnv hX hXD
  have henv := henvW.ordered
  have hU := henvW.stepUniq
  have hle : E' ≤ env := hext.le
  obtain ⟨hE's, hEs⟩ : E'.inducts s = some (d, t) ∧ E.inducts s = none := by
    simp only [newBlockEnv] at h1
    split at h1
    · exact ⟨h1, ‹_›⟩
    · cases h1
  obtain hold | ⟨rfl, T', hT', hname⟩ := induct_inducts_cases hD hE's
  · rw [hEs] at hold; cases hold
  rw [h2] at hT'; cases hT'
  subst hname
  have hs : env.inducts T.name = some (d, t) := hle.inducts hE's
  obtain ⟨hd, envT, envC, envR, hT1, hT2, hT3, hTE', -, -, -, hcCall⟩ := induct_facts hD hle
  have hTle : envT ≤ env := hTE'.trans hle
  have hEW : E.WF := ⟨_, hW⟩
  obtain ⟨dsT, hWT⟩ : envT.WF := VEnv.WF.addConstList hEW (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) hT1
  have hTo : envT.Ordered := VEnv.WF.ordered ⟨_, hWT⟩
  have hIT := (hR envT envC envR hT1 hT2 hT3).1
  have hTm : T ∈ d.types := List.mem_of_getElem? h2
  have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hTm
  have hcm : c ∈ T.ctors := by simp [h3]
  have hcC := hcCall T hTm c hcm
  have hnone : T.nested = none := (hd.types T hTm).2
  have hcW := (hd.ctors envT hT1 T hTA).2 c hcm
  obtain ⟨ps, Ds₀, hshape, hPD, hFW, -, -⟩ := hcW.shape
  have hpl : ps.length = d.params.length := hPD.length_eq
  have hDl : Ds₀.length = c.fields.length := hFW.length
  have hcty : c.type.instL ls = .foralls (ps.map (·.instL ls) ++ Ds₀.map (·.instL ls))
      (ctorCod T.name c (ps.map (·.instL ls)).length (Ds₀.map (·.instL ls)).length ls) := by
    rw [hshape, VEnv.foralls_instL', List.map_append, VInductiveType.typeApp_of_none hnone]
    simp only [ctorCod, instL_appN, VExpr.instL, VLevel.params_inst hlen, List.map_append,
      instL_bvars, List.length_map, hpl, hDl]
  generalize hPs : ps.map (·.instL ls) = Ps at hcty
  generalize hDs' : Ds₀.map (·.instL ls) = Ds at hcty
  have hPl : Ps.length = d.params.length := by rw [← hPs, List.length_map, hpl]
  have hDl' : Ds.length = c.fields.length := by rw [← hDs', List.length_map, hDl]
  have hty : envT.IsType U [] (c.type.instL ls) := by simpa using hcW.type.instL hls
  rw [hcty] at hty
  obtain ⟨hTe, -⟩ := VEnv.IsType.foralls_inv hTo hty
  have onT : OnCtx (Ps ++ Ds).reverse (envT.IsType U) := by
    simpa using hTe.onCtx (Γ := []) trivial
  have hcl := VEnv.IsTele.closedN hTo hTe trivial
  have hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (Ps.length + j) := by
    intro j D hD
    have := hcl (Ps.length + j) D (by rw [List.getElem?_append_right (by omega)]; simpa using hD)
    simpa using this
  have hP₀ : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le hT1)
  have onP : OnCtx d.params.reverse (envT.IsType d.uvars) := by
    simpa using hP₀.onCtx (Γ := []) trivial
  have hPctx : env.IsDefEqCtx U [] Ps.reverse (d.params.map (·.instL ls)).reverse := by
    have hTD := VEnv.TeleDefEq.instL' hls hPD
    simp only [List.map_nil] at hTD
    rw [← hPs]
    have := VEnv.TeleDefEq.defeqCtx_of_inj hTo hIT hTD .zero trivial (by simpa using hP₀.instL hls)
    simpa using VEnv.IsDefEqCtx.mono' hTle this
  have hSH : StructHyps env U d T c ls Ps Ds :=
    ⟨h3, hls, hlen, onT.mono fun h => h.mono hTle, hPctx, Ds₀, hDs'.symm, hDl,
      fun k D f hD hf => ((VInductDecl.FieldsWF.atSort hIT hFW onP k D f hD hf).1.mono hTle),
      hFW.viewsTele.mono hTle⟩
  have hInS : Inert env T.name := Inert.of_role hMX.roles
    (fun hdf e => henvW.rule_lhs_params hdf e) (.indTy hs h2) (fun _ h => nomatch h)
    (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hInC : Inert env c.name := Inert.of_role hMX.roles
    (fun hdf e => henvW.rule_lhs_params hdf e) (.ctor hs h2 hcm rfl)
    (fun _ h => nomatch h) (fun _ _ h => nomatch h) (fun h => nomatch h)
  have hIS : IsStruct c.name = true := hMX.structOf _ ⟨_, d, t, T, c, hs, h2, h3, hidx, hrec, rfl⟩
  have hF := henvW.projFacts hs h2 h3
  have hpar : OnCtx (d.params.map (·.instL ls)).reverse (env.IsType U) := by
    simpa using (hF.params.instL hls).onCtx (Γ := []) trivial
  have hnd : ¬X.dom T.name := fun hx => by
    have h := hdom _ hx
    rw [hTE'.constants (VEnv.addConstList_constants_of_mem hT1
      (List.mem_map_of_mem (f := fun T => (T.name, (⟨d.uvars, T.type⟩ : VConstant))) hTm))] at h
    cases h
  have hI0 : ([] : List VExpr).length = T.indices.length := by simp [hidx]
  intro ρ n m a hm ha hma
  refine LR.Adequate.fits fun hW' => ?_
  have hm' := (hSη.sound hW').1 hm
  have ade := ihe hm ha hma
  have adη := ihη hm' ha hma
  refine ⟨fun σ σ' W => ⟨(ade.1 W).1, (adη.1 W).1⟩, fun σ W => ?_⟩
  have H0 := ade.2 W
  have eA : (VExpr.appN (.const T.name ls) As).subst σ =
      (VExpr.const T.name ls).appN (As.map (·.subst σ)) := by simp [subst_appN, VExpr.subst]
  have eη : (VExpr.appN (.const c.name ls) (As ++ VExpr.projs T.name c.fields.length e)).subst σ =
      (VExpr.const c.name ls).appN (As.map (·.subst σ) ++
        VExpr.projs T.name c.fields.length (e.subst σ)) := by
    simp [subst_appN, VExpr.subst, List.map_append, VExpr.projs_subst]
  have hx := hSη.defeq.subst henv (W.toSubstEq hΓ₀) hΓ₀
  have hS := HA.defeq.hasType.1.subst henv (W.toSubstEq hΓ₀) hΓ₀
  rw [eA, eη] at hx ⊢
  rw [eA] at H0 hS
  generalize hAs : As.map (·.subst σ) = Asσ at hx hS H0 ⊢
  have hAσ : Asσ.length = d.params.length := by rw [← hAs, List.length_map, hA]
  generalize e.subst σ = eσ at hx H0 ⊢
  -- the value's shapes
  have hbot : m.T ≤ TShape.bot → (LR (U := U) (Γ := Γ₀) henvW.ordered henvW.stepUniq n).DefEq eσ
      ((VExpr.const c.name ls).appN (Asσ ++ VExpr.projs T.name c.fields.length eσ))
      ((VExpr.const T.name ls).appN Asσ) m a := fun hb => by
    cases show m = .bot from TShape.le_bot.1 hb
    exact (LR _ _ _).bot hma.isType
  rcases typed_indTy_inv hMX hnd hs h2 (args := As) (by simp [hA, hidx]) (WShape.HasType.T hma) ha
    with hb | ⟨N, c', hc', l, -, -, hle1, -⟩
  · exact hbot hb
  rw [h3, List.mem_singleton] at hc'; subst c'
  cases n with
  | zero =>
    obtain ⟨mv, wf⟩ := m
    cases mv with
    | bot => exact (LR _ _ _).bot hma.isType
    | sort r => exact (TShape.sort_not_le_ctor' (r := r) (n := 0) hle1).elim
  | succ N₀ =>
  rcases WShape.le_ctor'_cases hle1 with rfl | ⟨fs, hf, rfl, -⟩
  · exact (LR _ _ _).bot hma.isType
  obtain ⟨I, as, rfl⟩ := WShape.HasType.ctor_inv hma
  have hIn : I.name = T.name := by
    rw [(blockTy_inv hMX hnd hs h2 (args := As) (by simp [hA, hidx]) ha).1]
  have hSO : StructOK env U Γ₀ I ((VExpr.const T.name ls).appN Asσ) c.name := by
    refine ⟨hIS, fun lsA AsA r w d' t' T' cv hd' hT' hcv hcn k hk => ?_⟩
    rw [hIn] at r hd'
    obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf r)
    rw [hs] at hd'; cases hd'
    rw [h2] at hT'; cases hT'
    rw [h3, List.mem_singleton] at hcv; subst hcv
    exact hPA k hk
  simp only [LR, LRS, LRS.DefEq.ctor_indTy] at H0 ⊢
  unfold LRS.IndVal at H0 ⊢
  rw [if_pos hSO] at H0 ⊢
  replace H0 := H0.resolve_right fun h => h.elim
    (fun hNA => NeRed.not_inert henvW.stepUniq (hIn ▸ hInS) hNA .rfl) fun ⟨hn, _⟩ => hn hSO
  have hIeq := (blockTy_inv hMX hnd hs h2 (args := As) (by simp [hA, hidx]) ha).1
  have hi0 : I.ctors.idxOf? c.name = some 0 := by rw [hIeq, h3]; simp [List.idxOf?]
  have hk0 : I.arities[0]? = some c.fields.length := by rw [hIeq, h3]; rfl
  obtain ⟨hInS', hIT, i, k, ci, lsA, AsA, M', N', hi, hk, hci, hA', tM, wM, -, -, hfl, hFR, hTA⟩ :=
    H0
  rw [hi0] at hi; cases hi
  rw [hk0] at hk; cases hk
  rw [hcC] at hci; cases hci
  rw [hIn] at hA'
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInS.whnf hA')
  have hTel := hIT ls Asσ ls Asσ (by rw [hIn]; exact .rfl) (by rw [hIn]; exact .rfl) c.name 0
    c.fields.length ⟨d.uvars, c.type⟩ hi0 hk0 hcC
  have hte : ctorTeleAt ⟨d.uvars, c.type⟩ c.fields.length ls Asσ =
      (VExpr.foralls Ds (ctorCod T.name c Ps.length Ds.length ls)).subst (Subst.id.consList Asσ) := by
    rw [ctorTeleAt, ← piCount_instL c.type ls, hcty, piCount_foralls, ctorCod,
      piCount_appN_const, List.length_append, hDl', Nat.add_zero, Nat.add_sub_cancel,
      List.take_of_length_le (by omega), VExpr.foralls_append, piInst_foralls _ _ _ (by omega)]
  rw [hte] at hTel hFR
  rw [hIn] at hFR
  -- the parameters, along the block's
  have WP : VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList Asσ) (Subst.dflt.consList Asσ)
      (d.params.map (·.instL ls)).reverse := by
    have h := hTA.2
    rw [hIn, typeTele_block hs h2, hidx, List.append_nil] at h
    exact h.substEq hpar
  have hS' : env.IsDefEq U Γ₀ ((VExpr.const T.name ls).appN (Asσ ++ []))
      ((VExpr.const T.name ls).appN (Asσ ++ [])) (.sort u) := by rw [List.append_nil]; exact hS
  have tyX : ∀ {X Y : VExpr}, env.IsDefEq U Γ₀ X Y ((VExpr.const T.name ls).appN Asσ) →
      env.IsDefEq U Γ₀ X Y ((VExpr.const T.name ls).appN (Asσ ++ [])) := fun h => by
    rw [List.append_nil]; exact h
  have conv : ∀ {X Y p q : VExpr}, env.IsDefEq U Γ₀ X Y ((VExpr.const T.name ls).appN Asσ) →
      ∀ j (hj : j < c.fields.length) D, Ds[j]? = some D →
      TRed env U Γ₀ p q (c.projType ls T.name j Asσ Y) →
      TRed env U Γ₀ p q (D.subst ((Subst.id.consList Asσ).consList (VExpr.projs T.name j X))) := by
    intro X Y p q hXY j hj D hD tr
    obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
    have e1 := VEnv.projType_congr henv hΓ₀ hs h2 h3 hF hls hlen hls
      (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) hAσ hI0 hAσ hI0 WP hS' (tyX hXY) hf
      (hPA j hj)
    have e2 := projType_declDom henvW hΓ₀ hs h2 hSH hPl hDcl hAσ hI0 WP hS' hPA
      (tyX hXY).hasType.1 hD hf
    exact tr.defeqDF (e1.symm.trans e2)
  have red : ∀ {X Y : VExpr} {qs : List VExpr},
      env.IsDefEq U Γ₀ X Y ((VExpr.const T.name ls).appN Asσ) → qs.length = c.fields.length →
      (∀ j (hj : j < c.fields.length) (q : VExpr), qs[j]? = some q →
        TRed env U Γ₀ (.proj T.name j Y) q (c.projType ls T.name j Asσ Y)) →
      RedFields env U Γ₀
        ((VExpr.foralls Ds (ctorCod T.name c Ps.length Ds.length ls)).subst (Subst.id.consList Asσ))
        (VExpr.projs T.name c.fields.length X) (VExpr.projs T.name c.fields.length Y) qs := by
    intro X Y qs hXY hql H
    refine RedFields.of_foralls _ Ds _ _ _ _ (by simp [VExpr.projs, hDl'])
      (by simp [VExpr.projs, hDl']) (by omega) fun j h1' h2' h3' => ?_
    have hj : j < c.fields.length := by omega
    rw [VEnv.projs_take' _ _ (by simp [VExpr.projs] at h1'; omega)]
    simp only [VExpr.projs, List.getElem_map, List.getElem_range]
    exact conv hXY j hj _ (List.getElem?_eq_getElem h3')
      (H j hj _ (List.getElem?_eq_getElem h2'))
  have hM'A := tM.2.hasType.2
  refine .inl ⟨hInS', hIT, 0, c.fields.length, _, ls, Asσ, M', _, hi0, hk0, hcC, by rw [hIn]; exact .rfl,
    tM, wM, TRed.refl hx.hasType.2, hInC.whnf, hfl, ?_, hTA⟩
  rw [hIn, hte]
  refine FieldsRel.of_red henvW.stepUniq (by rw [hfl]; exact hTel) hFR.left
    (red hM'A (by simp [VExpr.projs]) fun j hj q hq => ?_)
    (red (tM.2.symm.trans hx) (by simp [VExpr.projs]) fun j hj q hq => ?_)
  · obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
    simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.some.injEq] at hq
    subst hq
    exact TRed.refl (VEnv.projCongr henv hΓ₀ hs h2 h3 hF hls hlen hAσ hI0 hAσ hI0 WP hS'
      (tyX hM'A) j f hf (hPA j hj)).2.hasType.1
  · obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hj⟩
    simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.some.injEq] at hq
    subst hq
    refine ⟨(StepS.single (.projIota hs h2 h3 hAσ (by simp [VExpr.projs]) ?_)).trans
      (StepS.proj tM.1), (VEnv.projCongr henv hΓ₀ hs h2 h3 hF hls hlen hAσ hI0 hAσ hI0 WP hS'
        (tyX (hx.symm.trans tM.2)) j f hf (hPA j hj)).2⟩
    simp [VExpr.projs, List.getElem?_range hj]

/-- A block's projection cases. -/
theorem indProjCase : IndProjCase := IndProjCase.of indProjDFNew indProjEtaNew

end LogRel
end Lean4Lean

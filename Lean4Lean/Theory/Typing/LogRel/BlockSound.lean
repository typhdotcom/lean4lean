import Lean4Lean.Theory.Typing.LogRel.SoundWF

/-!
# Soundness of a block's iota rules in the model

Each iota rule of a block is sound in the model of an environment the block's declaration is part
of, given that the model is sound for the environment the block was declared in.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat}

omit [ShapeEnv] in
theorem mem_iotaRules {d : VInductDecl} {df : VDefEq} (h : df ∈ d.iotaRules) :
    ∃ q j c, d.allCtors[q]? = some (j, c) ∧
      df = d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c := by
  simp only [VInductDecl.iotaRules, List.mem_map] at h
  obtain ⟨⟨⟨j, c⟩, q⟩, hm, rfl⟩ := h
  exact ⟨q, j, c, List.mk_mem_zipIdx_iff_getElem?.1 hm, rfl⟩

omit [ShapeEnv] in
theorem motiveType_liftN (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (j : Nat)
    (Tj : VInductiveType) (n : Nat) : ∃ Ps, (d.motiveType lsB v j Tj).liftN n =
      .foralls Ps (.sort v) ∧ Ps.length = Tj.indices.length + 1 := by
  unfold VInductDecl.motiveType
  rw [VExpr.liftN_foralls]
  exact ⟨_ ++ [_], by rw [VExpr.foralls_append]; rfl, by simp⟩

omit [ShapeEnv] in
theorem iotaBinders_motive (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (c : VConstructor)
    {j : Nat} {Tj : VInductiveType} (hj : d.allTypes[j]? = some Tj)
    (h : d.params.length + j < (d.iotaBinders lsB v c).length) :
    (d.iotaBinders lsB v c)[d.params.length + j] = d.motiveType lsB v j Tj := by
  have hjl := (List.getElem?_eq_some_iff.1 hj).1
  simp only [VInductDecl.iotaBinders, VInductDecl.recBinders]
  rw [List.getElem_append_left (by simp [VInductDecl.length_motiveTypes]; omega),
    List.getElem_append_left (by simp [VInductDecl.length_motiveTypes]; omega),
    List.getElem_append_right (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left, VInductDecl.motiveTypes, List.getElem_map,
    List.getElem_zipIdx, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.1 hj).2]

/-- The backward direction of an iota rule whose right-hand side is a proof (its motive's sort is
read as `Prop`): an interpretation of the right body is `bot`, which interprets anything. -/
theorem iota_bwd_small (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
    (hO : E.Ordered) {d : VInductDecl} {j : Nat} {Tj : VInductiveType} {c : VConstructor}
    (hj : d.allTypes[j]? = some Tj) (hcidx : c.indices.length = Tj.indices.length)
    {lsB : List VLevel} {v : VLevel} (hv : levelRel v = false)
    (hT : E.IsTele U [] (d.iotaBinders lsB v c))
    (hCT : E.IsType U (d.iotaBinders lsB v c).reverse (iotaCT d lsB j c))
    {R B' : VExpr} (hR : SoundTy env (d.iotaBinders lsB v c).reverse R B')
    (hBC : SoundEq env (d.iotaBinders lsB v c).reverse B' (iotaCT d lsB j c))
    {Γ₀ : List VExpr} {σ : Valuation}
    (W : Valuation.Fits env Γ₀ (d.iotaBinders lsB v c).reverse σ) {y : TShape}
    (h : LE_Interp env σ y R) (M : VExpr) : LE_Interp env σ y M := by
  have hjl := (List.getElem?_eq_some_iff.1 hj).1
  have hBl := length_iotaBinders d lsB v c
  have hi : d.params.length + j < (d.iotaBinders lsB v c).length := by rw [hBl]; omega
  obtain ⟨Ps, hK, hPs⟩ := motiveType_liftN d lsB v j Tj
    ((d.iotaBinders lsB v c).length - (d.params.length + j))
  rw [← iotaBinders_motive d lsB v c hj hi] at hK
  refine .mono (le_bot_of_pred hM hX hle hO hT hCT hi hK hv
    (args := c.indices.map (fun e => (e.instL lsB).reseat (d.allTypes.length + d.allCtors.length)
      c.fields.length c.fields.length 0 0) ++ [d.ctorAppAt j c lsB (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + c.fields.length))
        (VExpr.bvars c.fields.length 0)]) ?_ (by simp [hPs, hcidx]) hR hBC W h) .bot
  rw [iotaCT, VExpr.appN_append_singleton, hBl]
  congr 3; omega

omit [ShapeEnv] in
theorem addBlock_inducts_head {E E' : VEnv} {d : VInductDecl} {T : VInductiveType}
    (h : E.addBlock d = some E') (hT : d.types[0]? = some T) :
    E'.inducts T.name = some (d, 0) := by
  unfold VEnv.addBlock at h; split at h <;> cases h
  have ht := List.getElem?_eq_some_iff.1 hT
  simp only
  rw [show d.types.findIdx? (·.name == T.name) = some 0 from
    List.findIdx?_eq_some_iff_getElem.2 ⟨ht.1, by simp [ht.2], fun _ h => absurd h (Nat.not_lt_zero _)⟩]

/-! ### Levels of auxiliary types -/

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.EqUpToLevels.lvEqv_instL {U : Nat} {e e' : VExpr}
    (H : VEnv.EqUpToLevels U e e') (ls : List VLevel) : (e.instL ls).LvEqv (e'.instL ls) := by
  induction H with
  | bvar => exact .bvar
  | const _ _ h =>
    exact .const (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => VLevel.inst_congr_l h) h)))
  | sort _ _ h => exact .sort (VLevel.inst_congr_l h)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- A telescope typed in an environment the model is sound for is typed in the model. -/
theorem IsTele.soundTele (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
    (hO : E.Ordered) : ∀ {Γ Qs : List VExpr}, E.IsTele U Γ Qs → OnCtx Γ (E.IsType U) →
      SoundTele env Γ Qs
  | _, [], _, _ => .nil
  | _, _ :: _, .cons ⟨_, hA⟩ h, hΓ =>
    .cons (hX.strongSound' hM hle hO hΓ hA).left.sound
      (IsTele.soundTele hM hX hle hO h ⟨hΓ, _, hA⟩)

/-- A telescope typed in the model has values fitting it, over any fitting valuation. -/
theorem SoundTele.exists_fits : ∀ {Γ Qs : List VExpr}, SoundTele env Γ Qs →
    ∀ {Γ₀ : List VExpr} {ρ : Valuation}, Valuation.Fits env Γ₀ Γ ρ →
    ∃ P, P.length = Qs.length ∧ Valuation.Fits env Γ₀ (Qs.reverse ++ Γ) (pushAll ρ P)
  | _, [], .nil, _, _, W => ⟨[], rfl, by simpa [pushAll] using W⟩
  | _, _ :: _, .cons hA hT, _, _, W => by
    obtain ⟨m', a', -, hm', ha', hty⟩ := hA W (LE_Interp.bot (n := 0))
    have hb : (TShape.bot).HasType m' := TShape.HasType.bot (TShape.HasType.mono_r ha'.le_sort .sort hty)
    obtain ⟨P, hPl, W'⟩ := SoundTele.exists_fits hT (W.cons (InterpTyped.hsort (hA W)) hm' hb)
    exact ⟨_ :: P, by simp [hPl], by simpa [pushAll] using W'⟩

/-- A valuation fitting a context extended by a telescope fits the context. -/
theorem Valuation.Fits.of_pushAll : ∀ {Δ Γ : List VExpr} {ρ : Valuation} {P : List TShape},
    P.length = Δ.length → Valuation.Fits env [] (Δ.reverse ++ Γ) (pushAll ρ P) →
    Valuation.Fits env [] Γ ρ
  | [], _, _, [], _, W => by simpa [pushAll] using W
  | [], _, _, _ :: _, h, _ => by cases h
  | _ :: _, _, _, [], h, _ => by cases h
  | A :: Δ, Γ, ρ, x :: P, h, W => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, pushAll] at W
    have W' := Valuation.Fits.of_pushAll (by simpa using h) W
    obtain ⟨ρ', x', a, e, W'', -⟩ := W'.cons_inv
    obtain ⟨rfl, rfl⟩ := Valuation.push_inj e
    exact W''

omit [ShapeEnv] in
theorem teleDefEq_instL {E : VEnv} {U U' : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ∀ {Γ As Bs}, E.TeleDefEq U' Γ As Bs →
      E.TeleDefEq U (Γ.map (·.instL ls)) (As.map (·.instL ls)) (Bs.map (·.instL ls))
  | _, [], [], .nil => .nil
  | _, _ :: _, _ :: _, .cons h t => .cons (h.instL hls) (by simpa using teleDefEq_instL hls t)

/-- Values fitting a telescope fit any telescope definitionally equal to it, binder by binder. -/
theorem TeleDefEq.lamsFit (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
    (hO : E.Ordered) : ∀ {Γ As Bs : List VExpr}, E.TeleDefEq U Γ As Bs → E.IsTele U Γ Bs →
    OnCtx Γ (E.IsType U) → ∀ {ρ : Valuation} {P : List TShape}, P.length = Bs.length →
    Valuation.Fits env [] (Bs.reverse ++ Γ) (pushAll ρ P) → LamsFit env ρ As P
  | _, [], [], .nil, _, _, _, [], _, _ => .nil
  | _, _, _, .nil, _, _, _, _ :: _, h, _ => by cases h
  | Γ, A :: As, B :: Bs, .cons hAB hT, .cons ⟨u, hB⟩ hTB, hΓ, ρ, P, h, W => by
    obtain _ | ⟨x, P⟩ := P; · cases h
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, pushAll] at W
    have W1 : Valuation.Fits env [] (B :: Γ) (ρ.push x) :=
      Valuation.Fits.of_pushAll (by simpa using h) W
    obtain ⟨ρ', x', a, e, W0, -, ha, hx⟩ := W1.cons_inv
    obtain ⟨rfl, rfl⟩ := Valuation.push_inj e
    obtain ⟨_, hAB⟩ := hAB
    refine .cons (((hX.strongSound' hM hle hO hΓ hAB).sound W0).2 ha) hx ?_
    exact TeleDefEq.lamsFit hM hX hle hO hT hTB ⟨hΓ, u, hB⟩ (by simpa using h) W

/-- Values fitting a telescope as a pi type telescope's points, with a domain at each. -/
theorem LamsFit.tele : ∀ {ρ : Valuation} {Qs : List VExpr} {xs : List TShape},
    LamsFit env ρ Qs xs → ∃ L : List (TShape × TShape), L.map (·.2) = xs ∧
      L.length = Qs.length ∧ ∀ j b x A, L[j]? = some (b, x) → Qs[j]? = some A →
        LE_Interp env (pushAll ρ ((L.take j).map (·.2))) b A ∧ x.HasType b
  | _, _, _, .nil => ⟨[], rfl, rfl, fun _ _ _ _ h => by cases h⟩
  | _, _, _, .cons (a := a) (x := x) ha hx hF => by
    obtain ⟨L, h1, h2, h3⟩ := LamsFit.tele hF
    refine ⟨(a, x) :: L, by simp [h1], by simp [h2], fun j b y A hj hA => ?_⟩
    cases j with
    | zero => cases hj; cases hA; exact ⟨by simpa [pushAll] using ha, hx⟩
    | succ j => simpa [pushAll] using h3 j b y A (by simpa using hj) (by simpa using hA)

/-- A pi type telescope's interpretation, at values fitting its binders, whose application to them
is a given interpretation of the codomain. -/
theorem LamsFit.foralls_realize {ρ : Valuation} {Qs : List VExpr} {xs : List TShape}
    (hF : LamsFit env ρ Qs xs) {B : VExpr} {y : TShape} (hy : LE_Interp env (pushAll ρ xs) y B) :
    ∃ h, LE_Interp env ρ h (.foralls Qs B) ∧ PiAppS h xs y := by
  obtain ⟨L, h1, h2, h3⟩ := hF.tele
  subst h1
  exact ⟨_, piTele_interp L Qs h2 h3 hy, piTele_piAppS L y⟩

/-- A sort shape interpreting a sort reads it the same. -/
theorem levelRel_of_interp {u v : VLevel} {ρ : Valuation}
    (H : LE_Interp env ρ (.sort (levelRel u)) (.sort v)) : levelRel u = levelRel v := by
  have h := WShape.LE.of_T (n := 0) H.le_sort
  generalize levelRel u = r, levelRel v = r' at h
  exact Shape0.sort.inj (congrArg (·.1) (WShape.sort_le.1 h))

/-- An auxiliary type's sort and the sort of the earlier type it stands for are read the same by
the model: the auxiliary type's declared type is the earlier type's at the occurrence (`AuxWF`),
and both declared types are pi telescopes ending in their blocks' sorts. -/
theorem aux_levelRel (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {d : VInductDecl} {Tj : VInductiveType}
    (hTW : Tj.WF envT d) (hPT : envT.IsTele d.uvars [] d.params)
    {dI : VInductDecl} {TI : VInductiveType} (hTIW : TI.WF envT dI)
    (hPI : envT.IsTele dI.uvars [] dI.params)
    {ps : List VExpr} {Bt : VExpr} (hTI : TI.type = .foralls ps Bt)
    (hpsD : envT.TeleDefEq dI.uvars [] ps dI.params)
    {ps' : List VExpr} {Y : VExpr} (hTj : Tj.type = .foralls ps' Y)
    (hps'l : ps'.length = d.params.length) {lvls : List VLevel} {args : List VExpr}
    (hY : VEnv.EqUpToLevels d.uvars Y ((Bt.instL lvls).subst (VExpr.Subst.dflt.consList args)))
    (hargl : args.length = dI.params.length)
    (hargs : ∀ i (a P : VExpr), args[i]? = some a → dI.params[i]? = some P →
      envT.HasType d.uvars d.params.reverse a
        ((P.instL lvls).subst (VExpr.Subst.dflt.consList (args.take i))))
    (hidx : Tj.indices.length = TI.indices.length)
    {lsB : List VLevel} (hlsB : ∀ l ∈ lsB, l.WF U) :
    levelRel (d.level.inst lsB) = levelRel (dI.level.inst (lvls.map (·.inst lsB))) := by
  have hlv' : ∀ l ∈ lvls.map (·.inst lsB), l.WF U := by
    intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hlsB
  -- the auxiliary type's telescope, at values
  have hPT' : envT.IsTele U [] (d.params.map (·.instL lsB)) := by
    simpa using hPT.instL hlsB (Γ := [])
  have hPΓ : OnCtx (d.params.map (·.instL lsB)).reverse (envT.IsType U) := by
    simpa using hPT'.onCtx trivial
  have hIT' : envT.IsTele U (d.params.map (·.instL lsB)).reverse
      (Tj.indices.map (·.instL lsB)) := by
    simpa [List.map_reverse] using hTW.indices.instL hlsB
  obtain ⟨xsP, hxPl, WP⟩ := (IsTele.soundTele hM hX hle hO hPT' trivial).exists_fits
    (Valuation.Fits.nil (env := env) (Γ := []))
  rw [List.append_nil] at WP
  obtain ⟨xsI, hxIl, WI⟩ := (IsTele.soundTele hM hX hle hO hIT' hPΓ).exists_fits WP
  have WD : Valuation.Fits env [] (d.params.map (·.instL lsB) ++ Tj.indices.map (·.instL lsB)).reverse
      (pushAll .nil (xsP ++ xsI)) := by
    rw [List.reverse_append, pushAll_append]; exact WI
  obtain ⟨L, hLm, hLl, hL⟩ := Valuation.Fits.tele _ _ (xsP ++ xsI) rfl
    (by simp [hxPl, hxIl]) WD
  have hXD := piTele_interp (env := env) L _ (σ := .nil) (B := .sort (d.level.inst lsB))
    (by simp [hLl]) (fun j b x A h1 h2 => ⟨(hL j b x A h1 h2).1, (hL j b x A h1 h2).2.1⟩)
    (LE_Interp.sort' (l := d.level.inst lsB))
  -- the auxiliary type's declared type
  obtain ⟨_, hdef⟩ := hTW.defeq
  have hdef' := hdef.instL hlsB (ls := lsB)
  rw [VEnv.foralls_instL'] at hdef'
  have hS := (hX.strongSound' hM hle hO (Γ := []) trivial hdef').sound
  have hXT := (hS .nil).2 (by simpa [List.map_append, VExpr.instL] using hXD)
  rw [hTj, VExpr.instL_foralls] at hXT
  have hpi := piTele_append_piAppS (L.take d.params.length) (L.drop d.params.length)
    (.sort (levelRel (d.level.inst lsB)))
  rw [List.take_append_drop] at hpi
  have hY1 := LE_Interp.piAppS_foralls hM (Ds := []) (ps'.map (·.instL lsB)) (by simpa using hXT)
    hpi (by simp [hLl, hps'l])
  have hLP : (L.take d.params.length).map (·.2) = xsP := by
    rw [List.map_take, hLm, List.take_left' (by simp [hxPl])]
  rw [hLP] at hY1
  simp only [VExpr.foralls] at hY1
  -- the occurrence, at its levels and arguments
  have hY2 := LE_Interp.levels hY1 (hY.lvEqv_instL lsB)
  have hdf : (fun i => (VExpr.Subst.dflt i).instL lsB) = VExpr.Subst.dflt := funext fun _ => rfl
  rw [VExpr.instL_subst, VExpr.instL_instL, VExpr.Subst.consList_instL, hdf] at hY2
  obtain ⟨ρ', hB1, hσ⟩ := (LE_Interp.subst hM).1 hY2
  have hΔT : envT.IsTele U [] (dI.params.map (·.instL (lvls.map (·.inst lsB)))) := by
    simpa using hPI.instL hlv' (Γ := [])
  have hk : (args.map (·.instL lsB)).length =
      (dI.params.map (·.instL (lvls.map (·.inst lsB)))).length := by simp [hargl]
  have hPl : (dI.params.map (·.instL (lvls.map (·.inst lsB)))).length = dI.params.length := by simp
  generalize hΔe : dI.params.map (·.instL (lvls.map (·.inst lsB))) = Δ at hΔT hk hPl
  generalize hae : args.map (·.instL lsB) = args' at hk hB1 hσ
  have hkl : args'.length = dI.params.length := hk.trans hPl
  obtain ⟨Pv, hyP, hPv, WΔ⟩ := fits_ofSubst hM WP dI.params.length Δ args'
    ((List.range dI.params.length).map fun i => ρ' (dI.params.length - 1 - i)) hPl hkl
    (fun i A hA => ⟨by simpa using VEnv.IsTele.closedN hO hΔT trivial i A hA,
      by simpa using IsTele.soundAt hM hX hle hO hΔT trivial i A hA⟩)
    (fun i A x hA hx => by
      subst hae hΔe
      rw [List.getElem?_map] at hA
      rw [List.getElem?_map] at hx
      obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hA
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hx
      have h := (hargs i a P ha hP).instL hlsB (ls := lsB)
      rw [VExpr.instL_subst, VExpr.instL_instL, VExpr.Subst.consList_instL, hdf,
        List.map_take, List.map_reverse] at h
      exact (hX.strongSound' hM hle hO hPΓ h).left.sound)
    (by
      refine List.forall₂_of_getElem? (by simp [hkl]) fun i y x hy hx => ?_
      have hi : i < dI.params.length := by
        have := (List.getElem?_eq_some_iff.1 hy).1; simpa using this
      simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.some.injEq] at hy
      subst hy
      have := hσ (dI.params.length - 1 - i)
      rw [VExpr.Subst.consList_apply, dif_pos (by omega), List.getElem_reverse] at this
      obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 hx
      have e : args'.length - 1 - (dI.params.length - 1 - i) = i := by omega
      simpa [e] using this)
  have hPvl : Pv.length = dI.params.length := by
    rw [← List.Forall₂.length_eq hyP]; simp
  -- the earlier type's declared type, closed
  obtain ⟨_, hdefI⟩ := hTIW.defeq
  have hTIcl := (hdefI.closedN' hO.closed trivial).1
  rw [hTI] at hTIcl
  have hpsl : ps.length = dI.params.length := hpsD.length_eq
  have hBcl : (Bt.instL (lvls.map (·.inst lsB))).ClosedN dI.params.length := by
    have := hTIcl.foralls_body; rw [List.length_nil, Nat.zero_add, hpsl] at this; exact this.instL
  have hB2 : LE_Interp env (pushAll .nil Pv) (piTele (L.drop d.params.length)
      (.sort (levelRel (d.level.inst lsB)))) (Bt.instL (lvls.map (·.inst lsB))) := by
    refine LE_Interp.closed_le hM.closed hBcl (fun i hi => ?_) hB1
    rw [pushAll_apply, dif_pos (by omega), List.getElem_reverse]
    have hj : dI.params.length - 1 - i < Pv.length := by omega
    have hyj := List.Forall₂.getElem?_l hyP (j := dI.params.length - 1 - i)
      (a := ρ' i) (by
        rw [List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        congr 1; omega)
    rw [List.getElem?_eq_getElem hj] at hyj
    obtain ⟨b, hb, hyb⟩ := hyj
    cases hb
    have e : Pv.length - 1 - i = dI.params.length - 1 - i := by omega
    simp only [e]; exact hyb
  -- the earlier type's telescope at those arguments
  have hpsD' : envT.TeleDefEq U [] (ps.map (·.instL (lvls.map (·.inst lsB)))) Δ := by
    rw [← hΔe]; simpa using teleDefEq_instL hlv' hpsD
  have hLF := TeleDefEq.lamsFit hM hX hle hO hpsD' hΔT trivial (by rw [hPvl, ← hPl])
    (by simpa using WΔ)
  obtain ⟨hI, hIi, hIpi⟩ := hLF.foralls_realize hB2
  have hdefI' := hdefI.instL hlv' (ls := lvls.map (·.inst lsB))
  rw [VEnv.foralls_instL'] at hdefI'
  have hSI := (hX.strongSound' hM hle hO (Γ := []) trivial hdefI').sound
  have hJ := (hSI .nil).1 (by rw [hTI, VExpr.instL_foralls]; exact hIi)
  rw [List.map_append, hΔe] at hJ
  have hJ2 := LE_Interp.piAppS_foralls hM (Ds := TI.indices.map (·.instL (lvls.map (·.inst lsB))))
    Δ hJ hIpi (by rw [hPvl, ← hPl])
  have hJ3 := LE_Interp.piAppS_foralls hM (Ds := [])
    (TI.indices.map (·.instL (lvls.map (·.inst lsB)))) (by simpa using hJ2)
    (piTele_piAppS (L.drop d.params.length) _) (by simp [hLl, ← hidx])
  simp only [VExpr.foralls, VExpr.instL] at hJ3
  exact levelRel_of_interp hJ3

/-- The major premise of an iota rule for an auxiliary type, at levels where the earlier type it
stands for is not a proposition, at a valuation fitting the rule's binders: it has a constructor
shape interpreting it, with fields above the fields' values. -/
theorem iota_major_aux (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {d : VInductDecl} {j : Nat} {Tj : VInductiveType}
    {c : VConstructor} (hj : d.allTypes[j]? = some Tj) {n : VNested} (hTn : Tj.nested = some n)
    (hcW : c.WF envT d Tj) {dI : VInductDecl} {tI i : Nat} {TI : VInductiveType}
    {cI : VConstructor} (hsI : env.inducts n.ind = some (dI, tI)) (hndI : ¬AxInterp.dom n.ind) (hTI : dI.types[tI]? = some TI)
    (hci : TI.ctors[i]? = some cI) (hidxc : (TI.ctors.map (·.name)).idxOf? cI.name = some i)
    (hname : c.name = cI.name) (hfl : c.fields.length = cI.fields.length)
    (hidxI : Tj.indices.length = TI.indices.length) (hargl : n.args.length = dI.params.length)
    (hlvl : n.lvls.length = dI.uvars)
    (hTIW : TI.WF envT dI) (hcIW : cI.WF envT dI TI) (hPI : envT.IsTele dI.uvars [] dI.params)
    (hcT : env.constants n.ind = some ⟨dI.uvars, TI.type⟩)
    (hcC : env.constants cI.name = some ⟨dI.uvars, cI.type⟩)
    (hrecC : env.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.recUVars)
    (hlsB : ∀ l ∈ d.recLevels.map (·.inst ls), l.WF U)
    (hP : ¬dI.PropAt (n.lvls.map (·.inst (d.recLevels.map (·.inst ls))))) {u₀ : VLevel}
    (hrecS : StrongSound env U [] ((d.recType d.recLevels d.motiveLevel j Tj).instL ls) (.sort u₀))
    (hrecCl : ∀ i (A : VExpr), (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls)
      Tj)[i]? = some A → A.ClosedN i)
    (hrecRCl : ((d.recType d.recLevels d.motiveLevel j Tj).instL ls).ClosedN)
    {Γ₀ : List VExpr} {ρ : Valuation} {zs : List TShape}
    (W : Valuation.Fits env Γ₀ (d.iotaBinders (d.recLevels.map (·.inst ls))
      (d.motiveLevel.inst ls) c).reverse (pushAll ρ zs))
    (hzl : zs.length = d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length)
    {B : VExpr}
    (hLS : StrongSound env U (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls)
      c).reverse (iotaL d (d.recLevels.map (·.inst ls)) ls j c) B) :
    ∃ N', ∃ rf : List (WShape N'),
      LE_Interp env (pushAll ρ zs) (WShape.ctor' c.name rf).T
        (d.ctorAppAt j c (d.recLevels.map (·.inst ls)) (VExpr.bvars d.params.length
          (d.allTypes.length + d.allCtors.length + c.fields.length))
          (VExpr.bvars c.fields.length 0)) ∧
      List.Forall₂ (fun z w => z ≤ w.T)
        (zs.drop (d.params.length + d.allTypes.length + d.allCtors.length)) rf := by
  have hcidx : c.indices.length = Tj.indices.length := hcW.indices.1
  generalize hlsBe : d.recLevels.map (·.inst ls) = lsB at *
  generalize hve : d.motiveLevel.inst ls = v at *
  generalize hNe : d.params.length + d.allTypes.length + d.allCtors.length = N at *
  -- the recursor's telescope
  have hQ := rec_tele_facts (U := U) hM hrecS (by rw [hlsBe, hve]; exact hrecCl)
  rw [hlsBe, hve] at hQ
  have hRcl : (VExpr.foralls (d.recTele lsB v Tj) (.app (.appN (.bvar (1 + Tj.indices.length +
      d.allCtors.length + (d.allTypes.length - 1 - j))) (VExpr.bvars Tj.indices.length 1))
      (.bvar 0))).ClosedN := by
    rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele, hlsBe, hve] at hrecRCl
    exact hrecRCl
  have hXr : ∀ ci, env.constants (d.recName j) = some ci → ls.length = ci.uvars →
      SoundEq env (d.iotaBinders lsB v c).reverse (ci.type.instL ls)
        (.foralls (d.recTele lsB v Tj) (.app (.appN (.bvar (1 + Tj.indices.length +
          d.allCtors.length + (d.allTypes.length - 1 - j))) (VExpr.bvars Tj.indices.length 1))
          (.bvar 0))) := by
    intro ci hci' _
    cases hrecC.symm.trans hci'
    rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele, hlsBe, hve]; exact .rfl
  rw [iotaL_eq, hNe] at hLS
  generalize hidxe : c.indices.map (fun e => (e.instL lsB).reseat (d.allTypes.length +
    d.allCtors.length) c.fields.length c.fields.length 0 0) = idx at hLS
  have hidxl : idx.length = Tj.indices.length := by rw [← hidxe]; simp [hcidx]
  generalize hmaje : d.ctorAppAt j c lsB (VExpr.bvars d.params.length
    (d.allTypes.length + d.allCtors.length + c.fields.length))
    (VExpr.bvars c.fields.length 0) = major at hLS ⊢
  have hQl := length_recTele d lsB v Tj
  rw [hNe] at hQl
  -- the recursor's arguments, typed along its telescope
  obtain ⟨hTSr, -⟩ := MSpine.spine hM hQ hRcl hXr _ _ rfl (by simp [hQl, hidxl]; omega) hLS.mspine'
  rw [List.take_of_length_le (by simp [hQl, hidxl]; omega)] at hTSr
  -- the major premise
  have hLS' := hLS
  rw [VExpr.appN_append_singleton] at hLS'
  obtain ⟨A', B', u', hA', hfS, hmajS, -⟩ := hLS'.app_inv
  obtain ⟨-, hE⟩ := MSpine.spine hM hQ hRcl hXr _ (VExpr.bvars N c.fields.length ++ idx) rfl
    (by simp [hQl, hidxl]) hfS.mspine'
  -- the major premise's type in the telescope
  have hK : (VExpr.bvars N c.fields.length ++ idx).length = N + Tj.indices.length := by
    simp [hidxl]
  have hdrop : (d.recTele lsB v Tj).drop (N + Tj.indices.length) =
      [Tj.typeApp lsB (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + Tj.indices.length))
        (VExpr.bvars Tj.indices.length 0)] := by
    simp only [VInductDecl.recTele, ← hNe]
    rw [List.drop_append_of_le_length (by simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega)]
    rw [List.drop_eq_nil_of_le (by simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega)]
    simp
  rw [hK, hdrop] at hE
  simp only [VExpr.foralls, VExpr.subst] at hE
  have hQk : (d.recTele lsB v Tj)[N + Tj.indices.length]? = some (Tj.typeApp lsB
      (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + Tj.indices.length))
      (VExpr.bvars Tj.indices.length 0)) := by
    have := congrArg (·[0]?) hdrop
    simpa [List.getElem?_drop] using this
  generalize hQme : Tj.typeApp lsB (VExpr.bvars d.params.length
    (d.allTypes.length + d.allCtors.length + Tj.indices.length))
    (VExpr.bvars Tj.indices.length 0) = Qmaj at hQk hE
  -- the recursor's arguments before the major premise
  have hpre := hTSr.take (N + Tj.indices.length)
  rw [List.take_left' hK] at hpre
  obtain ⟨hQmcl, uQ, hQmS⟩ := hQ _ _ hQk
  have hQmS' := SoundTy.substTele hM hpre (by rw [hK]; exact hQmcl) hQmS
  simp only [VExpr.subst] at hQmS'
  obtain ⟨hAQ, -⟩ := SoundEq.forallE_inv hM hE hA' hQmS'
  -- the type at the major premise's parameters and indices
  have hnN : d.params.length ≤ N := by omega
  have hpsE : (VExpr.bvars N c.fields.length).take d.params.length =
      VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) := by
    rw [← hNe, Nat.add_assoc, ← bvars_append', Nat.add_assoc,
      List.take_left' (by simp)]
  have hargsE : (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + Tj.indices.length) ++
        VExpr.bvars Tj.indices.length 0).map
        (·.subst (VExpr.Subst.dflt.consList (VExpr.bvars N c.fields.length ++ idx))) =
      VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) ++
        idx := by
    rw [List.map_append, bvars_subst_consList _ (by simp [hidxl]; omega),
      bvars_subst_consList _ (by simp [hidxl])]
    simp only [List.length_append, VExpr.length_bvars, hidxl]
    congr 1
    · rw [show N + Tj.indices.length - d.params.length -
          (d.allTypes.length + d.allCtors.length + Tj.indices.length) = 0 by omega,
        List.drop_zero, List.take_append_of_le_length (by simp; omega), hpsE]
    · rw [show N + Tj.indices.length - Tj.indices.length - 0 = N by omega,
        List.drop_left' (by simp), List.take_of_length_le (by omega)]
  have hQmE : Qmaj = (VExpr.const n.ind (n.lvls.map (·.inst lsB))).appN
      (n.args.map (fun a => (a.instL lsB).subst (VExpr.Subst.dflt.consList (VExpr.bvars
        d.params.length (d.allTypes.length + d.allCtors.length + Tj.indices.length)))) ++
      VExpr.bvars Tj.indices.length 0) := by
    rw [← hQme]; simp [VInductiveType.typeApp, hTn]
  rw [List.map_append] at hargsE
  obtain ⟨hps2, hidx2⟩ := List.append_inj hargsE (by simp)
  have hQsub : Qmaj.subst (VExpr.Subst.dflt.consList (VExpr.bvars N c.fields.length ++ idx)) =
      (VExpr.const n.ind (n.lvls.map (·.inst lsB))).appN
        (n.args.map (fun a => (a.instL lsB).subst (VExpr.Subst.dflt.consList (VExpr.bvars
          d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)))) ++ idx) := by
    rw [← hQme, VInductiveType.typeApp_subst, hps2, hidx2]; simp [VInductiveType.typeApp, hTn]
  have hargs1 := hQsub
  rw [hQmE, VExpr.subst_appN] at hargs1
  replace hargs1 := VExpr.appN_const_inj hargs1
  -- the constructor application, typed at the type
  have hmajE : major = (VExpr.const cI.name (n.lvls.map (·.inst lsB))).appN
      (n.args.map (fun a => (a.instL lsB).subst (VExpr.Subst.dflt.consList (VExpr.bvars
        d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)))) ++
      VExpr.bvars c.fields.length 0) := by
    rw [← hmaje, VInductDecl.ctorAppAt_eq hj]; simp [VInductiveType.ctorApp, hTn, hname]
  generalize hAse : n.args.map (fun a => (a.instL lsB).subst (VExpr.Subst.dflt.consList
    (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)))) = As
    at hQsub hmajE hargs1
  have hAsl : As.length = dI.params.length := by rw [← hAse]; simp [hargl]
  rw [hmajE] at hmajS ⊢
  rw [hQsub] at hAQ
  have hCS := (hmajS.mspine').retype hAQ
  -- the type's spine, typed in the model
  have hlvI : ∀ l ∈ n.lvls.map (·.inst lsB), l.WF U := by
    intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hlsB
  have hlsBl : (n.lvls.map (·.inst lsB)).length = dI.uvars := by simp [hlvl]
  obtain ⟨hQh, hRh, hXh⟩ := typeTeleFacts (U := U) hM hX hle hO hTIW hPI hcT hlvI
  have hrecS' := hrecS
  rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele, hlsBe, hve] at hrecS'
  obtain ⟨uS, hQS⟩ := hrecS'.foralls_getElem (N + Tj.indices.length) (by rw [hQl]; omega)
  rw [(List.getElem?_eq_some_iff.1 hQk).2, hQmE, List.append_nil] at hQS
  obtain ⟨hTSq, -⟩ := typeSpine hM hX hle hO hTIW hPI hcT hlvI (by simp [hargl, hidxI])
    hQS.mspine'
  have hTSq' := TeleSubst.substTele hM (Δ := (d.recTele lsB v Tj).take (N + Tj.indices.length))
    (by simpa using hTSq) hpre (by
      intro x hx
      have := (VExpr.ClosedN.appN_args (hQmE ▸ hQmcl)).2 x hx
      rwa [hK])
  rw [hargs1] at hTSq'
  have hQhl : ((dI.params ++ TI.indices).map (·.instL (n.lvls.map (·.inst lsB)))).length =
      (As ++ idx).length := by simp [hidxl, hAsl, hidxI]
  have hTS := MSpine.ofTele hM hcT hlsBl hQh hRh (hXh _ hcT hlsBl) _ (As ++ idx) rfl (by rw [hQhl]; exact Nat.le_refl _)
      (by rw [List.take_of_length_le (by rw [hQhl]; exact Nat.le_refl _), List.map_append]
          exact hTSq')
  rw [← hQhl, List.drop_length] at hTS
  simp only [VExpr.foralls, VExpr.subst] at hTS
  -- the values of the parameters and fields interpret them
  have hbv : ∀ (a b : Nat) (ys : List TShape) (_ : ys.length = a) (hba : b + a ≤ zs.length),
      (∀ i (h : i < a), ys[i]? = some (zs[b + i]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left h b) hba))) →
      zs.length = N + c.fields.length →
      List.Forall₂ (fun y x => LE_Interp env (pushAll ρ zs) y x) ys
        (VExpr.bvars a (N + c.fields.length - b - a)) := by
    intro a b ys hl hba H hzl'
    refine List.forall₂_of_getElem? (by simp [hl]) fun i y x hy hx => ?_
    have hi : i < a := by have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    rw [H i hi] at hy; cases hy
    rw [List.getElem?_eq_some_iff] at hx
    obtain ⟨-, rfl⟩ := hx
    rw [getElem_bvars]
    refine bvar_iff.2 ?_
    have := pushAll_bvar (ρ := ρ) hzl' (b + i) (by omega)
    rw [show a - 1 - i + (N + c.fields.length - b - a) = N + c.fields.length - 1 - (b + i) by
      omega, this]
    exact .rfl
  have hps : List.Forall₂ (fun y x => LE_Interp env (pushAll ρ zs) y x)
      (As.map fun _ => (WShape.bot : WShape 0).T) As :=
    List.forall₂_map_left_iff.2 (List.forall₂_refl' (r := fun _ x =>
      LE_Interp env (pushAll ρ zs) (WShape.bot : WShape 0).T x) fun _ => .bot)
  have hfs := hbv c.fields.length N (zs.drop N) (by simp [hzl]) (by omega)
    (fun i h => by simp [List.getElem?_drop]) hzl
  rw [show N + c.fields.length - N - c.fields.length = 0 by omega] at hfs
  obtain ⟨N', rf, hrf, -, hCI⟩ := ctorApp_realize hM hX hle hO hndI hsI hTI hci hidxc hTIW hcIW hPI
    hcT hcC hlvI hP W hAsl (by simp [hfl]) (by rw [hidxl, hidxI]) hTS hCS
    (List.forall₂_append' hps hfs)
  rw [List.drop_left' (by simp [hAsl])] at hrf
  rw [hname]
  exact ⟨N', rf, hCI, hrf⟩

/-- An iota rule of a block is sound in the model, given the model's soundness for the environment
the block was declared in. -/
theorem iotaRuleSound_block (hM : ModelEnv env) (henv : env.WF) {E₁ E₂ : VEnv} (hE₁ : E₁.WF)
    {d : VInductDecl} (hd : d.WF E₁) (hg : d.GeneratedWF E₁) (h1 : E₁.addInduct d = some E₂)
    (hle : E₂ ≤ env) (hX₁ : SoundHyps E₁ env) (hni : NoDomI E₂) {q j : Nat} {c : VConstructor}
    (hq : d.allCtors[q]? = some (j, c)) :
    RuleSound env U (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c) := by
  have h1' := h1
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1'
  obtain ⟨envT, hTs, envC, hC, envR, hR', hB'⟩ := h1'
  have HB : VEnv.BlockEnvs env d E₁ envT envC envR := ⟨hE₁, hd, hg, hTs, hC, hR', ⟨E₂, hB', hle⟩⟩
  have hwfR := HB.envR_wf
  have hOR := hwfR.ordered
  have hleR := HB.envR_le
  have hXR : SoundHyps envR env :=
    hX₁.mono (fun h => HB.envR_defeqs ▸ h) (fun h => HB.envR_inducts ▸ h)
  have hle₁ : E₁ ≤ env := ((VEnv.addConstList_le hTs).trans ((VEnv.addConstList_le hC).trans
    (VEnv.addConstList_le hR'))).trans hleR
  obtain ⟨Tj, hj, hcm⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
  obtain ⟨T0, hT0⟩ : ∃ T0, d.types[0]? = some T0 := by
    cases e : d.types with
    | nil => exact (hd.nonempty e).elim
    | cons T _ => exact ⟨T, rfl⟩
  have hs0 : env.inducts T0.name = some (d, 0) := hle.inducts (addBlock_inducts_head hB' hT0)
  have hnd0 := hni (addBlock_inducts_head hB' hT0)
  have hcW := (hd.ctors envT hTs Tj (List.mem_of_getElem? hj)).2 c hcm
  have hmem : d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c ∈
      d.iotaRules := by
    simp only [VInductDecl.iotaRules, List.mem_map]
    exact ⟨((j, c), q), List.mk_mem_zipIdx_iff_getElem?.2 hq, rfl⟩
  have hdfE := hM.stepUniq.iota hs0 hmem
  have hdfR := (hg envT envC envR hTs hC hR').2 _ hmem
  refine iotaRuleSound_of hM hs0 (hnd0.2 j _ hj) hj hq hcW.indices.1
    ⟨(henv.ordered.closed.2 hdfE).1.1, (henv.ordered.closed.2 hdfE).2.1⟩ ?fwd ?bwd
  case fwd =>
    intro lsB σ x H
    simp only [VInductDecl.ctorAppAt, hj, Option.getD_some] at H
    rcases ctorApp_inv_all hM hE₁ hle₁ hd hTs hs0 hj hcm (by simp) (by simp) H with h | ⟨k, rf, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨k, rf, h2, h3⟩
  case bwd =>
  intro ls hls hlen R hRe B B' Γ₀ ρ zs hF W hLS hRS hBB hBC hTel W0 y hy
  -- the rule's binders, typed where it is checked
  have hTy := hdfR.1.instL hls (ls := ls)
  obtain ⟨-, -, hTyE⟩ := d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars)
    d.motiveLevel q j c
  simp only [List.map_nil] at hTy
  rw [hTyE, VLevel.inst_map_id hlen, iotaRule_type] at hTy
  obtain ⟨hTB, hCT⟩ := VEnv.IsType.foralls_inv hOR (hTy.isType (Γ := []) hOR trivial)
  rw [List.append_nil] at hCT
  by_cases hLE : d.LargeElim
  · have hOK := hd.largeElim hLE
    have hlarge : d.largeElim = true := hLE
    have hlsB : ∀ l ∈ d.recLevels.map (·.inst ls), l.WF U := by
      intro l hl; obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls
    obtain ⟨-, hR2, -⟩ := d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars)
      d.motiveLevel q j c
    rw [VLevel.inst_map_id hlen] at hR2
    have hiR : d.iotaRhs ls q j c = .lams (d.iotaBinders (d.recLevels.map (·.inst ls))
        (d.motiveLevel.inst ls) c) R := by
      rw [VInductDecl.iotaRhs, hR2, hRe]
    have hRT := hRS.sound.defeq_r hBB.symm
    have hLS' := hLS
    rw [iotaL_eq] at hLS ⊢
    have hBl := length_iotaBinders d (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c
    by_cases hPA : d.PropAt (d.blockLevels ls)
    · rcases hOK with hnz | ⟨T, hTs1, haux, hcs⟩
      · exfalso
        have := VLevel.equiv_def.1 hPA []
        rw [VLevel.eval_inst] at this
        exact hnz _ this
      · have hjT : j = 0 ∧ Tj = T := by
          rw [VInductDecl.allTypes, hTs1, haux] at hj
          cases j with
          | zero => exact ⟨rfl, (Option.some.inj hj).symm⟩
          | succ j => simp at hj
        obtain ⟨rfl, rfl⟩ := hjT
        rcases hcs with hnil | ⟨c', hc1, hfl⟩
        · rw [hnil] at hcm; cases hcm
        · obtain rfl : c' = c := by rw [hc1] at hcm; simpa [eq_comm] using hcm
          refine iota_body_ge_k hM hs0 (hnd0.2 _ _ hj) hj hq hc1 hPA hlarge hiR hBl (by simp [hcW.indices.1])
            (fun k i hk h => iotaIdx_spec hk h) hF W hLS.mspine' hRT (fun k hk hk' => ?_) hy
          have hzl : zs.length = _ := hF.length.trans hBl
          have hkf : k < c'.fields.length := by omega
          obtain ⟨f, hf⟩ : ∃ f, c'.fields[k]? = some f := ⟨_, List.getElem?_eq_getElem hkf⟩
          have hf0 : f.level.inst (d.recLevels.map (·.inst ls)) ≈ .zero := by
            by_cases h0 : f.level ≈ .zero
            · exact VLevel.inst_congr_l h0
            · have hm := hfl k f hf h0
              rw [VInductDecl.fieldIdx, List.findIdx?_eq_none_iff] at hk'
              exact absurd (hk' _ hm) (by simp [VExpr.isBVar])
          exact iota_proof_field hM hXR hleR hOR
            ((VEnv.addConstList_le hC).trans (VEnv.addConstList_le hR')) hcW hlsB hTB hf hf0
            hTel W0 hF hk
    · have hleC : envC ≤ envR := VEnv.addConstList_le hR'
      have hleTC : envT ≤ envR := (VEnv.addConstList_le hC).trans hleC
      have hXT : SoundHyps envT env := hXR.mono hleTC.defeqs hleTC.inducts
      have hXC : SoundHyps envC env := hXR.mono hleC.defeqs hleC.inducts
      have hOT := HB.envT_wf.ordered
      have hOC := HB.envC_wf.ordered
      have hrecC : env.constants (d.recName j) =
          some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩ :=
        hleR.constants (VEnv.addConstList_constants_of_mem hR'
          (List.mem_map.2 ⟨(Tj, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩))
      have hrecRCl : ((d.recType d.recLevels d.motiveLevel j Tj).instL ls).ClosedN :=
        (hM.closed.constType hrecC).instL
      have hrecCl : ∀ i (A : VExpr), (d.recTele (d.recLevels.map (·.inst ls))
          (d.motiveLevel.inst ls) Tj)[i]? = some A → A.ClosedN i := by
        intro i A hA
        have h := hrecRCl
        rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele] at h
        simpa using VExpr.ClosedN.foralls_getElem h i A hA
      obtain ⟨u₀, hrecS⟩ : ∃ u₀, StrongSound env U []
          ((d.recType d.recLevels d.motiveLevel j Tj).instL ls) (.sort u₀) := by
        have hW := (hg envT envC envR hTs hC hR').1 _
          (List.mem_map.2 ⟨(Tj, j), List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩)
        obtain ⟨u, hu⟩ := VEnv.IsType.instL (Γ := []) hls hW
        exact ⟨_, (hXC.strongSound' (Γ := []) hM (hleC.trans hleR) hOC trivial hu).left⟩
      cases hn : Tj.nested with
      | none =>
        have hjt : j < d.types.length := by
          refine Classical.byContradiction fun h => ?_
          have hja : d.aux[j - d.types.length]? = some Tj := by
            rw [VInductDecl.allTypes, List.getElem?_append_right (by omega)] at hj; exact hj
          obtain ⟨n, hn', -⟩ := hd.aux Tj (List.mem_of_getElem? hja)
          rw [hn] at hn'; cases hn'
        have hTj : d.types[j]? = some Tj := by
          rw [VInductDecl.allTypes, List.getElem?_append_left hjt] at hj; exact hj
        have hsT := henv.inducts_getElem hs0 hTj
        have hnd := (StepUniqProof.names_of_WF henv).ctorNodup hs0 (List.mem_of_getElem? hj)
        obtain ⟨i, hci⟩ := List.mem_iff_getElem?.1 hcm
        have hil := (List.getElem?_eq_some_iff.1 hci).1
        have hidxc : (Tj.ctors.map (·.name)).idxOf? c.name = some i := by
          refine List.idxOf?_eq_some_iff.2 ⟨by simpa using hil, by
            simp [(List.getElem?_eq_some_iff.1 hci).2], fun k hk => ?_⟩
          simp only [List.getElem_map]
          intro he
          have e2 := (List.getElem_inj (xs := Tj.ctors.map (·.name)) (i := k) (j := i)
            (h₀ := by simp; omega) (h₁ := by simpa using hil) hnd).1
            (by simp [he, (List.getElem?_eq_some_iff.1 hci).2])
          omega
        have hleT : envT ≤ env := hleTC.trans hleR
        have hcT : env.constants Tj.name = some ⟨d.uvars, Tj.type⟩ :=
          hleT.constants <| VEnv.addConstList_constants_of_mem hTs
            (List.mem_map.2 ⟨Tj, List.mem_of_getElem? hTj, rfl⟩)
        have hcC : env.constants c.name = some ⟨d.uvars, c.type⟩ :=
          (hleC.trans hleR).constants <| VEnv.addConstList_constants_of_mem hC
            (List.mem_map.2 ⟨(j, c), VInductDecl.mem_ctors_iff.2 ⟨Tj, hTj, hcm⟩, rfl⟩)
        have hTW := (hd.ctors envT hTs Tj (List.mem_of_getElem? hj)).1
        have hPT : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le hTs)
        have hmaj := iota_major_own hM hXT hleT hOT hsT (hnd0.1 Tj (List.mem_of_getElem? hTj)) hTj hj hn hci hidxc hTW hcW hPT hcT hcC
          hrecC hls hlen hlsB (by rwa [recLevels_inst d hlen]) hrecS hrecCl hrecRCl W
          (hF.length.trans hBl) hLS'
        exact iota_body_ge hM hs0 (hnd0.2 j _ hj) hj hq hPA hiR hBl (by simp [hcW.indices.1]) hF W hLS.mspine' hRT
          hmaj hy
      | some n =>
        have hTa : Tj ∈ d.aux := by
          rcases List.mem_append.1 (List.mem_of_getElem? hj) with h | h
          · rw [(hd.types Tj h).2] at hn; cases hn
          · exact h
        have hnz : d.level.IsNeverZero := by
          rcases hOK with hnz | ⟨T, -, haux, -⟩
          · exact hnz
          · rw [haux] at hTa; cases hTa
        obtain ⟨n', hn', hA⟩ := hd.aux Tj hTa
        rw [hn] at hn'; cases hn'
        obtain ⟨⟨dI, tI, TI, hsIT, hTI, hlvl, -, hargl, hargs,
          ⟨ps, Bt, hTIty, hpsD, ps', Y, hps'D, hTjty, hY⟩, hctors⟩⟩ := hA envT hTs
        have hWT := HB.envT_wf
        have hleT : envT ≤ env := hleTC.trans hleR
        obtain ⟨env₀', envTI, -, hdI, hTI', hleTI, TI', hTI2, hTIn⟩ := hWT.inducts hsIT
        obtain rfl := Option.some.inj (hTI.symm.trans hTI2)
        obtain ⟨env₀'', env₂', -, -, hadd, hle₂', -⟩ := hWT.inducts_block hsIT
        simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
        obtain ⟨envT2, hT2, envC2, hC2, envR2, hR2, hB2⟩ := hadd
        have hleC2 : envC2 ≤ envT := (VEnv.addConstList_le hR2).trans
          ((VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB2)).trans hle₂')
        have hsI : env.inducts n.ind = some (dI, tI) := hleT.inducts hsIT
        obtain ⟨cI, hcI, hcname, hcorr⟩ := List.Forall₂.forall_exists_r hctors c hcm
        have hTIm : TI ∈ dI.types := List.mem_of_getElem? hTI
        have hdIc := hdI.ctors envTI hTI' TI (List.mem_append_left _ hTIm)
        have hcIW := VConstructor.WF.mono hleTI (hdIc.2 cI hcI)
        have hTIW := VInductiveType.WF.mono hleTI hdIc.1
        have hPI := hdI.params.mono ((VEnv.addConstList_le hTI').trans hleTI)
        obtain ⟨hfl, hcidxI⟩ := VInductDecl.auxCounts hn hcW (hdI.types TI hTIm).2 hcIW hargl
          hcorr
        have hidxI : Tj.indices.length = TI.indices.length :=
          hcW.indices.1.symm.trans (hcidxI.trans hcIW.indices.1)
        have hnd := (StepUniqProof.names_of_WF henv).ctorNodup hsI (List.mem_append_left _ hTIm)
        obtain ⟨i, hci⟩ := List.mem_iff_getElem?.1 hcI
        have hil := (List.getElem?_eq_some_iff.1 hci).1
        have hidxc : (TI.ctors.map (·.name)).idxOf? cI.name = some i := by
          refine List.idxOf?_eq_some_iff.2 ⟨by simpa using hil, by
            simp [(List.getElem?_eq_some_iff.1 hci).2], fun k hk => ?_⟩
          simp only [List.getElem_map]
          intro he
          have e2 := (List.getElem_inj (xs := TI.ctors.map (·.name)) (i := k) (j := i)
            (h₀ := by simp; omega) (h₁ := by simpa using hil) hnd).1
            (by simp [he, (List.getElem?_eq_some_iff.1 hci).2])
          omega
        have hcT : env.constants n.ind = some ⟨dI.uvars, TI.type⟩ :=
          (hleTI.trans hleT).constants <| VEnv.addConstList_constants_of_mem hTI'
            (List.mem_map.2 ⟨TI, hTIm, by rw [hTIn]⟩)
        have hcC : env.constants cI.name = some ⟨dI.uvars, cI.type⟩ :=
          (hleC2.trans hleT).constants <| VEnv.addConstList_constants_of_mem hC2
            (List.mem_map.2 ⟨(tI, cI), VInductDecl.mem_ctors_iff.2 ⟨TI, hTI, hcI⟩, rfl⟩)
        have hTW := (hd.ctors envT hTs Tj (List.mem_of_getElem? hj)).1
        have hPT : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le hTs)
        have hrel := aux_levelRel (U := U) hM hXT hleT hOT hTW hPT hTIW hPI hTIty hpsD hTjty
          hps'D.length_eq hY hargl hargs hidxI hlsB
        have hdl : levelRel (d.level.inst (d.recLevels.map (·.inst ls))) = true := by
          simp only [levelRel, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          intro h
          have := VLevel.equiv_def.1 h []
          rw [VLevel.eval_inst] at this
          exact hnz _ this
        have hP : ¬dI.PropAt (n.lvls.map (·.inst (d.recLevels.map (·.inst ls)))) := by
          have := hrel ▸ hdl
          simpa [levelRel, VInductDecl.PropAt] using this
        exact iota_body_ge hM hs0 (hnd0.2 j _ hj) hj hq hPA hiR hBl (by simp [hcW.indices.1]) hF W hLS.mspine' hRT
          (iota_major_aux hM hXT hleT hOT hj hn hcW hsI
            (hTIn ▸ (hni ((hleTC.trans (VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB'))).inducts hsIT)).1 TI hTIm) hTI hci hidxc hcname hfl hidxI hargl hlvl
            hTIW hcIW hPI hcT hcC hrecC hls hlen hlsB hP hrecS hrecCl hrecRCl W
            (hF.length.trans hBl) hLS') hy
  · have hv : d.motiveLevel.inst ls = .zero := by
      simp [VInductDecl.motiveLevel, hLE, VLevel.inst]
    rw [hv] at hTB hCT hBC hRS hTel W
    exact iota_bwd_small hM hXR hleR hOR hj hcW.indices.1 (by rw [levelRel_zero]) hTB hCT
      hRS.sound hBC W hy _

/-- The iota rules of every block of a well-formed environment are sound in its model. -/
theorem _root_.Lean4Lean.VEnv.WF.blockSound (henv : env.WF) (hM : ModelEnv env) :
    BlockSound env := by
  intro E₁ d E₂ hE₁ hD hle hni hX U df hdf
  cases hD with
  | induct hd hg h1 =>
    obtain ⟨q, j, c, hq, rfl⟩ := mem_iotaRules hdf
    exact iotaRuleSound_block hM henv hE₁ hd hg h1 hle hX hni hq

end LogRel
end Lean4Lean

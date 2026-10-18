import Lean4Lean.Theory.Typing.LogRel.InjWF
import Lean4Lean.Theory.Typing.LogRel.Realize
import Lean4Lean.Theory.Typing.LogRel.AdeqBlock

/-!
# Chain inversion at projections, from adequacy

Two projections of the same term at inductive types joined by a chain of equalities at sorts have
types joined by one too (`ProjChain`). The chain's links are related at the least shape of the left
end's type (every argument and constructor telescope `bot`), the relation is transitive at a
shape, and at an inductive type shape it relates the two ends' arguments along the type's
telescope (`IndRel`), from which the projections' types are equal (`projType_congr`).
-/

noncomputable section

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

section
variable [ShapeEnv] [AxInterp] {env : VEnv}

/-- The head the model gives a recorded type. -/
def typeHead (s : Name) (d : VInductDecl) (T : VInductiveType) : IndHead :=
  ⟨s, d.params.length + T.indices.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩

/-- The least shape of an inductive type at arguments `Args`: every argument and every
constructor telescope `bot`. -/
def seedShape (r : Bool) (s : Name) (d : VInductDecl) (T : VInductiveType) (Args : List VExpr) :
    WShape 1 :=
  .indTy r (typeHead s d T)
    ((Args.map fun _ => (WShape.bot : WShape 0)) ++ T.ctors.map fun _ => .bot)

/-- An inductive type applied to its parameters and indices, typed in the model, is interpreted
at its least shape, which is typed at its sort's shape. -/
theorem seedShape_interp (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {s : Name} (hnd : ¬AxInterp.dom s) {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    (hTW : T.WF envT d) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩) {ls : List VLevel} {U : Nat}
    (hls : ∀ l ∈ ls, l.WF U) {Γ₀ Γ : List VExpr} {ρ : Valuation}
    (W : Valuation.Fits env Γ₀ Γ ρ) {Args : List VExpr} {u : VLevel}
    (hn : Args.length = d.params.length + T.indices.length)
    (hTS : MSpine env Γ ((VExpr.const s ls).appN Args) (.sort u)) :
    (levelRel u).rel = d.rel ls ∧
    (seedShape (d.rel ls) s d T Args).HasType (WShape.sort (levelRel u)) ∧
    LE_Interp env ρ (seedShape (d.rel ls) s d T Args).T ((VExpr.const s ls).appN Args) := by
  obtain ⟨-, hsort⟩ := typeSpine hM hX hle hO hTW hPT hcT hls (As := Args) (I := [])
    (by simpa using hn) (by simpa using hTS)
  have hrel : (levelRel u).rel = d.rel ls := by
    rw [SoundEq.sort.1 hsort]; simp only [levelRel, VInductDecl.rel, VInductDecl.PropAt]
    congr 1
  have hty : (seedShape (d.rel ls) s d T Args).HasType (WShape.sort (levelRel u)) := by
    refine WShape.HasType.indTy (by cases h : d.rel ls <;> simp [hrel, h]) ?_
    exact WShape.ctysOK_of (by simp [typeHead, hn])
      (fun x hx => by simp at hx; obtain ⟨-, -, rfl⟩ := hx; exact .bot' .sort)
  refine ⟨hrel, hty, ?_⟩
  have hC : Const env s ls (LE_Interp env ρ) (Args.map fun _ => (WShape.bot : WShape 0)).reverse
      (seedShape (d.rel ls) s d T Args).T := by
    refine .indTy (ctys := T.ctors.map fun _ => .bot) hs hT (by simp [hn]) (by simp)
      (fun j c' cty' hc' hcty' => ?_) ?_
    · have hj : j < T.ctors.length := (List.getElem?_eq_some_iff.1 hc').1
      obtain rfl : cty' = .bot := by simp [hj] at hcty'; exact hcty'.symm
      exact ⟨_, .bot, (PiAppS.bot _).mono_m TShape.bot_eqv.1⟩
    · simp only [List.length_reverse, List.length_map, hn, List.reverse_reverse]
      simp only [seedShape, typeHead]; exact .rfl
  have hsortI : LE_Interp env ρ (WShape.sort (n := 1) (levelRel u)).T (.sort u) := by
    refine .sort ?_
    have := (TShape.lift_eqv (a := TShape.sort (levelRel u)) (m := 1) (Nat.zero_le _)).1
    simpa [TShape.sort, WShape.lift_sort] using this
  rw [← spine_eq_appN] at hTS ⊢
  exact LE_Interp.apps_realize hM W (WShape.HasType.T hty) hsortI hTS
    ((List.Forall₂.reverse).2 (forall₂_bot (n := 0) (ρ := ρ) Args)) hC

end

variable {env : VEnv}

section
variable (henvW : env.WF) {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
  (hH : @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
    henvW.stepUniq env Γ)
include hΓ hH

/-- A link of a chain whose left end is interpreted at a shape not below `bot`'s, of depth one,
is related at it. -/
theorem link_at {X Y : VExpr} {w : VLevel} {a0 : @WShape env.shapeEnv 1}
    (ha0 : @WShape.HasType env.shapeEnv 1 a0 (@WShape.type env.shapeEnv 1))
    (hne : ∃ r h l, a0 = @WShape.indTy env.shapeEnv 0 r h l)
    (d : env.IsDefEq U Γ X Y (.sort w))
    (hX : @LE_Interp env.shapeEnv (@AxInterp.none env.shapeEnv) env (@Valuation.nil env.shapeEnv) (@WShape.T env.shapeEnv 1 a0) X) :
    TyRel henvW U Γ 1 X Y a0 := by
  letI := env.shapeEnv
  have H := d.strong henvW.ordered hΓ
  have hS : ∀ {Γ M N A}, env.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A :=
    henvW.modelSound
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  obtain ⟨n', m', a, hn, le_m, hm', ha, hty⟩ := ((hS H).left.sound W.fits hX).out
  have R := (LR.adequacy_of (henvW.modelEnv AxOK.none nofun) .rfl hS hΓ hH H hΓ hm' ha hty).2 W
  simp only [subst_id] at R
  have hle : a0.lift n' ≤ m' := (TShape.LE.lift_l (a := a0.T) (b := m'.T) hn).1 le_m
  rcases WShape.le_sort.1 ha.le_sort' with rfl | rfl
  · cases hty.bot_r
    obtain ⟨r, h, l, rfl⟩ := hne
    have := WShape.le_bot.1 hle
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by simp at hn; omega⟩
    rw [WShape.lift_indTy (Nat.zero_le _)] at this
    cases congrArg (·.1) this
  · have R := (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq _).toType R
    have R := (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq _).mono_r_2_ty hle
      ((WShape.HasType.lift hn).2 ha0) hty.toType R
    exact (LR.TyDefEq.lift hn ha0).1 R

/-- A chain's ends have the same interpretations, and it is related at every shape of depth one
not below `bot`'s its left end is interpreted at. -/
theorem chain_at {X Y : VExpr} (H : TyEq env U Γ X Y) :
    @SoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env Γ X Y ∧
    ∀ (a0 : @WShape env.shapeEnv 1), @WShape.HasType env.shapeEnv 1 a0 (@WShape.type env.shapeEnv 1) →
      (∃ r h l, a0 = @WShape.indTy env.shapeEnv 0 r h l) →
      @LE_Interp env.shapeEnv (@AxInterp.none env.shapeEnv) env (@Valuation.nil env.shapeEnv) (@WShape.T env.shapeEnv 1 a0) X →
      TyRel henvW U Γ 1 X Y a0 := by
  letI := env.shapeEnv
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  induction H with
  | base d =>
    exact ⟨(henvW.modelSound (d.strong henvW.ordered hΓ)).sound,
      fun a0 ha0 hne hX => link_at henvW hΓ hH ha0 hne d hX⟩
  | trans _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun a0 ha0 hne hX => ?_⟩
    exact (LR (U := U) (Γ := Γ) henvW.ordered henvW.stepUniq 1).trans_ty
      (ih1.2 a0 ha0 hne hX) (ih2.2 a0 ha0 hne ((ih1.1 W.fits).1 hX))

end

/-- Chain inversion at projections, from adequacy's environment cases at every context: two
projections of a term at inductive types joined by a chain have types joined by an equality. -/
theorem projChain_of (henvW : env.WF)
    (hH : ∀ U Γ, OnCtx Γ (env.IsType U) →
      @AdequacyHyps env U env.shapeEnv (@AxInterp.none env.shapeEnv) henvW.ordered
        henvW.stepUniq env Γ)
    (U : Nat) : ProjChain env U := by
  letI := env.shapeEnv
  intro Γ s d t T c k f ls ls' As As' I I' e u u' hΓ hs ht hc hf hls hlen hls' hlen' hA hI hA'
    hI' hP _ hX _ he _ _ H
  -- the block
  obtain ⟨env₀, envT, h₀, hd, hT', hle, T', hT'', hTn⟩ := henvW.inducts hs
  cases ht.symm.trans hT''
  have hTm : T ∈ d.types := List.mem_of_getElem? ht
  have hTW : T.WF envT d := (hd.ctors envT hT' T (List.mem_append_left _ hTm)).1
  have hPT0 : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le hT')
  have hcT : env.constants s = some ⟨d.uvars, T.type⟩ := hle.1
    (VEnv.addConstList_constants_of_mem hT' (by rw [← hTn]; exact List.mem_map_of_mem hTm))
  have hOT : envT.Ordered := (VEnv.WF.addConstList h₀ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp; exact (hd.types T hT).1) hT').ordered
  have hM := henvW.modelEnv AxOK.none nofun
  have hSH : SoundHyps envT env :=
    (henvW.soundHyps hM (quotRuleSound hM henvW) (henvW.blockSound hM) NoDom.none NoDomI.none).mono
      hle.2 hle.3
  have W : LR.SubstWF (U := U) henvW.ordered henvW.stepUniq Γ .id .id Γ .nil := .id
  have hXs : MSpine env Γ ((VExpr.const s ls).appN (As ++ I)) (.sort u) :=
    (henvW.modelSound (hX.strong henvW.ordered hΓ)).left.mspine'
  obtain ⟨-, hty0, hint0⟩ := seedShape_interp hM hSH hle hOT (fun h => h.elim) hs ht hTW hPT0 hcT hls W.fits
    (by simp [hA, hI]) hXs
  have R := (chain_at henvW hΓ (hH U Γ hΓ) H).2 _ hty0.toType ⟨_, _, _, rfl⟩ hint0
  simp only [TyRel, LR, LRS, seedShape, LRS.TyDefEq.indTy_iff] at R
  have hInert : Inert env s := Inert.of_role hM.roles
    (fun hdf e => henvW.rule_lhs_params hdf e) (.indTy hs ht) (fun _ => nofun) (fun _ _ => nofun)
    nofun
  obtain ⟨hR, -⟩ := R.resolve_right fun ⟨hN, _⟩ =>
    NeRed.not_inert henvW.stepUniq hInert hN .rfl
  obtain ⟨-, ls₁, ls₁', As₁, As₁', r1, r2, heq, hl1, hl2, hSR⟩ := hR
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInert.whnf r1)
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hInert.whnf r2)
  have hTT : ∀ ls, typeTele env (typeHead s d T).name ls = (d.params ++ T.indices).map (·.instL ls) :=
    fun ls => typeTele_block hs ht ls
  rw [hTT, hTT] at hSR
  -- the parameters, equal along the parameters' telescope
  have hSRp := SubstRel.take (σ := Subst.dflt) (σ' := Subst.dflt) d.params.length
    (by simp [hA, hI]) (by simp [hA', hI']) hSR
  simp only [List.take_left' hA, List.take_left' hA', ← List.map_take,
    List.take_left' (rfl : d.params.length = d.params.length)] at hSRp
  have hOnP : OnCtx (d.params.map (·.instL ls)).reverse (env.IsType U) := by
    have := henvW.blockTele_onCtx hs ht
    rw [List.reverse_append] at this
    rw [← List.map_reverse]; exact (OnCtx.of_append this).instL hls
  have W := hSRp.substEq hOnP
  have Wl := hSRp.left.substEq hOnP
  -- the earlier projections at both sides are the same terms, typed at the left side
  have hF := henvW.projFacts hs ht hc
  have W2 := VEnv.keptSubstEq hF hls W hf hP fun j _ fj hfj hPj =>
    (VEnv.projCongr henvW.ordered hΓ hs ht hc hF hls hlen hA hI hA hI Wl hX he j fj hfj hPj).2
  obtain ⟨hFt, hFk⟩ := hF.fields k f hf
  have hΓk := hFt.onCtx (by simpa using hF.params.onCtx trivial)
  have H := VEnv.IsDefEq.instL_r henvW.ordered hΓk hls hls' heq hFk
  simp only [List.map_append, List.map_reverse] at H
  have H := VEnv.IsDefEq.substDF henvW.ordered W2.wf hΓ W2 H
  rw [← VEnv.projType_eq hf, ← VEnv.projType_eq hf] at H
  exact .base H

/-- Chain inversion at projections holds in every well-formed environment whose adequacy cases
hold at every context: the projection hypothesis of `VEnv.WF'.inj_of`. -/
theorem projStep : ProjStep := fun henvW hH U => projChain_of henvW hH U

/-- Every well-formed environment has injectivity, given the inductive and quotient steps of the
fundamental lemma. -/
theorem _root_.Lean4Lean.VEnv.WF'.inj_of' (hInd : IndStep) (hQuot : QuotStep) :
    ∀ N (ds : List VDecl) (E : VEnv), E.WF' ds → VDecl.listRank ds ≤ N → E.Inj :=
  VEnv.WF'.inj_of hInd hQuot projStep

end LogRel
end Lean4Lean

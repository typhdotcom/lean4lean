import Lean4Lean.Theory.Typing.LogRel.BlockSound

/-!
# Soundness of the quotient's computation rule in the model
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat}

/-- The quotient's rule forward, under its binders, at any valuation: an interpretation of
`Quot.lift α r β f h (Quot.mk α r a)` interprets `f a`. -/
theorem quot_body_le (hM : ModelEnv env) (hq : env.defeqs quotDefEq) {u v : VLevel}
    {σ : Valuation} {y : TShape}
    (H : LE_Interp env σ y ((VExpr.const ``Quot.lift [u, v]).appN
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
        (VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0]])) :
    LE_Interp env σ y (.app (.bvar 2) (.bvar 0)) := by
  have hA : ConstArity env ``Quot.lift .quotLift 6 := .quotLift hq rfl
  rw [← spine_eq_appN] at H
  obtain ⟨n0, H0⟩ := H.spine_inv hM.roles (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; simp; omega)
  obtain ⟨rargs, y', hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = 6 := by rw [List.Forall₂.length_eq hra]; simp
  refine LE_Interp.mono hyy ?_
  cases hC with
  | bot => exact .bot
  | lam he hle => exact LE_Interp.mono (Const.lam_le_bot hM.roles he hle (hrl ▸ hA)) .bot
  | ext _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | delta _ h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | iota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | kIota h1 h2 h3 h4 => cases hM.roles (.recursor h1 h2 h4) hA
  | quotK h1 h2 h3 h4 h5 =>
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
    cases hra with | cons _ hra =>
    cases hra with | cons _ hra =>
    cases hra with | cons hf _ =>
    let .cons (f := f') (x := x0) h6 h7 h8 := h5
    let .nil h9 := h8
    exact .app (hf.mono h6) (.mono h7 .bot) h9
  | quot h1 h2 h3 h4 h5 h6 =>
    rename_i a x hh f β r α
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hra
    cases hra with | cons hx hra =>
    cases hra with | cons _ hra =>
    cases hra with | cons hf _ =>
    let .cons (f := f') (x := x0) h7 h8 h9 := h5
    let .nil h10 := h9
    refine .app (hf.mono h7) (.bvar ?_) h10
    refine h8.trans ?_
    -- the major premise's interpretation is a `Quot.mk` shape above `a`
    by_cases hne : IsStruct ``Quot.mk → WShape.ListNonZero [a]
    · have hB : ConstArity env ``Quot.mk .quotMk 3 := .quotMk hq rfl
      rw [← spine_eq_appN] at hx
      obtain ⟨n1, H1⟩ := hx.spine_inv hM.roles (fun r n' h => by
        cases hM.roles h hB; have := hB.determ h; simp; omega)
      obtain ⟨rargs', y'', hra', hyy', hC'⟩ := H1 n1 (Nat.le_refl _)
      have hrl' : rargs'.length = 3 := by rw [List.Forall₂.length_eq hra']; simp
      have hxy := h6.trans hyy'
      cases hC' with
      | quotMk g1 g2 g3 g4 g5 =>
        rename_i a' r' α'
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
          at hra'
        cases hra' with | cons ha' _ =>
        obtain ⟨-, hl⟩ := TShape.ctor'_le_ctor' hne (hxy.trans g5)
        cases hl with | cons hl _ =>
        exact hl.trans (bvar_iff.1 ha')
      | bot =>
        obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1
          (WShape.LE.of_T ((hxy.trans TShape.bot_eqv.1).trans TShape.bot_eqv.2)) hne
        simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
      | lam he hle =>
        have := Const.lam_le_bot hM.roles he hle (hrl' ▸ hB)
        obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1
          (WShape.LE.of_T ((hxy.trans this).trans TShape.bot_eqv.2)) hne
        simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
      | ext _ g1 g2 => cases hM.roles (.delta g1 g2) hB
      | delta _ g1 g2 => cases hM.roles (.delta g1 g2) hB
      | indTy g1 g2 => cases hM.roles (.indTy g1 g2) hB
      | ctor g1 g2 g3 g4 => cases hM.roles (.ctor g1 g2 g3 g4) hB
      | quotTy g1 g2 => cases hM.roles (.quotTy g1 g2) hB
      | quot g1 g2 => cases hM.roles (.quotLift g1 g2) hB
      | quotK g1 g2 => cases hM.roles (.quotLift g1 g2) hB
      | iota g1 g2 g3 g4 => cases hM.roles (.recursor g1 g2 g4) hB
      | kIota g1 g2 g3 g4 => cases hM.roles (.recursor g1 g2 g4) hB
    · have hz : a.1 ≤ .bot := Classical.byContradiction fun h' =>
        hne fun _ => ⟨a, .head _, h'⟩
      exact (WShape.LE.T (b := .bot) hz).trans TShape.bot_le'

/-- `Quot.mk`'s telescope, at the level `u`. -/
def quotMkTele (u : VLevel) : List VExpr :=
  [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]

omit [ShapeEnv] in
theorem quotMk_type (u : VLevel) : quotMkConst.type.instL [u] =
    .foralls (quotMkTele u) (.app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) := rfl

omit [ShapeEnv] in
theorem quot_type (u : VLevel) : quotConst.type.instL [u] =
    .foralls ((quotMkTele u).take 2) (.sort u) := rfl

omit [ShapeEnv] in
theorem quotMkTele_isTele {u : VLevel} {U : Nat} (hu : u.WF U) :
    VEnv.empty.IsTele U [] (quotMkTele u) := by
  have : VEnv.empty.IsTele 1 [] [.sort (.param 0),
      .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1] := by
    refine .cons ⟨_, by type_tac⟩ (.cons ⟨_, by type_tac⟩ (.cons ⟨_, by type_tac⟩ .nil))
  have := this.instL (ls := [u]) (U' := U) (by simpa using hu) (Γ := [])
  simpa [quotMkTele, VExpr.instL, VLevel.inst] using this

theorem quotMkTele_facts (hM : ModelEnv env) {u : VLevel} {U : Nat} (hu : u.WF U) :
    ∀ i (A : VExpr), (quotMkTele u)[i]? = some A → A.ClosedN i ∧
      ∃ v, SoundTy env ((quotMkTele u).take i).reverse A (.sort v) := by
  intro i A hA
  refine ⟨?_, ?_⟩
  · rcases i with _ | _ | _ | i <;> simp [quotMkTele] at hA <;> subst hA <;>
      simp [VExpr.ClosedN]
  · obtain ⟨v, h⟩ := IsTele.soundAt hM (envX := VEnv.empty) SoundHyps.empty
      ⟨nofun, nofun, nofun⟩ .empty (quotMkTele_isTele hu) trivial i A hA
    exact ⟨v, by simpa using h⟩

/-- `Quot.mk` applied to arguments typed at its telescope, where the quotient is not a
proposition, has a constructor shape as interpretation, with its argument above any given
interpretation of it. -/
theorem quotMk_realize (hM : ModelEnv env) (hq : env.defeqs quotDefEq)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hQc : env.constants ``Quot = some quotConst)
    {u : VLevel} {U : Nat} (hu : u.WF U) (hP : ¬u ≈ .zero)
    {Γ₀ Γ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ)
    {α r a T : VExpr}
    (hCS : MSpine env Γ ((VExpr.const ``Quot.mk [u]).appN [α, r, a]) T)
    {ys : List TShape} (hys : List.Forall₂ (fun y x => LE_Interp env ρ y x) ys [α, r, a]) :
    ∃ N, ∃ rf : List (WShape N), List.Forall₂ (fun y x => y ≤ x.T) (ys.drop 2) rf ∧
      List.Forall₂ (fun x A => LE_Interp env ρ x.T A) rf [a] ∧
      LE_Interp env ρ (WShape.ctor' ``Quot.mk rf).T
        ((VExpr.const ``Quot.mk [u]).appN [α, r, a]) := by
  have hrel : levelRel u = true := by simpa [levelRel] using hP
  have hQf := quotMkTele_facts hM (env := env) hu
  have hccl : (quotMkConst.type.instL [u]).ClosedN := (hM.closed.constType hmk).instL
  have hTSc := (MSpine.spine hM (Qs := quotMkTele u)
    (R := .app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) hQf
    (quotMk_type u ▸ hccl) (fun ci hci _ => by
      cases hmk.symm.trans hci; rw [quotMk_type]; exact .rfl)
    3 [α, r, a] rfl (by simp [quotMkTele]) hCS)
  rw [List.take_of_length_le (by simp [quotMkTele])] at hTSc
  -- values fitting it, above `ys`
  obtain ⟨PC, hP1, hP2, hP3⟩ := hTSc.1.exists_fits hM W (pushAll_consList hys)
  have hPCl : PC.length = 3 := List.Forall₂.length_eq hP1
  have hysl : ys.length = 3 := List.Forall₂.length_eq hys
  have hyP : List.Forall₂ (· ≤ ·) ys PC :=
    forall₂_le_of_pushAll (by omega) (fun i hi => hP3 i (by simp; omega))
  obtain ⟨L, hL1, hL2, hL3⟩ := Valuation.Fits.tele _ _ PC rfl (by simp [quotMkTele, hPCl]) hP2
  have hkey : ∀ b x, (b, x) ∈ L → x.HasType b := by
    intro b x h
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    have hj' : j < (quotMkTele u).length := by rw [hL2] at hj; exact hj
    exact (hL3 j b x _ (by rw [List.getElem?_eq_getElem hj, e])
      (List.getElem?_eq_getElem hj')).2.1
  have hcI : LE_Interp env ρ (piTele L TShape.bot) (quotMkConst.type.instL [u]) := by
    have := piTele_interp L (quotMkTele u) (σ := .nil) (r := TShape.bot)
      (B := .app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) hL2
      (fun j b x A h1 h2 => ⟨(hL3 j b x A h1 h2).1, (hL3 j b x A h1 h2).2.1⟩) .bot
    rw [← quotMk_type] at this
    exact (closed_iff hM.closed hccl).1 this
  let Lp := L.take 2
  let Lf := L.drop 2
  let cty := piTele Lf TShape.bot
  have hPi : PiAppS (piTele L TShape.bot) (Lp.map (·.2)) cty := by
    have := piTele_append_piAppS Lp Lf TShape.bot
    rwa [List.take_append_drop] at this
  have hkeyf : ∀ b x, (b, x) ∈ Lf → x.HasType b := fun b x h => hkey b x (List.mem_of_mem_drop h)
  have hctyT : cty.HasType (TShape.sort true) :=
    piTele_typed Lf hkeyf (WShape.HasType.T (n := 0) (.bot' .sort))
  have hLp : Lp.map (·.2) = PC.take 2 := by rw [← hL1, List.map_take]
  have hLf : Lf.map (·.2) = PC.drop 2 := by rw [← hL1, List.map_drop]
  -- a common level
  let K := max cty.1 (maxLvl PC)
  have hK1 : cty.1 ≤ K + 1 := by omega
  have hK2 : ∀ x ∈ PC, x.1 ≤ K + 1 := fun x h => by have := le_maxLvl h; omega
  let lft (x : TShape) : WShape (K+1) := x.2.lift (K+1)
  let params := (Lp.map (·.2)).map lft
  let rfN := (Lf.map (·.2)).map lft
  let ctyK : WShape (K+1) := cty.2.lift (K+1)
  let hd : IndHead := ⟨``Quot, 2, [``Quot.mk], [1]⟩
  have hplen : params.length = 2 := by simp [params, Lp, hL2, quotMkTele]
  have hrfl : rfN.length = 1 := by simp [rfN, Lf, hL2, quotMkTele]
  have hctysT : ∀ x ∈ [ctyK], x.HasType .type := by
    intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    have := (TShape.HasType.def hK1 (Nat.zero_le _)).1 hctyT
    simpa [TShape.sort, WShape.lift_sort] using this
  have hfit : WShape.FitsPi ctyK rfN := by
    have := piTele_fitsPi Lf TShape.bot K hkeyf hK1 (fun x hx => hK2 x (by
      rw [hLf] at hx; exact List.mem_of_mem_drop hx))
    show WShape.FitsPi ctyK ((Lf.map (·.2)).map lft)
    rw [List.map_map]; exact this
  have har : hd.arityOK ``Quot.mk rfN.length = true := by
    simp [IndHead.arityOK, hd, hrfl]
  obtain ⟨hctorTy, hindTy⟩ := WShape.ctor'_typed (N := K) (h := hd) (pre := params)
    (ctys := [ctyK]) (i := 0) (by simp [hd, hplen]) (by simp [hd]) rfl hctysT hfit har
  -- the arguments' shapes interpret them
  have hPa : List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) params [α, r] := by
    have h1 := List.forall₂_take' (k := 2) hP1
    rw [show [α, r, a].take 2 = [α, r] from rfl] at h1
    have := forall₂_lift (K := K+1) (fun x hx => hK2 x (List.mem_of_mem_take hx)) h1
    rwa [← hLp] at this
  have hFa : List.Forall₂ (fun x A => LE_Interp env ρ (WShape.T x) A) rfN [a] := by
    have h1 := List.forall₂_drop' (k := 2) hP1
    rw [show [α, r, a].drop 2 = [a] from rfl] at h1
    have := forall₂_lift (K := K+1) (fun x hx => hK2 x (List.mem_of_mem_drop hx)) h1
    rwa [← hLf] at this
  -- the quotient type at the arguments, with `Quot.mk`'s telescope at them
  have hCT : Const env ``Quot [u] (LE_Interp env ρ) params.reverse
      (WShape.indTy true hd (params ++ [ctyK])).T := by
    refine .quotTy (cty := ctyK) hq rfl rfl (by simp [hplen]) hmk hcI ?_ ?_
    · rw [List.reverse_reverse]
      refine PiAppS.mono_m (TShape.lift_eqv hK1).1 (PiAppS.mono_args ?_ hPi)
      have := forall₂_le_lift (K := K+1) (xs := Lp.map (·.2)) fun x hx => hK2 x (by
        rw [hLp] at hx; exact List.mem_of_mem_take hx)
      simpa [params, lft, List.map_map] using this
    · rw [hrel, List.reverse_reverse]; exact .rfl
  have hsortI : LE_Interp env ρ (WShape.sort (n := K+2) true).T (.sort u) := by
    refine .sort ?_
    rw [hrel]
    have := (TShape.lift_eqv (a := TShape.sort true) (m := K+2) (Nat.zero_le _)).1
    simpa [TShape.sort, WShape.lift_sort] using this
  have hTS : MSpine env Γ ((VExpr.const ``Quot [u]).appN [α, r]) (.sort u) := by
    have := MSpine.ofTele hM hQc rfl (Γ := Γ) (Qs := (quotMkTele u).take 2) (R := .sort u)
      (fun i A hA => by
        have hi : i < 2 := by
          have := (List.getElem?_eq_some_iff.1 hA).1; simp [quotMkTele] at this; omega
        rw [List.getElem?_take_of_lt hi] at hA
        rw [List.take_take, Nat.min_eq_left (by omega)]; exact hQf i A hA)
      (quot_type u ▸ (hM.closed.constType hQc).instL) (by rw [quot_type]; exact .rfl)
      2 [α, r] rfl (by simp [quotMkTele])
      (by rw [List.take_take, Nat.min_self]; exact hTSc.1.take 2)
    simpa [VExpr.subst] using this
  have hTyI : LE_Interp env ρ (WShape.indTy true hd (params ++ [ctyK])).T
      ((VExpr.const ``Quot [u]).appN [α, r]) := by
    rw [← spine_eq_appN] at hTS ⊢
    exact LE_Interp.apps_realize hM W (WShape.HasType.T hindTy) hsortI hTS
      ((List.Forall₂.reverse).2 hPa) hCT
  -- the constructor application
  have hCC : Const env ``Quot.mk [u] (LE_Interp env ρ) (params ++ rfN).reverse
      (WShape.ctor' ``Quot.mk rfN).T := by
    clear_value K
    obtain ⟨l1, l2, l3, rfl⟩ : ∃ l1 l2 l3, L = [l1, l2, l3] := by
      have : L.length = 3 := by simpa [quotMkTele] using hL2
      match L, this with | [l1, l2, l3], _ => exact ⟨l1, l2, l3, rfl⟩
    exact .quotMk hq rfl rfl hP .rfl
  have hCS' : MSpine env Γ ((VExpr.const ``Quot.mk [u]).appN [α, r, a])
      ((VExpr.const ``Quot [u]).appN [α, r]) := by
    refine hCS.retype (hTSc.2.trans ?_)
    simp [VExpr.subst, quotMkTele, VExpr.Subst.consList_apply]
    exact .rfl
  have hCI : LE_Interp env ρ (WShape.ctor' ``Quot.mk rfN).T
      ((VExpr.const ``Quot.mk [u]).appN [α, r, a]) := by
    rw [← spine_eq_appN] at hCS' ⊢
    exact LE_Interp.apps_realize hM W (WShape.HasType.T hctorTy) hTyI hCS'
      ((List.Forall₂.reverse).2 (by simpa using List.forall₂_append' hPa hFa)) hCC
  refine ⟨K + 1, rfN, ?_, hFa, hCI⟩
  have h1 := List.forall₂_drop' (k := 2) hyP
  rw [← hLf] at h1
  have h2 := forall₂_le_lift (K := K+1) (xs := Lf.map (·.2)) fun x hx => hK2 x (by
    rw [hLf] at hx; exact List.mem_of_mem_drop hx)
  have h3 := forall₂_le_trans h1 h2
  simp only [rfN, lft, List.map_map] at h3 ⊢
  exact List.forall₂_map_right_iff.1 (by simpa [List.map_map] using h3)

/-- The left body of the quotient's computation rule, at levels `u v`. -/
def quotL (u v : VLevel) : VExpr :=
  (VExpr.const ``Quot.lift [u, v]).appN [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
    (VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0]]

/-- The quotient's rule backward, under its binders, at a valuation fitting them: an
interpretation of `f a` interprets `Quot.lift α r β f h (Quot.mk α r a)`. -/
theorem quot_body_ge (hM : ModelEnv env) (hq : env.defeqs quotDefEq)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hQc : env.constants ``Quot = some quotConst)
    {u v : VLevel} {U : Nat} (hu : u.WF U)
    {Γ₀ Γ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ) {B : VExpr}
    (hLS : StrongSound env U Γ (quotL u v) B) (hRT : SoundTy env Γ (.app (.bvar 2) (.bvar 0)) B)
    {y : TShape} (hy : LE_Interp env ρ y (.app (.bvar 2) (.bvar 0))) :
    LE_Interp env ρ y (quotL u v) := by
  obtain ⟨y'', b, hyle, hy'', hb, hty⟩ := hRT W hy
  suffices LE_Interp env ρ y'' (quotL u v) from this.mono hyle
  -- the major premise, typed along `Quot.mk`'s telescope
  have hLS' := hLS
  rw [show quotL u v = .app ((VExpr.const ``Quot.lift [u, v]).appN
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1])
      ((VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0]) from rfl] at hLS'
  obtain ⟨A, -, -, -, -, hmaj, -⟩ := hLS'.app_inv
  have hMS := hmaj.mspine'
  have hccl : (quotMkConst.type.instL [u]).ClosedN := (hM.closed.constType hmk).instL
  obtain ⟨hTS, -⟩ := MSpine.spine hM (Qs := quotMkTele u)
    (R := .app (.app (.const ``Quot [u]) (.bvar 2)) (.bvar 1)) (quotMkTele_facts hM hu)
    (quotMk_type u ▸ hccl) (fun ci hci _ => by
      cases hmk.symm.trans hci; rw [quotMk_type]; exact .rfl)
    3 _ rfl (by simp [quotMkTele]) hMS
  have hSp : MSpine env Γ (spine ``Quot.lift [u, v]
      [(VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0],
        .bvar 1, .bvar 2, .bvar 3, .bvar 4, .bvar 5]) B := by
    have := hLS.mspine'; rw [← spine_eq_appN] at this; exact this
  rw [show quotL u v = spine ``Quot.lift [u, v]
      [(VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0],
        .bvar 1, .bvar 2, .bvar 3, .bvar 4, .bvar 5] by
    rw [quotL, ← spine_eq_appN]; rfl]
  cases hy'' with
  | bot => exact .bot
  | app hf ha' hle =>
  rename_i n f a
  have hfle : f.T ≤ ρ 2 := bvar_iff.1 hf
  by_cases hu0 : u ≈ .zero
  · -- the quotient is a proposition: `Quot.lift` reduces on any proof
    have hα : SoundTy env Γ (.bvar 5) (.sort u) := by
      have := hTS.typed 0 (.sort u) (.bvar 5) rfl rfl
      simpa [VExpr.subst] using this
    have hat : SoundTy env Γ (.bvar 0) (.bvar 5) := by
      have := hTS.typed 2 (.bvar 1) (.bvar 0) rfl rfl
      simpa [VExpr.subst, VExpr.Subst.consList_apply] using this
    have haBot : a.T ≤ TShape.bot := (bvar_iff.1 ha').trans
      (hat.le_bot hα (by simp [levelRel, hu0]) W (.bvar .rfl))
    let K := max (ρ 1).1 (max (ρ 2).1 (max (ρ 3).1 (max (ρ 4).1 (ρ 5).1)))
    have h1 : (ρ 1).1 ≤ K := by omega
    have h2 : (ρ 2).1 ≤ K := by omega
    have h3 : (ρ 3).1 ≤ K := by omega
    have h4 : (ρ 4).1 ≤ K := by omega
    have h5 : (ρ 5).1 ≤ K := by omega
    have hC : Const env ``Quot.lift [u, v] (LE_Interp env ρ)
        [WShape.bot, (ρ 1).2.lift K, (ρ 2).2.lift K, (ρ 3).2.lift K, (ρ 4).2.lift K,
          (ρ 5).2.lift K] y'' :=
      .quotK hq rfl rfl hu0 (.cons (f := f) (x := a) (hfle.trans (TShape.lift_eqv h2).2) haBot
        (.nil hle))
    exact LE_Interp.apps_realize hM W hty hb hSp
      (.cons .bot (.cons (.bvar (TShape.lift_eqv h1).1) (.cons (.bvar (TShape.lift_eqv h2).1)
        (.cons (.bvar (TShape.lift_eqv h3).1) (.cons (.bvar (TShape.lift_eqv h4).1)
          (.cons (.bvar (TShape.lift_eqv h5).1) .nil)))))) hC
  · -- otherwise the major premise has a `Quot.mk` shape above the argument
    obtain ⟨N, rf, hrf, hrfI, hx⟩ := quotMk_realize hM hq hmk hQc hu hu0 W hMS
      (ys := [ρ 5, ρ 4, a.T]) (.cons (.bvar .rfl) (.cons (.bvar .rfl) (.cons ha' .nil)))
    obtain ⟨a', rfl⟩ : ∃ a', rf = [a'] := by
      cases hrfI with | cons _ h => cases h; exact ⟨_, rfl⟩
    have haa : a.T ≤ a'.T := by cases hrf with | cons h _ => exact h
    let K := max N (max (ρ 1).1 (max (ρ 2).1 (max (ρ 3).1 (max (ρ 4).1 (ρ 5).1))))
    have hN : N ≤ K := by omega
    have h1 : (ρ 1).1 ≤ K + 1 := by omega
    have h2 : (ρ 2).1 ≤ K + 1 := by omega
    have h3 : (ρ 3).1 ≤ K + 1 := by omega
    have h4 : (ρ 4).1 ≤ K + 1 := by omega
    have h5 : (ρ 5).1 ≤ K + 1 := by omega
    have hxK : LE_Interp env ρ (WShape.ctor' ``Quot.mk [a'.lift K]).T
        ((VExpr.const ``Quot.mk [u]).appN [.bvar 5, .bvar 4, .bvar 0]) := by
      have := hx.lift (n := K + 1) (by simp; omega)
      simpa [WShape.lift_ctor' hN] using this
    have hC : Const env ``Quot.lift [u, v] (LE_Interp env ρ)
        [WShape.ctor' ``Quot.mk [a'.lift K], (ρ 1).2.lift (K+1), (ρ 2).2.lift (K+1),
          (ρ 3).2.lift (K+1), (ρ 4).2.lift (K+1), (ρ 5).2.lift (K+1)] y'' :=
      .quot hq rfl rfl hu0 (.cons (f := f) (x := a) (hfle.trans (TShape.lift_eqv h2).2)
        (haa.trans (TShape.lift_eqv (a := a'.T) (by simp; omega)).2)
        (.nil hle)) .rfl
    exact LE_Interp.apps_realize hM W hty hb hSp
      (.cons hxK (.cons (.bvar (TShape.lift_eqv h1).1) (.cons (.bvar (TShape.lift_eqv h2).1)
        (.cons (.bvar (TShape.lift_eqv h3).1) (.cons (.bvar (TShape.lift_eqv h4).1)
          (.cons (.bvar (TShape.lift_eqv h5).1) .nil)))))) hC

omit [ShapeEnv] in
/-- The quotient's computation rule at levels `u v`, as lambdas over its binders. -/
theorem quotDefEq_instL (u v : VLevel) :
    quotDefEq.lhs.instL [u, v] =
      .lams ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (VExpr.instL [u, v])) (quotL u v) ∧
    quotDefEq.rhs.instL [u, v] =
      .lams ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (VExpr.instL [u, v])) (.app (.bvar 2) (.bvar 0)) ∧
    quotDefEq.type.instL [u, v] =
      .foralls ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (VExpr.instL [u, v])) (.bvar 3) :=
  ⟨rfl, rfl, rfl⟩

/-- The quotient's computation rule is sound in the model of a well-formed environment. -/
theorem quotRuleSound (hM : ModelEnv env) (henv : env.WF) : QuotRuleSound env := by
  intro hq U Γ ls hls hlen h1 h2 _ _
  obtain ⟨hmk, hQc⟩ : env.constants ``Quot.mk = some quotMkConst ∧
      env.constants ``Quot = some quotConst := by
    have H := henv.ruleKind hq
    generalize e : quotDefEq = df at H
    cases H with
    | quot _ h2 _ h4 => exact ⟨h2, h4⟩
    | defn ci _ =>
      have := congrArg VDefEq.lhs e
      rw [QuotRed.quotDefEq_eq] at this
      simp [VDefVal.toDefEq, QuotRed.liftBinders] at this
    | iota _ hm =>
      subst e
      simp only [VInductDecl.iotaRules, List.mem_map] at hm
      obtain ⟨_, -, hm⟩ := hm
      have := congrArg VDefEq.type hm
      rw [QuotRed.quotDefEq_eq] at this
      simp only [VInductDecl.iotaRule] at this
      exact nomatch (VExpr.foralls_inj' (fun _ _ h => by cases h) (fun _ _ h => by cases h) this).2
  have hcl := henv.ordered.closed.2 hq
  match ls, hlen with
  | [u, v], _ =>
  have hu : u.WF U := hls u (by simp)
  obtain ⟨hL, hR, hTy⟩ := quotDefEq_instL u v
  have hcl1 := hcl.1.1.instL (ls := [u, v]); have hcl2 := hcl.2.1.instL (ls := [u, v])
  rw [hL] at h1 hcl1 ⊢; rw [hR] at h2 hcl2 ⊢; rw [hTy] at h1 h2
  refine SoundEq.closed hM hcl1 hcl2 ?_
  obtain ⟨BL, hTel, hLS, hBL⟩ := h1.lams_inv
  obtain ⟨BR, -, hRS, hBR⟩ := h2.lams_inv
  have hBB := SoundEq.foralls_inv hM hTel (hBL.trans hBR.symm)
  simp only [List.append_nil] at hLS hRS hBB
  refine SoundEq.lams_fit hTel fun {Γ₀ ρ} xs W0 hF W' y => ⟨fun hy => ?_, fun hy => ?_⟩
  · exact quot_body_le hM hq hy
  · exact quot_body_ge hM hq hmk hQc hu (by simpa using W') hLS (hRS.sound.defeq_r hBB.symm) hy

omit [ShapeEnv] [AxInterp] in
/-- The model of a well-formed environment, with its own structures, is sound for its typing
rules. -/
theorem _root_.Lean4Lean.VEnv.WF.modelSound {env : VEnv} (henv : env.WF)
    (H : env.IsDefEqStrong U Γ M N A) :
    @StrongSoundEq env.shapeEnv (@AxInterp.none env.shapeEnv) env U Γ M N A :=
  letI := env.shapeEnv
  henv.strongSound (quotRuleSound (henv.modelEnv AxOK.none) henv)
    (henv.blockSound (henv.modelEnv AxOK.none)) H

end LogRel
end Lean4Lean

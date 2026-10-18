import Lean4Lean.Theory.Typing.LogRel.Realize

/-!
# Structure eta is sound in the model

A term of a structure type is interpreted by `bot` or by a constructor shape of the structure's
constructor, since its interpretations are typed at the structure's `indTy` shape. The fields of
that shape interpret the projections, so the constructor applied to the projections has it as an
interpretation; conversely, the projections' interpretations join to an interpretation of the term.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv}

/-- A shape typed at an interpretation of an inductive type at its arity is `bot` or a
constructor shape of one of the type's constructors. -/
theorem typed_indTy_inv (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T)
    {ls : List VLevel} {args : List VExpr}
    (hargs : args.length = d.params.length + T.indices.length) {ρ : Valuation}
    {m a : TShape} (hty : m.HasType a) (ha : LE_Interp env ρ a ((VExpr.const s ls).appN args)) :
    m ≤ TShape.bot ∨ ∃ N, ∃ c' ∈ T.ctors, ∃ l : List (WShape N),
      (IsStruct c'.name → WShape.ListNonZero l) ∧ l.length = c'.fields.length ∧
      m ≤ (WShape.ctor' c'.name l).T ∧ (WShape.ctor' c'.name l).T ≤ m := by
  rw [← spine_eq_appN] at ha
  obtain ⟨n0, H0⟩ := ha.spine_inv hM.roles (fun r n' h => by
    cases hM.roles h (ConstArity.indTy hs hT)
    rw [(ConstArity.indTy hs hT).determ h] at *; simp [hargs])
  obtain ⟨K, hK0, hK1, hK2⟩ : ∃ K, n0 ≤ K + 1 ∧ m.1 ≤ K + 1 ∧ a.1 ≤ K + 1 :=
    ⟨max n0 (max m.1 a.1), by omega, by omega, by omega⟩
  obtain ⟨rargs, y, hra, hay, hC⟩ := H0 (K + 1) hK0
  have hrl : rargs.length = d.params.length + T.indices.length := by
    rw [List.Forall₂.length_eq hra, List.length_reverse, hargs]
  have hty' := (TShape.HasType.def (m := K+1+1) (by omega) (by omega)).1 hty
  have hmK : m ≤ (m.2.lift (K+1+1)).T ∧ (m.2.lift (K+1+1)).T ≤ m :=
    ⟨(TShape.lift_eqv (by omega)).2, (TShape.lift_eqv (by omega)).1⟩
  have hbot (h : m.2.lift (K+1+1) = .bot) : m ≤ TShape.bot := by
    refine hmK.1.trans ?_; rw [h]; exact TShape.bot_eqv.1
  obtain hy | ⟨ctys, -, -, hyY⟩ := Const.indTy_inv hM.roles hs hT hrl hC
  · have := (TShape.LE.def (m := K+1+1) (b := TShape.bot) (by omega) (Nat.zero_le _)).1
      (hay.trans hy)
    simp only [TShape.bot, WShape.T, WShape.lift_bot] at this
    rw [WShape.le_bot.1 this] at hty'
    exact .inl (hbot hty'.bot_r)
  have haY := (TShape.LE.def (m := K+1+1) (by omega) (by simp)).1 (hay.trans hyY)
  simp only [WShape.T, WShape.lift_self] at haY
  obtain h | ⟨l'', h1, -⟩ := WShape.le_indTy.1 haY
  · rw [h] at hty'; exact .inl (hbot hty'.bot_r)
  rw [h1] at hty'
  generalize m.2.lift (K+1+1) = m' at hty' hmK hbot
  generalize eqa : WShape.indTy (d.rel ls) _ l'' = A at hty'
  cases hty'.unfold with
  | bot => exact .inl (hbot rfl)
  | @ctor _ I as l c' wf H =>
    right
    obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 eqa
    obtain ⟨i, hi⟩ : ∃ i, (T.ctors.map (·.name)).idxOf? c' = some i := by
      unfold Shape.ctorOK Shape.ctorTy at H
      revert H; cases (T.ctors.map (·.name)).idxOf? c' <;> simp
    obtain ⟨hil, hic, -⟩ := List.idxOf?_eq_some_iff.1 hi
    have hil' : i < T.ctors.length := by simpa using hil
    have har : (T.ctors.map (·.fields.length))[i]? = some l.length := by
      unfold Shape.ctorOK Shape.ctorTy at H
      simp only [hi, Option.map_some, Bool.and_eq_true_iff] at H
      have := H.2.2
      simpa [IndHead.arityOK, hi] using this
    rw [List.getElem?_map, List.getElem?_eq_getElem hil'] at har
    simp only [List.getElem_map] at hic
    subst hic
    refine ⟨K + 1, T.ctors[i], List.getElem_mem hil', l, wf,
      (Option.some.inj har).symm, ?_, ?_⟩
    · rw [← WShape.ctor_eq_ctor' (h := wf)]; exact hmK.1
    · rw [← WShape.ctor_eq_ctor' (h := wf)]; exact hmK.2
  | _ => simp [WShape.ext_iff, WShape.indTy, WShape.sort, WShape.forallE, Shape.sort] at eqa

/-- A proof's interpretations are `bot`, at a sort the model reads as a proposition. -/
theorem StrongSound.proof_le_bot' {U : Nat} {Γ₀ Γ : List VExpr} {ρ : Valuation} {a A : VExpr}
    {l : VLevel} (H1 : StrongSound env U Γ a A) (H2 : StrongSound env U Γ A (.sort l))
    (hr : levelRel l = false) (W : Valuation.Fits env Γ₀ Γ ρ) {m : TShape}
    (h : LE_Interp env ρ m a) : m ≤ TShape.bot := by
  obtain ⟨_, _, a1, -, a3, a4⟩ := H1.sound W h
  obtain ⟨_, _, b1, -, b3, b4⟩ := H2.sound W a3
  have b4' := TShape.HasType.mono_r (by simpa [hr] using b3.le_sort) .sort b4
  exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))

omit [AxInterp] in
/-- Constructor shapes with fields below are below. -/
theorem TShape.ctor'_mono {c : Name} {l : List (WShape n)} {l' : List (WShape n')}
    (h : List.Forall₂ (fun x y => x.T ≤ y.T) l l') :
    (WShape.ctor' c l).T ≤ (WShape.ctor' c l').T := by
  have hK1 : n ≤ max n n' := Nat.le_max_left ..
  have hK2 : n' ≤ max n n' := Nat.le_max_right ..
  rw [TShape.LE.def (m := max n n' + 1) (by simp; omega) (by simp; omega)]
  simp only [WShape.T, WShape.lift_ctor' hK1, WShape.lift_ctor' hK2]
  refine WShape.ctor'_le_ctor' ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.Forall₂.imp (fun x y hxy =>
    (TShape.LE.def (m := max n n') (by simp; omega) (by simp; omega)).1 hxy) h

/-- Finitely many interpretations of a term are below one interpretation of it. -/
theorem exists_interp_above (hM : ModelEnv env) {ρ : Valuation} {e : VExpr} :
    ∀ {S : List TShape}, (∀ x ∈ S, LE_Interp env ρ x e) →
      ∃ M, LE_Interp env ρ M e ∧ ∀ x ∈ S, x ≤ M
  | [], _ => ⟨_, LE_Interp.bot (n := 0), nofun⟩
  | x :: S, h => by
    obtain ⟨M, hM1, hM2⟩ := exists_interp_above hM fun y hy => h y (.tail _ hy)
    have hx := h x (.head _)
    have hJ := (TShape.Join.mk (compat hM hx hM1)).le
    exact ⟨_, join' hM hx hM1, fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hJ.1
      · exact (hM2 y hy).trans hJ.2⟩

omit [ShapeEnv] in
theorem getElem?_projs {s : Name} {k j : Nat} {e : VExpr} :
    (VExpr.projs s k e)[j]? = if j < k then some (.proj s j e) else none := by
  simp only [VExpr.projs]
  split <;> simp_all

section projEta
variable (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hcs : T.ctors = [c]) (hI0 : T.indices = [])
    (hTW : T.WF envT d) (hcW : c.WF envT d T) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    {Γ : List VExpr} {ls : List VLevel} {As : List VExpr} {e : VExpr} {u : VLevel} {U : Nat}
    (hls : ∀ l ∈ ls, l.WF U) (hAs : As.length = d.params.length)
    (hTS : StrongSound env U Γ (.appN (.const s ls) As) (.sort u))
    (heS : StrongSound env U Γ e (.appN (.const s ls) As))
    (hCS : StrongSound env U Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
      (.appN (.const s ls) As))
    {Γ₀ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ)
include hM hX hle hO hs hT hcs hI0 hTW hcW hPT hcT hcC hls hAs hTS heS hCS W

/-- An interpretation of a structure-typed term is `bot` or a constructor shape interpreting it,
whose fields interpret the projections. -/
theorem struct_interp_inv {m : TShape} (hm : LE_Interp env ρ m e) :
    m ≤ TShape.bot ∨ ¬d.PropAt ls ∧ ∃ N, ∃ l : List (WShape N), l.length = c.fields.length ∧
      m ≤ (WShape.ctor' c.name l).T ∧ LE_Interp env ρ (WShape.ctor' c.name l).T e := by
  have hn : (As ++ ([] : List VExpr)).length = d.params.length + T.indices.length := by
    simp [hAs, hI0]
  have hTS' : StrongSound env U Γ ((VExpr.const s ls).appN (As ++ [])) (.sort u) := by
    simpa using hTS
  by_cases hP : d.PropAt ls
  · obtain ⟨-, hsort⟩ := typeSpine hM hX hle hO hTW hPT hcT hls hn hTS'.mspine'
    have hr : levelRel u = false := by
      rw [SoundEq.sort.1 hsort, levelRel_congr hP, levelRel_zero]
    exact .inl (heS.proof_le_bot' hTS hr W hm)
  obtain ⟨m', a, h1, h2, h3, h4⟩ := heS.sound W hm
  obtain ⟨a', b, g1, g2, g3, g4⟩ := hTS.sound W h3
  have ha' : a'.HasType (.sort (levelRel u)) := .mono_r g3.le_sort .sort g4
  have hm' : m'.HasType a' := .mono_r g1 ha' h4
  rcases typed_indTy_inv hM hs hT (by simpa using hn) hm' g2 with
    hb | ⟨N, c', hc', l, -, hl, hl1, hl2⟩
  · exact .inl (h1.trans hb)
  obtain rfl : c' = c := by simpa [hcs] using hc'
  exact .inr ⟨hP, N, l, hl, h1.trans hl1, LE_Interp.mono hl2 h2⟩

/-- Structure eta, forward: an interpretation of a structure-typed term interprets its
constructor applied to its projections. -/
theorem projEta_le {m : TShape} (hm : LE_Interp env ρ m e) :
    LE_Interp env ρ m (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e)) := by
  rcases struct_interp_inv hM hX hle hO hs hT hcs hI0 hTW hcW hPT hcT hcC hls hAs hTS heS hCS W
    hm with hb | ⟨hP, N, l, hl, hml, hce⟩
  · exact LE_Interp.mono hb .bot
  let ys : List TShape := As.map (fun _ => TShape.bot) ++ l.map (·.T)
  have hys : List.Forall₂ (fun y x => LE_Interp env ρ y x) ys
      (As ++ VExpr.projs s c.fields.length e) := by
    refine List.forall₂_append' ?_ ?_
    · refine List.forall₂_of_getElem? (by simp) fun j y x hy hx => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
      obtain ⟨_, -, rfl⟩ := hy
      exact LE_Interp.bot (n := 0)
    · refine List.forall₂_of_getElem? (by simp [hl]) fun j y x hy hx => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [getElem?_projs] at hx
      split at hx <;> cases hx
      exact .proj hs hT hcs hce hy' .rfl
  have hci : T.ctors[0]? = some c := by simp [hcs]
  have hidx : (T.ctors.map (·.name)).idxOf? c.name = some 0 := by simp [hcs]
  have hTS' : StrongSound env U Γ ((VExpr.const s ls).appN (As ++ [])) (.sort u) := by
    simpa using hTS
  have hCS' : StrongSound env U Γ ((VExpr.const c.name ls).appN
      (As ++ VExpr.projs s c.fields.length e)) ((VExpr.const s ls).appN (As ++ [])) := by
    simpa using hCS
  obtain ⟨N', rf, hrf, -, hCI⟩ := ctorApp_realize hM hX hle hO hs hT hci hidx hTW hcW hPT hcT hcC
    hls hP W hAs (by simp) (by simp [hI0]) hTS'.mspine' hCS'.mspine' hys
  have : ys.drop d.params.length = l.map (·.T) := by simp [ys, hAs]
  rw [this, List.forall₂_map_left_iff] at hrf
  exact LE_Interp.mono (hml.trans (TShape.ctor'_mono hrf)) hCI

/-- Structure eta, backward: an interpretation of the constructor applied to the projections
interprets the term, when the constructor's shape collapses with its fields. -/
theorem projEta_ge (hst : IsStruct c.name = true) {m : TShape}
    (hm : LE_Interp env ρ m (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))) :
    LE_Interp env ρ m e := by
  rcases ctorApp_inv hM hs hT (by simp [hcs]) hAs (by simp) hm with hb | ⟨hP, k, rf, hrf, hmle⟩
  · exact LE_Interp.mono hb .bot
  have hrfl : rf.length = c.fields.length := by simpa using List.Forall₂.length_eq hrf
  -- a nonzero field's interpretation comes from a constructor shape interpreting `e`
  have hfield : ∀ (j : Nat) (x : WShape k), rf[j]? = some x → ¬x.T ≤ TShape.bot →
      ∃ N, ∃ fs : List (WShape N), ∃ x' : WShape N, LE_Interp env ρ (WShape.ctor' c.name fs).T e ∧
        fs[j]? = some x' ∧ x.T ≤ x'.T := by
    intro j x hx hnz
    have hj : j < c.fields.length := hrfl ▸ (List.getElem?_eq_some_iff.1 hx).1
    have hp := hrf.getElem?' hx (by rw [getElem?_projs, if_pos hj])
    generalize hX : x.T = X at hp
    cases hp with
    | bot => exact absurd (hX ▸ TShape.bot_eqv.1) hnz
    | proj hs' hT' hcs' hce hx' hmx =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs'))
      obtain rfl := Option.some.inj (hT.symm.trans hT')
      obtain rfl := (List.cons.inj (hcs.symm.trans hcs')).1
      exact ⟨_, _, _, hce, hx', hX ▸ hmx⟩
  -- a nonzero field makes its constructor shape nonzero
  have hnz' : ∀ {N : Nat} {fs : List (WShape N)} {j : Nat} {x' : WShape N} (x : WShape k), fs[j]? = some x' →
      x.T ≤ x'.T → ¬x.T ≤ TShape.bot → WShape.ListNonZero fs := fun x hx' hxx hnz =>
    ⟨_, List.mem_of_getElem? hx', fun h => hnz (hxx.trans ((WShape.LE.T h).trans
      TShape.bot_eqv.1))⟩
  -- one interpretation of `e` above all of them
  have hacc : ∀ n : Nat, ∃ M, LE_Interp env ρ M e ∧ ∀ j < n, ∀ x : WShape k, rf[j]? = some x → ¬x.T ≤ TShape.bot →
      ∃ N, ∃ fs : List (WShape N), ∃ x' : WShape N, (WShape.ctor' c.name fs).T ≤ M ∧
        fs[j]? = some x' ∧ x.T ≤ x'.T := by
    intro n
    induction n with
    | zero => exact ⟨_, LE_Interp.bot (n := 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨M, hM1, hM2⟩ := ih
      by_cases h : ∃ x, rf[n]? = some x ∧ ¬x.T ≤ TShape.bot
      · obtain ⟨x, hx, hnz⟩ := h
        obtain ⟨N, fs, x', hce, hx', hxx⟩ := hfield n x hx hnz
        have hJ := (TShape.Join.mk (compat hM hce hM1)).le
        refine ⟨_, join' hM hce hM1, fun j hj y hy hny => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · obtain ⟨N', fs', y', h1, h2, h3⟩ := hM2 j hj y hy hny
          exact ⟨N', fs', y', h1.trans hJ.2, h2, h3⟩
        · obtain rfl := Option.some.inj (hy.symm.trans hx)
          exact ⟨N, fs, x', hJ.1, hx', hxx⟩
      · refine ⟨M, hM1, fun j hj y hy hny => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hM2 j hj y hy hny
        · exact absurd ⟨y, hy, hny⟩ h
  obtain ⟨M, hM1, hM2⟩ := hacc rf.length
  rcases struct_interp_inv hM hX hle hO hs hT hcs hI0 hTW hcW hPT hcT hcC hls hAs hTS heS hCS W
    hM1 with hb | ⟨-, N, l, hl, hMl, hle'⟩
  · -- every field is `bot`, so the constructor shape collapses
    have hz : ¬WShape.ListNonZero rf := by
      rintro ⟨x, hx, hnz⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hnz2 : ¬rf[j].T ≤ TShape.bot := fun h =>
        hnz (WShape.LE.of_T (h.trans TShape.bot_eqv.2))
      obtain ⟨N, fs, x', h1, h2, h3⟩ := hM2 j hj _ (List.getElem?_eq_getElem hj) hnz2
      obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1 (WShape.LE.of_T
        ((h1.trans hb).trans TShape.bot_eqv.2)) (fun _ => hnz' _ h2 h3 hnz2)
      simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
    have : WShape.ctor' c.name rf = .bot := by
      unfold WShape.ctor'; rw [dif_neg (fun h => hz (h hst))]
    rw [this] at hmle
    exact LE_Interp.mono (hmle.trans TShape.bot_eqv.1) .bot
  refine LE_Interp.mono (hmle.trans (TShape.ctor'_mono ?_)) hle'
  refine List.forall₂_of_getElem? (by rw [hrfl, hl]) fun j x y hx hy => ?_
  by_cases hnz : x.T ≤ TShape.bot
  · exact hnz.trans TShape.bot_le
  obtain ⟨N', fs, x', h1, h2, h3⟩ :=
    hM2 j (List.getElem?_eq_some_iff.1 hx).1 x hx hnz
  obtain ⟨-, hfl⟩ := TShape.ctor'_le_ctor' (fun _ => hnz' x h2 h3 hnz) (h1.trans hMl)
  exact h3.trans (hfl.getElem?' h2 hy)

end projEta

/-- The projection rules are sound in the model for each type of a block, given that the model is
sound for the environment the block was declared in. -/
theorem projSoundAt_block (hM : ModelEnv env) {E₁ E₂ : VEnv} (hE₁ : E₁.WF) {d : VInductDecl}
    (hd : d.WF E₁) (h1 : E₁.addInduct d = some E₂) (hle : E₂ ≤ env)
    (hX₁ : SoundHyps E₁ env) {U : Nat} {s : Name} {t : Nat} (hs₂ : E₂.inducts s = some (d, t))
    (hname : ∃ T, d.types[t]? = some T ∧ T.name = s) : ProjSoundAt env U s d t := by
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
  obtain ⟨envT, hTs, envC, hC, envR, hR', hB'⟩ := h1
  have hs : env.inducts s = some (d, t) := hle.inducts hs₂
  obtain ⟨T, hT, rfl⟩ := hname
  have hleT : envT ≤ env := (VEnv.addConstList_le hC).trans <| (VEnv.addConstList_le hR').trans <|
    (VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB')).trans hle
  have hX : SoundHyps envT env := hX₁.mono (fun h => (VEnv.addConstList_defeqs' hTs) ▸ h)
    (fun h => (VEnv.addConstList_inducts hTs) ▸ h)
  have hO : envT.Ordered := (VEnv.WF.addConstList hE₁ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hd.types T hT).1) hTs).ordered
  have hle₁ : E₁ ≤ envT := VEnv.addConstList_le hTs
  have hTm : T ∈ d.allTypes := List.mem_append_left _ (List.mem_of_getElem? hT)
  obtain ⟨hTW, hCW⟩ := hd.ctors envT hTs T hTm
  have hPT : envT.IsTele d.uvars [] d.params := hd.params.mono hle₁
  have hcT : env.constants T.name = some ⟨d.uvars, T.type⟩ :=
    hleT.constants <| VEnv.addConstList_constants_of_mem hTs
      (List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩)
  have hcC {c : VConstructor} (hc : c ∈ T.ctors) :
      env.constants c.name = some ⟨d.uvars, c.type⟩ :=
    ((VEnv.addConstList_le hR').trans <| (VEnv.addDefEqList_le.trans (VEnv.addBlock_le hB')).trans
      hle).constants <| VEnv.addConstList_constants_of_mem hC
      (List.mem_map.2 ⟨(t, c), VInductDecl.mem_ctors_iff.2 ⟨T, hT, hc⟩, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro Γ T' c k f ls As I e u hT' hcs hf hls hlen hAs hI _ hS he _
    obtain rfl := Option.some.inj (hT.symm.trans hT')
    exact projSound_at hM hE₁ hd hTs hleT hX hs hT rfl hcs hf hls hlen hAs hI hS he
  · intro Γ T' c k f fs a ls As I u hT' hcs hf ha hls _ hAs hfs hI hPA hTS hCS hPT' haS
    obtain rfl := Option.some.inj (hT.symm.trans hT')
    have hcW := hCW c (by simp [hcs])
    intro Γ₀ ρ W m
    exact ⟨fun hm => projIota_le hM hs hT hcs hAs hfs ha hm,
      projIota_ge hM hX hleT hO hs hT hcs hTW hcW hPT hcT (hcC (by simp [hcs])) hf ha hls hAs hfs
        hI hPA hTS hCS hPT' haS W⟩
  · intro Γ T' c ls As e u hT' hcs hI0 hrec hls _ hAs hTS heS hCS
    obtain rfl := Option.some.inj (hT.symm.trans hT')
    have hcW := hCW c (by simp [hcs])
    intro Γ₀ ρ W m
    exact ⟨projEta_le hM hX hleT hO hs hT hcs hI0 hTW hcW hPT hcT (hcC (by simp [hcs])) hls hAs
        hTS heS hCS W,
      projEta_ge hM hX hleT hO hs hT hcs hI0 hTW hcW hPT hcT (hcC (by simp [hcs])) hls hAs
        hTS heS hCS W (hM.structOf _ ⟨_, _, _, _, _, hs, hT, hcs, hI0, hrec, rfl⟩)⟩

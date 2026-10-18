import Lean4Lean.Theory.Typing.LogRel.SoundLemmas
import Lean4Lean.Theory.Typing.LogRel.RuleBodies

/-!
# Projections are sound in the model

A projection's interpretation is a field of a constructor shape interpreting the structure term.
That shape is typed at the structure type's `indTy` shape, so its fields fit the constructor's
field telescope, which the model computes from the constructor's declared type at the parameters.
The declared field domains have the same interpretations as the fields' views, which the
projection's type is stated with, by the model's soundness for the environment the block was
declared in.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv}

/-- A constructor shape below a shape typed at `a`: the shape is a constructor shape of the same
constructor with larger fields, and `a` an inductive type shape it fits. -/
theorem WShape.ctor_typed {c : Name} {l : List (WShape n)} (hne : IsStruct c → WShape.ListNonZero l)
    {m a : WShape (n+1)} (hle : WShape.ctor' c l ≤ m) (hty : m.HasType a) :
    ∃ l' h' I as, m = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l' ∧ a = WShape.indTy true I as ∧
      Shape.ctorOK Shape.hasType I (as.map (·.1)) c (l'.map (·.1)) = true := by
  obtain ⟨l', h', rfl, hl⟩ := WShape.ctor'_le.1 hle hne
  generalize eq : WShape.ctor c l' h' = m at hty
  cases hty.unfold with
  | ctor H =>
    obtain ⟨rfl, rfl⟩ := WShape.ctor.inj.1 eq
    exact ⟨_, _, _, _, rfl, hl, rfl, H⟩
  | lam => unfold WShape.lam' at eq; split at eq <;> cases eq
  | _ => cases eq

/-- A constructor shape fitting an inductive type shape fits the constructor's telescope. -/
theorem WShape.fitsPi_of_ctorOK {I : IndHead} {as l : List (WShape (n+1))} {c : Name} {i : Nat}
    (H : Shape.ctorOK Shape.hasType I (as.map (·.1)) c (l.map (·.1)) = true)
    (hi : I.ctors.idxOf? c = some i) : WShape.FitsPi (as.getD (I.nargs + i) .bot) l := by
  unfold Shape.ctorOK Shape.ctorTy at H
  simp only [hi, Option.map_some, Bool.and_eq_true] at H
  have e : (as.map (·.1)).getD (I.nargs + i) Shape.bot = (as.getD (I.nargs + i) .bot).1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases as[I.nargs + i]? <;> rfl
  rw [e] at H
  exact WShape.fitsPi_iff.1 H.2

/-- A constructor shape below a typed interpretation `m1` of a term of the inductive type `s`
applied to `args`: `m1` is a constructor shape of the same constructor with larger fields `fs1`,
each typed at an interpretation of its declared domain, at the valuation with interpretations `p`
of the parameters and the fields before it pushed. -/
theorem ctor_fields_typed (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t i : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hci : T.ctors[i]? = some c)
    (hidx : (T.ctors.map (·.name)).idxOf? c.name = some i)
    {ls : List VLevel} {Ps Ds : List VExpr} {B : VExpr}
    (hcty : c.type.instL ls = .foralls (Ps ++ Ds) B) (hPs : Ps.length = d.params.length)
    {args : List VExpr} (hargs : args.length = d.params.length + T.indices.length)
    {fs : List (WShape n)} (hne : IsStruct c.name → WShape.ListNonZero fs)
    {m1 a : TShape} (hle : (WShape.ctor' c.name fs).T ≤ m1) (hty : m1.HasType a)
    (ha : LE_Interp env ρ a ((VExpr.const s ls).appN args)) :
    ∃ N, ∃ fs1 : List (WShape N), ∃ p : List TShape,
      (WShape.ctor' c.name fs1).T ≤ m1 ∧
      List.Forall₂ (fun (x : WShape n) (y : WShape N) => x.T ≤ y.T) fs fs1 ∧
      List.Forall₂ (fun y A => LE_Interp env ρ y A) p (args.take d.params.length) ∧
      ∀ k (x : WShape N) (D : VExpr), fs1[k]? = some x → Ds[k]? = some D →
        ∃ b : WShape N, x.HasType b ∧
          LE_Interp env (pushAll ρ (p ++ (fs1.take k).map (·.T))) b.T D := by
  rw [← spine_eq_appN] at ha
  obtain ⟨n0, H0⟩ := ha.spine_inv hM.roles (fun r n' h => by
    cases hM.roles h (ConstArity.indTy hs hT)
    rw [(ConstArity.indTy hs hT).determ h] at *; simp [hargs])
  -- a common level for the shapes involved, above `0`
  obtain ⟨K, hK0, hK1, hK2, hK3⟩ : ∃ K, n0 ≤ K + 1 ∧ m1.1 ≤ K + 1 ∧ a.1 ≤ K + 1 ∧ n ≤ K :=
    ⟨max n0 (max m1.1 (max a.1 n)), by omega, by omega, by omega, by omega⟩
  obtain ⟨rargs, y, hra, hay, hC⟩ := H0 (K + 1) hK0
  have hrl : rargs.length = d.params.length + T.indices.length := by
    rw [List.Forall₂.length_eq hra, List.length_reverse, hargs]
  -- lifted to level `K + 2`
  have hty' := (TShape.HasType.def (m := K+1+1) (by omega) (by omega)).1 hty
  have hle' := (TShape.LE.def (m := K+1+1) (by simp; omega) (by omega)).1 hle
  simp only [WShape.T, WShape.lift_ctor' (show n ≤ K + 1 by omega)] at hle'
  have hne' : IsStruct c.name → WShape.ListNonZero (fs.map (WShape.lift (K+1))) :=
    fun h => (WShape.ListNonZero.lift_iff (by omega)).2 (hne h)
  obtain ⟨l', h', I, as, hm1, hfl, ha', hok⟩ := WShape.ctor_typed hne' hle' hty'
  have hnb {r I} {as : List (WShape (K+1))} : WShape.indTy r I as ≠ .bot := by
    simp [WShape.ext_iff, WShape.indTy, WShape.bot, Shape.bot]
  obtain hy | ⟨ctys, hcl, hcty', hyY⟩ := Const.indTy_inv hM.roles hs hT hrl hC
  · have := (TShape.LE.def (m := K+1+1) (b := TShape.bot) (by omega) (Nat.zero_le _)).1
      (hay.trans hy)
    simp only [TShape.bot, WShape.T, WShape.lift_bot] at this
    exact absurd (ha' ▸ WShape.le_bot.1 this) hnb
  have haY := (TShape.LE.def (m := K+1+1) (by omega) (by simp)).1 (hay.trans hyY)
  simp only [WShape.T, WShape.lift_self] at haY
  rw [ha'] at haY
  obtain h | ⟨l'', h1, h2⟩ := WShape.le_indTy.1 haY
  · exact absurd h hnb
  obtain ⟨-, rfl, rfl⟩ := WShape.indTy.inj.1 h1
  have hfit := WShape.fitsPi_of_ctorOK hok (i := i) hidx
  have hil : i < ctys.length := hcl ▸ (List.getElem?_eq_some_iff.1 hci).1
  obtain ⟨hc, hRc, hPA⟩ := hcty' i c ctys[i] hci (List.getElem?_eq_getElem hil)
  rw [hcty] at hRc
  let p := (rargs.reverse.take d.params.length).map (·.T)
  have hcI := hRc.piAppS_foralls hM Ps hPA (by simp [hPs]; omega)
  have hle₂ : as.getD (rargs.length + i) .bot ≤ ctys[i] := by
    have := List.forall₂_getD h2 (WShape.LE.rfl (s := .bot)) (rargs.length + i)
    rwa [List.getD_eq_getElem?_getD (l := rargs.reverse ++ ctys),
      List.getElem?_append_right (by simp), List.length_reverse, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hil, Option.getD_some] at this
  have hfs := LE_Interp.fitsPi_foralls hM hfit (hcI.mono (WShape.LE.T hle₂))
  refine ⟨K + 1, l', p, ?_, ?_, ?_, fun k x D hx hD => ?_⟩
  · rw [← WShape.ctor_eq_ctor' (h := h'), ← hm1]; exact (TShape.lift_eqv (m := K+1+1) (by omega)).1
  · refine List.forall₂_of_getElem? (by rw [← List.Forall₂.length_eq hfl]; simp) ?_
    intro j x y hx hy
    have := hfl.getElem?' (by rw [List.getElem?_map, hx]; rfl) hy
    exact (TShape.lift_eqv (a := x.T) (m := K+1) (by simp; omega)).2.trans (WShape.LE.T this)
  · have := (List.Forall₂.reverse (l := rargs) (l' := args.reverse)).2 hra
    rw [List.reverse_reverse] at this
    exact List.forall₂_map_left_iff.2 (List.forall₂_take' this)
  · obtain ⟨b, hb1, hb2⟩ := hfs k x D hx hD
    exact ⟨b, hb1, by rwa [pushAll_append]⟩

/-- Fields typed at interpretations of a constructor's declared field domains are typed at
interpretations of their views, at a valuation fitting the parameters and the fields before:
`FieldsWF`'s definitional equalities hold in the model, by its soundness for the environment the
fields were checked in. -/
theorem FieldsWF.view_interp (hM : ModelEnv env) {envX : VEnv} (hX : SoundHyps envX env)
    (hXe : envX ≤ env) (hO : envX.Ordered) {d : VInductDecl} {ls : List VLevel} {U : Nat}
    (hls : ∀ l ∈ ls, l.WF U) {Γc : List VExpr} {j : Nat} {Ds : List VExpr} {fs : List VField}
    (H : d.FieldsWF envX Γc j Ds fs) : OnCtx Γc (envX.IsType d.uvars) →
    ∀ {P : List TShape}, Valuation.Fits env [] (Γc.map (·.instL ls)) (pushAll .nil P) →
    ∀ {xs : List (WShape N)}, (∀ i x D, xs[i]? = some x → Ds[i]? = some D →
      ∃ b : WShape N, x.HasType b ∧
        LE_Interp env (pushAll .nil (P ++ (xs.take i).map (·.T))) b.T (D.instL ls)) →
    ∀ k x (f : VField), xs[k]? = some x → fs[k]? = some f → ∃ b : WShape N, x.HasType b ∧
      LE_Interp env (pushAll .nil (P ++ (xs.take k).map (·.T))) b.T (f.type.instL ls) := by
  induction H with
  | nil => intro _ _ _ _ _ _ _ _ _ h; cases h
  | @cons Γc D j f Ds fs h1 h2 _ _ _ _ _ ih =>
    intro hΓ P W xs hxs k x f' hx hf'
    obtain _ | ⟨x0, xs⟩ := xs; · cases hx
    obtain ⟨b0, hb0, hbD⟩ := hxs 0 x0 D rfl rfl
    simp only [List.take_zero, List.map_nil, List.append_nil] at hbD
    obtain ⟨u, hDf⟩ := h1
    have hS := hX.strongSound' hM hXe hO (hΓ.instL hls) (hDf.instL hls)
    have hbf := (hS.sound W).1 hbD
    cases k with
    | zero =>
      cases hx; cases hf'
      exact ⟨b0, hb0, by simpa using hbf⟩
    | succ k =>
      have hT := hX.strongSound' hM hXe hO (hΓ.instL hls) (h2.instL hls)
      have W' : Valuation.Fits env [] ((f.type :: Γc).map (·.instL ls))
          (pushAll .nil (P ++ [x0.T])) := by
        rw [pushAll_concat]
        exact .cons W (fun ha => InterpTyped.hsort (hT.left.sound W) ha) hbf
          (WShape.HasType.T hb0)
      have := ih ⟨hΓ, _, h2⟩ W' (xs := xs) (fun i x D hx hD => by
        obtain ⟨b, h1, h2⟩ := hxs (i + 1) x D hx hD
        refine ⟨b, h1, ?_⟩
        simpa [List.append_assoc] using h2) k x f' hx hf'
      simpa using this


/-- Interpretations of the terms of a substitution interpret its variables at `pushAll`. -/
theorem pushAll_consList {ρ : Valuation} {P : List TShape} {σs : List VExpr}
    (hP : List.Forall₂ (fun y x => LE_Interp env ρ y x) P σs) :
    ∀ i, LE_Interp env ρ (pushAll .nil P i) (VExpr.Subst.dflt.consList σs i) := by
  intro i
  have hl : P.length = σs.length := List.Forall₂.length_eq hP
  rw [pushAll_apply, VExpr.Subst.consList_apply]
  by_cases hi : i < σs.length
  · rw [dif_pos (by omega), dif_pos hi, List.getElem_reverse, List.getElem_reverse]
    exact hP.getElem?' (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) |>.mono
      (by simp only [hl]; exact .rfl)
  · rw [dif_neg (by omega)]; exact .bot

/-- A telescope typed in `envX` is sound in the model of `env`, binder by binder. -/
theorem IsTele.soundAt (hM : ModelEnv env) {envX : VEnv} (hX : SoundHyps envX env)
    (hXe : envX ≤ env) (hO : envX.Ordered) {U : Nat} :
    ∀ {Γ Qs : List VExpr}, envX.IsTele U Γ Qs → OnCtx Γ (envX.IsType U) →
      ∀ i (A : VExpr), Qs[i]? = some A → ∃ u, SoundTy env ((Qs.take i).reverse ++ Γ) A (.sort u)
  | _, [], _, _, _, _, h => by cases h
  | Γ, Q :: Qs, .cons ⟨u, hA⟩ h, hΓ, i, A, hi => by
    cases i with
    | zero =>
      cases hi
      exact ⟨u, (hX.strongSound' hM hXe hO hΓ hA).left.sound⟩
    | succ i =>
      obtain ⟨v, H⟩ := IsTele.soundAt hM hX hXe hO h ⟨hΓ, _, hA⟩ i A hi
      exact ⟨v, by simpa using H⟩

theorem _root_.Lean4Lean.VExpr.ClosedN.foralls_getElem :
    ∀ {As : List VExpr} {B : VExpr} {k : Nat}, (VExpr.foralls As B).ClosedN k →
      ∀ i (A : VExpr), As[i]? = some A → A.ClosedN (k + i)
  | [], _, _, _, _, _, h => by cases h
  | _ :: _, _, _, h, 0, _, hi => by cases hi; exact h.1
  | _ :: _, _, _, h, i+1, _, hi => by
    have := VExpr.ClosedN.foralls_getElem h.2 i _ hi
    rwa [Nat.add_right_comm, Nat.add_assoc] at this


/-- `ProjSound` for a block declared in `E₁`, whose model of `envT` (the block's types as axioms)
is sound. -/
theorem projSound_at (hM : ModelEnv env) {E₁ envT : VEnv} (hE₁ : E₁.WF) {d : VInductDecl}
    (hd : d.WF E₁) (hTs : E₁.addConstList d.typeConsts = some envT) (hle : envT ≤ env)
    (hX : SoundHyps envT env) {s : Name} {t : Nat} (hs : env.inducts s = some (d, t))
    {T : VInductiveType} (hT : d.types[t]? = some T) (hname : T.name = s)
    {Γ : List VExpr} {c : VConstructor} {k : Nat} {f : VField} {ls : List VLevel}
    {As I : List VExpr} {e : VExpr} {u : VLevel} {U : Nat}
    (hcs : T.ctors = [c]) (hf : c.fields[k]? = some f)
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars) (hAs : As.length = d.params.length)
    (hI : I.length = T.indices.length)
    (hS : StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u))
    (he : StrongSound env U Γ e (.appN (.const s ls) (As ++ I))) :
    SoundTy env Γ (.proj s k e) (c.projType ls s k As e) := by
  have hO : envT.Ordered := (VEnv.WF.addConstList hE₁ (fun p hp => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
    exact (hd.types T hT).1) hTs).ordered
  have hle₁ : E₁ ≤ envT := VEnv.addConstList_le hTs
  have hTm : T ∈ d.allTypes := List.mem_append_left _ (List.mem_of_getElem? hT)
  obtain ⟨hTW, hCW⟩ := hd.ctors envT hTs T hTm
  have hcW := hCW c (by simp [hcs])
  obtain ⟨Ps, Ds, hcty, hPD, hFW, -⟩ := hcW.shape
  have hPs : Ps.length = d.params.length := hPD.length_eq
  have hPT : envT.IsTele d.uvars [] d.params := hd.params.mono hle₁
  have hΓP : OnCtx d.params.reverse (envT.IsType d.uvars) := by simpa using hPT.onCtx trivial
  intro Γ₀ ρ W m hm
  cases hm with
  | bot => exact InterpTyped.bot
  | proj hs' hT' hcs' hce hx hmx =>
  rename_i n x fs d' t' T' c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs'))
  obtain rfl : T = T' := Option.some.inj (hT.symm.trans hT')
  obtain rfl : c = c' := (List.cons.inj (hcs.symm.trans hcs')).1
  by_cases hne : IsStruct c.name → WShape.ListNonZero fs
  · obtain ⟨m1, a, hle1, hm1, ha, hty⟩ := he.sound W hce
    have hcty' : c.type.instL ls = .foralls (Ps.map (·.instL ls) ++ Ds.map (·.instL ls))
        ((T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length c.fields.length)
          c.indices).instL ls) := by
      rw [hcty, VEnv.foralls_instL', List.map_append]
    obtain ⟨N, fs1, p, hle2, hfs, hp, hfields⟩ := ctor_fields_typed hM hs hT
      (i := 0) (by simp [hcs]) (by simp [hcs]) hcty' (by simpa using hPs)
      (args := As ++ I) (by simp [hAs, hI]) hne hle1 hty ha
    rw [List.take_left' hAs] at hp
    -- the parameters, typed along the block's telescope
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
    obtain ⟨P, hP1, hP2, hP3⟩ := hTS'.exists_fits hM W (pushAll_consList hp)
    have hpl : p.length = As.length := List.Forall₂.length_eq hp
    have hPl : P.length = As.length := List.Forall₂.length_eq hP1
    have hρLE : (pushAll .nil p).LE (pushAll .nil P) := fun i => by
      by_cases hi : i < As.length
      · exact hP3 i hi
      · rw [pushAll_apply, pushAll_apply, dif_neg (by omega), dif_neg (by omega), hpl, hPl]
        exact .rfl
    -- the fields, typed at interpretations of their declared domains over `P`
    have hccl : (c.type.instL ls).ClosedN := by
      obtain ⟨_, h⟩ := hcW.type; exact (h.closedN hO trivial).instL
    rw [hcty'] at hccl
    have hfsl : fs1.length = fs.length := (List.Forall₂.length_eq hfs).symm
    have hxs : ∀ i x (D : VExpr), fs1[i]? = some x → Ds[i]? = some D →
        ∃ b : WShape N, x.HasType b ∧
          LE_Interp env (pushAll .nil (P ++ (fs1.take i).map (·.T))) b.T (D.instL ls) := by
      intro i x D hx hD
      have hD' : (Ds.map (·.instL ls))[i]? = some (D.instL ls) := by simp [hD]
      obtain ⟨b, hb1, hb2⟩ := hfields i x _ hx hD'
      have hil : i < fs1.length := (List.getElem?_eq_some_iff.1 hx).1
      have hcl : (D.instL ls).ClosedN (Ps.length + i) := by
        have := VExpr.ClosedN.foralls_getElem hccl (Ps.length + i) (D.instL ls)
          (by rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
            hD'])
        simpa using this
      have h1 := LE_Interp.closed hM.closed hcl (ρ' := pushAll .nil (p ++ (fs1.take i).map (·.T)))
        (fun j hj => by
          rw [pushAll_apply, pushAll_apply]
          have : j < (p ++ (fs1.take i).map (·.T)).length := by simp [hpl, hAs, ← hPs]; omega
          rw [dif_pos this, dif_pos this]) hb2
      refine ⟨b, hb1, h1.mono_l ?_⟩
      rw [pushAll_append, pushAll_append]
      exact pushAll_mono hρLE (List.forall₂_refl' fun _ => .rfl)
    have W' : Valuation.Fits env [] (d.params.reverse.map (·.instL ls)) (pushAll .nil P) := by
      rw [List.map_reverse]; exact hP2
    obtain ⟨x1, hx1⟩ : ∃ x1, fs1[k]? = some x1 :=
      ⟨_, List.getElem?_eq_getElem (by rw [hfsl]; exact (List.getElem?_eq_some_iff.1 hx).1)⟩
    have hxx1 : x.T ≤ x1.T := hfs.getElem?' hx hx1
    obtain ⟨b, hb1, hb2⟩ := FieldsWF.view_interp hM hX hle hO hls hFW hΓP W' hxs k x1 f hx1 hf
    have hce1 : LE_Interp env ρ (WShape.ctor' c.name fs1).T e := hm1.mono hle2
    refine InterpTyped.mk (hmx.trans hxx1) (.proj hs hT hcs hce1 hx1 .rfl) ?_ (WShape.HasType.T hb1)
    unfold VConstructor.projType
    rw [hf]
    refine TeleSubst.interp_subst hM (List.forall₂_append' hP1 ?_) hb2
    have hkl : k ≤ fs1.length := by have := (List.getElem?_eq_some_iff.1 hx1).1; omega
    refine List.forall₂_of_getElem? (by simp [VExpr.projs, hkl]) fun j y z hy hz => ?_
    have hj : j < k := by simpa [VExpr.projs] using (List.getElem?_eq_some_iff.1 hz).1
    simp only [VExpr.projs, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.some.injEq] at hz
    subst hz
    simp only [List.getElem?_map, List.getElem?_take_of_lt hj] at hy
    obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1 hy
    exact .proj hs hT hcs hce1 hy' .rfl
  · have hz : x.1 ≤ .bot := by
      refine Classical.byContradiction fun h => hne fun _ => ⟨x, List.mem_of_getElem? hx, h⟩
    obtain ⟨m', a, h1, h2, h3, h4⟩ := InterpTyped.bot (env := env) (ρ := ρ) (n := n)
      (M := .proj s k e) (A := c.projType ls s k As e)
    exact ⟨m', a, hmx.trans ((WShape.LE.T (b := .bot) hz).trans h1), h2, h3, h4⟩


/-- A constructor shape that does not collapse, below another constructor shape: the same
constructor, with smaller fields. -/
theorem TShape.ctor'_le_ctor' {c c' : Name} {l : List (WShape n)} {l' : List (WShape n')}
    (hne : IsStruct c → WShape.ListNonZero l)
    (h : (WShape.ctor' c l).T ≤ (WShape.ctor' c' l').T) :
    c = c' ∧ List.Forall₂ (fun x y => x.T ≤ y.T) l l' := by
  have hK1 : n ≤ max n n' := Nat.le_max_left ..
  have hK2 : n' ≤ max n n' := Nat.le_max_right ..
  rw [TShape.LE.def (m := max n n' + 1) (by simp; omega) (by simp; omega)]
    at h
  simp only [WShape.T, WShape.lift_ctor' hK1, WShape.lift_ctor' hK2] at h
  have hne' : IsStruct c → WShape.ListNonZero (l.map (WShape.lift (max n n'))) :=
    fun hs => (WShape.ListNonZero.lift_iff hK1).2 (hne hs)
  obtain ⟨l'', h'', heq, hl⟩ := WShape.ctor'_le.1 h hne'
  unfold WShape.ctor' at heq
  split at heq
  · obtain ⟨rfl, rfl⟩ := WShape.ctor.inj.1 heq
    refine ⟨rfl, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hl
    exact List.Forall₂.imp (fun x y hxy =>
      (TShape.LE.def (m := max n n') (by simp [WShape.T]; omega) (by simp [WShape.T]; omega)).2 hxy) hl
  · simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq


/-- A constructor's `Const` derivation at its arity: `bot`, or the constructor shape of its
fields at levels where its type is not a proposition. -/
theorem Const.ctor_inv (hR : ConstRoles env) {s : Name} {d : VInductDecl} {t t' : Nat}
    {T : VInductiveType} {c' : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t']? = some T) (hc : c' ∈ T.ctors) {ls : List VLevel}
    {R : TShape → VExpr → Prop} {rargs : List (WShape n)} {m : TShape}
    (hl : rargs.length = d.params.length + c'.fields.length)
    (H : Const env c'.name ls R rargs m) :
    m ≤ TShape.bot ∨ ¬d.PropAt ls ∧
      m ≤ (WShape.ctor' c'.name (rargs.reverse.drop d.params.length)).T := by
  have hA : ConstArity env c'.name (.ctor d t' c') (d.params.length + c'.fields.length) :=
    .ctor hs hT hc rfl
  cases H with
  | bot => exact .inl TShape.bot_eqv.1
  | lam h1 h2 =>
    refine .inl (h2.trans ((WShape.lam'_le_bot fun x y h => WShape.LE.T_iff.1
      ((Const.compat_mismatch hR (by simp; omega) (h1 x y h) hA).trans
        TShape.bot_eqv.2)).T.trans TShape.bot_eqv.1))
  | delta h1 h2 => cases hR (.delta h1 h2) hA
  | indTy h1 h2 => cases hR (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 h5 h6 h7 =>
    have := hR (.ctor h1 h2 h3 h4) hA
    cases this
    exact .inr ⟨h5, h7⟩
  | iota h1 h2 _ h4 => cases hR (.recursor h1 h2 h4) hA
  | kIota h1 h2 _ h4 => cases hR (.recursor h1 h2 h4) hA
  | quotTy h1 h2 => cases hR (.quotTy h1 h2) hA
  | quotMk h1 h2 => cases hR (.quotMk h1 h2) hA
  | quot h1 h2 => cases hR (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hR (.quotLift h1 h2) hA


/-- An interpretation of a constructor applied to its parameters and fields: `bot`, or the
constructor shape of interpretations of the fields, at levels where its type is not a
proposition. -/
theorem ctorApp_inv (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t t' : Nat}
    {T : VInductiveType} {c' : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t']? = some T) (hc : c' ∈ T.ctors) {ls : List VLevel} {As fs : List VExpr}
    (hAs : As.length = d.params.length) (hfs : fs.length = c'.fields.length)
    {ρ : Valuation} {m : TShape}
    (H : LE_Interp env ρ m ((VExpr.const c'.name ls).appN (As ++ fs))) :
    m ≤ TShape.bot ∨ ¬d.PropAt ls ∧ ∃ k, ∃ rf : List (WShape k),
      List.Forall₂ (fun x A => LE_Interp env ρ x.T A) rf fs ∧
      m ≤ (WShape.ctor' c'.name rf).T := by
  have hA : ConstArity env c'.name (.ctor d t' c') (d.params.length + c'.fields.length) :=
    .ctor hs hT hc rfl
  rw [← spine_eq_appN] at H
  obtain ⟨n0, H0⟩ := H.spine_inv hM.roles (fun r n h => by
    cases hM.roles h hA
    rw [← hA.determ h]; simp [hAs, hfs]; omega)
  obtain ⟨rargs, y, hra, hmy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hl : rargs.length = d.params.length + c'.fields.length := by
    rw [List.Forall₂.length_eq hra]; simp [hAs, hfs]; omega
  rcases Const.ctor_inv hM.roles hs hT hc hl hC with h | ⟨hP, h⟩
  · exact .inl (hmy.trans h)
  · refine .inr ⟨hP, n0, _, ?_, hmy.trans h⟩
    have h2 := (List.Forall₂.reverse (l := rargs) (l' := (As ++ fs).reverse)).2 hra
    rw [List.reverse_reverse] at h2
    have := List.forall₂_drop' (k := d.params.length) h2
    rwa [List.drop_left' hAs] at this


/-- A projection of a constructor application's interpretations are its field's. -/
theorem projIota_le (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t : Nat}
    {T : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t))
    (hT : d.types[t]? = some T) (hcs : T.ctors = [c]) {ls : List VLevel} {As fs : List VExpr}
    {k : Nat} {a : VExpr} (hAs : As.length = d.params.length)
    (hfs : fs.length = c.fields.length) (ha : fs[k]? = some a) {ρ : Valuation} {m : TShape}
    (H : LE_Interp env ρ m (.proj s k ((VExpr.const c.name ls).appN (As ++ fs)))) :
    LE_Interp env ρ m a := by
  cases H with
  | bot => exact .bot
  | proj hs' hT' hcs' hce hx hmx =>
  rename_i n x fs' d' t' T' c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs'))
  obtain rfl : T = T' := Option.some.inj (hT.symm.trans hT')
  obtain rfl : c = c' := (List.cons.inj (hcs.symm.trans hcs')).1
  by_cases hne : IsStruct c.name → WShape.ListNonZero fs'
  · rcases ctorApp_inv hM hs hT (by simp [hcs]) hAs hfs hce with h | ⟨-, k', rf, hrf, h⟩
    · obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1 (WShape.LE.of_T (h.trans TShape.bot_eqv.2)) hne
      simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
    · obtain ⟨-, hl⟩ := TShape.ctor'_le_ctor' hne h
      obtain ⟨y, hy⟩ : ∃ y, rf[k]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by
          rw [← List.Forall₂.length_eq hl]; exact (List.getElem?_eq_some_iff.1 hx).1)⟩
      exact (hrf.getElem?' hy ha).mono (hmx.trans (hl.getElem?' hx hy))
  · have hz : x.1 ≤ .bot := by
      refine Classical.byContradiction fun h => hne fun _ => ⟨x, List.mem_of_getElem? hx, h⟩
    exact LE_Interp.mono (hmx.trans (WShape.LE.T (b := .bot) hz)) .bot

end LogRel
end Lean4Lean

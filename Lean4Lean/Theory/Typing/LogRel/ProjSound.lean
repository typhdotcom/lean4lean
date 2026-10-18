import Lean4Lean.Theory.Typing.LogRel.SoundLemmas

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

end LogRel
end Lean4Lean

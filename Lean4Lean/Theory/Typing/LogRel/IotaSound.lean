import Lean4Lean.Theory.Typing.LogRel.ProjEta

/-!
# Iota rules are sound in the model

An iota rule is a closed equation `lams Bs L ≡ lams Bs R`. Its two sides have the same
interpretations if its bodies do under any valuation fitting the binders: the recursor applied to
a constructor (`L`) computes, in the model, to the minor premise applied to the fields and
inductive hypotheses (`R`). Forward this is the model's own iota case read off the recursor's
interpretation; backward the recursor's interpretation is built from the right-hand side's, which
needs the arguments typed, so it holds only at valuations fitting the binders.
-/

namespace Lean4Lean
open VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat}

/-! ### Lambda telescopes -/

theorem StrongSound.lam_inv (H : StrongSound env U Γ (.lam A e) T) :
    ∃ B u, SoundTy env Γ A (.sort u) ∧ StrongSound env U (A::Γ) e B ∧
      SoundEq env Γ (.forallE A B) T := by
  obtain ⟨-, -, core, heq⟩ := H
  cases core with | lam h1 h2 => exact ⟨_, _, h1, h2, heq⟩

variable (env) in
/-- A telescope whose binders the model types at sorts, each over the ones before it. -/
inductive SoundTele : List VExpr → List VExpr → Prop where
  | nil : SoundTele Γ []
  | cons : SoundTy env Γ A (.sort u) → SoundTele (A::Γ) Bs → SoundTele Γ (A::Bs)

/-- A lambda telescope's syntax-directed typing: its binders are sound types and its body is
typed under them, at a type whose pi telescope the model cannot tell from the given one. -/
theorem StrongSound.lams_inv :
    ∀ {Bs : List VExpr} {Γ : List VExpr} {e T : VExpr},
    StrongSound env U Γ (.lams Bs e) T →
    ∃ B, SoundTele env Γ Bs ∧ StrongSound env U (Bs.reverse ++ Γ) e B ∧
      SoundEq env Γ (.foralls Bs B) T
  | [], _, _, _, H => ⟨_, .nil, H, .rfl⟩
  | A :: Bs, Γ, e, T, H => by
    obtain ⟨B₁, u, hA, hb, heq⟩ := StrongSound.lam_inv H
    obtain ⟨B, hT, hB, heq'⟩ := StrongSound.lams_inv hb
    refine ⟨B, .cons hA hT, by simpa using hB, ?_⟩
    exact (SoundEq.forallE hA .rfl heq').trans heq

/-- Sound-equal bodies under a sound telescope give sound-equal lambda telescopes. -/
theorem SoundEq.lams : ∀ {Γ Bs : List VExpr}, SoundTele env Γ Bs →
    ∀ {L R : VExpr}, SoundEq env (Bs.reverse ++ Γ) L R →
      SoundEq env Γ (.lams Bs L) (.lams Bs R)
  | _, _, .nil, _, _, H => H
  | Γ, A :: Bs, .cons hA hT, L, R, H => by
    have IH : SoundEq env (A::Γ) (.lams Bs L) (.lams Bs R) :=
      SoundEq.lams hT (by simpa using H)
    intro _ ρ W m
    suffices ∀ {L R}, SoundEq env (A::Γ) L R →
        LE_Interp env ρ m (.lam A L) → LE_Interp env ρ m (.lam A R) from
      ⟨this IH, this IH.symm⟩
    intro L R H h
    cases h with
    | bot => exact .bot
    | lam h1 h2 h3 h4 =>
      exact .lam h1 h2 (fun x hx =>
        (H (W.cons (InterpTyped.hsort (hA W)) h1 hx.T)).1 (h3 x hx)) h4

/-- The model's `SoundEq` of pi telescopes over a sound telescope gives `SoundEq` of the bodies. -/
theorem SoundEq.foralls_inv (hM : ModelEnv env) : ∀ {Γ Bs : List VExpr}, SoundTele env Γ Bs →
    ∀ {B B' : VExpr}, SoundEq env Γ (.foralls Bs B) (.foralls Bs B') →
      SoundEq env (Bs.reverse ++ Γ) B B'
  | _, _, .nil, _, _, H => H
  | _, _ :: _, .cons hA hT, _, _, H => by
    have := (SoundEq.forallE_inv hM H hA hA).2
    simpa using SoundEq.foralls_inv hM hT this

/-! ### Valuations below another -/

/-- A term closed under `k` binders, interpreted at a valuation below another at those binders, is
interpreted at the other. -/
theorem LE_Interp.closed_le (hcl : ClosedRules env) {M : VExpr} {k : Nat} (cl : M.ClosedN k)
    {ρ ρ' : Valuation} (h : ∀ i < k, ρ i ≤ ρ' i) {m : TShape}
    (H : LE_Interp env ρ m M) : LE_Interp env ρ' m M := by
  classical
  let ρ'' : Valuation := fun i => if i < k then ρ i else ρ' i
  have h1 : LE_Interp env ρ'' m M :=
    LE_Interp.closed hcl cl (fun i hi => by simp [ρ'', hi]) H
  refine h1.mono_l fun i => ?_
  by_cases hi : i < k
  · simp only [ρ'', if_pos hi]; exact h i hi
  · simp only [ρ'', if_neg hi]; exact .rfl

/-! ### Realizing a lambda telescope -/

variable (env) in
/-- Values `xs` for the binders `Bs` at `ρ`, each typed at an interpretation of its binder's type
over the values before it. -/
inductive LamsFit : Valuation → List VExpr → List TShape → Prop where
  | nil : LamsFit ρ [] []
  | cons : LE_Interp env ρ a A → x.HasType a → LamsFit (ρ.push x) Bs xs →
    LamsFit ρ (A::Bs) (x::xs)

theorem LamsFit.length : LamsFit env ρ Bs xs → xs.length = Bs.length
  | .nil => rfl
  | .cons _ _ H => by simp [H.length]

/-- An interpretation of a body at typed values for a lambda telescope's binders is the
application of an interpretation of the telescope to them. -/
theorem LE_Interp.lams_realize {M : VExpr} : ∀ {ρ : Valuation} {Bs : List VExpr}
    {xs : List TShape}, LamsFit env ρ Bs xs → ∀ {y : TShape},
    LE_Interp env (pushAll ρ xs) y M → ∃ h, LE_Interp env ρ h (.lams Bs M) ∧ AppS h xs y
  | _, _, _, .nil, y, H => ⟨y, H, .nil .rfl⟩
  | ρ, A :: Bs, x :: xs, .cons (a := a) ha hx hF, y, H => by
    obtain ⟨h', h1, h2⟩ := LE_Interp.lams_realize hF H
    let k := max h'.1 (max x.1 a.1)
    have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
    let f : WShapeFun k := WShapeFun.single (x.2.lift k) (h'.2.lift k)
    have hdom : WShape.HasDom f (a.2.lift k) :=
      (WShape.HasDom.single (y := h'.2.lift k)).2 (.inl ((TShape.HasType.def hk.2.1 hk.2.2).1 hx))
    refine ⟨WShape.T (n := k+1) (.lam' f), .lam' (ha.lift hk.2.2) hdom fun z _ => ?_, ?_⟩
    · simp only [f, WShapeFun.single_app]; split <;> [rename_i hz; exact .bot]
      refine (h1.lift hk.1).mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
      exact (TShape.lift_eqv hk.2.1).2.trans hz.T
    · refine .cons (f := WShape.lam' f) (x := x.2.lift k) .rfl (TShape.lift_eqv hk.2.1).1 ?_
      rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]
      exact h2.mono .rfl (TShape.lift_eqv hk.1).2

/-- What the bodies of two lambda telescopes do at each typed extension of a fitting valuation,
the telescopes do at the valuation. -/
theorem LE_Interp.lams_fit : ∀ {Γ Bs : List VExpr}, SoundTele env Γ Bs →
    ∀ {Γ₀ : List VExpr} {ρ : Valuation}, Valuation.Fits env Γ₀ Γ ρ → ∀ {L R : VExpr},
    (∀ xs, LamsFit env ρ Bs xs → Valuation.Fits env Γ₀ (Bs.reverse ++ Γ) (pushAll ρ xs) →
      ∀ y, LE_Interp env (pushAll ρ xs) y L → LE_Interp env (pushAll ρ xs) y R) →
    ∀ {m}, LE_Interp env ρ m (.lams Bs L) → LE_Interp env ρ m (.lams Bs R)
  | _, _, .nil, _, _, W, _, _, H, _, h => H [] .nil W _ h
  | Γ, A :: Bs, .cons hA hT, Γ₀, ρ, W, L, R, H, m, h => by
    cases h with
    | bot => exact .bot
    | lam h1 h2 h3 h4 =>
      refine .lam h1 h2 (fun x hx => ?_) h4
      refine LE_Interp.lams_fit hT (W.cons (InterpTyped.hsort (hA W)) h1 hx.T)
        (fun xs hF W' y hy => H (x.T :: xs) (.cons h1 hx.T hF) (by simpa [pushAll] using W') y hy) (h3 x hx)

/-- Two lambda telescopes over a sound telescope have the same interpretations if their bodies do
at every typed extension of a fitting valuation. -/
theorem SoundEq.lams_fit {Γ Bs : List VExpr} (hT : SoundTele env Γ Bs) {L R : VExpr}
    (H : ∀ {Γ₀ ρ} xs, Valuation.Fits env Γ₀ Γ ρ → LamsFit env ρ Bs xs →
      Valuation.Fits env Γ₀ (Bs.reverse ++ Γ) (pushAll ρ xs) →
      ∀ y, (LE_Interp env (pushAll ρ xs) y L ↔ LE_Interp env (pushAll ρ xs) y R)) :
    SoundEq env Γ (.lams Bs L) (.lams Bs R) := fun _ _ W _ =>
  ⟨LE_Interp.lams_fit hT W fun xs hF W' y => (H xs W hF W' y).1,
   LE_Interp.lams_fit hT W fun xs hF W' y => (H xs W hF W' y).2⟩

theorem LamsFit.getElem : ∀ {ρ : Valuation} {Bs : List VExpr} {zs : List TShape},
    LamsFit env ρ Bs zs → ∀ i (hi : i < zs.length) (hi' : i < Bs.length),
    ∃ b, LE_Interp env (pushAll ρ (zs.take i)) b Bs[i] ∧ zs[i].HasType b
  | _, _, _, .nil, _, hi, _ => absurd hi (by simp)
  | _, _, _, .cons h1 h2 _, 0, _, _ => ⟨_, h1, h2⟩
  | _, _, _, .cons _ _ hF, i+1, hi, hi' => by
    obtain ⟨b, h1, h2⟩ := hF.getElem i (by simpa using hi) (by simpa using hi')
    exact ⟨b, by simpa [pushAll] using h1, by simpa using h2⟩

theorem LamsFit.fits_take : ∀ {Γ Bs : List VExpr}, SoundTele env Γ Bs →
    ∀ {Γ₀ : List VExpr} {ρ : Valuation} {zs : List TShape}, Valuation.Fits env Γ₀ Γ ρ →
    LamsFit env ρ Bs zs → ∀ i, Valuation.Fits env Γ₀ ((Bs.take i).reverse ++ Γ)
      (pushAll ρ (zs.take i))
  | _, _, .nil, _, _, _, W, .nil, i => by simpa [pushAll] using W
  | _, _, _, _, _, _, W, _, 0 => by simpa [pushAll] using W
  | _, _, .cons hA hT, _, _, _, W, .cons h1 h2 hF, i+1 => by
    have := LamsFit.fits_take hT (W.cons (InterpTyped.hsort (hA W)) h1 h2) hF i
    simpa [pushAll] using this

/-! ### Variables and closed lambda telescopes -/

omit [ShapeEnv] in
theorem getElem_bvars {n k i : Nat} (h : i < (VExpr.bvars n k).length) :
    (VExpr.bvars n k)[i] = .bvar (n - 1 - i + k) := by
  simp only [VExpr.bvars, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]

omit [ShapeEnv] in
theorem bvars_append' (a b k : Nat) :
    VExpr.bvars a (b + k) ++ VExpr.bvars b k = VExpr.bvars (a + b) k := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [getElem_bvars h2]
  by_cases hi : i < a
  · rw [List.getElem_append_left (by simpa using hi), getElem_bvars]; congr 1; omega
  · rw [List.getElem_append_right (by simpa using hi), getElem_bvars]
    simp only [VExpr.length_bvars, List.length_append] at h1 h2 hi ⊢; congr 1; omega

omit [ShapeEnv] in
theorem ClosedN.lams_body : ∀ {Bs : List VExpr} {R : VExpr} {k : Nat},
    (VExpr.lams Bs R).ClosedN k → R.ClosedN (k + Bs.length)
  | [], _, _, h => h
  | _ :: Bs, _, k, h => by
    have := ClosedN.lams_body (Bs := Bs) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Shapes interpreting the variables `bvars n k` at `σ` are below `σ`'s values. -/
theorem forall₂_bvars_le {σ : Valuation} : ∀ {n k : Nat} {xs : List TShape},
    List.Forall₂ (fun x A => LE_Interp env σ x A) xs (VExpr.bvars n k) →
    ∀ i (h : i < xs.length), xs[i] ≤ σ (n - 1 - i + k) := by
  intro n k xs H i h
  have hl := List.Forall₂.length_eq H
  have := H.getElem?' (List.getElem?_eq_getElem h) (List.getElem?_eq_getElem (by simpa [hl] using h))
  rw [getElem_bvars] at this
  exact bvar_iff.1 this

/-- Values for binders below a valuation's: the first `N` below the variables above the last `m`,
the last `m` below those. -/
theorem pushAll_le_of {σ : Valuation} {N m : Nat} {pre fs : List TShape} (hpl : pre.length = N)
    (hfl : fs.length = m) (hp : ∀ i (h : i < pre.length), pre[i] ≤ σ (N - 1 - i + m))
    (hf : ∀ k (h : k < fs.length), fs[k] ≤ σ (m - 1 - k)) :
    ∀ i < N + m, pushAll σ (pre ++ fs) i ≤ σ i := by
  intro i hi
  rw [pushAll_apply, dif_pos (by simp; omega), List.getElem_reverse]
  simp only [List.length_append, hpl, hfl]
  by_cases h : N + m - 1 - i < N
  · rw [List.getElem_append_left (by omega)]
    have := hp (N + m - 1 - i) (by omega)
    rwa [show N - 1 - (N + m - 1 - i) + m = i by omega] at this
  · rw [List.getElem_append_right (by omega)]
    have := hf (N + m - 1 - i - pre.length) (by omega)
    rwa [show m - 1 - (N + m - 1 - i - pre.length) = i by omega] at this

/-! ### The forward direction -/

/-- The forward direction of an iota rule, under its binders, at any valuation: an interpretation
of the recursor applied to the binders before the fields, indices `idx` and a major premise whose
interpretations are constructor shapes of `c` with fields below the fields' values, interprets the
rule's right-hand side body. -/
theorem iota_body_le (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t₀ j q : Nat}
    {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (hj : d.allTypes[j]? = some Tj) (hq : d.allCtors[q]? = some (j, c)) {ls : List VLevel}
    {Bs : List VExpr} {R : VExpr} (hR : d.iotaRhs ls q j c = .lams Bs R)
    (hBs : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length)
    {idx : List VExpr} (hidxl : idx.length = Tj.indices.length)
    (hidx : ∀ k i, k < c.fields.length → VInductDecl.fieldIdx c k = some i →
      idx[i]? = some (.bvar (c.fields.length - 1 - k)))
    {major : VExpr} {σ : Valuation}
    (hmaj : ∀ x, LE_Interp env σ x major → x ≤ TShape.bot ∨ ∃ N, ∃ rf : List (WShape N),
      List.Forall₂ (fun z A => LE_Interp env σ z.T A) rf (VExpr.bvars c.fields.length 0) ∧
      x ≤ (WShape.ctor' c.name rf).T)
    {y : TShape}
    (H : LE_Interp env σ y ((VExpr.const (d.recName j) ls).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        idx ++ [major]))) :
    LE_Interp env σ y R := by
  generalize hN : d.params.length + d.allTypes.length + d.allCtors.length = N at *
  generalize hm : c.fields.length = m at *
  have hA : ConstArity env (d.recName j) (.recursor d j) (d.majorIdx Tj + 1) :=
    .recursor hs rfl hj
  have hlen : (VExpr.bvars N m ++ idx ++ [major]).length = d.majorIdx Tj + 1 := by
    simp only [VInductDecl.majorIdx, List.length_append, VExpr.length_bvars, hidxl,
      List.length_singleton, ← hN]; omega
  rw [← spine_eq_appN] at H
  obtain ⟨n0, H0⟩ := H.spine_inv hM.roles (fun r n' h => by
    cases hM.roles h hA; have := hA.determ h; rw [List.length_reverse, hlen]; omega)
  obtain ⟨rargs, y', hra, hyy, hC⟩ := H0 n0 (Nat.le_refl _)
  have hrl : rargs.length = d.majorIdx Tj + 1 := by
    rw [List.Forall₂.length_eq hra, List.length_reverse, hlen]
  have hRcl : R.ClosedN Bs.length := by
    have := ClosedN.lams_body (hR ▸ hM.closed.iotaRhs hs hq (ls := ls)); simpa using this
  -- the arguments before the indices, read off `rargs`
  refine LE_Interp.mono hyy ?_
  cases hC with
  | bot => exact .bot
  | lam he hle => exact LE_Interp.mono (Const.lam_le_bot hM.roles he hle (hrl ▸ hA)) .bot
  | delta h1 h2 => cases hM.roles (.delta h1 h2) hA
  | indTy h1 h2 => cases hM.roles (.indTy h1 h2) hA
  | ctor h1 h2 h3 h4 => cases hM.roles (.ctor h1 h2 h3 h4) hA
  | quotTy h1 h2 => cases hM.roles (.quotTy h1 h2) hA
  | quotMk h1 h2 => cases hM.roles (.quotMk h1 h2) hA
  | quot h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | quotK h1 h2 => cases hM.roles (.quotLift h1 h2) hA
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    rename_i s' hh fs x rest T' c' d' t' j' q'
    cases hM.roles hA (.recursor h1 h2 h4)
    obtain rfl := Option.some.inj (hj.symm.trans h4)
    have e : (VExpr.bvars N m ++ idx ++ [major]).reverse = major :: (VExpr.bvars N m ++ idx).reverse := by
      simp
    rw [e] at hra
    cases hra with | cons hx hrest =>
    have hrest' := List.Forall₂.reverse.2 hrest
    rw [List.reverse_reverse] at hrest'
    -- the constructor is `c`, and its fields are below the fields' values
    obtain ⟨hcq, hfs⟩ : q' = q ∧ ∀ k (hk : k < fs.length), (fs[k]).T ≤ σ (m - 1 - k) := by
      by_cases hne : IsStruct c'.name → WShape.ListNonZero fs
      · rcases hmaj x.T hx with hb | ⟨N', rf, hrf, hxle⟩
        · obtain ⟨l', h', heq, -⟩ := WShape.ctor'_le.1
            (WShape.LE.of_T ((h10.trans hb).trans TShape.bot_eqv.2)) hne
          simp [WShape.ext_iff, WShape.ctor, WShape.bot, Shape.bot] at heq
        obtain ⟨hn, hl⟩ := TShape.ctor'_le_ctor' hne (h10.trans hxle)
        refine ⟨hM.stepUniq.ctor hs h3 hq hn, fun k hk => ?_⟩
        have hk' : k < rf.length := by rw [← List.Forall₂.length_eq hl]; exact hk
        refine (hl.getElem?' (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hk')).trans ?_
        have := forall₂_bvars_le ((List.forall₂_map_left_iff (f := WShape.T)).2 hrf) k
          (by simpa using hk')
        simpa using this
      · have hst : IsStruct c'.name = true := Classical.byContradiction fun h' =>
          hne fun h'' => absurd h'' h'
        have hz : ∀ z ∈ fs, z.1 ≤ .bot := fun z hz =>
          Classical.byContradiction fun h' => hne fun _ => ⟨z, hz, h'⟩
        refine ⟨hM.etaCtor hs h3 hq (hM.struct _ hst), fun k hk => ?_⟩
        exact (WShape.LE.T (b := .bot) (hz _ (List.getElem_mem hk))).trans TShape.bot_le'
    subst hcq
    obtain rfl := (Prod.mk.inj (Option.some.inj (h3.symm.trans hq))).2
    rw [hR] at h8
    rw [hN] at h9
    have hpre := List.forall₂_take' (k := N) hrest'
    rw [List.take_left' (by simp)] at hpre
    have hrl : (rest.reverse.take N).length = N := by
      rw [List.Forall₂.length_eq hpre]; simp
    have hy := h8.appS_lams hM h9 (by
      rw [List.length_append, List.length_map, List.length_map, hrl, h7, hm, hBs])
    refine hy.closed_le hM.closed hRcl fun i hi => ?_
    refine pushAll_le_of (N := N) (m := m) (by simpa using hrl) (by simp [h7, hm]) (fun i h => ?_)
      (fun k h => by simpa using hfs k (by simpa using h)) i (by omega)
    have := forall₂_bvars_le ((List.forall₂_map_left_iff (f := WShape.T)).2 hpre) i
      (by simpa using h)
    simpa using this
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    rename_i s' hh d' t' j' q' T' c' rargs' e'
    cases hM.roles hA (.recursor h1 h2 h4)
    obtain rfl := Option.some.inj (hj.symm.trans h4)
    obtain ⟨T₁, hT₁, hcT⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
    obtain rfl := Option.some.inj (hj.symm.trans hT₁)
    rw [h5, List.mem_singleton] at hcT
    subst hcT
    obtain rfl := hM.stepUniq.ctor hs h3 hq rfl
    rw [hR] at h9
    rw [← Nat.add_assoc, hN] at h10
    have e : (VExpr.bvars N m ++ idx ++ [major]).reverse = major :: (VExpr.bvars N m ++ idx).reverse := by
      simp
    rw [e] at hra
    cases hra with | cons hx hrest =>
    have hrest' := List.Forall₂.reverse.2 hrest
    rw [List.reverse_reverse] at hrest'
    have hpre := List.forall₂_take' (k := N) hrest'
    rw [List.take_left' (by simp)] at hpre
    have hidxs := List.forall₂_drop' (k := N) hrest'
    rw [List.drop_left' (by simp)] at hidxs
    have hrl' : (rargs'.reverse.take N).length = N := by
      rw [List.Forall₂.length_eq hpre]; simp
    have hkl : (kFieldShapes c ((rargs'.reverse.drop N).map (·.T))).length = m := by
      simp [kFieldShapes, hm]
    have hy := h9.appS_lams hM h10 (by
      rw [List.length_append, List.length_map, hrl', hkl, hBs])
    refine hy.closed_le hM.closed hRcl fun i hi => ?_
    refine pushAll_le_of (N := N) (m := m) (by simpa using hrl') hkl (fun i h => ?_)
      (fun k h => ?_) i (by omega)
    · have := forall₂_bvars_le ((List.forall₂_map_left_iff (f := WShape.T)).2 hpre) i
        (by simpa using h)
      simpa using this
    · simp only [kFieldShapes, List.getElem_map, List.getElem_range]
      split
      · next i hi =>
        have hii := hidx k i (by simpa [kFieldShapes, hm] using h) hi
        rw [List.getD_eq_getElem?_getD]
        cases hgi : ((rargs'.reverse.drop N).map (·.T))[i]? with
        | none => exact TShape.bot_le
        | some z =>
          have := ((List.forall₂_map_left_iff (f := WShape.T)).2 hidxs).getElem?' hgi hii
          simpa using bvar_iff.1 this
      · exact TShape.bot_le

/-! ### The backward direction -/

theorem pushAll_bvar {ρ : Valuation} {zs : List TShape} {N m : Nat} (hl : zs.length = N + m)
    (i : Nat) (hi : i < zs.length) : pushAll ρ zs (N + m - 1 - i) = zs[i] := by
  rw [pushAll_apply, dif_pos (by omega), List.getElem_reverse]
  congr 1; omega

/-- The backward direction of an iota rule at levels where its type is not a proposition, under
its binders, at a valuation fitting them: an interpretation of the rule's right-hand side body
interprets the recursor applied to the binders before the fields, indices `idx` and a major
premise, given that the major premise has a constructor shape of `c` above the fields' values. -/
theorem iota_body_ge (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t₀ j q : Nat}
    {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (hj : d.allTypes[j]? = some Tj) (hq : d.allCtors[q]? = some (j, c)) {ls : List VLevel}
    (hP : ¬d.PropAt (d.blockLevels ls))
    {Bs : List VExpr} {R : VExpr} (hR : d.iotaRhs ls q j c = .lams Bs R)
    (hBs : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length)
    {idx : List VExpr} (hidxl : idx.length = Tj.indices.length) {major : VExpr}
    {Γ₀ Γ : List VExpr} {ρ₀ : Valuation} {zs : List TShape} (hF : LamsFit env ρ₀ Bs zs)
    (W : Valuation.Fits env Γ₀ Γ (pushAll ρ₀ zs)) {B : VExpr}
    (hLS : MSpine env Γ ((VExpr.const (d.recName j) ls).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        idx ++ [major])) B)
    (hRT : SoundTy env Γ R B)
    (hmaj : ∃ N', ∃ rf : List (WShape N'),
      LE_Interp env (pushAll ρ₀ zs) (WShape.ctor' c.name rf).T major ∧
      List.Forall₂ (fun z w => z ≤ w.T)
        (zs.drop (d.params.length + d.allTypes.length + d.allCtors.length)) rf)
    {y : TShape} (hy : LE_Interp env (pushAll ρ₀ zs) y R) :
    LE_Interp env (pushAll ρ₀ zs) y ((VExpr.const (d.recName j) ls).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        idx ++ [major])) := by
  generalize hN : d.params.length + d.allTypes.length + d.allCtors.length = N at *
  generalize hm : c.fields.length = m at *
  have hzl : zs.length = N + m := by rw [hF.length, hBs]
  obtain ⟨y'', b, hyle, hy'', hb, hty⟩ := hRT W hy
  obtain ⟨h, hh, hAppS⟩ := LE_Interp.lams_realize hF hy''
  have hh' : LE_Interp env (pushAll ρ₀ zs) h (d.iotaRhs ls q j c) := by
    rw [hR]; exact (closed_iff hM.closed (hR ▸ hM.closed.iotaRhs hs hq)).1 hh
  obtain ⟨N', rf, hx, hrf⟩ := hmaj
  -- a common level
  let K := max N' (maxLvl zs)
  have hKN : N' ≤ K := Nat.le_max_left ..
  have hKz : ∀ z ∈ zs, z.1 ≤ K + 1 := fun z hz => by
    have := le_maxLvl hz; omega
  let rfK : List (WShape K) := rf.map (·.lift K)
  let x : WShape (K+1) := WShape.ctor' c.name rfK
  let pre : List (WShape (K+1)) := (zs.take N).map (·.2.lift (K+1))
  let idxS : List (WShape (K+1)) := idx.map fun _ => .bot
  have hxI : LE_Interp env (pushAll ρ₀ zs) x.T major := by
    have := hx.lift (n := K + 1) (by simp [WShape.T]; omega)
    simpa [x, rfK, WShape.lift_ctor' hKN] using this
  have hrfl : rf.length = m := by
    rw [← List.Forall₂.length_eq hrf]; simp [hzl]
  have hC : LE_Interp.Const env (d.recName j) ls (LE_Interp env (pushAll ρ₀ zs))
      (x :: (pre ++ idxS).reverse) y'' := by
    refine .iota (fs := rfK) hs rfl hq hj hP
      (by simp [pre, idxS, VInductDecl.majorIdx, hidxl, ← hN]; omega)
      (by simp [rfK, hrfl, hm]) hh' ?_ .rfl
    rw [List.reverse_reverse, hN, List.take_left' (by simp [pre]; omega)]
    refine hAppS.args_mono ?_
    rw [← List.take_append_drop N zs]
    refine List.forall₂_append' ?_ ?_
    · have := forall₂_le_lift (K := K + 1) (xs := zs.take N) fun z hz =>
        hKz z (List.mem_of_mem_take hz)
      simpa [pre, List.map_map, Function.comp_def] using this
    · simp only [rfK, List.map_map]
      refine List.forall₂_map_right_iff.2 (List.Forall₂.imp (fun z w hzw => hzw.trans
        (TShape.lift_eqv (a := w.T) hKN).2) hrf)
  have hpre : List.Forall₂ (fun (x : WShape (K+1)) A => LE_Interp env (pushAll ρ₀ zs) x.T A)
      pre (VExpr.bvars N m) := by
    refine List.forall₂_of_getElem? (by
      rw [List.length_map, List.length_take, VExpr.length_bvars]; omega) fun i a A ha hA => ?_
    have hi : i < N := by have := (List.getElem?_eq_some_iff.1 hA).1; simpa using this
    simp only [pre, List.getElem?_map, List.getElem?_take, if_pos hi] at ha
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 ha
    rw [List.getElem?_eq_some_iff] at hA hz
    obtain ⟨-, rfl⟩ := hA; obtain ⟨hiz, rfl⟩ := hz
    rw [getElem_bvars]
    refine bvar_iff.2 ((TShape.lift_eqv (hKz _ (List.getElem_mem hiz))).1.trans ?_)
    rw [show N - 1 - i + m = N + m - 1 - i by omega, pushAll_bvar hzl i hiz]
    exact .rfl
  have hargs : List.Forall₂ (fun (x : WShape (K+1)) A => LE_Interp env (pushAll ρ₀ zs) x.T A)
      (x :: (pre ++ idxS).reverse) (VExpr.bvars N m ++ idx ++ [major]).reverse := by
    have e : (VExpr.bvars N m ++ idx ++ [major]).reverse =
        major :: (VExpr.bvars N m ++ idx).reverse := by simp
    rw [e]
    exact .cons hxI (List.Forall₂.reverse.2 (List.forall₂_append' hpre (forall₂_bot idx)))
  have hLS' := hLS
  rw [← spine_eq_appN] at hLS' ⊢
  exact (LE_Interp.apps_realize hM W hty hb hLS' hargs hC).mono hyle

/-- The backward direction of an iota rule at levels where its type is a proposition with large
elimination: the recursor reduces on any major premise, at fields read off the indices, and the
fields that are not indices are proofs, whose values are `bot`. -/
theorem iota_body_ge_k (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t₀ j q : Nat}
    {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (hj : d.allTypes[j]? = some Tj) (hq : d.allCtors[q]? = some (j, c)) (hTc : Tj.ctors = [c])
    {ls : List VLevel} (hPA : d.PropAt (d.blockLevels ls)) (hlarge : d.largeElim = true)
    {Bs : List VExpr} {R : VExpr} (hR : d.iotaRhs ls q j c = .lams Bs R)
    (hBs : Bs.length = d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length)
    {idx : List VExpr} (hidxl : idx.length = Tj.indices.length)
    (hidx : ∀ k i, k < c.fields.length → VInductDecl.fieldIdx c k = some i →
      idx[i]? = some (.bvar (c.fields.length - 1 - k)))
    {major : VExpr}
    {Γ₀ Γ : List VExpr} {ρ₀ : Valuation} {zs : List TShape} (hF : LamsFit env ρ₀ Bs zs)
    (W : Valuation.Fits env Γ₀ Γ (pushAll ρ₀ zs)) {B : VExpr}
    (hLS : MSpine env Γ ((VExpr.const (d.recName j) ls).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        idx ++ [major])) B)
    (hRT : SoundTy env Γ R B)
    (hproof : ∀ k (h : d.params.length + d.allTypes.length + d.allCtors.length + k < zs.length),
      VInductDecl.fieldIdx c k = none →
      zs[d.params.length + d.allTypes.length + d.allCtors.length + k] ≤ TShape.bot)
    {y : TShape} (hy : LE_Interp env (pushAll ρ₀ zs) y R) :
    LE_Interp env (pushAll ρ₀ zs) y ((VExpr.const (d.recName j) ls).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        idx ++ [major])) := by
  generalize hN : d.params.length + d.allTypes.length + d.allCtors.length = N at *
  generalize hm : c.fields.length = m at *
  have hzl : zs.length = N + m := by rw [hF.length, hBs]
  obtain ⟨y'', b, hyle, hy'', hb, hty⟩ := hRT W hy
  obtain ⟨h, hh, hAppS⟩ := LE_Interp.lams_realize hF hy''
  have hh' : LE_Interp env (pushAll ρ₀ zs) h (d.iotaRhs ls q j c) := by
    rw [hR]; exact (closed_iff hM.closed (hR ▸ hM.closed.iotaRhs hs hq)).1 hh
  let K := maxLvl zs
  have hKz : ∀ z ∈ zs, z.1 ≤ K + 1 := fun z hz => by have := le_maxLvl hz; omega
  let pre : List (WShape (K+1)) := (zs.take N).map (·.2.lift (K+1))
  let ishape : VExpr → WShape (K+1) := fun e => match e with
    | .bvar i => if hi : i < m then (zs[N + m - 1 - i]'(by omega)).2.lift (K+1) else .bot
    | _ => .bot
  let isS : List (WShape (K+1)) := idx.map ishape
  have hish : ∀ e, LE_Interp env (pushAll ρ₀ zs) (ishape e).T e := by
    intro e
    cases e with
    | bvar i =>
      simp only [ishape]; split
      · next hi =>
        refine bvar_iff.2 ((TShape.lift_eqv (hKz _ (List.getElem_mem _))).1.trans ?_)
        have := pushAll_bvar (ρ := ρ₀) hzl (N + m - 1 - i) (by omega)
        rw [show N + m - 1 - (N + m - 1 - i) = i by omega] at this
        rw [this]; exact .rfl
      · exact .bot
    | _ => exact .bot
  have hC : LE_Interp.Const env (d.recName j) ls (LE_Interp env (pushAll ρ₀ zs))
      ((WShape.bot : WShape (K+1)) :: (pre ++ isS).reverse) y'' := by
    refine .kIota hs rfl hq hj hTc hPA hlarge
      (by simp [pre, isS, VInductDecl.majorIdx, hidxl, ← hN]; omega) hh' ?_
    rw [List.reverse_reverse, ← Nat.add_assoc, hN, List.take_left' (by simp [pre]; omega),
      List.drop_left' (by simp [pre]; omega)]
    refine hAppS.args_mono ?_
    rw [← List.take_append_drop N zs]
    refine List.forall₂_append' ?_ ?_
    · have := forall₂_le_lift (K := K + 1) (xs := zs.take N) fun z hz =>
        hKz z (List.mem_of_mem_take hz)
      simpa [pre, List.map_map, Function.comp_def] using this
    · refine List.forall₂_of_getElem? (by simp [kFieldShapes, hm]; omega) fun k a b ha hb => ?_
      have hk : k < m := by
        have := (List.getElem?_eq_some_iff.1 hb).1; simpa [kFieldShapes, hm] using this
      rw [List.getElem?_drop] at ha
      obtain ⟨hka, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      simp only [kFieldShapes, List.getElem?_map, List.getElem?_range (show k < c.fields.length by omega),
        Option.map_some, Option.some.injEq] at hb
      subst hb
      split
      · next i hi =>
        have hii := hidx k i hk hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_map]
        simp only [isS, List.getElem?_map, hii, Option.map_some, Option.getD_some, ishape]
        rw [dif_pos (by omega)]
        have key : ∀ (a b : Nat) (ha : a < zs.length) (hb : b < zs.length), a = b →
            zs[a] ≤ (WShape.lift (K + 1) zs[b].snd).T := by
          intro a b ha hb e; subst e; exact (TShape.lift_eqv (hKz _ (List.getElem_mem _))).2
        exact key _ _ _ _ (by omega)
      · next hi => exact hproof k (by omega) hi
  have hpre : List.Forall₂ (fun (x : WShape (K+1)) A => LE_Interp env (pushAll ρ₀ zs) x.T A)
      pre (VExpr.bvars N m) := by
    refine List.forall₂_of_getElem? (by
      rw [List.length_map, List.length_take, VExpr.length_bvars]; omega) fun i a A ha hA => ?_
    have hi : i < N := by have := (List.getElem?_eq_some_iff.1 hA).1; simpa using this
    simp only [pre, List.getElem?_map, List.getElem?_take, if_pos hi] at ha
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 ha
    rw [List.getElem?_eq_some_iff] at hA hz
    obtain ⟨-, rfl⟩ := hA; obtain ⟨hiz, rfl⟩ := hz
    rw [getElem_bvars]
    refine bvar_iff.2 ((TShape.lift_eqv (hKz _ (List.getElem_mem hiz))).1.trans ?_)
    rw [show N - 1 - i + m = N + m - 1 - i by omega, pushAll_bvar hzl i hiz]
    exact .rfl
  have hargs : List.Forall₂ (fun (x : WShape (K+1)) A => LE_Interp env (pushAll ρ₀ zs) x.T A)
      ((WShape.bot : WShape (K+1)) :: (pre ++ isS).reverse)
      (VExpr.bvars N m ++ idx ++ [major]).reverse := by
    have e : (VExpr.bvars N m ++ idx ++ [major]).reverse =
        major :: (VExpr.bvars N m ++ idx).reverse := by simp
    rw [e]
    refine .cons .bot (List.Forall₂.reverse.2 (List.forall₂_append' hpre ?_))
    exact List.forall₂_map_left_iff.2 (List.forall₂_refl'
      (r := fun e A => LE_Interp env (pushAll ρ₀ zs) (ishape e).T A) hish)
  have hLS' := hLS
  rw [← spine_eq_appN] at hLS' ⊢
  exact (LE_Interp.apps_realize hM W hty hb hLS' hargs hC).mono hyle

/-! ### Telescopes in the model -/

theorem StrongSound.forallE_inv (H : StrongSound env U Γ (.forallE A B) T) :
    ∃ u v, StrongSound env U Γ A (.sort u) ∧ StrongSound env U (A::Γ) B (.sort v) := by
  obtain ⟨-, -, core, -⟩ := H
  cases core with | forallE h1 h2 => exact ⟨_, _, h1, h2⟩

/-- Each binder of a pi telescope the model types is a type over the binders before it. -/
theorem StrongSound.foralls_getElem : ∀ {Qs : List VExpr} {Γ : List VExpr} {B T : VExpr},
    StrongSound env U Γ (.foralls Qs B) T → ∀ k (h : k < Qs.length),
    ∃ u, StrongSound env U ((Qs.take k).reverse ++ Γ) Qs[k] (.sort u)
  | [], _, _, _, _, k, h => absurd h (by simp)
  | A :: Qs, Γ, B, T, H, k, h => by
    obtain ⟨u, v, hA, hB⟩ := StrongSound.forallE_inv H
    cases k with
    | zero => exact ⟨u, by simpa using hA⟩
    | succ k =>
      obtain ⟨u', h'⟩ := StrongSound.foralls_getElem hB k (by simpa using h)
      exact ⟨u', by simpa using h'⟩

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.ClosedN.subst_dflt_consList_subst {e : VExpr} {as : List VExpr}
    (he : e.ClosedN as.length) (σ : VExpr.Subst) :
    (e.subst (VExpr.Subst.dflt.consList as)).subst σ =
      e.subst (VExpr.Subst.dflt.consList (as.map (·.subst σ))) := by
  rw [VExpr.subst_subst, VExpr.Subst.consList_comp]
  refine he.subst_congr fun i hi => ?_
  rw [VExpr.Subst.consList_apply, VExpr.Subst.consList_apply, dif_pos (by simpa using hi),
    dif_pos (by simpa using hi)]
  try simp [← List.map_reverse]

/-- Terms typed along a telescope over a closed telescope, instantiated by terms typed along that
one, are typed along the first. -/
theorem TeleSubst.substTele (hM : ModelEnv env) {Δ Qs σs τs : List VExpr}
    (H : TeleSubst env Δ.reverse Qs σs) (Hτ : TeleSubst env Γ Δ τs)
    (hcl : ∀ x ∈ σs, x.ClosedN τs.length) :
    TeleSubst env Γ Qs (σs.map (·.subst (VExpr.Subst.dflt.consList τs))) where
  len := by simp [H.len]
  tele := H.tele
  typed i A x h1 h2 := by
    rw [List.getElem?_map] at h2
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h2
    have := SoundTy.substTele hM Hτ (hcl x' (List.mem_of_getElem? hx')) (H.typed i A x' h1 hx')
    obtain ⟨hAcl, -⟩ := H.tele i A h1
    have hil : i ≤ σs.length := by
      have := (List.getElem?_eq_some_iff.1 hx').1; omega
    rw [VExpr.ClosedN.subst_dflt_consList_subst (by simpa [hil] using hAcl)] at this
    simpa [List.map_take] using this

/-! ### The types of applications of variables -/

variable (env) in
/-- At every fitting valuation, the interpretations of `X` interpret `Y`. -/
def SoundLe (Γ : List VExpr) (X Y : VExpr) : Prop :=
  ∀ ⦃Γ₀ ρ⦄, Valuation.Fits env Γ₀ Γ ρ → ∀ {m}, LE_Interp env ρ m X → LE_Interp env ρ m Y

theorem SoundEq.le (H : SoundEq env Γ X Y) : SoundLe env Γ X Y := fun _ _ W _ h => (H W).1 h
theorem SoundLe.trans (H1 : SoundLe env Γ X Y) (H2 : SoundLe env Γ Y Z) : SoundLe env Γ X Z :=
  fun _ _ W _ h => H2 W (H1 W h)

/-- If the interpretations of a pi type interpret another, under the first's domain its codomain's
interpret the other's. -/
theorem SoundLe.forallE (hM : ModelEnv env) (H : SoundLe env Γ (.forallE A B) (.forallE A' B')) :
    SoundLe env (A::Γ) B B' := by
  intro Γ₀ ρ W m h
  cases W with
  | nil =>
    have := H .nil <| .forallE' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
    · have := (this.forallE_inv' hM).2 .bot
      simp [WShapeFun.single_app] at this
      refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
    · refine fun _ => ⟨_, WShape.bot_le, .bot' (.bot' .sort), ?_⟩
      simpa [WShapeFun.single_app] using .rfl
    · intro x h'; cases h'.bot_r
      simpa [WShapeFun.single_app, show m.2.T = m from rfl] using
        h.mono_l fun _ => TShape.bot_le'
  | @cons Γ ρ A a x b1 b2 b3 b4 =>
    let k := max (max x.1 m.1) a.1
    have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
    have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
    have b3' := b3.lift hk.2
    have := H b1 <| .forallE' (f := .single (x.2.lift k) (m.2.lift k)) b3' b3'
      (WShape.HasDom.iff.2 ?_) ?_
    · have := (this.forallE_inv' hM).2 (x.2.lift k)
      simp [WShapeFun.single_app, WShape.LE.rfl] at this
      exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
        Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
    · intro x'; simp [WShapeFun.single_app]
      split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot' b4'.isType, WShape.bot_le⟩]
      refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
    · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
      refine (h.lift hk.1.2).mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact (TShape.lift_eqv hk.1.1).2.trans h2.T

theorem SoundLe.inst (hM : ModelEnv env) (ht : SoundTy env Γ X A)
    (hA : SoundTy env Γ A (.sort u)) (H : SoundLe env (A::Γ) M N) :
    SoundLe env Γ (M.inst X) (N.inst X) := fun _ ρ W m h => by
  obtain ⟨a, h1, h2⟩ := (LE_Interp.inst hM).1 h
  obtain ⟨a', t, a1, a2, a3, a4⟩ := ht W h2
  refine (LE_Interp.inst hM).2 ⟨_, H (W.cons (InterpTyped.hsort (hA W)) a3 a4) ?_, a2⟩
  exact h1.mono_l (Valuation.LE.push.2 ⟨.rfl, a1⟩)

omit [ShapeEnv] in
theorem inst_foralls_gen (a : VExpr) : ∀ (Ps : List VExpr) (E : VExpr) (k : Nat),
    (VExpr.foralls Ps E).inst a k =
      .foralls ((Ps.zipIdx k).map fun (P, i) => P.inst a i) (E.inst a (k + Ps.length))
  | [], E, k => by simp [VExpr.foralls]
  | P :: Ps, E, k => by
    simp only [VExpr.foralls, VExpr.inst, List.zipIdx_cons, List.map_cons, List.length_cons]
    rw [inst_foralls_gen a Ps E (k+1)]
    simp [Nat.add_assoc, Nat.add_comm 1]

section
variable (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
  (hO : E.Ordered) {Γ : List VExpr} (hΓ : OnCtx Γ (E.IsType U))
include hM hX hle hO hΓ

/-- A variable's types, in an environment the model is sound for, are its declared type's. -/
theorem bvar_type_sound {i : Nat} {V : VExpr} (H : E.HasType U Γ (.bvar i) V) :
    ∃ A, Lookup Γ i A ∧ SoundEq env Γ A V := by
  replace H := (H.strong hO hΓ).hasType'.1
  generalize eqb : true = b, eq' : VExpr.bvar i = e' at H
  induction H with cases eqb
  | defeq _ h2 _ _ _ _ _ ih =>
    obtain ⟨A, h1, h3⟩ := ih hΓ rfl eq'
    exact ⟨A, h1, h3.trans (hX.strongSound' hM hle hO hΓ h2.defeq).sound⟩
  | base H => subst eq'; let .bvar h1 .. := H; exact ⟨_, h1, .rfl⟩

/-- An application's types, in an environment the model is sound for, are its function's
codomain at the argument. -/
theorem app_type_sound {f a V : VExpr} (H : E.HasType U Γ (.app f a) V) :
    ∃ A B u, E.HasType U Γ f (.forallE A B) ∧ SoundTy env Γ a A ∧
      SoundTy env Γ A (.sort u) ∧ SoundEq env Γ (B.inst a) V := by
  replace H := (H.strong hO hΓ).hasType'.1
  generalize eqb : true = b, eq' : f.app a = e' at H
  induction H with cases eqb
  | defeq _ h2 _ _ _ _ _ ih =>
    obtain ⟨A, B, u, h1, h3, h4, h5⟩ := ih hΓ rfl eq'
    exact ⟨A, B, u, h1, h3, h4, h5.trans (hX.strongSound' hM hle hO hΓ h2.defeq).sound⟩
  | base H =>
    subst eq'
    let .app _ _ hA _ _ hf ha _ := H
    exact ⟨_, _, _, hf.hasType, (hX.strongSound' hM hle hO hΓ ha.hasType).left.sound,
      (hX.strongSound' hM hle hO hΓ hA.hasType).left.sound, .rfl⟩

/-- An application of a variable whose type is a pi telescope ending in a sort, to as many
arguments as the telescope's binders, is typed, in an environment the model is sound for, only at
sorts the model cannot tell from that sort below. -/
theorem spine_sort_le : ∀ (args : List VExpr) (F K : VExpr) (Ps : List VExpr) (v : VLevel),
    K = .foralls Ps (.sort v) → Ps.length = args.length →
    (∀ T, E.HasType U Γ F T → SoundLe env Γ T K) →
    ∀ S, E.HasType U Γ (F.appN args) S → SoundLe env Γ S (.sort v)
  | [], F, K, Ps, v, hK, hl, hF, S, H => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    have := hF S H; rw [hK] at this; exact this
  | a :: args, F, K, P :: Ps, v, hK, hl, hF, S, H => by
    refine spine_sort_le args (.app F a) (VExpr.inst (.foralls Ps (.sort v)) a)
      (Ps.zipIdx.map fun (P, i) => P.inst a i) v ?_ (by simpa using hl) ?_ S H
    · rw [inst_foralls_gen]; rfl
    · intro T hT
      obtain ⟨A, B, u, h1, h2, h3, h4⟩ := app_type_sound hM hX hle hO hΓ hT
      have := hF _ h1; rw [hK] at this
      exact h4.symm.le.trans (SoundLe.inst hM h2 h3 (this.forallE hM))
end

/-- A term typed at a type of a sort the model reads as `Prop` has only `bot` as interpretation. -/
theorem SoundTy.le_bot {R X : VExpr} {w : VLevel} (hR : SoundTy env Γ R X)
    (hX : SoundTy env Γ X (.sort w)) (hw : levelRel w = false) {Γ₀ : List VExpr} {ρ : Valuation}
    (W : Valuation.Fits env Γ₀ Γ ρ) {m : TShape} (h : LE_Interp env ρ m R) : m ≤ TShape.bot := by
  obtain ⟨_, _, a1, -, a3, a4⟩ := hR W h
  obtain ⟨_, _, b1, -, b3, b4⟩ := hX W a3
  have b4' := TShape.HasType.mono_r (by simpa [hw] using b3.le_sort) .sort b4
  exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))

/-- A sort the model reads below `Prop` is read as `Prop`. -/
theorem levelRel_of_le {w v : VLevel} (H : SoundLe env Γ (.sort w) (.sort v))
    {Γ₀ : List VExpr} {ρ : Valuation} (W : Valuation.Fits env Γ₀ Γ ρ) :
    levelRel w = levelRel v := by
  have h := WShape.LE.of_T (n := 0) (H W LE_Interp.sort').le_sort
  generalize levelRel w = r, levelRel v = r' at h
  exact Shape0.sort.inj (congrArg (·.1) (WShape.sort_le.1 h))

/-- Under a telescope typed in an environment the model is sound for, a term whose type is an
application of a variable of a predicate type (a pi telescope ending in a sort the model reads as
`Prop`) to all its arguments has only `bot` as interpretation. -/
theorem le_bot_of_pred (hM : ModelEnv env) {E : VEnv} (hX : SoundHyps E env) (hle : E ≤ env)
    (hO : E.Ordered) {Bs : List VExpr} (hT : E.IsTele U [] Bs) {CT : VExpr}
    (hCT : E.IsType U Bs.reverse CT) {i : Nat} (hi : i < Bs.length) {Ps : List VExpr}
    {v : VLevel} (hK : Bs[i].liftN (Bs.length - i) = .foralls Ps (.sort v))
    (hv : levelRel v = false) {args : List VExpr}
    (hCTe : CT = (VExpr.bvar (Bs.length - 1 - i)).appN args) (hl : Ps.length = args.length)
    {R B : VExpr} (hR : SoundTy env Bs.reverse R B) (hBC : SoundEq env Bs.reverse B CT)
    {Γ₀ : List VExpr} {σ : Valuation} (W : Valuation.Fits env Γ₀ Bs.reverse σ) {y : TShape}
    (h : LE_Interp env σ y R) : y ≤ TShape.bot := by
  have hΓ : OnCtx Bs.reverse (E.IsType U) := by simpa using hT.onCtx trivial
  obtain ⟨w, hw⟩ := hCT
  have hL := Lookup.reverse_append Bs (Γ := []) i hi
  rw [List.append_nil] at hL
  have hle' := spine_sort_le hM hX hle hO hΓ args _ _ Ps v hK hl (fun T hT' => by
    obtain ⟨A, hA, hS⟩ := bvar_type_sound hM hX hle hO hΓ hT'
    cases hA.uniq hL; exact hS.symm.le) (.sort w) (hCTe ▸ hw)
  have hwv := levelRel_of_le hle' W
  have hCTs := (hX.strongSound' hM hle hO hΓ hw).left.sound
  exact SoundTy.le_bot (hR.defeq_r hBC) hCTs (hwv ▸ hv) W h

omit [ShapeEnv] in
theorem FieldsWF.hasType_getElem {E : VEnv} {d : VInductDecl} :
    ∀ {Γ : List VExpr} {k : Nat} {Ds : List VExpr} {fs : List VField}, d.FieldsWF E Γ k Ds fs →
    ∀ i (f : VField), fs[i]? = some f →
      E.HasType d.uvars (((fs.take i).map (·.type)).reverse ++ Γ) f.type (.sort f.level)
  | _, _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, _, .cons _ h2 _ _ _ _ _, 0, _, h => by
    cases h; simpa using h2
  | _, _, _, _, .cons _ _ _ _ _ _ hF, i+1, f, h => by
    have := FieldsWF.hasType_getElem hF i f (by simpa using h)
    simpa using this

omit [ShapeEnv] in
theorem Ctx.LiftN.liftTele {n : Nat} : ∀ (As : List VExpr) {k : Nat} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (k + As.length) (As.reverse ++ Γ) ((VExpr.liftTele n As k).reverse ++ Γ')
  | [], _, _, _, W => by simpa [VExpr.liftTele] using W
  | A :: As, k, Γ, Γ', W => by
    have := Ctx.LiftN.liftTele As (k := k+1) (W.succ (A := A))
    simpa [VExpr.liftTele, Nat.add_assoc, Nat.add_comm 1] using this

omit [ShapeEnv] in
theorem take_liftTele (n : Nat) : ∀ (As : List VExpr) (k i : Nat),
    (VExpr.liftTele n As k).take i = VExpr.liftTele n (As.take i) k
  | [], _, _ => by simp [VExpr.liftTele]
  | _ :: _, _, 0 => by simp [VExpr.liftTele]
  | _ :: As, k, i+1 => by simp [VExpr.liftTele, take_liftTele n As (k+1) i]

/-- A field of a constructor whose type is a proposition at the block levels `lsB` has, at a value
for the iota rule's binders, `bot` as value. -/
theorem iota_proof_field (hM : ModelEnv env) {E envT : VEnv} (hX : SoundHyps E env)
    (hle : E ≤ env) (hO : E.Ordered) (hTE : envT ≤ E) {d : VInductDecl} {Tj : VInductiveType}
    {c : VConstructor} (hcW : c.WF envT d Tj) {lsB : List VLevel} {v : VLevel}
    (hlsB : ∀ l ∈ lsB, l.WF U) (hTel : E.IsTele U [] (d.iotaBinders lsB v c))
    {k : Nat} {f : VField} (hf : c.fields[k]? = some f) (hf0 : f.level.inst lsB ≈ .zero)
    {Γ₀ : List VExpr} {ρ : Valuation} {zs : List TShape}
    (hST : SoundTele env [] (d.iotaBinders lsB v c)) (W0 : Valuation.Fits env Γ₀ [] ρ)
    (hF : LamsFit env ρ (d.iotaBinders lsB v c) zs)
    (hk : d.params.length + d.allTypes.length + d.allCtors.length + k < zs.length) :
    zs[d.params.length + d.allTypes.length + d.allCtors.length + k] ≤ TShape.bot := by
  have hkf : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨-, Ds, -, -, hFW, -, -⟩ := hcW.shape
  have hft := FieldsWF.hasType_getElem hFW k f hf
  have hft' := (hft.instL hlsB).mono hTE
  simp only [List.map_append, List.map_reverse, VExpr.instL, List.map_map, Function.comp_def]
    at hft'
  have W := Ctx.LiftN.liftTele (n := d.allTypes.length + d.allCtors.length)
    ((c.fields.take k).map (·.type.instL lsB))
    (Ctx.LiftN.zero (Γ := (d.params.map (·.instL lsB)).reverse)
      (d.motiveTypes lsB v ++ d.minorTypes lsB).reverse
      (by simp only [List.length_reverse, List.length_append, VInductDecl.length_motiveTypes,
        VInductDecl.minorTypes, List.length_map, List.length_zipIdx]))
  have hft'' := hft'.weakN hO W
  simp only [Nat.zero_add, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hkf),
    VExpr.liftN] at hft''
  -- the prefix of the binders
  have hBs : (d.iotaBinders lsB v c).take (d.params.length + d.allTypes.length +
      d.allCtors.length + k) = d.params.map (·.instL lsB) ++ (d.motiveTypes lsB v ++
        d.minorTypes lsB) ++ VExpr.liftTele (d.allTypes.length + d.allCtors.length)
          ((c.fields.take k).map (·.type.instL lsB)) := by
    simp only [VInductDecl.iotaBinders, VInductDecl.recBinders]
    rw [List.take_append, List.take_of_length_le (by
      simp [VInductDecl.minorTypes]; omega), take_liftTele, ← List.map_take]
    simp only [VInductDecl.minorTypes, List.length_append, List.length_map,
      VInductDecl.length_motiveTypes, List.length_zipIdx, List.append_assoc]
    rw [show d.params.length + d.allTypes.length + d.allCtors.length + k -
      (d.params.length + (d.allTypes.length + d.allCtors.length)) = k by omega]
  have hBl : (d.iotaBinders lsB v c).length =
      d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length := by
    simp [VInductDecl.iotaBinders, VInductDecl.recBinders, VInductDecl.minorTypes, Nat.add_assoc]
  have hTel' := (VEnv.IsTele.append_inv (by rw [List.take_append_drop]; exact hTel :
    E.IsTele U [] ((d.iotaBinders lsB v c).take (d.params.length + d.allTypes.length +
      d.allCtors.length + k) ++ (d.iotaBinders lsB v c).drop (d.params.length +
      d.allTypes.length + d.allCtors.length + k)))).1
  have hΓ : OnCtx ((d.iotaBinders lsB v c).take (d.params.length + d.allTypes.length +
      d.allCtors.length + k)).reverse (E.IsType U) := by simpa using hTel'.onCtx trivial
  rw [hBs] at hΓ
  simp only [List.reverse_append, List.append_assoc] at hΓ hft''
  have hS := (hX.strongSound' hM hle hO hΓ hft'').left.sound
  -- the field's value, typed at its binder's type
  obtain ⟨b, hb, hzb⟩ := hF.getElem _ hk (by rw [hBl]; omega)
  have hBk : (d.iotaBinders lsB v c)[d.params.length + d.allTypes.length + d.allCtors.length + k]'
      (by rw [hBl]; omega) = (f.type.instL lsB).liftN (d.allTypes.length + d.allCtors.length) k := by
    simp only [VInductDecl.iotaBinders]
    rw [List.getElem_append_right (by simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega)]
    rw [VExpr.getElem_liftTele]
    have key : ∀ a (ha : a < c.fields.length), a = k →
        VExpr.liftN (d.allTypes.length + d.allCtors.length) ((c.fields[a]).type.instL lsB) a =
        VExpr.liftN (d.allTypes.length + d.allCtors.length) (f.type.instL lsB) k := by
      intro a ha e; subst e; rw [(List.getElem?_eq_some_iff.1 hf).2]
    simp only [List.getElem_map, VInductDecl.recBinders, VInductDecl.minorTypes,
      List.length_append, List.length_map, VInductDecl.length_motiveTypes, List.length_zipIdx,
      Nat.zero_add]
    exact key _ _ (by omega)
  rw [hBk] at hb
  have W := LamsFit.fits_take hST W0 hF (d.params.length + d.allTypes.length + d.allCtors.length + k)
  rw [hBs] at W
  simp only [List.reverse_append, List.append_assoc, List.append_nil] at W
  obtain ⟨_, _, b1, -, b3, b4⟩ := hS W hb
  have hr : levelRel (f.level.inst lsB) = false := by rw [levelRel_congr hf0, levelRel_zero]
  have b4' := TShape.HasType.mono_r (by simpa [hr] using b3.le_sort) .sort b4
  exact b4'.proofIrrel (b4'.mono_r b1 hzb)

/-! ### Constructor applications of a block's types, auxiliary ones included -/

/-- An interpretation of a constructor of one of a block's types, auxiliary ones included (an
earlier type's constructor at the occurrence's parameters), applied to its parameters and fields:
`bot`, or a constructor shape of the constructor's name, with fields interpreting the fields. -/
theorem ctorApp_inv_all (hM : ModelEnv env) {E₁ : VEnv} (hE₁ : E₁.WF) (hle₁ : E₁ ≤ env)
    {d : VInductDecl} (hd : d.WF E₁) {envT : VEnv} (hT : E₁.addConstList d.typeConsts = some envT)
    {s : Name} {t₀ : Nat} (hs : env.inducts s = some (d, t₀)) {j : Nat} {T : VInductiveType}
    {c : VConstructor} (hj : d.allTypes[j]? = some T) (hc : c ∈ T.ctors) {ls : List VLevel}
    {ps fs : List VExpr} (hps : ps.length = d.params.length)
    (hfs : fs.length = c.fields.length) {ρ : Valuation} {m : TShape}
    (H : LE_Interp env ρ m (T.ctorApp c ls ps fs)) :
    m ≤ TShape.bot ∨ ∃ k, ∃ rf : List (WShape k),
      List.Forall₂ (fun x A => LE_Interp env ρ x.T A) rf fs ∧ m ≤ (WShape.ctor' c.name rf).T := by
  have hTm : T ∈ d.allTypes := List.mem_of_getElem? hj
  cases hn : T.nested with
  | none =>
    have hjt : j < d.types.length := by
      refine Classical.byContradiction fun h => ?_
      have hja : d.aux[j - d.types.length]? = some T := by
        rw [VInductDecl.allTypes, List.getElem?_append_right (by omega)] at hj; exact hj
      obtain ⟨n, hn', -⟩ := hd.aux T (List.mem_of_getElem? hja)
      rw [hn] at hn'; cases hn'
    have hTj : d.types[j]? = some T := by
      rw [VInductDecl.allTypes, List.getElem?_append_left hjt] at hj; exact hj
    rw [VInductiveType.ctorApp_of_none hn] at H
    rcases ctorApp_inv hM hs hTj hc hps hfs H with h | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  | some n =>
    have hTa : T ∈ d.aux := by
      rcases List.mem_append.1 hTm with h | h
      · rw [(hd.types T h).2] at hn; cases hn
      · exact h
    obtain ⟨n', hn', hA⟩ := hd.aux T hTa
    rw [hn] at hn'; cases hn'
    obtain ⟨⟨dI, tI, TI, hsI, hTI, -, -, hargs, -, -, hctors⟩⟩ := hA envT hT
    rw [VEnv.addConstList_inducts hT] at hsI
    have hsI' : env.inducts n.ind = some (dI, tI) := hle₁.inducts hsI
    obtain ⟨cI, hcI, hname, hcorr⟩ := List.Forall₂.forall_exists_r hctors c hc
    obtain ⟨env₀, envTI, envCI, envRI, hB⟩ := VEnv.WF.blockEnvs hE₁ hsI
    have hTIm : TI ∈ dI.types := List.mem_of_getElem? hTI
    have hdI : dI.WF env₀ := hB.decl
    have hcIW := (hdI.ctors envTI hB.hT TI (List.mem_append_left _ hTIm)).2 cI hcI
    have hcW := (hd.ctors envT hT T hTm).2 c hc
    obtain ⟨hfl, -⟩ := VInductDecl.auxCounts hn hcW (hdI.types TI hTIm).2 hcIW hargs hcorr
    simp only [VInductiveType.ctorApp, hn, hname] at H
    rcases ctorApp_inv hM hsI' hTI hcI (by simpa using hargs) (by rw [hfs, hfl]) H with
      h | ⟨-, h⟩
    · exact .inl h
    · rw [← hname] at h; exact .inr h

/-! ### Assembling an iota rule's soundness -/

omit [ShapeEnv] in
theorem fieldIdx_spec {c : VConstructor} {k i : Nat} (h : VInductDecl.fieldIdx c k = some i) :
    c.indices[i]? = some (.bvar (c.fields.length - 1 - k)) := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  rw [List.getElem?_eq_getElem hi]
  revert hp; generalize c.indices[i] = e
  cases e <;> simp [VExpr.isBVar]
  intro h; subst h; rfl

/-- The left body of the iota rule for the `q`th constructor `c`, of the `j`th type, at block levels
`lsB`, motive sort `v` and recursor levels `recLs`. -/
def iotaL (d : VInductDecl) (lsB : List VLevel) (recLs : List VLevel) (j : Nat)
    (c : VConstructor) : VExpr :=
  let n := d.params.length
  let T := d.allTypes.length
  let C := d.allCtors.length
  let m := c.fields.length
  (d.recConst recLs j).appN (VExpr.bvars n (T + C + m) ++ VExpr.bvars T (C + m) ++
    VExpr.bvars C m ++ c.indices.map (fun e => (e.instL lsB).reseat (T + C) m m 0 0) ++
    [d.ctorAppAt j c lsB (VExpr.bvars n (T + C + m)) (VExpr.bvars m 0)])

/-- The codomain of the iota rule's type: the motive at the constructor's indices and the
constructor application. -/
def iotaCT (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor) : VExpr :=
  let T := d.allTypes.length
  let C := d.allCtors.length
  let m := c.fields.length
  .app (.appN (.bvar (m + C + (T - 1 - j)))
    (c.indices.map (fun e => (e.instL lsB).reseat (T + C) m m 0 0)))
    (d.ctorAppAt j c lsB (VExpr.bvars d.params.length (T + C + m)) (VExpr.bvars m 0))

omit [ShapeEnv] in
theorem iotaRule_type (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (recLs : List VLevel)
    (q j : Nat) (c : VConstructor) :
    (d.iotaRule lsB v recLs q j c).type = .foralls (d.iotaBinders lsB v c) (iotaCT d lsB j c) :=
  rfl

omit [ShapeEnv] in
theorem iotaRule_lhs (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (recLs : List VLevel)
    (q j : Nat) (c : VConstructor) :
    (d.iotaRule lsB v recLs q j c).lhs = .lams (d.iotaBinders lsB v c) (iotaL d lsB recLs j c) :=
  rfl

omit [ShapeEnv] in
theorem iotaRule_rhs_lams (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (recLs : List VLevel)
    (q j : Nat) (c : VConstructor) :
    ∃ R, (d.iotaRule lsB v recLs q j c).rhs = .lams (d.iotaBinders lsB v c) R :=
  ⟨_, rfl⟩

omit [ShapeEnv] in
theorem iotaL_eq (d : VInductDecl) (lsB : List VLevel) (recLs : List VLevel) (j : Nat)
    (c : VConstructor) :
    iotaL d lsB recLs j c = (VExpr.const (d.recName j) recLs).appN
      (VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
        c.indices.map (fun e => (e.instL lsB).reseat (d.allTypes.length + d.allCtors.length)
          c.fields.length c.fields.length 0 0) ++
        [d.ctorAppAt j c lsB (VExpr.bvars d.params.length
          (d.allTypes.length + d.allCtors.length + c.fields.length))
          (VExpr.bvars c.fields.length 0)]) := by
  simp only [iotaL, VInductDecl.recConst]
  congr 2
  rw [← bvars_append', Nat.add_assoc, ← bvars_append']

omit [ShapeEnv] in
theorem iotaIdx_spec {c : VConstructor} {lsB : List VLevel} {a : Nat} {k i : Nat}
    (hk : k < c.fields.length) (h : VInductDecl.fieldIdx c k = some i) :
    (c.indices.map (fun e => (e.instL lsB).reseat a c.fields.length c.fields.length 0 0))[i]? =
      some (.bvar (c.fields.length - 1 - k)) := by
  rw [List.getElem?_map, fieldIdx_spec h]
  simp only [Option.map_some, VExpr.instL, VExpr.reseat, VExpr.liftN, Nat.sub_self,
    Nat.add_zero, Option.some.injEq]
  have : c.fields.length - 1 - k < c.fields.length := by omega
  simp [liftVar, this]

omit [ShapeEnv] in
theorem length_iotaBinders (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (c : VConstructor) :
    (d.iotaBinders lsB v c).length =
      d.params.length + d.allTypes.length + d.allCtors.length + c.fields.length := by
  simp [VInductDecl.iotaBinders, VInductDecl.recBinders, VInductDecl.minorTypes, Nat.add_assoc]

/-- An iota rule is sound in the model, given what its two directions need under its binders:
forward, that the major premise's interpretations are constructor shapes of the fields' values
(`hfwd`); backward, the right body's interpretations interpreting the left body at valuations
fitting the binders (`hbwd`). -/
theorem iotaRuleSound_of (hM : ModelEnv env) {s : Name} {d : VInductDecl} {t₀ j q : Nat}
    {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (hj : d.allTypes[j]? = some Tj) (hq : d.allCtors[q]? = some (j, c))
    (hcidx : c.indices.length = Tj.indices.length)
    (hcl : (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).lhs.ClosedN ∧
      (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.ClosedN)
    (hfwd : ∀ (lsB : List VLevel) (σ : Valuation) (x : TShape),
      LE_Interp env σ x (d.ctorAppAt j c lsB (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + c.fields.length))
        (VExpr.bvars c.fields.length 0)) →
      x ≤ TShape.bot ∨ ∃ N, ∃ rf : List (WShape N),
        List.Forall₂ (fun z A => LE_Interp env σ z.T A) rf (VExpr.bvars c.fields.length 0) ∧
        x ≤ (WShape.ctor' c.name rf).T)
    (hbwd : ∀ (ls : List VLevel), (∀ l ∈ ls, l.WF U) → ls.length = d.recUVars → ∀ R,
      (d.iotaRule (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) ls q j c).rhs =
        .lams (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c) R →
      ∀ {B B' : VExpr} {Γ₀ : List VExpr} {ρ : Valuation} {zs : List TShape},
      LamsFit env ρ (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c) zs →
      Valuation.Fits env Γ₀ (d.iotaBinders (d.recLevels.map (·.inst ls))
        (d.motiveLevel.inst ls) c).reverse (pushAll ρ zs) →
      StrongSound env U (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
        (iotaL d (d.recLevels.map (·.inst ls)) ls j c) B →
      StrongSound env U (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
        R B' →
      SoundEq env (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
        B B' →
      SoundEq env (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c).reverse
        B' (iotaCT d (d.recLevels.map (·.inst ls)) j c) →
      SoundTele env [] (d.iotaBinders (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) c) →
      Valuation.Fits env Γ₀ [] ρ →
      ∀ y, LE_Interp env (pushAll ρ zs) y R →
        LE_Interp env (pushAll ρ zs) y (iotaL d (d.recLevels.map (·.inst ls)) ls j c)) :
    RuleSound env U (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c) := by
  intro Γ ls hls hlen h1 h2 _ _
  have hlen' : ls.length = d.recUVars := by simpa [VInductDecl.iotaRule] using hlen
  have hp : (VLevel.params d.recUVars).map (VLevel.inst ls) = ls := VLevel.inst_map_id hlen'
  obtain ⟨hL, hR, hTy⟩ := d.iotaRule_instL d.recLevels ls (VLevel.params d.recUVars)
    d.motiveLevel q j c
  rw [hp] at hL hR hTy
  have hcl1 := hcl.1.instL (ls := ls); have hcl2 := hcl.2.instL (ls := ls)
  rw [hL] at h1 hcl1 ⊢; rw [hR] at h2 hcl2 ⊢; rw [hTy] at h1 h2
  refine SoundEq.closed hM hcl1 hcl2 ?_
  generalize hlsB : d.recLevels.map (·.inst ls) = lsB at *
  generalize hv : d.motiveLevel.inst ls = v at *
  obtain ⟨R, hRe⟩ := iotaRule_rhs_lams d lsB v ls q j c
  rw [iotaRule_lhs] at h1 ⊢
  rw [hRe] at h2 ⊢
  obtain ⟨BL, hTel, hLS, hBL⟩ := h1.lams_inv
  obtain ⟨BR, -, hRS, hBR⟩ := h2.lams_inv
  have hBB := SoundEq.foralls_inv hM hTel (hBL.trans hBR.symm)
  rw [iotaRule_type] at hBR
  have hBC := SoundEq.foralls_inv hM hTel hBR
  simp only [List.append_nil] at hLS hRS hBB hBC
  have hiR : d.iotaRhs ls q j c = .lams (d.iotaBinders lsB v c) R := by
    rw [VInductDecl.iotaRhs, hR, hRe]
  refine SoundEq.lams_fit hTel fun {Γ₀ ρ} xs W0 hF W' y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [iotaL_eq] at hy
    exact iota_body_le hM hs hj hq hiR (length_iotaBinders ..) (by simp [hcidx])
      (fun k i hk hi => iotaIdx_spec hk hi) (hfwd lsB (pushAll ρ xs)) hy
  · subst hlsB hv
    exact hbwd ls hls hlen' R hRe hF (by simpa using W') hLS hRS hBB hBC hTel W0 y hy

omit [ShapeEnv] in
theorem recLevels_inst (d : VInductDecl) {ls : List VLevel} (hlen : ls.length = d.recUVars) :
    d.recLevels.map (·.inst ls) = d.blockLevels ls := by
  unfold VInductDecl.recLevels VInductDecl.blockLevels VInductDecl.recUVars at *
  by_cases h : d.LargeElim
  · rw [if_pos h] at hlen ⊢
    rw [if_pos (show d.largeElim = true from h)]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp [VLevel.inst, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp at h2; omega)]; rfl
  · rw [if_neg h] at hlen ⊢
    rw [if_neg (show ¬d.largeElim = true from h)]
    exact VLevel.inst_map_id hlen

omit [ShapeEnv] in
theorem bvars_subst_consList (σ : VExpr.Subst) {a b : Nat} {l : List VExpr}
    (h : a + b ≤ l.length) :
    (VExpr.bvars a b).map (·.subst (σ.consList l)) = (l.drop (l.length - a - b)).take a := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
  rw [getElem_bvars (by simpa using h1), VExpr.subst_bvar, VExpr.Subst.consList_apply,
    dif_pos (by simp at h1; omega), List.getElem_reverse]
  congr 1; simp at h1; omega

/-- The recursor's telescope at the iota rule's levels, read off the recursor's type. -/
theorem rec_tele_facts (hM : ModelEnv env) {d : VInductDecl} {j : Nat} {Tj : VInductiveType}
    {ls : List VLevel} {u₀ : VLevel}
    (hrecS : StrongSound env U [] ((d.recType d.recLevels d.motiveLevel j Tj).instL ls) (.sort u₀))
    (hrecCl : ∀ i (A : VExpr), (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls)
      Tj)[i]? = some A → A.ClosedN i) :
    ∀ i (A : VExpr), (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj)[i]? =
      some A → A.ClosedN i ∧ ∃ u, SoundTy env
        ((d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj).take i).reverse A
        (.sort u) := by
  rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele] at hrecS
  intro i A hA
  refine ⟨hrecCl i A hA, ?_⟩
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hA
  obtain ⟨u, h⟩ := hrecS.foralls_getElem i hi
  exact ⟨u, by simpa using h.sound⟩

omit [ShapeEnv] in
theorem length_recTele (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (Tj : VInductiveType) :
    (d.recTele lsB v Tj).length =
      d.params.length + d.allTypes.length + d.allCtors.length + Tj.indices.length + 1 := by
  simp [VInductDecl.recTele, VInductDecl.recBinders, VInductDecl.minorTypes, Nat.add_assoc]

/-- A block type's telescope at levels `ls`, as `MSpine.ofTele` and `MSpine.spine` take it. -/
theorem typeTeleFacts (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {d : VInductDecl} {T : VInductiveType} {s : Name}
    (hTW : T.WF envT d) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants s = some ⟨d.uvars, T.type⟩) {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) :
    (∀ i (A : VExpr), ((d.params ++ T.indices).map (·.instL ls))[i]? = some A → A.ClosedN i ∧
      ∃ u, SoundTy env (((d.params ++ T.indices).map (·.instL ls)).take i).reverse A (.sort u)) ∧
    (VExpr.foralls ((d.params ++ T.indices).map (·.instL ls)) (.sort (d.level.inst ls))).ClosedN ∧
    ∀ {Γ : List VExpr} ci, env.constants s = some ci → ls.length = ci.uvars →
      SoundEq env Γ (ci.type.instL ls)
        (.foralls ((d.params ++ T.indices).map (·.instL ls)) (.sort (d.level.inst ls))) := by
  have hQT : envT.IsTele U [] ((d.params ++ T.indices).map (·.instL ls)) := by
    simpa using ((hPT.append (by simpa using hTW.indices)).instL hls (Γ := []))
  obtain ⟨_, hdef⟩ := hTW.defeq
  have hdef' := hdef.instL hls (ls := ls)
  rw [VEnv.foralls_instL'] at hdef'
  have hRcl := (hdef'.closedN' hO.closed trivial).2.1
  have hTcl : (T.type.instL ls).ClosedN := (hdef'.closedN' hO.closed trivial).1
  refine ⟨fun i A hA => ⟨by simpa using VEnv.IsTele.closedN hO hQT trivial i A hA,
    by simpa using IsTele.soundAt hM hX hle hO hQT trivial i A hA⟩, hRcl, ?_⟩
  intro Γ ci hci _
  cases hcT.symm.trans hci
  exact SoundEq.closed hM hTcl hRcl (hX.strongSound' hM hle hO (Γ := []) trivial hdef').sound

/-- The major premise of an iota rule for a block's own type, at levels where it is not a
proposition, at a valuation fitting the rule's binders: it has a constructor shape interpreting it,
with fields above the fields' values. -/
theorem iota_major_own (hM : ModelEnv env) {envT : VEnv} (hX : SoundHyps envT env)
    (hle : envT ≤ env) (hO : envT.Ordered) {d : VInductDecl} {j : Nat} {Tj : VInductiveType}
    {c : VConstructor} (hsT : env.inducts Tj.name = some (d, j)) (hTj : d.types[j]? = some Tj)
    (hj : d.allTypes[j]? = some Tj) (hTn : Tj.nested = none) {i : Nat}
    (hci : Tj.ctors[i]? = some c)
    (hidxc : (Tj.ctors.map (·.name)).idxOf? c.name = some i)
    (hTW : Tj.WF envT d) (hcW : c.WF envT d Tj) (hPT : envT.IsTele d.uvars [] d.params)
    (hcT : env.constants Tj.name = some ⟨d.uvars, Tj.type⟩)
    (hcC : env.constants c.name = some ⟨d.uvars, c.type⟩)
    (hrecC : env.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.recUVars)
    (hlsB : ∀ l ∈ d.recLevels.map (·.inst ls), l.WF U)
    (hP : ¬d.PropAt (d.recLevels.map (·.inst ls))) {u₀ : VLevel}
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
  have hcm : c ∈ Tj.ctors := List.mem_of_getElem? hci
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
  have hQmE : Qmaj = (VExpr.const Tj.name lsB).appN (VExpr.bvars d.params.length
      (d.allTypes.length + d.allCtors.length + Tj.indices.length) ++
      VExpr.bvars Tj.indices.length 0) := by
    rw [← hQme, VInductiveType.typeApp_of_none hTn]
  have hQsub : Qmaj.subst (VExpr.Subst.dflt.consList (VExpr.bvars N c.fields.length ++ idx)) =
      (VExpr.const Tj.name lsB).appN (VExpr.bvars d.params.length
        (d.allTypes.length + d.allCtors.length + c.fields.length) ++ idx) := by
    rw [hQmE, VExpr.subst_appN, hargsE]; rfl
  -- the constructor application, typed at the type
  have hmajE : major = (VExpr.const c.name lsB).appN (VExpr.bvars d.params.length
      (d.allTypes.length + d.allCtors.length + c.fields.length) ++
      VExpr.bvars c.fields.length 0) := by
    rw [← hmaje, VInductDecl.ctorAppAt_eq hj, VInductiveType.ctorApp_of_none hTn]
  rw [hmajE] at hmajS ⊢
  rw [hQsub] at hAQ
  have hCS := (hmajS.mspine').retype hAQ
  -- the type's spine, typed in the model
  have hlsBl : lsB.length = d.uvars := by
    rw [← hlsBe]; simp only [List.length_map, VInductDecl.recLevels]; split <;> simp
  obtain ⟨hQh, hRh, hXh⟩ := typeTeleFacts (U := U) hM hX hle hO hTW hPT hcT hlsB
  have hrecS' := hrecS
  rw [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele, hlsBe, hve] at hrecS'
  obtain ⟨uS, hQS⟩ := hrecS'.foralls_getElem (N + Tj.indices.length) (by rw [hQl]; omega)
  rw [(List.getElem?_eq_some_iff.1 hQk).2, hQmE, List.append_nil] at hQS
  obtain ⟨hTSq, -⟩ := typeSpine hM hX hle hO hTW hPT hcT hlsB (by simp) hQS.mspine'
  have hTSq' := TeleSubst.substTele hM (Δ := (d.recTele lsB v Tj).take (N + Tj.indices.length))
    (by simpa using hTSq) hpre (by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx <;> obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hx <;>
        rw [getElem_bvars] <;> simp at hi' <;> simp [VExpr.ClosedN, hK] <;> omega)
  rw [hargsE] at hTSq'
  have hQhl : ((d.params ++ Tj.indices).map (·.instL lsB)).length =
      (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) ++
        idx).length := by simp [hidxl]
  have hTS := MSpine.ofTele hM hcT hlsBl hQh hRh (hXh _ hcT hlsBl) _
    (VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) ++
      idx) rfl (by rw [hQhl]; exact Nat.le_refl _)
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
  have hps := hbv d.params.length 0 (zs.take d.params.length) (by simp [hzl]; omega)
    (by omega) (fun i h => by simp [List.getElem?_take, h]) hzl
  have hfs := hbv c.fields.length N (zs.drop N) (by simp [hzl]) (by omega)
    (fun i h => by simp [List.getElem?_drop]) hzl
  rw [show N + c.fields.length - 0 - d.params.length =
    d.allTypes.length + d.allCtors.length + c.fields.length by omega] at hps
  rw [show N + c.fields.length - N - c.fields.length = 0 by omega] at hfs
  obtain ⟨N', rf, hrf, -, hCI⟩ := ctorApp_realize hM hX hle hO hsT hTj hci hidxc hTW hcW hPT
    hcT hcC hlsB hP W (by simp) (by simp) hidxl hTS hCS (List.forall₂_append' hps hfs)
  rw [List.drop_left' (by simp [hzl]; omega)] at hrf
  exact ⟨N', rf, hCI, hrf⟩

end LogRel
end Lean4Lean

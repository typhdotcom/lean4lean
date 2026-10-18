import Lean4Lean.Theory.Typing.LogRel.Interp

/-!
# Soundness of the shape model

`SoundEq env Γ M N`: at every valuation fitting `Γ`, `M` and `N` have the same interpretations.
`SoundTy env Γ M A`: every interpretation of `M` is typed at an interpretation of `A`.
`StrongSound` pairs a typing with its soundness and a syntax-directed typing (`StrongSoundCore`)
whose type is sound-equal to it, which is what inverting an application spine needs.

Ported from `Experimental/ShapeLogRel.lean`.
-/

namespace Lean4Lean
open Lean4Lean VExpr
namespace LogRel
open LE_Interp

variable [ShapeEnv]

variable (env : VEnv) in
def SoundEq (Γ : List VExpr) (M N : VExpr) : Prop :=
  ∀ ⦃Γ₀ ρ⦄, Valuation.Fits env Γ₀ Γ ρ → ∀ {m}, LE_Interp env ρ m M ↔ LE_Interp env ρ m N

variable (env : VEnv) in
def SoundTy (Γ : List VExpr) (M A : VExpr) : Prop :=
  ∀ ⦃Γ₀ ρ⦄, Valuation.Fits env Γ₀ Γ ρ → ∀ {m}, LE_Interp env ρ m M → InterpTyped env ρ m M A

mutual
variable (env : VEnv) (U : Nat)
/-- A typing of `M` at `A`, sound in the model, with a syntax-directed typing at a type
sound-equal to `A`. -/
inductive StrongSound : List VExpr → VExpr → VExpr → Prop where
  | mk : env.HasType U Γ M A → SoundTy env Γ M A →
    StrongSoundCore Γ M A' → SoundEq env Γ A' A → StrongSound Γ M A

/-- The syntax-directed typings. Lambdas, applications, constants and pi types are inverted; the
other forms record no premises. -/
inductive StrongSoundCore : List VExpr → VExpr → VExpr → Prop where
  | bvar : StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort l) A
  | lam : SoundTy env Γ A (.sort u) → StrongSound (A::Γ) e B →
    StrongSoundCore Γ (.lam A e) (.forallE A B)
  | proj : StrongSoundCore Γ (.proj s k e) A
  | const : env.constants c = some ci → ls.length = ci.uvars →
    StrongSoundCore Γ (.const c ls) (ci.type.instL ls)
  | app : SoundTy env Γ A (.sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort (.imax u v))
end

variable (env : VEnv) (U : Nat) in
structure StrongSoundEq (Γ : List VExpr) (M N A : VExpr) : Prop where
  defeq : env.IsDefEq U Γ M N A
  sound : SoundEq env Γ M N
  left : StrongSound env U Γ M A
  right : StrongSound env U Γ N A

variable {E env : VEnv} {U : Nat}

protected theorem SoundEq.rfl : SoundEq env Γ M M := fun _ _ _ _ => .rfl
theorem SoundEq.symm : SoundEq env Γ M N → SoundEq env Γ N M := fun H _ _ W _ => (H W).symm
theorem SoundEq.trans (H1 : SoundEq env Γ M N) (H2 : SoundEq env Γ N P) : SoundEq env Γ M P :=
  fun _ _ W _ => (H1 W).trans (H2 W)

theorem StrongSoundEq.hasType : StrongSoundEq env U Γ M N A →
    StrongSound env U Γ M A ∧ StrongSound env U Γ N A
  | ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩
theorem StrongSoundEq.symm : StrongSoundEq env U Γ M N A → StrongSoundEq env U Γ N M A
  | ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h2.symm, h4, h3⟩
theorem StrongSound.defeq : StrongSound env U Γ M A → env.HasType U Γ M A
  | ⟨h, _, _, _⟩ => h
theorem StrongSound.sound : StrongSound env U Γ M A → SoundTy env Γ M A
  | ⟨_, h, _, _⟩ => h
theorem StrongSoundEq.rfl (H : StrongSound env U Γ M A) : StrongSoundEq env U Γ M M A :=
  ⟨H.defeq, .rfl, H, H⟩
theorem StrongSoundEq.trans :
    StrongSoundEq env U Γ M N A → StrongSoundEq env U Γ N P A → StrongSoundEq env U Γ M P A
  | ⟨a1, a2, a3, _⟩, ⟨b1, b2, _, b4⟩ => ⟨.trans a1 b1, a2.trans b2, a3, b4⟩
theorem SoundTy.defeq_l (H1 : SoundEq env Γ M N) (H : SoundTy env Γ M A) : SoundTy env Γ N A :=
  fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W ((H1 W).2 h); ⟨_, _, a1, (H1 W).1 a2, a3, a4⟩
theorem SoundTy.defeq_r (H1 : SoundEq env Γ A B) (H : SoundTy env Γ M A) : SoundTy env Γ M B :=
  fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W h; ⟨_, _, a1, a2, (H1 W).1 a3, a4⟩

/-- A typing whose two sides are sound with syntax-directed typings, at types sound-equal to `A`,
and whose sides have the same, typed, interpretations. -/
theorem StrongSoundEq.mk' (h1 : env.IsDefEq U Γ M N A)
    (h2 : StrongSoundCore env U Γ M A₁) (h2' : SoundEq env Γ A₁ A)
    (h3 : StrongSoundCore env U Γ N A₂) (h3' : SoundEq env Γ A₂ A)
    (h4 : ∀ ⦃Γ₀ ρ⦄, Valuation.Fits env Γ₀ Γ ρ → ∀ {m},
      (LE_Interp env ρ m M ↔ LE_Interp env ρ m N) ∧
      (LE_Interp env ρ m M → InterpTyped env ρ m M A)) :
    StrongSoundEq env U Γ M N A := by
  refine have ha := ?_; have ht := ?_
    ⟨h1, ha, ⟨h1.hasType.1, ht, h2, h2'⟩, ⟨h1.hasType.2, ht.defeq_l ha, h3, h3'⟩⟩
  · exact fun _ _ W _ => (h4 W).1
  · exact fun _ _ W _ => (h4 W).2

theorem SoundEq.inst (hM : ModelEnv env) (ht : SoundTy env Γ X A) (hA : SoundTy env Γ A (.sort u))
    (H : SoundEq env (A::Γ) M N) : SoundEq env Γ (M.inst X) (N.inst X) := fun _ ρ W m => by
  suffices ∀ M N, SoundEq env (A::Γ) M N →
      LE_Interp env ρ m (M.inst X) → LE_Interp env ρ m (N.inst X) from
    ⟨this _ _ H, this _ _ H.symm⟩
  intro M N H h
  have ⟨x, h1, h2⟩ := (LE_Interp.inst hM).1 h
  have ⟨x', a, a1, a2, a3, a4⟩ := ht W h2
  refine (LE_Interp.inst hM).2 ⟨_, (H (W.cons (InterpTyped.hsort (hA W)) a3 a4)).1 ?_, a2⟩
  exact h1.mono_l <| Valuation.LE.push.2 ⟨.rfl, a1⟩

theorem SoundEq.sort : SoundEq env Γ (.sort u) (.sort v) ↔ levelRel u = levelRel v := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have h := WShape.LE.of_T (n := 0) ((H .nil).1 .sort').le_sort
    generalize levelRel u = r, levelRel v = r' at h
    exact Shape0.sort.inj (congrArg (·.1) (WShape.sort_le.1 h))
  · intro _ ρ W m
    suffices ∀ {u v}, levelRel u = levelRel v →
        LE_Interp env ρ m (.sort u) → LE_Interp env ρ m (.sort v) from ⟨this H, this H.symm⟩
    intro u v H h; exact .mono (H ▸ h.le_sort) .sort'

theorem SoundEq.forallE (hA : SoundTy env Γ A (.sort u))
    (H1 : SoundEq env Γ A A') (H2 : SoundEq env (A::Γ) B B') :
    SoundEq env Γ (.forallE A B) (.forallE A' B') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq env Γ A A₁ → SoundEq env Γ A A₂ → SoundEq env (A::Γ) B₁ B₂ →
      LE_Interp env ρ m (.forallE A₁ B₁) → LE_Interp env ρ m (.forallE A₂ B₂) from
    ⟨this .rfl H1 H2, this H1 .rfl H2.symm⟩
  intro A₁ A₂ B₁ B₂ H1 H2 H3 h
  cases h with | bot => exact .bot | forallE h1 h2 h3 h4 h5
  have HA := H1.symm.trans H2
  refine .forallE ((HA W).1 h1) ((HA W).1 h2) h3 (fun _ h' => ?_) h5
  exact (H3 (W.cons (InterpTyped.hsort (hA W)) ((H1 W).2 h2) h'.T)).1 (h4 _ h')

omit [ShapeEnv] in
theorem levelRel_congr {a b : VLevel} (h : a ≈ b) : levelRel a = levelRel b := by
  unfold levelRel; congr 2; exact propext (VLevel.equiv_congr_left h)

omit [ShapeEnv] in
theorem levelRel_succ {l : VLevel} : levelRel (.succ l) = true := by
  unfold levelRel
  have : ¬VLevel.succ l ≈ .zero := fun h => by
    have := congrFun (VLevel.equiv_def'.1 h) []; simp [VLevel.eval] at this
  simp [this]

omit [ShapeEnv] in
theorem levelRel_zero : levelRel .zero = false := by
  unfold levelRel; simp [show (VLevel.zero ≈ VLevel.zero) from rfl]

/-- A variable's interpretation is typed at an interpretation of its type. -/
theorem LE_Interp.Valuation.Fits.lookup (hM : ModelEnv env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (h : Lookup Γ i A) (a1 : m ≤ ρ i) : InterpTyped env ρ m (.bvar i) A := by
  induction W generalizing i A with
  | nil => exact TShape.le_bot'.1 a1 ▸ .bot
  | cons _ h1 h2 h3 ih =>
    cases h with simp [Valuation.push] at a1
    | zero => exact ⟨_, _, a1, .bvar .rfl, h2.weak hM.closed, h3⟩
    | succ h =>
      have ⟨_, _, le, h1, h2, h3⟩ := ih h a1
      have h1 := bvar_iff.1 h1
      exact ⟨_, _, le, .bvar h1, h2.weak hM.closed, h3⟩

/-! ### Equivalent levels -/

/-- Terms equal up to equivalent universe levels. -/
inductive _root_.Lean4Lean.VExpr.LvEqv : VExpr → VExpr → Prop
  | bvar : VExpr.LvEqv (.bvar i) (.bvar i)
  | sort : l ≈ l' → VExpr.LvEqv (.sort l) (.sort l')
  | const : List.Forall₂ (· ≈ ·) ls ls' → VExpr.LvEqv (.const c ls) (.const c ls')
  | app : VExpr.LvEqv f f' → VExpr.LvEqv a a' → VExpr.LvEqv (.app f a) (.app f' a')
  | lam : VExpr.LvEqv A A' → VExpr.LvEqv e e' → VExpr.LvEqv (.lam A e) (.lam A' e')
  | forallE : VExpr.LvEqv A A' → VExpr.LvEqv B B' → VExpr.LvEqv (.forallE A B) (.forallE A' B')
  | proj : VExpr.LvEqv e e' → VExpr.LvEqv (.proj s k e) (.proj s k e')

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VLevel.forall₂_inst (h : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ us : List VLevel, List.Forall₂ (fun a b => a.inst ls ≈ b.inst ls') us us
  | [] => .nil
  | _ :: us => .cons (VLevel.inst_congr rfl h) (VLevel.forall₂_inst h us)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.LvEqv.instL (h : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ e : VExpr, (e.instL ls).LvEqv (e.instL ls')
  | .bvar _ => .bvar
  | .sort _ => .sort (VLevel.inst_congr rfl h)
  | .const _ us => .const <| List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
    VLevel.forall₂_inst h us
  | .app f a => .app (instL h f) (instL h a)
  | .lam A e => .lam (instL h A) (instL h e)
  | .forallE A B => .forallE (instL h A) (instL h B)
  | .proj _ _ e => .proj (instL h e)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VInductDecl.propAt_congr {d : VInductDecl}
    (h : List.Forall₂ (· ≈ ·) ls ls') : d.PropAt ls ↔ d.PropAt ls' :=
  VLevel.equiv_congr_left (VLevel.inst_congr rfl h)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VInductDecl.rel_congr {d : VInductDecl}
    (h : List.Forall₂ (· ≈ ·) ls ls') : d.rel ls = d.rel ls' := by
  unfold VInductDecl.rel; congr 2; exact propext (d.propAt_congr h)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VInductDecl.blockLevels_congr {d : VInductDecl}
    (h : List.Forall₂ (· ≈ ·) ls ls') : List.Forall₂ (· ≈ ·) (d.blockLevels ls) (d.blockLevels ls') := by
  unfold VInductDecl.blockLevels; split
  · clear ‹_›; induction h with
    | nil => exact .nil
    | cons _ h => exact h
  · exact h

theorem LE_Interp.Const.levels {R R' : TShape → VExpr → Prop} (hls : List.Forall₂ (· ≈ ·) ls ls')
    (hR : ∀ {h e}, R h e → ∀ {e'}, e.LvEqv e' → R' h e')
    (H : Const env c ls R rargs m) : Const env c ls' R' rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h ih => exact .lam (fun x y hm => ih x y hm) h
  | delta h1 h2 h3 h4 h5 =>
    exact .delta h1 h2 (hls.length_eq ▸ h3) (hR h4 (VExpr.LvEqv.instL hls _)) h5
  | indTy h1 h2 h3 h4 h5 h6 =>
    refine .indTy h1 h2 h3 h4 (fun i c' cty a1 a2 => ?_) ((VInductDecl.rel_congr hls) ▸ h6)
    have ⟨h, b1, b2⟩ := h5 i c' cty a1 a2
    exact ⟨h, hR b1 (VExpr.LvEqv.instL hls _), b2⟩
  | ctor h1 h2 h3 h4 h5 h6 h7 =>
    exact .ctor h1 h2 h3 h4 (mt (VInductDecl.propAt_congr hls).2 h5) h6 h7
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .iota h1 h2 h3 h4 (mt (VInductDecl.propAt_congr (VInductDecl.blockLevels_congr hls)).2 h5)
      h6 h7 (hR h8 (VExpr.LvEqv.instL hls _)) h9 h10
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .kIota h1 h2 h3 h4 h5
      ((VInductDecl.propAt_congr (VInductDecl.blockLevels_congr hls)).1 h6) h7 h8
      (hR h9 (VExpr.LvEqv.instL hls _)) h10
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 =>
    subst h3; let .cons hu .nil := hls
    exact .quotTy h1 h2 rfl h4 h5 (hR h6 (VExpr.LvEqv.instL (.cons hu .nil) _)) h7
      (levelRel_congr hu ▸ h8)
  | quotMk h1 h2 h3 h4 h5 =>
    subst h3; let .cons hu .nil := hls
    exact .quotMk h1 h2 rfl (mt (VLevel.equiv_congr_left hu).2 h4) h5
  | quot h1 h2 h3 h4 h5 h6 =>
    subst h3; let .cons hu (.cons _ .nil) := hls
    exact .quot h1 h2 rfl (mt (VLevel.equiv_congr_left hu).2 h4) h5 h6
  | quotK h1 h2 h3 h4 h5 =>
    subst h3; let .cons hu (.cons _ .nil) := hls
    exact .quotK h1 h2 rfl ((VLevel.equiv_congr_left hu).1 h4) h5

/-- Interpretations do not depend on the representatives of levels. -/
theorem LE_Interp.levels (H : LE_Interp env ρ m e) (he : e.LvEqv e') : LE_Interp env ρ m e' := by
  induction H generalizing e' with
  | bot => exact .bot
  | bvar h => cases he; exact .bvar h
  | sort h => let .sort h' := he; exact .sort (levelRel_congr h' ▸ h)
  | app _ _ h3 ih1 ih2 => let .app h1 h2 := he; exact .app (ih1 h1) (ih2 h2) h3
  | lam _ h2 _ h4 ih1 ih3 => let .lam h1 h3 := he; exact .lam (ih1 h1) h2 (fun x h => ih3 x h h3) h4
  | forallE _ _ h3 _ h5 ih1 ih2 ih4 =>
    let .forallE h1 h4 := he; exact .forallE (ih1 h1) (ih2 h1) h3 (fun x h => ih4 x h h4) h5
  | const h1 h2 h3 h4 _ h6 _ ih5 ih7 =>
    let .const hls := he
    exact .const h1 (hls.length_eq ▸ h2) h3 h4 (ih5 (VExpr.LvEqv.instL hls _))
      (h6.levels hls (R' := LE_Interp env _) fun hr _ he => ih7 _ _ hr he) fun _ _ h => h
  | proj h1 h2 h3 _ h5 h6 ih => let .proj he := he; exact .proj h1 h2 h3 (ih he) h5 h6


/-! ### Application spines of constants -/

/-- A constant applied to the arguments `rAs`, last argument first. -/
def spine (c : Name) (ls : List VLevel) (rAs : List VExpr) : VExpr :=
  rAs.foldr (fun A acc => .app acc A) (.const c ls)

omit [ShapeEnv] in
@[simp] theorem spine_nil : spine c ls [] = .const c ls := rfl
omit [ShapeEnv] in
@[simp] theorem spine_cons : spine c ls (A :: rAs) = .app (spine c ls rAs) A := rfl

omit [ShapeEnv] in
theorem spine_eq_appN (c : Name) (ls : List VLevel) (as : List VExpr) :
    spine c ls as.reverse = (VExpr.const c ls).appN as := by
  unfold spine; rw [List.foldr_reverse]
  generalize VExpr.const c ls = f
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

/-- An interpretation of a constant applied to at most as many arguments as it computes at is read
off its `Const` derivation at the arguments' interpretations. -/
theorem LE_Interp.spine_inv (hR : ConstRoles env) :
    ∀ {rAs : List VExpr} {m}, (∀ r n, ConstArity env c r n → rAs.length ≤ n) →
    LE_Interp env ρ m (spine c ls rAs) →
    ∃ n, ∀ k, n ≤ k → ∃ (rargs : List (WShape k)) (y : TShape),
      List.Forall₂ (fun x A => LE_Interp env ρ x.T A) rargs rAs ∧ m ≤ y ∧
      Const env c ls (LE_Interp env ρ) rargs y
  | [], m, _, H => by
    cases H with
    | bot => exact ⟨0, fun k _ => ⟨[], _, .nil, .rfl, .bot⟩⟩
    | const _ _ h3 _ _ h6 h7 =>
      obtain ⟨n, h6⟩ : ∃ n, Const (n := n) env c ls _ [] _ := ⟨_, h6⟩
      exact ⟨n, fun k hk => ⟨[], _, .nil, h3, by simpa using (h6.mapR (h7 _ _)).lift hk⟩⟩
  | A :: rest, m, harity, H => by
    cases H with
    | bot =>
      refine ⟨0, fun k _ => ⟨rest.map (fun _ => .bot) |>.cons .bot, _, ?_, .rfl, .bot⟩⟩
      refine .cons .bot ?_
      clear harity; induction rest with
      | nil => exact .nil
      | cons _ _ ih => exact .cons .bot ih
    | @app _ n f _ _ _ x_arg hLE_f hLE_a hle_app =>
    obtain ⟨n', ih'⟩ := spine_inv hR (fun r n h => Nat.le_of_succ_le (harity r n h)) hLE_f
    refine ⟨max (n + 1) n', fun k hk => ?_⟩
    have ⟨hk_app, hk⟩ := Nat.max_le.1 hk
    obtain ⟨rargs, y, hargs, hle, hConst⟩ := ih' k hk
    have hk_n : n ≤ k := Nat.le_of_succ_le hk_app
    refine ⟨x_arg.lift k :: rargs, _, .cons (hLE_a.mono (TShape.lift_eqv hk_n).1) hargs,
      hle_app, ?_⟩
    rcases hConst.arity with hb | ⟨f_const, hle_lam, hRec⟩ | ⟨r, hA⟩
    · have h_app_bot : (f.app x_arg).T ≤ .bot := by
        rw [show f = .bot from TShape.le_bot.1 (hle.trans hb |>.trans TShape.bot_eqv.1)]
        simp; exact TShape.bot_eqv.1
      exact TShape.le_bot'.1 h_app_bot ▸ .bot
    · let x_arg' : WShape k := x_arg.lift k
      obtain ⟨x', hx'_le, hx'_mem⟩ := WShapeFun.app_eq f_const x_arg'
      refine hRec x' (f_const.app x_arg') hx'_mem
        |>.mono_l (.cons hx'_le <| List.forall₂_refl' (fun _ => .rfl)) |>.mono ?_
      rw [← WShape.lam'_app (f := f_const) (x := x_arg')]
      exact TShape.app_mono (hle.trans hle_lam) (TShape.lift_eqv hk_n).2
    · have := harity r _ hA; rw [hargs.length_eq] at this; simp at this; omega

variable (env) in
/-- An application spine of a constant typed in the model: the constant's type and each
application's argument, at the model's level only. A `StrongSound` spine is one
(`StrongSound.mspine`); so is a spine typed along its constant's telescope (`MSpine.ofTele`). -/
inductive MSpine (Γ : List VExpr) : VExpr → VExpr → Prop where
  | const : env.constants c = some ci → ls.length = ci.uvars →
    SoundEq env Γ (ci.type.instL ls) T → MSpine Γ (.const c ls) T
  | app : SoundTy env Γ A (.sort u) → MSpine Γ f (.forallE A B) → SoundTy env Γ a A →
    SoundEq env Γ (B.inst a) T → MSpine Γ (.app f a) T

theorem StrongSound.mspine : ∀ {rAs : List VExpr} {T : VExpr},
    StrongSound env U Γ (spine c ls rAs) T → MSpine env Γ (spine c ls rAs) T
  | [], _, H => by
    obtain ⟨-, -, core, heq⟩ := H
    cases core with | const h1 h2 => exact .const h1 h2 heq
  | _ :: _, _, H => by
    obtain ⟨-, -, core, heq⟩ := H
    cases core with | app h1 h2 h3 => exact .app h1 (StrongSound.mspine h2) h3.sound heq

theorem MSpine.retype (H : MSpine env Γ M T) (h : SoundEq env Γ T T') : MSpine env Γ M T' := by
  cases H with
  | const h1 h2 h3 => exact .const h1 h2 (h3.trans h)
  | app h1 h2 h3 h4 => exact .app h1 h2 h3 (h4.trans h)

/-- A constant's `Const` derivation at shapes of its arguments interprets the application spine,
at a shape typed at an interpretation of the spine's type. -/
theorem LE_Interp.apps_realize (hM : ModelEnv env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp env ρ a T)
    (hTy_lhs : MSpine env Γ (spine c ls rAs) T)
    (hargs : List.Forall₂ (fun (x : WShape n) A => LE_Interp env ρ x.T A) rargs rAs)
    (hC : Const env c ls (LE_Interp env ρ) rargs m') :
    LE_Interp env ρ m' (spine c ls rAs) := by
  generalize h_len : rargs.length = k
  induction k generalizing m' a T rAs n with | succ k ih => ?_ | zero =>
    let .nil := hargs
    have .const h1 h2 hType := hTy_lhs
    exact .const h1 h2 .rfl mty ((hType W).2 ha) hC fun _ _ => id
  let .cons (a := arg) (b := A) (l₁ := rest_r) (l₂ := rest_s) h_arg h_rest := hargs
  cases h_len
  have .app _ hMf hMa hC_inst := hTy_lhs
  obtain ⟨y, hya, hy⟩ := (LE_Interp.inst hM).1 ((hC_inst W).2 ha)
  obtain ⟨n', arg', aT, _, jle, h_LE, ha', harg'⟩ := (hMa W (h_arg.join' hM hy)).out
  let k := max (max n m'.1) (max n' a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  let arg'' := arg'.lift k; let m'' := m'.2.lift k
  let m2 : WShape (k+1) := .lam' (.single arg'' m'')
  suffices LE_Interp env ρ m2.T (spine c ls rest_s) by
    have h_arg'_T : LE_Interp env ρ arg''.T A := h_LE.lift hk.2.1
    have h_app := this.app' h_arg'_T
    simp only [m2, WShape.lam'_app, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte] at h_app
    exact h_app.mono (TShape.lift_eqv hk.1.2).2
  have hJ := TShape.Join.mk (h_arg.compat hM hy)
  let aT' := aT.lift k; let a' := a.2.lift k
  let a2 : WShape (k+1) := .forallE aT' (.single arg'' a')
  have h_argw_typed : arg''.HasType aT' := (WShape.HasType.lift hk.2.1).2 harg'
  refine ih (a := a2.T) (rargs := rest_r.map (WShape.lift k)) ?_ ?_ hMf ?_ ?_ (by simp)
  · have h_m_typed := (TShape.HasType.def hk.1.2 hk.2.2).1 mty
    refine WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2 ⟨WShape.HasDom.single.2 (.inl h_argw_typed), fun x y h => ?_⟩
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 h
      · exact h_m_typed.isType
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl h_argw_typed)
    · simp only [WShapeFun.single_app]; split <;> [exact h_m_typed; exact .bot' (.bot' .sort)]
  · refine .forallE' (ha'.lift hk.2.1) (ha'.lift hk.2.1)
      (WShape.HasDom.single.2 (.inl h_argw_typed)) fun x _ => ?_
    rw [WShapeFun.single_app]; split <;> [rename_i h1; exact .bot]
    refine .lift hk.2.2 <| hya.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
    exact (hJ.le.2.trans jle).trans (TShape.lift_eqv hk.2.1).2 |>.trans h1.T
  · exact List.forall₂_map_left_iff.2 <| h_rest.imp fun _ _ h => h.mono (TShape.lift_eqv hk.1.1).1
  · refine Const.lam (fun x y hmem => ?_) .rfl
    obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hmem <;> [skip; exact .bot]
    refine hC.lift hk.1.1 |>.mono_l ?_ |>.mono (TShape.lift_eqv hk.1.2).1
    exact .cons ((TShape.LE.def hk.1.1 hk.2.1).1 (hJ.le.1.trans jle)) <|
      List.forall₂_refl' fun _ => .rfl

/-! ### The cases of soundness that need the environment's rules -/


variable (env) in
/-- Interpretations of a constant do not depend on the representatives of its levels. -/
def LevelInv : Prop := ∀ {ρ m c ls ls'}, List.Forall₂ (· ≈ ·) ls ls' →
  LE_Interp env ρ m (.const c ls) → LE_Interp env ρ m (.const c ls')

theorem LevelInv.of : LevelInv env := fun hls H => H.levels (.const hls)

variable (E env U) in
/-- The two sides of an instance of a rule of `E` have the same interpretations. -/
def ExtraSound : Prop := ∀ {Γ df ls}, E.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
  StrongSound env U [] (df.lhs.instL ls) (df.type.instL ls) →
  StrongSound env U [] (df.rhs.instL ls) (df.type.instL ls) →
  StrongSound env U Γ (df.lhs.instL ls) (df.type.instL ls) →
  StrongSound env U Γ (df.rhs.instL ls) (df.type.instL ls) →
  SoundEq env Γ (df.lhs.instL ls) (df.rhs.instL ls)

variable (E env U) in
/-- A projection out of a block of `E`'s interpretations are typed at its type. -/
def ProjSound : Prop := ∀ {Γ s d t T c k f ls As I e u}, E.inducts s = some (d, t) →
  d.types[t]? = some T → T.ctors = [c] → c.fields[k]? = some f → (∀ l ∈ ls, l.WF U) →
  ls.length = d.uvars → As.length = d.params.length → I.length = T.indices.length →
  d.ProjAllowed c ls k →
  StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u) →
  StrongSound env U Γ e (.appN (.const s ls) (As ++ I)) →
  StrongSound env U Γ (c.projType ls s k As e) (.sort (f.level.inst ls)) →
  SoundTy env Γ (.proj s k e) (c.projType ls s k As e)

variable (E env U) in
/-- A projection of a constructor application of a block of `E` has its field's
interpretations. -/
def ProjIotaSound : Prop := ∀ {Γ s d t T c k f fs a ls As I u}, E.inducts s = some (d, t) →
  d.types[t]? = some T → T.ctors = [c] → c.fields[k]? = some f → fs[k]? = some a →
  (∀ l ∈ ls, l.WF U) → ls.length = d.uvars → As.length = d.params.length →
  fs.length = c.fields.length → I.length = T.indices.length → d.ProjAllowed c ls k →
  StrongSound env U Γ (.appN (.const s ls) (As ++ I)) (.sort u) →
  StrongSound env U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)) →
  StrongSound env U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
    (.sort (f.level.inst ls)) →
  StrongSound env U Γ a (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) →
  SoundEq env Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a

variable (E env U) in
/-- A term of a structure type of a block of `E` has the interpretations of the constructor
applied to its projections. -/
def ProjEtaSound : Prop := ∀ {Γ s d t T c ls As e u}, E.inducts s = some (d, t) →
  d.types[t]? = some T → T.ctors = [c] → T.indices = [] → d.isRec = false →
  (∀ l ∈ ls, l.WF U) → ls.length = d.uvars → As.length = d.params.length →
  StrongSound env U Γ (.appN (.const s ls) As) (.sort u) →
  StrongSound env U Γ e (.appN (.const s ls) As) →
  StrongSound env U Γ (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))
    (.appN (.const s ls) As) →
  SoundEq env Γ e (.appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e))

theorem StrongSound.retype (H : StrongSound env U Γ M A) (h1 : SoundEq env Γ A B)
    (h2 : env.HasType U Γ M B) : StrongSound env U Γ M B :=
  let ⟨_, a2, a3, a4⟩ := H; ⟨h2, a2.defeq_r h1, a3, a4.trans h1⟩

/-! ### Interpretations under binders -/

/-- An interpretation of a lambda, applied to any shape, interprets the body. -/
theorem LE_Interp.lam_app (hM : ModelEnv env) {f : WShape (n+1)}
    (H : LE_Interp env ρ f.T (.lam A F)) (x : WShape n) :
    LE_Interp env (ρ.push x.T) (f.app x).T F := by
  cases f using WShape.casesOn' with
  | lam g hl => rw [WShape.lam_app]; exact H.lam_inv' hM x
  | _ => exact .bot

/-- The valuation `ρ` with the shapes `xs` pushed in order. -/
def pushAll (ρ : Valuation) : List TShape → Valuation
  | [] => ρ
  | x :: xs => pushAll (ρ.push x) xs

/-- An interpretation of `lams As F` applied to shapes `xs`, one per binder, interprets `F` at the
valuation with them pushed. -/
theorem LE_Interp.appS_lams (hM : ModelEnv env) {As : List VExpr} :
    ∀ {ρ h xs y}, LE_Interp env ρ h (.lams As F) → AppS h xs y →
      xs.length = As.length → LE_Interp env (pushAll ρ xs) y F := by
  induction As with
  | nil => intro ρ h xs y H hA hl; cases xs with
    | nil => let .nil le := hA; exact H.mono le
    | cons => cases hl
  | cons A As ih =>
    intro ρ h xs y H hA hl; cases hA with
    | nil => cases hl
    | cons le1 le2 hA =>
      have h1 := (H.mono le1).lam_app hM _ |>.mono_l (Valuation.LE.push.2 ⟨.rfl, le2⟩)
      have := ih h1 hA (by simpa using hl); exact this

/-- What every valuation extending `ρ` by one shape per binder sees of `L` it sees of `R`: then so
it is for `lams As L` and `lams As R` at `ρ`. -/
theorem LE_Interp.lams_congr :
    ∀ {As : List VExpr} {ρ m},
      (∀ xs y, xs.length = As.length → LE_Interp env (pushAll ρ xs) y L →
        LE_Interp env (pushAll ρ xs) y R) →
      LE_Interp env ρ m (.lams As L) → LE_Interp env ρ m (.lams As R)
  | [], ρ, _, H, h => H [] _ rfl h
  | A :: As, ρ, _, H, h => by
    cases h with
    | bot => exact .bot
    | lam h1 h2 h3 h4 =>
      refine .lam h1 h2 (fun x hx => lams_congr (fun xs y hl hL => ?_) (h3 x hx)) h4
      exact H (x.T :: xs) y (by simp [hl]) hL

/-! ### Rule instances -/

/-- A definition's unfolding: the constant and its value have the same interpretations. -/
theorem extraSound_defn (hM : ModelEnv env) {ci : VDefVal}
    (hc : env.constants ci.name = some ci.toVConstant) (hdf : env.defeqs ci.toDefEq)
    (hlen : ls.length = ci.uvars)
    (hr : StrongSound env U Γ (ci.value.instL ls) (ci.type.instL ls)) :
    SoundEq env Γ (.const ci.name ls) (ci.value.instL ls) := by
  have hlhs : ci.toDefEq.lhs = .const ci.name (VLevel.params ci.toDefEq.uvars) := rfl
  intro _ ρ W m; refine ⟨fun H => ?_, fun h => ?_⟩
  · cases H with
    | bot => exact .bot
    | const _ _ h3 _ _ h6 h7 =>
      cases h6 with
      | bot => exact TShape.le_bot'.1 (h3.trans TShape.bot_eqv.1) ▸ .bot
      | lam he hle =>
        have := Const.lam_le_bot hM.roles he hle (r := .delta ci.toDefEq) (.delta hdf hlhs)
        exact TShape.le_bot'.1 (h3.trans this) ▸ .bot
      | delta a1 a2 a3 a4 a5 =>
        cases hM.stepUniq.delta hdf a1 hlhs a2
        exact (h7 _ _ a4).mono (h3.trans a5)
      | indTy a1 a2 => cases hM.roles (.delta hdf hlhs) (.indTy a1 a2)
      | ctor a1 a2 a3 a4 => cases hM.roles (.delta hdf hlhs) (.ctor a1 a2 a3 a4)
      | quotTy _ _ _ a4 => cases a4
  · have ⟨_, _, le, hm1, ha, hty⟩ := hr.sound W h
    exact .const hc hlen le hty ha (.delta (n := 0) hdf hlhs hlen hm1 .rfl) fun _ _ h => h

/-- Soundness of the model of `env` for every typing rule of an environment `E ≤ env`, given the
cases that need `E`'s rules (`LevelInv`, `ExtraSound`, `ProjSound`, `ProjIotaSound`,
`ProjEtaSound`). -/
theorem strongSound_of (hM : ModelEnv env) (hE : E ≤ env) (hL : LevelInv env)
    (hX : ExtraSound E env U) (hP : ProjSound E env U) (hPI : ProjIotaSound E env U)
    (hPE : ProjEtaSound E env U)
    (H : E.IsDefEqStrong U Γ M N A) : StrongSoundEq env U Γ M N A := by
  induction H with
  | @bvar Γ i A u h _ hA _ =>
    have hD : env.IsDefEq U Γ _ _ A := .bvar h
    exact .rfl ⟨hD, fun _ _ W _ h1 => W.lookup hM h (bvar_iff.1 h1), .bvar, .rfl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @sortDF l l' Γ h1 h2 h3 =>
    have hD : env.IsDefEq U Γ _ _ _ := .sortDF h1 h2 h3
    have hS {Γ l} : SoundTy env Γ (.sort l) (.sort (.succ l)) := fun _ _ W _ h => by
      refine .mk h.le_sort .sort' .sort' ?_
      rw [levelRel_succ]; exact TShape.HasType.sort
    refine ⟨hD, (SoundEq.sort.2 (levelRel_congr h3)), ⟨hD.hasType.1, hS, .sort, .rfl⟩,
      ⟨hD.hasType.2, hS.defeq_l (SoundEq.sort.2 (levelRel_congr h3)), .sort, .rfl⟩⟩
  | @constDF c ci ls ls' u Γ h1 h2 h3 h4 h5 _ _ _ _ ih2 =>
    replace h1 := hE.constants h1
    have hD : env.IsDefEq U Γ _ _ _ := .constDF h1 h2 h3 h4 h5
    have hS : SoundEq env Γ (.const c ls) (.const c ls') := fun _ _ _ _ =>
      ⟨hL h5, hL (h5.flip.imp fun _ _ h => (h : _ = _).symm)⟩
    have hT {Γ ls} : SoundTy env Γ (.const c ls) (ci.type.instL ls) :=
      fun _ _ _ _ h => by
      cases h with
      | bot => exact .bot
      | const b1 b2 b3 b4 b5 b6 b7 =>
        cases h1.symm.trans b1; exact ⟨_, _, b3, .const b1 b2 .rfl b4 b5 b6 b7, b5, b4⟩
    exact ⟨hD, hS, ⟨hD.hasType.1, hT, .const h1 h4, .rfl⟩,
      ⟨hD.hasType.2, hT.defeq_r ih2.sound.symm, .const h1 (h5.length_eq ▸ h4), ih2.sound.symm⟩⟩
  | appDF _ _ _ _ _ _ _ ihA _ ih1 ih2 ih3 =>
    refine .mk' (.appDF ih1.defeq ih2.defeq)
      (.app ihA.left.sound ih1.left ih2.left) .rfl
      (.app ihA.left.sound ih1.right ih2.right) ih3.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_app hM (ih1.left.sound W) (InterpTyped.hsort (ih3.left.sound W))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih1.sound W).1 h1) ((ih2.sound W).1 h2) h3
    · exact .app ((ih1.sound W).2 h1) ((ih2.sound W).2 h2) h3
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 ih3 =>
    refine .mk' (.lamDF ih1.defeq ih2.defeq) (.lam ih1.left.sound ih2.left) .rfl
      (.lam ih1.right.sound ih3.right) (.symm <| .forallE ih1.left.sound ih1.sound .rfl)
      fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam hM (InterpTyped.hsort (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1.sound W).1 h1) h2 (fun _ h => ?_) h4
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h.T)).1 (h3 _ h)
    · refine .lam ((ih1.sound W).2 h1) h2 (fun _ h => ?_) h4
      exact (ih3.sound (W.cons (InterpTyped.hsort (ih1.right.sound W)) h1 h.T)).2 (h3 _ h)
  | forallEDF _ _ _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.forallEDF ih1.defeq ih2.defeq)
      (.forallE ih1.left ih2.left) .rfl (.forallE ih1.right ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE hM (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .forallE ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      exact (ih3.sound (W.cons (InterpTyped.hsort (ih1.right.sound W)) h2 h.T)).2 (h4 _ h)
  | defeqDF _ _ _ ih1 ih2 =>
    have ⟨_, a2, a3, a4⟩ := ih2.left
    have ⟨_, b2, b3, b4⟩ := ih2.right
    have hd := ih1.defeq.defeqDF ih2.defeq
    refine ⟨hd, ih2.sound, ?_, ?_⟩
    · exact ⟨hd.hasType.1, a2.defeq_r ih1.sound, a3, a4.trans ih1.sound⟩
    · exact ⟨hd.hasType.2, b2.defeq_r ih1.sound, b3, b4.trans ih1.sound⟩
  | beta _ _ _ _ _ _ _ _ ihA _ ih1 ih2 ih3 ih4 =>
    have lamS : StrongSound env U _ (.lam _ _) (.forallE _ _) :=
      ⟨.lamDF ihA.defeq ih1.defeq, fun _ _ W _ h => sound_lam hM (InterpTyped.hsort (ihA.left.sound W))
        (fun h1 h2 => ih1.left.sound (W.cons (InterpTyped.hsort (ihA.left.sound W)) h1 h2)) h,
        .lam ihA.left.sound ih1.left, .rfl⟩
    have appS : StrongSound env U _ (.app (.lam _ _) _) _ :=
      ⟨.appDF lamS.defeq ih2.defeq, fun _ _ W _ h =>
        sound_app hM (lamS.sound W) (InterpTyped.hsort (ih3.left.sound W)) h,
        .app ihA.left.sound lamS ih2.left, .rfl⟩
    refine ⟨.beta ih1.defeq ih2.defeq, fun _ _ W m => ?_, appS, ih4.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | bot => cases hm TShape.bot_le' | @app _ n₁ _ _ _ _ a h1 h2 h3
      cases h1 with
      | bot => cases hm (h3.trans TShape.bot_eqv.1)
      | @lam _ n₂ _ _ f' _ _ h4 h5 h6 h7
      let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
      obtain ⟨_, b1, b2⟩ := WShapeFun.app_eq (f'.lift k) (a.lift k)
      obtain ⟨a', y', b2', rfl, yb_eq⟩ := (WShapeFun.mem_lift hk.1).1 b2
      obtain ⟨bx', bxle, bx_ht, bapp⟩ := WShape.HasDom.iff.1 h5 a'
      refine (LE_Interp.inst hM).2 ⟨_, ?_, (h2.lift hk.2).mono b1.T⟩
      refine .mono_l (Valuation.LE.push.2 ⟨.rfl, bxle.T.trans (TShape.lift_eqv hk.1).2⟩) ?_
      refine (h6 bx' bx_ht).mono <| h3.trans <| .trans ?_ bapp.T
      rw [TShape.LE.def hk.2 hk.1, WShape.lift_app hk.2]
      have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
      refine (WShape.app_mono_l h7' _).trans ?_
      rw [WShape.lift_lam' hk.1, WShape.lam'_app, yb_eq]
      exact WShape.lift_mono hk.1 (WShapeFun.app_of_mem b2').2
    · have ⟨_, h1, h2⟩ := (LE_Interp.inst hM).1 h
      have ⟨e, a, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
      have := (WShape.HasDom.single (y := m.2.lift k)).2 <| .inl <|
        (TShape.HasType.def hk.2.1 hk.2.2).1 a4
      refine .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
      · rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
      · simp [WShapeFun.single_app]; split <;> [rename_i h; exact .bot]
        refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
        exact (TShape.LE.lift_l hk.2.1).2 h
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    refine ⟨.proofIrrel ih1.defeq ih2.defeq ih3.defeq, fun _ ρ W m => ?_, ih2.left, ih3.left⟩
    suffices ∀ {h h'}, InterpTyped env ρ m h _ → LE_Interp env ρ m h → LE_Interp env ρ m h' from
      ⟨fun h => this (ih2.left.sound W h) h, fun h => this (ih3.left.sound W h) h⟩
    refine fun ⟨_, _, a1, a2, a3, a4⟩ h1 => .mono (?_ : m ≤ .bot) .bot
    have ⟨_, _, b1, b2, b3, b4⟩ := ih1.left.sound W a3
    have b4' := TShape.HasType.mono_r (by simpa [levelRel_zero] using b3.le_sort) .sort b4
    exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))
  | @eta Γ A u B v e _ _ _ _ _ _ _ _ ihA ihB _ ih1 ih2 ihA' =>
    have appT : SoundTy env (A::Γ) (.app e.lift (.bvar 0)) B := fun _ _ W _ h => by
      have := sound_app hM (ih2.left.sound W) (B := B.liftN 1 1) (X := .bvar 0) ?_ h
      · rwa [VExpr.inst_liftN_bvar] at this
      · rw [VExpr.inst_liftN_bvar]; exact InterpTyped.hsort (ihB.left.sound W)
    have hD := VEnv.IsDefEq.eta ih1.defeq
    have bvarS : StrongSound env U (A::Γ) (.bvar 0) A.lift :=
      ⟨.bvar .zero, fun _ _ W _ h => W.lookup hM .zero (bvar_iff.1 h), .bvar, .rfl⟩
    have appS : StrongSound env U (A::Γ) (.app e.lift (.bvar 0)) B := by
      have := VEnv.IsDefEq.appDF ih2.defeq bvarS.defeq
      have core := StrongSoundCore.app ihA'.left.sound ih2.left bvarS
      rw [VExpr.inst_liftN_bvar] at this core
      exact ⟨this, appT, core, .rfl⟩
    have lamS : StrongSound env U Γ (.lam A (.app e.lift (.bvar 0))) (.forallE A B) :=
      ⟨hD.hasType.1, fun _ _ W _ h => sound_lam hM (InterpTyped.hsort (ihA.left.sound W))
        (fun h1 h2 => appT (W.cons (InterpTyped.hsort (ihA.left.sound W)) h1 h2)) h,
        .lam ihA.left.sound appS, .rfl⟩
    refine ⟨hD, fun _ ρ W m => ?_, lamS, ih1.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨e, t, h1, h2, h3, h4⟩ := lamS.sound W h
      have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
      cases h2 with
      | bot => cases hm (h1.trans TShape.bot_le')
      | @lam _ n _ _ f' _ _ h2a h2d h2f h2le
      cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans TShape.bot_le')
      have key {x y} (hmem : (x, y) ∈ f') :
          LE_Interp env ρ (WShape.T (n := n+1) (.lam' (WShapeFun.single x y))) e := by
        by_cases hy : y ≤ .bot
        · refine .mono (WShape.LE.T (?_ : _ ≤ .bot)) .bot
          rw [← WShape.lam'_bot, WShape.lam'_le_lam', WShapeFun.single_le]
          exact ⟨_, _, by simp [WShapeFun.mem_bot], WShape.bot_le, hy⟩
        rw [WShape.le_bot] at hy
        obtain ⟨x', x'le, x'ht, x'app⟩ := WShape.HasDom.iff.1 h2d x
        have := (h2f x' x'ht)
          |>.mono_l (Valuation.LE.push.2 ⟨.rfl, x'le.T⟩)
          |>.mono (WShape.LE.T <| (WShapeFun.app_of_mem hmem).2.trans x'app)
        cases this with | bot => cases hy rfl | @app _ n' f _ _ _ a' c1 c2 c3
        cases f using WShape.casesOn' with
        | lam g => ?_
        | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
        obtain ⟨x'', hle, mem⟩ := WShapeFun.app_eq g a'
        have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
        refine ((LE_Interp.weak_iff hM.closed).1 c1).mono ?_
        refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
        rw [WShape.lift_lam' le₂, WShapeFun.lift_single le₂, WShape.lam_eq_lam',
          WShape.lift_lam' le₁, WShape.lam'_le_lam', WShapeFun.single_le]
        exact ⟨_, _, (WShapeFun.mem_lift le₁).2 ⟨_, _, mem, rfl, rfl⟩,
          hle.T.trans (LE_Interp.bvar_iff.1 c2), (TShape.LE.def le₂ le₁).1 c3⟩
      have main (l : List (WShape n × WShape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g, (∀ z : WShapeFun n, g ≤ z ↔ ∀ x ∈ l, .single x.1 x.2 ≤ z) ∧
            LE_Interp env ρ (WShape.T (.lam' g)) e := by
        induction l with | nil => exact ⟨.bot, by simp, WShape.lam'_bot ▸ .bot⟩ | cons p l ih
        obtain ⟨x, y⟩ := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, a1, a2⟩ := ih H.2
        have hc := (key H.1).compat hM a2
        have hJ := WShapeFun.Join.mk <| WShape.Compat.lam'.1 <| WShape.Compat.T_iff.2 hc
        refine ⟨_, fun z => (hJ _).trans <| .trans ?_ List.forall_mem_cons.symm, ?_⟩
        · exact and_congr_right' (a1 _)
        · exact (key H.1).join hM (WShape.Join.lam'.2 hJ).T a2
      have ⟨g, a1, a2⟩ := main f'.elems fun _ => WShapeFun.mem_elems.1
      refine a2.mono (h2le.trans (WShape.lam'_le_lam'.2 ?_).T) |>.mono h1
      refine WShapeFun.LE.def'.2 fun x' y' hmem => WShapeFun.single_le.1 ?_
      exact (a1 _).1 .rfl _ (WShapeFun.mem_elems.2 hmem)
    · have ⟨m', f, a1, a2, a3, a4⟩ := ih1.left.sound W h
      have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
      have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
      cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' TShape.bot_le'
      have le_k := Nat.le_max_left n₂ m; have le_m := Nat.le_max_right n₂ m
      refine .mono (WShape.lift_lam' le_k ▸ a1.trans (TShape.lift_eqv (Nat.succ_le_succ le_k)).2) <|
        .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ => ?_
      simpa only [WShape.lift_lam' le_k, WShape.lam'_app] using
        ((a2.lift (Nat.succ_le_succ le_k)).weak hM.closed).app' .bvar0
  | extra hdf hls hlen _ _ _ _ _ _ _ ih5 ih6 ih7 ih8 =>
    exact ⟨.extra (hE.defeqs hdf) hls hlen, hX hdf hls hlen ih5.left ih6.left ih7.left ih8.left,
      ih7.left, ih8.left⟩
  | @projDF s d t T c k f ls Γ As I As' I' u e e' a a1 a2 a3 a4 a5 a6 a7 a8 a9 _ _ a12 _ _ _ ih13 ih14 ih15 =>
    have hD := VEnv.IsDefEq.projDF (hE.inducts a) a1 a2 a3 a4 a5 a6 a7 a8 a9 ih13.defeq ih14.defeq a12
      ih15.defeq
    have hS : SoundEq env Γ (.proj s k e) (.proj s k e') := fun _ _ W _ => by
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> cases h with
      | bot => exact .bot
      | proj h1 h2 h3 h4 h5 h6 => ?_
      · exact .proj h1 h2 h3 ((ih14.sound W).1 h4) h5 h6
      · exact .proj h1 h2 h3 ((ih14.sound W).2 h4) h5 h6
    have he' : StrongSound env U _ _ _ :=
      ih14.right.retype ih13.sound (ih13.defeq.defeqDF ih14.defeq).hasType.2
    refine ⟨hD, hS, ⟨hD.hasType.1, hP a a1 a2 a3 a4 a5 a6 a7 a12 ih13.left ih14.left ih15.left,
      .proj, .rfl⟩, ⟨hD.hasType.2, ?_, .proj, .rfl⟩⟩
    exact (hP a a1 a2 a3 a4 a5 a8 a9 a12 ih13.right he' ih15.right).defeq_r ih15.sound.symm
  | projIota a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _ _ a13 _ _ _ _ ih14 ih15 ih16 ih17 =>
    have hD := VEnv.IsDefEq.projIota (hE.inducts a1) a2 a3 a4 a5 a6 a7 a8 a9 a10 ih15.defeq a13 ih16.defeq
      ih17.defeq
    exact ⟨hD, hPI a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a13 ih14.left ih15.left ih16.left ih17.left,
      ⟨hD.hasType.1, hP a1 a2 a3 a4 a6 a7 a8 a10 a13 ih14.left ih15.left ih16.left, .proj, .rfl⟩,
      ih17.left⟩
  | projEta a a1 a2 a3 a4 a5 a6 a7 _ _ _ _ ih9 ih10 ih11 =>
    exact ⟨.projEta (hE.inducts a) a1 a2 a3 a4 a5 a6 a7 ih10.defeq ih11.defeq,
      hPE a a1 a2 a3 a4 a5 a6 a7 ih9.left ih10.left ih11.left, ih10.left, ih11.left⟩

end LogRel
end Lean4Lean

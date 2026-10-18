import Lean4Lean.Theory.Typing.LogRel.AdeqIndTy
import Lean4Lean.Theory.Typing.LogRel.BlockStage
import Lean4Lean.Theory.Typing.LogRel.AdeqCtor
import Lean4Lean.Theory.Typing.LogRel.StructProj

/-!
# Related substitutions across models, and the constructors' telescopes of a type former

Related substitutions mention the model only through interpretations of their context's types, so
two models that read those types alike have the same related substitutions (`LR.SubstWF.sameOn`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}

/-- A related substitution's context extends the context it substitutes into. -/
theorem LR.SubstWF.length_le {X : AxInterp} :
    @LR.SubstWF env U _ X henv hU Γ₀ σ σ' Γ ρ → Γ₀.length ≤ Γ.length
  | .id => Nat.le_refl _
  | .cons W .. => Nat.le_succ_of_le W.length_le

/-- One related pair at a type the two models read alike is related in both. -/
theorem LR.Subst1.sameOn {X Y : AxInterp} {Q : Name → Prop}
    (H' : SameOn env Y X Q) {A₀ : VExpr} (hQ : A₀.ConstsSat Q)
    (h : @LR.Subst1 env U _ X henv hU Γ₀ x x' A₀ A A' ρ i) :
    @LR.Subst1 env U _ Y henv hU Γ₀ x x' A₀ A A' ρ i := by
  refine ⟨h.1, fun n a ha => ?_⟩
  have ⟨h1, h2⟩ := h.2 a (LE_Interp.sameOn H' ha hQ)
  exact ⟨h1, fun m hm hma => h2 (LE_Interp.sameOn H' hm trivial) hma⟩

/-- Related substitutions of a context extension whose types two models read alike are related in
both. -/
theorem LR.SubstWF.sameOn {X Y : AxInterp} {Q : Name → Prop} (H : SameOn env X Y Q)
    (H' : SameOn env Y X Q)
    (W : @LR.SubstWF env U _ X henv hU Γ₀ σ σ' Γ ρ) :
    ∀ Δ, Γ = Δ ++ Γ₀ → (∀ A ∈ Δ, A.ConstsSat Q) →
    @LR.SubstWF env U _ Y henv hU Γ₀ σ σ' Γ ρ := by
  induction W with
  | id => intro _ _ _; exact .id
  | cons W h1 h2 h3 h4 h5 ih =>
    intro Δ e hQ
    obtain _ | ⟨A', Δ'⟩ := Δ
    · have := LR.SubstWF.length_le W
      simp only [List.nil_append] at e
      rw [← e] at this; exact absurd this (by simp)
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hA := hQ _ (.head _)
    refine .cons (ih Δ' rfl fun B hB => hQ B (.tail _ hB)) (fun hb => ?_)
      (LE_Interp.sameOn H h2 hA) h3 h4 (LR.Subst1.sameOn H' hA.liftN h5)
    obtain ⟨a', h6, h7, h8⟩ := h1 (LE_Interp.sameOn H' hb hA)
    exact ⟨a', h6, LE_Interp.sameOn H h7 hA, h8⟩

/-- The substitution without its first `n` values. -/
def _root_.Lean4Lean.VExpr.Subst.tailN : VExpr.Subst → Nat → VExpr.Subst
  | σ, 0 => σ
  | σ, n+1 => tailN σ.tail n

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.Subst.tailN_apply : ∀ (σ : VExpr.Subst) (n i : Nat),
    σ.tailN n i = σ (i + n)
  | _, 0, _ => rfl
  | σ, n+1, i => by
    rw [VExpr.Subst.tailN, tailN_apply σ.tail n i]; simp only [VExpr.Subst.tail, Nat.add_assoc]

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VExpr.Subst.tailN_succ (σ : VExpr.Subst) (n : Nat) :
    σ.tailN (n+1) = (σ.tailN n).tail := by
  funext i; simp only [VExpr.Subst.tailN_apply, VExpr.Subst.tail]; congr 1; omega

theorem _root_.Lean4Lean.LogRel.Valuation.push_inj' {ρ ρ' : Valuation} {x x' : TShape}
    (h : ρ.push x = ρ'.push x') : ρ = ρ' :=
  funext fun n => congrFun h (n+1)

/-- Related substitutions of a context extended by one type, at a valuation extended by one value,
are related without it, when the context still extends the one substituted into. -/
theorem LR.SubstWF.dropOne {X : AxInterp}
    (W : @LR.SubstWF env U _ X henv hU Γ₀ σ σ' (A :: Γ) (ρ.push x)) (hl : Γ₀.length ≤ Γ.length) :
    @LR.SubstWF env U _ X henv hU Γ₀ σ.tail σ'.tail Γ ρ := by
  rcases LR.SubstWF.cons_inv W with ⟨-, e⟩ | ⟨ρt, x', e, W'⟩
  · subst e; simp at hl; omega
  · obtain rfl := Valuation.push_inj' e; exact W'

/-- Related substitutions of a context extended by a telescope, at a valuation extended by one value
per binder, are related without them, when the context still extends the one substituted into. -/
theorem LR.SubstWF.dropN {X : AxInterp} :
    ∀ {Is : List VExpr} {is : List TShape} {Γ : List VExpr} {ρ : Valuation} {σ σ' : VExpr.Subst},
    Γ₀.length ≤ Γ.length → Is.length = is.length →
    @LR.SubstWF env U _ X henv hU Γ₀ σ σ' (Is.reverse ++ Γ) (pushAll ρ is) →
    @LR.SubstWF env U _ X henv hU Γ₀ (σ.tailN is.length) (σ'.tailN is.length) Γ ρ
  | [], [], _, _, _, _, _, _, W => W
  | B :: Bs, y :: ys, Γ, ρ, σ, σ', hl, h, W => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, pushAll] at W
    have := LR.SubstWF.dropN (by simp; omega) h W
    rw [List.length_cons, VExpr.Subst.tailN_succ, VExpr.Subst.tailN_succ]
    exact this.dropOne hl

/-- A type adequate under related substitutions is related to its counterpart at every type shape
below an interpretation of it, with what the relation knows of their typing. -/
theorem LR.Adequate.tyRel [AxInterp] {Γ₀ Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    {Tel Tel' : VExpr} {u : VLevel} (hu : u.WF U)
    (hS : StrongSoundEq env U Γ Tel Tel (.sort u))
    (HA : AdeqStmt (U := U) henv hU Γ₀ Γ Tel Tel' (.sort u))
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {y : TShape} (hy : LE_Interp env ρ y Tel)
    {n : Nat} {b : WShape n} (hb : b.T ≤ y) (ht : b.HasType .type) :
    (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (Tel.subst σ) (Tel'.subst σ') b ∧
    (LR (U := U) (Γ := Γ₀) henv hU n).TyTy (Tel.subst σ) b ∧
    (LR (U := U) (Γ := Γ₀) henv hU n).TyTy (Tel'.subst σ') b := by
  obtain ⟨n', m', a, -, le_m, hm', ha, hty⟩ := (hS.left.sound W.fits hy).out
  let k := max n n'
  have hn : n ≤ k := Nat.le_max_left _ _
  have hn' : n' ≤ k := Nat.le_max_right _ _
  have hm'' : LE_Interp env ρ (m'.lift k).T Tel := hm'.lift hn'
  have ha'' : LE_Interp env ρ (a.lift k).T (.sort u) := ha.lift hn'
  have hty'' : (m'.lift k).HasType (a.lift k) := (WShape.HasType.lift hn').2 hty
  have le_a : b.T ≤ (m'.lift k).T :=
    hb.trans (le_m.trans (TShape.lift_eqv (a := m'.T) hn').2)
  have hA := HA hm'' ha'' hty''
  have R1 := (hA.1 W).2
  have R2 := hA.2 W.left
  simp only [VExpr.subst] at R1 R2
  have T1 := LR.toValTy hn le_a ht ha'' hty'' R1
  have T2 := LR.toValTy hn le_a ht ha'' hty'' R2
  have hue : TyEq env U Γ₀ (.sort u) (.sort u) := TyEq.refl (.sort hu)
  refine ⟨(LR _ _ _).trans_ty T2 T1, (LR.toTyTy hn le_a ht ha'' hty'' hue R2).1,
    (LR.toTyTy hn le_a ht ha'' hty'' hue R1).2⟩

/-- A telescope adequate under related substitutions is related along any telescope shape below an
interpretation of it. -/
theorem LR.Adequate.teleRel [AxInterp] {Γ₀ Γ : List VExpr} {σ σ' : VExpr.Subst} {ρ : Valuation}
    {Tel Tel' : VExpr} {u : VLevel} (hu : u.WF U)
    (hS : StrongSoundEq env U Γ Tel Tel (.sort u))
    (HA : AdeqStmt (U := U) henv hU Γ₀ Γ Tel Tel' (.sort u))
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) {y : TShape} (hy : LE_Interp env ρ y Tel)
    {n k : Nat} {tel : WShape n} (hb : tel.T ≤ y) (ht : tel.HasType .type)
    (hk : k ≤ piCount (Tel.subst σ)) (hk' : k ≤ piCount (Tel'.subst σ')) :
    TeleRel (LR (U := U) (Γ := Γ₀) henv hU n) k (Tel.subst σ) (Tel'.subst σ') tel := by
  have hb' : (tel.lift (n+1)).T ≤ y :=
    (TShape.lift_eqv (a := tel.T) (Nat.le_succ n)).1.trans hb
  have ht' : (tel.lift (n+1)).HasType .type :=
    WShape.lift_type ▸ (WShape.HasType.lift (Nat.le_succ n)).2 ht
  obtain ⟨H, Y, Y'⟩ := LR.Adequate.tyRel hu hS HA W hy hb' ht'
  exact TeleRel.of_tyDefEq ht hk hk' H Y Y'

omit [ShapeEnv] in
/-- A term over `np` parameters, substituted by the parameter values of a spine, is the term under
the substitution without the values after them. -/
theorem subst_params_tailN (σ : VExpr.Subst) {np : Nat} (ni : Nat) {Tel : VExpr}
    (hcl : Tel.ClosedN np) :
    Tel.subst (VExpr.Subst.id.consList ((VExpr.bvars np ni).map (·.subst σ))) =
      Tel.subst (σ.tailN ni) := by
  refine hcl.subst_congr fun i hi => ?_
  rw [VExpr.Subst.consList_lt _ _ _ (by simpa [VExpr.bvars] using hi)]
  simp only [VExpr.bvars, List.map_reverse, List.reverse_reverse, List.map_map,
    List.getElem_map, List.getElem_range, Function.comp, VExpr.subst,
    VExpr.Subst.tailN_apply]

omit [ShapeEnv] in
/-- A spine's first `np` arguments are the parameters' values. -/
theorem bvars_take_map (σ : VExpr.Subst) (np ni : Nat) :
    ((VExpr.bvars (np + ni) 0).map (·.subst σ)).take np = (VExpr.bvars np ni).map (·.subst σ) := by
  rw [← bvars_append' np ni 0, Nat.add_zero, List.map_append, List.take_append_of_le_length
    (by simp [VExpr.bvars]), List.take_of_length_le (by simp [VExpr.bvars])]

omit [ShapeEnv] in
theorem piCount_subst_ge : ∀ (e : VExpr) (σ : VExpr.Subst), piCount e ≤ piCount (e.subst σ)
  | .forallE _ B, σ => Nat.succ_le_succ (piCount_subst_ge B σ.lift)
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _
  | .proj .., _ => Nat.zero_le _

/-- The constructors' telescopes of a type former's two applications at related arguments are
related at the type shape's telescopes, given, for each constructor, its telescope over the
parameters adequate in a model `G` that reads the parameters' types as the ambient model does and
interprets the constructors' types as the type former's interpretation read them. -/
theorem typeFormer_HC (X G : AxInterp) (hMG : @ModelEnv _ G env)
    {Q : Name → Prop} (hXG : SameOn env X G Q) (hGX : SameOn env G X Q)
    {c : Name} {d : VInductDecl} {T : VInductiveType} (hn : Inert env c)
    (hcon : ∀ c' ∈ T.ctors, ∀ ci, env.constants c'.name = some ci → ci.type = c'.type)
    {ls ls₃ : List VLevel} (hBp : ∀ A ∈ d.params.map (·.instL ls₃), A.ConstsSat Q)
    {R : TShape → VExpr → Prop} (hR : ∀ h e, R h e → @LE_Interp _ G env .nil h e)
    (hAd : ∀ (i : Nat) (c' : VConstructor), T.ctors[i]? = some c' → ∀ (l₁ l₂ : List VLevel), List.Forall₂ (· ≈ ·) ls l₁ →
      List.Forall₂ (· ≈ ·) ls l₂ → (∀ x ∈ l₁, x.WF U) → (∀ x ∈ l₂, x.WF U) →
      ∃ (Ps₁ Ps₂ : List VExpr) (Tel₁ Tel₂ : VExpr) (u : VLevel), c'.type.instL l₁ = .foralls Ps₁ Tel₁ ∧
        c'.type.instL l₂ = .foralls Ps₂ Tel₂ ∧ Ps₁.length = d.params.length ∧
        Ps₂.length = d.params.length ∧ Tel₁.ClosedN d.params.length ∧
        Tel₂.ClosedN d.params.length ∧ piCount Tel₁ = c'.fields.length ∧
        piCount Tel₂ = c'.fields.length ∧ u.WF U ∧
        @StrongSoundEq _ G env U ((d.params.map (·.instL ls₃)).reverse ++ Γ₀) Tel₁ Tel₁ (.sort u) ∧
        @AdeqStmt env U _ G henv hU Γ₀ ((d.params.map (·.instL ls₃)).reverse ++ Γ₀)
          Tel₁ Tel₂ (.sort u))
    {n : Nat} (rargs ctys : List (WShape n)) {F F' : VExpr} {σ σ' : VExpr.Subst}
    (hF : ConstAt U c ls F) (hF' : ConstAt U c ls F')
    (W : @LR.SubstWF env U _ X henv hU Γ₀ σ σ'
      (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs))
    (hlen : rargs.length = d.params.length + T.indices.length)
    (hcl : ctys.length = T.ctors.length)
    (hcty : ∀ (i : Nat) (c' : VConstructor) (cty : WShape n), T.ctors[i]? = some c' →
      ctys[i]? = some cty → ∃ h, R h (c'.type.instL ls) ∧
        PiAppS h ((rargs.reverse.take d.params.length).map (·.T)) cty.T)
    (l : List (WShape n)) (hl : l.Forall₂ (· ≤ ·) (rargs.reverse ++ ctys))
    (htel : ∀ i, (ctorTel (typeHeadOf c rargs.length T) l i).HasType .type) :
    IndTele (LR (U := U) (Γ := Γ₀) henv hU n) (typeHeadOf c rargs.length T) l
      (spineAt F (d.params ++ T.indices).length σ) (spineAt F' (d.params ++ T.indices).length σ') := by
  obtain ⟨l₁, e₁, hl₁, rfl⟩ := hF
  obtain ⟨l₂, e₂, hl₂, rfl⟩ := hF'
  intro lsX AsX lsX' AsX' rM rN c'' i k ci hi hk hc
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.determ hU .rfl hn.whnf rM hn.whnf)
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.determ hU .rfl hn.whnf rN hn.whnf)
  -- the constructor
  obtain ⟨hil, hie, -⟩ := List.idxOf?_eq_some_iff.1 hi
  have hil' : i < T.ctors.length := by simpa using hil
  obtain ⟨c', hci⟩ : ∃ c', T.ctors[i]? = some c' := ⟨_, List.getElem?_eq_getElem hil'⟩
  have hcm : c' ∈ T.ctors := List.mem_of_getElem? hci
  have hname : c'.name = c'' := by
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hci; simpa using hie
  have hkk : k = c'.fields.length := by
    rw [List.getElem?_map, hci] at hk; exact (Option.some.inj hk).symm
  subst hname hkk
  have hcity := hcon c' hcm ci hc
  -- its shape in the interpretation
  obtain ⟨cty, hcty'⟩ : ∃ cty, ctys[i]? = some cty :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨h, hRh, hPi⟩ := hcty i c' cty hci hcty'
  have hle : ctorTel (typeHeadOf c rargs.length T) l i ≤ cty := by
    have hll := Lean4Lean.List.Forall₂.length_eq hl
    simp only [List.length_append, List.length_reverse] at hll
    have hlt : rargs.length + i < l.length := by omega
    simp only [ctorTel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
    have hc2 : (rargs.reverse ++ ctys)[rargs.length + i]? = some cty := by
      rw [List.getElem?_append_right (by simp)]; simpa using hcty'
    exact List.Forall₂.getElem?' hl (List.getElem?_eq_getElem hlt) hc2
  -- the constructor's telescope over the parameters, adequate in `G`
  obtain ⟨Ps₁, Ps₂, Tel₁, Tel₂, u, eT₁, eT₂, hP₁, hP₂, hc₁, hc₂, hk₁, hk₂, hu, hS, HA⟩ :=
    hAd i c' hci l₁ l₂ e₁ e₂ hl₁ hl₂
  have hy : @LE_Interp _ G env (pushAll .nil ((rargs.reverse.take d.params.length).map (·.T)))
      cty.T Tel₁ := by
    have H := (hR _ _ hRh).levels (VExpr.LvEqv.instL e₁ _)
    rw [eT₁, ← List.append_nil Ps₁] at H
    exact LE_Interp.piAppS_foralls hMG Ps₁ H hPi (by simp [hP₁]; omega)
  -- the related substitutions of the parameters
  have W' : @LR.SubstWF env U _ X henv hU Γ₀ (σ.tailN T.indices.length) (σ'.tailN T.indices.length)
      ((d.params.map (·.instL ls₃)).reverse ++ Γ₀)
      (pushAll .nil ((rargs.reverse.take d.params.length).map (·.T))) := by
    have e : valOf rargs = pushAll (pushAll .nil ((rargs.reverse.take d.params.length).map (·.T)))
        ((rargs.reverse.drop d.params.length).map (·.T)) := by
      rw [← pushAll_append, ← List.map_append, List.take_append_drop]
    rw [e, List.map_append, List.reverse_append, List.append_assoc] at W
    have := LR.SubstWF.dropN (by simp) (by simp; omega) W
    simpa [hlen] using this
  have WG := LR.SubstWF.sameOn hXG hGX W' _ rfl fun A hA => hBp A (List.mem_reverse.1 hA)
  have TR := @LR.Adequate.teleRel _ env U henv hU G _ _ _ _ _ _ _ _ hu hS HA WG _ hy n
    c'.fields.length _ (WShape.LE.T_iff.2 hle) (htel i)
    (by have := piCount_subst_ge Tel₁ (σ.tailN T.indices.length); omega)
    (by have := piCount_subst_ge Tel₂ (σ'.tailN T.indices.length); omega)
  -- the telescopes are the constructor's at the spine's parameters
  have hpc : piCount ci.type - c'.fields.length = d.params.length := by
    rw [hcity, ← piCount_instL _ l₁, eT₁, piCount_foralls]; omega
  have key : ∀ (lj : List VLevel) (Psj : List VExpr) (Telj : VExpr) (τ : VExpr.Subst),
      c'.type.instL lj = .foralls Psj Telj → Psj.length = d.params.length →
      Telj.ClosedN d.params.length →
      ctorTeleAt ci c'.fields.length lj ((VExpr.bvars (d.params ++ T.indices).length 0).map
        (·.subst τ)) = Telj.subst (τ.tailN T.indices.length) := by
    intro lj Psj Telj τ eT hPj hcj
    rw [ctorTeleAt, hpc, hcity, eT, List.length_append, bvars_take_map,
      piInst_foralls _ _ _ (by simp [VExpr.bvars, hPj]), subst_params_tailN τ _ hcj]
  rw [key l₁ Ps₁ Tel₁ σ eT₁ hP₁ hc₁, key l₂ Ps₂ Tel₂ σ' eT₂ hP₂ hc₂]
  exact TR

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.TeleDefEq.length_eq'' {E : VEnv} {U : Nat} :
    ∀ {Γ As Bs}, E.TeleDefEq U Γ As Bs → As.length = Bs.length
  | _, [], [], .nil => rfl
  | _, _ :: _, _ :: _, .cons _ t => by simp [VEnv.TeleDefEq.length_eq'' t]

/-- A constructor's telescope over its parameters, at two equivalent instances of the levels, in
the parameters' context at a third, adequate given adequacy of the environment it is typed in with
injectivity there. This is `typeFormer_HC`'s premise for one constructor. -/
theorem ctorTele_adeq [AxInterp] (hM : ModelEnv env) {E₀ : VEnv} (hE₀ : E₀ ≤ env)
    (hE₀o : E₀.Ordered) (hI : E₀.Inj)
    (hS : ∀ {Γ M N A}, E₀.IsDefEqStrong U Γ M N A → StrongSoundEq env U Γ M N A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) (IH : AdequacyHyps (U := U) henv hU E₀ Γ₀)
    {d : VInductDecl} {T : VInductiveType} {c' : VConstructor}
    (hP : E₀.IsTele d.uvars [] d.params) (hcw : c'.WF E₀ d T)
    {ls₃ l₁ l₂ : List VLevel} (h3 : ∀ l ∈ ls₃, l.WF U) (h1 : ∀ l ∈ l₁, l.WF U)
    (h2 : ∀ l ∈ l₂, l.WF U) (e1 : List.Forall₂ (· ≈ ·) ls₃ l₁)
    (e2 : List.Forall₂ (· ≈ ·) ls₃ l₂) :
    ∃ (Ps₁ Ps₂ : List VExpr) (Tel₁ Tel₂ : VExpr) (u : VLevel), c'.type.instL l₁ = .foralls Ps₁ Tel₁ ∧
      c'.type.instL l₂ = .foralls Ps₂ Tel₂ ∧ Ps₁.length = d.params.length ∧
      Ps₂.length = d.params.length ∧ Tel₁.ClosedN d.params.length ∧
      Tel₂.ClosedN d.params.length ∧ piCount Tel₁ = c'.fields.length ∧
      piCount Tel₂ = c'.fields.length ∧ u.WF U ∧
      StrongSoundEq env U ((d.params.map (·.instL ls₃)).reverse ++ Γ₀) Tel₁ Tel₁ (.sort u) ∧
      AdeqStmt (U := U) henv hU Γ₀ ((d.params.map (·.instL ls₃)).reverse ++ Γ₀)
        Tel₁ Tel₂ (.sort u) := by
  obtain ⟨ps, Ds, eT, hTD, hFW, -, -⟩ := hcw.shape
  generalize hB : VExpr.foralls Ds (T.typeApp (VLevel.params d.uvars)
    (VExpr.bvars d.params.length c'.fields.length) c'.indices) = B at eT
  have hpl : ps.length = d.params.length := hTD.length_eq''
  have hDl : Ds.length = c'.fields.length := hFW.length
  have eT' : c'.type = .foralls ps B := by rw [eT, foralls_append, hB]
  have hty := hcw.type; rw [eT'] at hty
  obtain ⟨-, v, hBv⟩ := VEnv.IsType.foralls_inv hE₀o hty
  have hctx : E₀.IsDefEqCtx d.uvars [] (ps.reverse ++ []) (d.params.reverse ++ []) :=
    VEnv.TeleDefEq.defeqCtx_of_inj hE₀o hI hTD .zero trivial hP
  have hBv' : E₀.HasType d.uvars d.params.reverse B (.sort v) :=
    VEnv.HasType.defeqDFC hE₀o (by simpa using hctx) (by simpa using hBv)
  have hΓP : OnCtx d.params.reverse (E₀.IsType d.uvars) := by simpa using hP.onCtx trivial
  have D1 := VEnv.IsDefEq.instL_r hE₀o hΓP h3 h1 e1 hBv'
  have D2 := VEnv.IsDefEq.instL_r hE₀o hΓP h3 h2 e2 hBv'
  have D12 := D1.symm.trans D2
  simp only [VExpr.instL, List.map_reverse] at D12
  have hPT : E₀.IsTele U [] (d.params.map (·.instL ls₃)) := by simpa using hP.instL h3
  have hΓB : OnCtx (d.params.map (·.instL ls₃)).reverse (E₀.IsType U) := by
    simpa using hPT.onCtx trivial
  have hcc : CtxClosed (d.params.map (·.instL ls₃)).reverse := by
    simpa using VEnv.IsTele.ctxClosed hE₀o hPT trivial
  have DS := (D12.strong hE₀o hΓB).weakN hE₀o (.right hcc Γ₀)
  obtain ⟨c1, c2, -⟩ := D12.closedN' hE₀o.closed hcc
  simp only [List.length_reverse, List.length_map] at c1 c2
  simp only [List.length_reverse, List.length_map] at DS
  rw [c1.liftN_eq (Nat.le_refl _), c2.liftN_eq (Nat.le_refl _)] at DS
  simp only [VExpr.liftN] at DS
  have hpc : piCount B = c'.fields.length := by
    rw [← hB, piCount_foralls, hDl]
    cases hn : T.nested <;> simp [VInductiveType.typeApp, hn, piCount_appN_const]
  refine ⟨ps.map (·.instL l₁), ps.map (·.instL l₂), B.instL l₁, B.instL l₂, v.inst ls₃,
    by rw [eT', VEnv.foralls_instL'], by rw [eT', VEnv.foralls_instL'], by simp [hpl], by simp [hpl],
    by simpa using c1, by simpa using c2, by rw [piCount_instL, hpc],
    by rw [piCount_instL, hpc], ?_, hS DS.hasType.1, ?_⟩
  · exact VLevel.WF.inst h3
  · exact LR.adequacy_of hM hE₀ hS hΓ₀ IH DS (OnCtx.append_closed hE₀o hE₀ hΓ₀ hΓB)

/-- `SpineAtB` for a recorded type former: its telescope is the parameters and indices, typed in
the environment `E` before the block; its declared type's interpretations are the telescope's
(`hinterp`) and the two are related at them (`hconv`); and at its arity it is related by
`typeFormer_sat`, given the constructors' telescopes (`HC`) and the typing of stuck values (`HY`). -/
theorem typeFormer_spineAtB [AxInterp] (hM : ModelEnv env) (henvW : env.WF)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E : VEnv} {c : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (hs : env.inducts c = some (d, t)) (hT : d.types[t]? = some T) (hdom : ¬AxInterp.dom c)
    (hP : E.IsTele d.uvars [] d.params) (hI : E.IsTele d.uvars d.params.reverse T.indices)
    {ci : VConstant} {ls ls₃ : List VLevel}
    (hls₃ : ∀ l ∈ ls₃, l.WF U) (e₃ : List.Forall₂ (· ≈ ·) ls ls₃)
    (hinterp : ∀ {t'}, LE_Interp env .nil t' (ci.type.instL ls₃) →
      LE_Interp env .nil t' (.foralls ((d.params ++ T.indices).map (·.instL ls₃))
        (.sort (d.level.inst ls₃))))
    (hconvE : TyEq env U Γ₀ (.foralls ((d.params ++ T.indices).map (·.instL ls₃))
        (.sort (d.level.inst ls₃))) (ci.type.instL ls₃))
    (hconv : ∀ {n} {b : WShape n}, LE_Interp env .nil b.T (ci.type.instL ls₃) →
      b.HasType .type →
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (.foralls ((d.params ++ T.indices).map (·.instL ls₃))
        (.sort (d.level.inst ls₃))) (ci.type.instL ls₃) b)
    {R : TShape → VExpr → Prop}
    (HC : ∀ {n} (rargs ctys : List (WShape n)) {F F' : VExpr} {σ σ' : VExpr.Subst},
      ConstAt U c ls F → ConstAt U c ls F' →
      LR.SubstWF (U := U) henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length → ctys.length = T.ctors.length →
      (∀ (i : Nat) (c' : VConstructor) (cty : WShape n), T.ctors[i]? = some c' →
        ctys[i]? = some cty → ∃ h, R h (c'.type.instL ls) ∧
          PiAppS h ((rargs.reverse.take d.params.length).map (·.T)) cty.T) →
      ∀ l : List (WShape n), l.Forall₂ (· ≤ ·) (rargs.reverse ++ ctys) →
      (∀ i, (ctorTel (typeHeadOf c rargs.length T) l i).HasType .type) →
      IndTele (LR (U := U) (Γ := Γ₀) henv hU n) (typeHeadOf c rargs.length T) l
        (spineAt F (d.params ++ T.indices).length σ) (spineAt F' (d.params ++ T.indices).length σ'))
    (HY : ∀ {n} (rargs : List (WShape n)) {F : VExpr} {σ σ' : VExpr.Subst}, ConstAt U c ls F →
      LR.SubstWF (U := U) henv hU Γ₀ σ σ'
        (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs) →
      rargs.length = d.params.length + T.indices.length →
      StructTy env U Γ₀ (typeHeadOf c rargs.length T) (spineAt F (d.params ++ T.indices).length σ) ∧
      StructTy env U Γ₀ (typeHeadOf c rargs.length T) (spineAt F (d.params ++ T.indices).length σ')) :
    SpineAtB (U := U) (henv := henv) (hU := hU)
      (fun Γ' A => ∃ Δ, Γ' = Δ ++ Γ₀ ∧ OnCtx Δ (E.IsType U) ∧ E.IsType U Δ A) Γ₀ c ls R
      (ci.type.instL ls₃) ((d.params ++ T.indices).map (·.instL ls₃)) (.sort (d.level.inst ls₃)) := by
  refine ⟨fun A => ?_, ⟨[], by simp, trivial, ?_⟩, hinterp, fun hb hwb H => ?_,
    fun rargs m H hlen F F' σ σ' hF hF' W w a hw hwa ha =>
      typeFormer_sat hM henvW hΓ₀ hs hT hdom hls₃ e₃ HC HY rargs H hlen hF hF' W w a hw hwa ha⟩
  · have A0 := ConstArity.indTy hs hT
    cases hM.roles A A0
    have := ConstArity.determ A A0
    simpa using this
  · have hPI : E.IsTele U [] ((d.params ++ T.indices).map (·.instL ls₃)) := by
      simpa [List.map_append] using (VEnv.IsTele.append hP (by simpa using hI)).instL hls₃
    exact VEnv.IsTele.foralls hPI ⟨_, VEnv.HasType.sort (VLevel.WF.inst hls₃)⟩
  · exact (LR _ _ _).conv hconvE (hconv hb hwb.isType) H

/-- What `typeFormer_spineAtB` needs of a type former's declared type, in a model `X`, from its
equality with the telescope in an environment `E₁` that a model `G` is sound and adequate for, `G`
reading both types as `X` does. -/
theorem typeFormer_conv (X G : AxInterp) (hMG : @ModelEnv _ G env)
    {Q : Name → Prop} (hXG : SameOn env X G Q) (hGX : SameOn env G X Q)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E₁ : VEnv} (hE₁ : E₁ ≤ env) (hE₁o : E₁.Ordered)
    (hS₁ : ∀ {Γ M N A}, E₁.IsDefEqStrong U Γ M N A → @StrongSoundEq _ G env U Γ M N A)
    (IH₁ : @AdequacyHyps env U _ G henv hU E₁ Γ₀)
    {Ty B : VExpr} {uv : Nat} {u : VLevel} (hdef : E₁.IsDefEq uv [] Ty B (.sort u))
    (hQT : Ty.ConstsSat Q) (hQB : B.ConstsSat Q)
    {ls₃ : List VLevel} (hls₃ : ∀ l ∈ ls₃, l.WF U) :
    (∀ {t'}, @LE_Interp _ X env .nil t' (Ty.instL ls₃) → @LE_Interp _ X env .nil t' (B.instL ls₃)) ∧
    TyEq env U Γ₀ (B.instL ls₃) (Ty.instL ls₃) ∧
    (∀ {n} {b : WShape n}, @LE_Interp _ X env .nil b.T (Ty.instL ls₃) → b.HasType .type →
      (LR (U := U) (Γ := Γ₀) henv hU n).TyDefEq (B.instL ls₃) (Ty.instL ls₃) b) := by
  have D₀ := (VEnv.IsDefEq.instL hls₃ hdef).symm
  simp only [List.map_nil] at D₀
  have DS := IsDefEq.weak_closed hE₁o (Δ := []) trivial D₀ Γ₀
  simp only [List.nil_append] at DS
  have SS := hS₁ DS
  have hSE : ∀ {m}, @LE_Interp _ G env .nil m (B.instL ls₃) ↔
      @LE_Interp _ G env .nil m (Ty.instL ls₃) := SS.sound .nil
  refine ⟨fun ht => ?_, .base (DS.defeq.mono hE₁), fun {n b} hb ht => ?_⟩
  · exact LE_Interp.sameOn hGX (hSE.2 (LE_Interp.sameOn hXG ht hQT.instL)) hQB.instL
  · have hbG := LE_Interp.sameOn hXG hb hQT.instL
    have HA : @AdeqStmt env U _ G henv hU Γ₀ Γ₀ (B.instL ls₃) (Ty.instL ls₃)
        ((VExpr.sort u).instL ls₃) := fun hm ha hmem =>
      LR.adequacy_of (U := U) (henv := henv) (hU := hU) hMG hE₁ hS₁ hΓ₀ IH₁ DS hΓ₀ hm ha hmem
    have R := @LR.Adequate.tyRel _ env U henv hU G Γ₀ Γ₀ _ _ _ _ _ _ (VLevel.WF.inst hls₃)
      (hS₁ DS.hasType.1) HA .id _ (hSE.2 hbG) n b (TShape.LE.rfl) ht
    simpa [VExpr.subst_id] using R.1

end LogRel
end Lean4Lean

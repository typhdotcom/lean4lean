import Lean4Lean.Theory.Typing.LogRel.Mutual

/-!
# An inductive block's constants interpreted where they are related

An inductive type's interpretation reads its constructors' types, which mention the type, and a
recursor's reads its rules' right-hand sides, which mention the recursor; both are typed in an
environment with the block's constants as axioms. As for a recursive definition (`Mutual.lean`), the
model that interprets the block's types and recursors by the shapes where they are already related
(`GoodC`) breaks the cycle: there they are related by definition, so what is typed with them as
axioms is adequate, and every interpretation in the model before it is one in this model
(`transferB`), given that a constant's interpretation built from adequate pieces is related.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat}

variable (henv : env.Ordered) (hU : StepUniq env) in
/-- The shapes at which the constant `c` of `cs` is related: shapes interpreting it in `X`, typed at
an interpretation of its type, at which it is related to itself at every equivalent well-formed
levels, at every type shape typing them that interprets its type. -/
def GoodC (X : AxInterp) (Γ₀ : List VExpr) (cs : List (Name × VConstant)) (c : Name)
    (ls : List VLevel) (g : TShape) : Prop :=
  ∃ ci, (c, ci) ∈ cs ∧ ls.length = ci.uvars ∧
    @LE_Interp _ X env .nil g (.const c ls) ∧
    (∃ a₀, g.HasType a₀ ∧ @LE_Interp _ X env .nil a₀ (ci.type.instL ls)) ∧
    ∀ ls₁ ls₂ ls₃, List.Forall₂ (· ≈ ·) ls ls₁ → List.Forall₂ (· ≈ ·) ls ls₂ →
      List.Forall₂ (· ≈ ·) ls ls₃ → (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      (∀ l ∈ ls₃, l.WF U) →
      RelAt (U := U) henv hU Γ₀ (.const c ls₁) (.const c ls₂) (ci.type.instL ls₃)
        (fun t => @LE_Interp _ X env .nil t (ci.type.instL ls₃)) g

set_option warn.classDefReducibility false in
variable (henv : env.Ordered) (hU : StepUniq env) in
/-- The model interpreting the constants `cs` by the shapes they are related at, and every other
constant as `X` does. -/
def GoodOverC (X : AxInterp) (Γ₀ : List VExpr) (cs : List (Name × VConstant)) : AxInterp where
  dom c := X.dom c ∨ c ∈ cs.map (·.1)
  I c ls g := (c ∈ cs.map (·.1) ∧ GoodC (U := U) henv hU X Γ₀ cs c ls g) ∨
    (c ∉ cs.map (·.1) ∧ X.I c ls g)

omit [ShapeEnv] in
theorem List.eq_of_fst {cs : List (Name × VConstant)} (hnd : (cs.map (·.1)).Nodup)
    (h1 : (c, ci) ∈ cs) (h2 : (c, ci') ∈ cs) : ci = ci' := by
  induction cs with
  | nil => cases h1
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.mem_cons] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · subst h1; cases h2; rfl
    · exact (hnd.1 _ h2 (by subst h1; rfl)).elim
    · exact (hnd.1 _ h1 (by subst h2; rfl)).elim
    · exact ih hnd.2 h1 h2

variable {henv : env.Ordered} {hU : StepUniq env}

/-- `GoodC`'s shapes join, given the relation's join. -/
theorem GoodC.join (X : AxInterp) (hM : @ModelEnv _ X env) (hJ : LRJoin (U := U) henv hU Γ₀)
    (hnd : (cs.map (·.1)).Nodup)
    (H1 : GoodC (U := U) henv hU X Γ₀ cs c ls₁ g₁) (H2 : GoodC (U := U) henv hU X Γ₀ cs c ls₂ g₂)
    (hl : List.Forall₂ (· ≈ ·) ls₁ ls₂) :
    g₁.Compat g₂ ∧ GoodC (U := U) henv hU X Γ₀ cs c ls₁ (g₁.join g₂) := by
  obtain ⟨ci, hci, hlen, i1, ⟨a₁, w1, ia1⟩, R1⟩ := H1
  obtain ⟨ci', hci', -, i2, ⟨a₂, w2, ia2⟩, R2⟩ := H2
  cases List.eq_of_fst hnd hci hci'
  have hl' := levels_equiv_symm hl
  have i2' : @LE_Interp _ X env .nil g₂ (.const c ls₁) := i2.levels (.const hl')
  have ia2' : @LE_Interp _ X env .nil a₂ (ci.type.instL ls₁) := ia2.levels (.instL hl' _)
  have hc := i1.compat hM i2'
  have hca := ia1.compat hM ia2'
  have ja := TShape.Join.mk hca
  have aT : (a₁.join a₂).HasType .type := TShape.HasType.join' ja w1.isType w2.isType
  refine ⟨hc, ci, hci, hlen, i1.join' hM i2', ⟨a₁.join a₂,
    TShape.HasType.join' (TShape.Join.mk hc) (TShape.HasType.mono_r (r := true) ja.le.1 aT w1)
      (TShape.HasType.mono_r (r := true) ja.le.2 aT w2), ia1.join' hM ia2'⟩, ?_⟩
  intro k₁ k₂ k₃ e1 e2 e3 wf1 wf2 wf3
  have IA := IAOK.interp X hM (ci.type.instL k₃)
  refine RelAt.join IA hJ (R1 k₁ k₂ k₃ e1 e2 e3 wf1 wf2 wf3)
    (R2 k₁ k₂ k₃ (levels_equiv_trans hl' e1) (levels_equiv_trans hl' e2)
      (levels_equiv_trans hl' e3) wf1 wf2 wf3) w1 (ia1.levels (.instL e3 _)) w2
    (ia2.levels (.instL (levels_equiv_trans hl' e3) _)) hc

/-- `GoodOverC`'s shapes join, given `X`'s and the relation's join. -/
theorem GoodOverC.axOK (X : AxInterp) (hX : @AxOK _ X) (hM : @ModelEnv _ X env)
    (hJ : LRJoin (U := U) henv hU Γ₀) (hnd : (cs.map (·.1)).Nodup) :
    @AxOK _ (GoodOverC (U := U) henv hU X Γ₀ cs) := by
  refine @AxOK.mk _ (GoodOverC (U := U) henv hU X Γ₀ cs) fun {c ls₁ ls₂ m₁ m₂} h1 h2 hl => ?_
  rcases h1 with ⟨hc, h1⟩ | ⟨hc, h1⟩ <;> rcases h2 with ⟨hc', h2⟩ | ⟨hc', h2⟩
  · have := GoodC.join X hM hJ hnd h1 h2 hl; exact ⟨this.1, .inl ⟨hc, this.2⟩⟩
  · exact (hc' hc).elim
  · exact (hc hc').elim
  · have := hX.join h1 h2 hl; exact ⟨this.1, .inr ⟨hc, this.2⟩⟩

/-- `GoodOverC` interprets by given shapes only what `X` does and the constants `cs`, which are
inductive types and recursors. -/
theorem GoodOverC.domRole (X : AxInterp) (hX : @DomRole _ X env)
    (hcs : ∀ p ∈ cs, ∀ {r k}, ConstArity env p.1 r k → r.DomOK) :
    @DomRole _ (GoodOverC (U := U) henv hU X Γ₀ cs) env := fun hc A =>
  hc.elim (fun hx => hX hx A) fun hc' => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'; exact hcs p hp A

/-- A constant of `cs` interpreted in `GoodOverC X cs` is related, at any type shape interpreting
its type in `X`: it is interpreted only below its shapes in `GoodC`. -/
theorem GoodC.rel (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hnd : (cs.map (·.1)).Nodup) {c : Name} {ci : VConstant} (hci : (c, ci) ∈ cs)
    (hls : ∀ l ∈ ls, l.WF U) {m a : WShape n}
    (hm : @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ cs) env ρ m.T (.const c ls))
    (ha : @LE_Interp _ X env .nil a.T (ci.type.instL ls)) (hmem : m.HasType a)
    (ls₁ ls₂ : List VLevel) (e1 : List.Forall₂ (· ≈ ·) ls ls₁) (e2 : List.Forall₂ (· ≈ ·) ls ls₂)
    (w1 : ∀ l ∈ ls₁, l.WF U) (w2 : ∀ l ∈ ls₂, l.WF U) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.const c ls₁) (.const c ls₂)
      (ci.type.instL ls) m a := by
  letI G : AxInterp := GoodOverC (U := U) henv hU X Γ₀ cs
  have hcm : c ∈ cs.map (·.1) := List.mem_map_of_mem (f := (·.1)) hci
  have hdG : G.dom c := .inr hcm
  have H : m.T ≤ TShape.bot ∨ ∃ ls₀ g, List.Forall₂ (· ≈ ·) ls₀ ls ∧ m.T ≤ g ∧
      GoodC (U := U) henv hU X Γ₀ cs c ls₀ g := by
    cases hm with
    | bot => exact .inl TShape.bot_eqv.1
    | const _ _ h3 _ _ h6 _ =>
      cases h6 with
      | bot => exact .inl (h3.trans TShape.bot_eqv.1)
      | lam he hle => exact .inl (h3.trans (Const.lam_le_bot_dom hdG he hle))
      | ext _ a3 a4 a5 =>
        rcases a3 with ⟨-, a3⟩ | ⟨a3, -⟩
        · exact .inr ⟨_, _, a4, h3.trans a5, a3⟩
        · exact (a3 hcm).elim
      | delta a0 => exact (a0 hdG).elim
      | indTy _ _ _ _ _ _ g | ctor _ _ _ _ _ _ _ g | quotTy _ _ _ _ _ _ _ _ g =>
        exact (g hdG).elim
  rcases H with h | ⟨ls₀, g, e0, hmg, ⟨ci', hci', -, -, ⟨a₀, w0, ia0⟩, R⟩⟩
  · cases show m = .bot from TShape.le_bot.1 (h.trans TShape.bot_le)
    exact (LR _ _ _).bot hmem.isType
  · cases List.eq_of_fst hnd hci' hci
    exact (R ls₁ ls₂ ls (levels_equiv_trans e0 e1) (levels_equiv_trans e0 e2) e0 w1 w2 hls).down
      (IAOK.interp X hMX _) w0 (@LE_Interp.levels _ X env _ _ _ _ ia0 (.instL e0 _)) hmg hmem ha

/-- In `GoodOverC X cs`, a constant of `cs` is related wherever it is interpreted. Its type is
interpreted alike in both models. -/
theorem AdeqStmt.goodC (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hnd : (cs.map (·.1)).Nodup) {Q : Name → Prop}
    (hsame : SameOn env (GoodOverC (U := U) henv hU X Γ₀ cs) X Q)
    {c : Name} {ci : VConstant} (hci : (c, ci) ∈ cs) (hQ : ci.type.ConstsSat Q)
    (hcon : env.constants c = some ci)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ (GoodOverC (U := U) henv hU X Γ₀ cs) henv hU Γ₀ Γ
      (.const c ls) (.const c ls') (ci.type.instL ls) := by
  have hclX : ClosedRules env := hMX.closed
  have htc : (ci.type.instL ls).ClosedN := (hclX.constType hcon).instL
  letI G : AxInterp := GoodOverC (U := U) henv hU X Γ₀ cs
  intro ρ n m a hm ha hmem
  have ha' : @LE_Interp _ X env .nil a.T (ci.type.instL ls) :=
    (@LE_Interp.closed_iff _ X env hclX _ htc _ _ _).1 (LE_Interp.sameOn hsame ha hQ.instL)
  have rfl' := List.forall₂_refl' (r := (· ≈ ·)) (l := ls) fun _ => (rfl : VLevel.Equiv _ _)
  have key := GoodC.rel X hMX hnd hci hls hm ha' hmem
  exact LR.Adequate.of_closed (M := .const c ls) (N := .const c ls') trivial trivial
    htc (key _ _ rfl' rfl' hls hls)
    (key _ _ heq heq hls' hls') (key _ _ rfl' heq hls hls')

/-- Every interpretation in `X` is one in `GoodOverC X cs`, given that a constant of `cs`
interpreted from pieces that are interpretations in `GoodOverC X cs` too is at a shape of `GoodC`
(`hgood`). -/
theorem LE_Interp.transferB (X : AxInterp)
    (hcon : ∀ p ∈ cs, env.constants p.1 = some p.2)
    (hgood : ∀ {n c ci ls R m' a ρ}, (c, ci) ∈ cs → env.constants c = some ci →
      ls.length = ci.uvars → m'.HasType a → @LE_Interp _ X env ρ a (ci.type.instL ls) →
      @Const _ X env c ls R n [] m' →
      (∀ h e, R h e → @LE_Interp _ X env ρ h e ∧
        @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ cs) env ρ h e) →
      GoodC (U := U) henv hU X Γ₀ cs c ls m')
    (H : @LE_Interp _ X env ρ m e) :
    @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ cs) env ρ m e := by
  letI G : AxInterp := GoodOverC (U := U) henv hU X Γ₀ cs
  induction H with
  | bot => exact .bot
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | app _ _ h3 ih1 ih2 => exact .app ih1 ih2 h3
  | lam _ h2 _ h4 ih1 ih3 => exact .lam ih1 h2 (fun x hx => ih3 x hx) h4
  | forallE _ _ h3 _ h5 ih1 ih2 ih4 => exact .forallE ih1 ih2 h3 (fun x hx => ih4 x hx) h5
  | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 ih h5 h6
  | @const n₀ c ci₀ m m' ρ a ls R h1 h2 h3 h4 h5 h6 h7 ih5 ih7 =>
    refine @LE_Interp.const _ G env n₀ c ci₀ m m' ρ a ls
      (fun h e => @LE_Interp _ X env ρ h e ∧ @LE_Interp _ G env ρ h e) h1 h2 h3 h4 ih5 ?_
      (fun _ _ h => h.2)
    by_cases hc : c ∈ cs.map (·.1)
    · obtain ⟨⟨c', ci⟩, hp, rfl⟩ := List.mem_map.1 hc
      cases Option.some.inj (h1.symm.trans (hcon _ hp))
      have hgd := hgood hp h1 h2 h4 h5 h6 fun h e hr => ⟨h7 h e hr, ih7 h e hr⟩
      exact .ext (.inr hc) (.inl ⟨hc, hgd⟩) (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _))
        TShape.LE.rfl
    · exact Const.mapAx (Y := G) (fun h e hr => ⟨h7 h e hr, ih7 h e hr⟩) h6
        (fun hx hg => (hg.elim hx hc).elim) (fun hx _ hg => hg.elim hx hc)
        fun _ _ hx hI _ => ⟨.inl hx, .inr ⟨hc, hI⟩⟩

/-- A constant of `cs` is related wherever `X` interprets it, given `hgood`: its interpretation is
one of `GoodOverC X cs`, where it is related. -/
theorem AdeqStmt.blockC (X : AxInterp) (hMX : @ModelEnv _ X env) (hnd : (cs.map (·.1)).Nodup)
    (hcon : ∀ p ∈ cs, env.constants p.1 = some p.2)
    (hgood : ∀ {n c ci ls R m' a ρ}, (c, ci) ∈ cs → env.constants c = some ci →
      ls.length = ci.uvars → m'.HasType a → @LE_Interp _ X env ρ a (ci.type.instL ls) →
      @Const _ X env c ls R n [] m' →
      (∀ h e, R h e → @LE_Interp _ X env ρ h e ∧
        @LE_Interp _ (GoodOverC (U := U) henv hU X Γ₀ cs) env ρ h e) →
      GoodC (U := U) henv hU X Γ₀ cs c ls m')
    {c : Name} {ci : VConstant} (hci : (c, ci) ∈ cs)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ X henv hU Γ₀ Γ (.const c ls) (.const c ls') (ci.type.instL ls) := by
  have hclX : ClosedRules env := hMX.closed
  have htc : (ci.type.instL ls).ClosedN := (hclX.constType (hcon _ hci)).instL
  intro ρ n m a hm ha hmem
  have hmG := LE_Interp.transferB X hcon hgood hm
  have ha' : @LE_Interp _ X env .nil a.T (ci.type.instL ls) :=
    (@LE_Interp.closed_iff _ X env hclX _ htc _ _ _).1 ha
  have rfl' := List.forall₂_refl' (r := (· ≈ ·)) (l := ls) fun _ => (rfl : VLevel.Equiv _ _)
  have key := GoodC.rel X hMX hnd hci hls hmG ha' hmem
  exact LR.Adequate.of_closed (M := .const c ls) (N := .const c ls') trivial trivial
    htc (key _ _ rfl' rfl' hls hls) (key _ _ heq heq hls' hls') (key _ _ rfl' heq hls hls')

end LogRel
end Lean4Lean

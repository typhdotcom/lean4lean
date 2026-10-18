import Lean4Lean.Theory.Typing.LogRel.Good

/-!
# The constants of a recursive block, interpreted where they are related

`Good X cis c ls` are the shapes at which a constant `c` of the block `cis` is related: shapes that
interpret it in the model `X`, typed at an interpretation of its type, at which the constant is
related to itself at every equivalent levels. `GoodOver X cis` interprets the block's constants by
these shapes and every other constant as `X` does. That the shapes join needs the relation's
value-level join (`LRJoin`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv} {U : Nat}

variable (henv : env.Ordered) (hU : StepUniq env) in
/-- The relation's join at a value shape: what `Good`'s shapes joining rests on. -/
def LRJoin (Γ₀ : List VExpr) : Prop :=
  ∀ {n M N A} {m₁ m₂ a : WShape n}, m₁.Compat m₂ → m₁.HasType a → m₂.HasType a →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m₁ a →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m₂ a →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A (m₁.join m₂) a

variable (henv : env.Ordered) (hU : StepUniq env) in
/-- `M ≡ N : A` is related at every representative of `g`, at every type shape typing it that
`IA` holds of. -/
def RelAt (Γ₀ : List VExpr) (M N A : VExpr) (IA : TShape → Prop) (g : TShape) : Prop :=
  ∀ n (m a : WShape n), g ≤ m.T → m.T ≤ g → m.HasType a → IA a.T →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m a

/-- What a type's interpretations must satisfy for `RelAt` to move to smaller shapes: they are
downward closed, compatible, and join. -/
structure IAOK (IA : TShape → Prop) : Prop where
  mono : x ≤ y → IA y → IA x
  compat : IA x → IA y → x.Compat y
  join : IA x → IA y → IA (x.join y)

variable {henv : env.Ordered} {hU : StepUniq env}

/-- `RelAt` at `g` gives the relation at every smaller shape, at any type shape typing it that `IA`
holds of, given a type shape typing `g` that `IA` holds of: join the two type shapes, and move
down the value shape and then the type shape. -/
theorem RelAt.down (hIA : IAOK IA) (H : RelAt (U := U) henv hU Γ₀ M N A IA g)
    (hg₀ : g.HasType a₀) (ha₀ : IA a₀) {m a : WShape n} (hm : m.T ≤ g) (hma : m.HasType a)
    (ha : IA a.T) : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m a := by
  let N := max (max n g.1) a₀.1
  have hn : n ≤ N := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hg : g.1 ≤ N := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have h0 : a₀.1 ≤ N := Nat.le_max_right ..
  have hc : (a.lift N).Compat (a₀.2.lift N) :=
    (TShape.Compat.def (x := a.T) (y := a₀) hn h0).1 (hIA.compat ha ha₀)
  have hJ := WShape.Join.mk hc
  let j := (a.lift N).join (a₀.2.lift N)
  have hIAj : IA j.T := by
    refine hIA.mono (((WShape.Join.T hJ) _).2 ⟨?_, ?_⟩) (hIA.join ha ha₀)
    · exact (TShape.lift_eqv (a := a.T) hn).1.trans (TShape.Join.mk (hIA.compat ha ha₀)).le.1
    · exact (TShape.lift_eqv h0).1.trans (TShape.Join.mk (hIA.compat ha ha₀)).le.2
  have haT : (a.lift N).HasType .type := by
    have := (WShape.HasType.lift (n := n) (m := a) (a := .type) hn).2 hma.isType
    rwa [WShape.lift_type] at this
  have ha₀T : (a₀.2.lift N).HasType .type := by
    have := (TShape.HasType.def (x := a₀) (y := TShape.type) h0 (Nat.zero_le _)).1 hg₀.isType
    rwa [TShape.type, TShape.sort, WShape.lift_sort] at this
  have hjT : j.HasType .type := WShape.HasType.join hc haT ha₀T
  have hgj : (g.2.lift N).HasType j :=
    WShape.HasType.mono_r (r := true) hJ.le.2 hjT ((TShape.HasType.def hg h0).1 hg₀)
  have hmj : (m.lift N).HasType j :=
    WShape.HasType.mono_r (r := true) hJ.le.1 hjT ((WShape.HasType.lift hn).2 hma)
  have hle : m.lift N ≤ g.2.lift N := (TShape.LE.def (a := m.T) hn hg).1 hm
  have h1 := H N (g.2.lift N) j (TShape.lift_eqv hg).2 (TShape.lift_eqv hg).1 hgj hIAj
  have h2 := (LR _ _ _).mono_l hle hmj hgj h1
  have h3 := (LR _ _ _).mono_r_2 hJ.le.1 ((WShape.HasType.lift hn).2 hma) hjT h2
  exact (LR.DefEq.lift hn hma).1 h3

/-- `RelAt` at two compatible shapes, each typed at a type shape `IA` holds of, gives `RelAt` at
their join, by the relation's join at a type shape typing both. -/
theorem RelAt.join (hIA : IAOK IA) (hJ : LRJoin (U := U) henv hU Γ₀)
    (H1 : RelAt (U := U) henv hU Γ₀ M N A IA g₁) (H2 : RelAt (U := U) henv hU Γ₀ M N A IA g₂)
    (w1 : g₁.HasType a₁) (i1 : IA a₁) (w2 : g₂.HasType a₂) (i2 : IA a₂) (hc : g₁.Compat g₂) :
    RelAt (U := U) henv hU Γ₀ M N A IA (g₁.join g₂) := by
  intro n m a _ hm1 hma ha
  let t := (a.T.join a₁).join a₂
  have c1 : a.T.Compat a₁ := hIA.compat ha i1
  have it1 : IA (a.T.join a₁) := hIA.join ha i1
  have c2 : (a.T.join a₁).Compat a₂ := hIA.compat it1 i2
  have it : IA t := hIA.join it1 i2
  have j1 := TShape.Join.mk c1; have j2 := TShape.Join.mk c2
  have la : a.T ≤ t := j1.le.1.trans j2.le.1
  have l1 : a₁ ≤ t := j1.le.2.trans j2.le.1
  have l2 : a₂ ≤ t := j2.le.2
  have tT : t.HasType .type :=
    TShape.HasType.join' j2 (TShape.HasType.join' j1 hma.T.isType w1.isType) w2.isType
  let N := max (max n t.1) (max g₁.1 g₂.1)
  have hn : n ≤ N := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have ht : t.1 ≤ N := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hg1 : g₁.1 ≤ N := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have hg2 : g₂.1 ≤ N := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  let j := t.2.lift N
  have ij : IA j.T := hIA.mono (TShape.lift_eqv ht).1 it
  have jT : j.HasType .type := by
    have := (TShape.HasType.def (x := t) (y := TShape.type) ht (Nat.zero_le _)).1 tT
    rwa [TShape.type, TShape.sort, WShape.lift_sort] at this
  have hg1j : (g₁.2.lift N).HasType j :=
    (TShape.HasType.def hg1 ht).1 (TShape.HasType.mono_r (r := true) l1 tT w1)
  have hg2j : (g₂.2.lift N).HasType j :=
    (TShape.HasType.def hg2 ht).1 (TShape.HasType.mono_r (r := true) l2 tT w2)
  have d1 := H1.down hIA w1 i1 (TShape.lift_eqv hg1).1 hg1j ij
  have d2 := H2.down hIA w2 i2 (TShape.lift_eqv hg2).1 hg2j ij
  have hcN : (g₁.2.lift N).Compat (g₂.2.lift N) := (TShape.Compat.def hg1 hg2).1 hc
  have d12 := hJ hcN hg1j hg2j d1 d2
  have hJN := WShape.Join.mk hcN
  have hle : m.T ≤ ((g₁.2.lift N).join (g₂.2.lift N)).T := by
    refine hm1.trans ((TShape.Join.mk hc _).2 ⟨?_, ?_⟩)
    · exact (TShape.lift_eqv hg1).2.trans (WShape.LE.T_iff.2 hJN.le.1)
    · exact (TShape.lift_eqv hg2).2.trans (WShape.LE.T_iff.2 hJN.le.2)
  have hleN : m.lift N ≤ (g₁.2.lift N).join (g₂.2.lift N) := by
    have := (TShape.LE.def (a := m.T) (b := ((g₁.2.lift N).join (g₂.2.lift N)).T) hn
      (Nat.le_refl _)).1 hle
    rwa [WShape.lift_self] at this
  have haj : a.lift N ≤ j := (TShape.LE.def (a := a.T) hn ht).1 la
  have hmN : (m.lift N).HasType (a.lift N) := (WShape.HasType.lift hn).2 hma
  have hmj : (m.lift N).HasType j := WShape.HasType.mono_r (r := true) haj jT hmN
  have h2 := (LR _ _ _).mono_l hleN hmj (WShape.HasType.join hcN hg1j hg2j) d12
  have h3 := (LR _ _ _).mono_r_2 haj hmN jT h2
  exact (LR.DefEq.lift hn hma).1 h3

theorem IAOK.interp (X : AxInterp) (hM : @ModelEnv _ X env) (T : VExpr) :
    IAOK fun t => @LE_Interp _ X env .nil t T :=
  ⟨fun h H => H.mono h, fun h1 h2 => h1.compat hM h2, fun h1 h2 => h1.join' hM h2⟩

variable (henv : env.Ordered) (hU : StepUniq env) in
/-- The shapes at which the constant `c` of the block `cis` is related: shapes interpreting it in
`X`, typed at an interpretation of its type, at which it is related to itself at every
equivalent well-formed levels, at every type shape typing them that interprets its type. -/
def Good (X : AxInterp) (Γ₀ : List VExpr) (cis : List VDefVal) (c : Name) (ls : List VLevel)
    (g : TShape) : Prop :=
  ∃ ci ∈ cis, ci.name = c ∧ ls.length = ci.uvars ∧
    @LE_Interp _ X env .nil g (.const c ls) ∧
    (∃ a₀, g.HasType a₀ ∧ @LE_Interp _ X env .nil a₀ (ci.type.instL ls)) ∧
    ∀ ls₁ ls₂ ls₃, List.Forall₂ (· ≈ ·) ls ls₁ → List.Forall₂ (· ≈ ·) ls ls₂ →
      List.Forall₂ (· ≈ ·) ls ls₃ → (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      (∀ l ∈ ls₃, l.WF U) →
      RelAt (U := U) henv hU Γ₀ (.const c ls₁) (.const c ls₂) (ci.type.instL ls₃)
        (fun t => @LE_Interp _ X env .nil t (ci.type.instL ls₃)) g

set_option warn.classDefReducibility false in
variable (henv : env.Ordered) (hU : StepUniq env) in
/-- The model interpreting the block `cis`'s constants by the shapes they are related at, and every
other constant as `X` does. -/
def GoodOver (X : AxInterp) (Γ₀ : List VExpr) (cis : List VDefVal) : AxInterp where
  dom c := X.dom c ∨ c ∈ cis.map (·.name)
  I c ls g := (c ∈ cis.map (·.name) ∧ Good (U := U) henv hU X Γ₀ cis c ls g) ∨
    (c ∉ cis.map (·.name) ∧ X.I c ls g)

omit [ShapeEnv] in
theorem List.eq_of_name {cis : List VDefVal} (hnd : (cis.map (·.name)).Nodup)
    (h1 : ci ∈ cis) (h2 : ci' ∈ cis) (e : ci.name = ci'.name) : ci = ci' := by
  induction cis with
  | nil => cases h1
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.mem_cons] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2]
    · exact (hnd.1 _ h2 (by subst h1; exact e.symm)).elim
    · exact (hnd.1 _ h1 (by subst h2; exact e)).elim
    · exact ih hnd.2 h1 h2

/-- `Good`'s shapes join, given the relation's join. -/
theorem Good.join (X : AxInterp) (hM : @ModelEnv _ X env) (hJ : LRJoin (U := U) henv hU Γ₀)
    (hnd : (cis.map (·.name)).Nodup)
    (H1 : Good (U := U) henv hU X Γ₀ cis c ls₁ g₁) (H2 : Good (U := U) henv hU X Γ₀ cis c ls₂ g₂)
    (hl : List.Forall₂ (· ≈ ·) ls₁ ls₂) :
    g₁.Compat g₂ ∧ Good (U := U) henv hU X Γ₀ cis c ls₁ (g₁.join g₂) := by
  obtain ⟨ci, hci, rfl, hlen, i1, ⟨a₁, w1, ia1⟩, R1⟩ := H1
  obtain ⟨ci', hci', e, -, i2, ⟨a₂, w2, ia2⟩, R2⟩ := H2
  cases List.eq_of_name hnd hci hci' e.symm
  have hl' := levels_equiv_symm hl
  have i2' : @LE_Interp _ X env .nil g₂ (.const ci.name ls₁) := i2.levels (.const hl')
  have ia2' : @LE_Interp _ X env .nil a₂ (ci.type.instL ls₁) := ia2.levels (.instL hl' _)
  have hc := i1.compat hM i2'
  have hca := ia1.compat hM ia2'
  have ja := TShape.Join.mk hca
  have aT : (a₁.join a₂).HasType .type := TShape.HasType.join' ja w1.isType w2.isType
  refine ⟨hc, ci, hci, rfl, hlen, i1.join' hM i2', ⟨a₁.join a₂,
    TShape.HasType.join' (TShape.Join.mk hc) (TShape.HasType.mono_r (r := true) ja.le.1 aT w1)
      (TShape.HasType.mono_r (r := true) ja.le.2 aT w2), ia1.join' hM ia2'⟩, ?_⟩
  intro k₁ k₂ k₃ e1 e2 e3 wf1 wf2 wf3
  have IA := IAOK.interp X hM (ci.type.instL k₃)
  refine RelAt.join IA hJ (R1 k₁ k₂ k₃ e1 e2 e3 wf1 wf2 wf3)
    (R2 k₁ k₂ k₃ (levels_equiv_trans hl' e1) (levels_equiv_trans hl' e2)
      (levels_equiv_trans hl' e3) wf1 wf2 wf3) w1 (ia1.levels (.instL e3 _)) w2
    (ia2.levels (.instL (levels_equiv_trans hl' e3) _)) hc

/-- `GoodOver`'s shapes join, given `X`'s and the relation's join. -/
theorem GoodOver.axOK (X : AxInterp) (hX : @AxOK _ X) (hM : @ModelEnv _ X env)
    (hJ : LRJoin (U := U) henv hU Γ₀) (hnd : (cis.map (·.name)).Nodup) :
    @AxOK _ (GoodOver (U := U) henv hU X Γ₀ cis) := by
  refine @AxOK.mk _ (GoodOver (U := U) henv hU X Γ₀ cis) fun {c ls₁ ls₂ m₁ m₂} h1 h2 hl => ?_
  rcases h1 with ⟨hc, h1⟩ | ⟨hc, h1⟩ <;> rcases h2 with ⟨hc', h2⟩ | ⟨hc', h2⟩
  · have := Good.join X hM hJ hnd h1 h2 hl; exact ⟨this.1, .inl ⟨hc, this.2⟩⟩
  · exact (hc' hc).elim
  · exact (hc hc').elim
  · have := hX.join h1 h2 hl; exact ⟨this.1, .inr ⟨hc, this.2⟩⟩

/-- A derivation between closed terms is adequate where the relation holds of them. -/
theorem LR.Adequate.of_closed [AxInterp] {M N A : VExpr} (hM : M.ClosedN) (hN : N.ClosedN)
    (hA : A.ClosedN) {m a : WShape n}
    (h1 : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M M A m a)
    (h2 : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq N N A m a)
    (h3 : (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N A m a) :
    LR.Adequate (U := U) henv hU Γ₀ Γ ρ M N A m a := by
  refine ⟨fun σ σ' _ => ?_, fun σ _ => ?_⟩ <;>
    simp only [VExpr.ClosedN.subst_eq hM .zero, VExpr.ClosedN.subst_eq hN .zero,
      VExpr.ClosedN.subst_eq hA .zero]
  · exact ⟨h1, h2⟩
  · exact h3

/-- A block constant interpreted in `GoodOver X cis` is related, at any type shape interpreting its
type in `X`: it is interpreted only below its shapes in `Good`. -/
theorem Good.rel (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOver (U := U) henv hU X Γ₀ cis) env)
    (hnd : (cis.map (·.name)).Nodup)
    {ci : VDefVal} (hci : ci ∈ cis) (hdf : env.defeqs ci.toDefEq) (hls : ∀ l ∈ ls, l.WF U)
    {m a : WShape n}
    (hm : @LE_Interp _ (GoodOver (U := U) henv hU X Γ₀ cis) env ρ m.T (.const ci.name ls))
    (ha : @LE_Interp _ X env .nil a.T (ci.type.instL ls)) (hmem : m.HasType a)
    (ls₁ ls₂ : List VLevel) (e1 : List.Forall₂ (· ≈ ·) ls ls₁) (e2 : List.Forall₂ (· ≈ ·) ls ls₂)
    (w1 : ∀ l ∈ ls₁, l.WF U) (w2 : ∀ l ∈ ls₂, l.WF U) :
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq (.const ci.name ls₁) (.const ci.name ls₂)
      (ci.type.instL ls) m a := by
  letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
  have H : m.T ≤ TShape.bot ∨ ∃ ls₀ g, List.Forall₂ (· ≈ ·) ls₀ ls ∧ m.T ≤ g ∧
      Good (U := U) henv hU X Γ₀ cis ci.name ls₀ g := by
    cases hm with
    | bot => exact .inl TShape.bot_eqv.1
    | const _ _ h3 _ _ h6 _ =>
      cases h6 with
      | bot => exact .inl (h3.trans TShape.bot_eqv.1)
      | lam he hle =>
        exact .inl (h3.trans (Const.lam_le_bot hMG.roles he hle (r := .delta ci.toDefEq)
          (.delta hdf rfl)))
      | ext _ a3 a4 a5 =>
        rcases a3 with ⟨-, a3⟩ | ⟨a3, -⟩
        · exact .inr ⟨_, _, a4, h3.trans a5, a3⟩
        · exact (a3 (List.mem_map_of_mem hci)).elim
      | delta a0 => exact (a0 (.inr (List.mem_map_of_mem hci))).elim
      | indTy a1 a2 => cases hMG.roles (.delta hdf rfl) (.indTy a1 a2)
      | ctor a1 a2 a3 a4 => cases hMG.roles (.delta hdf rfl) (.ctor a1 a2 a3 a4)
      | quotTy _ _ _ a4 => cases a4
  rcases H with h | ⟨ls₀, g, e0, hmg, ⟨ci', hci', en, -, -, ⟨a₀, w0, ia0⟩, R⟩⟩
  · cases show m = .bot from TShape.le_bot.1 (h.trans TShape.bot_le)
    exact (LR _ _ _).bot hmem.isType
  · cases List.eq_of_name hnd hci' hci en
    exact (R ls₁ ls₂ ls (levels_equiv_trans e0 e1) (levels_equiv_trans e0 e2) e0 w1 w2 hls).down
      (IAOK.interp X hMX _) w0 (@LE_Interp.levels _ X env _ _ _ _ ia0 (.instL e0 _)) hmg hmem ha

/-- In `GoodOver X cis`, a constant of the block is related wherever it is interpreted. Its type is
interpreted alike in both models. -/
theorem AdeqStmt.good (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOver (U := U) henv hU X Γ₀ cis) env)
    (hnd : (cis.map (·.name)).Nodup) {Q : Name → Prop}
    (hsame : SameOn env (GoodOver (U := U) henv hU X Γ₀ cis) X Q)
    {ci : VDefVal} (hci : ci ∈ cis) (hdf : env.defeqs ci.toDefEq) (hQ : ci.type.ConstsSat Q)
    (hcon : env.constants ci.name = some ci.toVConstant)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU Γ₀ Γ
      (.const ci.name ls) (.const ci.name ls') (ci.type.instL ls) := by
  have hclX : ClosedRules env := hMX.closed
  have htc : (ci.type.instL ls).ClosedN := (hclX.constType hcon).instL
  letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
  intro ρ n m a hm ha hmem
  have ha' : @LE_Interp _ X env .nil a.T (ci.type.instL ls) :=
    (@LE_Interp.closed_iff _ X env hclX _ htc _ _ _).1 (LE_Interp.sameOn hsame ha hQ.instL)
  have rfl' := List.forall₂_refl' (r := (· ≈ ·)) (l := ls) fun _ => (rfl : VLevel.Equiv _ _)
  have key := Good.rel X hMX hMG hnd hci hdf hls hm ha' hmem
  exact LR.Adequate.of_closed (M := .const ci.name ls) (N := .const ci.name ls') trivial trivial
    htc (key _ _ rfl' rfl' hls hls)
    (key _ _ heq heq hls' hls') (key _ _ rfl' heq hls hls')

/-- A constant's interpretation in one model is one in another that agrees with it where the
derivation reads the models: at a definition's unfolding or at given shapes, when no argument has
been taken; a computing case of a constant `Y` interprets by given shapes is one of a definition. -/
theorem LE_Interp.Const.mapAx {X Y : AxInterp} {R R' : TShape → VExpr → Prop}
    (hR : ∀ h e, R h e → R' h e) (H : @Const _ X env c ls R n rargs m)
    (hC : ¬X.dom c → Y.dom c → ∀ {r k}, ConstArity env c r k → ∃ df, r = .delta df) :
    (¬X.dom c → rargs = [] → ¬Y.dom c) →
    (∀ ls₀ m', X.dom c → X.I c ls₀ m' → rargs = [] → Y.dom c ∧ Y.I c ls₀ m') →
    @Const _ Y env c ls R' n rargs m := by
  have hY {r k} (g : ¬X.dom c) (A : ConstArity env c r k) (hr : ∀ df, r ≠ .delta df) :
      ¬Y.dom c := fun hy => let ⟨df, e⟩ := hC g hy A; hr df e
  induction H with
  | bot => intros; exact .bot
  | lam _ h2 ih => intros; exact .lam (fun x y h => ih x y h (fun _ => nofun) fun _ _ _ _ => nofun) h2
  | ext h0 h3 h4 h5 =>
    intro _ he; have := he _ _ h0 h3 rfl; exact .ext this.1 this.2 h4 h5
  | delta h0 h1 h2 h3 h4 h5 => intro hd _; exact .delta (hd h0 rfl) h1 h2 h3 (hR _ _ h4) h5
  | indTy h1 h2 h3 h4 h5 h6 g =>
    intros
    refine .indTy h1 h2 h3 h4 (fun i c' cty a1 a2 => ?_) h6 (hY g (.indTy h1 h2) nofun)
    obtain ⟨h, b1, b2⟩ := h5 i c' cty a1 a2
    exact ⟨h, hR _ _ b1, b2⟩
  | ctor h1 h2 h3 h4 h5 h6 h7 g =>
    intros; exact .ctor h1 h2 h3 h4 h5 h6 h7 (hY g (.ctor h1 h2 h3 h4) nofun)
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 g =>
    intros; exact .iota h1 h2 h3 h4 h5 h6 h7 (hR _ _ h8) h9 h10 (hY g (.recursor h1 h2 h4) nofun)
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 g =>
    intros
    exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 (hR _ _ h9) h10 (hY g (.recursor h1 h2 h4) nofun)
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 g =>
    intros; exact .quotTy h1 h2 h3 h4 h5 (hR _ _ h6) h7 h8 (hY g (.quotTy h1 h2) nofun)
  | quotMk h1 h2 h3 h4 h5 g => intros; exact .quotMk h1 h2 h3 h4 h5 (hY g (.quotMk h1 h2) nofun)
  | quot h1 h2 h3 h4 h5 h6 g =>
    intros; exact .quot h1 h2 h3 h4 h5 h6 (hY g (.quotLift h1 h2) nofun)
  | quotK h1 h2 h3 h4 h5 g => intros; exact .quotK h1 h2 h3 h4 h5 (hY g (.quotLift h1 h2) nofun)

/-- Every interpretation in `X` is one in `GoodOver X cis`, given each block constant's value
adequate in `GoodOver X cis`: an unfolding of a block constant is related, by its value's
adequacy, so its shape is one of `Good`'s. -/
theorem LE_Interp.transfer (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hdom : ∀ ci ∈ cis, ¬X.dom ci.name) {Q : Name → Prop}
    (hsame : SameOn env X (GoodOver (U := U) henv hU X Γ₀ cis) Q)
    (hci : ∀ ci ∈ cis, env.defeqs ci.toDefEq ∧
      env.constants ci.name = some ci.toVConstant ∧ ci.type.ConstsSat Q)
    (hbody : ∀ ci ∈ cis, ∀ ls₁ ls₂ ls₃, List.Forall₂ (· ≈ ·) ls₁ ls₂ →
      List.Forall₂ (· ≈ ·) ls₁ ls₃ → (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      (∀ l ∈ ls₃, l.WF U) → ls₁.length = ci.uvars →
      @AdeqStmt env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU Γ₀ Γ₀
        (ci.value.instL ls₁) (ci.value.instL ls₂) (ci.type.instL ls₃))
    (H : @LE_Interp _ X env ρ m e) :
    @LE_Interp _ (GoodOver (U := U) henv hU X Γ₀ cis) env ρ m e := by
  have hclX : ClosedRules env := hMX.closed
  have hroles : ConstRoles env := hMX.roles
  have hsu : StepUniq env := hMX.stepUniq
  letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
  induction H with
  | bot => exact .bot
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | app _ _ h3 ih1 ih2 => exact .app ih1 ih2 h3
  | lam _ h2 _ h4 ih1 ih3 => exact .lam ih1 h2 (fun x hx => ih3 x hx) h4
  | forallE _ _ h3 _ h5 ih1 ih2 ih4 => exact .forallE ih1 ih2 h3 (fun x hx => ih4 x hx) h5
  | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 ih h5 h6
  | @const n₀ c ci₀ m m' ρ a ls R h1 h2 h3 h4 h5 h6 h7 ih5 ih7 =>
    refine @LE_Interp.const _ G env n₀ c ci₀ m m' ρ a ls _ h1 h2 h3 h4 ih5 ?_ (fun _ _ h => h)
    by_cases hc : c ∉ cis.map (·.name)
    · exact Const.mapAx (Y := G) ih7 h6 (fun hx hg => (hg.elim hx hc).elim)
        (fun hx _ hg => hg.elim hx hc) fun _ _ hx hI _ => ⟨.inl hx, .inr ⟨hc, hI⟩⟩
    rw [Classical.not_not] at hc
    obtain ⟨ci, hci', rfl⟩ := List.mem_map.1 hc
    obtain ⟨hdf, hcon, hQ⟩ := hci ci hci'
    cases Option.some.inj (h1.symm.trans hcon)
    have h6' := h6
    cases h6 with
    | bot => exact .bot
    | lam he hle =>
      exact .lam (fun x y h => Const.mapAx (Y := G) ih7 (he x y h)
        (fun _ _ _ _ A => ⟨_, hroles A (.delta hdf rfl)⟩) (fun _ => nofun)
        fun _ _ _ _ => nofun) hle
    | ext a0 => exact (hdom ci hci' a0).elim
    | indTy a1 a2 => cases hroles (.delta hdf rfl) (.indTy a1 a2)
    | ctor a1 a2 a3 a4 => cases hroles (.delta hdf rfl) (.ctor a1 a2 a3 a4)
    | quotTy _ _ _ a4 => cases a4
    | delta a0 a1 a2 a3 a4 a5 =>
      cases hsu.delta hdf a1 rfl a2
      have hv : (ci.value.instL ls).ClosedN := (hclX.defeq hdf).instL
      refine .ext (.inr hc) (.inl ⟨hc, ci, hci', rfl, a3, ?_, ⟨_, h4,
        (@LE_Interp.closed_iff _ X env hclX _ (hclX.constType h1).instL _ _ _).1 h5⟩, ?_⟩)
        (List.forall₂_refl' fun _ => (rfl : VLevel.Equiv _ _)) TShape.LE.rfl
      · exact (@LE_Interp.closed_iff _ X env hclX (.const ci.name ls) trivial _ _ _).1 (@LE_Interp.const _ X env _ _ _ _ _ _ _ _ _ h1 h2 TShape.LE.rfl
            h4 h5 h6' h7)
      intro ls₁ ls₂ ls₃ e1 e2 e3 w1 w2 w3 n' m'' a'' _ hle hma ia
      have l1 := levels_equiv_symm e1
      have hv1 : LE_Interp env .nil m''.T (ci.value.instL ls₁) :=
        (LE_Interp.closed_iff hclX (hclX.defeq hdf).instL).1
          (((ih7 _ _ a4).mono (hle.trans a5)).levels (.instL e1 _))
      have hty : LE_Interp env .nil a''.T (ci.type.instL ls₃) := LE_Interp.sameOn hsame ia hQ.instL
      have ad := (hbody ci hci' ls₁ ls₂ ls₃ (levels_equiv_trans l1 e2) (levels_equiv_trans l1 e3)
        w1 w2 w3 ((Lean4Lean.List.Forall₂.length_eq e1).symm.trans a3) hv1 hty hma).2 .id
      have hv1c : (ci.value.instL ls₁).ClosedN := (hclX.defeq hdf).instL
      have hv2c : (ci.value.instL ls₂).ClosedN := (hclX.defeq hdf).instL
      have htc : (ci.type.instL ls₃).ClosedN := (hclX.constType h1).instL
      rw [VExpr.ClosedN.subst_eq hv1c .zero, VExpr.ClosedN.subst_eq hv2c .zero,
        VExpr.ClosedN.subst_eq htc .zero] at ad
      have hs1 : TRed env U Γ₀ (.const ci.name ls₁) (ci.value.instL ls₁) (ci.type.instL ls₃) :=
        TRed.delta_at henv hdf hcon w1 w3 (levels_equiv_trans l1 e3)
          ((Lean4Lean.List.Forall₂.length_eq e1).symm.trans a3)
      have hs2 : TRed env U Γ₀ (.const ci.name ls₂) (ci.value.instL ls₂) (ci.type.instL ls₃) :=
        TRed.delta_at henv hdf hcon w2 w3 (levels_equiv_trans (levels_equiv_symm e2) e3)
          ((Lean4Lean.List.Forall₂.length_eq e2).symm.trans a3)
      exact ((LR _ _ _).whr hs1 hs2).2 ad

variable (henv : env.Ordered) (hU : StepUniq env) in
/-- What the relation at a recursive block's constants in `X` rests on: the block's values are
adequate in `GoodOver X cis`, the block's types are read alike by both models, and the block's
constants and rules are the environment's. -/
structure MutualOK (X : AxInterp) (Γ₀ : List VExpr) (cis : List VDefVal) (Q : Name → Prop) :
    Prop where
  modelX : @ModelEnv _ X env
  modelG : @ModelEnv _ (GoodOver (U := U) henv hU X Γ₀ cis) env
  nodup : (cis.map (·.name)).Nodup
  dom : ∀ ci ∈ cis, ¬X.dom ci.name
  same : SameOn env X (GoodOver (U := U) henv hU X Γ₀ cis) Q
  decl : ∀ ci ∈ cis, env.defeqs ci.toDefEq ∧
    env.constants ci.name = some ci.toVConstant ∧ ci.type.ConstsSat Q
  body : ∀ ci ∈ cis, ∀ ls₁ ls₂ ls₃, List.Forall₂ (· ≈ ·) ls₁ ls₂ →
    List.Forall₂ (· ≈ ·) ls₁ ls₃ → (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
    (∀ l ∈ ls₃, l.WF U) → ls₁.length = ci.uvars →
    @AdeqStmt env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU Γ₀ Γ₀
      (ci.value.instL ls₁) (ci.value.instL ls₂) (ci.type.instL ls₃)

/-- A recursive block's constant is related wherever `X` interprets it: the interpretation is one
of `GoodOver X cis`, where the constant is related. -/
theorem AdeqStmt.mutual (X : AxInterp) (H : MutualOK (U := U) henv hU X Γ₀ cis Q)
    {ci : VDefVal} (hci : ci ∈ cis)
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    @AdeqStmt env U _ X henv hU Γ₀ Γ (.const ci.name ls) (.const ci.name ls') (ci.type.instL ls) := by
  have hclX : ClosedRules env := H.modelX.closed
  obtain ⟨hdf, hcon, -⟩ := H.decl ci hci
  have htc : (ci.type.instL ls).ClosedN := (hclX.constType hcon).instL
  intro ρ n m a hm ha hmem
  have hmG := LE_Interp.transfer X H.modelX H.dom H.same H.decl H.body hm
  have ha' : @LE_Interp _ X env .nil a.T (ci.type.instL ls) :=
    (@LE_Interp.closed_iff _ X env hclX _ htc _ _ _).1 ha
  have rfl' := List.forall₂_refl' (r := (· ≈ ·)) (l := ls) fun _ => (rfl : VLevel.Equiv _ _)
  have key := Good.rel X H.modelX H.modelG H.nodup hci hdf hls hmG ha' hmem
  exact LR.Adequate.of_closed (M := .const ci.name ls) (N := .const ci.name ls') trivial trivial
    htc (key _ _ rfl' rfl' hls hls) (key _ _ heq heq hls' hls') (key _ _ rfl' heq hls hls')

/-- A recursive block's rule is related wherever `X` interprets its constant: its value is, in
`GoodOver X cis`, at the shapes `X` interprets it at. -/
theorem AdeqStmt.mutual_r (X : AxInterp) (H : MutualOK (U := U) henv hU X Γ₀ cis Q)
    {ci : VDefVal} (hci : ci ∈ cis) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = ci.uvars) :
    @AdeqStmt env U _ X henv hU Γ₀ Γ (.const ci.name ls) (ci.value.instL ls) (ci.type.instL ls) := by
  have hclX : ClosedRules env := H.modelX.closed
  have hM := H.modelX
  obtain ⟨hdf, hcon, hQ⟩ := H.decl ci hci
  have htc : (ci.type.instL ls).ClosedN := (hclX.constType hcon).instL
  have hvc : (ci.value.instL ls).ClosedN := (hclX.defeq hdf).instL
  intro ρ n m a hm ha hmem
  have hv := hm.const_delta hM (H.dom ci hci) hdf
  have haX := (LE_Interp.closed_iff hclX htc (ρ' := .nil)).1 ha
  have hvX := LE_Interp.transfer X H.modelX H.dom H.same H.decl H.body hv
  obtain ⟨hvG, haG⟩ :
      @LE_Interp _ (GoodOver (U := U) henv hU X Γ₀ cis) env .nil m.T (ci.value.instL ls) ∧
      @LE_Interp _ (GoodOver (U := U) henv hU X Γ₀ cis) env .nil a.T (ci.type.instL ls) := by
    letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
    exact ⟨(LE_Interp.closed_iff hclX hvc).1 hvX, LE_Interp.sameOn H.same haX hQ.instL⟩
  have hid : @LR.SubstWF env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU Γ₀ .id .id Γ₀ .nil := by
    letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
    exact .id
  have rfl' := List.forall₂_refl' (r := (· ≈ ·)) (l := ls) fun _ => (rfl : VLevel.Equiv _ _)
  have d := (H.body ci hci ls ls ls rfl' rfl' hls hls hls hlen hvG haG hmem).2 hid
  rw [VExpr.ClosedN.subst_eq hvc .zero, VExpr.ClosedN.subst_eq htc .zero] at d
  have hs : TRed env U Γ₀ (.const ci.name ls) (ci.value.instL ls) (ci.type.instL ls) :=
    TRed.delta (df := ci.toDefEq) hdf rfl hls hlen
  exact LR.Adequate.of_closed (M := .const ci.name ls) trivial hvc htc
    (((LR _ _ _).whr hs hs).2 d) d (((LR _ _ _).whr hs (.refl hs.2.hasType.2)).2 d)

omit [ShapeEnv] in
theorem _root_.Lean4Lean.VEnv.addConsts_constants_cases : ∀ {env env' : VEnv} {cis : List VDefVal},
    env.addConsts cis = some env' → env'.constants c = some x →
    env.constants c = some x ∨ ∃ ci ∈ cis, ci.name = c ∧ x = ci.toVConstant
  | _, _, [], h, hc => by cases h; exact .inl hc
  | _, _, ci :: _, h, hc => by
    simp only [VEnv.addConsts, List.foldlM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    rcases VEnv.addConsts_constants_cases h2 hc with hc | ⟨ci', hci', e1, e2⟩
    · rw [VEnv.addConst_constants_eq h1] at hc
      simp only at hc
      split at hc
      · cases hc; exact .inr ⟨ci, .head _, ‹_›, rfl⟩
      · exact .inl hc
    · exact .inr ⟨ci', .tail _ hci', e1, e2⟩

/-- Adding a recursive block keeps adequacy's environment cases in `X`: its constants and rules
are related by `MutualOK`. -/
theorem AdequacyHyps.addMutual (X : AxInterp) (H : MutualOK (U := U) henv hU X Γ₀ cis Q)
    {E E' : VEnv} (hX : @AdequacyHyps env U _ X henv hU E Γ₀) (h1 : E.addConsts cis = some E') :
    @AdequacyHyps env U _ X henv hU (E'.addDefEqs cis) Γ₀ := by
  have hinds : (E'.addDefEqs cis).inducts = E.inducts :=
    VEnv.addDefEqs_inducts.trans (VEnv.addConsts_inducts h1)
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun {Γ df ls u} hΓ hd hls hlen hu h6 h7 h8 h9 h10 hL hR => ?_,
    fun hΓ h => hX.projDF hΓ (hinds ▸ h), fun hΓ h => hX.projIota hΓ (hinds ▸ h),
    fun hΓ h => hX.projEta hΓ (hinds ▸ h)⟩
  · rw [VEnv.addDefEqs_constants] at hc
    rcases VEnv.addConsts_constants_cases h1 hc with hc | ⟨ci, hci, rfl, rfl⟩
    · exact hX.const hΓ hc hls hls' hlen heq hu h7 h8 hA
    · exact AdeqStmt.mutual X H hci hls hls' heq
  · rcases VEnv.addDefEqs_defeqs hd with ⟨ci, hci, rfl⟩ | hd
    · have hlen' : ls.length = ci.uvars := hlen
      have e : ci.toDefEq.lhs.instL ls = .const ci.name ls :=
        congrArg _ (VLevel.inst_map_id (n := ci.uvars) hlen')
      show @AdeqStmt env U _ X henv hU Γ₀ Γ (ci.toDefEq.lhs.instL ls) (ci.value.instL ls)
        (ci.type.instL ls)
      rw [e]; exact AdeqStmt.mutual_r X H hci hls hlen'
    · rw [VEnv.addConsts_defeqs h1] at hd
      exact hX.extra hΓ hd hls hlen hu h6 h7 h8 h9 h10 hL hR

/-- In `GoodOver X cis`, adding the block's constants without their rules keeps adequacy's
environment cases: the constants are related by `Good`. -/
theorem AdequacyHyps.addGood (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOver (U := U) henv hU X Γ₀ cis) env)
    (hnd : (cis.map (·.name)).Nodup)
    (hsame : SameOn env (GoodOver (U := U) henv hU X Γ₀ cis) X Q)
    (hdecl : ∀ ci ∈ cis, env.defeqs ci.toDefEq ∧
      env.constants ci.name = some ci.toVConstant ∧ ci.type.ConstsSat Q)
    {E E' : VEnv} (hG : @AdequacyHyps env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU E Γ₀)
    (h1 : E.addConsts cis = some E') :
    @AdequacyHyps env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU E' Γ₀ := by
  letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
  have hinds : E'.inducts = E.inducts := VEnv.addConsts_inducts h1
  refine ⟨fun {Γ c ci' ls ls' u} hΓ hc hls hls' hlen heq hu h7 h8 hA => ?_,
    fun hΓ hd => hG.extra hΓ (VEnv.addConsts_defeqs h1 ▸ hd),
    fun hΓ h => hG.projDF hΓ (hinds ▸ h), fun hΓ h => hG.projIota hΓ (hinds ▸ h),
    fun hΓ h => hG.projEta hΓ (hinds ▸ h)⟩
  rcases VEnv.addConsts_constants_cases h1 hc with hc | ⟨ci, hci, rfl, rfl⟩
  · exact hG.const hΓ hc hls hls' hlen heq hu h7 h8 hA
  · obtain ⟨hdf, hcon, hQ⟩ := hdecl ci hci
    exact AdeqStmt.good X hMX hMG hnd hsame hci hdf hQ hcon hls hls' heq

omit [ShapeEnv] in
/-- A block value's typing, at equivalent levels, as a strong derivation in any context. -/
theorem VDefVal.body_strong {E : VEnv} (hEo : E.Ordered) {ci : VDefVal}
    (hT : ci.toVConstant.WF E) (hv : ci.WF E)
    (e2 : List.Forall₂ (· ≈ ·) ls₁ ls₂) (e3 : List.Forall₂ (· ≈ ·) ls₁ ls₃)
    (w1 : ∀ l ∈ ls₁, l.WF U) (w2 : ∀ l ∈ ls₂, l.WF U) (w3 : ∀ l ∈ ls₃, l.WF U) :
    E.IsDefEqStrong U Γ (ci.value.instL ls₁) (ci.value.instL ls₂) (ci.type.instL ls₃) := by
  obtain ⟨u, hu⟩ := hT
  have h1 : E.IsDefEq U [] (ci.value.instL ls₁) (ci.value.instL ls₂) (ci.type.instL ls₁) :=
    VEnv.IsDefEq.instL_r hEo (U' := ci.uvars) (Γ := []) trivial w1 w2 e2 hv
  have h2 : E.IsDefEq U [] (ci.type.instL ls₁) (ci.type.instL ls₃) ((VExpr.sort u).instL ls₁) :=
    VEnv.IsDefEq.instL_r hEo (U' := ci.uvars) (Γ := []) trivial w1 w3 e3 hu
  exact ((h2.defeqDF h1).strong hEo (Γ := []) trivial).weak0 hEo

/-- `MutualOK` at a recursive block, from the model interpreting it by its related shapes being
sound and adequate for the derivations of the environment with the block's constants as axioms. -/
theorem MutualOK.of (X : AxInterp) (hMX : @ModelEnv _ X env)
    (hMG : @ModelEnv _ (GoodOver (U := U) henv hU X Γ₀ cis) env)
    (hnd : (cis.map (·.name)).Nodup) (hdom : ∀ ci ∈ cis, ¬X.dom ci.name)
    (hsame : SameOn env X (GoodOver (U := U) henv hU X Γ₀ cis) Q)
    (hdecl : ∀ ci ∈ cis, env.defeqs ci.toDefEq ∧
      env.constants ci.name = some ci.toVConstant ∧ ci.type.ConstsSat Q)
    {E' : VEnv} (hEo : E'.Ordered) (hle : E' ≤ env)
    (hwfT : ∀ ci ∈ cis, ci.toVConstant.WF E') (hwfV : ∀ ci ∈ cis, ci.WF E')
    (hS : ∀ {Γ M N A}, E'.IsDefEqStrong U Γ M N A →
      @StrongSoundEq _ (GoodOver (U := U) henv hU X Γ₀ cis) env U Γ M N A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hG : @AdequacyHyps env U _ (GoodOver (U := U) henv hU X Γ₀ cis) henv hU E' Γ₀) :
    MutualOK (U := U) henv hU X Γ₀ cis Q := by
  refine ⟨hMX, hMG, hnd, hdom, hsame, hdecl, fun ci hci ls₁ ls₂ ls₃ e2 e3 w1 w2 w3 _ => ?_⟩
  letI G : AxInterp := GoodOver (U := U) henv hU X Γ₀ cis
  intro ρ n m a hm ha hmem
  exact LR.adequacy_of hMG hle hS hΓ₀ hG
    (VDefVal.body_strong hEo (hwfT ci hci) (hwfV ci hci) e2 e3 w1 w2 w3) hΓ₀ hm ha hmem

end LogRel
end Lean4Lean

import Lean4Lean.Theory.Typing.LogRel.AdeqQuotRule
import Lean4Lean.Theory.Typing.LogRel.BlockGood

/-!
# A constant related along the lambda nodes of its interpretation

A constant's interpretation (`LE_Interp.Const`) is a tree of lambda nodes, one per argument, over
what it computes to once applied to as many arguments as its arity. The constant applied to
related arguments is related at every node, given that it is at the leaves: at a lambda node the
application to a related argument at shape `p` is related at the node's value at `p`, which is
the leaf's (or the next node's) for the argument shapes extended by `p`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}

omit [ShapeEnv] [AxInterp] in
/-- A closed term applied to the first `k+1` variables of a telescope, under a substitution that
gives the last one `x`: the term applied to the first `k`, applied to `x`. -/
theorem appN_bvars_cons {F : VExpr} (k : Nat) (σ : VExpr.Subst) (x : VExpr) :
    F.appN ((VExpr.bvars (k+1) 0).map (·.subst (σ.cons x))) =
      .app (F.appN ((VExpr.bvars k 0).map (·.subst σ))) x := by
  rw [VExpr.bvars_succ_right, List.map_append, VExpr.appN_append]
  simp [VExpr.appN, VExpr.bvars, Function.comp_def, VExpr.subst, VExpr.Subst.cons]


/-- The constant `F` applied to the first `k` variables, under `σ`. -/
abbrev spineAt (F : VExpr) (k : Nat) (σ : VExpr.Subst) : VExpr :=
  F.appN ((VExpr.bvars k 0).map (·.subst σ))

/-- The valuation the arguments' shapes `rargs` (last argument first) give the variables. -/
abbrev valOf {n} (rargs : List (WShape n)) : Valuation := pushAll .nil (rargs.reverse.map (·.T))

omit [AxInterp] in
theorem valOf_cons {n} (p : WShape n) (rargs : List (WShape n)) :
    valOf (p :: rargs) = (valOf rargs).push p.T := by
  simp [valOf, pushAll_concat]

/-- One lambda node of a constant's interpretation: given the relation at the node's values for
the argument shapes extended by every typed argument shape (`IB`), the terms `Sp F σ` and
`Sp F' σ'` are related at the node. The proof is `AdeqStmt.etaLam`'s, with `IB` for the body's
adequacy. -/
theorem lamNode_rel (hM : ModelEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (hAt : env.HasType U Γ A (.sort u)) (hBt : env.HasType U (A::Γ) B (.sort v))
    (hSA : StrongSoundEq env U Γ A A (.sort u)) (hSB : StrongSoundEq env U (A::Γ) B B (.sort v))
    (ihA : AdeqStmt (U := U) henv hU Γ₀ Γ A A (.sort u))
    (ihB : AdeqStmt (U := U) henv hU Γ₀ (A::Γ) B B (.sort v))
    (Sp : VExpr → VExpr.Subst → VExpr) (Ok : VExpr → Prop)
    {ρ : Valuation} {k : Nat} {g : WShapeFun k} {hg : g.NonZero}
    {a₁ : WShape k} {a₂ : WShapeFun k}
    (htm : WShape.HasTypeLam g a₁ a₂)
    (hA : LE_Interp env ρ (WShape.T (n := k+1) (.forallE a₁ a₂)) (.forallE A B))
    (IB : ∀ {G G' : VExpr} {σ₁ σ₂ : VExpr.Subst} {x x' p}, Ok G → Ok G' → p.HasType a₁ →
      LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T) →
      (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app (Sp G σ₁) x) (.app (Sp G' σ₂) x')
        (B.subst (σ₁.cons x)) (g.app p) (a₂.app p))
    {F F' : VExpr} (hF : Ok F) (hF' : Ok F')
    {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
    (LR (U := U) (Γ := Γ₀) henv hU (k+1)).DefEq (Sp F σ) (Sp F' σ') ((VExpr.forallE A B).subst σ)
      (WShape.lam g hg) (WShape.forallE a₁ a₂) := by
  have hmem : (WShape.lam g hg).HasType (WShape.forallE a₁ a₂) := by
    rw [WShape.lam_eq_lam']; exact .lam htm
  have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, _, hAt⟩
  have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
  have aty := WShape.HasTypePi.iff.1 aty
  have hA1 := (hA.forallE_inv' hM).1
  have cons := LR.Adequate.cons hM hΓ hΓ₀ hSA.left.sound ihA hAt
  have htmF := (WShape.HasTypeLam.iff.1 htm).2.2
  have TB {σ₁ σ₂ : VExpr.Subst} {x x' p} (hp : p.HasType a₁)
      (W' : LR.SubstWF (U := U) henv hU Γ₀ (σ₁.cons x) (σ₂.cons x') (A::Γ) (ρ.push p.T)) :
      (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (B.subst (σ₁.cons x)) (B.subst (σ₂.cons x'))
        (a₂.app p) := by
    have hB := (hA.forallE_inv' hM).2 p
    have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (hSB.left.sound W'.fits hB).out
    exact LR.toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
  have hdom {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
      (LR (U := U) (Γ := Γ₀) henv hU k).TyDefEq (A.subst σ) (A.subst σ') a₁ := by
    have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (hSA.left.sound W.fits hA1).out
    exact LR.toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
  have hAσ {σ σ' : VExpr.Subst} (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ' Γ ρ) :
      env.IsDefEq U Γ₀ (A.subst σ) (A.subst σ') (.sort u) :=
    hAt.substDF henv hΓ hΓ₀ (W.toSubstEq hΓ₀)
  have hΓ₀A : OnCtx (A.subst σ :: Γ₀) (env.IsType U) := ⟨hΓ₀, _, (hAσ W.left).hasType.1⟩
  have hBσ := hBt.subst henv ((W.left.toSubstEq hΓ₀).lift henv hAt) hΓ₀A
  -- the applications at the other substitution, converted to the type at `σ`
  have other {x x' p} (hp : p.HasType a₁) (hx : env.IsDefEq U Γ₀ x x' (A.subst σ))
      (hv : (LR (U := U) (Γ := Γ₀) henv hU k).DefEq x x' (A.subst σ) p a₁) :
      (LR (U := U) (Γ := Γ₀) henv hU k).DefEq (.app (Sp F' σ') x)
        (.app (Sp F' σ') x') (B.subst (σ.cons x)) (g.app p) (a₂.app p) := by
    have W2 := cons hp hA1 ((hAσ W).defeqDF hx) ((LR _ _ _).conv (.base (hAσ W)) (hdom W) hv)
      W.symm.left
    have W3 := cons hp hA1 hx.hasType.1 ((LR _ _ _).left hv) W
    have hc := (LR _ _ _).symm_ty (TB hp W3)
    have hcE : TyEq env U Γ₀ (B.subst (σ'.cons x)) (B.subst (σ.cons x)) :=
      .base (hBt.substDF henv hΓA hΓ₀ (W3.toSubstEq hΓ₀)).symm
    exact (LR _ _ _).conv hcE hc (IB hF' hF' hp W2)
  simp only [LR, LRS, LRS.DefEq.lam_forallE]
  refine .inl ⟨A.subst σ, B.subst σ.lift, u, v, .rfl,
    TyEq.refl (VEnv.IsDefEq.forallEDF (hAσ W.left).hasType.1 hBσ), (hAσ W.left).hasType.1,
    hdom W.left, hBσ, ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩,
    ⟨fun x x' p hp hx hv => ?_, fun x p hp hx hv => ?_⟩⟩ <;> simp only [inst_lift_cons]
  · have := TB hp (cons hp hA1 hx hv W.left); exact ⟨this, this⟩
  · exact TB hp (cons hp hA1 hx hv W.left)
  · exact ⟨IB hF hF hp (cons hp hA1 hx hv W.left), other hp hx hv⟩
  · exact IB hF hF' hp (cons hp hA1 hx hv W)

omit [ShapeEnv] [AxInterp] in
theorem take_succ_reverse {Bs : List VExpr} {k : Nat} (h : k < Bs.length) :
    (Bs.take (k+1)).reverse = Bs[k] :: (Bs.take k).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; simp

/-- A constant related along its interpretation: at a lambda node with `j` arguments to go, the
constant applied to `k` related arguments, whose shapes are the node's argument shapes, is related
at the node, given that it is at the nodes with all `Bs.length` arguments (`Hsat`). The telescope
`Bs` and its result `Rty` are the constant's type, `P` its types along the way. -/
theorem constSpine_core (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (P : List VExpr → VExpr → Prop)
    (hP : ∀ {Γ A B}, P Γ (.forallE A B) → P Γ A ∧ P (A::Γ) B)
    (hTy : ∀ {Γ T}, OnCtx Γ (env.IsType U) → P Γ T → ∃ u, env.HasType U Γ T (.sort u) ∧
      StrongSoundEq env U Γ T T (.sort u) ∧ AdeqStmt (U := U) henv hU Γ₀ Γ T T (.sort u))
    {c : Name} {ls : List VLevel} {R : TShape → VExpr → Prop}
    (Ok : VExpr → Prop) (hdom : ¬AxInterp.dom c) (Bs : List VExpr) (Rty : VExpr)
    (hrole : ∀ {r j}, ConstArity env c r j → j = Bs.length)
    (Hsat : ∀ {n} (rargs : List (WShape n)) {m}, Const env c ls R rargs m →
      rargs.length = Bs.length → ∀ {F F' σ σ'}, Ok F → Ok F' →
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ₀) (valOf rargs) →
      ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a → LE_Interp env (valOf rargs) a.T Rty →
      (LR (U := U) (Γ := Γ₀) henv hU (n+1)).DefEq (spineAt F Bs.length σ)
        (spineAt F' Bs.length σ') (Rty.subst σ) w a) :
    ∀ j k, k + j = Bs.length → ∀ {n} (rargs : List (WShape n)) {m},
      Const env c ls R rargs m → rargs.length = k →
      OnCtx ((Bs.take k).reverse ++ Γ₀) (env.IsType U) →
      P ((Bs.take k).reverse ++ Γ₀) (.foralls (Bs.drop k) Rty) →
      ∀ {F F' σ σ'}, Ok F → Ok F' →
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' ((Bs.take k).reverse ++ Γ₀) (valOf rargs) →
      ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a →
      LE_Interp env (valOf rargs) a.T (.foralls (Bs.drop k) Rty) →
      (LR (U := U) (Γ := Γ₀) henv hU (n+1)).DefEq (spineAt F k σ) (spineAt F' k σ')
        ((VExpr.foralls (Bs.drop k) Rty).subst σ) w a := by
  intro j
  induction j with
  | zero =>
    intro k hk n rargs m H hl _ _ F F' σ σ' hF hF' W w a hw hwa ha
    obtain rfl : k = Bs.length := by omega
    simp only [List.take_length, List.drop_length, VExpr.foralls] at W ha ⊢
    exact Hsat rargs H hl hF hF' W w a hw hwa ha
  | succ j ih =>
    intro k hk n rargs m H hl hΓk hPk F F' σ σ' hF hF' W w a hw hwa ha
    have hlt : k < Bs.length := by omega
    have hdrop : Bs.drop k = Bs[k] :: Bs.drop (k+1) := List.drop_eq_getElem_cons hlt
    rw [hdrop] at hPk ha ⊢
    obtain ⟨hPA, hPB⟩ := hP hPk
    obtain ⟨u, hAt, hSA, ihA⟩ := hTy hΓk hPA
    have hΓk' : OnCtx (Bs[k] :: ((Bs.take k).reverse ++ Γ₀)) (env.IsType U) := ⟨hΓk, _, hAt⟩
    obtain ⟨v, hBt, hSB, ihB⟩ := hTy hΓk' hPB
    have hctx : (Bs.take (k+1)).reverse ++ Γ₀ = Bs[k] :: ((Bs.take k).reverse ++ Γ₀) := by
      rw [take_succ_reverse hlt]; rfl
    rcases H.arity with hb | ⟨f, hmf, hsub⟩ | ⟨r, hr⟩ | ⟨hd, -⟩
    · have : w = .bot := by
        have := (WShape.LE.T_iff (a := w) (b := .bot)).1 (hw.trans (hb.trans TShape.bot_eqv.2))
        exact WShape.le_bot.1 this
      subst this; exact (LR _ _ _).bot hwa.isType
    · cases hwa.unfold with
      | bot => exact (LR _ _ _).bot hwa.isType
      | sort => exact (LE_Interp.not_sort_forallE ha).elim
      | forallE => exact (LE_Interp.not_sort_forallE ha).elim
      | ctor => exact (LE_Interp.not_indTy_forallE ha).elim
      | indTy => exact (LE_Interp.not_sort_forallE ha).elim
      | @lam _ g a₁ a₂ htm =>
        by_cases hg : g.NonZero
        rotate_left
        · have e : WShape.lam' g = .bot := by simp [WShape.lam', hg]
          rw [e]; exact (LR _ _ _).bot (e ▸ hwa).isType
        have hgf : g ≤ f := WShape.lam'_le_lam'.1 ((WShape.LE.T_iff).1 (hw.trans hmf))
        rw [← WShape.lam_eq_lam' (hl := hg)]
        refine lamNode_rel hM hΓk hΓ₀ hAt hBt hSA hSB ihA ihB (fun G σ => spineAt G k σ) Ok htm ha
          ?_ hF hF' W
        intro G G' σ₁ σ₂ x x' p hG hG' hp W'
        have htp := (WShape.HasTypeLam.iff.1 htm).2.2 p hp
        obtain ⟨x₀, hx₀, hmem⟩ := WShapeFun.app_eq f p
        have Hs : Const env c ls R (p :: rargs) (f.app p).T :=
          (hsub _ _ hmem).mono_l (.cons hx₀ (List.forall₂_refl' fun _ => WShape.LE.rfl))
        have IH := ih (k+1) (by omega) (p :: rargs) Hs (by simp [hl]) (hctx ▸ hΓk')
          (hctx ▸ hPB) hG hG' (by rw [valOf_cons, hctx]; exact W')
          ((g.app p).lift (n+1)) ((a₂.app p).lift (n+1)) ?_ ((WShape.HasType.lift (Nat.le_succ n)).2 htp) ?_
        · rw [← appN_bvars_cons, ← appN_bvars_cons]
          exact (LR.DefEq.lift (Nat.le_succ n) htp).1 IH
        · exact (TShape.lift_eqv (Nat.le_succ n)).1.trans
            (WShape.LE.T_iff.2 (WShapeFun.app_mono_l hgf p))
        · rw [valOf_cons]
          exact ((ha.forallE_inv' hM).2 p).mono (TShape.lift_eqv (Nat.le_succ n)).1
    · exact absurd (hrole hr) (by omega)
    · exact (hdom hd).elim

/-- The constants `c` at levels equivalent to `ls`. -/
def ConstAt (U : Nat) (c : Name) (ls : List VLevel) (F : VExpr) : Prop :=
  ∃ l, List.Forall₂ (· ≈ ·) ls l ∧ (∀ x ∈ l, x.WF U) ∧ F = .const c l

/-- What relating a constant along its interpretation needs, for the type `ci.type.instL ls₃`:
it is converted to a telescope `Bs` ending in `Rty`, as long as the constant's arity, whose types
are related (`P`), and the constant at levels equivalent to `ls` applied to all of `Bs` is related
at the interpretation's nodes at that arity (`sat`). -/
structure SpineAtB (P : List VExpr → VExpr → Prop) (Γ₀ : List VExpr) (c : Name) (ls : List VLevel)
    (R : TShape → VExpr → Prop) (T : VExpr) (Bs : List VExpr) (Rty : VExpr) : Prop where
  arity : ∀ {r j}, ConstArity env c r j → j = Bs.length
  pT : P Γ₀ (.foralls Bs Rty)
  interp : ∀ {t}, LE_Interp env .nil t T → LE_Interp env .nil t (.foralls Bs Rty)
  conv : ∀ {n} {M N : VExpr} {w b : WShape n}, LE_Interp env .nil b.T T → w.HasType b →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N (.foralls Bs Rty) w b →
    (LR (U := U) (Γ := Γ₀) henv hU n).DefEq M N T w b
  sat : ∀ {n} (rargs : List (WShape n)) {m}, Const env c ls R rargs m →
      rargs.length = Bs.length → ∀ {F F' σ σ'}, ConstAt U c ls F → ConstAt U c ls F' →
      LR.SubstWF (U := U) henv hU Γ₀ σ σ' (Bs.reverse ++ Γ₀) (valOf rargs) →
      ∀ (w a : WShape (n+1)), w.T ≤ m → w.HasType a → LE_Interp env (valOf rargs) a.T Rty →
      (LR (U := U) (Γ := Γ₀) henv hU (n+1)).DefEq (spineAt F Bs.length σ)
        (spineAt F' Bs.length σ') (Rty.subst σ) w a

variable (henv hU) in
/-- `SpineAtB` for some telescope. -/
def SpineAt (P : List VExpr → VExpr → Prop) (Γ₀ : List VExpr) (c : Name) (ls : List VLevel)
    (R : TShape → VExpr → Prop) (T : VExpr) : Prop :=
  ∃ Bs Rty, SpineAtB (U := U) (henv := henv) (hU := hU) P Γ₀ c ls R T Bs Rty

/-- A constant of `cs` interpreted by `Const` from `R`, typed at an interpretation of its type, is
at a shape of `GoodC`, given that it is related along its interpretation's nodes at its arity
(`SpineAt`). -/
theorem GoodC.of_spine (hM : ModelEnv env) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (P : List VExpr → VExpr → Prop)
    (hP : ∀ {Γ A B}, P Γ (.forallE A B) → P Γ A ∧ P (A::Γ) B)
    (hTy : ∀ {Γ T}, OnCtx Γ (env.IsType U) → P Γ T → ∃ u, env.HasType U Γ T (.sort u) ∧
      StrongSoundEq env U Γ T T (.sort u) ∧ AdeqStmt (U := U) henv hU Γ₀ Γ T T (.sort u))
    {cs : List (Name × VConstant)} {c : Name} {ci : VConstant} {ls : List VLevel}
    {R : TShape → VExpr → Prop} {n : Nat} {m' a : TShape} {ρ : Valuation}
    (hci : (c, ci) ∈ cs) (hcon : env.constants c = some ci) (hlen : ls.length = ci.uvars)
    (hm'a : m'.HasType a) (ha : LE_Interp env ρ a (ci.type.instL ls))
    (H : Const (n := n) env c ls R [] m') (hR : ∀ h e, R h e → LE_Interp env ρ h e)
    (hdom : ¬AxInterp.dom c)
    (hS : ∀ ls₁ ls₂ ls₃, List.Forall₂ (· ≈ ·) ls ls₁ → List.Forall₂ (· ≈ ·) ls ls₂ →
      List.Forall₂ (· ≈ ·) ls ls₃ → (∀ l ∈ ls₁, l.WF U) → (∀ l ∈ ls₂, l.WF U) →
      (∀ l ∈ ls₃, l.WF U) → SpineAt (U := U) henv hU P Γ₀ c ls R (ci.type.instL ls₃)) :
    GoodC (U := U) henv hU ‹AxInterp› Γ₀ cs c ls m' := by
  have hcl : ClosedRules env := hM.closed
  have htc : (ci.type.instL ls).ClosedN := (hcl.constType hcon).instL
  refine ⟨ci, hci, hlen, ?_, ⟨a, hm'a, (closed_iff hcl htc).1 ha⟩, ?_⟩
  · exact (closed_iff hcl (M := .const c ls) trivial).1
      (.const hcon hlen TShape.LE.rfl hm'a ha H hR)
  intro ls₁ ls₂ ls₃ e1 e2 e3 w1 w2 w3
  obtain ⟨Bs, Rty, har, hPT, hint, hconv, hsat⟩ := hS ls₁ ls₂ ls₃ e1 e2 e3 w1 w2 w3
  intro N w b hgw hwg hwb hb
  have hb' := hint hb
  refine hconv hb hwb ?_
  -- relate at a depth both the shape and the interpretation's derivation reach
  let n₂ := max N n
  have hND : N ≤ n₂ + 1 := Nat.le_succ_of_le (Nat.le_max_left _ _)
  have hn₂ : n ≤ n₂ := Nat.le_max_right _ _
  have H' : Const (n := n₂) env c ls R [] m' := by simpa using H.lift hn₂
  have key := constSpine_core hM hΓ₀ P hP hTy (ConstAt U c ls) hdom Bs Rty har
    (fun rargs _ H hl _ _ _ _ hF hF' W w a hw hwa ha => hsat rargs H hl hF hF' W w a hw hwa ha)
    Bs.length 0 (by simp) [] H' rfl (by simpa using hΓ₀) (by simpa using hPT)
    ⟨ls₁, e1, w1, rfl⟩ ⟨ls₂, e2, w2, rfl⟩ (σ := .id) (σ' := .id)
    (by simpa [valOf, pushAll] using LR.SubstWF.id)
    (w.lift (n₂+1)) (b.lift (n₂+1)) ((TShape.lift_eqv hND).1.trans hwg)
    ((WShape.HasType.lift hND).2 hwb)
    (by simpa [valOf, pushAll] using hb'.mono (TShape.lift_eqv hND).1)
  simp only [spineAt, VExpr.bvars, List.range_zero, List.reverse_nil, List.map_nil, VExpr.appN,
    List.drop_zero, subst_id] at key
  exact (LR.DefEq.lift hND hwb).1 key

omit [ShapeEnv] [AxInterp] in
/-- A substitution along a context at levels `ls` is one along it at equivalent levels. -/
theorem Ctx.SubstEq.instL_congr (henv : env.Ordered) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {ls ls' : List VLevel} {U' : Nat} (hls : ∀ l ∈ ls, l.WF U)
    (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ {Δ : List VExpr} {σ σ'}, OnCtx Δ (env.IsType U') →
      VEnv.Ctx.SubstEq env U Γ σ σ' (Δ.map (·.instL ls)) →
      VEnv.Ctx.SubstEq env U Γ σ σ' (Δ.map (·.instL ls'))
  | [], _, _, _, _ => .nil
  | _ :: Δ, _, _, ⟨hΔ, _, hA⟩, .cons W _ ha => by
    have hd := (hA.instL_r henv hΔ hls hls' heq).substDF henv (hΔ.instL hls) hΓ W.left
    exact .cons (Ctx.SubstEq.instL_congr henv hΓ hls hls' heq hΔ W) (hA.instL hls')
      (hd.defeqDF ha)

omit [ShapeEnv] [AxInterp] in
/-- A substitution along a closed context depends only on its values at the context's variables. -/
theorem Ctx.SubstEq.congr_closed {Γ : List VExpr} :
    ∀ {Cs : List VExpr} {σ σ' τ τ' : VExpr.Subst}, CtxClosed Cs →
      (∀ i < Cs.length, σ i = τ i) → (∀ i < Cs.length, σ' i = τ' i) →
      VEnv.Ctx.SubstEq env U Γ σ σ' Cs → VEnv.Ctx.SubstEq env U Γ τ τ' Cs
  | [], _, _, _, _, _, _, _, _ => .nil
  | _ :: Cs, σ, σ', τ, τ', ⟨hC, hA⟩, h1, h2, .cons W hAt ha => by
    refine .cons (Ctx.SubstEq.congr_closed hC (fun i hi => h1 (i+1) (by simp; omega))
      (fun i hi => h2 (i+1) (by simp; omega)) W) hAt ?_
    have e1 : σ.head = τ.head := h1 0 (by simp)
    have e2 : σ'.head = τ'.head := h2 0 (by simp)
    have e3 := hA.subst_congr (σ := σ.tail) (σ' := τ.tail) fun i hi => h1 (i+1) (by simp; omega)
    rw [← e1, ← e2, ← e3]; exact ha

/-- A recorded type former at levels equivalent to `ls₁`, applied to arguments related along its
telescope at `ls₁`, is related to itself as an application of a type former (`IndRel`). -/
theorem indRel_spine (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {h : IndHead}
    {d : VInductDecl} {t : Nat} {T : VInductiveType} (hs : env.inducts h.name = some (d, t))
    (hT : d.types[t]? = some T) (hn : Inert env h.name)
    {ls₁ l₁ l₂ : List VLevel} (hls₁ : ∀ l ∈ ls₁, l.WF U) (hl₁ : ∀ l ∈ l₁, l.WF U)
    (hl₂ : ∀ l ∈ l₂, l.WF U) (e₁ : List.Forall₂ (· ≈ ·) ls₁ l₁) (e₂ : List.Forall₂ (· ≈ ·) l₁ l₂)
    {σ σ' : VExpr.Subst} {ρ : Valuation}
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ'
      (((d.params ++ T.indices).map (·.instL ls₁)).reverse ++ Γ₀) ρ) :
    IndRel env U Γ₀ h (spineAt (.const h.name l₁) (d.params ++ T.indices).length σ)
      (spineAt (.const h.name l₂) (d.params ++ T.indices).length σ') := by
  have hΔ := henvW.blockTele_onCtx hs hT
  have hΔ₁ : OnCtx (((d.params ++ T.indices).map (·.instL ls₁)).reverse) (env.IsType U) := by
    rw [← List.map_reverse]; exact hΔ.instL hls₁
  have W1 := Ctx.SubstEq.vals henvW.ordered hΔ₁ (W.toSubstEq hΓ₀)
  rw [List.length_reverse, List.length_map, ← List.map_reverse] at W1
  have W2 := Ctx.SubstEq.instL_congr henvW.ordered hΓ₀ hls₁ hl₁ e₁ hΔ W1
  have hcl : CtxClosed (((d.params ++ T.indices).reverse).map (·.instL l₁)) :=
    (hΔ.instL hl₁).ctxClosed henvW.ordered
  have hlen : ((VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ)).length =
      (d.params ++ T.indices).length := by simp [VExpr.bvars]
  have hlen' : ((VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ')).length =
      (d.params ++ T.indices).length := by simp [VExpr.bvars]
  have W3 := Ctx.SubstEq.congr_closed (τ := Subst.dflt.consList
      ((VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ)))
    (τ' := Subst.dflt.consList ((VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ')))
    hcl (fun i hi => ?_) (fun i hi => ?_) W2
  · refine IndRel.of_substEq henvW hn hs hΓ₀ hl₁ hl₂ e₂ ?_ ?_ ?_
    · rw [typeTele_block hs hT]; simpa using hlen
    · rw [typeTele_block hs hT]; simpa using hlen'
    · rw [typeTele_block hs hT, ← List.map_reverse]; exact W3
  · simp only [List.length_map, List.length_reverse] at hi
    rw [Subst.consList_lt _ _ _ (by rw [hlen]; exact hi), Subst.consList_lt _ _ _ (by rw [hlen]; exact hi)]
  · simp only [List.length_map, List.length_reverse] at hi
    rw [Subst.consList_lt _ _ _ (by rw [hlen']; exact hi),
      Subst.consList_lt _ _ _ (by rw [hlen']; exact hi)]

end LogRel
end Lean4Lean

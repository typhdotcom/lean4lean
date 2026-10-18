import Lean4Lean.Theory.Typing.LogRel.RelLift

/-!
# Telescopes related from their types

Two telescopes of `k` pi binders whose types are related, one depth up, at a telescope shape are
related along it (`TeleRel.of_tyDefEq`). This is how the constructors' telescopes of an
inductive type's application become related (`IndTele`) from the constructors' types: the
relation at depth `n+1` relates a pi type's codomains at arguments of depth `n`, which is what
`TeleRel` at depth `n` quantifies over, and each codomain goes back up a depth by `LR.TyDefEq.lift`.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr} [ShapeEnv] {henv : env.Ordered}
  {hU : StepUniq env}

omit [ShapeEnv] in
theorem piCount_inst_ge : ∀ (e a : VExpr) (k : Nat), piCount e ≤ piCount (e.inst a k)
  | .forallE _ B, a, k => Nat.succ_le_succ (piCount_inst_ge B a (k+1))
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .app .., _, _ | .lam .., _, _
  | .proj .., _, _ => Nat.zero_le _

omit [ShapeEnv] in
theorem exists_forallE_of_piCount : ∀ {T : VExpr}, 0 < piCount T → ∃ D B, T = .forallE D B
  | .forallE _ _, _ => ⟨_, _, rfl⟩

/-- Telescopes whose types are related one depth up at a telescope shape are related along it. -/
theorem TeleRel.of_tyDefEq : ∀ {k T T'} {tel : WShape n}, tel.HasType .type →
    k ≤ piCount T → k ≤ piCount T' →
    (LR (U := U) (Γ := Γ) henv hU (n+1)).TyDefEq T T' (tel.lift (n+1)) →
    (LR (U := U) (Γ := Γ) henv hU (n+1)).TyTy T (tel.lift (n+1)) →
    (LR (U := U) (Γ := Γ) henv hU (n+1)).TyTy T' (tel.lift (n+1)) →
    TeleRel (LR (U := U) (Γ := Γ) henv hU n) k T T' tel
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | k+1, T, T', tel, ht, hk, hk', H, hY, hY' => by
    cases hv : tel.piView with
    | none => exact .inl hv
    | some bg =>
      obtain ⟨b, g⟩ := bg
      cases n with
      | zero => simp at hv
      | succ n =>
      obtain ⟨s, f, rfl, rfl, rfl⟩ := WShape.piView_eq_some hv
      have ⟨tb, tg⟩ := WShape.piView_type ht hv
      rw [WShape.lift_forallE (Nat.le_succ n)] at H hY hY'
      simp only [LR, LRS, LRS.TyDefEq.forallE_iff] at H
      simp only [LR, LRS, LRS.TyTyped.forallE_iff] at hY hY'
      obtain ⟨D, B, rT⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk)
      obtain ⟨D', B', rT'⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk')
      subst rT rT'
      rcases H with ⟨B₁, F₁, B₂, F₂, r1, r2, hBB, -, hTy, hP⟩ | ⟨hN, -⟩
      · cases StepS.determ hU .rfl forallE_whnf' r1 forallE_whnf'
        cases StepS.determ hU .rfl forallE_whnf' r2 forallE_whnf'
        obtain ⟨A₁, A₂, -, -, rA, -, -, -, y1, hY1⟩ :=
          hY.resolve_left fun hN => NeRed.not_forallE hU hN .rfl
        obtain ⟨A₁', A₂', -, -, rA', -, -, -, y2, hY2⟩ :=
          hY'.resolve_left fun hN => NeRed.not_forallE hU hN .rfl
        cases StepS.determ hU .rfl forallE_whnf' rA forallE_whnf'
        cases StepS.determ hU .rfl forallE_whnf' rA' forallE_whnf'
        refine .inr ⟨_, _, _, _, _, _, hv, .rfl, .rfl, hBB, hTy, y1, y2,
          fun a a' p hp ha hr => ?_⟩
        have h1 := (hP.1 hp ha hr).1
        have h2 := hP.2 hp ha.hasType.2 ((LR _ _ _).left ((LR _ _ _).symm hr))
        have h12 := (LR (U := U) (Γ := Γ) henv hU (n+1)).trans_ty h1 h2
        have ha' := hBB.defeqDF ha.hasType.2
        have hr' := (LR (U := U) (Γ := Γ) henv hU (n+1)).conv hBB hTy
          ((LR _ _ _).left ((LR _ _ _).symm hr))
        have t1 := hY1 _ p hp ha.hasType.1 ((LR _ _ _).left hr)
        have t2 := hY2 _ p hp ha' hr'
        have T1 := (LR (U := U) (Γ := Γ) henv hU (n+1)).left_ty h12
        have T2 := (LR (U := U) (Γ := Γ) henv hU (n+1)).left_ty
          ((LR (U := U) (Γ := Γ) henv hU (n+1)).symm_ty h12)
        refine TeleRel.of_tyDefEq (tg p) ?_ ?_ ((LR.TyDefEq.lift (Nat.le_succ _) (tg p)).2 h12)
          ((LR.TyTy.lift (Nat.le_succ _) (tg p) T1).2 t1)
          ((LR.TyTy.lift (Nat.le_succ _) (tg p) T2).2 t2)
        · exact Nat.le_trans (Nat.le_of_succ_le_succ hk) (piCount_inst_ge _ _ _)
        · exact Nat.le_trans (Nat.le_of_succ_le_succ hk') (piCount_inst_ge _ _ _)
      · exact (NeRed.not_forallE hU hN .rfl).elim

/-- A telescope shape applied in turn to argument shapes, through its pi views. -/
def WShape.piApps : WShape n → List (WShape n) → WShape n
  | tel, [] => tel
  | tel, p :: ps => match tel.piView with
    | some (_, g) => WShape.piApps (g.app p) ps
    | none => .bot

section
variable {IH : LogRel env U Γ n}

omit [ShapeEnv] in
theorem piInst_forallE : piInst (.forallE D B) (a :: As) = piInst (B.inst a) As := rfl

/-- A telescope relation of `np + k` binders, at syntactic pi types, instantiated at arguments
related along its first `np` domains, is a relation of the remaining `k`. -/
theorem TeleRel.instArgs (hU : StepUniq env) : ∀ {As As' : List VExpr} {k T T'} {tel : WShape n}
    {ps : List (WShape n)}, As.length ≤ piCount T → As'.length ≤ piCount T' →
    TeleRel IH (As.length + k) T T' tel → FieldsRel IH T tel As As' ps →
    TeleRel IH k (piInst T As) (piInst T' As') (tel.piApps ps)
  | [], [], _, _, _, _, [], _, _, H, _ => by simpa [WShape.piApps, piInst] using H
  | a :: As, a' :: As', k, T, T', tel, p :: ps, hk, hk', H, HF => by
    obtain ⟨D, B, b, g, hv, r, hp, ha, hr, HF'⟩ := HF
    obtain ⟨D₀, B₀, rfl⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos _) hk)
    obtain ⟨D₀', B₀', rfl⟩ := exists_forallE_of_piCount (Nat.lt_of_lt_of_le (Nat.succ_pos _) hk')
    cases StepS.determ hU .rfl forallE_whnf' r forallE_whnf'
    have e : (a :: As).length + k = (As.length + k) + 1 := by simp; omega
    rw [e] at H
    obtain ⟨D₁, B₁, D₁', B₁', r1, r1', -, -, Hq⟩ := H.of_piView hv
    cases StepS.determ hU .rfl forallE_whnf' r1 forallE_whnf'
    cases StepS.determ hU .rfl forallE_whnf' r1' forallE_whnf'
    have := instArgs hU (Nat.le_trans (Nat.le_of_succ_le_succ hk) (piCount_inst_ge _ _ _))
      (Nat.le_trans (Nat.le_of_succ_le_succ hk') (piCount_inst_ge _ _ _)) (Hq a a' p hp ha hr) HF'
    simpa [WShape.piApps, hv, piInst] using this
  | [], _ :: _, _, _, _, _, _, _, _, _, HF => by cases HF
  | _ :: _, [], _, _, _, _, _, _, _, _, HF => by cases HF
  | [], [], _, _, _, _, _ :: _, _, _, _, HF => by cases HF
  | _ :: _, _ :: _, _, _, _, _, [], _, _, _, HF => by cases HF

end

omit [ShapeEnv] in
theorem piCount_instL : ∀ (e : VExpr) (ls : List VLevel), piCount (e.instL ls) = piCount e
  | .forallE _ B, ls => by simp [VExpr.instL, piCount, piCount_instL B ls]
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _ | .proj .., _ => rfl

section
variable {IH : LogRel env U Γ n}

/-- The constructors' telescopes of two applications of an inductive type former are related at
the type shape's telescopes, given, for each constructor, its types at the two levels related
along a telescope shape whose instance at the parameters' shapes lies above the constructor's
telescope shape, and the parameters related along it. -/
theorem IndTele.of_ctors (hU : StepUniq env) {h : IndHead} {l : List (WShape n)}
    {ls ls' : List VLevel} {As As' : List VExpr} (hn : Inert env h.name)
    (H : ∀ c i k ci, h.ctors.idxOf? c = some i → h.arities[i]? = some k →
      env.constants c = some ci →
      ∃ (tel : WShape n) (ps : List (WShape n)), (ctorTel h l i).HasType .type ∧
        (tel.piApps ps).HasType .type ∧ ctorTel h l i ≤ tel.piApps ps ∧
        (As.take (piCount ci.type - k)).length = piCount ci.type - k ∧
        (As'.take (piCount ci.type - k)).length = piCount ci.type - k ∧
        TeleRel IH (piCount ci.type - k + k) (ci.type.instL ls) (ci.type.instL ls') tel ∧
        FieldsRel IH (ci.type.instL ls) tel (As.take (piCount ci.type - k))
          (As'.take (piCount ci.type - k)) ps) :
    IndTele IH h l ((VExpr.const h.name ls).appN As) ((VExpr.const h.name ls').appN As') := by
  intro lsX AsX lsX' AsX' rM rN c i k ci hi hk hc
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.determ hU .rfl hn.whnf rM hn.whnf)
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.determ hU .rfl hn.whnf rN hn.whnf)
  obtain ⟨tel, ps, ht, ht', hle, hl1, hl2, HT, HF⟩ := H c i k ci hi hk hc
  have := TeleRel.instArgs hU (k := k) (T := ci.type.instL ls) (T' := ci.type.instL ls')
    (by rw [hl1, piCount_instL]; omega)
    (by rw [hl2, piCount_instL]; omega) (by rw [hl1]; exact HT) HF
  exact TeleRel.mono hU hle ht ht' this

end

end LogRel
end Lean4Lean

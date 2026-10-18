import Lean4Lean.Theory.Typing.LogRel.ConstSpine
import Lean4Lean.Theory.Typing.LogRel.IndTeleOf

/-!
# A type former related along its interpretation

A recorded inductive type former applied to arguments related along its telescope is related at
its interpretation's inductive type shape: the two applications are applications of the same type
former with related arguments (`IndRel`, `indRel_spine`), their constructors' telescopes are
related at the shape's telescopes (`IndTele`), and what the relation knows of their typing as types
(`StructTy`) holds. The last two are what the constructors' types give, and are taken here as
hypotheses on the applications.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] [AxInterp] {env : VEnv} {U : Nat} {henv : env.Ordered} {hU : StepUniq env}

/-- The inductive type shape's head for the type former `c` of the type `T`, applied to `k`
arguments. -/
abbrev typeHeadOf (c : Name) (k : Nat) (T : VInductiveType) : IndHead :=
  ⟨c, k, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩

/-- A recorded type former at its arity: the type former applied to arguments related along its
telescope is related at every shape below its interpretation, typed at an interpretation of the
sort it lives in, given that the constructors' telescopes of such applications are related at the
interpretation's telescopes (`HC`) and that the applications are typed as types are (`HY`). -/
theorem typeFormer_sat (hM : ModelEnv env) (henvW : env.WF) (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {c : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (hs : env.inducts c = some (d, t)) (hT : d.types[t]? = some T) (hdom : ¬AxInterp.dom c)
    {ls ls₃ : List VLevel} (hls₃ : ∀ l ∈ ls₃, l.WF U) (e₃ : List.Forall₂ (· ≈ ·) ls ls₃)
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
      StructTy env U Γ₀ (typeHeadOf c rargs.length T) (spineAt F (d.params ++ T.indices).length σ'))
    {n : Nat} (rargs : List (WShape n)) {m : TShape} (H : Const env c ls R rargs m)
    (hlen : rargs.length = ((d.params ++ T.indices).map (·.instL ls₃)).length)
    {F F' : VExpr} {σ σ' : VExpr.Subst} (hF : ConstAt U c ls F) (hF' : ConstAt U c ls F')
    (W : LR.SubstWF (U := U) henv hU Γ₀ σ σ'
      (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀) (valOf rargs))
    (w a : WShape (n+1)) (hw : w.T ≤ m) (hwa : w.HasType a)
    (ha : LE_Interp env (valOf rargs) a.T (.sort (d.level.inst ls₃))) :
    (LR (U := U) (Γ := Γ₀) henv hU (n+1)).DefEq
      (spineAt F ((d.params ++ T.indices).map (·.instL ls₃)).length σ)
      (spineAt F' ((d.params ++ T.indices).map (·.instL ls₃)).length σ')
      ((VExpr.sort (d.level.inst ls₃)).subst σ) w a := by
  rw [List.length_map]
  rw [List.length_map, List.length_append] at hlen
  have hR : ConstRoles env := hM.roles
  rcases LE_Interp.Const.indTy_inv hR hdom hs hT hlen H with hb | ⟨ctys, hcl, hcty, hle⟩
  · have : w = .bot := WShape.le_bot.1 (WShape.LE.T_iff.1 (hw.trans (hb.trans TShape.bot_eqv.2)))
    subst this; exact (LR _ _ _).bot hwa.isType
  rcases WShape.le_indTy.1 (WShape.LE.T_iff.1 (hw.trans hle)) with rfl | ⟨l, rfl, hl⟩
  · exact (LR _ _ _).bot hwa.isType
  obtain ⟨j, rfl, -⟩ := WShape.HasType.indTy_inv hwa
  have htel := WShape.HasType.indTy_tels' hwa
  obtain ⟨l₁, e₁, hl₁, rfl⟩ := hF
  obtain ⟨l₂, e₂, hl₂, rfl⟩ := hF'
  have hn : Inert env c := Inert.of_role hR (fun hdf e => henvW.rule_lhs_params hdf e)
    (ConstArity.indTy hs hT) (fun _ h => by cases h) (fun _ _ h => by cases h) (fun h => by cases h)
  have IR := indRel_spine (h := typeHeadOf c rargs.length T) henvW hΓ₀ hs hT hn hls₃ hl₁ hl₂
    (levels_equiv_trans (levels_equiv_symm e₃) e₁)
    (levels_equiv_trans (levels_equiv_symm e₁) e₂) W
  have IT := HC rargs ctys ⟨l₁, e₁, hl₁, rfl⟩ ⟨l₂, e₂, hl₂, rfl⟩ W hlen hcl hcty l hl htel
  obtain ⟨Y1, Y2⟩ := HY rargs ⟨l₁, e₁, hl₁, rfl⟩ W hlen
  obtain ⟨Y1', Y2'⟩ := HY rargs ⟨l₂, e₂, hl₂, rfl⟩ W hlen
  refine (LR _ _ _).sort_a_iff.2 ⟨?_, fun _ _ => ⟨?_, ?_⟩⟩
  · simp only [LR, LRS, LRS.TyDefEq.indTy_iff]; exact .inl ⟨IR, IT⟩
  · simp only [LR, LRS, LRS.TyTyped.indTy_iff]; exact .inr Y1
  · simp only [LR, LRS, LRS.TyTyped.indTy_iff]; exact .inr Y2'

end LogRel
end Lean4Lean

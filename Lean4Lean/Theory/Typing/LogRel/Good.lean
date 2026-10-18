import Lean4Lean.Theory.Typing.LogRel.ConstDelta
import Lean4Lean.Theory.Typing.ConstsSat

/-!
# Recursive definitions in the logical relation

A recursive definition's value is typed in the environment with its block's constants as axioms,
so adequacy of the value needs the constants related at every shape the value's derivation reaches,
not only at the shapes that interpret the constant: the model's soundness moves a derivation to
other interpretations. The model that interprets the block's constants by the shapes where they are
already related (`Good`) breaks the cycle: there the constants are related by definition, the
value's derivation is adequate, and every interpretation of a constant in the model before it
reaches a shape of `Good` (`transfer`), by induction on the interpretation's derivation.

Two models interpret a term alike when it mentions only constants neither interprets by given
shapes and whose unfoldings mention only such constants (`SameOn`).
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable [ShapeEnv] {env : VEnv}

variable (env) in
/-- Constants `Q` two models interpret alike: neither interprets one by given shapes, and the
closed terms the model reads off one mention only constants of `Q`. -/
structure SameOn (X Y : AxInterp) (Q : Name → Prop) : Prop where
  domX : Q c → ¬X.dom c
  domY : Q c → ¬Y.dom c
  delta : env.defeqs df → df.lhs = .const c (VLevel.params df.uvars) → Q c → df.rhs.ConstsSat Q
  constType : env.constants c = some ci → Q c → ci.type.ConstsSat Q
  ctorType : env.inducts c = some (d, t) → Q c → d.types[t]? = some T → c' ∈ T.ctors →
    c'.type.ConstsSat Q
  iotaRhs : env.inducts s = some (d, t) → Q c → c = d.recName j → d.allCtors[q]? = some (j, c') →
    (d.iotaRhs ls q j c').ConstsSat Q
  quotMk : env.defeqs quotDefEq → Q ``Quot → env.constants ``Quot.mk = some ci →
    ci.type.ConstsSat Q

theorem SameOn.symm {X Y : AxInterp} (H : SameOn env X Y Q) : SameOn env Y X Q :=
  ⟨H.domY, H.domX, H.delta, H.constType, H.ctorType, H.iotaRhs, H.quotMk⟩

/-- A constant of `Q` is interpreted alike by both models, reading the same closed terms. -/
theorem LE_Interp.Const.sameOn {X Y : AxInterp} (H : SameOn env X Y Q) (hc : Q c)
    (h : @Const _ X env c ls R n rargs m) :
    @Const _ Y env c ls (fun h e => R h e ∧ e.ConstsSat Q) n rargs m := by
  induction h with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ext h0 => exact (H.domX hc h0).elim
  | delta _ h1 h2 h3 h4 h5 =>
    exact .delta (H.domY hc) h1 h2 h3 ⟨h4, (H.delta h1 h2 hc).instL⟩ h5
  | indTy h1 h2 h3 h4 h5 h6 =>
    refine .indTy h1 h2 h3 h4 (fun i c' cty a1 a2 => ?_) h6
    obtain ⟨h, b1, b2⟩ := h5 i c' cty a1 a2
    exact ⟨h, ⟨b1, (H.ctorType h1 hc h2 (List.mem_of_getElem? a1)).instL⟩, b2⟩
  | ctor h1 h2 h3 h4 h5 h6 h7 => exact .ctor h1 h2 h3 h4 h5 h6 h7
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .iota h1 h2 h3 h4 h5 h6 h7 ⟨h8, H.iotaRhs h1 hc h2 h3⟩ h9 h10
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 ⟨h9, H.iotaRhs h1 hc h2 h3⟩ h10
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .quotTy h1 h2 h3 h4 h5 ⟨h6, (H.quotMk h1 (h2 ▸ hc) h5).instL⟩ h7 h8
  | quotMk h1 h2 h3 h4 h5 => exact .quotMk h1 h2 h3 h4 h5
  | quot h1 h2 h3 h4 h5 h6 => exact .quot h1 h2 h3 h4 h5 h6
  | quotK h1 h2 h3 h4 h5 => exact .quotK h1 h2 h3 h4 h5

/-- A term mentioning only constants of `Q` has the same interpretations in both models. -/
theorem LE_Interp.sameOn {X Y : AxInterp} (H : SameOn env X Y Q)
    (h : @LE_Interp _ X env ρ m e) (he : e.ConstsSat Q) : @LE_Interp _ Y env ρ m e := by
  induction h with
  | bot => exact .bot
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | app _ _ h3 ih1 ih2 => exact .app (ih1 he.1) (ih2 he.2) h3
  | lam _ h2 _ h4 ih1 ih3 => exact .lam (ih1 he.1) h2 (fun x hx => ih3 x hx he.2) h4
  | forallE _ _ h3 _ h5 ih1 ih2 ih4 =>
    exact .forallE (ih1 he.1) (ih2 he.1) h3 (fun x hx => ih4 x hx he.2) h5
  | const h1 h2 h3 h4 _ h6 _ ih5 ih7 =>
    exact .const h1 h2 h3 h4 (ih5 (H.constType h1 he).instL) (h6.sameOn H he)
      fun m e ⟨hr, hq⟩ => ih7 m e hr hq
  | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih he) h5 h6

end LogRel
end Lean4Lean

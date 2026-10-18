import Lean4Lean.Theory.Typing.LogRel.Mutual
import Lean4Lean.Theory.Typing.LogRel.BlockSound
import Lean4Lean.Theory.Typing.ConstsSatTyping

/-!
# Environments a well-formed one is built through

A declaration adds only fresh names, so a rule headed by an earlier constant, the quotient's rule
once its names exist, and the block recorded for a name once one of the block's names exists are
already the earlier environment's. Hence a constant's role, and what the model reads off it, are
decided where it is declared: a constant declared without rules has no role, and two models that
interpret none of an earlier environment's constants by given shapes read its constants alike.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open StepUniqProof LE_Interp

/-- `E₂` is built from `E` by well-formed declarations. -/
inductive Extends : VEnv → VEnv → Prop where
  | refl : Extends E E
  | step : VDecl.WF E d E₁ → Extends E₁ E₂ → Extends E E₂

theorem Extends.le : Extends E E₂ → E ≤ E₂
  | .refl => VEnv.LE.rfl
  | .step h1 h2 => h1.le.trans h2.le

/-- A block recorded by a declaration from `E`: its types, own constructors and recursors are
fresh in `E`, and `s` is one of its types. -/
structure NewBlock (E : VEnv) (d : VInductDecl) (s : Name) : Prop where
  name : ∃ T ∈ d.types, T.name = s
  types : ∀ T ∈ d.types, E.constants T.name = none
  ctors : ∀ T ∈ d.types, ∀ c ∈ T.ctors, E.constants c.name = none
  recs : ∀ j < d.allTypes.length, E.constants (d.recName j) = none

/-- One of the quotient's names is a constant of `E`. -/
def QuotOld (E : VEnv) : Prop :=
  E.constants ``Quot ≠ none ∨ E.constants ``Quot.mk ≠ none ∨ E.constants ``Quot.lift ≠ none

theorem QuotOld.mono {E E' : VEnv} (hle : E ≤ E') (h : QuotOld E) : QuotOld E' := by
  have m {n} (h : E.constants n ≠ none) : E'.constants n ≠ none := fun h' => by
    obtain ⟨ci, e⟩ := Option.ne_none_iff_exists'.1 h; rw [hle.constants e] at h'; cases h'
  exact h.imp m (Or.imp m m)

/-- What a declaration leaves of the environment before it. -/
structure Back (E₁ E₂ : VEnv) : Prop where
  defeq : E₂.defeqs df → df.lhs = .const c us → E₁.constants c ≠ none → E₁.defeqs df
  quot : E₂.defeqs quotDefEq → QuotOld E₁ → E₁.defeqs quotDefEq
  inducts : E₂.inducts s = some (d, t) → E₁.inducts s = some (d, t) ∨ NewBlock E₁ d s

theorem _root_.Lean4Lean.VDecl.WF.back {E₁ E₂ : VEnv} (hD : VDecl.WF E₁ dc E₂) : Back E₁ E₂ := by
  cases hD with
  | «axiom» _ h1 | «opaque» _ h1 =>
    exact ⟨fun h _ _ => VEnv.addConst_defeqs h1 ▸ h, fun h _ => VEnv.addConst_defeqs h1 ▸ h,
      fun h => .inl (VEnv.addConst_inducts h1 ▸ h)⟩
  | «example» => exact ⟨fun h _ _ => h, fun h _ => h, fun h => .inl h⟩
  | «def» _ h1 =>
    have f1 := (VEnv.addConst_constants_iff h1).1
    refine ⟨fun h e hc => ?_, fun h _ => ?_, fun h => ?_⟩
    · rcases h with rfl | h
      · cases e; exact (hc f1).elim
      · exact VEnv.addConst_defeqs h1 ▸ h
    · rcases h with h | h
      · exact (defn_ne_quot _ h.symm).elim
      · exact VEnv.addConst_defeqs h1 ▸ h
    · exact .inl (VEnv.addConst_inducts h1 ▸ h)
  | @mutualDef cis E' _ _ h1 _ =>
    rw [VEnv.addConsts_eq] at h1
    obtain ⟨-, g2, -⟩ := VEnv.addConstList_spec h1
    have hd₁ := VEnv.addConstList_defeqs' h1
    have hi₁ := VEnv.addConstList_inducts h1
    refine ⟨fun h e hc => ?_, fun h _ => ?_, fun h => ?_⟩
    · rcases VEnv.addDefEqs_defeqs h with ⟨ci, hci, rfl⟩ | h
      · cases e
        exact (hc (g2 _ (List.mem_map_of_mem (f := fun ci : VDefVal => (ci.name, ci.toVConstant))
          hci))).elim
      · exact hd₁ ▸ h
    · rcases VEnv.addDefEqs_defeqs h with ⟨ci, -, h⟩ | h
      · exact (defn_ne_quot ci h.symm).elim
      · exact hd₁ ▸ h
    · rw [VEnv.addDefEqs_inducts, hi₁] at h; exact .inl h
  | quot _ h1 =>
    obtain ⟨f1, f2, f0, -⟩ := VEnv.addQuot_spec h1
    refine ⟨fun h e _ => ?_, fun h hq => ?_, fun h => .inl (VEnv.addQuot_inducts h1 ▸ h)⟩
    · rcases VEnv.addQuot_defeqs h1 h with rfl | h
      · obtain ⟨A, b, e'⟩ := quotDefEq_lhs; rw [e'] at e; cases e
      · exact h
    · rcases VEnv.addQuot_defeqs h1 h with - | h
      · rcases hq with h | h | h
        · exact absurd f0 h
        · exact absurd f2 h
        · exact absurd f1 h
      · exact h
  | @induct _ E' d hd _ h1 =>
    simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
    obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := h1
    obtain ⟨-, t2, t3⟩ := VEnv.addConstList_spec hT
    obtain ⟨-, c2, c3⟩ := VEnv.addConstList_spec hC
    obtain ⟨-, r2, -⟩ := VEnv.addConstList_spec hR
    have hd' {df} (h : E₂.defeqs df) : df ∈ d.iotaRules ∨ E₁.defeqs df := by
      rw [VEnv.addBlock_defeqs hB] at h
      rcases VEnv.addDefEqList_defeqs' h with h | h
      · exact .inl h
      · rw [VEnv.addConstList_defeqs' hR, VEnv.addConstList_defeqs' hC,
          VEnv.addConstList_defeqs' hT] at h
        exact .inr h
    have envT_none {m} (h : envT.constants m = none) : E₁.constants m = none :=
      Classical.byContradiction fun h' => (t3 m).2 (.inl h') h
    have ctorFresh {m} (hm : m ∈ d.ctorConsts.map (·.1)) : E₁.constants m = none := by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm; exact envT_none (c2 p hp)
    have recFresh {m} (hm : m ∈ d.recConsts.map (·.1)) : E₁.constants m = none := by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      exact envT_none (Classical.byContradiction fun h' => (c3 _).2 (.inl h') (r2 p hp))
    have typeFresh {m} (hm : m ∈ d.typeConsts.map (·.1)) : E₁.constants m = none := by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm; exact t2 p hp
    refine ⟨fun h e _ => ?_, fun h _ => ?_, fun h => ?_⟩
    · rcases hd' h with h | h
      · exact (StepUniqProof.iotaRule_lhs hd.nonempty h e).elim
      · exact h
    · rcases hd' h with h | h
      · exact (iotaRule_ne_quot h rfl).elim
      · exact h
    · rcases VEnv.addBlock_inducts hB h with h | ⟨e, T, hT', rfl⟩
      · rw [VEnv.addDefEqList_inducts, VEnv.addConstList_inducts hR, VEnv.addConstList_inducts hC,
          VEnv.addConstList_inducts hT] at h
        exact .inl h
      · have e' : _ = d := e
        subst e'
        exact .inr ⟨⟨T, List.mem_of_getElem? hT', rfl⟩, fun T hT => typeFresh (mem_typeNames (List.mem_iff_getElem?.1 hT).choose_spec),
          fun T hT c hc => ctorFresh (mem_ctorNames hT hc),
          fun j hj => recFresh (mem_recNames.2 ⟨j, hj, rfl⟩)⟩

theorem not_newBlock_of {E E' : VEnv} (hle : E ≤ E') {n : Name} (hn : E.constants n ≠ none)
    (h : E'.constants n = none) : False := by
  obtain ⟨ci, e⟩ := Option.ne_none_iff_exists'.1 hn
  rw [hle.constants e] at h; cases h

theorem Extends.defeq (H : Extends E E₂) (h : E₂.defeqs df) (e : df.lhs = .const c us)
    (hc : E.constants c ≠ none) : E.defeqs df := by
  induction H with
  | refl => exact h
  | step h1 _ ih =>
    exact h1.back.defeq (ih h fun h' => not_newBlock_of h1.le hc h') e hc

theorem Extends.quot (H : Extends E E₂) (h : E₂.defeqs quotDefEq) (hq : QuotOld E) :
    E.defeqs quotDefEq := by
  induction H with
  | refl => exact h
  | step h1 _ ih => exact h1.back.quot (ih h (hq.mono h1.le)) hq

theorem Extends.inducts (H : Extends E E₂) (h : E₂.inducts s = some (d, t))
    (hold : ∀ E', E ≤ E' → ¬NewBlock E' d s) : E.inducts s = some (d, t) := by
  induction H with
  | refl => exact h
  | step h1 _ ih =>
    rcases h1.back.inducts (ih h fun E' le => hold E' (h1.le.trans le)) with h | h
    · exact h
    · exact (hold _ VEnv.LE.rfl h).elim

/-- A constant of `E` has the roles in `E₂` it has in `E`. -/
theorem Extends.constArity (H : Extends E E₂) (hc : E.constants c ≠ none)
    (h : ConstArity E₂ c r k) : ConstArity E c r k := by
  cases h with
  | delta hdf e => exact .delta (H.defeq hdf e hc) e
  | indTy hs hT =>
    exact .indTy (H.inducts hs fun E' le hN => by
      obtain ⟨T', hT', rfl⟩ := hN.name; exact not_newBlock_of le hc (hN.types T' hT')) hT
  | ctor hs hT hc' e =>
    subst e
    exact .ctor (H.inducts hs fun E' le hN =>
      not_newBlock_of le hc (hN.ctors _ (List.mem_of_getElem? hT) _ hc')) hT hc' rfl
  | recursor hs e hT =>
    subst e
    exact .recursor (H.inducts hs fun E' le hN =>
      not_newBlock_of le hc (hN.recs _ (List.getElem?_eq_some_iff.1 hT).1)) rfl hT
  | quotTy h e => subst e; exact .quotTy (H.quot h (.inl hc)) rfl
  | quotMk h e => subst e; exact .quotMk (H.quot h (.inr (.inl hc))) rfl
  | quotLift h e => subst e; exact .quotLift (H.quot h (.inr (.inr hc))) rfl

/-- A constant with a role in a well-formed environment is one of its constants. -/
theorem LE_Interp.ConstArity.const {E : VEnv} (hE : E.WF) (h : ConstArity E c r k) : E.constants c ≠ none := by
  obtain ⟨ρ, hρ⟩ := (names_of_WF hE).roles
  refine hρ.const ?_
  cases h with
  | delta hdf e => rw [hρ.defn hdf e]; nofun
  | indTy hs _ => rw [hρ.indTy hs]; nofun
  | ctor hs hT hc' e => subst e; rw [hρ.ownCtor hs hT hc']; nofun
  | recursor hs e hT =>
    subst e; rw [hρ.recr hs (List.getElem?_eq_some_iff.1 hT).1]; nofun
  | quotTy h e => subst e; rw [(hρ.quot h).2.2]; nofun
  | quotMk h e => subst e; rw [(hρ.quot h).2.1]; nofun
  | quotLift h e => subst e; rw [(hρ.quot h).1]; nofun

theorem LE_Interp.ConstArity.congr {E E' : VEnv} (hd : E'.defeqs = E.defeqs) (hi : E'.inducts = E.inducts)
    (h : ConstArity E' c r k) : ConstArity E c r k := by
  cases h with
  | delta hdf e => exact .delta (hd ▸ hdf) e
  | indTy hs hT => exact .indTy (hi ▸ hs) hT
  | ctor hs hT hc' e => exact .ctor (hi ▸ hs) hT hc' e
  | recursor hs e hT => exact .recursor (hi ▸ hs) e hT
  | quotTy h e => exact .quotTy (hd ▸ h) e
  | quotMk h e => exact .quotMk (hd ▸ h) e
  | quotLift h e => exact .quotLift (hd ▸ h) e

/-- A constant declared without rules has no role in any environment built from its own. -/
theorem Extends.noRole (hW : VEnv.WF' ds E) (h1 : E.addConst c ci = some E')
    (H : Extends E' env) : ∀ r k, ¬ConstArity env c r k := by
  intro r k h
  obtain ⟨f1, f2⟩ := VEnv.addConst_constants_iff h1
  have hc' : E'.constants c ≠ none := (f2 c).2 (.inr rfl)
  have h' := (H.constArity hc' h).congr (VEnv.addConst_defeqs h1) (VEnv.addConst_inducts h1)
  exact h'.const ⟨_, hW⟩ f1

theorem ConstsSat.of_isSome {e : VExpr} {E : VEnv}
    (h : e.ConstsSat (E.constants · |>.isSome)) : e.ConstsSat (E.constants · ≠ none) :=
  h.mono fun c hc => by simpa [Option.isSome_iff_ne_none] using hc

theorem iotaRule_mem {d : VInductDecl} (h : d.allCtors[q]? = some (j, c)) :
    d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c ∈ d.iotaRules := by
  simp only [VInductDecl.iotaRules, List.mem_map]
  exact ⟨((j, c), q), List.mk_mem_zipIdx_iff_getElem?.2 h, rfl⟩

variable [ShapeEnv] in
/-- Two models interpreting none of `E`'s constants by given shapes read `E`'s constants alike in
any environment built from `E`. -/
theorem Extends.sameOn (hW : VEnv.WF' ds E) (H : Extends E env) (X Y : AxInterp)
    (hX : ∀ c, X.dom c → E.constants c = none) (hY : ∀ c, Y.dom c → E.constants c = none) :
    SameOn env X Y (E.constants · ≠ none) := by
  have hE : E.WF := ⟨_, hW⟩
  have hO := hE.ordered.constsSat
  have hle := H.le
  have hconst {n ci} (hn : E.constants n ≠ none) (h : env.constants n = some ci) :
      E.constants n = some ci := by
    obtain ⟨ci', e⟩ := Option.ne_none_iff_exists'.1 hn
    rw [hle.constants e] at h; cases h; exact e
  refine ⟨fun hq hx => hq (hX _ hx), fun hq hx => hq (hY _ hx), fun hdf e hq => ?_,
    fun h hq => ?_, fun hs hq hT hc => ?_, fun hs hq e hq' => ?_, fun hdf hq h => ?_⟩
  · exact ConstsSat.of_isSome (hO.2 (H.defeq hdf e hq)).2.1
  · obtain ⟨_, h⟩ := hO.1 (hconst hq h); exact ConstsSat.of_isSome h.1
  · have hs' := H.inducts hs fun E' le hN => by
      obtain ⟨T', hT', e⟩ := hN.name; subst e; exact not_newBlock_of le hq (hN.types T' hT')
    obtain ⟨_, h⟩ := hO.1 (hE.ctor_constant hs' (mem_ctors hT hc))
    exact ConstsSat.of_isSome h.1
  · subst e
    obtain ⟨T, hT', -⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq')
    have hj := (List.getElem?_eq_some_iff.1 hT').1
    have hs' := H.inducts hs fun E' le hN => not_newBlock_of le hq (hN.recs _ hj)
    have hdf := (names_of_WF hE).iota hs' (iotaRule_mem hq')
    exact (ConstsSat.of_isSome (hO.2 hdf).2.1).instL
  · have hdf := H.quot hdf (.inl hq)
    obtain ⟨ρ, hρ⟩ := (names_of_WF hE).roles
    have hmk : E.constants ``Quot.mk ≠ none := hρ.const (by rw [(hρ.quot hdf).2.1]; nofun)
    obtain ⟨_, h⟩ := hO.1 (hconst hmk h); exact ConstsSat.of_isSome h.1

end LogRel
end Lean4Lean

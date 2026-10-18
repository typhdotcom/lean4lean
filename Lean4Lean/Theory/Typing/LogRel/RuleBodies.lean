import Lean4Lean.Theory.Typing.LogRel.WHRed
import Lean4Lean.Theory.Typing.LogRel.KIota
import Lean4Lean.Theory.Typing.LogRel.Inv
import Lean4Lean.Theory.Typing.Meta

/-!
# The rules' bodies are typed

`WF.iotaTyped`, `WF.kIotaTyped` and `WF.quotTyped` take as hypotheses that a
rule's bodies are typed under its binders. The quotient's rule is typed by computation. A block's
iota rules are typed as closed lambdas in the environment `envR` that has the block's types,
constructors and recursors but not yet its rules (`VInductDecl.GeneratedWF`); the bodies follow by
inverting lambda typing, which needs injectivity of pi types and uniqueness of typing in `envR`
(`VEnv.Inj`). `envR` has the defining equations and blocks of the environment the block was
declared in, and only axioms besides, so the fundamental lemma gives `Inj envR` before it has the
block's rules.
-/

namespace Lean4Lean
open VExpr

namespace VEnv
variable {env : VEnv}

/-- The quotient's rule has typed bodies, in any environment with the quotient's constants. -/
theorem quotBodyWF (hEq : env.constants ``Eq = some eqConst)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    (hlift : env.constants ``Quot.lift = some quotLiftConst) :
    quotDefEq.BodyWF env (QuotRed.liftBinders ++ [VExpr.bvar 4])
      (VExpr.appN (.const ``Quot.lift [.param 0, .param 1])
        [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
          .appN (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]])
      (.app (.bvar 2) (.bvar 0)) (VExpr.bvar 3) where
  lhs := by rw [QuotRed.quotDefEq_eq]
  rhs := by rw [QuotRed.quotDefEq_eq]
  type := by rw [QuotRed.quotDefEq_eq]
  tele := by
    rw [QuotRed.quotDefEq_eq]
    simp only [QuotRed.liftBinders, List.cons_append, List.nil_append]
    refine .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <|
      .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ <| .cons ⟨_, by type_tac⟩ .nil
  hasL := by
    rw [QuotRed.quotDefEq_eq]
    simp only [QuotRed.liftBinders, VExpr.appN, List.cons_append, List.nil_append,
      List.reverse_cons, List.reverse_nil]
    type_tac
  hasR := by
    rw [QuotRed.quotDefEq_eq]
    simp only [QuotRed.liftBinders, List.cons_append, List.nil_append,
      List.reverse_cons, List.reverse_nil]
    type_tac

/-- In a well-formed environment, the quotient's rule, if present, has typed bodies. -/
theorem WF.quotBodyWF (henv : env.WF) (hdf : env.defeqs quotDefEq) :
    ∃ L R A, quotDefEq.BodyWF env (QuotRed.liftBinders ++ [VExpr.bvar 4]) L R A := by
  have H := henv.ruleKind hdf
  generalize e : quotDefEq = df at H
  cases H with
  | defn ci _ =>
    have := congrArg VDefEq.lhs e
    rw [QuotRed.quotDefEq_eq] at this
    simp [VDefVal.toDefEq, QuotRed.liftBinders] at this
  | quot h1 h2 h3 => exact ⟨_, _, _, VEnv.quotBodyWF h3 h2 h1⟩
  | iota _ hm =>
    subst e
    simp only [VInductDecl.iotaRules, List.mem_map] at hm
    obtain ⟨_, -, hm⟩ := hm
    have := congrArg VDefEq.type hm
    rw [QuotRed.quotDefEq_eq] at this
    simp only [VInductDecl.iotaRule] at this
    exact nomatch (VExpr.foralls_inj' (fun _ _ h => by cases h) (fun _ _ h => by cases h) this).2

theorem _root_.Lean4Lean.VDefEq.BodyWF.mono {env env' : VEnv} (hle : env ≤ env') {df : VDefEq}
    {Bs : List VExpr} {L R A : VExpr} (H : df.BodyWF env Bs L R A) : df.BodyWF env' Bs L R A where
  lhs := H.lhs
  rhs := H.rhs
  type := H.type
  tele := H.tele.mono hle
  hasL := H.hasL.mono hle
  hasR := H.hasR.mono hle

/-- A closed equation typed in an environment where injectivity holds has typed bodies under
its binders. -/
theorem VDefEq.WF.bodyWF {df : VDefEq} (henv : Ordered env) (hI : env.Inj) (H : df.WF env)
    {Bs : List VExpr} {L R A : VExpr} (hl : df.lhs = .lams Bs L) (hr : df.rhs = .lams Bs R)
    (ht : df.type = .foralls Bs A) : df.BodyWF env Bs L R A := by
  obtain ⟨hL, hR⟩ := H
  rw [hl, ht] at hL; rw [hr, ht] at hR
  refine ⟨hl, hr, ht, (IsType.foralls_inv henv (hL.isType henv (Γ := []) trivial)).1, ?_, ?_⟩
  · simpa using hI.lams_body henv (Γ := []) trivial hL
  · simpa using hI.lams_body henv (Γ := []) trivial hR

/-- The environments a recorded block was declared through: `env₀` before it, `envR` with its
types, constructors and recursors as axioms, then its iota rules and its record. -/
structure BlockEnvs (env : VEnv) (d : VInductDecl) (env₀ envT envC envR : VEnv) : Prop where
  wf₀ : env₀.WF
  decl : d.WF env₀
  gen : d.GeneratedWF env₀
  hT : env₀.addConstList d.typeConsts = some envT
  hC : envT.addConstList d.ctorConsts = some envC
  hR : envC.addConstList d.recConsts = some envR
  block : ∃ env₂, (envR.addDefEqList d.iotaRules).addBlock d = some env₂ ∧ env₂ ≤ env

theorem WF.blockEnvs {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl} {t : Nat}
    (h : env.inducts s = some (d, t)) : ∃ env₀ envT envC envR, BlockEnvs env d env₀ envT envC envR := by
  obtain ⟨ds, H⟩ := henv
  induction H with
  | empty => cases h
  | @decl _ env₂ _ env₁ hD hW ih =>
    have IH : env₁.inducts s = some (d, t) → ∃ env₀ envT envC envR,
        BlockEnvs env₂ d env₀ envT envC envR := fun h =>
      let ⟨a, b, c, e, H⟩ := ih h
      ⟨a, b, c, e, { H with block := let ⟨x, y, z⟩ := H.block; ⟨x, y, z.trans hD.le⟩ }⟩
    cases hD with
    | «axiom» _ h1 | «opaque» _ h1 => exact IH (addConst_inducts h1 ▸ h)
    | «def» _ h1 => exact IH (addConst_inducts h1 ▸ h)
    | mutualDef _ h1 _ => exact IH (addConsts_inducts h1 ▸ addDefEqs_inducts ▸ h)
    | «example» => exact IH h
    | quot _ h1 => exact IH (addQuot_inducts h1 ▸ h)
    | @induct _ d' _ hd hg h1 =>
      simp [addInduct, Option.bind_eq_some_iff] at h1
      obtain ⟨envT, hT, envC, hC, envR, hR, hB⟩ := h1
      rcases addBlock_inducts hB h with h | ⟨rfl, -⟩
      · rw [addDefEqList_inducts, addConstList_inducts hR, addConstList_inducts hC,
          addConstList_inducts hT] at h
        exact IH h
      · exact ⟨_, _, _, _, ⟨⟨_, hW⟩, hd, hg, hT, hC, hR, _, hB, .rfl⟩⟩

theorem _root_.Lean4Lean.VExpr.ClosedN.foralls_body :
    ∀ {As : List VExpr} {B : VExpr} {k : Nat}, (VExpr.foralls As B).ClosedN k →
      B.ClosedN (k + As.length)
  | [], _, _, h => h
  | _ :: _, _, _, h => by
    have := VExpr.ClosedN.foralls_body h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem _root_.Lean4Lean.VExpr.ClosedN.appN_args :
    ∀ {as : List VExpr} {f : VExpr} {k : Nat}, (VExpr.appN f as).ClosedN k →
      f.ClosedN k ∧ ∀ a ∈ as, a.ClosedN k
  | [], _, _, h => ⟨h, nofun⟩
  | a :: as, f, k, h => by
    have ⟨h1, h3⟩ := VExpr.ClosedN.appN_args (as := as) (f := .app f a) h
    have ⟨h1', h2⟩ : f.ClosedN k ∧ a.ClosedN k := h1
    exact ⟨h1', fun b hb => (List.mem_cons.1 hb).elim (· ▸ h2) (h3 b)⟩

/-- A constructor's indices mention only its parameters and fields. -/
theorem _root_.Lean4Lean.VConstructor.WF.indices_closed {env : VEnv} {d : VInductDecl}
    {T : VInductiveType} {c : VConstructor} (henv : Ordered env) (H : c.WF env d T) :
    ∀ e ∈ c.indices, e.ClosedN (d.params.length + c.fields.length) := by
  obtain ⟨_, hty⟩ := H.type
  obtain ⟨ps, Ds, hsh, hps, hF, -⟩ := H.shape
  have hcl := hty.closedN henv (Γ := []) trivial
  rw [hsh] at hcl
  have hb := hcl.foralls_body
  rw [List.length_append, hps.length_eq, hF.length, VInductiveType.typeApp_eq] at hb
  simpa using (VExpr.ClosedN.appN_args hb).2

/-- The indices of a recorded block's constructors mention only its parameters and fields. -/
theorem WF.ctor_indices_closed {env : VEnv} (henv : env.WF) {s : Name} {d : VInductDecl}
    {t₀ j : Nat} {c : VConstructor} (hs : env.inducts s = some (d, t₀)) (hc : (j, c) ∈ d.allCtors) :
    ∀ e ∈ c.indices, e.ClosedN (d.params.length + c.fields.length) := by
  obtain ⟨env₀, envT, hwf₀, hd, hT, -⟩ := henv.inducts hs
  obtain ⟨T, hT', hcT⟩ := VInductDecl.mem_allCtors_iff.1 hc
  have hwfT : envT.WF := by
    exact VEnv.WF.addConstList hwf₀ (fun p hp => by
      simp only [VInductDecl.typeConsts, List.mem_map] at hp
      obtain ⟨T, hT, rfl⟩ := hp
      exact (hd.types T hT).1) hT
  exact ((hd.ctors envT hT T (List.mem_of_getElem? hT')).2 c hcT).indices_closed hwfT.ordered

/-- The entries of a telescope over a closed context are closed under it and the entries before
them. -/
theorem IsTele.closedN {env : VEnv} (henv : env.Ordered) {U : Nat} :
    ∀ {Γ As : List VExpr}, env.IsTele U Γ As → CtxClosed Γ →
      ∀ i (A : VExpr), As[i]? = some A → A.ClosedN (Γ.length + i)
  | _, [], _, _, _, _, h => by cases h
  | Γ, _ :: _, .cons ⟨_, hA⟩ h, hΓ, i, A, hi => by
    have hcA := hA.closedN henv hΓ
    cases i with
    | zero => cases hi; exact hcA
    | succ i =>
      have := IsTele.closedN henv h ⟨hΓ, hcA⟩ i A hi
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- The context of a closed telescope, reversed, is closed. -/
theorem IsTele.ctxClosed {env : VEnv} (henv : env.Ordered) {U : Nat} :
    ∀ {Γ As : List VExpr}, env.IsTele U Γ As → CtxClosed Γ → CtxClosed (As.reverse ++ Γ)
  | _, [], _, hΓ => hΓ
  | _, _ :: _, .cons ⟨_, hA⟩ h, hΓ => by
    simpa using IsTele.ctxClosed henv h ⟨hΓ, hA.closedN henv hΓ⟩

/-- A well-formed environment's recorded blocks have closed field types, constructor indices and
type indices. -/
theorem WF.kClosed (henv : env.WF) : LogRel.KClosed env where
  field {s d t q j k c f} hs hq hf := by
    obtain ⟨env₀, envT, hwf₀, hd, hT, -⟩ := henv.inducts hs
    obtain ⟨T, hT', hcT⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
    have hwfT : envT.WF := VEnv.WF.addConstList hwf₀ (fun p hp => by
      simp only [VInductDecl.typeConsts, List.mem_map] at hp
      obtain ⟨T, hT, rfl⟩ := hp
      exact (hd.types T hT).1) hT
    have hc := (hd.ctors envT hT T (List.mem_of_getElem? hT')).2 c hcT
    obtain ⟨_ps, _Ds, -, -, hF, -⟩ := hc.shape
    have hP := hd.params.mono (VEnv.addConstList_le hT)
    have hPc : CtxClosed d.params.reverse := by
      simpa using IsTele.ctxClosed hwfT.ordered hP trivial
    have := IsTele.closedN hwfT.ordered (VInductDecl.FieldsWF.tele hF).1 hPc k f.type (by simp [hf])
    simpa using this
  ctorIdx {s d t q j c e} hs hq he :=
    WF.ctor_indices_closed henv hs (List.mem_of_getElem? hq) e he
  typeIdx {s d t j i T e} hs hT he := by
    obtain ⟨env₀, envT, hwf₀, hd, hT₁, -⟩ := henv.inducts hs
    have hwfT : envT.WF := VEnv.WF.addConstList hwf₀ (fun p hp => by
      simp only [VInductDecl.typeConsts, List.mem_map] at hp
      obtain ⟨T, hT, rfl⟩ := hp
      exact (hd.types T hT).1) hT₁
    have hTW := (hd.ctors envT hT₁ T (List.mem_of_getElem? hT)).1
    have hP := hd.params.mono (VEnv.addConstList_le hT₁)
    have hPc : CtxClosed d.params.reverse := by
      simpa using IsTele.ctxClosed hwfT.ordered hP trivial
    simpa using IsTele.closedN hwfT.ordered hTW.indices hPc i e he

namespace BlockEnvs
variable {env : VEnv} {d : VInductDecl} {env₀ envT envC envR : VEnv}
  (H : BlockEnvs env d env₀ envT envC envR)
include H

theorem envT_wf : envT.WF :=
  VEnv.WF.addConstList H.wf₀ (fun p hp => by
    simp only [VInductDecl.typeConsts, List.mem_map] at hp
    obtain ⟨T, hT, rfl⟩ := hp
    exact (H.decl.types T hT).1) H.hT

theorem envC_wf : envC.WF :=
  VEnv.WF.addConstList H.envT_wf (fun p hp => by
    simp only [VInductDecl.ctorConsts, VInductDecl.ctors, List.mem_map, List.mem_flatten] at hp
    obtain ⟨⟨j, c⟩, ⟨_, ⟨⟨T, i⟩, hm, rfl⟩, hc⟩, rfl⟩ := hp
    obtain ⟨c, hc, ⟨⟩⟩ := List.mem_map.1 hc
    have hT := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hm)
    exact ((H.decl.ctors envT H.hT T (List.mem_append_left _ hT)).2 c hc).type) H.hC

theorem envR_wf : envR.WF :=
  VEnv.WF.addConstList H.envC_wf (H.gen envT envC envR H.hT H.hC H.hR).1 H.hR

theorem envR_le : envR ≤ env :=
  let ⟨_, h1, h2⟩ := H.block
  (VEnv.addDefEqList_le.trans (addBlock_le h1)).trans h2

theorem envR_defeqs : envR.defeqs = env₀.defeqs := by
  rw [addConstList_defeqs' H.hR, addConstList_defeqs' H.hC, addConstList_defeqs' H.hT]

theorem envR_inducts : envR.inducts = env₀.inducts := by
  rw [addConstList_inducts H.hR, addConstList_inducts H.hC, addConstList_inducts H.hT]

/-- The block's iota rules have typed bodies, given injectivity where they are checked. -/
theorem iotaBodyWF (hI : envR.Inj) {q j : Nat} {c : VConstructor}
    (hq : d.allCtors[q]? = some (j, c)) : d.IotaBodyWF env q j c := by
  have hdf := (H.gen envT envC envR H.hT H.hC H.hR).2 _ <| by
    simp only [VInductDecl.iotaRules, List.mem_map]
    exact ⟨((j, c), q), List.mem_zipIdx_iff_getElem?.2 hq, rfl⟩
  exact ⟨_, _, _, (VDefEq.WF.bodyWF H.envR_wf.ordered hI hdf rfl rfl rfl).mono H.envR_le⟩

end BlockEnvs

end VEnv
end Lean4Lean

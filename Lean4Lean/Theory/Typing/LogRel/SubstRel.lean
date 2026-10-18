import Lean4Lean.Theory.Typing.LogRel.Rel
import Lean4Lean.Theory.Typing.LogRel.Rules
import Lean4Lean.Theory.Typing.Telescope

/-!
# Substitutions related along two telescopes

`SubstRel env U Γ σ σ' Δ Δ'`: the substitutions `σ` and `σ'` are related along the contexts `Δ`
and `Δ'`, entry by entry: the entries' instances are joined by a chain (`TyEq`) and the heads are
equal at the left entry's instance. Unlike `Ctx.SubstEq`, it is symmetric and transitive with no
condition on the context, since a chain composes at any sorts; given that `Δ` is a context, it is
a `Ctx.SubstEq` (`SubstRel.substEq`).

`typeTele env n ls` is the telescope of parameters and indices of the type former `n` at levels
`ls`: its recorded block's, or, for the quotient, read off its type.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- Two substitutions related along two contexts, the instances of whose entries are joined. -/
inductive SubstRel : VExpr.Subst → VExpr.Subst → List VExpr → List VExpr → Prop where
  | nil : SubstRel σ σ' [] []
  | cons : SubstRel σ.tail σ'.tail Δ Δ' → TyEq env U Γ (A.subst σ.tail) (A'.subst σ'.tail) →
    env.IsDefEq U Γ σ.head σ'.head (A.subst σ.tail) → SubstRel σ σ' (A :: Δ) (A' :: Δ')

end

/-- The number of leading pi binders of `e`. -/
def forallCount : VExpr → Nat
  | .forallE _ B => forallCount B + 1
  | _ => 0

/-- The parameters and indices of the type former `n` at levels `ls`, as its recorded block
declares them, or else read off its type. -/
def typeTele (env : VEnv) (n : Name) (ls : List VLevel) : List VExpr :=
  match env.inducts n with
  | some (d, t) => (d.params ++ ((d.types[t]?).map (·.indices)).getD []).map (·.instL ls)
  | none => match env.constants n with
    | some ci => (VEnv.peelForalls (forallCount ci.type) (ci.type.instL ls)).1
    | none => []

theorem _root_.Lean4Lean.VExpr.Subst.consList_shift (σ : VExpr.Subst) :
    ∀ (bs : List VExpr) (i : Nat), σ.consList bs (i + bs.length) = σ i
  | [], _ => rfl
  | b :: bs, i => by
    have := VExpr.Subst.consList_shift (σ.cons b) bs (i+1)
    rw [Nat.add_right_comm] at this
    exact this

/-- The indices of the constructor `c` of the type former `n` at levels `ls`, for the parameters
and fields `as`. -/
def ctorIdx (env : VEnv) (n c : Name) (ls : List VLevel) (as : List VExpr) : List VExpr :=
  match env.inducts n with
  | some (d, t) => match (d.types[t]?).bind (·.ctors.find? (·.name == c)) with
    | some cv => cv.indices.map fun e => (e.instL ls).subst (VExpr.Subst.dflt.consList as)
    | none => []
  | none => []

theorem typeTele_block {env : VEnv} {n : Name} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    (hs : env.inducts n = some (d, t)) (ht : d.types[t]? = some T) (ls : List VLevel) :
    typeTele env n ls = (d.params ++ T.indices).map (·.instL ls) := by
  simp [typeTele, hs, ht]

/-- A recorded type's parameters and indices are a context, closed, at its block's universes. -/
theorem _root_.Lean4Lean.VEnv.WF.blockTele_onCtx {env : VEnv} (henv : env.WF) {n : Name}
    {d : VInductDecl} {t : Nat} {T : VInductiveType} (hs : env.inducts n = some (d, t))
    (ht : d.types[t]? = some T) : OnCtx (d.params ++ T.indices).reverse (env.IsType d.uvars) := by
  obtain ⟨env₀, env₂, -, hd, hadd, hle, T', hT, -⟩ := henv.inducts_block hs
  rw [ht] at hT; cases hT
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at hadd
  obtain ⟨envT, hT', envC, hC, envR, hR, hB⟩ := hadd
  have hle' : envT ≤ env :=
    (VEnv.addConstList_le hC).trans <| (VEnv.addConstList_le hR).trans <|
      VEnv.addDefEqList_le.trans ((VEnv.addBlock_le hB).trans hle)
  have hI := ((hd.ctors envT hT') T (List.mem_append_left _ (List.mem_of_getElem? ht))).1.indices
  have hP := hd.params.mono ((VEnv.addConstList_le hT').trans hle')
  simpa using (hP.append (by simpa using hI.mono hle')).onCtx (Γ := []) trivial

/-- A recorded type former's telescope is a context, at any well-formed levels. -/
theorem _root_.Lean4Lean.VEnv.WF.typeTele_onCtx {env : VEnv} (henv : env.WF) {n : Name}
    {d : VInductDecl} {t : Nat} {U : Nat} {ls : List VLevel} (hs : env.inducts n = some (d, t))
    (hls : ∀ l ∈ ls, l.WF U) : OnCtx (typeTele env n ls).reverse (env.IsType U) := by
  obtain ⟨-, -, -, -, -, -, T, hT, -⟩ := henv.inducts_block hs
  rw [typeTele_block hs hT, ← List.map_reverse]
  exact (henv.blockTele_onCtx hs hT).instL hls

theorem _root_.Lean4Lean.OnCtx.of_append {P : List VExpr → VExpr → Prop} :
    ∀ {Δ₁ Δ₂ : List VExpr}, OnCtx (Δ₁ ++ Δ₂) P → OnCtx Δ₂ P
  | [], _, h => h
  | _ :: Δ₁, _, h => OnCtx.of_append (Δ₁ := Δ₁) h.1

namespace SubstRel
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem length : SubstRel env U Γ σ σ' Δ Δ' → Δ.length = Δ'.length
  | .nil => rfl
  | .cons h _ _ => congrArg (· + 1) h.length

theorem symm : SubstRel env U Γ σ σ' Δ Δ' → SubstRel env U Γ σ' σ Δ' Δ
  | .nil => .nil
  | .cons h hA ha => .cons h.symm hA.symm (hA.defeqDF ha.symm)

theorem trans : SubstRel env U Γ σ₁ σ₂ Δ₁ Δ₂ → SubstRel env U Γ σ₂ σ₃ Δ₂ Δ₃ →
    SubstRel env U Γ σ₁ σ₃ Δ₁ Δ₃
  | .nil, .nil => .nil
  | .cons h hA ha, .cons h' hA' ha' =>
    .cons (h.trans h') (hA.trans hA') (ha.trans (hA.symm.defeqDF ha'))

theorem left : SubstRel env U Γ σ σ' Δ Δ' → SubstRel env U Γ σ σ Δ Δ := fun h =>
  h.trans h.symm

/-- The last entries of the contexts relate the substitutions with that many heads dropped. -/
theorem drop : ∀ {Δ₁ Δ₁' : List VExpr} {σ σ'}, Δ₁.length = Δ₁'.length →
    SubstRel env U Γ σ σ' (Δ₁ ++ Δ₂) (Δ₁' ++ Δ₂') →
    SubstRel env U Γ (fun i => σ (i + Δ₁.length)) (fun i => σ' (i + Δ₁.length)) Δ₂ Δ₂'
  | [], [], _, _, _, h => h
  | _ :: Δ₁, _ :: Δ₁', σ, σ', hl, .cons h _ _ => by
    have := drop (σ := σ.tail) (σ' := σ'.tail) (Nat.succ.inj hl) h
    simpa [VExpr.Subst.tail, Nat.add_assoc, Nat.add_comm 1] using this

/-- The first `k` entries of two telescopes relate the first `k` values. -/
theorem take {σ σ' : VExpr.Subst} {as bs Δ Δ' : List VExpr} (k : Nat)
    (hl : as.length = Δ.length) (hl' : bs.length = Δ'.length)
    (H : SubstRel env U Γ (σ.consList as) (σ'.consList bs) Δ.reverse Δ'.reverse) :
    SubstRel env U Γ (σ.consList (as.take k)) (σ'.consList (bs.take k))
      (Δ.take k).reverse (Δ'.take k).reverse := by
  have hΔ : Δ.length = Δ'.length := by simpa using H.length
  rw [← List.take_append_drop k Δ, ← List.take_append_drop k Δ', List.reverse_append,
    List.reverse_append, ← List.take_append_drop k as, ← List.take_append_drop k bs,
    VExpr.Subst.consList_append, VExpr.Subst.consList_append] at H
  have := H.drop (by simp [hΔ])
  have e1 : (Δ.drop k).reverse.length = (as.drop k).length := by simp [hl]
  have e2 : (Δ.drop k).reverse.length = (bs.drop k).length := by simp [hl', hΔ]
  have f1 : (fun i => (σ.consList (as.take k)).consList (as.drop k) (i + (Δ.drop k).reverse.length))
      = σ.consList (as.take k) := by
    funext i; rw [e1, VExpr.Subst.consList_shift]
  have f2 : (fun i => (σ'.consList (bs.take k)).consList (bs.drop k) (i + (Δ.drop k).reverse.length))
      = σ'.consList (bs.take k) := by
    funext i; rw [e2, VExpr.Subst.consList_shift]
  rwa [f1, f2] at this

/-- A `Ctx.SubstEq` along a context at levels `ls` relates the substitutions along it and along
the same context at equivalent levels. -/
theorem of_substEq (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) {ls ls' : List VLevel}
    {U' : Nat} (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ {Δ : List VExpr} {σ σ'}, OnCtx Δ (env.IsType U') →
      VEnv.Ctx.SubstEq env U Γ σ σ' (Δ.map (·.instL ls)) →
      SubstRel env U Γ σ σ' (Δ.map (·.instL ls)) (Δ.map (·.instL ls'))
  | [], _, _, _, _ => .nil
  | _ :: Δ, _, _, ⟨hΔ, _, hA⟩, .cons W _ ha =>
    .cons (of_substEq henv hΓ hls hls' heq hΔ W)
      (.base ((hA.instL_r henv hΔ hls hls' heq).substDF henv (hΔ.instL hls) hΓ W)) ha

/-- Given that `Δ` is a context, related substitutions are a `Ctx.SubstEq`. -/
theorem substEq : ∀ {Δ Δ' : List VExpr} {σ σ'}, SubstRel env U Γ σ σ' Δ Δ' →
    OnCtx Δ (env.IsType U) → VEnv.Ctx.SubstEq env U Γ σ σ' Δ
  | [], _, _, _, .nil, _ => .nil
  | _ :: _, _ :: _, _, _, .cons h _ ha, ⟨hΔ, _, hA⟩ => .cons (substEq h hΔ) hA ha

end SubstRel

end LogRel
end Lean4Lean

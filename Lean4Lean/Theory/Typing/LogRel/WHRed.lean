import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Telescope

/-!
# Head reduction for the logical relation

A step (`Step env U Γ`) is read off the environment's own rules: beta, a definition's unfolding
(`delta`), the quotient's rule, a projection of a constructor application (`projIota`), and a
recursor's iota rule on a constructor application at a non-propositional instance of its block
(`iota`), under applications, projections and major premises. These steps check nothing: the
constructor's parameters and levels, the indices and the quotient's type and relation are left to
typed reduction, which carries each step's definitional equality (`TRed`).

At a propositional instance of a block with large elimination, the recursor reduces on any major
premise (`kIota`) to the iota rule's right-hand side at fields the context provides: the fields
that are indices are read off the indices, the others are proofs typed in `Γ`, and the constructor's
indices at those fields must be the major premise's (`KFields`). Likewise `Quot.lift` of a
quotient that is a proposition reduces on any major premise to the function at a term of the
quotient's type (`kQuot`). These steps depend on the context: a proof the reduct needs may exist
only in an extension of it. Which proofs is a choice (`kFieldsOf`, `quotWit`), so steps are
deterministic (`Step.determ`). The logical relation is over a fixed context, so steps are never
weakened or substituted.

A term is neutral (`Neutral`) when it is a variable, or a projection, application or major premise
of a neutral term, or a recursor or `Quot.lift` at a propositional instance: its only steps are
`kIota` and `kQuot` ones inside it (`Neutral.kStep`).
-/

namespace Lean4Lean
open VExpr

@[elab_as_elim] private theorem snocInd {α} {motive : List α → Prop} (nil : motive [])
    (append_singleton : ∀ as a, motive as → motive (as ++ [a])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a l ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

theorem appN_eq_app {e : VExpr} (he : ∀ f a, e ≠ .app f a) :
    ∀ {as : List VExpr} {f a}, e.appN as = .app f a ↔ ∃ as', as = as' ++ [a] ∧ f = e.appN as'
  | as, f, a => by
    induction as using snocInd with
    | nil => simp [he]
    | append_singleton as b _ =>
      rw [appN_append]; simp only [appN, app.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨_, rfl, rfl⟩
      · rintro ⟨as', h, rfl⟩
        obtain ⟨rfl, h⟩ := List.append_inj' h rfl
        simp at h; exact ⟨rfl, h⟩

/-- A term that is not an application is the head of its spine. -/
def NotApp (e : VExpr) : Prop := ∀ f a, e ≠ .app f a

theorem appN_inj (he : NotApp e) (he' : NotApp e') :
    ∀ {as bs : List VExpr}, e.appN as = e'.appN bs → e = e' ∧ as = bs
  | as, bs, h => by
    induction as using snocInd generalizing bs with
    | nil =>
      induction bs using snocInd with
      | nil => exact ⟨h, rfl⟩
      | append_singleton bs b _ => rw [appN_append] at h; exact (he _ _ h).elim
    | append_singleton as a ih =>
      induction bs using snocInd with
      | nil => rw [appN_append] at h; exact (he' _ _ h.symm).elim
      | append_singleton bs b _ =>
        simp only [appN_append, appN, app.injEq] at h
        obtain ⟨rfl, rfl⟩ := ih _ h.1
        exact ⟨rfl, by rw [h.2]⟩

theorem appN_const_inj :
    ∀ {as bs : List VExpr}, (VExpr.const c ls).appN as = (VExpr.const c' ls').appN bs →
      c = c' ∧ ls = ls' ∧ as = bs
  | as, bs, h => by
    induction as using snocInd generalizing bs with
    | nil =>
      induction bs using snocInd with
      | nil => cases h; exact ⟨rfl, rfl, rfl⟩
      | append_singleton bs b _ => rw [appN_append] at h; cases h
    | append_singleton as a ih =>
      induction bs using snocInd with
      | nil => rw [appN_append] at h; cases h
      | append_singleton bs b _ =>
        simp only [appN_append, appN, app.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := ih _ h.1
        exact ⟨rfl, rfl, by rw [h.2]⟩

theorem appN_const_ne_lam : (VExpr.const c ls).appN as ≠ .lam A e :=
  appN_ne_of_ne (P := (· ≠ .lam A e)) (fun _ _ => nofun) as nofun

theorem appN_const_ne_proj : (VExpr.const c ls).appN as ≠ .proj s k e :=
  appN_ne_of_ne (P := (· ≠ .proj s k e)) (fun _ _ => nofun) as nofun


namespace VInductDecl
variable (d : VInductDecl)

/-- The block's levels as its recursor at levels `recLs` sees them: after the motive's, when it
has one. -/
def blockLevels (recLs : List VLevel) : List VLevel := if d.largeElim then recLs.drop 1 else recLs

/-- At levels `ls`, the block's types are propositions. -/
def PropAt (ls : List VLevel) : Prop := d.level.inst ls ≈ .zero

/-- The number of arguments the recursor of `T` takes before its major premise. -/
def majorIdx (T : VInductiveType) : Nat :=
  d.params.length + (d.allTypes.length + d.allCtors.length) + T.indices.length

/-- The number of parameters a constructor of `T` is applied to: the occurrence's, for an
auxiliary type. -/
def ctorParams (T : VInductiveType) : Nat := (T.nested.map (·.args.length)).getD d.params.length

/-- The right-hand side of the iota rule for the `q`th constructor `c`, of the `j`th type, with the
recursors at `recLs`: a closed lambda over the recursor's arguments before the indices and over
the constructor's fields. -/
noncomputable def iotaRhs (recLs : List VLevel) (q j : Nat) (c : VConstructor) : VExpr :=
  (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).rhs.instL recLs

/-- At block levels `ls`, the `j`th type is a structure with eta whose recursor eliminates into any
sort, with its projections allowed: its recursor reduces on any major premise, at the major
premise's projections (`Step.etaIota`), as structure eta and iota make it equal to. -/
def EtaRec (j : Nat) (ls : List VLevel) : Prop :=
  ∃ T c, d.types[j]? = some T ∧ T.ctors = [c] ∧ T.indices = [] ∧ d.isRec = false ∧
    d.largeElim = true ∧ ∀ k < c.fields.length, d.ProjAllowed c ls k

omit d in
theorem EtaRec.indices {d : VInductDecl} {j : Nat} {ls : List VLevel} {T : VInductiveType}
    (h : d.EtaRec j ls) (hT : d.types[j]? = some T) : T.indices = [] := by
  obtain ⟨T', c, h1, -, h3, -⟩ := h; cases hT.symm.trans h1; exact h3

omit d in
theorem allTypes_getElem? {d : VInductDecl} {t : Nat}
    {T : VInductiveType} (h : d.types[t]? = some T) : d.allTypes[t]? = some T := by
  simp [VInductDecl.allTypes, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

/-- `e` is the variable `i`. -/
def _root_.Lean4Lean.VExpr.isBVar (i : Nat) : VExpr → Bool
  | .bvar j => i == j
  | _ => false

/-- The position among `c`'s indices of its `k`th field, if the field is one of them. -/
def fieldIdx (c : VConstructor) (k : Nat) : Option Nat :=
  c.indices.findIdx? (VExpr.isBVar (c.fields.length - 1 - k))

/-- The constructor's indices at the parameters `ps` and fields `fs`, at block levels `lsB`. -/
def idxAt (c : VConstructor) (lsB : List VLevel) (ps fs : List VExpr) : List VExpr :=
  (c.indices.map (·.instL lsB)).map (·.subst (VExpr.Subst.id.consList (ps ++ fs)))

end VInductDecl

namespace LogRel

/-- `Quot.lift` at levels `ls` is about a quotient that is a proposition. -/
def QuotProp (ls : List VLevel) : Prop := ∃ u v, ls = [u, v] ∧ u ≈ .zero

/-- Fields `fs` of the single constructor `c` of `T`, at block levels `lsB` and parameters `ps`, for
a K-like reduction of a recursor at indices `is`: a field that is an index is read off the indices,
every field is typed at its declared type, and the constructor's indices at the fields are `is`. -/
structure KFields (env : VEnv) (U : Nat) (Γ : List VExpr) (T : VInductiveType) (c : VConstructor)
    (lsB : List VLevel) (ps is fs : List VExpr) : Prop where
  idx : ∀ k i, k < c.fields.length → VInductDecl.fieldIdx c k = some i → fs[k]? = is[i]?
  fields : ∀ k (h : k < fs.length) (h' : k < c.fields.length),
    env.HasType U Γ fs[k] ((c.fields[k].type.instL lsB).subst
      (VExpr.Subst.id.consList (ps ++ fs.take k)))
  index : ∀ i (h : i < (VInductDecl.idxAt c lsB ps fs).length) (h' : i < is.length)
    (h'' : i < T.indices.length),
    env.IsDefEq U Γ (VInductDecl.idxAt c lsB ps fs)[i] is[i] ((T.indices[i].instL lsB).subst
      (VExpr.Subst.id.consList (ps ++ (VInductDecl.idxAt c lsB ps fs).take i)))

/-- Some fields for a K-like reduction, if the context provides any. -/
noncomputable def kFieldsOf (env : VEnv) (U : Nat) (Γ : List VExpr) (T : VInductiveType)
    (c : VConstructor) (lsB : List VLevel) (ps is : List VExpr) : List VExpr :=
  open Classical in
  if h : ∃ fs, fs.length = c.fields.length ∧ KFields env U Γ T c lsB ps is fs then
    Classical.choose h
  else []

theorem kFieldsOf_spec {env : VEnv} {U : Nat} {Γ : List VExpr} {T : VInductiveType}
    {c : VConstructor} {lsB : List VLevel} {ps is fs : List VExpr}
    (h1 : fs.length = c.fields.length) (h2 : KFields env U Γ T c lsB ps is fs) :
    (kFieldsOf env U Γ T c lsB ps is).length = c.fields.length ∧
      KFields env U Γ T c lsB ps is (kFieldsOf env U Γ T c lsB ps is) := by
  have h : ∃ fs, fs.length = c.fields.length ∧ KFields env U Γ T c lsB ps is fs := ⟨_, h1, h2⟩
  simp only [kFieldsOf, dif_pos h]; exact Classical.choose_spec h

/-- Some term of type `α`, if the context provides one. -/
noncomputable def quotWit (env : VEnv) (U : Nat) (Γ : List VExpr) (α : VExpr) : VExpr :=
  open Classical in
  if h : ∃ a, env.HasType U Γ a α then Classical.choose h else .sort .zero

theorem quotWit_spec {env : VEnv} {U : Nat} {Γ : List VExpr} {α a : VExpr}
    (h : env.HasType U Γ a α) : env.HasType U Γ (quotWit env U Γ α) α := by
  have h' : ∃ a, env.HasType U Γ a α := ⟨_, h⟩
  simp only [quotWit, dif_pos h']; exact Classical.choose_spec h'

/-! ### Steps -/

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- A head reduction step. -/
inductive Step : VExpr → VExpr → Prop where
  | app : Step f f' → Step (.app f a) (.app f' a)
  | beta : Step (.app (.lam A e) a) (e.inst a)
  | proj : Step e e' → Step (.proj s k e) (.proj s k e')
  | projIota : env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    As.length = d.params.length → fs.length = c.fields.length → fs[k]? = some a →
    Step (.proj s k ((VExpr.const c.name ls).appN (As ++ fs))) a
  | delta : env.defeqs df → df.lhs = .const n (VLevel.params df.uvars) → ls.length = df.uvars →
    Step (.const n ls) (df.rhs.instL ls)
  | quot : env.defeqs quotDefEq → ¬QuotProp ls →
    Step (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h])
      ((VExpr.const ``Quot.mk ls').appN [α', r', a])) (.app f a)
  | quotMajor : env.defeqs quotDefEq → ¬QuotProp ls → Step e e' →
    Step (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
      (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e')
  | major : env.inducts s = some (d, t) → d.allTypes[j]? = some T →
    ¬d.PropAt (d.blockLevels recLs) → ¬d.EtaRec j (d.blockLevels recLs) →
    args.length = d.majorIdx T → Step e e' →
    Step (.app ((VExpr.const (d.recName j) recLs).appN args) e)
      (.app ((VExpr.const (d.recName j) recLs).appN args) e')
  | iota : env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    d.allTypes[j]? = some T → ¬d.PropAt (d.blockLevels recLs) →
    ¬d.EtaRec j (d.blockLevels recLs) → ps.length = d.params.length → ms.length = d.allTypes.length + d.allCtors.length →
    is.length = T.indices.length → qs.length = d.ctorParams T → fs.length = c.fields.length →
    Step (.app ((VExpr.const (d.recName j) recLs).appN (ps ++ ms ++ is))
        ((VExpr.const c.name ls').appN (qs ++ fs)))
      ((d.iotaRhs recLs q j c).appN (ps ++ ms ++ fs))
  | etaIota : env.inducts T.name = some (d, j) → d.types[j]? = some T → T.ctors = [c] →
    d.allCtors[q]? = some (j, c) → ¬d.PropAt (d.blockLevels recLs) →
    d.EtaRec j (d.blockLevels recLs) → ps.length = d.params.length →
    ms.length = d.allTypes.length + d.allCtors.length →
    Step (.app ((VExpr.const (d.recName j) recLs).appN (ps ++ ms)) e)
      ((d.iotaRhs recLs q j c).appN (ps ++ ms ++ VExpr.projs T.name c.fields.length e))
  | kIota : env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    d.allTypes[j]? = some T → T.ctors = [c] → d.PropAt (d.blockLevels recLs) →
    d.largeElim = true → ps.length = d.params.length →
    ms.length = d.allTypes.length + d.allCtors.length → is.length = T.indices.length →
    (kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is).length = c.fields.length →
    KFields env U Γ T c (d.recLevels.map (·.inst recLs)) ps is
      (kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is) →
    Step (.app ((VExpr.const (d.recName j) recLs).appN (ps ++ ms ++ is)) e)
      ((d.iotaRhs recLs q j c).appN
        (ps ++ ms ++ kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is))
  | kQuot : env.defeqs quotDefEq → ls = [u, v] → u ≈ .zero →
    env.HasType U Γ (quotWit env U Γ α) α →
    Step (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e) (.app f (quotWit env U Γ α))

/-- A term in weak head normal form takes no step. -/
def WHNF (e : VExpr) : Prop := ∀ e', ¬Step env U Γ e e'

end

/-- A name that heads no step: no definition unfolds it, it is not `Quot.lift` while the quotient's
rule is present, and it names no recursor of a recorded block. -/
structure Inert (env : VEnv) (n : Name) : Prop where
  delta : env.defeqs df → df.lhs ≠ .const n us
  quot : env.defeqs quotDefEq → n ≠ ``Quot.lift
  notRec : env.inducts s = some (d, t) → j < d.allTypes.length → n ≠ d.recName j

/-- The rules' names are unique: one definition unfolds a constant, a recursor belongs to one
block, a type's constructors have distinct names, constructors and `Quot.mk` head no step, and
recursors and `Quot.lift` do not unfold. A well-formed environment's are (`VEnv.WF.stepUniq`). -/
structure StepUniq (env : VEnv) : Prop where
  delta : env.defeqs df₁ → env.defeqs df₂ → df₁.lhs = .const n us₁ → df₂.lhs = .const n us₂ →
    df₁ = df₂
  recName : env.inducts s = some (d, t) → env.inducts s' = some (d', t') → j < d.allTypes.length →
    j' < d'.allTypes.length → d.recName j = d'.recName j' → d = d' ∧ j = j'
  ctor {q q' j : Nat} {c c' : VConstructor} : env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    d.allCtors[q']? = some (j, c') → c.name = c'.name → q = q'
  ctorInert : env.inducts s = some (d, t) → (j, c) ∈ d.allCtors → Inert env c.name
  quotMk : env.defeqs quotDefEq → Inert env ``Quot.mk
  recDelta : env.inducts s = some (d, t) → j < d.allTypes.length → env.defeqs df →
    df.lhs ≠ .const (d.recName j) us
  recQuot : env.defeqs quotDefEq → env.inducts s = some (d, t) → j < d.allTypes.length →
    d.recName j ≠ ``Quot.lift
  quotDelta : env.defeqs quotDefEq → env.defeqs df → df.lhs ≠ .const ``Quot.lift us
  iota : env.inducts s = some (d, t) → df ∈ d.iotaRules → env.defeqs df

/-- The types `KFields` checks against are closed: a constructor's field types under the
parameters and the fields before it, its indices under the parameters and its fields, and a type's
indices under the parameters and the indices before them. A well-formed environment's are. -/
structure KClosed (env : VEnv) : Prop where
  field {s : Name} {d : VInductDecl} {t q j k : Nat} {c : VConstructor} {f : VField} :
    env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) → c.fields[k]? = some f →
    f.type.ClosedN (d.params.length + k)
  ctorIdx {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor} {e : VExpr} :
    env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) → e ∈ c.indices →
    e.ClosedN (d.params.length + c.fields.length)
  typeIdx {s : Name} {d : VInductDecl} {t j i : Nat} {T : VInductiveType} {e : VExpr} :
    env.inducts s = some (d, t) → d.allTypes[j]? = some T → T.indices[i]? = some e →
    e.ClosedN (d.params.length + i)

theorem _root_.Lean4Lean.VExpr.ClosedN.subst_consList_subst {e : VExpr} {as : List VExpr}
    (he : e.ClosedN as.length) (σ : VExpr.Subst) :
    (e.subst (VExpr.Subst.id.consList as)).subst σ =
      e.subst (VExpr.Subst.id.consList (as.map (·.subst σ))) := by
  rw [VExpr.subst_subst, VExpr.Subst.consList_comp]
  refine he.subst_congr fun i hi => ?_
  rw [VExpr.Subst.consList_apply, VExpr.Subst.consList_apply, dif_pos (by simpa using hi),
    dif_pos (by simpa using hi)]
  try simp [← List.map_reverse]

theorem _root_.Lean4Lean.VExpr.ClosedN.inst_consList_subst {e : VExpr} {as : List VExpr}
    (he : e.ClosedN as.length) (a : VExpr) (k : Nat) :
    (e.subst (VExpr.Subst.id.consList as)).inst a k =
      e.subst (VExpr.Subst.id.consList (as.map (·.inst a k))) := by
  simp only [VExpr.instN_eq]; exact he.subst_consList_subst _

theorem _root_.Lean4Lean.VExpr.ClosedN.lift'_consList_subst {e : VExpr} {as : List VExpr}
    (he : e.ClosedN as.length) (ρ : Lift) :
    (e.subst (VExpr.Subst.id.consList as)).lift' ρ =
      e.subst (VExpr.Subst.id.consList (as.map (·.lift' ρ))) := by
  rw [VExpr.lift'_subst]
  refine he.subst_congr fun i hi => ?_
  simp only [VExpr.Subst.lift_r]
  rw [VExpr.Subst.consList_apply, VExpr.Subst.consList_apply, dif_pos (by simpa using hi),
    dif_pos (by simpa using hi)]
  try simp [← List.map_reverse]


namespace Step
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem appN_snoc (e : VExpr) (as : List VExpr) (a : VExpr) :
    e.appN (as ++ [a]) = .app (e.appN as) a := by rw [appN_append]; rfl

/-- A constant applied to arguments steps only if it unfolds, or it is `Quot.lift` or a recursor
applied past its major premise. -/
theorem appN_const : ∀ {as : List VExpr} {e'},
    Step env U Γ ((VExpr.const h ls).appN as) e' →
    (∃ df us, env.defeqs df ∧ df.lhs = .const h us) ∨
    (env.defeqs quotDefEq ∧ h = ``Quot.lift ∧ 6 ≤ as.length) ∨
    (∃ s d t j T, env.inducts s = some (d, t) ∧ d.allTypes[j]? = some T ∧ h = d.recName j ∧
      d.majorIdx T + 1 ≤ as.length) := by
  intro as
  induction as using snocInd with
  | nil =>
    intro e' H
    generalize hx : VExpr.const h ls = x at H
    cases H <;> cases hx
    exact .inl ⟨_, _, ‹_›, ‹_›⟩
  | append_singleton as a ih =>
    intro e' H
    rw [appN_snoc] at H
    generalize hx : VExpr.app _ a = x at H
    cases H with
    | app r1 =>
      cases hx
      rcases ih r1 with h1 | ⟨h1, h2, h3⟩ | ⟨s, d, t, j, T, h1, h2, h3, h4⟩
      · exact .inl h1
      · exact .inr (.inl ⟨h1, h2, by simp; omega⟩)
      · exact .inr (.inr ⟨s, d, t, j, T, h1, h2, h3, by simp; omega⟩)
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inl ⟨r1, rfl, by simp⟩)
    | quotMajor r1 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inl ⟨r1, rfl, by simp⟩)
    | major r1 r2 _ _ r4 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inr ⟨_, _, _, _, _, r1, r2, rfl, by simp; omega⟩)
    | iota r1 r2 r3 _ _ r5 r6 r7 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inr ⟨_, _, _, _, _, r1, r3, rfl, by simp [VInductDecl.majorIdx]; omega⟩)
    | kIota r1 _ r3 _ _ _ r7 r8 r9 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inr ⟨_, _, _, _, _, r1, r3, rfl, by
        simp [VInductDecl.majorIdx, r7, r8, r9]; omega⟩)
    | etaIota r1 r2 _ _ _ r6 r7 r8 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inr ⟨_, _, _, _, _, r1, VInductDecl.allTypes_getElem? r2, rfl, by
        simp [VInductDecl.majorIdx, r7, r8, r6.indices r2]; omega⟩)
    | kQuot r1 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr (.inl ⟨r1, rfl, by simp⟩)
    | _ => cases hx

theorem _root_.Lean4Lean.LogRel.Inert.whnf (hn : Inert env h) : WHNF env U Γ ((VExpr.const h ls).appN as) := by
  intro e' H
  rcases appN_const H with ⟨df, us, h1, h2⟩ | ⟨h1, rfl, -⟩ | ⟨s, d, t, j, T, h1, h2, rfl, -⟩
  · exact hn.delta h1 h2
  · exact hn.quot h1 rfl
  · exact hn.notRec h1 (List.getElem?_eq_some_iff.1 h2).1 rfl

theorem lam_whnf : WHNF env U Γ (.lam A e) := fun _ H => nomatch H


variable (hU : StepUniq env)
include hU

theorem recName_inj (h1 : env.inducts s = some (d, t)) (h2 : d.allTypes[j]? = some T)
    (h1' : env.inducts s' = some (d', t')) (h2' : d'.allTypes[j']? = some T')
    (h : d.recName j = d'.recName j') : d = d' ∧ j = j' ∧ T = T' := by
  obtain ⟨rfl, rfl⟩ := hU.recName h1 h1' (List.getElem?_eq_some_iff.1 h2).1
    (List.getElem?_eq_some_iff.1 h2').1 h
  exact ⟨rfl, rfl, Option.some.inj (h2.symm.trans h2')⟩

/-- A recursor applied up to its major premise takes no step. -/
theorem recHead_whnf (h1 : env.inducts s = some (d, t)) (h2 : d.allTypes[j]? = some T)
    (h3 : args.length = d.majorIdx T) :
    WHNF env U Γ ((VExpr.const (d.recName j) recLs).appN args) := by
  intro e' H
  rcases appN_const H with ⟨df, us, r1, r2⟩ | ⟨r1, r2, -⟩ | ⟨s', d', t', j', T', r1, r2, r3, r4⟩
  · exact hU.recDelta h1 (List.getElem?_eq_some_iff.1 h2).1 r1 r2
  · exact hU.recQuot r1 h1 (List.getElem?_eq_some_iff.1 h2).1 r2
  · obtain ⟨rfl, rfl, rfl⟩ := recName_inj hU h1 h2 r1 r2 r3; omega

/-- `Quot.lift` applied up to its major premise takes no step. -/
theorem quotHead_whnf (h1 : env.defeqs quotDefEq) :
    WHNF env U Γ ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) := by
  intro e' H
  rcases appN_const H with ⟨df, us, r1, r2⟩ | ⟨-, -, r3⟩ | ⟨s', d', t', j', T', r1, r2, r3, -⟩
  · exact hU.quotDelta h1 r1 r2
  · simp at r3
  · exact hU.recQuot h1 r1 (List.getElem?_eq_some_iff.1 r2).1 r3.symm

theorem ctor_whnf {T : VInductiveType} {c : VConstructor} {j : Nat} (h1 : env.inducts s = some (d, t))
    (h2 : d.allTypes[j]? = some T)
    (h3 : c ∈ T.ctors) : WHNF env U Γ ((VExpr.const c.name ls).appN as) :=
  (hU.ctorInert h1 (VInductDecl.mem_allCtors_iff.2 ⟨_, h2, h3⟩)).whnf

theorem ctor_whnf' {c : VConstructor} {q j : Nat} (h1 : env.inducts s = some (d, t))
    (h2 : d.allCtors[q]? = some (j, c)) :
    WHNF env U Γ ((VExpr.const c.name ls).appN as) :=
  (hU.ctorInert h1 (List.mem_of_getElem? h2)).whnf

theorem quotMk_whnf (h1 : env.defeqs quotDefEq) :
    WHNF env U Γ ((VExpr.const ``Quot.mk ls).appN as) := (hU.quotMk h1).whnf

omit hU in
theorem allTypes_of_allCtors {d : VInductDecl} {q j : Nat} {c : VConstructor}
    (h : d.allCtors[q]? = some (j, c)) : ∃ T, d.allTypes[j]? = some T ∧ c ∈ T.ctors :=
  VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? h)

/-- Steps are deterministic. -/
theorem determ (H1 : Step env U Γ e e₁) (H2 : Step env U Γ e e₂) :
    e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 =>
      cases hx
      cases ih r1; rfl
    | beta => cases hx; cases lam_whnf _ l1
    | quot r1 => injection hx with hx; subst hx; cases quotHead_whnf hU r1 _ l1
    | quotMajor r1 => injection hx with hx; subst hx; cases quotHead_whnf hU r1 _ l1
    | kQuot r1 => injection hx with hx; subst hx; cases quotHead_whnf hU r1 _ l1
    | major r1 r2 _ _ r4 => injection hx with hx; subst hx; cases recHead_whnf hU r1 r2 r4 _ l1
    | iota r1 r2 r3 _ _ r5 r6 r7 =>
      injection hx with hx; subst hx
      obtain ⟨T, hT, -⟩ := allTypes_of_allCtors r2
      cases r3.symm.trans hT
      cases recHead_whnf hU r1 hT (by simp [VInductDecl.majorIdx, r5, r6, r7]; omega) _ l1
    | kIota r1 _ r3 _ _ _ r7 r8 r9 =>
      injection hx with hx; subst hx
      cases recHead_whnf hU r1 r3 (by simp [VInductDecl.majorIdx, r7, r8, r9]; omega) _ l1
    | etaIota r1 r2 _ _ _ r6 r7 r8 =>
      injection hx with hx; subst hx
      cases recHead_whnf hU r1 (VInductDecl.allTypes_getElem? r2)
        (by simp [VInductDecl.majorIdx, r7, r8, r6.indices r2]) _ l1
    | _ => cases hx
  | beta =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => cases hx; cases lam_whnf _ r1
    | beta => cases hx; rfl
    | _ => first | cases hx | (injection hx with hx; cases appN_const_ne_lam hx.symm)
  | proj l1 ih =>
    generalize hx : VExpr.proj _ _ _ = x at H2
    cases H2 with
    | proj r1 =>
      cases hx
      cases ih r1; rfl
    | projIota r1 r2 r3 =>
      injection hx with _ _ hx; subst hx
      cases ctor_whnf hU r1 (VInductDecl.allTypes_getElem? r2) (by simp [r3]) _ l1
    | _ => cases hx
  | projIota l1 l2 l3 l4 l5 l6 =>
    generalize hx : VExpr.proj _ _ _ = x at H2
    cases H2 with
    | proj r1 =>
      injection hx with _ _ hx; subst hx
      cases ctor_whnf hU l1 (VInductDecl.allTypes_getElem? l2) (by simp [l3]) _ r1
    | projIota r1 r2 r3 r4 r5 r6 =>
      injection hx with hs hk he; subst hs hk
      cases l1.symm.trans r1; cases l2.symm.trans r2; cases l3.symm.trans r3
      obtain ⟨-, -, h⟩ := appN_const_inj he
      obtain ⟨-, rfl⟩ := List.append_inj h (l4.trans r4.symm)
      exact Option.some.inj (l6.symm.trans r6)
    | _ => cases hx
  | delta l1 l2 l3 =>
    generalize hx : VExpr.const _ _ = x at H2
    cases H2 with
    | delta r1 r2 r3 =>
      cases hx; cases hU.delta l1 r1 l2 r2; rfl
    | _ => cases hx
  | quot l1 l2 =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases quotHead_whnf hU l1 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx1 hx2
      obtain ⟨-, -, h1⟩ := appN_const_inj hx1
      obtain ⟨-, -, h2⟩ := appN_const_inj hx2
      simp only [List.cons.injEq, and_true] at h1 h2
      obtain ⟨-, -, -, rfl, -⟩ := h1; obtain ⟨-, -, rfl⟩ := h2; rfl
    | quotMajor r1 r2 r3 =>
      injection hx with _ hx; subst hx; cases quotMk_whnf hU l1 _ r3
    | kQuot r1 r2 r3 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (l2 ⟨_, _, r2, r3⟩).elim
    | major r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r2).1 (appN_const_inj hx).1.symm).elim
    | iota r1 r2 r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | kIota r1 _ r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | etaIota r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 (VInductDecl.allTypes_getElem? r2)).1
        (appN_const_inj hx).1.symm).elim
    | _ => cases hx
  | quotMajor l1 l2 l3 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases quotHead_whnf hU l1 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with _ hx; subst hx; cases quotMk_whnf hU l1 _ l3
    | quotMajor r1 r2 r3 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨-, rfl, h1⟩ := appN_const_inj hx1
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
      cases ih r3; rfl
    | kQuot r1 r2 r3 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (l2 ⟨_, _, r2, r3⟩).elim
    | major r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r2).1 (appN_const_inj hx).1.symm).elim
    | iota r1 r2 r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | kIota r1 _ r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | etaIota r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 (VInductDecl.allTypes_getElem? r2)).1
        (appN_const_inj hx).1.symm).elim
    | _ => cases hx
  | kQuot l1 l2 l3 l4 =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases quotHead_whnf hU l1 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 r2 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (r2 ⟨_, _, l2, l3⟩).elim
    | quotMajor r1 r2 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (r2 ⟨_, _, l2, l3⟩).elim
    | kQuot r1 r2 r3 r4 =>
      injection hx with hx
      obtain ⟨-, rfl, h1⟩ := appN_const_inj hx
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
      rfl
    | major r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r2).1 (appN_const_inj hx).1.symm).elim
    | iota r1 r2 r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | kIota r1 _ r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | etaIota r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 (VInductDecl.allTypes_getElem? r2)).1
        (appN_const_inj hx).1.symm).elim
    | _ => cases hx
  | major l1 l2 l3 le l4 l5 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases recHead_whnf hU l1 l2 l4 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 re r4 r5 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨hn, rfl, rfl⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, rfl⟩ := recName_inj hU l1 l2 r1 r2 hn
      cases ih r5; rfl
    | iota r1 r2 r3 =>
      injection hx with hx1 hx2; subst hx2
      exact (ctor_whnf' hU r1 r2 _ l5).elim
    | kIota r1 _ r3 _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 l2 r1 r3 hn
      exact (l3 r5).elim
    | etaIota r1 r2 _ _ _ r6 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, -⟩ := recName_inj hU l1 l2 r1 (VInductDecl.allTypes_getElem? r2) hn
      exact (le r6).elim
    | _ => cases hx
  | iota l1 l2 l3 l4 le l5 l6 l7 l8 l9 =>
    obtain ⟨T, hT, hc⟩ := allTypes_of_allCtors l2
    cases l3.symm.trans hT
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 =>
      injection hx with hx; subst hx
      cases recHead_whnf hU l1 hT (by simp [VInductDecl.majorIdx, l5, l6, l7]; omega) _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 re r4 r5 =>
      injection hx with _ hx2; subst hx2
      exact (ctor_whnf' hU l1 l2 _ r5).elim
    | iota r1 r2 r3 r4 re r5 r6 r7 r8 r9 =>
      injection hx with hx1 hx2
      obtain ⟨hn, rfl, h1⟩ := appN_const_inj hx1
      obtain ⟨T', hT', -⟩ := allTypes_of_allCtors r2
      cases r3.symm.trans hT'
      obtain ⟨rfl, rfl, rfl⟩ := recName_inj hU l1 hT r1 hT' hn
      obtain ⟨hc, -, h2⟩ := appN_const_inj hx2
      cases hU.ctor l1 l2 r2 hc
      cases l2.symm.trans r2
      obtain ⟨h3, rfl⟩ := List.append_inj h1 (by simp only [List.length_append]; rw [l5, r5, l6, r6])
      obtain ⟨rfl, rfl⟩ := List.append_inj' h3 (by rw [l6, r6])
      obtain ⟨-, rfl⟩ := List.append_inj h2 (by simp [l8, r8])
      rfl
    | kIota r1 _ r3 _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 hT r1 r3 hn
      exact (l4 r5).elim
    | etaIota r1 r2 _ _ _ r6 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, -⟩ := recName_inj hU l1 hT r1 (VInductDecl.allTypes_getElem? r2) hn
      exact (le r6).elim
    | _ => cases hx
  | kIota l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 =>
      injection hx with hx; subst hx
      cases recHead_whnf hU l1 l3 (by simp [VInductDecl.majorIdx, l7, l8, l9]; omega) _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l3).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l3).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l3).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 l3 r1 r2 hn
      exact (r3 l5).elim
    | iota r1 r2 r3 r4 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 l3 r1 r3 hn
      exact (r4 l5).elim
    | kIota r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨hn, rfl, h1⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, rfl⟩ := recName_inj hU l1 l3 r1 r3 hn
      cases l4.symm.trans r4
      cases hU.ctor l1 l2 r2 rfl
      obtain ⟨h3, rfl⟩ := List.append_inj h1 (by simp only [List.length_append]; rw [l7, r7, l8, r8])
      obtain ⟨rfl, rfl⟩ := List.append_inj' h3 (by rw [l8, r8])
      rfl
    | etaIota r1 r2 _ _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 l3 r1 (VInductDecl.allTypes_getElem? r2) hn
      exact (r5 l5).elim
    | _ => cases hx
  | etaIota l1 l2 l3 l4 l5 l6 l7 l8 =>
    have hT := VInductDecl.allTypes_getElem? l2
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 =>
      injection hx with hx; subst hx
      cases recHead_whnf hU l1 hT (by simp [VInductDecl.majorIdx, l7, l8, l6.indices l2]) _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 hT).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 r4 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, -⟩ := recName_inj hU l1 hT r1 r2 hn
      exact (r4 l6).elim
    | iota r1 r2 r3 r4 r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, -⟩ := recName_inj hU l1 hT r1 r3 hn
      exact (r5 l6).elim
    | kIota r1 _ r3 _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := recName_inj hU l1 hT r1 r3 hn
      exact (l5 r5).elim
    | etaIota r1 r2 r3 r4 r5 r6 r7 r8 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨hn, rfl, h1⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, rfl⟩ := recName_inj hU l1 hT r1 (VInductDecl.allTypes_getElem? r2) hn
      cases l3.symm.trans r3
      cases hU.ctor l1 l4 r4 rfl
      obtain ⟨rfl, rfl⟩ := List.append_inj h1 (by rw [l7, r7])
      rfl
    | _ => cases hx

end Step

/-! ### Weakening and substitution -/

namespace KFields
variable {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}

/-- The fields' checks carry over along a map of terms that commutes with substituting closed
terms and carries judgments: lifting and substitution. -/
theorem map {s : Name} {d : VInductDecl} {t q j : Nat} {c : VConstructor} {T : VInductiveType}
    {ps is fs : List VExpr} {lsB : List VLevel} (hk : KClosed env) (h1 : env.inducts s = some (d, t))
    (h2 : d.allCtors[q]? = some (j, c)) (h3 : d.allTypes[j]? = some T)
    (hps : ps.length = d.params.length) (hfs : fs.length = c.fields.length)
    {F : VExpr → VExpr}
    (hF : ∀ {A : VExpr} {as : List VExpr}, A.ClosedN as.length →
      F (A.subst (VExpr.Subst.id.consList as)) = A.subst (VExpr.Subst.id.consList (as.map F)))
    (hD : ∀ {e e' A}, env.IsDefEq U Γ e e' A → env.IsDefEq U Γ' (F e) (F e') (F A))
    (H : KFields env U Γ T c lsB ps is fs) :
    KFields env U Γ' T c lsB (ps.map F) (is.map F) (fs.map F) := by
  have hidx : VInductDecl.idxAt c lsB (ps.map F) (fs.map F) =
      (VInductDecl.idxAt c lsB ps fs).map F := by
    simp only [VInductDecl.idxAt, List.map_map]
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp_apply]
    rw [hF, List.map_append]
    simpa [hps, hfs] using (hk.ctorIdx h1 h2 he).instL (ls := lsB)
  refine ⟨fun k i hk h => ?_, fun k hk1 hk2 => ?_, fun i hi1 hi2 hi3 => ?_⟩
  · simp [List.getElem?_map, H.idx k i hk h]
  · have hk1' : k < fs.length := by simpa using hk1
    have := hD (H.fields k hk1' hk2)
    simp only [List.getElem_map]
    rw [hF] at this
    · simp only [List.map_append, List.map_take] at this; exact this
    · have hf := hk.field h1 h2 (List.getElem?_eq_getElem hk2)
      simpa [hps, Nat.min_eq_left (Nat.le_of_lt hk1')] using hf.instL (ls := lsB)
  · have hi1' : i < (VInductDecl.idxAt c lsB ps fs).length := by
      rw [hidx] at hi1; simpa using hi1
    have hi2' : i < is.length := by simpa using hi2
    have := hD (H.index i hi1' hi2' hi3)
    have e1 : (VInductDecl.idxAt c lsB (ps.map F) (fs.map F))[i] =
        F (VInductDecl.idxAt c lsB ps fs)[i] := by simp [hidx]
    have e2 : (VInductDecl.idxAt c lsB (ps.map F) (fs.map F)).take i =
        ((VInductDecl.idxAt c lsB ps fs).take i).map F := by simp [hidx, List.map_take]
    rw [e1, e2, List.getElem_map]
    rw [hF] at this
    · simp only [List.map_append] at this; exact this
    · have hf := hk.typeIdx h1 h3 (List.getElem?_eq_getElem hi3)
      simpa [hps, Nat.min_eq_left (Nat.le_of_lt hi1')] using hf.instL (ls := lsB)

end KFields

namespace Step
variable {env : VEnv} {U : Nat} {Γ : List VExpr}
  (henv : env.Ordered) (hU : StepUniq env) (hk : KClosed env)

include henv in
theorem delta_closed (h : env.defeqs df) : (df.rhs.instL ls).ClosedN :=
  (henv.closed.2 h).2.1.instL

include henv hU in
theorem iotaRhs_closed (h1 : env.inducts s = some (d, t)) (h2 : d.allCtors[q]? = some (j, c)) :
    (d.iotaRhs recLs q j c).ClosedN := by
  refine (henv.closed.2 (hU.iota h1 ?_)).2.1.instL
  simp only [VInductDecl.iotaRules, List.mem_map]
  exact ⟨((j, c), q), List.mk_mem_zipIdx_iff_getElem?.2 h2, rfl⟩

end Step

/-! ### Lifted terms -/

theorem lift'_eq_app {e : VExpr} (h : e.lift' ρ = .app f a) :
    ∃ f0 a0, e = .app f0 a0 ∧ f = f0.lift' ρ ∧ a = a0.lift' ρ := by
  cases e <;> simp at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem lift'_eq_lam {e : VExpr} (h : e.lift' ρ = .lam A b) :
    ∃ A0 b0, e = .lam A0 b0 ∧ A = A0.lift' ρ ∧ b = b0.lift' ρ.cons := by
  cases e <;> simp at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem lift'_eq_proj {e : VExpr} (h : e.lift' ρ = .proj s k x) :
    ∃ x0, e = .proj s k x0 ∧ x = x0.lift' ρ := by
  cases e <;> simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

theorem lift'_eq_const {e : VExpr} (h : e.lift' ρ = .const c ls) : e = .const c ls := by
  cases e <;> simp at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem lift'_eq_appN_const : ∀ {as : List VExpr} {e : VExpr},
    e.lift' ρ = (VExpr.const c ls).appN as →
    ∃ as0, e = (VExpr.const c ls).appN as0 ∧ as = as0.map (·.lift' ρ) := by
  intro as
  induction as using snocInd with
  | nil => intro e h; exact ⟨[], lift'_eq_const h, rfl⟩
  | append_singleton as a ih =>
    intro e h
    rw [Step.appN_snoc] at h
    obtain ⟨f0, a0, rfl, hf, rfl⟩ := lift'_eq_app h
    obtain ⟨as0, rfl, rfl⟩ := ih hf.symm
    exact ⟨as0 ++ [a0], by rw [Step.appN_snoc], by simp⟩

theorem lift'_eq_appN_const5 {e : VExpr}
    (h : e.lift' ρ = (VExpr.const c ls).appN [α, r, β, f, x]) :
    ∃ α0 r0 β0 f0 x0, e = (VExpr.const c ls).appN [α0, r0, β0, f0, x0] ∧ α = α0.lift' ρ ∧
      r = r0.lift' ρ ∧ β = β0.lift' ρ ∧ f = f0.lift' ρ ∧ x = x0.lift' ρ := by
  obtain ⟨as0, rfl, hm⟩ := lift'_eq_appN_const h
  replace hm := hm.symm
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hm
  obtain ⟨α0, _, rfl, rfl, r0, _, rfl, rfl, β0, _, rfl, rfl, f0, _, rfl, rfl, x0, _, rfl, rfl, rfl⟩ :=
    hm
  exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lift'_eq_appN_const3 {e : VExpr}
    (h : e.lift' ρ = (VExpr.const c ls).appN [α, r, x]) :
    ∃ α0 r0 x0, e = (VExpr.const c ls).appN [α0, r0, x0] ∧ α = α0.lift' ρ ∧
      r = r0.lift' ρ ∧ x = x0.lift' ρ := by
  obtain ⟨as0, rfl, hm⟩ := lift'_eq_appN_const h
  replace hm := hm.symm
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hm
  obtain ⟨α0, _, rfl, rfl, r0, _, rfl, rfl, x0, _, rfl, rfl, rfl⟩ := hm
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-! ### Neutral terms -/

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- A neutral term: a variable, or an application, projection or major premise of a neutral term,
or a recursor at a propositional instance of its block, whatever its major premise. -/
inductive Neutral : VExpr → Prop where
  | bvar : Neutral (.bvar i)
  | app : Neutral f → Neutral (.app f a)
  | proj : Neutral e → Neutral (.proj s k e)
  | major : env.inducts s = some (d, t) → d.allTypes[j]? = some T →
    ¬d.PropAt (d.blockLevels recLs) → ¬d.EtaRec j (d.blockLevels recLs) →
    args.length = d.majorIdx T → Neutral e →
    Neutral (.app ((VExpr.const (d.recName j) recLs).appN args) e)
  | quot : env.defeqs quotDefEq → ¬QuotProp ls → Neutral e →
    Neutral (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
  | propQuot : env.defeqs quotDefEq → QuotProp ls →
    Neutral (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
  | propRec : env.inducts s = some (d, t) → d.allTypes[j]? = some T →
    d.PropAt (d.blockLevels recLs) → args.length = d.majorIdx T →
    Neutral (.app ((VExpr.const (d.recName j) recLs).appN args) e)

/-- A `kIota` or `kQuot` step, under applications, projections and major premises: the only steps
a neutral term takes (`Neutral.kStep`). -/
inductive KStep : VExpr → VExpr → Prop where
  | app : KStep f f' → KStep (.app f a) (.app f' a)
  | proj : KStep e e' → KStep (.proj s k e) (.proj s k e')
  | major : env.inducts s = some (d, t) → d.allTypes[j]? = some T →
    ¬d.PropAt (d.blockLevels recLs) → ¬d.EtaRec j (d.blockLevels recLs) →
    args.length = d.majorIdx T → KStep e e' →
    KStep (.app ((VExpr.const (d.recName j) recLs).appN args) e)
      (.app ((VExpr.const (d.recName j) recLs).appN args) e')
  | quotMajor : env.defeqs quotDefEq → ¬QuotProp ls → KStep e e' →
    KStep (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
      (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e')
  | kIota : env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    d.allTypes[j]? = some T → T.ctors = [c] → d.PropAt (d.blockLevels recLs) →
    d.largeElim = true → ps.length = d.params.length →
    ms.length = d.allTypes.length + d.allCtors.length → is.length = T.indices.length →
    (kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is).length = c.fields.length →
    KFields env U Γ T c (d.recLevels.map (·.inst recLs)) ps is
      (kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is) →
    KStep (.app ((VExpr.const (d.recName j) recLs).appN (ps ++ ms ++ is)) e)
      ((d.iotaRhs recLs q j c).appN
        (ps ++ ms ++ kFieldsOf env U Γ T c (d.recLevels.map (·.inst recLs)) ps is))
  | kQuot : env.defeqs quotDefEq → ls = [u, v] → u ≈ .zero →
    env.HasType U Γ (quotWit env U Γ α) α →
    KStep (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e) (.app f (quotWit env U Γ α))

end

theorem KStep.step {env : VEnv} {U : Nat} {Γ : List VExpr}
    (H : KStep env U Γ e e') : Step env U Γ e e' := by
  induction H with
  | app _ ih => exact .app ih
  | proj _ ih => exact .proj ih
  | major h1 h2 h3 he h4 _ ih => exact .major h1 h2 h3 he h4 ih
  | quotMajor h1 h2 _ ih => exact .quotMajor h1 h2 ih
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | kQuot h1 h2 h3 h4 => exact .kQuot h1 h2 h3 h4

namespace Neutral
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem not_lam : ¬Neutral env (.lam A e) := nofun

/-- A neutral constant application is a recursor or `Quot.lift` applied past its major premise. -/
theorem appN_const : ∀ {as : List VExpr}, Neutral env ((VExpr.const h ls).appN as) →
    (env.defeqs quotDefEq ∧ h = ``Quot.lift ∧ 6 ≤ as.length) ∨
    (∃ s d t j T, env.inducts s = some (d, t) ∧ d.allTypes[j]? = some T ∧ h = d.recName j ∧
      d.majorIdx T + 1 ≤ as.length) := by
  intro as
  induction as using snocInd with
  | nil => intro H; nomatch H
  | append_singleton as a ih =>
    intro H
    rw [Step.appN_snoc] at H
    generalize hx : VExpr.app _ a = x at H
    cases H with
    | app r1 =>
      cases hx
      rcases ih r1 with ⟨h1, h2, h3⟩ | ⟨s, d, t, j, T, h1, h2, h3, h4⟩
      · exact .inl ⟨h1, h2, by simp; omega⟩
      · exact .inr ⟨s, d, t, j, T, h1, h2, h3, by simp; omega⟩
    | quot r1 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inl ⟨r1, rfl, by simp⟩
    | propQuot r1 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inl ⟨r1, rfl, by simp⟩
    | major r1 r2 _ _ r4 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr ⟨_, _, _, _, _, r1, r2, rfl, by simp; omega⟩
    | propRec r1 r2 _ r4 =>
      injection hx with hx
      obtain ⟨rfl, -, rfl⟩ := appN_const_inj hx.symm
      exact .inr ⟨_, _, _, _, _, r1, r2, rfl, by simp; omega⟩
    | _ => cases hx

theorem _root_.Lean4Lean.LogRel.Inert.not_neutral (hn : Inert env h) :
    ¬Neutral env ((VExpr.const h ls).appN as) := fun H => by
  rcases appN_const H with ⟨h1, rfl, -⟩ | ⟨s, d, t, j, T, h1, h2, rfl, -⟩
  · exact hn.quot h1 rfl
  · exact hn.notRec h1 (List.getElem?_eq_some_iff.1 h2).1 rfl

variable (hU : StepUniq env)
include hU

theorem recHead (h1 : env.inducts s = some (d, t)) (h2 : d.allTypes[j]? = some T)
    (h3 : args.length = d.majorIdx T) :
    ¬Neutral env ((VExpr.const (d.recName j) recLs).appN args) := fun H => by
  rcases appN_const H with ⟨r1, r2, -⟩ | ⟨s', d', t', j', T', r1, r2, r3, r4⟩
  · exact hU.recQuot r1 h1 (List.getElem?_eq_some_iff.1 h2).1 r2
  · obtain ⟨rfl, rfl, rfl⟩ := Step.recName_inj hU h1 h2 r1 r2 r3; omega

theorem quotHead (h1 : env.defeqs quotDefEq) :
    ¬Neutral env ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) := fun H => by
  rcases appN_const H with ⟨-, -, r3⟩ | ⟨s', d', t', j', T', r1, r2, r3, -⟩
  · simp at r3
  · exact hU.recQuot h1 r1 (List.getElem?_eq_some_iff.1 r2).1 r3.symm

/-- The only steps a neutral term takes are `kIota` and `kQuot` steps inside it. -/
theorem kStep (H : Neutral env e) (H2 : Step env U Γ e e') : KStep env U Γ e e' := by
  induction H generalizing e' with
  | bvar => nomatch H2
  | app l1 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => cases hx; exact .app (ih r1)
    | beta => cases hx; exact (not_lam l1).elim
    | quot r1 => injection hx with hx; subst hx; exact (quotHead hU r1 l1).elim
    | quotMajor r1 => injection hx with hx; subst hx; exact (quotHead hU r1 l1).elim
    | kQuot r1 => injection hx with hx; subst hx; exact (quotHead hU r1 l1).elim
    | major r1 r2 _ _ r4 => injection hx with hx; subst hx; exact (recHead hU r1 r2 r4 l1).elim
    | iota r1 r2 r3 _ _ r5 r6 r7 =>
      injection hx with hx; subst hx
      obtain ⟨T, hT, -⟩ := Step.allTypes_of_allCtors r2
      cases r3.symm.trans hT
      exact (recHead hU r1 hT (by simp [VInductDecl.majorIdx, r5, r6, r7]; omega) l1).elim
    | kIota r1 _ r3 _ _ _ r7 r8 r9 =>
      injection hx with hx; subst hx
      exact (recHead hU r1 r3 (by simp [VInductDecl.majorIdx, r7, r8, r9]; omega) l1).elim
    | etaIota r1 r2 _ _ _ r6 r7 r8 =>
      injection hx with hx; subst hx
      exact (recHead hU r1 (VInductDecl.allTypes_getElem? r2)
        (by simp [VInductDecl.majorIdx, r7, r8, r6.indices r2]) l1).elim
    | _ => cases hx
  | proj l1 ih =>
    generalize hx : VExpr.proj _ _ _ = x at H2
    cases H2 with
    | proj r1 => cases hx; exact .proj (ih r1)
    | projIota r1 r2 r3 =>
      injection hx with _ _ hx; subst hx
      exact ((hU.ctorInert r1 (VInductDecl.mem_allCtors_iff.2
        ⟨_, VInductDecl.allTypes_getElem? r2, by simp [r3]⟩)).not_neutral l1).elim
    | _ => cases hx
  | major l1 l2 l3 le l4 l5 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases Step.recHead_whnf hU l1 l2 l4 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 re r4 r5 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨hn, rfl, rfl⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, rfl⟩ := Step.recName_inj hU l1 l2 r1 r2 hn
      exact .major l1 l2 l3 le l4 (ih r5)
    | iota r1 r2 =>
      injection hx with _ hx2; subst hx2
      exact ((hU.ctorInert r1 (List.mem_of_getElem? r2)).not_neutral l5).elim
    | kIota r1 _ r3 _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := Step.recName_inj hU l1 l2 r1 r3 hn
      exact (l3 r5).elim
    | etaIota r1 r2 _ _ _ r6 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, -⟩ :=
        Step.recName_inj hU l1 l2 r1 (VInductDecl.allTypes_getElem? r2) hn
      exact (le r6).elim
    | _ => cases hx
  | quot l1 l2 l3 ih =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases Step.quotHead_whnf hU l1 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with _ hx; subst hx; exact ((hU.quotMk l1).not_neutral l3).elim
    | quotMajor r1 r2 r3 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨-, rfl, h1⟩ := appN_const_inj hx1
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
      exact .quotMajor l1 l2 (ih r3)
    | kQuot r1 r2 r3 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (l2 ⟨_, _, r2, r3⟩).elim
    | major r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r2).1 (appN_const_inj hx).1.symm).elim
    | iota r1 r2 r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | kIota r1 _ r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | etaIota r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 (VInductDecl.allTypes_getElem? r2)).1
        (appN_const_inj hx).1.symm).elim
    | _ => cases hx
  | propQuot l1 l2 =>
    obtain ⟨u, v, rfl, huv⟩ := l2
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases Step.quotHead_whnf hU l1 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 r2 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (r2 ⟨_, _, rfl, huv⟩).elim
    | quotMajor r1 r2 =>
      injection hx with hx
      obtain ⟨-, rfl, -⟩ := appN_const_inj hx
      exact (r2 ⟨_, _, rfl, huv⟩).elim
    | kQuot r1 r2 r3 r4 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨-, rfl, h1⟩ := appN_const_inj hx1
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
      exact .kQuot r1 r2 r3 r4
    | major r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r2).1 (appN_const_inj hx).1.symm).elim
    | iota r1 r2 r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | kIota r1 _ r3 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 r3).1 (appN_const_inj hx).1.symm).elim
    | etaIota r1 r2 =>
      injection hx with hx
      exact (hU.recQuot l1 r1 (List.getElem?_eq_some_iff.1 (VInductDecl.allTypes_getElem? r2)).1
        (appN_const_inj hx).1.symm).elim
    | _ => cases hx
  | propRec l1 l2 l3 l4 =>
    generalize hx : VExpr.app _ _ = x at H2
    cases H2 with
    | app r1 => injection hx with hx; subst hx; cases Step.recHead_whnf hU l1 l2 l4 _ r1
    | beta => injection hx with hx; cases appN_const_ne_lam hx
    | quot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | quotMajor r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | kQuot r1 =>
      injection hx with hx
      exact (hU.recQuot r1 l1 (List.getElem?_eq_some_iff.1 l2).1 (appN_const_inj hx).1).elim
    | major r1 r2 r3 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := Step.recName_inj hU l1 l2 r1 r2 hn
      exact (r3 l3).elim
    | iota r1 r2 r3 r4 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := Step.recName_inj hU l1 l2 r1 r3 hn
      exact (r4 l3).elim
    | kIota r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 =>
      injection hx with hx1 hx2; subst hx2
      obtain ⟨hn, rfl, rfl⟩ := appN_const_inj hx1
      obtain ⟨rfl, rfl, rfl⟩ := Step.recName_inj hU l1 l2 r1 r3 hn
      exact .kIota r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
    | etaIota r1 r2 _ _ r5 =>
      injection hx with hx1
      obtain ⟨hn, rfl, -⟩ := appN_const_inj hx1
      obtain ⟨rfl, -, -⟩ := Step.recName_inj hU l1 l2 r1 (VInductDecl.allTypes_getElem? r2) hn
      exact (r5 l3).elim
    | _ => cases hx

/-- A neutral term none of whose recursors at a propositional instance has a `kIota` step is in
weak head normal form. -/
theorem whnf_of_noK (H : Neutral env e) (hK : ∀ e', ¬KStep env U Γ e e') : WHNF env U Γ e :=
  fun _ h => hK _ (H.kStep hU h)

end Neutral

namespace Neutral
variable {env : VEnv}

theorem lift' (H : Neutral env e) : Neutral env (e.lift' ρ) := by
  induction H generalizing ρ with
  | bvar => exact .bvar
  | app _ ih => exact .app ih
  | proj _ ih => exact .proj ih
  | major h1 h2 h3 he h4 _ ih =>
    simp only [VExpr.lift', lift'_appN]; exact .major h1 h2 h3 he (by simpa) ih
  | quot h1 h2 _ ih => simp only [VExpr.lift', lift'_appN, List.map]; exact .quot h1 h2 ih
  | propQuot h1 h2 => simp only [VExpr.lift', lift'_appN, List.map]; exact .propQuot h1 h2
  | propRec h1 h2 h3 h4 =>
    simp only [VExpr.lift', lift'_appN]; exact .propRec h1 h2 h3 (by simpa)

theorem lift'_inv (H : Neutral env e') (he : e' = e.lift' ρ) : Neutral env e := by
  induction H generalizing e with
  | bvar => cases e <;> simp at he; exact .bvar
  | app _ ih =>
    obtain ⟨f0, a0, rfl, rfl, rfl⟩ := lift'_eq_app he.symm; exact .app (ih rfl)
  | proj _ ih =>
    obtain ⟨x0, rfl, rfl⟩ := lift'_eq_proj he.symm; exact .proj (ih rfl)
  | major h1 h2 h3 h3' h4 _ ih =>
    obtain ⟨g, x, rfl, hg, rfl⟩ := lift'_eq_app he.symm
    obtain ⟨as0, rfl, rfl⟩ := lift'_eq_appN_const hg.symm
    exact .major h1 h2 h3 h3' (by simpa using h4) (ih rfl)
  | quot h1 h2 _ ih =>
    obtain ⟨g, x, rfl, hg, rfl⟩ := lift'_eq_app he.symm
    obtain ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_appN_const5 hg.symm
    exact .quot h1 h2 (ih rfl)
  | propQuot h1 h2 =>
    obtain ⟨g, x, rfl, hg, rfl⟩ := lift'_eq_app he.symm
    obtain ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩ := lift'_eq_appN_const5 hg.symm
    exact .propQuot h1 h2
  | propRec h1 h2 h3 h4 =>
    obtain ⟨g, x, rfl, hg, rfl⟩ := lift'_eq_app he.symm
    obtain ⟨as0, rfl, rfl⟩ := lift'_eq_appN_const hg.symm
    exact .propRec h1 h2 h3 (by simpa using h4)

theorem lift'_iff : Neutral env (e.lift' ρ) ↔ Neutral env e := ⟨(lift'_inv · rfl), lift'⟩

theorem liftN_iff : Neutral env (e.liftN n k) ↔ Neutral env e := by
  rw [← lift'_consN_skipN]; exact lift'_iff

end Neutral

/-! ### Reduction sequences and typed reduction -/

section
variable (env : VEnv) (U : Nat)
  (Γ : List VExpr)

/-- Zero or more steps. -/
def StepS : VExpr → VExpr → Prop := ReflTransGen (Step env U Γ)

/-- Typed reduction: `e` reduces to `e'`, and they are definitionally equal at `A`. Subject
reduction is not available before injectivity of pi types, so the equality is part of the
judgment, established where each step is taken. -/
def TRed (e e' A : VExpr) : Prop := StepS env U Γ e e' ∧ env.IsDefEq U Γ e e' A

end

namespace StepS
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem single (H : Step env U Γ e e') : StepS env U Γ e e' := .tail .rfl H

theorem trans (H1 : StepS env U Γ e₁ e₂) (H2 : StepS env U Γ e₂ e₃) :
    StepS env U Γ e₁ e₃ := ReflTransGen.trans H1 H2

theorem head (H1 : Step env U Γ e₁ e₂) (H2 : StepS env U Γ e₂ e₃) : StepS env U Γ e₁ e₃ :=
  (single H1).trans H2

/-- Steps under a context that steps carry. -/
theorem map {F : VExpr → VExpr} (hF : ∀ {e e'}, Step env U Γ e e' → Step env U Γ (F e) (F e'))
    (H : StepS env U Γ e e') : StepS env U Γ (F e) (F e') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (hF h)

theorem app (H : StepS env U Γ f f') : StepS env U Γ (.app f a) (.app f' a) := H.map .app

theorem proj (H : StepS env U Γ e e') : StepS env U Γ (.proj s k e) (.proj s k e') :=
  H.map .proj

theorem major (h1 : env.inducts s = some (d, t)) (h2 : d.allTypes[j]? = some T)
    (h3 : ¬d.PropAt (d.blockLevels recLs)) (h3' : ¬d.EtaRec j (d.blockLevels recLs))
    (h4 : args.length = d.majorIdx T)
    (H : StepS env U Γ e e') :
    StepS env U Γ (.app ((VExpr.const (d.recName j) recLs).appN args) e)
      (.app ((VExpr.const (d.recName j) recLs).appN args) e') :=
  H.map (.major h1 h2 h3 h3' h4)

theorem quotMajor (h1 : env.defeqs quotDefEq) (h2 : ¬QuotProp ls) (H : StepS env U Γ e e') :
    StepS env U Γ (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
      (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e') :=
  H.map (.quotMajor h1 h2)

/-- Steps along a map of terms and contexts that carries each step. -/
theorem map' {F : VExpr → VExpr} {Γ' : List VExpr}
    (hF : ∀ {e e'}, Step env U Γ e e' → Step env U Γ' (F e) (F e'))
    (H : StepS env U Γ e e') : StepS env U Γ' (F e) (F e') := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (hF h)


theorem of_whnf (W : WHNF env U Γ e) (H : StepS env U Γ e e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h => cases W _ h

/-- Of two reduction sequences from one term, one extends the other. -/
theorem total (hU : StepUniq env) (H1 : StepS env U Γ e e₁) (H2 : StepS env U Γ e e₂) :
    StepS env U Γ e₁ e₂ ∨ StepS env U Γ e₂ e₁ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact .inl H2
  | head h1 _ ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => exact .inr (.head h1 ‹_›)
    | head h2 H2 => cases Step.determ hU h1 h2; exact ih H2

/-- A reduction sequence reaching a normal form is extended by every other from the same term. -/
theorem determ_l (hU : StepUniq env) (H1 : StepS env U Γ e e₁) (H2 : StepS env U Γ e e₂)
    (W : WHNF env U Γ e₂) : StepS env U Γ e₁ e₂ :=
  (total hU H1 H2).elim id fun h => of_whnf W h ▸ .rfl

/-- A term has at most one normal form. -/
theorem determ (hU : StepUniq env) (H1 : StepS env U Γ e e₁) (W1 : WHNF env U Γ e₁)
    (H2 : StepS env U Γ e e₂) (W2 : WHNF env U Γ e₂) : e₁ = e₂ :=
  of_whnf W1 (determ_l hU H1 H2 W2)

end StepS

namespace TRed
variable {env : VEnv} {U : Nat}
  {Γ : List VExpr}

theorem defeq (H : TRed env U Γ e e' A) : env.IsDefEq U Γ e e' A := H.2

theorem refl (H : env.HasType U Γ e A) : TRed env U Γ e e A := ⟨.rfl, H⟩

theorem step (H : Step env U Γ e e') (h : env.IsDefEq U Γ e e' A) : TRed env U Γ e e' A :=
  ⟨.single H, h⟩

theorem trans (H1 : TRed env U Γ e₁ e₂ A) (H2 : TRed env U Γ e₂ e₃ A) :
    TRed env U Γ e₁ e₃ A := ⟨H1.1.trans H2.1, H1.2.trans H2.2⟩

theorem defeqDF (h : env.IsDefEq U Γ A B (.sort u)) (H : TRed env U Γ e e' A) :
    TRed env U Γ e e' B := ⟨H.1, .defeqDF h H.2⟩

theorem beta (hb : env.HasType U (A::Γ) body B) (ha : env.HasType U Γ a A) :
    TRed env U Γ (.app (.lam A body) a) (body.inst a) (B.inst a) :=
  ⟨.single .beta, .beta hb ha⟩

theorem app (H : TRed env U Γ f f' (.forallE A B)) (ha : env.HasType U Γ a A) :
    TRed env U Γ (.app f a) (.app f' a) (B.inst a) := ⟨H.1.app, .appDF H.2 ha⟩

theorem major (h1 : env.inducts s = some (d, t)) (h2 : d.allTypes[j]? = some T)
    (h3 : ¬d.PropAt (d.blockLevels recLs)) (h3' : ¬d.EtaRec j (d.blockLevels recLs))
    (h4 : args.length = d.majorIdx T)
    (hf : env.HasType U Γ ((VExpr.const (d.recName j) recLs).appN args) (.forallE A B))
    (H : TRed env U Γ e e' A) :
    TRed env U Γ (.app ((VExpr.const (d.recName j) recLs).appN args) e)
      (.app ((VExpr.const (d.recName j) recLs).appN args) e') (B.inst e) :=
  ⟨H.1.major h1 h2 h3 h3' h4, .appDF hf H.2⟩

theorem quotMajor (h1 : env.defeqs quotDefEq) (h2 : ¬QuotProp ls)
    (hf : env.HasType U Γ ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) (.forallE A B))
    (H : TRed env U Γ e e' A) :
    TRed env U Γ (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e)
      (.app ((VExpr.const ``Quot.lift ls).appN [α, r, β, f, h]) e') (B.inst e) :=
  ⟨H.1.quotMajor h1 h2, .appDF hf H.2⟩

theorem proj (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T) (h3 : T.ctors = [c])
    (h4 : c.fields[k]? = some f) (h5 : ∀ l ∈ ls, l.WF U) (h6 : ls.length = d.uvars)
    (h7 : As.length = d.params.length) (h8 : I.length = T.indices.length)
    (hT : env.HasType U Γ (.appN (.const s ls) (As ++ I)) (.sort u))
    (H : TRed env U Γ e e' (.appN (.const s ls) (As ++ I))) (hP : d.ProjAllowed c ls k)
    (hty : env.IsDefEq U Γ (c.projType ls s k As e) (c.projType ls s k As e')
      (.sort (f.level.inst ls))) :
    TRed env U Γ (.proj s k e) (.proj s k e') (c.projType ls s k As e) :=
  ⟨H.1.proj, .projDF h1 h2 h3 h4 h5 h6 h7 h8 h7 h8 hT H.2 hP hty⟩

theorem projIota (h1 : env.inducts s = some (d, t)) (h2 : d.types[t]? = some T)
    (h3 : T.ctors = [c]) (h4 : c.fields[k]? = some f) (h5 : fs[k]? = some a)
    (h6 : ∀ l ∈ ls, l.WF U) (h7 : ls.length = d.uvars) (h8 : As.length = d.params.length)
    (h9 : fs.length = c.fields.length) (h10 : I.length = T.indices.length)
    (h11 : env.HasType U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)))
    (h12 : d.ProjAllowed c ls k)
    (h13 : env.HasType U Γ (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))
      (.sort (f.level.inst ls)))
    (h14 : env.HasType U Γ a (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)))) :
    TRed env U Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) a
      (c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))) :=
  ⟨.single (.projIota h1 h2 h3 h8 h9 h5),
    .projIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14⟩

theorem delta (h1 : env.defeqs df) (h2 : df.lhs = .const n (VLevel.params df.uvars))
    (h3 : ∀ l ∈ ls, l.WF U) (h4 : ls.length = df.uvars) :
    TRed env U Γ (.const n ls) (df.rhs.instL ls) (df.type.instL ls) := by
  refine ⟨.single (.delta h1 h2 h4), ?_⟩
  have := VEnv.IsDefEq.extra (Γ := Γ) h1 h3 h4
  rwa [h2, VExpr.instL, VLevel.inst_map_id h4] at this


end TRed

end LogRel
end Lean4Lean

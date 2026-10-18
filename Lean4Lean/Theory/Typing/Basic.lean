import Lean4Lean.Theory.VEnv

namespace Lean4Lean
open Lean4Lean

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

/-- The substitution sending every variable to a closed term. -/
def VExpr.Subst.dflt : VExpr.Subst := fun _ => default

@[simp] theorem VExpr.Subst.dflt_comp (σ : VExpr.Subst) : VExpr.Subst.dflt.comp σ = .dflt := rfl

/-- The first `k` projections of `e`, a term of the type `s`. -/
def VExpr.projs (s : Name) (k : Nat) (e : VExpr) : List VExpr := (List.range k).map (.proj s · e)

/-- Two terms of the same shape whose universe levels are equivalent and well formed. -/
inductive VEnv.EqUpToLevels (U : Nat) : VExpr → VExpr → Prop
  | bvar : EqUpToLevels U (.bvar i) (.bvar i)
  | const : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    EqUpToLevels U (.const c ls) (.const c ls')
  | sort : l.WF U → l'.WF U → l ≈ l' → EqUpToLevels U (.sort l) (.sort l')
  | app : EqUpToLevels U f f' → EqUpToLevels U a a' → EqUpToLevels U (.app f a) (.app f' a')
  | lam : EqUpToLevels U A A' → EqUpToLevels U e e' → EqUpToLevels U (.lam A e) (.lam A' e')
  | forallE : EqUpToLevels U A A' → EqUpToLevels U B B' → EqUpToLevels U (.forallE A B) (.forallE A' B')
  | proj : EqUpToLevels U e e' → EqUpToLevels U (.proj s k e) (.proj s k e')

theorem VEnv.EqUpToLevels.symm {U : Nat} {e e' : VExpr} (H : VEnv.EqUpToLevels U e e') :
    VEnv.EqUpToLevels U e' e := by
  induction H with
  | bvar => exact .bvar
  | const h1 h2 h3 => exact .const h2 h1 (List.Forall₂.flip (Lean4Lean.List.Forall₂.imp
      (fun _ _ h => h.symm) h3))
  | sort h1 h2 h3 => exact .sort h2 h1 h3.symm
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- `e` is `e'` under type annotations, `optParam`, `autoParam`, `outParam` and `semiOutParam`
applied to it: a binder's declared type and the type the kernel reads off it. -/
inductive VExpr.StripsTo : VExpr → VExpr → Prop
  | refl : StripsTo e e
  | app2 {c : Lean.Name} : c = ``optParam ∨ c = ``autoParam → StripsTo A e →
    StripsTo (.app (.app (.const c ls) A) v) e
  | app1 {c : Lean.Name} : c = ``outParam ∨ c = ``semiOutParam → StripsTo A e →
    StripsTo (.app (.const c ls) A) e

/-- `StripsTo`, stripping only annotations whose names satisfy `P`. -/
inductive VExpr.StripsToBy (P : Lean.Name → Prop) : VExpr → VExpr → Prop
  | refl : StripsToBy P e e
  | app2 {c : Lean.Name} : c = ``optParam ∨ c = ``autoParam → P c → StripsToBy P A e →
    StripsToBy P (.app (.app (.const c ls) A) v) e
  | app1 {c : Lean.Name} : c = ``outParam ∨ c = ``semiOutParam → P c → StripsToBy P A e →
    StripsToBy P (.app (.const c ls) A) e

theorem VExpr.StripsToBy.toStripsTo {P : Lean.Name → Prop} {e e' : VExpr}
    (H : e.StripsToBy P e') : e.StripsTo e' := by
  induction H with
  | refl => exact .refl
  | app2 hc _ _ ih => exact .app2 hc ih
  | app1 hc _ _ ih => exact .app1 hc ih

theorem VExpr.StripsToBy.mono {P Q : Lean.Name → Prop} (h : ∀ c, P c → Q c) {e e' : VExpr}
    (H : e.StripsToBy P e') : e.StripsToBy Q e' := by
  induction H with
  | refl => exact .refl
  | app2 hc hP _ ih => exact .app2 hc (h _ hP) ih
  | app1 hc hP _ ih => exact .app1 hc (h _ hP) ih

theorem VExpr.StripsTo.skips {e e' : VExpr} (H : e.StripsTo e') {n k : Nat} (h : e.Skips n k) :
    e'.Skips n k := by
  induction H with
  | refl => exact h
  | app2 _ _ ih => simp only [VExpr.skips_iff, VExpr.Skips'] at h; exact ih (VExpr.skips_iff.2 h.1.2)
  | app1 _ _ ih => simp only [VExpr.skips_iff, VExpr.Skips'] at h; exact ih (VExpr.skips_iff.2 h.2)

namespace VConstructor
variable (c : VConstructor)

/-- The type of the `k`th projection of `e : s As I`, where `c` is `s`'s constructor, at universe
levels `ls`: the field's type at the parameters `As` and the earlier projections of `e`. The field's
type mentions nothing else, so the variables beyond them can go anywhere; sending them to a closed
term makes the type commute with substitutions syntactically. -/
def projType (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr) : VExpr :=
  (((c.fields[k]?.map VField.type).getD default).instL ls).subst
    (VExpr.Subst.dflt.consList (As ++ VExpr.projs s k e))

theorem _root_.Lean4Lean.VExpr.Subst.consList_comp (σ σ' : VExpr.Subst) :
    ∀ L : List VExpr, (σ.consList L).comp σ' = (σ.comp σ').consList (L.map (·.subst σ'))
  | [] => rfl
  | a :: L => by
    show ((σ.cons a).consList L).comp σ' = ((σ.comp σ').cons (a.subst σ')).consList _
    rw [VExpr.Subst.consList_comp _ _ L]
    have : (σ.cons a).comp σ' = (σ.comp σ').cons (a.subst σ') := by
      funext i; cases i <;> rfl
    rw [this]

theorem _root_.Lean4Lean.VExpr.projs_map (f : VExpr → VExpr)
    (hf : ∀ i e, f (.proj s i e) = .proj s i (f e)) :
    (VExpr.projs s k e).map f = VExpr.projs s k (f e) := by
  simp [VExpr.projs, hf]

@[simp] theorem _root_.Lean4Lean.VExpr.projs_liftN :
    (VExpr.projs s k e).map (·.liftN n j) = VExpr.projs s k (e.liftN n j) :=
  VExpr.projs_map _ fun _ _ => rfl

@[simp] theorem _root_.Lean4Lean.VExpr.projs_lift' :
    (VExpr.projs s k e).map (·.lift' ρ) = VExpr.projs s k (e.lift' ρ) :=
  VExpr.projs_map _ fun _ _ => rfl

@[simp] theorem _root_.Lean4Lean.VExpr.projs_inst :
    (VExpr.projs s k e).map (·.inst a j) = VExpr.projs s k (e.inst a j) :=
  VExpr.projs_map _ fun _ _ => rfl

@[simp] theorem _root_.Lean4Lean.VExpr.projs_instL :
    (VExpr.projs s k e).map (·.instL ls) = VExpr.projs s k (e.instL ls) :=
  VExpr.projs_map _ fun _ _ => rfl

@[simp] theorem _root_.Lean4Lean.VExpr.projs_subst :
    (VExpr.projs s k e).map (·.subst σ) = VExpr.projs s k (e.subst σ) :=
  VExpr.projs_map _ fun _ _ => rfl

@[simp] theorem _root_.Lean4Lean.VExpr.length_projs : (VExpr.projs s k e).length = k := by
  simp [VExpr.projs]

theorem projType_subst (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr)
    (σ : VExpr.Subst) :
    (c.projType ls s k As e).subst σ = c.projType ls s k (As.map (·.subst σ)) (e.subst σ) := by
  simp only [projType, VExpr.subst_subst, VExpr.Subst.consList_comp, List.map_append,
    VExpr.Subst.dflt_comp]
  rw [VExpr.projs_subst]

theorem projType_lift' (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr)
    (ρ : Lift) :
    (c.projType ls s k As e).lift' ρ = c.projType ls s k (As.map (·.lift' ρ)) (e.lift' ρ) := by
  have h : ∀ x : VExpr, x.lift' ρ = x.subst (.lift_l ρ .id) := by
    intro x; have := VExpr.subst_lift' (e := x) (ρ := ρ) (σ := .id); simpa using this
  simp only [h]; rw [projType_subst]

theorem projType_liftN (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr)
    (n j : Nat) :
    (c.projType ls s k As e).liftN n j =
      c.projType ls s k (As.map (·.liftN n j)) (e.liftN n j) := by
  simp only [← VExpr.lift'_consN_skipN, projType_lift']

theorem projType_inst (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e a : VExpr)
    (j : Nat) :
    (c.projType ls s k As e).inst a j = c.projType ls s k (As.map (·.inst a j)) (e.inst a j) := by
  simp only [VExpr.instN_eq, projType_subst]

theorem _root_.Lean4Lean.VExpr.instL_subst (ls : List VLevel) :
    ∀ (e : VExpr) (σ : VExpr.Subst),
      (e.subst σ).instL ls = (e.instL ls).subst fun i => (σ i).instL ls
  | .bvar _, _ | .sort _, _ | .const .., _ => rfl
  | .app f a, σ => by simp only [VExpr.subst, VExpr.instL, VExpr.instL_subst ls f, VExpr.instL_subst ls a]
  | .lam A b, σ | .forallE A b, σ => by
    simp only [VExpr.subst, VExpr.instL, VExpr.instL_subst ls A, VExpr.instL_subst ls b]
    congr 2; funext i; cases i <;> simp [VExpr.Subst.lift, VExpr.lift, VExpr.instL]
  | .proj _ _ e, σ => by simp only [VExpr.subst, VExpr.instL, VExpr.instL_subst ls e]

theorem _root_.Lean4Lean.VExpr.Subst.consList_instL (ls : List VLevel) (σ : VExpr.Subst) :
    ∀ L : List VExpr, (fun i => (σ.consList L i).instL ls) =
      VExpr.Subst.consList (fun i => (σ i).instL ls) (L.map (·.instL ls))
  | [] => rfl
  | a :: L => by
    show (fun i => ((σ.cons a).consList L i).instL ls) = _
    rw [VExpr.Subst.consList_instL ls _ L]
    have : (fun i => (σ.cons a i).instL ls) = VExpr.Subst.cons (fun i => (σ i).instL ls) (a.instL ls) := by
      funext i; cases i <;> rfl
    rw [this]; rfl

theorem projType_instL (ls ls' : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr) :
    (c.projType ls s k As e).instL ls' =
      c.projType (ls.map (VLevel.inst ls')) s k (As.map (·.instL ls')) (e.instL ls') := by
  simp only [projType, VExpr.instL_subst, VExpr.Subst.consList_instL, VExpr.instL_instL,
    List.map_append, VExpr.projs_instL]
  rfl

/-- No field from the `j`th to the `k`th mentions the `j`th: the `k`th projection's type does not
depend on it, directly or through the fields in between. -/
def Unused (k j : Nat) : Prop :=
  ∀ i (f : VField), j < i → i ≤ k → c.fields[i]? = some f → f.type.Skips 1 (i - 1 - j)

end VConstructor

/-- `inferProj`'s condition on projecting the `k`th field of a type of the block `d` with
constructor `c` at levels `ls`: when that instance of the block may be a proposition, the field
is a proof, and so is each earlier field its type depends on. The kernel tests the sort with
`isNeverZero`, which decides `VLevel.IsNeverZero`, and dependence by looking for the field's
variable in everything after it, which implies `VConstructor.Unused`.

This is what keeps projections out of a proposition sound under proof irrelevance, which makes
any two proofs of it definitionally equal. The projection is then a proof, and its type depends
on the projected term only through earlier fields that are proofs too, so two proofs of the same
proposition have projections of definitionally equal types, themselves equal by proof
irrelevance. Fields after the `k`th, and earlier ones its type does not reach, enter neither the
projection nor its type, so they may be anything: the kernel's check, which also covers them, is
stricter than soundness needs. -/
def VInductDecl.ProjAllowed (d : VInductDecl) (c : VConstructor) (ls : List VLevel)
    (k : Nat) : Prop :=
  ¬(d.level.inst ls).IsNeverZero →
    (∀ f, c.fields[k]? = some f → f.level.inst ls ≈ .zero) ∧
    ∀ j < k, ∀ f, c.fields[j]? = some f → f.level.inst ls ≈ .zero ∨ c.Unused k j

theorem VInductDecl.ProjAllowed.congr {d : VInductDecl} {c : VConstructor} {ls ls' : List VLevel}
    {k : Nat} (H : d.ProjAllowed c ls k) (heq : List.Forall₂ (· ≈ ·) ls ls') :
    d.ProjAllowed c ls' k := by
  have e {l : VLevel} : l.inst ls ≈ l.inst ls' := VLevel.inst_congr (VLevel.equiv_def'.2 rfl) heq
  have e' {l : VLevel} : l.inst ls' ≈ .zero ↔ l.inst ls ≈ .zero :=
    ⟨fun h => VLevel.equiv_def'.2 (e.trans h), fun h => VLevel.equiv_def'.2 (e.symm.trans h)⟩
  intro hz
  obtain ⟨h1, h2⟩ := H fun hn => hz fun ns => by rw [← congrFun e ns]; exact hn ns
  exact ⟨fun f hf => e'.2 (h1 f hf), fun j hj f hf => (h2 j hj f hf).imp_left e'.2⟩

theorem VInductDecl.ProjAllowed.instL {d : VInductDecl} {c : VConstructor} {ls : List VLevel}
    {k : Nat} (H : d.ProjAllowed c ls k) (ls' : List VLevel) :
    d.ProjAllowed c (ls.map (VLevel.inst ls')) k := by
  intro hz
  have hz' : ¬(d.level.inst ls).IsNeverZero := fun h => hz fun ns => by
    rw [← VLevel.inst_inst, VLevel.eval_inst]; exact h _
  obtain ⟨h1, h2⟩ := H hz'
  refine ⟨fun f hf => ?_, fun j hj f hf => ?_⟩
  · rw [← VLevel.inst_inst]; exact (VLevel.inst_congr_l (h1 f hf)).trans (by rfl)
  · rcases h2 j hj f hf with h | h
    · left; rw [← VLevel.inst_inst]; exact (VLevel.inst_congr_l h).trans (by rfl)
    · exact .inr h

namespace VEnv

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEq Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

inductive IsDefEq : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  /-- The `k`th projection of a term of a type `s` with a single constructor, as `inferProj`
  types it, at parameters `As` and indices `I` of `e`'s type. That the projection's type is a
  type, and agrees with its type at `e'` and other parameters `As'` of the same type, are
  premises: when an earlier field is a term the projection may not take, its projection is
  substituted where the field's type does not mention it, and these only follow by
  strengthening that variable away. `VInductDecl.ProjAllowed` says why the rule is sound when the
  instance may be a proposition, and why the fields after the `k`th do not matter for that. -/
  | projDF :
    env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → (∀ l ∈ ls, l.WF uvars) → ls.length = d.uvars →
    As.length = d.params.length → I.length = T.indices.length →
    As'.length = d.params.length → I'.length = T.indices.length →
    Γ ⊢ .appN (.const s ls) (As ++ I) ≡ .appN (.const s ls) (As' ++ I') : .sort u →
    Γ ⊢ e ≡ e' : .appN (.const s ls) (As ++ I) →
    d.ProjAllowed c ls k →
    Γ ⊢ c.projType ls s k As e ≡ c.projType ls s k As' e' : .sort (f.level.inst ls) →
    Γ ⊢ .proj s k e ≡ .proj s k e' : c.projType ls s k As e
  /-- A projection of the constructor applied to fields is the field (`reduceProj`). -/
  | projIota :
    env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    c.fields[k]? = some f → fs[k]? = some a → (∀ l ∈ ls, l.WF uvars) → ls.length = d.uvars →
    As.length = d.params.length → fs.length = c.fields.length → I.length = T.indices.length →
    Γ ⊢ .appN (.const c.name ls) (As ++ fs) : .appN (.const s ls) (As ++ I) →
    d.ProjAllowed c ls k →
    Γ ⊢ c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)) : .sort (f.level.inst ls) →
    Γ ⊢ a : c.projType ls s k As (.appN (.const c.name ls) (As ++ fs)) →
    Γ ⊢ .proj s k (.appN (.const c.name ls) (As ++ fs)) ≡ a :
      c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))
  /-- Structure eta: a term of a non-recursive single-constructor type without indices is the
  constructor applied to its projections (`tryEtaStruct`). -/
  | projEta :
    env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] → T.indices = [] →
    d.isRec = false → (∀ l ∈ ls, l.WF uvars) → ls.length = d.uvars →
    As.length = d.params.length →
    Γ ⊢ e : .appN (.const s ls) As →
    Γ ⊢ .appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e) : .appN (.const s ls) As →
    Γ ⊢ e ≡ .appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e) : .appN (.const s ls) As

end

def HasType (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEq env U Γ e e A

def IsType (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, env.HasType U Γ A (.sort u)

def IsDefEqU (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) :=
  ∃ A, env.IsDefEq U Γ e₁ e₂ A

end VEnv

def VExpr.WF (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) := env.IsDefEqU U Γ e e

def VConstant.WF (env : VEnv) (ci : VConstant) : Prop := env.IsType ci.uvars [] ci.type

def VDefEq.WF (env : VEnv) (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type ∧ env.HasType df.uvars [] df.rhs df.type

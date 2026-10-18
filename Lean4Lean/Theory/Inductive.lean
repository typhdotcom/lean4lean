import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

/-!
# Inductive types

An inductive block adds, in order, its type formers, its constructors, one recursor per type and an
iota rule per constructor, and records itself for each of its types (`VEnv.addBlock`). This
mirrors `Lean4Lean.Environment.addInductive` (`Lean4Lean/Inductive/Add.lean`): the recursor's type
and the right-hand side of each iota rule are built from the same pieces, in the same binder
order, as `AddInductive.run` builds them. Primitive projections, their computation on a
constructor and structure eta are rules of the type theory (`VEnv.IsDefEq.projDF`, `projIota` and
`projEta`), read off the recorded block.

The rules are closed equations over the recursor's binders, the way `VDefEq` states every rule:
`rec ps Ms ms (idx_c) (c ps fs) ≡ m_c fs ihs`, abstracted over `ps Ms ms fs`.

The kernel checks positivity, universe levels and a field's recursive view in separate passes
over the constructor types, so `VInductDecl.WF` states each separately and up to definitional
equality: each is then a consequence of the pass that checks it.

Two of the kernel's inductive reductions need no rule of their own here:
* K-like reduction (`toCtorWhenK`) replaces a proof of a subsingleton by its constructor; proof
  irrelevance makes the two defeq, and then the iota rule applies.
* Unit-like defeq (`isDefEqUnitLike`) relates any two inhabitants of a fieldless non-recursive
  structure; eta makes each defeq to the constructor.

Not covered: nested inductives. A declaration here is a mutual block whose constructors mention
its types only directly; the kernel turns a nested block into such a block plus auxiliary types,
and then restores the nested occurrences, which this spec does not model.
-/

namespace Lean4Lean

namespace VExpr

/-- References to a telescope of `n` binders, outermost first, whose innermost binder is
`bvar k`. -/
def bvars (n k : Nat) : List VExpr := (List.range n).reverse.map fun i => .bvar (i + k)

/-- Lift each entry of a telescope past `n` binders inserted beneath it: entry `i` sits under the
`i` entries before it, so the cutoff grows along the telescope. -/
def liftTele (n : Nat) : List VExpr → (k : Nat := 0) → List VExpr
  | [], _ => []
  | A :: As, k => A.liftN n k :: liftTele n As (k + 1)

/-- Move `e` from under the parameters, `k` fields and `l` further binders, to under the
parameters, `a` new binders, all `m` fields, `b` new binders and the same `l` binders. -/
def reseat (e : VExpr) (a k m b l : Nat) : VExpr :=
  (e.liftN (m - k + b) l).liftN a (l + m + b)

/-- Whether `e` mentions one of the constants `ns`. -/
def mentions (ns : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => ns.contains c
  | .app f a => f.mentions ns || a.mentions ns
  | .lam A b | .forallE A b => A.mentions ns || b.mentions ns
  | .proj s _ e => ns.contains s || e.mentions ns

end VExpr

namespace VEnv
variable (env : VEnv) (U : Nat)

/-- Each entry of a telescope is a type in the context of the entries before it. -/
inductive IsTele : List VExpr → List VExpr → Prop
  | nil : IsTele Γ []
  | cons : env.IsType U Γ A → IsTele (A :: Γ) As → IsTele Γ (A :: As)

/-- Two telescopes agree entry by entry, each in the context of the second's earlier entries. -/
inductive TeleDefEq : List VExpr → List VExpr → List VExpr → Prop
  | nil : TeleDefEq Γ [] []
  | cons : env.IsDefEqU U Γ A B → TeleDefEq (B :: Γ) As Bs → TeleDefEq Γ (A :: As) (B :: Bs)

/-- Add constants one after another. -/
def addConstList (env : VEnv) (cs : List (Name × VConstant)) : Option VEnv :=
  cs.foldlM (fun env (n, ci) => env.addConst n ci) env

/-- Add rules one after another. -/
def addDefEqList (env : VEnv) (dfs : List VDefEq) : VEnv := dfs.foldl addDefEq env

end VEnv

namespace VConstructor
variable (c : VConstructor)

/-- The recursive fields, each with its position among the fields. -/
def recFields : List (Nat × VRecArg) :=
  c.fields.zipIdx.filterMap fun (f, k) => f.recArg.map (k, ·)

/-- The fields before the `k`th that its projection skips: no field from one of them to the `k`th
mentions it (`VConstructor.Unused`). -/
def Skipped (k j : Nat) : Prop := j < k ∧ c.Unused k j

open Classical in
/-- The lift from the parameters and the fields before the `i`th that the `k`th projection does not
skip, to the parameters and all the fields before the `i`th. -/
noncomputable def keptLift (k : Nat) : Nat → Lift
  | 0 => .refl
  | i + 1 => if c.Skipped k i then .skip (keptLift k i) else .cons (keptLift k i)

/-- A type under the parameters and the fields before the `i`th, with the fields the `k`th
projection skips removed. -/
noncomputable def strippedType (k i : Nat) (A : VExpr) : VExpr := A.subst (c.keptLift k i).inv

open Classical in
/-- The types of the fields before the `k`th that its projection does not skip, each with the
skipped fields before it removed. -/
noncomputable def keptFields (k : Nat) : List VExpr :=
  ((List.range k).filter fun j => ¬c.Skipped k j).map fun j =>
    c.strippedType k j ((c.fields[j]?.map VField.type).getD default)

end VConstructor

namespace VInductDecl
open VExpr (bvars liftTele)
variable (d : VInductDecl)

/-- The names of the block's types. -/
def names : List Name := d.types.map (·.name)

/-- The block's constructors in order, each with the position of its type. -/
def ctors : List (Nat × VConstructor) :=
  (d.types.zipIdx.map fun (T, j) => T.ctors.map (j, ·)).flatten

/-- The recursor eliminates into every sort, not only `Prop`. -/
def LargeElim : Prop := d.largeElim

/-- When the recursor may eliminate into every sort: when the block cannot be a proposition, and
otherwise only for a single type with at most one constructor, every field of which is a proof or
appears among the indices of the constructor's result, so that it is determined by the type being
eliminated. The kernel's `isLargeEliminator` tests this syntactically, so it can answer no where
this holds; eliminating only into `Prop` is always sound. -/
def LargeElimOK : Prop :=
  d.level.IsNeverZero ∨
  ∃ T, d.types = [T] ∧ (T.ctors = [] ∨ ∃ c, T.ctors = [c] ∧
    ∀ k (f : VField), c.fields[k]? = some f → ¬f.level ≈ .zero →
      .bvar (c.fields.length - 1 - k) ∈ c.indices)

/-- The kernel's `isKTarget`: a single type in `Prop` with one constructor and no fields. The
kernel reduces its recursor on any major premise whose indices match the constructor's; here that
follows from proof irrelevance and the iota rule, so it adds no rule. -/
def IsKTarget : Prop :=
  d.level ≈ .zero ∧ ∃ T c, d.types = [T] ∧ T.ctors = [c] ∧ c.fields = []

open Classical in
noncomputable def recUVars : Nat := if d.LargeElim then d.uvars + 1 else d.uvars

open Classical in
/-- The block's level parameters as the recursor sees them: after the motive's, when it has one. -/
noncomputable def recLevels : List VLevel :=
  if d.LargeElim then (List.range d.uvars).map (.param <| · + 1) else VLevel.params d.uvars

open Classical in
noncomputable def motiveLevel : VLevel := if d.LargeElim then .param 0 else .zero

/-! The recursor is built for block levels `ls` and motive sort `v`. -/
section
variable (ls : List VLevel) (v : VLevel)

/-- The `j`th motive's type, under the parameters and the motives before it. -/
def motiveType (j : Nat) (T : VInductiveType) : VExpr :=
  let k := T.indices.length
  .foralls (liftTele j (T.indices.map (·.instL ls))) <|
    .forallE (.appN (.const T.name ls) (bvars d.params.length (j + k) ++ bvars k 0)) (.sort v)

def motiveTypes : List VExpr := d.types.zipIdx.map fun (T, j) => d.motiveType ls v j T

/-- The minor premise for constructor `c` of the `j`th type, under the parameters, the motives,
and the `q` minor premises before it: the fields, then an inductive hypothesis per recursive
field, concluding the motive at `c` applied to the fields. -/
def minorType (q j : Nat) (c : VConstructor) : VExpr :=
  let n := d.params.length
  let T := d.types.length
  let m := c.fields.length
  let u := c.recFields.length
  let fields := liftTele (T + q) (c.fields.map (·.type.instL ls))
  let ihs := c.recFields.zipIdx.map fun ((k, ra), r) =>
    let l := ra.binders.length
    let xs := ra.binders.zipIdx.map fun (A, i) => (A.instL ls).reseat (T + q) k m r i
    let idx := ra.indices.map fun e => (e.instL ls).reseat (T + q) k m r l
    .foralls xs <| .app (.appN (.bvar (l + r + m + q + (T - 1 - ra.typeIdx))) idx)
      (.appN (.bvar (l + r + (m - 1 - k))) (bvars l 0))
  let idx := c.indices.map fun e => (e.instL ls).reseat (T + q) m m u 0
  .foralls (fields ++ ihs) <| .app (.appN (.bvar (u + m + q + (T - 1 - j))) idx)
    (.appN (.const c.name ls) (bvars n (T + q + m + u) ++ bvars m u))

def minorTypes : List VExpr := d.ctors.zipIdx.map fun ((j, c), q) => d.minorType ls q j c

/-- The recursor's binders up to its minor premises. -/
def recBinders : List VExpr :=
  d.params.map (·.instL ls) ++ d.motiveTypes ls v ++ d.minorTypes ls

/-- The `i`th type's recursor: over the parameters, motives, minor premises, indices, and the
major premise, it concludes the `i`th motive. -/
def recType (i : Nat) (Ti : VInductiveType) : VExpr :=
  let n := d.params.length
  let T := d.types.length
  let C := d.ctors.length
  let k := Ti.indices.length
  .foralls (d.recBinders ls v ++ liftTele (T + C) (Ti.indices.map (·.instL ls))) <|
    .forallE (.appN (.const Ti.name ls) (bvars n (T + C + k) ++ bvars k 0)) <|
      .app (.appN (.bvar (1 + k + C + (T - 1 - i))) (bvars k 1)) (.bvar 0)

/-- The `j`th type's recursor, at levels `recLs`. -/
def recConst (recLs : List VLevel) (j : Nat) : VExpr :=
  .const (Lean.mkRecName ((d.types[j]?.map (·.name)).getD .anonymous)) recLs

/-- The iota rule for constructor `c` of the `j`th type, the `q`th constructor of the block, with
the recursors at levels `recLs`. Over the recursor's binders and `c`'s fields, the recursor at
`c` applied to the fields is the minor premise applied to the fields and to the recursor at each
recursive field. -/
def iotaRule (recLs : List VLevel) (q j : Nat) (c : VConstructor) : VDefEq :=
  let n := d.params.length
  let T := d.types.length
  let C := d.ctors.length
  let m := c.fields.length
  let binders := d.recBinders ls v ++ liftTele (T + C) (c.fields.map (·.type.instL ls))
  let ps := bvars n (T + C + m)
  let idx := c.indices.map fun e => (e.instL ls).reseat (T + C) m m 0 0
  let ctorApp := VExpr.appN (.const c.name ls) (ps ++ bvars m 0)
  let lhs := VExpr.appN (d.recConst recLs j)
    (ps ++ bvars T (C + m) ++ bvars C m ++ idx ++ [ctorApp])
  let ihs := c.recFields.map fun (k, ra) =>
    let l := ra.binders.length
    let xs := ra.binders.zipIdx.map fun (A, i) => (A.instL ls).reseat (T + C) k m 0 i
    let idx := ra.indices.map fun e => (e.instL ls).reseat (T + C) k m 0 l
    .lams xs <| .app
      (.appN (d.recConst recLs ra.typeIdx) (bvars n (T + C + m + l) ++
        bvars T (C + m + l) ++ bvars C (m + l) ++ idx))
      (.appN (.bvar (l + (m - 1 - k))) (bvars l 0))
  { uvars := recLs.length
    lhs := .lams binders lhs
    rhs := .lams binders <| .appN (.bvar (m + (C - 1 - q))) (bvars m 0 ++ ihs)
    type := .foralls binders <| .app (.appN (.bvar (m + C + (T - 1 - j))) idx) ctorApp }

end

def typeConsts : List (Name × VConstant) :=
  d.types.map fun T => (T.name, ⟨d.uvars, T.type⟩)

def ctorConsts : List (Name × VConstant) :=
  d.ctors.map fun p => (p.2.name, ⟨d.uvars, p.2.type⟩)

noncomputable def recConsts : List (Name × VConstant) :=
  d.types.zipIdx.map fun p =>
    (Lean.mkRecName p.1.name, ⟨d.recUVars, d.recType d.recLevels d.motiveLevel p.2 p.1⟩)

noncomputable def iotaRules : List VDefEq :=
  d.ctors.zipIdx.map fun ((j, c), q) =>
    d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c

/-- The view of a recursive field the kernel's `isRecArg` takes, which the recursor's inductive
hypothesis is built from. `k` fields precede it, under the parameters. A field the kernel does not
see as recursive gets no inductive hypothesis, which only weakens the recursor. -/
def RecArgWF (env : VEnv) (Γ : List VExpr) (k : Nat) (f : VField) : Prop :=
  match f.recArg with
  | some ra => ∃ T, d.types[ra.typeIdx]? = some T ∧ ra.indices.length = T.indices.length ∧
    env.IsDefEqU d.uvars Γ f.type (.foralls ra.binders <| .appN
      (.const T.name (VLevel.params d.uvars))
      (bvars d.params.length (k + ra.binders.length) ++ ra.indices))
  | none => True

/-- Strict positivity, the kernel's `checkPositivity`, up to definitional equality: under `Γ`,
`k` binders below the parameters, `t` is free of the block's types, or is a pi whose domain is
free of them and whose codomain is positive, or applies a type of the block to the parameters and
to indices free of them. -/
inductive Positive (env : VEnv) : List VExpr → Nat → VExpr → Prop
  | none : env.IsDefEqU d.uvars Γ t A → !A.mentions d.names → Positive env Γ k t
  | pi : env.IsDefEqU d.uvars Γ t (.forallE A B) → !A.mentions d.names →
    Positive env (A :: Γ) (k + 1) B → Positive env Γ k t
  | app {T : VInductiveType} {j : Nat} {is : List VExpr} : d.types[j]? = some T → is.length = T.indices.length →
    env.IsDefEqU d.uvars Γ t (.appN (.const T.name (VLevel.params d.uvars))
      (bvars d.params.length k ++ is)) →
    is.all (!·.mentions d.names) → Positive env Γ k t

/-- `FieldsWF env Γ k Ds fs`: the fields `fs` of a constructor whose declared field domains are
`Ds`, checked in `Γ`, the parameters followed by `k` fields. The universe bound is checked at the
sort the kernel infers for the declared domain, and `f.level` is the sort the elimination test
infers; the two agree up to uniqueness of typing. -/
inductive FieldsWF (env : VEnv) : List VExpr → Nat → List VExpr → List VField → Prop
  | nil : FieldsWF env Γ k [] []
  | cons :
    env.IsDefEqU d.uvars Γ D f.type →
    env.HasType d.uvars Γ f.type (.sort f.level) →
    f.level.WF d.uvars →
    (∃ u, env.HasType d.uvars Γ f.type (.sort u) ∧ (d.level ≈ .zero ∨ u ≤ d.level)) →
    (d.isUnsafe = false → d.Positive env Γ k f.type) →
    d.RecArgWF env Γ k f →
    FieldsWF env (f.type :: Γ) (k + 1) Ds fs →
    FieldsWF env Γ k (D :: Ds) (f :: fs)

end VInductDecl

/-- A type former's index telescope, read off its type as the recursor reads it: in an environment
with the block's types, which the kernel normalizes in. -/
structure VInductiveType.WF (env : VEnv) (d : VInductDecl) (T : VInductiveType) : Prop where
  indices : env.IsTele d.uvars d.params.reverse T.indices
  defeq : env.IsDefEqU d.uvars [] T.type (.foralls (d.params ++ T.indices) (.sort d.level))

/-- A constructor of `T`, as `checkConstructors` checks it, in an environment with the block's
types. Its declared type is syntactically a telescope of parameters agreeing with the block's,
then fields, ending in `T` at the parameters and indices that do not mention the block. -/
structure VConstructor.WF (env : VEnv) (d : VInductDecl) (T : VInductiveType)
    (c : VConstructor) : Prop where
  type : env.IsType d.uvars [] c.type
  shape : ∃ ps Ds, c.type = .foralls (ps ++ Ds) (.appN (.const T.name (VLevel.params d.uvars))
      (VExpr.bvars d.params.length c.fields.length ++ c.indices)) ∧
    env.TeleDefEq d.uvars [] ps d.params ∧ d.FieldsWF env d.params.reverse 0 Ds c.fields
  indices : c.indices.length = T.indices.length ∧ c.indices.all (!·.mentions d.names)
  /-- With the earlier fields its projection skips removed, each field's type is still a type of
  its sort. This is the strengthening `inferProj` relies on when it lets a projection past an
  earlier field that is not a proof but that nothing after it mentions. -/
  projFields : ∀ k (f : VField), c.fields[k]? = some f →
    env.IsTele d.uvars d.params.reverse (c.keptFields k) ∧
    env.HasType d.uvars ((c.keptFields k).reverse ++ d.params.reverse)
      (c.strippedType k k f.type) (.sort f.level)

/-- An inductive block as `addInductive` checks it, for a block without nested occurrences. -/
structure VInductDecl.WF (env : VEnv) (d : VInductDecl) : Prop where
  nonempty : d.types ≠ []
  level : d.level.WF d.uvars
  params : env.IsTele d.uvars [] d.params
  types : ∀ T ∈ d.types, env.IsType d.uvars [] T.type
  ctors : ∀ env', env.addConstList d.typeConsts = some env' →
    ∀ T ∈ d.types, T.WF env' d ∧ ∀ c ∈ T.ctors, c.WF env' d T
  isRec : d.isRec = false → ∀ T ∈ d.types, ∀ c ∈ T.ctors, ∀ f ∈ c.fields, f.recArg = none
  largeElim : d.LargeElim → d.LargeElimOK

/-- What `VEnv.addInduct` adds is well typed: the recursors given the types and constructors, and
the iota rules given the recursors. For a well-formed declaration this is a theorem
(`VInductDecl.generatedWF`); `VDecl.WF` asks for it alongside, so that a well-formed environment
is ordered without that theorem, which needs uniqueness of typing in well-formed environments. -/
def VInductDecl.GeneratedWF (env : VEnv) (d : VInductDecl) : Prop :=
  ∀ envT envC envR, env.addConstList d.typeConsts = some envT →
    envT.addConstList d.ctorConsts = some envC → envC.addConstList d.recConsts = some envR →
    (∀ p ∈ d.recConsts, p.2.WF envC) ∧ ∀ df ∈ d.iotaRules, df.WF envR

noncomputable def VEnv.addInduct (env : VEnv) (d : VInductDecl) : Option VEnv := do
  let env ← env.addConstList d.typeConsts
  let env ← env.addConstList d.ctorConsts
  let env ← env.addConstList d.recConsts
  (env.addDefEqList d.iotaRules).addBlock d

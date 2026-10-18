import Lean4Lean.Theory.VExpr

namespace Lean4Lean

/-! An inductive declaration as the kernel elaborates it: besides the declared types, it carries
the telescopes `addInductive` reads off them by weak-head normalizing and consuming type
annotations, since that is what the recursor is built from. All of it is stated over the block's
`uvars` level parameters, and telescopes are listed outermost first. -/

/-- The view of a recursive field: its type normalizes to `Π xs, I params indices`, where `I` is
the `typeIdx`-th type of the block. The `binders` sit under the parameters and the earlier
fields, and the `indices` under those and the `binders`. -/
structure VRecArg where
  binders : List VExpr
  typeIdx : Nat
  indices : List VExpr

structure VField where
  /-- The field's type with annotations consumed, under the parameters and the earlier fields. -/
  type : VExpr
  /-- The sort `type` lives in. -/
  level : VLevel
  recArg : Option VRecArg

structure VConstructor where
  name : Name
  /-- As declared: `Π params fields, I params indices`, syntactically. -/
  type : VExpr
  fields : List VField
  /-- The indices of the constructor's result, under the parameters and the fields. -/
  indices : List VExpr

/-- The occurrence an auxiliary type of a nested block stands for: the inductive type `ind` of an
earlier block, at universe levels `lvls` and at parameters `args`, which are stated over the
block's parameters and mention its types. -/
structure VNested where
  ind : Name
  lvls : List VLevel
  args : List VExpr

structure VInductiveType where
  name : Name
  /-- As declared. -/
  type : VExpr
  /-- The index telescope, under the parameters. -/
  indices : List VExpr
  ctors : List VConstructor
  /-- For an auxiliary type of a nested block, the occurrence it stands for. -/
  nested : Option VNested := none
  deriving Inhabited

structure VInductDecl where
  uvars : Nat
  /-- The parameter telescope, shared by the block. -/
  params : List VExpr
  /-- The sort every type of the block lives in. -/
  level : VLevel
  types : List VInductiveType
  /-- Whether some constructor binder mentions a type of the block: the kernel's `isRec`, which
  decides whether a structure gets eta. -/
  isRec : Bool
  /-- Whether the recursor eliminates into every sort, not only `Prop`: the kernel's
  `isLargeEliminator`, a syntactic test that `VInductDecl.LargeElimOK` justifies. -/
  largeElim : Bool
  isUnsafe : Bool
  /-- The auxiliary types of a nested block: an earlier inductive type at parameters mentioning
  the block's types, where a constructor uses one. They get motives, minor premises for their
  constructors (the earlier type's), recursors and iota rules, but no constants of their own. -/
  aux : List VInductiveType := []

structure VConstant where
  uvars : Nat
  type : VExpr

structure VDefEq where
  uvars : Nat
  lhs : VExpr
  rhs : VExpr
  type : VExpr

@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  /-- The block each inductive type belongs to, and its position there: primitive projections,
  their computation rule and structure eta are read off it. -/
  inducts : Name → Option (VInductDecl × Nat)

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  inducts _ := none

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.contains (env : VEnv) (name : Name) := ∃ ci, env.constants name = some ci

def VEnv.addConst (env : VEnv) (name : Name) (ci : VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

/-- Record the block `d` for each of its types, which must not have a block yet. -/
def VEnv.addBlock (env : VEnv) (d : VInductDecl) : Option VEnv :=
  if d.types.all fun T => (env.inducts T.name).isNone then
    some { env with inducts := fun n => match d.types.findIdx? (·.name == n) with
      | some t => some (d, t)
      | none => env.inducts n }
  else none

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  inducts : env1.inducts n = some b → env2.inducts n = some b

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3⟩

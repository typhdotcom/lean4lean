import Lean4Lean.Theory.VEnv

namespace Lean4Lean

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

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

structure VInductiveType where
  name : Name
  /-- As declared. -/
  type : VExpr
  /-- The index telescope, under the parameters. -/
  indices : List VExpr
  ctors : List VConstructor

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

inductive VDecl where
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
  | mutualDef (_ : List VDefVal)

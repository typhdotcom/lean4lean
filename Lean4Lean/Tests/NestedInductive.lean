import Lean4Lean.Environment

/-!
Regression tests for the nested-inductive parameter check added for
leanprover/lean4#14577.

When a nested occurrence `I Ds is` is eliminated, the parametric arguments `Ds` are dropped
from the generated auxiliary type, so they escape the ordinary type checking of the
declaration. The kernel checks them separately at the end; so must we.

Both declarations are built by hand rather than elaborated, so that the environment does
not already contain them and only the kernel path is exercised.
-/

namespace Lean4Lean.Tests.NestedInductive

open Lean

/-- `inductive Tree0 (α : Type) | node : Array (Tree0 α) → Tree0 α` -/
def treeDecl : Declaration :=
  let tree := fun a => mkApp (mkConst `Tree0 []) a
  .inductDecl [] 1
    [{ name := `Tree0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Tree0.node
         type := .forallE `α (.sort 1)
           (.forallE `es (mkApp (mkConst ``Array [.zero]) (tree (.bvar 0)))
             (tree (.bvar 1)) .default) .default }] }]
    false

/-- As above, but the dropped parametric argument `Tree0 Bool.true` is ill typed. -/
def badDecl : Declaration :=
  .inductDecl [] 1
    [{ name := `Bad0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Bad0.node
         type := .forallE `α (.sort 1)
           (.forallE `es
             (mkApp (mkConst ``Array [.zero])
               (mkApp (mkConst `Bad0 []) (mkConst ``Bool.true)))
             (mkApp (mkConst `Bad0 []) (.bvar 1)) .default) .default }] }]
    false

/-- `inductive LvlTree.{u} | node : List.{max u u} LvlTree.{u} → LvlTree.{u}`, whose nested
occurrence's level is not in normal form: the recursors keep it as written. -/
def lvlDecl : Declaration :=
  let u := Level.param `u
  let tree := mkConst `LvlTree [u]
  .inductDecl [`u] 0
    [{ name := `LvlTree
       type := .sort (.succ u)
       ctors := [{
         name := `LvlTree.node
         type := .forallE `es (mkApp (mkConst ``List [.max u u]) tree) tree .default }] }]
    false

/-- `inductive LetTree | node : (let L := List LetTree; L) → LetTree`: restoring its recursors
gives terms with a `let`, which are checked. -/
def letDecl : Declaration :=
  let tree := mkConst `LetTree []
  .inductDecl [] 0
    [{ name := `LetTree
       type := .sort 1
       ctors := [{
         name := `LetTree.node
         type := .forallE `es (.letE `L (.sort 1) (mkApp (mkConst ``List [.zero]) tree) (.bvar 0)
           false) tree .default }] }]
    false

/-- `inductive MdTree | node : List MdTree → MdTree` with the field's type under metadata, which
the recursors keep. -/
def mdDecl : Declaration :=
  let tree := mkConst `MdTree []
  .inductDecl [] 0
    [{ name := `MdTree
       type := .sort 1
       ctors := [{
         name := `MdTree.node
         type := .forallE `es (.mdata (KVMap.empty.insert `k (.ofBool true))
           (mkApp (mkConst ``List [.zero]) tree)) tree .default }] }]
    false

run_meta do
  let kenv := (← getEnv).toKernelEnv

  -- The restored recursors are Lean's, levels included.
  let .ok kenv' := kenv.addDecl {} lvlDecl | throwError "Lean's kernel rejected `LvlTree`"
  match Lean4Lean.addDecl kenv lvlDecl with
  | .error e => throwError "`LvlTree` was rejected: {← (e.toMessageData {}).toString}"
  | .ok lenv =>
    for n in [`LvlTree.rec, `LvlTree.rec_1, `LvlTree.node] do
      let same := match kenv'.find? n, lenv.find? n with
        | some (.recInfo a), some (.recInfo b) => a == b
        | some (.ctorInfo a), some (.ctorInfo b) => a == b
        | _, _ => false
      unless same do throwError "`{n}` differs from Lean's"
  let .ok kenv' := kenv.addDecl {} letDecl | throwError "Lean's kernel rejected `LetTree`"
  match Lean4Lean.addDecl kenv letDecl with
  | .error e => throwError "`LetTree` was rejected: {← (e.toMessageData {}).toString}"
  | .ok lenv =>
    for n in [`LetTree.rec, `LetTree.rec_1, `LetTree.node] do
      let same := match kenv'.find? n, lenv.find? n with
        | some (.recInfo a), some (.recInfo b) => a == b
        | some (.ctorInfo a), some (.ctorInfo b) => a == b
        | _, _ => false
      unless same do throwError "`{n}` differs from Lean's"
  let .ok kenv' := kenv.addDecl {} mdDecl | throwError "Lean's kernel rejected `MdTree`"
  match Lean4Lean.addDecl kenv mdDecl with
  | .error e => throwError "`MdTree` was rejected: {← (e.toMessageData {}).toString}"
  | .ok lenv =>
    for n in [`MdTree.rec, `MdTree.rec_1, `MdTree.node] do
      let same := match kenv'.find? n, lenv.find? n with
        | some (.recInfo a), some (.recInfo b) => a == b
        | some (.ctorInfo a), some (.ctorInfo b) => a == b
        | _, _ => false
      unless same do throwError "`{n}` differs from Lean's"

  -- A well-formed nested inductive must be accepted. Storing `aux2nested` abstracted over
  -- the parameters while checking it against a context of free variables regressed this
  -- into "type checker does not support loose bound variables" (#17).
  match Lean4Lean.addDecl kenv treeDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "nested inductive was rejected: {← (e.toMessageData {}).toString}"

  -- ... and an ill-typed dropped parameter must still be caught.
  match Lean4Lean.addDecl kenv badDecl with
  | .ok _ => throwError "nested inductive with an ill-typed parameter was accepted"
  | .error _ => pure ()

end Lean4Lean.Tests.NestedInductive

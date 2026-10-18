import Lean4Lean.Environment

/-!
What the type checker learns in a variable's scope is kept after the scope closes only if it does
not rest on the scope's variable, and comparing two lambdas or pis opens every binder, dependent
or not.
-/

namespace Lean4Lean.Tests.BinderScope

open Lean Lean4Lean TypeChecker

/-! `F a hI` and `b0` are definitionally equal once a proof `p : P a` is in the context (`hI` is
then `I.mk a p` by proof irrelevance, and `F` reduces), but not, as far as anyone knows, without
one: the type theory cannot type `c : G b0` below for `c : C (F a hI)` without `p`. -/

axiom B : Type
axiom b0 : B
axiom A : B → Type
axiom P : A b0 → Prop
inductive I : (n : B) → A n → Prop
  | mk (x : A b0) (h : P x) : I b0 x
noncomputable def F (a : A b0) (h : I b0 a) : B := I.rec (motive := fun _ _ _ => B) (fun _ _ => b0) h
axiom C : B → Type
axiom k : (n : B) → C n → C n → Unit
def G (n : B) : Type := C n

private def runM (r : Except Kernel.Exception α) : MetaM α := do
  match r with
  | .ok a => pure a
  | .error e => throwError "kernel operation failed: {← (e.toMessageData {}).toString}"

private def two : Expr := mkApp (.const ``Nat.succ []) (mkApp (.const ``Nat.succ []) (.const ``Nat.zero []))

run_meta do
  let env := (← getEnv).toKernelEnv
  let nat := Expr.const ``Nat []
  let current (s : State) (c : InferCache) (e : Expr) : Bool :=
    match c[e]? with
    | some c => s.scopeIds.valid c.lvl c.id
    | none => false
  -- What is inferred under a binder about `two`, which does not mention its variable, stays
  -- current. An entry about a term mentioning the variable may stay too, but is never found again:
  -- the next binder declares a different variable.
  let (inside, afterTwo, sx, sy) ← runM <| M.run env (x := do
    let (inside, sx) ← withLocalDecl `x .default nat fun x => do
      let sx := mkApp (.const ``Nat.succ []) x
      _ ← inferType sx
      _ ← inferType two
      let s ← get
      pure ((current s s.inferTypeI sx, current s s.inferTypeI two), sx)
    let sy ← withLocalDecl `x .default nat fun y => pure (mkApp (.const ``Nat.succ []) y)
    let s ← get
    pure (inside, current s s.inferTypeI two, sx, sy))
  unless inside == (true, true) do throwError "nothing was cached under the binder: {inside}"
  unless afterTwo do throwError "a fact not about the binder's variable was dropped"
  if sx == sy then throwError "a later binder reused the variable"
  -- Two lambdas whose bodies do not mention their variable are compared under a fresh variable.
  let f := Expr.lam `x nat (mkApp (.lam `y nat (.bvar 0) .default) (.const ``Nat.zero [])) .default
  let g := Expr.lam `x nat (.const ``Nat.zero []) .default
  let (eq, idx) ← runM <| M.run env (x := do
    let eq ← isDefEq f g
    pure (eq, (← get).ngen.idx))
  unless eq do throwError "the lambdas were not found equal"
  unless idx > 0 do throwError "comparing the lambdas opened no binder"
  -- And the same through `Lean4Lean.addDecl`.
  let decl : Declaration := .thmDecl
    { name := `binderScopeThm, levelParams := []
      type := mkApp3 (.const ``Eq [1]) (.forallE `x nat nat .default) f g
      value := mkApp2 (.const ``Eq.refl [1]) (.forallE `x nat nat .default) f }
  let .ok _ := Lean4Lean.addDecl env decl | throwError "lean4lean rejected `binderScopeThm`"
  let .ok _ := env.addDecl {} decl | throwError "Lean's kernel rejected `binderScopeThm`"

/-- `fun a hI c d => (fun p => fst p, snd)` at `(P a → α) × G b0`: `fst p` checks `c` and `d` at
`C (F a (I.mk a p))`, so the equivalence manager learns `C (F a hI) ≡ C (F a (I.mk a p)) ≡ C b0`
under `p`. `snd` is `c`, at `G b0`, outside `p`; `fst` also has `snd` checked under `p` when
`α` is `Unit × G b0`, so the check is cached. -/
private def leakDecl (name : Name) (cached : Bool) : Declaration :=
  let a := Expr.bvar 3; let hI := Expr.bvar 2; let c := Expr.bvar 1; let d := Expr.bvar 0
  let F' (a h : Expr) := mkApp2 (.const ``F []) a h
  let gb0 := mkApp (.const ``G []) (.const ``b0 [])
  let idc (c : Expr) := mkApp2 (.const ``id [1]) gb0 c
  let pa := mkApp (.const ``P []) a
  let kk := mkApp3 (.const ``k []) (F' (a.liftLooseBVars 0 1) (mkApp2 (.const ``I.mk [])
    (a.liftLooseBVars 0 1) (.bvar 0))) (c.liftLooseBVars 0 1) (d.liftLooseBVars 0 1)
  let α := if cached then mkApp2 (.const ``Prod [0, 0]) (.const ``Unit []) gb0 else .const ``Unit []
  let fstBody := if cached then
      mkApp4 (.const ``Prod.mk [0, 0]) (.const ``Unit []) gb0 kk (idc (c.liftLooseBVars 0 1))
    else kk
  let snd := if cached then idc c else c
  let body := mkApp4 (.const ``Prod.mk [0, 0]) (.forallE `p pa α .default) gb0
    (.lam `p pa fstBody .default) snd
  let ctx := [(`a, mkApp (.const ``A []) (.const ``b0 [])),
    (`hI, mkApp2 (.const ``I []) (.const ``b0 []) (.bvar 0)),
    (`c, mkApp (.const ``C []) (F' (.bvar 1) (.bvar 0))), (`d, mkApp (.const ``C []) (.const ``b0 []))]
  let ty := ctx.foldr (fun (n, A) b => .forallE n A b .default)
    (mkApp2 (.const ``Prod [0, 0]) (.forallE `p pa α .default) gb0)
  let val := ctx.foldr (fun (n, A) b => .lam n A b .default) body
  .defnDecl { name, levelParams := [], type := ty, value := val, hints := .opaque, safety := .safe }

run_meta do
  let env := (← getEnv).toKernelEnv
  -- Lean's kernel keeps both equivalences after leaving `p` and accepts both; for lean4lean they
  -- rest on `p`, as does the check cached under `p` with them, so they end with it, and it rejects
  -- both.
  for (n, cached) in [(`leakEqv, false), (`leakCache, true)] do
    unless (env.addDecl {} (leakDecl n cached)) matches .ok _ do
      throwError "Lean's kernel rejected `{n}`"
    match Lean4Lean.addDecl env (leakDecl n cached) with
    | .ok _ => throwError "lean4lean accepted `{n}`"
    | .error e =>
      let msg ← (e.toMessageData {}).toString
      unless (msg.splitOn "type mismatch").length > 1 do
        throwError "lean4lean rejected `{n}` for the wrong reason: {msg}"

end Lean4Lean.Tests.BinderScope

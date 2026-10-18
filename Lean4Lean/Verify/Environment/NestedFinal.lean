import Lean4Lean.Verify.Environment.Run
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Environment.Restore

/-!
# The final phase of `addInductive` on a nested block

Once the translated block has been checked, `Environment.addInductive` restores what the flat
check produced and adds it to the environment it started from (`nestedFinal`, the code after
`if numNested = 0 then return env'`; `Environment.addInductive_eq`). `nestedFinal.WF` reads a
successful run (`NestedFinalOK`): the restored types, constructors and recursors as built from the
translation's, the check that no auxiliary name survives restoring (`anySub_auxP_false`), the
types-as-axioms environment and the nested occurrences' check in it, the checks of restored terms
with a `let` (`checkRestored.WF`), and the constants added, which are `AddInduct`'s in another
order (`NestedFinalOK.addConsts`). `mkAuxRecNameMap_spec` gives the auxiliary recursors' names.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-- The part of `Environment.addInductive` that adds a nested block, after its translation has been
checked into `env'`. -/
def nestedFinal (env env' : Environment) (lparams : List Name) (types : List InductiveType)
    (res : ElimNestedInductive.Result) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    Except Exception Environment := do
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  let restore e := res.restoreNested env' lparams e recNameMap'
  let inds ← types.mapM fun indType => do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    let ctors ← ind.ctors.mapM fun ctorName => do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      return { ctor with type := restore ctor.type }
    return ({ ind with all := allIndNames }, ctors)
  let recs ← (types.map (mkRecName ·.name) ++ recNames').mapM fun recName => do
    let newRecName := recNameMap'.getD recName recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let rules := recInfo.rules.map fun rule =>
      { rule with
        ctor := if newRecName == recName then rule.ctor else res.restoreCtorName env' rule.ctor
        rhs := restore rule.rhs }
    return { recInfo with name := newRecName, type := restore recInfo.type, all := allIndNames, rules }
  let auxNames : NameSet := (res.types.drop types.length).foldl (init := .ofList recNames')
    fun s t => t.ctors.foldl (·.insert ·.name) (s.insert t.name)
  let isAux (c : Name) := auxNames.contains c
  let restored := inds.flatMap (·.2.map (·.type)) ++ recs.flatMap fun r => r.type :: r.rules.map (·.rhs)
  for e in restored do
    if e.anySubterm fun | .const c _ => isAux c | .proj s _ _ => isAux s | _ => false then
      throw <| .other "invalid nested inductive datatype, an auxiliary constant was not restored"
  let ax (env : Environment) (name : Name) (levelParams : List Name) (type : Expr) := do
    env.checkName name allowPrimitive
    return env.add <| .axiomInfo { name, levelParams, type, isUnsafe }
  let check (env : Environment) (levelParams : List Name) (e : Expr) (isType : Bool) := do
    if e.anySubterm (·.isLet) then
      TypeChecker.M.run env safety {} levelParams fuel do
        let ty ← TypeChecker.checkType e
        if isType then _ ← TypeChecker.ensureSort ty e
  let envT ← inds.foldlM (fun env (ind, _) => ax env ind.name lparams ind.type) env
  TypeChecker.M.run envT (safety := safety) (lctx := res.lctx) (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do _ ← TypeChecker.checkType e
  if restored.any (·.anySubterm (·.isLet)) then
    for (_, ctors) in inds do
      for ctor in ctors do check envT lparams ctor.type true
    let envC ← inds.foldlM (init := envT) fun env (_, ctors) =>
      ctors.foldlM (fun env ctor => ax env ctor.name lparams ctor.type) env
    for r in recs do check envC r.levelParams r.type true
    let envR ← recs.foldlM (fun env r => ax env r.name r.levelParams r.type) envC
    for r in recs do
      for rule in r.rules do check envR r.levelParams rule.rhs false
  (·.2) <$> StateT.run (s := env) do
  for (ind, ctors) in inds, r in recs do
    (← get).checkName ind.name allowPrimitive
    modify (·.add <| .inductInfo ind)
    for ctor in ctors do
      (← get).checkName ctor.name allowPrimitive
      modify (·.add <| .ctorInfo ctor)
    (← get).checkName r.name allowPrimitive
    modify (·.add <| .recInfo r)
  for r in recs.drop types.length do
    (← get).checkName r.name allowPrimitive
    modify (·.add <| .recInfo r)

theorem Except.ok_of_bind {ε α β} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `Environment.addInductive`, with the nested block's final phase as `nestedFinal`. -/
theorem Environment.addInductive_eq (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel = (do
      for indType in types do
        env.checkNoMVarNoFVar indType.name indType.type
        checkClosed indType.name indType.type
        for ctor in indType.ctors do
          env.checkNoMVarNoFVar ctor.name ctor.type
          checkClosed ctor.name ctor.type
          checkNoNestedAux ctor.name ctor.type
      let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
        |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
      let env' ← AddInductive.run nparams res.types res.aux2nested.size
        { env, allowPrimitive, lparams, fuel, safety := if isUnsafe then .unsafe else .safe }
      if res.aux2nested.size = 0 then return env'
      nestedFinal env env' lparams types res isUnsafe allowPrimitive fuel) := rfl

/-! ### Generic facts about successful runs -/

theorem Except.mapM_ok {ε α β} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by cases h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Except.ok_of_bind h
    obtain ⟨bs, hbs, h⟩ := Except.ok_of_bind h
    cases h; exact .cons hb (Except.mapM_ok hbs)

/-- A loop over a list that only yields, run to success, ran its body to success on each
element. -/
theorem Except.forIn_yield_ok {ε α} {f : α → PUnit → Except ε (ForInStep PUnit)}
    (hf : ∀ x u s, f x u = .ok s → s = .yield PUnit.unit) :
    ∀ {l : List α} {r : PUnit}, forIn l PUnit.unit f = .ok r → ∀ x ∈ l, ∃ s, f x PUnit.unit = .ok s
  | [], _, _ => nofun
  | x :: l, r, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, h1, h2⟩ := Except.ok_of_bind h
    obtain rfl := hf _ _ _ h1
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, h1⟩
    · exact Except.forIn_yield_ok hf h2 y hy

/-- Constants added one at a time, each under a name `checkName` accepts in the environment so
far. -/
inductive CheckedAdds (allowPrimitive : Bool) : Environment → List ConstantInfo → Environment → Prop
  | nil : CheckedAdds allowPrimitive env [] env
  | cons : env.checkName ci.name allowPrimitive = .ok () →
    CheckedAdds allowPrimitive (env.add ci) cis env' →
    CheckedAdds allowPrimitive env (ci :: cis) env'

theorem CheckedAdds.append {ap : Bool} :
    ∀ {env₁ env₂ env₃ : Environment} {as bs : List ConstantInfo},
    CheckedAdds ap env₁ as env₂ → CheckedAdds ap env₂ bs env₃ → CheckedAdds ap env₁ (as ++ bs) env₃
  | _, _, _, [], _, .nil, h => h
  | _, _, _, _ :: _, _, .cons h1 h2, h => .cons h1 (h2.append h)

theorem CheckedAdds.eq {ap : Bool} :
    ∀ {env env' : Environment} {cis : List ConstantInfo},
    CheckedAdds ap env cis env' → env' = cis.foldl (fun e ci => e.add ci) env
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons _ h => h.eq

/-- What checked additions give: the constants are inserted, under distinct names fresh for the
environment, each a primitive's only where those are allowed. -/
theorem CheckedAdds.spec {ap : Bool} :
    ∀ {env env' : Environment} {cis : List ConstantInfo}, env.constants.WF →
    CheckedAdds ap env cis env' →
    env'.constants = insertConsts env.constants cis ∧ env'.quotInit = env.quotInit ∧
    (cis.map (·.name)).Nodup ∧ (∀ ci ∈ cis, env.find? ci.name = none) ∧
    (∀ ci ∈ cis, Environment.primitives.contains ci.name → ap)
  | _, _, [], _, .nil => ⟨rfl, rfl, .nil, nofun, nofun⟩
  | env, env', ci :: cis, hwf, .cons h1 h2 => by
    obtain ⟨hfr, hp⟩ := checkName.WF hwf ci.name ap _ h1
    have hfr' : env.constants.find? ci.name = none := by
      rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at hfr
    have hwf' : (env.add ci).constants.WF := hwf.insert ci.name ci hfr'
    obtain ⟨e1, e2, e3, e4, e5⟩ := h2.spec hwf'
    refine ⟨e1, e2, List.nodup_cons.2 ⟨fun hm => ?_, e3⟩, fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
      have := e4 c hc
      rw [he, Kernel.Environment.find?, hwf'.find?'_eq_find?] at this
      change (env.constants.insert ci.name ci).find? ci.name = none at this
      rw [hwf.find?_insert] at this; simp at this
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact hfr
      · have := e4 c hc
        rw [Kernel.Environment.find?, hwf'.find?'_eq_find?] at this
        change (env.constants.insert ci.name ci).find? c.name = none at this
        rw [hwf.find?_insert] at this
        split at this; · cases this
        rwa [Kernel.Environment.find?, hwf.find?'_eq_find?]
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact hp
      · exact e5 c hc

theorem CheckedAdds.foldlM {ap : Bool} {α} {F : Environment → α → Except Exception Environment}
    {g : α → List ConstantInfo} (hF : ∀ e x e', F e x = .ok e' → CheckedAdds ap e (g x) e') :
    ∀ {xs : List α} {env env' : Environment}, xs.foldlM F env = .ok env' →
      CheckedAdds ap env (xs.flatMap g) env'
  | [], _, _, h => by cases h; exact .nil
  | x :: xs, env, env', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨e, h1, h2⟩ := Except.ok_of_bind h
    exact (hF _ _ _ h1).append (CheckedAdds.foldlM hF h2)

theorem CheckedAdds.single {ap : Bool} {env env' : Environment} {ci : ConstantInfo}
    (h : (do env.checkName ci.name ap; pure (env.add ci) : Except Exception Environment) = .ok env') :
    CheckedAdds ap env [ci] env' := by
  obtain ⟨_, h1, h2⟩ := Except.ok_of_bind h
  cases h2; exact .cons h1 .nil

section
local notation "SM" => StateT Environment (Except Exception)

theorem CheckedAdds.step {ap : Bool} {ci : ConstantInfo} {env env' : Environment} {u : PUnit}
    (h : (do
      let e ← get
      liftM (e.checkName ci.name ap)
      modify fun x => Lean.Kernel.Environment.add x ci : SM PUnit).run env = .ok (u, env')) :
    CheckedAdds ap env [ci] env' := by
  simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind, liftM, monadLift,
    MonadLift.monadLift, StateT.run_lift, bind_assoc] at h
  obtain ⟨_, h1, h2⟩ := Except.ok_of_bind h
  cases h2; exact .cons h1 .nil

theorem CheckedAdds.ofForIn {ap : Bool} {β} {g : β → ConstantInfo} :
    ∀ {xs : List β} {env env' : Environment} {u : PUnit},
    (forIn xs PUnit.unit fun x _ => (do
      let e ← get
      liftM (e.checkName (g x).name ap)
      modify fun y => Lean.Kernel.Environment.add y (g x)
      pure (ForInStep.yield PUnit.unit) : SM (ForInStep PUnit))).run env = .ok (u, env') →
    CheckedAdds ap env (xs.map g) env'
  | [], _, _, _, h => by cases h; exact .nil
  | x :: xs, env, env', u, h => by
    rw [List.forIn_cons, StateT.run_bind] at h
    obtain ⟨⟨r, e₁⟩, h1, h2⟩ := Except.ok_of_bind h
    simp only [← bind_assoc] at h1
    rw [StateT.run_bind] at h1
    obtain ⟨⟨_, e₀⟩, h3, h4⟩ := Except.ok_of_bind h1
    cases h4
    exact (CheckedAdds.step h3).append (CheckedAdds.ofForIn h2)

/-- The constants the final loop adds alongside each type: the type, its constructors and its
recursor. -/
def finalZip (inds : List (InductiveVal × List ConstructorVal)) (recs : List RecursorVal) :
    List ConstantInfo :=
  (List.zipWith (fun p r => .inductInfo p.1 :: (p.2.map .ctorInfo ++ [.recInfo r])) inds recs).flatten

theorem CheckedAdds.ofForInZip {ap : Bool} :
    ∀ {inds : List (InductiveVal × List ConstructorVal)} {recs : List RecursorVal}
      {env env' : Environment} {s},
    (forIn inds (Std.toStream recs) fun x __s => (match Std.Stream.next? __s with
      | none => pure (ForInStep.done __s)
      | some (r, s') => do
        let e ← get
        liftM (e.checkName x.1.name ap)
        modify fun y => Lean.Kernel.Environment.add y (.inductInfo x.1)
        forIn x.2 PUnit.unit fun ctor _ => do
          let e ← get
          liftM (e.checkName ctor.name ap)
          modify fun y => Lean.Kernel.Environment.add y (.ctorInfo ctor)
          pure (ForInStep.yield PUnit.unit)
        let e ← get
        liftM (e.checkName r.name ap)
        modify fun y => Lean.Kernel.Environment.add y (.recInfo r)
        pure (ForInStep.yield s') : SM (ForInStep (List RecursorVal)))).run env = .ok (s, env') →
    CheckedAdds ap env (finalZip inds recs) env'
  | [], _, _, _, _, h => by cases h; exact .nil
  | x :: inds, [], env, env', s, h => by
    rw [List.forIn_cons, StateT.run_bind] at h
    obtain ⟨⟨r, e₁⟩, h1, h2⟩ := Except.ok_of_bind h
    cases h1; cases h2; exact .nil
  | x :: inds, r :: recs, env, env', s, h => by
    rw [List.forIn_cons, StateT.run_bind] at h
    obtain ⟨⟨st, e₁⟩, h1, h2⟩ := Except.ok_of_bind h
    simp only [Std.toStream, Std.Stream.next?] at h1
    simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind, liftM, monadLift,
      MonadLift.monadLift, StateT.run_lift, bind_assoc, StateT.run_pure] at h1
    obtain ⟨⟨⟩, c1, h1⟩ := Except.ok_of_bind h1
    obtain ⟨⟨_, e₂⟩, c2, h1⟩ := Except.ok_of_bind h1
    obtain ⟨⟨⟩, c3, h1⟩ := Except.ok_of_bind h1
    cases h1
    simp only at h2 c3
    have := CheckedAdds.ofForInZip h2
    show CheckedAdds ap env (.inductInfo x.1 :: (x.2.map .ctorInfo ++ [.recInfo r]) ++
      finalZip inds recs) env'
    rw [List.cons_append, List.append_assoc]
    exact .cons c1 ((CheckedAdds.ofForIn (g := ConstantInfo.ctorInfo) c2).append
      (.cons (ci := .recInfo r) c3 this))

end

/-! ### The final phase -/

/-- The terms the final phase restores: the constructors' types, and the recursors' types and
rules' right-hand sides. -/
def restoredTerms (inds : List (InductiveVal × List ConstructorVal)) (recs : List RecursorVal) :
    List Expr :=
  inds.flatMap (·.2.map (·.type)) ++ recs.flatMap fun r => r.type :: r.rules.map (·.rhs)

/-- The names the final phase checks the restored terms for. -/
def auxNameSet (res : ElimNestedInductive.Result) (types : List InductiveType)
    (recNames' : List Name) : NameSet :=
  (res.types.drop types.length).foldl (init := .ofList recNames')
    fun s t => t.ctors.foldl (·.insert ·.name) (s.insert t.name)

/-- The check the final phase makes of a restored term, when it has a `let`. -/
def checkRestored (env : Environment) (safety : DefinitionSafety) (levelParams : List Name)
    (fuel : FuelConfig) (e : Expr) (isType : Bool) : Except Exception Unit :=
  if e.anySubterm (·.isLet) then
    TypeChecker.M.run env safety {} levelParams fuel do
      let ty ← TypeChecker.checkType e
      if isType then _ ← TypeChecker.ensureSort ty e
  else pure ()

/-- The block's types, as the axioms the final phase checks restored terms against. -/
def typeAxiomsN (inds : List (InductiveVal × List ConstructorVal)) (lparams : List Name)
    (isUnsafe : Bool) : List ConstantInfo :=
  inds.map fun p => .axiomInfo { name := p.1.name, levelParams := lparams, type := p.1.type, isUnsafe }

/-- The block's constructors, restored, as axioms. -/
def ctorAxiomsN (inds : List (InductiveVal × List ConstructorVal)) (lparams : List Name)
    (isUnsafe : Bool) : List ConstantInfo :=
  inds.flatMap fun p => p.2.map fun c =>
    .axiomInfo { name := c.name, levelParams := lparams, type := c.type, isUnsafe }

/-- The block's recursors, restored, as axioms. -/
def recAxiomsN (recs : List RecursorVal) (isUnsafe : Bool) : List ConstantInfo :=
  recs.map fun r => .axiomInfo { name := r.name, levelParams := r.levelParams, type := r.type, isUnsafe }

/-- The constants the final phase adds, in its order: each type with its constructors and
recursor, then the auxiliary recursors. -/
def finalConsts (inds : List (InductiveVal × List ConstructorVal)) (recs : List RecursorVal) :
    List ConstantInfo :=
  finalZip inds recs ++ (recs.drop inds.length).map .recInfo

/-- A recursor as the final phase restores it from the translated block's. -/
def restoreRec (env' : Environment) (lparams : List Name) (types : List InductiveType)
    (res : ElimNestedInductive.Result) (n : Name) (r₀ : RecursorVal) : RecursorVal :=
  let m := (mkAuxRecNameMap env' types).2
  { r₀ with
    name := m.getD n n
    type := res.restoreNested env' lparams r₀.type m
    all := types.map (·.name)
    rules := r₀.rules.map fun rule =>
      { rule with
        ctor := if (m.getD n n == n) = true then rule.ctor else res.restoreCtorName env' rule.ctor
        rhs := res.restoreNested env' lparams rule.rhs m } }

/-- Every projection in `e` is out of a structure whose name satisfies `p`. -/
def _root_.Lean.Expr.ProjsOK (p : Name → Prop) : Expr → Prop
  | .app f a | .lam _ f a _ | .forallE _ f a _ => f.ProjsOK p ∧ a.ProjsOK p
  | .letE _ t v b _ => t.ProjsOK p ∧ v.ProjsOK p ∧ b.ProjsOK p
  | .mdata _ e => e.ProjsOK p
  | .proj s _ e => p s ∧ e.ProjsOK p
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ | .const .. => True

/-- What the final phase looks for in a restored term: an auxiliary constant, or a projection out of
an auxiliary type. -/
def auxP (S : NameSet) : Expr → Bool
  | .const c _ => S.contains c
  | .proj s _ _ => S.contains s
  | _ => false

theorem anySubterm_auxP (S : NameSet) (e : Expr) : e.anySubterm (auxP S) = e.anySub (auxP S) := by
  refine anySubterm_eq (fun a b h => ?_) e
  cases a <;> cases b <;>
    simp only [(· == ·), Expr.eqv_eq, Expr.eqv', Bool.and_eq_true, reduceCtorEq] at h <;>
    try rfl
  · rename_i n₁ _ n₂ _
    have : n₁ = n₂ := eq_of_beq (h.1 : (n₁ == n₂) = true)
    subst this; rfl
  · rename_i n₁ _ _ n₂ _ _
    have : n₁ = n₂ := eq_of_beq (h.1.2 : (n₁ == n₂) = true)
    subst this; rfl

/-- What the final phase of a nested block establishes when it succeeds. `inds` are the block's
types with their constructors, `recs` its recursors, own then auxiliary, `envT` the environment
with the types as axioms. -/
structure NestedFinalOK (env env' : Environment) (lparams : List Name) (types : List InductiveType)
    (res : ElimNestedInductive.Result) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (inds : List (InductiveVal × List ConstructorVal)) (recs : List RecursorVal)
    (envT envF : Environment) : Prop where
  indsSpec : List.Forall₂ (fun (t : InductiveType) (p : InductiveVal × List ConstructorVal) =>
    ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      p.1 = { ind with all := types.map (·.name) } ∧
      List.Forall₂ (fun n (c : ConstructorVal) => ∀ c₀, env'.find? n = some (.ctorInfo c₀) →
        c = { c₀ with type := res.restoreNested env' lparams c₀.type (mkAuxRecNameMap env' types).2 })
        ind.ctors p.2) types inds
  recsSpec : List.Forall₂ (fun n (r : RecursorVal) => ∀ r₀, env'.find? n = some (.recInfo r₀) →
      r = restoreRec env' lparams types res n r₀)
    (types.map (mkRecName ·.name) ++ (mkAuxRecNameMap env' types).1) recs
  clean : ∀ e ∈ restoredTerms inds recs,
    e.anySub (auxP (auxNameSet res types (mkAuxRecNameMap env' types).1)) = false
  typeAx : CheckedAdds allowPrimitive env (typeAxiomsN inds lparams isUnsafe) envT
  occ : TypeChecker.M.run envT (if isUnsafe then .unsafe else .safe) res.lctx lparams fuel
    (res.aux2nested.forM fun _ e => do _ ← TypeChecker.checkType e) = .ok ()
  lets : (restoredTerms inds recs).any (·.anySubterm (·.isLet)) → ∃ envC envR,
    CheckedAdds allowPrimitive envT (ctorAxiomsN inds lparams isUnsafe) envC ∧
    CheckedAdds allowPrimitive envC (recAxiomsN recs isUnsafe) envR ∧
    (∀ p ∈ inds, ∀ c ∈ p.2,
      checkRestored envT (if isUnsafe then .unsafe else .safe) lparams fuel c.type true = .ok ()) ∧
    (∀ r ∈ recs,
      checkRestored envC (if isUnsafe then .unsafe else .safe) r.levelParams fuel r.type true =
        .ok ()) ∧
    (∀ r ∈ recs, ∀ rule ∈ r.rules,
      checkRestored envR (if isUnsafe then .unsafe else .safe) r.levelParams fuel rule.rhs false =
        .ok ())
  final : CheckedAdds allowPrimitive env (finalConsts inds recs) envF

theorem Except.map_ok {ε α β} {f : α → β} {x : Except ε α} {b : β} (h : f <$> x = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, by cases h; rfl⟩

theorem List.flatMap_singleton_eq_map {α β} (f : α → β) :
    ∀ l : List α, l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | _ :: l => by simp [List.flatMap_singleton_eq_map f l]

theorem Except.forIn_yield_ok' {ε α} {g : α → Except ε Unit} {l : List α} {r : PUnit}
    (h : forIn l PUnit.unit (fun x _ => do g x; pure (ForInStep.yield PUnit.unit)) = .ok r) :
    ∀ x ∈ l, g x = .ok () := by
  intro x hx
  obtain ⟨s, hs⟩ := Except.forIn_yield_ok (fun x u s h => by
    obtain ⟨_, -, h⟩ := Except.ok_of_bind h; cases h; rfl) h x hx
  obtain ⟨⟨⟩, h1, -⟩ := Except.ok_of_bind hs; exact h1

theorem nestedFinal.WF (h : nestedFinal env env' lparams types res isUnsafe allowPrimitive fuel = .ok envF) :
    ∃ inds recs envT,
      NestedFinalOK env env' lparams types res isUnsafe allowPrimitive fuel inds recs envT envF := by
  unfold nestedFinal at h
  generalize hm : mkAuxRecNameMap env' types = m at h
  obtain ⟨recNames', recNameMap'⟩ := m
  dsimp only at h
  obtain ⟨inds, hinds, h⟩ := Except.ok_of_bind h
  obtain ⟨recs, hrecs, h⟩ := Except.ok_of_bind h
  obtain ⟨u1, hscan, h⟩ := Except.ok_of_bind h
  obtain ⟨envT, henvT, h⟩ := Except.ok_of_bind h
  obtain ⟨u2, hocc, h⟩ := Except.ok_of_bind h
  have hm2 : (mkAuxRecNameMap env' types).2 = recNameMap' := by rw [hm]
  have hm1 : (mkAuxRecNameMap env' types).1 = recNames' := by rw [hm]
  have indsSpec : List.Forall₂ (fun (t : InductiveType) (p : InductiveVal × List ConstructorVal) =>
      ∀ ind, env'.find? t.name = some (.inductInfo ind) →
        p.1 = { ind with all := types.map (·.name) } ∧
        List.Forall₂ (fun n (c : ConstructorVal) => ∀ c₀, env'.find? n = some (.ctorInfo c₀) →
          c = { c₀ with type := res.restoreNested env' lparams c₀.type (mkAuxRecNameMap env' types).2 })
          ind.ctors p.2) types inds := by
    refine Lean4Lean.List.Forall₂.imp (fun t p hb ind hf => ?_) (Except.mapM_ok hinds)
    simp only [hf] at hb
    obtain ⟨ctors, hc, hb⟩ := Except.ok_of_bind hb
    cases hb
    refine ⟨rfl, Lean4Lean.List.Forall₂.imp (fun n c hc c₀ hf' => ?_) (Except.mapM_ok hc)⟩
    simp only [hf'] at hc
    cases hc; rw [hm2]
  have recsSpec : List.Forall₂ (fun n (r : RecursorVal) => ∀ r₀, env'.find? n = some (.recInfo r₀) →
        r = restoreRec env' lparams types res n r₀)
      (types.map (mkRecName ·.name) ++ (mkAuxRecNameMap env' types).1) recs := by
    rw [hm1]
    refine Lean4Lean.List.Forall₂.imp (fun n r hb r₀ hf => ?_) (Except.mapM_ok hrecs)
    simp only [hf] at hb
    cases hb; simp only [restoreRec, hm2]
  clear hinds hrecs
  have hlen : inds.length = types.length := (Lean4Lean.List.Forall₂.length_eq indsSpec).symm
  have hclean : ∀ e ∈ restoredTerms inds recs,
      e.anySub (auxP (auxNameSet res types (mkAuxRecNameMap env' types).1)) = false := by
    intro e he
    obtain ⟨st, hs⟩ := Except.forIn_yield_ok (fun x u s h => by
      split at h
      · obtain ⟨_, h1, -⟩ := Except.ok_of_bind h; cases h1
      · cases h; rfl) hscan e he
    split at hs
    · obtain ⟨_, h1, -⟩ := Except.ok_of_bind hs; cases h1
    · rename_i hc
      rw [hm1, ← anySubterm_auxP]
      refine (congrArg (Expr.anySubterm · e) ?_).trans (by simpa using hc)
      funext x; cases x <;> rfl
  have htypeAx : CheckedAdds allowPrimitive env (typeAxiomsN inds lparams isUnsafe) envT := by
    have := CheckedAdds.foldlM (ap := allowPrimitive)
      (g := fun (x : InductiveVal × List ConstructorVal) => [ConstantInfo.axiomInfo
        { name := x.1.name, levelParams := lparams, type := x.1.type, isUnsafe }])
      (fun _ _ _ h => CheckedAdds.single h) henvT
    rwa [List.flatMap_singleton_eq_map] at this
  -- the final insertion, after the checks of restored terms with a `let`, if any
  have hfinal {envF'} (h : ((fun x => x.snd) <$> (do
      let _ ← forIn inds (Std.toStream recs) fun x __s => (match Std.Stream.next? __s with
        | none => pure (ForInStep.done __s)
        | some (r, s') => do
          let e ← get
          liftM (e.checkName x.1.name allowPrimitive)
          modify fun y => Lean.Kernel.Environment.add y (.inductInfo x.1)
          forIn x.2 PUnit.unit fun ctor _ => do
            let e ← get
            liftM (e.checkName ctor.name allowPrimitive)
            modify fun y => Lean.Kernel.Environment.add y (.ctorInfo ctor)
            pure (ForInStep.yield PUnit.unit)
          let e ← get
          liftM (e.checkName r.name allowPrimitive)
          modify fun y => Lean.Kernel.Environment.add y (.recInfo r)
          pure (ForInStep.yield s') : StateT Environment (Except Exception) _)
      forIn (recs.drop types.length) PUnit.unit fun r _ => do
        let e ← get
        liftM (e.checkName r.name allowPrimitive)
        modify fun y => Lean.Kernel.Environment.add y (.recInfo r)
        pure (ForInStep.yield PUnit.unit)
      pure () : StateT Environment (Except Exception) Unit).run env) = .ok envF') :
      CheckedAdds allowPrimitive env (finalConsts inds recs) envF' := by
    obtain ⟨⟨_, e₀⟩, hrun, rfl⟩ := Except.map_ok h
    rw [StateT.run_bind] at hrun
    obtain ⟨⟨_, e₁⟩, h1, hrun⟩ := Except.ok_of_bind hrun
    rw [StateT.run_bind] at hrun
    obtain ⟨⟨_, e₂⟩, h2, hrun⟩ := Except.ok_of_bind hrun
    cases hrun
    unfold finalConsts; rw [hlen]
    exact (CheckedAdds.ofForInZip h1).append (CheckedAdds.ofForIn (g := ConstantInfo.recInfo) h2)
  split at h
  · rename_i hany
    obtain ⟨_, hc1, h⟩ := Except.ok_of_bind h
    obtain ⟨envC, hC, h⟩ := Except.ok_of_bind h
    obtain ⟨_, hc2, h⟩ := Except.ok_of_bind h
    obtain ⟨envR, hR, h⟩ := Except.ok_of_bind h
    obtain ⟨_, hc3, h⟩ := Except.ok_of_bind h
    refine ⟨inds, recs, envT, indsSpec, recsSpec, hclean, htypeAx, hocc, fun _ => ⟨envC, envR, ?_,
      ?_, ?_, ?_, ?_⟩, hfinal h⟩
    · have := CheckedAdds.foldlM (ap := allowPrimitive)
        (g := fun (x : InductiveVal × List ConstructorVal) => x.2.flatMap fun c =>
          [ConstantInfo.axiomInfo { name := c.name, levelParams := lparams, type := c.type, isUnsafe }])
        (fun _ _ _ h => CheckedAdds.foldlM (g := fun (c : ConstructorVal) =>
          [ConstantInfo.axiomInfo { name := c.name, levelParams := lparams, type := c.type, isUnsafe }])
          (fun _ _ _ h => CheckedAdds.single h) h) hC
      simp only [List.flatMap_singleton_eq_map] at this; exact this
    · have := CheckedAdds.foldlM (ap := allowPrimitive)
        (g := fun (r : RecursorVal) => [ConstantInfo.axiomInfo
          { name := r.name, levelParams := r.levelParams, type := r.type, isUnsafe }])
        (fun _ _ _ h => CheckedAdds.single h) hR
      rwa [List.flatMap_singleton_eq_map] at this
    · intro p hp c hc
      exact Except.forIn_yield_ok' (Except.forIn_yield_ok' hc1 p hp) c hc
    · exact Except.forIn_yield_ok' hc2
    · intro r hr rule hrule
      exact Except.forIn_yield_ok' (Except.forIn_yield_ok' hc3 r hr) rule hrule
  · rename_i hany
    refine ⟨inds, recs, envT, indsSpec, recsSpec, hclean, htypeAx, hocc, fun h' => ?_, hfinal h⟩
    exact absurd h' hany

/-- The final phase adds what `AddInduct` describes, in another order. -/
theorem finalConsts_perm : ∀ {inds : List (InductiveVal × List ConstructorVal)}
    {recs : List RecursorVal}, inds.length ≤ recs.length →
    (finalConsts inds recs).Perm (inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs)
  | [], recs, _ => by simp [finalConsts, finalZip, inductConsts]
  | p :: inds, [], h => by simp at h
  | p :: inds, r :: recs, h => by
    have ih := finalConsts_perm (inds := inds) (recs := recs) (by simpa using h)
    simp only [finalConsts, finalZip, inductConsts, List.length_cons, List.drop_succ_cons,
      List.zipWith_cons_cons, List.flatten_cons, List.map_cons, List.flatMap_cons,
      List.map_append] at ih ⊢
    classical
    rw [List.perm_iff_count] at ih ⊢
    intro a; have := ih a
    simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append] at this ⊢
    omega

/-! ### The auxiliary recursors' names -/

/-- `NameMap Name` as the tree map it is. -/
abbrev NM := Std.TreeMap Name Name Name.quickCmp

/-- A step of `mkAuxRecNameMap`'s loop. -/
def auxRecStep (main : Name) (s : Array Name × NM × Nat) (n : Name) : Array Name × NM × Nat :=
  (s.1.push (mkRecName n), s.2.1.insert (mkRecName n) ((mkRecName main).appendIndexAfter s.2.2),
    s.2.2 + 1)

theorem nm_getD_insert {m : NM} {k a d v : Name} :
    (m.insert k v).getD a d = if k = a then v else m.getD a d := by
  rw [Std.TreeMap.getD_insert]
  by_cases h : k = a
  · subst h; simp
  · rw [if_neg, if_neg h]; rw [Std.LawfulBEqCmp.compare_eq_iff_beq]; simpa using h

theorem auxRecFold_fst (main : Name) : ∀ (L : List Name) (arr : Array Name) (m : NM)
    (i : Nat), (L.foldl (auxRecStep main) (arr, m, i)).1.toList = arr.toList ++ L.map mkRecName
  | [], _, _, _ => by simp
  | n :: L, arr, m, i => by
    show (L.foldl (auxRecStep main) (arr.push (mkRecName n), _, _)).1.toList = _
    rw [auxRecFold_fst main L]; simp

theorem auxRecFold_getD_not (main : Name) {n d : Name} : ∀ (L : List Name) (arr : Array Name)
    (m : NM) (i : Nat), n ∉ L.map mkRecName →
    (L.foldl (auxRecStep main) (arr, m, i)).2.1.getD n d = m.getD n d
  | [], _, _, _, _ => rfl
  | k :: L, arr, m, i, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show (L.foldl (auxRecStep main) (_, m.insert (mkRecName k) _, _)).2.1.getD n d = _
    rw [auxRecFold_getD_not main L _ _ _ h.2, nm_getD_insert, if_neg (Ne.symm h.1)]

theorem auxRecFold_getD (main : Name) {d : Name} : ∀ (L : List Name) (arr : Array Name)
    (m : NM) (i : Nat), (L.map mkRecName).Nodup → ∀ j n, (L.map mkRecName)[j]? = some n →
    (L.foldl (auxRecStep main) (arr, m, i)).2.1.getD n d = (mkRecName main).appendIndexAfter (i + j)
  | [], _, _, _, _, _, _, h => by cases h
  | k :: L, arr, m, i, hnd, j, n, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show (L.foldl (auxRecStep main) (_, m.insert (mkRecName k) _, i + 1)).2.1.getD n d = _
    cases j with
    | zero =>
      cases h
      rw [auxRecFold_getD_not main L _ _ _ hnd.1, nm_getD_insert, if_pos rfl]; rfl
    | succ j =>
      rw [auxRecFold_getD main L _ _ _ hnd.2 j n (by simpa using h)]
      congr 1; omega

/-- The auxiliary recursors `mkAuxRecNameMap` renames, and their new names: the `i`th is the
first type's recursor's name with `i + 1` appended. Every other name keeps its own. -/
theorem mkAuxRecNameMap_spec {env' : Environment} {T : InductiveType} {Ts : List InductiveType}
    {info : InductiveVal} (hf : env'.find? T.name = some (.inductInfo info))
    (hlen : (T :: Ts).length < info.all.length) :
    (mkAuxRecNameMap env' (T :: Ts)).1 = (info.all.drop (T :: Ts).length).map mkRecName ∧
    (((info.all.drop (T :: Ts).length).map mkRecName).Nodup → ∀ i n d,
      ((info.all.drop (T :: Ts).length).map mkRecName)[i]? = some n →
      (mkAuxRecNameMap env' (T :: Ts)).2.getD n d = (mkRecName T.name).appendIndexAfter (i + 1)) ∧
    (∀ n d, n ∉ (mkAuxRecNameMap env' (T :: Ts)).1 → (mkAuxRecNameMap env' (T :: Ts)).2.getD n d = d) := by
  have e : mkAuxRecNameMap env' (T :: Ts) =
      let s := (info.all.drop (T :: Ts).length).foldl (auxRecStep T.name) (#[], (∅ : NM), 1)
      (s.1.toList, s.2.1) := by
    unfold mkAuxRecNameMap
    simp only [hf, Id.run]
    rw [if_pos hlen]
    simp only [List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
    rfl
  rw [e]; dsimp only
  refine ⟨by rw [auxRecFold_fst]; simp, fun hnd i n d h => ?_, fun n d h => ?_⟩
  · rw [auxRecFold_getD _ _ _ _ _ hnd i n h, Nat.add_comm]
  · rw [auxRecFold_fst] at h
    rw [auxRecFold_getD_not _ _ _ _ _ (by simpa using h)]
    rfl

/-! ### The aux-free check, read as facts about constants -/

/-- The names of the auxiliary types, their constructors and the auxiliary recursors before
renaming. -/
def IsAuxName (res : ElimNestedInductive.Result) (types : List InductiveType)
    (recNames' : List Name) (c : Name) : Prop :=
  c ∈ recNames' ∨ ∃ t ∈ res.types.drop types.length, c = t.name ∨ c ∈ t.ctors.map (·.name)

/-- `NameSet` as the tree set it is. -/
abbrev NS := Std.TreeSet Name Name.quickCmp

theorem ns_contains_insert_of {s : NS} {k c : Name} (h : s.contains c) : (s.insert k).contains c := by
  rw [Std.TreeSet.contains_insert, h]; simp

theorem ns_contains_insert_self {s : NS} {k : Name} : (s.insert k).contains k := by
  rw [Std.TreeSet.contains_insert]; simp

theorem ns_foldl_ctors_contains_of {c : Name} :
    ∀ (cs : List Constructor) {s : NS}, s.contains c → (cs.foldl (·.insert ·.name) s).contains c
  | [], _, h => h
  | _ :: cs, _, h => ns_foldl_ctors_contains_of cs (ns_contains_insert_of h)

theorem ns_foldl_ctors_contains_mem {c : Name} :
    ∀ (cs : List Constructor) {s : NS}, c ∈ cs.map (·.name) → (cs.foldl (·.insert ·.name) s).contains c
  | [], _, h => by cases h
  | x :: cs, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ns_foldl_ctors_contains_of cs ns_contains_insert_self
    · exact ns_foldl_ctors_contains_mem cs h

theorem ns_foldl_types_contains_of {c : Name} : ∀ (ts : List InductiveType) {s : NS},
    s.contains c → (ts.foldl (fun s t => t.ctors.foldl (·.insert ·.name) (s.insert t.name)) s).contains c
  | [], _, h => h
  | t :: ts, _, h => ns_foldl_types_contains_of ts
    (ns_foldl_ctors_contains_of t.ctors (ns_contains_insert_of h))

theorem ns_foldl_types_contains_mem {c : Name} : ∀ (ts : List InductiveType) {s : NS},
    (∃ t ∈ ts, c = t.name ∨ c ∈ t.ctors.map (·.name)) →
    (ts.foldl (fun s t => t.ctors.foldl (·.insert ·.name) (s.insert t.name)) s).contains c
  | [], _, ⟨_, h, _⟩ => by cases h
  | t :: ts, _, ⟨t', ht', h⟩ => by
    rcases List.mem_cons.1 ht' with rfl | ht'
    · refine ns_foldl_types_contains_of ts ?_
      rcases h with rfl | h
      · exact ns_foldl_ctors_contains_of _ ns_contains_insert_self
      · exact ns_foldl_ctors_contains_mem _ h
    · exact ns_foldl_types_contains_mem ts ⟨t', ht', h⟩

/-- Every auxiliary name is in the set the final phase checks for. -/
theorem auxNameSet_contains {res : ElimNestedInductive.Result} {types : List InductiveType}
    {recNames' : List Name} {c : Name} (h : IsAuxName res types recNames' c) :
    (auxNameSet res types recNames').contains c := by
  show (((res.types.drop types.length).foldl
    (fun s t => t.ctors.foldl (·.insert ·.name) (s.insert t.name)) (Std.TreeSet.ofList recNames' _) :
      NS)).contains c
  rcases h with h | h
  · refine ns_foldl_types_contains_of _ ?_
    rw [Std.TreeSet.contains_ofList]; simpa using h
  · exact ns_foldl_types_contains_mem _ h

/-- A term the check finds no auxiliary name in mentions none, as a constant or as a projection's
structure. -/
theorem anySub_auxP_false {S : NameSet} {p : Name → Prop} (hp : ∀ c, p c → S.contains c)
    {e : Expr} (h : e.anySub (auxP S) = false) :
    e.ConstsOK (fun c _ => ¬ p c) ∧ e.ProjsOK (fun s => ¬ p s) := by
  induction e with
  | bvar | fvar | mvar | sort | lit => exact ⟨trivial, trivial⟩
  | const c _ => exact ⟨fun hc => by simp [Expr.anySub, auxP, hp c hc] at h, trivial⟩
  | app f a ih1 ih2 | lam _ f a _ ih1 ih2 | forallE _ f a _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    have h1 := ih1 h.1.2
    have h2 := ih2 h.2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | letE _ t v b _ ih1 ih2 ih3 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    have h1 := ih1 h.1.1.2
    have h2 := ih2 h.1.2
    have h3 := ih3 h.2
    exact ⟨⟨h1.1, h2.1, h3.1⟩, ⟨h1.2, h2.2, h3.2⟩⟩
  | mdata _ e ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    exact ih h.2
  | proj s _ e ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    have h1 := ih h.2
    exact ⟨h1.1, fun hs => by simp [auxP, hp s hs] at h, h1.2⟩

/-! ### Restored terms with and without a `let` -/

theorem anySubterm_isLet (e : Expr) : e.anySubterm (·.isLet) = e.anySub (·.isLet) :=
  anySubterm_eq (fun a b h => by
    cases a <;> cases b <;>
      simp only [(· == ·), Expr.eqv_eq, Expr.eqv', reduceCtorEq] at h <;> rfl) e

/-- A term without a `let`, found so by the final phase's check, and without metavariables, is
`let`-free. -/
theorem Expr.letFree_of_anySub {e : Expr} (h : e.anySub (·.isLet) = false)
    (hm : e.hasExprMVar' = false) : e.LetFree := by
  induction e with
  | bvar | fvar | sort | lit | const => trivial
  | mvar => simp [Expr.hasExprMVar'] at hm
  | app f a ih1 ih2 | lam _ f a _ ih1 ih2 | forallE _ f a _ ih1 ih2 =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    simp only [Expr.hasExprMVar', Bool.or_eq_false_iff] at hm
    exact ⟨ih1 h.1.2 hm.1, ih2 h.2 hm.2⟩
  | letE => simp [Expr.anySub, Expr.isLet] at h
  | mdata _ e ih | proj _ _ e ih =>
    simp only [Expr.anySub, Bool.or_eq_false_iff] at h
    simp only [Expr.hasExprMVar'] at hm
    exact ih h.2 hm

/-- The check the final phase makes of a restored term with a `let`, run in an environment with a
model, translates and types it. -/
theorem checkRestored.WF {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) {levelParams : List Name} {fuel : FuelConfig} {e : Expr}
    {isType : Bool} (hclosed : e.FVarsIn fun _ => False) (hlet : e.anySubterm (·.isLet))
    (h : checkRestored env safety levelParams fuel e isType = .ok ()) :
    ∃ e' T, TrExprS venv levelParams [] e e' ∧ venv.HasType levelParams.length [] e' T ∧
      (isType → venv.IsType levelParams.length [] e') := by
  rw [checkRestored, if_pos hlet] at h
  refine TypeChecker.M.WF.run1 (lparams := levelParams) (fuel := fuel) wf
    (Q := fun _ => ∃ e' T, TrExprS venv levelParams [] e e' ∧
      venv.HasType levelParams.length [] e' T ∧ (isType → venv.IsType levelParams.length [] e'))
    ?_ _ h
  have hclosed' : e.FVarsIn (· ∈ (TypeChecker.VContext.mk1 wf levelParams fuel).vlctx.fvars) := by
    simpa [TypeChecker.VContext.mk1] using hclosed
  refine (TypeChecker.checkType.WF hclosed').bind fun _ _ _ ⟨e', ty', _, htype, hsort, hhasType⟩ => ?_
  split
  · refine (TypeChecker.ensureSort.WF hsort).bind fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => .pure ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with | sort hu
    refine ⟨e', _, htype, hhasType, fun _ => ?_⟩
    exact ⟨_, hhasType.defeqU_r wf.tr.wf (by trivial) hdefeq.symm⟩
  · rename_i hT
    exact .pure ⟨e', _, htype, hhasType, fun h => absurd h hT⟩

/-- What the final phase adds, in the terms `AddInduct` states it: the types, constructors and
recursors, inserted in some order under distinct names fresh for the environment. -/
theorem NestedFinalOK.addConsts {env env' envT envF : Environment} {lparams : List Name}
    {types : List InductiveType} {res : ElimNestedInductive.Result} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {inds : List (InductiveVal × List ConstructorVal)} {recs : List RecursorVal}
    (H : NestedFinalOK env env' lparams types res isUnsafe allowPrimitive fuel inds recs envT envF)
    (hwf : env.constants.WF) :
    let cs := inductConsts (inds.map (·.1)) (inds.flatMap (·.2)) recs
    ∃ cis, cis.Perm cs ∧ envF.constants = insertConsts env.constants cis ∧
      (cs.map (·.name)).Nodup ∧ (∀ ci ∈ cs, env.constants.find? ci.name = none) ∧
      (∀ ci ∈ cs, Environment.primitives.contains ci.name → allowPrimitive) ∧
      envF.quotInit = env.quotInit := by
  intro cs
  have hle : inds.length ≤ recs.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq H.indsSpec, ← Lean4Lean.List.Forall₂.length_eq H.recsSpec]
    simp
  have hp := finalConsts_perm hle
  obtain ⟨e1, e2, e3, e4, e5⟩ := H.final.spec hwf
  refine ⟨_, hp, e1, (hp.map _).nodup_iff.1 e3, fun ci hci => ?_, fun ci hci => e5 ci (hp.mem_iff.2 hci),
    e2⟩
  have := e4 ci (hp.mem_iff.2 hci)
  rwa [Kernel.Environment.find?, hwf.find?'_eq_find?] at this

/-- The occurrence check, as a loop over a list, which `checkType.forM_lit` reads. -/
theorem occCheck_eq (m : Std.TreeMap Name Expr Name.quickCmp) :
    (m.forM fun _ e => do _ ← TypeChecker.checkType e : TypeChecker.M Unit) =
      (m.toList.forM fun p => do _ ← TypeChecker.checkType p.2) := by
  rw [Std.TreeMap.forM_eq_forM, Std.TreeMap.forM_eq_forM_toList]
  rfl

/-- The occurrence check of a successful final phase, over the list of recorded occurrences. -/
theorem NestedFinalOK.occList {env env' envT envF : Environment} {lparams : List Name}
    {types : List InductiveType} {res : ElimNestedInductive.Result} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {inds : List (InductiveVal × List ConstructorVal)} {recs : List RecursorVal}
    (H : NestedFinalOK env env' lparams types res isUnsafe allowPrimitive fuel inds recs envT envF) :
    TypeChecker.M.run envT (if isUnsafe then .unsafe else .safe) res.lctx lparams fuel
      ((Std.TreeMap.toList (res.aux2nested : Std.TreeMap Name Expr Name.quickCmp)).forM fun p => do
        _ ← TypeChecker.checkType p.2) = .ok () := by
  exact (congrArg (TypeChecker.M.run envT _ res.lctx lparams fuel)
    (occCheck_eq res.aux2nested)).symm.trans H.occ

/-- An environment checked axioms were added to has a model, given their translations, as the flat
run's axiom environments do (`VEnvAt.addAxiomList`). -/
theorem CheckedAdds.venvAt {env env₂ : Environment} {safety : DefinitionSafety} {venv venv₂ : VEnv}
    {ap : Bool} {axs : List AxiomVal} {cs : List (Name × VConstant)}
    (wf : VEnvAt env safety venv) (H : CheckedAdds ap env (axs.map .axiomInfo) env₂)
    (htr : List.Forall₂ (fun (ax : AxiomVal) (p : Name × VConstant) => ax.name = p.1 ∧
      TrConstant safety venv (.axiomInfo ax) p.2 ∧ p.2.WF venv) axs cs)
    (hnp : ∀ ax ∈ axs, Environment.primitives.contains ax.name = false)
    (e : venv.addConstList cs = some venv₂) : VEnvAt env₂ safety venv₂ := by
  obtain ⟨-, -, hnd, hfr, -⟩ := H.spec wf.tr.map_wf
  rw [H.eq, List.foldl_map]
  refine VEnvAt.addAxiomList axs cs wf htr (by rw [List.map_map] at hnd; exact hnd)
    (fun ax hax => hfr _ (List.mem_map_of_mem hax)) hnp e

end Lean4Lean

# Lean-for-Lean: experimental fork

> **LLM-maintained and unaudited.** This fork's changes and documentation are
> maintained with LLM agents and have not received an independent human audit.
> Successful builds and machine-checked proofs do not establish that the
> specification, assumptions, or implementation are correct. The main verification
> theorem is conditional on two open metatheoretic assumptions, described below.

This is a research fork of [digama0/lean4lean](https://github.com/digama0/lean4lean),
an implementation of the Lean 4 kernel in mostly pure Lean 4, with a formal
specification and proofs connecting the implementation to it. The implementation
derives from Lean's C++ kernel and can share its bugs. This fork extends the
inductive-type specification and verification, changes some kernel checks, and
develops the remaining metatheory. It is not an independently audited replacement
for Lean's kernel or an upstream release.

- [Verification status and trust assumptions](#verification-status-and-trust-assumptions)
- [Build and test](#build-and-test)
- [Run the checker](#run-the-checker)
- [What this fork changes](#what-this-fork-changes)
- [Findings and regression tests](#findings-and-regression-tests)
- [Design and proof guide](#design-and-proof-guide)
- [Open metatheory](#open-metatheory)
- [Source map and contributing](#source-map-and-contributing)

## Verification status and trust assumptions

| Area | Status |
| --- | --- |
| Declaration checking, including flat and nested inductives and quotient initialization | `Lean4Lean.addDecl.WF` is proved **assuming `VEnv.Injective`**, as are the supporting results that need injectivity. |
| Primitive projections, structure eta, recursor and quotient reduction | Specified and connected to the implementation; the verification uses the same injectivity hypothesis where needed. |
| Shape model | Sound for well-formed environments. Proves that a sort cannot equal a pi type, and that equal sorts have equivalent universe levels, without the injectivity hypothesis. |
| Injectivity of pi types and inductive type formers | **Open.** These are the two fields of [`VEnv.Injective`](Lean4Lean/Theory/Typing/Injectivity.lean), not proved instances. |
| Logical relation intended to establish injectivity | Incomplete at a recursor's full application (`IndRecSat`), especially K-like reduction and indexed iota reduction. |
| Church–Rosser and experimental developments | Unfinished. `NormalEq.parRed` has two `sorry` cases; `Experimental` contains further incomplete proofs. |

There are no `sorry` proofs in the active `Verify` development. In particular,
`#print axioms Lean4Lean.addDecl.WF` has no `sorryAx`. This does **not** discharge
`VEnv.Injective`: it is an explicit argument to the theorem. The theorem states
preservation of the formal environment invariant when declaration checking
succeeds; it does not by itself prove consistency of the type theory.

To inspect that boundary in Lean:

```lean
import Lean4Lean.Verify
#check @Lean4Lean.addDecl.WF
#print axioms Lean4Lean.addDecl.WF
```

The verification also trusts the runtime-model axioms in
[`Verify/Axioms.lean`](Lean4Lean/Verify/Axioms.lean), Lean's proof checker, and the
compiler/runtime correspondence for native and opaque operations. The fork
corrects some inherited axiom statements and removes others. Runtime comparison
tests exercise the remaining models, but cannot prove those axioms. A review
must examine the specification and the statements of the hypotheses as well as
the proof terms.

## Build and test

Install [elan](https://github.com/leanprover/elan), then run these commands from
the repository root. The toolchain is pinned in [lean-toolchain](lean-toolchain)
(currently Lean `v4.33.0-rc2`), and dependencies in
[lake-manifest.json](lake-manifest.json).

```nu
lake build
lake build Lean4Lean.Tests Lean4Lean.Experimental
```

The default build includes the library, executable, theory and verification.
Tests and experimental modules are explicit additional targets. Expected `sorry`
warnings in unfinished theory and experiments are not evidence that verification
assumptions have been resolved.

| Target | Contents |
| --- | --- |
| `lake build Lean4Lean` | Kernel library, without the verification proofs |
| `lake build lean4lean` | Command-line checker |
| `lake build Lean4Lean.Theory` | Abstract type theory and metatheory |
| `lake build Lean4Lean.Verify` | Implementation verification |
| `lake build Lean4Lean.Tests` | Regression suite, including compile-time runtime-model checks |
| `lake build Lean4Lean.Experimental` | Unfinished formalization experiments |

The CI smoke tests exercise both replay modes:

```nu
lake exe lean4lean Init.Core
lake exe lean4lean --fresh Init.System.IO
```

## Run the checker

```nu
lake exe lean4lean Init.Core
lake exe lean4lean --fresh Init.System.IO
```

Without a module argument, the checker infers the current package's main module
from its Lake manifest. Otherwise, each module argument is a **prefix**: it checks
all matching built modules. Ordinary replay checks each module against its
imported environment and runs modules concurrently. Broad prefixes can use a
large amount of memory; start with a single small module.

`--fresh` requires the prefix to match exactly one module. It rechecks that module
and its imports into a fresh environment; it does not rebuild the source files.

To check another package, build that package with the same toolchain, change to
its directory, and run this fork's executable in that package's Lake environment:

```nu
lake env /path/to/lean4lean/.lake/build/bin/lean4lean MyPackage.Module
```

| Option | Effect |
| --- | --- |
| `--fresh` | Recheck one module and all its imports from scratch |
| `-v`, `--verbose` | Print declarations as they are checked |
| `--compare` | Compare slow checks with Lean's C++ kernel |
| `--config=path.json` | Read fuel limits from a JSON file |
| `--config:field=value` | Override one fuel limit with a JSON value |

The configuration fields and defaults are in
[`FuelConfig.lean`](Lean4Lean/FuelConfig.lean). File and field options are applied
in command-line order. Imported declarations are trusted in ordinary replay;
use `--fresh` when that distinction matters.

## What this fork changes

- **Inductive declarations and their verification.** `VInductDecl.WF` specifies
  mutual blocks, positivity, universes, large elimination, constructors, recursors
  and iota rules. Flat and nested `addInductive` paths are connected to
  `VEnv.addInduct`, including `Bool` and `Nat`. Generated recursors and rules are
  proved well typed under the stated metatheoretic assumptions.
- **Primitive projections.** `VExpr.proj` models projections directly, with
  typing, iota and structure-eta rules. Translation is syntactic and unique.
  Projection permissions are tested at the instantiated sort, including
  structures that may inhabit `Prop`.
- **Context-sensitive checking.** Support and simulation theorems describe which
  variables, universe parameters and constants a checker run can read. Caches
  and the equivalence manager track the scopes their facts depend on. Verification
  no longer assumes that typing or definitional equality can always be
  strengthened by dropping unused variables.
- **Kernel checks and runtime models.** Annotation definitions are checked before
  stripping them; nested restoration, projection and reduction checks expose
  conditions the proofs need. Simultaneous instantiation and abstraction are
  modelled correctly, and the inconsistent `mkLevelIMaxCore_eq` axiom is removed.
- **Metatheory.** A shape model proves sort separation and sort injectivity. A
  logical relation develops the remaining injectivity argument and makes its
  unresolved recursor case explicit.

These changes include deliberate acceptance differences from Lean's C++ kernel.
See [divergences.md](divergences.md) for the behavior and reproducing tests, and
[bugs-found.md](bugs-found.md) for upstream's existing bug catalogue. Neither
matching replay results nor a passing regression suite establishes full
compatibility.

## Findings and regression tests

The examples below are specific to the pinned toolchain. Claims about missing
derivations and unfinished metatheory remain research claims, not established
unsoundness results for Lean.

| Example | What is exercised |
| --- | --- |
| [InductiveSpec](Lean4Lean/Tests/InductiveSpec.lean) | Generated recursors and iota/eta rules checked against Lean's kernel; primitive projections at instantiated universe levels |
| [NestedInductive](Lean4Lean/Tests/NestedInductive.lean) | Restoring nested blocks with nontrivial levels, metadata and `let` types |
| [Annotations](Lean4Lean/Tests/Annotations.lean) | A custom prelude whose non-identity annotation definitions let Lean generate ill-typed recursors; this fork checks the definitions |
| [BinderScope](Lean4Lean/Tests/BinderScope.lean) | Equivalences and cached checks learned under a binder being reused outside its scope |
| [FieldViews](Lean4Lean/Tests/FieldViews.lean) | Field domains with defaults and dead `let`s, including a structure accepted through a fact learned under a discarded field |
| [PrimitiveScope](Lean4Lean/Tests/PrimitiveScope.lean) | Primitive recognizers checking retained terms outside temporary binders, while still recognizing the prelude's primitives |
| [AxiomModels](Lean4Lean/Tests/AxiomModels.lean), [LevelStd](Lean4Lean/Tests/LevelStd.lean) | Runtime operations compared with their logical models, including open terms, repeated variables, metadata and universe levels |
| [QuotInit](Lean4Lean/Tests/QuotInit.lean) | Quotient declarations matching Lean's, including binder information |
| [DeclFVar](Lean4Lean/Tests/DeclFVar.lean), [ReservedName](Lean4Lean/Tests/ReservedName.lean), [UnsafeEq](Lean4Lean/Tests/UnsafeEq.lean) | Malformed declaration inputs, the reserved panic constant, and unsafe `Eq` during quotient initialization |

The old instantiation model substituted one term at a time. Lean substitutes
simultaneously: `(bvar 0).instantiate #[bvar 0, X]` is `bvar 0`, not `X`. The old
abstraction model similarly mishandled loose bound variables and repeated
variables. The replacement models state simultaneous semantics; the old forms
are derived for the closed, distinct-variable inputs where they apply. A third
axiom, `mkLevelIMaxCore_eq`, equated two definitions that disagree on `imax 1 u`;
it was unused and has been removed. Tests do not extend these models to inputs
where the runtime aborts with an internal panic.

## Design and proof guide

### Inductive blocks and nested restoration

The specification states a block's constructor and recursor facts with its types
declared but without its constructors. Index telescopes must already be types
**before** the block exists, since an index cannot depend on the block's types.
The implementation sometimes normalizes in a larger environment; simulation
repeats those runs in the environment the specification needs.

Nested auxiliary types stand for occurrences of earlier types at parameters
mentioning the new block. They have motives, minor premises, recursors and iota
rules, but introduce no auxiliary type constants in the final specification.
The kernel's temporary auxiliary constants are eliminated when it restores the
block. `AuxWF` relates their declarations to the earlier types up to equivalent
universe levels, accommodating the simplification performed by level
instantiation.

`restoreNested` replaces an auxiliary application at its own arguments and
levels. It preserves metadata and checks that restored terms contain no
auxiliary constants; restored terms with `let`s are checked explicitly. Nested
occurrences are checked against the block's types as axioms, before relying on
the finished environment. The final insertion order may interleave each type
with its constructors and recursor, so `AddInduct` allows that order.

The proof starts in [`Verify/Environment/Inductive.lean`](Lean4Lean/Verify/Environment/Inductive.lean).
[`Run.lean`](Lean4Lean/Verify/Environment/Run.lean) assembles the flat phases;
[`MkRecInfos.lean`](Lean4Lean/Verify/Environment/MkRecInfos.lean) and
[`Rules.lean`](Lean4Lean/Verify/Environment/Rules.lean) handle recursors;
[`NestedBranch.lean`](Lean4Lean/Verify/Environment/NestedBranch.lean) assembles the
nested path. Restoration in the theory is developed in
[`Nested.lean`](Lean4Lean/Theory/Typing/Nested.lean) through
[`NestedWF.lean`](Lean4Lean/Theory/Typing/NestedWF.lean).

### Projections and field domains

Primitive projections cannot always be represented by recursor applications:
the kernel can project from `Foo.{1}` even when `Foo`'s recursor eliminates only
into `Prop`. Recording blocks in `VEnv.inducts` lets each projection rule identify
the structure's declaration and constructor telescope directly.

`ProjAllowed` describes when a projection from a possibly propositional type is
permitted. `projEta` requires those permissions for the expansion's projections.
The model can be more permissive than the kernel about dependencies of fields
after the projected field; soundness only needs the fields reached by the
projection. The `Ex` example in `InductiveSpec` exercises this distinction.

`checkConstructors` checks each field's declared domain, its form with `let`s
unfolded, and its view with annotations stripped. `FieldsKeptWF` and `CtorDoms`
provide the domain typings needed when a projection skips earlier fields.
These are established by simulation in the smaller contexts, and survive
nested restoration. The proof of [`inferProj.WF`](Lean4Lean/Verify/TypeChecker/Proj.lean)
therefore does not assume strengthening.

The checker compares structure names, checks projection indices and universe
counts, and reduces only complete constructor applications. Quotient reduction
also checks the constructor's type and relation against the eliminator. These
checks avoid relying on additional unproved separation properties of type
formers. [divergences.md](divergences.md) records the observable differences.

### Scope tracking and simulation

A fact learned under `p : P a` can depend on `p` without mentioning it. Proof
irrelevance can equate `hI` with `I.mk a p`, enabling an iota reduction that has
no known derivation after `p` leaves scope. Merely examining a cached term's
free variables does not justify keeping that fact.

Each cache entry and union-find link carries the deepest scope of the facts its
derivation consulted. Entries depending on a closed scope cease to be current;
other entries remain available. Keys need no extra label for their own free
variables because variable identifiers are fresh and a key mentioning a closed
variable cannot be queried again. `withFreshId` rejects an already declared
identifier.

[`Verify/Support`](Lean4Lean/Verify/Support) proves support and simulation
separately from typing, so these properties do not themselves require
`VEnv.Injective`. The cache proofs rerun computations in the context where their
results are used, with facts above the allowed scope set aside by a ceiling.
[`ScopedEquivManager.lean`](Lean4Lean/ScopedEquivManager.lean) and its
[verification](Lean4Lean/Verify/ScopedEquivManager.lean) handle labelled equivalences.

Scope tracking has a measurable cost. Local development measurements of Lean
core replay recorded 1155.5 billion user-mode instructions versus 990.4 billion
before scope tracking, about 16.7% more. These are historical measurements,
not a portable benchmark or a CI performance guarantee. Cache bookkeeping,
larger state and the pair map account for much of the remaining overhead.

Primitive recognizers likewise check retained closed terms outside the binders
where they discovered them. The kernel checks annotation definitions as
identities before stripping them and uses the total, cached `Expr.anySubterm`
instead of relying on an axiom for native subterm search.

## Open metatheory

The shape model is sound and distinguishes sorts and pi types, but does not
establish injectivity of pi domains/codomains or inductive parameters/indices.
The logical relation's remaining `IndRecSat` case must relate a recursor's
reduct at the type of its full application. K-like and indexed iota reduction
require a judgmental equality between the spine's indices and the constructor's
indices. Turning that equality into a relation at the motive's argument shape
is precisely the unresolved conversion problem.

No counterexample to either injectivity assumption has been established here.
Attempts to prove them by the current relation, or by induction on derivations,
stop at this same step. The detailed notes below record arguments and obstacles;
they are not additional formal results.

General strengthening is also not assumed. The binder-scope examples motivate
why it is suspect, but an argument that a particular equality has no derivation
is not a formal nonderivability proof. The implementation verification uses
support, simulation and explicit domain checks instead.

<details>
<summary>Research notes: the conversion gap and attempted injectivity arguments</summary>

The logical relation (`LogRel/Rel.lean`, `RelS.lean`) has every adequacy case but a recursor's
full application (`IndRecSat`), in its K-like case and its iota case at a type with indices.
Every use of the conjectures on `addDecl.WF`'s path goes through unique typing or untyped defeq
composition (`isDefEqArgs` compares arguments without their types), so nothing weaker than full
injectivity serves; it has to come from the relation.

- The gap. `T.rec mot m is h` steps when the indices `is` equal the constructor's `idx`
  judgmentally (`KFields.index`; in the iota case `CtorParams`' `SubstRel`). The reduct is
  typed at `mot idx …`, the spine at `mot is …`; converting between them goes through the
  motive's `PiDefEq`, which needs `is` and `idx` related at a shape at or above the valuation's
  `ρ_is`. Judgmental equality alone does not give that: the relation is not known to be closed
  under conversion, and closure would itself give `forallE_inv`.
- Normalization is not the obstacle: relevant terms need a weak head normal form only at
  non-`bot` shapes, and a recursor on a proof major steps by the K-like rule without reducing
  it, `Acc`'s included.
- Tightness (in progress): a related pair's value shape lies below both terms' interpretations
  at the all-`bot` valuation in the model with no given shapes (`Tight`, `AxBelow`). It keeps
  stuck values at shapes their interpretations reach.
- Every source of closure tried so far fails on depth. The relation is defined by recursion on
  depth, and adequacy needs it to agree across depths: `LR.DefEq.lift`/`TyDefEq.lift` are used
  in both directions, and the application case relates `F X` at the function's depth and lowers
  the result to the goal's.
  - Depth-bounded adequacy (adequacy of the whole environment below a constant case's depth)
    fails because the application case climbs depth: `f : (Nat → Nat) → Nat` needs depth 2 for a
    result at depth 0, and `InterpTyped.out` moves premises to the model's witness depth.
  - Saturation (pi clauses and related substitutions quantify only over arguments related at
    every typed shape below their interpretation) gives adequacy from saturated substitutions
    (`LE_Interp.subst` is an equivalence, valuations join), the identity substitution is
    saturated (variables at `bot`), and a firing condition stated with it makes both
    substitutions fire together. But "every shape below the interpretation" depends on the
    depth: at depth `n` it ranges over depth-`n` shapes. `lift`'s direction from depth `n'` to
    `n ≤ n'` then needs arguments saturated at depth `n` to be saturated at depth `n'`, which
    nothing gives; quantifying over every depth makes `LR (n+1)` refer to deeper relations.
  - Relational firing (the relation's reduction fires K-like and indexed iota steps only when
    the indices are related to `idx` at every shape below their interpretation, one depth
    down) settles the K and iota cases and the derived K-like equalities: a firing condition is
    a fact about the terms, and wherever adequacy needs it the index equality is a
    subderivation. It fails the same way: a spine can fire at depth `n+1` (indices related at
    every depth-`n` shape) and stay stuck at depth `n+2`, so `lift` and `mono_l` across that
    depth relate two stuck spines at one depth and need their reducts related at the other.
    Firing at the interpretation's own depth is not well founded, since a spine's indices can
    be interpreted deeper than the spine is checked.
- All three need the same missing fact: pairs related at every depth-`n` shape below their
  interpretation are related at every deeper one. For judgmentally equal terms that is closure
  under conversion again.
- The K-like case needs injectivity itself, not only some closure. For `X Y : Type`,
  `Eq.rec (motive := fun T _ => T) (m : X) Y h : Y` steps to `m` when `Y ≡ X`; relating `m` at `Y` is
  `LR.conv` with `TyDefEq X Y`, and where `X` and `Y` are pi types that is the relation of their
  domains, `forallE_inv`'s content at the motive's argument depth. Any route through the
  relation must prove injectivity below a recursor's depth inside its constant case, from the
  one fact the case has, `Y ≡ X`.
- Other recursion orders do not supply it.
  - Depth-free shapes ordered by structure: the size the motive conversion needs is bounded by
    the motive's shape, as with depth, but the relation there comes from adequacy of the
    derivation of `Y ≡ X`, and adequacy at a shape needs constant cases at larger ones (the
    application case climbs, as with depth: `(fun g => g 0) (fun _ => 5)` at a depth-6 result
    needs `fun _ => 5` at depth 7 and the function at depth 8). The regress has no measure:
    each constant case appeals to another derivation in the whole environment.
  - Depth-uniform relations (the relation at depth `n` agreeing with every deeper one on lifted
    shapes): depth `n+1` sees fields and graph entries depth `n` does not, so relation at every
    depth-`n` shape never implies relation at depth `n+1` unless the terms are judgmentally
    equal and the relation is closed under conversion, the fact sought.
  - Firing and conversion decided by the model: the model gives `⟦X⟧ = ⟦Y⟧` and, at sort
    shapes, equivalent levels (`sort_inv`), but `TyDefEq` at a pi shape asks for the domains'
    judgmental equality, which no interpretation determines; proving `X ≡ Y ∧ tight → TyDefEq X Y a` by induction on `a` stops at the pi case, where it is `forallE_inv`.
- So the logical relation, with constant cases quantified over arbitrary related substitutions,
  cannot close `IndRecSat`'s K-like case on its own. Closing it needs injectivity below each
  depth from an independent argument, such as a confluence proof for a reduction that includes
  the K-like and eta steps.
- No counterexample to `forallE_inv` or `indApp_inv` is known. A failure needs a type-level
  redex whose major premise the theory equates with two different values; every rule that
  equates terms non-congruently is ruled out as a source:
  - Proof irrelevance equates proofs, never types, and only at one type. Large elimination out
    of a proposition needs a single constructor whose non-proof fields appear among its indices
    as variables (`LargeElimOK`, as the kernel's `isLargeEliminator`), so two constructor
    applications at one type differ only in proofs unless their indices already differ: a
    failure of `indApp_inv` is needed before proof irrelevance can produce one. The same holds
    for `Eq.rec`'s K-like computation, `Acc`, a quotient of a proposition (`Quot.lift` out of a
    proof of `Quot α r` computes at a proof of `α`) and `Quot.lift`'s rule, whose left side
    repeats `α` and `r`.
  - Structure eta expands deterministically, and on a type that may be a proposition only where
    every projection is allowed, so only proofs are projected; unit-like types hold no types.
  - The remaining rules (beta, delta, iota, projections, the quotient's, partial definitions'
    recursive equations) have one rule per head, so they overlap only through proof
    irrelevance and eta.
- K-like reduction with an impredicative `Prop`, where Gilbert–Cockx–Sozeau–Tabareau and
  Abel–Coquand locate the breakdown of the usual metatheory, gives no counterexample either:
  - A cast `Eq.rec (motive := fun T _ => T) m Y h` computes only once `refl X : Eq X Y`, that is
    `Eq X X ≡ Eq X Y`; no hypothesis or proof supplies a judgmental equality (there is no
    equality reflection), so it needs `X ≡ Y` or an `indApp_inv` failure first.
  - A `Prop`-valued result (`Eq X X` against `Eq X Y`) out of a proof needs a motive into
    `Type`, which is large elimination: `Or` and other non-subsingletons eliminate only into
    `Prop`, so proof irrelevance between `Or.inl a` and `Or.inr b` produces no type equality.
  - Large elimination out of a proof computes from the spine's own indices, whatever the proof:
    Lean's kernel does not reduce `K.rec … h` for `inductive K : Bool → Type → Prop | mk X : K true X` at a hypothesis `h` (it does no K-like step there), while the spec derives it
    through `h ≡ K.mk Y`, at the same `Y → Nat` iota gives at `K.mk Y`. An index that is not a
    variable (`mk n : I (n+1)`) removes large elimination.
  - Abel–Coquand's non-normalizing proofs only loop: proof irrelevance already equates them
    with every proof of their type, so they add no equality between types. Likewise `Acc` and
    other impredicative inductives in `Prop`: unfolding `Acc.rec` through proof irrelevance is
    deterministic in the spine.
  - Every non-joinable peak between type-producing redexes therefore needs a proof typed at a
    type former applied to arguments other than its own indices (`c fs : I idx` with
    `I (ctorIdx fs) ≡ I idx`, `ctorIdx fs ≢ idx`), which is a smaller `indApp_inv` failure in the
    major's typing derivation. Turning that regress into a proof needs the statement for every
    zigzag of steps, not only between type formers: transitivity passes through arbitrary
    redexes, which is where a confluence argument would be needed.
- Injectivity fails for heads that are not type formers, so the relation must not assume it
  there: a definition with an unused level parameter is equal at any two levels
  (`C.{0} ≡ C.{1}` for `def C.{u} : Type := Nat`), a definition can ignore its arguments, and a
  variable applied to proofs is equal at any two proofs.
- Induction on derivations (scoping; nothing built). The invariant is a typed relation `Inv Γ e e' T`, defined by recursion on the head form of `T` under a deterministic type-level head
  reduction (beta, delta, iota, projections' iota, the quotient's rule, and for recursors of
  large-eliminating propositions only the K-like step, firing when the spine's indices equal the
  constructor's judgmentally, so that it never overlaps ordinary iota):
  - at a sort: if either side head-reduces to a head form, so does the other, and the two agree:
    equivalent sorts; pi types with related domains and codomains; the same type former, level
    and argument by level and argument; the same neutral head with related arguments;
  - at a pi type: applications to related arguments are related (this absorbs lambda eta);
  - at a structure: projections are related (structure eta); at a proposition: nothing (proof
    irrelevance); at an inductive type: the least relation closed under constructors and
    neutrals.
    The recursion is on universe level and structure: `Prop` contributes nothing, so impredicativity
    does not enter, and types without a head form (`Acc.rec` unfolding forever) are covered by
    the clause that transfers having one. `forallE_inv` and `indApp_inv` are its sort clause.
    Unique typing at the components' sorts has to be carried along, as `IsDefEq.uniq` does.
- The rules, with the fundamental lemma stated under related substitutions:
  - pass from the induction hypothesis: `symm`, `sortDF`, `forallEDF`, `lamDF` (substitution),
    `beta`, `eta`, `proofIrrel` (a proposition's clause is empty), `defeqDF` (the type equality is
    a subderivation, so its sort clause moves the relation from `A` to `B`), `projDF`,
    `projIota`, `projEta`;
  - pass with a lemma: `bvar` (determinism of the head reduction), `constDF` (reduction commutes
    with `instL`, and the K-like firing condition moves along equivalent levels), `trans`
    (agreement composes once components' sorts agree), `extra` (the right side's typing is not a
    subderivation, so this needs an outer induction on the environment, as `AdequacyHyps`
    does);
  - fail: `appDF` at a recursor spine, in the recursor's own case. Ordinary iota is a constant
    case like the logical relation's. The K-like step fails: it fires on a judgmental index
    equality with no derivation in the induction, and relating the reduct needs the relation
    between the motive at the spine's indices and at the constructor's. For
    `Eq.rec (motive := fun T _ => T) (m : X) Y h` that is `Inv` of `X ≡ Y` at `Type`, from an
    arbitrary derivation. Neither derivation size nor the stratification index bounds it:
    `HasTypeStratified.defeq` holds an unstratified conversion. Universe level grows the wrong
    way (the needed judgment `X ≡ Y : Type` sits one universe above `m : Y`).
  - Firing the K-like step only on syntactically equal indices, or on indices related by the
    induction hypothesis, breaks congruence under proof irrelevance instead:
    `Eq.rec mot m Y h ≡ Eq.rec mot m Y (refl X)` relates a stuck spine to one that computes.
    Allowing ordinary iota on proof majors as well brings an overlap with the K-like step whose
    reducts agree only by `indApp_inv` on the major's typing, again an unbounded conversion.
- So this route stops at the same place as the logical relation, the K-like case, and for the
  same reason: no measure decreases from the judgment being proved to the index equality that
  lets a K-like step fire.

</details>

## Source map and contributing

| Path | Starting point |
| --- | --- |
| [Main.lean](Main.lean), [Replay.lean](Lean4Lean/Replay.lean) | CLI and replay |
| [Environment.lean](Lean4Lean/Environment.lean), [TypeChecker.lean](Lean4Lean/TypeChecker.lean) | Kernel entry points |
| [Inductive/Add.lean](Lean4Lean/Inductive/Add.lean), [Inductive/Reduce.lean](Lean4Lean/Inductive/Reduce.lean) | Inductive declaration checking and reduction |
| [Theory/Inductive.lean](Lean4Lean/Theory/Inductive.lean), [Theory/Typing/Basic.lean](Lean4Lean/Theory/Typing/Basic.lean) | Inductive specification and typing rules |
| [Verify/Environment.lean](Lean4Lean/Verify/Environment.lean) | Top-level declaration verification |
| [Theory/Typing/Injectivity.lean](Lean4Lean/Theory/Typing/Injectivity.lean) | Explicit open hypotheses and proved sort properties |
| [Theory/Typing/LogRel](Lean4Lean/Theory/Typing/LogRel) | Shape model and logical relation |
| [Verify/Axioms.lean](Lean4Lean/Verify/Axioms.lean) | Trusted runtime models |
| [Tests](Lean4Lean/Tests), [Experimental](Lean4Lean/Experimental) | Regressions and unfinished experiments |

For a review or proposed change, state which specification, implementation or
proof obligation it affects, include a reproducer for behavior changes, and run
the relevant build and replay checks above. New hypotheses and differences from
Lean's kernel should be explicit. Reports about this fork should be filed here;
establish whether an issue also occurs upstream before reporting it there.

The project retains upstream's [Apache 2.0 license](LICENSE), copyright notices
and author attribution. The LLM-maintenance disclaimer describes this fork's
changes, not the authorship of the upstream project.

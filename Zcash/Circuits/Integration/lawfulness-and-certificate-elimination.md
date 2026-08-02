# Halo2 lawfulness and certificate elimination

## Status and scope

This document specifies the next major integration arc after the Action circuit
capstone: replace concrete, whole-Action computational certificates with reusable
Halo2-Clean lawfulness and compiler theorems.

The deployed verifying-key equality is intentionally **not** part of this cleanup.
Checking that the circuit-derived key equals the deployed Orchard key is a legitimate
concrete trust-boundary check. It must not, however, double as evidence that the Clean
formal circuit is internally lawful.

There are currently 23 Action-specific computations on the live integration path.
That number understates the architectural debt:

* `ActionGateCoherence.gateData_eq` bundles two independent facts;
* the VK-match bundle contains two further non-capture wellformedness checks; and
* `ActionGateCoherence.lookupData_eq` proves the lookup component of closure
  inactivity as one concrete whole-Action computation rather than a compositional
  configure/synthesis law.

The cleanup backlog therefore contains **26 atomic lawfulness obligations**. The
tables below keep the original 22 rows recognizable, then list the four extra atomic
obligations. The count excludes the intentional deployed-VK equality and does not
double-count the bundle's `K = 11`, which is already represented by
`domainExponent_eq`.

Two further synthesis laws, `LookupRelevantSelectorActivationsExact` and
`LookupInputsNoSimpleSelectors`, were once proved here — at the wrong abstraction
layer, as fields of `TopLevelCircuit` rather than of `FormalCircuit`, backed by a
roughly 3,000-line Action/NoteCommit proof stack. Since nothing consumed them they
have been withdrawn rather than relocated; the residual fidelity gap that leaves is
recorded below. They were never included in the count of 26.

The guiding rule is:

> A concrete VK comparison may establish deployment identity. It must not establish
> that a formal circuit is well formed.

## Why `closeWithOperations` belongs in this inventory

Clean currently defines `FormalCircuit.toConstraintSystem` by taking the raw result of
`configure` and applying `ConstraintSystem.closeWithOperations` to the circuit's
synthesis stream. Closure:

1. appends gates enabled by synthesis but absent from `configure`;
2. appends lookups enabled by synthesis but absent from `configure`;
3. registers queries for those appended arguments; and
4. increases `numSelectors` when lookup expressions use selectors beyond the bound
   allocated by `configure`.

This produces a self-consistent internal object, but it is not the algorithm Halo2
uses. In Halo2, synthesis can enable only a gate or lookup already established by
configuration. If closure changes the raw constraint system, the model has repaired
an invalid formal circuit instead of rejecting it. The live Action path now rules out
the lookup-list case explicitly; the generic compiler still performs the repair for
an arbitrary `FormalCircuit`.

The problem is not cured by comparing the resulting pinned CS with a captured VK.
Such a comparison says that the *repaired derivation* matches the deployed data; it
does not say that the repair was inactive. In particular, semantically redundant or
projection-equivalent repairs need not be observable in every downstream pinned
field.

The desired endpoint is:

```text
rawCS := (c.configure ci {}).2
ops   := c.toOperations ci input

FormalCircuit lawfulness proves:
  every enabled gate is in rawCS.gates
  every enabled lookup is in rawCS.lookups
  every lookup selector is below rawCS.numSelectors

c.toConstraintSystem ci input = rawCS
c.toPinnedCS ci input = PinnedConstraintSystem.ofClosedOperations rawCS ops
```

`closeWithOperations` can remain as a diagnostic or migration helper, but it should
not define the canonical keygen semantics. A useful transition theorem is that lawful
circuits satisfy

```text
rawCS.closeWithOperations ops = rawCS.
```

That theorem makes the current and intended pipelines coincide while callers migrate.
After migration, the raw configure result should be used directly.

The query-registration folds in closure are not a separate atomic obligation. Once
both missing-argument lists are empty, those folds are inactive. The selector maximum
is separate: it can change even with no missing lookup when a configured lookup
mentions an unallocated selector.

## Classification

Each obligation receives one primary classification:

* **G — generic now:** follows from existing `FormalCircuit`, `TopLevelCircuit`, or
  compiler guarantees, with additional generic reasoning only.
* **L — local law needed:** requires a new lawfulness fact attached to the gate,
  lookup, configure program, region, circuit bundle, or operation stream that creates
  the relevant data.
* **R — remove the demand:** the concrete fact exists only because downstream code is
  specialized to Action constants; make that code consume circuit-derived data
  generically.

“Local law needed” does not mean adding a sidecar theorem next to every concrete
circuit. Laws belong in the formal-circuit package or in the object being constructed,
and should normally be discharged by default tactics and compositional theorems.

## The 22 capstone-facing computations

| # | Current computation | Class | Structural replacement | Expected difficulty |
|---:|---|:---:|---|---|
| 1 | `queryCoverageFailures_eq_nil` | L | Gate and lookup query-support laws, plus generic registration/projection theorems. The current diagnostic checks both that every allocated fixed column is queried and that every queried column is allocated; replace both directions structurally, while narrowing coverage to semantically consumed columns. | Medium |
| 2 | `realizationFailures_eq_nil` | L | Region-local fixed-write consistency, table-load consistency, constant-allocation consistency, and selector-packing consistency; compose them using V1 shared-column non-overlap. | Hard |
| 3 | `actionNumPermCols_pos` | R | Let generic replay accept an empty permutation family; derive positivity only in branches that consume a copy edge. | Easy |
| 4 | `actionCopyBounds` | L | Every copied cell is allocated and both endpoint columns are equality-enabled; derive encoded address bounds generically. | Medium |
| 5 | `actionCopyActiveRowFailures_eq_nil` | L | Every referenced cell belongs to its claimed region and its row is below that region's measured extent; transfer through placement. | Medium |
| 6 | `actionNumPermCols_eq` | R | Parameterize replay by `permutationColumns` derived from the circuit; remove the literal `15`. | Easy |
| 7 | `actionCopyAddressFailures_eq_nil` | L | From allocated/equality-enabled endpoints, prove the generic permutation-column-index and placement address round trip. | Medium |
| 8 | `actionMissingConstantAllocations_eq_nil` | L | A constants-allocation law: every `constrainConstant` has an enabled constant column and a free V1 allocation site. | Medium–hard |
| 9 | `actionConstantSites_fit` | L | Derive from the stronger allocation-completeness theorem rather than checking the final Action list. | Medium |
| 10 | `actionConstantValueFailures_eq_nil` | G | Prove that constant collection and allocation traverse the same ordered stream and preserve values through `zip`/`map`. | Easy–medium |
| 11 | `actionConstantCellAddressFailures_eq_nil` | L | Configure law: constant columns are equality-enabled and represented by the permutation/fixed-query machinery; combine with generic address routing. | Medium |
| 12a | `gateData_eq`, gate component | L | Raw configure/synthesis registration: every synthesis-enabled gate was registered by `configure`. This must make gate closure inactive. | Medium |
| 12b | `gateData_eq`, selector-count component | L | Every selector used by a configured or enabled lookup is below raw `numSelectors`. This must make the closure maximum inactive. | Medium |
| 13 | `selectorDegree` | L | Compositional gate/lookup degree bounds, then a generic `ConstraintSystem` degree theorem. | Medium |
| 14 | gate `domainExponent_lt` | L | A supported-domain property on `TopLevelCircuit`, preferably derived compositionally from region/bundle footprint bounds. | Medium–hard |
| 15 | permutation `domainExponent_lt` | R | Share the generic top-level supported-domain fact; remove the duplicate Action computation. | Easy |
| 16 | `domainExponent_eq` | R | Reason over the abstract derived exponent. Keep exact `K = 11` only as part of deployment identity. | Medium |
| 17 | `chunks_eq` | R | Prove generic chunking order/index facts over the derived permutation columns; remove literal `[7, 7, 1]`. | Medium |
| 18 | `columnCount_chunkLen_eq` | R | Consume derived lengths and chunk width; remove literal `(15, 7)`. | Easy–medium |
| 19 | `queryLayouts_eq` | G | Both sides project the same pinned CS. Prove the projection equality with behavioral simp lemmas, not reduction through the concrete circuit. | Medium |
| 20 | `routingCoherent` | L | Configure permutation law: every permutation column has the required zero-rotation query; derive routing from generic chunk indices. | Medium |
| 21 | `deltaPowers_injective` | G | Pure field/group-order argument for the supported permutation-column range. | Medium |
| 22 | `primaryRegistered` | L | Every `constrainInstance` target column is equality-enabled, plus the generic permutation-query law. | Medium |

The split of row 12 makes this table contain 23 atomic obligations even though it
still corresponds to the original 22 theorem rows.

## Additional correctness obligations

| # | Current location or hidden behavior | Class | Structural replacement | Expected difficulty |
|---:|---|:---:|---|---|
| 24 | `action_queriedCells_wellFormed` in the VK-match bundle | L | Gate/lookup query declarations consist only of valid query atoms and match expression support. This belongs in argument lawfulness, not in a concrete capture. | Easy–medium |
| 25 | `action_gates_selectorsCovered` in the VK-match bundle, currently replaced by the Action-specific `Action/SelectorCoherence.lean` sidecar | L | Move gate-selector allocation into the `FormalCircuit` lawfulness package or enforce it through the configure API. The existing compositional proof can discharge that packaged law during migration; selector-compression coverage then follows from a generic compiler theorem. | Medium |
| 26 | `ActionGateCoherence.lookupData_eq` | L | Every synthesis-enabled lookup is present in the raw configure lookup list. The live Action path now proves exact raw/closed lookup-list equality and carries it through `TopLevelGateCoherence`; replace the whole-Action computation with a compositional configure/synthesis law. | Medium |

Together with rows 12a and 12b, these bring the inventory to 26 atomic obligations.
The VK bundle's `actionK_eq` is not another item because row 16 already covers it.

Obligation 26 is therefore enforced on the live theorem path, but remains in this
cleanup inventory because its discharge is computational rather than compositional.
`TopLevelLookup.projectedValues` first transports every enabled lookup back to the raw
configure list through `TopLevelGateCoherence.lookups_eq_configure`; selector coverage
and resolver projection are proved only after that check.

The old `invalidQueriedCells = []` check was previously easy to dismiss because it
was not imported by the capstone. It belongs here nevertheless: this arc is about the
correctness of the formal-circuit/keygen interface, not only the minimum imports of one
terminal theorem.

`Action/SelectorCoherence.lean` is an improvement over a whole-circuit
`native_decide`: it proves selector allocation compositionally through the configure
program. It remains architectural debt because the result lives beside the Action
formal circuit rather than in the circuit package or the construction API whose
lawfulness it establishes. It is therefore an interim implementation of obligation
25, not the endpoint.

## Withdrawn synthesis-law sidecars and the residual fidelity gap

`TopLevelCircuit` once carried two static synthesis obligations:

* `LookupRelevantSelectorActivationsExact`: every lookup operation's recorded enabled
  selectors exactly match the relevant selectors activated in its complete region at
  that row; and
* `LookupInputsNoSimpleSelectors`: lookup input expressions contain no simple
  selectors.

Both fields, together with the sidecars that discharged them for Action
(`Action/SynthesisLaws.lean`, `NoteCommit/SynthesisLaws.lean`, and
`Action/TopLevelSynthesisLaws.lean`, which retraced the entire Action and NoteCommit
synthesis call graphs because circuit and subcircuit constructors do not preserve
this evidence), have been withdrawn as consumerless: no keygen or verifier theorem
ever read them. Lookup projection coverage is established independently, by counting
selector indices rather than by appealing to a region-local activation law.

That withdrawal leaves a known fidelity gap. Halo 2 rejects simple selectors supplied
to a lookup argument — lookup registration panics on one — and Clean no longer models
that rejection anywhere. Nothing in the present chain becomes unsound as a result,
because nothing claims it; but a keygen-fidelity theorem relating Clean's
`configure`/`synthesize` output to halo2's own key generation cannot be stated
faithfully without it. Such a theorem will need a no-simple-selectors premise
reintroduced explicitly.

When that happens, the premise should not be reinstated in the withdrawn shape. The
lesson of the sidecars is that these are laws of `FormalCircuit.synthesize`: the
obligation belongs locally on lookup-emitting bundles, preserved compositionally by
the circuit combinators, rather than reproved across a whole synthesis call graph and
reattached at the top-level wrapper.

## Current compile-cost baseline

The following measurements were taken on one development machine before the most
recent keygen performance work. They are order-of-magnitude costs for compiling the
containing module, not isolated timings for one `native_decide`: module elaboration,
shared concrete-circuit evaluation, and proof checking are included.

| Certificate group | Containing module | Approximate compile time | Approximate peak memory |
|---|---|---:|---:|
| Gate/lookup data, degree, domain | `ActionGateCoherenceCompute.lean` | 10 s | 7.0 GB |
| Primary-instance registration | `ActionInstanceCommitmentCompute.lean` | 4 s | 3.8 GB |
| Domain, chunks, layouts, routing, delta powers | `ActionPermutationDomainCompute.lean` | 1–2 min | 7.4 GB |
| Copy bounds, addresses, constants | `ActionCopyWitness.lean` | 30–40 s | 7.7 GB |
| Fixed query coverage and realization | `ActionFixedCoherenceCompute.lean` | 40 s | 7.0 GB |

The serial total was roughly 2 minutes 40 seconds. These numbers should guide
iteration priorities, not be treated as stable benchmarks: several facts share one
large circuit evaluation, and moving or bundling a theorem can shift the apparent
cost. The closure-inertness obligations are also entangled with circuit derivation and
the VK match rather than timed as a clean standalone group.

## Proposed lawfulness interfaces

### 1. Exact gate query support

For a gate, the list supplied as `queriedCells` records Rust closure-call order, while
expression traversal records syntactic use order and may repeat atoms differently.
The right law is therefore support equality, not list equality:

```text
Gate.QueryExact gate :=
  every entry of gate.queriedCells is an advice/fixed/instance query
  ∧ constraintQuerySupport gate.constraints
      = gate.queriedCells.toFinset
  ∧ constraintSelectorSupport gate.constraints
      = {gate.selector}
```

This captures the user's seed: the cells in the constraints are exactly the declared
queries, plus the gate selector. If future Halo2 APIs deliberately permit valid but
unused closure queries, equality can be relaxed to the required subset direction.
Start with equality because it detects both missing and stale declarations.

The existing `Gate.WellFormed` selector discipline and `QueryExact` should become
parts of a single gate lawfulness interface. Construction should retain current call
syntax through default proof arguments and tactics.

Consequences should include:

* no invalid `queriedCells`;
* every expression query receives the intended registered query index;
* query coverage for every semantically consumed gate fixed column;
* expression projection is independent of an unrelated concrete VK check.

### 2. Lookup query support

Lookups need the analogous law:

```text
LookupArgument.QueryExact argument declaredQueries :=
  querySupport (argument.inputs ++ argument.tables)
    = declaredQueries.toFinset
```

It composes with the existing lookup properties: table expressions are selector-free,
input selectors are disciplined, tuple arities match, and activation rows are exact.
The declaration must reflect the actual configure closure-call order when that order
affects query indices.

### 3. Configure/synthesis registration

The raw configure result and synthesis stream need a packaged law such as:

```text
FormalCircuit.RegisteredIn :=
  let rawCS := (configure configInput {}).2
  let ops := toOperations configInput input
  OperationsKeygenCoherent rawCS ops
  ∧ LookupSelectorsAllocated rawCS
```

The name and exact factorization can change, but the property must live on
`FormalCircuit` (or a construction it contains), not beside each Action subcircuit.
As with Clean's other lawfulness fields, primitives should prove it once and
combinators should preserve it. A default tactic should solve ordinary bundles from
those compositional lemmas.

This law gives:

* `missingEnabledGates rawCS ops = []`;
* `missingEnabledLookups rawCS ops = []`;
* the closure selector maximum equals `rawCS.numSelectors`;
* `rawCS.closeWithOperations ops = rawCS`; and
* canonical `toConstraintSystem` and `toPinnedCS` can use `rawCS` directly.

This is stricter and more faithful than merely baking synthesis-enabled arguments into
the derived CS.

### 4. Configure permutation and constant laws

Configure should also expose:

* every equality-enabled column has the zero-rotation query required by permutation
  routing;
* every constant column is equality-enabled;
* every instance column targeted by synthesis is equality-enabled; and
* allocated column/selector counters are monotone and references are in range.

These are good candidates for proof-by-construction in a restricted append-only
configure monad. Until then, they should be fields preserved by configure primitives
and discharged compositionally.

### 5. Region-operation lawfulness

Each region should certify locally:

* every referenced cell was allocated in that region;
* referenced offsets are below the measured region extent;
* repeated writes to the same local fixed cell agree; and
* copy endpoints use equality-enabled columns.

The V1 planner already proves that regions sharing a measured column receive
non-overlapping column-and-row intervals. That generic theorem turns local fixed-write
consistency into cross-region consistency. Regions may share row numbers; what cannot
overlap is a cell in a shared column.

Tables, constant allocation, and selector packing are separate compiler stages, not
exceptions. Each stage needs a small consistency theorem and a composition theorem
showing that its writes do not conflict with region writes or with the other stages.

### 6. Operation-stream lawfulness

Move the two existing lookup synthesis laws from `TopLevelCircuit` to
`FormalCircuit`, with compositional support in circuit and subcircuit constructors.
The same formal-circuit lawfulness package should grow to cover:

* table loads for the same destination are consistent;
* constants are allocatable;
* instance constraints target enabled columns; and
* region-local laws hold for every synthesized region.

These should compose through operation-list append and circuit calls, so a top-level
circuit inherits them without enumerating every Action subcircuit in one theorem.

### 7. Supported domain

`TopLevelCircuit` should expose a supported-domain fact:

```text
∃ k ≤ fieldTwoAdicity, top.FitsAt k
```

Ideally this follows from per-region or per-bundle footprint bounds and generic
planner bounds. If the complete structural proof is too large initially, a concrete
domain check may remain only as a prominently marked interim certificate with this
replacement named.

## Generic compiler proofs still required

Even a fully lawful circuit does not eliminate all work. The compiler needs reusable
proofs that:

1. the pinned query layouts are exactly the final query-registration state;
2. constant collection and allocation preserve the ordered value stream;
3. permutation column lookup, chunking, and address encoding round-trip;
4. replay handles the empty permutation family and arbitrary derived widths;
5. V1 placement transports region-local bounds and consistency to placed cells;
6. selector compression covers every selector of a lawful gate or lookup; and
7. the required delta powers are injective within the field-supported column range.

These are generic algorithms over small abstract inputs. They should be proved with
behavioral simp lemmas and induction, not `rfl`/`whnf` through a concrete Action
definition.

## Recommended implementation sequence

### Phase A — make raw configure authoritative

1. Define the configure/synthesis registration and selector-allocation laws.
2. Prove closure is inactive for lawful circuits.
3. Put the law on `FormalCircuit` with compositional primitive/bundle support.
4. Change canonical `toConstraintSystem`/`toPinnedCS` to use raw configure output.
5. Retain `closeWithOperations` only as a migration/diagnostic helper.

This phase replaces gate closure, lookup closure, and selector-bound closure and
prevents the VK capture from hiding a modeling error.

### Phase B — remove concrete downstream demands

Generalize permutation replay and domain consumers to remove rows 3, 6, 15, 16, 17,
and 18. Exact deployed constants remain visible only in the VK identity check.

### Phase C — gate, lookup, and configure lawfulness

Add exact query support, degree bounds, permutation-column registration, constant
column laws, and instance registration. This addresses query coverage, constant-cell
routing, degree safety, permutation routing, primary-instance registration, invalid
query declarations, and the local premise of selector-compression coverage.

### Phase D — generic projection and algebra

Prove query-layout projection, constant-stream value preservation,
selector-compression coverage, and delta-power injectivity.

### Phase E — region, copy, constants, and fixed realization

Build region-local allocation/write laws and generic placement transfer, then compose
the fixed-producing stages. This addresses rows 2, 4, 5, 7, 8, 9, and the remaining
part of 11.

### Phase F — supported domain

Derive the top-level domain bound compositionally and remove row 14. This can proceed
in parallel with much of Phase E once the footprint interface is settled.

## Completion criteria

This arc is complete when:

* the canonical Clean keygen pipeline does not repair configure/synthesis mismatch;
* all 26 lawfulness obligations are discharged generically or compositionally;
* lookup synthesis laws are carried by every `FormalCircuit`, rather than proved by
  Action/NoteCommit sidecars and attached only at `TopLevelCircuit`;
* the Action integration capstone imports none of the listed concrete certificate
  theorems;
* no whole-Action `native_decide` remains for circuit correctness, layout
  consistency, query registration, routing, or domain safety;
* any retained concrete computation checks only deployment identity or fixture data;
  and
* adding another lawful top-level Halo2 circuit requires no analogous hand-written
  certificate module.

## Non-goals

This work does not remove the deployed Action VK capture, prove fixture provenance,
or change verifier/soundness semantics to speak in Clean-native terms. It strengthens
the Clean-to-Ironwood boundary so that the circuit interface arrives with the
Ironwood-facing properties that soundness needs.

# The Clean boundary: architecture rule

This note is normative for how Clean-originated concepts appear in the ironwood
codebase. It exists so that the work converges on one structure, instead of each
workstream growing local bridge plumbing.

## The principle

Ironwood is the host, Clean is a guest. Ironwood has its own first-class vocabulary —
`VerifyingKey`, `Expr`, `Shape`, its satisfaction notions, its polynomial environments —
and the guest must not scatter *its* vocabulary (`Halo2.ConstraintSystem`, `Operations`,
`Gate`, `Expression F Query`, `RichExpression`, …) through the host's rooms.

Everything Clean produces is funneled through **one concept: `TopLevelCircuit`**, which
carries everything downstream needs and is instantiated once per concrete circuit
(`actionCircuit`).

`TopLevelCircuit` is deliberately two-sided:

* It is a **Clean-native core concept** (it may well migrate into Clean itself —
  `TopLevelKeygen` already consumes only Clean and could follow). Its Clean-typed
  methods (`constraintSystem`, `operations`, `config`, …) are legitimate and public —
  *for the boundary implementation*.
* Ironwood defines an **ironwood-native interface on top of it**, and that interface is
  the only thing non-boundary ironwood code may consume. Its outputs are ironwood-typed;
  a reader never needs to know Clean exists to use it.

The canonical example of the pattern is

```
TopLevelCircuit.toVerifierKey : TopLevelCircuit → ProofParams → URS G → VerifyingKey …
```

— *the* core Clean concept bridged to a core ironwood concept in one method, with every
Clean internal invisible in the signature.

## The ironwood-native interface (target surface)

On `TopLevelCircuit`, defined ironwood-side in the designated boundary modules:

* `toVerifierKey (pp : ProofParams) (urs : URS G) : VerifyingKey (pp.mergeDerived top) …`
  — keygen, with the derived `Shape` in the return type (no lawfulness side condition).
* Shape/domain data as needed by consumers (`ProofParams.mergeDerived`, domain scalars).
* An `Expr`-typed pinned-constraint-system view (the boundary applies
  `RichExpression.toExpr` internally, exactly as `toVerifierKey` already does for the
  VK's `gates`).
* **A satisfaction contract in ironwood terms**: an ironwood-decoded assignment
  satisfying the circuit's derived key implies the circuit's public statement. The
  internal generic proof may pass through `top.Statement` over a reconstructed Clean
  environment, but that environment and the whole satisfaction-integration cluster
  are implementation details rather than a public seam.

## The rule (enforceable, greppable)

> Clean identifiers may appear only under `Zcash/Circuits/` and inside the designated
> boundary modules. Every other `Zcash/Snark/` (and `Common/`, `Security/`) signature
> mentions only ironwood types and definitions the boundary modules export.

`TopLevelCircuit` is the largest of those exports but it is not the only one: a consumer may
name anything the boundary presents in ironwood terms. What it may not do is reach past the
boundary to Clean's own vocabulary.

Review test: *would a reader of this file need to know Clean exists to understand it?
If yes and it is not a boundary module, it is misplaced.*

## Worked example of the anti-pattern

`Zcash/Common/ExprRich.lean`. `RichExpression` exists precisely because ripping
ironwood's `Expr` out of ironwood for Clean's use would have been rude in the other
direction — the type was deliberately duplicated so the clone stays on the guest's side
of the wall. Installing its conversion (`ofExpr`/`toExpr`/`eval_ofExpr`) in the host's
`Common/` un-quarantines it: it presents a Clean-side clone as a core ironwood concept.
(Contrast `Common/Expr.lean` in the same folder — ironwood's own shared AST — which is
exactly what `Common` is for.) The conversion belongs inside the boundary as private
plumbing; with an `Expr`-typed pinned view on the interface, nothing outside the
boundary mentions `RichExpression` at all.

## Current state of the boundary

Checked against the tree as of [`dc421aa0`](https://github.com/zcash/ironwood/commit/dc421aa04592bf37ebb404e3e562793d029581a5) (2026-08-21), except where a later date is given:

* `Zcash/Bridge/` is dissolved; `Snark/VkCommit/` became the designated boundary
  family `Snark/Keygen/`; and the `RichExpression` conversion lives inside the
  boundary (`Circuits/Integration/ExprRich.lean`).
* The cross-language satisfaction seam lives under `Zcash/Circuits/Integration/`.
* Clean imports are otherwise confined to `Zcash/Circuits/` and `Snark/Keygen/`.
  One violation of the greppable rule remains:
  `Snark/Fixtures/SingleAction/Honest/VkMatch.lean` imports Clean, declares
  definitions with `Halo2.SelCompressMap` and `Halo2.AnyColumn` in their types, and
  applies `RichExpression.ofExpr`. It should be restated over the interface, in the style
  that `Snark/Keygen/Certificate.lean` demonstrates.
* The cross-repo migrations — `Circuits/Fixtures/Layout.lean`'s keygen semantics
  into Clean's `Halo2/Keygen`, and eventually `Circuits/TopLevel{,Keygen}.lean`
  themselves into Clean core — ride Clean pin cycles and have not happened.
* **2026-09-15.** The zero-knowledge development is now the concentration of rule
  violations: 22 modules under `Zcash/Snark/ZeroKnowledge/` import Clean directly and 29
  name `RegionOperation`, `Operations`, `LookupArgument` or `ComplexSelector` in their
  signatures. `Zcash/Snark/Soundness/` does not name any of them, so the rule holds
  everywhere else.

  This is not drift in one corner. Reading the 22 module docs, every one of them describes
  pure Halo2 compiler semantics — planner start rows, copy-stream footprints, fixed and
  packed-selector column support outside the usable rows, expression degree bounds through
  the compiler, selector compression counts and roots, advice witness execution, native
  witness read support, and the compact activation traces. Only two of the 22 mention a
  zero-knowledge concept at all, and one of those states that it uses only expression
  structure and query classifications. The rule was not applied to this tree.

  About a third of them are the activation-trace family, whose shared layer now lives at
  `Circuits/Trace/Activations.lean`, written against Clean and Mathlib alone so that it can
  be lifted into Clean. The rest — keygen, copy, advice-witness and selector-compression
  semantics — are a separate migration of the same kind.

  For the trace family the consuming side is easy: what the zero-knowledge argument takes
  from it is label lists — `List (ℕ × ℕ)` and `List ((ℕ × String) × ℕ)` — which need no Clean
  vocabulary at all, so per-circuit label accessors and their coverage facts exported from a
  boundary module retire that third. The other two thirds each need the same treatment
  before the rule can be enforced mechanically.

## Drawing the boundary precisely

The directory boundary is a dependency boundary, not merely a collection of files
created during the circuit-integration work.

### What stays verifier-native

The following concepts speak only the ironwood verifier's language and remain under
`Zcash/Snark/Soundness/`:

* `ConstraintSatisfaction` and `ConstraintPolyModel`;
* `CanonicalConstraintModel` and the canonical domain-selector mathematics;
* permutation and lookup instantiation and semantics;
* the decoded multiopen constraint resolver.

In particular, `CanonicalConstraintModel` takes a `VerifyingKey`, challenges, and an
ironwood `CommitmentId → Polynomial` resolver and produces an ironwood
`ConstraintPolyModel`. It does not know about a Clean circuit and is an input to the
boundary, not part of its implementation.

Some existing files need splitting rather than moving wholesale. For example,
`PolynomialEnvironment` currently contains both the verifier-native interpolation
construction (`rowPolynomial` and its algebraic facts) and the Clean-facing constructor
of a `Halo2.Environment`. The former stays in `Snark/Soundness`; only the latter moves
into `Circuits/Integration`.

### What lives in `Zcash/Circuits/Integration`

This directory contains the implementation that is forced to understand both sides:

* extracting the gate, copy, lookup, and fixed-data obligations of Clean operations;
* interpreting ironwood resolver polynomials as a placed Clean environment;
* connecting selector compression and query layouts to Clean gate evaluation;
* reassembling those families as Clean's authoritative `Halo2.Constraints`;
* applying `TopLevelCircuit.soundness`;
* specializing the generic result to a concrete circuit statement such as Orchard
  Action.

Pure Clean compiler semantics should instead live in `Zcash/Circuits/` or, preferably
when reusable, upstream in Clean itself. Pure ironwood soundness stays in
`Zcash/Snark/Soundness/`.

### Deployed specializations stay with soundness

A theorem that relies on the large captured VK artifacts—`Fixture.shape`,
`Fixture.vk`, `capturedURS`, or the certificate equating those values with
circuit-derived keygen output—belongs under `Zcash/Snark/Soundness/Deployed/`, not in
this directory. Such a theorem may import the boundary's public circuit-derived
terminal, but it should not re-establish Clean semantics itself. Conversely,
`Circuits/Integration` should not import the fixture dumps merely to advertise the
final deployed capstone.

### The public satisfaction contract has two levels

`TopLevelCircuit` declares a `PublicInput` type and an injective layout of its encoded
elements in instance cells. That one layout derives both extraction from a Clean
environment and the cell/value assignments consumed by verifier integration. The
top-level circuit separately extracts a private witness, recombines public and private
data into its formal-circuit witness, and proves that this factorization agrees with
the formal circuit's native extractor. Its `Spec` receives public and private data
explicitly; only `Statement public` existentially hides the private witness.

The boundary therefore exposes two theorem levels:

1. a boundary-internal generic theorem taking satisfaction of the circuit-derived key
   to `top.Statement` at the public input extracted through the declared layout;
2. a public theorem phrased only in ironwood-decoded data and the concrete circuit's
   public statement, for example the structured Orchard Action public inputs.

No caller of the public theorem should construct a Clean environment or mention
`Operations`, `ConstraintSystem`, selector compression, placement, or
`RichExpression`.

### Consequence of circuit-derived key generation

For `vk := top.toVerifierKey pp urs`, the gate and lookup expressions, query layouts,
shape counts, domain parameters, permutation chunks, and commitment families are
outputs of the same circuit-owned keygen pipeline. Their correspondence must not be
reintroduced as an arbitrary caller-supplied coherence record.

Gate and lookup registration plus selector allocation now come from packaged Clean
lawfulness. The remaining `TopLevelConstraintBounds` contains only supported-domain
and polynomial-degree bounds; it is not a gate-coherence sidecar. Gate
well-formedness remains intrinsic to `Gate`.

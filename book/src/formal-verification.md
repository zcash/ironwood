# Formal Verification

Ironwood's formal verification is a Lean 4 development (over Mathlib) in this repository:
verifier soundness for the deployed Halo 2 verifier under `Zcash/Snark/`, and the protocol
security-property layers (binding-signature balance, key binding, and the ledger-model
security games) under `Zcash/Security/`.

The [Guide to the Ironwood Formalization](formal-verification/guide.md) is the reader-facing
overview of what is proved and what a reader of the theorems is trusting;
[Security Models](formal-verification/security-models.md) develops the adversary models and
where hardness judgements live. This page documents two development-wide conventions — how
security breaks are represented, and how what the development trusts is checked at build time.

## Breaks as computed data

The security arguments are reduction-style: a theorem shows that a violation of a protocol
property *exhibits* a concrete break of an underlying primitive — for example a
discrete-log relation, a hash collision, or a commitment-opening collision. Hardness
assumptions are consumed only at the computational layer, against the exhibited break.

Care is needed in how "exhibits" is stated. In a prime-order group, a nontrivial
discrete-log relation between any two elements always *exists*; for any compressing hash,
collisions always *exist* by pigeonhole. So a `Prop` that existentially quantifies over the
break data ("there exist distinct inputs with equal outputs") is simply *true* at every
instantiation of interest. A theorem concluding `property ∨ ∃-break` is then vacuous, and a
hypothesis `¬ ∃-break` is unsatisfiable. Proof irrelevance makes this unrecoverable: even
when a proof constructs the break honestly, a consumer of the statement cannot extract it.

The convention:

* **Break events are structures carrying the breaking data** (the colliding queries, the
  relation coefficients), with `Prop` certificates attached. Examples:
  `RandomOracle.Collision` and `RandomOracle.CollisionUpToSign` (the ±-collision shape
  produced by coordinate-extractor arguments — and the Merkle tree-hash collision computed
  by `Merkle.collisionOfWrongLeaf` is a `Collision` directly), `Ledger.NoteCommitBreak`, and
  `BindingSignature.NontrivialRelation` (the discrete-log relation computed from a
  non-balancing verifying bundle).
* **Reductions are plain computable `def`s** producing them, such as
  `Merkle.collisionOfWrongLeaf`, `noteCommitBreakOfNe`, and the
  `NontrivialRelation.ofImbalance` family (through to the per-pool Orchard and Sapling
  bundle capstones, whose balance statements are the contrapositives under discrete-log
  relation hardness). A structure with data fields
  cannot be inhabited by proof-irrelevant existence, and a plain `def` cannot conjure the
  data from mere existence via choice — the compiler enforces this, so `noncomputable` is
  not permitted for these definitions.
* Efficiency of a reduction is the one property Lean cannot express; it is established by
  inspection. The constructions here are straight-line manipulations of their inputs.
* Predicates over *named* witnesses (for example, a key-binding break of two specific
  witnesses) keep their content as `Prop`s: the breaking pair is bound in the statement
  rather than existentially closed.

The principle's scope is **computational reductions**: it applies wherever the argument is
that an efficient adversary achieving some effect would thereby violate a computational
assumption. For that argument to have content, the reduction must be the kind of object an
adversary's output can be fed through — a computable function producing the break the
assumption forbids. It is not a constructivism requirement on the development at large.
`Classical.choice` is used throughout Mathlib and throughout the `Prop`-valued reasoning
here, and Lean is not intended to support purely constructive proofs. The point is that
choice must not be what *produces the break data*: a `noncomputable` reduction could
satisfy its type by using classical choice to "find" the break, proving nothing about
efficient adversaries. Ordinary theorems, and the `Prop` certificate fields inside break
structures, remain freely classical.

## Trust discipline

Following the pattern of CompElliptic's
[trust discipline](https://github.com/daira/CompElliptic#trust-discipline), the development
distinguishes general theorems from concrete, closed computational facts, and holds them to
different trust standards.

**General, quantified theorems** (the soundness statements and security reductions) rest, in
their abstract form over an arbitrary `Fp`-module, only on the standard classical axioms
`propext`, `Classical.choice`, and `Quot.sound` — no `sorry`, no additional axioms, no compiler
trust. Instantiated at the concrete Pasta curves they may inherit CompElliptic's closed
`native_decide` arithmetic facts: the Pallas or Vesta point-count witness and, where Pallas
square-root data enters, its Tonelli–Shanks root-of-unity certificate. The reusable census also
contains Ironwood's closed NU6.3 cross-address separation check. The `+native` flag on each
build-time check names exactly which owners that endpoint reaches.

**`@[csimp]` replacement lemmas** get their own `assert_axioms` entries in
`Zcash/TrustBoundary.lean`, enforced by `scripts/check_csimp_census.sh` in CI: the compiler
applies a csimp substitution in all downstream compiled code, but the axioms of the lemma's
own proof are not propagated into downstream `native_decide` axiom tracking (
[lean4#7463](https://github.com/leanprover/lean4/issues/7463)), so the check must sit on the
lemma itself. The underlying mechanism study — what `native_decide`, the interpreter, and
precompiled native code actually trust — is
[`design/lean-native-trust-research.md`](https://github.com/daira/CompElliptic/blob/main/design/lean-native-trust-research.md)
in the CompElliptic repository.

**Native-executing checks are temporary, and opt-in until they go.** Executing a check through
locally compiled native code (a `precompileModules` dylib — ours, or the CompElliptic pin's)
trusts the C emitter, the local C toolchain, and the loader, coarse-grained and with no axiom
trace. That is a real extension of the trusted base, and the performance it buys does not
justify it: these checks are slated for removal rather than for permanent accommodation, and
the discipline below is what contains them in the meantime, not a settled design. Loading a
lane's dylib is inseparable from elaborating modules that import it, so the enforced
invariant sits at the level of checks: no module whose import closure reaches a lane module
may contain an evaluation-based check (`#eval`, `#guard`, `native_decide`) unless explicitly
opted in — a documented review discipline; nothing in CI enforces it today. Appendix C of the
research document linked above records the observed Lake behaviour behind this rule.

**Concrete, closed facts with no free variables** may additionally use `native_decide`
(which discharges a goal by running compiled native code, adding a compiler-trust axiom) and
the kernel's GMP-backed bignum arithmetic. The principal such facts in this repository are the
generated per-capture `fingerprint_matches` theorems: numeric checks that the Lean verifier's
assembled multi-scalar multiplication equals the Rust verifier's on each captured proof — two
honest, two at random inputs. Each family's strongest boundary theorem,
`nonInteractiveFingerprint_matches_derived_keyDigest`, composes that captured anchor with the
derived key, concrete transcript hash, and derived key digest. The CompElliptic dependency
applies the same discipline to its concrete curve-arithmetic facts (cardinalities, primality
certificates). Such facts are independently re-checkable (another implementation, or hand
computation, would compute the same result), so a miscompiled or buggy oracle could in principle
be caught by disagreement.

These boundaries are *checked at build time*, not merely documented. `Zcash.TrustBoundary` is the
top-level census for reusable library claims — the key-binding, birthday, ledger, and
binding-signature break reductions together with the fixture-free SNARK
binding/knowledge-soundness stack (the executable extractors, the endpoints across the modeled
adversaries, and the DL capstones). `Zcash.lean` imports it directly, so `lake build Zcash` enforces
that census. Concrete capstones stay with their captures in the fixture-local trust-boundary
modules and are enforced by `FixtureCheck`. The obligations use two commands from
`Zcash.Meta.AxiomCheck`:

* `assert_axioms d` fails the build unless `d` rests only on the standard classical axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — in particular no `sorry` and no `native_decide`;
  `assert_axioms d +native(…)` additionally permits the toolchain-dependent `native_decide`
  compiler-trust axioms of the named owning declarations, which the curve-instantiated
  endpoints carry. Unlike a `#guard_msgs`-pinned `#print axioms`, it states the expected tier
  in one line and stays green across toolchain bumps that rename the `native_decide` axiom,
  while still failing the moment a declaration reaches beyond its tier. It covers the
  general soundness theorems, probability bounds, and run-time/query-charge lemmas.
* `assert_computable d` additionally requires `d` to be a plain `def` — not `noncomputable` — so it
  guards the *breaks-as-computed-data* discipline: the data-producing reductions (a collision, fold,
  peel, or fork turned into a discrete-log relation) stay genuinely computable, closing the gap
  where a reduction could silently become `noncomputable` and still build. `Classical.choice` is
  admitted only through erased `Prop` certificate fields (`+choice`); the relation coefficients are
  direct terms of the inputs, so the break data cannot have been conjured from mere propositional
  existence. `+native` covers the Vesta producers.

The boundaries kept as literal pins are the four fixture censuses —
`Zcash.Snark.Fixtures.SingleAction.Honest.TrustBoundary`, `…MultiAction.Honest.TrustBoundary`,
and their two `…Random.TrustBoundary` siblings — which belong to
the `FixtureCheck` target (kept out of `lake build Zcash` because the captures are large and slow).
Each states its tier with `assert_axioms` like the rest of the development, and *additionally*
retains `#guard_msgs`-pinned `#print axioms` checks on `fingerprint_matches` and the derived
boundary theorems, documenting precisely *which*
compiler-trust axiom `native_decide` adds — on this toolchain a per-declaration axiom
(`…_native.native_decide.ax_1_1`), where older Lean versions used the global `Lean.ofReduceBool` —
because for a captured fingerprint match the exact axiom set *is* the claim, the case
`Zcash.Meta.AxiomCheck` reserves the pinned form for. CI builds all the default lake targets
(`scripts/check_build_coverage.sh` checks that CI and the lakefile agree on that list, and
that every Lean module is reachable from it), and each `fingerprint_matches`'s
`native_decide` compiles and runs the verifier, so anything `noncomputable` on the
assembled-verifier path fails the build.

What the fixture captures actually *check* is the strongest statement of record in each family's
`Boundary.lean` — `nonInteractiveFingerprint_matches_derived_keyDigest` — with the quantified
match and its ε in `Snark/Fingerprint/Epsilon.lean` and the per-capture headliners in
`Fixtures/*/Random/Epsilon.lean`. Capture lineage, seeds, and the reproducibility pipeline are in
`Zcash/Snark/Fixtures/PROVENANCE.md`. Together, the captures and ε theorems support the typed
Rust↔Lean boundary. The byte layer beneath it is modeled and checked against the captures: every
captured challenge is recomputed from halo2's transcript encoding through a Lean BLAKE2b
(`Snark/Verifier/Transcript.lean`), and the random captures' raw proof bytes decode to their typed
proofs through a canonical reader (`Snark/Verifier/ProofBytes.lean`). BLAKE2b's idealization as a
random oracle remains external; the verifying-key digest that opens the transcript is itself
recomputed from the pinned key description (`Snark/Fixtures/PinnedKey.lean`).
`Snark/Fingerprint/Match.lean` enumerates the boundary. The concrete byte-layer instantiation and
its landing status are tracked in [#66](https://github.com/zcash/ironwood/issues/66).

**The circuit-side layout fixtures are pinned, not regenerated.** The CS and layout dumps behind
`CircuitCheck`'s `TestVk*` comparisons (`Zcash/Circuits/Fixtures/*.json`) were emitted by one-off
instrumentation of halo2/orchard that was never published, so unlike the verifier-fingerprint
captures they have no regenerate-and-diff pipeline: CI pins their bytes (`SHA256SUMS`, with a
set-equality check so an unpinned dump cannot be added), and those pins live in the same
repository they guard. Independent anchoring exists at verifying-key granularity —
`Keygen/Certificate.lean` checks the key derived from the ported circuit against the
upstream-regenerated capture — but the row-level layout content below the key, and the
base-circuit dump (`actionBaseLayout.json`), which has no capture-side anchor at all, rest on the
pinned bytes plus review. Lineage, and the follow-up to regenerate these from released sources,
are recorded in `Zcash/Circuits/Fixtures/PROVENANCE.md`.

## Modelling boundaries

The trust discipline above bounds what the *proofs* rest on. The boundaries in what the
statements *model* —the random-oracle treatment of the challenge hash, the
algebraic-adversary restriction, the abstract types standing in for byte-level encodings, and
the sampled bases standing in for the deployed fixed ones— are neither axioms nor
compiler-trust questions, so no census sees them. The Guide's
[What you are trusting](formal-verification/guide.md#what-you-are-trusting) states each of
these boundaries and collects the whole set;
[Security Models](formal-verification/security-models.md) develops the adversary models they
define and where the hardness judgements live.

Coined terms and shorthand for the development are
collected on the [Definitions](formal-verification/definitions.md) page.

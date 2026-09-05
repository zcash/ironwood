# Source Map

A directory-by-directory index of the Lean development under [`Zcash/`](https://github.com/zcash/ironwood/tree/main/Zcash):
what each subtree contains and where to start reading. It is the source-tree companion
to the [proof map](proof-map.md) (which traces how the results connect), the
[ledger security games](ledger-security-games.md) (which state the properties being proven),
the [security models](security-models.md) page (which describes the methodology),
and the [definitions](definitions.md) page (which defines the coined terms).

The development has four tiers. **`Zcash/Arithmetic/`** holds the objects the other three are
stated over — the scalar field, the verifier group and its reference string, the fingerprint
multiscalar multiplication, and the transform machinery and fast kernels behind them.
**`Zcash/Snark/`** is verifier soundness for the deployed Halo 2 verifier — an accepting proof is
bound to a witness satisfying the circuit, or else an explicit break of a hardness assumption is
computed. **`Zcash/Circuits/`** is the circuit layer — a port of the Orchard Action circuit onto
Clean's Halo 2 formalization, saying what satisfying that circuit means in protocol terms, with
`Integration/` carrying the Clean-to-Ironwood boundary. **`Zcash/Security/`** is the protocol
security-property layer — the binding-signature balance, key-binding, and ledger-model games built
on top. A small set of shared leaves (`Zcash/Common/`, `Zcash/Meta/`) and a library-wide trust
census (`Zcash/TrustBoundary.lean`) support all four.

Each `.lean` file carries a module docstring with the details; this page stays at the
directory level, naming the notable modules as entry points.

## Top level — `Zcash/`

- **`Common/`** — shared leaves that two tiers need and neither should import the other for.
  `DiscreteLogRelation` carries a nontrivial `F`-linear (discrete-log) relation over an arbitrary
  indexed basis (`AlgebraicRelationWitness`) as *computed data* — the coefficients — so the
  reduction-style security arguments can produce a break rather than merely assert one exists (see
  *breaks as computed data* on the [Formal Verification](../formal-verification.md) page), and
  turns one into a discrete log against known slot logs. `ProgrammedBasis` turns a relation into a
  discrete log against a basis programmed from the DL challenge (Jaeger–Tessaro,
  [Expected-Time Cryptography: Generic Techniques and Applications to Concrete Soundness](https://eprint.iacr.org/2020/1213), Lemma 3);
  `RelationProbability` and `RelationProbabilityCoins` price that reduction's single miss hyperplane at `1/|F|`, and
  `UniformMeasure` holds the distribution facts they count with. None of these restrict the
  adversary — they consume relation coefficients from any source, and what scopes them is how the
  basis is sampled — so they sit here rather than under `Snark/Soundness/AGM/`. `Expr` is the
  gate-polynomial AST exactly
  as halo2 evaluates it, produced by the circuit-side VK-match projection and consumed by the
  verifier stack. `RelationWitness` supplies the combinators for sequencing a computed break branch:
  a conclusion `A ⊕' R` cannot be case-split classically, so composing such reductions — and
  commuting a family of them past `∀` — needs explicit searches rather than `by_cases`. `ParMap` is
  `List.map` on the task runtime, proven equal to `List.map` definitionally. The `Oracle/` subtree
  holds the generic oracle-computation machinery shared by the Fiat–Shamir soundness reductions and
  the group-hash indifferentiability argument, so neither tier owns it: `OracleComp` is the
  bounded querying-adversary model — an adaptive oracle-query computation with eager whole-table
  semantics, an explicit query bound, and a per-run read log, plus dedup, domain restriction,
  query-charge accounting, and escape bounds; `Model` holds the one-sided
  `PMFEventBiasLE`/`PMFWeightedBiasLE` bias-transport interfaces; `Hybrid` is the adaptive
  fresh-answer hybrid that turns a single-query bias into the `Q·ε` bound; `LabeledOracleComp` adds
  labeled query trees and the first-label bad-set bounds; and `WithReads` returns a run's own reads
  with its output, growing the query bound only by the re-queried family's size.
- **`Meta/`** — build-time metaprogramming. `AxiomCheck` provides `assert_axioms`, a sibling
  of Mathlib's `assert_no_sorry` that asserts an *upper bound* on a declaration's trusted
  base without hard-coding the pretty-printed axiom list, so the trust pins stay green across
  toolchain bumps that rename the `native_decide` axiom, and `assert_computable`, which additionally
  requires the declaration to be a plain `def`. `EndpointCensus` enforces the endpoint census a
  second time from the elaborated environment: both census commands record every pin they
  elaborate, and `assert_endpoint_census` — run by `Zcash/CensusCheck.lean`, the `CensusCheck`
  target, whose imports span every census file — fails the build on an endpoint-named declaration
  with no recorded pin, closing the surface-syntax evasions a source-text scan cannot see.
- **`Arithmetic.lean`** — the tier's root module, and the only place in the repository that earns
  root vocabulary: `Fp` and `URS` are re-exported at `Zcash` so every module finds them by the
  enclosing-namespace walk.
- **`TrustBoundary.lean`** — the library-wide census that makes the trust claims build-time
  checks rather than prose: a change that widens any checked declaration's trusted base — a
  reachable `sorry`, an unexpected axiom, or `native_decide` where none was permitted — fails
  the build here. Computed break reductions are pinned with `assert_computable`, theorems with
  `assert_axioms`. The SNARK-side censuses were consolidated into this one file, so apart from
  the four per-capture fixture boundaries below it is the single place the trust claims are pinned.

## Arithmetic — `Zcash/Arithmetic/`

The objects every other tier is stated over, and the evaluation lanes that make the concrete
computations affordable. Most of these names stay qualified; a module that wants one opens
`Zcash.Arithmetic` for exactly that name.

`Field` fixes the scalar field `F_p` (Vesta's scalar = Pallas base) and its cardinality, which
appears in every Schwartz–Zippel bound; `Group` fixes the verifier group `E_q` (Vesta) and the
uniform reference string as an `F`-module, with the concrete instantiation unconditional —
CompElliptic's Vesta curve is a proven `AddCommGroup` and its order is pinned with no assumption —
and `VestaModule` supplies that module instance as a plain `def`. `Msm` is the fingerprint
multiscalar multiplication the verifier collapses its whole check into, mirroring halo2's `MSM<C>`,
and `FastMsm` gives it a windowed Pippenger evaluation path registered with `@[csimp]`, so the
fixtures' `native_decide` auxiliaries run fast while the statement surface is untouched.

The transform stack is what the verifying-key derivation is built from: `Domain` (halo2's domain
scalars
— `omegaOf`, `DELTA`, the primitive-root facts, bridged to CompElliptic's certified Pasta root),
`Fft` (`bestFftG`, halo2's `best_fft` over an arbitrary `Fp`-module, so the scalar and group
instances share one definition), `FftSpec` (its full DFT specification, `bestFftG_dft`), `InvDft`
and `ScalarInvDft`, `LagrangeBasis` (the closed coefficient form `ℓ_i = n⁻¹ · Σ_t ω^{-i·t} Xᵗ`),
and `CommitLagrange` (the per-column committer, which inverse-DFTs the coefficients as *scalars*
and commits against the monomial basis, so no group FFT is ever evaluated). `NatKernel` and
`NatKernelEquiv` are the dictionary-free evaluation lane underneath — projective Vesta points as
canonical-`ℕ` triples dispatching to GMP under the interpreter, proven equal to the
statement-surface functions.

## Verifier soundness — `Zcash/Snark/`

### `Core/` — the verifier's proof-side objects

`ProofString` is the proof as opaque field and group elements after canonical decoding;
`Challenges` records the verifier's challenges in squeeze order (`θ, β, γ, y, x`, the multiopen
`x₁…x₄`, and the IPA `ξ, z` and round challenges `uⱼ`). The field, group, and MSM these are read
against live in `Zcash/Arithmetic/`; `Core.lean` is a one-line compatibility shim re-exporting
`Msm` at `Zcash.Snark` for the generated captures, to be deleted when they are next regenerated.

### `Verifier/` — the MSM assembly

The pure function that assembles the fingerprint MSM in the exact order of halo2's
`plonk/verifier.rs` — the Lean image of the interactive verifier.

- `Assemble` and `Checks` compose the building blocks.
- `Queries` builds the per-argument opening queries; `QueryCommitment` resolves each assembled
  query back to the canonical group element it references.
- `Expressions` recomputes the vanishing argument's `expected_h_eval`.
- `Ipa` is the inner-product-argument opening (`compute_s` / `compute_b`).
- `FiatShamir` models halo2's BLAKE2b challenge schedule as an abstract `squeeze`.
- `AssembleSpec` says what the rejecting `assemble?` returns when it does not reject — exactly
  the total assembly's value — the operational interface both the fingerprint walk and the
  deployed soundness layer consume.
- `OrchardShape` specializes the verifier shape to the captured Orchard column and query
  dimensions while leaving the action count free; every consensus-valid action count
  instantiates it.
- `Parametric` proves the assembly and schedule traverse every sub-proof for an arbitrary proof
  count; every consensus-valid Orchard action count is one such count. At zero, this describes the
  transaction-level absence of an Orchard bundle, not a verifier call with an empty bundle. Actual
  Action-verifier invocations have a positive proof count and the deployed domain exponent `k = 11`.
  The generic Lean functions remain total at `k = 0`, while halo2's IPA implementation requires a
  nonempty challenge vector, so behavioral correspondence is scoped to the deployed positive domain.

### `Keygen/` — the verifying key, derived rather than assumed

The circuit-side half of halo2's `keygen_vk`. `Pipeline` is the single generic route from a closed
`TopLevelCircuit` and a monomial URS to a full `VerifyingKey`: Clean's `Halo2.Keygen` supplies the
pinned constraint system, domain exponent and selector map, and this module adds the group side.
`Derivation` instantiates it at the closed Orchard Action circuit — every definition there is a
`TopLevelCircuit` method applied to `actionCircuit` — and is what ordinary clients consume.
`Lagrange` relates the two directions of the Lagrange basis: the verifier-side commitment keys are
built from the closed coefficient rows, and conversely the derived basis's `i`-th entry is the
monomial commitment to that same closed row. `Certificate` holds the one slow check — a single
bundled
`native_decide` comparing every field of the derived key against the capture, which dominates the
elaboration time of the lane — and so is built only in the fixture lane. `InstanceCapture` joins
the fixture's captured instance commitments to the circuit-derived family the deployed capstone
consumes: the Lagrange commitment key is identified with the certified monomial derivation, and
the captured public-input column is read back as the circuit's own `PublicInputs` record.

### `Fingerprint/` — the cross-check and its soundness

`Match` is the fingerprint match: running the deployed Rust verifier and the Lean `assemble`
on the same proof and challenges and comparing the assembled MSMs coefficient-for-coefficient
— the cross-check that validates the Lean assembly in place of a line-by-line translation
proof; the per-family `Boundary` modules under `Fixtures/` restate it at the Lean-derived key
and schedule as the statements of record. `SchwartzZippel` supplies the abstract
random-evaluation bound: a fingerprint agrees with a random evaluation only with negligible
probability. Outer batching of separate proof blobs by Halo2's optional `BatchVerifier` is
outside this formalization's scope.

`SampleSpace` encodes the proof-string scalars and challenges as one product sample space
(`ScalarSlot`, with the deployed read schedule's `lastEval` shape baked into the type).
`Rational/` instantiates the Schwartz–Zippel bound at `assemble`'s own coefficients — the
quantified random match. `GoodEvent` enumerates the challenge-only denominator factors whose
joint nonvanishing is the good event; `Representation` is the representation toolkit (cleared
`num/den` identities on the event, with challenge folds costing one degree unit per element);
`Family` holds `RationalCoeffFamily`, the object the walk constructs and the ε theorem
consumes. `ConstraintWalk`, `GroupingTable` (with `Verifier/GroupingRef`), `OpeningWalk`,
`IpaWalk`, `OtherCoefficients`, and `Capstone` walk the whole
assembly — grouping stability through a fixed reference table, the opening value, the IPA
scalars, and the positional `other` coefficient stream — into `assembleCoeffFamily`: every
MSM coefficient as a polynomial numerator over enumerated denominators with one degree budget.
`Epsilon` then prices the match. For bounded-degree polynomial numerators over the walk's
enumerated challenge denominators, a family that differs from Lean's agrees at a uniform point
with probability at most `(D + B)/p`. The random fixtures state the concrete ε values;
`Fingerprint/Match.lean` lists the premisses, including class membership and sample uniformity.

### `Fixtures/` — captured proofs and boundary checks

Concrete Orchard captures that exercise the assembly end-to-end and make the Rust/Lean boundary
less silent. This subtree is the `FixtureCheck` lake target, kept out of `lake build Zcash` (the
captures are large, generated, and slow) but built by CI.
`Shared/ScheduleMarker` re-encodes captured Fiat–Shamir schedules into the model's marker form;
`Shared/TamperSweep` is the shared mutation vocabulary of the per-slot negative sweeps; `PostNu63` pins
the canonical post-NU6.3 verifying key and URS so fixture drift is visible here, and
`PostNu63Random` extends the same point equalities to the random captures — kept separate so the
honest lane does not depend on compiling the random data modules. (The join between the captured
instance commitments and the circuit-derived family lives in `Keygen/InstanceCapture`.)

`SingleAction/Honest/` and `MultiAction/Honest/` hold the captured honest single- and
multi-action proofs, each
with its **Fiat–Shamir** schedule check, its `Boundary` statement of record at the Lean-derived
key and schedule, its per-slot tamper sweep (`Negative/Sweep`), and its checked `TrustBoundary`
turning the fingerprint match into
build-time obligations; `SingleAction/Honest/VkMatch` computes the capture's constraint-system fields equal
to the ones derived end to end from the ported `configure` as a standalone diagnostic, not a
soundness or fixture-trust input. The multi-action capture additionally
carries the shape/VK **faithfulness** checks, the adversarial **negative** fixtures, the degree,
schedule and static-check modules, the adaptive-statement knowledge-failure endpoints — the
conditionally staged-certified `2^125` adversary-work one and the deployed `2^123` one, with the
declared-profile `2^123` instantiation pinned as the latter's rung — data-coupled programmed-basis
and verifier-commitment accounting, explicit adversary and
complete-program staging-fidelity obligations, mechanically composed reduction work, a direct-decode
bound derived from a required family invariant, and a separate oracle-query budget, and
`CapturedZeroFamily` — the shape-generic zero prover instantiated at the
captured key's own scalar data, so the staged IPA trace carries eleven live rounds.

Each family's `Random/` subfolder holds the random match-only
captures — the deployed verifier run on random proof strings, deliberately non-accepting. Each has
the same schedule checks and `Faithfulness`, a `VkCertificate` transporting the single-action
keygen certificate along `PostNu63Random`'s point equalities, its `Boundary` statement of record,
aliveness guards in `Negative` (the model assembles at the random point, the capture is genuinely
non-accepting, and one tamper canary), and its own `TrustBoundary` census. What the four families
jointly check is that Lean's assembled MSM equals the deployed one coefficient-for-coefficient at
each captured proof; the two `Random/` families additionally carry the per-capture ε modules that
price the quantified match (`Fingerprint/Epsilon.lean`, `Fixtures/*/Random/Epsilon.lean`).
Capture lineage and seeds live in `Fixtures/PROVENANCE.md`, and `Fixtures/MANIFEST.tsv` binds
each committed capture to its digest, generator, and invocation —
`scripts/check_fixture_manifest.sh` verifies the binding on every CI run and rejects any
generated-looking artifact without an entry.

### `Soundness/` — the soundness argument

The core argument that an accepting proof yields a witness or a computed break. The top-level
modules cover the argument end to end: `Main` (the deployed-acceptance predicate and explicit
verifier-equation correspondence), `KnowledgeSoundness` (the `SnarkRelation` knowledge-soundness relation), `Constraints`
(Schwartz–Zippel soundness of the vanishing check) with `FoldSplit` (recovering the individual
constraints from the verifier's `y`-fold), `ConstraintCore` and `ConstraintRouting` (the
rewind-free deterministic identities the algebraic decoder consumes), `ConstraintRelations` (the
row-level results the capstone's satisfaction predicate yields — the permutation argument's copy
constraints and the lookup argument's inclusion), `DegreeWalk` (an explicit degree
bound `D` for the combined constraint difference, hence `εx = D / |𝔽|`), and
`GoodChallenge`/`ChallengePricing` (deriving the good-challenge exclusions from challenge
uniformity rather than assuming them). The permutation/lookup stack is `GrandProduct` — the shared
grand-product-to-multiset kernel — with `RunningProduct` (telescoping the running product),
`GrandProductBridge` (the two Schwartz–Zippel steps from the verifier's evaluated check to the
multiset identity), `Permutation`, `PermutationConstruction`, `PermutationRows`, `Lookup`, and
`LookupAssembly`. The IPA algebra is `InnerProduct`, `Halves`, `IpaSoundness`, `Consistency`, and
`CommitFold`; the executable extraction route itself lives in `AGM/StraightLineIpa`. `InstanceBinding` closes the public-instance gap: a decoded instance column is the
polynomial halo2 committed from its `instances` argument, or a `(g, U, W)` relation is computed.
`ZeroData` supplies the zero-data multiopen keystone the constant prover families
are built on. `Vesta` pins the abstract group to the actual Vesta curve.
`TopLevelTerminal` connects canonical constraint satisfaction to the Spec of an
arbitrary top-level circuit using that circuit's derived verifier key and public
inputs. `Action/StraightLineTerminal` and `Action/StraightLineEvent` connect the one-run computed
decode to the concrete Action statement and carry a failure as explicit relation data.
`Action/AdaptiveStatement*` is the adaptive-statement stack, the strongest Action notion: one
online-AGM adversary returns the public inputs and proof together. `DeploymentRecord` states the
machine-readable deployment-instantiation record — one identification field per model floor
(challenge law, basis law, key digest, typed acceptance, discrete-log advantage), plus a
certified ceiling on the failure observer's query budget, without which the joint Challenge255
charge would be a free multiple — that a deployed interpretation of the capstones supplies.
`AdaptiveStatementModel`
defines the game and binds the verifying key and selected instance commitments before `theta`;
`Accounting`, `Terminal`, and `Surfaces` decode arbitrary statement prefixes and price the
root, IPA, and semantic surfaces under the single `(Q + 1)` query factor; `Provenance`,
`Semantic`, and `Complete` identify the selected statement's decoded polynomials with the
executable resolver stages; `Event` unions the priced events and `Capstone` discharges the
statistical residual against them; `Knowledge` ends at the executable knowledge extractor and
its failure bound; `Cached` proves that one retained execution gives the same finder and extraction
event; and `Cost` constructs the programmed basis through reified Vesta operations, feeds those
computed points into the adversary, threads reified canonical commitments into verifier assembly,
and derives the conditional staged `2×` group-operation bound. Its private composition carries
one closed program that constructs the charged basis, specializes the exact adversary path with
its annotations and group nodes, constructs a proof-carrying cache from that result, and consumes
that same cache in reified postprocessing. Lean proves the resulting counter equals adversary work
plus reduction work. Since the cost language is [shallow](definitions.md#shallow), fidelity of the supplied
adversary and of generic host callbacks inside the complete program remains external and is stated
separately.
The modeled three-decode inequality is derived from the family's required fixed-representation
cap rather than retained as a free certified-profile number; this generic development does not
construct the concrete deployment family that must satisfy the cap. `Profile` retains
the older declared-resource
compatibility theorem. The shared
`AdaptiveSurfaces` and `AdaptiveTerminal` supply the per-commitment
activity predicates, challenge surfaces, and pointwise semantic terminal both Action routes
consume.

Six subtrees carry the heavier machinery:

- **`AGM/`** — the algebraic-group-model layer: what it adds is the restriction on the *prover*,
  namely that it emits a representation alongside every group element (Fuchsbauer–Kiltz–Loss,
  [The Algebraic Group Model and its Applications](https://eprint.iacr.org/2017/620)). The
  known-log relation-to-discrete-log machinery is model-free and lives in
  `Common/DiscreteLogRelation`, and the programmed-basis adapter in `Common/ProgrammedBasis`;
  `Adapter` supplies only the view of the deployed URS as an augmented basis `(g, U, W)`. This
  subtree adds the algebraic coefficients to the online prover interfaces (`OnlineMembers`,
  `OnlineMultiopen`), reifies erasable group-work events for adaptive programs (`CostedOracle`),
  and evaluates the reduction's probability loss at Vesta (`ProbabilityVesta`) — programming *every*
  basis slot from the
  DL challenge rather than guessing which slot the relation will hit, so the loss is an additive
  `1/|F|` with no multiplicative factor. The bulk of the subtree is the rewind-free deployed
  decoder, consisting of the unbatching chain (`AlgebraicUnbatch`, `DeployedX1`,
  `DeployedMultiopen`,
  `ValueUnbatch`, `DeployedValueUnbatch`, `ShiftRecovery`), the direct coordinate decode
  (`DirectX4Columns`, `DirectConstraintFamily`),
  the explicit root sets it must avoid (`DeployedRootSets`, `DeployedRootDecode`,
  `DeployedPinnedRoots`, `PinnedRootWitness`), the retained-provenance route (`OnlineMembers`,
  `OnlineMultiopen`, `OnlineConstraint`, `DeployedConstraintSupply`), and the adapters back onto
  the opened-batch interfaces (`SyntheticOpened`, `DeployedSyntheticOpened`,
  `DecodeToOpened`). `StraightLineIpa` and `StraightLinePinnedRoots` classify one accepting
  algebraic transcript as a clean opening, an explicit relation, or a squeeze-pinned bad-challenge
  event, from a single execution with no rewinding; `AdaptiveOnline`, `AdaptiveRootCore`,
  `AdaptiveDecode`, `AdaptiveIpaSurfaces`, and the `AdaptiveStatement*` modules extend the same
  rewind-free machinery to adversaries that choose their statement online, decoding accepting
  prefixes and pricing the per-round IPA surfaces; `StraightLineFiniteSecurity` records group
  work, random-oracle queries and direct-decode field work as distinct quantities and asserts no
  generic-group DLOG formula. `ZeroFamily` and `ZeroFamilyRoots` are the constant zero-data prover
  at an arbitrary shape, whose multiopen obligation reduces to `0 = 0`.
- **`Canonical/`** — the verifier-native constraint model the circuit layer is handed. It installs
  the fixed selector triple into the commitment-ID resolver (`ConstraintModel`, `DomainSelectors`),
  recovers the three constraint families from the flat `y`-folded list (`ConstraintSatisfaction`),
  interpolates rows on the `ω` domain (`PolynomialEnvironment`), joins halo2's Lagrange-basis
  instance commitments to the extractor's monomial coefficient vectors (`InstanceCommitment`), and
  instantiates the permutation and lookup arguments at routed decoded polynomials
  (`PermutationInstantiation`, `PermutationSemantics`, `LookupInstantiation`, `LookupSemantics`,
  `LookupRows`), ending at `Terminal`.
- **`Composition/`** — joining the two halves the architecture keeps apart and bounding the
  probability loss the join costs. `Bridge`
  identifies the algebraic extraction's aggregate witness with the deployed decoded terminal's
  opened commitment.
  `DeployedAcceptance` and `DeployedRuntime` name the deployed decision on one oracle table;
  `DeployedRootContainment` and
  `DeployedConstraintContainment` replace the four-level joint-event coupling with a finite union
  of explicit bad-root events, each fixed before its own squeeze, so the residual is additive and
  has no fourth root. `Quotient` reconstructs a genuinely pre-`x` quotient, `PrefixedSqueeze` and
  `ScheduleBudget` bound the probability loss at the `x` squeeze, and `ActionBudget` and
  `AlgebraicRootBudget` cap the
  action-dependent counts at the consensus maximum, with `OrchardConsensusBounds` (and its
  straight-line sibling under `AGM/`) evaluating the composite bounds at the captured Orchard
  shape up to that maximum. The straight-line route is
  `StraightLineDeployed` (the primary deployed path), `StraightLineConstraint`,
  `StraightLineDecodeSupply`, and the two inhabitants of its interface — `StraightLineWitness` at
  the degenerate shape and `ZeroStraightLine` with eleven live IPA rounds.
  `ZeroBasisAcceptance` proves the computation-free steps toward an accepting run of the adaptive
  knowledge machinery: representations and algebraic points vanish at the all-zero basis, MSM
  evaluation reduces to its base terms, and assembly success plus vanishing bases give
  `DeployedAccepts`; assembly success at a guard-passing oracle and the base-provenance walk
  remain open.
  `SemanticChallengeRemainder` bounds the probability loss from the bundle-wide `y`/`β`/`γ`/`θ`
  exclusions the Action-level statement needs, and `DirectPathCost` bounds the direct-coordinate
  postprocessing's field
  operations and data traversal by a shape polynomial with no `|F|` term.
- **`Deployed/`** — algebra for halo2's actual deployed IPA. `Fold` rewrites the flattened
  verifier MSM's generator term into the closed-form fold consumed by the straight-line extractor;
  `Verification` exposes halo2's explicit IPA verifier equation; and `Binding` supplies the
  augmented-generator collision reductions shared by the computed AGM path.
- **`FiatShamir/`** — the reusable Fiat–Shamir random-oracle kernel: random-oracle primitives
  (`Oracle`), the deployed squeeze ordering (`Ordering`), random-oracle execution and IPA-field
  splicing (`Execution`), closed-form IPA assembly algebra (`Assembly`), the
  one-level pinned-squeeze bound and the additive union of pinned root events (`PinnedSqueeze`,
  `PinnedRoots`), and the wrapper that returns a run's own oracle reads with its output
  (`WithReads`).
  **`FiatShamir/Adversary/`** builds the querying-adversary reduction on top: the `Q`-query
  adaptive adversary model (`OracleComp`), the Fiat–Shamir-to-AGM handoff (`Algebraic`),
  oracle-domain reduction to finite support (`DomainReduction`), and the adaptive interface and
  pre-IPA query accounting (`Adaptive`, `PreIpa`, `Provenance`). These components use the bounded
  querying-adversary model to price straight-line pinned-root events.
- **`Oracle/`** — the squeeze idealization and its deployed gap. `ChallengeUniform` gives the
  exactly-uniform challenge law over `Fp`; `Challenge255` prices the deployed conversion against
  that ideal — a uniform 512-bit digest reduced modulo `p` overshoots uniform by exactly
  `r(p−r)/(p·2^512) < 2^-260`, stated as the `PMFEventBiasLE` premiss the work-factor capstone's
  bias conjunct consumes, with BLAKE2b's idealization as the uniform digest remaining external.
  (The generic oracle-computation machinery — `OracleComp`, the adaptive hybrid, and the
  `PMFEventBiasLE` transport interface — are in `Common/Oracle/`.)
- **`Multiopen/`** — the multiopen argument's value binding. `Decode` supplies the coefficient and
  Vandermonde primitives; `Opened` defines the augmented opened-batch and member-decode interfaces
  populated by explicit AGM representations; and `Deployed` proves that halo2's `x₄` fold has the
  required flat power-batch shape. `Compat` is the MSM evaluation spine; `RPoly` supplies the
  interpolation core (Mathlib's `Lagrange.interpolate`, plus the bridge to the deployed `foldl`);
  `ValueCheck`, `ValueCheckDeployed`, and `NodeBinding` provide the deployed algebra consumed by the
  AGM unbatching chain; and `ConstraintResolver`, `CanonicalSelection` and
  `CanonicalRelation` route the decoded members into the canonical constraint model, which is the
  semantic handoff to the formal circuit.

### `Capstones/` — the advertised endpoints

Where the deployed Action circuit's own statements are stated. `Action.lean` states the
endpoints — knowledge-soundness bounds for every consensus-valid bundle size, in compositional
error-formula form with declared and with staged-certified group-work accounting, in the
staged-certified finite-security form at `2^125` adversary work, and in
the deployed form that consumes an `ActionDeploymentInstantiation`, charges the
joint Challenge255 bias once for the whole transcript, and prices that charge at `2^-136` against
the record's certified query ceiling. Knowledge soundness is the only property advertised: it implies
the plain-soundness statement, so that is not stated separately. Legacy fixed-statement endpoints
and their events are retired.

`Action.lean` is the only endpoint file here. The `Action/` subdirectory below it holds what
discharges those endpoints at the captured key: `Base` carries the shape identification the
chain is stated over, `Checks` the captured key's scalars and static checks, and `Budgets` the
semantic surfaces. Those three are instance-level — stated at the capture and reaching it through
their imports — which is why they sit here rather than under `Soundness/`, a subtree that imports
no fixture so that the captures stay off `lake build Zcash`'s path.

Endpoints about the *verifier's algebra* rather than the circuit statement live with the layer that
proves them: the captured straight-line knowledge errors in
`Fixtures/MultiAction/Honest/StraightLineKnowledgeError`, and the consensus-maximum work factors in
`Soundness/AGM/StraightLineOrchardConsensusBounds`. Every endpoint, wherever it sits, is a
top-level leaf that nothing else depends on, which is why each must be named directly in a
`TrustBoundary.lean` census entry — see `scripts/check_endpoint_census.sh`, enforced a second
time from the elaborated environment by the `CensusCheck` target (`Zcash/Meta/EndpointCensus.lean`).

### `Contract/` — what the endpoints promise

The auditor-facing layer over `Capstones/`. `Knowledge` defines `KnowledgeContract`, a record of
the runs a knowledge claim quantifies over, their law, what acceptance means, what an extraction
returns, what a returned witness certifies, the failure event, and the concrete error — together
with the generic consequence that accepting a false statement is bounded by the same error.
`Action` instantiates it at the deployed Action circuit, reusing
`orchard_action_adaptiveStatement_knowledge_error_bound` unchanged as the claim.

The record is deliberately not circuit-specific. Action is its only instance today because it is
the only circuit carrying an advertised capstone; `CommitIvk`, `NoteCommit`, `Ecc`, `Sinsemilla`,
and `Poseidon` are components composed into its specification rather than independent surfaces.

Nothing here proves anything new, so the layer adds no trust: both declarations are pinned in
`Fixtures/MultiAction/Honest/TrustBoundary.lean` with the same axiom footprint as the endpoint
they re-export. The prose counterpart is
[The knowledge-soundness contract](knowledge-contract.md).

## Circuit layer — `Zcash/Circuits/`

A port of the Orchard Action circuit onto [Clean](https://github.com/Verified-zkEVM/clean)'s
Halo 2 formalization, with elliptic-curve arithmetic from
[CompElliptic](https://github.com/daira/CompElliptic). Each chip is ported from the actual Rust
(`orchard@0.14.0`, `halo2_gadgets-0.5.0`) rather than from memory, and the module docstrings cite
the source lines. Where the Sinsemilla incomplete-addition escapes can fire, the statements carry
them as data (`SpecOrBreak`) rather than assuming them away.

- **`Specs/`** — the value-level protocol specifications the circuits are proven against:
  Orchard data shapes (`Types`), the Pallas curve and its certified arithmetic (`Pallas`,
  `PallasCert`), bit-range arithmetic (`Bitrange`), and the Sinsemilla hash with its
  generators and break structure (`Sinsemilla`, `SinsemillaGenerators`, `SinsemillaBreak`).
- **`Utilities/`** — the shared gadgets: `LookupRangeCheck` (the first lookup-consuming gadget
  ported, generic over `K`), `RunningSum`/`DecomposeRunningSum`, `CondSwap`, and `AddChip`.
- **`Ecc/`** — the ECC chip. Point witnessing (`WitnessPoint`), complete and incomplete addition
  (`Add`, `AddIncomplete`), variable-base multiplication in its incomplete/complete/overflow
  phases (`Mul`, `MulIncomplete`, `MulIncompleteRound`, `MulComplete`, `MulOverflow`,
  `DoubleAndAdd`), and fixed-base multiplication (`MulFixed/`, with full-width, short, and
  base-field-element variants). **`MulFixed/Certs/`** holds the six deployed fixed bases with
  their window-table certificates, kernel-checked through `CertCheck`'s `ℕ`-literal evaluator.
- **`Sinsemilla/`** — the Sinsemilla chip: the `2^K` generator table (`Basic`), one hash piece
  and its rounds (`HashPiece`, `HashPieceRound`), the `⊥`-propagating chain (`Chain`,
  `HashToPoint`), the commit domain (`CommitDomain`), and the fixed-depth Merkle path (`Merkle`).
- **`Poseidon/`** — the Poseidon chip: the `pow5` S-box and round structure (`Pow5`, `Rounds`,
  `Constants`), the permutation (`Permute`), and the sponge/hash at `ConstantLength<2>` (`Hash`).
- **`NoteCommit/`** and **`CommitIvk/`** — the two commitment circuits, each as pieces and
  decompositions, the gate set, the canonicity checks, and the assembled `Main`/`MainBundle`
  contract at the extracted window scalar.
- **`Action/`** — the top-level Orchard Action circuit. `Circuit` is the ironwood `configure`
  and `synthesize` in exact region-creation order; `CircuitPreNU63` is the post-NU6.2
  circuit without the cross-address region (both share `configure`);
  `RealBases` instantiates everything at the actual deployed constants; `PublicInput` declares the
  public instance-cell layout and splits the semantic witness into public and private halves;
  `SelectorCoherence` certifies that every selector reference the configure program registers was
  allocated by that same program; the per-check modules are `ValueCommit`, `DeriveNullifier`,
  `SpendAuthority`, and `AddressIntegrity`; `Bundle` is the end-to-end statement against protocol
  spec §4.17.4; and `TopLevel` presents the whole thing as a closed `TopLevelCircuit`.
- **`Integration/`** — the Clean-to-Ironwood boundary, and the largest directory in the tree. Only
  modules that *translate* belong here; pure verifier-native constraint, permutation and lookup
  mathematics stays in `Zcash/Snark/`. It compiles the circuit's declared structure into what the
  verifier's soundness model quantifies over: gates and lookups from the operation stream
  (`OperationGates`, `OperationLookups`, `OperationFixed`, `OperationCopies`), the permutation
  round trip (`PermutationCompiler`, `PermutationReplay`, `CopyListMembership`), the layout and
  selector compilers (`FixedLayout`, `SelectorCoherence`, `LookupSelectorRows`, `QueryLayouts`),
  the commitment provenance of the fixed, σ and instance columns (`FixedColumns`,
  `PermutationColumns`, `InstanceColumns`), the resolver-backed environments (`ResolverGates`,
  `ResolverQueryEnvironment`, `PolynomialEnvironment`, `ExprRich`), and the reassembly of full
  circuit satisfaction (`CircuitSatisfaction`, `CircuitIntegration`). The `Action*` modules
  specialize all of that to the deployed Action circuit and land at `ActionTerminal`; the
  `TopLevel*` modules are the circuit-generic versions. `Soundness/Action/StraightLineTerminal`
  reaches that same terminal from one accepting execution, and
  `Soundness/Action/StraightLineEvent` bounds the probability loss from the challenge exclusions it
  leaves open — the probability that an accepting run carries neither the bundle statement nor a
  nontrivial relation.
- **`Fixtures/`** and **`Tests/`** — the VK cross-check against Rust. `Fixtures/` reconstructs,
  purely and computably, the layout products a keygen-view dump pins (the ordered copy list, the
  permutation σ, the fixed assignments) from a circuit's `Operations`, with the dumps carried as
  JSON data files (`Json`) and their SHA-256 pins as Lean data (`Stamp`, generated, the module that
  carries a fixture change into Lake's import graph); `Tests/` checks that the ported `configure` is equal
  to those dumps' post-`compress_selectors`, and is the `CircuitCheck` lake target —
  like `FixtureCheck`, kept out of `lake build Zcash` but compiled by CI, with the glob covering the
  whole directory so a newly added test cannot land in no target at all.

## Protocol security — `Zcash/Security/`

The security-property games layered on the verifier, all in the reduction style: a property
violation *exhibits* a concrete break (a hash collision or a discrete-log relation), carried as
computed data.

- **`Common/`** — the classical random-oracle foundation shared by the games. `RandomOracle`
  is the collision vocabulary (the `Collision` / `CollisionUpToSign` structures); `Birthday`
  is the birthday-bound counting for random-oracle ±-collisions, in the counting-fraction style
  used throughout (no probability monad).
- **`Concrete/`** — `PallasGroup`, the Pallas group behind a small protocol-facing wrapper over
  CompElliptic's affine `SWPoint`, carrying the transported group laws and the scalar-module
  structure the deployed pool's primitives are stated over.
- **`BindingSignature/`** — the binding-signature *balance* argument (spec §4.13 Sapling /
  §4.14 Orchard). `Balance` is the shared algebraic core over an arbitrary `F`-module;
  `Orchard` and `Sapling` add the per-pool no-overflow bounds that keep the value sums below
  the scalar-field order. `DiscreteLog` carries the computed relation the rest of the way, to
  the discrete log of `Vbase` base `Rbase`: *if you can unbalance, you can solve DL*. It is
  scoped by the sampling of the two bases, not by any restriction on the adversary, which is
  why it sits here rather than under `Snark/Soundness/AGM/`.
- **`KeyBinding/`** — the key-binding theorem (ZIP 2005, ROM). `Basic` is the deterministic
  layer: a verifying Recovery-Statement witness pins the key components (`ak` up to y-sign,
  `nk`, and the `qk`/`sk` branch) to `ivk` unless an explicit break is computed. `Instance`
  bridges that concrete development to the games' `KeyBindingInterface`, `Pool` states it at the
  Orchard Action, and `Probability` adds the whole-table random-oracle model that turns the
  counting facts into a probability bound.
- **`Ledger/`** — the ledger-model games. `Statement` transcribes the games-relevant conjuncts
  of an Orchard-shaped Action statement over abstract primitives — the interface the games
  consume — and `Model` is the witness-annotated ledger they quantify over, with `Effects`
  reading off the outputs, spends, and shielded-pool balance. `Bridge` is deliberately the only
  place that translates an extracted Action circuit witness into that statement, and the only place
  Sinsemilla escapes become break statements, with `BridgeTests` guarding the protocol
  distinctions a type-correct refinement can silently erase and `SinsemillaDLR` carrying a
  classified escape onward as a relation. The games themselves: `Balance` (every nonzero spend is a
  committed output of a strictly earlier transaction, or a Merkle/note-commitment break is
  computed), `Spendability` (the Faerie-Gold core — nullifiers pin note tuples — plus persistence),
  and `SpendAuthority` (an unsigned spend yields a signature forgery or a key-binding break), with
  `Merkle` proving fixed-depth Merkle trees position-binding up to an exhibited tree-hash collision
  and `Nullifier` reducing a nullifier collision to a discrete-log relation. `Pool` instantiates
  the abstract primitives at the deployed pool, `Value` discharges the transaction-balance premiss
  against the binding-signature layer, `KeyBindingArm` discharges the key-binding ε in the oracle
  model, `Capstone` lifts the deterministic layer to a distribution over valid annotated ledgers,
  and `Completeness` checks the other direction — that an honest wallet's spend actually verifies.
  The experiment lane places those capstones in the challenge-oracle model.
  `ConservationExperiment` and `IntegrityExperiment` compose the arms in one sample space
  —at the sampled bases and, in their `At` forms, at the deployed value bases— and
  `OrchardIntegrityExperiment` instantiates them at the deployed choices.
  `OrchardExtractionExperiment` builds the annotated adversary from a proof-emitting one,
  annotating its chain with the Action circuit's extracted witnesses.

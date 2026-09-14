# Zero knowledge and executable reductions

The zero-knowledge release target is one post-NU6.3 Orchard proof call in
Zakura 1.4.0, using Common `50f712ee22ca95e2dd5230c6f331ce2e433d70ee`.
The model compares that call's observation with a simulator that receives
public inputs and setup parameters. The Action
application theorem constructs the prover's rows from
`ActionWitnessConstructionConditions`, which includes `ActionSpec`, defined
hashes and canonical encodings. The five scalar hints use two 128-bit limbs and
decode over the full `Fq` range. The one-attempt interactive
comparison uses independent uniform input bits and a nonidentity blinding point.

Fiat–Shamir comparisons use a programmable classical random oracle. The
release model returns proof bytes or an error, or records the zero-IPA-challenge
panic. It rejects public identity commitments before the first prover oracle
query and never requests or starts a retry. Its observation hides a failed
call's private proof buffer while retaining the oracle cache.
At an opening-node collision, the IPA receives the actual polynomial
evaluation and the call continues.

`Zcash.Snark.ZeroKnowledge.Zakura.action_simulation_error_bound` transports the
one-attempt reference comparison through this observation. Its new proof terms
and census entries await elaboration. Authenticated source hashes and stored
setup/key comparisons in `Zcash/Snark/ZeroKnowledge/Zakura/release.json` identify
the release; they do not establish universal Rust-to-Lean correspondence.
The existing verifier fixtures were regenerated from pinned Rust and are
consumed by the Lean fixture checks. The unchanged circuit dumps retain their provenance. New
RNG/trace instrumentation is outside this task.

Auxiliary retry and continuing-generator theorems concern additional external
caller policies and are outside the release claim. Concrete BLAKE2b security,
security of a particular PRNG, and whole-program Rust correspondence remain
separate claims. The
[Action witness theorem statements](https://github.com/zcash/ironwood/blob/main/Zcash/Snark/ZeroKnowledge/ActionWitnessSimulation.lean)
give the precise application contract.

## Computability boundary

The operational reduction programs are ordinary Lean definitions with
`assert_computable` pins. `ActionReductionProgram.evalCosted` and
`InteractiveReductionProgram.evalCosted` consume stored inputs and random bits,
produce a Boolean observation, and retain execution counters. Their erasure and
cost theorems connect those computations to the security games; an abstract
probability kernel alone does not supply an executable reduction. See the
[program interfaces and resource model](https://github.com/zcash/ironwood/blob/main/Zcash/Snark/ZeroKnowledge/PROGRAMS.md).

The following proof-side objects retain `noncomputable` declarations:

| Objects | Why the marker remains | Where they are used |
| --- | --- | --- |
| Sampling laws, event masses, error bounds, retry measures, and PRNG kernels | `PMF`, measure, and extended-real operations describe mathematical probabilities. In particular, `ActionReductionProgram.kernel`, `InteractiveReductionProgram.kernel`, and `tapeReduction` are laws of computations, not implementations of a random-bit source. | Distribution equalities, probability bounds, and admissibility predicates. |
| Masking equivalences, linear maps, and finite enumerations | The algebraic proofs use inverse maps and finite-type constructions supplied through choice. The `CommitmentMask`, `IpaSimulation`, `RowMaskRank`, and `PlonkFiniteView` modules own these objects. | Coupling, rank, and finite-distribution proofs; the operational programs do not execute these choice-based constructions. |
| Action source certificates | Normalized source programs can contain auxiliary definitions intended only for kernel reduction. Code generation is disabled for these static certificate values. | Proofs of source erasure, read availability, alias validity, and activation coverage. |

The static Action values are `actionAdviceSourceCertificateRaw`,
`actionAdviceSourceCertificate`, `actionGateSourceCertificateRaw`,
`actionGateActivationSourceCertificate`, `actionWitnessLoadSourceCertificate`,
and `actionValueSourceCertificate`. Their retained data are checked against the
original programs. The noncomputable source-certificate values in
`Zcash.Meta.Tests` serve the same purpose in positive and negative regression cases.

`ActionAdviceSourceData` and `ActionGateSourceCertificate` each certify their
complete original source. `ActionAdviceSourceAliasCheck` and
`ActionAdviceReadPlan` check the full alias and read scans.
`ActionGateActivationCoverage` establishes coverage of the original Action
circuit's gate activations from the gate certificate.
`ActionLookupActivationCoverage` establishes coverage of its lookup activations
from the compositional source trace, which is assembled from the gadgets' traces
and opens the opaque circuit only through its recorded implementation equation.

These large static checks raise the recursion limit and use larger or unlimited
heartbeat budgets during elaboration. The tactics construct intermediate
proofs internally and submit them to the kernel. The final source equalities,
read and alias checks, and activation coverage retain their axiom assertions.
The resource overrides affect elaboration; they do not add logical assumptions
or change the cost model for the prover and simulator.

`ActionWitnessRows` owns the executable application witness constructor.
`ActionWitnessSimulation` uses the static certificates only to prove that its
output satisfies the relation required by the simulation theorems. Executable
finite-tape simulators and their probability laws are likewise separate
declarations. Replacing a proof-side object with an operational producer requires
a computability pin and an update to this boundary.

# Clean-to-ironwood integration boundary

This directory is the designated implementation boundary between Clean formal
circuits and ironwood's verifier and soundness development.

Modules here may import and reason about both vocabularies. Their job is to translate
a closed `TopLevelCircuit` and its circuit-derived keygen data into ironwood-native
interfaces:

* an ironwood `VerifyingKey` and pinned constraint view;
* reconstruction of Clean operation satisfaction from ironwood polynomial
  satisfaction;
* semantic projection of configured lookup tuples into the verifier's
  query-index expression language;
* a final circuit statement expressed without exposing Clean implementation details
  to verifier or soundness callers.

This directory is not a home for generally useful code merely because that code was
written during circuit integration:

* pure verifier algebra, decoded constraint models, permutation/lookup semantics, and
  challenge arguments remain under `Zcash/Snark/`;
* pure circuit definitions and semantics remain under `Zcash/Circuits/`, and reusable
  Halo2 compiler facts live locally in `Circuits/Halo2` pending upstreaming to Clean;
* only code that genuinely translates between the two sides belongs here.

The normative architecture rule and current migration guidance are in
[`clean-boundary.md`](../../../book/src/formal-verification/clean-boundary.md).

The lookup bridge is split deliberately:

* `LookupProjection.lean` proves the query-erasure and selector-substitution
  compiler semantics for configured lookups;
* `LookupSelectorRows.lean` derives exact expression-level selector projection from
  singleton packed-selector cells and the generic fixed-row realization theorem.
  TLC supplies the solution of its children's lookup-selector anchor requirements.
* `TopLevelLookups.lean` routes synthesis-enabled lookups through the
  circuit-derived verifying key, derives selector coverage, table freedom, tuple
  arity, and activation-row fit from Clean's top-level keygen invariants, reduces
  the remaining projection boundary to exact packed-selector values, packages the
  bundle-wide `β`/`γ`/`θ` exclusions into the per-proof witness conditions, and
  constructs the deployed witnesses consumed by the generic full-circuit bridge.
* `TopLevelBridge.lean` is the generic join: it derives gate and lookup families
  from the canonical circuit-owned constraint model and combines them with the
  fixed/table and copy constraints into `FullCircuitBridge`.
* `CopyConstraints.lean` derives Clean copy constraints directly from compiler
  copy-pair equalities and fixed-cell reads, including allocated constants.
* `CopyPermutation.lean` and `PermutationCycle.lean` identify compiler copy replay
  with the verifier's sigma polynomials. `TopLevelCopyConstraints.lean` combines
  that identification with permutation challenge exclusions and constant reads.
* `TopLevelInterpretation.lean` assembles these generic arguments into executable
  private witnesses. `TopLevelWitness.lean` provides the witness types and the
  transport to the circuit's canonical proof assignment.
  `CircuitFieldSupport top` supplies only numerical compatibility bounds;
  `Arithmetic.FieldDomainParams` derives roots and permutation-column separation
  from a certified field generator and its two-adic factorization. The field's
  chosen parameter instance and the circuit's exponent determine `top.omega`.
* `TopLevelInstanceCommitment.lean` derives the verifier's instance commitments
  from any top-level circuit's public-input layout and binds accepted instance
  polynomials back to the supplied public inputs, for arbitrary column and proof
  counts.

The circuit-generic terminal lives outside this boundary.
`Snark/Soundness/Circuit/Terminal` turns canonical constraint satisfaction and
challenge exclusions into circuit-owned witnesses at the verifier's supplied public
inputs. `Snark/Soundness/Action/StraightLineTerminal.lean` specializes it to Action;
the Action event modules charge its relation branch. The compiler-to-polynomial
interpretation is shared by all top-level circuits.

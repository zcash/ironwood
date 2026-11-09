# Clean-to-ironwood integration boundary

This directory is the designated implementation boundary between Clean formal
circuits and ironwood's verifier and soundness development.

Modules here may import and reason about both vocabularies. Their job is to translate
a closed `TopLevelCircuit` and its circuit-derived keygen data into ironwood-native
interfaces:

* an ironwood `VerifyingKey` and pinned constraint view;
* compiled row satisfaction from ironwood polynomial satisfaction;
* interpretation of compiled expressions in the verifier's query-index language;
* a final circuit statement expressed without exposing Clean implementation details
  to verifier or soundness callers.

This directory is not a home for generally useful code merely because that code was
written during circuit integration:

* pure verifier algebra, decoded constraint models, permutation/lookup semantics, and
  challenge arguments remain under `Zcash/Snark/`;
* pure circuit definitions and semantics remain under `Zcash/Circuits/`, and reusable
  compiler theory lives in `Clean.Halo2.Compiler`;
* only code that genuinely translates between the two sides belongs here.

The normative architecture rule and current migration guidance are in
[`clean-boundary.md`](../../../book/src/formal-verification/clean-boundary.md).

The semantic bridge is split by responsibility:

* `Clean.Halo2.Compiler.CompiledGates` and `Clean.Halo2.Compiler.CompiledLookups` recover source
  constraints from compiled row semantics. Query erasure, selector substitution,
  activation routing, and fixed-row realization belong to that compiler layer.
* `PolynomialConstraints.lean` derives compiled gate vanishing from polynomial divisibility
  and compiled tuple membership from the scalar lookup
  argument and the existing `β`/`γ`/`θ` exclusions. Tuple decompression is required
  only at compiler-derived activation rows, with every usable table row available.
  The `θ` event and its executable checks compare compiled tuples; their budget
  depends only on the compiled arities, activation count, usable rows, and proof count.
  Finite-family tuple collision mathematics lives in `Snark/Soundness/Pricing/TupleCompression`.
* `Clean.Halo2.Compiler.CompiledCopies` derives source copy constraints from equality on
  resolved copy pairs. The circuit-owned environment realizes allocated constants.
  `Clean.Halo2.Compiler.CopyPermutation` exports the compiled permutation, its usable-row
  preservation, and recovery of copies from cycle equality. `Clean.Halo2.Compiler.PermutationAssembly`
  proves that executable assembly implements that permutation;
  `Clean.Halo2.Compiler.PermutationRows` computes the row vectors that Keygen commits.
* `PermutationCompiler.lean` proves query routing and chunk-layout facts.
  `Permutation.lean` identifies the compiled permutation with the verifier's sigma
  polynomials and combines that identification with permutation challenge exclusions
  to prove compiled copy equality.
  Verifier-generic coordinate changes live in `Snark/Soundness/Canonical/PermutationCoordinates`.
* `TopLevelInterpretation.lean` assembles `ConstraintsCompiled` and applies
  `top.soundness_compiled` to extract executable witnesses. The compiler theorem in
  `Clean.Halo2.Compiler.ConstraintsCompiled` supplies source constraints and invokes TLC soundness.
  `Assignment.lean` provides the witness types and identifies polynomial column reads
  with the circuit's canonical proof assignment and public-input layout.
  `CircuitFieldSupport top` supplies only numerical compatibility bounds;
  `Arithmetic.FieldDomainParams` derives roots and permutation-column separation
  from a certified field generator and its two-adic factorization. The field's
  chosen parameter instance and the circuit's exponent determine `top.omega`.
* `TopLevelInstanceCommitment.lean` derives the verifier's instance commitments
  from any top-level circuit's public-input layout and binds accepted instance
  polynomials back to the supplied public inputs, for arbitrary column and proof
  counts.

Fixed, permutation, and instance commitments share the verifier-native opening comparison
in `Snark/Soundness/Multiopen/RowBinding.lean`; `Multiopen/InstanceColumns.lean` supplies
the public-instance query routing. Integration supplies compiler provenance for fixed and
permutation rows. Generic list chunking theory lives in `Common/ListChunks.lean`.
`Multiopen/PermutationColumns.lean` provides the verifier-native σ-column commitment
binding argument. `PolynomialEnvironment.lean` translates verifier query feeds to Clean
column reads in the polynomial environment.

The circuit-generic terminal lives outside this boundary.
`Snark/Soundness/Circuit/Terminal` turns canonical constraint satisfaction and
challenge exclusions into circuit-owned witnesses at the verifier's supplied public
inputs. `Snark/Soundness/Action/StraightLineTerminal.lean` specializes it to Action;
the Action event modules charge its relation branch. The compiler-to-polynomial
interpretation is shared by all top-level circuits.

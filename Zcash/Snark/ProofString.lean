import Mathlib

/-!
# The proof string as opaque field and group elements

Auditing the verify call graph established that the halo2 verifier consumes
the proof purely as opaque group elements (Vesta points, `E_q`) and field elements (`F_p`): it reads
them, squeezes Fiat-Shamir challenges, assembles one MSM, and checks `MSM = identity`, never branching
on a proof element's value. This module captures that proof string as plain data, cross-referenced
against the reads in `plonk/verifier.rs` (and the sub-argument verifiers).

A single Ironwood proof covers a whole bundle: `Proof::verify` (`../orchard/src/circuit.rs`) passes
all `N` actions' instances to `plonk::verify_proof`, which reads the per-action elements
`num_proofs = N` times against one shared set of challenges and a single multiopen / IPA opening. So
the proof string splits into **per-sub-proof** vectors (indexed by `Fin numProofs`) and **shared**
elements. The verifier reads all sub-proofs' advice, then all sub-proofs' lookups, and so on,
which `Fin numProofs → Fin _ → …` reproduces; the field order below is the read order.

`Shape` records the per-circuit counts (read off the verifying key) that fix every vector length;
`ProofString shape F G` is the proof itself, over a field carrier `F` and a group carrier `G`. Both
stay generic, so the symbolic verifier (`Zcash.Snark.Verifier`) is field- and group-agnostic; the
concrete instantiation is `F = F_p`, `G = E_q`.
-/

namespace Zcash.Snark

/-- Per-circuit element counts, read off the verifying key; they fix every vector length in a
`ProofString` and the read schedule. Fields: `k` (`log₂` of the domain size, `n = 2 ^ k`, and the IPA
opening has `k` rounds); `numProofs` (sub-proofs verified together — the bundle's Orchard action
count, `instances.len()`); `numAdviceColumns` (`vk.cs.num_advice_columns`, `10` for Ironwood);
`numLookups` (`vk.cs.lookups`); `numPermutationSets` (permutation product-commitment chunks,
`vk.cs.permutation.columns.chunks(cs_degree − 2)`); `numPermutationColumns`
(`vk.permutation.commitments`, one common eval each); `numQuotientPieces`
(`vk.domain.get_quotient_poly_degree()`); `numInstanceQueries`, `numAdviceQueries`, `numFixedQueries`
(`vk.cs.{instance,advice,fixed}_queries`); and `numPointSets` (multi-open point sets, one `u` scalar
each). -/
structure Shape where
  k : ℕ
  numProofs : ℕ
  numAdviceColumns : ℕ
  numLookups : ℕ
  numPermutationSets : ℕ
  numPermutationColumns : ℕ
  numQuotientPieces : ℕ
  numInstanceQueries : ℕ
  numAdviceQueries : ℕ
  numFixedQueries : ℕ
  numPointSets : ℕ

/-- Per-set permutation product evaluations (halo2 `EvaluatedSet`): the product polynomial `zᵢ` at
`x` (`eval`) and `ω x` (`nextEval`), plus — for every set except the last — at `ω^{last} x`
(`lastEval`, hence `Option`). -/
structure PermSetEval (F : Type*) where
  eval : F
  nextEval : F
  lastEval : Option F

/-- Per-lookup evaluations (halo2 lookup `Evaluated`): the product `z` at `x` (`productEval`) and
`ω x` (`productNextEval`); the permuted input `a'` at `x` (`permutedInputEval`) and `ω⁻¹ x`
(`permutedInputInvEval`); and the permuted table `s'` at `x` (`permutedTableEval`). -/
structure LookupEval (F : Type*) where
  productEval : F
  productNextEval : F
  permutedInputEval : F
  permutedInputInvEval : F
  permutedTableEval : F

/-- The proof string, over a field carrier `F` and group carrier `G`, with the fields declared in the
verifier's read order. Group elements are commitments (Vesta points, `E_q`); field elements are
claimed evaluations and the IPA opening scalars.

Per-sub-proof vectors carry an outer `Fin shape.numProofs` (one Ironwood proof covers all `N` bundle
actions): `adviceCommitments` (advice column commitments); `lookupPermutedInput`,
`lookupPermutedTable` (lookup permuted commitments); `permutationProduct` (permutation product
commitments); `lookupProduct` (lookup product commitments); `instanceEvals`, `adviceEvals` (instance
and advice evaluations); `permutationSetEvals` (per-set permutation product evaluations); and
`lookupEvals` (lookup evaluations).

Shared across sub-proofs (read once): `vanishingRandom` (vanishing random-poly commitment); `hPieces`
(quotient `h(X)` pieces); `fixedEvals` (fixed evaluations); `vanishingRandomEval` (vanishing random-
poly evaluation); `permutationCommonEvals` (permutation common evaluations); `multiopenQPrime`,
`multiopenU` (the multiopen `f(X)` commitment and its per-point-set evaluations); and the IPA opening
`ipaS`, `ipaRounds`, `ipaC`, `ipaF` (the blinded-poly commitment `S`, the `k` round commitments
`(Lⱼ, Rⱼ)`, and the final scalars `c` and `f`). -/
structure ProofString (shape : Shape) (F G : Type*) where
  adviceCommitments : Fin shape.numProofs → Fin shape.numAdviceColumns → G
  lookupPermutedInput : Fin shape.numProofs → Fin shape.numLookups → G
  lookupPermutedTable : Fin shape.numProofs → Fin shape.numLookups → G
  permutationProduct : Fin shape.numProofs → Fin shape.numPermutationSets → G
  lookupProduct : Fin shape.numProofs → Fin shape.numLookups → G
  vanishingRandom : G
  hPieces : Fin shape.numQuotientPieces → G
  instanceEvals : Fin shape.numProofs → Fin shape.numInstanceQueries → F
  adviceEvals : Fin shape.numProofs → Fin shape.numAdviceQueries → F
  fixedEvals : Fin shape.numFixedQueries → F
  vanishingRandomEval : F
  permutationCommonEvals : Fin shape.numPermutationColumns → F
  permutationSetEvals : Fin shape.numProofs → Fin shape.numPermutationSets → PermSetEval F
  lookupEvals : Fin shape.numProofs → Fin shape.numLookups → LookupEval F
  multiopenQPrime : G
  multiopenU : Fin shape.numPointSets → F
  ipaS : G
  ipaRounds : Fin shape.k → G × G
  ipaC : F
  ipaF : F

end Zcash.Snark

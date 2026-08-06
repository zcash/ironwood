import Zcash.Snark.Core.Shape

/-!
# The proof string as opaque field and group elements

After canonical decoding, the halo2 verifier consumes the proof purely as opaque group elements
(Vesta points, `E_q`) and field elements (`F_p`): it reads them, squeezes Fiat–Shamir challenges,
assembles one MSM, and checks `MSM = identity`, never branching on a proof element's value
(established by auditing the verify call graph). This module captures that post-decoding proof
string as plain data, cross-referenced against the reads in `plonk/verifier.rs`. Byte-level
decoding — including rejection of invalid encodings and points at infinity — is outside this
typed layer.

A single Orchard proof covers a whole bundle: `Proof::verify`
([zcash/orchard#531](https://github.com/zcash/orchard/pull/531) `src/circuit.rs`) passes all `N` actions'
instances to `plonk::verify_proof`, which reads the per-action elements `N` times against one
shared set of challenges and a single multiopen/IPA opening. So the proof string splits into
per-sub-proof vectors and shared elements; the field order below is the verifier's read order.

`Shape` records the circuit and invocation counts that fix every vector length;
`ProofString shape F G` is the proof itself, generic over the field and group carriers,
with concrete instantiation `F = F_p`, `G = E_q`.
-/

namespace Zcash.Snark

/-- Per-set permutation product evaluations (halo2 `EvaluatedSet`): the product polynomial `zᵢ` at
`x` (`eval`) and `ω x` (`nextEval`), plus — for every set except the last — at `ω^{last} x`
(`lastEval`, hence `Option`). -/
structure PermSetEval (F : Type*) where
  eval : F
  nextEval : F
  lastEval : Option F

/-- Map a permutation set's evaluations along `f` — used to evaluate a polynomial-carrier set at a
point, turning the polynomial-level constraint terms into the verifier's value-level ones. -/
def PermSetEval.map {F G : Type*} (f : F → G) (e : PermSetEval F) : PermSetEval G :=
  { eval := f e.eval, nextEval := f e.nextEval, lastEval := e.lastEval.map f }

/-- Per-lookup evaluations (halo2 lookup `Evaluated`): the product `z` at `x` (`productEval`) and
`ω x` (`productNextEval`); the permuted input `a'` at `x` (`permutedInputEval`) and `ω⁻¹ x`
(`permutedInputInvEval`); and the permuted table `s'` at `x` (`permutedTableEval`). -/
structure LookupEval (F : Type*) where
  productEval : F
  productNextEval : F
  permutedInputEval : F
  permutedInputInvEval : F
  permutedTableEval : F

/-- Map a lookup's evaluations along `f`, as `PermSetEval.map`. -/
def LookupEval.map {F G : Type*} (f : F → G) (e : LookupEval F) : LookupEval G :=
  { productEval := f e.productEval, productNextEval := f e.productNextEval,
    permutedInputEval := f e.permutedInputEval, permutedInputInvEval := f e.permutedInputInvEval,
    permutedTableEval := f e.permutedTableEval }

/-- The proof string, over a field carrier `F` and group carrier `G`, with the fields declared in the
verifier's read order. Group elements are commitments (Vesta points, `E_q`); field elements are
claimed evaluations and the IPA opening scalars.

Per-sub-proof vectors carry an outer `Fin shape.numProofs` (one Orchard proof covers all `N` bundle
actions): `adviceCommitments` (advice column commitments); `lookupPermutedInput`,
`lookupPermutedTable` (lookup permuted commitments); `permutationProduct` (permutation product
commitments); `lookupProduct` (lookup product commitments); `instanceEvals`, `adviceEvals` (instance
and advice evaluations); `permutationSetEvals` (per-set permutation product evaluations); and
`lookupEvals` (lookup evaluations).

Shared across sub-proofs (read once): `vanishingRandom` (vanishing random-poly commitment); `hPieces`
(quotient `h(X)` pieces); `fixedEvals` (fixed evaluations); `vanishingRandomEval` (vanishing random-
poly evaluation); `permutationCommonEvals` (permutation common evaluations); `multiopenQPrime`,
`multiopenU` (the multiopen quotient commitment `q'` — halo2's commitment to the multi-point quotient
polynomial `f(X)` — and the prover's claimed per-point-set quotient evaluations `u`); and the IPA opening
`ipaS`, `ipaRounds`, `ipaC`, `ipaF` (the blinding-poly commitment `S`, the `k` round commitments
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
  /-- The IPA final scalar `c`. Halo2 absorbs it only after the last squeeze, so Lean's omitted
  final absorption does not affect challenge derivation. -/
  ipaC : F
  /-- The IPA final blind `f`; like `ipaC`, Halo2 absorbs it only after the last squeeze. -/
  ipaF : F

end Zcash.Snark

import Mathlib
import Zcash.Snark.Verifier
import Zcash.Snark.ProofString

/-!
# The verifier's opening queries

Before the multiopen compression, the verifier assembles the flat list of opening queries — each a
commitment, the (rotated) point it is opened at, and its claimed evaluation (halo2 `plonk/verifier.rs`
`queries`, together with the per-argument `queries` methods). This module provides one builder per
argument, transcribed from the Rust:

* `columnQueries` — instance / advice / fixed column queries (`plonk/verifier.rs`).
* `permutationQueries` — permutation product queries at `x`, `ω x`, `ω^{last} x` (`permutation/verifier.rs`).
* `lookupQueries` — lookup product / permuted queries at `x`, `ω⁻¹ x`, `ω x` (`lookup/verifier.rs`).
* `permutationCommonQueries` — the common permutation commitments at `x` (`permutation/verifier.rs`).
* `vanishingQueries` — the folded `h` MSM and the random-poly commitment at `x` (`vanishing/verifier.rs`).

The full query list is these concatenated in the verifier's order (per sub-proof: instance, advice,
permutation, lookups; then shared: fixed, permutation-common, vanishing); that concatenation, with the
`ProofString`/VK wiring, is the assembly step. The rotations and column→commitment layout are VK-fixed.
-/

namespace Zcash.Snark

/-- halo2 `domain.rotate_omega(x, Rotation(rot))`: the rotated evaluation point `x · ω^rot`, with `ω`
the domain generator (VK-fixed). Negative rotations use the field's integer power. -/
def rotateOmega {F : Type*} [Field F] (omega x : F) (rot : ℤ) : F := x * omega ^ rot

/-- A lookup argument's three commitments (halo2 `Committed` / `PermutationCommitments`): the product
commitment `z` and the permuted input `a'` and table `s'` commitments. -/
structure LookupCommitments (G : Type*) where
  product : G
  permutedInput : G
  permutedTable : G

/-- Queries for one column family — instance / advice / fixed (halo2 `plonk/verifier.rs`): for each
layout entry `(columnIndex, rotation)` paired with its claimed evaluation, open the column's commitment
at `rotate_omega x rotation`. `commitment` resolves a column index to its commitment; `layout` is the
VK-fixed `(column, rotation)` list, zipped with the read evaluations. -/
def columnQueries {k : ℕ} {F G : Type*} [Field F] (omega x : F) (commitment : ℕ → G)
    (layout : List (ℕ × ℤ)) (evals : List F) : List (VerifierQuery k F G) :=
  (layout.zip evals).map fun e =>
    { point := rotateOmega omega x e.1.2, commitment := .point (commitment e.1.1), eval := e.2 }

/-- Permutation product queries (halo2 `permutation/verifier.rs`): open each set's product commitment
at `x` and `ω x` (`xNext`), and — for every set except the last (`rev().skip(1)`) — at `ω^{last} x`
(`xLast`). `sets` pairs each product commitment with its `PermSetEval`. -/
def permutationQueries {k : ℕ} {F G : Type*} [Field F] (x xNext xLast : F)
    (sets : List (G × PermSetEval F)) : List (VerifierQuery k F G) :=
  (sets.flatMap fun s =>
      [{ point := x, commitment := .point s.1, eval := s.2.eval },
       { point := xNext, commitment := .point s.1, eval := s.2.nextEval }])
    ++ (sets.reverse.drop 1).filterMap fun s =>
      s.2.lastEval.map fun le => { point := xLast, commitment := .point s.1, eval := le }

/-- Lookup queries (halo2 `lookup/verifier.rs`): open the product at `x` and `ω x` (`xNext`), the
permuted input at `x` and `ω⁻¹ x` (`xInv`), and the permuted table at `x`. `lookups` pairs each
lookup's commitments with its `LookupEval`. -/
def lookupQueries {k : ℕ} {F G : Type*} [Field F] (x xInv xNext : F)
    (lookups : List (LookupCommitments G × LookupEval F)) : List (VerifierQuery k F G) :=
  lookups.flatMap fun l =>
    [{ point := x, commitment := .point l.1.product, eval := l.2.productEval },
     { point := x, commitment := .point l.1.permutedInput, eval := l.2.permutedInputEval },
     { point := x, commitment := .point l.1.permutedTable, eval := l.2.permutedTableEval },
     { point := xInv, commitment := .point l.1.permutedInput, eval := l.2.permutedInputInvEval },
     { point := xNext, commitment := .point l.1.product, eval := l.2.productNextEval }]

/-- Common permutation queries (halo2 `permutation/verifier.rs` `CommonEvaluated::queries`): open each
common permutation commitment at `x` to its evaluation. -/
def permutationCommonQueries {k : ℕ} {F G : Type*} [Field F] (x : F)
    (commsEvals : List (G × F)) : List (VerifierQuery k F G) :=
  commsEvals.map fun ce => { point := x, commitment := .point ce.1, eval := ce.2 }

/-- Vanishing argument queries (halo2 `vanishing/verifier.rs`): open the folded `h` commitment (an MSM)
at `x` to `expectedHEval`, and the random-poly commitment at `x` to `randomEval`. -/
def vanishingQueries {k : ℕ} {F G : Type*} [Field F] (x : F) (hCommitment : Msm k F G)
    (expectedHEval : F) (randomPolyCommitment : G) (randomEval : F) : List (VerifierQuery k F G) :=
  [{ point := x, commitment := .msm hCommitment, eval := expectedHEval },
   { point := x, commitment := .point randomPolyCommitment, eval := randomEval }]

end Zcash.Snark

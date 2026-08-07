import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Verifier.Checks
import Zcash.Snark.Core.ProofString

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

open Zcash.Arithmetic (Msm)

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
layout entry `(columnIndex, rotation)` paired with its claimed evaluation, open the column's
commitment at `rotate_omega x rotation`. `commitment` resolves a column index to its commitment;
`layout` is the VK-fixed `(column, rotation)` list. Because `zip` truncates on mismatched lengths,
the derived-key query-count lemmas in `Keygen/Pipeline.lean` prove that `layout` and `evals` agree.
Halo2 enforces the same invariant by reading one evaluation per query. -/
def columnQueries {k : ℕ} {F G : Type*} [Field F] (omega x : F) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F) : List (VerifierQuery k F G) :=
  (layout.zip evals).map fun e =>
    { point := rotateOmega omega x e.1.2, commitment := .point (commitment e.1.1), eval := e.2,
      commId := mkId e.1.1 }

/-- `columnQueries` depends on a commitment family only at columns named by its layout. -/
theorem columnQueries_congr_commitment
    {k : ℕ} {F G : Type*} [Field F]
    (omega x : F) (commitment commitment' : ℕ → G) (mkId : ℕ → CommitmentId)
    (layout : List (ℕ × ℤ)) (evals : List F)
    (h : ∀ column rotation, (column, rotation) ∈ layout →
      commitment column = commitment' column) :
    columnQueries (k := k) omega x commitment mkId layout evals =
      columnQueries omega x commitment' mkId layout evals := by
  unfold columnQueries
  apply List.map_congr_left
  intro entry hentry
  rw [h entry.1.1 entry.1.2 (List.of_mem_zip hentry).1]

/--
The query at an in-range layout/evaluation index occurs in `columnQueries`.

This exposes the exact query, including its claimed evaluation, for soundness
arguments that reconstruct a resolver feed from the assembled opening list.
-/
theorem columnQuery_getD_mem
    {k : ℕ} {F G : Type*} [Field F]
    (omega x : F) (commitment : ℕ → G) (mkId : ℕ → CommitmentId)
    (layout : List (ℕ × ℤ)) (evals : List F) {i : ℕ}
    (hil : i < layout.length) (hie : i < evals.length) :
    { point := rotateOmega omega x (layout.getD i (0, 0)).2,
      commitment := .point (commitment (layout.getD i (0, 0)).1),
      eval := evals.getD i 0,
      commId := mkId (layout.getD i (0, 0)).1 } ∈
        columnQueries (k := k) omega x commitment mkId layout evals := by
  unfold columnQueries
  refine List.mem_map.mpr ⟨(layout[i], evals[i]), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨i, by simp [hil, hie], ?_⟩
    simp
  · simp [hil, hie]

/-- Permutation product queries (halo2 `permutation/verifier.rs`): open each set's product commitment
at `x` and `ω x` (`xNext`), and — for every set except the last (`rev().skip(1)`) — at `ω^{last} x`
(`xLast`). `sets` pairs each product commitment with its `PermSetEval`. -/
def permutationQueries {k : ℕ} {F G : Type*} [Field F] (x xNext xLast : F) (mkId : ℕ → CommitmentId)
    (sets : List (G × PermSetEval F)) : List (VerifierQuery k F G) :=
  let indexed := sets.zip (List.range sets.length)
  (indexed.flatMap fun s =>
      [{ point := x, commitment := .point s.1.1, eval := s.1.2.eval, commId := mkId s.2 },
       { point := xNext, commitment := .point s.1.1, eval := s.1.2.nextEval, commId := mkId s.2 }])
    ++ (indexed.reverse.drop 1).filterMap fun s =>
      s.1.2.lastEval.map fun le =>
        { point := xLast, commitment := .point s.1.1, eval := le, commId := mkId s.2 }

/-- Lookup queries (halo2 `lookup/verifier.rs`): open the product at `x` and `ω x` (`xNext`), the
permuted input at `x` and `ω⁻¹ x` (`xInv`), and the permuted table at `x`. `lookups` pairs each
lookup's commitments with its `LookupEval`. -/
def lookupQueries {k : ℕ} {F G : Type*} [Field F] (x xInv xNext : F)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval F)) : List (VerifierQuery k F G) :=
  (lookups.zip (List.range lookups.length)).flatMap fun l =>
    [{ point := x, commitment := .point l.1.1.product, eval := l.1.2.productEval, commId := mkProduct l.2 },
     { point := x, commitment := .point l.1.1.permutedInput, eval := l.1.2.permutedInputEval,
       commId := mkInput l.2 },
     { point := x, commitment := .point l.1.1.permutedTable, eval := l.1.2.permutedTableEval,
       commId := mkTable l.2 },
     { point := xInv, commitment := .point l.1.1.permutedInput, eval := l.1.2.permutedInputInvEval,
       commId := mkInput l.2 },
     { point := xNext, commitment := .point l.1.1.product, eval := l.1.2.productNextEval,
       commId := mkProduct l.2 }]

/-- Common permutation queries (halo2 `permutation/verifier.rs` `CommonEvaluated::queries`): open each
common permutation commitment at `x` to its evaluation. -/
def permutationCommonQueries {k : ℕ} {F G : Type*} [Field F] (x : F) (mkId : ℕ → CommitmentId)
    (commsEvals : List (G × F)) : List (VerifierQuery k F G) :=
  (commsEvals.zip (List.range commsEvals.length)).map fun ce =>
    { point := x, commitment := .point ce.1.1, eval := ce.1.2, commId := mkId ce.2 }

/-- Vanishing argument queries (halo2 `vanishing/verifier.rs`): open the folded `h` commitment (an MSM)
at `x` to `expectedHEval`, and the random-poly commitment at `x` to `randomEval`. -/
def vanishingQueries {k : ℕ} {F G : Type*} [Field F] (x : F) (hCommitment : Msm k F G)
    (expectedHEval : F) (randomPolyCommitment : G) (randomEval : F) : List (VerifierQuery k F G) :=
  [{ point := x, commitment := .msm hCommitment, eval := expectedHEval, commId := .vanishingH },
   { point := x, commitment := .point randomPolyCommitment, eval := randomEval, commId := .randomPoly }]

end Zcash.Snark

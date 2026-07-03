import Mathlib
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble

/-!
# Binding the multiopen witness to decoded columns

The IPA extractor returns one coefficient vector for the deployed batched multiopen commitment. The gate
check, however, talks about the individual column polynomials. This module records the missing witness
decode layer: if rewinding supplies openings of the same batched commitment at enough distinct batching
challenges, `batch_open_soundV` recovers the individual columns and proves that they open the claimed
commitments and evaluations.

This closes the witness-to-real-columns half of the constraint-side bridge. The separate fact that the
deployed quotient check supplies `hquot` for those decoded columns remains outside this module.

## Scope of the model

This decode layer models a *single-point, rotation-free* multiopen: every column is opened at the one
evaluation vector `b`, batching is one flat challenge-power combination, and the recovered columns feed
gate polynomials with no rotation structure (`Expr.toPoly` has no `X ↦ ωX` composition). The deployed
assembly (`assembleQueries`/`constructIntermediateSets`) is richer on all three axes: queries hit rotated
points `ωⁱ·x`, the collapse is two-level (`x₁` within point sets, then `x₄` across, with components the
multiopen aggregates `qPrime`/`u_j`, not circuit columns), and the gate check lives at `ch.x` while the
final opening is at `x₃`. Discharging `hbatch`/`hquot` against the deployed verifier therefore needs a
generalization of this module — per-column opening points, a nested batch structure, and the `x`-to-`x₃`
quotient transport — not only a rewinding lemma. Until then, the decoded capstones are exercised
faithfully only by single-point, rotation-free instantiations.

To keep the hypotheses satisfiable, the decoded capstones state `hquot`/`hgood` for the *canonical*
decode of the supplied batch (`decodedCols`), not for every family opening the same commitments: the
family set has `≥ 2^k − 2` free dimensions per column at a prime-order curve (only the commitment and one
evaluation are pinned), so quantified over all of it the pair `hquot ∧ hgood` is jointly unsatisfiable —
tweak one gate-read column by a kernel vector vanishing at the opened point and at `x`. For the same
reason they are dischargeable only with `x` the opened point.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Interpret a coefficient vector as the corresponding polynomial. -/
noncomputable def coeffsToPoly {n : ℕ} (a : Fin n → Fp) : Polynomial Fp :=
  ∑ i, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- Evaluating `coeffsToPoly` is the same linear form as committing to the powers evaluation vector. -/
theorem coeffsToPoly_eval {k : ℕ} (a : Fin (2 ^ k) → Fp) (x : Fp) :
    (coeffsToPoly a).eval x = commitGen (evalVector k x) a := by
  rw [coeffsToPoly, Polynomial.eval_finset_sum]
  simp [commitGen, evalVector, smul_eq_mul]

/-- A family of rewound batched openings for one batch of column commitments.

`batched r` is the IPA witness extracted when the batching challenge is `batchChallenge r`; `current_eq`
marks which rewound opening is the current deployed witness. The commitment and value equations are the
premises consumed by `batch_open_soundV`. -/
structure BatchOpeningsForWitness (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (currentWitness : Fin (2 ^ urs.k) → Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  batched : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  current : Fin numColumns
  current_eq : batched current = currentWitness
  commitment :
    ∀ r, commit urs (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j
  value :
    ∀ r, commitGen b (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j

/-- The recovered per-column polynomials and their opening facts. -/
structure DecodedColumnFamily (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (cols : Fin numColumns → Polynomial Fp) where
  coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  commitment : ∀ i, commit urs (coeffs i) = columnCommitments i
  value : ∀ i, commitGen b (coeffs i) = columnEvals i
  polynomial : ∀ i, cols i = coeffsToPoly (coeffs i)

/-- The same decoded columns, tied back to the full family of rewound batched witnesses. -/
structure DecodedColumnFamilyOfBatch {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness)
    (cols : Fin numColumns → Polynomial Fp) where
  decodedColumns : DecodedColumnFamily urs b columnCommitments columnEvals cols
  reconstruct :
    ∀ r, hbatch.batched r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • decodedColumns.coeffs i

/-- The current extracted witness is the current batch-challenge combination of the decoded columns. -/
theorem DecodedColumnFamilyOfBatch.currentWitness_eq {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    {hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness}
    {cols : Fin numColumns → Polynomial Fp} (hdecoded : DecodedColumnFamilyOfBatch hbatch cols) :
    currentWitness
      = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.decodedColumns.coeffs i := by
  calc
    currentWitness = hbatch.batched hbatch.current := hbatch.current_eq.symm
    _ = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.decodedColumns.coeffs i := hdecoded.reconstruct hbatch.current

/-- Right inverse of the Vandermonde inverse: the row functional reconstructing a sample. -/
theorem vandermonde_inv_right {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * (Matrix.vandermonde z)⁻¹ k j)
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : Matrix.vandermonde z * (Matrix.vandermonde z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- Left inverse of the Vandermonde inverse, specialized to the explicit inverse coefficients. -/
theorem vandermonde_inv_left {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, (Matrix.vandermonde z)⁻¹ i k * z k ^ (j : ℕ))
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : (Matrix.vandermonde z)⁻¹ * Matrix.vandermonde z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- The explicit Vandermonde-decoded columns reconstruct each rewound batched witness. -/
theorem batch_open_reconstruct_with_coeffs {m n : ℕ} (z : Fin n → Fp)
    (a : Fin n → (Fin m → Fp)) (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * μ k j)
      = if i = j then 1 else 0)
    (i : Fin n) :
    (∑ j : Fin n, z i ^ (j : ℕ) • (∑ k : Fin n, μ j k • a k)) = a i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Recover the individual column polynomials from rewound batched openings. -/
noncomputable def decodedColumnFamily_of_batch_openings {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G}
    {columnEvals : Fin numColumns → Fp} {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness) :
    Σ cols : Fin numColumns → Polynomial Fp,
      DecodedColumnFamilyOfBatch hbatch cols := by
  have haC :
      ∀ r, commitGen urs.g (hbatch.batched r)
        = ∑ j : Fin numColumns, hbatch.batchChallenge r ^ (j : ℕ) • columnCommitments j := by
    intro r
    rw [← commit_eq_commitGen urs (hbatch.batched r)]
    exact hbatch.commitment r
  let μ : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde hbatch.batchChallenge)⁻¹
  let coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp) :=
    fun i => ∑ r, μ i r • hbatch.batched r
  have hleft :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          μ i k * hbatch.batchChallenge k ^ (j : ℕ))
        = if i = j then 1 else 0 := by
    intro i j
    simpa [μ] using vandermonde_inv_left hbatch.batchChallenge hbatch.challengesDistinct i j
  have hright :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          hbatch.batchChallenge i ^ (k : ℕ) * μ k j)
        = if i = j then 1 else 0 := by
    intro i j
    simpa [μ] using vandermonde_inv_right hbatch.batchChallenge hbatch.challengesDistinct i j
  exact
    ⟨fun i => coeffsToPoly (coeffs i),
      { decodedColumns :=
          { coeffs := coeffs
            commitment := by
              intro i
              rw [commit_eq_commitGen]
              exact batch_open_with_coeffs urs.g columnCommitments hbatch.batchChallenge
                hbatch.batched μ hleft haC i
            value := by
              intro i
              exact batch_open_with_coeffs b columnEvals hbatch.batchChallenge hbatch.batched μ
                hleft hbatch.value i
            polynomial := by
              intro i
              rfl }
        reconstruct := by
          intro r
          exact (batch_open_reconstruct_with_coeffs hbatch.batchChallenge hbatch.batched μ hright r).symm }⟩

/-- The canonical decoded columns of a batch family: the explicit Vandermonde decode of
`decodedColumnFamily_of_batch_openings`, projected out. The decoded capstones state their
`hquot`/`hgood` hypotheses about *this* family — the one their proofs construct — see the module doc's
scope section for why quantifying over every decoded family instead is unsatisfiable. -/
noncomputable def decodedCols {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness) :
    Fin numColumns → Polynomial Fp :=
  (decodedColumnFamily_of_batch_openings hbatch).1

/-- The canonical decode is a decoded-column family for its batch: it opens the claimed
commitments/evaluations and reconstructs every rewound batched witness (hence the current one). -/
noncomputable def decodedCols_spec {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp}
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals currentWitness) :
    DecodedColumnFamilyOfBatch hbatch (decodedCols hbatch) :=
  (decodedColumnFamily_of_batch_openings hbatch).2

namespace DecodedColumnFamily

/-- A decoded column's claimed evaluation is the value of the recovered polynomial at the opened point. -/
theorem eval_eq {urs : URS G} {numColumns : ℕ} {columnCommitments : Fin numColumns → G}
    {columnEvals : Fin numColumns → Fp} {cols : Fin numColumns → Polynomial Fp}
    {x : Fp}
    (hcols : DecodedColumnFamily urs (evalVector urs.k x) columnCommitments columnEvals cols)
    (i : Fin numColumns) :
    (cols i).eval x = columnEvals i := by
  rw [hcols.polynomial i, coeffsToPoly_eval, hcols.value i]

end DecodedColumnFamily

/-- Select a finite family of recovered columns and totalize it for gate-expression evaluation. -/
noncomputable def selectedPolys {numColumns numSelected : ℕ} (cols : Fin numColumns → Polynomial Fp)
    (idx : Fin numSelected → Fin numColumns) : ℕ → Polynomial Fp :=
  finFn fun i : Fin numSelected => cols (idx i)

/-- A witness-indexed decode function that ignores the witness after the columns have been recovered. -/
noncomputable def selectedPolysDecode {k numColumns numSelected : ℕ}
    (cols : Fin numColumns → Polynomial Fp) (idx : Fin numSelected → Fin numColumns) :
    (Fin (2 ^ k) → Fp) → ℕ → Polynomial Fp :=
  fun _ => selectedPolys cols idx

/-- The SNARK relation with the circuit side fed by columns recovered from the same batched opening family
that contains the extracted IPA witness. -/
structure SnarkRelationWithDecodedColumns (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ urs.k) → Fp) (cols : Fin numColumns → Polynomial Fp) where
  opens : IpaRelation urs P b v a
  batchOpenings : BatchOpeningsForWitness urs b columnCommitments columnEvals a
  decodedColumns : DecodedColumnFamilyOfBatch batchOpenings cols
  satisfiesCircuit :
    circuitSatViaGates fixedCols (selectedPolysDecode (k := urs.k) cols adviceIndex)
      (selectedPolysDecode (k := urs.k) cols instanceIndex) y gates hpoly deg a

end Zcash.Snark

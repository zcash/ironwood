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

This closes the witness-to-real-columns half of the constraint-side bridge once the multiopen rewinding has
produced the relevant batch openings. The separate facts that the deployed quotient check supplies `hquot`
for those decoded columns, and that the `x₁`/`x₄` transcript rewinds produce the batch family, remain outside
this module.

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

/-- The exact multiopen-rewinding output the decoded-column capstone consumes, indexed by the accepting
clean IPA transcript `t` it is rewound from.

The index records the intended provenance but is not itself binding — no field constrains `witness` by
`t`. The tie is enforced where the structure is consumed: the decoded capstones extract the transcript's
own witness from `t`'s acceptance and either identify it with `witness` or return the
`HasNontrivialRelation` branch (two distinct openings of the pinned `(P, b, v)` collide on `commit`,
`hasNontrivialRelation_of_two_openings`). It is not a free function from arbitrary mathematical openings
to columns. -/
structure MultiopenRewindBatch (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (t : IpaTreeV Fp G urs.k) where
  witness : Fin (2 ^ urs.k) → Fp
  opens : IpaRelation urs P b v witness
  batchOpenings : BatchOpeningsForWitness urs b columnCommitments columnEvals witness

/-- Terminal form of the multiopen-rewinding output, for capstones whose forking ladder exposes only the
final opened multiopen relation (post unshift/unblind). The `∀`-witness shape costs nothing beyond a
transcript-tied one — all openings of the pinned `(P, b, v)` share the same commitment and value, so a
batch family for one witness transfers to any other by swapping the `current` slot; that claim is
machine-checked (`multiopenRewindForRelation_of_batch`). The whole output is derivable from a family of
accepting rewound IPA transcripts at distinct batching challenges
(`multiopenRewindForRelation_of_acceptedFamily`), so the assumption the terminal capstones carry reduces
to the accept-probability→transcripts step — that rewinding the deployed batching-challenge squeeze
yields such a family — plus the flat-batch scope recorded in the module doc. -/
abbrev MultiopenRewindForRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp) :
    Type _ :=
  ∀ a, IpaRelation urs P b v a →
    BatchOpeningsForWitness urs b columnCommitments columnEvals a

/-- The `∀`-witness transfer, machine-checked: a batch family for one witness of the pinned `(P, b, v)`
yields the terminal `MultiopenRewindForRelation` form. Any other opening of the same statement is
swapped into the `current` slot — the current-slot equations only mention the shared commitment `P` and
value `v`, which every opening satisfies. -/
noncomputable def multiopenRewindForRelation_of_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {w : Fin (2 ^ urs.k) → Fp} (hw : IpaRelation urs P b v w)
    (hb : BatchOpeningsForWitness urs b columnCommitments columnEvals w) :
    MultiopenRewindForRelation urs P b v columnCommitments columnEvals := fun a hrel => by
  classical
  obtain ⟨z, hzinj, batched, cur, hcur, hcomm, hval⟩ := hb
  refine
    { batchChallenge := z
      challengesDistinct := hzinj
      batched := Function.update batched cur a
      current := cur
      current_eq := Function.update_self cur a batched
      commitment := ?_
      value := ?_ }
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · rw [hr, Function.update_self, hrel.1, ← hw.1, ← hcur]
      exact hcomm cur
    · rw [Function.update_of_ne hr]
      exact hcomm r
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · have hia : commitGen b a = innerProduct a b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      have hiw : commitGen b w = innerProduct w b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      rw [hr, Function.update_self, hia, hrel.2, ← hw.2, ← hiw, ← hcur]
      exact hval cur
    · rw [Function.update_of_ne hr]
      exact hval r

/-- A family of accepting clean IPA transcripts at pairwise-distinct batching challenges, each for the
power-form batched statement over shared column commitments/evaluations — the shape rewinding a flat
power batch at its batching challenge produces. `current_P`/`current_v` pin the designated run to the
deployed statement `(P, v)`. -/
structure AcceptedBatchFamily (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G)
    (columnEvals : Fin numColumns → Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  trees : Fin numColumns → IpaTreeV Fp G urs.k
  accepts : ∀ r, IpaAcceptV urs.g b
    (∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j)
    (∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j) (trees r)
  current : Fin numColumns
  current_P : (∑ j : Fin numColumns, batchChallenge current ^ (j : ℕ) • columnCommitments j) = P
  current_v : (∑ j : Fin numColumns, batchChallenge current ^ (j : ℕ) • columnEvals j) = v

/-- Extraction turns an accepted batch family into the terminal rewinding output: `ipa_soundV`
extracts each run's batched witness, the designated run's witness opens the pinned `(P, b, v)`
(`current_P`/`current_v`), and the `∀`-witness form follows by the current-slot swap
(`multiopenRewindForRelation_of_batch`). This derives the terminal capstones' `hbatch` from accepting
rewound transcripts; what remains assumed upstream is the accept-probability→transcripts step for the
deployed batching challenge, plus the flat-batch scope in the module doc. -/
noncomputable def multiopenRewindForRelation_of_acceptedFamily {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    (fam : AcceptedBatchFamily urs P b v columnCommitments columnEvals) :
    MultiopenRewindForRelation urs P b v columnCommitments columnEvals := by
  classical
  choose batched hbC hbe using fun r =>
    ipa_soundV urs.g b _ _ (fam.trees r) (fam.accepts r)
  have hw : IpaRelation urs P b v (batched fam.current) := by
    refine ⟨?_, ?_⟩
    · rw [commit_eq_commitGen, hbC fam.current, fam.current_P]
    · have hib : innerProduct (batched fam.current) b = commitGen b (batched fam.current) := by
        simp [innerProduct, commitGen, smul_eq_mul]
      rw [hib, hbe fam.current, fam.current_v]
  exact multiopenRewindForRelation_of_batch hw
    { batchChallenge := fam.batchChallenge
      challengesDistinct := fam.challengesDistinct
      batched := batched
      current := fam.current
      current_eq := rfl
      commitment := fun r => by rw [commit_eq_commitGen]; exact hbC r
      value := hbe }

/-- Package rewound accepting transcripts at distinct batching challenges into an
`AcceptedBatchFamily`, given the flat power form of the batched statement in the batching challenge.
`P`/`v` are the statement as a function of that challenge — for the deployed verifier,
`fun ξ => deployedCommitment urs hk vk ps {ch with x4 := ξ}` and the matching `multiopenValue`, the
runs `Soundness.Forking.reprogramX4` (via its apply lemmas) identifies with oracle reprogramming — and
`hP`/`hv` are the flat-batch power form, the model boundary the scope section above records. -/
noncomputable def acceptedBatchFamily_of_rewinds {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    (ξ : Fin numColumns → Fp) (hξinj : Function.Injective ξ)
    (P : Fp → G) (v : Fp → Fp)
    (hP : ∀ r, P (ξ r) = ∑ j : Fin numColumns, ξ r ^ (j : ℕ) • columnCommitments j)
    (hv : ∀ r, v (ξ r) = ∑ j : Fin numColumns, ξ r ^ (j : ℕ) • columnEvals j)
    (cur : Fin numColumns)
    (htrees : ∀ r, ∃ t : IpaTreeV Fp G urs.k, IpaAcceptV urs.g b (P (ξ r)) (v (ξ r)) t) :
    AcceptedBatchFamily urs (P (ξ cur)) b (v (ξ cur)) columnCommitments columnEvals := by
  classical
  choose trees htacc using htrees
  exact
    { batchChallenge := ξ
      challengesDistinct := hξinj
      trees := trees
      accepts := fun r => by rw [← hP r, ← hv r]; exact htacc r
      current := cur
      current_P := (hP cur).symm
      current_v := (hv cur).symm }

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

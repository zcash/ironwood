import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# Opened batch and member-decode interfaces

The current AGM route carries every opening in augmented `(g, u, w)` representation. This module
defines the two interface objects consumed by the canonical and Action terminals:

1. `OpenedBatchOpenings` — the batch family: per-run witnesses with declared components, the
   commitment equations in augmented power form `commit(aᵣ) + pUᵣ•u + pWᵣ•w = Σⱼ ξᵣʲ • Cⱼ`
   together with the corresponding evaluation equations.
2. `openedColumnDecode` — the canonical Vandermonde decode, run componentwise: the same inverse
   matrix decodes the witness vectors, the `U`-components, and the `W`-components
   (`vandermonde_decode_map`/`vandermonde_reconstruct_map`, the module-valued decode core).
   Each decoded column opens its aggregate in augmented form and every run's triple is
   reconstructed as its `ξᵣ`-power combination.
3. `OpenedMemberDecode` — one augmented opening for every member commitment in a deployed point
   set, reconstructing the corresponding `x₄` aggregate at the actual `x₁` challenge.

`DeployedAlgebraicDecode.toOpenedBatch` and `.toMemberDecode` construct these interfaces from
explicit AGM coordinate batches. No accept-measure or rewind constructor is exported here.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm.zero)

-- The deployed grouping definitions appear inside index types (`Fin (deployedSetQueries …).length`),
-- so every defeq check on an index invites `whnf` to unfold the whole
-- `constructIntermediateSets (assembleQueries …)` computation. Sealing them keeps those checks
-- syntactic; the proofs below use their equation lemmas, never delta-reduction.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

section Opened

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## The Vandermonde decode core, module-valued

The opened decode inverts the same power system three times — witness vectors, `U`-components,
`W`-components — so the core is stated once over an arbitrary `Fp`-module and instantiated per
component. -/

/-- Vandermonde decode in any `Fp`-module: a family in flat power form over columns `C` is inverted
columnwise by the inverse-matrix combination. -/
theorem vandermonde_decode_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} {C F : Fin n → M} (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0)
    (hF : ∀ r, F r = ∑ j : Fin n, z r ^ (j : ℕ) • C j) (i : Fin n) :
    (∑ r : Fin n, μ i r • F r) = C i := by
  simp only [hF, Finset.smul_sum, _root_.smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Vandermonde reconstruction in any `Fp`-module: the power combination of the decoded columns
returns each family member. -/
theorem vandermonde_reconstruct_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} (F : Fin n → M) (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * μ k j) = if i = j then 1 else 0)
    (i : Fin n) :
    (∑ j : Fin n, z i ^ (j : ℕ) • (∑ k : Fin n, μ j k • F k)) = F i := by
  simp only [Finset.smul_sum, _root_.smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! ## The opened batch family and its canonical decode -/

/-- A family of batched openings carried in augmented `(g, u, w)` representation: run `r`'s
witness `batched r` opens the power batch after removing its declared components, so the commitment
equation reads `commit(batched r) + batchedU r • u + batchedW r • w = Σⱼ ξᵣʲ • Cⱼ`. The current slot
pins the designated run's triple to `(currentWitness, pU, pW)`. -/
structure OpenedBatchOpenings (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (currentWitness : Fin (2 ^ urs.k) → Fp) (pU pW : Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  batched : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  batchedU : Fin numColumns → Fp
  batchedW : Fin numColumns → Fp
  current : Fin numColumns
  current_eq : batched current = currentWitness
  currentU_eq : batchedU current = pU
  currentW_eq : batchedW current = pW
  commitment :
    ∀ r, commit urs (batched r) + batchedU r • urs.u + batchedW r • urs.w
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j
  value :
    ∀ r, commitGen b (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j

/-- The decoded columns of an opened batch: per column, a witness vector plus `U`/`W` components
opening the column commitment in augmented form and the claimed evaluation, with every run's triple
reconstructed as its power combination of the decoded triples. -/
structure OpenedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) where
  coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  uComp : Fin numColumns → Fp
  wComp : Fin numColumns → Fp
  commitment :
    ∀ i, commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w = columnCommitments i
  value : ∀ i, commitGen b (coeffs i) = columnEvals i
  reconstruct :
    ∀ r, hbatch.batched r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • coeffs i
  reconstructU :
    ∀ r, hbatch.batchedU r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • uComp i
  reconstructW :
    ∀ r, hbatch.batchedW r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • wComp i

/-- The canonical decode of an opened batch: the Vandermonde-inverse combination, run componentwise
on the witness vectors and the two declared-component families — the same matrix inverts all three
power systems (`vandermonde_decode_map`, one instance per component). -/
noncomputable def openedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) :
    OpenedColumnDecode hbatch := by
  classical
  set μ : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde hbatch.batchChallenge)⁻¹ with hμdef
  have hleft :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          μ i k * hbatch.batchChallenge k ^ (j : ℕ))
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_left hbatch.batchChallenge hbatch.challengesDistinct i j
  have hright :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          hbatch.batchChallenge i ^ (k : ℕ) * μ k j)
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_right hbatch.batchChallenge hbatch.challengesDistinct i j
  refine
    { coeffs := fun i => ∑ r, μ i r • hbatch.batched r
      uComp := fun i => ∑ r, μ i r • hbatch.batchedU r
      wComp := fun i => ∑ r, μ i r • hbatch.batchedW r
      commitment := ?_
      value := ?_
      reconstruct := fun r =>
        (vandermonde_reconstruct_map hbatch.batched μ hright r).symm
      reconstructU := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedU μ hright r).symm
      reconstructW := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedW μ hright r).symm }
  · -- The three linear pieces collapse to one μ-combination of the per-run augmented equations,
    -- which `vandermonde_decode_map` inverts.
    intro i
    have hlin :
        commit urs (∑ r, μ i r • hbatch.batched r)
            + (∑ r, μ i r • hbatch.batchedU r) • urs.u
            + (∑ r, μ i r • hbatch.batchedW r) • urs.w
          = ∑ r, μ i r • (commit urs (hbatch.batched r) + hbatch.batchedU r • urs.u
              + hbatch.batchedW r • urs.w) := by
      rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [commitGen_smul_left, smul_eq_mul, smul_eq_mul, SemigroupAction.mul_smul, SemigroupAction.mul_smul, smul_add, smul_add,
        commit_eq_commitGen]
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.commitment i
  · intro i
    have hlin : commitGen b (∑ r, μ i r • hbatch.batched r)
        = ∑ r, μ i r • commitGen b (hbatch.batched r) := by
      rw [commitGen_sum]
      exact Finset.sum_congr rfl fun r _ => commitGen_smul_left b _ _
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.value i

/-! ## The opened member-decode interface -/

/-- The decoded member triples for point set `i`: each opens its member commitment — an actual
queried column commitment — in augmented form, and the honest opened `x₄`-decode triple at set
`i`'s batch position is the `ch.x1`-power combination of the decoded triples. The AGM adapters
`DeployedAlgebraicDecode.toMemberDecode` and `deployedSyntheticMemberDecode` produce this object;
the canonical and Action terminals consume it. -/
structure OpenedMemberDecode [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a pU pW)
    (i : ℕ) (hi : i < deployedX4PairCount vk instanceCommitment ps ch) where
  cols : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → (Fin (2 ^ urs.k) → Fp)
  uComp : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Fp
  wComp : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Fp
  commitment : ∀ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
    commit urs (cols m) + uComp m • urs.u + wComp m • urs.w
      = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).1.eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
  reconstruct :
    (openedColumnDecode pbatch).coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length, ch.x1 ^ (m : ℕ) • cols m
  reconstructU :
    (openedColumnDecode pbatch).uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length, ch.x1 ^ (m : ℕ) • uComp m
  reconstructW :
    (openedColumnDecode pbatch).wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
      = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length, ch.x1 ^ (m : ℕ) • wComp m

/-! ## Layout-rotated polynomial feeds -/

open CompPoly.CPolynomial in
/-- **The halo2-faithful gate feed for one column family.** halo2 evaluates a gate on the claimed
evaluation `advice_evals[query_index]` of query `j = (column, rotation)`, opened at
`rotate_omega x rot = ω^rot·x` (`plonk/verifier.rs`). Feeding the gate the decoded column composed
with its layout rotation — `col_j ∘ (ω^rot_j · X)` — makes its value at the gate point `x` equal
`col_j (ω^rot_j·x)`. The rotation `rot_j` is read from the
verifying key's query layout (`(column, rotation)` list), so it is not a free choice. -/
def rotatedFeed {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (col : Fin n → CPoly) : ℕ → CPoly :=
  fun j =>
    if hj : j < n then
      comp (col ⟨j, hj⟩) (C (omega ^ (layout.getD j (0, 0)).2) * X)
    else 0

end Opened

end Zcash.Snark

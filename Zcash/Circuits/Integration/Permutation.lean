import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Snark.Soundness.Canonical.PermutationCoordinates
import Zcash.Circuits.Integration.Assignment
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Zcash.Circuits.Halo2.CopyPermutation
import Zcash.Snark.Soundness.Multiopen.PermutationColumns
import Zcash.Circuits.Halo2.CompiledCopies
import Zcash.Snark.Soundness.Pricing.ChallengePricing

/-! # Circuit-generic keygen permutation semantics

The compiled permutation is restricted to active rows and reindexed into verifier
chunk coordinates. Polynomial permutation constraints then enforce its cycle equalities.
Commitment binding identifies the accepted σ polynomials with that permutation,
yielding compiled copy satisfaction or an executable relation witness.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 Halo2.Layout
open Keygen Halo2.TopLevelCircuit

namespace TopLevelCopy

section Coordinates

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

/-- Resolver-backed circuit permutation chunks have the compiler-derived width. -/
theorem resolverChunkWidth
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (chunk :
      Fin top.permutationSetCount) :
    (ResolverPermutationPairs
        (top.toVerifierKey urs)
        poly proofIndex chunk).length =
      min top.chunkLen
        (top.permutationColumnCount -
          (chunk : ℕ) *
            top.chunkLen) := by
  exact top.resolverPermutationPairs_length
    urs poly proofIndex chunk

/-- The derived chunk family has enough total slots for every circuit
permutation column. -/
theorem permutationChunks_cover
    : top.permutationColumnCount ≤
      top.permutationSetCount * top.chunkLen := by
  have hcover :=
    permutationColumns_length_le_chunks_mul top
  rw [verifierCS_permutationChunks_length] at hcover
  exact hcover

/-- Flatten the compiler-derived circuit chunks to `(row, global column)`. -/
def chunkFlatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    ResolverPermutationCell
        (top.toVerifierKey urs)
        poly proofIndex top.n ≃
      Fin top.n × Fin top.permutationColumnCount :=
  PermutationCoordinates.chunkFlatten
    top.permutationSetCount
    top.permutationColumnCount
    top.chunkLen
    top.n
    (fun chunk =>
      (ResolverPermutationPairs
        (top.toVerifierKey urs)
        poly proofIndex chunk).length)
    (constraintSystem_chunkLen_pos top.constraintSystem)
    (permutationChunks_cover top)
    ((resolverChunkWidth top) pp urs poly proofIndex)

theorem chunkFlatten_apply_column
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (top.toVerifierKey urs) poly proofIndex top.n) :
    (((chunkFlatten top) pp urs poly proofIndex cell).2 : ℕ) =
      (cell.1 : ℕ) * top.chunkLen + (cell.2.2 : ℕ) := by
  simpa only [chunkFlatten] using
    PermutationCoordinates.chunkFlatten_apply_column
      (constraintSystem_chunkLen_pos top.constraintSystem)
      (permutationChunks_cover top)
      ((resolverChunkWidth top) pp urs poly proofIndex) cell

theorem chunkFlatten_symm_apply_row
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : Fin top.n × Fin top.permutationColumnCount) :
    (((chunkFlatten top) pp urs poly proofIndex).symm cell).2.1 = cell.1 := by
  simpa only [chunkFlatten] using
    PermutationCoordinates.chunkFlatten_symm_apply_row
      (constraintSystem_chunkLen_pos top.constraintSystem)
      (permutationChunks_cover top)
      ((resolverChunkWidth top) pp urs poly proofIndex) cell

theorem chunkFlatten_symm_apply_column
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : Fin top.n × Fin top.permutationColumnCount) :
    ((((chunkFlatten top) pp urs poly proofIndex).symm cell).1 : ℕ) *
          top.chunkLen +
        ((((chunkFlatten top) pp urs poly proofIndex).symm cell).2.2 : ℕ) =
      (cell.2 : ℕ) := by
  simpa only [chunkFlatten] using
    PermutationCoordinates.chunkFlatten_symm_apply_column
      (constraintSystem_chunkLen_pos top.constraintSystem)
      (permutationChunks_cover top)
      ((resolverChunkWidth top) pp urs poly proofIndex) cell

/-- The full-domain circuit keygen permutation in resolver chunk coordinates. -/
def fullSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (top.toVerifierKey urs)
        poly proofIndex top.n) :=
  chunkPermutationOfFlat
    ((chunkFlatten top) pp urs poly proofIndex)
    ((Equiv.prodComm
        (Fin top.permutationColumnCount) (Fin top.n)).permCongr
      (top.copyPermutation))

/-- Copy endpoints are active, and flattening preserves rows, so the full-domain
replay preserves the active-row prefix. -/
theorem fullSigma_preservesActive
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (top.toVerifierKey urs)
      poly proofIndex (top.usableRowsAt top.domainExponent)) :
    ((((fullSigma top) pp urs poly proofIndex)
        (widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n cell)).2.1 :
      ℕ) < (top.usableRowsAt top.domainExponent) := by
  let flat : FlatCell top.permutationColumnCount top.n :=
    (Equiv.prodComm (Fin top.permutationColumnCount) (Fin top.n)).symm
      ((chunkFlatten top) pp urs poly proofIndex
        (widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n cell))
  have hflat : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent) := by
    simpa only [flat, Equiv.prodComm_symm, Equiv.prodComm_apply, chunkFlatten,
      PermutationCoordinates.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using cell.2.1.isLt
  have hreplay := (top.copyPermutation_preserves_usableRows) flat hflat
  simpa only [fullSigma, chunkPermutationOfFlat_apply,
    Equiv.permCongr_apply, Equiv.prodComm_apply, chunkFlatten,
    PermutationCoordinates.chunkFlatten_symm_apply_row, flat] using hreplay

/-- Restrict the full circuit keygen replay to the usable-row prefix. -/
def activeSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (top.toVerifierKey urs)
        poly proofIndex (top.usableRowsAt top.domainExponent)) :=
  PermutationCoordinates.restrictActivePerm top.usableRowsAt_domainExponent_le_n
    ((fullSigma top) pp urs poly proofIndex)
    ((fullSigma_preservesActive top) pp urs poly proofIndex)

/-- The active circuit replay is the restriction of its full-domain replay. -/
theorem activeSigma_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (top.toVerifierKey urs)
      poly proofIndex (top.usableRowsAt top.domainExponent)) :
    widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n
        ((activeSigma top) pp urs poly proofIndex cell) =
      (fullSigma top) pp urs poly proofIndex
        (widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n cell) :=
  PermutationCoordinates.restrictActivePerm_widen
    top.usableRowsAt_domainExponent_le_n
    ((fullSigma top) pp urs poly proofIndex)
    ((fullSigma_preservesActive top) pp urs poly proofIndex)
    cell

/-- Re-express an active flat keygen cell in resolver chunk coordinates. -/
def activeChunkCell
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell top.permutationColumnCount top.n)
    (hrow : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    ResolverPermutationCell
      (top.toVerifierKey urs)
      poly proofIndex (top.usableRowsAt top.domainExponent) :=
  let full :=
    ((chunkFlatten top) pp urs poly proofIndex).symm (flat.2, flat.1)
  ⟨full.1,
    ⟨(full.2.1 : ℕ), by
      simpa only [chunkFlatten,
        PermutationCoordinates.chunkFlatten_symm_apply_row] using hrow⟩,
    full.2.2⟩

/-- Widening the active chunk encoding recovers the full inverse flattening. -/
theorem activeChunkCell_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell top.permutationColumnCount top.n)
    (hrow : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n
        ((activeChunkCell top) pp urs poly proofIndex flat hrow) =
      ((chunkFlatten top) pp urs poly proofIndex).symm
        (flat.2, flat.1) := by
  apply PermutationCoordinates.chunkCell_ext <;> rfl

/-- Flattening the resolver encoding of an active flat cell returns `(row,column)`. -/
theorem activeChunkCell_flatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell top.permutationColumnCount top.n)
    (hrow : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    (chunkFlatten top) pp urs poly proofIndex
        (widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n
          ((activeChunkCell top) pp urs poly proofIndex flat hrow)) =
      (flat.2, flat.1) := by
  rw [activeChunkCell_widen, Equiv.apply_symm_apply]

/--
The resolver chunk coordinate obtained from an active flat circuit cell decodes
to the same concrete column as the flat cell's global permutation-column
index.
-/
theorem activeChunkCell_columnAddress
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell top.permutationColumnCount top.n)
    (hrow : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    let cell :=
      (activeChunkCell top) pp urs poly proofIndex flat hrow
    permutationColumnAddress
        (top.toVerifierKey urs)
        ((top.verifierCS.permutationChunks.getD
          cell.1 []).getD cell.2.2 ((.advice 0), 0)).1 =
      ColRef.toAny
        ((top.permutationLayout).getD flat.1 (.advice 0)) := by
  let vk := top.toVerifierKey urs
  let cell :=
    (activeChunkCell top) pp urs poly proofIndex flat hrow
  have hvkChunks :
      vk.permutationChunks =
        top.verifierCS.permutationChunks := by
    simpa only [vk] using
      top.toVerifierKey_permutationChunks urs
  have hchunk :
      (cell.1 : ℕ) < vk.permutationChunks.length := by
    rw [hvkChunks, verifierCS_permutationChunks_length]
    exact cell.1.isLt
  have hcolumn :
      (cell.2.2 : ℕ) <
        (vk.permutationChunks.getD cell.1 []).length := by
    simpa only [cell, vk, ResolverPermutationPairs,
      permutationChunkPairsOfResolver, List.length_map] using
        cell.2.2.isLt
  have hglobal :
      (flat.1 : ℕ) <
        ((top.permutationLayout).map ColRef.toAny).length := by
    simpa only [List.length_map, permutationLayout_length] using flat.1.isLt
  have hcoordinate :
      (cell.1 : ℕ) * vk.chunkLen + (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hflatten :=
      (activeChunkCell_flatten top)
        pp urs poly proofIndex flat hrow
    have hsecond :=
      congrArg (fun coordinate => (coordinate.2 : ℕ)) hflatten
    simpa only [chunkFlatten,
      PermutationCoordinates.chunkFlatten,
      cell, vk, top.toVerifierKey_chunkLen] using hsecond
  have hindex :
      (vk.permutationChunks.take cell.1).flatten.length +
          (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hprefix :
        (vk.permutationChunks.take cell.1).flatten.length =
          (cell.1 : ℕ) * vk.chunkLen := by
      exact top.toVerifierKey_permutationChunks_take_flatten_length
        urs cell.1 hchunk
    rw [hprefix]
    exact hcoordinate
  have hdecoded := List.decodedChunkAddress_eq_sourceColumn
    (fun reference =>
      permutationColumnAddress vk reference.1)
    ((.advice 0), 0)
    (ColRef.toAny (.advice 0))
    vk.permutationChunks
    ((top.permutationLayout).map ColRef.toAny)
    (by
      simpa only [vk, permutationLayout,
        top.toVerifierKey_permutationChunks] using
        topLevelPermutationColumnAddresses_eq top urs)
    cell.1 cell.2.2 flat.1
    hchunk hcolumn hglobal hindex
  have hmap :
      ((top.permutationLayout).map ColRef.toAny).getD flat.1
          (ColRef.toAny (.advice 0)) =
        ColRef.toAny ((top.permutationLayout).getD flat.1 (.advice 0)) :=
    List.getD_map (top.permutationLayout) (.advice 0) ColRef.toAny
  rw [← hvkChunks]
  simpa only [vk, cell] using hdecoded.trans hmap

/--
The circuit flat-cell valuation in the canonical resolver environment is exactly
the verifier-native `chunkRowValue` at its active resolver chunk coordinate.
-/
theorem copyValue_eq_activeChunkRowValue
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell top.permutationColumnCount top.n)
    (hrow : (flat.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    let circuitShape : CircuitShape := top.shape
    let vk : VerifyingKey circuitShape Fp G := top.toVerifierKey urs
    let cell : ResolverPermutationCell
        (shape := circuitShape) (numProofs := pp.numProofs)
        vk poly proofIndex (top.usableRowsAt top.domainExponent) :=
      activeChunkCell top pp urs poly proofIndex flat hrow
    top.permutationValue
        (polynomialEnvironmentOfCommitments vk poly proofIndex (top.usableRowsAt top.domainExponent)) flat =
      chunkRowValue top.omega
        (ResolverPermutationPairs (shape := circuitShape)
          (numProofs := pp.numProofs) vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2 := by
  let vk := top.toVerifierKey urs
  let cell := activeChunkCell top pp urs poly proofIndex flat hrow
  have hchunk : (cell.1 : ℕ) < vk.permutationChunks.length := by
    rw [top.toVerifierKey_permutationChunks_length]
    exact cell.1.isLt
  have hcolumn : (cell.2.2 : ℕ) < (vk.permutationChunks.getD cell.1 []).length := by
    simpa only [ResolverPermutationPairs, permutationChunkPairsOfResolver, List.length_map]
      using cell.2.2.isLt
  have hcoherent := (top.permutationChunkRoutingCoherent urs
    (vk.permutationChunks.getD cell.1 [])
    (by rw [List.getD_eq_getElem _ _ hchunk]; exact List.getElem_mem ..)
    ((vk.permutationChunks.getD cell.1 []).getD cell.2.2 ((.advice 0), 0))
    (by rw [List.getD_eq_getElem _ _ hcolumn]; exact List.getElem_mem ..)).1
  have hread := chunkRowValue_eq_polynomialEnvironment vk poly proofIndex
    (top.usableRowsAt top.domainExponent) cell.1 cell.2.1 cell.2.2 hcolumn
    hcoherent
  have haddress := activeChunkCell_columnAddress top pp urs poly proofIndex flat hrow
  rw [← top.toVerifierKey_permutationChunks urs] at haddress
  have hcellRow : (cell.2.1 : ℕ) = (flat.2 : ℕ) := by
    have h := congrArg (fun coordinate => (coordinate.1 : ℕ))
      (activeChunkCell_flatten top pp urs poly proofIndex flat hrow)
    simpa only [chunkFlatten, PermutationCoordinates.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using h
  rw [haddress, hcellRow] at hread
  simpa only [permutationValue, top.toVerifierKey_omega, ResolverPermutationPairs]
    using hread.symm

/-- Polynomial permutation constraints make values constant along compiled cycles. -/
theorem permutationValues_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    [CircuitFieldSupport top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges top.domainExponent Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (hsat : ConstraintSatisfaction
      (top.constraintModel pp urs ch poly) top.n)
    (hcycle : ResolverPermutationCycle
      (top.toVerifierKey urs)
      poly proofIndex (top.usableRowsAt top.domainExponent))
    (hcycleSigma :
      hcycle.sigma =
        (activeSigma top) pp urs poly proofIndex)
    (hgood : ResolverPermutationGoodChallenges
      (top.toVerifierKey urs)
      ch poly proofIndex (top.usableRowsAt top.domainExponent)) :
    ∀ l r : FlatCell top.permutationColumnCount top.n,
      (l.2 : ℕ) < top.usableRowsAt top.domainExponent →
      (r.2 : ℕ) < top.usableRowsAt top.domainExponent →
      top.copyPermutation.SameCycle l r →
      (top.permutationValue)
          (polynomialEnvironmentOfCommitments
            (top.toVerifierKey urs)
            poly proofIndex (top.usableRowsAt top.domainExponent))
          l =
        (top.permutationValue)
          (polynomialEnvironmentOfCommitments
            (top.toVerifierKey urs)
            poly proofIndex (top.usableRowsAt top.domainExponent))
        r := by
  intro l r hl hr hsame
  have hdom := top.resolverPermutationDomain pp urs ch poly
  have hsatResolver := hsat
  rw [top.constraintModel_eq_constraintModelOfResolver_projections]
    at hsatResolver
  let left :=
    (activeChunkCell top) pp urs poly proofIndex l hl
  let right :=
    (activeChunkCell top) pp urs poly proofIndex r hr
  have hrestrict :
      ∀ cell : ResolverPermutationCell
          (top.toVerifierKey urs) poly proofIndex (top.usableRowsAt top.domainExponent),
        widenPermutationChunkCell top.usableRowsAt_domainExponent_le_n
            (hcycle.sigma cell) =
          chunkPermutationOfFlat
            ((chunkFlatten top) pp urs poly proofIndex)
            ((Equiv.prodComm
              (Fin top.permutationColumnCount)
              (Fin top.n)).permCongr
                (top.copyPermutation))
            (widenPermutationChunkCell
              top.usableRowsAt_domainExponent_le_n cell) := by
    intro cell
    rw [hcycleSigma]
    simpa only [fullSigma] using
      (activeSigma_widen top) pp urs poly proofIndex cell
  have hchunkValues :=
    PermutationCoordinates.chunkRowValue_eq_of_sameCycle
      (numProofs := pp.numProofs)
      (top.toVerifierKey urs) ch poly
      (top.constraintModel pp urs ch poly).l0
      (top.constraintModel pp urs ch poly).lLast
      (top.constraintModel pp urs ch poly).lBlind
      proofIndex hsatResolver hdom hcycle hgood
      top.usableRowsAt_domainExponent_le_n top.copyPermutation
      ((chunkFlatten top) pp urs poly proofIndex)
      hrestrict
      l r hsame left right
      (by
        simpa only [left] using
          (activeChunkCell_flatten top)
            pp urs poly proofIndex l hl)
      (by
        simpa only [right] using
          (activeChunkCell_flatten top)
            pp urs poly proofIndex r hr)
  rw [copyValue_eq_activeChunkRowValue top pp urs poly proofIndex l hl,
    copyValue_eq_activeChunkRowValue top pp urs poly proofIndex r hr]
  simpa only [left, right, top.toVerifierKey_omega] using hchunkValues

end Coordinates

/-!
## Identifying the accepted permutation columns

This module identifies the common-permutation polynomials routed from the
accepted verifier relation with the σ columns generated by circuit keygen. It
then constructs the exact `ResolverPermutationCycle` consumed by the generic
copy semantics, retaining only the shared augmented-commitment relation branch.

All large objects remain in their compiler-native index types. The sole domain
size equality is discharged by the generic size-transport theorem in
`PermutationColumns`.
-/

open Zcash.Arithmetic (derivedUrsGLagrange omegaOf)

open Halo2 CompPoly.CPolynomial
open Keygen

section Cycle

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

omit [Module Fp G] [DecidableEq G] in
theorem permutationRows_eq_chunkRowName
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (chunk : Fin top.permutationSetCount)
    (column : Fin
      (ResolverPermutationPairs
        (top.toVerifierKey urs) poly proofIndex chunk).length)
    (row : Fin top.n) :
    (top.permutationRows
      (((chunkFlatten top) pp urs poly proofIndex
        ⟨chunk, row, column⟩).2 : ℕ)).getD (row : ℕ) 0 =
      chunkRowName
        top.omega
        Zcash.Arithmetic.deltaFp
        top.chunkLen
        (((fullSigma top) pp urs poly proofIndex
          ⟨chunk, row, column⟩).1 : ℕ)
        (((fullSigma top) pp urs poly proofIndex
          ⟨chunk, row, column⟩).2.1 : ℕ)
        (((fullSigma top) pp urs poly proofIndex
          ⟨chunk, row, column⟩).2.2 : ℕ) := by
  let flatten := chunkFlatten top pp urs poly proofIndex
  let cell : FlatCell top.permutationColumnCount top.n :=
    ((flatten ⟨chunk, row, column⟩).2, row)
  have hrow : (flatten ⟨chunk, row, column⟩).1 = row :=
    PermutationCoordinates.chunkFlatten_apply_row _ _ _ _
  rw [top.permutationRows_getD cell, chunkRowName, rowName]
  have himage :
      fullSigma top pp urs poly proofIndex ⟨chunk, row, column⟩ =
        flatten.symm ((top.copyPermutation cell).2, (top.copyPermutation cell).1) := by
    simp only [fullSigma, chunkPermutationOfFlat_apply, Equiv.permCongr_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap, cell, flatten, hrow]
  rw [himage]
  rw [show ((flatten.symm ((top.copyPermutation cell).2,
      (top.copyPermutation cell).1)).2.1 : ℕ) = (top.copyPermutation cell).2.val from
        congrArg Fin.val (chunkFlatten_symm_apply_row top pp urs poly proofIndex _),
    chunkFlatten_symm_apply_column top pp urs poly proofIndex]
  ring

theorem zipIdx_getD_snd
    {α : Type} (xs : List α) (fallback : α)
    (index : ℕ) (hindex : index < xs.length) :
    (xs.zipIdx.getD index (fallback, 0)).2 = index := by
  rw [List.getD_eq_getElem _ _ (by simpa using hindex)]
  simp

omit [Module Fp G] [DecidableEq G] in
theorem chunkCommonIndex
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (chunk : Fin top.permutationSetCount)
    (column : Fin
      (ResolverPermutationPairs
        (top.toVerifierKey urs) poly proofIndex chunk).length) :
    ((top.verifierCS.permutationChunks.getD chunk []).getD
        column ((.advice 0), 0)).2 =
      (chunk : ℕ) * top.chunkLen + (column : ℕ) := by
  have hchunk : (chunk : ℕ) < top.verifierCS.permutationChunks.length := by
    rw [verifierCS_permutationChunks_length]
    exact chunk.isLt
  have hcolumn : (column : ℕ) <
      (top.verifierCS.permutationChunks.getD chunk []).length := by
    simpa only [ResolverPermutationPairs, permutationChunkPairsOfResolver,
      List.length_map, top.toVerifierKey_permutationChunks] using column.isLt
  rw [verifierCS_permutationChunks_getD top chunk column hchunk hcolumn]
  apply zipIdx_getD_snd
  have hwidth := verifierCS_permutationChunks_getD_length top chunk hchunk
  rw [hwidth] at hcolumn
  rw [List.length_map, ← top.permutationColumnCount_eq_permutationColumns_length]
  omega

variable [CircuitFieldSupport top]

def resolverPermutationCycle_or_relation
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.domainExponent Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          urs hk
            (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := instanceCommitment)
        urs hk
          (top.toVerifierKey urs) ps ch batchOpenings i hi}
    {y : Fp} {hpoly : CPoly} {deg : ℕ}
    (relation : CanonicalMemberConstraintRelation
      (shape := top.shape.withProofParams pp)
      urs hk
        (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs)
        y hpoly deg)
    (proofIndex : Fin pp.numProofs) :
    ResolverPermutationCycleWitness
        (top.toVerifierKey urs) relation.polynomial proofIndex
        (top.usableRowsAt top.domainExponent)
        ((activeSigma top) pp urs relation.polynomial proofIndex)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  classical
  have hkDomain : top.domainExponent = urs.k :=
    hk
  have hkUrs : urs.k ≤ 32 := by
    rw [← hkDomain]
    exact Nat.le_of_lt_succ top.domainExponent_lt
  let setup := LagrangePrefixSetup.ofDerived urs hkUrs
  have hcolumns : ∀
      (chunk : Fin top.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs
          (top.toVerifierKey urs) relation.polynomial
          proofIndex chunk).length),
      (ResolverPermutationPairs
        (top.toVerifierKey urs) relation.polynomial
        proofIndex chunk)[column].2 =
          keygenSigmaColumn
            top.omega Arithmetic.deltaFp top.chunkLen
            ((fullSigma top) pp urs relation.polynomial proofIndex)
            chunk column ⊕'
        AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
    intro chunk column
    let vk := top.toVerifierKey urs
    have hcommonIndex :=
      (chunkCommonIndex top) pp urs relation.polynomial proofIndex
        chunk column
    have hcommon :
        (chunk : ℕ) * top.chunkLen + (column : ℕ) <
          top.permutationColumnCount := by
      have hlt :=
        (((chunkFlatten top)
          pp urs relation.polynomial proofIndex
          ⟨chunk, ⟨0, top.n_pos⟩, column⟩).2).isLt
      simpa only [chunkFlatten_apply_column] using hlt
    let common : Fin top.permutationColumnCount :=
      ⟨(chunk : ℕ) * top.chunkLen + (column : ℕ), hcommon⟩
    let shapeCommon : Fin top.permutationColumnCount :=
      common
    have homega :
        vk.omega = omegaOf urs.k := by
      simpa only [vk, top.toVerifierKey_omega, TopLevelCircuit.omega,
        Zcash.Arithmetic.pastaDomain_omega_eq] using congrArg omegaOf hkDomain
    let key := LagrangeCommitmentKey.canonical urs vk.omega
    have hcommit :
        vk.permutationCommonCommitment shapeCommon =
          key.commitInstance
            (top.permutationRows common) 1 := by
      simp only [vk]
      rw [top.toVerifierKey_permutationCommonCommitment]
      have source :=
        top.permutationCommitments_getD_eq_commitInstance
          urs hkDomain setup.length_eq setup.generator_eq common
          common.isLt
      rw [LagrangeCommitmentKey.commitInstance_eq] at source ⊢
      simpa only [← homega] using source
    have hj :
        (column : ℕ) <
          (vk.permutationChunks.getD chunk []).length := by
      simpa only [vk, ResolverPermutationPairs,
        permutationChunkPairsOfResolver, List.length_map] using
          column.isLt
    have hval :
        ∀ i : Fin top.n,
          (top.permutationRows common).getD (i : ℕ) 0 =
            chunkRowName vk.omega vk.delta vk.chunkLen
              ((fullSigma top)
                pp urs relation.polynomial proofIndex
                ⟨chunk, i, column⟩).1
              ((fullSigma top)
                pp urs relation.polynomial proofIndex
                ⟨chunk, i, column⟩).2.1
              ((fullSigma top)
                pp urs relation.polynomial proofIndex
                ⟨chunk, i, column⟩).2.2 := by
      intro i
      have source :=
        (permutationRows_eq_chunkRowName top)
          pp urs relation.polynomial proofIndex chunk column i
      have hcommonRow :
          (common : ℕ) =
            (((chunkFlatten top)
              pp urs relation.polynomial proofIndex
              ⟨chunk, i, column⟩).2 : ℕ) := by
        simp only [common,
          chunkFlatten_apply_column]
      rw [hcommonRow]
      simpa only [vk,
        top.toVerifierKey_omega,
        top.toVerifierKey_delta,
        top.toVerifierKey_chunkLen] using source
    have hidx :
        ((vk.permutationChunks.getD chunk [])[column]).2 =
          (shapeCommon : ℕ) := by
      calc
        ((vk.permutationChunks.getD chunk [])[column]).2 =
            ((vk.permutationChunks.getD chunk []).getD
              column ((.advice 0), 0)).2 :=
          congrArg Prod.snd (List.getD_eq_getElem _ _ hj).symm
        _ = ((top.verifierCS.permutationChunks.getD chunk []).getD
              column ((.advice 0), 0)).2 := by
          simp only [vk, top.toVerifierKey_permutationChunks]
        _ = (chunk : ℕ) * top.chunkLen + (column : ℕ) :=
          hcommonIndex
        _ = (common : ℕ) := (Fin.val_mk hcommon).symm
        _ = (shapeCommon : ℕ) := by
          simp only [shapeCommon]
    have hidentified :=
      relation.resolverPermutationPairs_snd_eq_keygenSigmaColumn_or_relation_of_size
        proofIndex chunk column hj shapeCommon hidx key
        (top.permutationRows common)
        hcommit (by simpa only [top.toVerifierKey_omega] using top.domainRowsInjective_of_domainExponent_eq hk)
        (by
          simpa only [top.n_eq_two_pow_domainExponent] using
            congrArg (2 ^ ·) hkDomain)
        ((fullSigma top)
          pp urs relation.polynomial proofIndex)
        chunk column hval
    simpa only [top.toVerifierKey_omega,
      top.toVerifierKey_delta,
      top.toVerifierKey_chunkLen] using hidentified
  -- The successful cycle is returned as data; only its sigma equality is proof-valued.
  exact bindOrRelationWitness
    (finForallOrRelationWitness fun chunk =>
      finForallOrRelationWitness fun column => hcolumns chunk column)
    (fun hcolumns =>
      ⟨top.resolverPermutationCycleOfKeygenColumns urs relation.polynomial proofIndex
        top.usableRowsAt_domainExponent_le_n
        ((fullSigma top)
          pp urs relation.polynomial proofIndex)
        ((activeSigma top)
          pp urs relation.polynomial proofIndex)
        hcolumns
        ((activeSigma_widen top)
          pp urs relation.polynomial proofIndex),
        rfl⟩)

end Cycle

end TopLevelCopy

/-! ## Compiled copy equality from the verifier permutation argument

Commitment binding identifies the generated σ cycle. The permutation argument then
gives equal values on every resolved compiler copy pair.
-/

open Halo2 CompPoly.CPolynomial
open TopLevelCopy

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top] [CircuitFieldSupport top]

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/-- Recover compiled copy equality, or an augmented-commitment relation. -/
def CanonicalMemberConstraintRelation.copiesCompiled_or_relation
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.domainExponent Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          urs hk (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := instanceCommitment)
        urs hk (top.toVerifierKey urs) ps ch batchOpenings i hi}
    {y : Fp} {hpoly : CPoly}
    (relation : CanonicalMemberConstraintRelation
      (shape := top.shape.withProofParams pp)
      urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs)
        y hpoly top.n)
    (satisfaction : ConstraintSatisfaction
      (top.constraintModel pp urs ch relation.polynomial) top.n)
    (exclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (top.toVerifierKey urs) ch relation.polynomial (top.usableRowsAt top.domainExponent))
    (proofIndex : Fin pp.numProofs)
    (hencoding : top.FixedColumnEncoding relation.polynomial) :
    top.CopiesCompiled (polynomialAssignment top.omega relation.polynomial proofIndex) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  rcases resolverPermutationCycle_or_relation top pp urs hk relation proofIndex with hcycle | hbad
  · have hvalues := permutationValues_of_constraintSatisfaction top
        pp urs ch relation.polynomial
        proofIndex satisfaction hcycle.cycle hcycle.sigma_eq
        (exclusions.good proofIndex)
    rw [top.polynomialEnvironmentOfCommitments_eq_environment
      urs relation.polynomial proofIndex hencoding] at hvalues
    exact PSum.inl (top.copiesCompiled_of_permutation _ hvalues)
  · exact PSum.inr hbad

end Zcash.Snark

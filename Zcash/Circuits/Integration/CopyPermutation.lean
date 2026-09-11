import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Snark.Soundness.Canonical.PermutationCoordinates
import Zcash.Circuits.Integration.AssignmentEncoding
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Zcash.Circuits.Halo2.CopyPermutation

/-! # Circuit-generic keygen permutation semantics

The compiled permutation is restricted to active rows and reindexed into verifier
chunk coordinates. Polynomial permutation constraints then enforce its cycle equalities.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 Halo2.Layout
open Keygen Halo2.TopLevelCircuit

namespace TopLevelCopy

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
  have hdecoded := decodedChunkAddress_eq_sourceColumn
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
    let vk : VerifyingKey circuitShape Fp G :=
      top.toVerifierKey urs
    let cell : ResolverPermutationCell
        (shape := circuitShape) (numProofs := pp.numProofs)
        vk poly proofIndex (top.usableRowsAt top.domainExponent) :=
      (activeChunkCell top) pp urs poly proofIndex flat hrow
    (top.permutationValue)
        (resolverEnvironment vk poly proofIndex (top.usableRowsAt top.domainExponent)) flat =
      chunkRowValue top.omega
        (ResolverPermutationPairs (shape := circuitShape)
          (numProofs := pp.numProofs) vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2 := by
  let circuitShape : CircuitShape := top.shape
  let vk : VerifyingKey circuitShape Fp G :=
    top.toVerifierKey urs
  let cell : ResolverPermutationCell
      (shape := circuitShape) (numProofs := pp.numProofs)
      vk poly proofIndex (top.usableRowsAt top.domainExponent) :=
    (activeChunkCell top) pp urs poly proofIndex flat hrow
  simp only
  let chunk : ℕ := cell.1
  let row : ℕ := cell.2.1
  let column : ℕ := cell.2.2
  have hvkChunks :
      vk.permutationChunks =
        top.verifierCS.permutationChunks := by
    simpa only [vk] using
      top.toVerifierKey_permutationChunks urs
  have hchunk :
      chunk < vk.permutationChunks.length := by
    rw [hvkChunks, verifierCS_permutationChunks_length]
    simpa only [chunk, circuitShape] using cell.1.isLt
  have hcolumn :
      column <
        (vk.permutationChunks.getD chunk []).length := by
    simpa only [column, chunk, cell, vk, ResolverPermutationPairs,
      permutationChunkPairsOfResolver, List.length_map] using
        cell.2.2.isLt
  have hchunkMem :
      vk.permutationChunks.getD chunk [] ∈
        vk.permutationChunks := by
    rw [List.getD_eq_getElem _ _ hchunk]
    exact List.getElem_mem ..
  have hreferenceMem :
      (vk.permutationChunks.getD chunk []).getD
          column ((.advice 0), 0) ∈
        vk.permutationChunks.getD chunk [] := by
    rw [List.getD_eq_getElem _ _ hcolumn]
    exact List.getElem_mem ..
  have hcoherent :
      PermutationColumnRef.Coherent vk
        ((vk.permutationChunks.getD chunk []).getD
          column ((.advice 0), 0)).1 :=
    (top.permutationChunkRoutingCoherent urs
      _ hchunkMem _ hreferenceMem).1
  generalize hreference :
    ((vk.permutationChunks.getD chunk []).getD
      column ((.advice 0), 0)).1 = reference at hcoherent
  have hcolumnReference :
      (vk.permutationChunks.getD chunk [])[column].1 = reference := by
    calc
      (vk.permutationChunks.getD chunk [])[column].1 =
          ((vk.permutationChunks.getD chunk []).getD
            column ((.advice 0), 0)).1 :=
        congrArg Prod.fst (List.getD_eq_getElem _ _ hcolumn).symm
      _ = reference := hreference
  have hresolver :
      chunkRowValue vk.omega
          (permutationChunkPairsOfResolver vk poly proofIndex)
          chunk row column =
        (resolverEnvironment vk poly proofIndex (top.usableRowsAt top.domainExponent)).get
          (permutationColumnAddress vk reference)
          (row : ℤ) := by
    rw [chunkRowValue, rowValue]
    have hpairs :
        column <
          (permutationChunkPairsOfResolver
            vk poly proofIndex chunk).length := by
      simpa only [permutationChunkPairsOfResolver,
        List.length_map] using hcolumn
    rw [List.getD_eq_getElem _ _ hpairs]
    simp only [permutationChunkPairsOfResolver, List.getElem_map]
    rw [hcolumnReference]
    apply permutationColumnPolynomial_eval_environment
    assumption
  rw [← hcolumnReference] at hresolver
  have haddressRaw :=
    (activeChunkCell_columnAddress top)
      pp urs poly proofIndex flat hrow
  simp only at haddressRaw
  rw [← hvkChunks] at haddressRaw
  have haddress :
      permutationColumnAddress vk
          ((vk.permutationChunks.getD chunk []).getD
            column ((.advice 0), 0)).1 =
        ColRef.toAny ((top.permutationLayout).getD flat.1 (.advice 0)) := by
    simpa only [chunk, column] using haddressRaw
  rw [List.getD_eq_getElem _ _ hcolumn] at haddress
  have hcellRow : row = (flat.2 : ℕ) := by
    have hflatten :=
      (activeChunkCell_flatten top)
        pp urs poly proofIndex flat hrow
    have hfirst :=
      congrArg (fun coordinate => (coordinate.1 : ℕ)) hflatten
    simpa only [chunkFlatten,
      PermutationCoordinates.chunkFlatten_apply_row,
      widenPermutationChunkCell_row, row, cell] using hfirst
  rw [haddress, hcellRow] at hresolver
  simpa only [permutationValue, vk, top.toVerifierKey_omega, ResolverPermutationPairs,
    chunk, row, column] using hresolver.symm

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
          (resolverEnvironment
            (top.toVerifierKey urs)
            poly proofIndex (top.usableRowsAt top.domainExponent))
          l =
        (top.permutationValue)
          (resolverEnvironment
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
  calc
    (top.permutationValue)
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex (top.usableRowsAt top.domainExponent))
        l =
      chunkRowValue top.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (top.toVerifierKey urs) poly proofIndex)
        left.1 left.2.1 left.2.2 := by
          simpa only [left] using
            (copyValue_eq_activeChunkRowValue top)
              pp urs poly proofIndex l hl
    _ = chunkRowValue top.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (top.toVerifierKey urs) poly proofIndex)
        right.1 right.2.1 right.2.2 := by
          simpa only [top.toVerifierKey_omega] using hchunkValues
    _ = (top.permutationValue)
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex (top.usableRowsAt top.domainExponent))
        r := by
          symm
          simpa only [right] using
            (copyValue_eq_activeChunkRowValue top)
              pp urs poly proofIndex r hr

end TopLevelCopy

end Zcash.Snark

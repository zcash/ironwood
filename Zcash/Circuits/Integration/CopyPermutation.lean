import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Zcash.Circuits.Integration.CopyListMembership

/-! # Circuit-generic keygen permutation semantics

The compiler's bounded copy pairs are replayed over the full domain, then
restricted to active rows and reindexed into verifier chunk coordinates.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 Halo2.Layout
open Keygen

namespace TopLevelCopy

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

/-- Compiler permutation columns in verifying-key order. -/
def columns : List ColRef :=
  permColsOf top.constraintSystem

/-- The copy compiler and the published shape use the same column count. -/
theorem columns_length : (columns top).length = top.permutationColumnCount := by
  rw [top.permutationColumnCount_eq_permutationColumns_length]
  simp only [columns, Keygen.permColsOf, List.length_map, TopLevelCircuit.permutationColumns]

/-- The V1 constants allocation of the circuit operation stream. -/
def constants : List (ℕ × ℕ × ℕ) :=
  constantCopyEntries top.constraintSystem
    (top.operations)

omit [TopLevelShape top] in
/-- V1 allocates at least one fixed cell for every circuit constant site. -/
theorem constantSites_fit :
    (operationConstSites
        (top.operations)).length ≤
      (constants top).length := by
  rw [constants, Keygen.constantCopyEntries, List.length_map,
    operationConstSites_length]
  exact top.constantValues_length_le_constantAssignments_length

/-- The keygen copy list of the circuit operation stream. -/
def rawPairs : List (ℕ × ℕ × ℕ × ℕ) :=
  Halo2.Layout.V1.copyList (columns top)
    top.regionStarts
    (top.operations) (constants top)

theorem usedRows_le_domainSize :
    Halo2.usedRows top.operations ≤ top.n :=
  top.operations_usedRows_le_usedRows.trans
    (top.usedRows_le_usableRowsAt_domainExponent.trans
      top.usableRowsAt_domainExponent_le_n)

omit [TopLevelShape top] in
/-- Every circuit constants allocation uses an equality-enabled configured constants
column. -/
theorem const_column_mem_permutationColumns
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ (constants top)) :
    (AnyColumn.mk .fixed entry.2.1) ∈
      top.constraintSystem.permutationColumns := by
  rw [constants, Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact top.constantAssignmentColumn_mem_permutationColumns
    hassignment

/-- Every keygen copy tuple names two circuit permutation columns. Row bounds are
proved generically from the compiler below. -/
theorem copyColumnBounds : ∀ t ∈ (rawPairs top),
    t.1 < top.permutationColumnCount ∧ t.2.2.1 < top.permutationColumnCount := by
  intro tuple htuple
  rw [← columns_length top]
  apply V1_copyList_columns_lt top.constraintSystem
    top.operations top.keygenCoherent
    top.regionStarts (constants top) (constantSites_fit top)
    (const_column_mem_permutationColumns top) tuple
  simpa only [rawPairs, columns] using htuple

omit [TopLevelShape top] in
/-- Every V1 circuit constant allocation lies below the compiler-derived operation
footprint. -/
theorem const_row_lt_usedRows
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ (constants top)) :
    entry.2.2 < Halo2.usedRows top.operations := by
  rw [constants, Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact V1_constantAssignments_row_lt_usedRows
    top.operations
    (top.constraintSystem.constants.map (·.index))
    hassignment

omit [TopLevelShape top] in
/-- Every raw circuit keygen copy endpoint lies below the compiler-derived operation
footprint. -/
theorem copyRaw_rows_lt_usedRows
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ (rawPairs top)) :
    tuple.2.1 < Halo2.usedRows top.operations ∧
      tuple.2.2.2 < Halo2.usedRows top.operations := by
  apply V1_copyList_rows_lt_usedRows top.operations
    (columns top) (constants top) (constantSites_fit top)
    (const_row_lt_usedRows top) tuple
  simpa only [rawPairs, TopLevelCircuit.regionStarts,
    TopLevelCompilation.regionStarts] using htuple

/-- Registration and the compiler footprint bound both coordinates of each copy. -/
theorem copyBounds : ∀ t ∈ (rawPairs top), t.1 < top.permutationColumnCount ∧
    t.2.1 < top.n ∧ t.2.2.1 < top.permutationColumnCount ∧
    t.2.2.2 < top.n := by
  intro tuple htuple
  have hcolumns := (copyColumnBounds top) tuple htuple
  have hrows := (copyRaw_rows_lt_usedRows top) tuple htuple
  exact ⟨hcolumns.1, hrows.1.trans_le (usedRows_le_domainSize top),
    hcolumns.2, hrows.2.trans_le (usedRows_le_domainSize top)⟩

/-- The decoded circuit copy list. -/
def pairs :
    List (FlatCell top.permutationColumnCount top.n ×
      FlatCell top.permutationColumnCount top.n) :=
  decodeCopies top.permutationColumnCount top.n (rawPairs top) (copyBounds top)

/-- Every decoded copy pair lies in the compiler-derived usable-row prefix. -/
theorem copyRowsActive
    (pair : FlatCell top.permutationColumnCount top.n ×
      FlatCell top.permutationColumnCount top.n)
    (hpair : pair ∈ (pairs top)) :
    (pair.1.2 : ℕ) < (top.usableRowsAt top.domainExponent) ∧
      (pair.2.2 : ℕ) < (top.usableRowsAt top.domainExponent) := by
  have hrawMap := decodeCopies_map top.permutationColumnCount top.n
    (rawPairs top) (copyBounds top)
  have hraw :
      (pair.1.pair.1, pair.1.pair.2,
        pair.2.pair.1, pair.2.pair.2) ∈ (rawPairs top) := by
    rw [← hrawMap]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  have hrows := (copyRaw_rows_lt_usedRows top) _ hraw
  have husedRows :
      Halo2.usedRows top.operations ≤ (top.usableRowsAt top.domainExponent) :=
    top.operations_usedRows_le_usedRows.trans
      top.usedRows_le_usableRowsAt_domainExponent
  exact ⟨hrows.1.trans_le husedRows, hrows.2.trans_le husedRows⟩

/-- Circuit keygen replays preserve the usable-row prefix. -/
theorem replayPreservesActive
    (cell : FlatCell top.permutationColumnCount top.n)
    (hcell : (cell.2 : ℕ) < (top.usableRowsAt top.domainExponent)) :
    ((replayKeygenPermutation (pairs top) cell).2 : ℕ) <
      (top.usableRowsAt top.domainExponent) := by
  apply replayKeygenPermutation_preserves (pairs top)
    (fun candidate => (candidate.2 : ℕ) < (top.usableRowsAt top.domainExponent))
  · intro pair hpair
    exact (copyRowsActive top) pair hpair
  · exact hcell

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
  Layout.Asm.chunkFlatten
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
    Layout.Asm.chunkFlatten_apply_column
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
    Layout.Asm.chunkFlatten_symm_apply_row
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
    Layout.Asm.chunkFlatten_symm_apply_column
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
      (replayKeygenPermutation (pairs top)))

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
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using cell.2.1.isLt
  have hreplay := (replayPreservesActive top) flat hflat
  simpa only [fullSigma, chunkPermutationOfFlat_apply,
    Equiv.permCongr_apply, Equiv.prodComm_apply, chunkFlatten,
    _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row, flat] using hreplay

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
  Layout.Asm.restrictActivePerm top.usableRowsAt_domainExponent_le_n
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
  Layout.Asm.restrictActivePerm_widen
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
        _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row] using hrow⟩,
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
  apply _root_.Zcash.Snark.Layout.Asm.chunkCell_ext <;> rfl

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

/-- The circuit cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def value (env : Environment Fp)
    (fc : FlatCell top.permutationColumnCount top.n) : Fp :=
  env.get (ColRef.toAny ((columns top).getD (fc.1 : ℕ) (.advice 0)))
    (((fc.2 : ℕ) : ℕ) : ℤ)

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
        ((columns top).getD flat.1 (.advice 0)) := by
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
        ((columns top).map ColRef.toAny).length := by
    simpa only [List.length_map, columns_length] using flat.1.isLt
  have hcoordinate :
      (cell.1 : ℕ) * vk.chunkLen + (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hflatten :=
      (activeChunkCell_flatten top)
        pp urs poly proofIndex flat hrow
    have hsecond :=
      congrArg (fun coordinate => (coordinate.2 : ℕ)) hflatten
    simpa only [chunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten,
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
    ((columns top).map ColRef.toAny)
    (by
      simpa only [vk, columns,
        top.toVerifierKey_permutationChunks] using
        topLevelPermutationColumnAddresses_eq top urs)
    cell.1 cell.2.2 flat.1
    hchunk hcolumn hglobal hindex
  have hmap :
      ((columns top).map ColRef.toAny).getD flat.1
          (ColRef.toAny (.advice 0)) =
        ColRef.toAny ((columns top).getD flat.1 (.advice 0)) :=
    List.getD_map (columns top) (.advice 0) ColRef.toAny
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
    (value top)
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
        ColRef.toAny ((columns top).getD flat.1 (.advice 0)) := by
    simpa only [chunk, column] using haddressRaw
  rw [List.getD_eq_getElem _ _ hcolumn] at haddress
  have hcellRow : row = (flat.2 : ℕ) := by
    have hflatten :=
      (activeChunkCell_flatten top)
        pp urs poly proofIndex flat hrow
    have hfirst :=
      congrArg (fun coordinate => (coordinate.1 : ℕ)) hflatten
    simpa only [chunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row, row, cell] using hfirst
  rw [haddress, hcellRow] at hresolver
  simpa only [value, vk, top.toVerifierKey_omega, ResolverPermutationPairs,
    chunk, row, column] using hresolver.symm

/--
Every decoded circuit keygen-copy pair has equal values in the canonical
resolver environment once the generic permutation premises hold.

`hcycleSigma` records the construction provenance intentionally omitted from
the abstract `ResolverPermutationCycle`: the cycle is the circuit active replay.
-/
theorem copyPairValue_of_resolverPermutation
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges top.domainExponent Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    {n : ℕ}
    (hsat : ConstraintSatisfaction
      (top.constraintModel pp urs ch poly) n)
    (hdom : ResolverPermutationDomain
      (top.toVerifierKey urs)
      (top.constraintModel pp urs ch poly).l0
      (top.constraintModel pp urs ch poly).lLast
      (top.constraintModel pp urs ch poly).lBlind
      n (top.usableRowsAt top.domainExponent))
    (hcycle : ResolverPermutationCycle
      (top.toVerifierKey urs)
      poly proofIndex (top.usableRowsAt top.domainExponent))
    (hcycleSigma :
      hcycle.sigma =
        (activeSigma top) pp urs poly proofIndex)
    (hgood : ResolverPermutationGoodChallenges
      (top.toVerifierKey urs)
      ch poly proofIndex (top.usableRowsAt top.domainExponent)) :
    ∀ pair ∈ (pairs top),
      (value top)
          (resolverEnvironment
            (top.toVerifierKey urs)
            poly proofIndex (top.usableRowsAt top.domainExponent))
          pair.1 =
        (value top)
          (resolverEnvironment
            (top.toVerifierKey urs)
            poly proofIndex (top.usableRowsAt top.domainExponent))
        pair.2 := by
  intro pair hpair
  have hsatResolver := hsat
  rw [top.constraintModel_eq_constraintModelOfResolver_projections]
    at hsatResolver
  have hrows := (copyRowsActive top) pair hpair
  let left :=
    (activeChunkCell top) pp urs poly proofIndex pair.1 hrows.1
  let right :=
    (activeChunkCell top) pp urs poly proofIndex pair.2 hrows.2
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
                (replayKeygenPermutation (pairs top)))
            (widenPermutationChunkCell
              top.usableRowsAt_domainExponent_le_n cell) := by
    intro cell
    rw [hcycleSigma]
    simpa only [fullSigma] using
      (activeSigma_widen top) pp urs poly proofIndex cell
  have hchunkValues :=
    Layout.Asm.chunkRowValue_eq_of_mem_copies
      (numProofs := pp.numProofs)
      (top.toVerifierKey urs) ch poly
      (top.constraintModel pp urs ch poly).l0
      (top.constraintModel pp urs ch poly).lLast
      (top.constraintModel pp urs ch poly).lBlind
      proofIndex hsatResolver hdom hcycle hgood
      top.usableRowsAt_domainExponent_le_n (pairs top)
      ((chunkFlatten top) pp urs poly proofIndex)
      hrestrict
      pair.1 pair.2 hpair left right
      (by
        simpa only [left] using
          (activeChunkCell_flatten top)
            pp urs poly proofIndex pair.1 hrows.1)
      (by
        simpa only [right] using
          (activeChunkCell_flatten top)
            pp urs poly proofIndex pair.2 hrows.2)
  calc
    (value top)
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex (top.usableRowsAt top.domainExponent))
        pair.1 =
      chunkRowValue top.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (top.toVerifierKey urs) poly proofIndex)
        left.1 left.2.1 left.2.2 := by
          simpa only [left] using
            (copyValue_eq_activeChunkRowValue top)
              pp urs poly proofIndex pair.1 hrows.1
    _ = chunkRowValue top.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (top.toVerifierKey urs) poly proofIndex)
        right.1 right.2.1 right.2.2 := by
          simpa only [top.toVerifierKey_omega] using hchunkValues
    _ = (value top)
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex (top.usableRowsAt top.domainExponent))
        pair.2 := by
          symm
          simpa only [right] using
            (copyValue_eq_activeChunkRowValue top)
              pp urs poly proofIndex pair.2 hrows.2

/-- Decode membership in the raw circuit copy list to a typed copy pair. -/
theorem exists_pair_of_raw
    {tuple : ℕ × ℕ × ℕ × ℕ} (hraw : tuple ∈ (rawPairs top)) :
    ∃ pair ∈ (pairs top),
      pair.1.pair = (tuple.1, tuple.2.1) ∧
        pair.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
  have hrawMap :
      (rawPairs top) = (pairs top).map
        (fun pair =>
          (pair.1.pair.1, pair.1.pair.2,
            pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map top.permutationColumnCount top.n
      (rawPairs top) (copyBounds top)).symm
  rw [hrawMap, List.mem_map] at hraw
  obtain ⟨pair, hpair, htuple⟩ := hraw
  refine ⟨pair, hpair, ?_, ?_⟩
  · rw [← htuple]
  · rw [← htuple]


end TopLevelCopy

end Zcash.Snark

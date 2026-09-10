import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Circuits.Integration.CopyListMembership

/-! # Action keygen permutation semantics

The compiler's bounded copy pairs are replayed over the full domain, then
restricted to active rows and reindexed into verifier chunk coordinates.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 Halo2.Layout Zcash.Circuits Zcash.Circuits.Action
open Keygen

set_option maxRecDepth 100000

/-- Action's permutation columns, in verifying-key order. -/
def actionPermCols : List ColRef :=
  permColsOf actionCircuit.constraintSystem

/-- The permutation-column count (15 for the deployed Action circuit). -/
def actionNumPermCols : ℕ := actionPermCols.length

/-- The evaluation-domain size at the derived exponent. -/
def actionDomainSize : ℕ := actionCircuit.n

/-- The V1 constants allocation of the Action operation stream. -/
def actionConsts : List (ℕ × ℕ × ℕ) :=
  constantCopyEntries actionCircuit.constraintSystem
    (actionCircuit.operations)

/-- V1 allocates at least one fixed cell for every Action constant site. -/
theorem actionConstantSites_fit :
    (operationConstSites
        (actionCircuit.operations)).length ≤
      actionConsts.length := by
  rw [actionConsts, Keygen.constantCopyEntries, List.length_map,
    operationConstSites_length]
  exact actionCircuit.constantValues_length_le_constantAssignments_length

/-- The keygen copy list of the Action operation stream. -/
def actionCopyRaw : List (ℕ × ℕ × ℕ × ℕ) :=
  Halo2.Layout.V1.copyList actionPermCols
    actionCircuit.regionStarts
    (actionCircuit.operations) actionConsts

/-- The last usable row of the circuit-derived Action domain. -/
def actionActiveRows : ℕ :=
  actionCircuit.usableRowsAt
    actionCircuit.domainExponent

@[simp]
theorem actionActiveRows_eq :
    actionActiveRows =
      actionCircuit.n - actionCircuit.blindingFactors - 1 := by
  simpa only [actionActiveRows] using
    actionCircuit.usableRowsAt_domainExponent

theorem actionDomainSize_pos : 0 < actionDomainSize :=
  Nat.two_pow_pos _

theorem actionActiveRows_le_domainSize :
    actionActiveRows ≤ actionDomainSize := by
  unfold actionActiveRows TopLevelCircuit.usableRowsAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem actionUsedRows_le_domainSize :
    Halo2.usedRows actionCircuit.operations ≤ actionDomainSize :=
  actionCircuit.operations_usedRows_le_usedRows.trans
    (actionCircuit.usedRows_le_usableRowsAt_domainExponent.trans
      actionActiveRows_le_domainSize)

/-- Every Action constants allocation uses an equality-enabled configured constants
column. -/
theorem actionConst_column_mem_permutationColumns
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ actionConsts) :
    (AnyColumn.mk .fixed entry.2.1) ∈
      actionCircuit.constraintSystem.permutationColumns := by
  rw [actionConsts, Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact actionCircuit.constantAssignmentColumn_mem_permutationColumns
    hassignment

/-- Every keygen copy tuple names two Action permutation columns. Row bounds are
proved generically from the compiler below. -/
theorem actionCopyColumnBounds : ∀ t ∈ actionCopyRaw,
    t.1 < actionNumPermCols ∧ t.2.2.1 < actionNumPermCols := by
  intro tuple htuple
  apply V1_copyList_columns_lt actionCircuit.constraintSystem
    actionCircuit.operations actionCircuit.keygenCoherent
    actionCircuit.regionStarts actionConsts actionConstantSites_fit
    actionConst_column_mem_permutationColumns tuple
  simpa only [actionCopyRaw, actionPermCols] using htuple

/-- Every V1 Action constant allocation lies below the compiler-derived operation
footprint. -/
theorem actionConst_row_lt_usedRows
    (entry : ℕ × ℕ × ℕ) (hentry : entry ∈ actionConsts) :
    entry.2.2 < Halo2.usedRows actionCircuit.operations := by
  rw [actionConsts, Keygen.constantCopyEntries, List.mem_map] at hentry
  obtain ⟨⟨value, column, row⟩, hassignment, rfl⟩ := hentry
  exact V1_constantAssignments_row_lt_usedRows
    actionCircuit.operations
    (actionCircuit.constraintSystem.constants.map (·.index))
    hassignment

/-- Every raw Action keygen copy endpoint lies below the compiler-derived operation
footprint. -/
theorem actionCopyRaw_rows_lt_usedRows
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ actionCopyRaw) :
    tuple.2.1 < Halo2.usedRows actionCircuit.operations ∧
      tuple.2.2.2 < Halo2.usedRows actionCircuit.operations := by
  apply V1_copyList_rows_lt_usedRows actionCircuit.operations
    actionPermCols actionConsts actionConstantSites_fit
    actionConst_row_lt_usedRows tuple
  simpa only [actionCopyRaw, TopLevelCircuit.regionStarts,
    TopLevelCompilation.regionStarts] using htuple

/-- Every keygen copy tuple is in range. Only column membership remains
Action-specific; row bounds follow from the generic compiler footprint. -/
theorem actionCopyBounds : ∀ t ∈ actionCopyRaw, t.1 < actionNumPermCols ∧
    t.2.1 < actionDomainSize ∧ t.2.2.1 < actionNumPermCols ∧
    t.2.2.2 < actionDomainSize := by
  intro tuple htuple
  have hcolumns := actionCopyColumnBounds tuple htuple
  have hrows := actionCopyRaw_rows_lt_usedRows tuple htuple
  exact ⟨hcolumns.1, hrows.1.trans_le actionUsedRows_le_domainSize,
    hcolumns.2, hrows.2.trans_le actionUsedRows_le_domainSize⟩

/-- The decoded Action copy list. -/
def actionCopies :
    List (FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize) :=
  decodeCopies actionNumPermCols actionDomainSize actionCopyRaw actionCopyBounds

/-- Every decoded copy pair lies in the compiler-derived usable-row prefix. -/
theorem actionCopyRowsActive
    (pair : FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize)
    (hpair : pair ∈ actionCopies) :
    (pair.1.2 : ℕ) < actionActiveRows ∧
      (pair.2.2 : ℕ) < actionActiveRows := by
  have hrawMap := decodeCopies_map actionNumPermCols actionDomainSize
    actionCopyRaw actionCopyBounds
  have hraw :
      (pair.1.pair.1, pair.1.pair.2,
        pair.2.pair.1, pair.2.pair.2) ∈ actionCopyRaw := by
    rw [← hrawMap]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  have hrows := actionCopyRaw_rows_lt_usedRows _ hraw
  have husedRows :
      Halo2.usedRows actionCircuit.operations ≤ actionActiveRows :=
    actionCircuit.operations_usedRows_le_usedRows.trans
      actionCircuit.usedRows_le_usableRowsAt_domainExponent
  exact ⟨hrows.1.trans_le husedRows, hrows.2.trans_le husedRows⟩

/-- Action keygen replays preserve the usable-row prefix. -/
theorem actionReplayPreservesActive
    (cell : FlatCell actionNumPermCols actionDomainSize)
    (hcell : (cell.2 : ℕ) < actionActiveRows) :
    ((replayKeygenPermutation actionCopies cell).2 : ℕ) <
      actionActiveRows := by
  apply replayKeygenPermutation_preserves actionCopies
    (fun candidate => (candidate.2 : ℕ) < actionActiveRows)
  · intro pair hpair
    exact actionCopyRowsActive pair hpair
  · exact hcell

/-- The replay's flat column count is the circuit-derived permutation-column count. -/
theorem actionNumPermCols_eq_derived :
    actionNumPermCols =
      actionCircuit.permutationColumnCount := by
  rw [actionCircuit.permutationColumnCount_eq_permutationColumns_length]
  simp only [actionNumPermCols, actionPermCols, Keygen.permColsOf,
    List.length_map, TopLevelCircuit.permutationColumns]

/-- Resolver-backed Action permutation chunks have the compiler-derived width. -/
theorem actionResolverChunkWidth
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (chunk :
      Fin actionCircuit.permutationSetCount) :
    (ResolverPermutationPairs
        (actionCircuit.toVerifierKey urs)
        poly proofIndex chunk).length =
      min actionCircuit.chunkLen
        (actionNumPermCols -
          (chunk : ℕ) *
            actionCircuit.chunkLen) := by
  rw [actionNumPermCols_eq_derived]
  exact actionCircuit.resolverPermutationPairs_length
    urs poly proofIndex chunk

/-- The circuit-derived Action permutation chunk width is positive. -/
theorem actionChunkLen_pos
    : 0 < actionCircuit.chunkLen :=
  constraintSystem_chunkLen_pos
    actionCircuit.constraintSystem

/-- The derived chunk family has enough total slots for every Action
permutation column. -/
theorem actionPermutationChunks_cover
    : actionNumPermCols ≤
      actionCircuit.permutationSetCount * actionCircuit.chunkLen := by
  rw [actionNumPermCols_eq_derived]
  have hcover :=
    permutationColumns_length_le_chunks_mul actionCircuit
  rw [verifierCS_permutationChunks_length] at hcover
  exact hcover

/-- Flatten the compiler-derived Action chunks to `(row, global column)`. -/
def actionChunkFlatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    ResolverPermutationCell
        (actionCircuit.toVerifierKey urs)
        poly proofIndex actionDomainSize ≃
      Fin actionDomainSize × Fin actionNumPermCols :=
  Layout.Asm.chunkFlatten
    actionCircuit.permutationSetCount
    actionNumPermCols
    actionCircuit.chunkLen
    actionDomainSize
    (fun chunk =>
      (ResolverPermutationPairs
        (actionCircuit.toVerifierKey urs)
        poly proofIndex chunk).length)
    actionChunkLen_pos
    actionPermutationChunks_cover
    (actionResolverChunkWidth pp urs poly proofIndex)

theorem actionChunkFlatten_apply_column
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (actionCircuit.toVerifierKey urs) poly proofIndex actionDomainSize) :
    ((actionChunkFlatten pp urs poly proofIndex cell).2 : ℕ) =
      (cell.1 : ℕ) * actionCircuit.chunkLen + (cell.2.2 : ℕ) := by
  simpa only [actionChunkFlatten] using
    Layout.Asm.chunkFlatten_apply_column
      actionChunkLen_pos
      actionPermutationChunks_cover
      (actionResolverChunkWidth pp urs poly proofIndex) cell

theorem actionChunkFlatten_symm_apply_row
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : Fin actionDomainSize × Fin actionNumPermCols) :
    ((actionChunkFlatten pp urs poly proofIndex).symm cell).2.1 = cell.1 := by
  simpa only [actionChunkFlatten] using
    Layout.Asm.chunkFlatten_symm_apply_row
      actionChunkLen_pos
      actionPermutationChunks_cover
      (actionResolverChunkWidth pp urs poly proofIndex) cell

theorem actionChunkFlatten_symm_apply_column
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) (proofIndex : Fin pp.numProofs)
    (cell : Fin actionDomainSize × Fin actionNumPermCols) :
    (((actionChunkFlatten pp urs poly proofIndex).symm cell).1 : ℕ) *
          actionCircuit.chunkLen +
        (((actionChunkFlatten pp urs poly proofIndex).symm cell).2.2 : ℕ) =
      (cell.2 : ℕ) := by
  simpa only [actionChunkFlatten] using
    Layout.Asm.chunkFlatten_symm_apply_column
      actionChunkLen_pos
      actionPermutationChunks_cover
      (actionResolverChunkWidth pp urs poly proofIndex) cell

/-- The full-domain Action keygen permutation in resolver chunk coordinates. -/
def actionFullSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (actionCircuit.toVerifierKey urs)
        poly proofIndex actionDomainSize) :=
  chunkPermutationOfFlat
    (actionChunkFlatten pp urs poly proofIndex)
    ((Equiv.prodComm
        (Fin actionNumPermCols) (Fin actionDomainSize)).permCongr
      (replayKeygenPermutation actionCopies))

/-- The full-domain Action replay sends active chunk cells to active chunk
cells. This is structural after the finite endpoint-row certificate: flattening
and unflattening preserve the row coordinate. -/
theorem actionFullSigma_preservesActive
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (actionCircuit.toVerifierKey urs)
      poly proofIndex actionActiveRows) :
    (((actionFullSigma pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).2.1 :
      ℕ) < actionActiveRows := by
  let flat : FlatCell actionNumPermCols actionDomainSize :=
    (Equiv.prodComm (Fin actionNumPermCols) (Fin actionDomainSize)).symm
      (actionChunkFlatten pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell))
  have hflat : (flat.2 : ℕ) < actionActiveRows := by
    change
      (((actionChunkFlatten pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).1 :
        ℕ) < actionActiveRows
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using cell.2.1.isLt
  have hreplay := actionReplayPreservesActive flat hflat
  simpa only [actionFullSigma, chunkPermutationOfFlat_apply,
    Equiv.permCongr_apply, Equiv.prodComm_apply, actionChunkFlatten,
    _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row, flat] using hreplay

/-- Restrict the full Action keygen replay to the usable-row prefix. -/
def actionActiveSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (actionCircuit.toVerifierKey urs)
        poly proofIndex actionActiveRows) :=
  Layout.Asm.restrictActivePerm actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)

/-- The active Action replay is the restriction of its full-domain replay. -/
theorem actionActiveSigma_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (cell : ResolverPermutationCell
      (actionCircuit.toVerifierKey urs)
      poly proofIndex actionActiveRows) :
    widenPermutationChunkCell actionActiveRows_le_domainSize
        (actionActiveSigma pp urs poly proofIndex cell) =
      actionFullSigma pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell) :=
  Layout.Asm.restrictActivePerm_widen
    actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)
    cell

/-- Re-express an active flat keygen cell in resolver chunk coordinates. -/
def actionActiveChunkCell
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    ResolverPermutationCell
      (actionCircuit.toVerifierKey urs)
      poly proofIndex actionActiveRows :=
  let full :=
    (actionChunkFlatten pp urs poly proofIndex).symm (flat.2, flat.1)
  ⟨full.1,
    ⟨(full.2.1 : ℕ), by
      simpa only [actionChunkFlatten,
        _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row] using hrow⟩,
    full.2.2⟩

/-- Widening the active chunk encoding recovers the full inverse flattening. -/
theorem actionActiveChunkCell_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    widenPermutationChunkCell actionActiveRows_le_domainSize
        (actionActiveChunkCell pp urs poly proofIndex flat hrow) =
      (actionChunkFlatten pp urs poly proofIndex).symm
        (flat.2, flat.1) := by
  apply _root_.Zcash.Snark.Layout.Asm.chunkCell_ext <;> rfl

/-- Flattening the resolver encoding of an active flat cell returns `(row,column)`. -/
theorem actionActiveChunkCell_flatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    actionChunkFlatten pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize
          (actionActiveChunkCell pp urs poly proofIndex flat hrow)) =
      (flat.2, flat.1) := by
  rw [actionActiveChunkCell_widen, Equiv.apply_symm_apply]

/-- The Action cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def actionCopyValue (env : Environment Fp)
    (fc : FlatCell actionNumPermCols actionDomainSize) : Fp :=
  env.get (ColRef.toAny (actionPermCols.getD (fc.1 : ℕ) (.advice 0)))
    (((fc.2 : ℕ) : ℕ) : ℤ)

/--
The resolver chunk coordinate obtained from an active flat Action cell decodes
to the same concrete column as the flat cell's global permutation-column
index.
-/
theorem actionActiveChunkCell_columnAddress
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    let cell :=
      actionActiveChunkCell pp urs poly proofIndex flat hrow
    permutationColumnAddress
        (actionCircuit.toVerifierKey urs)
        ((actionCircuit.verifierCS.permutationChunks.getD
          cell.1 []).getD cell.2.2 ((.advice 0), 0)).1 =
      ColRef.toAny
        (actionPermCols.getD flat.1 (.advice 0)) := by
  let vk := actionCircuit.toVerifierKey urs
  let cell :=
    actionActiveChunkCell pp urs poly proofIndex flat hrow
  have hvkChunks :
      vk.permutationChunks =
        actionCircuit.verifierCS.permutationChunks := by
    simpa only [vk] using
      actionCircuit.toVerifierKey_permutationChunks urs
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
        (actionPermCols.map ColRef.toAny).length := by
    simpa only [List.length_map] using flat.1.isLt
  have hcoordinate :
      (cell.1 : ℕ) * vk.chunkLen + (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hflatten :=
      actionActiveChunkCell_flatten
        pp urs poly proofIndex flat hrow
    have hsecond :=
      congrArg (fun coordinate => (coordinate.2 : ℕ)) hflatten
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten,
      cell, vk, actionCircuit.toVerifierKey_chunkLen] using hsecond
  have hindex :
      (vk.permutationChunks.take cell.1).flatten.length +
          (cell.2.2 : ℕ) =
        (flat.1 : ℕ) := by
    have hprefix :
        (vk.permutationChunks.take cell.1).flatten.length =
          (cell.1 : ℕ) * vk.chunkLen := by
      exact actionCircuit.toVerifierKey_permutationChunks_take_flatten_length
        urs cell.1 hchunk
    rw [hprefix]
    exact hcoordinate
  have hdecoded := decodedChunkAddress_eq_sourceColumn
    (fun reference =>
      permutationColumnAddress vk reference.1)
    ((.advice 0), 0)
    (ColRef.toAny (.advice 0))
    vk.permutationChunks
    (actionPermCols.map ColRef.toAny)
    (by
      simpa only [vk, actionPermCols,
        actionCircuit.toVerifierKey_permutationChunks] using
        ActionPermutationDomain.permutationColumnAddresses_eq urs)
    cell.1 cell.2.2 flat.1
    hchunk hcolumn hglobal hindex
  have hmap :
      (actionPermCols.map ColRef.toAny).getD flat.1
          (ColRef.toAny (.advice 0)) =
        ColRef.toAny (actionPermCols.getD flat.1 (.advice 0)) :=
    List.getD_map actionPermCols (.advice 0) ColRef.toAny
  rw [← hvkChunks]
  simpa only [vk, cell] using hdecoded.trans hmap

/--
The Action flat-cell valuation in the canonical resolver environment is exactly
the verifier-native `chunkRowValue` at its active resolver chunk coordinate.
-/
theorem actionCopyValue_eq_activeChunkRowValue
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex :
      Fin pp.numProofs)
    (flat : FlatCell actionNumPermCols actionDomainSize)
    (hrow : (flat.2 : ℕ) < actionActiveRows) :
    let circuitShape : CircuitShape := actionCircuit.shape
    let vk : VerifyingKey circuitShape Fp G :=
      actionCircuit.toVerifierKey urs
    let cell : ResolverPermutationCell
        (shape := circuitShape) (numProofs := pp.numProofs)
        vk poly proofIndex actionActiveRows :=
      actionActiveChunkCell pp urs poly proofIndex flat hrow
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
      chunkRowValue actionCircuit.omega
        (ResolverPermutationPairs (shape := circuitShape)
          (numProofs := pp.numProofs) vk poly proofIndex)
        cell.1 cell.2.1 cell.2.2 := by
  let circuitShape : CircuitShape := actionCircuit.shape
  let vk : VerifyingKey circuitShape Fp G :=
    actionCircuit.toVerifierKey urs
  let cell : ResolverPermutationCell
      (shape := circuitShape) (numProofs := pp.numProofs)
      vk poly proofIndex actionActiveRows :=
    actionActiveChunkCell pp urs poly proofIndex flat hrow
  simp only
  let chunk : ℕ := cell.1
  let row : ℕ := cell.2.1
  let column : ℕ := cell.2.2
  have hvkChunks :
      vk.permutationChunks =
        actionCircuit.verifierCS.permutationChunks := by
    simpa only [vk] using
      actionCircuit.toVerifierKey_permutationChunks urs
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
    (actionCircuit.permutationChunkRoutingCoherent urs
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
        (resolverEnvironment vk poly proofIndex actionActiveRows).get
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
    actionActiveChunkCell_columnAddress
      pp urs poly proofIndex flat hrow
  simp only at haddressRaw
  rw [← hvkChunks] at haddressRaw
  have haddress :
      permutationColumnAddress vk
          ((vk.permutationChunks.getD chunk []).getD
            column ((.advice 0), 0)).1 =
        ColRef.toAny (actionPermCols.getD flat.1 (.advice 0)) := by
    simpa only [chunk, column] using haddressRaw
  rw [List.getD_eq_getElem _ _ hcolumn] at haddress
  have hcellRow : row = (flat.2 : ℕ) := by
    have hflatten :=
      actionActiveChunkCell_flatten
        pp urs poly proofIndex flat hrow
    have hfirst :=
      congrArg (fun coordinate => (coordinate.1 : ℕ)) hflatten
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row, row, cell] using hfirst
  have hresult :
    actionCopyValue
        (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
      chunkRowValue actionCircuit.omega
        (ResolverPermutationPairs (shape := circuitShape)
          (numProofs := pp.numProofs) vk poly proofIndex)
        chunk row column := by
    calc
      actionCopyValue
          (resolverEnvironment vk poly proofIndex actionActiveRows) flat =
        (resolverEnvironment vk poly proofIndex actionActiveRows).get
          (ColRef.toAny (actionPermCols.getD flat.1 (.advice 0)))
          (flat.2 : ℤ) := by
            simp only [actionCopyValue]
      _ = (resolverEnvironment vk poly proofIndex actionActiveRows).get
          (permutationColumnAddress vk
            ((vk.permutationChunks.getD chunk [])[column]).1)
          (row : ℤ) := by
            rw [← hcellRow]
            congr 1
            exact haddress.symm
      _ = chunkRowValue actionCircuit.omega
          (ResolverPermutationPairs (shape := circuitShape)
            (numProofs := pp.numProofs) vk poly proofIndex)
          chunk row column := by
            simpa only [vk,
              actionCircuit.toVerifierKey_omega] using hresolver.symm
  simpa only [chunk, row, column] using hresult

/--
Every decoded Action keygen-copy pair has equal values in the canonical
resolver environment once the generic permutation premises hold.

`hcycleSigma` records the construction provenance intentionally omitted from
the abstract `ResolverPermutationCycle`: the cycle is the Action active replay.
-/
theorem actionCopyPairValue_of_resolverPermutation
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges actionCircuit.domainExponent Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    {n : ℕ}
    (hsat : ConstraintSatisfaction
      (actionCircuit.constraintModel pp urs ch poly) n)
    (hdom : ResolverPermutationDomain
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.constraintModel pp urs ch poly).l0
      (actionCircuit.constraintModel pp urs ch poly).lLast
      (actionCircuit.constraintModel pp urs ch poly).lBlind
      n actionActiveRows)
    (hcycle : ResolverPermutationCycle
      (actionCircuit.toVerifierKey urs)
      poly proofIndex actionActiveRows)
    (hcycleSigma :
      hcycle.sigma =
        actionActiveSigma pp urs poly proofIndex)
    (hgood : ResolverPermutationGoodChallenges
      (actionCircuit.toVerifierKey urs)
      ch poly proofIndex actionActiveRows) :
    ∀ pair ∈ actionCopies,
      actionCopyValue
          (resolverEnvironment
            (actionCircuit.toVerifierKey urs)
            poly proofIndex actionActiveRows)
          pair.1 =
        actionCopyValue
          (resolverEnvironment
            (actionCircuit.toVerifierKey urs)
            poly proofIndex actionActiveRows)
        pair.2 := by
  intro pair hpair
  have hsatResolver := hsat
  rw [actionCircuit.constraintModel_eq_constraintModelOfResolver_projections]
    at hsatResolver
  have hrows := actionCopyRowsActive pair hpair
  let left :=
    actionActiveChunkCell pp urs poly proofIndex pair.1 hrows.1
  let right :=
    actionActiveChunkCell pp urs poly proofIndex pair.2 hrows.2
  have hrestrict :
      ∀ cell : ResolverPermutationCell
          (actionCircuit.toVerifierKey urs) poly proofIndex actionActiveRows,
        widenPermutationChunkCell actionActiveRows_le_domainSize
            (hcycle.sigma cell) =
          chunkPermutationOfFlat
            (actionChunkFlatten pp urs poly proofIndex)
            ((Equiv.prodComm
              (Fin actionNumPermCols)
              (Fin actionDomainSize)).permCongr
                (replayKeygenPermutation actionCopies))
            (widenPermutationChunkCell
              actionActiveRows_le_domainSize cell) := by
    intro cell
    rw [hcycleSigma]
    simpa only [actionFullSigma] using
      actionActiveSigma_widen pp urs poly proofIndex cell
  have hchunkValues :=
    Layout.Asm.chunkRowValue_eq_of_mem_copies
      (numProofs := pp.numProofs)
      (actionCircuit.toVerifierKey urs) ch poly
      (actionCircuit.constraintModel pp urs ch poly).l0
      (actionCircuit.constraintModel pp urs ch poly).lLast
      (actionCircuit.constraintModel pp urs ch poly).lBlind
      proofIndex hsatResolver hdom hcycle hgood
      actionActiveRows_le_domainSize actionCopies
      (actionChunkFlatten pp urs poly proofIndex)
      hrestrict
      pair.1 pair.2 hpair left right
      (by
        simpa only [left] using
          actionActiveChunkCell_flatten
            pp urs poly proofIndex pair.1 hrows.1)
      (by
        simpa only [right] using
          actionActiveChunkCell_flatten
            pp urs poly proofIndex pair.2 hrows.2)
  calc
    actionCopyValue
        (resolverEnvironment
          (actionCircuit.toVerifierKey urs) poly proofIndex actionActiveRows)
        pair.1 =
      chunkRowValue actionCircuit.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (actionCircuit.toVerifierKey urs) poly proofIndex)
        left.1 left.2.1 left.2.2 := by
          simpa only [left] using
            actionCopyValue_eq_activeChunkRowValue
              pp urs poly proofIndex pair.1 hrows.1
    _ = chunkRowValue actionCircuit.omega
        (ResolverPermutationPairs (numProofs := pp.numProofs)
          (actionCircuit.toVerifierKey urs) poly proofIndex)
        right.1 right.2.1 right.2.2 := by
          simpa only [actionCircuit.toVerifierKey_omega] using hchunkValues
    _ = actionCopyValue
        (resolverEnvironment
          (actionCircuit.toVerifierKey urs) poly proofIndex actionActiveRows)
        pair.2 := by
          symm
          simpa only [right] using
            actionCopyValue_eq_activeChunkRowValue
              pp urs poly proofIndex pair.2 hrows.2

/-- Decode membership in the raw Action copy list to a typed copy pair. -/
theorem exists_actionCopy_of_raw
    {tuple : ℕ × ℕ × ℕ × ℕ} (hraw : tuple ∈ actionCopyRaw) :
    ∃ pair ∈ actionCopies,
      pair.1.pair = (tuple.1, tuple.2.1) ∧
        pair.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
  have hrawMap :
      actionCopyRaw = actionCopies.map
        (fun pair =>
          (pair.1.pair.1, pair.1.pair.2,
            pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map actionNumPermCols actionDomainSize
      actionCopyRaw actionCopyBounds).symm
  rw [hrawMap, List.mem_map] at hraw
  obtain ⟨pair, hpair, htuple⟩ := hraw
  refine ⟨pair, hpair, ?_, ?_⟩
  · rw [← htuple]
  · rw [← htuple]


end Zcash.Snark

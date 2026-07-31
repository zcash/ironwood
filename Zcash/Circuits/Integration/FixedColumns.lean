import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Circuits.Integration.FixedLayout
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.SelectorCoherence
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Keygen.Lagrange

/-!
# Fixed-column commitment provenance

The verifier's fixed columns are commitments in the verifying key, while the
multiopen extractor returns augmented monomial-basis openings. This module crosses
that representation boundary without assuming commitment binding: a routed decoded
fixed polynomial is the keygen row polynomial, or the two openings compute a
nontrivial relation among the augmented URS generators.

The result is generic in the fixed row vector and its Lagrange commitment key.
`TopLevelCircuit` keygen supplies those vectors; the Action endpoint only selects
the circuit-owned instance.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (derivedUrsGLagrange)
open Halo2 CompPoly.CPolynomial
open CompElliptic.Curves.Pasta

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

omit [AddCommGroup G] [Module Fp G] in
/--
A fixed-column entry in the accepted key's query layout produces the assembled
query used by canonical member routing.
-/
theorem fixedQuery_of_layout
    {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (column : ℕ) (rotation : ℤ)
    (hcount :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hlayout : (column, rotation) ∈ vk.fixedQueryLayout) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .fixedCol column := by
  obtain ⟨queryIndex, hqueryIndex, hentry⟩ :=
    List.mem_iff_getElem.mp hlayout
  have hevalIndex :
      queryIndex < (List.ofFn ps.fixedEvals).length := by
    simpa only [List.length_ofFn, ← hcount] using hqueryIndex
  obtain ⟨q, hq, hqid, -⟩ :=
    columnQueries_layout_mem_eval
      (k' := shape.k) vk.omega ch.x vk.fixedCommitment
      CommitmentId.fixedCol vk.fixedQueryLayout
      (List.ofFn ps.fixedEvals) hqueryIndex hevalIndex
  refine ⟨q, ?_, ?_⟩
  · simp only [assembleQueries, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hq))
  · rw [List.getD_eq_getElem _ _ hqueryIndex, hentry] at hqid
    exact hqid

omit [AddCommGroup G] [Module Fp G] in
/-- A fixed-column identity can occur in the assembled verifier queries only through
the verifying key's fixed-query layout. -/
theorem fixedLayout_of_assembledQuery
    {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (q : VerifierQuery shape.k Fp G)
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch)
    (column : ℕ)
    (hid : q.commId = .fixedCol column) :
    ∃ rotation, (column, rotation) ∈ vk.fixedQueryLayout := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ :=
      List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ :=
      List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with hleft | hlookup
    · rcases hleft with hleft | hpermutation
      · rcases hleft with hinstance | hadvice
        · rw [columnQueries, List.mem_map] at hinstance
          obtain ⟨entry, _, rfl⟩ := hinstance
          simp at hid
        · rw [columnQueries, List.mem_map] at hadvice
          obtain ⟨entry, _, rfl⟩ := hadvice
          simp at hid
      · simp only [permutationQueries, List.mem_append] at hpermutation
        rcases hpermutation with hregular | hlast
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
            or_false] at hregular
          obtain ⟨entry, _, hq | hq⟩ := hregular
          · subst q
            simp at hid
          · subst q
            simp at hid
        · rw [List.mem_filterMap] at hlast
          obtain ⟨entry, _, hentry⟩ := hlast
          cases hlastEval : entry.1.2.lastEval with
          | none => simp [hlastEval] at hentry
          | some lastEvaluation =>
            simp [hlastEval] at hentry
            subst q
            simp at hid
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, _, hq | hq | hq | hq | hq⟩ := hlookup
      all_goals
        subst q
        simp at hid
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, hentry, rfl⟩ := hfixed
    injection hid with hcolumn
    obtain ⟨index, hindex, hentryAt⟩ := List.mem_iff_getElem.mp hentry
    have hlayout : index < vk.fixedQueryLayout.length := by
      exact hindex.trans_le (by
        simp only [List.length_zip]
        exact Nat.min_le_left _ _)
    refine ⟨entry.1.2, ?_⟩
    have hfirst : entry.1 = vk.fixedQueryLayout[index] := by
      rw [← hentryAt]
      simp
    rw [← hcolumn]
    change entry.1 ∈ vk.fixedQueryLayout
    rw [hfirst]
    exact List.getElem_mem _
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨entry, _, rfl⟩ := hcommon
    simp at hid
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with hq | hq
    · subst q
      simp at hid
    · subst q
      simp at hid

/-- Sparse table and region-local fixed assignments emitted by top-level keygen. -/
def topLevelFixedOperationEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.tableFixed (ZMod.val : Fp → ℕ)
      (top.usableRowsAt top.domainExponent) (top.operations) ++
    Layout.regionAssignFixed (ZMod.val : Fp → ℕ)
      top.regionStarts (indexedRegions (top.operations) 0).1

/--
Sparse packed-selector assignments emitted by top-level keygen.

The current full-circuit realization check also fails closed if two selector
activations assign incompatible values to the same packed cell: the final dense
cell cannot realize both sparse entries. That failure is intentionally safe but
opaque. The structural replacement should instead derive non-overlap (or compatible
composition) from selector packing and region-placement invariants.
-/
def topLevelSelectorEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.selectorFixed top.selectorMap top.selectorActivations

/--
Expected dense cells for lookup-relevant selectors that the selector compiler packed
alone at root one. Enabled leaves read one; disabled leaves read zero.

A missing or non-singleton map entry emits an out-of-bounds sentinel, so realization
of this interim list also rules those malformed cases out. This encoding relies on
the strict `column < numFixedColumns` check in `interimFixedRealizationFailures`;
widening or removing that bound would silently turn malformed selector mappings into
accepted zero entries. The structural replacement derives singleton ownership and
disabled-row zero from compiler invariants instead.
-/
def topLevelSingletonLookupSelectorEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  let operations := top.operations
  let selectorMap := top.selectorMap
  let starts := top.regionStarts
  (operationEnabledLookups operations 0).flatMap fun lookup =>
    lookup.inputSelectorLeaves.filterMap fun selector =>
      match selectorMap.lookup selector.index with
      | some compressed =>
          if compressed.combinationLen = 1 ∧
              compressed.assignedRoot = 1 then
            some
              (compressed.packedCol,
                starts.getD lookup.region 0 + lookup.row,
                if lookup.enabled.any
                    (fun candidate =>
                      candidate.index == selector.index) then
                  1
                else
                  0)
          else
            some
              (top.pinnedCS.numFixedColumns,
                starts.getD lookup.region 0 + lookup.row, 0)
      | none =>
          some
            (top.pinnedCS.numFixedColumns,
              starts.getD lookup.region 0 + lookup.row, 0)

/-- Fixed cells allocated for `constrainConstant` values by the V1 floor planner. -/
def topLevelConstantEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.constantsFixed
    (Keygen.constantCopyEntries top.constraintSystem (top.operations))

/--
Every fixed cell whose value is consumed by the semantic bridge: emitted table,
region, constant, and selector assignments, plus the interim exact cells needed by
lookup-selector projection.
-/
def topLevelRequiredFixedEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  topLevelFixedOperationEntries top ++
    topLevelConstantEntries top ++
    topLevelSelectorEntries top ++
    topLevelSingletonLookupSelectorEntries top

/--
**INTERIM full-circuit fallback.** Columns allocated by the pinned constraint
system but absent from the final fixed-query layout, followed by queried columns
outside the allocated range.

This finite diagnostic exists only to unblock concrete circuits while the query
registration compiler is given a structural coverage theorem.  New generic
interfaces should consume that theorem, not this computation.
-/
def interimFixedQueryCoverageFailures
    (top : TopLevelCircuit Fp Config PublicInput) : List ℕ :=
  let pinned := top.pinnedCS
  let queried := pinned.fixedQueryLayout.map Prod.fst
  (List.range pinned.numFixedColumns).filter
      (fun column => decide (column ∉ queried)) ++
    queried.filter (fun column => decide (pinned.numFixedColumns ≤ column))

/--
An empty interim query-coverage diagnostic supplies the current
`TopLevelFixedCoherence` coverage field.
-/
theorem fixedQueryCoverage_of_interimFailures_eq_nil
    (top : TopLevelCircuit Fp Config PublicInput)
    (hfail : interimFixedQueryCoverageFailures top = []) :
    ∀ column,
      column < top.pinnedCS.numFixedColumns →
        ∃ rotation, (column, rotation) ∈ top.pinnedCS.fixedQueryLayout := by
  intro column hcolumn
  have hnotFailure :
      column ∉ interimFixedQueryCoverageFailures top := by
    rw [hfail]
    simp
  have hcolumnMem :
      column ∈ top.pinnedCS.fixedQueryLayout.map Prod.fst := by
    by_contra hmissing
    apply hnotFailure
    simp [interimFixedQueryCoverageFailures, hcolumn, hmissing]
  rw [List.mem_map] at hcolumnMem
  obtain ⟨entry, hentry, hcolumnEntry⟩ := hcolumnMem
  rcases entry with ⟨entryColumn, rotation⟩
  simp only at hcolumnEntry
  subst entryColumn
  exact ⟨rotation, hentry⟩

/-- An empty interim query diagnostic also rules out out-of-range layout entries. -/
theorem fixedQueryBounded_of_interimFailures_eq_nil
    (top : TopLevelCircuit Fp Config PublicInput)
    (hfail : interimFixedQueryCoverageFailures top = []) :
    ∀ column rotation,
      (column, rotation) ∈ top.pinnedCS.fixedQueryLayout →
        column < top.pinnedCS.numFixedColumns := by
  intro column rotation hentry
  have hnotFailure :
      column ∉ interimFixedQueryCoverageFailures top := by
    rw [hfail]
    simp
  have hqueried :
      column ∈ top.pinnedCS.fixedQueryLayout.map Prod.fst := by
    exact List.mem_map.mpr ⟨(column, rotation), hentry, rfl⟩
  by_contra hbound
  apply hnotFailure
  simp only [interimFixedQueryCoverageFailures, List.mem_append]
  apply Or.inr
  rw [List.mem_filter]
  exact ⟨hqueried, decide_eq_true (Nat.le_of_not_gt hbound)⟩

/--
**INTERIM full-circuit fallback.** Required fixed/table/selector writes whose
final dense keygen cell does not have the required bounds and value.

The intended replacement follows the compiler pipeline:

* V1 placement proves that different regions never overlap in cells;
* region-local fixed writes are checked or proved within their small region;
* table layout, constant allocation, and selector packing expose their own
  collision and composition laws;
* generic last-write/dedup/scatter theorems assemble those local facts.

This diagnostic is deliberately named `interim` so a successful whole-circuit
`native_decide` certificate cannot silently become the permanent architecture.
-/
def interimFixedRealizationFailures
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  let n := 2 ^ top.domainExponent
  let numFixedColumns := top.pinnedCS.numFixedColumns
  let rows := top.fixedRows
  let required := topLevelRequiredFixedEntries top
  required.filter fun entry =>
    decide (¬ (
      entry.2.1 < n ∧
      entry.1 < numFixedColumns ∧
      (rows.getD entry.1 []).getD entry.2.1 0 =
        (entry.2.2 : Fp)))

/--
An empty interim realization diagnostic proves the exact sparse-to-dense fact
used by `TopLevelFixedCoherence`.
-/
theorem fixedRowsRealize_of_interimFailures_eq_nil
    (top : TopLevelCircuit Fp Config PublicInput)
    (hfail : interimFixedRealizationFailures top = []) :
    ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < 2 ^ top.domainExponent ∧
          column < top.pinnedCS.numFixedColumns ∧
          (top.fixedRows.getD column []).getD row 0 =
            (value : Fp) := by
  intro column row value hentry
  let property : Prop :=
    row < 2 ^ top.domainExponent ∧
      column < top.pinnedCS.numFixedColumns ∧
      (top.fixedRows.getD column []).getD row 0 = (value : Fp)
  have hnotFailure :
      (column, row, value) ∉ interimFixedRealizationFailures top := by
    rw [hfail]
    simp
  have hnotnot : ¬ ¬ property := by
    intro hnot
    apply hnotFailure
    rw [interimFixedRealizationFailures, List.mem_filter]
    refine ⟨hentry, ?_⟩
    change decide (¬ property) = true
    exact decide_eq_true hnot
  exact Classical.not_not.mp hnotnot

/--
The fixed-row part of a top-level circuit's keygen boundary.

This record contains no proof-dependent data. Its rows, commitments, and query
coverage are shared by every proof in a bundle. `realizes` is the layout compiler's
sparse-to-dense correctness statement for exactly the entries consumed by Clean
fixed/table semantics and selector activation.
-/
structure TopLevelFixedCoherence
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G) where
  key :
    LagrangeCommitmentKey urs (top.toVerifierKey pp urs).omega
  commitment : ∀ column,
    column < top.pinnedCS.numFixedColumns →
      (top.toVerifierKey pp urs).fixedCommitment column =
        key.commitInstance (top.fixedRows.getD column []) 1
  fixedQueryCount :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived top).numFixedQueries
  queryLayout : ∀ column,
    column < top.pinnedCS.numFixedColumns →
      ∃ rotation,
        (column, rotation) ∈
          (top.toVerifierKey pp urs).fixedQueryLayout
  queryLayoutBounded : ∀ column rotation,
    (column, rotation) ∈
        (top.toVerifierKey pp urs).fixedQueryLayout →
      column < top.pinnedCS.numFixedColumns
  realizes : ∀ column row value,
    (column, row, value) ∈
        topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
        column < top.pinnedCS.numFixedColumns ∧
        (top.fixedRows.getD column []).getD row 0 = (value : Fp)

namespace TopLevelFixedCoherence

/-- The circuit-derived VK's fixed commitment at one in-range column is the
full-list commitment of the corresponding keygen row vector. -/
theorem fixedCommitment_eq_commitInstance
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (top.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp)))))
    (column : ℕ) (hcolumn : column < top.pinnedCS.numFixedColumns) :
    (top.toVerifierKey pp urs).fixedCommitment column =
      (LagrangeCommitmentKey.ofFullList
        urs (top.toVerifierKey pp urs).omega
        (derivedUrsGLagrange urs) hgenerators).commitInstance
          (top.fixedRows.getD column []) 1 := by
  rw [top.toVerifierKey_fixedCommitment]
  have hcolumnRows : column < top.fixedRows.length := by
    simpa only [top.fixedRows_length] using hcolumn
  have hget :
      (top.fixedRows.map
        (Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs))).getD column 0 =
        Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs)
          (top.fixedRows.getD column []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hcolumnRows,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hcolumnRows]
    rfl
  rw [TopLevelCircuit.fixedCommitments, List.parMap_eq_map, hget]
  apply Keygen.commitLagrangeFastWith_eq_ofFullList_commitInstance
    urs (top.toVerifierKey pp urs).omega hlen hgenerators
  rw [top.fixedRows_getD_length column hcolumn, hk]

/--
Construct fixed coherence from the exact circuit-derived keygen rows.

Dense-row shape, commitment provenance, and the query-count equality are generic.
The caller supplies only the setup's Lagrange-basis equations plus the two genuinely
static circuit/layout facts: coverage of every committed fixed column by the final
query layout, and preservation of the sparse assignments after last-write
deduplication and dense scattering.
-/
def ofKeygen
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (top.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp)))))
    (queryLayout : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        ∃ rotation,
          (column, rotation) ∈
            (top.toVerifierKey pp urs).fixedQueryLayout)
    (queryLayoutBounded : ∀ column rotation,
      (column, rotation) ∈
          (top.toVerifierKey pp urs).fixedQueryLayout →
        column < top.pinnedCS.numFixedColumns)
    (realizes : ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (top.fixedRows.getD column []).getD row 0 =
            (value : Fp)) :
    TopLevelFixedCoherence top pp urs where
  key :=
    LagrangeCommitmentKey.ofFullList
      urs (top.toVerifierKey pp urs).omega
      (derivedUrsGLagrange urs) hgenerators
  commitment :=
    fixedCommitment_eq_commitInstance
      top pp urs hk hlen hgenerators
  fixedQueryCount := top.toVerifierKey_fixedQueryCount pp urs
  queryLayout := queryLayout
  queryLayoutBounded := queryLayoutBounded
  realizes := realizes

end TopLevelFixedCoherence

omit [Module Fp G] in
/--
Binding every fixed-column resolver polynomial to the circuit's dense keygen rows
supplies the exact fixed-column encoding expected by `TopLevelAssignment`.
-/
theorem topLevelFixedColumnEncoding_of_binding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {proofIndex : Fin (pp.mergeDerived top).numProofs}
    (assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex)
    (hrows : Function.Injective
      fun row : Fin (2 ^ top.domainExponent) =>
        (top.toVerifierKey pp urs).omega ^ (row : ℕ))
    (hroot :
      (top.toVerifierKey pp urs).omega ^
        (2 ^ top.domainExponent) = 1)
    (binding : ∀ column,
      assignment.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ top.domainExponent)
          (top.toVerifierKey pp urs).omega
          (top.fixedRows.getD column [])) :
    assignment.FixedColumnEncoding pp urs := by
  intro column row
  rw [binding column.index]
  let domainRow : Fin (2 ^ top.domainExponent) :=
    ⟨row.natMod (2 ^ top.domainExponent),
      Int.natMod_lt (by positivity)⟩
  have hpow :
      (top.toVerifierKey pp urs).omega ^ row =
        (top.toVerifierKey pp urs).omega ^ (domainRow : ℕ) := by
    simpa only [domainRow] using
      zpow_eq_pow_natMod
        (top.toVerifierKey pp urs).omega
        (2 ^ top.domainExponent) (by positivity) hroot row
  rw [hpow]
  have heval :=
    instanceRowPolynomial_eval
      (values := top.fixedRows.getD column.index [])
      hrows domainRow
  change
    (instanceRowPolynomial (2 ^ top.domainExponent)
      (top.toVerifierKey pp urs).omega
      (top.fixedRows.getD column.index [])).eval
        ((top.toVerifierKey pp urs).omega ^ (domainRow : ℕ)) =
      (top.fixedRows.getD column.index []).getD
        (row.natMod (2 ^ top.domainExponent)) 0
  simpa only [domainRow] using heval

omit [Module Fp G] in
/--
One required sparse fixed entry reads back from its canonically bound dense-row
polynomial, or the caller's shared exceptional branch fires.

This is the pointwise form used by consumers such as constant-copy replay; the
family theorem below merely applies it to selectors and fixed/table operations.
-/
theorem topLevelFixedEntryRead_of_column
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈ topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp))
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top)
    (hpolyEq : poly (.fixedCol column) =
      instanceRowPolynomial (2 ^ urs.k)
        (top.toVerifierKey pp urs).omega (rows column)) :
    (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = (value : Fp) := by
  obtain ⟨hrow, hcolumn, hvalue⟩ :=
    realizes column row value hentry
  have hrow' : row < 2 ^ urs.k := by
    rwa [← hn]
  rw [resolverEnvironment_fixed, hpolyEq]
  simpa using
    (instanceRowPolynomial_eval hrows
      ⟨row, hrow'⟩).trans hvalue

omit [Module Fp G] in
/--
The same entry read, carrying the caller's shared exceptional branch as data: either the entry
reads back, or the binding family has computed a break at this entry's column.
-/
def topLevelFixedEntryRead_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈ topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp))
    {Bad : Type}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ⊕'
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = (value : Fp) ⊕'
      Bad :=
  bindOrRelationWitness
    (binding column (realizes column row value hentry).2.1)
    (topLevelFixedEntryRead_of_column poly rows hrows hn realizes proofIndex hentry)

omit [Module Fp G] in
/--
Polynomial binding for every used fixed column supplies selector and fixed/table
semantics. This lemma is independent of decoded-member provenance; callers choose
the exceptional event carried by `binding`.
-/
def topLevelFixedConstraints_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp))
    {Bad : Type}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ⊕'
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0) ⊕' Bad :=
  bindOrRelationWitness
    (boundedForallOrRelationWitness (n := top.pinnedCS.numFixedColumns) binding)
    fun hbinding => by
    let environment :=
      resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    have fixedRead :
        ∀ {column row value},
          (column, row, value) ∈
              topLevelRequiredFixedEntries top →
            environment.fixed ⟨column⟩ (row : ℤ) = (value : Fp) := by
      intro column row value hentry
      exact
        topLevelFixedEntryRead_of_column
          poly rows hrows hn realizes proofIndex hentry
          (hbinding column (realizes column row value hentry).2.1)
    change
      SelectorActivationsRealized
          top.selectorMap top.selectorActivations environment ∧
        CircuitConstraintFamily.constraints .fixed
          (Layout.place top.regionStarts) environment
          (top.operations) 0
    constructor
    · apply selectorActivationsRealized_of_selectorFixed
      intro column row value hentry
      apply fixedRead
      change (column, row, value) ∈ topLevelSelectorEntries top at hentry
      simp [topLevelRequiredFixedEntries, hentry]
    · exact FixedLayout.constraints_of_entries
        top.regionStarts (top.usableRowsAt top.domainExponent)
        (top.operations) 0 environment rfl
        (fun column row value hentry => fixedRead (by
          change
            (column, row, value) ∈ topLevelFixedOperationEntries top at hentry
          simp [topLevelRequiredFixedEntries, hentry]))

namespace CanonicalMemberConstraintRelation

variable
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : CPoly} {deg : ℕ}

/-- Commitment identities absent from the assembled verifier queries resolve to
the zero polynomial. -/
theorem polynomial_eq_zero_of_not_assembled
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (id : CommitmentId)
    (habsent :
      ¬ ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
          q.commId = id) :
    relation.polynomial id = 0 := by
  unfold CanonicalMemberConstraintRelation.polynomial
  have hnone : relation.route id = none := by
    unfold CanonicalMemberConstraintRelation.route
    unfold assembledQueryMemberRoute
    simp only
    split
    · rfl
    · rename_i q hfind
      exfalso
      apply habsent
      refine ⟨q, List.mem_of_find?_eq_some hfind, ?_⟩
      simpa using List.find?_some hfind
  unfold decodedPolynomialResolver
  rw [hnone]

/--
A canonically routed fixed-column opening is the polynomial interpolating its
keygen rows, or it exhibits an augmented commitment relation.

`hcommit` is the circuit-keygen side of the boundary: the fixed commitment stored
in the derived VK is the Lagrange commitment to `rows` with Halo 2's default blind
`1`. It is independent of the proof and can be established once for the generic
`TopLevelCircuit.toVerifierKey` construction.
-/
def fixedColumn_eq_rowPolynomial_or_relation
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (column : ℕ)
    (key : LagrangeCommitmentKey urs vk.omega)
    (rows : List Fp)
    (hcommit :
      vk.fixedCommitment column =
        key.commitInstance rows 1)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .fixedCol column) :
    relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega rows ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hsome : (relation.route (.fixedCol column)).isSome := by
    obtain ⟨q, hq, hqid⟩ := hquery
    have routed := assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment) vk ps ch relation.groupingCount
      relation.noDuplicateQueries q hq
    unfold CanonicalMemberConstraintRelation.route
    rw [← hqid, routed.route_eq]
    rfl
  let slot := (relation.route (.fixedCol column)).get hsome
  have routedFixed :
      relation.route (.fixedCol column) = some slot := (Option.some_get hsome).symm
  have hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD
          (slot.memberIndex : ℕ) .vanishingH =
        .fixedCol column := by
    apply assembledQueryMemberRoute_id
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries
      (.fixedCol column) slot
    simpa [CanonicalMemberConstraintRelation.route] using routedFixed
  have href :=
    deployedMemberRef_eq_fixedCommitment
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount slot column hid
  let decoded :=
    memberDecode slot.setIndex slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols slot.memberIndex) +
          decoded.uComp slot.memberIndex • urs.u +
          decoded.wComp slot.memberIndex • urs.w =
        key.commitInstance rows 1 := by
    calc
      commit urs (decoded.cols slot.memberIndex) +
            decoded.uComp slot.memberIndex • urs.u +
            decoded.wComp slot.memberIndex • urs.w =
          ((deployedSetQueries
              (instanceCommitment := instanceCommitment)
              vk ps ch slot.setIndex).getD
            (slot.memberIndex : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ :=
        decoded.commitment slot.memberIndex
      _ = vk.fixedCommitment column := by
        rw [href]
        rfl
      _ = key.commitInstance rows 1 := hcommit
  have hbound :=
    coeffsToPoly_eq_instanceRowPolynomial_or_relation
      key rows 1
      (decoded.cols slot.memberIndex)
      (decoded.uComp slot.memberIndex)
      (decoded.wComp slot.memberIndex)
      hrows hopen
  refine bindOrRelationWitness hbound fun heq => ?_
  rw [CanonicalMemberConstraintRelation.polynomial,
    decodedPolynomialResolver, routedFixed]
  exact heq

/--
All fixed-column resolver polynomials encode the circuit's complete dense fixed
rows, or commitment binding has produced the shared nontrivial relation.

In-range columns use the circuit-derived fixed commitments. Out-of-range
identities are absent from the bounded fixed-query layout, so both the resolver
polynomial and the circuit's `getD` row vector are zero.
-/
def fixedColumns_eq_rowPolynomials_or_relation
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (numFixedColumns : ℕ)
    (rows : List (List Fp))
    (rowsLength : rows.length = numFixedColumns)
    (key : LagrangeCommitmentKey urs vk.omega)
    (commitment : ∀ column,
      column < numFixedColumns →
        vk.fixedCommitment column =
          key.commitInstance (rows.getD column []) 1)
    (fixedQueryCount :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (queryLayout : ∀ column,
      column < numFixedColumns →
        ∃ rotation, (column, rotation) ∈ vk.fixedQueryLayout)
    (queryLayoutBounded : ∀ column rotation,
      (column, rotation) ∈ vk.fixedQueryLayout →
        column < numFixedColumns)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        vk.omega ^ (i : ℕ)) :
    (∀ column,
      relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k)
          vk.omega (rows.getD column [])) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  bindOrRelationWitness
    (boundedForallOrRelationWitness (n := numFixedColumns) fun column hcolumn =>
      relation.fixedColumn_eq_rowPolynomial_or_relation
        column key (rows.getD column [])
        (commitment column hcolumn) hrows
        (by
          obtain ⟨rotation, hlayout⟩ :=
            queryLayout column hcolumn
          exact fixedQuery_of_layout
            vk instanceCommitment ps ch
            column rotation fixedQueryCount hlayout))
    fun hinrange => by
    intro column
    by_cases hcolumn : column < numFixedColumns
    · exact hinrange column hcolumn
    · have habsent :
          ¬ ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
              q.commId = .fixedCol column := by
        rintro ⟨q, hq, hqid⟩
        obtain ⟨rotation, hlayout⟩ :=
          fixedLayout_of_assembledQuery
            vk instanceCommitment ps ch q hq column hqid
        exact hcolumn
          (queryLayoutBounded column rotation hlayout)
      rw [relation.polynomial_eq_zero_of_not_assembled
        (.fixedCol column) habsent]
      have hrowsDefault : rows.getD column [] = [] := by
        apply List.getD_eq_default
        rw [rowsLength]
        exact Nat.le_of_not_gt hcolumn
      rw [hrowsDefault]
      simp [instanceRowPolynomial, zeroPaddedRows, rowPolynomial]

/--
Circuit-derived fixed rows discharge both consumers of fixed-column semantics:
packed selector activations and explicit fixed/table operations. Commitment binding
is retained as an explicit alternative.
-/
def topLevelFixedConstraints_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams}
    {urs : URS G}
    {hk : (pp.mergeDerived top).k = urs.k}
    {vk : VerifyingKey (pp.mergeDerived top) Fp G}
    {instanceCommitment :
      Fin (pp.mergeDerived top).numProofs → ℕ → G}
    {ps : ProofString (pp.mergeDerived top) Fp G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : CPoly}
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk instanceCommitment ps ch pU pW a
        batchOpenings memberDecode hblinding y hpoly vk.n)
    (hvk : vk = top.toVerifierKey pp urs)
    (coherence : TopLevelFixedCoherence top pp urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst vk
  apply topLevelFixedConstraints_or_bad
    relation.polynomial
      (fun column => top.fixedRows.getD column [])
      hrows hn coherence.realizes
  · intro column hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      column coherence.key (top.fixedRows.getD column [])
      (coherence.commitment column hcolumn) hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          coherence.queryLayout column hcolumn
        exact fixedQuery_of_layout
          (top.toVerifierKey pp urs) instanceCommitment ps ch
          column rotation coherence.fixedQueryCount hlayout)

/--
Pointwise fixed-cell realization at the canonical decoded-member relation.
Constants replay uses this theorem for the V1-allocated constants cells; selector
and fixed/table family proofs use its bundled sibling above.
-/
def topLevelFixedEntryRead_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams}
    {urs : URS G}
    {hk : (pp.mergeDerived top).k = urs.k}
    {vk : VerifyingKey (pp.mergeDerived top) Fp G}
    {instanceCommitment :
      Fin (pp.mergeDerived top).numProofs → ℕ → G}
    {ps : ProofString (pp.mergeDerived top) Fp G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : CPoly}
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk instanceCommitment ps ch pU pW a
        batchOpenings memberDecode hblinding y hpoly vk.n)
    (hvk : vk = top.toVerifierKey pp urs)
    (coherence : TopLevelFixedCoherence top pp urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey pp urs) relation.polynomial proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = (value : Fp) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst vk
  apply topLevelFixedEntryRead_or_bad
    relation.polynomial
      (fun column => top.fixedRows.getD column [])
      hrows hn coherence.realizes
  · intro fixedColumn hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      fixedColumn coherence.key (top.fixedRows.getD fixedColumn [])
      (coherence.commitment fixedColumn hcolumn) hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          coherence.queryLayout fixedColumn hcolumn
        exact fixedQuery_of_layout
          (top.toVerifierKey pp urs) instanceCommitment ps ch
          fixedColumn rotation coherence.fixedQueryCount hlayout)
  · exact hentry

end CanonicalMemberConstraintRelation

end Zcash.Snark

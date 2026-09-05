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

open Zcash.Arithmetic (derivedUrsGLagrange derivedUrsGLagrange_length omegaOf)
open Halo2 CompPoly.CPolynomial
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

omit [AddCommGroup G] [Module Fp G] [DecidableEq G] in
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

omit [Module Fp G] [DecidableEq G] in
/-- A circuit-owned fixed-query layout entry is assembled by the verifier for
the circuit-derived key. -/
theorem topLevelFixedQuery_of_layout
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (pp : ProofParams)
    (instanceCommitment : Fin pp.numProofs → ℕ → G)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.shape.k Fp)
    (column : ℕ) (rotation : ℤ)
    (hlayout : (column, rotation) ∈ top.fixedQueryLayout) :
    ∃ q ∈ assembleQueries (top.toVerifierKey urs)
        instanceCommitment ps ch,
      q.commId = .fixedCol column := by
  apply fixedQuery_of_layout
    (shape := top.shape.withProofParams pp)
    (top.toVerifierKey urs) instanceCommitment ps ch column rotation
  · simpa only [top.shape_numFixedQueries] using
      top.toVerifierKey_fixedQueryCount urs
  · simpa only [top.toVerifierKey_fixedQueryLayout] using hlayout

omit [AddCommGroup G] [Module Fp G] [DecidableEq G] in
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

omit [Module Fp G] [DecidableEq G] in
/-- A fixed-column query assembled for a circuit-derived key comes from that
circuit's fixed-query layout. -/
theorem topLevelFixedLayout_of_assembledQuery
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (pp : ProofParams)
    (instanceCommitment : Fin pp.numProofs → ℕ → G)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.shape.k Fp)
    (q : VerifierQuery top.shape.k Fp G)
    (hq : q ∈ assembleQueries (top.toVerifierKey urs)
      instanceCommitment ps ch)
    (column : ℕ) (hid : q.commId = .fixedCol column) :
    ∃ rotation, (column, rotation) ∈ top.fixedQueryLayout := by
  obtain ⟨rotation, hlayout⟩ :=
    fixedLayout_of_assembledQuery
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey urs) instanceCommitment ps ch q hq column hid
  exact ⟨rotation, by
    simpa only [top.toVerifierKey_fixedQueryLayout] using hlayout⟩

/-- Sparse table and region-local fixed assignments emitted by top-level keygen. -/
def topLevelFixedOperationEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (Layout.FixedAssignment Fp) :=
  Layout.tableAssignments
      (top.usableRowsAt top.domainExponent) top.operations ++
    Layout.regionAssignments top.regionStarts
      (indexedRegions top.operations 0).1

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
    List (Layout.FixedAssignment Fp) :=
  Layout.selectorAssignments top.selectorMap top.selectorActivations

/-- Fixed cells allocated for `constrainConstant` values by the V1 floor planner. -/
def topLevelConstantEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (Layout.FixedAssignment Fp) :=
  Layout.constantAssignments
    (FloorPlanner.V1.constantAssignments top.operations
      (top.constraintSystem.constants.map (·.index)))

/-- The canonical ordered stream of every fixed write emitted by top-level keygen. -/
def topLevelCompilerFixedEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (Layout.FixedAssignment Fp) :=
  Layout.rawAssignments
    (top.usableRowsAt top.domainExponent)
    top.selectorMap top.constraintSystem top.operations

theorem mem_topLevelCompilerFixedEntries_of_operation
    (top : TopLevelCircuit Fp Config PublicInput)
    {assignment : Layout.FixedAssignment Fp}
    (hassignment : assignment ∈ topLevelFixedOperationEntries top) :
    assignment ∈ topLevelCompilerFixedEntries top := by
  simp only [topLevelFixedOperationEntries, topLevelCompilerFixedEntries,
    Layout.rawAssignments, List.mem_append] at hassignment ⊢
  aesop

theorem mem_topLevelCompilerFixedEntries_of_constant
    (top : TopLevelCircuit Fp Config PublicInput)
    {assignment : Layout.FixedAssignment Fp}
    (hassignment : assignment ∈ topLevelConstantEntries top) :
    assignment ∈ topLevelCompilerFixedEntries top := by
  simp only [topLevelConstantEntries, topLevelCompilerFixedEntries,
    Layout.rawAssignments, List.mem_append] at hassignment ⊢
  aesop

theorem mem_topLevelCompilerFixedEntries_of_selector
    (top : TopLevelCircuit Fp Config PublicInput)
    {assignment : Layout.FixedAssignment Fp}
    (hassignment : assignment ∈ topLevelSelectorEntries top) :
    assignment ∈ topLevelCompilerFixedEntries top := by
  simpa only [topLevelSelectorEntries, topLevelCompilerFixedEntries,
    Layout.rawAssignments, List.mem_append] using Or.inl (Or.inr hassignment)

/-- Every compiler-emitted fixed cell consumed by the semantic bridge. -/
def topLevelRequiredFixedEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (Layout.FixedAssignment Fp) :=
  topLevelCompilerFixedEntries top

/-- Compiler-emitted fixed assignments are generically in bounds and realized by the
top-level circuit's canonical dense fixed rows. -/
theorem topLevelCompilerFixedEntry_realized
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : Layout.FixedAssignment Fp)
    (hassignment : assignment ∈ topLevelCompilerFixedEntries top) :
    assignment.2.1 < top.n ∧
      assignment.1 < top.fixedColumnCount ∧
      (top.fixedRows.getD assignment.1 []).getD assignment.2.1 0 =
        assignment.2.2 := by
  have hbounds := top.fixedAssignment_bounds_of_mem_raw assignment hassignment
  exact ⟨hbounds.2, hbounds.1,
    top.fixedRows_getD_getD_eq_of_mem_raw assignment hassignment⟩

/-- Every required fixed entry is realized by the canonical dense compiler output. -/
theorem topLevelRequiredFixedEntry_realized
    (top : TopLevelCircuit Fp Config PublicInput)
    (assignment : Layout.FixedAssignment Fp)
    (hassignment : assignment ∈ topLevelRequiredFixedEntries top) :
    assignment.2.1 < top.n ∧
      assignment.1 < top.fixedColumnCount ∧
      (top.fixedRows.getD assignment.1 []).getD assignment.2.1 0 =
        assignment.2.2 :=
  topLevelCompilerFixedEntry_realized top assignment hassignment

/--
The fixed-row part of a top-level circuit's keygen boundary.

The canonical Lagrange commitment key agrees with every circuit-derived fixed row.
Fixed-row realization, query coverage, and bounds follow generically from the
top-level compiler.
-/
def TopLevelFixedCoherence
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) : Prop :=
  ∀ column, column < top.fixedColumnCount →
    (top.fixedCommitments urs).getD column 0 =
      (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
        (top.fixedRows.getD column []) 1

namespace TopLevelFixedCoherence

omit [DecidableEq G] in
/-- The circuit-derived VK's fixed commitment at one in-range column is the
full-list commitment of the corresponding keygen row vector. -/
theorem fixedCommitment_eq_commitInstance
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial top.omega
            (Pi.single i (1 : Fp)))))
    (column : ℕ) (hcolumn : column < top.fixedColumnCount) :
    (top.fixedCommitments urs).getD column 0 =
      (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
          (top.fixedRows.getD column []) 1 := by
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
  rw [show LagrangeCommitmentKey.canonical urs top.omega =
      LagrangeCommitmentKey.ofFullList
        urs top.omega (derivedUrsGLagrange urs) hgenerators from
    Subsingleton.elim _ _]
  apply Keygen.commitLagrangeFastWith_eq_ofFullList_commitInstance
    urs top.omega hlen hgenerators
  rw [top.fixedRows_getD_length column hcolumn]
  simp only [TopLevelCircuit.n, hk]

/-- Construct fixed coherence from the derived Lagrange basis of any top-level
circuit whose domain is supported by the Pasta field. -/
def ofDerived
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hdomainExponent : top.domainExponent < 33) :
    TopLevelFixedCoherence top urs := by
  have hkUrs : urs.k ≤ 32 := by
    rw [← hk]
    exact Nat.le_of_lt_succ hdomainExponent
  have homega : top.omega = omegaOf urs.k := by
    simp only [TopLevelCircuit.omega, hk]
  apply fixedCommitment_eq_commitInstance top urs hk
    (derivedUrsGLagrange_length urs)
  intro i
  simpa only [homega] using
    Keygen.ofPrefix_setup_of_closed urs hkUrs
      (Keygen.derivedUrsGLagrange_generator_eq urs hkUrs) i
      (by
        rw [derivedUrsGLagrange_length]
        exact i.isLt)

end TopLevelFixedCoherence

omit [AddCommGroup G] [Inhabited G] [Module Fp G] [DecidableEq G] in
/--
Binding every fixed-column resolver polynomial to the circuit's dense keygen rows
supplies the exact fixed-column encoding expected by `TopLevelAssignment`.
-/
theorem topLevelFixedColumnEncoding_of_binding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {numProofs : ℕ} {proofIndex : Fin numProofs}
    (assignment :
      TopLevelAssignment top numProofs proofIndex)
    (hrows : Function.Injective
      fun row : Fin top.n =>
        top.omega ^ (row : ℕ))
    (hroot :
      top.omega ^
        top.n = 1)
    (binding : ∀ column,
      assignment.polynomial (.fixedCol column) =
        instanceRowPolynomial top.n
          top.omega
          (top.fixedRows.getD column [])) :
    assignment.FixedColumnEncoding := by
  intro column row
  rw [binding column.index]
  let domainRow : Fin top.n :=
    ⟨row.natMod top.n,
      Int.natMod_lt top.n_ne_zero⟩
  have hpow :
      top.omega ^ row =
        top.omega ^ (domainRow : ℕ) := by
    simpa only [domainRow] using
      zpow_eq_pow_natMod
        top.omega
        top.n top.n_pos hroot row
  rw [hpow]
  have heval :=
    instanceRowPolynomial_eval
      (values := top.fixedRows.getD column.index [])
      hrows domainRow
  change
    (instanceRowPolynomial top.n
      top.omega
      (top.fixedRows.getD column.index [])).eval
        (top.omega ^ (domainRow : ℕ)) =
      (top.fixedRows.getD column.index []).getD
        (row.natMod top.n) 0
  simpa only [domainRow] using heval

omit [Module Fp G] [DecidableEq G] in
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
    {pp : ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        top.omega ^ (i : ℕ))
    (hn : top.n = 2 ^ urs.k)
    (proofIndex : Fin pp.numProofs)
    {column row : ℕ} {value : Fp}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top)
    (hpolyEq : poly (.fixedCol column) =
      instanceRowPolynomial (2 ^ urs.k)
        top.omega (top.fixedRows.getD column [])) :
    (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = value := by
  obtain ⟨hrow, hcolumn, hvalue⟩ :=
    topLevelRequiredFixedEntry_realized top (column, row, value) hentry
  have hrow' : row < 2 ^ urs.k := by
    rwa [← hn]
  rw [resolverEnvironment_fixed, hpolyEq]
  simpa using
    (instanceRowPolynomial_eval hrows
      ⟨row, hrow'⟩).trans hvalue

omit [Module Fp G] [DecidableEq G] in
/--
The same entry read, carrying the caller's shared exceptional branch as data: either the entry
reads back, or the binding family has computed a break at this entry's column.
-/
def topLevelFixedEntryRead_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        top.omega ^ (i : ℕ))
    (hn : top.n = 2 ^ urs.k)
    {Bad : Type}
    (binding : ∀ column,
      column < top.fixedColumnCount →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              top.omega (top.fixedRows.getD column []) ⊕'
          Bad)
    (proofIndex : Fin pp.numProofs)
    {column row : ℕ} {value : Fp}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = value ⊕'
      Bad :=
  bindOrRelationWitness
    (binding column
      (topLevelRequiredFixedEntry_realized top (column, row, value) hentry).2.1)
    (topLevelFixedEntryRead_of_column poly hrows hn proofIndex hentry)

omit [Module Fp G] [DecidableEq G] in
/--
Polynomial binding for every used fixed column supplies selector and fixed/table
semantics. This lemma is independent of decoded-member provenance; callers choose
the exceptional event carried by `binding`.
-/
def topLevelFixedConstraints_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        top.omega ^ (i : ℕ))
    (hn : top.n = 2 ^ urs.k)
    {Bad : Type}
    (binding : ∀ column,
      column < top.fixedColumnCount →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              top.omega (top.fixedRows.getD column []) ⊕'
          Bad)
    (proofIndex : Fin pp.numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0) ⊕' Bad :=
  bindOrRelationWitness
    (boundedForallOrRelationWitness (n := top.fixedColumnCount) binding)
    fun hbinding => by
    let environment :=
      resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    have fixedRead :
        ∀ {column row value},
          (column, row, value) ∈
              topLevelRequiredFixedEntries top →
            environment.fixed ⟨column⟩ (row : ℤ) = value := by
      intro column row value hentry
      exact
        topLevelFixedEntryRead_of_column
          poly hrows hn proofIndex hentry
          (hbinding column
            (topLevelRequiredFixedEntry_realized
              top (column, row, value) hentry).2.1)
    change
      SelectorActivationsRealized
          top.selectorMap top.selectorActivations environment ∧
        CircuitConstraintFamily.constraints .fixed
          (Layout.place top.regionStarts) environment
          (top.operations) 0
    constructor
    · apply selectorActivationsRealized_of_selectorAssignments
      intro assignment hentry
      apply fixedRead
      exact mem_topLevelCompilerFixedEntries_of_selector top hentry
    · exact FixedLayout.constraints_of_entries
        top.regionStarts (top.usableRowsAt top.domainExponent)
        (top.operations) 0 environment rfl
        (fun column row value hentry => fixedRead (by
          exact mem_topLevelCompilerFixedEntries_of_operation top hentry))

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
          (shape := shape)
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := shape)
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (shape := shape)
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
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
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
def topLevelFixedColumns_eq_rowPolynomials_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}
    {hk : top.shape.k = urs.k}
    {instanceCommitment : Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.shape.k Fp}
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
    {y : Fp} {hpoly : CPoly} {deg : ℕ}
    (relation : CanonicalMemberConstraintRelation
      (shape := top.shape.withProofParams pp)
      urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs) y hpoly deg)
    (coherence : TopLevelFixedCoherence top urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => top.omega ^ (i : ℕ)) :
    (∀ column,
      relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k)
          top.omega (top.fixedRows.getD column [])) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hrowsVk : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey urs).omega ^ (i : ℕ) := by
    simpa only [top.toVerifierKey_omega] using hrows
  exact
  bindOrRelationWitness
    (boundedForallOrRelationWitness (n := top.fixedColumnCount)
      fun column hcolumn =>
      (by
        have hcommitment :
            (top.toVerifierKey urs).fixedCommitment column =
              (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
                (top.fixedRows.getD column []) 1 := by
          rw [top.toVerifierKey_fixedCommitment]
          exact coherence column hcolumn
        have source :=
          relation.fixedColumn_eq_rowPolynomial_or_relation
            column (LagrangeCommitmentKey.canonical urs top.omega)
            (top.fixedRows.getD column [])
            hcommitment hrowsVk
            (by
              obtain ⟨rotation, hlayout⟩ :=
                top.exists_rotation_mem_fixedQueryLayout_of_lt column hcolumn
              exact topLevelFixedQuery_of_layout top urs pp
                instanceCommitment ps ch column rotation hlayout)
        simpa only [top.toVerifierKey_omega] using source))
    fun hinrange => by
    intro column
    by_cases hcolumn : column < top.fixedColumnCount
    · exact hinrange column hcolumn
    · have habsent :
          ¬ ∃ q ∈ assembleQueries (top.toVerifierKey urs)
              instanceCommitment ps ch,
              q.commId = .fixedCol column := by
        rintro ⟨q, hq, hqid⟩
        obtain ⟨rotation, hlayout⟩ :=
          topLevelFixedLayout_of_assembledQuery
            top urs pp instanceCommitment ps ch q hq column hqid
        exact hcolumn
          (List.forall_iff_forall_mem.mp
            top.fixedQueryLayout_columns_lt _ hlayout)
      rw [relation.polynomial_eq_zero_of_not_assembled
        (.fixedCol column) habsent]
      have hrowsDefault : top.fixedRows.getD column [] = [] := by
        apply List.getD_eq_default
        rw [top.fixedRows_length]
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
    {pp : ProofParams}
    {urs : URS G}
    {hk : top.shape.k = urs.k}
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.shape.k Fp}
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
    (relation :
      CanonicalMemberConstraintRelation
        (shape := top.shape.withProofParams pp)
        urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
        batchOpenings memberDecode
          (top.toVerifierKey_blindingFactors_lt_n urs) y hpoly top.n)
    (coherence : TopLevelFixedCoherence top urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        top.omega ^ (i : ℕ))
    (hn : top.n = 2 ^ urs.k)
    (proofIndex : Fin pp.numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  apply topLevelFixedConstraints_or_bad
    relation.polynomial
      hrows hn
  · intro column hcolumn
    have hcommitment :
        (top.toVerifierKey urs).fixedCommitment column =
          (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
            (top.fixedRows.getD column []) 1 := by
      rw [top.toVerifierKey_fixedCommitment]
      exact coherence column hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      column (LagrangeCommitmentKey.canonical urs top.omega)
      (top.fixedRows.getD column [])
      hcommitment hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          top.exists_rotation_mem_fixedQueryLayout_of_lt column hcolumn
        exact fixedQuery_of_layout
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) instanceCommitment ps ch
          column rotation (top.toVerifierKey_fixedQueryCount urs) hlayout)

/--
Pointwise fixed-cell realization at the canonical decoded-member relation.
Constants replay uses this theorem for the V1-allocated constants cells; selector
and fixed/table family proofs use its bundled sibling above.
-/
def topLevelFixedEntryRead_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams}
    {urs : URS G}
    {hk : top.shape.k = urs.k}
    {instanceCommitment :
      Fin pp.numProofs → ℕ → G}
    {ps : ProofString (top.shape.withProofParams pp) Fp G}
    {ch : Challenges top.shape.k Fp}
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
    (relation :
      CanonicalMemberConstraintRelation
        (shape := top.shape.withProofParams pp)
        urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
        batchOpenings memberDecode
          (top.toVerifierKey_blindingFactors_lt_n urs) y hpoly top.n)
    (coherence : TopLevelFixedCoherence top urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        top.omega ^ (i : ℕ))
    (hn : top.n = 2 ^ urs.k)
    (proofIndex : Fin pp.numProofs)
    {column row : ℕ} {value : Fp}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey urs) relation.polynomial proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = value ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  apply topLevelFixedEntryRead_or_bad
    relation.polynomial
      hrows hn
  · intro fixedColumn hcolumn
    have hcommitment :
        (top.toVerifierKey urs).fixedCommitment fixedColumn =
          (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
            (top.fixedRows.getD fixedColumn []) 1 := by
      rw [top.toVerifierKey_fixedCommitment]
      exact coherence fixedColumn hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      fixedColumn (LagrangeCommitmentKey.canonical urs top.omega)
      (top.fixedRows.getD fixedColumn [])
      hcommitment hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          top.exists_rotation_mem_fixedQueryLayout_of_lt fixedColumn hcolumn
        exact fixedQuery_of_layout
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) instanceCommitment ps ch
          fixedColumn rotation (top.toVerifierKey_fixedQueryCount urs) hlayout)
  · exact hentry

end CanonicalMemberConstraintRelation

end Zcash.Snark

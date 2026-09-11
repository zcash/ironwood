import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Circuits.Halo2.FixedConstraints
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Halo2.SelectorCompression
import Zcash.Circuits.Integration.AssignmentEncoding
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

open Zcash.Arithmetic (omegaOf)

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
    [TopLevelShape top]
    (urs : URS G) (pp : ProofParams)
    (instanceCommitment : Fin pp.numProofs → ℕ → G)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.domainExponent Fp)
    (column : ℕ) (rotation : ℤ)
    (hlayout : (column, rotation) ∈ top.fixedQueryLayout) :
    ∃ q ∈ assembleQueries (top.toVerifierKey urs)
        instanceCommitment ps ch,
      q.commId = .fixedCol column := by
  apply fixedQuery_of_layout
    (shape := top.shape.withProofParams pp)
    (top.toVerifierKey urs) instanceCommitment ps ch column rotation
  · exact top.toVerifierKey_fixedQueryCount urs
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
    [TopLevelShape top]
    (urs : URS G) (pp : ProofParams)
    (instanceCommitment : Fin pp.numProofs → ℕ → G)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.domainExponent Fp)
    (q : VerifierQuery top.domainExponent Fp G)
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

omit [AddCommGroup G] [Inhabited G] [Module Fp G] [DecidableEq G] in
/--
Binding every fixed-column resolver polynomial to the circuit's dense keygen rows
identifies their evaluations with the circuit's compiled fixed values.
-/
theorem topLevelFixedColumnEncoding_of_binding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top] [CircuitFieldSupport top]
    (poly : CommitmentId → CPoly)
    (binding : ∀ column,
      poly (.fixedCol column) =
        instanceRowPolynomial top.n
          top.omega
          (top.fixedRows.getD column [])) :
    top.FixedColumnEncoding poly := by
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
        top.n top.n_pos top.omega_pow_n row
  rw [hpow]
  have heval :=
    instanceRowPolynomial_eval
      (values := top.fixedRows.getD column.index [])
      top.domainRowsInjective domainRow
  rw [top.fixedValue_eq_fixedRows_getD]
  simpa only [domainRow] using heval

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
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}
    {hk : top.domainExponent = urs.k}
    {instanceCommitment : Fin pp.numProofs → ℕ → G}
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
    {y : Fp} {hpoly : CPoly} {deg : ℕ}
    (relation : CanonicalMemberConstraintRelation
      (shape := top.shape.withProofParams pp)
      urs hk (top.toVerifierKey urs) instanceCommitment ps ch pU pW a
      batchOpenings memberDecode
        (top.toVerifierKey_blindingFactors_lt_n urs) y hpoly deg)
    [CircuitFieldSupport top] :
    (∀ column,
      relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k)
          top.omega (top.fixedRows.getD column [])) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hrows := top.domainRowsInjective_of_domainExponent_eq hk
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
          exact top.fixedCommitments_getD_eq_commitInstance urs hk column hcolumn
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

end CanonicalMemberConstraintRelation

end Zcash.Snark

import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.QueryLayouts
import Zcash.Circuits.Integration.TopLevelCorrectness
import Mathlib.Util.AssertNoSorry

/-!
# Generic top-level public-instance commitments

A top-level circuit determines both the instance columns visible to the verifier and
the dense public rows supplied in each column. This module derives the corresponding
commitment family and proves that verifier acceptance binds the circuit's statement
to the supplied public inputs, for any `TopLevelCircuit`.
-/

namespace Halo2.TopLevelCircuit

open Zcash Zcash.Snark Zcash.Snark.Keygen Polynomial

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The canonical Lagrange commitment key for a top-level circuit's instance domain.
Each row generator is the monomial commitment to the corresponding interpolating
basis polynomial.
-/
def instanceCommitmentKey
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    LagrangeCommitmentKey urs (top.toVerifierKey pp urs).omega where
  generators := fun i =>
    commit urs
      (polynomialCoefficients (2 ^ urs.k)
        (rowPolynomial
          (top.toVerifierKey pp urs).omega
          (Pi.single i (1 : Fp))))
  generator_eq := fun _ => rfl

/--
The verifier commitment family determined by a top-level circuit's public-input
layout. It supports arbitrary proof multiplicity and any number of instance columns.
-/
def instanceCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp) :
    Fin numProofs → ℕ → G :=
  fun proofIndex column =>
    (top.instanceCommitmentKey pp urs).commitInstance
      (top.publicInputRows (inputs proofIndex) ⟨column⟩) 1

@[simp] theorem instanceCommitment_column
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp)
    (proofIndex : Fin numProofs) (column : Column .instance) :
    top.instanceCommitment pp urs inputs proofIndex column.index =
      (top.instanceCommitmentKey pp urs).commitInstance
        (top.publicInputRows (inputs proofIndex) column) 1 :=
  rfl

assert_no_sorry instanceCommitment_column

/--
Every public instance-column commitment is the monomial-URS commitment to its
layout-derived row polynomial, with Halo 2's default blind.
-/
theorem instanceCommitment_column_eq_commit
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp)
    (proofIndex : Fin numProofs) (column : Column .instance) :
    top.instanceCommitment pp urs inputs proofIndex column.index =
      commit urs
          (instanceCoefficients (2 ^ urs.k)
            (top.toVerifierKey pp urs).omega
            (top.publicInputRows (inputs proofIndex) column)) +
        urs.w := by
  rw [top.instanceCommitment_column,
    LagrangeCommitmentKey.commitInstance_eq, one_smul]

assert_no_sorry instanceCommitment_column_eq_commit

end Halo2.TopLevelCircuit

namespace Zcash.Snark

open Halo2 Polynomial Keygen

namespace TopLevelInstanceCommitment

variable
    {G : Type} [AddCommGroup G] [Module Fp G]
    [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived top).k = urs.k)
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp)
    (ps : ProofString (pp.mergeDerived top) Fp G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        urs hk (top.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs)
        (top.instanceCommitment pp urs inputs) ps ch)

/--
Verifier acceptance binds one cell's circuit-derived instance column to its
layout-derived row polynomial, or yields the augmented-basis relation.
-/
def acceptedColumn_eq_rowPolynomial_or_relation
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (index : Fin (size PublicInput))
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ)) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts
        (.instanceCol proofIndex
          (top.publicInputLayout.cells index).1.index) =
      instanceRowPolynomial (2 ^ top.domainExponent)
        (Zcash.Arithmetic.omegaOf top.domainExponent)
        (top.publicInputRows (inputs proofIndex)
          (top.publicInputLayout.cells index).1) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let column := (top.publicInputLayout.cells index).1
  have hquery : ∃ q ∈ assembleQueries (top.toVerifierKey pp urs)
      (top.instanceCommitment pp urs inputs) ps ch,
      q.commId = .instanceCol proofIndex column.index := by
    obtain ⟨instanceRotation, hregistered⟩ :=
      top.exists_rotation_mem_instanceQueries_of_publicInputLayout_cell index
    exact instanceQuery_of_layout
      (top.toVerifierKey pp urs) (top.instanceCommitment pp urs inputs) ps ch proofIndex
      column.index instanceRotation (top.toVerifierKey_instanceQueryCount pp urs)
      (QueryLayouts.instanceQueryLayout_of_constraintSystem
        top pp urs column instanceRotation hregistered)
  have hbound :=
    CanonicalMemberConstraintRelation.acceptedInstanceColumn_eq_rowPolynomial_or_relation
      (pU := pU) (pW := pW) (a := a)
      (batchOpenings := batchOpenings)
      (memberDecode := memberDecode)
      haccepts proofIndex column.index
      (top.instanceCommitmentKey pp urs)
      (top.publicInputRows (inputs proofIndex) column) 1
      (top.instanceCommitment_column pp urs inputs proofIndex column)
      hrows
      hquery
  simpa only [← hk, column] using hbound

assert_no_sorry
  acceptedColumn_eq_rowPolynomial_or_relation

/--
Verifier acceptance binds one decoded assignment to the public input supplied for
that proof, or yields the augmented-basis relation.
-/
def publicInputEncoding_or_relation
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (domainExponent_lt : top.domainExponent < 33) :
    (let assignment : TopLevelAssignment top
          (pp.mergeDerived top).numProofs proofIndex :=
        { polynomial :=
            CanonicalMemberConstraintRelation.acceptedPolynomial
              (memberDecode := memberDecode) haccepts };
      assignment.PublicInputEncoding (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let assignment : TopLevelAssignment top
      (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial :=
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts }
  change assignment.PublicInputEncoding (inputs proofIndex) ⊕'
    NontrivialRelation (F := Fp) urs.g urs.u urs.w
  refine bindOrRelationWitness
    (finForallOrRelationWitness fun index =>
      acceptedColumn_eq_rowPolynomial_or_relation
        top pp urs hk inputs ps ch pU pW a batchOpenings
        memberDecode haccepts proofIndex index
        (by
          change Function.Injective
            fun i : Fin (2 ^ urs.k) =>
              Zcash.Arithmetic.omegaOf top.domainExponent ^ (i : ℕ)
          rw [← hk]
          exact Zcash.Arithmetic.omegaOf_powers_injective
            top.domainExponent (by omega)))
    fun hcolumns => ?_
  apply TopLevelAssignment.publicInputEncoding_of_publicInputRowPolynomials
      (assignment := assignment) (inputs proofIndex)
  · exact hcolumns
  · exact Zcash.Arithmetic.omegaOf_powers_injective
      top.domainExponent (by omega)

assert_no_sorry publicInputEncoding_or_relation

/--
Present the generic statement of an accepted top-level circuit at the public inputs
supplied to the verifier.

Acceptance binds every circuit-derived public instance column to its layout-derived
row polynomial, or yields the shared augmented-basis relation. No assumption is made
about proof multiplicity, column count, column indices, or query rotations.
-/
def statements_or_relation_of_accepted_topLevelBundleStatement
    (domainExponent_lt : top.domainExponent < 33)
    (htop :
      TopLevelBundleStatement top pp
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let poly :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  change TopLevelBundleStatement top pp poly at htop
  refine bindOrRelationWitness
    (finForallOrRelationWitness
      (A := fun proofIndex : Fin (pp.mergeDerived top).numProofs =>
        let assignment : TopLevelAssignment top
            (pp.mergeDerived top).numProofs proofIndex :=
          { polynomial := poly }
        assignment.PublicInputEncoding (inputs proofIndex))
      fun proofIndex =>
        publicInputEncoding_or_relation
          top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
          haccepts proofIndex domainExponent_lt)
    fun hencoding =>
      TopLevelBundleStatement.of_publicInputEncoding
        top pp poly inputs hencoding htop

/-- Present retained private witnesses at the public inputs bound by the accepted instance
commitments, preserving a computed relation on binding failure. -/
def witnesses_or_relation_of_accepted_topLevelBundleWitness
    (domainExponent_lt : top.domainExponent < 33)
    (witness : TopLevelBundleWitness top pp
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let poly :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  change TopLevelBundleWitness top pp poly at witness
  refine bindOrRelationWitness
    (finForallOrRelationWitness
      (A := fun proofIndex : Fin (pp.mergeDerived top).numProofs =>
        let assignment : TopLevelAssignment top
            (pp.mergeDerived top).numProofs proofIndex :=
          { polynomial := poly }
        assignment.PublicInputEncoding (inputs proofIndex))
      fun proofIndex =>
        publicInputEncoding_or_relation
          top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
          haccepts proofIndex domainExponent_lt)
    fun hencoding =>
      TopLevelBundleWitness.of_publicInputEncoding
        top pp poly inputs hencoding witness

assert_no_sorry
  statements_or_relation_of_accepted_topLevelBundleStatement
assert_no_sorry
  witnesses_or_relation_of_accepted_topLevelBundleWitness

end TopLevelInstanceCommitment

end Zcash.Snark

import Zcash.Snark.Soundness.Multiopen.InstanceColumns
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelWitness
import Mathlib.Util.AssertNoSorry

set_option maxHeartbeats 20000

/-!
# Generic top-level public-instance commitments

A top-level circuit determines both the instance columns visible to the verifier and
the dense public rows supplied in each column. This module derives the corresponding
commitment family and proves that verifier acceptance binds the circuit's statement
to the supplied public inputs, for any `TopLevelCircuit`.
-/

open Zcash.Arithmetic (omegaOf omegaOf_powers_injective)

namespace Halo2.TopLevelCircuit

open Zcash Zcash.Snark Zcash.Snark.Keygen

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

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
    [TopLevelShape top]
    (urs : URS G) :
    LagrangeCommitmentKey urs (top.toVerifierKey urs).omega where
  generators := fun i =>
    commit urs
      (polynomialCoefficients (2 ^ urs.k)
        (rowPolynomial
          (top.toVerifierKey urs).omega
          (Pi.single i (1 : Fp))))
  generator_eq := fun _ => rfl

/--
The verifier commitment family determined by a top-level circuit's public-input
layout. It supports arbitrary proof multiplicity and any number of instance columns.
-/
def instanceCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp) :
    Fin numProofs → ℕ → G :=
  fun proofIndex column =>
    (top.instanceCommitmentKey urs).commitInstance
      (top.publicInputRows (inputs proofIndex) ⟨column⟩) 1

omit [DecidableEq G] in
@[simp] theorem instanceCommitment_column
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (proofIndex : Fin pp.numProofs) (column : Column .instance) :
    top.instanceCommitment urs inputs proofIndex column.index =
      (top.instanceCommitmentKey urs).commitInstance
        (top.publicInputRows (inputs proofIndex) column) 1 :=
  by
    simp [instanceCommitment]

assert_no_sorry instanceCommitment_column

omit [DecidableEq G] in
/--
Every public instance-column commitment is the monomial-URS commitment to its
layout-derived row polynomial, with Halo 2's default blind.
-/
theorem instanceCommitment_column_eq_commit
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (proofIndex : Fin pp.numProofs) (column : Column .instance) :
    top.instanceCommitment urs inputs proofIndex column.index =
      commit urs
          (instanceCoefficients (2 ^ urs.k)
            top.omega
            (top.publicInputRows (inputs proofIndex) column)) +
        urs.w := by
  rw [top.instanceCommitment_column,
    LagrangeCommitmentKey.commitInstance_eq, one_smul]
  rw [top.toVerifierKey_omega]

assert_no_sorry instanceCommitment_column_eq_commit

end Halo2.TopLevelCircuit

namespace Zcash.Snark

open Halo2 Keygen

namespace TopLevelInstanceCommitment

variable
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.domainExponent Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          urs hk (top.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := top.shape.withProofParams pp)
          (instanceCommitment := top.instanceCommitment urs inputs)
          (top.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := top.shape.withProofParams pp)
        (instanceCommitment := top.instanceCommitment urs inputs)
        urs hk (top.toVerifierKey urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts (top.shape.withProofParams pp) urs hk
        (top.toVerifierKey urs)
        (top.instanceCommitment urs inputs) ps ch)

/--
Verifier acceptance binds one cell's circuit-derived instance column to its
layout-derived row polynomial, or yields the augmented-basis relation.
-/
def acceptedColumn_eq_rowPolynomial_or_relation
    (proofIndex : Fin pp.numProofs)
    (index : Fin (size PublicInput))
    (hrows : Function.Injective
      fun i : Fin (2 ^ top.domainExponent) =>
        top.omega ^ (i : ℕ)) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
          (shape := top.shape.withProofParams pp)
          (memberDecode := memberDecode) haccepts
        (.instanceCol proofIndex
          (top.publicInputLayout.cells index).1.index) =
      instanceRowPolynomial top.n
        (top.omega)
        (top.publicInputRows (inputs proofIndex)
          (top.publicInputLayout.cells index).1) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let column := (top.publicInputLayout.cells index).1
  have hk' : top.domainExponent = urs.k :=
    hk
  have hn : 2 ^ urs.k = 2 ^ top.domainExponent :=
    congrArg (2 ^ ·) hk'.symm
  have hrows' : Function.Injective
      (fun i : Fin (2 ^ urs.k) => top.omega ^ (i : ℕ)) := by
    intro i j hij
    have hcast :
        Fin.cast hn i = Fin.cast hn j :=
      hrows (by simpa only [Fin.val_cast] using hij)
    exact Fin.ext (by
      simpa only [Fin.val_cast] using congrArg Fin.val hcast)
  have hquery : ∃ q ∈ assembleQueries
      (shape := top.shape.withProofParams pp) (top.toVerifierKey urs)
      (top.instanceCommitment urs inputs) ps ch,
      q.commId = .instanceCol proofIndex column.index := by
    obtain ⟨instanceRotation, hregistered⟩ :=
      top.exists_rotation_mem_instanceQueries_of_publicInputLayout_cell index
    have hlayout :
        (column.index, instanceRotation) ∈ top.instanceQueryLayout :=
      top.mem_instanceQueryLayout_of_mem_constraintSystem
        column instanceRotation hregistered
    have hvkLayout :
        (column.index, instanceRotation) ∈
          (top.toVerifierKey urs).instanceQueryLayout := by
      simpa only [top.toVerifierKey_instanceQueryLayout] using hlayout
    exact instanceQuery_of_layout
        (shape := top.shape.withProofParams pp)
        (top.toVerifierKey urs) (top.instanceCommitment urs inputs) ps ch
        proofIndex column.index instanceRotation
        (by
          calc
            (top.toVerifierKey urs).instanceQueryLayout.length =
                top.instanceQueryCount :=
              top.toVerifierKey_instanceQueryCount urs
            _ = (top.shape.withProofParams pp).numInstanceQueries :=
              (top.shape.withProofParams_numInstanceQueries pp).symm)
        hvkLayout
  have hbound :=
    CanonicalMemberConstraintRelation.acceptedInstanceColumn_eq_rowPolynomial_or_relation
      (shape := top.shape.withProofParams pp)
      (pU := pU) (pW := pW) (a := a)
      (batchOpenings := batchOpenings)
      (memberDecode := memberDecode)
      haccepts proofIndex column.index
      (top.instanceCommitmentKey urs)
      (top.publicInputRows (inputs proofIndex) column) 1
      (top.instanceCommitment_column pp urs inputs proofIndex column)
      (by simpa only [top.toVerifierKey_omega] using hrows')
      hquery
  refine bindOrRelationWitness hbound fun heq => ?_
  have hn' : 2 ^ urs.k = top.n :=
    hn.trans top.n_eq_two_pow_domainExponent.symm
  rw [hn', top.toVerifierKey_omega] at heq
  exact heq

assert_no_sorry
  acceptedColumn_eq_rowPolynomial_or_relation

/--
Verifier acceptance binds one decoded assignment to the public input supplied for
that proof, or yields the augmented-basis relation.
-/
def publicInputEncoding_or_relation
    (proofIndex : Fin pp.numProofs)
    [CircuitFieldSupport top] :
    top.PublicInputEncoding
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (shape := top.shape.withProofParams pp)
        (memberDecode := memberDecode) haccepts)
      proofIndex (inputs proofIndex) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  refine bindOrRelationWitness
    (finForallOrRelationWitness fun index =>
      acceptedColumn_eq_rowPolynomial_or_relation
        top pp urs hk inputs ps ch pU pW a batchOpenings
        memberDecode haccepts proofIndex index
        (top.domainRowsInjective))
    fun hcolumns => ?_
  exact top.publicInputEncoding_of_publicInputRowPolynomials _ proofIndex
    (inputs proofIndex) hcolumns

assert_no_sorry publicInputEncoding_or_relation

/-- Present retained private witnesses at the public inputs bound by the accepted instance
commitments, preserving a computed relation on binding failure. -/
def witnesses_or_relation_of_accepted_topLevelBundleWitness
    [CircuitFieldSupport top]
    (witness : TopLevelBundleWitness top pp.numProofs
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (shape := top.shape.withProofParams pp)
        (memberDecode := memberDecode) haccepts)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let poly :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (shape := top.shape.withProofParams pp)
      (memberDecode := memberDecode) haccepts
  refine bindOrRelationWitness
    (finForallOrRelationWitness
      (A := fun proofIndex : Fin pp.numProofs =>
        top.PublicInputEncoding poly proofIndex (inputs proofIndex))
      fun proofIndex =>
        publicInputEncoding_or_relation
          top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
          haccepts proofIndex)
    fun hencoding proofIndex => by
      refine { w := (witness proofIndex).w, satisfied := ?_ }
      rw [← top.extractPublicInput_eq_of_encoding poly proofIndex
        (inputs proofIndex) (hencoding proofIndex)]
      exact (witness proofIndex).satisfied

assert_no_sorry
  witnesses_or_relation_of_accepted_topLevelBundleWitness

end TopLevelInstanceCommitment

end Zcash.Snark

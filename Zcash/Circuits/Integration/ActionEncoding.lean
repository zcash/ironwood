import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.LookupSelectorRows
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.TopLevelCircuit
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.ActionCopyReplay
import Zcash.Circuits.Action.FieldSupport
import Zcash.Snark.Keygen.Pipeline
import Mathlib.Util.AssertNoSorry

/-!
# Action correctness instantiation

This module packages the representation laws needed to instantiate generic
top-level-circuit correctness for the Orchard Action circuit. Public-input encoding
is handled by the generic assignment layer. The generic terminal theorem remains in
`Zcash.Snark.Soundness.Circuit.Terminal`.
-/

open Zcash.Arithmetic (omegaOf pastaDomain)

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open Zcash.Circuits
open Zcash.Circuits.Action
open Keygen

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Package the Action circuit's gate, fixed, copy, and lookup representation laws for
one canonical decoded relation.

This is the Action-specific constructor for the generic top-level soundness
interface.  It does not mention the Action statement or its public-input
presentation.
-/
def actionTopLevelCircuitCorrectness
    (pp : ProofParams) (urs : URS G)
    (hk :
      actionCircuit.domainExponent = urs.k)
    (instanceCommitment :
      Fin pp.numProofs →
        ℕ → G)
    (ps : ProofString
      (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges
      actionCircuit.domainExponent Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          urs hk (actionCircuit.toVerifierKey urs) ps ch)
        (x4BatchEvals
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (shape := actionCircuit.shape.withProofParams pp)
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey urs) ps ch),
      OpenedMemberDecode
        (shape := actionCircuit.shape.withProofParams pp)
        (instanceCommitment := instanceCommitment)
        urs hk (actionCircuit.toVerifierKey urs)
        ps ch batchOpenings i hi)
    (hpoly : CPoly)
    (relation :
      CanonicalMemberConstraintRelation
        (shape := actionCircuit.shape.withProofParams pp)
        urs hk (actionCircuit.toVerifierKey urs)
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        ch.y hpoly
        actionCircuit.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          actionCircuit.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        pp.numProofs (actionCircuit.toVerifierKey urs)
        ch relation.polynomial actionActiveRows)
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        actionCircuit pp urs ch relation.polynomial) :
    TopLevelCircuitCorrectness
      actionCircuit pp urs ch relation.polynomial
      (FlatCell actionNumPermCols actionDomainSize)
      (AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) := by
  classical
  have hdomainExponent :
      actionCircuit.domainExponent = urs.k := by
    exact hk
  have fixedCoherence :
      TopLevelFixedCoherence actionCircuit urs :=
    TopLevelFixedCoherence.ofDerived actionCircuit urs hdomainExponent
      (CircuitFieldSupport.domainExponent_lt actionCircuit pastaDomain)
  have hdomainSize :
      actionCircuit.n = 2 ^ urs.k := by
    rw [actionCircuit.n_eq_two_pow_domainExponent]
    exact congrArg (2 ^ ·) hdomainExponent
  have hfixedRows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (omegaOf actionCircuit.domainExponent) ^
          (i : ℕ) :=
    TopLevelAssignment.domainRowsInjective_of_domainExponent_eq
      (CircuitFieldSupport.domainExponent_lt actionCircuit pastaDomain) hdomainExponent
  refine
    { fixedEncoding := ?_
      fixed := ?_
      copies := ?_
      lookups := ?_ }
  · intro proofIndex
    refine bindOrRelationWitness
      (relation.topLevelFixedColumns_eq_rowPolynomials_or_relation
        fixedCoherence hfixedRows)
      fun hbinding => ?_
    let assignment :
        TopLevelAssignment actionCircuit
          pp.numProofs
          proofIndex :=
      { polynomial := relation.polynomial }
    apply topLevelFixedColumnEncoding_of_binding
      assignment
      (TopLevelAssignment.domainRowsInjective
        (top := actionCircuit)
        (CircuitFieldSupport.domainExponent_lt actionCircuit pastaDomain))
      (TopLevelAssignment.domainRoot
        (top := actionCircuit)
        (CircuitFieldSupport.domainExponent_lt actionCircuit pastaDomain))
    intro column
    simpa only [assignment, hdomainSize] using hbinding column
  · intro proofIndex
    exact relation.topLevelFixedConstraints_or_relation
      fixedCoherence hfixedRows hdomainSize proofIndex
  · intro proofIndex
    simpa only [actionActiveRows] using
      actionCopyReplayWitness_or_relation
        pp urs hk relation hgoodY fixedCoherence
        permutationExclusions proofIndex
  · intro proofIndex
    · have hrows : Function.Injective
          fun i : Fin
              actionCircuit.n =>
            (omegaOf actionCircuit.domainExponent) ^
              (i : ℕ) := by
        rw [hdomainSize]
        exact hfixedRows
      have hroot :
          (omegaOf actionCircuit.domainExponent) ^
            actionCircuit.n = 1 :=
        TopLevelAssignment.domainRoot
          (CircuitFieldSupport.domainExponent_lt actionCircuit pastaDomain)
      have hn : actionCircuit.n ≠ 0 := by
        exact actionCircuit.n_ne_zero
      have hsatisfaction :=
        relation.constraintSatisfaction hn hgoodY
      refine bindOrRelationWitness
        (listForallOrRelationWitness
          (operationEnabledLookups (actionCircuit.operations) 0)
          fun lookup henabled => ?_)
        fun lookupSelectorValues =>
          TopLevelLookup.WitnessConditions.ofChallengeExclusions
            ch relation.polynomial proofIndex
            lookupSelectorValues lookupExclusions
      · have hrow :
            actionCircuit.placement lookup.region + lookup.row <
              actionCircuit.n :=
          by
            exact
              (lookup.activationRow_lt_usableRows henabled).trans_le
                actionCircuit.usableRowsAt_domainExponent_le_n
        have hexact :=
          lookup.inputSelectorLeafRowsExact actionCircuit
            henabled
        have hvalues :=
          lookup.inputSelectorValuesRealized_or_bad
            relation.polynomial
            (fun column =>
              actionCircuit.fixedRows.getD column [])
            hfixedRows hdomainSize
            (Bad :=
              AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
            (fun column hcolumn =>
              relation.fixedColumn_eq_rowPolynomial_or_relation
                column
                (LagrangeCommitmentKey.canonical urs (omegaOf actionCircuit.domainExponent))
                (actionCircuit.fixedRows.getD column [])
                (fixedCoherence column hcolumn)
                hfixedRows
                (by
                  obtain ⟨rotation, hlayout⟩ :=
                    actionCircuit.exists_rotation_mem_fixedQueryLayout_of_lt
                      column hcolumn
                  exact topLevelFixedQuery_of_layout
                    actionCircuit urs pp instanceCommitment ps ch
                    column rotation hlayout))
            proofIndex hrow hexact
        exact hvalues

assert_no_sorry actionTopLevelCircuitCorrectness

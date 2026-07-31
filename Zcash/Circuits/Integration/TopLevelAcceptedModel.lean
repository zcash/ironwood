import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Snark.Soundness.TopLevelTerminal
import Mathlib.Util.AssertNoSorry

/-!
# Generic accepted-model circuit composition

This module turns satisfaction of the canonical model selected by an accepting
verifier run into a top-level circuit's statements at the public inputs supplied
to the verifier. It composes circuit correctness with generic public-instance
commitment binding and preserves computed break witnesses as data.
-/

namespace Zcash.Snark

open Halo2 Polynomial Keygen

namespace TopLevelAcceptedModel

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
Canonical circuit satisfaction and the circuit's named correctness package yield
its statements at the supplied public inputs, or a computed nontrivial relation.
-/
def statements_or_relation_of_circuitSat
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly (top.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).constraints
          (top.toVerifierKey pp urs).n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hn :
      (top.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ top.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
  have htop :=
    topLevelBundleStatement_or_bad_of_constraintSatisfaction
      (top := top) (pp := pp) (urs := urs) (ch := ch)
      (cell := cell) hblinding
      (by simpa only [hpolynomial] using hsatisfaction)
      correctness
  rcases htop with htop | hrelation
  · exact
      TopLevelInstanceCommitment.statements_or_relation_of_accepted_topLevelBundleStatement
        top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
        haccepts correctness.gates.domainExponent_lt htop
  · exact PSum.inr hrelation

/-- Canonical circuit satisfaction retaining each extracted private witness as data. -/
def witnesses_or_relation_of_circuitSat
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly (top.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).constraints
          (top.toVerifierKey pp urs).n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hn :
      (top.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ top.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
  have houtcome :=
    topLevelBundleWitness_or_bad_of_constraintSatisfaction
      (top := top) (pp := pp) (urs := urs) (ch := ch)
      (cell := cell) hblinding
      (by simpa only [hpolynomial] using hsatisfaction)
      correctness
  rcases houtcome with witness | hrelation
  · exact
      TopLevelInstanceCommitment.witnesses_or_relation_of_accepted_topLevelBundleWitness
        top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
        haccepts correctness.gates.domainExponent_lt witness
  · exact PSum.inr hrelation

assert_no_sorry statements_or_relation_of_circuitSat
assert_no_sorry witnesses_or_relation_of_circuitSat

end TopLevelAcceptedModel

end Zcash.Snark

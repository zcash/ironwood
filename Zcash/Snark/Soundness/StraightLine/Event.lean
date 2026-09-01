import Zcash.Snark.Soundness.Composition.StraightLineConstraint
import Zcash.Snark.Soundness.StraightLine.Terminal

/-!
# Straight-line semantic events for any top-level circuit

These predicates connect the circuit-independent straight-line constraint event
to the `Statement` owned by an arbitrary `TopLevelCircuit`. They contain no
circuit-specific correctness argument or numerical budget.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Arithmetic (scalarFieldOrder)

local instance topLevelStraightLineEventInhabitedVesta : Inhabited VestaG := ⟨0⟩

/-- The canonical constraint model accepted at a straight-line run's own decode. -/
abbrev topLevelRunModel
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (basis : AugmentedIndex top.n → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.domainExponent) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi =>
      (straightLineRunDecodeAt (shape := top.shape.withProofParams pp) family static basis O
        (top.toVerifierKey
          (ursOfAugmentedBasis top.domainExponent basis))
        (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
        (hvk basis) (hI basis) h).toMemberDecode (hchar basis O) i hi)
    (hblinding := top.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis top.domainExponent basis))
    (straightLineRunAcceptsAt (shape := top.shape.withProofParams pp) family static basis O
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (hvk basis) (hI basis) h)

/-- The canonical accepted member polynomial at a straight-line run's own decode. -/
abbrev topLevelRunPolynomial
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (basis : AugmentedIndex top.n → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.domainExponent) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi =>
      (straightLineRunDecodeAt (shape := top.shape.withProofParams pp) family static basis O
        (top.toVerifierKey
          (ursOfAugmentedBasis top.domainExponent basis))
        (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
        (hvk basis) (hI basis) h).toMemberDecode (hchar basis O) i hi)
    (straightLineRunAcceptsAt (shape := top.shape.withProofParams pp) family static basis O
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (hvk basis) (hI basis) h)

section ChallengeFailureEvents

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- Runs whose `x` or `y` challenge lands in a top-level terminal exclusion set. -/
def topLevelXYFailureEvent :
    Set ((AugmentedIndex top.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.domainExponent) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).x ∉ szBadSet
        (let model :=
            topLevelRunModel top pp family static inputs hvk hI hchar q.1 q.2 h;
          combineConstraints
            model.fixedCols model.adviceCols model.instanceCols model.gates
            model.sets model.chunks model.lookups
            model.beta model.gamma model.delta model.theta
            (straightLineRunRecord family q.1 q.2).y
            model.chunkLen model.l0 model.lLast model.lBlind -
          topLevelRunPolynomial top pp family static inputs hvk hI hchar q.1 q.2 h
              CommitmentId.vanishingH *
            (X ^ (top.toVerifierKey
              (ursOfAugmentedBasis top.domainExponent q.1)).n - 1))) ∧
      ∀ j, (straightLineRunRecord family q.1 q.2).y ∉ szBadSet
        (foldSplitWitness
          (topLevelRunModel top pp family static inputs hvk hI hchar
            q.1 q.2 h).constraints
          (top.toVerifierKey
            (ursOfAugmentedBasis top.domainExponent q.1)).n j))}

/-- Runs whose `β` challenge lands in a permutation or lookup exclusion set. -/
def topLevelBetaFailureEvent :
    Set ((AugmentedIndex top.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.domainExponent) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).beta ∉
        allResolverPermutationBetaBadSet
          pp.numProofs (top.toVerifierKey
            (ursOfAugmentedBasis top.domainExponent q.1))
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            q.1 q.2 h)
          (top.usableRowsAt top.domainExponent)) ∧
      (straightLineRunRecord family q.1 q.2).beta ∉
        allResolverLookupBetaBadSet
          pp.numProofs
          (top.toVerifierKey
            (ursOfAugmentedBasis top.domainExponent q.1))
          (straightLineRunRecord family q.1 q.2)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            q.1 q.2 h)
          ((top.toVerifierKey
              (ursOfAugmentedBasis top.domainExponent q.1)).n -
            (top.toVerifierKey
              (ursOfAugmentedBasis top.domainExponent q.1)).blindingFactors - 2))}

/-- Runs whose `γ` challenge lands in a permutation or lookup exclusion set. -/
def topLevelGammaFailureEvent :
    Set ((AugmentedIndex top.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.domainExponent) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).gamma ∉
        allResolverPermutationGammaBadSet
          pp.numProofs (top.toVerifierKey
            (ursOfAugmentedBasis top.domainExponent q.1))
          (straightLineRunRecord family q.1 q.2)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            q.1 q.2 h)
          (top.usableRowsAt top.domainExponent)) ∧
      (straightLineRunRecord family q.1 q.2).gamma ∉
        allResolverLookupGammaBadSet
          pp.numProofs
          (top.toVerifierKey
            (ursOfAugmentedBasis top.domainExponent q.1))
          (straightLineRunRecord family q.1 q.2)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            q.1 q.2 h)
          ((top.toVerifierKey
              (ursOfAugmentedBasis top.domainExponent q.1)).n -
            (top.toVerifierKey
              (ursOfAugmentedBasis top.domainExponent q.1)).blindingFactors - 2))}

/-- Runs whose `θ` challenge lands in a top-level lookup exclusion set. -/
def topLevelThetaFailureEvent :
    Set ((AugmentedIndex top.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.domainExponent) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬((straightLineRunRecord family q.1 q.2).theta ∉
      TopLevelLookup.thetaBadSet top pp
        (ursOfAugmentedBasis top.domainExponent q.1)
        (topLevelRunPolynomial top pp family static inputs hvk hI hchar
          q.1 q.2 h))}

end ChallengeFailureEvents

/--
A computed finder covers the top-level terminal when it returns explicit
relation coefficients on every decoded run outside the challenge-failure
events whose circuit statement is false.
-/
def topLevelTerminalRelationFinderCovers
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.domainExponent basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (finder :
      (basis : AugmentedIndex top.n → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.domainExponent) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) : Prop :=
  ∀ basis O,
    family.straightLineConstraintDecoded static basis O →
    (basis, O) ∉
      topLevelXYFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelBetaFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelGammaFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelThetaFailureEvent top pp family static inputs hvk hI hchar →
    (¬∀ proofIndex, top.Statement (inputs proofIndex)) →
    (finder basis O).isSome

/-- The exact semantic target: the circuit statement holds for every bundled proof. -/
def topLevelBundleStatementDecoded
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInput Fp) :
    (AugmentedIndex top.n → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.domainExponent) → Fp) → Prop :=
  fun _ _ => ∀ proofIndex, top.Statement (inputs proofIndex)

/-- Runs on which an executable terminal finder returns relation coefficients. -/
def straightLineTerminalRelationEvent
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (finder :
      (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)) :=
  {q | (finder q.1 q.2).isSome}

end Zcash.Snark

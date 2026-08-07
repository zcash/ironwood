import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge
import Zcash.Snark.Soundness.Composition.AssembleGroupCost

/-!
# Adaptive-statement finite-security profile

This module records the four-stage price for the executable adaptive-statement relation finder and
knowledge-failure theorem, defines the direct-decode work quantity, and transfers events across the
Orchard generator random-oracle setup.  Each run view retains one adversary output and materialized
challenge vectors; the combined finder short-circuits after its first relation. The certified
capstone derives its direct-decode bound from the family's structural source-length cap; the older
compatibility profile below retains its explicit premise.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementProfileVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Independently charged traversals of the four-stage combined relation finder. -/
def adaptiveStatementDlogTraversalSlots : Nat := 4

@[simp] theorem adaptiveStatementDlogTraversalSlots_eq_four :
    adaptiveStatementDlogTraversalSlots = 4 := rfl

/-- Exact traversal count returned by the same execution as the relation result. -/
def relationFinderCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  (family.relationFinderWithCalls hchar basis O).2

theorem relationFinderCalls_le_traversalSlots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.relationFinderCalls hchar basis O ≤ adaptiveStatementDlogTraversalSlots := by
  unfold relationFinderCalls relationFinderWithCalls adaptiveStatementDlogTraversalSlots
  split <;> try omega
  split <;> try omega
  split <;> omega

/-- Length of the exact represented-point source traversed by direct-coordinate decoding. -/
def adaptiveStatementDirectDecodeSourceLength {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  let output := family.runOutput basis O
  (output.proofData.algebraicProof.preX1AssemblySource
    (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
      family.fixedRepresentations basis)).length

/-- Direct-coordinate work of the actual selected-statement deployed-root decode. -/
def adaptiveStatementDirectDecodeOps {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  let output := family.runOutput basis O
  deployedDirectDecodeOps (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O)
    (adaptiveStatementDirectDecodeSourceLength family basis O)

/-- The relation finder may construct the direct batches in both its identity and terminal
stages. -/
def adaptiveStatementDlogDirectDecodeSlots : Nat := 2

/-- If the relation finder returns no relation, knowledge extraction constructs the same direct
batches once more to return the selected-statement witness. -/
def adaptiveStatementKnowledgeExtractorDirectDecodeSlots : Nat := 3

/-- Conservative random-oracle work for the combined finder, charging all four stages. -/
def adaptiveStatementDlogRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementDlogTraversalSlots * family.Q +
    adaptiveStatementDlogTraversalSlots * (11 + (AdaptiveActionStatementShape pp).k)

/-- Table-specific query envelope using the traversal count returned by that finder execution. -/
def adaptiveStatementDlogRandomOracleQueriesAt {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  family.relationFinderCalls hchar basis O * family.Q +
    family.relationFinderCalls hchar basis O *
      (11 + (AdaptiveActionStatementShape pp).k)

/-- The exact-stage query envelope fits the conservative four-traversal profile. -/
theorem adaptiveStatementDlogRandomOracleQueriesAt_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    adaptiveStatementDlogRandomOracleQueriesAt family hchar basis O ≤
      adaptiveStatementDlogRandomOracleQueries family := by
  unfold adaptiveStatementDlogRandomOracleQueriesAt adaptiveStatementDlogRandomOracleQueries
  exact Nat.add_le_add
    (Nat.mul_le_mul_right family.Q (family.relationFinderCalls_le_traversalSlots hchar basis O))
    (Nat.mul_le_mul_right (11 + (AdaptiveActionStatementShape pp).k)
      (family.relationFinderCalls_le_traversalSlots hchar basis O))

/-- Knowledge extraction reruns the complete terminal once after the four-stage relation finder
returns no relation, for a total of five independently charged traversals. -/
def adaptiveStatementKnowledgeExtractorTraversalSlots : Nat := 5

/-- Random-oracle work of the executable witness extractor. -/
def adaptiveStatementKnowledgeExtractorRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementKnowledgeExtractorTraversalSlots * family.Q +
    adaptiveStatementKnowledgeExtractorTraversalSlots *
      (11 + (AdaptiveActionStatementShape pp).k)

/-- Table-specific extractor envelope: the counted finder execution plus one retained extraction
view. -/
def adaptiveStatementKnowledgeExtractorRandomOracleQueriesAt {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  (family.relationFinderCalls hchar basis O + 1) * family.Q +
    (family.relationFinderCalls hchar basis O + 1) *
      (11 + (AdaptiveActionStatementShape pp).k)

theorem adaptiveStatementKnowledgeExtractorRandomOracleQueriesAt_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    adaptiveStatementKnowledgeExtractorRandomOracleQueriesAt family hchar basis O ≤
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family := by
  unfold adaptiveStatementKnowledgeExtractorRandomOracleQueriesAt
    adaptiveStatementKnowledgeExtractorRandomOracleQueries
    adaptiveStatementKnowledgeExtractorTraversalSlots
  have hcalls := family.relationFinderCalls_le_traversalSlots hchar basis O
  rw [adaptiveStatementDlogTraversalSlots_eq_four] at hcalls
  exact Nat.add_le_add
    (Nat.mul_le_mul_right family.Q (by omega))
    (Nat.mul_le_mul_right (11 + (AdaptiveActionStatementShape pp).k) (by omega))

theorem adaptiveStatementDlogRandomOracleQueries_le_knowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    adaptiveStatementDlogRandomOracleQueries family ≤
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family := by
  unfold adaptiveStatementDlogRandomOracleQueries
    adaptiveStatementKnowledgeExtractorRandomOracleQueries
    adaptiveStatementKnowledgeExtractorTraversalSlots adaptiveStatementDlogTraversalSlots
  omega

/-- Group-work envelope for the four charged traversals and one relation reduction. -/
def adaptiveStatementDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  4 * proverGroupWork + reductionGroupWork

/-- Group-work envelope of witness extraction's five traversals and relation post-processing. -/
def adaptiveStatementKnowledgeExtractorGroupWork
    (proverGroupWork reductionGroupWork : Nat) : Nat :=
  5 * proverGroupWork + reductionGroupWork

/-- Shape-derived envelope for the reduction's currently costed group-operation components:
programming one
augmented-basis slot per index (`scalarBasis`, `2 ^ k + 2` scalar multiplications) plus, per
extractor traversal, one acceptance-assembly evaluation (`assembleGroupOpsBudget`) and one
stage-local commitment evaluation over the basis.  This is not a cost semantics for the complete
finder; uninstrumented group checks remain covered by the profile's declared
`reductionGroupWork`. -/
def adaptiveStatementCostedGroupOpsBudget (pp : ProofParams) : Nat :=
  (2 ^ (AdaptiveActionStatementShape pp).k + 2) +
    adaptiveStatementKnowledgeExtractorTraversalSlots *
      (assembleGroupOpsBudget (AdaptiveActionStatementShape pp) +
        (2 ^ (AdaptiveActionStatementShape pp).k + 2))

/-- Per-run count of the costed assembly/basis components at the selected statement. -/
def adaptiveStatementCostedGroupOpsAt {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  (2 ^ (AdaptiveActionStatementShape pp).k + 2) +
    adaptiveStatementKnowledgeExtractorTraversalSlots *
      (deployedAssembleGroupOps (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runRecord basis O) +
        (2 ^ (AdaptiveActionStatementShape pp).k + 2))

/-- **The costed acceptance-assembly and basis components fit the shape formula.**  This theorem
does not claim to count every group operation executed by the finder. -/
theorem adaptiveStatementCostedGroupOpsAt_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    adaptiveStatementCostedGroupOpsAt family basis O ≤
      adaptiveStatementCostedGroupOpsBudget pp := by
  unfold adaptiveStatementCostedGroupOpsAt adaptiveStatementCostedGroupOpsBudget
  have h := deployedAssembleGroupOps_le (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right h _)) _

/-- Finite-security premise for the complete adaptive-statement relation finder.

Random-oracle support is certified against the code: `relationFinderReads` is the concrete table
point set, `relationFinderReads_card_le` bounds one retained traversal by `Q + (11 + k)`, the run
view materializes those canonical reads, and the locality theorems prove the finder and extractor
read nothing outside that set.  `relationFinderWithCalls` returns the stage count alongside the
result, and the two `RandomOracleQueriesAt_le` theorems lift that count into the four/five-slot
profile envelopes.  Direct field work and the assembled-MSM component have concrete
certificates, but two group-work quantities remain declared: `proverGroupWork` for the supplied
adversary and `reductionGroupWork` for the complete finder postprocessing.  The latter must remain
explicit until every group-valued branch is connected to an operational counter;
`adaptiveStatementCostedGroupOpsAt_le` certifies only its named assembly/basis sub-budget. -/
structure AdaptiveStatementDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  finderAdvantageLE : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar)
    (advantage (adaptiveStatementDlogRandomOracleQueries family)
      (adaptiveStatementDlogGroupWork proverGroupWork reductionGroupWork))

/-- Concrete work profile for adaptive-statement soundness and knowledge soundness. -/
structure AdaptiveStatementDirectDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (T : Nat) extends AdaptiveStatementDlogProfile family hchar B where
  /-- This threshold proves the query envelope from the circuit-derived supported-domain bound
  `domainExponent < 33`; no captured `domainExponent = 11` certificate is required. -/
  targetAtLeastSeventyTwo : 72 ≤ T
  queryBound : family.Q ≤ T
  proverWorkBound : toAdaptiveStatementDlogProfile.proverGroupWork ≤ T
  reductionWorkBound : toAdaptiveStatementDlogProfile.reductionGroupWork ≤ T
  costedAssemblyWorkBound : adaptiveStatementCostedGroupOpsBudget pp ≤ T
  directDecodeWorkBound : ∀ basis O,
    adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
      adaptiveStatementDirectDecodeOps family basis O ≤ T

theorem AdaptiveStatementDirectDlogProfile.solverCost_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder}
    {B : VestaG} {T : Nat}
    (profile : AdaptiveStatementDirectDlogProfile family hchar B T) :
    adaptiveStatementDlogRandomOracleQueries family ≤ 8 * T ∧
      adaptiveStatementDlogGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
        8 * T ∧
      ∀ basis O, adaptiveStatementDlogDirectDecodeSlots *
        adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  constructor
  · unfold adaptiveStatementDlogRandomOracleQueries
    rw [adaptiveStatementDlogTraversalSlots_eq_four]
    rw [CircuitShape.withProofParams_k, actionCircuit.shape_k]
    have hk := ActionPermutationDomain.domainExponent_lt
    have hT := profile.targetAtLeastSeventyTwo
    calc
      4 * family.Q + 4 * (11 + actionCircuit.domainExponent) ≤
          4 * T + 4 * (11 + actionCircuit.domainExponent) := by
        gcongr
        exact profile.queryBound
      _ ≤ 8 * T := by omega
  constructor
  · unfold adaptiveStatementDlogGroupWork
    calc
      4 * profile.proverGroupWork + profile.reductionGroupWork ≤ 4 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 8 * T := by omega
  · intro basis O
    have h := profile.directDecodeWorkBound basis O
    unfold adaptiveStatementKnowledgeExtractorDirectDecodeSlots at h
    unfold adaptiveStatementDlogDirectDecodeSlots
    omega

theorem AdaptiveStatementDirectDlogProfile.knowledgeExtractorCost_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder}
    {B : VestaG} {T : Nat}
    (profile : AdaptiveStatementDirectDlogProfile family hchar B T) :
    adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 8 * T ∧
      adaptiveStatementKnowledgeExtractorGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
        8 * T ∧
      ∀ basis O, adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
        adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  constructor
  · unfold adaptiveStatementKnowledgeExtractorRandomOracleQueries
      adaptiveStatementKnowledgeExtractorTraversalSlots
    rw [CircuitShape.withProofParams_k, actionCircuit.shape_k]
    have hk := ActionPermutationDomain.domainExponent_lt
    have hT := profile.targetAtLeastSeventyTwo
    calc
      5 * family.Q + 5 * (11 + actionCircuit.domainExponent) ≤
          5 * T + 5 * (11 + actionCircuit.domainExponent) := by
        gcongr
        exact profile.queryBound
      _ ≤ 8 * T := by omega
  constructor
  · unfold adaptiveStatementKnowledgeExtractorGroupWork
    calc
      5 * profile.proverGroupWork + profile.reductionGroupWork ≤ 5 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 8 * T := by omega
  · exact profile.directDecodeWorkBound

/-- Transfer any adaptive-statement event across a uniform-URS basis identification. -/
theorem event_prob_eq_of_uniformURS {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (basisOf : Omega → AugmentedIndex actionCircuit.n → VestaG)
    (hURS : OrchardUniformURSIdentification setup actionCircuit.domainExponent B basisOf)
    (event : Set ((AugmentedIndex actionCircuit.n → VestaG) × family.Coins)) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
      ((fun p => (basisOf p.1, p.2)) ⁻¹' event) =
    (PMF.uniformOfFintype
      ((AugmentedIndex actionCircuit.n → Fp) × family.Coins)).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := by
  let oraclePMF := PMF.uniformOfFintype family.Coins
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
          oraclePMF).map (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp)).map
            (scalarBasis B)) oraclePMF :=
        congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex actionCircuit.n → VestaG) × family.Coins) =>
      p.toOuterMeasure event) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure event =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
      oraclePMF).map (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure event at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
        (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := hmeasure
    _ = _ := by rw [independentProductPMF_uniform]

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark

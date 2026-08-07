import Zcash.Snark.Capstones.ActionChecks
import Zcash.Snark.Soundness.Action.AdaptiveStatementCost

/-!
# The Action semantic budgets, discharged and counted

The `theta`/`beta`/`gamma`/`y` surface budgets and the `x` degree bound, at the captured
parameters and at arbitrary bundle size, plus the statistical models the resource-accounted
endpoints evaluate.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark ComputedAdaptiveActionStatementFSFamily CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## Every semantic budget discharged and counted

Captured counting caps transfer to the derived key and discharge every semantic budget. The
statistical model assembled here reserves the larger pinned-root coefficient and an extra
compressed-constraint `x` term, so it upper-bounds the bare-adaptive remainder.
-/

/-- The Action circuit enables at most `2^12` lookup activations. -/
theorem actionLookupActivationCount_le :
    (operationEnabledLookups actionCircuit.operations 0).length ≤ 2 ^ 12 := by
  native_decide

/-- Every enabled Action lookup has at most four inputs. -/
theorem actionLookupInputArity_le :
    ∀ i : Fin (operationEnabledLookups actionCircuit.operations 0).length,
      ((operationEnabledLookups actionCircuit.operations 0).get i).argument.inputs.length ≤ 4 := by
  native_decide

/-- The exact per-Action permutation-cell count.  Unlike the old `2^16` envelope, this
tight value keeps the consensus-maximum β budget below `2^46`. -/
theorem resolverPermutationCell_card_eq
    (pp : ProofParams) (urs : URS VestaG)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    Fintype.card
        (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p actionActiveRows) =
      30630 := by
  rw [resolverPermutationCell_card]
  rw [actionCircuit.shape_numPermutationSets]
  rw [actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.2.2.2.2]
  rw [show actionCircuit.permutationSetCount = shape.numPermutationSets by
    simpa only [actionCircuit.shape_numPermutationSets] using
      congrArg CircuitShape.numPermutationSets
        actionCircuitShape_eq_fixtureCircuitShape]
  clear p poly urs pp
  native_decide

/-- Each Action permutation-cell resolver has at most `2^16` entries. -/
theorem resolverPermutationCell_card_le
    (pp : ProofParams) (urs : URS VestaG)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    Fintype.card
        (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p actionActiveRows) ≤
      2 ^ 16 := by
  rw [resolverPermutationCell_card_eq pp urs poly p]
  norm_num

/-- The θ budget is linear in the number of Actions. -/
theorem actionThetaBudget (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      TopLevelLookup.thetaBudget actionCircuit
        (actionProofParamsFor numProofs)
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) poly ≤
        numProofs * 2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookup.thetaBudget_eq]
  calc
    ∑ index : TopLevelLookup.ActivationIndex
          actionCircuit (actionProofParamsFor numProofs),
        actionCircuit.usableRowsAt actionCircuit.domainExponent *
          ((operationEnabledLookups actionCircuit.operations 0).get
            index.2).argument.inputs.length
      ≤ ∑ _index : TopLevelLookup.ActivationIndex
          actionCircuit (actionProofParamsFor numProofs), 2 ^ 11 * 4 := by
        gcongr with index
        · change actionActiveRows ≤ 2 ^ 11
          have hrows : actionActiveRows ≤ actionCircuit.n := by
            simpa only [actionDomainSize] using actionActiveRows_le_domainSize
          rw [actionCircuit.n_eq_two_pow_domainExponent,
            action_domainExponent_eq] at hrows
          norm_num at hrows ⊢
          exact hrows
        · exact actionLookupInputArity_le index.2
    _ ≤ numProofs * 2 ^ 25 := by
        simp only [TopLevelLookup.ActivationIndex,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hscaled :
            (operationEnabledLookups actionCircuit.operations 0).length *
                (2 ^ 11 * 4) ≤ 2 ^ 25 := by
          calc
            (operationEnabledLookups actionCircuit.operations 0).length * (2 ^ 11 * 4)
                ≤ 2 ^ 12 * (2 ^ 11 * 4) :=
              Nat.mul_le_mul_right _ actionLookupActivationCount_le
            _ = 2 ^ 25 := by norm_num
        simpa only [CircuitShape.withProofParams, actionProofParamsFor,
          Nat.cast_id, _root_.mul_assoc] using Nat.mul_le_mul_left numProofs hscaled

/-- The tight β budget is `950835027` per Action, including permutation cells and all three
lookup arguments. -/
theorem actionBetaBudget (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin (actionProofParamsFor numProofs).numProofs,
        (Fintype.card (ResolverPermutationCell
            (vkAt basis) poly p actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell
            (vkAt basis) poly p actionActiveRows)) +
      (actionProofParamsFor numProofs).numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1)) ≤
        numProofs * 950835027 := by
  intro basis poly
  let pp := actionProofParamsFor numProofs
  let urs := ursOfAugmentedBasis actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin pp.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) =
        30630 := by
    intro p
    exact resolverPermutationCell_card_eq pp urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n - actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  change
    (∑ p : Fin pp.numProofs,
      (Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) + 1) *
        Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows)) +
      pp.numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤
      numProofs * 950835027
  calc
    _ ≤ (∑ _p : Fin pp.numProofs,
          (30630 + 1) * 30630) +
        pp.numProofs *
          actionCircuit.lookupCount *
          ((2 ^ 11 + 2) * (2 ^ 11 + 1) + (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals rw [hcell p]
    _ = numProofs * 950835027 := by
      have hproofs : pp.numProofs = numProofs := by
        rfl
      have hlookups : actionCircuit.lookupCount = 3 := by
        rw [action_numLookups_eq]
        norm_num [shape]
      rw [hproofs, hlookups]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
      omega

/-- The tight γ budget is `73554` per Action. -/
theorem actionGammaBudget (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin (actionProofParamsFor numProofs).numProofs,
        2 * Fintype.card (ResolverPermutationCell
          (vkAt basis) poly p actionActiveRows)) +
      (actionProofParamsFor numProofs).numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n -
          actionCircuit.blindingFactors - 2 + 1)) ≤
        numProofs * 73554 := by
  intro basis poly
  let pp := actionProofParamsFor numProofs
  let urs := ursOfAugmentedBasis actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin pp.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) =
        30630 := by
    intro p
    exact resolverPermutationCell_card_eq pp urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n - actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  change
    (∑ p : Fin pp.numProofs,
      2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows)) +
      pp.numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤
      numProofs * 73554
  calc
    _ ≤ (∑ _p : Fin pp.numProofs, 2 * 30630) +
        pp.numProofs *
          actionCircuit.lookupCount * (2 * (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals rw [hcell p]
    _ = numProofs * 73554 := by
      have hproofs : pp.numProofs = numProofs := by
        rfl
      have hlookups : actionCircuit.lookupCount = 3 := by
        rw [action_numLookups_eq]
        norm_num [shape]
      rw [hproofs, hlookups]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
      omega

/-- The captured `θ` surface budget is at most `2^25`. -/
theorem capturedActionThetaBudget :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      TopLevelLookup.thetaBudget actionCircuit actionProofParams
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) poly ≤
        2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookup.thetaBudget_eq]
  calc
    ∑ index : TopLevelLookup.ActivationIndex
          actionCircuit actionProofParams,
        actionCircuit.usableRowsAt actionCircuit.domainExponent *
          ((operationEnabledLookups actionCircuit.operations 0).get
            index.2).argument.inputs.length
      ≤ ∑ _index : TopLevelLookup.ActivationIndex
          actionCircuit actionProofParams, 2 ^ 11 * 4 := by
        gcongr with index
        · change actionActiveRows ≤ 2 ^ 11
          have hrows : actionActiveRows ≤ actionCircuit.n := by
            simpa only [actionDomainSize] using actionActiveRows_le_domainSize
          rw [actionCircuit.n_eq_two_pow_domainExponent,
            action_domainExponent_eq] at hrows
          norm_num at hrows ⊢
          exact hrows
        · exact actionLookupInputArity_le index.2
    _ ≤ 2 ^ 25 := by
        simp only [TopLevelLookup.ActivationIndex,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hscaled :
            (operationEnabledLookups actionCircuit.operations 0).length *
                (2 ^ 11 * 4) ≤ 2 ^ 25 := by
          calc
            (operationEnabledLookups actionCircuit.operations 0).length * (2 ^ 11 * 4)
                ≤ 2 ^ 12 * (2 ^ 11 * 4) :=
              Nat.mul_le_mul_right _ actionLookupActivationCount_le
            _ = 2 ^ 25 := by norm_num
        simpa only [CircuitShape.withProofParams, actionProofParams, actionProofParamsFor,
          _root_.one_mul, Nat.cast_id] using hscaled

/-- The captured `β` surface budget is at most `2^35`. -/
theorem capturedActionBetaBudget :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin actionProofParams.numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows)) +
      actionProofParams.numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors -
              2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors -
              2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors -
            2 + 1)) ≤ 2 ^ 35 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin actionProofParams.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n -
      actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin actionProofParams.numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows)) +
        actionProofParams.numProofs *
          actionCircuit.lookupCount *
          ((actionCircuit.n -
                actionCircuit.blindingFactors - 2 + 2) *
              (actionCircuit.n -
                actionCircuit.blindingFactors - 2 + 1) +
            (actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin actionProofParams.numProofs,
          (2 ^ 16 + 1) * 2 ^ 16) +
      actionProofParams.numProofs *
          actionCircuit.lookupCount *
          ((2 ^ 11 + 2) * (2 ^ 11 + 1) + (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 35 := by
      rw [action_numLookups_eq]
      norm_num [actionProofParams, actionProofParamsFor, shape]

/-- The captured `γ` surface budget is at most `2^21`. -/
theorem capturedActionGammaBudget :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin actionProofParams.numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p
          actionActiveRows)) +
      actionProofParams.numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors -
          2 + 1)) ≤ 2 ^ 21 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin actionProofParams.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n -
      actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin actionProofParams.numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p
          actionActiveRows)) +
        actionProofParams.numProofs *
          actionCircuit.lookupCount *
          (2 * (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin actionProofParams.numProofs,
          2 * 2 ^ 16) +
      actionProofParams.numProofs *
          actionCircuit.lookupCount *
          (2 * (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 21 := by
      rw [action_numLookups_eq]
      norm_num [actionProofParams, actionProofParamsFor, shape]

/-- The Action evaluation domain is nonempty. -/
theorem derived_n_ne_zero :
    actionCircuit.n ≠ 0 :=
  actionCircuit.n_ne_zero

/-- A captured `2^12` constraint cap yields the `2^23` `y` budget. -/
theorem capturedActionYBudget {L : ℕ} (hL : L ≤ 2 ^ 12) :
    actionCircuit.n * L ≤ 2 ^ 23 := by
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  rw [hn]
  calc 2 ^ 11 * L ≤ 2 ^ 11 * 2 ^ 12 := Nat.mul_le_mul_left _ hL
    _ = 2 ^ 23 := by norm_num

/-- The `y` fold cap is linear in the bundle size once its constraint list is. -/
theorem actionYBudget (numProofs : ℕ) {L : ℕ}
    (hL : L ≤ numProofs * 2 ^ 12) :
    actionCircuit.n * L ≤
      numProofs * 2 ^ 23 := by
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  rw [hn]
  calc
    2 ^ 11 * L ≤ 2 ^ 11 * (numProofs * 2 ^ 12) := Nat.mul_le_mul_left _ hL
    _ = numProofs * 2 ^ 23 := by
      rw [show (2 : ℕ) ^ 23 = 2 ^ 11 * 2 ^ 12 by norm_num]
      omega

/-- Bound on the captured Action constraint count: the model has at most `2^12` constraints for
every prover polynomial assignment.  `actionConstraintCount_bound` is the generic
`numProofs`-dependent form. -/
theorem capturedActionConstraintCount_bound
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams actionProofParams) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionCommittedModel actionProofParams basis inputs ps source ch).constraints.length
      ≤ 2 ^ 12 := by
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    VerifyingKey.constraintModel constraintModelOfResolver
    ConstraintPolyModel.constraints ConstraintPolyModel.subProofConstraints
    ConstraintPolyModel.gateConstraints ConstraintPolyModel.permutationConstraints
    ConstraintPolyModel.lookupConstraints
  simp only [List.length_flatten, permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [actionCircuit.toVerifierKey_gates,
    actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.1, derived_scalars.2.2.2.2.2.2]
  have hproofs := congrArg Shape.numProofs actionShape_eq_fixtureShape
  have hsets := congrArg (fun proofShape : Shape => proofShape.numPermutationSets)
    actionShape_eq_fixtureShape
  have hlookups := congrArg (fun proofShape : Shape => proofShape.numLookups)
    actionShape_eq_fixtureShape
  norm_num [shape] at hproofs hsets hlookups
  simp [hproofs, hsets, hlookups, permutationSetsOfResolver,
    permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 actionCircuit.verifierCS.permutationChunks.length) ≤
      vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    rw [vk_gates_length, vk_permutationChunks_length]
    norm_num
  omega

/-- The adaptive Action constraint list is linear in the number of bundled Actions. -/
private theorem action_length_flatten_ofFn_le {α : Type*} {n : ℕ}
    (f : Fin n → List α) (c : ℕ) (hf : ∀ i, (f i).length ≤ c) :
    ((List.ofFn f).flatten).length ≤ n * c := by
  rw [List.length_flatten]
  refine le_trans (List.sum_le_card_nsmul _ c ?_) ?_
  · intro m hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact hf i
  · rw [List.length_map, List.length_ofFn, smul_eq_mul]

/-- Bound on the Action constraint count at arbitrary `numProofs`: the constraint list grows by at
most `2^12` entries per proof.  The captured specialization is stated separately as
`capturedActionConstraintCount_bound`. -/
theorem actionConstraintCount_bound (numProofs : ℕ)
    (basis : AugmentedIndex
      actionCircuit.n → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionCommittedModel (actionProofParamsFor numProofs) basis inputs ps source ch).constraints.length ≤
      numProofs * 2 ^ 12 := by
  unfold ConstraintPolyModel.constraints
  apply action_length_flatten_ofFn_le
  intro p
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    VerifyingKey.constraintModel constraintModelOfResolver
    ConstraintPolyModel.subProofConstraints
    ConstraintPolyModel.gateConstraints ConstraintPolyModel.permutationConstraints
    ConstraintPolyModel.lookupConstraints
  simp only [permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [actionCircuit.toVerifierKey_gates,
    actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.1, derived_scalars.2.2.2.2.2.2]
  have hsets := congrArg (fun proofShape : Shape => proofShape.numPermutationSets)
    (actionShapeFor_eq_fixtureShape numProofs)
  have hlookups := congrArg (fun proofShape : Shape => proofShape.numLookups)
    (actionShapeFor_eq_fixtureShape numProofs)
  norm_num [shape] at hsets hlookups
  simp [hsets, hlookups, permutationSetsOfResolver,
    permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 actionCircuit.verifierCS.permutationChunks.length) ≤
      vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    rw [vk_gates_length, vk_permutationChunks_length]
    norm_num
  omega

/-- The adaptive pre-`x` polynomial is assembled from coordinate vectors of degree below the
captured basis size, so the existing captured degree walk applies without a trace premise. -/
theorem adaptiveActionXDegree_bound (numProofs : ℕ)
    (basis : AugmentedIndex
      actionCircuit.n → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionPreXDifference (actionProofParamsFor numProofs) basis inputs ps source ch).natDegree ≤
      20470 := by
  let avk := ActionTerminal.vkAt basis
  let ic := actionCircuit.instanceCommitment (ursOfAugmentedBasis
      actionCircuit.domainExponent basis) inputs
  let poly := adaptiveActionCommitmentPolynomial
    (actionProofParamsFor numProofs) basis inputs ps source ch
  have hk : actionCircuit.n - 1 = 2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
    norm_num
  have hpoint : ∀ g : VestaG,
      (onlinePointPolynomial
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).natDegree ≤ 2047 := by
    intro g
    unfold onlinePointPolynomial
    have h := coeffsToPoly_natDegree_lt
      (n := 2 ^ actionCircuit.domainExponent)
      (by positivity)
      (onlinePointCoordinates
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).1
    have hsize :
        2 ^ actionCircuit.domainExponent = 2048 := by
      rw [action_domainExponent_eq]
      norm_num
    calc
      (onlinePointPolynomial
          (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          source g).natDegree ≤ 2 ^ actionCircuit.domainExponent - 1 :=
        Nat.le_sub_one_of_lt h
      _ = 2047 := by rw [hsize]
  have hpoly : ∀ id, (poly id).natDegree ≤ 2047 := by
    intro id
    unfold poly adaptiveActionCommitmentPolynomial
      adaptiveActionCommitmentPolynomialOf adaptiveActionPointPolynomial
    split
    · split
      · exact hpoint _
      · simp
    · simp
  have hresolver : ∀ {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
      (column : ℕ → CPoly),
      (∀ i, (column i).natDegree ≤ 2047) →
      ∀ i, (resolverQueryFeed (n := n) omega layout column i).natDegree ≤ 2047 := by
    intro n omega layout column hcolumn i
    unfold resolverQueryFeed
    split
    · exact natDegree_comp_rotateData_le _ _ (hcolumn _)
    · simp
  have hfixed : ∀ i, (fixedQueryFeedOfResolver avk poly i).natDegree ≤ 2047 :=
    hresolver avk.omega avk.fixedQueryLayout _ (fun _ => hpoly _)
  have hadvice : ∀ p i, (adviceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.adviceQueryLayout _ (fun _ => hpoly _)
  have hinstance : ∀ p i, (instanceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.instanceQueryLayout _ (fun _ => hpoly _)
  have hpermutationColumn :
      ∀ p : Fin (actionProofParamsFor numProofs).numProofs, ∀ cr,
      (permutationColumnPolynomialOfResolver avk poly p cr).natDegree ≤ 2047 := by
    intro p cr
    rcases cr with i | i | i <;>
      simp only [permutationColumnPolynomialOfResolver, ColumnRef.resolve] <;>
      unfold finFn <;> split
    all_goals
      first
      | exact hpoly _
      | simp
  have hnB : actionCircuit.n - 1 ≤ 2047 := by
    rw [derived_scalars.2.1]
    exact vk_n_pred_le
  have hrows : Function.Injective fun i : Fin actionCircuit.n =>
      actionCircuit.omega ^ (i : ℕ) :=
    TopLevelAssignment.domainRowsInjective
      ActionPermutationDomain.domainExponent_lt
  have hblindingVk : avk.blindingFactors < avk.n :=
    actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis
        actionCircuit.domainExponent basis)
  have hn : 0 < actionCircuit.n :=
    Nat.pos_of_ne_zero actionCircuit.n_ne_zero
  have hlookups : ∀ p, ∀ lk ∈ lookupEntriesOfResolver avk poly p,
      (lk.1.productEval.natDegree ≤ 2047 ∧ lk.1.productNextEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputInvEval.natDegree ≤ 2047 ∧
        lk.1.permutedTableEval.natDegree ≤ 2047) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * 2047 ≤ 8188) ∧
      ∀ e ∈ lk.2.2, e.degreeBound * 2047 ≤ 8188 := by
    intro p lk hlk
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
    refine ⟨⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _,
      natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _⟩, ?_, ?_⟩
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _
  have hmodel :
      adaptiveActionCommittedModel (actionProofParamsFor numProofs) basis inputs ps source ch =
        avk.constraintModel ch poly hblindingVk := by
    rfl
  rw [adaptiveActionPreXDifference_eq]
  rw [hmodel]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · apply natDegree_combineConstraints_le (B := 2047) (W := 7)
      (Dc := 8188) (D := 20470)
    · norm_num
    · simpa only [VerifyingKey.constraintModel_fixedCols] using hfixed
    · intro p i
      simpa only [VerifyingKey.constraintModel_adviceCols] using hadvice p i
    · intro p i
      simpa only [VerifyingKey.constraintModel_instanceCols] using hinstance p i
    · have hgates : ∀ e ∈ actionCircuit.verifierCS.gates,
          e.degreeBound * 2047 ≤ 20470 := by
        rw [derived_scalars.2.2.1]
        exact vk_gates_degree_le
      simpa only [VerifyingKey.constraintModel_gates, avk,
        ActionTerminal.vkAt, actionCircuit.toVerifierKey_gates] using hgates
    · intro p s hs
      change s ∈ permutationSetsOfResolver avk poly p at hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      dsimp only [permutationSetOfResolver]
      refine ⟨hpoly _, ?_⟩
      split
      · simp
      · exact natDegree_comp_rotateData_le _ _ (hpoly _)
    · intro p c hc
      change c ∈ permutationChunksOfResolver avk poly p at hc
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s1, s2⟩ := sc
      obtain ⟨hs1, hs2⟩ := List.of_mem_zip hsc
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs1
        exact ⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _)⟩
      · dsimp only [avk] at hs2
        rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_permutationChunks,
          derived_scalars.2.2.2.2.2.2] at hs2
        simpa using vk_chunk_width_le _ hs2
      · intro pr hpr
        obtain ⟨cr, -, hpr'⟩ := List.mem_map.mp hpr
        rw [← hpr']
        exact ⟨hpermutationColumn _ _, hpoly _⟩
    · intro p
      simpa only [VerifyingKey.constraintModel_lookups] using hlookups p
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [blindSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · rw [committedPreXQuotient_eq]
    refine le_trans (natDegree_preXQuotient_mul_le (Bq := 2047) _ _ ?_) ?_
    · intro j
      exact hpoint _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_n,
          derived_scalars.2.1,
        CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces,
        (actionDerivedShapeCounts numProofs).2.2.2.2]
      have hshape : 2 ^ shape.k - 1 = 2047 := by
        norm_num [shape]
      simpa only [hshape] using vk_quotient_tail_le

/-- **The semantic counts at the query ceiling**: at `Q ≤ 2^123` the five
counted caps total at most `2^160`. -/
theorem action_semantic_count_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
      ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) ≤ 2 ^ 160 := by
  have h1 : 1 ≤ (2 : ℕ) ^ 123 := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ 124 = 2 ^ 123 * 2 := pow_succ 2 123
  have hs : (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25)) : ℕ) ≤ 2 ^ 36 := by norm_num
  have h3 : (2 : ℕ) ^ 160 = 2 ^ 124 * 2 ^ 36 := by rw [← pow_add]
  calc (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
        ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25))
      = (Q + 1) * (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25))) := by ring
    _ ≤ 2 ^ 124 * 2 ^ 36 := Nat.mul_le_mul (by omega) hs
    _ = 2 ^ 160 := h3.symm

/-- The scalar field clears `2^254`: the counted remainder is at most `2^160 / |Fp| ≤ 2^-94`,
ten bits under the compressed model's `2^-84` ceiling. -/
theorem two_pow_254_le_card : 2 ^ 254 ≤ Fintype.card Fp := by
  rw [Zcash.Arithmetic.card_Fp]
  norm_num

/-- The four bundle-linear Action surfaces plus the bundle-independent `x` surface, collapsed to
one numerator.  The coefficient is the exact sum of the proved `y`, `β`, `γ`, and `θ` caps. -/
noncomputable def actionSemanticModelFor (numProofs Q : ℕ) : ENNReal :=
  (((Q + 1) * (20470 + numProofs * 992851621) : ℕ) : ENNReal) /
    Fintype.card Fp

/-- At every consensus-valid Action count and `Q ≤ 2^123`, all five semantic surfaces fit
inside `2^-84`. -/
theorem actionSemanticModelFor_at_2pow123 {numProofs Q : ℕ}
    (hn : numProofs ≤ orchardConsensusMaxProofs) (hQ : Q ≤ 2 ^ 123) :
    actionSemanticModelFor numProofs Q ≤ 1 / (2 ^ 84 : ENNReal) := by
  have hcap : 20470 + numProofs * 992851621 ≤ 2 ^ 46 := by
    calc
      20470 + numProofs * 992851621 ≤
          20470 + orchardConsensusMaxProofs * 992851621 := by omega
      _ ≤ 2 ^ 46 := by norm_num [orchardConsensusMaxProofs]
  have hqueries : Q + 1 ≤ 2 ^ 124 := by
    have hone : 1 ≤ (2 : ℕ) ^ 123 := Nat.one_le_two_pow
    omega
  have hnum : (Q + 1) * (20470 + numProofs * 992851621) ≤ 2 ^ 170 := by
    calc
      (Q + 1) * (20470 + numProofs * 992851621) ≤ 2 ^ 124 * 2 ^ 46 :=
        Nat.mul_le_mul hqueries hcap
      _ = 2 ^ 170 := by rw [← pow_add]
  rw [actionSemanticModelFor]
  calc
    ((((Q + 1) * (20470 + numProofs * 992851621) : ℕ) : ENNReal) /
        Fintype.card Fp) ≤
        ((2 ^ 170 : ℕ) : ENNReal) / Fintype.card Fp := by gcongr
    _ ≤ ((2 ^ 170 : ℕ) : ENNReal) / (2 ^ 254 : ℕ) := by
      gcongr
      exact_mod_cast two_pow_254_le_card
    _ ≤ 1 / (2 ^ 84 : ENNReal) := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      rw [show ((2 ^ 254 : ℕ) : ENNReal) =
          (2 ^ 84 : ENNReal) * (2 ^ 170 : ENNReal) by norm_num [← pow_add]]
      rw [div_eq_mul_inv, _root_.one_mul, ← _root_.mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), _root_.one_mul]
      norm_num

/-- The compressed straight-line remainder at an arbitrary Action count. -/
noncomputable def actionCompressedStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
    (Q + 1 : ℕ) * (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
      algebraicRootBudget shape actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    (Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ENNReal))

/-- Complete non-DLOG remainder for an `numProofs`-Action bundle. -/
noncomputable def actionStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  actionCompressedStatisticalModelFor numProofs Q + actionSemanticModelFor numProofs Q

/-- Valid bundles at `Q ≤ 2^123` fit the consensus compressed-statistical model. -/
private theorem actionCompressedStatisticalModelFor_le_consensus
    {numProofs Q : ℕ} (hn : numProofs ≤ orchardConsensusMaxProofs)
    (hQ : Q ≤ 2 ^ 123) :
    actionCompressedStatisticalModelFor numProofs Q ≤
      Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel (2 ^ 123) := by
  have hk : actionCircuit.domainExponent = 11 := by
    exact action_domainExponent_eq
  have hroot :
      algebraicRootBudget
          (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) 11 ≤
        algebraicRootBudget
          (Zcash.Snark.FixtureMax.shape orchardConsensusMaxProofs) 11 := by
    rw [actionProofShape_eq_maxShape]
    exact Zcash.Snark.FixtureMax.algebraicRootBudget_at_captured_shape_le_consensus_max hn
  rw [actionCompressedStatisticalModelFor,
    Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel,
    Zcash.Snark.FixtureMax.consensusPinnedRootMultiopenModel,
    hk]
  gcongr
  all_goals first | exact hroot | assumption_mod_cast | norm_num

/-- Consensus-valid bundles retain the `2^123` work target with a conservative `2^-83`
statistical remainder: one `2^-84` compressed term plus one `2^-84` semantic term. -/
theorem actionStatisticalModelFor_at_2pow123 {numProofs Q : ℕ}
    (hn : numProofs ≤ orchardConsensusMaxProofs) (hQ : Q ≤ 2 ^ 123) :
    actionStatisticalModelFor numProofs Q ≤ 1 / (2 ^ 83 : ENNReal) := by
  calc
    actionStatisticalModelFor numProofs Q =
        actionCompressedStatisticalModelFor numProofs Q +
          actionSemanticModelFor numProofs Q := rfl
    _ ≤ Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel (2 ^ 123) +
        1 / (2 ^ 84 : ENNReal) :=
      add_le_add (actionCompressedStatisticalModelFor_le_consensus hn hQ)
        (actionSemanticModelFor_at_2pow123 hn hQ)
    _ ≤ 1 / (2 ^ 84 : ENNReal) + 1 / (2 ^ 84 : ENNReal) := by
      gcongr
      exact Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel_at_2pow123
    _ ≤ 1 / (2 ^ 83 : ENNReal) := by
      rw [ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
        (Or.inl (by norm_num))).2
      have h :
          ((1 + 1 : ENNReal) / 2 ^ 84) * 2 ^ 83 =
            ((1 + 1 : ENNReal) * 2 ^ 83) / 2 ^ 84 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [h]
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      norm_num [← pow_succ]

/-- **The five semantic terms collapse to one count over the field**: the
endpoint's added tail is at most `2^160 / |Fp|`, with the count proven at the ceiling and no
absorption assumed. -/
theorem action_semantic_terms_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))))
      ≤ ((2 ^ 160 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  have hcollapse :
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
            ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)))) =
        (((Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
          ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) : ℕ) : ℝ≥0∞) /
          (Fintype.card Fp : ℝ≥0∞) := by
    rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc',
      ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
      ENNReal.div_add_div_same]
    norm_cast
  rw [hcollapse]
  gcongr
  exact_mod_cast action_semantic_count_le hQ

/-- The deployed one-Action shape has a much smaller pinned-root numerator than the
consensus-maximum bundle: `queryBudget = 96` and the six root families total `48808 / |Fp|`. -/
theorem action_algebraicRootBudget_eq :
    algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
        actionCircuit.domainExponent =
      (48808 : ENNReal) / Fintype.card Fp := by
  rw [actionShape_eq_fixtureShape]
  rw [action_domainExponent_eq]
  norm_num [algebraicRootBudget, queryBudget, shape]

/-- All non-DLOG terms in the exact Action endpoint, including the five semantic tails. -/
noncomputable def actionStatisticalModel (Q : Nat) : ENNReal :=
  (Q + 1 : Nat) * (1 / Fintype.card Fp) +
    (Q + 1 : Nat) *
      (actionCircuit.domainExponent *
        (2 / (Fintype.card Fp : ENNReal))) +
    (Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
      algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
        actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    (Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)) +
    (((Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal)) +
      (Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal))) +
      ((Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
          (Fintype.card Fp : ENNReal)) +
        ((Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)))))

/-- At `Q ≤ 2^123`, the compressed and five semantic remainders fit within `2^-84`. -/
theorem actionStatisticalModel_at_2pow123 {Q : Nat} (hQ : Q <= 2 ^ 123) :
    actionStatisticalModel Q <= 1 / (2 ^ 84 : ENNReal) := by
  have hbase :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <= 2 ^ 141 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <=
          (2 ^ 123 + 1) * (1 + 11 * 2 + 20470) +
            (2 ^ 123 + 23) * 48808 + 1 := by omega
      _ <= 2 ^ 141 := by norm_num
  have htotal :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 <=
        2 ^ 170 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 ≤
          2 ^ 141 + 2 ^ 160 := Nat.add_le_add_right hbase _
      _ ≤ 2 ^ 170 := by norm_num
  have hcount :
      actionStatisticalModel Q <=
        (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
          2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
    rw [actionStatisticalModel, action_algebraicRootBudget_eq]
    have hk : actionCircuit.domainExponent = 11 := by
      change actionCircuit.domainExponent = 11
      exact action_domainExponent_eq
    rw [hk]
    calc
      ((Q + 1 : Nat) : ENNReal) * (1 / (Fintype.card Fp : ENNReal)) +
          ((Q + 1 : Nat) : ENNReal) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
          ((Q + 23 : Nat) : ENNReal) * (48808 / (Fintype.card Fp : ENNReal)) +
          1 / (Fintype.card Fp : ENNReal) +
          ((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
          ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
            ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
              (Fintype.card Fp : ENNReal))) +
            (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                (Fintype.card Fp : ENNReal)) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                  (Fintype.card Fp : ENNReal))))) =
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
              ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
                (Fintype.card Fp : ENNReal))) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                    (Fintype.card Fp : ENNReal)) +
                  ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                    (Fintype.card Fp : ENNReal))))) := by
        simp only [div_eq_mul_inv]
        push_cast
        ring
      _ ≤
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        exact add_le_add_right (action_semantic_terms_le hQ) _
      _ = (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
            2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        rw [ENNReal.div_add_div_same]
        norm_cast
  refine hcount.trans ?_
  calc
    (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
        2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp <=
        ((2 ^ 170 : Nat) : ENNReal) / Fintype.card Fp := by gcongr
    _ <= ((2 ^ 170 : Nat) : ENNReal) / (2 ^ 254 : Nat) := by
      gcongr
      exact_mod_cast two_pow_254_le_card
    _ ≤ 1 / (2 ^ 84 : ENNReal) := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      rw [show ((2 ^ 254 : Nat) : ENNReal) =
          (2 ^ 84 : ENNReal) * (2 ^ 170 : ENNReal) by
            norm_num [← pow_add]]
      rw [div_eq_mul_inv, _root_.one_mul, ← _root_.mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), _root_.one_mul]
      norm_num

/-- Bound on `actionDlogOracleQueryCost`: if the adversary query cost is at most `2^123`, the
combined constraint-plus-Action solver's oracle-query cost is at most `2^126`. -/
theorem actionDlogOracleQueryCost_bound
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hQ : family.Q ≤ 2 ^ 123) :
    actionDlogOracleQueryCost actionProofParams family ≤ 2 ^ 126 := by
  unfold actionDlogOracleQueryCost
  have hk : actionCircuit.domainExponent = 11 := by
    exact action_domainExponent_eq
  rw [hk]
  calc
    6 * family.Q + 6 * (11 + 11) ≤ 6 * 2 ^ 123 + 6 * (11 + 11) := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-- Bound on `actionDlogGroupWork`: if prover and terminal-reduction group work each fit the
`2^123` target, the combined six-call solver fits the matching `2^126` envelope. -/
theorem actionDlogGroupWork_bound
    {proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork ≤ 2 ^ 123)
    (hreduction : reductionGroupWork ≤ 2 ^ 123) :
    actionDlogGroupWork proverGroupWork reductionGroupWork ≤ 2 ^ 126 := by
  unfold actionDlogGroupWork
  calc
    6 * proverGroupWork + reductionGroupWork ≤ 6 * 2 ^ 123 + 2 ^ 123 := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-! ## Adaptive-statement budgets

The counting caps, degree bound, surface measure and statistical model the adaptive-statement
endpoints evaluate, where the adversary chooses the statement and proof together.
-/

/-- The same constraint-count bound holds for every explicit instance-commitment function; the
count depends only on the Action verifier layout. -/
theorem adaptive_action_constraint_count_of_le_for (numProofs : ℕ)
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (instanceCommitment :
      Fin (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)).numProofs →
        Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionCommittedModelOf
      (ActionTerminal.vkAt basis)
      instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))).constraints.length ≤
      numProofs * 2 ^ 12 := by
  unfold ConstraintPolyModel.constraints
  apply action_length_flatten_ofFn_le
  intro p
  unfold adaptiveActionCommittedModelOf VerifyingKey.constraintModel constraintModelOfResolver
    ConstraintPolyModel.subProofConstraints ConstraintPolyModel.gateConstraints
    ConstraintPolyModel.permutationConstraints ConstraintPolyModel.lookupConstraints
  simp only [permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [actionCircuit.toVerifierKey_gates,
    actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.1, derived_scalars.2.2.2.2.2.2]
  have hsets := congrArg (fun proofShape : Shape => proofShape.numPermutationSets)
    (actionShapeFor_eq_fixtureShape numProofs)
  have hlookups := congrArg (fun proofShape : Shape => proofShape.numLookups)
    (actionShapeFor_eq_fixtureShape numProofs)
  norm_num [shape] at hsets hlookups
  simp [hsets, hlookups, permutationSetsOfResolver, permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 actionCircuit.verifierCS.permutationChunks.length) ≤
        vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    rw [vk_gates_length, vk_permutationChunks_length]
    norm_num
  omega

/-- The adaptive pre-`x` polynomial is assembled from coordinate vectors of degree below the
captured basis size, so the existing captured degree walk applies without a trace premise. -/
private theorem adaptive_action_x_degree_of_le_for (numProofs : ℕ)
    (basis : AugmentedIndex
      actionCircuit.n → VestaG)
    (instanceCommitment :
      Fin (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)).numProofs →
        Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionPreXDifferenceOf
      (ActionTerminal.vkAt basis)
      instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))).natDegree ≤ 20470 := by
  let avk := ActionTerminal.vkAt basis
  let ic := instanceCommitment
  let poly := adaptiveActionCommitmentPolynomialOf avk ic ps source ch
  have hk : actionCircuit.n - 1 = 2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
    norm_num
  have hpoint : ∀ g : VestaG,
      (onlinePointPolynomial
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).natDegree ≤ 2047 := by
    intro g
    unfold onlinePointPolynomial
    have h := coeffsToPoly_natDegree_lt
      (n := 2 ^ actionCircuit.domainExponent)
      (by positivity)
      (onlinePointCoordinates
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).1
    have hsize :
        2 ^ actionCircuit.domainExponent = 2048 := by
      rw [action_domainExponent_eq]
      norm_num
    calc
      (onlinePointPolynomial
          (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          source g).natDegree ≤ 2 ^ actionCircuit.domainExponent - 1 :=
        Nat.le_sub_one_of_lt h
      _ = 2047 := by rw [hsize]
  have hpoly : ∀ id, (poly id).natDegree ≤ 2047 := by
    intro id
    unfold poly adaptiveActionCommitmentPolynomialOf adaptiveActionPointPolynomial
    split
    · split
      · exact hpoint _
      · simp
    · simp
  have hresolver : ∀ {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
      (column : ℕ → CPoly),
      (∀ i, (column i).natDegree ≤ 2047) →
      ∀ i, (resolverQueryFeed (n := n) omega layout column i).natDegree ≤ 2047 := by
    intro n omega layout column hcolumn i
    unfold resolverQueryFeed
    split
    · exact natDegree_comp_rotateData_le _ _ (hcolumn _)
    · simp
  have hfixed : ∀ i, (fixedQueryFeedOfResolver avk poly i).natDegree ≤ 2047 :=
    hresolver avk.omega avk.fixedQueryLayout _ (fun _ => hpoly _)
  have hadvice : ∀ p i, (adviceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.adviceQueryLayout _ (fun _ => hpoly _)
  have hinstance : ∀ p i, (instanceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.instanceQueryLayout _ (fun _ => hpoly _)
  have hpermutationColumn :
      ∀ p : Fin (actionProofParamsFor numProofs).numProofs, ∀ cr,
      (permutationColumnPolynomialOfResolver avk poly p cr).natDegree ≤ 2047 := by
    intro p cr
    rcases cr with i | i | i <;>
      simp only [permutationColumnPolynomialOfResolver, ColumnRef.resolve] <;>
      unfold finFn <;> split
    all_goals
      first
      | exact hpoly _
      | simp
  have hnB : actionCircuit.n - 1 ≤ 2047 := by
    rw [derived_scalars.2.1]
    exact vk_n_pred_le
  have hrows : Function.Injective fun i : Fin actionCircuit.n =>
      actionCircuit.omega ^ (i : ℕ) :=
    TopLevelAssignment.domainRowsInjective
      ActionPermutationDomain.domainExponent_lt
  have hblindingVk : avk.blindingFactors < avk.n :=
    actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis
        actionCircuit.domainExponent basis)
  have hn : 0 < actionCircuit.n :=
    Nat.pos_of_ne_zero actionCircuit.n_ne_zero
  have hlookups : ∀ p, ∀ lk ∈ lookupEntriesOfResolver avk poly p,
      (lk.1.productEval.natDegree ≤ 2047 ∧ lk.1.productNextEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputInvEval.natDegree ≤ 2047 ∧
        lk.1.permutedTableEval.natDegree ≤ 2047) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * 2047 ≤ 8188) ∧
      ∀ e ∈ lk.2.2, e.degreeBound * 2047 ≤ 8188 := by
    intro p lk hlk
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
    refine ⟨⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _,
      natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _⟩, ?_, ?_⟩
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _
  have hmodel : adaptiveActionCommittedModelOf avk ic ps source ch hblindingVk =
      avk.constraintModel ch poly hblindingVk := by
    rfl
  rw [adaptiveActionPreXDifferenceOf_eq]
  rw [hmodel]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · apply natDegree_combineConstraints_le (B := 2047) (W := 7)
      (Dc := 8188) (D := 20470)
    · norm_num
    · simpa only [VerifyingKey.constraintModel_fixedCols] using hfixed
    · intro p i
      simpa only [VerifyingKey.constraintModel_adviceCols] using hadvice p i
    · intro p i
      simpa only [VerifyingKey.constraintModel_instanceCols] using hinstance p i
    · have hgates : ∀ e ∈ actionCircuit.verifierCS.gates,
          e.degreeBound * 2047 ≤ 20470 := by
        rw [derived_scalars.2.2.1]
        exact vk_gates_degree_le
      simpa only [VerifyingKey.constraintModel_gates, avk,
        ActionTerminal.vkAt, actionCircuit.toVerifierKey_gates] using hgates
    · intro p s hs
      change s ∈ permutationSetsOfResolver avk poly p at hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      dsimp only [permutationSetOfResolver]
      refine ⟨hpoly _, ?_⟩
      split
      · simp
      · exact natDegree_comp_rotateData_le _ _ (hpoly _)
    · intro p c hc
      change c ∈ permutationChunksOfResolver avk poly p at hc
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s1, s2⟩ := sc
      obtain ⟨hs1, hs2⟩ := List.of_mem_zip hsc
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs1
        exact ⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _)⟩
      · dsimp only [avk] at hs2
        rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_permutationChunks,
          derived_scalars.2.2.2.2.2.2] at hs2
        simpa using vk_chunk_width_le _ hs2
      · intro pr hpr
        obtain ⟨cr, -, hpr'⟩ := List.mem_map.mp hpr
        rw [← hpr']
        exact ⟨hpermutationColumn _ _, hpoly _⟩
    · intro p
      simpa only [VerifyingKey.constraintModel_lookups] using hlookups p
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [blindSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · rw [committedPreXQuotient_eq]
    refine le_trans (natDegree_preXQuotient_mul_le (Bq := 2047) _ _ ?_) ?_
    · intro j
      exact hpoint _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_n,
          derived_scalars.2.1,
        CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces,
        (actionDerivedShapeCounts numProofs).2.2.2.2]
      have hshape : 2 ^ shape.k - 1 = 2047 := by
        norm_num [shape]
      simpa only [hshape] using vk_quotient_tail_le

/-- The five captured surface bounds for the explicit instance commitments selected by an
adaptive statement. Commitment values change coefficients, not the proved degrees or resolver
cardinalities. -/
theorem orchard_adaptiveActionStatementSurface_measure_le_for
    (numProofs : ℕ)
    (basis : AugmentedIndex (2 ^ actionCircuit.domainExponent) → VestaG)
    (instanceCommitment :
      Fin (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)).numProofs →
        Nat → VestaG)
    (i : Fin 5)
    (ps : ProofString
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (i : ℕ) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment i ps source earlier) ≤
      ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
          numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp := by
  fin_cases i
  · refine le_trans
      (adaptiveActionThetaSurfaceAtOf_measure_le basis instanceCommitment ps source earlier) ?_
    gcongr
    exact_mod_cast actionThetaBudget numProofs basis
      (adaptiveActionCommitmentPolynomialOf
        (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
        instanceCommitment ps source (chRecord (fun _ => 0) (fun _ => 0)))
  · have h := adaptiveActionBetaSurfaceAtOf_measure_le
      basis instanceCommitment ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast actionBetaBudget numProofs basis
      (adaptiveActionCommitmentPolynomialOf
        (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
        instanceCommitment ps source
        (chRecord (fun j => if hj : (j : ℕ) < 1 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionGammaSurfaceAtOf_measure_le
      basis instanceCommitment ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast actionGammaBudget numProofs basis
      (adaptiveActionCommitmentPolynomialOf
        (adaptiveActionStatementVk (actionProofParamsFor numProofs) basis)
        instanceCommitment ps source
        (chRecord (fun j => if hj : (j : ℕ) < 2 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionYSurfaceAtOf_measure_le
      basis instanceCommitment ps source earlier derived_n_ne_zero
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast actionYBudget numProofs
      (adaptive_action_constraint_count_of_le_for numProofs basis instanceCommitment ps source
        (chRecord (fun j => if hj : (j : ℕ) < 3 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionXSurfaceAtOf_measure_le
      basis instanceCommitment ps source earlier
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast adaptive_action_x_degree_of_le_for numProofs basis instanceCommitment ps source
      (chRecord (fun j => if hj : (j : ℕ) < 4 then earlier ⟨j, hj⟩ else 0)
        (fun _ => 0))

/-! ## Certified adaptive-statement reduction work -/

/-- At every consensus-valid Action bundle size, the cached relation-finder and witness-extraction
group-operation program costs at most `2^123`.  Equality/list traversal and direct-coordinate work
are separate resources; the group-law bound is a structural consequence of the captured shape. -/
theorem adaptiveStatementReductionGroupWork_at_consensus
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs) :
    adaptiveStatementReductionGroupWork (actionProofParamsFor numProofs) ≤ 2 ^ 123 := by
  rw [adaptiveStatementReductionGroupWork_eq]
  simp only [adaptiveStatementBasisWidth, AdaptiveActionStatementShape]
  rw [actionShapeFor_eq_fixtureShape]
  simp only [assembleGroupOpsBudget, queryBudget, Zcash.Snark.Fixture.shape]
  have hn' : numProofs ≤ 2 ^ 16 - 1 := by
    simpa only [orchardConsensusMaxProofs] using hn
  calc
    _ = 30830 + 2050 * numProofs + 27 * (50 * numProofs + 46) ^ 2 := by
      ring
    _ ≤
        30830 + 2050 * (2 ^ 16 - 1) + 27 * (50 * (2 ^ 16 - 1) + 46) ^ 2 := by
      gcongr
    _ ≤ 2 ^ 123 := by norm_num

/-- The adaptive-statement remainder at an arbitrary Action count. It has the same four
bundle-linear semantic terms and one `x` term, but only one execution of the pinned-root surface. -/
noncomputable def adaptiveStatementStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
    (Q + 1 : ℕ) * (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    actionSemanticModelFor numProofs Q

/-- The sequential statistical model safely upper-bounds the adaptive-statement one: it reserves the
larger pinned-root coefficient and an additional compressed-constraint `x` term. -/
theorem adaptiveStatementStatisticalModelFor_le_action (numProofs Q : ℕ) :
    adaptiveStatementStatisticalModelFor numProofs Q ≤
      actionStatisticalModelFor numProofs Q := by
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  have hcoeff : ((Q + 1 : ℕ) : ENNReal) ≤
      ((Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) : ENNReal) := by
    exact Nat.cast_le.mpr (by omega)
  have hroot :
      (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent ≤
        (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
          algebraicRootBudget shape actionCircuit.domainExponent := by
    exact mul_le_mul_left hcoeff (algebraicRootBudget shape actionCircuit.domainExponent)
  unfold adaptiveStatementStatisticalModelFor actionStatisticalModelFor
    actionCompressedStatisticalModelFor
  dsimp only
  let a : ENNReal :=
    (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
      (Q + 1 : ℕ) *
        (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal)))
  let e : ENNReal := 1 / Fintype.card Fp
  let x : ENNReal :=
    (Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ENNReal))
  let s : ENNReal := actionSemanticModelFor numProofs Q
  change a + (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent + e + s ≤
    a + (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
      algebraicRootBudget shape actionCircuit.domainExponent + e + x + s
  calc
    _ ≤ a + (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
          algebraicRootBudget shape actionCircuit.domainExponent + e + s :=
      add_le_add_left (add_le_add_left (add_le_add_right hroot a) e) s
    _ ≤ _ := add_le_add_left
      (le_add_of_nonneg_right (show 0 ≤ x from bot_le)) s
end Zcash.Snark.Capstone

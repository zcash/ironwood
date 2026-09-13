import Zcash.Snark.ZeroKnowledge.ActionTyped
import Zcash.Snark.ZeroKnowledge.ActionWitnessSimulation
import Zcash.Snark.ZeroKnowledge.PlonkCompleteness
import Zcash.Common.Probability.Retry

/-!
# High-probability completeness for application Action witnesses

For a nonempty bundle, a valid application witness produces a completed proof
accepted by the existing typed verifier except with probability at most
`plonkCompletenessErrorBound actions`. The proof uses the actual Action compiler
key, instance commitments, canonical proof codecs, and the reference prover's
wide-reduced private and verifier tapes. It assumes neither successful emission
nor verifier acceptance.

The probability is for one interactive attempt. This is not perfect
completeness: a zero evaluation challenge has positive probability and prevents
completion. The typed verifier starts after decoding, as `DeployedAccepts`
does throughout the repository; no byte-parser or concrete-hash refinement is
asserted here. `actionZkTypedProver_encoded` identifies the observed attempt with
the existing `actionZkProver` computation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Complete canonical emission and verifier acceptance for the same Action proof. -/
def actionAcceptedAttemptSet {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) : Set (PlonkFreshView actions urs.k VestaG) :=
  plonkAcceptedAttemptSet urs
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionCircuit.instanceCommitment urs inputs) plonkPointCodec plonkScalarCodec

/-- Acceptance observes the canonical writer's status and the rejecting verifier on its typed proof. -/
theorem actionAcceptedAttemptSet_mem_iff {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (view : PlonkFreshView actions urs.k VestaG) :
    view ∈ actionAcceptedAttemptSet urs hk inputs ↔
      (encodedPlonkAttempt view).2.status = .complete ∧
        DeployedAccepts (plonkProofShape actions urs.k) urs rfl
          (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
          (actionCircuit.instanceCommitment urs inputs) view.2 view.1 := Iff.rfl

/-- The permitted zero evaluation challenge prevents an accepted attempt, even for a valid witness. -/
theorem actionAcceptedAttemptSet_not_mem_of_zero_x {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (view : PlonkFreshView actions urs.k VestaG) (hx : view.1.x = 0) :
    view ∉ actionAcceptedAttemptSet urs hk inputs := by
  intro hview
  have hcomplete := ((actionAcceptedAttemptSet_mem_iff urs hk inputs view).mp hview).1
  exact ((encodedPlonkAttempt_complete_iff view).mp hcomplete).2.1 hx

/-- The actual wide-reduced challenge law assigns positive probability to a non-accepting attempt. -/
theorem actionZkTypedProver_failure_pos [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    0 < (actionZkTypedProver urs hk inputs witness).toOuterMeasure
      (actionAcceptedAttemptSet urs hk inputs)ᶜ := by
  let actual := actionZkTypedProver urs hk inputs witness
  have hch : actual.map Prod.fst = widePlonkChallenges urs.k := by
    dsimp only [actual, actionZkTypedProver]
    exact freshSampledPlonkVerifier_challenges _ _ _ _ _ _
  have hx : actual.map (fun view => view.1.x) = fieldSample := by
    change actual.map ((fun ch : Challenges urs.k Fp => ch.x) ∘ Prod.fst) = _
    rw [← PMF.map_comp, hch, widePlonkChallenges_x]
  have hmass : actual.toOuterMeasure {view | view.1.x = 0} = fieldSample 0 := by
    change actual.toOuterMeasure ((fun view => view.1.x) ⁻¹' {0}) = _
    rw [← PMF.toOuterMeasure_map_apply, hx, PMF.toOuterMeasure_apply_singleton]
  have hle : actual.toOuterMeasure {view | view.1.x = 0} ≤
      actual.toOuterMeasure (actionAcceptedAttemptSet urs hk inputs)ᶜ :=
    actual.toOuterMeasure.mono fun view hzero =>
      actionAcceptedAttemptSet_not_mem_of_zero_x urs hk inputs view hzero
  rw [hmass] at hle
  exact (pos_iff_ne_zero.mpr (fieldSample_ne_zero 0)).trans_le hle

/-- Valid circuit rows and copies give completeness for the concrete Action compiler and verifier. -/
theorem wideActionZkRelation_completeness_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    (actionZkTypedProver urs hk inputs witness).toOuterMeasure
        (actionAcceptedAttemptSet urs hk inputs)ᶜ ≤ plonkCompletenessErrorBound actions := by
  let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
  let pub := actionPublicPolynomials inputs
  have hdomain := actionReferenceKey_domain (actions := actions) urs hk
    actionCircuit_newFixedCols_eq_fifteen
  exact widePlonk_completeness_error_bound urs hk (plonkTotalColumnConstructor vk pub witness) []
    vk (actionReferenceKey_queryLayout (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    pub (actionCircuit.instanceCommitment urs inputs) plonkPointCodec plonkScalarCodec
    plonkPointCodec_none_iff hpositive (actionReferenceKey_publicCommitmentsMatch urs hk inputs)
    hdomain.2 hdomain.1 (vestaBlinding_bijective urs.w hW)
    (wideActionZkTyped_simulation_error_bound urs hk inputs witness hvalid hW).1

/-- Valid application witnesses produce an accepted proof except with the explicit one-attempt error. -/
theorem wideActionWitness_completeness_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    (actionZkTypedProver urs hk inputs (actionWitnessRowBundle inputs witnesses)).toOuterMeasure
        (actionAcceptedAttemptSet urs hk inputs)ᶜ ≤ plonkCompletenessErrorBound actions :=
  wideActionZkRelation_completeness_error_bound urs hk inputs (actionWitnessRowBundle inputs witnesses)
    (actionWitnessRows_relation_capstone urs hk inputs witnesses conditions) hpositive hW

/-- The probability of completed emission and verifier acceptance is at least `1 - eta(m)`. -/
theorem wideActionWitness_acceptance_probability_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    1 - plonkCompletenessErrorBound actions ≤
      (actionZkTypedProver urs hk inputs (actionWitnessRowBundle inputs witnesses)).toOuterMeasure
        (actionAcceptedAttemptSet urs hk inputs) :=
  success_mass_lower_bound _ _
    (wideActionWitness_completeness_error_bound urs hk inputs witnesses conditions hpositive hW)

/-- For `m >= 1`, abort or rejection has probability strictly below `m * 2^(-238)`. -/
theorem wideActionWitness_completeness_binary_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    (actionZkTypedProver urs hk inputs (actionWitnessRowBundle inputs witnesses)).toOuterMeasure
        (actionAcceptedAttemptSet urs hk inputs)ᶜ < actions * (1 / (2 : ℝ≥0∞) ^ 238) :=
  (wideActionWitness_completeness_error_bound urs hk inputs witnesses conditions hpositive hW).trans_lt
    (plonkCompletenessErrorBound_lt_actions_mul_two_pow (by omega))

/-- The captured setup discharges the round-count and blinding-generator assumptions. -/
theorem wideCapturedActionWitness_completeness_error_bound [Fintype VestaG] {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) :
    (actionZkTypedProver capturedActionURS capturedActionURS_rounds inputs
      (actionWitnessRowBundle inputs witnesses)).toOuterMeasure
        (actionAcceptedAttemptSet capturedActionURS capturedActionURS_rounds inputs)ᶜ ≤
      plonkCompletenessErrorBound actions :=
  wideActionWitness_completeness_error_bound capturedActionURS capturedActionURS_rounds inputs witnesses
    conditions hpositive capturedActionURS_blinding_ne_zero

end Zcash.Snark.ZeroKnowledge

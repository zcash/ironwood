import Zcash.Snark.ZeroKnowledge.ActionRetryBounds
import Zcash.Snark.ZeroKnowledge.RetryLimit
import Zcash.Snark.ZeroKnowledge.RetryExpectation

/-!
# Unlimited independent attempts under an auxiliary caller

These laws retain every encoded attempt, received challenge, verifier tape, and
terminal status. The external `CallerRetryPolicy` repeats point failures and
handled IPA panics; completed emission and the coincident-opening error stop.
The statement and witness stay fixed, with fresh independent private and verifier
tapes in each attempt. This composition is outside the Zakura release model.

The simulator takes public data and a proof that its retry probability is below
one. That proof is erased and cannot affect its law. The theorem supplies it from
validity of the statement. No witness is supplied to the simulation computation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

variable [Fintype VestaG]

/-- Run the encoded Action reference policy to a terminal outcome, retaining every attempt. -/
noncomputable def actionZkRetryProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hW : urs.w ≠ 0) (hbudget : plonkCommonFailureBound actions < 1) :
    PMF (RetryHistory (Challenges urs.k Fp × ProverAttemptResult)) :=
  unlimitedRetainedRetries (actionZkProver urs hk inputs witness) plonkObservedRetrySet
    (actionZkProver_retry_lt_one urs hk inputs witness hW hbudget)

/-- The public simulator repeats its independent attempt law under the same stopping policy. -/
noncomputable def actionZkRetrySimulator {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp)
    (hstop : (actionZkSimulator urs hk inputs).toOuterMeasure plonkObservedRetrySet < 1) :
    PMF (RetryHistory (Challenges urs.k Fp × ProverAttemptResult)) :=
  unlimitedRetainedRetries (actionZkSimulator urs hk inputs) plonkObservedRetrySet hstop

/-- Every finite observation of the unlimited reference law is the established tape execution. -/
theorem actionZkRetryProver_truncate {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hW : urs.w ≠ 0) (hbudget : plonkCommonFailureBound actions < 1) (budget : ℕ) :
    (actionZkRetryProver urs hk inputs witness hW hbudget).map
        (truncateRetryHistory plonkObservedRetrySet budget) =
      (retryAttemptTape (actionZkProver urs hk inputs witness) budget).map
        (runRetryHistory plonkObservedRetrySet) := by
  rw [retainedRetries_fromTape]
  exact unlimitedRetainedRetries_truncate _ _ _ _

/-- The closed Action construction has statistical HVZK for its complete unlimited retained history. -/
theorem wideUnlimitedActionZk_simulation_error_bound {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (hbudget : plonkCommonFailureBound actions < 1) :
    let hstop := actionZkSimulator_retry_lt_one urs hk inputs witness hvalid hW hbudget
    PMFEventBiasLE (actionZkRetryProver urs hk inputs witness hW hbudget)
        (actionZkRetrySimulator urs hk inputs hstop)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) ∧
      PMFEventBiasLE (actionZkRetrySimulator urs hk inputs hstop)
        (actionZkRetryProver urs hk inputs witness hW hbudget)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) := by
  have h := wideActionZkRelation_simulation_error_bound urs hk inputs witness hvalid hW
  exact unlimitedRetainedRetries_simulation_error_bound h.1 h.2 plonkObservedRetrySet
    (wideActionZk_retry_le urs hk inputs witness hW)
    ((show plonkAttemptFailureBound actions ≤ plonkCommonFailureBound actions from le_self_add).trans_lt hbudget)
    (actionZkSimulator_retry_lt_one urs hk inputs witness hvalid hW hbudget)

/-- Expected attempts are bounded by the real and common geometric budgets respectively. -/
theorem wideUnlimitedActionZk_expected_attempts_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (hbudget : plonkCommonFailureBound actions < 1) :
    let hstop := actionZkSimulator_retry_lt_one urs hk inputs witness hvalid hW hbudget
    (∑' history, (actionZkRetryProver urs hk inputs witness hW hbudget) history *
      (history.attempts.length : ℝ≥0∞)) ≤ (1 - plonkAttemptFailureBound actions)⁻¹ ∧
    (∑' history, (actionZkRetrySimulator urs hk inputs hstop) history *
      (history.attempts.length : ℝ≥0∞)) ≤ (1 - plonkCommonFailureBound actions)⁻¹ := by
  exact ⟨unlimitedRetainedRetries_expected_attempts_le _ _ (wideActionZk_retry_le urs hk inputs witness hW)
      ((show plonkAttemptFailureBound actions ≤ plonkCommonFailureBound actions from le_self_add).trans_lt hbudget),
    unlimitedRetainedRetries_expected_attempts_le _ _
      (wideActionZkSimulator_retry_le urs hk inputs witness hvalid hW) hbudget⟩

/-- The real and simulated complete histories have the previously certified exhaustion tails. -/
theorem wideUnlimitedActionZk_length_tail_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (hbudget : plonkCommonFailureBound actions < 1) (budget : ℕ) :
    let hstop := actionZkSimulator_retry_lt_one urs hk inputs witness hvalid hW hbudget
    (actionZkRetryProver urs hk inputs witness hW hbudget).toOuterMeasure
        {history | budget < history.attempts.length} ≤ plonkAttemptFailureBound actions ^ budget ∧
      (actionZkRetrySimulator urs hk inputs hstop).toOuterMeasure
        {history | budget < history.attempts.length} ≤ plonkCommonFailureBound actions ^ budget := by
  simp only [actionZkRetryProver, actionZkRetrySimulator, unlimitedRetainedRetries_length_tail]
  constructor
  · gcongr
    exact wideActionZk_retry_le urs hk inputs witness hW
  · gcongr
    exact wideActionZkSimulator_retry_le urs hk inputs witness hvalid hW

/-- The checked Action-count range supplies the numerical normalization premise.
This arithmetic range is not asserted to be a protocol maximum. -/
theorem wideUnlimitedActionZk_simulation_capstone {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0) (hsize : actions ≤ 65535) :
    let hbudget := plonkCommonFailureBound_lt_one hsize
    let hstop := actionZkSimulator_retry_lt_one urs hk inputs witness hvalid hW hbudget
    PMFEventBiasLE (actionZkRetryProver urs hk inputs witness hW hbudget)
        (actionZkRetrySimulator urs hk inputs hstop)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) ∧
      PMFEventBiasLE (actionZkRetrySimulator urs hk inputs hstop)
        (actionZkRetryProver urs hk inputs witness hW hbudget)
        (plonkSimulationErrorBound actions / (1 - plonkAttemptFailureBound actions)) :=
  wideUnlimitedActionZk_simulation_error_bound urs hk inputs witness hvalid hW (plonkCommonFailureBound_lt_one hsize)

end Zcash.Snark.ZeroKnowledge

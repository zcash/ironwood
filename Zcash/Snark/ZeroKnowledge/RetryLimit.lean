import Zcash.Snark.ZeroKnowledge.RetryProjection
import Zcash.Common.Probability.DistributionAgreement

/-!
# Statistical simulation of complete unlimited retry histories

Each finite-budget law is the exact truncation of the stopped-history law. Its
only possible disagreement with that history is an unobserved later attempt,
whose probability is a geometric tail. Letting both tails tend to zero preserves
the existing uniform simulation bound, for every event of the complete history.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Truncation changes the observed complete history with at most its geometric tail probability. -/
theorem unlimitedRetainedRetries_truncation_error_bound {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1) (budget : ℕ) :
    PMFEventBiasLE (unlimitedRetainedRetries law retry hrate) (retainedRetries law retry budget)
        (law.toOuterMeasure retry ^ budget) ∧
      PMFEventBiasLE (retainedRetries law retry budget) (unlimitedRetainedRetries law retry hrate)
        (law.toOuterMeasure retry ^ budget) := by
  let complete := unlimitedRetainedRetries law retry hrate
  let bad := {history : RetryHistory A | budget < history.attempts.length}
  have hagree : ∀ history ∈ complete.support, history ∉ bad →
      truncateRetryHistory retry budget history = history := by
    intro history hs hn
    exact truncateRetryHistory_of_length_le retry budget history
      (unlimitedRetainedRetries_supported law retry hrate history hs).1 (Nat.le_of_not_gt hn)
  have hf := eventBias_map_of_agree complete id (truncateRetryHistory retry budget) bad
    (fun history hs hn => (hagree history hs hn).symm)
  have hr := eventBias_map_of_agree complete (truncateRetryHistory retry budget) id bad hagree
  simpa only [complete, bad, PMF.map_id, unlimitedRetainedRetries_truncate,
    unlimitedRetainedRetries_length_tail] using And.intro hf hr

/-- The finite uniform comparison extends to every event of the normalized unlimited history. -/
theorem unlimitedRetainedRetries_simulation_error_bound {A : Type*}
    {actual ideal : PMF A} {ε failure : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)]
    (hfailure : actual.toOuterMeasure retry ≤ failure) (hrate : failure < 1)
    (hideal : ideal.toOuterMeasure retry < 1) :
    PMFEventBiasLE (unlimitedRetainedRetries actual retry (hfailure.trans_lt hrate))
        (unlimitedRetainedRetries ideal retry hideal) (ε / (1 - failure)) ∧
      PMFEventBiasLE (unlimitedRetainedRetries ideal retry hideal)
        (unlimitedRetainedRetries actual retry (hfailure.trans_lt hrate)) (ε / (1 - failure)) := by
  have ha := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hfailure.trans_lt hrate)
  have hi := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hideal
  have hbound (budget : ℕ) := retainedRetries_uniform_error_bound forward reverse retry hfailure hrate budget
  have hactual (budget : ℕ) := unlimitedRetainedRetries_truncation_error_bound actual retry
    (hfailure.trans_lt hrate) budget
  have hsim (budget : ℕ) := unlimitedRetainedRetries_truncation_error_bound ideal retry hideal budget
  constructor
  · intro event
    have hlim := Filter.Tendsto.add
      (tendsto_const_nhds (x := (unlimitedRetainedRetries ideal retry hideal).toOuterMeasure event))
      ((hi.add (tendsto_const_nhds (x := ε / (1 - failure)))).add ha)
    have h := ge_of_tendsto' hlim (fun budget =>
      ((hactual budget).1.trans ((hbound budget).1.trans (hsim budget).2)) event)
    simpa only [zero_add, add_zero] using h
  · intro event
    have hlim := Filter.Tendsto.add
      (tendsto_const_nhds (x :=
        (unlimitedRetainedRetries actual retry (hfailure.trans_lt hrate)).toOuterMeasure event))
      ((ha.add (tendsto_const_nhds (x := ε / (1 - failure)))).add hi)
    have h := ge_of_tendsto' hlim (fun budget =>
      ((hsim budget).1.trans ((hbound budget).2.trans (hactual budget).2)) event)
    simpa only [zero_add, add_zero] using h

end Zcash.Snark.ZeroKnowledge

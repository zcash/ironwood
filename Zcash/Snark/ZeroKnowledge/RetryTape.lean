import Zcash.Common.Probability.RetainedRetriesSimulation
import Zcash.Common.Probability.DistributionKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A normalized law of independent tapes stopped at their first terminal attempt

The law sums the probability of each finite sequence of retry requests followed
by one terminal observation. The retry probability is strictly below one, so
these disjoint possibilities have total mass one. No failed observation is
discarded, and a terminal observation may be an error rather than completion.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- The complement of an event has the remaining probability mass. -/
theorem event_mass_compl_eq_sub {A : Type*} (law : PMF A) (event : Set A) :
    law.toOuterMeasure eventᶜ = 1 - law.toOuterMeasure event := by
  have hf : law.toOuterMeasure event ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (law.toOuterMeasure_apply_le_one event)
  have hs : law.toOuterMeasure eventᶜ + law.toOuterMeasure event = 1 := by
    simpa only [add_comm] using event_mass_add_compl law event
  apply le_antisymm
  · apply (ENNReal.add_le_add_iff_right hf).mp
    rw [hs, tsub_add_cancel_of_le (law.toOuterMeasure_apply_le_one event)]
  · apply (ENNReal.add_le_add_iff_right hf).mp
    rw [hs, tsub_add_cancel_of_le (law.toOuterMeasure_apply_le_one event)]

/-- The probability weight of one specified finite sequence consisting only of retry requests. -/
noncomputable def retryTapeWeight {A : Type*} (law : PMF A) (retry : Set A) :
    (count : ℕ) → (Fin count → A) → ℝ≥0∞
  | 0, _ => 1
  | count + 1, tape => retry.indicator law (tape 0) * retryTapeWeight law retry count (Fin.tail tape)

/-- Summing over every length-`count` retry tape gives the corresponding geometric power. -/
theorem retryTapeWeight_tsum {A : Type*} (law : PMF A) (retry : Set A) (count : ℕ) :
    (∑' tape, retryTapeWeight law retry count tape) = law.toOuterMeasure retry ^ count := by
  induction count with
  | zero =>
    simp only [retryTapeWeight, pow_zero]
    exact tsum_eq_single Fin.elim0 (fun tape h => (h (funext fun i => Fin.elim0 i)).elim)
  | succ count ih =>
    let e := Fin.consEquiv (fun _ : Fin (count + 1) => A)
    calc
      _ = ∑' pair : A × (Fin count → A),
          retryTapeWeight law retry (count + 1) (Fin.cons pair.1 pair.2) :=
        (e.tsum_eq (retryTapeWeight law retry (count + 1))).symm
      _ = ∑' value, retry.indicator law value *
          (∑' tape, retryTapeWeight law retry count tape) := by
        rw [ENNReal.tsum_prod']
        simp only [retryTapeWeight, Fin.cons_zero, Fin.tail_cons, ENNReal.tsum_mul_left]
      _ = law.toOuterMeasure retry * law.toOuterMeasure retry ^ count := by
        rw [ih, ENNReal.tsum_mul_right, ← law.toOuterMeasure_apply retry]
      _ = _ := (pow_succ' _ _).symm

/-- A finite vector of failed attempts and its following terminal observation. -/
abbrev StoppedRetryTape (A : Type*) := Σ count : ℕ, (Fin count → A) × A

/-- The independent probability of the complete stopped tape. -/
noncomputable def stoppedRetryWeight {A : Type*} (law : PMF A) (retry : Set A)
    (tape : StoppedRetryTape A) : ℝ≥0∞ :=
  retryTapeWeight law retry tape.1 tape.2.1 * retryᶜ.indicator law tape.2.2

/-- The stopped tapes have total probability one whenever a fresh attempt has a positive chance to stop. -/
theorem stoppedRetryWeight_tsum {A : Type*} (law : PMF A) (retry : Set A)
    (hrate : law.toOuterMeasure retry < 1) :
    (∑' tape, stoppedRetryWeight law retry tape) = 1 := by
  unfold stoppedRetryWeight
  rw [ENNReal.tsum_sigma']
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, retryTapeWeight_tsum]
  rw [← law.toOuterMeasure_apply retryᶜ, event_mass_compl_eq_sub, ENNReal.tsum_geometric]
  exact ENNReal.inv_mul_cancel (tsub_pos_iff_lt.mpr hrate).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)

/-- The normalized distribution of all finite stopped tapes, with no externally chosen attempt budget. -/
noncomputable def stoppedRetryTapes {A : Type*} (law : PMF A) (retry : Set A)
    (hrate : law.toOuterMeasure retry < 1) : PMF (StoppedRetryTape A) :=
  ⟨stoppedRetryWeight law retry, by
    rw [← stoppedRetryWeight_tsum law retry hrate]
    exact ENNReal.summable.hasSum⟩

/-- Preserve each retry observation in order, followed by the terminal observation. -/
def stoppedRetryTapeHistory {A : Type*} (tape : StoppedRetryTape A) : RetryHistory A :=
  ⟨List.ofFn tape.2.1 ++ [tape.2.2], false⟩

/-- The complete observed history of independent attempts without a finite retry budget. -/
noncomputable def unlimitedRetainedRetries {A : Type*} (law : PMF A) (retry : Set A)
    (hrate : law.toOuterMeasure retry < 1) : PMF (RetryHistory A) :=
  (stoppedRetryTapes law retry hrate).map stoppedRetryTapeHistory

end Zcash.Snark.ZeroKnowledge

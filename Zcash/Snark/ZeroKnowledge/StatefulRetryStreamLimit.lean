import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamLaw
import Zcash.Snark.ZeroKnowledge.MeasureStreamLimit

/-!
# Statistical comparison of complete stateful retry streams

Finite projections retain every emitted attempt and intermediate public state.
Their uniform comparison therefore gives the same error for every measurable
event of the full infinite observation, including the event of never stopping.
The proof does not condition either execution on termination.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- Uniform finite comparisons lift to the complete stream, retaining possible infinite histories. -/
theorem statefulRetryStreamLaw_simulation_error_bound {A State ActualTape IdealTape : Type*}
    [Fintype ActualTape] [Nonempty ActualTape] [MeasurableSpace ActualTape] [MeasurableSingletonClass ActualTape]
    [Fintype IdealTape] [Nonempty IdealTape] [MeasurableSpace IdealTape] [MeasurableSingletonClass IdealTape]
    [MeasurableSpace (Option (A × State))]
    (actual : State → ActualTape → A × State) (ideal : State → IdealTape → A × State)
    (retry : Set A) [DecidablePred (fun a => a ∈ retry)] (state : State) (error : ℝ≥0∞)
    (h : ∀ budget,
      PMFEventBiasLE
        (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype ActualTape).map (actual prior)) retry budget state)
        (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype IdealTape).map (ideal prior)) retry budget state) error ∧
      PMFEventBiasLE
        (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype IdealTape).map (ideal prior)) retry budget state)
        (statefulRetryRecorded (fun prior => (PMF.uniformOfFintype ActualTape).map (actual prior)) retry budget state) error) :
    MeasureEventBiasLE (statefulRetryStreamLaw actual retry state) (statefulRetryStreamLaw ideal retry state) error ∧
      MeasureEventBiasLE (statefulRetryStreamLaw ideal retry state) (statefulRetryStreamLaw actual retry state) error := by
  constructor
  · apply measureEventBias_of_prefixes _ _ error
    intro budget
    rw [statefulRetryStreamLaw_prefix, statefulRetryStreamLaw_prefix]
    exact eventBias_toMeasure (eventBias_map (h budget).1
      (fun output (i : Fin budget) => output.1.attempts[i.val]?))
  · apply measureEventBias_of_prefixes _ _ error
    intro budget
    rw [statefulRetryStreamLaw_prefix, statefulRetryStreamLaw_prefix]
    exact eventBias_toMeasure (eventBias_map (h budget).2
      (fun output (i : Fin budget) => output.1.attempts[i.val]?))

end Zcash.Snark.ZeroKnowledge

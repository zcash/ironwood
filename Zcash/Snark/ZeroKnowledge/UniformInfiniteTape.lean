import Zcash.Snark.ZeroKnowledge.RetryTapeSource
import Mathlib.Probability.Independence.InfinitePi

/-!
# An actual probability space for unlimited uniform attempt tapes

The countable product retains the entire stream. It is a probability measure,
not a mass function on infinite sequences. Every finite prefix has exactly the
existing independent uniform tape law.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open MeasureTheory

/-- The complete stream of independent uniform finite attempt tapes. -/
noncomputable def uniformInfiniteTape (Tape : Type*) [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] : Measure (ℕ → Tape) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Tape).toMeasure)

/-- Unlimited tape sampling is a normalized probability measure. -/
instance uniformInfiniteTape_isProbabilityMeasure (Tape : Type*) [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] : IsProbabilityMeasure (uniformInfiniteTape Tape) := by
  unfold uniformInfiniteTape
  infer_instance

/-- Every finite prefix is the complete uniform vector, with no stopping conditioning. -/
theorem uniformInfiniteTape_prefix {Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] (budget : ℕ) :
    (uniformInfiniteTape Tape).map (fun tape (i : Fin budget) => tape i.val) =
      (PMF.uniformOfFintype (Fin budget → Tape)).toMeasure := by
  rw [uniformInfiniteTape, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]
  apply Measure.ext_of_singleton
  intro tape
  simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton, measurableSet_singleton,
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Every deterministic finite-prefix computation has exactly its existing PMF semantics. -/
theorem uniformInfiniteTape_prefix_map {Tape Output : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace Output]
    (budget : ℕ) (run : (Fin budget → Tape) → Output) :
    (uniformInfiniteTape Tape).map (fun tape => run (fun i => tape i.val)) =
      ((PMF.uniformOfFintype (Fin budget → Tape)).map run).toMeasure := by
  have hm : Measurable run := measurable_of_countable _
  change (uniformInfiniteTape Tape).map (run ∘ (fun tape (i : Fin budget) => tape i.val)) = _
  rw [← Measure.map_map hm (by fun_prop), uniformInfiniteTape_prefix, PMF.toMeasure_map _ _ hm]

/-- The finite list used by retained retries is precisely the prefix of this infinite stream. -/
theorem uniformInfiniteTape_prefix_list {Tape : Type*} [Fintype Tape] [Nonempty Tape]
    [MeasurableSpace Tape] [MeasurableSingletonClass Tape] [MeasurableSpace (List Tape)] (budget : ℕ) :
    (uniformInfiniteTape Tape).map (fun tape => List.ofFn (fun i : Fin budget => tape i.val)) =
      (retryAttemptTape (PMF.uniformOfFintype Tape) budget).toMeasure := by
  rw [uniformInfiniteTape_prefix_map]
  rw [← independentTapeLaw_uniform (A := Tape), independentTapeLaw_toList]

end Zcash.Snark.ZeroKnowledge

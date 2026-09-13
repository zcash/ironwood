import Zcash.Snark.ZeroKnowledge.RandomTapeSource
import Zcash.Common.Probability.DistributionKernel

/-!
# A test-dependent reduction for a seeded private tape

The reduction receives one candidate tape, independently samples the public
coins, runs the prover continuation once, and runs the supplied probabilistic
distinguisher once. Its output law is exactly the distinguisher's law on the
corresponding source experiment.

Only a bound for this reduction's Boolean output is assumed. This does not
assume statistical closeness of a PRNG's full output tape. Applying a particular
PRNG security theorem also requires its seed, state, and resource conditions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- A deterministic generator applied to an explicit seed distribution. -/
noncomputable def seededTapeSource {Seed Tape : Type*} (seeds : PMF Seed)
    (generate : Seed → Tape) : PMF Tape := seeds.map generate

/-- A randomness distinguisher that runs one prover continuation and one view test. -/
noncomputable def tapeReduction {C T V : Type*} (coins : PMF C) (run : C → T → V)
    (test : V → PMF Bool) (tape : T) : PMF Bool :=
  coins.bind fun c => test (run c tape)

/-- Running a view test after the source experiment is exactly the tape reduction's output law. -/
theorem tapeReduction_law {C T V : Type*} (coins : PMF C) (source : PMF T)
    (run : C → T → V) (test : V → PMF Bool) :
    (sourceTapeExperiment coins source run).bind test =
      source.bind (tapeReduction coins run test) := by
  simp only [sourceTapeExperiment, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm coins source (fun c tape => test (run c tape))

/-- A PRNG bound for the actual reduction adds to the protocol's statistical simulation error. -/
theorem seededTape_test_simulation_error_bound {C T V Seed : Type*}
    (coins : PMF C) (seeds : PMF Seed) (generate : Seed → T) (ideal : PMF T)
    (run : C → T → V) (simulator : PMF V) (test : V → PMF Bool) (η ε : ℝ≥0∞)
    (sourceForward : PMFEventBiasLE
      ((seededTapeSource seeds generate).bind (tapeReduction coins run test))
      (ideal.bind (tapeReduction coins run test)) η)
    (sourceReverse : PMFEventBiasLE (ideal.bind (tapeReduction coins run test))
      ((seededTapeSource seeds generate).bind (tapeReduction coins run test)) η)
    (simulateForward : PMFEventBiasLE (sourceTapeExperiment coins ideal run) simulator ε)
    (simulateReverse : PMFEventBiasLE simulator (sourceTapeExperiment coins ideal run) ε) :
    PMFEventBiasLE ((sourceTapeExperiment coins (seededTapeSource seeds generate) run).bind test)
        (simulator.bind test) (ε + η) ∧
      PMFEventBiasLE (simulator.bind test)
        ((sourceTapeExperiment coins (seededTapeSource seeds generate) run).bind test) (ε + η) := by
  have hf := eventBias_bind_kernel simulateForward test
  have hr := eventBias_bind_kernel simulateReverse test
  rw [tapeReduction_law] at hf hr ⊢
  exact ⟨sourceForward.trans hf, by simpa only [add_comm] using hr.trans sourceReverse⟩

end Zcash.Snark.ZeroKnowledge

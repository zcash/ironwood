import Zcash.Snark.ZeroKnowledge.PrngSecurity
import Zcash.Snark.ZeroKnowledge.OracleContinuation

/-!
# From a PRNG game to a tested simulation experiment

The auxiliary data may select the public coins, deterministic continuation, and
view test, but is independent of the fresh seed. The reduction receives one
whole candidate tape, runs that continuation with independent public coins,
and applies the view test. Exact equality of the distinguishing experiments
lets its PRNG advantage add once to the protocol's statistical error.

Membership of this entire reduction in the stated admissible class remains an
explicit premise. This module supplies the distribution reduction, not a
running-time proof for arbitrary supplied continuations or tests.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Testing the source experiment is exactly the auxiliary-input PRNG game for the displayed reduction. -/
theorem auxiliaryPrngGame_reduction_law {Aux Coins Tape View : Type*}
    (auxiliary : PMF Aux) (source : PMF Tape) (coins : Aux → PMF Coins)
    (run : Aux → Coins → Tape → View) (test : Aux → View → PMF Bool) :
    auxiliary.bind (fun aux => (sourceTapeExperiment (coins aux) source (run aux)).bind (test aux)) =
      auxiliaryPrngGame auxiliary source (fun aux => tapeReduction (coins aux) (run aux) (test aux)) := by
  apply congrArg (PMF.bind auxiliary)
  funext aux
  exact tapeReduction_law (coins aux) source (run aux) (test aux)

/-- A secure generator and the admitted reduction give protocol error plus PRNG advantage for the tested view. -/
theorem uniformSeedPrng_simulation_error_bound {Aux Coins Tape View : Type*}
    [Fintype Tape] [Nonempty Tape] (auxiliary : PMF Aux) (seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → Tape) (coins : Aux → PMF Coins)
    (run : Aux → Coins → Tape → View) (simulator : Aux → PMF View)
    (test : Aux → View → PMF Bool) (admissible : Set (Aux → Tape → PMF Bool)) (η ε : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate auxiliary admissible η)
    (hclass : (fun aux => tapeReduction (coins aux) (run aux) (test aux)) ∈ admissible)
    (simulate : ∀ aux ∈ auxiliary.support,
      PMFEventBiasLE (sourceTapeExperiment (coins aux) (PMF.uniformOfFintype Tape) (run aux))
          (simulator aux) ε ∧
        PMFEventBiasLE (simulator aux)
          (sourceTapeExperiment (coins aux) (PMF.uniformOfFintype Tape) (run aux)) ε) :
    PMFEventBiasLE
        (auxiliary.bind (fun aux => (sourceTapeExperiment (coins aux)
          (uniformSeedTapeSource seedBits generate) (run aux)).bind (test aux)))
        (auxiliary.bind (fun aux => (simulator aux).bind (test aux))) (ε + η) ∧
      PMFEventBiasLE (auxiliary.bind (fun aux => (simulator aux).bind (test aux)))
        (auxiliary.bind (fun aux => (sourceTapeExperiment (coins aux)
          (uniformSeedTapeSource seedBits generate) (run aux)).bind (test aux))) (ε + η) := by
  have hsource := uniformSeedPrngSecure_event_bias secure hclass
  have hf := eventBias_bind_support auxiliary (fun aux haux =>
    eventBias_bind_kernel (simulate aux haux).1 (test aux))
  have hr := eventBias_bind_support auxiliary (fun aux haux =>
    eventBias_bind_kernel (simulate aux haux).2 (test aux))
  rw [auxiliaryPrngGame_reduction_law] at hf hr ⊢
  exact ⟨hsource.1.trans hf, by simpa only [add_comm] using hr.trans hsource.2⟩

end Zcash.Snark.ZeroKnowledge

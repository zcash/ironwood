import Zcash.Snark.ZeroKnowledge.OracleRetry

/-!
# Executing shared-oracle retries on independent private tapes

The deterministic runner passes the returned cache to the next attempt and
retains the same observations as the probability recursion. Future unused tapes
do not run after a terminal result. Both the real prover and the bit simulator
instantiate this runner with their existing one-attempt implementations.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

/-- A deterministic finite retry runner around an existing cached-oracle attempt implementation. -/
def runOracleRetries {Query Reply Tape : Type*}
    (run : OracleCache Query Reply → Tape → Option (ProverAttemptResult × OracleCache Query Reply))
    (tapes : List Tape) (cache : OracleCache Query Reply) :
    RetryHistory (Option ProverAttemptResult) × OracleCache Query Reply :=
  runStatefulRetries (fun cache tape => oracleAttemptState cache (run cache tape)) oracleRetrySet tapes cache

/-- Exact one-attempt tape laws lift to the complete retained shared-oracle execution. -/
theorem oracleRetries_fromTape {Query Reply Tape : Type*} (tapeLaw : PMF Tape)
    (run : OracleCache Query Reply → Tape → Option (ProverAttemptResult × OracleCache Query Reply))
    (attempt : OracleCache Query Reply → PMF (Option (ProverAttemptResult × OracleCache Query Reply)))
    (hrun : ∀ cache, tapeLaw.map (run cache) = attempt cache)
    (budget : ℕ) (cache : OracleCache Query Reply) :
    (retryAttemptTape tapeLaw budget).map (fun tapes => runOracleRetries run tapes cache) =
      oracleRetries attempt budget cache := by
  have htransition : (fun cache => tapeLaw.map (fun tape => oracleAttemptState cache (run cache tape))) =
      oracleRetryTransition attempt := by
    funext cache
    have h := congrArg (PMF.map (oracleAttemptState cache)) (hrun cache)
    simpa only [oracleRetryTransition, PMF.map_comp, Function.comp_def] using h
  have h := statefulRetries_fromTape tapeLaw
    (fun cache tape => oracleAttemptState cache (run cache tape)) oracleRetrySet budget cache
  rw [htransition] at h
  exact h

end Zcash.Snark.ZeroKnowledge

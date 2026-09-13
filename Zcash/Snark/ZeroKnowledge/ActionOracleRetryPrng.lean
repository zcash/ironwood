import Zcash.Snark.ZeroKnowledge.ActionFiatShamirRetry
import Zcash.Snark.ZeroKnowledge.ActionOracleRetrySource
import Zcash.Snark.ZeroKnowledge.PrngSecurityReduction

/-!
# A PRNG reduction for the complete finite shared-oracle retry experiment

One fresh seed supplies the whole private prefix for all available attempts.
The preprocessing request, valid witness, auxiliary state, and prior oracle
cache are sampled before and independently of that seed. The reduction keeps
every failed prefix, uses the same oracle cache across retries, and executes
the adversary's adaptive postprocessing and final Boolean test.

Security of that complete generated prefix against the admitted reduction
adds `eta` once to the existing finite statistical bound. No independence of
the generated attempt blocks is assumed. The assumption's output length and
resource class must cover the full budget, even when execution stops earlier.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (URS)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Adaptive postprocessing after retries driven by an arbitrary joint private source. -/
noncomputable def actionOracleRetrySourceContinuation {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    {budget : ℕ} (source : PMF (RawPrivateRetryTape actions budget))
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleRetriesFromSource urs hk view.1.request.inputs view.1.witness view.1.request.vkTranscriptRepr source view.2).bind
    fun observed => cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.state view.1.request observed.1) observed.2

/-- The complete source experiment samples the private source freshly after the adaptive request. -/
noncomputable def actionOracleRetrySourceExperiment {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    {budget : ℕ} (source : PMF (RawPrivateRetryTape actions budget)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleRetryPreprocessing adversary).bind (actionOracleRetrySourceContinuation adversary source)

/-- Uniform raw private blocks recover the existing full adaptive finite-retry experiment exactly. -/
theorem actionOracleRetrySourceExperiment_uniform {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ) :
    actionOracleRetrySourceExperiment adversary (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) =
      actionOracleRetryRealExperiment adversary budget := by
  apply congrArg (PMF.bind (actionOracleRetryPreprocessing adversary))
  funext view
  simp only [actionOracleRetrySourceContinuation, actionOracleRetriesFromSource_uniform,
    actionOracleRetryRealContinuation]

/-- The actual retry-and-postprocessing distinguisher receives one candidate private prefix. -/
noncomputable def actionOracleRetryPrngReduction {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ) (test : (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → PMF Bool)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) : RawPrivateRetryTape actions budget → PMF Bool :=
  tapeReduction (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget))
    (fun replies privateTape => actionOracleRetriesFromRawTapes urs hk view.1.request.inputs view.1.witness
      view.1.request.vkTranscriptRepr replies privateTape view.2)
    (fun observed => (cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.state view.1.request observed.1) observed.2).bind test)

/-- The displayed PRNG game is exactly the tested execution with retained history and adaptive oracle access. -/
theorem actionOracleRetryPrng_game_law {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    {budget : ℕ} (source : PMF (RawPrivateRetryTape actions budget))
    (test : (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → PMF Bool) :
    (actionOracleRetrySourceExperiment adversary source).bind test =
      auxiliaryPrngGame (actionOracleRetryPreprocessing adversary) source
        (actionOracleRetryPrngReduction adversary budget test) := by
  simp only [actionOracleRetrySourceExperiment, actionOracleRetrySourceContinuation,
    actionOracleRetriesFromSource, PMF.bind_bind]
  exact auxiliaryPrngGame_reduction_law (actionOracleRetryPreprocessing adversary) source _ _ _

/-- A single assumption on the whole generated prefix gives finite Fiat–Shamir test advantage at most `R(m,q,n) + eta`. -/
theorem uniformSeedActionFiatShamirRetry_test_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (budget seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateRetryTape actions budget)
    (test : (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → PMF Bool)
    (admissible : Set ((ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → RawPrivateRetryTape actions budget → PMF Bool))
    (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (actionOracleRetryPreprocessing adversary) admissible η)
    (hclass : actionOracleRetryPrngReduction adversary budget test ∈ admissible) :
    PMFEventBiasLE
        ((actionOracleRetrySourceExperiment adversary (uniformSeedTapeSource seedBits generate)).bind test)
        ((actionOracleRetrySimulatedExperiment adversary budget).bind test)
        (oracleRetryError actions adversary.beforeBudget budget + η) ∧
      PMFEventBiasLE ((actionOracleRetrySimulatedExperiment adversary budget).bind test)
        ((actionOracleRetrySourceExperiment adversary (uniformSeedTapeSource seedBits generate)).bind test)
        (oracleRetryError actions adversary.beforeBudget budget + η) := by
  have hsource := uniformSeedPrngSecure_event_bias secure hclass
  rw [← actionOracleRetryPrng_game_law, ← actionOracleRetryPrng_game_law,
    actionOracleRetrySourceExperiment_uniform] at hsource
  have h := actionFiatShamirRetry_simulation_error_bound adversary hpositive hW budget
  have hf := eventBias_bind_kernel h.1 test
  have hr := eventBias_bind_kernel h.2 test
  exact ⟨hsource.1.trans hf, by simpa only [add_comm] using hr.trans hsource.2⟩

end Zcash.Snark.ZeroKnowledge

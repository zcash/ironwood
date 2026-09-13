import Zcash.Snark.ZeroKnowledge.ActionOracleRetryResources

/-!
# Finite Action Fiat–Shamir retries with adaptive oracle access

The adversary may query the oracle, select one valid statement/witness pair,
and retain arbitrary auxiliary state. The internal retry run keeps that request
fixed and shares its evolving cache across all attempts. The adversary then
receives the complete observed history and continues querying the same cache.
There are no intervening adversary queries or changes of request during the
internal run. Every attempt uses fresh independent private tapes.

For at most `n` attempts and `q_pre` preprocessing queries, the two-sided error
is at most `n * epsilon_bits(m, q_pre) + 11n(n-1)/p`. The simulator is witness
free, uses fixed Boolean tapes, and retains explicit exhaustion and programming
failure. This finite theorem assumes no shared-oracle termination law.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (URS scalarFieldOrder)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Adaptive oracle phases surrounding one internal retained-history retry run. -/
structure ActionOracleRetryAdversary {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (Coins State Output : Type*) where
  coins : PMF Coins
  beforeBudget : ℕ
  before : Coins → OracleComp TranscriptHashAddress (Fin challengeDigestCard)
    (ActionOracleSelection (actions := actions) urs hk State)
  before_queryBound : ∀ coins, (before coins).QueryBound beforeBudget
  afterBudget : ℕ
  after : State → ActionOracleRequest actions → RetryHistory (Option ProverAttemptResult) →
    OracleComp TranscriptHashAddress (Fin challengeDigestCard) Output
  after_queryBound : ∀ state request history, (after state request history).QueryBound afterBudget

/-- Preprocessing selects the fixed request and auxiliary state using an initially empty oracle. -/
noncomputable def actionOracleRetryPreprocessing {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output) :
    PMF (ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  adversary.coins.bind fun coins =>
    cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard)) (adversary.before coins) []

/-- The chosen request starts with at most the declared number of prior oracle queries. -/
theorem actionOracleRetryPreprocessing_cache_length_le {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hview : view ∈ (actionOracleRetryPreprocessing adversary).support) :
    view.2.length ≤ adversary.beforeBudget := by
  obtain ⟨coins, _, hcoins⟩ := (PMF.mem_support_bind_iff _ _ _).mp hview
  simpa only [List.length_nil, Nat.zero_add] using
    cachedOracleLaw_cache_length_le _ (adversary.before_queryBound coins) [] view hcoins

/-- Real retries followed by adaptive postprocessing of the complete observed history. -/
noncomputable def actionOracleRetryRealContinuation {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ) (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleRetries urs hk view.1.request.inputs view.1.witness view.1.request.vkTranscriptRepr budget view.2).bind
    fun observed => cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.state view.1.request observed.1) observed.2

/-- The retry simulator's continuation receives only the public request, auxiliary data, and prior cache. -/
noncomputable def actionOracleRetrySimulatedContinuation {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ)
    (view : (ActionOracleRequest actions × State) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleBitRetries urs hk view.1.1.inputs view.1.1.vkTranscriptRepr budget view.2).bind
    fun observed => cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.2 view.1.1 observed.1) observed.2

/-- The full real experiment with adaptive selection and postprocessing around finite shared-oracle retries. -/
noncomputable def actionOracleRetryRealExperiment {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ) : PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleRetryPreprocessing adversary).bind (actionOracleRetryRealContinuation adversary budget)

/-- The full simulated experiment erases the witness before running the public retry simulator. -/
noncomputable def actionOracleRetrySimulatedExperiment {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (budget : ℕ) : PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  ((actionOracleRetryPreprocessing adversary).map actionOraclePublicContext).bind
    (actionOracleRetrySimulatedContinuation adversary budget)

/-- The complete retry continuation respects the bound from its preceding oracle-query budget. -/
theorem actionOracleRetryContinuation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (budget : ℕ)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hcache : view.2.length ≤ adversary.beforeBudget) :
    PMFEventBiasLE (actionOracleRetryRealContinuation adversary budget view)
        (actionOracleRetrySimulatedContinuation adversary budget (actionOraclePublicContext view))
        (oracleRetryError actions adversary.beforeBudget budget) ∧
      PMFEventBiasLE (actionOracleRetrySimulatedContinuation adversary budget (actionOraclePublicContext view))
        (actionOracleRetryRealContinuation adversary budget view)
        (oracleRetryError actions adversary.beforeBudget budget) := by
  have h := actionOracleRetries_simulation_error_bound urs hk view.1.request.inputs view.1.witness
    view.1.valid hpositive hW view.1.request.vkTranscriptRepr budget view.2
  let after := fun observed : RetryHistory (Option ProverAttemptResult) ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard) =>
    cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.state view.1.request observed.1) observed.2
  have hf := eventBias_bind_kernel h.1 after
  have hr := eventBias_bind_kernel h.2 after
  have hbudget := oracleRetryError_mono_queries actions budget hcache
  exact ⟨fun event => (hf event).trans (add_le_add le_rfl hbudget),
    fun event => (hr event).trans (add_le_add le_rfl hbudget)⟩

/-- Statistical Fiat–Shamir simulation for every finite shared-oracle retry budget and complete final oracle view. -/
theorem actionFiatShamirRetry_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (budget : ℕ) :
    PMFEventBiasLE (actionOracleRetryRealExperiment adversary budget) (actionOracleRetrySimulatedExperiment adversary budget)
        (oracleRetryError actions adversary.beforeBudget budget) ∧
      PMFEventBiasLE (actionOracleRetrySimulatedExperiment adversary budget) (actionOracleRetryRealExperiment adversary budget)
        (oracleRetryError actions adversary.beforeBudget budget) := by
  simp only [actionOracleRetryRealExperiment, actionOracleRetrySimulatedExperiment, PMF.bind_map, Function.comp_def]
  constructor
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleRetryContinuation_error_bound adversary hpositive hW budget view
      (actionOracleRetryPreprocessing_cache_length_le adversary view hview)).1
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleRetryContinuation_error_bound adversary hpositive hW budget view
      (actionOracleRetryPreprocessing_cache_length_le adversary view hview)).2

/-- The finite retry comparison has an explicit binary bound plus its full prior-cache contribution. -/
theorem actionFiatShamirRetry_binary_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (budget : ℕ) :
    let error := (budget * actions : ℝ≥0∞) * (1 / (2 : ℝ≥0∞) ^ 238) +
      ((budget * adversary.beforeBudget + 11 * budget * (budget - 1) : ℕ) : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleRetryRealExperiment adversary budget) (actionOracleRetrySimulatedExperiment adversary budget) error ∧
      PMFEventBiasLE (actionOracleRetrySimulatedExperiment adversary budget) (actionOracleRetryRealExperiment adversary budget) error := by
  have h := actionFiatShamirRetry_simulation_error_bound adversary hpositive hW budget
  have hbound := oracleRetryError_binary_le hpositive adversary.beforeBudget budget
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hbound),
    fun event => (h.2 event).trans (add_le_add le_rfl hbound)⟩

/-- The complete real before/retries/after experiment obeys its combined oracle-cache budget. -/
theorem actionOracleRetryRealExperiment_cache_length_le {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output) (budget : ℕ)
    (output : Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleRetryRealExperiment adversary budget).support) :
    output.2.length ≤ adversary.beforeBudget + 22 * budget + adversary.afterBudget := by
  rw [actionOracleRetryRealExperiment, PMF.mem_support_bind_iff] at houtput
  obtain ⟨view, hview, houtput⟩ := houtput
  rw [actionOracleRetryRealContinuation, PMF.mem_support_bind_iff] at houtput
  obtain ⟨observed, hobs, houtput⟩ := houtput
  have hpre := actionOracleRetryPreprocessing_cache_length_le adversary view hview
  have hproof := actionOracleRetries_cache_length_le urs hk view.1.request.inputs view.1.witness
    view.1.request.vkTranscriptRepr budget view.2 observed hobs
  have hpost := cachedOracleLaw_cache_length_le _
    (adversary.after_queryBound view.1.state view.1.request observed.1) observed.2 output houtput
  omega

/-- The complete simulated before/retries/after experiment obeys the same oracle-cache budget. -/
theorem actionOracleRetrySimulatedExperiment_cache_length_le {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output) (budget : ℕ)
    (output : Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleRetrySimulatedExperiment adversary budget).support) :
    output.2.length ≤ adversary.beforeBudget + 22 * budget + adversary.afterBudget := by
  rw [actionOracleRetrySimulatedExperiment, PMF.bind_map, PMF.mem_support_bind_iff] at houtput
  obtain ⟨view, hview, houtput⟩ := houtput
  dsimp only [Function.comp_def, actionOracleRetrySimulatedContinuation, actionOraclePublicContext] at houtput
  rw [PMF.mem_support_bind_iff] at houtput
  obtain ⟨observed, hobs, houtput⟩ := houtput
  have hpre := actionOracleRetryPreprocessing_cache_length_le adversary view hview
  have hproof := actionOracleBitRetries_cache_length_le urs hk view.1.request.inputs
    view.1.request.vkTranscriptRepr budget view.2 observed hobs
  have hpost := cachedOracleLaw_cache_length_le _
    (adversary.after_queryBound view.1.state view.1.request observed.1) observed.2 output houtput
  omega

end Zcash.Snark.ZeroKnowledge

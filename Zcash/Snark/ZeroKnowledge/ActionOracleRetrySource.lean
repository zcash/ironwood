import Zcash.Snark.ZeroKnowledge.ActionOracleRetry
import Zcash.Snark.ZeroKnowledge.RetryTapeSource

/-!
# Finite shared-oracle Action retries with a complete private source

The private source supplies one joint vector of `budget` raw attempt tapes,
each containing `148m + 46` 512-bit words. Its blocks need not be independent.
Oracle reply slots are sampled separately and used with the same persistent
cache as before. Uniform raw private tapes have exactly the existing finite
shared-oracle retry law, including every failure prefix and exhaustion.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action

/-- One complete raw private block for each available attempt. -/
abbrev RawPrivateRetryTape (actions budget : ℕ) := Fin budget → RawPrivateTape actions

/-- Separately supplied raw oracle reply slots for every available attempt. -/
abbrev OracleReplyRetryTape (k budget : ℕ) := Fin budget → PlonkChallengeTape k (Fin challengeDigestCard)

/-- Convert only the private field words; oracle replies retain their full raw digests. -/
def actionRawOracleTape {actions k : ℕ}
    (tape : PlonkChallengeTape k (Fin challengeDigestCard) × RawPrivateTape actions) :
    ActionOracleTape actions k := (tape.1, reducePrivateTape tape.2)

/-- Independent raw uniform inputs reproduce the exact existing private-and-reply tape law. -/
theorem actionRawOracleTape_law (actions k : ℕ) :
    (PMF.uniformOfFintype (PlonkChallengeTape k (Fin challengeDigestCard) × RawPrivateTape actions)).map
        actionRawOracleTape = actionOracleTapeLaw actions k := by
  rw [← Zcash.independentProductPMF_uniform]
  simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp,
    Function.comp_def, actionRawOracleTape, actionOracleTapeLaw]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (PlonkChallengeTape k (Fin challengeDigestCard))))
  funext replies
  have h := congrArg (PMF.map (Prod.mk replies)) (uniformRawPrivateTape_reduce actions)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Replay all observed shared-oracle attempts from separately fixed reply and raw private tapes. -/
def actionOracleRetriesFromRawTapes {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) {budget : ℕ} (replies : OracleReplyRetryTape urs.k budget)
    (privateTape : RawPrivateRetryTape actions budget)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard) :=
  actionOracleRetriesFromTapes urs hk inputs witness vkTranscriptRepr
    (List.ofFn (fun i => actionRawOracleTape (replies i, privateTape i))) cache

/-- An arbitrary joint private source, sampled independently of all public oracle reply slots. -/
noncomputable def actionOracleRetriesFromSource {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) {budget : ℕ} (source : PMF (RawPrivateRetryTape actions budget))
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  sourceTapeExperiment (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget)) source
    (fun replies privateTape => actionOracleRetriesFromRawTapes urs hk inputs witness vkTranscriptRepr replies privateTape cache)

/-- Uniform private raw blocks give exactly the proved finite shared-oracle reference experiment. -/
theorem actionOracleRetriesFromSource_uniform {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    actionOracleRetriesFromSource urs hk inputs witness vkTranscriptRepr
        (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache =
      actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache := by
  have h := uniformRetryTape_source_map_law budget (actionRawOracleTape (actions := actions) (k := urs.k))
    (fun tapes => actionOracleRetriesFromTapes urs hk inputs witness vkTranscriptRepr tapes cache)
  rw [actionRawOracleTape_law] at h
  exact h.trans (actionOracleRetries_fromTape urs hk inputs witness vkTranscriptRepr budget cache)

end Zcash.Snark.ZeroKnowledge

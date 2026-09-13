import Zcash.Snark.ZeroKnowledge.ActionFiatShamirBits
import Zcash.Snark.ZeroKnowledge.OracleRetryTape
import Zcash.Snark.ZeroKnowledge.OracleRetrySimulation
import Zcash.Snark.ZeroKnowledge.OracleRetryBounds

/-!
# Finite Action retries sharing one random oracle

The statement and witness stay fixed while each attempt takes fresh independent
private randomness and the previous oracle cache. The simulator receives no
witness and uses its existing fixed-bit implementation. Histories retain failed
prefixes, received challenges, terminal errors, programming failure, and explicit
exhaustion. The final cache is part of the compared observation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability

/-- Real reference attempts with fresh private randomness and one evolving oracle cache. -/
noncomputable def actionOracleRetries {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  oracleRetries (actionOracleProver urs hk inputs witness vkTranscriptRepr) budget cache

/-- Witness-free retries using the fixed-bit simulator and the same retained-cache policy. -/
noncomputable def actionOracleBitRetries {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  oracleRetries (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) budget cache

/-- Execute real retained retries from a fixed list of reference private-and-reply tapes. -/
def actionOracleRetriesFromTapes {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (tapes : List (ActionOracleTape actions urs.k))
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard) :=
  runOracleRetries (actionOracleRunTape urs hk inputs witness vkTranscriptRepr) tapes cache

/-- Execute the public simulator's retained retries from fixed Boolean tapes. -/
def actionOracleBitRetriesFromTapes {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (tapes : List (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool))
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard) :=
  runOracleRetries (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr) tapes cache

/-- The real retry law is exactly its deterministic runner on independent reference attempt tapes. -/
theorem actionOracleRetries_fromTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (retryAttemptTape (actionOracleTapeLaw actions urs.k) budget).map
        (fun tapes => actionOracleRetriesFromTapes urs hk inputs witness vkTranscriptRepr tapes cache) =
      actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache :=
  oracleRetries_fromTape (actionOracleTapeLaw actions urs.k)
    (actionOracleRunTape urs hk inputs witness vkTranscriptRepr)
    (actionOracleProver urs hk inputs witness vkTranscriptRepr)
    (actionOracleRunTape_law urs hk inputs witness vkTranscriptRepr) budget cache

/-- The simulated retry law is exactly its public runner on independent fixed-size Boolean tapes. -/
theorem actionOracleBitRetries_fromTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (retryAttemptTape (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)) budget).map
        (fun tapes => actionOracleBitRetriesFromTapes urs hk inputs vkTranscriptRepr tapes cache) =
      actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache :=
  oracleRetries_fromTape _ (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr)
    (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) (fun _ => rfl) budget cache

/-- The complete shared-oracle history has the finite two-sided comparison, including exhaustion and programming failure. -/
theorem actionOracleRetries_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMFEventBiasLE (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache)
        (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache)
        (oracleRetryError actions cache.length budget) ∧
      PMFEventBiasLE (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache)
        (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache)
        (oracleRetryError actions cache.length budget) := by
  have h := oracleRetries_simulation_error_bound
    (actionOracleProver urs hk inputs witness vkTranscriptRepr)
    (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) 22 (plonkBitSimulationErrorBound actions)
    (fun bound cache hcache => by
      have h := actionOracleBit_simulation_error_bound urs hk inputs witness hvalid hpositive hW vkTranscriptRepr cache
      have hbudget := plonkBitSimulationErrorBound_mono_queries actions hcache
      exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hbudget),
        fun event => (h.2 event).trans (add_le_add le_rfl hbudget)⟩)
    (actionOracleProver_cache_length_le urs hk inputs witness vkTranscriptRepr) budget cache.length cache le_rfl
  simpa only [oracleRetryError_eq_stateful] using h

end Zcash.Snark.ZeroKnowledge

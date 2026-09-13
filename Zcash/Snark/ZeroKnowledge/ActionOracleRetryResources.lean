import Zcash.Snark.ZeroKnowledge.ActionOracleRetry
import Zcash.Snark.ZeroKnowledge.OracleRetryResources

/-!
# Persistent Action oracle state and finite retry resources

The real prover and fixed-bit simulator preserve every earlier oracle answer.
Each retained attempt adds at most twenty-two entries, including on ordinary
prover failure; simulator programming failure keeps the prior cache. A finite
simulator tape allocation contains exactly the prescribed number of bit blocks.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action

/-- Every supported real Action attempt preserves previously stored raw oracle answers. -/
theorem actionOracleProver_keeps {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (observation : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)))
    (hobs : observation ∈ (actionOracleProver urs hk inputs witness vkTranscriptRepr cache).support)
    (query : TranscriptHashAddress) (reply : Fin challengeDigestCard)
    (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup (oracleAttemptCache cache observation) query = some reply := by
  rw [actionOracleProver, PMF.mem_support_bind_iff] at hobs
  obtain ⟨privateTape, _, hobs⟩ := hobs
  rw [PMF.mem_support_map_iff] at hobs
  obtain ⟨output, houtput, rfl⟩ := hobs
  exact cachedOracleLaw_keeps _ (actionOracleComp_queryBound urs hk inputs witness privateTape vkTranscriptRepr)
    cache output houtput query reply hstored

/-- Every fixed-bit simulator execution preserves stored answers, including the programming-failure branch. -/
theorem actionOracleSimulatorFromBits_keeps {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (bits : Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)
    (query : TranscriptHashAddress) (reply : Fin challengeDigestCard)
    (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup (oracleAttemptCache cache
      (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr cache bits)) query = some reply := by
  unfold actionOracleSimulatorFromBits actionOracleSimulatorFromRawTape actionOracleSimulatorFromTapes
  exact programOracleView_attemptCache_keeps cache _ query reply hstored

/-- Every supported simulator attempt inherits the fixed-tape answer-preservation theorem. -/
theorem actionOracleBitSimulator_keeps {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (observation : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)))
    (hobs : observation ∈ (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache).support)
    (query : TranscriptHashAddress) (reply : Fin challengeDigestCard)
    (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup (oracleAttemptCache cache observation) query = some reply := by
  rw [actionOracleBitSimulator, PMF.mem_support_map_iff] at hobs
  obtain ⟨bits, _, rfl⟩ := hobs
  exact actionOracleSimulatorFromBits_keeps urs hk inputs vkTranscriptRepr cache bits query reply hstored

/-- The real retry experiment adds at most twenty-two oracle entries per available attempt. -/
theorem actionOracleRetries_cache_length_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache).support) :
    output.2.length ≤ cache.length + 22 * budget :=
  oracleRetries_cache_length_le _ 22
    (actionOracleProver_cache_length_le urs hk inputs witness vkTranscriptRepr) budget cache output houtput

/-- The bit-simulator retry experiment obeys the same full cache budget. -/
theorem actionOracleBitRetries_cache_length_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache).support) :
    output.2.length ≤ cache.length + 22 * budget :=
  oracleRetries_cache_length_le _ 22
    (actionOracleBitSimulator_cache_length_le urs hk inputs vkTranscriptRepr) budget cache output houtput

/-- All real attempts share the previously recorded oracle answers. -/
theorem actionOracleRetries_keeps {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleRetries urs hk inputs witness vkTranscriptRepr budget cache).support)
    (query : TranscriptHashAddress) (reply : Fin challengeDigestCard)
    (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup output.2 query = some reply :=
  oracleRetries_keeps _ (actionOracleProver_keeps urs hk inputs witness vkTranscriptRepr)
    budget cache output houtput query reply hstored

/-- All simulated attempts share the same recorded answers, including after preceding failed prefixes. -/
theorem actionOracleBitRetries_keeps {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (budget : ℕ)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (output : RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleBitRetries urs hk inputs vkTranscriptRepr budget cache).support)
    (query : TranscriptHashAddress) (reply : Fin challengeDigestCard)
    (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup output.2 query = some reply :=
  oracleRetries_keeps _ (actionOracleBitSimulator_keeps urs hk inputs vkTranscriptRepr)
    budget cache output houtput query reply hstored

/-- The simulator's complete finite tape allocation has a checked exact bit-input length. -/
theorem actionOracleBitRetries_tape_bits {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (budget : ℕ) (tapes : List (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool))
    (htapes : tapes ∈ (retryAttemptTape
      (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)) budget).support) :
    tapes.length * actionOracleSimulatorBitCount actions urs.k = budget * (512 * (132 * actions + 58)) := by
  rw [retryAttemptTape_support_length _ budget tapes htapes, hk, actionOracleSimulatorBitCount_eleven]

end Zcash.Snark.ZeroKnowledge

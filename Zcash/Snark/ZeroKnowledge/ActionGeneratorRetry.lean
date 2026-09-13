import Zcash.Snark.ZeroKnowledge.ActionOracleRetrySource
import Zcash.Snark.ZeroKnowledge.GeneratedRetryCoins

/-!
# Action retries from one continuing private word generator

Each started attempt allocates its full `148m + 46` raw private words, even if
the reference attempt aborts before using all of them. Remaining words in that
block are discarded. Later blocks are allocated only when the additional caller
policy selects a terminal failure. This caller is absent from the released
Orchard proof entry point.
The word generator is never reseeded; its private final state advances by the
number of started attempts times the block width. It is not revealed to the
verifier. Oracle reply slots remain independent, separately supplied inputs.

The complete observed history and final oracle cache equal the existing replay
from the generator's budget-length prefix. This exact identity permits a PRNG
assumption for that whole prefix, without assuming independent generated blocks.
It specifies an allocation policy, not Rust early-abort cursor correspondence.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common
open Zcash.Common.Probability

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action

/-- Allocate the full private prefix by carrying one word-generator state across all attempt blocks. -/
def actionGeneratorRetryTape {Generator : Type*}
    (next : Generator → Fin challengeDigestCard × Generator) (actions budget : ℕ)
    (generator : Generator) : RawPrivateRetryTape actions budget :=
  (drawGeneratorBlocks next (fieldSampleCount actions) budget generator).1

/-- Execute actual shared-oracle attempts with separately supplied replies and on-demand private blocks. -/
def actionGeneratedOracleRetries {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) {budget : ℕ}
    (replies : OracleReplyRetryTape urs.k budget)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) (generator : Generator) :
    (RetryHistory (Option ProverAttemptResult) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) × Generator :=
  runGeneratedCoinRetries
    (fun cache replies privateTape => oracleAttemptState cache
      (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache (actionRawOracleTape (replies, privateTape))))
    oracleRetrySet (drawGeneratorTape next (fieldSampleCount actions)) (List.ofFn replies) cache generator

/-- The actual observation agrees exactly with the generator-prefix source replay, including every stopping branch. -/
theorem actionGeneratedOracleRetries_replay {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) {budget : ℕ}
    (replies : OracleReplyRetryTape urs.k budget)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) (generator : Generator) :
    (actionGeneratedOracleRetries urs hk inputs witness vkTranscriptRepr next replies cache generator).1 =
      actionOracleRetriesFromRawTapes urs hk inputs witness vkTranscriptRepr replies
        (actionGeneratorRetryTape next actions budget generator) cache := by
  simp only [actionGeneratedOracleRetries, runGeneratedCoinRetries_replay,
    List.length_ofFn, zip_ofFn_pair, actionOracleRetriesFromRawTapes,
    actionOracleRetriesFromTapes, runOracleRetries, actionGeneratorRetryTape, drawGeneratorBlocks]
  simp only [drawGeneratorTape_cast]
  let tapes := List.ofFn (fun i => (replies i,
    (drawGeneratorTape (drawGeneratorTape next (fieldSampleCount actions)) budget generator).1 i))
  have h := runStatefulRetries_map
    (fun cache tape => oracleAttemptState cache (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache tape))
    oracleRetrySet (actionRawOracleTape (actions := actions) (k := urs.k)) tapes cache
  simpa only [tapes, List.map_ofFn, Function.comp_def] using h.symm

/-- The private generator advances through started attempts only, with exactly one full raw block per attempt. -/
theorem actionGeneratedOracleRetries_state {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) {budget : ℕ}
    (replies : OracleReplyRetryTape urs.k budget)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) (generator : Generator) :
    (actionGeneratedOracleRetries urs hk inputs witness vkTranscriptRepr next replies cache generator).2 =
      ((fun g => (next g).2)^[
        (actionGeneratedOracleRetries urs hk inputs witness vkTranscriptRepr next replies cache generator).1.1.attempts.length
          * fieldSampleCount actions]) generator :=
  runGeneratedCoinRetries_word_state _ oracleRetrySet next (List.ofFn replies) cache generator

/-- Every private block is the corresponding consecutive segment of the same generator stream. -/
theorem actionGeneratorRetryTape_at {Generator : Type*}
    (next : Generator → Fin challengeDigestCard × Generator) (actions budget : ℕ)
    (generator : Generator) (attempt : Fin budget) (slot : Fin (fieldSampleCount actions)) :
    actionGeneratorRetryTape next actions budget generator attempt slot =
      (next (((fun g => (next g).2)^[attempt.val * fieldSampleCount actions + slot.val]) generator)).1 :=
  drawGeneratorBlocks_at next (fieldSampleCount actions) budget generator attempt slot

/-- Independent public replies and a generated private prefix have exactly the on-demand runner's observation law. -/
theorem actionGeneratedOracleRetries_source_law {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (budget : ℕ)
    (generators : PMF Generator) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    sourceTapeExperiment (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget)) generators
        (fun replies generator =>
          (actionGeneratedOracleRetries urs hk inputs witness vkTranscriptRepr next replies cache generator).1) =
      actionOracleRetriesFromSource urs hk inputs witness vkTranscriptRepr
        (generators.map (actionGeneratorRetryTape next actions budget)) cache := by
  simp only [sourceTapeExperiment, actionOracleRetriesFromSource, PMF.map_comp]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget)))
  funext replies
  apply congrArg (PMF.map (p := generators))
  funext generator
  exact actionGeneratedOracleRetries_replay urs hk inputs witness vkTranscriptRepr next replies cache generator

/-- Total consumed private words are bounded by the entire retry prefix covered by the PRNG assumption. -/
theorem actionGeneratedOracleRetries_word_budget {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) {budget : ℕ}
    (replies : OracleReplyRetryTape urs.k budget)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) (generator : Generator) :
    (actionGeneratedOracleRetries urs hk inputs witness vkTranscriptRepr next replies cache generator).1.1.attempts.length
        * fieldSampleCount actions ≤ budget * (148 * actions + 46) := by
  have h := runGeneratedCoinRetries_length_le
    (fun cache replies privateTape => oracleAttemptState cache
      (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache (actionRawOracleTape (replies, privateTape))))
    oracleRetrySet (drawGeneratorTape next (fieldSampleCount actions)) (List.ofFn replies) cache generator
  simpa only [List.length_ofFn, fieldSampleCount] using Nat.mul_le_mul_right (fieldSampleCount actions) h

end Zcash.Snark.ZeroKnowledge

import Zcash.Snark.ZeroKnowledge.ActionOracleStreamSimulation
import Zcash.Snark.ZeroKnowledge.ActionGeneratorRetry
import Zcash.Snark.ZeroKnowledge.RetryRecordedSource

/-!
# Whole private prefixes for the complete recorded Action view

The finite observation retains every intermediate public cache, as does the
complete-stream theorem. The private prefix is one joint source, independent of
the raw oracle reply slots. Its uniform law is the existing reference prover;
its generated law is the existing continuing-generator execution.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Finite attempted results with all returned public caches and the final cache. -/
abbrev ActionRetryRecordedView :=
  RetryHistory (Option ProverAttemptResult × ActionRetryOracleState) × ActionRetryOracleState

/-- Replay the actual Action steps with all intermediate caches observed. -/
def actionOracleRecordFromRawTapes {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) {budget : ℕ} (replies : OracleReplyRetryTape urs.k budget)
    (privateTape : RawPrivateRetryTape actions budget) (cache : ActionRetryOracleState) : ActionRetryRecordedView :=
  recordedCoinRetries (fun state coins tape =>
    actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape))
    oracleRetrySet replies privateTape cache

/-- A whole private source with independent reply slots, retaining the complete finite public history. -/
noncomputable def actionOracleRecordFromSource {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) {budget : ℕ} (source : PMF (RawPrivateRetryTape actions budget))
    (cache : ActionRetryOracleState) : PMF ActionRetryRecordedView :=
  recordedCoinRetriesFromSource (fun state coins tape =>
    actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape)) oracleRetrySet source cache

/-- The extra public cache observations erase exactly to the existing finite Action retry observation. -/
theorem actionOracleRecordFromRawTapes_forget {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) {budget : ℕ} (replies : OracleReplyRetryTape urs.k budget)
    (privateTape : RawPrivateRetryTape actions budget) (cache : ActionRetryOracleState) :
    forgetRetryStates (actionOracleRecordFromRawTapes urs hk inputs witness vkTranscriptRepr replies privateTape cache) =
      actionOracleRetriesFromRawTapes urs hk inputs witness vkTranscriptRepr replies privateTape cache := by
  rw [actionOracleRecordFromRawTapes, recordedCoinRetries, runStatefulRetries_forget_states]
  have h := runStatefulRetries_map
    (fun state tape => oracleAttemptState state (actionOracleRunTape urs hk inputs witness vkTranscriptRepr state tape))
    oracleRetrySet (actionRawOracleTape (actions := actions) (k := urs.k))
    (List.ofFn (fun i => (replies i, privateTape i))) cache
  simpa only [actionOracleRetriesFromRawTapes, actionOracleRetriesFromTapes, runOracleRetries,
    List.map_ofFn, Function.comp_def, actionRawOracleStep] using h.symm

/-- Uniform raw private prefixes reproduce the exact recorded reference retry law. -/
theorem actionOracleRecordFromSource_uniform {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) :
    actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
        (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache =
      statefulRetryRecorded (oracleRetryTransition (actionOracleProver urs hk inputs witness vkTranscriptRepr))
        oracleRetrySet budget cache := by
  rw [actionOracleRecordFromSource, recordedCoinRetriesFromSource_uniform]
  apply congrArg (fun attempt => statefulRetryRecorded attempt oracleRetrySet budget cache)
  funext prior
  exact actionRawOracleStep_law urs hk inputs witness vkTranscriptRepr prior

/-- Generated recorded prefixes are exactly the on-demand execution from the same continuing generator. -/
theorem actionOracleRecordFromSource_generated {actions : ℕ} {Generator : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (next : Generator → Fin challengeDigestCard × Generator) (generators : PMF Generator)
    (budget : ℕ) (cache : ActionRetryOracleState) :
    generators.bind (generatedRetryRecordLaw (fun state coins tape =>
        actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape))
        oracleRetrySet (drawGeneratorTape next (fieldSampleCount actions)) budget cache) =
      actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
        (generators.map (actionGeneratorRetryTape next actions budget)) cache := by
  rw [generatedRetryRecordLaw_source]
  unfold actionOracleRecordFromSource
  apply congrArg (fun source => recordedCoinRetriesFromSource
    (fun state coins tape => actionRawOracleStep urs hk inputs witness vkTranscriptRepr state (coins, tape))
    oracleRetrySet source cache)
  apply congrArg (PMF.map (p := generators))
  funext generator
  rfl

/-- The uniform private-prefix exhaustion event has the complete-stream geometric tail bound. -/
theorem actionOracleRecordFromSource_exhaustion_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) :
    (actionOracleRecordFromSource urs hk inputs witness vkTranscriptRepr
      (PMF.uniformOfFintype (RawPrivateRetryTape actions budget)) cache).toOuterMeasure
        {output | output.1.exhausted = true} ≤
      actionOracleRetryRate actions ^ budget + oracleRetryPotential actions cache.length := by
  rw [actionOracleRecordFromSource_uniform]
  have h := (actionOracleRetryRecorded_error_bound urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache).1 {output | output.1.exhausted = true}
  exact h.trans (add_le_add
    (statefulRetryRecorded_exhaustion_le _ oracleRetrySet (actionOracleRetryRate actions)
      (actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr) budget cache) le_rfl)

end Zcash.Snark.ZeroKnowledge

import Zcash.Snark.ZeroKnowledge.ActionFiatShamir
import Zcash.Snark.ZeroKnowledge.Zakura.Attempt

/-!
# One Action-bundle call with the released API's failure behavior

Public identity commitments are rejected before any prover oracle query.
Otherwise one reference attempt determines the returned proof, error, or
panic, retaining the oracle cache. There is no retry step.

The existing simulation bound survives this public guard and deterministic
observation. These are model theorems: the optimized Rust computation's
agreement with the reference attempt is recorded separately in `PROVENANCE.md`.
The request has matching circuit/key versions and satisfying witness rows;
allocation failures, arbitrary invalid Rust requests and process side channels
are outside this observation.
-/

namespace Zcash.Snark.ZeroKnowledge.Zakura

open Zcash.Arithmetic (Fp URS scalarFieldOrder)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

-- Keep the concrete oracle implementation folded in proofs about its public wrapper.
attribute [local irreducible] actionOracleInitial actionOracleRunTape
  actionOracleProver actionOracleTapeLaw

/-- The public oracle cache remains observable after a failed proof call. -/
abbrev OracleObservation :=
  Option (AttemptOutcome × OracleCache TranscriptHashAddress (Fin challengeDigestCard))

/-- Convert the returned attempt and retain its cache; simulator programming failure stays explicit. -/
def observeOracleResult
    (result : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :
    OracleObservation :=
  result.map fun output => (observeAttempt output.1, output.2)

/-- Run one fixed-tape reference call, rejecting a public identity without querying the oracle. -/
def actionRunTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (tapes : ActionOracleTape actions urs.k) : OracleObservation :=
  if acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) then
    observeOracleResult (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache tapes)
  else some (.error .transcript, cache)

/-- The one-call model uses the original private randomness law after the public initialization guard. -/
noncomputable def actionProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF OracleObservation :=
  if acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) then
    (actionOracleProver urs hk inputs witness vkTranscriptRepr cache).map observeOracleResult
  else PMF.pure (some (.error .transcript, cache))

/-- The witness-free simulator applies the same public rejection and single-call observation. -/
noncomputable def actionSimulator [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF OracleObservation :=
  if acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) then
    (actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache).map observeOracleResult
  else PMF.pure (some (.error .transcript, cache))

/-- Independent raw oracle replies and private field tapes execute exactly the single-call model. -/
theorem actionRunTape_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (actionOracleTapeLaw actions urs.k).map (actionRunTape urs hk inputs witness vkTranscriptRepr cache) =
      actionProver urs hk inputs witness vkTranscriptRepr cache := by
  by_cases haccept : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true
  · have hrun : actionRunTape urs hk inputs witness vkTranscriptRepr cache =
        observeOracleResult ∘ actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache := by
      funext tapes
      exact if_pos haccept
    rw [hrun, ← PMF.map_comp, actionOracleRunTape_law]
    exact (if_pos haccept).symm
  · have hrun : actionRunTape urs hk inputs witness vkTranscriptRepr cache =
        fun _ => some (.error .transcript, cache) := by
      funext tapes
      exact if_neg haccept
    rw [hrun, actionProver, if_neg haccept]
    exact PMF.map_const _ _

/-- The fixed-tape rejection branch leaves the cache unchanged and does not inspect either tape. -/
theorem actionRunTape_rejects {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (tapes : ActionOracleTape actions urs.k)
    (hreject : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = false) :
    actionRunTape urs hk inputs witness vkTranscriptRepr cache tapes = some (.error .transcript, cache) := by
  simp only [actionRunTape, hreject, Bool.false_eq_true, ↓reduceIte]

/-- Rejected public initialization has the same deterministic observation for prover and simulator. -/
theorem action_publicRejection [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hreject : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = false) :
    actionProver urs hk inputs witness vkTranscriptRepr cache =
      actionSimulator urs hk inputs vkTranscriptRepr cache := by
  simp only [actionProver, actionSimulator, hreject, Bool.false_eq_true, ↓reduceIte]

/-- **Released API observation.** The public guard and failure outcomes preserve the reference
one-attempt bound, including the final oracle cache and simulator programming failure. -/
theorem action_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := plonkSimulationErrorBound actions + (cache.length : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionProver urs hk inputs witness vkTranscriptRepr cache)
        (actionSimulator urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionSimulator urs hk inputs vkTranscriptRepr cache)
        (actionProver urs hk inputs witness vkTranscriptRepr cache) error := by
  by_cases haccept : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true
  · simp only [actionProver, actionSimulator, haccept, ↓reduceIte]
    have h := actionFiatShamir_program_simulation_error_bound urs hk inputs witness
      hvalid hpositive hW vkTranscriptRepr cache
    exact ⟨eventBias_map h.1 observeOracleResult, eventBias_map h.2 observeOracleResult⟩
  · simp only [actionProver, actionSimulator, haccept]
    constructor <;> intro event <;> exact le_self_add

end Zcash.Snark.ZeroKnowledge.Zakura

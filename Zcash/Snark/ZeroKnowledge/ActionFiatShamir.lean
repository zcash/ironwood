import Zcash.Snark.ZeroKnowledge.ActionOracleResources
import Zcash.Snark.ZeroKnowledge.PlonkQuerySchedule

/-!
# Action Fiat–Shamir simulation in a programmable classical random oracle

The one-attempt experiment permits adaptive statement selection and oracle
queries both before and after the proof. It uses the actual Action instance
commitments and the existing verifier's complete byte-query schedule. Oracle
answers are uniform raw 512-bit words and private prover fields follow the
specified independent wide-reduced law.

For `m > 0` Actions and `q` preprocessing queries, every event-probability
difference in either direction is at most `epsilon(m) + q / p`. The simulator
uses no witness. The observed attempt retains all emitted prefixes and statuses;
its explicit programming failure is included in this bound. Completion of an
attempt does not assert verifier acceptance.

The setup is fixed, with eleven rounds and nonidentity `W`; each selected
witness satisfies `ActionZkRelation`. The statement prefix uses the existing
Lean protocol's total coordinate encoding. Concrete hash security, Rust
correspondence, and retries sharing oracle state are separate claims.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS scalarFieldOrder)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- Every statement-bound verifier challenge uses the reference oracle program's exact byte address. -/
theorem actionFiatShamir_challengeSchedule {actions : ℕ} (urs : URS VestaG)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (oracle : TranscriptHashAddress → Fin challengeDigestCard)
    (proof : ProofString (plonkProofShape actions urs.k) Fp VestaG) (index : Fin (urs.k + 11)) :
    plonkAttemptChallenge
        (deriveChallengesForStatement (byteFiatShamir oracle) vkTranscriptRepr
          (actionCircuit.instanceCommitment urs inputs) proof) index.val =
      ((oracle (protocolQueryAddress (actionOracleInitial urs vkTranscriptRepr inputs)
        (plonkAttemptTrace proof) index.val)).val : Fp) :=
  byteFiatShamir_protocolQuery _ _ _ _

/-- The actual online Action reference program makes at most twenty-two oracle queries per attempt. -/
theorem actionFiatShamir_prover_queryBound {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (privateTape : Fin (fieldSampleCount actions) → Fp) (vkTranscriptRepr : Fp) :
    (actionOracleComp urs hk inputs witness privateTape vkTranscriptRepr).QueryBound 22 := by
  simpa only [hk] using actionOracleComp_queryBound urs hk inputs witness privateTape vkTranscriptRepr

/-- The explicit simulator tape program realizes the same one-attempt statistical comparison. -/
theorem actionFiatShamir_program_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := plonkSimulationErrorBound actions + (cache.length : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs witness vkTranscriptRepr cache) error := by
  rw [actionOracleSimulatorProgram_law urs hk inputs hW vkTranscriptRepr cache]
  exact actionOracle_cached_simulation_error_bound urs hk inputs witness hvalid hpositive hW vkTranscriptRepr cache

end Zcash.Snark.ZeroKnowledge

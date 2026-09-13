import Zcash.Snark.ZeroKnowledge.ActionProverCompleteness
import Zcash.Snark.ZeroKnowledge.Zakura.Action

/-!
# Acceptance of one initialized Zakura proof call

The existing interactive acceptance theorem transfers to `actionProver` with
an empty initial oracle cache. Successive transcript addresses are distinct, so
lazy oracle execution and the independent raw-reply experiment agree on every
tape, including exceptional values. The typed marginal is exactly the prover
law used by `wideActionZkRelation_completeness_error_bound`; no additional
statistical error is introduced.

Acceptance requires returned canonical proof bytes, acceptance of their typed
proof by `DeployedAccepts`, and agreement of every scheduled challenge with the
final oracle cache. Errors, panics, and missing results cannot qualify. As in
the existing acceptance theorem, decoding is a typed boundary; this is not a
byte-parser or concrete BLAKE2b correctness theorem.

Public initialization is an explicit premise. By `acceptsPublicPrefix_iff`, it
requires the public point commitments to be nonidentity. This theorem neither
derives that condition from witness validity nor charges it to the sampling-error
budget. A rejected prefix fails deterministically. The probability bound below
is for one call with a fresh random oracle, not an arbitrary prepopulated cache.
-/

namespace Zcash.Snark.ZeroKnowledge.Zakura

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Fresh-oracle execution returns the exact independently generated proof and its installed replies. -/
theorem actionRunTape_empty_eq_programmed {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (tapes : ActionOracleTape actions urs.k)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true) :
    actionRunTape urs hk inputs witness vkTranscriptRepr [] tapes =
      observeOracleResult (actionOracleProgramView urs vkTranscriptRepr inputs []
        (actionOracleDigestView urs hk inputs witness tapes)) := by
  simp only [actionRunTape, hinit, ↓reduceIte]
  rw [actionOracleRunTape_eq_programmed urs hk inputs witness vkTranscriptRepr [] tapes
    (actionOracleProgramView_empty_ne_none urs vkTranscriptRepr inputs _)]

/-- Returned canonical bytes with an accepted typed proof and all of its oracle answers.

This public predicate uses no witness. Its typed proof must have completed the
canonical writer, and every one of its `k + 11` challenges must be read from the
returned cache at the actual transcript address. -/
def actionAcceptedCallSet {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) : Set OracleObservation :=
  {output | ∃ (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard))
      (proof : ProofString (plonkProofShape actions urs.k) Fp VestaG)
      (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)),
    let view := (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof)
    output = some (.proof (encodedPlonkAttempt view).2.proof, cache) ∧
      view ∈ actionAcceptedAttemptSet urs hk inputs ∧
      ∀ i : Fin (urs.k + 11),
        oracleCacheLookup cache
          (protocolQueryAddress (actionOracleInitial urs vkTranscriptRepr inputs)
            (plonkAttemptTrace proof) i.val) = some (digests i)}

/-- Membership requires an actual proof result; neither an error, a panic, nor `none` suffices. -/
theorem actionAcceptedCallSet_returns_proof {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (output : OracleObservation)
    (haccepted : output ∈ actionAcceptedCallSet urs hk inputs vkTranscriptRepr) :
    ∃ bytes cache, output = some (.proof bytes, cache) := by
  obtain ⟨digests, proof, cache, houtput, _⟩ := haccepted
  exact ⟨_, cache, houtput⟩

/-- Programming an accepted typed proof installs every answer required by the call predicate. -/
private theorem programmedAttempt_mem_acceptedCallSet {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions urs.k) Fp VestaG)
    (haccepted : (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof) ∈
      actionAcceptedAttemptSet urs hk inputs) :
    observeOracleResult (programOracleView []
      (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) digests proof)) ∈
      actionAcceptedCallSet urs hk inputs vkTranscriptRepr := by
  let view := (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof)
  let raw := plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) digests proof
  have hgood : programOracleTrace [] raw.2 ≠ none :=
    programOracleTrace_ne_none_of_fresh raw.2 []
      (plonkRawOracleView_queries_nodup _ _ _) (by intro query hquery; simp)
  cases hcache : programOracleTrace [] raw.2 with
  | none => exact False.elim (hgood hcache)
  | some cache =>
    have hrun : observeOracleResult (programOracleView [] raw) =
        some (observeAttempt raw.1, cache) := by
      simp only [programOracleView, hcache, observeOracleResult, Option.map_some]
    have hresult : raw.1 = (encodedPlonkAttempt view).2 := by
      simpa only [raw, view, encodedPlonkAttempt, plonkAttemptObservation] using
        plonkRawOracleView_result (actionOracleInitial urs vkTranscriptRepr inputs) digests proof
    have hcomplete := ((actionAcceptedAttemptSet_mem_iff urs hk inputs view).mp haccepted).1
    rw [hrun, hresult]
    simp only [observeAttempt, hcomplete]
    refine ⟨digests, proof, cache, rfl, haccepted, ?_⟩
    intro i
    exact programOracleTrace_answers raw.2 [] cache hcache
      (protocolQueryAddress (actionOracleInitial urs vkTranscriptRepr inputs)
        (plonkAttemptTrace proof) i.val, digests i)
      (plonkRawOracleView_query_mem_of_complete
        (actionOracleInitial urs vkTranscriptRepr inputs) digests proof hcomplete i)

/-- An initialized fresh-oracle call preserves every successful typed acceptance certificate. -/
theorem actionRunTape_mem_acceptedCallSet {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (tapes : ActionOracleTape actions urs.k)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true)
    (haccepted : (actionOracleDigestView urs hk inputs witness tapes).2 ∈
      actionAcceptedAttemptSet urs hk inputs) :
    actionRunTape urs hk inputs witness vkTranscriptRepr [] tapes ∈
      actionAcceptedCallSet urs hk inputs vkTranscriptRepr := by
  rw [actionRunTape_empty_eq_programmed urs hk inputs witness vkTranscriptRepr tapes hinit]
  exact programmedAttempt_mem_acceptedCallSet urs hk inputs vkTranscriptRepr tapes.1
    (actionOracleDigestView urs hk inputs witness tapes).2.2 haccepted

/-- **Initialized released-call model.** The same completeness bound holds with a fresh random oracle. -/
theorem action_completeness_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hpositive : 0 < actions) (hW : urs.w ≠ 0)
    (vkTranscriptRepr : Fp)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true) :
    (actionProver urs hk inputs witness vkTranscriptRepr []).toOuterMeasure
      (actionAcceptedCallSet urs hk inputs vkTranscriptRepr)ᶜ ≤ plonkCompletenessErrorBound actions := by
  have hbound := wideActionZkRelation_completeness_error_bound urs hk inputs witness hvalid hpositive hW
  rw [← actionOracleTypedTape_law urs hk inputs witness, PMF.toOuterMeasure_map_apply] at hbound
  rw [← actionRunTape_law urs hk inputs witness vkTranscriptRepr [], PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ hbound
  apply (actionOracleTapeLaw actions urs.k).toOuterMeasure.mono
  intro tapes hfailure haccepted
  exact hfailure (actionRunTape_mem_acceptedCallSet urs hk inputs witness vkTranscriptRepr
    tapes hinit haccepted)

/-- The application-witness bridge supplies the valid rows for the initialized proof call. -/
theorem actionWitness_completeness_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true) :
    (actionProver urs hk inputs (actionWitnessRowBundle inputs witnesses) vkTranscriptRepr []).toOuterMeasure
      (actionAcceptedCallSet urs hk inputs vkTranscriptRepr)ᶜ ≤ plonkCompletenessErrorBound actions :=
  action_completeness_error_bound urs hk inputs (actionWitnessRowBundle inputs witnesses)
    (actionWitnessRows_relation_capstone urs hk inputs witnesses conditions) hpositive hW vkTranscriptRepr hinit

/-- The probability of returning an accepted proof is at least `1 - eta(m)`. -/
theorem actionWitness_acceptance_probability_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true) :
    1 - plonkCompletenessErrorBound actions ≤
      (actionProver urs hk inputs (actionWitnessRowBundle inputs witnesses) vkTranscriptRepr []).toOuterMeasure
        (actionAcceptedCallSet urs hk inputs vkTranscriptRepr) :=
  success_mass_lower_bound _ _
    (actionWitness_completeness_error_bound urs hk inputs witnesses conditions hpositive hW vkTranscriptRepr hinit)

/-- For `m >= 1`, the initialized call fails to return an accepted proof with probability below `m * 2^(-238)`. -/
theorem actionWitness_completeness_binary_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness)
    (conditions : ∀ action, ActionWitnessConstructionConditions (inputs action) (witnesses action))
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (hinit : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = true) :
    (actionProver urs hk inputs (actionWitnessRowBundle inputs witnesses) vkTranscriptRepr []).toOuterMeasure
      (actionAcceptedCallSet urs hk inputs vkTranscriptRepr)ᶜ < actions * (1 / (2 : ℝ≥0∞) ^ 238) :=
  (actionWitness_completeness_error_bound urs hk inputs witnesses conditions
    hpositive hW vkTranscriptRepr hinit).trans_lt
    (plonkCompletenessErrorBound_lt_actions_mul_two_pow (by omega))

/-- Rejected public initialization fails with probability one, independently of witness and oracle cache. -/
theorem action_initialization_failure {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hreject : acceptsPublicPrefix (actionOracleInitial urs vkTranscriptRepr inputs) = false) :
    (actionProver urs hk inputs witness vkTranscriptRepr cache).toOuterMeasure
      (actionAcceptedCallSet urs hk inputs vkTranscriptRepr)ᶜ = 1 := by
  classical
  simp only [actionProver, hreject, Bool.false_eq_true, ↓reduceIte]
  have hfailure : some (.error .transcript, cache) ∉ actionAcceptedCallSet urs hk inputs vkTranscriptRepr := by
    intro haccepted
    obtain ⟨bytes, finalCache, houtput⟩ :=
      actionAcceptedCallSet_returns_proof urs hk inputs vkTranscriptRepr _ haccepted
    cases houtput
  simp [PMF.toOuterMeasure_pure_apply, hfailure]

end Zcash.Snark.ZeroKnowledge.Zakura

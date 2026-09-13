import Zcash.Snark.ZeroKnowledge.PlonkChallengeCausality
import Zcash.Snark.ZeroKnowledge.ProtocolStages

/-!
# The existing prover schedule as causal stages

The stage decomposition is proved equal to the existing verifier's pre-IPA
transcript and the specified IPA suffix. Empty stages preserve consecutive
receives. The final scalars follow every challenge. This reduces full-prefix
causality to each stage's dependency on its already received challenge prefix.

The final theorem is a composition interface; its stage-dependency premise
must still be discharged by the concrete reference prover on a fixed tape.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Exactly the verifier's evaluation-scalar block, before `x1,x2`. -/
def plonkEvaluationStage {shape : Shape} {F G : Type*} (proof : ProofString shape F G) :
    List (TranscriptElt F G) :=
  absorbScalars2 proof.instanceEvals ++ absorbScalars2 proof.adviceEvals ++
    absorbScalars proof.fixedEvals ++ [.scalar proof.vanishingRandomEval] ++
    absorbScalars proof.permutationCommonEvals ++
    (List.ofFn (fun a => (List.ofFn (fun s => absorbPermSet (proof.permutationSetEvals a s))).flatten)).flatten ++
    (List.ofFn (fun a => (List.ofFn (fun l => absorbLookup (proof.lookupEvals a l))).flatten)).flatten

/-- The eleven pre-IPA message blocks, including empty blocks between consecutive receives. -/
def plonkPreIpaStages {shape : Shape} {F G : Type*} (proof : ProofString shape F G) :
    Fin 11 → List (TranscriptElt F G) :=
  ![absorbPoints2 proof.adviceCommitments,
    absorbLookupPermuted proof.lookupPermutedInput proof.lookupPermutedTable,
    [],
    absorbPoints2 proof.permutationProduct ++ absorbPoints2 proof.lookupProduct ++ [.point proof.vanishingRandom],
    absorbPoints proof.hPieces,
    plonkEvaluationStage proof,
    [],
    [.point proof.multiopenQPrime],
    absorbScalars proof.multiopenU,
    [.point proof.ipaS],
    []]

/-- Every intermediate message block is followed by precisely its next verifier challenge. -/
def plonkStageMessages {shape : Shape} {F G : Type*} (proof : ProofString shape F G) :
    Fin (11 + shape.k) → List (TranscriptElt F G) :=
  Fin.addCases (plonkPreIpaStages proof)
    (fun j => [.point (proof.ipaRounds j).1, .point (proof.ipaRounds j).2])

/-- The evaluation block contains no hidden challenge receive. -/
theorem plonkEvaluationStage_challengeCount {shape : Shape} {F G : Type*}
    (proof : ProofString shape F G) : protocolChallengeCount (plonkEvaluationStage proof) = 0 := by
  simp [plonkEvaluationStage, challenges_absorbScalars2, challenges_absorbScalars,
    challenges_absorbPermSet, challenges_absorbLookup, protocolChallengeCount,
    List.map_ofFn, Function.comp_def]

/-- All stage blocks contain only messages; their following receives are supplied by the scheduler. -/
theorem plonkStageMessages_challengeCount {shape : Shape} {F G : Type*}
    (proof : ProofString shape F G) (j : Fin (11 + shape.k)) :
    protocolChallengeCount (plonkStageMessages proof j) = 0 := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [plonkStageMessages, Fin.addCases_left]
    fin_cases i <;>
      simp [plonkPreIpaStages, challenges_absorbPoints2,
        challenges_absorbLookupPermuted, challenges_absorbPoints, challenges_absorbScalars,
        plonkEvaluationStage_challengeCount, protocolChallengeCount]
  · intro i
    simp only [plonkStageMessages, Fin.addCases_right, protocolChallengeCount]

/-- The staged schedule is the existing complete attempt trace, in exactly its original order. -/
theorem plonkAttemptTrace_eq_stages {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) :
    plonkAttemptTrace proof =
      protocolStagesTrace (11 + k) (plonkStageMessages proof) [.scalar proof.ipaC, .scalar proof.ipaF] := by
  have hstages : List.ofFn (fun j : Fin (11 + k) => plonkStageMessages proof j ++ [.challenge]) =
      List.ofFn (fun j => plonkPreIpaStages proof j ++ [.challenge]) ++
        List.ofFn (fun j : Fin k =>
          [.point (proof.ipaRounds j).1, .point (proof.ipaRounds j).2, .challenge]) := by
    rw [List.ofFn_add (n := 11) (m := k)]
    refine congrArg₂ List.append ?_ ?_
    · apply congrArg List.ofFn
      funext j
      change plonkStageMessages proof (Fin.castAdd k j) ++ [.challenge] = _
      apply congrArg (fun block : List (TranscriptElt F G) =>
        block ++ [TranscriptElt.challenge (F := F) (G := G)])
      unfold plonkStageMessages
      exact Fin.addCases_left j
    · apply congrArg List.ofFn
      funext j
      change plonkStageMessages proof (Fin.natAdd 11 j) ++ [.challenge] =
        [.point (proof.ipaRounds j).1, .point (proof.ipaRounds j).2] ++ [.challenge]
      apply congrArg (fun block : List (TranscriptElt F G) =>
        block ++ [TranscriptElt.challenge (F := F) (G := G)])
      unfold plonkStageMessages
      exact Fin.addCases_right j
  rw [protocolStagesTrace_eq_flatten]
  rw [hstages]
  simp [plonkAttemptTrace, plonkPreIpaStages, plonkEvaluationStage,
    preIpaTranscript, List.ofFn_succ, List.append_assoc]

/-- Per-stage dependency on already received coins establishes causality of the complete schedule. -/
theorem plonkAttemptTrace_causal_of_stages {actions k : ℕ} {G : Type*}
    (produce : Challenges k Fp → ProofString (plonkProofShape actions k) Fp G)
    (hstages : ∀ (j : Fin (11 + k)) (left right : Challenges k Fp),
      (∀ i < j.val, plonkAttemptChallenge left i = plonkAttemptChallenge right i) →
        plonkStageMessages (produce left) j = plonkStageMessages (produce right) j) :
    ProtocolCausal plonkAttemptChallenge (fun ch => plonkAttemptTrace (produce ch)) := by
  intro n left right hcoins
  change protocolPrefix n (plonkAttemptTrace (produce left)) =
    protocolPrefix n (plonkAttemptTrace (produce right))
  rw [plonkAttemptTrace_eq_stages, plonkAttemptTrace_eq_stages]
  apply protocolStagesTrace_prefix_congr
  · exact plonkStageMessages_challengeCount (produce left)
  · exact plonkStageMessages_challengeCount (produce right)
  · intro j hj
    apply hstages j left right
    intro i hi
    exact hcoins i (hi.trans_le hj)
  · intro hn
    have h := plonkAttemptChallenge_prefix_injective left right
      (fun i hi => hcoins i (hi.trans_le hn))
    rw [h]

/-- The same stage facts establish causality after encoding and the specified abort checks. -/
theorem plonkObservedPrefix_causal_of_stages {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (produce : Challenges k Fp → ProofString (plonkProofShape actions k) Fp G)
    (hstages : ∀ (j : Fin (11 + k)) (left right : Challenges k Fp),
      (∀ i < j.val, plonkAttemptChallenge left i = plonkAttemptChallenge right i) →
        plonkStageMessages (produce left) j = plonkStageMessages (produce right) j)
    (n : ℕ) (left right : Challenges k Fp)
    (hcoins : ∀ i < n, plonkAttemptChallenge left i = plonkAttemptChallenge right i) :
    observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge left) (plonkAfterChallenge left) 0
        (protocolPrefix n (plonkAttemptTrace (produce left))) =
      observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge right) (plonkAfterChallenge right) 0
        (protocolPrefix n (plonkAttemptTrace (produce right))) :=
  plonkProtocolCausal_observation pointCodec scalarCodec produce
    (plonkAttemptTrace_causal_of_stages produce hstages) n left right hcoins

end Zcash.Snark.ZeroKnowledge

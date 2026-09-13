import Zcash.Snark.ZeroKnowledge.ProverAttempt
import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkChallengePoints
import Zcash.Snark.Soundness.FiatShamir.Ordering

/-!
# The specified PLONK and IPA attempt

The message order is the existing verifier's `preIpaTranscript`, followed by the
same round blocks and the two final scalars. The common public initialization is
fixed separately and contributes no proof bytes. Challenge markers receive fresh
coins from the full interactive tape; they do not perform Fiat–Shamir hashing.

An identity-rejecting point codec stops at the first identity.
The duplicate-opening failure at `x = 0` is checked after `x1,x2`, before writing
`Q'`. Each zero round challenge stops with the IPA panic after both round points.
The observer adds no test on `xi`, on `q`, or on evaluation-domain membership.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The complete message/receive schedule, reusing the existing verifier's prefix. -/
def plonkAttemptTrace {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) : List (TranscriptElt F G) :=
  preIpaTranscript [] proof ++
    (List.ofFn fun j : Fin k =>
      [TranscriptElt.point (proof.ipaRounds j).1, .point (proof.ipaRounds j).2, .challenge]).flatten ++
    [.scalar proof.ipaC, .scalar proof.ipaF]

/-- The field values received at the schedule's successive challenge markers. -/
def plonkChallengeSequence {k : ℕ} (ch : Challenges k Fp) : List Fp :=
  [ch.theta, ch.beta, ch.gamma, ch.y, ch.x, ch.x1, ch.x2, ch.x3, ch.x4, ch.xi, ch.z] ++
    List.ofFn ch.ipaRound

/-- A zero totalized out-of-range read is never used by the fixed complete schedule. -/
def plonkAttemptChallenge {k : ℕ} (ch : Challenges k Fp) (index : ℕ) : Fp :=
  (plonkChallengeSequence ch).getD index 0

/-- Check only the exceptional values which the specified prover treats as failures. -/
def plonkAfterChallenge {k : ℕ} (ch : Challenges k Fp) (index : ℕ) :
    Option ProverAttemptFailure :=
  if index = 6 ∧ ch.x = 0 then some .coincidentOpeningQueries
  else if 11 ≤ index ∧ plonkAttemptChallenge ch index = 0 then some .zeroIpaChallenge
  else none

/-- Observe all protocol phases, retaining the prefix if an attempt stops. -/
def observePlonkAttempt {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : PlonkFreshView actions k G) : ProverAttemptResult :=
  observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge view.1)
    (plonkAfterChallenge view.1) 0 (plonkAttemptTrace view.2)

/-- Keep the verifier's full tape, including challenges unused by an unsuccessful attempt. -/
def plonkAttemptObservation {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : PlonkFreshView actions k G) : Challenges k Fp × ProverAttemptResult :=
  (view.1, observePlonkAttempt pointCodec scalarCodec view)

/-- Absorbing a point vector introduces no verifier challenge, preserving challenge indices across
this message block. -/
theorem challenges_absorbPoints {F G : Type*} {n : ℕ} (points : Fin n → G) :
    protocolChallengeCount (absorbPoints (F := F) points) = 0 := by
  rw [protocolChallengeCount_eq_zero_iff]
  simp [absorbPoints]

/-- Absorbing a scalar vector introduces no verifier challenge, preserving challenge indices across
this message block. -/
theorem challenges_absorbScalars {F G : Type*} {n : ℕ} (scalars : Fin n → F) :
    protocolChallengeCount (absorbScalars (G := G) scalars) = 0 := by
  rw [protocolChallengeCount_eq_zero_iff]
  simp [absorbScalars]

/-- Absorbing a point matrix introduces no verifier challenge, preserving challenge indices across
this message block. -/
theorem challenges_absorbPoints2 {F G : Type*} {a b : ℕ} (points : Fin a → Fin b → G) :
    protocolChallengeCount (absorbPoints2 (F := F) points) = 0 := by
  rw [protocolChallengeCount_eq_zero_iff]
  simp [absorbPoints2, absorbPoints]

/-- Absorbing a scalar matrix introduces no verifier challenge, preserving challenge indices across
this message block. -/
theorem challenges_absorbScalars2 {F G : Type*} {a b : ℕ} (scalars : Fin a → Fin b → F) :
    protocolChallengeCount (absorbScalars2 (G := G) scalars) = 0 := by
  rw [protocolChallengeCount_eq_zero_iff]
  simp [absorbScalars2, absorbScalars]

/-- Absorbing the permuted lookup commitments introduces no verifier challenge, preserving challenge
indices across this message block. -/
theorem challenges_absorbLookupPermuted {F G : Type*} {a b : ℕ}
    (input table : Fin a → Fin b → G) :
    protocolChallengeCount (absorbLookupPermuted (F := F) input table) = 0 := by
  rw [protocolChallengeCount_eq_zero_iff]
  simp [absorbLookupPermuted]

/-- Absorbing permutation evaluations introduces no verifier challenge, preserving challenge indices
across this message block. -/
theorem challenges_absorbPermSet {F G : Type*} (evals : PermSetEval F) :
    protocolChallengeCount (absorbPermSet (G := G) evals) = 0 := by
  cases h : evals.lastEval <;> simp [absorbPermSet, h, protocolChallengeCount]

/-- Absorbing lookup evaluations introduces no verifier challenge, preserving challenge indices
across this message block. -/
theorem challenges_absorbLookup {F G : Type*} (evals : LookupEval F) :
    protocolChallengeCount (absorbLookup (G := G) evals) = 0 := rfl

/-- Exactly eleven challenges precede the first IPA round, for any well-typed proof. -/
theorem plonkPreIpaTranscript_challengeCount {shape : Shape} {F G : Type*}
    (proof : ProofString shape F G) :
    protocolChallengeCount (preIpaTranscript [] proof) = 11 := by
  simp [preIpaTranscript, challenges_absorbPoints, challenges_absorbScalars,
    challenges_absorbPoints2, challenges_absorbScalars2, challenges_absorbLookupPermuted,
    challenges_absorbPermSet, challenges_absorbLookup, List.map_ofFn, Function.comp_def,
    protocolChallengeCount]

/-- The observer consumes precisely the `11+k` challenges present in the typed tape. -/
theorem plonkAttemptTrace_challengeCount {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) :
    protocolChallengeCount (plonkAttemptTrace proof) = 11 + k := by
  simp [plonkAttemptTrace, plonkPreIpaTranscript_challengeCount, List.map_ofFn,
    protocolChallengeCount, List.sum_ofFn]

/-- The supplied challenge sequence has exactly the length of the full receive schedule. -/
theorem plonkChallengeSequence_length {k : ℕ} (ch : Challenges k Fp) :
    (plonkChallengeSequence ch).length = 11 + k := by
  simp only [plonkChallengeSequence, List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn]

/-- Reading at a round's schedule position returns that round's typed challenge. -/
theorem plonkAttemptChallenge_round {k : ℕ} (ch : Challenges k Fp) (j : Fin k) :
    plonkAttemptChallenge ch (11 + j.val) = ch.ipaRound j := by
  unfold plonkAttemptChallenge plonkChallengeSequence
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- Every in-range receive reads the corresponding coin of the original verifier tape. -/
theorem plonkAttemptChallenge_fromTape {k : ℕ} (tape : PlonkChallengeTape k Fp)
    (j : Fin (k + 11)) :
    plonkAttemptChallenge (plonkChallengesFromTape tape) j.val = tape j := by
  by_cases hj : j.val < 11
  · have hearly (i : Fin 11) :
        plonkAttemptChallenge (plonkChallengesFromTape tape) i.val =
          tape ⟨i.val, by omega⟩ := by
      fin_cases i <;> rfl
    exact hearly ⟨j.val, hj⟩
  · let round : Fin k := ⟨j.val - 11, by omega⟩
    have hindex : j.val = 11 + round.val := by dsimp [round]; omega
    rw [hindex, plonkAttemptChallenge_round]
    change tape ⟨11 + round.val, _⟩ = tape j
    apply congrArg tape
    exact Fin.ext hindex.symm

/-- The opening failure occurs after the seventh received challenge (`x2`). -/
theorem plonkAfterChallenge_opening {k : ℕ} (ch : Challenges k Fp) :
    plonkAfterChallenge ch 6 = none ↔ ch.x ≠ 0 := by
  simp [plonkAfterChallenge]

/-- The five actual interpolation node lists are distinct exactly when `x` is nonzero. -/
theorem plonkOpeningPointSets_nodup_iff (omega x : Fp) (hroot : IsPrimitiveRoot omega 2048) :
    (∀ i : Fin 5, (plonkOpeningPointSets omega x i).Nodup) ↔ x ≠ 0 := by
  constructor
  · intro h hx
    have hsecond := h 1
    simp [plonkOpeningPointSets, hx] at hsecond
  · intro hx i
    have hpoints := plonkObservationPoints_injective omega x 0 hroot hx (by
      intro j
      exact (mul_ne_zero hx (pow_ne_zero _ (hroot.ne_zero (by decide)))).symm)
    exact plonkOpeningPointSets_nodup omega x 0 hpoints i

/-- The post-`x2` check tests precisely the distinctness required by the opening interpolants. -/
theorem plonkAfterChallenge_opening_points {k : ℕ} (ch : Challenges k Fp)
    (omega : Fp) (hroot : IsPrimitiveRoot omega 2048) :
    plonkAfterChallenge ch 6 = none ↔
      ∀ i : Fin 5, (plonkOpeningPointSets omega ch.x i).Nodup :=
  (plonkAfterChallenge_opening ch).trans (plonkOpeningPointSets_nodup_iff omega ch.x hroot).symm

/-- A round checks only its own zero challenge, after emitting both of its points. -/
theorem plonkAfterChallenge_round {k : ℕ} (ch : Challenges k Fp) (j : Fin k) :
    plonkAfterChallenge ch (11 + j.val) = none ↔ ch.ipaRound j ≠ 0 := by
  have hne : 11 + j.val ≠ 6 := by omega
  simp [plonkAfterChallenge, hne, plonkAttemptChallenge_round]

/-- No other simulator challenge exclusion is made into a prover failure condition. -/
theorem plonkAfterChallenge_all {k : ℕ} (ch : Challenges k Fp) :
    (∀ j < 11 + k, plonkAfterChallenge ch j = none) ↔
      ch.x ≠ 0 ∧ ∀ j, ch.ipaRound j ≠ 0 := by
  constructor
  · intro h
    refine ⟨(plonkAfterChallenge_opening ch).mp (h 6 (by omega)), ?_⟩
    intro j
    exact (plonkAfterChallenge_round ch j).mp (h (11 + j.val) (by omega))
  · rintro ⟨hx, hrounds⟩ j hj
    by_cases hround : 11 ≤ j
    · let index : Fin k := ⟨j - 11, by omega⟩
      have heq : j = 11 + index.val := by dsimp [index]; omega
      rw [heq]
      exact (plonkAfterChallenge_round ch index).mpr (hrounds index)
    · simp [plonkAfterChallenge, hx, hround]

/-- The exact completion criterion includes point encodings, `x`, and the IPA round challenges. -/
theorem observePlonkAttempt_complete_iff {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : PlonkFreshView actions k G) :
    (observePlonkAttempt pointCodec scalarCodec view).status = .complete ↔
      (∀ point, .point point ∈ plonkAttemptTrace view.2 → pointCodec point ≠ none) ∧
        view.1.x ≠ 0 ∧ ∀ j, view.1.ipaRound j ≠ 0 := by
  rw [observePlonkAttempt, observeProtocolTrace_complete_iff, plonkAttemptTrace_challengeCount]
  simp only [Nat.zero_add, plonkAfterChallenge_all]

/-- For the specified identity-rejecting codec, these are precisely the algebraic failure events. -/
theorem plonkAttempt_complete_iff {actions k : ℕ} {G : Type*} [Zero G]
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (view : PlonkFreshView actions k G) :
    (observePlonkAttempt pointCodec scalarCodec view).status = .complete ↔
      (∀ point, .point point ∈ plonkAttemptTrace view.2 → point ≠ 0) ∧
        view.1.x ≠ 0 ∧ ∀ j, view.1.ipaRound j ≠ 0 := by
  simp only [observePlonkAttempt_complete_iff, Ne, hcodec]

end Zcash.Snark.ZeroKnowledge

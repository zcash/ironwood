import Zcash.Snark.Fixtures.MultiAction.Honest.FiatShamir
import Zcash.Snark.Soundness.Decoded.Vesta

/-!
# Negative fixtures for the multi-action capture

These adversarial fixtures start from the Rust-captured multi-action proof and mutate the typed Lean data
to exercise modeled verifier rejection paths. They are not byte-level malformed proof captures: invalid
encodings and Rust-side decode failures sit below `ProofString`. The point here is concrete
regression coverage for non-accepting verifier states that the Lean model already exposes through
`assemble?` and `assembleOpening?`, plus tamper sensitivity for the two
positive checks: the fingerprint match (`MsmMatch`) and the captured Fiat–Shamir schedule
(`deriveChallenges_matches_captured_schedule`).
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open Zcash.Arithmetic (Msm)

theorem valid_capture_assembles : (assemble? vk derivedInstanceCommitment ps ch).isSome = true := by
  native_decide

/-- The captured two-action proof satisfies `DeployedAccepts`: assembly succeeds and the assembled
MSM evaluates to zero. This witnesses an accepting run at the captured URS; sampled-basis
soundness remains separate. -/
theorem capture_deployedAccepts :
    DeployedAccepts shape capturedURS rfl vk derivedInstanceCommitment ps ch := by
  unfold DeployedAccepts
  split
  · rename_i m hm
    have hassemble : assemble vk derivedInstanceCommitment ps ch = m := by
      simp [assemble, hm]
    have hzero := assembledMsm_eval_eq_zero
    rw [hassemble, Msm.evalNat_eq_eval_vesta] at hzero
    exact hzero
  · rename_i hm
    have hsome := valid_capture_assembles
    rw [hm] at hsome
    simp at hsome

def psUnexpectedLastPermutationEval : ProofString shape Fp G :=
  { ps with
    permutationSetEvals := fun p s =>
      if s.val + 1 = shape.numPermutationSets then
        { (ps.permutationSetEvals p s) with lastEval := some 0 }
      else
        ps.permutationSetEvals p s }

theorem unexpected_last_permutation_eval_rejected :
    assemble? vk derivedInstanceCommitment psUnexpectedLastPermutationEval ch = none := by
  native_decide

def psMissingNonLastPermutationEval : ProofString shape Fp G :=
  { ps with
    permutationSetEvals := fun p s =>
      if s.val + 1 = shape.numPermutationSets then
        ps.permutationSetEvals p s
      else
        { (ps.permutationSetEvals p s) with lastEval := none } }

theorem missing_nonlast_permutation_eval_rejected :
    assemble? vk derivedInstanceCommitment psMissingNonLastPermutationEval ch = none := by
  native_decide

def chXPowerOne : Challenges shape.k Fp :=
  { ch with x := 1 }

theorem x_power_one_rejected : assemble? vk derivedInstanceCommitment ps chXPowerOne = none := by
  native_decide

def chX3Collision : Challenges shape.k Fp :=
  { ch with x3 := ch.x }

theorem x3_collision_rejected : assemble? vk derivedInstanceCommitment ps chX3Collision = none := by
  native_decide

def duplicateFirstLayoutEntry (layout : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  match layout with
  | [] => []
  | first :: [] => [first]
  | first :: _ :: rest => first :: first :: rest

def vkDuplicateAdviceQuery : VerifyingKey shape Fp G :=
  { vk with adviceQueryLayout := duplicateFirstLayoutEntry vk.adviceQueryLayout }

theorem duplicate_advice_query_rejected :
    assemble? vkDuplicateAdviceQuery derivedInstanceCommitment ps ch = none := by
  native_decide

def psTamperedAdviceEval : ProofString shape Fp G :=
  { ps with
    adviceEvals := fun p q =>
      if p.val = 0 ∧ q.val = 0 then
        ps.adviceEvals p q + 1
      else
        ps.adviceEvals p q }

theorem tampered_advice_eval_assembles : (assemble? vk derivedInstanceCommitment psTamperedAdviceEval ch).isSome = true := by
  native_decide

theorem tampered_advice_eval_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psTamperedAdviceEval ch) capturedMsm := by
  native_decide

def validGrouped : MultiopenGrouped shape.k Fp G :=
  constructIntermediateSets (assembleQueries vk derivedInstanceCommitment ps ch)

theorem malformed_u_count_rejected :
    assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (capturedMultiopenU.drop 1)
      validGrouped (Msm.zero shape.k Fp G) = none := by
  native_decide

/-- Swap the two sub-proofs' advice commitments (`Fin.rev` swaps the indices at `numProofs = 2`). The
Fiat–Shamir oracle then sees a transcript prefix that differs from the Rust-captured one at the very
first proof-derived absorb block, so the schedule check fails: cross-sub-proof absorb order is
detected, not just argued. -/
def psSwappedAdviceCommitments : ProofString shape Fp G :=
  { ps with adviceCommitments := fun p => ps.adviceCommitments p.rev }

theorem swapped_advice_absorb_breaks_schedule :
    deriveChallenges capturedFs capturedInit psSwappedAdviceCommitments ≠ ch := by
  native_decide

/-- Swap each lookup's permuted-input and permuted-table commitments: the transcript then presents the
`(table, input)` interleaving instead of the deployed `(input, table)`, so the schedule check
fails. -/
def psSwappedLookupPermuted : ProofString shape Fp G :=
  { ps with
    lookupPermutedInput := ps.lookupPermutedTable,
    lookupPermutedTable := ps.lookupPermutedInput }

theorem swapped_lookup_permuted_breaks_schedule :
    deriveChallenges capturedFs capturedInit psSwappedLookupPermuted ≠ ch := by
  native_decide

/-- Swap the two sub-proofs' data wholesale (instance commitments are statement-derived and stay). The
mutated proof still assembles — the typed read schedule is position-based — but the fingerprint no
longer matches the capture: the assembled MSM is sensitive to which sub-proof sits at which
position. -/
def psSwappedSubProofs : ProofString shape Fp G :=
  { ps with
    adviceCommitments := fun p => ps.adviceCommitments p.rev,
    lookupPermutedInput := fun p => ps.lookupPermutedInput p.rev,
    lookupPermutedTable := fun p => ps.lookupPermutedTable p.rev,
    permutationProduct := fun p => ps.permutationProduct p.rev,
    lookupProduct := fun p => ps.lookupProduct p.rev,
    instanceEvals := fun p => ps.instanceEvals p.rev,
    adviceEvals := fun p => ps.adviceEvals p.rev,
    permutationSetEvals := fun p => ps.permutationSetEvals p.rev,
    lookupEvals := fun p => ps.lookupEvals p.rev }

theorem swapped_sub_proofs_assemble : (assemble? vk derivedInstanceCommitment psSwappedSubProofs ch).isSome = true := by
  native_decide

theorem swapped_sub_proofs_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSwappedSubProofs ch) capturedMsm := by
  native_decide

/-! ## Blind-slot tampers

`fixedEvals`, `permutationCommonEvals`, and `instanceEvals` are the proof-string slots whose
honest value is recomputable from the verifying key, the public inputs, and the challenges — so
on honest captures a sourcing error in `assemble` (say, recomputing fixed evaluations from
VK-derived polynomials instead of reading the proof's claimed values) would be invisible: the
recomputed and claimed values coincide. These tampers witness that the match reads each slot
from the proof string: the tampered proof still assembles (the slots are transcript-claimed,
bound only through the multiopen), but the assembled MSM no longer matches the capture. All
three are stated at the captured `ch`, so a failure is MSM sensitivity, not a schedule
derailment. -/

def psTamperedFixedEval : ProofString shape Fp G :=
  { ps with
    fixedEvals := fun q =>
      if q.val = 0 then
        ps.fixedEvals q + 1
      else
        ps.fixedEvals q }

theorem tampered_fixed_eval_assembles : (assemble? vk derivedInstanceCommitment psTamperedFixedEval ch).isSome = true := by
  native_decide

theorem tampered_fixed_eval_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psTamperedFixedEval ch) capturedMsm := by
  native_decide

def psTamperedPermutationCommonEval : ProofString shape Fp G :=
  { ps with
    permutationCommonEvals := fun c =>
      if c.val = 0 then
        ps.permutationCommonEvals c + 1
      else
        ps.permutationCommonEvals c }

theorem tampered_permutation_common_eval_assembles :
    (assemble? vk derivedInstanceCommitment psTamperedPermutationCommonEval ch).isSome = true := by
  native_decide

theorem tampered_permutation_common_eval_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psTamperedPermutationCommonEval ch) capturedMsm := by
  native_decide

def psTamperedInstanceEval : ProofString shape Fp G :=
  { ps with
    instanceEvals := fun p q =>
      if p.val = 0 ∧ q.val = 0 then
        ps.instanceEvals p q + 1
      else
        ps.instanceEvals p q }

theorem tampered_instance_eval_assembles : (assemble? vk derivedInstanceCommitment psTamperedInstanceEval ch).isSome = true := by
  native_decide

theorem tampered_instance_eval_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psTamperedInstanceEval ch) capturedMsm := by
  native_decide

end Zcash.Snark.Fixture2

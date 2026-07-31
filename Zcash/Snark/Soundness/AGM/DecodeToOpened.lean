import Zcash.Snark.Soundness.AGM.DeployedSyntheticOpened
import Zcash.Snark.Soundness.AGM.DeployedRootDecode

/-!
# A decode presented through the opened-batch interface

`DeployedAlgebraicDecode` supplies AGM coordinate columns for the `x₄` batch and each routed `x₁`
batch, together with the value equations they open to. The Action-side terminal consumes the
opened-batch interface — an
`OpenedBatchOpenings` and a per-set `OpenedMemberDecode`.

The two are the same data.  `AGM.SyntheticOpened` already rebuilds the opened-batch object from
coordinates by linearity, at any injective family of interpolation points with one point pinned to
the batching challenge, and `pinnedPoints` supplies such a family.  This module ties the knot:
given a decode, it hands back exactly the two objects the terminal asks for.

Nothing here rewinds.  The interpolation points are extractor-side arithmetic, not oracle answers,
which is why one accepting execution suffices.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

variable [Inhabited G] {shape : Shape}

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments

/-- The interpolation points a decode is presented at: a walk up from the actual `x₄` challenge. -/
def decodePoints (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) → Fp :=
  pinnedPoints ch.x4 (deployedX4PairCount vk instanceCommitment ps ch)

omit [AddCommGroup G] [Module Fp G] in
/-- The pair count stays below the characteristic, so the points are distinct. -/
theorem decodePoints_injective (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hchar : deployedX4PairCount vk instanceCommitment ps ch < scalarFieldOrder) :
    Function.Injective (decodePoints vk instanceCommitment ps ch) :=
  pinnedPoints_injective ch.x4 hchar

omit [AddCommGroup G] [Module Fp G] in
/-- Index `0` carries the actual batching challenge. -/
theorem decodePoints_zero (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    decodePoints vk instanceCommitment ps ch 0 = ch.x4 := by
  simp [decodePoints, pinnedPoints]

/-- **A decode's `x₄` batch as an opened-batch object.**  No rewinding: the columns are the
decode's own AGM coordinates and the openings are their power combinations. -/
def DeployedAlgebraicDecode.toOpenedBatch
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (decode : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hchar : deployedX4PairCount vk instanceCommitment ps ch < scalarFieldOrder) :
    OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) aggregate aggregateU aggregateW :=
  deployedSyntheticOpenedX4 urs hk vk instanceCommitment ps ch decode.batches.x4
    decode.x4Values (decodePoints vk instanceCommitment ps ch)
    (decodePoints_injective vk instanceCommitment ps ch hchar) 0
    (decodePoints_zero vk instanceCommitment ps ch)

/-- **A decode's routed `x₁` batch as a member decode**, against the opened batch above. -/
def DeployedAlgebraicDecode.toMemberDecode
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (decode : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hchar : deployedX4PairCount vk instanceCommitment ps ch < scalarFieldOrder)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch) :
    OpenedMemberDecode urs hk vk instanceCommitment ps ch
      (decode.toOpenedBatch hchar) i hi :=
  deployedSyntheticMemberDecode urs hk vk instanceCommitment ps ch decode.batches.x4
    decode.x4Values (decodePoints vk instanceCommitment ps ch)
    (decodePoints_injective vk instanceCommitment ps ch hchar) 0
    (decodePoints_zero vk instanceCommitment ps ch) i hi (decode.batches.x1 i hi)

/-- The opened batch's designated column is the actual `x₄` challenge, which is the form the
Action terminal's `hξcur` premise takes. -/
theorem DeployedAlgebraicDecode.toOpenedBatch_current
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (decode : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hchar : deployedX4PairCount vk instanceCommitment ps ch < scalarFieldOrder) :
    (decode.toOpenedBatch hchar).batchChallenge (decode.toOpenedBatch hchar).current = ch.x4 :=
  decodePoints_zero vk instanceCommitment ps ch


/-! ## The member-binding premise

The Action terminal asks for each routed member's decoded polynomial to hit the grouping's claimed
value at every point of its set.  That is what a decode's `memberValues` already says — the two
sides name the point differently, positionally against the set's point list versus by `idxOf`, and
the list is duplicate-free, so the two agree.
-/

/-- **A decode discharges the terminal's member-binding premise.**  No relation branch is needed:
the decode already carries the value equations, so this always lands on the left. -/
theorem DeployedAlgebraicDecode.memberBinding
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (decode : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hchar : deployedX4PairCount vk instanceCommitment ps ch < scalarFieldOrder)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (point : Fp)
    (hpoint : point ∈ deployedSetPts vk instanceCommitment ps ch slot.setIndex) :
    (decodedMemberPolynomial (instanceCommitment := instanceCommitment) urs hk vk ps ch
        (fun i hi => decode.toMemberDecode hchar i hi) slot).eval point =
      deployedMemberClaim (instanceCommitment := instanceCommitment) vk ps ch slot point := by
  classical
  have hpointsEq :=
    deployedSetsForEval_getD_points vk instanceCommitment ps ch slot.setIndex_lt
  have hmem : point ∈ ((deployedSetsForEval vk instanceCommitment ps ch).getD slot.setIndex
      ([], [], 0)).1 := by
    have hp := hpoint
    rw [← deployedSetsForEval_getD_toFinset vk instanceCommitment ps ch slot.setIndex_lt] at hp
    exact List.mem_toFinset.mp hp
  have hidx := List.idxOf_lt_length_of_mem hmem
  have hget := List.getElem_idxOf hidx
  have h := decode.memberValues slot.setIndex slot.setIndex_lt ⟨_, hidx⟩ slot.memberIndex
  rw [Fin.getElem_fin] at h
  rw [hget] at h
  unfold decodedMemberPolynomial deployedMemberClaim
  show (coeffsToPoly ((decode.toMemberDecode hchar slot.setIndex slot.setIndex_lt).cols
      slot.memberIndex)).eval point = _
  have hcols : (decode.toMemberDecode hchar slot.setIndex slot.setIndex_lt).cols
      = (decode.batches.x1 slot.setIndex slot.setIndex_lt).coeffs := rfl
  rw [hcols, ← hpointsEq]
  exact h

end Zcash.Snark

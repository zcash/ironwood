import Zcash.Snark.Soundness.AGM.SyntheticOpened

/-!
# Deployed synthetic-opened adapter

The Halo2 specialization of `AlgebraicPowerBatch.toSyntheticOpened`: the `x4` and `x1` AGM batches
presented through the member-constraint interface, with every entry computed locally from
representation coordinates.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments

/-- A deployed `x4` algebraic batch presented through the opened-batch interface. -/
def deployedSyntheticOpenedX4 [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (points : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (hcurrent : points current = ch.x4) :
    OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW :=
  batch.toSyntheticOpened (evalVector urs.k ch.x3) (x4BatchEvals vk instanceCommitment ps ch)
    hvalues points hpoints current hcurrent

/-- The deployed synthetic opened object's canonical `x4` decode is the AGM decode. -/
theorem deployedSyntheticOpenedX4_coeffs [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (points : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (hcurrent : points current = ch.x4) (i : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)) :
    (openedColumnDecode
      (deployedSyntheticOpenedX4 urs hk vk instanceCommitment ps ch batch hvalues points hpoints current hcurrent)
    ).coeffs i = batch.coeffs i :=
  batch.openedColumnDecode_toSyntheticOpened_coeffs
    (evalVector urs.k ch.x3) (x4BatchEvals vk instanceCommitment ps ch) hvalues points hpoints current hcurrent i

/-- The deployed synthetic opened object's canonical `U` decode is the AGM decode. -/
theorem deployedSyntheticOpenedX4_uComp [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (points : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (hcurrent : points current = ch.x4) (i : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)) :
    (openedColumnDecode
      (deployedSyntheticOpenedX4 urs hk vk instanceCommitment ps ch batch hvalues points hpoints current hcurrent)
    ).uComp i = batch.uComp i :=
  batch.openedColumnDecode_toSyntheticOpened_uComp
    (evalVector urs.k ch.x3) (x4BatchEvals vk instanceCommitment ps ch) hvalues points hpoints current hcurrent i

/-- The deployed synthetic opened object's canonical `W` decode is the AGM decode. -/
theorem deployedSyntheticOpenedX4_wComp [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (points : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (hcurrent : points current = ch.x4) (i : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)) :
    (openedColumnDecode
      (deployedSyntheticOpenedX4 urs hk vk instanceCommitment ps ch batch hvalues points hpoints current hcurrent)
    ).wComp i = batch.wComp i :=
  batch.openedColumnDecode_toSyntheticOpened_wComp
    (evalVector urs.k ch.x3) (x4BatchEvals vk instanceCommitment ps ch) hvalues points hpoints current hcurrent i

/-- Adapt one deployed `x1` AGM member batch to `OpenedMemberDecode`.  Its reconstruction target is
the `x4` AGM coordinate because the synthetic `x4` decode was identified above. -/
def deployedSyntheticMemberDecode [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (x4Batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (hvalues : forall i,
      commitGen (evalVector urs.k ch.x3) (x4Batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i)
    (points : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) -> Fp)
    (hpoints : Function.Injective points)
    (current : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1))
    (hcurrent : points current = ch.x4)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (x1Batch : AlgebraicPowerBatch urs (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)
      (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) ch.x1) :
    OpenedMemberDecode urs hk vk instanceCommitment ps ch
      (deployedSyntheticOpenedX4 urs hk vk instanceCommitment ps ch x4Batch hvalues
        points hpoints current hcurrent) i hi := by
  let pos : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) :=
    ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩
  refine
    { cols := x1Batch.coeffs
      uComp := x1Batch.uComp
      wComp := x1Batch.wComp
      commitment := ?_
      reconstruct := ?_
      reconstructU := ?_
      reconstructW := ?_ }
  · intro m
    rw [<- deployedSetMemberCommitments_apply urs hk vk instanceCommitment ps ch i m]
    exact x1Batch.commitment m
  · rw [deployedSyntheticOpenedX4_coeffs urs hk vk instanceCommitment ps ch x4Batch hvalues
      points hpoints current hcurrent pos]
    exact x1Batch.reconstruct
  · rw [deployedSyntheticOpenedX4_uComp urs hk vk instanceCommitment ps ch x4Batch hvalues
      points hpoints current hcurrent pos]
    exact x1Batch.reconstructU
  · rw [deployedSyntheticOpenedX4_wComp urs hk vk instanceCommitment ps ch x4Batch hvalues
      points hpoints current hcurrent pos]
    exact x1Batch.reconstructW

end Zcash.Snark

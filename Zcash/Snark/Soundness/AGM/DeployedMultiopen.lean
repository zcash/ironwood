import Zcash.Snark.Soundness.AGM.AlgebraicUnbatch

/-!
# AGM unbatching for the deployed `x₄` multiopen collapse

This file connects the generic rewind-free algebraic unbatcher to the exact power batch assembled by
the deployed verifier.  It deliberately stops at the clean aggregate-value premise: deriving that
premise from the recursive IPA extractor, including the `U`-shift, is the next composition seam.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Provenance-preserving deployed `x₄` unbatch.  The successful branch records that every
recovered column is exactly the online column representation passed to the executable walk. -/
def deployedX4AlgebraicBatchWithSourceOrRelation [Inhabited G]
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (cols : AlgebraicColumnRepresentations urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch))
    (aggregate : Fin (2 ^ urs.k) → Fp) (aggregateU aggregateW : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch) :
    AlgebraicPowerBatchWithSource urs cols aggregate aggregateU aggregateW ch.x4 ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  apply algebraicPowerBatchWithSourceOrRelation cols aggregate aggregateU aggregateW ch.x4
  have hbatch := deployedCommitment_x4_batch urs hk vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  exact haggregate.trans hbatch

/-- At the deployed `x₄` collapse, online representations of the individual aggregate columns
either reconstruct the aggregate AGM coordinates immediately or expose an augmented-basis relation.
No accepting `x₄` rewinds are used. -/
def deployedX4AlgebraicBatchOrRelation [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (cols : AlgebraicColumnRepresentations urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch))
    (aggregate : Fin (2 ^ urs.k) → Fp) (aggregateU aggregateW : Fp)
    (haggregate : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch) :
    AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        aggregate aggregateU aggregateW ch.x4 ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  match deployedX4AlgebraicBatchWithSourceOrRelation urs hk vk instanceCommitment ps ch cols
      aggregate aggregateU aggregateW haggregate with
  | PSum.inl result => exact PSum.inl result.batch
  | PSum.inr relation => exact PSum.inr relation

/-- Once the clean aggregate opens to the verifier's deployed value, a good `x₄` challenge makes
the represented aggregate columns open to all of the verifier's claimed `x₄` column values. -/
theorem deployedX4AlgebraicValues_of_good [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4)
    (b : Fin (2 ^ urs.k) → Fp)
    (hvalue : commitGen b aggregate = multiopenValue vk instanceCommitment ps ch)
    (hgood : ch.x4 ∉ szBadSet
      (algebraicBatchErrorPolynomial b batch.coeffs
        (x4BatchEvals vk instanceCommitment ps ch))) :
    ∀ i, commitGen b (batch.coeffs i) = x4BatchEvals vk instanceCommitment ps ch i := by
  apply batch.values_of_good_challenge b (x4BatchEvals vk instanceCommitment ps ch)
  have hbatch := multiopenValue_x4_batch vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  exact hvalue.trans hbatch
  exact hgood

end Zcash.Snark

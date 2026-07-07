import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGM.Probability

/-!
# Deployed-curve instantiation of the AGM probability wrapper (Vesta)

The generic probability wrapper (`Soundness.AGM.Probability`) specializes to the deployed *index
shapes* — the augmented basis index `AugmentedIndex (2 ^ urs.k)` and the URS index `Fin (2 ^ urs.k)` —
over the Vesta group `VestaG` with scalar field `Fp`. This is the concrete-curve endpoint of the
"relation-finder ⇒ discrete-log solver" reduction that discharges the `∨ HasNontrivialRelation`
branch of the deployed Orchard verifier capstones.

**The uniform-basis seam.** In these theorems the adversary acts on the reduction's *sampled* basis
`scalarBasis B s` (uniform scalars times `B`), not on the deployed generators themselves (`urs.g`
appears only through its index size `urs.k`). Reading them as statements about the deployed URS
assumes the URS is distributed as uniform multiples of a generator `B` — i.e. a uniformly sampled
("nothing-up-my-sleeve") URS over the prime-order Vesta group, where uniform points are exactly
uniform scalars times any fixed generator. That distribution identification is a named modeling
assumption of this file, alongside the other seam of issue #15: identifying the deployed Ironwood
prover with the abstract algebraic relation-finder `A` (its group outputs carrying representations
through the IPA verifier equation). The probability accounting itself is fully formalized upstream.
-/

open scoped ENNReal

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- **Binding from discrete-log hardness, at the deployed curve.** At the augmented basis *index*
`AugmentedIndex (2 ^ urs.k)` over Vesta: if this reduction solves the discrete log of the challenge
slot with probability at most `bound` (`DLAdvantageLE`), then an algebraic adversary against the
sampled basis `scalarBasis B s` finds a nontrivial relation with probability at most `|ι| · bound`.
Reading the sampled basis as the deployed `(g, U, W)` is the uniform-basis seam (module doc). Direct
specialization of `relation_prob_le_of_DL` to `ι := AugmentedIndex (2 ^ urs.k)`, `F := Fp`,
`G := VestaG`. -/
theorem orchard_relation_prob_le_of_DL [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : DLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (AugmentedIndex (2 ^ urs.k)) * bound :=
  relation_prob_le_of_DL B A h

/-- The deployed-curve advantage-preserving reduction: over the uniform product, the reduction's
discrete-log-solving probability is at least `1/|ι|` times the algebraic adversary's relation-finding
probability on the sampled basis (uniform-basis seam: module doc). Specialization of
`reduction_advantage_ge` at the deployed index shape. -/
theorem orchard_reduction_advantage_ge [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ urs.k))
        * (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((AugmentedIndex (2 ^ urs.k) → Fp) × AugmentedIndex (2 ^ urs.k))).toOuterMeasure
          (succSet B A) :=
  reduction_advantage_ge B A

/-- **Commitment binding from plain discrete log (URS index shape).** Specializing the reduction to
the URS *index* `Fin (2 ^ urs.k)` over Vesta: under textbook single-generator DL hardness for this
reduction (`TextbookDLAdvantageLE`), an algebraic adversary finds a nontrivial relation over the
sampled basis `scalarBasis B s` with probability at most `2^k · bound`. The binding reading — a
commitment collision on the URS yields such a relation via its difference `a - a'`
(`relationWitnessOfCollision`), so collisions are as hard as discrete log — additionally requires the
uniform-basis seam (module doc): the deployed URS generators distributed as uniform multiples of a
generator `B`. The statement itself is about the sampled basis; `urs` enters only through `urs.k`. -/
theorem commitment_binding_prob_le_of_textbookDL [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (B : VestaG)
    (A : (b : Fin (2 ^ urs.k) → VestaG) → Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (Fin (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (Fin (2 ^ urs.k)) * bound :=
  relation_prob_le_of_textbookDL B A h

end Zcash.Snark

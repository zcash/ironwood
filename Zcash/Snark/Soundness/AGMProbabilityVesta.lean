import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGMProbability

/-!
# Deployed-curve instantiation of the AGM probability wrapper (Vesta)

The generic probability wrapper (`Soundness.AGMProbability`) specializes to the deployed augmented
basis index `AugmentedIndex (2 ^ urs.k)` over the Vesta group `VestaG` with scalar field `Fp`. This is
the concrete-curve endpoint of the "relation-finder ⇒ discrete-log solver" reduction that discharges
the `∨ HasNontrivialRelation` branch of the deployed Orchard verifier capstones.

The one remaining gap is issue #15's other half: identifying the deployed Ironwood prover with the
abstract algebraic relation-finder `A` here (its group outputs carrying representations through the IPA
verifier equation). The probability accounting itself is fully formalized upstream.
-/

open scoped ENNReal

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- **Binding from discrete-log hardness, at the deployed curve.** For the augmented `(g, U, W)` basis
index over Vesta, if no reduction solves the discrete log of the challenge slot with probability more
than `bound` (`DLAdvantageLE`), then an algebraic adversary against that basis finds a nontrivial
relation with probability at most `|ι| · bound`. Direct specialization of `relation_prob_le_of_DL` to
`ι := AugmentedIndex (2 ^ urs.k)`, `F := Fp`, `G := VestaG`. -/
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
probability. Specialization of `reduction_advantage_ge`. -/
theorem orchard_reduction_advantage_ge [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ urs.k))
        * (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((AugmentedIndex (2 ^ urs.k) → Fp) × AugmentedIndex (2 ^ urs.k))).toOuterMeasure
          (succSet B A) :=
  reduction_advantage_ge B A

end Zcash.Snark

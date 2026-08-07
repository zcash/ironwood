import Zcash.Common.RelationProbability
import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Decoded.Vesta

/-!
# Vesta AGM probability bounds

`Common.RelationProbability` specialized to Vesta and the deployed augmented basis `(g, U, W)`:
relation finding costs the textbook DL advantage plus `1/|Fp|`, with no augmented-basis
cardinality factor.

The reduction samples a basis as uniform scalar multiples of `B`.
`OrchardUniformURSIdentification` says that the deployed setup has the same distribution.
`orchard_uniformURSIdentification_of_generatorRO` proves this inside a uniform generator random-
oracle model. Treating halo2's hash-to-curve as that oracle remains a heuristic identification.

`Soundness.FiatShamir.Adversary.Algebraic` builds the basis-indexed adversary family from the deployed
bounded-query Fiat–Shamir adversary and names the events this file prices.
-/

open scoped ENNReal

namespace Zcash.Snark

open Zcash.Arithmetic (card_Fp)

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder






/-- The deployed setup and programmed-basis reduction produce the same augmented-basis
distribution. -/
def OrchardUniformURSIdentification {Ω : Type*} (setup : PMF Ω) (k : ℕ) (B : VestaG)
    (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG) : Prop :=
  setup.map basisOf =
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B)

/-- Uniform group-valued oracle answers at the parameter queries for the augmented URS basis. -/
noncomputable def orchardGeneratorROSetup {T : Type*} [DecidableEq T]
    {k : ℕ} (query : AugmentedIndex (2 ^ k) → T) :
    PMF (↥(Set.range query) → VestaG) := by
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  exact PMF.uniformOfFintype (↥(Set.range query) → VestaG)

/-- Read an augmented basis from the generator random oracle at its distinct parameter queries. -/
def orchardGeneratorROBasis {T : Type*} {k : ℕ}
    (query : AugmentedIndex (2 ^ k) → T) :
    (↥(Set.range query) → VestaG) → AugmentedIndex (2 ^ k) → VestaG :=
  fun O i => O ⟨query i, Set.mem_range_self i⟩

/-- Distinct queries to a uniform group-valued oracle produce the sampled-basis distribution.

This models halo2's parameter derivation (`gᵢ = H(0 || i)`, `W = H(1)`, `U = H(2)`). For `B ≠ 0`,
scalar multiplication by `B` maps uniform scalars to uniform Vesta points. Identifying halo2's
concrete hash-to-curve with this oracle remains a heuristic identification. -/
theorem orchard_uniformURSIdentification_of_generatorRO {T : Type*} [DecidableEq T]
    (k : ℕ) (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ k) → T) (hquery : Function.Injective query) :
    OrchardUniformURSIdentification
      (orchardGeneratorROSetup query) k B
      (orchardGeneratorROBasis query) := by
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  have hinj : Function.Injective (fun c : Fp => c • B) := by
    intro c c' h
    rcases eq_or_ne c c' with hcc | hcc
    · exact hcc
    · exfalso
      apply hB
      change c • B = c' • B at h
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
      have hzero : (c - c') • B = 0 := by rw [sub_smul, h, sub_self]
      rw [← one_smul Fp B, ← inv_mul_cancel₀ hd, mul_smul, hzero, smul_zero]
  have hcard : Fintype.card Fp = Fintype.card VestaG := by
    rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq]
  let pointEquiv : Fp ≃ VestaG := Equiv.ofBijective (fun c : Fp => c • B)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩)
  have hscalar :
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B) =
        PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → VestaG) := by
    simpa [scalarBasis, pointEquiv] using
      (map_uniformOfFintype_equiv
        (Equiv.arrowCongr (Equiv.refl (AugmentedIndex (2 ^ k))) pointEquiv))
  unfold OrchardUniformURSIdentification orchardGeneratorROSetup
  simpa [orchardGeneratorROBasis] using
    (uniformOfFintype_map_eval_injective query hquery).trans hscalar.symm




/-- Over the Vesta URS-generator basis, textbook DL hardness bounds relation finding by
`bound + 1/|Fp|`.

A commitment collision yields such a relation through `relationWitnessOfCollision`. The deployed
reading also requires the URS distribution described in the module documentation. -/
theorem commitment_binding_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : Fin (2 ^ urs.k) → VestaG) → Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (Fin (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card Fp :=
  relation_prob_le_of_textbookDL B A h

/-- Over Vesta's augmented basis, textbook DL hardness bounds relation finding by
`bound + 1/|Fp|`. -/
theorem orchard_relation_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card Fp :=
  relation_prob_le_of_textbookDL B A h

end Zcash.Snark

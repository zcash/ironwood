import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGM.Probability
import Zcash.Snark.Soundness.AGM.Capstone

/-!
# Vesta AGM probability bounds

This module applies the generic relation-to-DL probability proof to Vesta and the deployed augmented
basis `(g, U, W)`.

The reduction samples a basis as uniform scalar multiples of `B`.
`OrchardUniformURSIdentification` says that the deployed setup has the same distribution.
`orchard_uniformURSIdentification_of_generatorRO` proves this inside a uniform generator random-
oracle model. Treating halo2's hash-to-curve as that oracle remains an assumption.

The Fiat–Shamir layer must still produce `DeployedAlgebraicForkingInstance` values and relate its
acceptance event to the relation event measured here.
-/

open scoped ENNReal

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- Run the computed opening-or-DL endpoint over Vesta. All transcript and AGM data are explicit. -/
def orchardDeployedAlgebraicForkingFixedSlot
    (urs : URS VestaG) (B : VestaG) (challenge : AugmentedIndex (2 ^ urs.k))
    (embedding : FixedSlotEmbedding (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' FixedSlotRelationOutcome (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge := by
  letI : Inhabited VestaG := ⟨0⟩
  exact deployedAlgebraicForkingFixedSlot urs B challenge embedding b v ξ z blind
    aMulti aDep s cert hz hb0 hP hvalid

/-! ## Exact deployed-producer event -/

/-- Scalar samples on which the supplied deployed algebraic producer computes its relation branch. -/
noncomputable def orchardDeployedRelationSet (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    Finset (AugmentedIndex (2 ^ k) → Fp) := by
  classical
  exact Finset.univ.filter fun scalars =>
    deployedAlgebraicRelationProduced instances (scalarBasis B scalars)

/-- The supplied instances' relation event equals the generic reduction's `relSet`. -/
theorem orchard_deployed_relation_set_eq_relSet (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    orchardDeployedRelationSet k B instances =
      relSet B (deployedAlgebraicRelationFinder instances) := by
  classical
  ext scalars
  simp only [orchardDeployedRelationSet, relSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (deployedAlgebraicRelationFinder_isSome_iff instances (scalarBasis B scalars)).symm

/-- Apply the fixed-slot probability bound to the supplied deployed Vesta instances. -/
theorem orchard_deployed_reduction_advantage_ge (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ k)) *
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
          (relSet B (deployedAlgebraicRelationFinder instances))
      ≤ (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ k) → Fp) × AugmentedIndex (2 ^ k))).toOuterMeasure
          (succSet B (deployedAlgebraicRelationFinder instances)) :=
  reduction_advantage_ge B (deployedAlgebraicRelationFinder instances)

/-- Bound the supplied instances' relation probability by textbook DL hardness. -/
theorem orchard_deployed_relation_prob_le_of_textbookDL (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (relSet B (deployedAlgebraicRelationFinder instances))
      ≤ Fintype.card (AugmentedIndex (2 ^ k)) * bound :=
  relation_prob_le_of_textbookDL B (deployedAlgebraicRelationFinder instances) hDL

/-- State the textbook-DL bound directly on the supplied instances' computed relation event.

The Fiat–Shamir layer must show that its executions populate `instances`. -/
theorem orchard_deployed_relation_event_prob_le_of_textbookDL (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (orchardDeployedRelationSet k B instances)
      ≤ Fintype.card (AugmentedIndex (2 ^ k)) * bound := by
  rw [orchard_deployed_relation_set_eq_relSet]
  exact orchard_deployed_relation_prob_le_of_textbookDL k B instances hDL

/-- The deployed setup and fixed-slot reduction produce the same augmented-basis distribution. -/
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
concrete hash-to-curve with this oracle remains an assumption. -/
theorem orchard_uniformURSIdentification_of_generatorRO {T : Type*} [DecidableEq T]
    (k : ℕ) (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ k) → T) (hquery : Function.Injective query) :
    OrchardUniformURSIdentification
      (orchardGeneratorROSetup query) k B
      (orchardGeneratorROBasis query) := by
  classical
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

/-- Transfer the supplied relation event from a uniform URS setup to the sampled-scalar experiment. -/
theorem orchard_deployed_relation_prob_eq_of_uniformURS {Ω : Type*} (setup : PMF Ω)
    (k : ℕ) (B : VestaG) (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    (hURS : OrchardUniformURSIdentification setup k B basisOf) :
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances) =
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (orchardDeployedRelationSet k B instances) := by
  have h := congrArg
    (fun p : PMF (AugmentedIndex (2 ^ k) → VestaG) =>
      p.toOuterMeasure (deployedAlgebraicRelationEvent instances)) hURS
  change (setup.map basisOf).toOuterMeasure (deployedAlgebraicRelationEvent instances) =
    ((PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B)).toOuterMeasure
      (deployedAlgebraicRelationEvent instances) at h
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at h
  calc
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances)
        = (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
            (scalarBasis B ⁻¹' deployedAlgebraicRelationEvent instances) := h
    _ = (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
          (orchardDeployedRelationSet k B instances) := by
      congr 1
      ext scalars
      simp only [Set.mem_preimage, deployedAlgebraicRelationEvent, Set.mem_setOf_eq,
        orchardDeployedRelationSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Bound the supplied relation event under an explicit URS setup distribution. -/
theorem orchard_deployed_relation_prob_le_of_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (k : ℕ) (B : VestaG) (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup k B basisOf)
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances) ≤
      Fintype.card (AugmentedIndex (2 ^ k)) * bound := by
  rw [orchard_deployed_relation_prob_eq_of_uniformURS setup k B basisOf instances hURS]
  exact orchard_deployed_relation_event_prob_le_of_textbookDL k B instances hDL

/-- Bound the supplied relation event by textbook DL in the generator random-oracle model. -/
theorem orchard_deployed_relation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (k : ℕ) (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ k) → T) (hquery : Function.Injective query)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (orchardGeneratorROSetup query).toOuterMeasure
        (orchardGeneratorROBasis query ⁻¹' deployedAlgebraicRelationEvent instances) ≤
      Fintype.card (AugmentedIndex (2 ^ k)) * bound :=
  orchard_deployed_relation_prob_le_of_uniformURS_textbookDL
    (orchardGeneratorROSetup query) k B (orchardGeneratorROBasis query) instances
    (orchard_uniformURSIdentification_of_generatorRO k B hB query hquery) hDL

/-- Over Vesta's augmented basis, embedded-DL hardness bounds relation finding by `|ι| · bound`. -/
theorem orchard_relation_prob_le_of_DL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : DLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (AugmentedIndex (2 ^ urs.k)) * bound :=
  relation_prob_le_of_DL B A h

/-- Over Vesta's augmented basis, DL-solving probability is at least relation probability divided by
`|ι|`. -/
theorem orchard_reduction_advantage_ge
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ urs.k))
        * (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((AugmentedIndex (2 ^ urs.k) → Fp) × AugmentedIndex (2 ^ urs.k))).toOuterMeasure
          (succSet B A) :=
  reduction_advantage_ge B A

/-- Over the Vesta URS-generator basis, textbook DL hardness bounds relation finding by
`2^urs.k · bound`.

A commitment collision yields such a relation through `relationWitnessOfCollision`. The deployed
reading also requires the URS distribution described in the module documentation. -/
theorem commitment_binding_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : Fin (2 ^ urs.k) → VestaG) → Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (Fin (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (Fin (2 ^ urs.k)) * bound :=
  relation_prob_le_of_textbookDL B A h

/-- Over Vesta's augmented basis, textbook DL hardness bounds relation finding by `|ι| · bound`. -/
theorem orchard_relation_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (AugmentedIndex (2 ^ urs.k)) * bound :=
  relation_prob_le_of_textbookDL B A h

end Zcash.Snark

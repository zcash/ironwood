import Zcash.Snark.Capstones.Action.Base
import Zcash.Circuits.Action.PlannerTrace

/-!
# The captured checks, scalars, and schedule at the derived key

Everything the endpoints need to know about the deployed Action key itself: the derived key's
captured scalars, the shape counts they induce, the static checks, and the `x`-squeeze
schedule whose degree caps make `epsilonX` concrete.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## The derived key's captured scalars -/

/-- Field projections commute with the shape cast when the field's type does not mention the
shape. -/
private theorem castVk_field {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) :
    K.omega = (h ▸ K : VerifyingKey s₂ Fp VestaG).omega ∧
    K.n = (h ▸ K : VerifyingKey s₂ Fp VestaG).n ∧
    K.gates = (h ▸ K : VerifyingKey s₂ Fp VestaG).gates ∧
    K.instanceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).instanceQueryLayout ∧
    K.adviceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).adviceQueryLayout ∧
    K.fixedQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).fixedQueryLayout ∧
    K.permutationChunks = (h ▸ K : VerifyingKey s₂ Fp VestaG).permutationChunks := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Lookup-expression projections commute with the shape cast, up to the index cast. -/
private theorem castVk_lookup {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) (l : Fin s₁.numLookups) :
    K.lookupInputExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupInputExprs
        (Fin.cast (congrArg Halo2.CircuitShape.numLookups h) l) ∧
    K.lookupTableExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupTableExprs
        (Fin.cast (congrArg Halo2.CircuitShape.numLookups h) l) := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **The Action circuit carries the captured scalar data.** The scalar fields do not depend on
the proof parameters or URS; the keygen certificate pins their circuit-owned values to the
capture. -/
theorem derived_scalars :
    actionCircuit.omega = vk.omega ∧
    actionCircuit.n = vk.n ∧
    actionCircuit.verifierCS.gates = vk.gates ∧
    actionCircuit.instanceQueryLayout =
      vk.instanceQueryLayout ∧
    actionCircuit.adviceQueryLayout =
      vk.adviceQueryLayout ∧
    actionCircuit.fixedQueryLayout =
      vk.fixedQueryLayout ∧
    actionCircuit.verifierCS.permutationChunks =
      vk.permutationChunks := by
  have hcast := castVk_field actionCircuitShape_eq_fixtureCircuitShape
    (actionCircuit.toVerifierKey capturedURS)
  simp only [actionCircuit.toVerifierKey_omega, actionCircuit.toVerifierKey_n,
    actionCircuit.toVerifierKey_gates, actionCircuit.toVerifierKey_instanceQueryLayout,
    actionCircuit.toVerifierKey_adviceQueryLayout, actionCircuit.toVerifierKey_fixedQueryLayout,
    actionCircuit.toVerifierKey_permutationChunks] at hcast
  have hvk : (actionCircuitShape_eq_fixtureCircuitShape ▸
      actionCircuit.toVerifierKey capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  exact ⟨hcast.1.trans (congrArg VerifyingKey.omega hvk),
    hcast.2.1.trans (congrArg VerifyingKey.n hvk),
    hcast.2.2.1.trans (congrArg VerifyingKey.gates hvk),
    hcast.2.2.2.1.trans (congrArg VerifyingKey.instanceQueryLayout hvk),
    hcast.2.2.2.2.1.trans (congrArg VerifyingKey.adviceQueryLayout hvk),
    hcast.2.2.2.2.2.1.trans (congrArg VerifyingKey.fixedQueryLayout hvk),
    hcast.2.2.2.2.2.2.trans (congrArg VerifyingKey.permutationChunks hvk)⟩

/-- The Action circuit and captured shape have the same lookup count. -/
theorem action_numLookups_eq :
    actionCircuit.lookupCount =
      shape.numLookups := by
  exact congrArg Halo2.CircuitShape.numLookups
    actionCircuitShape_eq_fixtureCircuitShape

private theorem actionShape_numLookups_eq :
    actionCircuit.lookupCount = shape.numLookups :=
  congrArg Halo2.CircuitShape.numLookups
    actionCircuitShape_eq_fixtureCircuitShape

/-- The circuit-owned lookup expressions are the captured ones, up to the index cast. -/
theorem derived_lookups
    (l : Fin actionCircuit.lookupCount) :
    actionCircuit.verifierCS.lookupInputExprs
        l =
      vk.lookupInputExprs (Fin.cast actionShape_numLookups_eq l) ∧
    actionCircuit.verifierCS.lookupTableExprs
        l =
      vk.lookupTableExprs (Fin.cast actionShape_numLookups_eq l) := by
  have hcast := castVk_lookup actionCircuitShape_eq_fixtureCircuitShape
    (actionCircuit.toVerifierKey capturedURS) l
  simp only [actionCircuit.toVerifierKey_lookupInputExprs,
    actionCircuit.toVerifierKey_lookupTableExprs] at hcast
  have hvk : (actionCircuitShape_eq_fixtureCircuitShape ▸
      actionCircuit.toVerifierKey capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  rw [hvk] at hcast
  exact hcast

/-! ## The captured checks and schedule at the derived shape -/

/-- The derived shape's count fields are the captured ones. -/
private theorem capturedActionDerivedShapeCounts :
    actionCircuit.domainExponent = shape.k ∧
    actionCircuit.adviceQueryCount =
      shape.numAdviceQueries ∧
    actionCircuit.instanceQueryCount =
      shape.numInstanceQueries ∧
    actionCircuit.fixedQueryCount =
      shape.numFixedQueries ∧
    actionCircuit.quotientPieceCount =
      shape.numQuotientPieces :=
  ⟨by
      exact congrArg Halo2.CircuitShape.k
        actionCircuitShape_eq_fixtureCircuitShape,
    by simpa only [Halo2.CircuitShape.withProofParams_numAdviceQueries,
        Halo2.TopLevelCircuit.adviceQueryCount] using
      congrArg (fun proofShape : Shape => proofShape.numAdviceQueries)
        actionShape_eq_fixtureShape,
    by simpa only [Halo2.CircuitShape.withProofParams_numInstanceQueries,
        Halo2.TopLevelCircuit.instanceQueryCount] using
      congrArg (fun proofShape : Shape => proofShape.numInstanceQueries)
        actionShape_eq_fixtureShape,
    by simpa only [Halo2.CircuitShape.withProofParams_numFixedQueries,
        Halo2.TopLevelCircuit.fixedQueryCount] using
      congrArg (fun proofShape : Shape => proofShape.numFixedQueries)
        actionShape_eq_fixtureShape,
    by simpa only [Halo2.CircuitShape.withProofParams_numQuotientPieces,
        Halo2.TopLevelCircuit.quotientPieceCount] using
      congrArg (fun proofShape : Shape => proofShape.numQuotientPieces)
        actionShape_eq_fixtureShape⟩

theorem action_domainExponent_eq :
    actionCircuit.domainExponent = 11 := by
  rw [Halo2.TopLevelCircuit.domainExponent,
    actionCircuit_shape_eq, actionShape_k]

/-- **The captured static checks at the derived key**: the concrete specialization
of `actionStaticChecks`, with the five decided facts transferred through the captured key's scalar
equalities. -/
theorem capturedActionStaticChecks
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_adviceQueryLayout,
      Halo2.CircuitShape.withProofParams_numAdviceQueries]
    exact le_of_eq actionCircuit.adviceQueryCount_eq_adviceQueryLayout_length
  instanceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_instanceQueryLayout,
      Halo2.CircuitShape.withProofParams_numInstanceQueries]
    exact le_of_eq actionCircuit.instanceQueryCount_eq_instanceQueryLayout_length
  fixedLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_fixedQueryLayout,
      Halo2.CircuitShape.withProofParams_numFixedQueries]
    exact le_of_eq actionCircuit.fixedQueryCount_eq_fixedQueryLayout_length
  omegaOrder := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_omega,
      actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainRoot
      ActionConstraintBounds.domainExponent_lt
  characteristic := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainSizeCastNeZero
      ActionConstraintBounds.domainExponent_lt

/-- **The captured `x`-squeeze schedule at the derived key**: the degree caps
transfer through the scalar equalities, and pinning is the family's own derived projection. -/
def capturedActionXSqueezeSchedule
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : actionCircuit.n - 1 = 2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
    norm_num
  have hkShape :
      2 ^ (actionCircuit.shape.withProofParams actionProofParams).k - 1 = 2047 := by
    simpa only [Halo2.CircuitShape.withProofParams_k,
      ← actionCircuit.n_eq_two_pow_domainExponent] using hk
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hkShape)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n, hk])
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_gates,
        derived_scalars.2.2.1]
      exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_permutationChunks,
        derived_scalars.2.2.2.2.2.2]
      exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      have hquotient :
          actionCircuit.quotientPieceCount = shape.numQuotientPieces :=
        capturedActionDerivedShapeCounts.2.2.2.2
      simp only [Halo2.TopLevelCircuit.quotientPieceCount] at hquotient
      rw [hvk basis, actionCircuit.toVerifierKey_n,
        Halo2.CircuitShape.withProofParams_numQuotientPieces,
        hquotient, ← hk,
        actionCircuit.n_eq_two_pow_domainExponent,
        action_domainExponent_eq]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

/-- Shape-independent Action circuit counts agree with the derived fixture fields. -/
theorem actionDerivedShapeCounts (numProofs : ℕ) :
    actionCircuit.domainExponent = shape.k ∧
    actionCircuit.adviceQueryCount =
      shape.numAdviceQueries ∧
    actionCircuit.instanceQueryCount =
      shape.numInstanceQueries ∧
    actionCircuit.fixedQueryCount =
      shape.numFixedQueries ∧
    actionCircuit.quotientPieceCount =
      shape.numQuotientPieces := by
  have h := actionShapeFor_eq_fixtureShape numProofs
  exact
    ⟨by
        exact congrArg (fun proofShape : Shape => proofShape.k) h,
      by simpa only [Halo2.CircuitShape.withProofParams_numAdviceQueries,
          Halo2.TopLevelCircuit.adviceQueryCount] using
        congrArg (fun proofShape : Shape => proofShape.numAdviceQueries) h,
      by simpa only [Halo2.CircuitShape.withProofParams_numInstanceQueries,
          Halo2.TopLevelCircuit.instanceQueryCount] using
        congrArg (fun proofShape : Shape => proofShape.numInstanceQueries) h,
      by simpa only [Halo2.CircuitShape.withProofParams_numFixedQueries,
          Halo2.TopLevelCircuit.fixedQueryCount] using
        congrArg (fun proofShape : Shape => proofShape.numFixedQueries) h,
      by simpa only [Halo2.CircuitShape.withProofParams_numQuotientPieces,
          Halo2.TopLevelCircuit.quotientPieceCount] using
        congrArg (fun proofShape : Shape => proofShape.numQuotientPieces) h⟩

/-- The canonical Action static checks, quantified over arbitrary `numProofs`.  The captured-key
specialization is stated separately as `capturedActionStaticChecks`. -/
theorem actionStaticChecks (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_adviceQueryLayout,
      Halo2.CircuitShape.withProofParams_numAdviceQueries]
    exact le_of_eq actionCircuit.adviceQueryCount_eq_adviceQueryLayout_length
  instanceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_instanceQueryLayout,
      Halo2.CircuitShape.withProofParams_numInstanceQueries]
    exact le_of_eq actionCircuit.instanceQueryCount_eq_instanceQueryLayout_length
  fixedLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_fixedQueryLayout,
      Halo2.CircuitShape.withProofParams_numFixedQueries]
    exact le_of_eq actionCircuit.fixedQueryCount_eq_fixedQueryLayout_length
  omegaOrder := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_omega,
      actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainRoot
      ActionConstraintBounds.domainExponent_lt
  characteristic := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainSizeCastNeZero
      ActionConstraintBounds.domainExponent_lt

/-- The captured `x`-squeeze schedule transported to an arbitrary Action bundle size. -/
def actionXSqueezeSchedule (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : actionCircuit.n - 1 =
      2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
    norm_num
  have hkShape :
      2 ^ (actionCircuit.shape.withProofParams
          (actionProofParamsFor numProofs)).k - 1 = 2047 := by
    simpa only [Halo2.CircuitShape.withProofParams_k,
      ← actionCircuit.n_eq_two_pow_domainExponent] using hk
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hkShape)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n, hk])
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_gates,
        derived_scalars.2.2.1]
      exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_permutationChunks,
        derived_scalars.2.2.2.2.2.2]
      exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      have hquotient :
          actionCircuit.quotientPieceCount = shape.numQuotientPieces :=
        (actionDerivedShapeCounts numProofs).2.2.2.2
      simp only [Halo2.TopLevelCircuit.quotientPieceCount] at hquotient
      rw [hvk basis, actionCircuit.toVerifierKey_n,
        Halo2.CircuitShape.withProofParams_numQuotientPieces,
        hquotient, ← hk,
        actionCircuit.n_eq_two_pow_domainExponent,
        action_domainExponent_eq]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

end Zcash.Snark.Capstone

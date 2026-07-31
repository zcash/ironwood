import Zcash.Snark.Soundness.AGM.DeployedSyntheticOpened
import Zcash.Snark.Soundness.AGM.DeployedValueUnbatch
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.Composition.AlgebraicRootBudget

/-!
# Explicit deployed root sets for AGM multiopen decoding

This module packages the deterministic AGM `x4` batch and each within-set `x1` batch, then defines
the actual bad-root sets used by the rewind-free proof.  The bounds are direct Schwartz--Zippel
bounds.  Transcript causality (showing each set is pinned before its squeeze) is deliberately kept
separate in the computed-family adapter.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial
open scoped ENNReal

set_option maxRecDepth 10000

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments

/-- The rewind-free algebraic batches needed by the deployed value decoder. -/
structure DeployedAlgebraicBatches [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW : Fp) where
  x4 : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    aggregate aggregateU aggregateW ch.x4
  x1 : forall i (hi : i < deployedX4PairCount vk instanceCommitment ps ch),
    AlgebraicPowerBatch urs (deployedSetMemberCommitments urs hk vk instanceCommitment ps ch i)
      (x4.coeffs ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4.uComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩)
      (x4.wComp ⟨deployedX4PairCount vk instanceCommitment ps ch - 1 - i, by omega⟩) ch.x1

/-- The `x4` value-unbatching root set. -/
def deployedX4RootSet [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    Set Fp :=
  szBadSet (algebraicBatchErrorPolynomial (evalVector urs.k ch.x3)
    batches.x4.coeffs (x4BatchEvals vk instanceCommitment ps ch))

/-- The `x3` cleared-quotient root set, including collisions with any opened point. -/
def deployedX3RootSet [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    Set Fp :=
  ↑(szBadSet (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batches.x4) ∪
    deployedAllPts vk instanceCommitment ps ch)

/-- All `x2` set-separation roots, united over deployed opened nodes. -/
def deployedX2RootSet [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    Set Fp :=
  {x | ∃ node, node ∈ deployedAllPts vk instanceCommitment ps ch ∧
    x ∈ szBadSet (nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
      (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
      (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batches.x4)
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node)}

/-- The member-binding polynomial for one deployed point set and one node in that set. -/
def deployedX1RootPolynomial [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length) :
    CPoly :=
  memberBindingErrorPolynomial
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
      coeffsToPoly ((batches.x1 i hi).coeffs m))
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (idx : Nat) 0)
    ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]

/-- All `x1` member-separation roots for one point set, united over that set's nodes.  Out-of-range
shape slots are empty, allowing the final root family to use the fixed size `shape.numPointSets`. -/
def deployedX1RootSet [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) : Set Fp :=
  if hi : i < deployedX4PairCount vk instanceCommitment ps ch then
    {x | exists idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length,
      idx ∈ (Finset.univ : Finset
        (Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length)) ∧
      x ∈ szBadSet (deployedX1RootPolynomial urs hk vk instanceCommitment ps ch batches i hi idx)}
  else ∅

/-- Direct price of the `x4` root set. -/
theorem deployedX4RootSet_measure_le [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX4RootSet urs hk vk instanceCommitment ps ch batches) <=
      (deployedX4PairCount vk instanceCommitment ps ch + 1 : Nat) / (Fintype.card Fp : ENNReal) := by
  exact algebraicBatch_badSet_measure_le (evalVector urs.k ch.x3)
    batches.x4.coeffs (x4BatchEvals vk instanceCommitment ps ch)

/-- Direct price of the `x3` identity and point-collision union. -/
theorem deployedX3RootSet_measure_le [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX3RootSet urs hk vk instanceCommitment ps ch batches) <=
      (max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card +
        2 * (deployedAllPts vk instanceCommitment ps ch).card : Nat) /
          (Fintype.card Fp : ENNReal) := by
  rw [deployedX3RootSet, uniformChallenge_badSet]
  apply ENNReal.div_le_div_right
  have hcard :
      (szBadSet (deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batches.x4) ∪
          deployedAllPts vk instanceCommitment ps ch).card <=
        max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card +
          2 * (deployedAllPts vk instanceCommitment ps ch).card := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have hroot := le_trans (szBadSet_card_le _)
      (deployedX3ErrorPolynomial_natDegree_le urs hk vk instanceCommitment ps ch batches.x4)
    omega
  exact_mod_cast hcard

/-- Direct price of all `x2` node roots. -/
theorem deployedX2RootSet_measure_le [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX2RootSet urs hk vk instanceCommitment ps ch batches) <=
      ((deployedAllPts vk instanceCommitment ps ch).card * deployedX4PairCount vk instanceCommitment ps ch : Nat) /
        (Fintype.card Fp : ENNReal) := by
  exact uniformChallenge_szBadSet_iUnion_le (deployedAllPts vk instanceCommitment ps ch)
    (fun node => nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
      (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
      (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batches.x4)
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node)
    (deployedX4PairCount vk instanceCommitment ps ch) (fun _ _ => powerErrorPolynomial_natDegree_le _)

/-- Direct price of one point set's `x1` member roots. -/
theorem deployedX1RootSet_measure_le [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) :
    uniformChallenge.toOuterMeasure (deployedX1RootSet urs hk vk instanceCommitment ps ch batches i) <=
      ((queryBudget shape * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  rw [deployedX1RootSet]
  split
  next hi =>
    have hroot := uniformChallenge_szBadSet_iUnion_le
      (Finset.univ : Finset
        (Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length))
      (deployedX1RootPolynomial urs hk vk instanceCommitment ps ch batches i hi)
      (deployedSetQueries vk instanceCommitment ps ch i).length
      (fun _ _ => powerErrorPolynomial_natDegree_le _)
    refine le_trans hroot ?_
    have hnd := deployedSetsForEval_getD_nodup vk instanceCommitment ps ch hi
    have hpoints : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length <=
        queryBudget shape := by
      rw [<- List.toFinset_card_of_nodup hnd,
        deployedSetsForEval_getD_toFinset vk instanceCommitment ps ch hi]
      exact le_trans (Finset.card_le_card (deployedSetPts_subset vk instanceCommitment ps ch i))
        (deployedAllPts_card_le_budget vk instanceCommitment ps ch)
    have hmembers := deployedSetQueries_length_le vk instanceCommitment ps ch i
    gcongr
    · simpa using hpoints
  next hi => simp

/-- All deployed `x1` root sets, united into the single event at the one `x1` squeeze. -/
def deployedX1AllRootSet [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    Set Fp :=
  {x | exists i : Fin shape.numPointSets,
    x ∈ deployedX1RootSet urs hk vk instanceCommitment ps ch batches i}

/-- Every in-range per-set `x1` root belongs to the single union charged at the `x1` squeeze. -/
theorem mem_deployedX1AllRootSet_of_mem [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch) {x : Fp}
    (hx : x ∈ deployedX1RootSet urs hk vk instanceCommitment ps ch batches i) :
    x ∈ deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches :=
  ⟨⟨i, lt_of_lt_of_le hi (deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch)⟩, hx⟩

/-- Avoiding the union at `x1` avoids every in-range per-set root set. -/
theorem not_mem_deployedX1RootSet_of_not_mem_all [Inhabited G]
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    {x : Fp} (hgood : x ∉ deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches) :
    forall i, i < deployedX4PairCount vk instanceCommitment ps ch ->
      x ∉ deployedX1RootSet urs hk vk instanceCommitment ps ch batches i := by
  intro i hi hbad
  exact hgood (mem_deployedX1AllRootSet_of_mem urs hk vk instanceCommitment ps ch batches i hi hbad)

/-- Direct price of the union of every deployed `x1` root set. -/
theorem deployedX1AllRootSet_measure_le [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches) <=
      ((shape.numPointSets * queryBudget shape * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  have hsub : deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches <=
      ⋃ i : Fin shape.numPointSets, deployedX1RootSet urs hk vk instanceCommitment ps ch batches i := by
    rintro x ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    (∑ i : Fin shape.numPointSets,
        uniformChallenge.toOuterMeasure (deployedX1RootSet urs hk vk instanceCommitment ps ch batches i)) <=
      ∑ _i : Fin shape.numPointSets,
        ((queryBudget shape * queryBudget shape : Nat) : ENNReal) / Fintype.card Fp :=
        Finset.sum_le_sum fun i _ => deployedX1RootSet_measure_le urs hk vk instanceCommitment ps ch batches i
    _ = ((shape.numPointSets * queryBudget shape * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      simp only [div_eq_mul_inv]
      ring

/-! ## Shape-only prices used by the final pinned-root family -/

/-- Conservative shape price for the `x4` root. -/
theorem deployedX4RootSet_measure_le_shape [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX4RootSet urs hk vk instanceCommitment ps ch batches) <=
      ((shape.numPointSets + 1 : Nat) : ENNReal) / Fintype.card Fp := by
  refine le_trans (deployedX4RootSet_measure_le urs hk vk instanceCommitment ps ch batches) ?_
  gcongr
  exact deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch

/-- Conservative shape price for the `x3` identity and collision root. -/
theorem deployedX3RootSet_measure_le_shape [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX3RootSet urs hk vk instanceCommitment ps ch batches) <=
      ((max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  refine le_trans (deployedX3RootSet_measure_le urs hk vk instanceCommitment ps ch batches) ?_
  have hpts := deployedAllPts_card_le_budget vk instanceCommitment ps ch
  have hmax : max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card <=
      max (2 ^ shape.k) (queryBudget shape) := by
    rw [hk]
    exact max_le_max le_rfl hpts
  have hnum : max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card +
      2 * (deployedAllPts vk instanceCommitment ps ch).card <=
        max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape :=
    Nat.add_le_add hmax (Nat.mul_le_mul_left 2 hpts)
  apply ENNReal.div_le_div_right
  exact_mod_cast hnum

/-- Conservative shape price for all `x2` node roots. -/
theorem deployedX2RootSet_measure_le_shape [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    uniformChallenge.toOuterMeasure (deployedX2RootSet urs hk vk instanceCommitment ps ch batches) <=
      ((shape.numPointSets * queryBudget shape : Nat) : ENNReal) / Fintype.card Fp := by
  refine le_trans (deployedX2RootSet_measure_le urs hk vk instanceCommitment ps ch batches) ?_
  have hnum : (deployedAllPts vk instanceCommitment ps ch).card * deployedX4PairCount vk instanceCommitment ps ch <=
      shape.numPointSets * queryBudget shape := by
    calc
      (deployedAllPts vk instanceCommitment ps ch).card * deployedX4PairCount vk instanceCommitment ps ch <=
          queryBudget shape * shape.numPointSets :=
        Nat.mul_le_mul (deployedAllPts_card_le_budget vk instanceCommitment ps ch)
          (deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch)
      _ = shape.numPointSets * queryBudget shape := Nat.mul_comm _ _
  apply ENNReal.div_le_div_right
  exact_mod_cast hnum

end Zcash.Snark

import Zcash.Snark.Soundness.Composition.OrchardConsensusBounds
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Consensus-maximum concrete inputs for the primary straight-line AGM capstone

The DLOG advantage remains an explicit finite-security profile.  This file evaluates the
information-theoretic terms, connects the implemented direct-coordinate cost, and records the
tight three-bit query/group-work interpretation.
-/

namespace Zcash.Snark.FixtureMax


open Zcash.Arithmetic (card_Fp scalarFieldOrder)
open Zcash.Snark
open Zcash.Snark.ComputedStraightLineDeployedFSFamily (straightLineDlogGroupWork)
open scoped ENNReal

/-- Cross-multiplication helper for the concrete finite-field arithmetic. -/
private theorem ennreal_nat_div_le_one_div_straightLine {a p m : Nat}
    (hp : 0 < p) (hm : 0 < m) (h : a * m <= p) :
    (a : ENNReal) / p <= 1 / (m : ENNReal) := by
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hp.ne')
    (ENNReal.natCast_ne_top p)).2
  have hcast : (a : ENNReal) * (m : ENNReal) <= (p : ENNReal) := by exact_mod_cast h
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
    (Or.inl (ENNReal.natCast_ne_top m))).2 hcast
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- All straight-line statistical terms at the consensus maximum, excluding the supplied DLOG
advantage: `z=0`, the eleven IPA quadratics, six deployed roots, programmed-slot loss, and the
captured constraint-`x` root budget. -/
noncomputable def consensusStraightLineStatisticalModel (T : Nat) : ENNReal :=
  (T + 1 : Nat) * (1 / Fintype.card Fp) +
    (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
    consensusPinnedRootMultiopenModel T +
    1 / Fintype.card Fp +
    (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))

/-- Single-fraction form used for exact arithmetic. -/
theorem consensusStraightLineStatisticalModel_eq (T : Nat) :
    consensusStraightLineStatisticalModel T =
      (((T + 1) * (1 + 11 * 2 + 20470) +
          (T + 23) * 53_686_986_342_456 + 1 : Nat) : ENNReal) /
        Fintype.card Fp := by
  rw [consensusStraightLineStatisticalModel,
    consensusPinnedRootMultiopenModel_eq]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- At the largest work target supported by the explicit direct profile under a conservative
three-bit total-resource loss, the non-DLOG terms are below `2^-84`.  This is a probability
exponent, not the computational-security work factor. -/
theorem consensusStraightLineStatisticalModel_at_2pow123 :
    consensusStraightLineStatisticalModel (2 ^ 123) <=
      1 / (2 ^ 84 : ENNReal) := by
  rw [consensusStraightLineStatisticalModel_eq, card_Fp]
  convert ennreal_nat_div_le_one_div_straightLine
    (a := ((2 ^ 123 + 1) * (1 + 11 * 2 + 20470) +
      (2 ^ 123 + 23) * 53_686_986_342_456 + 1))
    (p := scalarFieldOrder) (m := 2 ^ 84)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) using 1
  norm_num

/-- Consensus-maximum compressed-identity bound with caller-supplied DLOG advantage and concrete
statistical error. -/
theorem straightLineConstraintFailure_prob_le_at_consensus_max
    (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineConstraintDlogProfile B)
    {T : Nat} (hQ : family.Q <= T) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
            3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B) <=
      profile.advantage family.straightLineDlogRandomOracleQueries
          (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
        consensusStraightLineStatisticalModel T := by
  refine le_trans
    (family.straightLineConstraintFailure_prob_le_of_dlogProfile B schedule profile) ?_
  rw [consensusStraightLineStatisticalModel]
  change _ <= profile.advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
    ((T + 1 : Nat) * (1 / Fintype.card Fp) +
      (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
      consensusPinnedRootMultiopenModel T +
      1 / Fintype.card Fp +
      (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
  rw [consensusPinnedRootMultiopenModel]
  simp only [show (shape orchardConsensusMaxProofs).k = 11 from rfl]
  -- Relax `Q` to `T` in the capstone's own association, then reassociate the shared DLOG term.
  calc
    _ <= (T + 1 : Nat) * (1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((11 : Nat) : ENNReal) * (2 / (Fintype.card Fp : ENNReal))) +
          ((T + 23 : Nat) : ENNReal) *
            algebraicRootBudget (shape orchardConsensusMaxProofs) 11 +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((20470 : Nat) : ENNReal) / (Fintype.card Fp : ENNReal)) := by
      gcongr
    _ = _ := by push_cast; ring

/-- Generator-random-oracle form of the consensus-maximum straight-line **compressed-identity**
endpoint. -/
theorem straightLineConstraintFailure_prob_le_at_consensus_max_generatorRO
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> T')
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineConstraintDlogProfile B)
    {T : Nat} (hQ : family.Q <= T) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
            3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent) <=
      profile.advantage family.straightLineDlogRandomOracleQueries
          (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
        consensusStraightLineStatisticalModel T := by
  refine le_trans
    (family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
      B hB query hquery schedule profile) ?_
  rw [consensusStraightLineStatisticalModel]
  change _ <= profile.advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
    ((T + 1 : Nat) * (1 / Fintype.card Fp) +
      (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
      consensusPinnedRootMultiopenModel T +
      1 / Fintype.card Fp +
      (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
  rw [consensusPinnedRootMultiopenModel]
  simp only [show (shape orchardConsensusMaxProofs).k = 11 from rfl]
  -- Relax `Q` to `T` in the capstone's own association, then reassociate the shared DLOG term.
  calc
    _ <= (T + 1 : Nat) * (1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((11 : Nat) : ENNReal) * (2 / (Fintype.card Fp : ENNReal))) +
          ((T + 23 : Nat) : ENNReal) *
            algebraicRootBudget (shape orchardConsensusMaxProofs) 11 +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((20470 : Nat) : ENNReal) / (Fintype.card Fp : ENNReal)) := by
      gcongr
    _ = _ := by push_cast; ring

/-- One execution of the actual direct-coordinate decode at the consensus shape, specialized to
the represented source consumed on that run. -/
theorem straightLineDirectDecodeOps_at_consensus_max_of_source
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    (hsource : forall basis O,
      (((wrappedAdversary family.toFamily basis).run O).1.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)).length <= 2 ^ 90) :
    forall basis O, family.straightLineDirectDecodeOps basis O <= 2 ^ 122 := by
  intro basis O
  unfold ComputedStraightLineDeployedFSFamily.straightLineDirectDecodeOps
  exact deployedDirectDecodeOps_at_consensus_max (Nat.le_refl orchardConsensusMaxProofs)
    _ _ _ _ (hsource basis O)

/-- Both possible direct-decode executions on the complete finder's fallback path fit the
`2^123` field/data budget under the same represented-source premise. -/
theorem straightLineDirectDecodeOps_twice_at_consensus_max_of_source
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    (hsource : forall basis O,
      (((wrappedAdversary family.toFamily basis).run O).1.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)).length <= 2 ^ 90) :
    forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= 2 ^ 123 := by
  intro basis O
  calc
    2 * family.straightLineDirectDecodeOps basis O <= 2 * 2 ^ 122 :=
      Nat.mul_le_mul_left 2
        (straightLineDirectDecodeOps_at_consensus_max_of_source family hsource basis O)
    _ = 2 ^ 123 := by norm_num

/-- **Primary profiled work-factor package for the direct route.**  At adversary target `2^123`,
the exact query formula and complete group-work profile each reach at most `2^126`; both possible
direct-decode executions remain below `2^123` modeled field/data operations.  The probability
bound is therefore

`Pr[failure] <= Adv_DLOG(2^126, 2^126) + 2^-84`.

This records a conservative **123-bit protocol work-factor target**, not 126-bit end-to-end
security.  With Vesta itself estimated at about 126 bits, the present three-bit resource loss
cannot justify a 126-bit protocol claim. -/
theorem orchard_deployed_straightline_consensus_2pow123_generatorRO_finite_security
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> T')
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineDirectDlogProfile B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
              3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.straightLineConstraintFailureEvent) <=
        profile.advantage (2 ^ 126) (2 ^ 126) +
          1 / (2 ^ 84 : ENNReal)) ∧
      family.straightLineDlogRandomOracleQueries <= 2 ^ 126 ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 2 ^ 126 ∧
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= 2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : family.straightLineDlogRandomOracleQueries <= 2 ^ 126 := by
    calc
      family.straightLineDlogRandomOracleQueries <= 8 * 2 ^ 123 := hcost.1
      _ = 2 ^ 126 := by norm_num
  have hgroup : straightLineDlogGroupWork profile.proverGroupWork
      profile.reductionGroupWork <= 2 ^ 126 := by
    calc
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <=
          8 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 126 := by norm_num
  refine ⟨?_, hqueries, hgroup, hcost.2.2⟩
  refine le_trans
    (straightLineConstraintFailure_prob_le_at_consensus_max_generatorRO
      B hB query hquery family schedule
      profile.toStraightLineConstraintDlogProfile profile.queryBound) ?_
  exact add_le_add
    (profile.advantage_mono hqueries hgroup)
    consensusStraightLineStatisticalModel_at_2pow123

end Zcash.Snark.FixtureMax

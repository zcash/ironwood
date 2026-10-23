import Zcash.Snark.Soundness.AGM.OnlineConstraint
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
import Zcash.Snark.Verifier.FieldSupport
import Zcash.Snark.Verifier.WellFormed
import Zcash.Arithmetic.Domain

/-!
# Composite constraint bound for the rewind-free AGM path

This module carries any additional explicit relation produced while upgrading the deployed member
decode to the concrete constraint relation through the same textbook-DLOG finder.  The remaining
`x`-challenge failure is an additive event supplied by the concrete pre-`x` schedule; no multiopen
rewind or fourth-root threshold appears.
-/

namespace Zcash.Snark

open Zcash.Common

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedDeployedConstraintContainment : Inhabited VestaG := ⟨0⟩

/-- **The total pre-`x` constraint difference**: built from the run's own pre-`x`
representation source over the family's retained list.  It mentions no root witness, batch
witness, decode, or outcome branch, so it is defined on every run — honest, cheating, or
degenerate. -/
def deployedConstraintDifferencePreX
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :
    CPoly :=
  let pnu := deployedRootRunOutput family basis coins
  committedPreXConstraintDifference
    (deployedConstraintPointPolynomial family basis pnu)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family basis pnu i).1)
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)

/-- Run the concrete online constraint adapter from a successful root decode and deployed
acceptance.  The result still preserves the explicit quotient-collision relation branch. -/
def deployedConstraintOutcomeOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferencePreX family basis coins)) :
    let pnu := deployedRootRunOutput family basis coins
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu))
        (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins haccept
  have hdeployed' : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins) hdeployed'
  exact deployedOnlineConstraintOutcomeOfDecode family basis pnu root.batchWitness
    (family.outcome_source basis coins root.batchWitness root.outcome_eq) root.decoded
    root.batches_eq checks
    (VerifyingKey.WellFormed.adviceQueryLayout_length (vk := family.vk basis)).ge
    (VerifyingKey.WellFormed.instanceQueryLayout_length (vk := family.vk basis)).ge
    (VerifyingKey.WellFormed.fixedQueryLayout_length (vk := family.vk basis)).ge
    (family.vk basis).omega_pow_n (family.vk basis).n_cast_ne_zero hxgood

/-- A relation returned by the proof-producing root adapter is exactly the relation returned by
the standalone computable quotient comparison. -/
theorem deployedConstraintOutcomeOfRoot_relation_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferencePreX family basis coins))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hout : deployedConstraintOutcomeOfRoot family basis coins haccept root hxgood =
      PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis
      (deployedRootRunOutput family basis coins) = PSum.inr relation := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins haccept
  have hdeployed' : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins) hdeployed'
  apply deployedOnlineConstraintOutcome_relation_eq_online family basis pnu root.batchWitness
    (family.outcome_source basis coins root.batchWitness root.outcome_eq)
    root.decoded root.batches_eq checks
    (VerifyingKey.WellFormed.adviceQueryLayout_length (vk := family.vk basis)).ge
    (VerifyingKey.WellFormed.instanceQueryLayout_length (vk := family.vk basis)).ge
    (VerifyingKey.WellFormed.fixedQueryLayout_length (vk := family.vk basis)).ge
    (family.vk basis).omega_pow_n (family.vk basis).n_cast_ne_zero hxgood
    relation
  simpa [deployedConstraintOutcomeOfRoot, pnu, checks] using hout

/-- Proposition that the actual root-decode data yields a concrete constraint witness.  The
polynomial witness is executable finite data; every relation branch is also exposed by the
standalone computable `deployedConstraintQuotientFinder`. -/
def deployedConstraintDecodedOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    [∀ basis, VerifyingKey.FieldSupport (family.vk basis)]
    [∀ basis, VerifyingKey.WellFormed (family.vk basis)]
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  ∃ (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord
        (deployedRootRunOutput family basis coins)).x ∉
        szBadSet (deployedConstraintDifferencePreX family basis coins)),
    ∃ witness, deployedConstraintOutcomeOfRoot family basis coins haccept root hxgood =
      PSum.inl witness

/-- The concrete pre-`x` failure event: the run's `x` answer lands in the total constraint
difference's root set.  No decode or witness guard. -/
def deployedConstraintBadXEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (wrappedPreIpaRecord (deployedRootRunOutput family p.1 p.2)).x ∈
    szBadSet (deployedConstraintDifferencePreX family p.1 p.2)}

/-- **The total constraint-difference root set of one oracle table**: `szBadSet` of
the total pre-`x` difference, with no existential or success guard. -/
def deployedConstraintXBadSet (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Set Fp :=
  szBadSet (deployedConstraintDifferencePreX family basis O)

/-- A sufficient chronological condition for the constraint root set. This is stronger than the
live interface below: a reverse-unbatching decoder may legitimately consume challenges after `x`
while still being invariant under changing `x` itself. -/
def DeployedConstraintXPrefixDetermined
    (family : ComputedDeployedRootFSFamily shape) : Prop :=
  forall basis
    (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (forall t : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length 4 -> O t = O' t) ->
    deployedConstraintXBadSet family basis O =
      deployedConstraintXBadSet family basis O'

/-- **The exact causal property at `x`.** Changing only the run's priced `x` answer leaves the
constraint-difference bad set unchanged. Unlike strict prefix determination, this permits the
reverse-unbatching decoder to use later batching challenges. -/
def DeployedConstraintXPinning
    (family : ComputedDeployedRootFSFamily shape) : Prop :=
  forall basis
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    deployedConstraintXBadSet family basis
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) 4) v) =
      deployedConstraintXBadSet family basis O

/-- Strict pre-`x` determination implies the exact self-reprogramming equality consumed by
`PinnedRootEvent`.  The update point has the `x` prefix's own length, hence is outside the strict
prefix restriction. -/
theorem deployedConstraintXPinning_of_prefixDetermined
    (family : ComputedDeployedRootFSFamily shape)
    (hcausal : DeployedConstraintXPrefixDetermined family) :
    DeployedConstraintXPinning family := by
  intro basis O v
  apply hcausal basis _ O
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) 4).val.length =
      preIpaLen shape family.init.length 4 :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 4
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

/-- A computation of the constraint-difference root set that stops short of the deployed `x`
squeeze. `fresh` records that the selected `x` point was not queried, while `agrees` connects the
stage result to the final decoded root witness. -/
structure DeployedConstraintXOnlineTrace
    (family : ComputedDeployedRootFSFamily shape) where
  stage :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      OracleComp
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k)) Fp (Set Fp)
  agrees : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (stage basis).run O = deployedConstraintXBadSet family basis O
  fresh : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4 ∉
      (stage basis).queries O

/-- The staged pre-`x` trace derives the exact pinning equation used by the schedule. -/
theorem DeployedConstraintXOnlineTrace.toPinning
    {family : ComputedDeployedRootFSFamily shape}
    (trace : DeployedConstraintXOnlineTrace family) :
    DeployedConstraintXPinning family := by
  intro basis O v
  let updated := Function.update O (algebraicFullPrefixesPre family.init
    ((family.adversary basis).run O) 4) v
  calc
    deployedConstraintXBadSet family basis updated = (trace.stage basis).run updated :=
      (trace.agrees basis updated).symm
    _ = (trace.stage basis).run O :=
      OracleComp.run_update_of_not_mem_queries _ _ _ _ (trace.fresh basis O)
    _ = deployedConstraintXBadSet family basis O := trace.agrees basis O

/-- The deployed constraint family: direct root extraction plus the staged trace at `x`.
Both pinning equations used by the capstone are derived projections of its two traces. -/
/-
Inhabited twice.  `Composition.StraightLineWitness` does it at the degenerate witness shape;
`Composition.ZeroStraightLine` does it over the shape-generic zero prover, and
`Fixtures.MultiAction.Honest.CapturedZeroFamily` instantiates that at the captured key's own scalar
metadata, layouts and domain — so the six staged root events run against captured query layouts
and the staged IPA trace carries eleven live rounds rather than quantifying over `Fin 0`.

The zero prover inhabits this interface at the full captured shape
(`Fixtures.MultiAction.Honest.CapturedZeroFamily`): with
sub-proofs the pre-`x` difference is a nonzero polynomial, and the stage prices its root set
from the four folding squeezes alone.
-/
structure ComputedDeployedConstraintFSFamily (shape : Shape)
    extends ComputedDeployedRootFSFamily shape where
  constraintXTrace :
    DeployedConstraintXOnlineTrace toComputedDeployedRootFSFamily

namespace ComputedDeployedConstraintFSFamily

/-- Forget the constraint-`x` trace while retaining the deployed root trace. -/
abbrev toRootFamily (family : ComputedDeployedConstraintFSFamily shape) :
    ComputedDeployedRootFSFamily shape := family.toComputedDeployedRootFSFamily

/-- Forget both deployed chronology refinements. -/
abbrev toFamily (family : ComputedDeployedConstraintFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toRootFamily.toFamily

/-- Package a deployed root family with its staged constraint-`x` trace. -/
def ofRoot (family : ComputedDeployedRootFSFamily shape)
    (trace : DeployedConstraintXOnlineTrace family) :
    ComputedDeployedConstraintFSFamily shape where
  toComputedDeployedRootFSFamily := family
  constraintXTrace := trace

/-- Exact constraint-`x` pinning derived from the family's staged trace. -/
theorem pinnedX (family : ComputedDeployedConstraintFSFamily shape) :
    DeployedConstraintXPinning family.toRootFamily :=
  family.constraintXTrace.toPinning

end ComputedDeployedConstraintFSFamily

/-- Causal condition at the `x` squeeze: the constraint-difference root set carries a uniform
bound and is unchanged when the run's own `x` answer is reprogrammed.  It may consume the earlier
`θ`/`β`/`γ`/`y` answers and the retained representations, but cannot be chosen after seeing
`x`. -/
structure DeployedConstraintXSqueezeSchedule (family : ComputedDeployedRootFSFamily shape)
    (epsilonX : ENNReal) where
  measure_le : forall basis O,
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (deployedConstraintXBadSet family basis O) <= epsilonX
  pinned : DeployedConstraintXPinning family

/-- The single pinned event for the constraint evaluation challenge. -/
def deployedConstraintXPinnedEvent
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootEvent (family.adversary basis) where
  point := fun p => algebraicFullPrefixesPre family.init p 4
  bad := fun _p O => deployedConstraintXBadSet family basis O
  budget := epsilonX
  measure_le := fun _p O => schedule.measure_le basis O
  pinned := fun O v => schedule.pinned basis O v

/-- The root-backed bad-`x` event lands in its run's exact pinned root set. -/
theorem deployedConstraintBadX_subset_landing
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins | (basis, coins) ∈ deployedConstraintBadXEvent family} <=
      {coins : family.toFamily.Coins |
        (deployedConstraintXPinnedEvent family schedule basis).Landing coins} := by
  rintro coins hx
  change coins (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run coins) 4) ∈
    deployedConstraintXBadSet family basis coins
  simpa [deployedConstraintBadXEvent, deployedRootRunOutput, wrappedPreIpaRecord, chRecord,
    wrappedPreIpaReads_run, runReads, runProof] using hx

/-- The exact constraint bad-root event has the direct additive cost `(Q + 1) * epsilonX`.
There is no multiopen rewind, continuation threshold, or fourth-root loss. -/
theorem deployedConstraintBadX_prob_le
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintBadXEvent family)
      <= (family.Q + 1 : Nat) * epsilonX := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.toFamily.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        deployedConstraintBadXEvent family =
      {x : (↥(Set.range query) -> VestaG) × family.toFamily.Coins | x.2 ∈
        (fun setup => {coins : family.toFamily.Coins |
          (orchardGeneratorROBasis query setup, coins) ∈
            deployedConstraintBadXEvent family}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)
    (fun setup => {coins : family.toFamily.Coins |
      (orchardGeneratorROBasis query setup, coins) ∈
        deployedConstraintBadXEvent family}) ?_
  intro setup
  let basis := orchardGeneratorROBasis query setup
  refine le_trans (MeasureTheory.measure_mono
    (deployedConstraintBadX_subset_landing family schedule basis)) ?_
  exact (deployedConstraintXPinnedEvent family schedule basis).landing_measure_le
    (family.queryBound basis)

/-! ## Promotion from the compressed identity to circuit semantics

The constraint witness above proves the verifier's identity only after `y` has compressed the
constraint list and `beta`, `gamma`, and `theta` have compressed the permutation and lookup values.
Calling that semantic circuit satisfaction is unsound without pricing collisions at those four
earlier squeezes. The interface below makes the step explicit: the caller supplies the semantic
predicate, the four failure events, and a proof that a compressed witness outside them has the
intended semantics.
-/

/-- Outside the four challenge-failure events, a compressed constraint witness upgrades to the
caller's row-level semantic predicate. In a concrete Orchard instantiation, `ConstraintRelations`
supplies this implication from the good-`y` fold split, good permutation `beta`/`gamma`, and good
lookup-tuple `theta` hypotheses. -/
def DeployedConstraintSemanticUpgradeContained
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins)) : Prop :=
  {p | compressedDecoded p.1 p.2 ∧ ¬ semanticDecoded p.1 p.2} <=
    badY ∪ (badBeta ∪ (badGamma ∪ badTheta))

/-- Failure of the semantic predicate is either failure of the compressed-identity extractor or
one of the four explicitly priced challenge surfaces. -/
theorem deployedConstraintSemanticFailure_subset_union
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hsemantic : DeployedConstraintSemanticUpgradeContained family compressedDecoded
      semanticDecoded badY badBeta badGamma badTheta) :
    snarkExtractionFailureEventDeployed family.toFamily semanticDecoded <=
      snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
        (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))) := by
  rintro p ⟨haccept, hnotSemantic⟩
  by_cases hcompressed : compressedDecoded p.1 p.2
  · exact Or.inr (hsemantic ⟨hcompressed, hnotSemantic⟩)
  · exact Or.inl ⟨haccept, hcompressed⟩

/-- The four-budget semantic promotion, factored over an arbitrary bound for the
compressed-identity failure event.  Both the schedule-only and the runtime-aware capstones pass
through this one calculation. -/
theorem snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    {compressedBound yBound betaBound gammaBound thetaBound : ENNReal}
    (hsemantic : DeployedConstraintSemanticUpgradeContained family
      compressedDecoded semanticDecoded badY badBeta badGamma badTheta)
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded)
      <= compressedBound)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
      <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) := by
  let mu := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
  let basisCoins : ((↥(Set.range query) -> VestaG) × family.toFamily.Coins) ->
      ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
    fun p => (orchardGeneratorROBasis query p.1, p.2)
  change mu (basisCoins ⁻¹'
      snarkExtractionFailureEventDeployed family.toFamily semanticDecoded) <= _
  have hsubset : basisCoins ⁻¹'
        snarkExtractionFailureEventDeployed family.toFamily semanticDecoded <=
      basisCoins ⁻¹'
        (snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
          (badY ∪ (badBeta ∪ (badGamma ∪ badTheta)))) :=
    Set.preimage_mono
      (deployedConstraintSemanticFailure_subset_union family compressedDecoded semanticDecoded
        badY badBeta badGamma badTheta hsemantic)
  calc
    mu (basisCoins ⁻¹'
        snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
        <= mu (basisCoins ⁻¹'
          (snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
            (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))))) :=
      MeasureTheory.measure_mono hsubset
    _ = mu ((basisCoins ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded) ∪
        ((basisCoins ⁻¹' badY) ∪
          ((basisCoins ⁻¹' badBeta) ∪
            ((basisCoins ⁻¹' badGamma) ∪ (basisCoins ⁻¹' badTheta))))) := by
      simp only [Set.preimage_union]
    _ <= mu (basisCoins ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded) +
        (mu (basisCoins ⁻¹' badY) +
          (mu (basisCoins ⁻¹' badBeta) +
            (mu (basisCoins ⁻¹' badGamma) + mu (basisCoins ⁻¹' badTheta)))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
            (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))))
    _ <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) :=
      add_le_add hcompressed (add_le_add hY (add_le_add hBeta (add_le_add hGamma hTheta)))



end Zcash.Snark

import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Action knowledge soundness as priced straight-line events

Prices straight-line extraction failures. Witness and relation projections share one executable
outcome.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedStraightLineActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin pp.numProofs → PublicInputs Fp)

variable
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- Knowledge-soundness failure for the straight-line/sequential presentation: the verifier
accepts, but the executable projection of the shared terminal outcome returns no private Action
witness bundle. -/
def actionKnowledgeFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    actionKnowledgeExtractor pp family static inputs hvk hI hchar q.1 q.2 = none}

/-- The accepted constraint model at the run's own decode. -/
abbrev actionRunModel
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- The accepted member polynomial at the run's own decode. -/
abbrev actionRunPolynomial
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- Decoding runs whose `x` or `y` challenge lands in the terminal's constraint-fold exclusion
sets: `x` in the combined-constraint difference roots, `y` in a fold-split witness. -/
def actionXYFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).x ∉ szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gates
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).sets
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunks
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lookups
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).beta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gamma
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).delta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).theta
          (straightLineRunRecord family q.1 q.2).y
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).l0
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lLast
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h
              CommitmentId.vanishingH *
            (X ^ actionCircuit.n - 1))) ∧
      ∀ j, (straightLineRunRecord family q.1 q.2).y ∉ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).constraints
          actionCircuit.n j))}

/-- Decoding runs whose `β` challenge lands in a permutation or lookup resolver exclusion set. -/
def actionBetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).beta ∉ allResolverPermutationBetaBadSet
        pp.numProofs (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k q.1))
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).beta ∉ allResolverLookupBetaBadSet
        pp.numProofs
        (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2))}

/-- Decoding runs whose `γ` challenge lands in a permutation or lookup resolver exclusion set. -/
def actionGammaFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).gamma ∉ allResolverPermutationGammaBadSet
        pp.numProofs (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).gamma ∉ allResolverLookupGammaBadSet
        pp.numProofs
        (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2))}

/-- Decoding runs whose `θ` challenge lands in the top-level lookup exclusion set. -/
def actionThetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬((straightLineRunRecord family q.1 q.2).theta ∉
      TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k q.1)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h))}

/-- The Action terminal on a decoded run outside all four challenge-failure events.  This is a
specification object: the DLOG reduction must not project its relation branch noncomputably, but
must cover that branch with `actionTerminalRelationFinderCovers` below. -/
def actionTerminalOutcomeOfGood
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hXY : (basis, O) ∉ actionXYFailureEvent pp family static inputs hvk hI hchar)
    (hBeta : (basis, O) ∉ actionBetaFailureEvent pp family static inputs hvk hI hchar)
    (hGamma : (basis, O) ∉ actionGammaFailureEvent pp family static inputs hvk hI hchar)
    (hTheta : (basis, O) ∉ actionThetaFailureEvent pp family static inputs hvk hI hchar) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).w := by
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  exact action_bundleStatement_or_relation_of_straightLineDecoded pp family static
    basis O inputs (hvk basis) (hI basis) hdecoded (hchar basis O)
    hxy.1 hxy.2 ⟨hgamma.1, hbeta.1⟩ ⟨hgamma.2, hbeta.2, htheta⟩

/-- Coverage requires every decoded good false-statement run to return explicit relation data. -/
def actionTerminalRelationFinderCovers
    (finder :
      (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) : Prop :=
  ∀ basis O,
    family.straightLineConstraintDecoded static basis O →
    (basis, O) ∉ actionXYFailureEvent pp family static inputs hvk hI hchar →
    (basis, O) ∉ actionBetaFailureEvent pp family static inputs hvk hI hchar →
    (basis, O) ∉ actionGammaFailureEvent pp family static inputs hvk hI hchar →
    (basis, O) ∉ actionThetaFailureEvent pp family static inputs hvk hI hchar →
    ¬BundleStatement inputs →
    (finder basis O).isSome

set_option maxHeartbeats 800000 in
/-- Outside the four semantic challenge surfaces, a decoded run computes either all private
witnesses or explicit relation data. -/
theorem actionKnowledgeOutcome_isSome_of_good
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hXY : (basis, O) ∉ actionXYFailureEvent pp family static inputs hvk hI hchar)
    (hBeta : (basis, O) ∉ actionBetaFailureEvent pp family static inputs hvk hI hchar)
    (hGamma : (basis, O) ∉ actionGammaFailureEvent pp family static inputs hvk hI hchar)
    (hTheta : (basis, O) ∉ actionThetaFailureEvent pp family static inputs hvk hI hchar) :
    (actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O).isSome := by
  obtain ⟨success, hout⟩ :=
    family.straightLineConstraintOutcome?_eq_some_of_decoded static basis O hdecoded
  have hsuccess := family.straightLineConstraintSuccess_eq_of_outcome
    static basis O hdecoded success hout
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  have hdecode : actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) hdecoded =
      hI basis ▸ hvk basis ▸
        success.witness.decode.reRound (runRounds family.toFamily basis O) := by
    simp only [actionRunDecode, straightLineDecode, straightLineConstraintWitness, hsuccess]
  have haccepts := actionRunAccepts pp family static basis O inputs
    (hvk basis) (hI basis) hdecoded
  have hacceptsEq : actionRunAccepts pp family static basis O inputs
      (hvk basis) (hI basis) hdecoded =
      hI basis ▸ hvk basis ▸ success.accepts :=
    Subsingleton.elim _ _
  let successDecode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O)
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O))) :=
    hI basis ▸ hvk basis ▸
      success.witness.decode.reRound (runRounds family.toFamily basis O)
  let successAccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
    hI basis ▸ hvk basis ▸ success.accepts
  have hdecodeEq : actionRunDecode pp family static basis O inputs
      (hvk basis) (hI basis) hdecoded = successDecode := hdecode
  have hacceptsEq' : actionRunAccepts pp family static basis O inputs
      (hvk basis) (hI basis) hdecoded = successAccepts :=
    Subsingleton.elim _ _
  have hmodelEq : actionRunModel pp family static inputs hvk hI hchar basis O hdecoded =
      CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi =>
          successDecode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
        successAccepts := by
    unfold actionRunModel
    rw [hdecodeEq]
  have hpolyEq : actionRunPolynomial pp family static inputs hvk hI hchar basis O hdecoded =
      CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          successDecode.toMemberDecode (hchar basis O) i hi)
        successAccepts := by
    unfold actionRunPolynomial
    rw [hdecodeEq]
  unfold actionKnowledgeOutcome
  split
  · rfl
  · unfold actionTerminalWitnessOrRelationFinder
    rw [hout]
    simp only
    have hxgood : (straightLineRunRecord family basis O).x ∉ szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).gates
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).sets
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).chunks
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).lookups
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).beta
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).gamma
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).delta
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).theta
          (straightLineRunRecord family basis O).y
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).l0
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).lLast
          (actionRunModel pp family static inputs hvk hI hchar basis O hdecoded).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar basis O hdecoded
              CommitmentId.vanishingH *
            (X ^ actionCircuit.n - 1)) := hxy.1
    rw [hmodelEq, hpolyEq] at hxgood
    have hxgoodData := hxgood
    unfold straightLineRunRecord straightLineRunOutput at hxgoodData
    have hxgoodSome := (szBadSetAvoidance?_isSome_iff _ _).2 hxgoodData
    split
    · rename_i hxgoodProof _
      have hgoodY' := hxy.2
      rw [hmodelEq] at hgoodY'
      let hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
      have hgoodYSome := foldSplitAvoidance?_isSome_of _ _ hn _ hgoodY'
      split
      · rename_i hgoodYProof _
        have hpermutation' : ResolverPermutationChallengeExclusions
                pp.numProofs (actionCircuit.toVerifierKey
                  (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
                (straightLineRunRecord family basis O)
                (actionRunPolynomial pp family static inputs hvk hI hchar
                  basis O hdecoded) actionActiveRows := ⟨hgamma.1, hbeta.1⟩
        rw [hpolyEq] at hpermutation'
        have hpermutationSome := resolverPermutationChallengeExclusions?_isSome_of
          pp.numProofs _ _ _ _ hpermutation'
        split
        · have hlookup' : TopLevelLookup.ChallengeExclusions
                  actionCircuit pp
                  (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
                  (straightLineRunRecord family basis O)
                  (actionRunPolynomial pp family static inputs hvk hI hchar
                    basis O hdecoded) := ⟨hgamma.2, hbeta.2, htheta⟩
          rw [hpolyEq] at hlookup'
          have hlookupSome :=
            TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
              actionCircuit pp
              (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) _ _ hlookup'
          split
          · split
            · rfl
            · split <;> rfl
          · rename_i hlookupEq
            simpa only [hlookupEq] using hlookupSome
        · rename_i hpermutationEq
          simpa only [hpermutationEq] using hpermutationSome
      · rename_i hgoodYEq
        simpa only [hgoodYEq] using hgoodYSome
    · rename_i hxgoodEq
      simpa only [hxgoodEq] using hxgoodSome

/-- The relation projection covers every good decoded run whose extracted witness would
contradict a claimed false bundle statement. -/
theorem actionRelationFinder_covers :
    actionTerminalRelationFinderCovers pp family static inputs hvk hI hchar
      (actionRelationFinder pp family static inputs hvk hI hchar) := by
  intro basis O hdecoded hXY hBeta hGamma hTheta hfalse
  have hsome := actionKnowledgeOutcome_isSome_of_good pp family static inputs hvk hI hchar
    basis O hdecoded hXY hBeta hGamma hTheta
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hsome
  cases outcome with
  | inl witness => exact False.elim (hfalse witness.statement)
  | inr relation =>
      unfold actionRelationFinder
      rw [houtcome]
      rfl

set_option maxHeartbeats 800000 in
/-- Straight-line knowledge failure is covered by the compressed failure, the computed DLOG
relation, and the four semantic challenge surfaces. -/
theorem actionKnowledgeFailure_subset_union :
    actionKnowledgeFailureEvent pp family static inputs hvk hI hchar ⊆
      (family.straightLineConstraintFailureEvent static ∪
        family.straightLineRelationEvent
          (actionRelationFinder pp family static inputs hvk hI hchar)) ∪
      (actionXYFailureEvent pp family static inputs hvk hI hchar ∪
        (actionBetaFailureEvent pp family static inputs hvk hI hchar ∪
          (actionGammaFailureEvent pp family static inputs hvk hI hchar ∪
            actionThetaFailureEvent pp family static inputs hvk hI hchar))) := by
  rintro q ⟨haccept, hextractor⟩
  by_cases hdecoded : family.straightLineConstraintDecoded static q.1 q.2
  · by_cases hXY : q ∈ actionXYFailureEvent pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inl hXY)
    by_cases hBeta : q ∈ actionBetaFailureEvent pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inl hBeta))
    by_cases hGamma : q ∈ actionGammaFailureEvent pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inr (Or.inl hGamma)))
    by_cases hTheta : q ∈ actionThetaFailureEvent pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTheta)))
    have hsome := actionKnowledgeOutcome_isSome_of_good pp family static inputs hvk hI hchar
      q.1 q.2 hdecoded hXY hBeta hGamma hTheta
    obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hsome
    cases outcome with
    | inl witness =>
        have hextracted := actionKnowledgeExtractor_eq_some_of_outcome_eq_inl
          pp family static inputs hvk hI hchar q.1 q.2 witness houtcome
        cases hextracted.symm.trans hextractor
    | inr relation =>
        refine Or.inl (Or.inr ?_)
        change (actionRelationFinder pp family static inputs hvk hI hchar q.1 q.2).isSome
        have hfinder := actionRelationFinder_eq_some_of_outcome_eq_inr
          pp family static inputs hvk hI hchar q.1 q.2 relation houtcome
        rw [hfinder]
        rfl
  · exact Or.inl (Or.inl ⟨haccept, hdecoded⟩)

/-- Conservative black-box calls of the combined finder: the existing constraint finder has its
proved four-call bound, and the terminal fallback performs at most two further represented-run
evaluations. -/
def actionRelationFinderCalls
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) : Nat :=
  family.straightLineConstraintRelationFinderCalls basis O + 2

/-- The combined constraint and Action relation finder uses at most six represented runs. -/
theorem actionRelationFinderCalls_le_six
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    actionRelationFinderCalls pp family basis O ≤ 6 := by
  unfold actionRelationFinderCalls
  have hcalls := family.straightLineConstraintRelationFinderCalls_le_four basis O
  omega

/-- The numeric random-oracle query cost of the combined constraint-plus-Action solver.  All six
represented prover runs include their own `11+k` designated transcript reads; no cache-sharing
convention is assumed.  This definition is the cost; fixture theorems separately prove ceilings
on it. -/
def actionDlogOracleQueryCost : Nat :=
  6 * family.Q + 6 * (11 + actionCircuit.domainExponent)

/-- The sequential witness extractor's numeric oracle-query cost.  It is the other projection of
the same six-call outcome. -/
def actionKnowledgeExtractorOracleQueryCost : Nat :=
  actionDlogOracleQueryCost pp family

/-- The knowledge extractor shares the combined finder's oracle-query cost. -/
@[simp] theorem actionKnowledgeExtractorOracleQueryCost_eq :
    actionKnowledgeExtractorOracleQueryCost pp family =
      actionDlogOracleQueryCost pp family := rfl

/-- The combined solver's numeric group-work cost.  Terminal comparison work is included in the
explicit reduction component; fixture theorems separately prove ceilings on this cost. -/
def actionDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  6 * proverGroupWork + reductionGroupWork

/-- One finite-security premise for the complete constraint-plus-Action relation finder. -/
structure StraightLineActionDlogProfile (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (advantage (actionDlogOracleQueryCost pp family)
      (actionDlogGroupWork proverGroupWork reductionGroupWork))

/-- Direct-route profile covering prover, postprocessing, and both possible decoder executions. -/
structure StraightLineActionDirectDlogProfile (B : VestaG) (T : Nat)
    extends StraightLineActionDlogProfile pp family static inputs hvk hI hchar B where
  scheduleOverheadBound : 3 * (11 + actionCircuit.domainExponent) <= T
  queryBound : family.Q <= T
  proverWorkBound : toStraightLineActionDlogProfile.proverGroupWork <= T
  reductionWorkBound : toStraightLineActionDlogProfile.reductionGroupWork <= T
  directDecodeWorkBound : forall basis O,
    2 * family.straightLineDirectDecodeOps basis O <= T

/-- The concrete Action profile bounds both DLOG-solver resources by an eightfold envelope and
retains the direct-decoder certificate used by the straight-line implementation. -/
theorem StraightLineActionDirectDlogProfile.solverCost_le
    {B : VestaG} {T : Nat}
    (profile : StraightLineActionDirectDlogProfile pp family static inputs
      hvk hI hchar B T) :
    actionDlogOracleQueryCost pp family <= 8 * T /\
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T /\
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  constructor
  · unfold actionDlogOracleQueryCost
    have hT := profile.scheduleOverheadBound
    calc
      6 * family.Q + 6 * (11 + actionCircuit.domainExponent) <=
          6 * T + 6 * (11 + actionCircuit.domainExponent) := by
        gcongr
        exact profile.queryBound
      _ <= 8 * T := by omega
  constructor
  · unfold actionDlogGroupWork
    calc
      6 * profile.proverGroupWork + profile.reductionGroupWork <= 6 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ <= 8 * T := by omega
  · exact profile.directDecodeWorkBound

/-- Runtime accounting for the sequential witness projection: it shares the profiled combined
outcome and therefore adds no seventh represented-prover run. -/
theorem StraightLineActionDirectDlogProfile.knowledgeExtractorCost_le
    {B : VestaG} {T : Nat}
    (profile : StraightLineActionDirectDlogProfile pp family static inputs
      hvk hI hchar B T) :
    actionKnowledgeExtractorOracleQueryCost pp family <= 8 * T /\
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T /\
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  simpa only [actionKnowledgeExtractorOracleQueryCost_eq] using profile.solverCost_le

/-- The combined finder exactly extends the constraint finder on every branch where that finder
succeeds.
-/
theorem actionRelationFinder_extends_constraint
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    (family.straightLineConstraintRelationFinder basis O).isSome →
      (actionRelationFinder pp family static inputs hvk hI hchar basis O).isSome := by
  intro hsome
  unfold actionRelationFinder
  cases hfinder : family.straightLineConstraintRelationFinder basis O with
  | none => simp [hfinder] at hsome
  | some relation =>
      have hout : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
          some (Sum.inr relation) := by
        unfold actionKnowledgeOutcome
        rw [hfinder]
      rw [hout]
      rfl

/-- Generator-random-oracle probability bound for the union of compressed failure and the complete
Action relation event.  The combined DLOG advantage occurs once. -/
theorem actionBaseUnion_probability_bound_of_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → T)
    (hquery : Function.Injective query)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineActionDlogProfile pp family static inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent
              (actionRelationFinder pp family static inputs hvk hI hchar))) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((actionCircuit.shape.withProofParams pp).k *
            (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + (actionCircuit.shape.withProofParams pp).k) + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams pp)
            (actionCircuit.shape.withProofParams pp).k +
        (profile.advantage (actionDlogOracleQueryCost pp family)
            (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  rw [family.straightLineConstraintFailure_union_relation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B static
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      (actionCircuit.shape.withProofParams pp).k B hB query hquery)]
  exact family.straightLineConstraintFailure_union_relation_prob_le_of_relationSupersetTextbookDL
    B static (actionRelationFinder pp family static inputs hvk hI hchar)
    (actionRelationFinder_extends_constraint pp family static inputs hvk hI hchar)
    schedule profile.hardness

/-- Probability bound for end-to-end straight-line Action knowledge failure, factored through the
profiled base-union and the four semantic challenge bounds. -/
theorem actionKnowledgeFailure_probability_bound_of_baseUnionBound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → T)
    {baseBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hbase : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent
              (actionRelationFinder pp family static inputs hvk hI hchar))) ≤ baseBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionKnowledgeFailureEvent pp family static inputs hvk hI hchar) ≤
      baseBound + (xyBound + (betaBound + (gammaBound + thetaBound))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (actionKnowledgeFailure_subset_union pp family static inputs
      hvk hI hchar))) ?_
  rw [Set.preimage_union, Set.preimage_union, Set.preimage_union, Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hbase ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hXY ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hBeta ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add hGamma hTheta

/-! ## Pricing the events over their squeezes

Each failure event fires on one challenge, and the run reads that challenge from the oracle at
its own squeeze prefix (`straightLineRunReads_eq`).  A caller who covers the run's exclusion set
with a prefix-determined bad-value function embeds the event into the index-generic squeeze
surface, so it costs `(Q + 1)` times a per-challenge measure.  Covering with a prefix-determined
function is a family-level fact — an AGM family's decode is pinned by the transcript prefix —
supplied here as the `hcompat` premises.
-/

/-- The `θ` event embeds into the index-`0` squeeze surface. -/
theorem actionThetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) →
      (Fin 0 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(TopLevelLookup.thetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (0 : Fin 11).isLt))))) :
    actionThetaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 0 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).theta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 0) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 0
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr hbad)
  rw [hread] at hmem
  exact hmem

/-- The `β` event embeds into the index-`1` squeeze surface. -/
theorem actionBetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) →
      (Fin 1 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationBetaBadSet
          pp.numProofs (actionCircuit.toVerifierKey
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupBetaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          (actionCircuit.n -
            actionCircuit.blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (1 : Fin 11).isLt))))) :
    actionBetaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 1 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).beta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 1) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 1
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `γ` event embeds into the index-`2` squeeze surface. -/
theorem actionGammaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) →
      (Fin 2 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationGammaBadSet
          pp.numProofs (actionCircuit.toVerifierKey
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupGammaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          (actionCircuit.n -
            actionCircuit.blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (2 : Fin 11).isLt))))) :
    actionGammaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 2 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).gamma =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 2) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 2
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `x`/`y` event embeds into the union of the index-`4` and index-`3` squeeze surfaces. -/
theorem actionXYFailureEvent_subset_surfaces
    (badFX : (AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) →
      (Fin 4 → Fp) → Set Fp)
    (badFY : (AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) →
      (Fin 3 → Fp) → Set Fp)
    (hcompatX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar basis O h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gates
          (actionRunModel pp family static inputs hvk hI hchar basis O h).sets
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunks
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lookups
          (actionRunModel pp family static inputs hvk hI hchar basis O h).beta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gamma
          (actionRunModel pp family static inputs hvk hI hchar basis O h).delta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).theta
          (straightLineRunRecord family basis O).y
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar basis O h).l0
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lLast
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ actionCircuit.n - 1))) ⊆
        badFX basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (4 : Fin 11).isLt)))))
    (hcompatY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      {v : Fp | ∃ j, v ∈ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar basis O h).constraints
          actionCircuit.n j)} ⊆
        badFY basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (3 : Fin 11).isLt))))) :
    actionXYFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 4 family.toFamily badFX ∪
        squeezeSurfaceEvent 3 family.toFamily badFY := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not] at hbad
  rcases hbad with hx | hy
  · have hread : (straightLineRunRecord family q.1 q.2).x =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 4) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 4
    have hmem := hcompatX q.1 q.2 h (Finset.mem_coe.mpr hx)
    rw [hread] at hmem
    exact Set.mem_union_left _ hmem
  · rw [not_forall] at hy
    obtain ⟨j, hj⟩ := hy
    rw [not_not] at hj
    have hread : (straightLineRunRecord family q.1 q.2).y =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 3) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 3
    have hmem := hcompatY q.1 q.2 h ⟨j, hj⟩
    rw [hread] at hmem
    exact Set.mem_union_right _ hmem

end ActionTerminal

end Zcash.Snark

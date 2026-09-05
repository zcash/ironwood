import Zcash.Snark.Soundness.Action.AdaptiveStatementSemantic

/-!
# Complete semantic terminal for adaptive Action statements

The complete terminal separates the identically-zero fixed pre-`x` difference from the ordinary
nonzero Schwartz--Zippel branch. Both branches operate on the statement and proof selected by the
same adaptive random-oracle run.
-/

namespace Zcash.Snark

open Classical Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance adaptiveStatementCompleteVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Good direct roots and the shifted equality decode the selected proof at the pre-IPA record. -/
def rawDecodeOfBatchGoodRootsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (witness : family.BatchWitnessV basis view)
    (hgood : family.BatchGoodRootsV basis view witness)
    (hshifted : family.ShiftedValueV basis view) :
    DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)) := by
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)
  have hvalue : commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      ((view.output.toAlgebraicWfProof).aMulti (view.pre)) =
      multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
        (view.output.toAlgebraicWfProof).proof.1 ch :=
    rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _
      hshifted.1 hshifted.2 hgood.xi hgood.z
  have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hgood.x1
  exact deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
    (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hvalue hgood.x4 hgood.x3 hgood.x2 hgood1

/-- Good direct roots and the shifted equality decode the selected proof at one table. -/
abbrev rawDecodeOfBatchGoodRoots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness)
    (hshifted : family.ShiftedValue basis O) :=
  family.rawDecodeOfBatchGoodRootsV basis (runView family basis O) witness hgood hshifted

theorem decodeOfBatchGoodRoots_eq_reRound {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness)
    (hshifted : family.ShiftedValue basis O) :
    family.decodeOfBatchGoodRoots basis O witness hgood hshifted =
      (family.rawDecodeOfBatchGoodRoots basis O witness hgood hshifted).reRound
        (family.runIpaReads basis O) := by
  rfl

theorem accepts?V_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (haccepts : family.acceptsV basis view) :
    (family.accepts?V basis view).isSome := by
  simp [accepts?V, haccepts]

theorem accepts?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (haccepts : family.accepts basis O) :
    (family.accepts? basis O).isSome :=
  family.accepts?V_isSome_of basis (runView family basis O) (by
    simpa only [acceptsV, accepts, runView_output, runView_pre, runView_rounds,
      family.runRecord_eq_chRecord] using haccepts)

theorem batchGoodRoots?V_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) (witness : family.BatchWitnessV basis view)
    (hgood : family.BatchGoodRootsV basis view witness) :
    (family.batchGoodRoots?V basis view witness).isSome := by
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let delta := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      ((view.output.toAlgebraicWfProof).aMulti (view.pre)) -
    multiopenValue (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 ch
  let sEval := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
    (view.output.toAlgebraicWfProof).s
  have hx1Some := deployedX1RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
    (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hgood.x1
  have hx2Some := deployedX2RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
    (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hgood.x2
  have hx3Some := deployedX3RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
    (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hgood.x3
  have hx4Some := deployedX4RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
    (view.output.toAlgebraicWfProof).proof.1 ch witness.batches hgood.x4
  have hxiSome := deployedXiRootAvoidance?_isSome_of delta sEval ch.xi hgood.xi
  have hzSome := deployedZRootAvoidance?_isSome_of delta
    ((view.output.toAlgebraicWfProof).multiU (view.pre))
    (view.output.toAlgebraicWfProof).sU sEval ch.xi ch.z hgood.z
  obtain ⟨hx1, hhx1⟩ := Option.isSome_iff_exists.mp hx1Some
  obtain ⟨hx2, hhx2⟩ := Option.isSome_iff_exists.mp hx2Some
  obtain ⟨hx3, hhx3⟩ := Option.isSome_iff_exists.mp hx3Some
  obtain ⟨hx4, hhx4⟩ := Option.isSome_iff_exists.mp hx4Some
  obtain ⟨hxi, hhxi⟩ := Option.isSome_iff_exists.mp hxiSome
  obtain ⟨hz, hhz⟩ := Option.isSome_iff_exists.mp hzSome
  unfold batchGoodRoots?V
  dsimp only
  rw [hhx1, hhx2, hhx3, hhx4, hhxi, hhz]
  rfl

theorem batchGoodRoots?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness) :
    (family.batchGoodRoots? basis O witness).isSome :=
  family.batchGoodRoots?V_isSome_of basis (runView family basis O) witness hgood

/-- The identically-zero pre-`x` branch yields an Action witness or an explicit relation. -/
def preXIdentityOutcome?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hfacts : family.SemanticStageFacts basis view)
    (witness : family.BatchWitnessV basis view)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder) :
    Option (ActionTerminal.ActionBundleWitness (view.output).inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := by
  let output := view.output
  let data := output.proofData
  let proof := view.output.toAlgebraicWfProof
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let source := data.algebraicProof.preX1AssemblySource fixed
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  let difference := adaptiveActionPreXDifference pp basis output.inputs
    data.algebraicProof.erase source ch
  if hsupport : difference = 0 then
    let decode := rawDecode.reRound (view.rounds)
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
    let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
    let preXPoly := committedPreXQuotient (adaptiveActionStatementVk pp basis) piecePoly
    have hpolyStage : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
        polynomial id = adaptiveActionCommitmentPolynomial pp basis output.inputs
          data.algebraicProof.erase
          (semanticRepresentationTarget output (4 : Fin 5) ++
            family.fixedRepresentations basis) ch id := by
      intro id hvanishing hrandom
      have havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
          adaptiveActionCommitmentAvailable (4 : Fin 5) id := by
        intro hactive
        cases id <;> simp_all [adaptiveActionCommitmentAvailable]
      have hraw := adaptiveStatementAcceptedPolynomialV_eq_stage_nonterminal
        family basis view (4 : Fin 5) id havailable ⟨hvanishing, hrandom⟩
        witness rawDecode hbatches hchar haccepts hfacts
      simpa only [polynomial, decode, output, data, ch] using hraw
    have hmodelStage : model = adaptiveActionCommittedModel pp basis output.inputs
        data.algebraicProof.erase
        (semanticRepresentationTarget output (4 : Fin 5) ++
          family.fixedRepresentations basis) ch := by
      unfold model adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      exact VerifyingKey.constraintModel_congr_nonterminal _
        (adaptiveActionStatementVk pp basis) ch _ _ _ hpolyStage
    have hsource4 : semanticRepresentationTarget output (4 : Fin 5) ++
        family.fixedRepresentations basis = source := by
      unfold semanticRepresentationTarget source fixed
      rw [List.append_assoc]
      exact data.algebraicProof.actionRepresentationsBefore_four_append
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis)
    have hmodel : model = adaptiveActionCommittedModel pp basis output.inputs
        data.algebraicProof.erase source ch := by
      rw [← hsource4]
      exact hmodelStage
    have hidentity :
        let committedModel := adaptiveActionCommittedModel pp basis output.inputs
          data.algebraicProof.erase source ch
        combineConstraints committedModel.fixedCols committedModel.adviceCols
            committedModel.instanceCols committedModel.gates committedModel.sets
            committedModel.chunks committedModel.lookups committedModel.beta
            committedModel.gamma committedModel.delta committedModel.theta ch.y
            committedModel.chunkLen committedModel.l0 committedModel.lLast
            committedModel.lBlind =
          preXPoly * (X ^ (adaptiveActionStatementVk pp basis).n - 1) := by
      have hzero := hsupport
      unfold difference at hzero
      rw [adaptiveActionPreXDifference_eq] at hzero
      exact sub_eq_zero.mp (by
        simpa only [preXPoly, piecePoly, adaptiveActionStatementVk] using hzero)
    have hsatisfiedRaw : model.CircuitSat ch.y preXPoly
        (adaptiveActionStatementVk pp basis).n
        (proof.aMulti (view.pre)) := by
      rw [hmodel]
      simpa only [proof, output] using hidentity
    have hsatisfied : model.CircuitSat ch.y preXPoly actionCircuit.n
        (proof.aMulti (view.pre)) := by
      simpa only [adaptiveActionStatementVk, actionCircuit.toVerifierKey_n] using hsatisfiedRaw
    let hn : actionCircuit.n ≠ 0 := by
      change 2 ^ actionCircuit.domainExponent ≠ 0
      positivity
    exact match hgoodY : foldSplitAvoidance? model.constraints actionCircuit.n hn ch.y with
    | none => none
    | some hgoodYProof =>
      match hpermutation : resolverPermutationChallengeExclusions?
          pp.numProofs (adaptiveActionStatementVk pp basis) ch polynomial actionActiveRows with
      | none => none
      | some hpermutationProof =>
        match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
            actionCircuit pp
            (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) ch polynomial with
        | none => none
        | some hlookupProof =>
          match ActionTerminal.action_bundleWitness_or_relation_of_decode_circuitSat pp
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl output.inputs
              proof.proof.1 ch
              (proof.multiU (view.pre))
              (proof.multiBlind (view.pre))
              (proof.aMulti (view.pre)) decode hchar haccepts
              preXPoly hsatisfied hgoodYProof.down hpermutationProof.down
              hlookupProof.down with
          | PSum.inl extracted => some (Sum.inl extracted)
          | PSum.inr relation => some (Sum.inr
              (augmentedBasis_ursOfAugmentedBasis
                (AdaptiveActionStatementShape pp).k basis ▸ relation))
  else
    exact none

/-- Relation-only projection of the pre-`x` identity outcome. -/
def preXIdentityRelation?V {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hfacts : family.SemanticStageFacts basis view)
    (witness : family.BatchWitnessV basis view)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.preXIdentityOutcome?V basis view hfacts witness rawDecode hbatches
      haccepts hchar with
  | some (Sum.inr relation) => some relation
  | _ => none

theorem preXIdentityRelationV_isSome_of_outcome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hfacts) (witness) (rawDecode) (hbatches) (haccepts) (hchar)
    (hcomplete : (family.preXIdentityOutcome?V basis view hfacts witness rawDecode
      hbatches haccepts hchar).isSome)
    (hfalse : ¬BundleStatement view.output.inputs) :
    (family.preXIdentityRelation?V basis view hfacts witness rawDecode hbatches
      haccepts hchar).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hcomplete
  cases outcome with
  | inl extracted => exact False.elim (hfalse extracted.statement)
  | inr relation =>
      unfold preXIdentityRelation?V
      rw [houtcome]
      rfl

theorem preXIdentityOutcomeV_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hfacts : family.SemanticStageFacts basis view)
    (witness : family.BatchWitnessV basis view)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (hsupport :
      let output := view.output
      let source := output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis)
      adaptiveActionPreXDifference pp basis output.inputs
        output.proofData.algebraicProof.erase source (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) = 0)
    (hgoodY :
      let decode := rawDecode.reRound (view.rounds)
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
      ∀ j, (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation :
      let decode := rawDecode.reRound (view.rounds)
      ResolverPermutationChallengeExclusions pp.numProofs (adaptiveActionStatementVk pp basis)
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
        actionActiveRows)
    (hlookup :
      let decode := rawDecode.reRound (view.rounds)
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    (family.preXIdentityOutcome?V basis view hfacts witness rawDecode hbatches
      haccepts hchar).isSome := by
  let decode := rawDecode.reRound (view.rounds)
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  dsimp only at hsupport hgoodY hpermutation hlookup
  have hn : actionCircuit.n ≠ 0 := by
    change 2 ^ actionCircuit.domainExponent ≠ 0
    positivity
  have hySome := foldSplitAvoidance?_isSome_of model.constraints _ hn _ hgoodY
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of _ _ _ _ _ hpermutation
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
      _ _ hlookup
  obtain ⟨hgoodYProof, hgoodYEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpermutationProof, hpermutationEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlookupProof, hlookupEq⟩ := Option.isSome_iff_exists.mp hlSome
  unfold preXIdentityOutcome?V
  rw [dif_pos hsupport]
  dsimp only
  rw [hgoodYEq, hpermutationEq, hlookupEq]
  dsimp only
  split <;> rfl

/-- Execute the identically-zero pre-`x` relation branch from a supplied acceptance result.  This
form lets the costed reduction feed in the result of its reified verifier MSM without evaluating
that group equation a second time. -/
def identityRelationFinderWithAcceptanceV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (acceptance : Option (PLift (family.acceptsV basis view)))
    (source : Option (AlgebraicRelationWitness (F := Fp) basis))
    (hfacts : source = none → family.SemanticStageFacts basis view) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match source, hfacts with
  | some relation, _ => some relation
  | none, hfacts =>
    let proof := view.output.toAlgebraicWfProof
    let nu := view.pre
    let rounds := view.rounds
    match acceptance with
    | none => none
    | some hacceptsProof =>
        let haccepts : family.acceptsV basis view := hacceptsProof.down
        if hz : nu 10 ≠ 0 then
          letI : Decidable (fullAlgebraicBindingAttackZ basis
              (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
              proof nu rounds) :=
            decidable_of_iff (family.bindingValueMismatchV basis view)
              (family.fullAlgebraicBindingAttackZ_iff_bindingValueMismatchV
                basis view haccepts hz).symm
          if hattack : fullAlgebraicBindingAttackZ basis
              (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
              proof nu rounds then
            none
          else
            match family.batchOutcomeV basis view with
            | PSum.inr relation =>
                some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
            | PSum.inl witness =>
                match family.batchGoodRoots?V basis view witness with
                | none => none
                | some hroots =>
                    let hshifted := family.shiftedValueV_of_accept_not_attack
                      basis view haccepts hz hattack
                    let rawDecode := family.rawDecodeOfBatchGoodRootsV basis view witness
                      hroots.down hshifted
                    let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
                        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
                        (adaptiveActionStatementVk pp basis)
                        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
                        proof.proof.1 (chRecord nu rounds) := haccepts
                    let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
                        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
                        proof.proof.1 (chRecord nu rounds) < scalarFieldOrder := hcharV
                    family.preXIdentityRelation?V basis view (hfacts rfl) witness
                      rawDecode rfl hacceptsFull hcharFull
        else none

/-- Execute just the identically-zero pre-`x` relation branch over one run view, with the
source-mismatch verdict supplied as an input. -/
def identityRelationFinderV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (source : Option (AlgebraicRelationWitness (F := Fp) basis))
    (hfacts : source = none → family.SemanticStageFacts basis view) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  family.identityRelationFinderWithAcceptanceV basis view hcharV
    (family.accepts?V basis view) source hfacts

/-- Identity relation branch at one table. -/
abbrev identityRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    family.identityRelationFinderV basis (runView family basis O)
      (by simpa only [runView_output, runView_pre, runView_rounds,
        family.runRecord_eq_chRecord] using hchar basis O)
      (family.semanticSourceMismatchRelationFinder basis O)
      (fun hsource => family.semanticStageFacts_of_sourceFinder_none basis O hsource)

theorem identityRelationFinder_none_source {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.identityRelationFinder hchar basis O = none) :
    family.semanticSourceMismatchRelationFinder basis O = none := by
  unfold identityRelationFinder identityRelationFinderV
    identityRelationFinderWithAcceptanceV at hnone
  split at hnone
  · simp_all
  · assumption

theorem identityRelationFinder_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none)
    (witness : family.BatchWitness basis O)
    (hout : family.batchOutcomeV basis (runView family basis O) = PSum.inl witness)
    (hroots : family.BatchGoodRoots basis O witness)
    (haccepts : family.accepts basis O)
    (hz : (runView family basis O).pre 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis
        (runView family basis O).output.inputs)
      (runView family basis O).output.toAlgebraicWfProof
      (runView family basis O).pre (runView family basis O).rounds)
    (hidentity :
      let hshifted := family.shiftedValue_of_accept_not_attack
        basis O haccepts hz hattack
      let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness hroots hshifted
      let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) := by
        simpa only [accepts, family.runRecord_eq_chRecord] using haccepts
      let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
            scalarFieldOrder := by
        simpa only [family.runRecord_eq_chRecord] using hchar basis O
      (family.preXIdentityRelation?V basis (runView family basis O)
        (family.semanticStageFacts_of_sourceFinder_none basis O hsource)
        witness rawDecode rfl hacceptsFull hcharFull).isSome) :
    (family.identityRelationFinder hchar basis O).isSome := by
  let hshifted := family.shiftedValue_of_accept_not_attack basis O haccepts hz hattack
  let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness hroots hshifted
  let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) := by
    simpa only [accepts, family.runRecord_eq_chRecord] using haccepts
  let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
        scalarFieldOrder := by
    simpa only [family.runRecord_eq_chRecord] using hchar basis O
  have hacceptsSome := family.accepts?V_isSome_of basis (runView family basis O)
    (by simpa only [acceptsV, accepts, runView_output, runView_pre, runView_rounds,
      family.runRecord_eq_chRecord] using haccepts)
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.batchGoodRoots?V_isSome_of basis (runView family basis O)
    witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  obtain ⟨relation, hrelationEq⟩ := Option.isSome_iff_exists.mp hidentity
  unfold identityRelationFinder identityRelationFinderV
    identityRelationFinderWithAcceptanceV
  split
  · simp_all
  · rw [hacceptsEq]
    dsimp only
    rw [dif_pos hz, dif_neg hattack, hout]
    dsimp only
    rw [hrootsEq]
    dsimp only
    rw [hrelationEq]
    rfl

/-- The existing nonzero semantic terminal returns relation data once its computed semantic
projection does. -/
theorem terminalRelationFinderV_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (witness : family.BatchWitnessV basis view)
    (hout : family.batchOutcomeV basis view = PSum.inl witness)
    (hroots : family.BatchGoodRootsV basis view witness)
    (haccepts : family.acceptsV basis view)
    (hz : view.pre 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof view.pre view.rounds)
    (hsemantic :
      let hshifted := family.shiftedValueV_of_accept_not_attack
        basis view haccepts hz hattack
      let run : family.DecodedRunV basis view :=
        { hchar := hcharV
          decode := family.decodeOfBatchGoodRootsV basis view witness hroots hshifted
          accepts := haccepts }
      (family.semanticRelation?V basis view run).isSome) :
    (family.terminalRelationFinderV basis view hcharV).isSome := by
  have hacceptsSome := family.accepts?V_isSome_of basis view haccepts
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.batchGoodRoots?V_isSome_of basis view witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  obtain ⟨relation, hrelationEq⟩ := Option.isSome_iff_exists.mp hsemantic
  unfold terminalRelationFinderV terminalRelationFinderWithAcceptanceV
  rw [hacceptsEq]
  dsimp only
  rw [dif_pos hz, dif_neg hattack, hout]
  dsimp only
  rw [hrootsEq]
  dsimp only
  rw [hrelationEq]
  rfl

/-- The nonzero semantic terminal projection at one table. -/
theorem terminalRelationFinder_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hout : family.batchOutcome basis O = PSum.inl witness)
    (hroots : family.BatchGoodRoots basis O witness)
    (haccepts : family.accepts basis O)
    (hz : family.runPreIpaReads basis O 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O) (family.runPreIpaReads basis O)
      (family.runIpaReads basis O))
    (hsemantic :
      let hshifted := family.shiftedValue_of_accept_not_attack
        basis O haccepts hz hattack
      let run : family.DecodedRun basis O :=
        { hchar := hchar basis O
          decode := family.decodeOfBatchGoodRoots basis O witness hroots hshifted
          accepts := haccepts }
      (family.semanticRelation? basis O run).isSome) :
    (family.terminalRelationFinder hchar basis O).isSome :=
  family.terminalRelationFinderV_isSome_of basis (runView family basis O) (hchar basis O)
    witness hout hroots
    (by simpa only [acceptsV, accepts, runView_output, runView_pre, runView_rounds,
      family.runRecord_eq_chRecord] using haccepts)
    hz hattack hsemantic

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark

import Zcash.Snark.Soundness.Action.AdaptiveStatementSurfaces

/-!
# Semantic bridge for adaptive Action statements

This module identifies the verifier's accepted polynomials with the online-AGM polynomials of
the statement and proof selected by the adversary. It also exposes deterministic relation
branches for source-coordinate and quotient-coordinate collisions.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

local instance adaptiveStatementSemanticVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

theorem adaptiveStatementInstanceLayout_column_lt {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (column : Nat) (rotation : Int)
    (hmem : (column, rotation) ∈
      (adaptiveActionStatementVk pp basis).instanceQueryLayout) :
    column < (AdaptiveActionStatementShape pp).numInstanceColumns := by
  rw [adaptiveActionStatement_numInstanceColumns]
  have hmem' : (column, rotation) ∈ actionCircuit.instanceQueryLayout := by
    simpa only [actionCircuit.toVerifierKey_instanceQueryLayout] using hmem
  have hall := actionCircuit.instanceQueryLayout_columns_lt
  have hlt := List.forall_iff_forall_mem.mp hall (column, rotation) hmem'
  simpa only [actionCircuit_numInstanceColumns_eq] using hlt

theorem BatchWitnessV.acceptedPolynomial_eq_online_of_query {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis}
    (witness : family.BatchWitnessV basis view)
    (decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      (view.output.toAlgebraicWfProof.aMulti view.pre)
      (view.output.toAlgebraicWfProof.multiU view.pre)
      (view.output.toAlgebraicWfProof.multiBlind view.pre))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (id : CommitmentId)
    (q : VerifierQuery (AdaptiveActionStatementShape pp).k Fp VestaG)
    (hq : q ∈ assembleQueries (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hqid : q.commId = id) (P : VestaG)
    (hpoint : assembledCommitment (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id = .point P) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound view.rounds).toMemberDecode hchar i hi)
        haccepts id =
      onlinePointPolynomial
        (view.output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              view.output.instanceRepresentations ++
            family.fixedRepresentations basis)) P := by
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
    view.output.toAlgebraicWfProof.proof.1
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis
      view.output.inputs)
    (adaptiveActionStatementVk pp basis) view.output.toAlgebraicWfProof.proof.1
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
    routing.1 routing.2 q hq
  have hmemberPoint : ((deployedSetQueries (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
      routed.slot.setIndex).getD (routed.slot.memberIndex : Nat) (.point 0, [])).1 =
        .point P := by
    rw [deployed_member_commitment_eq_assembled
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
        routed.slot.setIndex routed.slot.memberIndex CommitmentId.vanishingH
        (assembledQueryMemberRoute_id
          (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          (adaptiveActionStatementVk pp basis) view.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
          routing.1 routing.2 id routed.slot
          (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid]
            using routed.route_eq)) (.point 0, [])]
    exact hpoint
  have hmember : (decode.reRound view.rounds).memberPoly
        routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex =
      onlinePointPolynomial
        (view.output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              view.output.instanceRepresentations ++
            family.fixedRepresentations basis)) P := by
    change decode.memberPoly routed.slot.setIndex routed.slot.setIndex_lt
      routed.slot.memberIndex = _
    unfold DeployedAlgebraicDecode.memberPoly onlinePointPolynomial
    rw [hbatches]
    rw [congrFun (witness.memberCoeffs routed.slot.setIndex routed.slot.setIndex_lt)
      routed.slot.memberIndex]
    exact congrArg coeffsToPoly
      (deployedMemberRepresentationsOfCovered_coeffs_point
        view.output.toAlgebraicWfProof
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis)
        view.output.proofData.membersCovered
        view.pre
        routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex P hmemberPoint)
  have hroute : (CanonicalMemberConstraintRelation.acceptedRoute
      (G := VestaG) (shape := AdaptiveActionStatementShape pp)
      (urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
      (hk := rfl) (vk := adaptiveActionStatementVk pp basis)
      (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis
        view.output.inputs)
      (ps := view.output.toAlgebraicWfProof.proof.1)
      (ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds)
      haccepts) id = some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  exact hmember

/-- An active selected-statement commitment available at stage `n` has an explicit point in the
selected semantic source. -/
theorem adaptiveStatementActive_point_mem_stage {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5) (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id)
    (havailable : adaptiveActionCommitmentAvailable n id) :
    ∃ P,
      assembledCommitment (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 (family.runRecord basis O) id = .point P ∧
        ∃ ap ∈ semanticRepresentationTarget (family.runOutput basis O) n ++
            family.fixedRepresentations basis,
          ap.point = P := by
  let output := family.runOutput basis O
  let data := output.proofData
  let ic := adaptiveActionStatementInstanceCommitment pp basis output.inputs
  cases id with
  | instanceCol p column =>
      rcases hactive with ⟨hp, rotation, hlayout⟩
      have hcolumn := adaptiveStatementInstanceLayout_column_lt
        (pp := pp) basis column rotation hlayout
      let columnFin : Fin (AdaptiveActionStatementShape pp).numInstanceColumns :=
        ⟨column, hcolumn⟩
      let ap := output.instanceRepresentations ⟨p, hp⟩ columnFin
      refine ⟨ic ⟨p, hp⟩ column, ?_, ap, ?_, ?_⟩
      · rw [assembledCommitment, dif_pos hp]
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inr
        unfold adaptiveStatementInstanceRepresentationList
        apply List.mem_flatten.mpr
        refine ⟨List.ofFn (output.instanceRepresentations ⟨p, hp⟩), ?_, ?_⟩
        · exact List.mem_ofFn.mpr ⟨⟨p, hp⟩, rfl⟩
        · exact List.mem_ofFn.mpr ⟨columnFin, rfl⟩
      · exact output.instanceRepresented ⟨p, hp⟩ columnFin
  | adviceCol p column =>
      rcases hactive with ⟨hp, hcolumn, rotation, hlayout⟩
      let ap := data.algebraicProof.adviceCommitments ⟨p, hp⟩ ⟨column, hcolumn⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hcolumn]
        simp only [ap, data, output, runProof]
        rfl
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inl
        exact data.algebraicProof.adviceCommitment_mem_actionRepresentationsBefore
          n ⟨p, hp⟩ ⟨column, hcolumn⟩
  | fixedCol column =>
      rcases hactive with ⟨rotation, hlayout⟩
      obtain ⟨ap, hap, hpoint⟩ := family.fixedRepresented basis column ⟨rotation, hlayout⟩
      refine ⟨(adaptiveActionStatementVk pp basis).fixedCommitment column, rfl,
        ap, List.mem_append.mpr (Or.inr hap), hpoint⟩
  | permProduct p s =>
      rcases hactive with ⟨hp, hs⟩
      let ap := data.algebraicProof.permutationProduct ⟨p, hp⟩ ⟨s, hs⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hs]
        simp only [ap, data, output, runProof]
        rfl
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inl
        exact data.algebraicProof.permutationProduct_mem_actionRepresentationsBefore
          n ⟨p, hp⟩ ⟨s, hs⟩
          (by simpa [adaptiveActionCommitmentAvailable] using havailable)
  | lookupProduct p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupProduct ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, output, runProof]
        rfl
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inl
        exact data.algebraicProof.lookupProduct_mem_actionRepresentationsBefore
          n ⟨p, hp⟩ ⟨l, hl⟩
          (by simpa [adaptiveActionCommitmentAvailable] using havailable)
  | lookupPermInput p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedInput ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, output, runProof]
        rfl
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inl
        exact data.algebraicProof.lookupPermutedInput_mem_actionRepresentationsBefore
          n ⟨p, hp⟩ ⟨l, hl⟩
          (by simpa [adaptiveActionCommitmentAvailable] using havailable)
  | lookupPermTable p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedTable ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, output, runProof]
        rfl
      · apply List.mem_append.mpr
        apply Or.inl
        unfold semanticRepresentationTarget
        apply List.mem_append.mpr
        apply Or.inl
        exact data.algebraicProof.lookupPermutedTable_mem_actionRepresentationsBefore
          n ⟨p, hp⟩ ⟨l, hl⟩
          (by simpa [adaptiveActionCommitmentAvailable] using havailable)
  | permCommon c =>
      have hc : c < actionCircuit.permutationColumnCount := hactive
      obtain ⟨ap, hap, hpoint⟩ := family.permutationCommonRepresented basis ⟨c, hc⟩
      refine ⟨(adaptiveActionStatementVk pp basis).permutationCommonCommitment ⟨c, hc⟩,
        ?_, ap, List.mem_append.mpr (Or.inr hap), hpoint⟩
      simp [assembledCommitment, finFnG, hc]
  | vanishingH => exact False.elim hactive
  | randomPoly => exact False.elim hactive

/-- View-level semantic-stage facts an empty source-mismatch finder certifies: every active
commitment available at stage `n` resolves to a stage representation point, and the full
assembly polynomial agrees with each stage polynomial at those points. -/
structure SemanticStageFacts {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Prop where
  point_mem : ∀ (n : Fin 5) (id : CommitmentId),
    adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp)
      (adaptiveActionStatementVk pp basis) id →
    adaptiveActionCommitmentAvailable n id →
    ∃ P, assembledCommitment (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id =
          .point P ∧
      ∃ ap ∈ semanticRepresentationTarget view.output n ++
        family.fixedRepresentations basis, ap.point = P
  stage_eq : ∀ (n : Fin 5) (P : VestaG),
    (∃ ap ∈ semanticRepresentationTarget view.output n ++
      family.fixedRepresentations basis, ap.point = P) →
    onlinePointPolynomial
        (view.output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              view.output.instanceRepresentations ++
            family.fixedRepresentations basis)) P =
      onlinePointPolynomial
        (semanticRepresentationTarget view.output n ++
          family.fixedRepresentations basis) P

/-- An empty source-mismatch finder certifies the stage facts at the selected run's view. -/
theorem semanticStageFacts_of_sourceFinder_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none) :
    family.SemanticStageFacts basis (runView family basis O) := by
  constructor
  · intro n id hactive havailable
    simpa only [runView_output, runView_pre, runView_rounds,
      family.runRecord_eq_chRecord] using
      adaptiveStatementActive_point_mem_stage family basis O n id hactive havailable
  · intro n P hmem
    simpa only [runView_output] using
      family.semanticStagePolynomial_eq_full basis O hsource n P
        (by simpa only [runView_output] using hmem)


/-- On an accepted selected-statement decode, every active commitment available at a semantic
stage resolves to that stage's AGM polynomial. -/
theorem adaptiveStatementAcceptedPolynomialV_eq_stage {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (n : Fin 5) (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id)
    (havailable : adaptiveActionCommitmentAvailable n id)
    (witness : family.BatchWitnessV basis view)
    (decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      (view.output.toAlgebraicWfProof.aMulti view.pre)
      (view.output.toAlgebraicWfProof.multiU view.pre)
      (view.output.toAlgebraicWfProof.multiBlind view.pre))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hfacts : family.SemanticStageFacts basis view) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound view.rounds).toMemberDecode hchar i hi)
        haccepts id =
      adaptiveActionCommitmentPolynomial pp basis view.output.inputs
        view.output.toAlgebraicWfProof.proof.1
        (semanticRepresentationTarget view.output n ++
          family.fixedRepresentations basis)
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id := by
  obtain ⟨q, hq, hqid⟩ := adaptiveActionActive_query pp basis
    view.output.inputs view.output.toAlgebraicWfProof.proof.1
    (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id hactive
  obtain ⟨P, hpoint, hmem⟩ := hfacts.point_mem n id hactive havailable
  have hfull := BatchWitnessV.acceptedPolynomial_eq_online_of_query witness
    decode hbatches hchar haccepts id q hq hqid P hpoint
  have hstageP := hfacts.stage_eq n P hmem
  unfold adaptiveActionCommitmentPolynomial adaptiveActionCommitmentPolynomialOf
  rw [if_pos (show adaptiveActionCommitmentActive
      (actionCircuit.shape.withProofParams pp) (ActionTerminal.vkAt basis) id from hactive),
    show assembledCommitment (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id =
      CommitmentRef.point P from hpoint]
  exact hfull.trans hstageP

/-- Every selected-statement nonterminal slot agrees with the exact semantic-stage resolver;
inactive slots are absent from the accepting query list and therefore resolve to zero. -/
theorem adaptiveStatementAcceptedPolynomialV_eq_stage_nonterminal {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (n : Fin 5) (id : CommitmentId)
    (havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
      adaptiveActionCommitmentAvailable n id)
    (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly)
    (witness : family.BatchWitnessV basis view)
    (decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hfacts : family.SemanticStageFacts basis view) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound (view.rounds)).toMemberDecode hchar i hi)
        haccepts id =
      adaptiveActionCommitmentPolynomial pp basis (view.output).inputs
        (view.output.toAlgebraicWfProof).proof.1
        (semanticRepresentationTarget (view.output) n ++
          family.fixedRepresentations basis)
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) id := by
  by_cases hactive : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id
  · exact adaptiveStatementAcceptedPolynomialV_eq_stage family basis view n id
      hactive (havailable hactive) witness decode hbatches hchar haccepts hfacts
  · have habsent : ∀ q ∈ assembleQueries (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
        (view.output.toAlgebraicWfProof).proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds),
        q.commId ≠ id := by
      intro q hq hqid
      have hkind := adaptiveActionQuery_active_or_terminal pp basis
        (view.output).inputs (view.output.toAlgebraicWfProof).proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) q hq
      rw [hqid] at hkind
      rcases hkind with hactive' | hvanishing | hrandom
      · exact hactive hactive'
      · exact hterminal.1 hvanishing
      · exact hterminal.2 hrandom
    have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts id = none := by
      unfold CanonicalMemberConstraintRelation.acceptedRoute assembledQueryMemberRoute
      dsimp only
      split
      · rfl
      · rename_i q hfind
        have hq := List.mem_of_find?_eq_some hfind
        have hqid : q.commId = id := by simpa using List.find?_some hfind
        exact False.elim (habsent q hq hqid)
    have hzero : CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi =>
            (decode.reRound (view.rounds)).toMemberDecode hchar i hi)
          haccepts id = 0 := by
      unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
      rw [hroute]
    unfold adaptiveActionCommitmentPolynomial adaptiveActionCommitmentPolynomialOf
    rw [if_neg (show ¬adaptiveActionCommitmentActive
      (actionCircuit.shape.withProofParams pp) (ActionTerminal.vkAt basis) id from hactive)]
    exact hzero

/-- Compare the selected quotient MSM coordinates with the explicit quotient-piece power sum. -/
def statementQuotientAgreementOrRelationV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    let output := view.output
    let proof := view.output.toAlgebraicWfProof
    let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
      family.fixedRepresentations basis
    let source := proof.algebraicProof.preX1AssemblySource fixed
    let xn := (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x ^ (adaptiveActionStatementVk pp basis).n
    let msm := vanishingHCommitment (AdaptiveActionStatementShape pp).k xn
      (List.ofFn proof.proof.1.hPieces)
    let hcovered : CommitmentRefCovered source (.msm msm) := by
      intro pr hpr
      have hpoint : pr.2 ∈ msm.otherPoints := by
        rw [Zcash.Arithmetic.Msm.otherPoints]
        exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
      have hpiece := mem_otherPoints_vanishingHCommitment xn
        (List.ofFn proof.proof.1.hPieces) pr.2 hpoint
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
      refine ⟨proof.algebraicProof.hPieces i,
        proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, ?_⟩
      change (proof.algebraicProof.hPieces i).point = pr.2 at hi
      exact hi
    let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
    let pieces : AlgebraicColumnRepresentations
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) proof.proof.1.hPieces :=
      { coeffs := fun i => (onlinePointCoordinates source
            (proof.algebraicProof.hPieces i).point).1
        uComp := fun i => (onlinePointCoordinates source
            (proof.algebraicProof.hPieces i).point).2.1
        wComp := fun i => (onlinePointCoordinates source
            (proof.algebraicProof.hPieces i).point).2.2
        commitment := fun i => by
          simpa using onlinePointCoordinates_commitment source
            (proof.algebraicProof.hPieces i).point
            ⟨proof.algebraicProof.hPieces i,
              proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, rfl⟩ }
    (represented.coeffs = ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
        xn ^ (i : Nat) • pieces.coeffs i ∧
      represented.uComp = ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
        xn ^ (i : Nat) * pieces.uComp i ∧
      represented.wComp = ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
        xn ^ (i : Nat) * pieces.wComp i) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w := by
  dsimp only
  let output := view.output
  let proof := view.output.toAlgebraicWfProof
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let source := proof.algebraicProof.preX1AssemblySource fixed
  let xn := (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0)).x ^ (adaptiveActionStatementVk pp basis).n
  let msm := vanishingHCommitment (AdaptiveActionStatementShape pp).k xn
    (List.ofFn proof.proof.1.hPieces)
  let hcovered : CommitmentRefCovered source (.msm msm) := by
    intro pr hpr
    have hpoint : pr.2 ∈ msm.otherPoints := by
      rw [Zcash.Arithmetic.Msm.otherPoints]
      exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
    have hpiece := mem_otherPoints_vanishingHCommitment xn
      (List.ofFn proof.proof.1.hPieces) pr.2 hpoint
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    refine ⟨proof.algebraicProof.hPieces i,
      proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, ?_⟩
    change (proof.algebraicProof.hPieces i).point = pr.2 at hi
    exact hi
  let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
  let pieces : AlgebraicColumnRepresentations
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) proof.proof.1.hPieces :=
    { coeffs := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).1
      uComp := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).2.1
      wComp := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).2.2
      commitment := fun i => by
        simpa using onlinePointCoordinates_commitment source
          (proof.algebraicProof.hPieces i).point
          ⟨proof.algebraicProof.hPieces i,
            proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, rfl⟩ }
  let pieceCoeffs := ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
    xn ^ (i : Nat) • pieces.coeffs i
  let pieceU := ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
    xn ^ (i : Nat) * pieces.uComp i
  let pieceW := ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
    xn ^ (i : Nat) * pieces.wComp i
  have hvanishing : msm.eval
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) =
      ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
        xn ^ (i : Nat) • proof.proof.1.hPieces i := by
    calc
      _ = ∑ i ∈ Finset.range (List.ofFn proof.proof.1.hPieces).length,
          xn ^ i • (List.ofFn proof.proof.1.hPieces).getD i 0 :=
        vanishingHCommitment_eval
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) xn
          (List.ofFn proof.proof.1.hPieces)
      _ = _ := by
        rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
          List.getElem_ofFn]
  have hrepresented : commit
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) represented.coeffs +
      represented.uComp • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u +
      represented.wComp • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w =
        ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
          xn ^ (i : Nat) • proof.proof.1.hPieces i :=
    represented.commitment.trans hvanishing
  have hpieces : commit
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) pieceCoeffs +
      pieceU • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u +
      pieceW • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w =
        ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
          xn ^ (i : Nat) • proof.proof.1.hPieces i :=
    pieces.power_commitment xn
  have hcollision : commitGen
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g represented.coeffs +
      represented.uComp • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u +
      represented.wComp • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w =
      commitGen (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g pieceCoeffs +
        pieceU • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u +
        pieceW • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen, hrepresented, hpieces]
  exact separateOrRelationWitness
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w
    represented.coeffs pieceCoeffs represented.uComp pieceU represented.wComp pieceW hcollision

/-- Selected quotient-coordinate comparison at one table. -/
abbrev statementQuotientAgreementOrRelation {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  family.statementQuotientAgreementOrRelationV basis (runView family basis O)

/-- Project relation data from the selected quotient-coordinate comparison. -/
def statementQuotientRelationFinderV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.statementQuotientAgreementOrRelationV basis view with
  | PSum.inl _ => none
  | PSum.inr relation =>
      some (augmentedBasis_ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis ▸
        relation)

/-- Quotient relation projection at one table. -/
abbrev statementQuotientRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  family.statementQuotientRelationFinderV basis (runView family basis O)

/-- An empty quotient relation projection leaves the coordinate-agreement branch. -/
theorem statementQuotientAgreementV_of_finder_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hnone : family.statementQuotientRelationFinderV basis view = none) :
    ∃ agreement,
      family.statementQuotientAgreementOrRelationV basis view = PSum.inl agreement := by
  unfold statementQuotientRelationFinderV at hnone
  cases hout : family.statementQuotientAgreementOrRelationV basis view with
  | inl agreement => exact ⟨agreement, rfl⟩
  | inr relation => simp [hout] at hnone

/-- Off the semantic surface, the sampled challenges avoid every stage bad set: the `x`
difference, the `y` fold, and the permutation and lookup resolver exclusions. -/
theorem statementExclusionsV_of_no_surface {pp : ProofParams}
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
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (hsurface : ∀ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      let nu := view.pre
      nu n11 ∉ adaptiveActionSurfaceAt pp basis (view.output).inputs n
        (view.output.toAlgebraicWfProof).proof.1
        (semanticRepresentationTarget (view.output) n ++
          family.fixedRepresentations basis)
        (fun i => nu (i.castLE (le_of_lt n11.isLt)))) :
    let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
    let output := view.output
    let data := output.proofData
    let source := data.algebraicProof.preX1AssemblySource
      (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis)
    let decode := rawDecode.reRound (view.rounds)
    let actionModel := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
    let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
    ch.x ∉ szBadSet (adaptiveActionPreXDifference pp basis output.inputs
        data.algebraicProof.erase source ch) ∧
      (∀ j, ch.y ∉ szBadSet (foldSplitWitness actionModel.constraints
        actionCircuit.n j)) ∧
      ResolverPermutationChallengeExclusions pp.numProofs (adaptiveActionStatementVk pp basis)
        ch actionPoly actionActiveRows ∧
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) ch actionPoly := by
  simp only
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
  let output := view.output
  let data := output.proofData
  let inputs := output.inputs
  let nu := view.pre
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let source := data.algebraicProof.preX1AssemblySource fixed
  let decode := rawDecode.reRound (view.rounds)
  let actionModel := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
  let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  let stageCh (n : Fin 5) : Challenges (AdaptiveActionStatementShape pp).k Fp :=
    chRecord (fun i => if _h : (i : Nat) < (n : Nat) then nu ⟨i, by omega⟩ else 0)
      (fun _ => 0)
  let stageSource (n : Fin 5) :=
    semanticRepresentationTarget output n ++ family.fixedRepresentations basis
  let stagePoly (n : Fin 5) := adaptiveActionCommitmentPolynomial pp basis inputs
    data.algebraicProof.erase (stageSource n) (stageCh n)
  have hthetaRead : ch.theta = nu 0 := by rfl
  have hbetaRead : ch.beta = nu 1 := by rfl
  have hgammaRead : ch.gamma = nu 2 := by rfl
  have hyRead : ch.y = nu 3 := by rfl
  have hxRead : ch.x = nu 4 := by rfl
  have hpolyStage (n : Fin 5) (id : CommitmentId)
      (havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable n id)
      (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly) :
      actionPoly id = adaptiveActionCommitmentPolynomial pp basis inputs
        data.algebraicProof.erase (stageSource n) ch id := by
    have hraw := adaptiveStatementAcceptedPolynomialV_eq_stage_nonterminal
      family basis view n id havailable hterminal witness rawDecode hbatches hchar
      haccepts hfacts
    simpa only [actionPoly, decode, inputs, data, output, stageSource, ch] using hraw
  have hpolySurface (n : Fin 5) (id : CommitmentId)
      (havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable n id)
      (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly) :
      actionPoly id = stagePoly n id := by
    exact (hpolyStage n id havailable hterminal).trans
      (adaptiveActionCommitmentPolynomial_challenge_congr pp basis inputs
        data.algebraicProof.erase (stageSource n) ch (stageCh n) id hterminal.1)
  have hcolumnAvailable (id : CommitmentId) (hid : id.isColumnInput) :
      adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable (0 : Fin 5) id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isColumnInput, adaptiveActionCommitmentAvailable] at hid ⊢
  have hpermutationAvailable (n : Fin 5) (hn1 : 1 ≤ (n : Nat))
      (id : CommitmentId) (hid : id.isPermutationInput) :
      adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isPermutationInput, adaptiveActionCommitmentAvailable] at hid ⊢
  have hlookupAvailable (n : Fin 5) (hn1 : 1 ≤ (n : Nat))
      (id : CommitmentId) (hid : id.isLookupInput) :
      adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isLookupInput, adaptiveActionCommitmentAvailable, hn1] at hid ⊢
  have hnonterminal (id : CommitmentId)
      (hid : id.isColumnInput ∨ id.isPermutationInput ∨ id.isLookupInput) :
      id ≠ .vanishingH ∧ id ≠ .randomPoly := by
    cases id <;> simp [CommitmentId.isColumnInput, CommitmentId.isPermutationInput,
      CommitmentId.isLookupInput] at hid ⊢
  have hs0 := hsurface (0 : Fin 5)
  have hthetaStage : nu 0 ∉
      TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) (stagePoly 0) := by
    simpa [adaptiveActionSurfaceAt, stagePoly, stageCh, stageSource] using hs0
  have hthetaSet := TopLevelLookup.thetaBadSet_congr
    actionCircuit pp (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
    (poly₁ := actionPoly) (poly₂ := stagePoly 0) (fun id hid =>
      hpolySurface 0 id (hcolumnAvailable id hid) (hnonterminal id (Or.inl hid)))
  have htheta : ch.theta ∉
      TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) actionPoly := by
    rw [hthetaSet]
    simpa only [hthetaRead] using hthetaStage
  have hs1 := hsurface (1 : Fin 5)
  change nu 1 ∉ adaptiveActionSurfaceAt pp basis inputs 1
    data.algebraicProof.erase (stageSource 1)
      (fun i => nu (i.castLE (by omega))) at hs1
  let betaNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 1 then nu ⟨i, by omega⟩ else 0
  let betaCh : Challenges (AdaptiveActionStatementShape pp).k Fp :=
    chRecord betaNu (fun _ => 0)
  have hbetaCh : betaCh = stageCh 1 := by
    unfold betaCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [betaNu]
  have hbetaSurface : nu 1 ∉
      (↑(allResolverPermutationBetaBadSet pp.numProofs (adaptiveActionStatementVk pp basis)
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 1) betaCh) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupBetaBadSet
          pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord betaCh.theta 0
            (k := (AdaptiveActionStatementShape pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 1) betaCh)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    simpa [adaptiveActionSurfaceAt, betaNu, betaCh] using hs1
  have hbetaStage : nu 1 ∉
      (↑(allResolverPermutationBetaBadSet pp.numProofs (adaptiveActionStatementVk pp basis)
          (stagePoly 1) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupBetaBadSet
          pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord (nu 0) 0
            (k := (AdaptiveActionStatementShape pp).k)) (stagePoly 1)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    rw [hbetaCh] at hbetaSurface
    simpa [stagePoly, stageCh] using hbetaSurface
  rw [Set.mem_union, not_or] at hbetaStage
  have hbetaPermSet := allResolverPermutationBetaBadSet_congr pp.numProofs
    (adaptiveActionStatementVk pp basis) actionActiveRows
      (poly₁ := actionPoly) (poly₂ := stagePoly 1) (fun id hid =>
      hpolySurface 1 id (hpermutationAvailable 1 (by omega) id hid)
          (hnonterminal id (Or.inr (Or.inl hid))))
  have hbetaPerm : ch.beta ∉ allResolverPermutationBetaBadSet pp.numProofs
      (adaptiveActionStatementVk pp basis) actionPoly actionActiveRows := by
    rw [hbetaPermSet]
    simpa only [hbetaRead] using hbetaStage.1
  have hbetaLookupSet := allResolverLookupBetaBadSet_congr
    pp.numProofs (adaptiveActionStatementVk pp basis)
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2)
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) 0
        (k := (AdaptiveActionStatementShape pp).k))
      (by simpa using hthetaRead)
      (fun id hid => hpolySurface 1 id (hlookupAvailable 1 (by omega) id hid)
        (hnonterminal id (Or.inr (Or.inr hid))))
  have hbetaLookup : ch.beta ∉ allResolverLookupBetaBadSet
      pp.numProofs
      (adaptiveActionStatementVk pp basis) ch actionPoly
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2) := by
    rw [hbetaLookupSet]
    simpa only [hbetaRead] using hbetaStage.2
  have hs2 := hsurface (2 : Fin 5)
  change nu 2 ∉ adaptiveActionSurfaceAt pp basis inputs 2
    data.algebraicProof.erase (stageSource 2)
      (fun i => nu (i.castLE (by omega))) at hs2
  let gammaNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 2 then nu ⟨i, by omega⟩ else 0
  let gammaCh : Challenges (AdaptiveActionStatementShape pp).k Fp :=
    chRecord gammaNu (fun _ => 0)
  have hgammaCh : gammaCh = stageCh 2 := by
    unfold gammaCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [gammaNu]
  have hgammaSurface : nu 2 ∉
      (↑(allResolverPermutationGammaBadSet pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord gammaCh.theta gammaCh.beta
            (k := (AdaptiveActionStatementShape pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 2) gammaCh) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupGammaBadSet
          pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord gammaCh.theta gammaCh.beta
            (k := (AdaptiveActionStatementShape pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 2) gammaCh)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    simpa [adaptiveActionSurfaceAt, gammaNu, gammaCh] using hs2
  have hgammaStage : nu 2 ∉
      (↑(allResolverPermutationGammaBadSet pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord (nu 0) (nu 1)
            (k := (AdaptiveActionStatementShape pp).k)) (stagePoly 2)
          actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupGammaBadSet
          pp.numProofs (adaptiveActionStatementVk pp basis)
          (ActionTerminal.semanticChRecord (nu 0) (nu 1)
            (k := (AdaptiveActionStatementShape pp).k)) (stagePoly 2)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    rw [hgammaCh] at hgammaSurface
    simpa [stagePoly, stageCh] using hgammaSurface
  rw [Set.mem_union, not_or] at hgammaStage
  have hgammaPermSet := allResolverPermutationGammaBadSet_congr pp.numProofs
    (adaptiveActionStatementVk pp basis) actionActiveRows
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) (nu 1)
        (k := (AdaptiveActionStatementShape pp).k))
      (by simpa using hbetaRead)
      (poly₁ := actionPoly) (poly₂ := stagePoly 2) (fun id hid =>
        hpolySurface 2 id (hpermutationAvailable 2 (by omega) id hid)
          (hnonterminal id (Or.inr (Or.inl hid))))
  have hgammaPerm : ch.gamma ∉ allResolverPermutationGammaBadSet pp.numProofs
      (adaptiveActionStatementVk pp basis) ch actionPoly actionActiveRows := by
    rw [hgammaPermSet]
    simpa only [hgammaRead] using hgammaStage.1
  have hgammaLookupSet := allResolverLookupGammaBadSet_congr
    pp.numProofs (adaptiveActionStatementVk pp basis)
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2)
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) (nu 1)
        (k := (AdaptiveActionStatementShape pp).k))
      (by simpa using hthetaRead)
      (by simpa using hbetaRead)
      (fun id hid => hpolySurface 2 id (hlookupAvailable 2 (by omega) id hid)
        (hnonterminal id (Or.inr (Or.inr hid))))
  have hgammaLookup : ch.gamma ∉ allResolverLookupGammaBadSet
      pp.numProofs
      (adaptiveActionStatementVk pp basis) ch actionPoly
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2) := by
    rw [hgammaLookupSet]
    simpa only [hgammaRead] using hgammaStage.2
  have hallAvailable (n : Fin 5) (hn3 : 3 ≤ (n : Nat)) (id : CommitmentId)
      (hvanishing : id ≠ .vanishingH) (hrandom : id ≠ .randomPoly) :
      adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    have hn1 : 1 ≤ (n : Nat) := Nat.le_trans (by decide) hn3
    cases id <;>
      simp [adaptiveActionCommitmentAvailable, hn1, hn3] at hvanishing hrandom ⊢
  have hmodelStage (n : Fin 5) (hn3 : 3 ≤ (n : Nat)) : actionModel =
      adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
        (stageSource n) (stageCh n) := by
    have hfull : actionModel = adaptiveActionCommittedModel pp basis inputs
        data.algebraicProof.erase (stageSource n) ch := by
      unfold actionModel adaptiveActionCommittedModel
      exact VerifyingKey.constraintModel_congr_nonterminal _
        (adaptiveActionStatementVk pp basis) ch _ _ _ (fun id hv hr =>
          hpolyStage n id (hallAvailable n hn3 id hv hr) ⟨hv, hr⟩)
    have h0n : (0 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have h1n : (1 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have h2n : (2 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have hthetaStageCh : ch.theta = (stageCh n).theta := by
      calc
        ch.theta = nu 0 := hthetaRead
        _ = (stageCh n).theta := by
          change nu 0 = if _h : (0 : Nat) < (n : Nat) then nu 0 else 0
          rw [dif_pos h0n]
    have hbetaStageCh : ch.beta = (stageCh n).beta := by
      calc
        ch.beta = nu 1 := hbetaRead
        _ = (stageCh n).beta := by
          change nu 1 = if _h : (1 : Nat) < (n : Nat) then nu 1 else 0
          rw [dif_pos h1n]
    have hgammaStageCh : ch.gamma = (stageCh n).gamma := by
      calc
        ch.gamma = nu 2 := hgammaRead
        _ = (stageCh n).gamma := by
          change nu 2 = if _h : (2 : Nat) < (n : Nat) then nu 2 else 0
          rw [dif_pos h2n]
    exact hfull.trans (adaptiveActionCommittedModel_challenge_congr pp basis inputs
      data.algebraicProof.erase (stageSource n) ch (stageCh n)
      hthetaStageCh hbetaStageCh hgammaStageCh)
  have hs3 := hsurface (3 : Fin 5)
  change nu 3 ∉ adaptiveActionSurfaceAt pp basis inputs 3
    data.algebraicProof.erase (stageSource 3)
      (fun i => nu (i.castLE (by omega))) at hs3
  let yNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 3 then nu ⟨i, by omega⟩ else 0
  let yCh : Challenges (AdaptiveActionStatementShape pp).k Fp :=
    chRecord yNu (fun _ => 0)
  have hyCh : yCh = stageCh 3 := by
    unfold yCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [yNu]
  have hySurface : nu 3 ∉ ⋃ j,
      ↑(szBadSet (foldSplitWitness
        (adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
          (stageSource 3) yCh).constraints
        actionCircuit.n j)) := by
    simpa [adaptiveActionSurfaceAt, yNu, yCh] using hs3
  have hyStage : nu 3 ∉ ⋃ j,
      ↑(szBadSet (foldSplitWitness
        (adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
          (stageSource 3) (stageCh 3)).constraints
        actionCircuit.n j)) := by
    rw [hyCh] at hySurface
    exact hySurface
  have hy : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness actionModel.constraints actionCircuit.n j) := by
    intro j hj
    apply hyStage
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [← hmodelStage 3 (by omega)]
    simpa only [hyRead] using hj
  have hs4 := hsurface (4 : Fin 5)
  change nu 4 ∉ adaptiveActionSurfaceAt pp basis inputs 4
    data.algebraicProof.erase (stageSource 4)
      (fun i => nu (i.castLE (by omega))) at hs4
  let xNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 4 then nu ⟨i, by omega⟩ else 0
  let xCh : Challenges (AdaptiveActionStatementShape pp).k Fp :=
    chRecord xNu (fun _ => 0)
  have hxCh : xCh = stageCh 4 := by
    unfold xCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [xNu]
  have hxSurface : nu 4 ∉ szBadSet
      (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase
      (stageSource 4) xCh) := by
    simpa [adaptiveActionSurfaceAt, xNu, xCh] using hs4
  have hxStage : nu 4 ∉ szBadSet
      (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase
        source (stageCh 4)) := by
    rw [hxCh] at hxSurface
    have hsource4 : stageSource 4 = source := by
      unfold stageSource semanticRepresentationTarget source fixed
      rw [List.append_assoc]
      exact data.algebraicProof.actionRepresentationsBefore_four_append
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis)
    rw [hsource4] at hxSurface
    exact hxSurface
  have hdiff := adaptiveActionPreXDifference_challenge_congr pp basis inputs
    data.algebraicProof.erase source ch (stageCh 4)
    (by simpa [stageCh] using hthetaRead)
    (by simpa [stageCh] using hbetaRead)
    (by simpa [stageCh] using hgammaRead)
    (by simpa [stageCh] using hyRead)
  have hx : ch.x ∉ szBadSet (adaptiveActionPreXDifference pp basis inputs
      data.algebraicProof.erase source ch) := by
    rw [hdiff]
    simpa only [hxRead] using hxStage
  exact ⟨hx, hy, ⟨hgammaPerm, hbetaPerm⟩,
    ⟨hgammaLookup, hbetaLookup, htheta⟩⟩

/-- Outside the selected quotient-coordinate relation branch, the accepted vanishing member is
the quotient polynomial reassembled from the selected proof's explicit piece coordinates. -/
theorem statementAcceptedVanishingV_eq_fullQuotient {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hnone : family.statementQuotientRelationFinderV basis view = none)
    (witness : family.BatchWitnessV basis view)
    (decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre (fun _ => 0))
      ((view.output.toAlgebraicWfProof).aMulti (view.pre))
      ((view.output.toAlgebraicWfProof).multiU (view.pre))
      ((view.output.toAlgebraicWfProof).multiBlind (view.pre)))
    (hbatches : decode.batches = witness.batches)
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
        Zcash.Arithmetic.scalarFieldOrder) :
    (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound (view.rounds)).toMemberDecode hchar i hi)
        haccepts .vanishingH).eval (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).x =
      (committedPreXQuotient (adaptiveActionStatementVk pp basis)
        (fun i => onlinePointPolynomial
          ((view.output).proofData.algebraicProof.preX1AssemblySource
            (adaptiveStatementInstanceRepresentationList
                (view.output).instanceRepresentations ++
              family.fixedRepresentations basis))
          ((view.output).proofData.algebraicProof.hPieces i).point)).eval
            (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds).x := by
  let output := view.output
  let proof := view.output.toAlgebraicWfProof
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
  let source := proof.algebraicProof.preX1AssemblySource fixed
  let xn := ch.x ^ (adaptiveActionStatementVk pp basis).n
  let msm := vanishingHCommitment (AdaptiveActionStatementShape pp).k xn
    (List.ofFn proof.proof.1.hPieces)
  obtain ⟨agreement, hagreement⟩ :=
    family.statementQuotientAgreementV_of_finder_none basis view hnone
  have hcovered : CommitmentRefCovered source (.msm msm) := by
    intro pr hpr
    have hpoint : pr.2 ∈ msm.otherPoints := by
      rw [Zcash.Arithmetic.Msm.otherPoints]
      exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
    have hpiece := mem_otherPoints_vanishingHCommitment xn
      (List.ofFn proof.proof.1.hPieces) pr.2 hpoint
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    refine ⟨proof.algebraicProof.hPieces i,
      proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, ?_⟩
    change (proof.algebraicProof.hPieces i).point = pr.2 at hi
    exact hi
  let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
  let pieces : AlgebraicColumnRepresentations
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) proof.proof.1.hPieces :=
    { coeffs := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).1
      uComp := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).2.1
      wComp := fun i => (onlinePointCoordinates source
          (proof.algebraicProof.hPieces i).point).2.2
      commitment := fun i => by
        simpa using onlinePointCoordinates_commitment source
          (proof.algebraicProof.hPieces i).point
          ⟨proof.algebraicProof.hPieces i,
            proof.algebraicProof.hPiece_mem_preX1AssemblySource fixed i, rfl⟩ }
  have hcoeff : represented.coeffs =
      ∑ i : Fin (AdaptiveActionStatementShape pp).numQuotientPieces,
        xn ^ (i : Nat) • pieces.coeffs i := by
    simpa [statementQuotientAgreementOrRelationV, output, proof, fixed, source, xn,
      msm, hcovered, represented, pieces, chRecord, ch] using agreement.1
  obtain ⟨q, hq, hqid, -, -⟩ := vanishing_query_mem_assembleQueries
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    proof.proof.1 ch
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    proof.proof.1 ch haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    (adaptiveActionStatementVk pp basis) proof.proof.1 ch routing.1 routing.2 q hq
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts .vanishingH =
      some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  have hmemberCommit : ((deployedSetQueries (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      proof.proof.1 ch routed.slot.setIndex).getD
        (routed.slot.memberIndex : Nat) (.point 0, [])).1 = .msm msm := by
    rw [deployed_member_commitment_eq_assembled
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      proof.proof.1 ch routed.slot.setIndex routed.slot.memberIndex
      CommitmentId.vanishingH
      (assembledQueryMemberRoute_id
        (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveActionStatementVk pp basis) proof.proof.1 ch routing.1 routing.2
        .vanishingH routed.slot
        (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing] using hroute))
      (.point 0, [])]
    rfl
  have hmemberComponents := deployedMemberRepresentationsOfCovered_components proof fixed
    output.proofData.membersCovered (view.pre)
    routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex (.msm msm)
    hmemberCommit hcovered
  have hdecodedCoeffRaw : (decode.batches.x1 routed.slot.setIndex
      routed.slot.setIndex_lt).coeffs routed.slot.memberIndex = represented.coeffs := by
    rw [hbatches, congrFun (witness.memberCoeffs routed.slot.setIndex
      routed.slot.setIndex_lt) routed.slot.memberIndex]
    exact hmemberComponents.1
  have hdecodedCoeff : ((decode.reRound (view.rounds)).batches.x1
      routed.slot.setIndex routed.slot.setIndex_lt).coeffs routed.slot.memberIndex =
        represented.coeffs := hdecodedCoeffRaw
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  change (coeffsToPoly (((decode.reRound (view.rounds)).batches.x1
    routed.slot.setIndex routed.slot.setIndex_lt).coeffs routed.slot.memberIndex)).eval ch.x = _
  rw [hdecodedCoeff, hcoeff, coeffsToPoly_scaledSum]
  calc
    (reassembledQuotient xn (fun i => coeffsToPoly (pieces.coeffs i))).eval ch.x =
        (preXQuotient (adaptiveActionStatementVk pp basis).n
          (fun i => coeffsToPoly (pieces.coeffs i))).eval ch.x := by
      exact reassembledQuotient_eval_eq_preXQuotient_eval
        (adaptiveActionStatementVk pp basis).n
        (fun i => coeffsToPoly (pieces.coeffs i)) ch.x
    _ = (committedPreXQuotient (adaptiveActionStatementVk pp basis)
        (fun i => onlinePointPolynomial source
          (proof.algebraicProof.hPieces i).point)).eval ch.x := by
      apply congrArg (fun polynomial : CPoly => polynomial.eval ch.x)
      exact (committedPreXQuotient_eq (adaptiveActionStatementVk pp basis)
        (fun i => onlinePointPolynomial source
          (proof.algebraicProof.hPieces i).point)).symm

/-- The accepted selected-statement quotient check and fixed pre-`x` difference agree at the
sampled `x` outside the quotient-coordinate relation branch. -/
theorem statementAcceptedDifferenceV_eval_eq_preX {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hfacts : family.SemanticStageFacts basis view)
    (hquotient : family.statementQuotientRelationFinderV basis view = none)
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
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (view.output).inputs)
      (view.output.toAlgebraicWfProof).proof.1 (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder) :
    let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
    let output := view.output
    let data := output.proofData
    let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
      family.fixedRepresentations basis
    let source := data.algebraicProof.preX1AssemblySource fixed
    let decode := rawDecode.reRound (view.rounds)
    let actionModel := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
    let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
    (combineConstraints actionModel.fixedCols actionModel.adviceCols actionModel.instanceCols
        actionModel.gates actionModel.sets actionModel.chunks actionModel.lookups
        actionModel.beta actionModel.gamma actionModel.delta actionModel.theta ch.y
        actionModel.chunkLen actionModel.l0 actionModel.lLast actionModel.lBlind -
      actionPoly .vanishingH * (X ^ actionCircuit.n - 1)).eval ch.x =
    (adaptiveActionPreXDifference pp basis output.inputs data.algebraicProof.erase source ch).eval
      ch.x := by
  simp only
  let ch := chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds
  let output := view.output
  let data := output.proofData
  let inputs := output.inputs
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let source := data.algebraicProof.preX1AssemblySource fixed
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  let decode := rawDecode.reRound (view.rounds)
  let actionModel := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
  let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  have hvanishingRaw := statementAcceptedVanishingV_eq_fullQuotient family basis view
    hquotient witness rawDecode hbatches haccepts hchar
  have hvanishing : (actionPoly .vanishingH).eval ch.x =
      (committedPreXQuotient (adaptiveActionStatementVk pp basis) piecePoly).eval ch.x := by
    simpa only [actionPoly, decode, ch, output, data, fixed, source,
      piecePoly] using hvanishingRaw
  have hpolyStage : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
      actionPoly id = adaptiveActionCommitmentPolynomial pp basis inputs
        data.algebraicProof.erase
        (semanticRepresentationTarget output (4 : Fin 5) ++
          family.fixedRepresentations basis) ch id := by
    intro id hvanishingId hrandom
    have havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
        adaptiveActionCommitmentAvailable (4 : Fin 5) id := by
      intro hactive
      cases id <;> simp_all [adaptiveActionCommitmentAvailable]
    have hraw := adaptiveStatementAcceptedPolynomialV_eq_stage_nonterminal
      family basis view (4 : Fin 5) id havailable ⟨hvanishingId, hrandom⟩
      witness rawDecode hbatches hchar haccepts hfacts
    simpa only [actionPoly, decode, inputs, data, output, ch] using hraw
  have hmodelStage : actionModel = adaptiveActionCommittedModel pp basis inputs
      data.algebraicProof.erase
      (semanticRepresentationTarget output (4 : Fin 5) ++
        family.fixedRepresentations basis) ch := by
    unfold actionModel adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    exact VerifyingKey.constraintModel_congr_nonterminal _
      (adaptiveActionStatementVk pp basis) ch _ _ _ hpolyStage
  have hsource4 : semanticRepresentationTarget output (4 : Fin 5) ++
      family.fixedRepresentations basis = source := by
    unfold semanticRepresentationTarget source fixed
    rw [List.append_assoc]
    exact data.algebraicProof.actionRepresentationsBefore_four_append
      (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis)
  have hmodel : actionModel = adaptiveActionCommittedModel pp basis inputs
      data.algebraicProof.erase source ch := by
    rw [← hsource4]
    exact hmodelStage
  have hpiecePoly : piecePoly = fun i =>
      onlinePointPolynomial source (data.algebraicProof.erase.hPieces i) := by
    rfl
  change (combineConstraints actionModel.fixedCols actionModel.adviceCols
      actionModel.instanceCols actionModel.gates actionModel.sets actionModel.chunks
      actionModel.lookups actionModel.beta actionModel.gamma actionModel.delta actionModel.theta
      ch.y actionModel.chunkLen actionModel.l0 actionModel.lLast actionModel.lBlind -
    actionPoly .vanishingH * (X ^ actionCircuit.n - 1)).eval ch.x =
    (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase source ch).eval ch.x
  rw [hmodel]
  simp only [eval_sub, eval_mul]
  rw [hvanishing]
  rw [hpiecePoly]
  rw [adaptiveActionPreXDifference_eq]
  simp only [eval_sub, eval_mul, adaptiveActionStatementVk,
    actionCircuit.toVerifierKey_n]
  rfl


end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark

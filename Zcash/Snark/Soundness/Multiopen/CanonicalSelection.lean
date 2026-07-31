import Mathlib.Util.AssertNoSorry
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Canonical accepted-member selection

An accepting deployed verifier canonically routes each assembled query to a
decoded multiopen member. This module selects the advice- and instance-column
members named by the verifying key's query layouts and proves that the resulting
polynomial feeds are exactly those of the canonical accepted constraint model.

The construction is verifier-native and generic in the proof shape, group, and
verifying key. Every proof in the bundle gets its own selections.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial
open Classical

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

section Advice

variable {shape : Shape}
  (urs : URS G) (hk : shape.k = urs.k)
  (vk : VerifyingKey shape Fp G)
  (instanceCommitment : Fin shape.numProofs → ℕ → G)
  (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
  {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
  (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
    (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
  (memberDecode : ∀ i (hi : i <
      deployedX4PairCount vk instanceCommitment ps ch),
    OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
  (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
  (proofIndex : Fin shape.numProofs)
  (hLayout :
    vk.adviceQueryLayout.length = shape.numAdviceQueries)

omit [AddCommGroup G] [Module Fp G] in
private theorem adviceQueryExists
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    ∃ query ∈ assembleQueries vk instanceCommitment ps ch,
      query.commId =
        CommitmentId.adviceCol proofIndex
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).1 ∧
      query.point =
        rotateOmega vk.omega ch.x
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).2 := by
  obtain ⟨query, hmem, hid, hpt, -⟩ :=
    advice_query_mem_assembleQueries_eval vk instanceCommitment ps ch proofIndex
      (by rw [hLayout]; exact queryIndex.isLt) queryIndex.isLt
  exact ⟨query, hmem, hid, hpt⟩

private noncomputable def acceptedAdviceQuery
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    VerifierQuery shape.k Fp G :=
  Classical.choose
    (adviceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)

omit [AddCommGroup G] [Module Fp G] in
private theorem acceptedAdviceQuery_mem
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    acceptedAdviceQuery vk instanceCommitment ps ch proofIndex hLayout
        queryIndex ∈
      assembleQueries vk instanceCommitment ps ch :=
  (Classical.choose_spec
    (adviceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).1

omit [AddCommGroup G] [Module Fp G] in
private theorem acceptedAdviceQuery_id
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    (acceptedAdviceQuery vk instanceCommitment ps ch proofIndex hLayout
      queryIndex).commId =
        CommitmentId.adviceCol proofIndex
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).1 :=
  (Classical.choose_spec
    (adviceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).2.1

/--
The decoded member slot canonically routed from an advice query in the verifying
key's advice-query layout.
-/
noncomputable def acceptedAdviceSlot
    (urs : URS G) (hk : shape.k = urs.k)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    DeployedMemberSlot
      (instanceCommitment := instanceCommitment) vk ps ch :=
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  (assembledQueryMemberRoute_faithful
    (instanceCommitment := instanceCommitment)
    vk ps ch routing.1 routing.2
    (acceptedAdviceQuery vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)
    (acceptedAdviceQuery_mem vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).slot

private theorem acceptedAdviceSlot_route
    (urs : URS G) (hk : shape.k = urs.k)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (CommitmentId.adviceCol proofIndex
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).1) =
      some
        (acceptedAdviceSlot
          (vk := vk) (instanceCommitment := instanceCommitment)
          (ps := ps) (ch := ch) (proofIndex := proofIndex)
          urs hk haccepts hLayout queryIndex) := by
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  let routed :=
    assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment)
      vk ps ch routing.1 routing.2
      (acceptedAdviceQuery vk instanceCommitment ps ch proofIndex hLayout
        queryIndex)
      (acceptedAdviceQuery_mem vk instanceCommitment ps ch proofIndex hLayout
        queryIndex)
  calc
    CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (CommitmentId.adviceCol proofIndex
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).1) =
      CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (acceptedAdviceQuery vk instanceCommitment ps ch proofIndex hLayout
          queryIndex).commId := by
            apply congrArg
            exact (acceptedAdviceQuery_id vk instanceCommitment ps ch
              proofIndex hLayout queryIndex).symm
    _ = some routed.slot := by
      simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing] using
        routed.route_eq
    _ = some
        (acceptedAdviceSlot
          (vk := vk) (instanceCommitment := instanceCommitment)
          (ps := ps) (ch := ch) (proofIndex := proofIndex)
          urs hk haccepts hLayout queryIndex) := by
      rfl

private theorem acceptedAdviceSlot_polynomial
    (urs : URS G) (hk : shape.k = urs.k)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount vk instanceCommitment ps ch),
      OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (queryIndex : Fin shape.numAdviceQueries) :
    coeffsToPoly
        ((memberDecode
          (acceptedAdviceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).setIndex
          (acceptedAdviceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).setIndex_lt).cols
          (acceptedAdviceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).memberIndex) =
      CanonicalMemberConstraintRelation.acceptedPolynomial
        (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts
        (CommitmentId.adviceCol proofIndex
          (vk.adviceQueryLayout.getD queryIndex (0, 0)).1) := by
  rw [CanonicalMemberConstraintRelation.acceptedPolynomial,
    decodedPolynomialResolver,
    acceptedAdviceSlot_route
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hLayout queryIndex]
  rfl

/--
The member slots chosen directly from the accepted canonical route reproduce
the accepted model's complete advice polynomial feed, proof by proof.
-/
theorem acceptedAdviceSelection_feed_eq
    (hblinding : vk.blindingFactors < vk.n) :
    let slot := fun proofIndex =>
      acceptedAdviceSlot
        (vk := vk) (instanceCommitment := instanceCommitment)
        (ps := ps) (ch := ch) (proofIndex := proofIndex)
        urs hk haccepts hLayout
    (fun proofIndex : Fin shape.numProofs =>
      rotatedFeed vk.omega vk.adviceQueryLayout
        (fun queryIndex : Fin shape.numAdviceQueries =>
          coeffsToPoly
            ((memberDecode
              (slot proofIndex queryIndex).setIndex
              (slot proofIndex queryIndex).setIndex_lt).cols
              (slot proofIndex queryIndex).memberIndex))) =
      (CanonicalMemberConstraintRelation.acceptedModel
        (batchOpenings := pbatch)
        (memberDecode := memberDecode)
        (hblinding := hblinding)
        haccepts).adviceCols := by
  let slot := fun proofIndex =>
    acceptedAdviceSlot
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hLayout
  let selected :
      Fin shape.numProofs → Fin shape.numAdviceQueries → CPoly :=
    fun proofIndex queryIndex =>
      coeffsToPoly
        ((memberDecode
          (slot proofIndex queryIndex).setIndex
          (slot proofIndex queryIndex).setIndex_lt).cols
          (slot proofIndex queryIndex).memberIndex)
  funext proofIndex query
  change
    rotatedFeed vk.omega vk.adviceQueryLayout
        (selected proofIndex) query =
      adviceQueryFeedOfResolver vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts)
        proofIndex query
  by_cases hquery : query < shape.numAdviceQueries
  · simp only [rotatedFeed, adviceQueryFeedOfResolver, resolverQueryFeed,
      dif_pos hquery]
    rw [show selected proofIndex ⟨query, hquery⟩ =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts
          (CommitmentId.adviceCol proofIndex
            (vk.adviceQueryLayout.getD query (0, 0)).1) by
      exact acceptedAdviceSlot_polynomial
        (vk := vk) (instanceCommitment := instanceCommitment)
        (ps := ps) (ch := ch) (pbatch := pbatch)
        (proofIndex := proofIndex)
        urs hk memberDecode haccepts hLayout ⟨query, hquery⟩]
  · simp only [rotatedFeed, adviceQueryFeedOfResolver, resolverQueryFeed,
      dif_neg hquery]

assert_no_sorry acceptedAdviceSelection_feed_eq

end Advice

section Instance

variable {shape : Shape}
  (urs : URS G) (hk : shape.k = urs.k)
  (vk : VerifyingKey shape Fp G)
  (instanceCommitment : Fin shape.numProofs → ℕ → G)
  (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
  {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
  (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
    (x4BatchCommitments urs hk vk instanceCommitment ps ch)
    (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
  (memberDecode : ∀ i (hi : i <
      deployedX4PairCount vk instanceCommitment ps ch),
    OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
  (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
  (proofIndex : Fin shape.numProofs)
  (hLayout :
    vk.instanceQueryLayout.length = shape.numInstanceQueries)

omit [AddCommGroup G] [Module Fp G] in
private theorem instanceQueryExists
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    ∃ query ∈ assembleQueries vk instanceCommitment ps ch,
      query.commId =
        CommitmentId.instanceCol proofIndex
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).1 ∧
      query.point =
        rotateOmega vk.omega ch.x
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).2 := by
  obtain ⟨query, hmem, hid, hpt, -⟩ :=
    instance_query_mem_assembleQueries_eval vk instanceCommitment ps ch proofIndex
      (by rw [hLayout]; exact queryIndex.isLt) queryIndex.isLt
  exact ⟨query, hmem, hid, hpt⟩

private noncomputable def acceptedInstanceQuery
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    VerifierQuery shape.k Fp G :=
  Classical.choose
    (instanceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)

omit [AddCommGroup G] [Module Fp G] in
private theorem acceptedInstanceQuery_mem
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    acceptedInstanceQuery vk instanceCommitment ps ch proofIndex hLayout
        queryIndex ∈
      assembleQueries vk instanceCommitment ps ch :=
  (Classical.choose_spec
    (instanceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).1

omit [AddCommGroup G] [Module Fp G] in
private theorem acceptedInstanceQuery_id
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    (acceptedInstanceQuery vk instanceCommitment ps ch proofIndex hLayout
      queryIndex).commId =
        CommitmentId.instanceCol proofIndex
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).1 :=
  (Classical.choose_spec
    (instanceQueryExists vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).2.1

/--
The decoded member slot canonically routed from an instance query in the
verifying key's instance-query layout.
-/
noncomputable def acceptedInstanceSlot
    (urs : URS G) (hk : shape.k = urs.k)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    DeployedMemberSlot
      (instanceCommitment := instanceCommitment) vk ps ch :=
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  (assembledQueryMemberRoute_faithful
    (instanceCommitment := instanceCommitment)
    vk ps ch routing.1 routing.2
    (acceptedInstanceQuery vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)
    (acceptedInstanceQuery_mem vk instanceCommitment ps ch proofIndex hLayout
      queryIndex)).slot

private theorem acceptedInstanceSlot_route
    (urs : URS G) (hk : shape.k = urs.k)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (CommitmentId.instanceCol proofIndex
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).1) =
      some
        (acceptedInstanceSlot
          (vk := vk) (instanceCommitment := instanceCommitment)
          (ps := ps) (ch := ch) (proofIndex := proofIndex)
          urs hk haccepts hLayout queryIndex) := by
  let routing :=
    canonicalRoutingConditions_of_accepts
      urs hk vk instanceCommitment ps ch haccepts
  let routed :=
    assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment)
      vk ps ch routing.1 routing.2
      (acceptedInstanceQuery vk instanceCommitment ps ch proofIndex hLayout
        queryIndex)
      (acceptedInstanceQuery_mem vk instanceCommitment ps ch proofIndex hLayout
        queryIndex)
  calc
    CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (CommitmentId.instanceCol proofIndex
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).1) =
      CanonicalMemberConstraintRelation.acceptedRoute haccepts
        (acceptedInstanceQuery vk instanceCommitment ps ch proofIndex hLayout
          queryIndex).commId := by
            apply congrArg
            exact (acceptedInstanceQuery_id vk instanceCommitment ps ch
              proofIndex hLayout queryIndex).symm
    _ = some routed.slot := by
      simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing] using
        routed.route_eq
    _ = some
        (acceptedInstanceSlot
          (vk := vk) (instanceCommitment := instanceCommitment)
          (ps := ps) (ch := ch) (proofIndex := proofIndex)
          urs hk haccepts hLayout queryIndex) := by
      rfl

private theorem acceptedInstanceSlot_polynomial
    (urs : URS G) (hk : shape.k = urs.k)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount vk instanceCommitment ps ch),
      OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (queryIndex : Fin shape.numInstanceQueries) :
    coeffsToPoly
        ((memberDecode
          (acceptedInstanceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).setIndex
          (acceptedInstanceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).setIndex_lt).cols
          (acceptedInstanceSlot
            (vk := vk) (instanceCommitment := instanceCommitment)
            (ps := ps) (ch := ch) (proofIndex := proofIndex)
            urs hk haccepts hLayout queryIndex).memberIndex) =
      CanonicalMemberConstraintRelation.acceptedPolynomial
        (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts
        (CommitmentId.instanceCol proofIndex
          (vk.instanceQueryLayout.getD queryIndex (0, 0)).1) := by
  rw [CanonicalMemberConstraintRelation.acceptedPolynomial,
    decodedPolynomialResolver,
    acceptedInstanceSlot_route
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hLayout queryIndex]
  rfl

/--
The instance-column twin of `acceptedAdviceSelection_feed_eq`.
-/
theorem acceptedInstanceSelection_feed_eq
    (hblinding : vk.blindingFactors < vk.n) :
    let slot := fun proofIndex =>
      acceptedInstanceSlot
        (vk := vk) (instanceCommitment := instanceCommitment)
        (ps := ps) (ch := ch) (proofIndex := proofIndex)
        urs hk haccepts hLayout
    (fun proofIndex : Fin shape.numProofs =>
      rotatedFeed vk.omega vk.instanceQueryLayout
        (fun queryIndex : Fin shape.numInstanceQueries =>
          coeffsToPoly
            ((memberDecode
              (slot proofIndex queryIndex).setIndex
              (slot proofIndex queryIndex).setIndex_lt).cols
              (slot proofIndex queryIndex).memberIndex))) =
      (CanonicalMemberConstraintRelation.acceptedModel
        (batchOpenings := pbatch)
        (memberDecode := memberDecode)
        (hblinding := hblinding)
        haccepts).instanceCols := by
  let slot := fun proofIndex =>
    acceptedInstanceSlot
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hLayout
  let selected :
      Fin shape.numProofs → Fin shape.numInstanceQueries → CPoly :=
    fun proofIndex queryIndex =>
      coeffsToPoly
        ((memberDecode
          (slot proofIndex queryIndex).setIndex
          (slot proofIndex queryIndex).setIndex_lt).cols
          (slot proofIndex queryIndex).memberIndex)
  funext proofIndex query
  change
    rotatedFeed vk.omega vk.instanceQueryLayout
        (selected proofIndex) query =
      instanceQueryFeedOfResolver vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts)
        proofIndex query
  by_cases hquery : query < shape.numInstanceQueries
  · simp only [rotatedFeed, instanceQueryFeedOfResolver, resolverQueryFeed,
      dif_pos hquery]
    rw [show selected proofIndex ⟨query, hquery⟩ =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (batchOpenings := pbatch) (memberDecode := memberDecode) haccepts
          (CommitmentId.instanceCol proofIndex
            (vk.instanceQueryLayout.getD query (0, 0)).1) by
      exact acceptedInstanceSlot_polynomial
        (vk := vk) (instanceCommitment := instanceCommitment)
        (ps := ps) (ch := ch) (pbatch := pbatch)
        (proofIndex := proofIndex)
        urs hk memberDecode haccepts hLayout ⟨query, hquery⟩]
  · simp only [rotatedFeed, instanceQueryFeedOfResolver, resolverQueryFeed,
      dif_neg hquery]

assert_no_sorry acceptedInstanceSelection_feed_eq

end Instance

end Zcash.Snark

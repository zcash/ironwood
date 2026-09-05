import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Zcash.Snark.Verifier.QueryCommitment

/-!
# Routing decoded multiopen members into constraint polynomials

`OpenedMemberDecode` recovers one polynomial for every member of every deployed point set, while
the constraint layer names polynomials by `CommitmentId`.  This file is the small adapter between
those two views:

* `DeployedMemberSlot` is a valid `(point set, member)` position in the deployed grouping;
* `decodedPolynomialResolver` turns a partial `CommitmentId` routing into the total resolver used
  by `constraintModelOfResolver` (unrouted identifiers map to zero);
* `decodedPolynomialResolver_opens_or_relation` converts member-node binding and routing
  faithfulness into the uniform assembled-query opening fact, retaining the binding reduction's
  computed `NontrivialRelation` alternative;
* `eval_lookupEntriesOfDecodedResolver_or_relation` feeds that fact directly into the lookup
  instantiation layer.

The adapter is generic in the verification key and proof string. It does not select a concrete
Action circuit verification key or duplicate the straight-line AGM argument that produces
member-node binding.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

open CompPoly.CPolynomial

set_option maxHeartbeats 200000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
variable {shape : Shape} (instanceCommitment : Fin shape.numProofs → ℕ → G)

/-- A valid position in an abstract list of member lists.  Keeping this small dependent index
generic avoids unfolding the deployed verifier while elaborating the structure itself. -/
structure MemberSlot (setCount : ℕ) (memberCount : ℕ → ℕ) where
  setIndex : ℕ
  setIndex_lt : setIndex < setCount
  memberIndex : Fin (memberCount setIndex)

/-- A valid decoded member position in the deployed multiopen grouping. -/
abbrev DeployedMemberSlot [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :=
  MemberSlot
    (deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch)
    (fun i =>
      (deployedSetQueries (instanceCommitment := instanceCommitment) vk ps ch i).length)

/-- The polynomial decoded at a valid deployed member slot. -/
def decodedMemberPolynomial [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch) :
    CPoly :=
  coeffsToPoly
    ((memberDecode slot.setIndex slot.setIndex_lt).cols slot.memberIndex)

/-- Resolve a commitment identity to its decoded member polynomial.  The resolver is total because
the constraint model is total; identities outside the routed query block use the zero polynomial. -/
def decodedPolynomialResolver [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)) :
    CommitmentId → CPoly :=
  fun id =>
    match route id with
    | some slot =>
        decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot
    | none => 0

/-- The claimed value stored by the deployed grouping for a member at a point of its point set. -/
def deployedMemberClaim [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (point : Fp) : Fp :=
  ((deployedSetQueries (instanceCommitment := instanceCommitment) vk ps ch
      slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).2.getD
    (((constructIntermediateSets
      (assembleQueries vk instanceCommitment ps ch)).points.getD slot.setIndex []).idxOf point) 0

/-- Generic routing evidence for a claimed opening.  Like `MemberSlot`, this stays independent of
the deployed definitions so its projections elaborate without unfolding the verifier. -/
structure RoutedClaim {Slot Id Point Value : Type*}
    (route : Id → Option Slot) (id : Id) (point : Point) (value : Value)
    (pointMem : Slot → Point → Prop) (claim : Slot → Point → Value) where
  slot : Slot
  route_eq : route id = some slot
  point_mem : pointMem slot point
  claim_eq : claim slot point = value

/-- Routing evidence for one verifier query: its commitment ID selects a decoded member, its point
belongs to that member's point set, and the grouped claimed value there is the query's value. -/
abbrev DeployedQueryRoute [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (q : VerifierQuery shape.k Fp G) :=
  RoutedClaim route q.commId q.point q.eval
    (fun slot point =>
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex)
    (deployedMemberClaim (instanceCommitment := instanceCommitment) vk ps ch)

/-- Canonical partial routing from commitment identities to deployed member positions.  For an
identity present in the assembled query list, `List.find?` selects its first concrete query and
`constructIntermediateSets_comm_route` performs the verifier's deterministic grouping searches.
Absent identities remain unrouted.  No existential witness is projected into routing data. -/
def assembledQueryMemberRoute [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
  (hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false) :
    CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch) :=
  fun id =>
    let queries := assembleQueries vk instanceCommitment ps ch
    match hfind : queries.find? (fun q => decide (q.commId = id)) with
    | none => none
    | some q =>
        have hq : q ∈ queries := List.mem_of_find?_eq_some hfind
        have hqid : q.commId = id := by simpa using List.find?_some hfind
        let route := constructIntermediateSets_comm_route queries hq hqid
          (fun q hq q' hq' hid hpoint =>
            congrArg VerifierQuery.eval
              (eq_of_not_hasDuplicateCommitmentPoint hdup hq' hq hid hpoint))
          (fun q' hq' hid =>
            assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq hq'
              (hid.trans hqid.symm))
        some
          { setIndex := route.setIndex
            setIndex_lt := by rw [hcount]; exact route.setIndex_lt
            memberIndex := ⟨route.memberIndex, by
              simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
                route.memberIndex_lt⟩ }

/-- The canonical route is faithful for every assembled query: it selects the member carrying the
query's identity, point, and claimed evaluation. -/
def assembledQueryMemberRoute_faithful [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false)
    (q : VerifierQuery shape.k Fp G)
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch) :
    DeployedQueryRoute (instanceCommitment := instanceCommitment) vk ps ch
      (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
        vk ps ch hcount hdup) q := by
  let queries := assembleQueries vk instanceCommitment ps ch
  have hsome : (queries.find? (fun q' => decide (q'.commId = q.commId))).isSome := by
    rw [List.find?_isSome]
    exact ⟨q, hq, by simp⟩
  let q' := (queries.find? (fun q' => decide (q'.commId = q.commId))).get hsome
  have hfind : queries.find? (fun q' => decide (q'.commId = q.commId)) = some q' :=
    (Option.some_get hsome).symm
  have hq'mem : q' ∈ queries := List.mem_of_find?_eq_some hfind
  have hq'id : q'.commId = q.commId := by simpa using List.find?_some hfind
  let route := constructIntermediateSets_comm_route queries hq'mem hq'id
    (fun left hleft right hright hid hpoint =>
      congrArg VerifierQuery.eval
        (eq_of_not_hasDuplicateCommitmentPoint hdup hright hleft hid hpoint))
    (fun candidate hcandidate hid =>
      assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq'mem hcandidate
        (hid.trans hq'id.symm))
  let slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch :=
    { setIndex := route.setIndex
      setIndex_lt := by rw [hcount]; exact route.setIndex_lt
      memberIndex := ⟨route.memberIndex, by
        simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
          route.memberIndex_lt⟩ }
  have hall := route.all_queries q hq rfl
  refine
    { slot := slot
      route_eq := ?_
      point_mem := ?_
      claim_eq := ?_ }
  · have hfind' : (assembleQueries vk instanceCommitment ps ch).find?
        (fun candidate => decide (candidate.commId = q.commId)) = some q' := by
      simpa only [queries] using hfind
    dsimp only [assembledQueryMemberRoute]
    split
    · rename_i hnone
      rw [hnone] at hfind'
      contradiction
    · rename_i found hfound
      have hfoundEq : found = q' := Option.some.inj (hfound.symm.trans hfind')
      subst found
      rfl
  · rw [deployedSetPts, List.mem_toFinset]
    exact hall.1
  · simpa only [deployedMemberClaim, deployedSetQueries,
      constructIntermediateSets_zip_sets_getD] using hall.2 (.point 0, []) 0

omit [AddCommGroup G] [Module Fp G] in
/--
The member selected by the canonical route carries the routed commitment identity.
This exposes the positional identity fact retained by `MultiopenGrouped.ids`.
-/
theorem assembledQueryMemberRoute_id [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false)
    (id : CommitmentId)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (hroute :
      assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
        vk ps ch hcount hdup id = some slot) :
    (deployedSetCommIds (instanceCommitment := instanceCommitment)
      vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) .vanishingH = id := by
  dsimp only [assembledQueryMemberRoute] at hroute
  split at hroute
  · cases hroute
  · rename_i q hfind
    let queries := assembleQueries vk instanceCommitment ps ch
    have hq : q ∈ queries := List.mem_of_find?_eq_some hfind
    have hqid : q.commId = id := by simpa using List.find?_some hfind
    let route := constructIntermediateSets_comm_route queries hq hqid
      (fun left hleft right hright hid hpoint =>
        congrArg VerifierQuery.eval
          (eq_of_not_hasDuplicateCommitmentPoint hdup hright hleft hid hpoint))
      (fun candidate hcandidate hid =>
        assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq hcandidate
          (hid.trans hqid.symm))
    have hslot : slot =
        { setIndex := route.setIndex
          setIndex_lt := by rw [hcount]; exact route.setIndex_lt
          memberIndex := ⟨route.memberIndex, by
            simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
              route.memberIndex_lt⟩ } := Option.some.inj hroute |>.symm
    subst slot
    simpa only [deployedSetCommIds] using route.id_eq .vanishingH

omit [Module Fp G] in
/--
Any deployed member carrying an instance-column identity is the statement-derived commitment for
that proof and column.  This is the commitment-side companion of the canonical query route: the
grouping retains `CommitmentId` positionally, so no circuit-specific placement fact is needed.
-/
theorem deployedMemberRef_eq_instanceCommitment [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (p : Fin shape.numProofs) (column : ℕ)
    (hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) .vanishingH
        = .instanceCol p column) :
    ((deployedSetQueries (instanceCommitment := instanceCommitment)
      vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).1
      = .point (instanceCommitment p column) := by
  classical
  have hi :
      slot.setIndex <
        (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length := by
    rw [← hcount]
    exact slot.setIndex_lt
  have hm :
      (slot.memberIndex : ℕ) <
        ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.getD slot.setIndex []).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
      slot.memberIndex.isLt
  obtain ⟨q, hq, href, hqid⟩ :=
    constructIntermediateSets_member_provenance
      (assembleQueries vk instanceCommitment ps ch)
      slot.setIndex (slot.memberIndex : ℕ) hi hm (.point 0, []) .vanishingH
  have hqId : q.commId = .instanceCol p column := by
    exact hqid.symm.trans hid
  have hqCommitment :
      q.commitment = .point (instanceCommitment p column) :=
    assembleQueries_instance_commitment vk instanceCommitment ps ch q hq p column hqId
  simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using
    href.trans hqCommitment

omit [Module Fp G] in
/--
Any deployed member carrying a fixed-column identity is the corresponding
verifying-key commitment. This is the fixed-column counterpart of
`deployedMemberRef_eq_instanceCommitment`.
-/
theorem deployedMemberRef_eq_fixedCommitment [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (column : ℕ)
    (hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) .vanishingH
        = .fixedCol column) :
    ((deployedSetQueries (instanceCommitment := instanceCommitment)
      vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).1
      = .point (vk.fixedCommitment column) := by
  classical
  have hi :
      slot.setIndex <
        (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length := by
    rw [← hcount]
    exact slot.setIndex_lt
  have hm :
      (slot.memberIndex : ℕ) <
        ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.getD
            slot.setIndex []).length := by
    simpa only [deployedSetQueries,
      constructIntermediateSets_zip_sets_getD] using
      slot.memberIndex.isLt
  obtain ⟨q, hq, href, hqid⟩ :=
    constructIntermediateSets_member_provenance
      (assembleQueries vk instanceCommitment ps ch)
      slot.setIndex (slot.memberIndex : ℕ) hi hm
      (.point 0, []) .vanishingH
  have hqId : q.commId = .fixedCol column := by
    exact hqid.symm.trans hid
  have hqCommitment :
      q.commitment = .point (vk.fixedCommitment column) :=
    assembleQueries_fixed_commitment
      vk instanceCommitment ps ch q hq column hqId
  simpa only [deployedSetQueries,
    constructIntermediateSets_zip_sets_getD] using
    href.trans hqCommitment

omit [Module Fp G] in
/-- Any deployed member carrying a common-permutation identity is the corresponding
verifying-key σ-column commitment. This is the σ-column counterpart of
`deployedMemberRef_eq_fixedCommitment`. -/
theorem deployedMemberRef_eq_permCommonCommitment [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (c : Fin shape.numPermutationColumns)
    (hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) .vanishingH
        = .permCommon (c : ℕ)) :
    ((deployedSetQueries (instanceCommitment := instanceCommitment)
      vk ps ch slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).1
      = .point (vk.permutationCommonCommitment c) := by
  classical
  have hi :
      slot.setIndex <
        (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length := by
    rw [← hcount]
    exact slot.setIndex_lt
  have hm :
      (slot.memberIndex : ℕ) <
        ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.getD
            slot.setIndex []).length := by
    simpa only [deployedSetQueries,
      constructIntermediateSets_zip_sets_getD] using
      slot.memberIndex.isLt
  obtain ⟨q, hq, href, hqid⟩ :=
    constructIntermediateSets_member_provenance
      (assembleQueries vk instanceCommitment ps ch)
      slot.setIndex (slot.memberIndex : ℕ) hi hm
      (.point 0, []) .vanishingH
  have hqId : q.commId = .permCommon (c : ℕ) := by
    exact hqid.symm.trans hid
  have hqCommitment :
      q.commitment = .point (vk.permutationCommonCommitment c) :=
    assembleQueries_permCommon_commitment
      vk instanceCommitment ps ch q hq c hqId
  simpa only [deployedSetQueries,
    constructIntermediateSets_zip_sets_getD] using
    href.trans hqCommitment

omit [AddCommGroup G] [Module Fp G] in
/-- A successful rejecting assembly supplies exactly the two structural facts needed by the
canonical member route: duplicate commitment-point queries were rejected, and the `u` vector has
one entry per grouped point set, so the deployed pair count covers every group. -/
lemma assembledQueryRoutingConditions_of_assemble?_eq_some
    [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {m : Msm shape.k Fp G}
    (hm : assemble? vk instanceCommitment ps ch = some m) :
    deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
        = (constructIntermediateSets
            (assembleQueries vk instanceCommitment ps ch)).sets.length
      ∧ hasDuplicateCommitmentPoint
          (assembleQueries vk instanceCommitment ps ch) = false := by
  classical
  unfold assemble? at hm
  by_cases hwf : proofStringWellFormed ps = true
  · rw [if_pos hwf] at hm
    by_cases hxn : ch.x ^ vk.n = (1 : Fp)
    · rw [if_pos hxn] at hm
      exact absurd hm (by simp)
    · rw [if_neg hxn] at hm
      cases hcis : constructIntermediateSets?
          (assembleQueries vk instanceCommitment ps ch) with
      | none =>
          rw [hcis] at hm
          exact absurd hm (by simp)
      | some grouped =>
          rw [hcis] at hm
          simp only [] at hm
          by_cases hpts : multiopenPointsAvoidX3 ch.x3 grouped = true
          · rw [if_pos hpts] at hm
            have hgrouped := constructIntermediateSets?_eq_some hcis
            have hdup : hasDuplicateCommitmentPoint
                (assembleQueries vk instanceCommitment ps ch) = false := by
              unfold constructIntermediateSets? at hcis
              by_cases hd : hasDuplicateCommitmentPoint
                  (assembleQueries vk instanceCommitment ps ch) = true
              · rw [if_pos hd] at hcis
                exact absurd hcis (by simp)
              · exact Bool.eq_false_of_not_eq_true hd
            unfold assembleFinalMsm? at hm
            cases hopen : assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
                (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k Fp G) with
            | none =>
                rw [hopen] at hm
                exact absurd hm (by simp)
            | some opened =>
                unfold assembleOpening? at hopen
                by_cases hc : (List.ofFn ps.multiopenU).length = grouped.sets.length
                    ∧ grouped.points.length = grouped.sets.length
                · have hu := hc.1
                  subst grouped
                  refine ⟨?_, hdup⟩
                  simp [deployedX4PairCount, deployedX4Pairs, deployedX4Qs,
                    List.length_zip, constructIntermediateSets_points_length, hu]
                · rw [if_neg hc] at hopen
                  exact absurd hopen (by simp)
          · rw [if_neg hpts] at hm
            exact absurd hm (by simp)
  · rw [if_neg hwf] at hm
    exact absurd hm (by simp)

/-- If every routed member is node-bound, the decoded resolver opens every query in `queries`;
otherwise the existing augmented-basis relation branch is retained. -/
def decodedPolynomialResolver_opens_or_relation [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (queries : List (VerifierQuery shape.k Fp G))
    (hrouted : ∀ q ∈ queries,
      DeployedQueryRoute (instanceCommitment := instanceCommitment) vk ps ch route q)
    (hbind : ∀
      (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk ps ch slot.setIndex →
      (decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot).eval point
          = deployedMemberClaim (instanceCommitment := instanceCommitment)
              vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) :
    (∀ q ∈ queries,
      (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode route q.commId).eval q.point = q.eval)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  listForallOrRelationWitness queries fun q hq =>
    let hroute := hrouted q hq
    bindOrRelationWitness (hbind hroute.slot q.point hroute.point_mem) fun hb => by
      rw [decodedPolynomialResolver, hroute.route_eq]
      exact hb.trans hroute.claim_eq

/-- The decoded-member bridge specialized to the lookup instantiation: either all coherent lookup
entries evaluate to the proof's five claimed lookup values, or commitment binding has produced a
nontrivial augmented-basis relation. -/
def eval_lookupEntriesOfDecodedResolver_or_relation
    [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false)
    (hbind : ∀
      (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk ps ch slot.setIndex →
      (decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot).eval point
          = deployedMemberClaim (instanceCommitment := instanceCommitment)
              vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (p : Fin shape.numProofs) :
    (lookupEntriesOfResolver vk
        (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode
          (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
            vk ps ch hcount hdup)) p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
        = subProofLookups vk ps p
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  bindOrRelationWitness
    (decodedPolynomialResolver_opens_or_relation
      (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode
      (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
        vk ps ch hcount hdup)
      (assembleQueries vk instanceCommitment ps ch)
      (fun q hq => assembledQueryMemberRoute_faithful
        (instanceCommitment := instanceCommitment) vk ps ch hcount hdup q hq)
      hbind)
    fun hopen => eval_lookupEntriesOfResolver_of_assembleQueries
      vk instanceCommitment ps ch
      (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode
        (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
          vk ps ch hcount hdup)) p hopen

end Zcash.Snark

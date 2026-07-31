import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.AGM.DeployedRootDecode
import Zcash.Snark.Soundness.ConstraintRouting
import Zcash.Snark.Soundness.Composition.Quotient

/-!
# Constraint supply from rewind-free deployed AGM decoding

`DeployedAlgebraicDecode` supplies member polynomials directly from squeeze-pinned AGM coordinates,
together with their values at every routed node. This module connects that deterministic output to
the concrete Halo2 constraint layer.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial

universe u v w

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments


/-- Small proof bundle used to sequence the nine finite binding comparisons consumed by the
constraint adapter without collapsing any failed comparison to an existential proposition. -/
structure ConstraintAgreementBundle
    (A B C D E F G H I : Prop) : Prop where
  advice : A
  instanceCols : B
  fixed : C
  permutation : D
  common : E
  lookupProduct : F
  lookupInput : G
  lookupTable : H
  quotient : I

/-! ## The pre-IPA facts actually consumed by constraint routing -/

/-- Constraint routing does not consume the IPA verification equation.  It only needs the three
pre-IPA guards enforced before that equation is assembled: unique `(commitment, point)` queries,
one `multiopenU` value per grouped point set, and exclusion of an `n`th root of unity at `x`. -/
structure DeployedConstraintChecks [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop where
  noDuplicate : hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false
  uCount : (List.ofFn ps.multiopenU).length =
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length
  xnNeOne : ch.x ^ vk.n ≠ 1

/-- Actual deployed acceptance supplies the pre-IPA checks at the representation record.  The
round vector may differ because none of these checks reads `ipaRound`. -/
theorem DeployedConstraintChecks.of_accepts_chRecord [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (nu : Fin 11 -> Fp) (rounds : Fin shape.k -> Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps (chRecord nu rounds)) :
    DeployedConstraintChecks vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  obtain ⟨hdup, hu⟩ := deployedAccepts_pipeline urs hk vk instanceCommitment ps (chRecord nu rounds) hacc
  have hxn := deployedAccepts_xn_ne_one urs hk vk instanceCommitment ps (chRecord nu rounds) hacc
  refine ⟨?_, ?_, ?_⟩
  · change hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps (chRecord nu rounds)) = false
    exact hdup
  · change (List.ofFn ps.multiopenU).length =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps (chRecord nu rounds))).sets.length
    exact hu
  · change (chRecord nu rounds).x ^ vk.n ≠ 1
    exact hxn

omit [AddCommGroup G] [Module Fp G] in
/-- The pair count follows from the precise `multiopenU` guard, without the final IPA equation. -/
theorem deployedX4PairCount_eq_sets_length_of_checks [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    deployedX4PairCount vk instanceCommitment ps ch =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
  rw [deployedX4PairCount_eq, deployedX4Pairs, List.length_zip, deployedX4Qs]
  simp only [List.length_map, List.length_zip, checks.uCount,
    ← constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch), min_self]

/-- Computed deployed route for one commitment slot.  Both indices are the deterministic grouping
searches returned by `constructIntermediateSets_comm_route`; the remaining fields certify those
exact values against the deployed `getD` views. -/
structure DeployedSlotRoute [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (c : CommitmentId) (commitment : CommitmentRef shape.k Fp G) where
  setIndex : Nat
  setIndex_lt : setIndex < deployedX4PairCount vk instanceCommitment ps ch
  memberIndex : Fin (deployedSetQueries vk instanceCommitment ps ch setIndex).length
  id_eq : ∀ c0,
    (deployedSetCommIds vk instanceCommitment ps ch setIndex).getD (memberIndex : Nat) c0 = c
  commitment_eq : ∀ d0,
    ((deployedSetQueries vk instanceCommitment ps ch setIndex).getD
      (memberIndex : Nat) d0).1 = commitment
  all_queries : ∀ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = c →
    q.point ∈ deployedSetPts vk instanceCommitment ps ch setIndex ∧
    ((deployedSetQueries vk instanceCommitment ps ch setIndex).getD
      (memberIndex : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD
          setIndex []).idxOf q.point) 0 = q.eval

/-- Slot routing from the two grouping guards, with no dependence on the final IPA equation. -/
def deployed_slot_route_of_checks [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    {c : CommitmentId} {q0 : VerifierQuery shape.k Fp G}
    (hq0 : q0 ∈ assembleQueries vk instanceCommitment ps ch) (hq0c : q0.commId = c) :
    DeployedSlotRoute vk instanceCommitment ps ch c q0.commitment := by
  let route :=
    constructIntermediateSets_comm_route (assembleQueries vk instanceCommitment ps ch) hq0 hq0c
      (fun q hq q' hq' hid hpt =>
        congrArg VerifierQuery.eval
          (eq_of_not_hasDuplicateCommitmentPoint checks.noDuplicate hq' hq hid hpt))
      (fun q hq hid => assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq0 hq
        (hid.trans hq0c.symm))
  have hmlen : route.memberIndex <
      (deployedSetQueries vk instanceCommitment ps ch route.setIndex).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
      using route.memberIndex_lt
  refine
    { setIndex := route.setIndex
      setIndex_lt := ?_
      memberIndex := ⟨route.memberIndex, hmlen⟩
      id_eq := route.id_eq
      commitment_eq := ?_
      all_queries := ?_ }
  · rw [deployedX4PairCount_eq_sets_length_of_checks vk instanceCommitment ps ch checks]
    exact route.setIndex_lt
  · intro d0
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
      using route.commitment_eq d0
  · intro q hq hqc
    obtain ⟨hpt, hev⟩ := route.all_queries q hq hqc
    refine ⟨by rw [deployedSetPts, List.mem_toFinset]; exact hpt, ?_⟩
    have h := hev (.point 0, []) 0
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using h

omit [Module Fp G] in
/-- Proposition-valued wrapper for constraint-routing consumers. -/
theorem deployed_slot_routed_all_of_checks [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    {c : CommitmentId} {q0 : VerifierQuery shape.k Fp G}
    (hq0 : q0 ∈ assembleQueries vk instanceCommitment ps ch) (hq0c : q0.commId = c) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c) ∧
        (∀ d0, ((deployedSetQueries vk instanceCommitment ps ch i).getD
          (m : Nat) d0).1 = q0.commitment) ∧
        ∀ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = c →
          q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD
            (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD
                i []).idxOf q.point) 0 = q.eval := by
  let route := deployed_slot_route_of_checks vk instanceCommitment ps ch checks hq0 hq0c
  exact ⟨route.setIndex, route.setIndex_lt, route.memberIndex, route.id_eq,
    route.commitment_eq, route.all_queries⟩

/-- The canonical concrete query for a slot, point, and claimed evaluation. -/
def deployedCanonicalQuery [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (c : CommitmentId) (point eval : Fp) : VerifierQuery shape.k Fp G :=
  { point := point
    commitment := assembledCommitment vk instanceCommitment ps ch c
    eval := eval
    commId := c }

omit [AddCommGroup G] [Module Fp G] in
/-- An existential query specification proves membership of the corresponding canonical query;
the witness is consumed only in this proposition-valued proof, never to choose routing data. -/
theorem deployedCanonicalQuery_mem_of_spec [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (c : CommitmentId) (point eval : Fp)
    (hspec : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = c ∧ q.point = point ∧ q.eval = eval) :
    deployedCanonicalQuery vk instanceCommitment ps ch c point eval ∈
      assembleQueries vk instanceCommitment ps ch := by
  obtain ⟨q, hq, hqid, hpoint, heval⟩ := hspec
  have hcommit := assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq
  have hqeq : q = deployedCanonicalQuery vk instanceCommitment ps ch c point eval := by
    cases q
    simp_all [deployedCanonicalQuery]
  rwa [← hqeq]

/-- A family of computed deployed routes indexed by protocol slots. -/
structure DeployedRouteSelector [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (I : Type*) (target : I → CommitmentId) (point eval : I → Fp) where
  canonical_mem : ∀ i,
    deployedCanonicalQuery vk instanceCommitment ps ch (target i) (point i) (eval i) ∈
      assembleQueries vk instanceCommitment ps ch
  route : ∀ i, DeployedSlotRoute vk instanceCommitment ps ch (target i)
    (assembledCommitment vk instanceCommitment ps ch (target i))

/-- Build computed routes from proposition-valued query-presence proofs.  The returned indices are
determined by `target`, `point`, and `eval`; `hspec` only certifies membership. -/
def deployedRouteSelectorOfSpecs [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (I : Type*) (target : I → CommitmentId) (point eval : I → Fp)
    (hspec : ∀ i, ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = target i ∧ q.point = point i ∧ q.eval = eval i) :
    DeployedRouteSelector vk instanceCommitment ps ch I target point eval := by
  let hmem := fun i => deployedCanonicalQuery_mem_of_spec vk instanceCommitment ps ch
    (target i) (point i) (eval i) (hspec i)
  exact
    { canonical_mem := hmem
      route := fun i =>
        deployed_slot_route_of_checks vk instanceCommitment ps ch checks (hmem i) rfl }

/-- The polynomial represented by member `m` of deployed point set `i`. -/
def DeployedAlgebraicDecode.memberPoly [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) : CPoly :=
  coeffsToPoly ((decoded.batches.x1 i hi).coeffs m)

/-- The decoder's member polynomial takes the proof string's recorded value at every point routed
to its set — no rewind premise and no relation disjunction; both were discharged while
constructing `DeployedAlgebraicDecode`. -/
theorem DeployedAlgebraicDecode.memberPoly_eval_at_point [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
    {p : Fp} (hpt : p ∈ deployedSetPts vk instanceCommitment ps ch i) :
    (decoded.memberPoly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p) 0 := by
  have hmem : p ∈ (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] := by
    rw [deployedSetPts] at hpt
    exact List.mem_toFinset.mp hpt
  have hmem' : p ∈ ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1 := by
    rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hi]
    exact hmem
  have hlt : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p <
      ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length :=
    List.idxOf_lt_length_iff.mpr hmem'
  let idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length :=
    ⟨((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p, hlt⟩
  have hb := decoded.memberValues i hi idx m
  change (decoded.memberPoly i hi m).eval
      ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] = _ at hb
  have hidx : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] = p := by
    exact List.getElem_idxOf hlt
  have hidxOf : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p =
      ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p := by
    rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hi]
  rw [hidx] at hb
  change (decoded.memberPoly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p) 0 at hb
  rw [hidxOf] at hb
  exact hb

/-- The exact deterministic interface consumed by the constraint layer: one polynomial per routed
member and its value at every point in that member's set. -/
structure DeployedMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) where
  poly : forall i, i < deployedX4PairCount vk instanceCommitment ps ch ->
    Fin (deployedSetQueries vk instanceCommitment ps ch i).length -> CPoly
  eval_at_point : forall i (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) (p : Fp),
    p ∈ deployedSetPts vk instanceCommitment ps ch i ->
    (poly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p) 0

/-- Package the rewind-free AGM decode as the deterministic member-polynomial interface. -/
def DeployedAlgebraicDecode.toMemberPolynomials [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    DeployedMemberPolynomials vk instanceCommitment ps ch :=
  { poly := decoded.memberPoly
    eval_at_point := decoded.memberPoly_eval_at_point }

/-- The decoded aggregate directly opens the deployed IPA statement, using the actual `x4` power
batch rather than a family of accepting rewinds. -/
theorem DeployedAlgebraicDecode.ipaRelation [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    IpaRelation urs
      (deployedCommitment urs hk vk instanceCommitment ps ch - aggregateU • urs.u - aggregateW • urs.w)
      (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) aggregate := by
  let cols : AlgebraicColumnRepresentations urs (x4BatchCommitments urs hk vk instanceCommitment ps ch) :=
    { coeffs := decoded.batches.x4.coeffs
      uComp := decoded.batches.x4.uComp
      wComp := decoded.batches.x4.wComp
      commitment := decoded.batches.x4.commitment }
  have hc := cols.power_commitment ch.x4
  rw [<- decoded.batches.x4.reconstruct, <- decoded.batches.x4.reconstructU,
    <- decoded.batches.x4.reconstructW] at hc
  have hbatch := deployedCommitment_x4_batch urs hk vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  have hcommit : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch := hc.trans hbatch.symm
  refine ⟨?_, ?_⟩
  · rw [sub_sub, eq_sub_iff_add_eq]
    simpa [_root_.add_assoc] using hcommit
  · have hv : commitGen (evalVector urs.k ch.x3) aggregate =
        ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
          ch.x4 ^ (j : Nat) *
            commitGen (evalVector urs.k ch.x3) (decoded.batches.x4.coeffs j) := by
      calc
        commitGen (evalVector urs.k ch.x3) aggregate =
            commitGen (evalVector urs.k ch.x3)
              (∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
                ch.x4 ^ (j : Nat) • decoded.batches.x4.coeffs j) :=
          congrArg (commitGen (evalVector urs.k ch.x3)) decoded.batches.x4.reconstruct
        _ = _ := by
          rw [commitGen_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [commitGen_smul_left, smul_eq_mul]
    have hib : innerProduct aggregate (evalVector urs.k ch.x3) =
        commitGen (evalVector urs.k ch.x3) aggregate := by
      simp [innerProduct, commitGen, smul_eq_mul]
    rw [hib, hv]
    rw [Finset.sum_congr rfl (fun j _ => by rw [decoded.x4Values j])]
    have hvalues := multiopenValue_x4_batch vk instanceCommitment ps ch ch.x4
    rw [heta] at hvalues
    exact hvalues.symm

/-! ## The canonical pre-`x` constraint polynomial -/

/-- Advice feeds built from an arbitrary pre-`x` polynomial source for committed points. -/
def committedAdviceFeed [Inhabited G] {shape : Shape}
    (poly : G -> CPoly) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs -> Nat -> CPoly := fun q =>
  rotatedFeed vk.omega vk.adviceQueryLayout fun j : Fin shape.numAdviceQueries =>
    poly (finFnG (ps.adviceCommitments q)
      (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Instance feeds built from a pre-`x` polynomial source. -/
def committedInstanceFeed {shape : Shape} (poly : G -> CPoly)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) :
    Fin shape.numProofs -> Nat -> CPoly := fun q =>
  rotatedFeed vk.omega vk.instanceQueryLayout fun j : Fin shape.numInstanceQueries =>
    poly (instanceCommitment q (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Fixed-column feed built from a pre-`x` polynomial source. -/
def committedFixedFeed {shape : Shape} (poly : G -> CPoly)
    (vk : VerifyingKey shape Fp G) : Nat -> CPoly :=
  rotatedFeed vk.omega vk.fixedQueryLayout fun j : Fin shape.numFixedQueries =>
    poly (vk.fixedCommitment (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Permutation-product carriers built from a pre-`x` polynomial source.

The final set's `else` branch is dead: halo2 reads a last-rotation evaluation only for the sets
before the final one, so its `lastEval` is `none`. -/
def committedPermSets {shape : Shape} (poly : G -> CPoly)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs -> List (PermSetEval (CPoly)) := fun q =>
  List.ofFn fun s : Fin shape.numPermutationSets =>
    let z := poly (ps.permutationProduct q s)
    PermSetEval.mk z
      (comp z (C (vk.omega ^ (1 : Int)) * X))
      ((ps.permutationSetEvals q s).lastEval.map fun le =>
        if (s : Nat) + 1 < shape.numPermutationSets then
          comp z (C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * X)
        else C le)

/-- Common permutation columns built from a pre-`x` polynomial source. -/
def committedPermCommonFeed [Inhabited G] {shape : Shape}
    (poly : G -> CPoly) (vk : VerifyingKey shape Fp G) : Nat -> CPoly := fun c =>
  if h : c < shape.numPermutationColumns then poly (vk.permutationCommonCommitment ⟨c, h⟩)
  else 0

/-- Permutation chunks built from a pre-`x` polynomial source. -/
def committedPermChunks [Inhabited G] {shape : Shape}
    (poly : G -> CPoly) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs ->
      List (PermSetEval (CPoly) × List (CPoly × CPoly)) := fun q =>
  ((committedPermSets poly vk ps q).zip vk.permutationChunks).map fun sc =>
    (sc.1, sc.2.map fun cr =>
      ((match cr.1 with
        | .advice i => committedAdviceFeed poly vk ps q i
        | .fixed i => committedFixedFeed poly vk i
        | .instance i => committedInstanceFeed poly vk instanceCommitment q i),
       committedPermCommonFeed poly vk cr.2))

/-- Lookup carriers built from a pre-`x` polynomial source. -/
def committedLookups {shape : Shape} (poly : G -> CPoly)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs ->
      List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)) := fun q =>
  List.ofFn fun l : Fin shape.numLookups =>
    let product := poly (ps.lookupProduct q l)
    let input := poly (ps.lookupPermutedInput q l)
    let table := poly (ps.lookupPermutedTable q l)
    (LookupEval.mk product
      (comp product (C (vk.omega ^ (1 : Int)) * X)) input
      (comp input (C (vk.omega ^ (-1 : Int)) * X)) table,
     vk.lookupInputExprs l, vk.lookupTableExprs l)

/-- Pre-`x` quotient assembled from explicit represented quotient-piece polynomials. -/
def committedPreXQuotient {shape : Shape} (vk : VerifyingKey shape Fp G)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly) : CPoly :=
  preXQuotient vk.n piecePoly

omit [AddCommGroup G] [Module Fp G] in
theorem committedPreXQuotient_eq {shape : Shape} (vk : VerifyingKey shape Fp G)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly) :
    committedPreXQuotient vk piecePoly = preXQuotient vk.n piecePoly := rfl

/-- Executable sum of the Lagrange selectors for blinded rows. -/
def committedBlindSelector {shape : Shape} (vk : VerifyingKey shape Fp G) : CPoly :=
  ((List.range vk.blindingFactors).map
    (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : Int) + 1)))).sum

omit [AddCommGroup G] [Module Fp G] in
theorem committedBlindSelector_eq {shape : Shape} (vk : VerifyingKey shape Fp G) :
    committedBlindSelector vk =
      ((List.range vk.blindingFactors).map
        (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : Int) + 1)))).foldl (· + ·) 0 := by
  rw [committedBlindSelector]
  symm
  exact List.sum_eq_foldl.symm

/-- The pre-`x` constraint difference built entirely from explicit online AGM coordinates. -/
def committedPreXConstraintDifference [Inhabited G] {shape : Shape}
    (poly : G -> CPoly)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : CPoly :=
  (combineConstraints (committedFixedFeed poly vk) (committedAdviceFeed poly vk ps)
      (committedInstanceFeed poly vk instanceCommitment) vk.gates (committedPermSets poly vk ps)
      (committedPermChunks poly vk instanceCommitment ps) (committedLookups poly vk ps)
      ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
      (lagrangeBasisPoly vk.omega vk.n 0)
      (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
      (committedBlindSelector vk))
    - committedPreXQuotient vk piecePoly * (X ^ vk.n - 1)

omit [AddCommGroup G] [Module Fp G] in
theorem committedPreXConstraintDifference_eq [Inhabited G] {shape : Shape}
    (poly : G -> CPoly)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch =
      combineConstraints (committedFixedFeed poly vk) (committedAdviceFeed poly vk ps)
        (committedInstanceFeed poly vk instanceCommitment) vk.gates (committedPermSets poly vk ps)
        (committedPermChunks poly vk instanceCommitment ps) (committedLookups poly vk ps)
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
        (lagrangeBasisPoly vk.omega vk.n 0)
        (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
        (((List.range vk.blindingFactors).map
          (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : Int) + 1)))).foldl (· + ·) 0)
      - committedPreXQuotient vk piecePoly * (X ^ vk.n - 1) := by
  rw [committedPreXConstraintDifference, committedBlindSelector_eq]

/-- Computed comparison between the decoded vanishing member and a pre-`x` quotient assembled
from explicit online quotient-piece coordinates. -/
def DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness
    [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hcommit : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) d₀).1 =
      .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))) :
    ((decoded.memberPoly i hi m).eval ch.x =
        (preXQuotient vk.n piecePoly).eval ch.x) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hopen := (decoded.batches.x1 i hi).commitment m
  rw [deployedSetMemberCommitments_apply, hcommit (.point 0, [])] at hopen
  have hvanishing :
      (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)).eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ =
        ∑ j : Fin shape.numQuotientPieces,
          (ch.x ^ vk.n) ^ (j : Nat) • ps.hPieces j := by
    calc
      _ = ∑ j ∈ Finset.range (List.ofFn ps.hPieces).length,
          (ch.x ^ vk.n) ^ j • (List.ofFn ps.hPieces).getD j 0 :=
        vanishingHCommitment_eval (⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ : URS G)
          (ch.x ^ vk.n) (List.ofFn ps.hPieces)
      _ = _ := by
        rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt),
          List.getElem_ofFn]
  have hopen' :
      commit urs ((decoded.batches.x1 i hi).coeffs m) +
          (decoded.batches.x1 i hi).uComp m • urs.u +
          (decoded.batches.x1 i hi).wComp m • urs.w =
        ∑ j : Fin shape.numQuotientPieces,
          (ch.x ^ vk.n) ^ (j : Nat) • ps.hPieces j := by
    rw [hopen]
    exact hvanishing
  exact match decodedQuotientEqReassembledOrRelationWitness urs (ch.x ^ vk.n)
      hpieceOpen hopen' with
    | PSum.inr relation => PSum.inr relation
    | PSum.inl hdecoded => PSum.inl (by
        change (coeffsToPoly ((decoded.batches.x1 i hi).coeffs m)).eval ch.x = _
        rw [hdecoded]
        have hp : (fun j => coeffsToPoly (pieceCoeffs j)) = piecePoly := funext hpiecePoly
        rw [hp, reassembledQuotient_eval_eq_preXQuotient_eval])

/-! ## Routed feeds from a deterministic member source -/

/-- Computed carrier selection for one rotated query feed. -/
structure DeployedRotatedFeedBinding [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (Q : Type*) (numQueries : Nat) (layout : List (Nat × Int))
    (target : Q → Fin numQueries → CommitmentId) (claims : Q → Nat → Fp) where
  setIndex : Q → Fin numQueries → Nat
  setIndex_lt : ∀ q j, setIndex q j < deployedX4PairCount vk instanceCommitment ps ch
  memberIndex : ∀ q j,
    Fin (deployedSetQueries vk instanceCommitment ps ch (setIndex q j)).length
  id_eq : ∀ q j,
    (deployedSetCommIds vk instanceCommitment ps ch (setIndex q j)).getD
      (memberIndex q j : Nat) CommitmentId.vanishingH = target q j
  bind : ∀ q n,
    (rotatedFeed vk.omega layout
      (fun j => src.poly (setIndex q j) (setIndex_lt q j) (memberIndex q j)) n).eval ch.x =
      claims q n

/-- Build a rotated feed from computed grouped routes.  Query existence is used only to certify the
canonical query; all set/member indices are returned by the deterministic route search. -/
def deployedRotatedFeedBindingOfSpecs [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (Q : Type*) (numQueries : Nat) (layout : List (Nat × Int))
    (target : Q → Fin numQueries → CommitmentId) (claims : Q → Nat → Fp)
    (hclaimsZero : ∀ q n, numQueries ≤ n → claims q n = 0)
    (hspec : ∀ q j, ∃ query ∈ assembleQueries vk instanceCommitment ps ch,
      query.commId = target q j ∧
      query.point = rotateOmega vk.omega ch.x (layout.getD (j : Nat) (0, 0)).2 ∧
      query.eval = claims q (j : Nat)) :
    DeployedRotatedFeedBinding vk instanceCommitment ps ch src Q numQueries layout
      target claims := by
  let I := Q × Fin numQueries
  let targetI : I → CommitmentId := fun qj => target qj.1 qj.2
  let pointI : I → Fp := fun qj =>
    rotateOmega vk.omega ch.x (layout.getD (qj.2 : Nat) (0, 0)).2
  let evalI : I → Fp := fun qj => claims qj.1 (qj.2 : Nat)
  let selector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    targetI pointI evalI (fun qj => hspec qj.1 qj.2)
  refine
    { setIndex := fun q j => (selector.route (q, j)).setIndex
      setIndex_lt := fun q j => (selector.route (q, j)).setIndex_lt
      memberIndex := fun q j => (selector.route (q, j)).memberIndex
      id_eq := fun q j => (selector.route (q, j)).id_eq CommitmentId.vanishingH
      bind := ?_ }
  intro q n
  by_cases h : n < numQueries
  · let j : Fin numQueries := ⟨n, h⟩
    let route := selector.route (q, j)
    have hall := route.all_queries
      (deployedCanonicalQuery vk instanceCommitment ps ch
        (target q j) (pointI (q, j)) (evalI (q, j)))
      (selector.canonical_mem (q, j)) rfl
    rw [rotatedFeed_eval vk.omega layout _ h ch.x]
    rw [src.eval_at_point route.setIndex route.setIndex_lt route.memberIndex
      (pointI (q, j)) hall.1]
    exact hall.2
  · rw [rotatedFeed_eval_of_ge vk.omega layout _ (Nat.not_lt.mp h) ch.x]
    rw [hclaimsZero q n (Nat.not_lt.mp h)]

/-- Computed advice-column carrier selection. -/
def adviceFeedBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length) :
    DeployedRotatedFeedBinding vk instanceCommitment ps ch src
      (Fin shape.numProofs) shape.numAdviceQueries vk.adviceQueryLayout
      (fun q j => CommitmentId.adviceCol q
        (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1)
      (fun q => finFn (ps.adviceEvals q)) :=
  deployedRotatedFeedBindingOfSpecs vk instanceCommitment ps ch src checks
    (Fin shape.numProofs) shape.numAdviceQueries vk.adviceQueryLayout
    (fun q j => CommitmentId.adviceCol q
      (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1)
    (fun q => finFn (ps.adviceEvals q))
    (fun _ n hn => by simp [finFn, hn])
    (fun q j => advice_query_mem_assembleQueries_eval vk instanceCommitment ps ch q
      (lt_of_lt_of_le j.isLt hAdvLen) j.isLt)

/-- Computed instance-column carrier selection. -/
def instanceFeedBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length) :
    DeployedRotatedFeedBinding vk instanceCommitment ps ch src
      (Fin shape.numProofs) shape.numInstanceQueries vk.instanceQueryLayout
      (fun q j => CommitmentId.instanceCol q
        (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1)
      (fun q => finFn (ps.instanceEvals q)) :=
  deployedRotatedFeedBindingOfSpecs vk instanceCommitment ps ch src checks
    (Fin shape.numProofs) shape.numInstanceQueries vk.instanceQueryLayout
    (fun q j => CommitmentId.instanceCol q
      (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1)
    (fun q => finFn (ps.instanceEvals q))
    (fun _ n hn => by simp [finFn, hn])
    (fun q j => instance_query_mem_assembleQueries_eval vk instanceCommitment ps ch q
      (lt_of_lt_of_le j.isLt hInstLen) j.isLt)

/-- Computed fixed-column carrier selection. -/
def fixedFeedBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length) :
    DeployedRotatedFeedBinding vk instanceCommitment ps ch src
      Unit shape.numFixedQueries vk.fixedQueryLayout
      (fun _ j => CommitmentId.fixedCol
        (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1)
      (fun _ => finFn ps.fixedEvals) :=
  deployedRotatedFeedBindingOfSpecs vk instanceCommitment ps ch src checks
    Unit shape.numFixedQueries vk.fixedQueryLayout
    (fun _ j => CommitmentId.fixedCol
      (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1)
    (fun _ => finFn ps.fixedEvals)
    (fun _ n hn => by simp [finFn, hn])
    (fun _ j => fixed_query_mem_assembleQueries vk instanceCommitment ps ch
      (lt_of_lt_of_le j.isLt hFixedLen) j.isLt)

open Classical in
/-- Permutation-set carriers from rewind-free member polynomials. -/
structure DeployedPermSetsBinding [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch) where
  setIndex : Fin shape.numProofs → Fin shape.numPermutationSets → Nat
  setIndex_lt : ∀ q s, setIndex q s < deployedX4PairCount vk instanceCommitment ps ch
  memberIndex : ∀ q s,
    Fin (deployedSetQueries vk instanceCommitment ps ch (setIndex q s)).length
  id_eq : ∀ q s,
    (deployedSetCommIds vk instanceCommitment ps ch (setIndex q s)).getD
      (memberIndex q s : Nat) CommitmentId.vanishingH = CommitmentId.permProduct q s
  bind : ∀ q : Fin shape.numProofs,
    (List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
      (src.poly (setIndex q s) (setIndex_lt q s) (memberIndex q s))
      ((src.poly (setIndex q s) (setIndex_lt q s) (memberIndex q s)).comp (C (vk.omega ^ (1 : Int)) * X))
      ((ps.permutationSetEvals q s).lastEval.map (fun le =>
        if (s : Nat) + 1 < shape.numPermutationSets then
          (src.poly (setIndex q s) (setIndex_lt q s) (memberIndex q s)).comp (C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * X)
        else C le)))).map (PermSetEval.map (fun r => r.eval ch.x)) =
      subProofPermSets ps q

/-- Computed permutation-product carrier selection and binding. -/
def permSetsBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    DeployedPermSetsBinding vk instanceCommitment ps ch src := by
  let I := Fin shape.numProofs × Fin shape.numPermutationSets
  let target : I → CommitmentId := fun qs => CommitmentId.permProduct qs.1 qs.2
  let point : I → Fp := fun _ => ch.x
  let value : I → Fp := fun qs => (ps.permutationSetEvals qs.1 qs.2).eval
  let selector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    target point value (fun qs => perm_product_query_mem_assembleQueries
      vk instanceCommitment ps ch qs.1 qs.2)
  refine
    { setIndex := fun q s => (selector.route (q, s)).setIndex
      setIndex_lt := fun q s => (selector.route (q, s)).setIndex_lt
      memberIndex := fun q s => (selector.route (q, s)).memberIndex
      id_eq := fun q s => (selector.route (q, s)).id_eq CommitmentId.vanishingH
      bind := ?_ }
  intro q
  rw [List.map_ofFn, subProofPermSets]
  refine congrArg List.ofFn (funext fun s => ?_)
  let route := selector.route (q, s)
  set zdec := src.poly route.setIndex route.setIndex_lt route.memberIndex with hz
  have hbindAt : ∀ p, p ∈ deployedSetPts vk instanceCommitment ps ch route.setIndex →
      zdec.eval p =
        ((deployedSetQueries vk instanceCommitment ps ch route.setIndex).getD
          (route.memberIndex : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD
          route.setIndex []).idxOf p) 0 := by
    intro p hp
    exact src.eval_at_point route.setIndex route.setIndex_lt route.memberIndex p hp
  obtain ⟨qx, hqx, hqxid, hqxpt, hqxev⟩ :=
    perm_product_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptx, hevx⟩ := route.all_queries qx hqx hqxid
  have hbx : zdec.eval ch.x = (ps.permutationSetEvals q s).eval := by
    have hb := hbindAt qx.point hptx
    rw [hqxpt] at hb hevx
    rw [hb, hevx, hqxev]
  obtain ⟨qn, hqn, hqnid, hqnpt, hqnev⟩ :=
    perm_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptn, hevn⟩ := route.all_queries qn hqn hqnid
  have hbn : zdec.eval (rotateOmega vk.omega ch.x 1) =
      (ps.permutationSetEvals q s).nextEval := by
    have hb := hbindAt qn.point hptn
    rw [hqnpt] at hb hevn
    rw [hb, hevn, hqnev]
  have heta : ps.permutationSetEvals q s =
      PermSetEval.mk (ps.permutationSetEvals q s).eval
        (ps.permutationSetEvals q s).nextEval (ps.permutationSetEvals q s).lastEval := rfl
  rw [Function.comp_apply, heta]
  simp only [PermSetEval.map, PermSetEval.mk.injEq]
  refine ⟨hbx, ?_, ?_⟩
  · rw [eval_comp_rotate, ← hbn, rotateOmega, _root_.mul_comm]
  · rcases hle : (ps.permutationSetEvals q s).lastEval with _ | le
    · rfl
    · rw [Option.map_map]
      by_cases hlast : (s : Nat) + 1 < shape.numPermutationSets
      · obtain ⟨ql, hql, hqlid, hqlpt, hqlev⟩ :=
          perm_product_last_query_mem_assembleQueries vk instanceCommitment ps ch q s hlast hle
        obtain ⟨hptl, hevl⟩ := route.all_queries ql hql hqlid
        have hbl : zdec.eval
            (rotateOmega vk.omega ch.x (-((vk.blindingFactors : Int) + 1))) = le := by
          have hb := hbindAt ql.point hptl
          rw [hqlpt] at hb hevl
          rw [hb, hevl, hqlev]
        simp only [Option.map_some, Function.comp_apply, if_pos hlast]
        rw [eval_comp_rotate, ← hbl, rotateOmega, _root_.mul_comm]
      · simp only [Option.map_some, Function.comp_apply, if_neg hlast, eval_C]

open Classical in
/-- Lookup carriers from rewind-free member polynomials. -/
structure DeployedLookupsBinding [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch) where
  productSet : Fin shape.numProofs → Fin shape.numLookups → Nat
  inputSet : Fin shape.numProofs → Fin shape.numLookups → Nat
  tableSet : Fin shape.numProofs → Fin shape.numLookups → Nat
  productSet_lt : ∀ q l, productSet q l < deployedX4PairCount vk instanceCommitment ps ch
  inputSet_lt : ∀ q l, inputSet q l < deployedX4PairCount vk instanceCommitment ps ch
  tableSet_lt : ∀ q l, tableSet q l < deployedX4PairCount vk instanceCommitment ps ch
  productMember : ∀ q l,
    Fin (deployedSetQueries vk instanceCommitment ps ch (productSet q l)).length
  inputMember : ∀ q l,
    Fin (deployedSetQueries vk instanceCommitment ps ch (inputSet q l)).length
  tableMember : ∀ q l,
    Fin (deployedSetQueries vk instanceCommitment ps ch (tableSet q l)).length
  id_eq : ∀ q l,
    (deployedSetCommIds vk instanceCommitment ps ch (productSet q l)).getD
        (productMember q l : Nat) CommitmentId.vanishingH = CommitmentId.lookupProduct q l ∧
    (deployedSetCommIds vk instanceCommitment ps ch (inputSet q l)).getD
        (inputMember q l : Nat) CommitmentId.vanishingH = CommitmentId.lookupPermInput q l ∧
    (deployedSetCommIds vk instanceCommitment ps ch (tableSet q l)).getD
        (tableMember q l : Nat) CommitmentId.vanishingH = CommitmentId.lookupPermTable q l
  bind : ∀ q : Fin shape.numProofs,
    (List.ofFn (fun l : Fin shape.numLookups =>
      (LookupEval.mk
        (src.poly (productSet q l) (productSet_lt q l) (productMember q l))
        ((src.poly (productSet q l) (productSet_lt q l) (productMember q l)).comp
          (C (vk.omega ^ (1 : Int)) * X))
        (src.poly (inputSet q l) (inputSet_lt q l) (inputMember q l))
        ((src.poly (inputSet q l) (inputSet_lt q l) (inputMember q l)).comp
          (C (vk.omega ^ (-1 : Int)) * X))
        (src.poly (tableSet q l) (tableSet_lt q l) (tableMember q l)),
      vk.lookupInputExprs l, vk.lookupTableExprs l))).map
        (fun lk => (lk.1.map (fun r => r.eval ch.x), lk.2.1, lk.2.2)) =
      subProofLookups vk ps q

/-- Computed lookup carrier selection and binding. -/
def lookupsBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    DeployedLookupsBinding vk instanceCommitment ps ch src := by
  classical
  let I := Fin shape.numProofs × Fin shape.numLookups
  let point : I → Fp := fun _ => ch.x
  let productTarget : I → CommitmentId := fun ql => CommitmentId.lookupProduct ql.1 ql.2
  let productValue : I → Fp := fun ql => (ps.lookupEvals ql.1 ql.2).productEval
  let inputTarget : I → CommitmentId := fun ql => CommitmentId.lookupPermInput ql.1 ql.2
  let inputValue : I → Fp := fun ql => (ps.lookupEvals ql.1 ql.2).permutedInputEval
  let tableTarget : I → CommitmentId := fun ql => CommitmentId.lookupPermTable ql.1 ql.2
  let tableValue : I → Fp := fun ql => (ps.lookupEvals ql.1 ql.2).permutedTableEval
  let productSelector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    productTarget point productValue (fun ql => lookup_product_query_mem_assembleQueries
      vk instanceCommitment ps ch ql.1 ql.2)
  let inputSelector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    inputTarget point inputValue (fun ql => lookup_permInput_query_mem_assembleQueries
      vk instanceCommitment ps ch ql.1 ql.2)
  let tableSelector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    tableTarget point tableValue (fun ql => lookup_permTable_query_mem_assembleQueries
      vk instanceCommitment ps ch ql.1 ql.2)
  refine
    { productSet := fun q l => (productSelector.route (q, l)).setIndex
      inputSet := fun q l => (inputSelector.route (q, l)).setIndex
      tableSet := fun q l => (tableSelector.route (q, l)).setIndex
      productSet_lt := fun q l => (productSelector.route (q, l)).setIndex_lt
      inputSet_lt := fun q l => (inputSelector.route (q, l)).setIndex_lt
      tableSet_lt := fun q l => (tableSelector.route (q, l)).setIndex_lt
      productMember := fun q l => (productSelector.route (q, l)).memberIndex
      inputMember := fun q l => (inputSelector.route (q, l)).memberIndex
      tableMember := fun q l => (tableSelector.route (q, l)).memberIndex
      id_eq := fun q l =>
        ⟨(productSelector.route (q, l)).id_eq CommitmentId.vanishingH,
          (inputSelector.route (q, l)).id_eq CommitmentId.vanishingH,
          (tableSelector.route (q, l)).id_eq CommitmentId.vanishingH⟩
      bind := ?_ }
  intro q
  rw [List.map_ofFn, subProofLookups]
  refine congrArg List.ofFn (funext fun l => ?_)
  rw [Function.comp_apply]
  let productRoute := productSelector.route (q, l)
  let inputRoute := inputSelector.route (q, l)
  let tableRoute := tableSelector.route (q, l)
  obtain ⟨q1, hq1, hq1id, hq1pt, hq1ev⟩ :=
    lookup_product_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt1, hev1⟩ := productRoute.all_queries q1 hq1 hq1id
  have hb1 : (src.poly productRoute.setIndex productRoute.setIndex_lt
      productRoute.memberIndex).eval ch.x = (ps.lookupEvals q l).productEval := by
    have hb := src.eval_at_point productRoute.setIndex productRoute.setIndex_lt
      productRoute.memberIndex q1.point hpt1
    rw [hq1pt] at hb hev1
    rw [hb, hev1, hq1ev]
  obtain ⟨q2, hq2, hq2id, hq2pt, hq2ev⟩ :=
    lookup_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt2, hev2⟩ := productRoute.all_queries q2 hq2 hq2id
  have hb2 : (src.poly productRoute.setIndex productRoute.setIndex_lt
      productRoute.memberIndex).eval (rotateOmega vk.omega ch.x 1) =
      (ps.lookupEvals q l).productNextEval := by
    have hb := src.eval_at_point productRoute.setIndex productRoute.setIndex_lt
      productRoute.memberIndex q2.point hpt2
    rw [hq2pt] at hb hev2
    rw [hb, hev2, hq2ev]
  obtain ⟨q3, hq3, hq3id, hq3pt, hq3ev⟩ :=
    lookup_permInput_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt3, hev3⟩ := inputRoute.all_queries q3 hq3 hq3id
  have hb3 : (src.poly inputRoute.setIndex inputRoute.setIndex_lt
      inputRoute.memberIndex).eval ch.x = (ps.lookupEvals q l).permutedInputEval := by
    have hb := src.eval_at_point inputRoute.setIndex inputRoute.setIndex_lt
      inputRoute.memberIndex q3.point hpt3
    rw [hq3pt] at hb hev3
    rw [hb, hev3, hq3ev]
  obtain ⟨q4, hq4, hq4id, hq4pt, hq4ev⟩ :=
    lookup_permInput_inv_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt4, hev4⟩ := inputRoute.all_queries q4 hq4 hq4id
  have hb4 : (src.poly inputRoute.setIndex inputRoute.setIndex_lt
      inputRoute.memberIndex).eval (rotateOmega vk.omega ch.x (-1)) =
      (ps.lookupEvals q l).permutedInputInvEval := by
    have hb := src.eval_at_point inputRoute.setIndex inputRoute.setIndex_lt
      inputRoute.memberIndex q4.point hpt4
    rw [hq4pt] at hb hev4
    rw [hb, hev4, hq4ev]
  obtain ⟨q5, hq5, hq5id, hq5pt, hq5ev⟩ :=
    lookup_permTable_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt5, hev5⟩ := tableRoute.all_queries q5 hq5 hq5id
  have hb5 : (src.poly tableRoute.setIndex tableRoute.setIndex_lt
      tableRoute.memberIndex).eval ch.x = (ps.lookupEvals q l).permutedTableEval := by
    have hb := src.eval_at_point tableRoute.setIndex tableRoute.setIndex_lt
      tableRoute.memberIndex q5.point hpt5
    rw [hq5pt] at hb hev5
    rw [hb, hev5, hq5ev]
  have heta : ps.lookupEvals q l =
      LookupEval.mk (ps.lookupEvals q l).productEval (ps.lookupEvals q l).productNextEval
        (ps.lookupEvals q l).permutedInputEval (ps.lookupEvals q l).permutedInputInvEval
        (ps.lookupEvals q l).permutedTableEval := rfl
  refine congrArg (fun z => (z, vk.lookupInputExprs l, vk.lookupTableExprs l)) ?_
  rw [heta]
  simp only [LookupEval.map, LookupEval.mk.injEq]
  refine ⟨hb1, ?_, hb3, ?_, hb5⟩
  · rw [eval_comp_rotate, ← hb2, rotateOmega, _root_.mul_comm]
  · rw [eval_comp_rotate, ← hb4, rotateOmega, _root_.mul_comm]

open Classical in
/-- Permutation-common feed binding from rewind-free member polynomials. -/
structure DeployedPermCommonBinding [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch) where
  setIndex : Fin shape.numPermutationColumns → Nat
  setIndex_lt : ∀ c, setIndex c < deployedX4PairCount vk instanceCommitment ps ch
  memberIndex : ∀ c,
    Fin (deployedSetQueries vk instanceCommitment ps ch (setIndex c)).length
  id_eq : ∀ c,
    (deployedSetCommIds vk instanceCommitment ps ch (setIndex c)).getD
      (memberIndex c : Nat) CommitmentId.vanishingH = CommitmentId.permCommon c
  bind : ∀ n : Nat, (if h : n < shape.numPermutationColumns then
    src.poly (setIndex ⟨n, h⟩) (setIndex_lt ⟨n, h⟩) (memberIndex ⟨n, h⟩)
    else 0).eval ch.x = finFn ps.permutationCommonEvals n

/-- Computed permutation-common carrier selection. -/
def permCommonBindingOfMemberPolynomials [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    DeployedPermCommonBinding vk instanceCommitment ps ch src := by
  classical
  let I := Fin shape.numPermutationColumns
  let target : I → CommitmentId := fun c => CommitmentId.permCommon c
  let point : I → Fp := fun _ => ch.x
  let value : I → Fp := fun c => ps.permutationCommonEvals c
  let selector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks I
    target point value (fun c => permCommon_query_mem_assembleQueries
      vk instanceCommitment ps ch c)
  refine
    { setIndex := fun c => (selector.route c).setIndex
      setIndex_lt := fun c => (selector.route c).setIndex_lt
      memberIndex := fun c => (selector.route c).memberIndex
      id_eq := fun c => (selector.route c).id_eq CommitmentId.vanishingH
      bind := ?_ }
  intro n
  by_cases h : n < shape.numPermutationColumns
  · let c : Fin shape.numPermutationColumns := ⟨n, h⟩
    let route := selector.route c
    have hall := route.all_queries
      (deployedCanonicalQuery vk instanceCommitment ps ch
        (target c) (point c) (value c)) (selector.canonical_mem c) rfl
    rw [dif_pos h, finFn, dif_pos h]
    rw [src.eval_at_point route.setIndex route.setIndex_lt route.memberIndex ch.x hall.1]
    exact hall.2
  · rw [dif_neg h, finFn, dif_neg h, eval_zero]

/-! ## Complete deterministic constraint supply -/

/-- The successful constraint-side output for one decoded run. It retains the concrete carrier
polynomials used by `circuitSatViaConstraints`, so the left branch carries the verifier's compressed
full-list identity while the right branch remains an explicit relation witness. The identity is
not yet row-level semantic satisfaction: that promotion also needs the `y`, `beta`, `gamma`, and
`theta` good-challenge conditions priced by the semantic capstone. -/
structure DeployedConstraintWitness [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW : Fp) where
  fixedF : Nat -> CPoly
  adviceF : Fin shape.numProofs -> Nat -> CPoly
  instanceF : Fin shape.numProofs -> Nat -> CPoly
  setsC : Fin shape.numProofs -> List (PermSetEval (CPoly))
  chunksC : Fin shape.numProofs ->
    List (PermSetEval (CPoly) × List (CPoly × CPoly))
  lookupsC : Fin shape.numProofs ->
    List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp))
  l0P : CPoly
  lLastP : CPoly
  lBlindP : CPoly
  hpolyP : CPoly
  /-- The concrete algebraic decode from which all carrier polynomials were routed. -/
  decode : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
    aggregate aggregateU aggregateW
  /-- Canonical polynomial assigned to each plain commitment. -/
  commitmentPolynomial : G → CPoly
  quotientPieces : Fin shape.numQuotientPieces → CPoly
  member_plain : ∀ {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G},
    ((deployedSetQueries vk instanceCommitment ps ch i).getD
      (m : Nat) (.point 0, [])).1 = CommitmentRef.point P →
      decode.memberPoly i hi m = commitmentPolynomial P
  fixed_canonical : fixedF = committedFixedFeed commitmentPolynomial vk
  advice_canonical : adviceF = committedAdviceFeed commitmentPolynomial vk ps
  instance_canonical : instanceF =
    committedInstanceFeed commitmentPolynomial vk instanceCommitment
  sets_canonical : setsC = committedPermSets commitmentPolynomial vk ps
  chunks_canonical : chunksC =
    committedPermChunks commitmentPolynomial vk instanceCommitment ps
  lookups_canonical : lookupsC = committedLookups commitmentPolynomial vk ps
  quotient_canonical : hpolyP = committedPreXQuotient vk quotientPieces
  relation : SnarkRelation urs
    (deployedCommitment urs hk vk instanceCommitment ps ch - aggregateU • urs.u - aggregateW • urs.w)
    (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
    (circuitSatViaConstraints fixedF (fun _ => adviceF) (fun _ => instanceF) vk.gates
      setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
      l0P lLastP lBlindP hpolyP vk.n) aggregate

open CompPoly.CPolynomial in
omit [AddCommGroup G] [Module Fp G] in
/-- Relation-free specialization used by the computed AGM adapter once member-value decoding has
already supplied the exact routed equality. -/
theorem hfold_of_constraint_polys_of_xn_ne_direct
    {shape : Shape} (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (fixedCols : Nat -> CPoly)
    (adviceCols instanceCols : Fin shape.numProofs -> Nat -> CPoly)
    (sets : Fin shape.numProofs -> List (PermSetEval (CPoly)))
    (chunks : Fin shape.numProofs ->
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin shape.numProofs ->
      List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (l0 lLast lBlind hpoly : CPoly)
    (hvanishing : hpoly.eval ch.x = expectedHEval
      (allExpressions vk ps ch
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
      ch.y (ch.x ^ vk.n))
    (hxn : ch.x ^ vk.n ≠ 1)
    (hfixed : forall j, (fixedCols j).eval ch.x = finFn ps.fixedEvals j)
    (hadvice : forall p j, (adviceCols p j).eval ch.x = finFn (ps.adviceEvals p) j)
    (hinstance : forall p j, (instanceCols p j).eval ch.x = finFn (ps.instanceEvals p) j)
    (hsets : forall p,
      (sets p).map (PermSetEval.map (fun q => q.eval ch.x)) = subProofPermSets ps p)
    (hchunks : forall p,
      (chunks p).map (fun c => (c.1.map (fun q => q.eval ch.x),
        c.2.map (fun q => (q.1.eval ch.x, q.2.eval ch.x)))) = subProofPermChunks vk ps p)
    (hlookups : forall p,
      (lookups p).map (fun lk =>
        (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2)) = subProofLookups vk ps p)
    (hl0 : l0.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1)
    (hlLast : lLast.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1)
    (hlBlind : lBlind.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) :
    (combineConstraints fixedCols adviceCols instanceCols vk.gates sets chunks lookups
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0 lLast lBlind).eval ch.x =
      hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
  have hfp := eval_combineConstraints_deployed vk ps ch fixedCols adviceCols instanceCols
    sets chunks lookups l0 lLast lBlind hfixed hadvice hinstance hsets hchunks hlookups
    hl0 hlLast hlBlind
  rw [eval_combineConstraints] at hfp ⊢
  exact hfold_of_expectedHEval_binding _ ch.y ch.x hpoly vk.n _ hxn hvanishing hfp

open CompPoly.CPolynomial in
open Classical in
/-- Constraint-witness adapter produced directly from `DeployedAlgebraicDecode`, with no opened
or joint-acceptance premises.  The relation branch is the computable quotient comparison of
`deployedConstraintQuotientFinder`.  The polynomial success branch is finite executable arithmetic
over `Fp`, so the complete outcome remains computed data. -/
def deployedConstraintOutcomeOfDecode
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (poly : G -> CPoly)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    (hplain : forall {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G},
      ((deployedSetQueries vk instanceCommitment ps ch i).getD
        (m : Nat) (.point 0, [])).1 = CommitmentRef.point P ->
      decoded.memberPoly i hi m = poly P)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length)
    (homega : vk.omega ^ vk.n = 1) (hn : (vk.n : Fp) ≠ 0)
    (hxgood : ch.x ∉ szBadSet
      (committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch)) :
    DeployedConstraintWitness urs hk vk instanceCommitment ps ch
        aggregate aggregateU aggregateW ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let src := decoded.toMemberPolynomials
  let adviceBinding := adviceFeedBindingOfMemberPolynomials
    vk instanceCommitment ps ch src checks hAdvLen
  let aSet := adviceBinding.setIndex
  let haSet := adviceBinding.setIndex_lt
  let aMem := adviceBinding.memberIndex
  have haLayout := adviceBinding.id_eq
  have haBind := adviceBinding.bind
  let instanceBinding := instanceFeedBindingOfMemberPolynomials
    vk instanceCommitment ps ch src checks hInstLen
  let iSet := instanceBinding.setIndex
  let hiSet := instanceBinding.setIndex_lt
  let iMem := instanceBinding.memberIndex
  have hiLayout := instanceBinding.id_eq
  have hiBind := instanceBinding.bind
  let fixedBinding := fixedFeedBindingOfMemberPolynomials
    vk instanceCommitment ps ch src checks hFixedLen
  let fSet : Fin shape.numFixedQueries → Nat := fun j => fixedBinding.setIndex () j
  let hfSet : ∀ j, fSet j < deployedX4PairCount vk instanceCommitment ps ch :=
    fun j => fixedBinding.setIndex_lt () j
  let fMem : ∀ j, Fin (deployedSetQueries vk instanceCommitment ps ch (fSet j)).length :=
    fun j => fixedBinding.memberIndex () j
  have hfLayout : ∀ j,
      (deployedSetCommIds vk instanceCommitment ps ch (fSet j)).getD
        (fMem j : Nat) CommitmentId.vanishingH =
          CommitmentId.fixedCol (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1 :=
    fun j => fixedBinding.id_eq () j
  have hfBind : ∀ n,
      (rotatedFeed vk.omega vk.fixedQueryLayout
        (fun j => src.poly (fSet j) (hfSet j) (fMem j)) n).eval ch.x = finFn ps.fixedEvals n :=
    fixedBinding.bind ()
  let permBinding := permSetsBindingOfMemberPolynomials vk instanceCommitment ps ch src checks
  let pSet := permBinding.setIndex
  let hpSet := permBinding.setIndex_lt
  let pMem := permBinding.memberIndex
  have hpLayout := permBinding.id_eq
  have hpBind := permBinding.bind
  let commonBinding := permCommonBindingOfMemberPolynomials vk instanceCommitment ps ch src checks
  let cSet := commonBinding.setIndex
  let hcSet := commonBinding.setIndex_lt
  let cMem := commonBinding.memberIndex
  have hcLayout := commonBinding.id_eq
  have hcommonF := commonBinding.bind
  let lookupBinding := lookupsBindingOfMemberPolynomials vk instanceCommitment ps ch src checks
  let lpSel := lookupBinding.productSet
  let liSel := lookupBinding.inputSet
  let ltSel := lookupBinding.tableSet
  let hlpSel := lookupBinding.productSet_lt
  let hliSel := lookupBinding.inputSet_lt
  let hltSel := lookupBinding.tableSet_lt
  let lpMem := lookupBinding.productMember
  let liMem := lookupBinding.inputMember
  let ltMem := lookupBinding.tableMember
  have hlLayout := lookupBinding.id_eq
  have hlBind := lookupBinding.bind
  let vanishingValue := expectedHEval
    (allExpressions vk ps ch
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
    ch.y (ch.x ^ vk.n)
  let vanishingSelector := deployedRouteSelectorOfSpecs vk instanceCommitment ps ch checks Unit
    (fun _ => CommitmentId.vanishingH) (fun _ => ch.x) (fun _ => vanishingValue)
    (fun _ => vanishing_query_mem_assembleQueries vk instanceCommitment ps ch)
  let vanishingRoute := vanishingSelector.route ()
  let iV := vanishingRoute.setIndex
  have hiV := vanishingRoute.setIndex_lt
  let mV : Nat := vanishingRoute.memberIndex
  have hmV : mV < (deployedSetQueries vk instanceCommitment ps ch iV).length :=
    vanishingRoute.memberIndex.isLt
  have hcommitV : ∀ d₀,
      ((deployedSetQueries vk instanceCommitment ps ch iV).getD mV d₀).1 = .msm
        (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)) := by
    intro d₀
    change ((deployedSetQueries vk instanceCommitment ps ch vanishingRoute.setIndex).getD
      (vanishingRoute.memberIndex : Nat) d₀).1 = _
    have h := vanishingRoute.commitment_eq d₀
    change ((deployedSetQueries vk instanceCommitment ps ch vanishingRoute.setIndex).getD
      (vanishingRoute.memberIndex : Nat) d₀).1 = .msm
        (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)) at h
    exact h
  have hvanishingRoute := vanishingRoute.all_queries
    (deployedCanonicalQuery vk instanceCommitment ps ch CommitmentId.vanishingH
      ch.x vanishingValue) (vanishingSelector.canonical_mem ()) rfl
  set adviceF : Fin shape.numProofs -> Nat -> CPoly := fun q =>
    rotatedFeed vk.omega vk.adviceQueryLayout
      (fun j : Fin shape.numAdviceQueries => src.poly (aSet q j) (haSet q j) (aMem q j))
    with hadviceF
  set instanceF : Fin shape.numProofs -> Nat -> CPoly := fun q =>
    rotatedFeed vk.omega vk.instanceQueryLayout
      (fun j : Fin shape.numInstanceQueries => src.poly (iSet q j) (hiSet q j) (iMem q j))
    with hinstanceF
  set fixedF : Nat -> CPoly :=
    rotatedFeed vk.omega vk.fixedQueryLayout
      (fun j : Fin shape.numFixedQueries => src.poly (fSet j) (hfSet j) (fMem j))
    with hfixedF
  set commonF : Nat -> CPoly := fun n =>
    if h : n < shape.numPermutationColumns then
      src.poly (cSet ⟨n, h⟩) (hcSet ⟨n, h⟩) (cMem ⟨n, h⟩)
    else 0 with hcommonDef
  set setsC : Fin shape.numProofs -> List (PermSetEval (CPoly)) := fun q =>
    List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
      (src.poly (pSet q s) (hpSet q s) (pMem q s))
      (comp (src.poly (pSet q s) (hpSet q s) (pMem q s)) (C (vk.omega ^ (1 : Int)) * X))
      ((ps.permutationSetEvals q s).lastEval.map (fun le =>
        if (s : Nat) + 1 < shape.numPermutationSets then
          comp (src.poly (pSet q s) (hpSet q s) (pMem q s))
            (C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * X)
        else C le))) with hsetsC
  set chunksC : Fin shape.numProofs ->
      List (PermSetEval (CPoly) × List (CPoly × CPoly)) := fun q =>
    ((setsC q).zip vk.permutationChunks).map (fun sc => (sc.1, sc.2.map (fun cr =>
      ((match cr.1 with
        | .advice i => adviceF q i
        | .fixed i => fixedF i
        | .instance i => instanceF q i), commonF cr.2)))) with hchunksC
  set lookupsC : Fin shape.numProofs ->
      List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)) := fun q =>
    List.ofFn (fun l : Fin shape.numLookups =>
      (LookupEval.mk
        (src.poly (lpSel q l) (hlpSel q l) (lpMem q l))
        (comp (src.poly (lpSel q l) (hlpSel q l) (lpMem q l)) (C (vk.omega ^ (1 : Int)) * X))
        (src.poly (liSel q l) (hliSel q l) (liMem q l))
        (comp (src.poly (liSel q l) (hliSel q l) (liMem q l)) (C (vk.omega ^ (-1 : Int)) * X))
        (src.poly (ltSel q l) (hltSel q l) (ltMem q l)),
      vk.lookupInputExprs l, vk.lookupTableExprs l)) with hlookupsC
  let decodedHP := src.poly iV hiV ⟨mV, hmV⟩
  let hpolyP := committedPreXQuotient vk piecePoly
  have hplainRouted : forall {i : Nat}
      (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
      {c : CommitmentId} {P : G} (c0 : CommitmentId)
      (hid : (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c)
      (hresolve : assembledCommitment vk instanceCommitment ps ch c = CommitmentRef.point P),
      src.poly i hi m = poly P := by
    intro i hi m c P c0 hid hresolve
    apply hplain hi m
    exact (deployed_member_commitment_eq_assembled vk instanceCommitment ps ch i m c0 hid _).trans
      hresolve
  have hadviceBase : forall (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
      src.poly (aSet q j) (haSet q j) (aMem q j) =
        poly (finFnG (ps.adviceCommitments q)
          (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro q j
    exact hplainRouted (haSet q j) (aMem q j) CommitmentId.vanishingH
      (haLayout q j) (by simp [assembledCommitment, q.isLt])
  have hinstanceBase : forall (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
      src.poly (iSet q j) (hiSet q j) (iMem q j) =
        poly (instanceCommitment q
          (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro q j
    exact hplainRouted (hiSet q j) (iMem q j) CommitmentId.vanishingH
      (hiLayout q j) (by simp [assembledCommitment, q.isLt])
  have hfixedBase : forall j : Fin shape.numFixedQueries,
      src.poly (fSet j) (hfSet j) (fMem j) =
        poly (vk.fixedCommitment (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro j
    exact hplainRouted (hfSet j) (fMem j) CommitmentId.vanishingH
      (hfLayout j) (by rfl)
  have hpermBase : forall (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
      src.poly (pSet q s) (hpSet q s) (pMem q s) = poly (ps.permutationProduct q s) := by
    intro q s
    exact hplainRouted (hpSet q s) (pMem q s) CommitmentId.vanishingH
      (hpLayout q s) (by simp [assembledCommitment, q.isLt, finFnG, s.isLt])
  have hcommonBase : forall c : Fin shape.numPermutationColumns,
      src.poly (cSet c) (hcSet c) (cMem c) = poly (vk.permutationCommonCommitment c) := by
    intro c
    exact hplainRouted (hcSet c) (cMem c) CommitmentId.vanishingH
      (hcLayout c) (by simp [assembledCommitment, finFnG, c.isLt])
  have hlookupProductBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (lpSel q l) (hlpSel q l) (lpMem q l) = poly (ps.lookupProduct q l) := by
    intro q l
    exact hplainRouted (hlpSel q l) (lpMem q l) CommitmentId.vanishingH
      (hlLayout q l).1 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  have hlookupInputBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (liSel q l) (hliSel q l) (liMem q l) = poly (ps.lookupPermutedInput q l) := by
    intro q l
    exact hplainRouted (hliSel q l) (liMem q l) CommitmentId.vanishingH
      (hlLayout q l).2.1 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  have hlookupTableBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (ltSel q l) (hltSel q l) (ltMem q l) = poly (ps.lookupPermutedTable q l) := by
    intro q l
    exact hplainRouted (hltSel q l) (ltMem q l) CommitmentId.vanishingH
      (hlLayout q l).2.2 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  let hquotientOutcome := decoded.quotientEvalEqCommittedPreXOrRelationWitness
    pieceCoeffs pieceU pieceW piecePoly hpieceOpen hpiecePoly hiV ⟨mV, hmV⟩ hcommitV
  refine bindOrRelationWitness hquotientOutcome ?_
  intro hquotEval
  obtain ⟨hl0, hlLast, hlBlind⟩ :=
    lagrange_bind_derived vk.omega vk.n vk.blindingFactors ch.x homega hn checks.xnNeOne
  have hlBlind' : (committedBlindSelector vk).eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2 := by
    rw [committedBlindSelector_eq]
    exact hlBlind
  have hpBind' : ∀ q,
      (setsC q).map (PermSetEval.map (fun r => r.eval ch.x)) = subProofPermSets ps q := by
    intro q
    rw [hsetsC]
    exact hpBind q
  have hlBind' : ∀ q,
      (lookupsC q).map (fun lk =>
        (lk.1.map (fun r => r.eval ch.x), lk.2.1, lk.2.2)) = subProofLookups vk ps q := by
    intro q
    rw [hlookupsC]
    exact hlBind q
  have hcommonF' : ∀ n, (commonF n).eval ch.x = finFn ps.permutationCommonEvals n := by
    intro n
    rw [hcommonDef]
    exact hcommonF n
  have hadviceCanonical : adviceF = committedAdviceFeed poly vk ps := by
    funext q
    change rotatedFeed vk.omega vk.adviceQueryLayout
        (fun j => src.poly (aSet q j) (haSet q j) (aMem q j)) =
      rotatedFeed vk.omega vk.adviceQueryLayout
        (fun j : Fin shape.numAdviceQueries =>
        poly (finFnG (ps.adviceCommitments q)
          (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.adviceQueryLayout)
      (funext fun j => hadviceBase q j)
  have hinstanceCanonical : instanceF = committedInstanceFeed poly vk instanceCommitment := by
    funext q
    change rotatedFeed vk.omega vk.instanceQueryLayout
        (fun j => src.poly (iSet q j) (hiSet q j) (iMem q j)) =
      rotatedFeed vk.omega vk.instanceQueryLayout
        (fun j : Fin shape.numInstanceQueries =>
        poly (instanceCommitment q
          (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.instanceQueryLayout)
      (funext fun j => hinstanceBase q j)
  have hfixedCanonical : fixedF = committedFixedFeed poly vk := by
    change rotatedFeed vk.omega vk.fixedQueryLayout
        (fun j => src.poly (fSet j) (hfSet j) (fMem j)) =
      rotatedFeed vk.omega vk.fixedQueryLayout
        (fun j : Fin shape.numFixedQueries =>
        poly (vk.fixedCommitment
          (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.fixedQueryLayout) (funext hfixedBase)
  have hcommonCanonical : commonF = committedPermCommonFeed poly vk := by
    funext n
    change (if h : n < shape.numPermutationColumns then
      src.poly (cSet ⟨n, h⟩) (hcSet ⟨n, h⟩) (cMem ⟨n, h⟩)
      else 0) = _
    by_cases h : n < shape.numPermutationColumns
    · rw [dif_pos h, committedPermCommonFeed, dif_pos h, hcommonBase]
    · rw [dif_neg h, committedPermCommonFeed, dif_neg h]
  have hsetsCanonical : setsC = committedPermSets poly vk ps := by
    funext q
    rw [hsetsC, committedPermSets]
    apply congrArg List.ofFn
    funext s
    rw [hpermBase q s]
  have hlookupsCanonical : lookupsC = committedLookups poly vk ps := by
    funext q
    rw [hlookupsC, committedLookups]
    apply congrArg List.ofFn
    funext l
    rw [hlookupProductBase q l, hlookupInputBase q l, hlookupTableBase q l]
  have hchunksCanonical : chunksC = committedPermChunks poly vk instanceCommitment ps := by
    funext q
    rw [hchunksC, committedPermChunks, hsetsCanonical, hadviceCanonical, hfixedCanonical,
      hinstanceCanonical, hcommonCanonical]
  have hconstraintDiff :
      combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
          ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          (lagrangeBasisPoly vk.omega vk.n 0)
          (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
          (committedBlindSelector vk) -
        hpolyP * (X ^ vk.n - 1) =
          committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch := by
    rw [hadviceCanonical, hinstanceCanonical, hfixedCanonical, hsetsCanonical,
      hchunksCanonical, hlookupsCanonical]
    rw [committedBlindSelector_eq]
    exact (committedPreXConstraintDifference_eq poly piecePoly vk instanceCommitment ps ch).symm
  have hxgood' : ch.x ∉ szBadSet
      (combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
          ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          (lagrangeBasisPoly vk.omega vk.n 0)
          (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
          (committedBlindSelector vk) -
        hpolyP * (X ^ vk.n - 1)) := by
    rw [hconstraintDiff]
    exact hxgood
  have hquotEval' : decodedHP.eval ch.x = hpolyP.eval ch.x := by
    change (decoded.memberPoly iV hiV ⟨mV, hmV⟩).eval ch.x =
      (committedPreXQuotient vk piecePoly).eval ch.x
    rw [committedPreXQuotient_eq]
    exact hquotEval
  have hdecodedExpected : decodedHP.eval ch.x = vanishingValue := by
    have hb := src.eval_at_point iV hiV ⟨mV, hmV⟩ ch.x hvanishingRoute.1
    exact hb.trans hvanishingRoute.2
  have hvanishing : hpolyP.eval ch.x = expectedHEval
      (allExpressions vk ps ch
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
      ch.y (ch.x ^ vk.n) := by
    rw [← hquotEval']
    exact hdecodedExpected
  have hfold := hfold_of_constraint_polys_of_xn_ne_direct vk ps ch
    fixedF adviceF instanceF setsC chunksC lookupsC _ _ (committedBlindSelector vk)
    hpolyP hvanishing checks.xnNeOne
    hfBind haBind hiBind hpBind'
    (fun q => permChunks_bind_of_feeds vk ps ch q (setsC q) (hpBind' q) fixedF (adviceF q)
      (instanceF q) commonF hfBind (haBind q) (hiBind q) hcommonF')
    hlBind' hl0 hlLast hlBlind'
  have hfold' :
      (combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
        (lagrangeBasisPoly vk.omega vk.n 0)
        (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
        (committedBlindSelector vk)).eval ch.x =
          hpolyP.eval ch.x * (ch.x ^ vk.n - 1) := by
    exact hfold
  exact
    { fixedF := fixedF
      adviceF := adviceF
      instanceF := instanceF
      setsC := setsC
      chunksC := chunksC
      lookupsC := lookupsC
      l0P := lagrangeBasisPoly vk.omega vk.n 0
      lLastP := lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1))
      lBlindP := committedBlindSelector vk
      hpolyP := hpolyP
      decode := decoded
      commitmentPolynomial := poly
      quotientPieces := piecePoly
      member_plain := hplain
      fixed_canonical := hfixedCanonical
      advice_canonical := hadviceCanonical
      instance_canonical := hinstanceCanonical
      sets_canonical := hsetsCanonical
      chunks_canonical := hchunksCanonical
      lookups_canonical := hlookupsCanonical
      quotient_canonical := rfl
      relation := ⟨decoded.ipaRelation,
        circuitSatViaConstraints_of_check fixedF (fun _ => adviceF) (fun _ => instanceF)
          vk.gates setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          _ _ _ hpolyP vk.n aggregate ch.x hfold'
          (hgood_of_good_challenge _ hpolyP vk.n hxgood')⟩ }

/-- Compatibility theorem for callers that only require logical existence of the direct outcome.
The active composition consumes `deployedConstraintOutcomeOfDecode` itself so relation
coefficients remain data. -/
theorem constraints_supply_of_deployedAlgebraicDecode
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (poly : G -> CPoly)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> CPoly)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    (hplain : forall {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G},
      ((deployedSetQueries vk instanceCommitment ps ch i).getD
        (m : Nat) (.point 0, [])).1 = CommitmentRef.point P ->
      decoded.memberPoly i hi m = poly P)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length)
    (homega : vk.omega ^ vk.n = 1) (hn : (vk.n : Fp) ≠ 0)
    (hxgood : ch.x ∉ szBadSet
      (committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch)) :
    Nonempty (DeployedConstraintWitness urs hk vk instanceCommitment ps ch
        aggregate aggregateU aggregateW ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) := by
  exact ⟨deployedConstraintOutcomeOfDecode urs hk vk instanceCommitment ps ch decoded
      poly pieceCoeffs pieceU pieceW piecePoly hpieceOpen hpiecePoly hplain checks
      hAdvLen hInstLen hFixedLen homega hn hxgood⟩

end Zcash.Snark

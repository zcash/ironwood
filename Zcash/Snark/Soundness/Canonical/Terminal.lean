import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.Constraint.VanishingSlotFold

/-!
# Canonical decoded-model constraint terminal

The deployed quotient capstone works with separate fixed, advice, instance,
permutation, lookup, and row-selector polynomial families. The circuit integration
boundary instead consumes the single model canonically routed from an accepting
query assembly.

This module joins those verifier-native views. It contains no Clean or Action
concepts.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Successful deployed acceptance supplies the proof string's permutation
last-evaluation read schedule.
-/
theorem permutationLastEvalsWellFormed_of_deployedAccepts
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    permutationLastEvalsWellFormed ps = true := by
  unfold DeployedAccepts at haccepts
  cases hassemble :
      assemble? vk instanceCommitment ps ch with
  | none =>
      rw [hassemble] at haccepts
      exact False.elim haccepts
  | some msm =>
      exact permutationLastEvalsWellFormed_of_assemble?_eq_some
        vk instanceCommitment ps ch hassemble

/--
The canonical decoded model evaluates at the quotient challenge to exactly the
claims carried by the accepted proof string.

This is the compact input expected from decoded-member node binding. It replaces
the terminal's older collection of independently chosen decoder functions.
-/
structure AcceptedModelClaimedEvaluations
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch) : Prop where
  fixed : ∀ column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).fixedCols column).eval ch.x =
        finFn ps.fixedEvals column
  advice : ∀ proofIndex column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).adviceCols
        proofIndex column).eval ch.x =
      finFn (ps.adviceEvals proofIndex) column
  «instance» : ∀ proofIndex column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).instanceCols
        proofIndex column).eval ch.x =
      finFn (ps.instanceEvals proofIndex) column
  sets : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).sets proofIndex).map
        (PermSetEval.map fun polynomial => polynomial.eval ch.x) =
      subProofPermSets ps proofIndex
  chunks : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).chunks proofIndex).map
        (fun chunk =>
          (chunk.1.map fun polynomial => polynomial.eval ch.x,
            chunk.2.map fun pair =>
              (pair.1.eval ch.x, pair.2.eval ch.x))) =
      subProofPermChunks vk ps proofIndex
  lookups : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lookups proofIndex).map
        (fun lookup =>
          (lookup.1.map fun polynomial => polynomial.eval ch.x,
            lookup.2.1, lookup.2.2)) =
      subProofLookups vk ps proofIndex
  l0 :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).l0.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).1
  lLast :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lLast.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).2.1
  lBlind :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lBlind.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).2.2

namespace AcceptedModelClaimedEvaluations

/--
Construct the complete canonical fingerprint from uniform assembled-query
openings, the three query-layout counts, and the standard permutation/domain
facts.

The fixed, advice, and instance feed equations are all reconstructed from the
same opening family; they are not independent terminal premises.
-/
def ofOpenings
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hfixedLayout :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hadviceLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hinstanceLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (hopen : ∀ query ∈
      assembleQueries vk instanceCommitment ps ch,
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts query.commId).eval
          query.point = query.eval)
    (hpermutationWellFormed :
      permutationLastEvalsWellFormed ps = true)
    (hpermutationRouting :
      PermutationChunkRoutingCoherent vk)
    (hrows : Function.Injective
      fun row : Fin vk.n => vk.omega ^ (row : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxDomain : ch.x ^ vk.n ≠ 1) :
    AcceptedModelClaimedEvaluations
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts := by
  let polynomial :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  let selectors :=
    canonicalLagrangePolynomials vk.omega hblinding
  have hselectorEvaluations :=
    VerifyingKey.constraintModel_selectorEvaluations
      (numProofs := shape.numProofs)
      vk ch polynomial hblinding hrows hroot hnFp hxDomain
  refine
    { fixed := ?_
      advice := ?_
      «instance» := ?_
      sets := ?_
      chunks := ?_
      lookups := ?_
      l0 := ?_
      lLast := ?_
      lBlind := ?_ }
  · intro query
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, fixedQueryFeedOfResolver, polynomial] using
      resolverQueryFeed_eval_of_columnQueries
        (k := shape.k)
        vk.omega ch.x vk.fixedCommitment CommitmentId.fixedCol
        vk.fixedQueryLayout ps.fixedEvals hfixedLayout polynomial
        (fun q hq => hopen q (by
          simp only [assembleQueries]
          exact List.mem_append_left _
            (List.mem_append_left _
              (List.mem_append_right _ hq))))
        query
  · intro proofIndex query
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, adviceQueryFeedOfResolver, polynomial] using
      resolverQueryFeed_eval_of_columnQueries
        (k := shape.k)
        vk.omega ch.x (finFnG (ps.adviceCommitments proofIndex))
        (CommitmentId.adviceCol proofIndex)
        vk.adviceQueryLayout (ps.adviceEvals proofIndex)
        hadviceLayout polynomial
        (fun q hq => hopen q (by
          simp only [assembleQueries]
          refine List.mem_append.mpr
            (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl ?_)))))
          refine List.mem_flatten.mpr
            ⟨_, List.mem_ofFn.mpr ⟨proofIndex, rfl⟩, ?_⟩
          exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inr hq))))) ))
        query
  · intro proofIndex query
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, instanceQueryFeedOfResolver, polynomial] using
      resolverQueryFeed_eval_of_columnQueries
        (k := shape.k)
        vk.omega ch.x (instanceCommitment proofIndex)
        (CommitmentId.instanceCol proofIndex)
        vk.instanceQueryLayout (ps.instanceEvals proofIndex)
        hinstanceLayout polynomial
        (fun q hq => hopen q (by
          simp only [assembleQueries]
          refine List.mem_append.mpr
            (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl ?_)))))
          refine List.mem_flatten.mpr
            ⟨_, List.mem_ofFn.mpr ⟨proofIndex, rfl⟩, ?_⟩
          exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl hq))))) ))
        query
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, polynomial, selectors] using
      eval_permutationSetsOfResolver
        vk instanceCommitment ps ch polynomial
        hpermutationWellFormed proofIndex hopen
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, polynomial, selectors] using
      eval_permutationChunksOfResolver
        vk instanceCommitment ps ch polynomial
        hpermutationWellFormed hpermutationRouting proofIndex hopen
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver, polynomial, selectors] using
      eval_lookupEntriesOfResolver_of_assembleQueries
        vk instanceCommitment ps ch polynomial proofIndex hopen
  · exact congrArg Prod.fst hselectorEvaluations
  · exact congrArg (fun values => values.2.1) hselectorEvaluations
  · exact congrArg (fun values => values.2.2) hselectorEvaluations

/--
Construct the canonical claimed-evaluation fingerprint directly from decoded
member-node binding, retaining the augmented-basis relation when binding fails.

Compared with `ofOpenings`, this is the protocol-facing entry point: acceptance
chooses the route, and node binding supplies all assembled openings.
-/
def ofNodeBinding_or_relation
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hfixedLayout :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hadviceLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hinstanceLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := instanceCommitment)
          vk ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := instanceCommitment)
            vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (hpermutationWellFormed :
      permutationLastEvalsWellFormed ps = true)
    (hpermutationRouting :
      PermutationChunkRoutingCoherent vk)
    (hrows : Function.Injective
      fun row : Fin vk.n => vk.omega ^ (row : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxDomain : ch.x ^ vk.n ≠ 1) :
    AcceptedModelClaimedEvaluations
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  bindOrRelationWitness
    (CanonicalMemberConstraintRelation.acceptedPolynomial_opens_or_relation
      (memberDecode := memberDecode) haccepts hbind)
    fun hopen =>
      ofOpenings haccepts hfixedLayout hadviceLayout hinstanceLayout
        hopen hpermutationWellFormed hpermutationRouting
        hrows hroot hnFp hxDomain

end AcceptedModelClaimedEvaluations

/--
The deployed quotient-member binding, instantiated at the accepted canonical
decoded model, proves that model's complete circuit identity or returns the shared
augmented commitment relation.
-/
def acceptedModel_circuitSat_or_relation
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : CPoly)
    (i m : ℕ)
    (hm :
      m < (deployedSetQueries
        vk instanceCommitment ps ch i).length)
    (columnPolynomial :
      Fin (deployedSetQueries
        vk instanceCommitment ps ch i).length →
        CPoly)
    (hbindAll : ∀
      (pointIndex : Fin
        ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD
            i []).length)
      (memberIndex : Fin
        (deployedSetQueries
          vk instanceCommitment ps ch i).length),
      (columnPolynomial memberIndex).eval
          (((constructIntermediateSets
            (assembleQueries vk instanceCommitment ps ch)).points.getD
              i [])[pointIndex]) =
        ((deployedSetQueries
          vk instanceCommitment ps ch i).getD
            (memberIndex : ℕ) (.point 0, [])).2.getD
              (pointIndex : ℕ) 0
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = columnPolynomial ⟨m, hm⟩)
    (hroute :
      (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ defaultQuery,
      ((deployedSetQueries
        vk instanceCommitment ps ch i).getD m defaultQuery).2 =
        [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lBlind -
          hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts
  have hfold :=
    hfold_of_constraint_polys
      urs hk vk instanceCommitment ps ch
      model.fixedCols model.adviceCols model.instanceCols
      model.sets model.chunks model.lookups
      model.l0 model.lLast model.lBlind hpoly
      i m hm columnPolynomial hbindAll hquot hroute hevals haccepts
      claimed.fixed claimed.advice claimed.«instance»
      claimed.sets claimed.chunks claimed.lookups
      claimed.l0 claimed.lLast claimed.lBlind
  refine bindOrRelationWitness hfold fun hcheck => ?_
  apply circuitSatViaConstraints_of_check
    model.fixedCols (fun _ => model.adviceCols)
    (fun _ => model.instanceCols)
    model.gates model.sets model.chunks model.lookups
    model.beta model.gamma model.delta model.theta ch.y
    model.chunkLen model.l0 model.lLast model.lBlind
    hpoly vk.n a ch.x
  · simpa [model, CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver] using hcheck
  · apply hgood_of_good_challenge
    simpa only [model] using hxgood

/--
Uniform openings of the accepted canonical resolver prove satisfaction directly
when `hpoly` is that resolver's vanishing-quotient polynomial.

Unlike `acceptedModel_circuitSat_or_relation`, this formulation does not expose a
point-set index, member index, or an independently selected member-polynomial
family. The unique assembled `vanishingH` query supplies the quotient evaluation.
-/
theorem acceptedModel_circuitSat_of_openings
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : CPoly)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hopen : ∀ query ∈
      assembleQueries vk instanceCommitment ps ch,
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts query.commId).eval
          query.point = query.eval)
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lBlind -
          hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a := by
  let polynomial :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts
  obtain ⟨query, hquery, hqueryId, hqueryPoint, hqueryEval⟩ :=
    vanishing_query_mem_assembleQueries
      vk instanceCommitment ps ch
  have hpolyEval :
      hpoly.eval ch.x =
        expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n) := by
    calc
      hpoly.eval ch.x =
          (polynomial .vanishingH).eval ch.x := by
            rw [hquot]
      _ = (polynomial query.commId).eval query.point := by
            rw [hqueryId, hqueryPoint]
      _ = query.eval := hopen query hquery
      _ = _ := hqueryEval
  have hfingerprint :=
    eval_combineConstraints_deployed
      vk ps ch model.fixedCols model.adviceCols model.instanceCols
      model.sets model.chunks model.lookups
      model.l0 model.lLast model.lBlind
      claimed.fixed claimed.advice claimed.«instance»
      claimed.sets claimed.chunks claimed.lookups
      claimed.l0 claimed.lLast claimed.lBlind
  have hcheck :
      (combineConstraints
        model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups
        model.beta model.gamma model.delta model.theta ch.y
        model.chunkLen model.l0 model.lLast model.lBlind).eval ch.x =
          hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
    exact hfingerprint.trans <|
      hfold_of_expectedHEval_binding
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).2.2)
        ch.y ch.x hpoly vk.n
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors
            (ch.x ^ vk.n) ch.x).2.2)
        (deployedAccepts_xn_ne_one
          urs hk vk instanceCommitment ps ch haccepts)
        hpolyEval rfl
  apply circuitSatViaConstraints_of_check
    model.fixedCols (fun _ => model.adviceCols)
    (fun _ => model.instanceCols)
    model.gates model.sets model.chunks model.lookups
    model.beta model.gamma model.delta model.theta ch.y
    model.chunkLen model.l0 model.lLast model.lBlind
    hpoly vk.n a ch.x
  · simpa [model, CanonicalMemberConstraintRelation.acceptedModel,
      VerifyingKey.constraintModel,
      constraintModelOfResolver] using hcheck
  · apply hgood_of_good_challenge
    simpa only [model] using hxgood

/--
The canonical quotient terminal directly from accepted member-node binding.

All query evaluations and the quotient carrier are fixed by the accepted
`CommitmentId` resolver. The only exceptional branch is the existing
augmented-basis relation produced by node binding.
-/
def acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : CPoly)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hfixedLayout :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hadviceLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hinstanceLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := instanceCommitment)
          vk ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := instanceCommitment)
            vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (hpermutationRouting :
      PermutationChunkRoutingCoherent vk)
    (hrows : Function.Injective
      fun row : Fin vk.n => vk.omega ^ (row : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lBlind -
          hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  refine bindOrRelationWitness
    (CanonicalMemberConstraintRelation.acceptedPolynomial_opens_or_relation
      (memberDecode := memberDecode) haccepts hbind)
    fun hopen => ?_
  have claimed :=
      AcceptedModelClaimedEvaluations.ofOpenings
        (hblinding := hblinding)
        haccepts hfixedLayout hadviceLayout hinstanceLayout hopen
        (permutationLastEvalsWellFormed_of_deployedAccepts
          urs hk vk instanceCommitment ps ch haccepts)
        hpermutationRouting hrows hroot hnFp
        (deployedAccepts_xn_ne_one
          urs hk vk instanceCommitment ps ch haccepts)
  exact
    acceptedModel_circuitSat_of_openings
      urs hk vk instanceCommitment ps ch memberDecode
      haccepts hblinding hpoly hquot hopen claimed hxgood

end Zcash.Snark

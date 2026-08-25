import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Soundness.StraightLine.Event
import Zcash.Snark.Soundness.Composition.SequentialLift
import Zcash.Snark.Soundness.Composition.ChallengeReads
import Zcash.Snark.Soundness.Composition.SemanticChallengeRemainder
import Zcash.Circuits.Integration.PermutationCompiler

/-!
# Pricing the Action semantic failure events from sequential cuts

The capstone takes four bounds as premises: the run's `θ`, `β`, `γ` and `x`/`y` challenges
landing in their terminal exclusion sets.  This module discharges each from a sequential cut at
the challenge's own squeeze index and a *view* — the exclusion set's inputs read off the cut
state.  The chain per challenge:

1. the run record's challenge is the oracle's answer at its squeeze prefix
   (`straightLineRunReads_eq`);
2. the exclusion set reads only data the view supplies (`ChallengeReads` congruences, or the
   model view outright for `x`/`y`), so the failure event is contained in the cut's state
   surface (`SequentialCut.surfaceEvent`);
3. the surface costs `(Q + 1) * epsilon` (`SequentialCut.surfaceEvent_prob_le`).

The view-agreement premises are the sequential model's content: a prover that commits its
columns before `θ` is squeezed determines, at that moment, everything the `θ` set reads.  The
final endpoint quantifies over families equipped with such cuts.
-/

namespace Zcash.Snark

open Halo2

/-- The permutation cell count is `m` rows per chunk pair — a layout count: the pair list is a
`map` over the key's own `permutationChunks`. -/
theorem resolverPermutationCell_card {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    Fintype.card (ResolverPermutationCell vk poly p m) =
      ∑ c : Fin shape.numPermutationSets,
        m * (vk.permutationChunks.getD c []).length := by
  simp [ResolverPermutationCell, ChunkCell, resolverPermutationPairs_length]

/-- For a circuit-derived key, the permutation-cell resolver contains one cell
per active row and equality-enabled circuit column. -/
theorem topLevelResolverPermutationCell_card
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    {numProofs : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    Fintype.card
        (ResolverPermutationCell (top.toVerifierKey urs) poly p m) =
      m * top.permutationColumnCount := by
  rw [resolverPermutationCell_card]
  rw [← Finset.mul_sum]
  congr 1
  let chunks := (top.toVerifierKey urs).permutationChunks
  have hchunks : chunks.length = top.permutationSetCount :=
    top.toVerifierKey_permutationChunks_length urs
  simp only [TopLevelCircuit.permutationSetCount] at hchunks
  rw [← hchunks]
  rw [← List.sum_ofFn]
  calc
    (List.ofFn fun i : Fin chunks.length =>
        (chunks.getD i []).length).sum =
        (List.ofFn fun i : Fin chunks.length =>
          (chunks[i]).length).sum := by
            congr 2
            funext i
            simp
    _ = (chunks.map List.length).sum := by
      exact congrArg List.sum
        (List.ofFn_getElem_eq_map chunks List.length)
    _ = chunks.flatten.length := by
      rw [List.length_flatten]
    _ = top.permutationColumnCount := by
      rw [top.permutationColumnCount_eq_permutationColumns_length]
      simp only [chunks, top.toVerifierKey_permutationChunks,
        verifierCS_permutationChunks_flatten, List.length_zipIdx,
        List.length_map]

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open Classical MeasureTheory
open scoped ENNReal

local instance vestaInhabitedStraightLineActionBudgets : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin pp.numProofs → PublicInputs Fp)
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- The deployed Action key at one basis. -/
abbrev vkAt
    (basis : AugmentedIndex actionCircuit.n → VestaG) :
    VerifyingKey actionCircuit.shape Fp VestaG :=
  actionCircuit.toVerifierKey (ursOfAugmentedBasis actionCircuit.domainExponent basis)

/-- A challenge record carrying only `θ` and `β` — the fields a pre-`x` exclusion set reads. -/
def semanticChRecord (theta beta : Fp) {k : ℕ} : Challenges k Fp :=
  chRecord (fun i => if i = 0 then theta else if i = 1 then beta else 0) (fun _ => 0)

/-- `semanticChRecord` preserves its `theta` input. -/
@[simp] theorem semanticChRecord_theta (theta beta : Fp) {k : ℕ} :
    (semanticChRecord theta beta (k := k)).theta = theta := rfl

/-- `semanticChRecord` preserves its `beta` input. -/
@[simp] theorem semanticChRecord_beta (theta beta : Fp) {k : ℕ} :
    (semanticChRecord theta beta (k := k)).beta = beta := rfl

/-- The run record's challenge at squeeze index `i` is the oracle's answer at the index-`i`
squeeze prefix. -/
theorem straightLineRunRecord_read
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.domainExponent) → Fp) (i : Fin 11) :
    wrappedPreIpaReads (straightLineRunOutput family basis O) i =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) i) :=
  congrFun (straightLineRunReads_eq family basis O) i

/-! ## `θ` (squeeze index 0) -/

/-- **The `θ` failure event is a state surface.**  The `θ` exclusion set reads only the query
columns, which the index-0 view supplies. -/
theorem actionThetaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 0)
    (view : cut.State → CommitmentId → CPoly)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isColumnInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id) :
    topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(TopLevelLookup.thetaBadSet actionCircuit pp
          (ursOfAugmentedBasis actionCircuit.domainExponent basis) (view s))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hin := not_not.mp hmem
  rw [TopLevelLookup.thetaBadSet_congr actionCircuit pp
    (ursOfAugmentedBasis actionCircuit.domainExponent basis)
    (fun id hid => hview basis O h id hid)] at hin
  have hproj : (straightLineRunRecord family basis O).theta =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0) :=
    straightLineRunRecord_read pp family basis O 0
  rw [hproj] at hin
  exact Finset.mem_coe.mpr hin

/-- Probability bound for the `θ` failure event: `(Q + 1)` times the per-state `θ` set
probability. -/
theorem actionThetaFailure_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 0)
    (view : cut.State → CommitmentId → CPoly)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isColumnInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) (view s)) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionThetaFailureEvent_subset pp family static inputs hvk hI hchar cut view hview))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `β` (squeeze index 1) -/

/-- The `β` failure event lies in its permutation and lookup state surfaces. -/
theorem actionBetaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 1)
    (view : cut.State → CommitmentId → CPoly)
    (thetaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O)) :
    topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(allResolverPermutationBetaBadSet pp.numProofs (vkAt basis) (view s)
          (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupBetaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) 0
            (k := actionCircuit.domainExponent)) (view s)
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hproj : (straightLineRunRecord family basis O).beta =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1) :=
    straightLineRunRecord_read pp family basis O 1
  rcases not_and_or.mp hmem with hperm | hlook
  · have hin := not_not.mp hperm
    rw [allResolverPermutationBetaBadSet_congr pp.numProofs (vkAt basis)
      (actionCircuit.usableRowsAt actionCircuit.domainExponent)
      (fun id hid => hview basis O h id (Or.inl hid)), hproj] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr hin)
  · have hin := not_not.mp hlook
    simp only [actionCircuit.toVerifierKey_n,
      actionCircuit.toVerifierKey_blindingFactors] at hin
    rw [allResolverLookupBetaBadSet_congr pp.numProofs (vkAt basis)
      (actionCircuit.n - actionCircuit.blindingFactors - 2)
      ((htheta basis O).trans (semanticChRecord_theta _ _).symm)
      (fun id hid => hview basis O h id (Or.inr hid)), hproj] at hin
    exact Set.mem_union_right _ (Finset.mem_coe.mpr hin)

/-- Probability bound for the `β` failure event: `(Q + 1)` times the per-state probability of the
union of the two `β` exclusion sets. -/
theorem actionBetaFailure_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 1)
    (view : cut.State → CommitmentId → CPoly)
    (thetaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationBetaBadSet pp.numProofs (vkAt basis) (view s)
        (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupBetaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) 0
            (k := actionCircuit.domainExponent)) (view s)
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionBetaFailureEvent_subset pp family static inputs hvk hI hchar
      cut view thetaOf hview htheta))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `γ` (squeeze index 2) -/

/-- **The `γ` failure event is a state surface.**  Both `γ` sets read their input slots and, of
the record, only `θ` and `β` — squeezed earlier, so the state supplies them. -/
theorem actionGammaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 2)
    (view : cut.State → CommitmentId → CPoly)
    (thetaOf betaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    (hbeta : ∀ basis O, (straightLineRunRecord family basis O).beta =
      betaOf ((cut.pre basis).run O)) :
    topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(allResolverPermutationGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s) (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) (betaOf s)
            (k := actionCircuit.domainExponent)) (view s)
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hproj : (straightLineRunRecord family basis O).gamma =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2) :=
    straightLineRunRecord_read pp family basis O 2
  rcases not_and_or.mp hmem with hperm | hlook
  · have hin := not_not.mp hperm
    rw [allResolverPermutationGammaBadSet_congr pp.numProofs (vkAt basis)
      (actionCircuit.usableRowsAt actionCircuit.domainExponent)
      ((hbeta basis O).trans (semanticChRecord_beta _ _).symm)
      (fun id hid => hview basis O h id (Or.inl hid)), hproj] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr hin)
  · have hin := not_not.mp hlook
    simp only [actionCircuit.toVerifierKey_n,
      actionCircuit.toVerifierKey_blindingFactors] at hin
    rw [allResolverLookupGammaBadSet_congr pp.numProofs (vkAt basis)
      (actionCircuit.n - actionCircuit.blindingFactors - 2)
      ((htheta basis O).trans (semanticChRecord_theta _ _).symm)
      ((hbeta basis O).trans (semanticChRecord_beta _ _).symm)
      (fun id hid => hview basis O h id (Or.inr hid)), hproj] at hin
    exact Set.mem_union_right _ (Finset.mem_coe.mpr hin)

/-- Probability bound for the `γ` failure event: `(Q + 1)` times the per-state probability of the
union of the two `γ` exclusion sets. -/
theorem actionGammaFailure_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 2)
    (view : cut.State → CommitmentId → CPoly)
    (thetaOf betaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    (hbeta : ∀ basis O, (straightLineRunRecord family basis O).beta =
      betaOf ((cut.pre basis).run O))
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s) (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord (thetaOf s) (betaOf s)
            (k := actionCircuit.domainExponent)) (view s)
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionGammaFailureEvent_subset pp family static inputs hvk hI hchar
      cut view thetaOf betaOf hview htheta hbeta))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `x` and `y` (squeeze indices 4 and 3) -/

/-- The fused `x`/`y` failure event lies in the union of its two state surfaces. -/
theorem actionXYFailureEvent_subset
    (cutY : SequentialCut family.toComputedAlgebraicFSFamily 3)
    (cutX : SequentialCut family.toComputedAlgebraicFSFamily 4)
    (modelY : cutY.State → ConstraintPolyModel pp.numProofs)
    (modelX : cutX.State → ConstraintPolyModel pp.numProofs)
    (yOf : cutX.State → Fp) (vanishingOf : cutX.State → CPoly)
    (hmodelY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
        modelY ((cutY.pre basis).run O))
    (hmodelX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
        modelX ((cutX.pre basis).run O))
    (hy : ∀ basis O, (straightLineRunRecord family basis O).y =
      yOf ((cutX.pre basis).run O))
    (hvanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
          CommitmentId.vanishingH =
        vanishingOf ((cutX.pre basis).run O)) :
    topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      cutX.surfaceEvent (fun _basis s =>
        ↑(szBadSet (combineConstraints (modelX s).fixedCols (modelX s).adviceCols
          (modelX s).instanceCols (modelX s).gates (modelX s).sets (modelX s).chunks
          (modelX s).lookups (modelX s).beta (modelX s).gamma (modelX s).delta
          (modelX s).theta (yOf s) (modelX s).chunkLen (modelX s).l0 (modelX s).lLast
          (modelX s).lBlind -
          vanishingOf s * (X ^ actionCircuit.n - 1)))) ∪
      cutY.surfaceEvent (fun _basis s =>
        ⋃ j, ↑(szBadSet (foldSplitWitness (modelY s).constraints actionCircuit.n j))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hprojX : (straightLineRunRecord family basis O).x =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4) :=
    straightLineRunRecord_read pp family basis O 4
  have hprojY : (straightLineRunRecord family basis O).y =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3) :=
    straightLineRunRecord_read pp family basis O 3
  rcases not_and_or.mp hmem with hx | hy'
  · have hin := not_not.mp hx
    rw [hmodelX basis O h, hy basis O, hvanishing basis O h, hprojX] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr (by
      simpa only [actionCircuit.toVerifierKey_n] using hin))
  · rw [not_forall] at hy'
    obtain ⟨j, hj⟩ := hy'
    have hin := not_not.mp hj
    rw [hmodelY basis O h, hprojY] at hin
    exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, Finset.mem_coe.mpr (by
      simpa only [actionCircuit.toVerifierKey_n] using hin)⟩)

/-- Probability bound for the fused `x`/`y` failure event: each half pays its own state-surface
price. -/
theorem actionXYFailure_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    (cutY : SequentialCut family.toComputedAlgebraicFSFamily 3)
    (cutX : SequentialCut family.toComputedAlgebraicFSFamily 4)
    (modelY : cutY.State → ConstraintPolyModel pp.numProofs)
    (modelX : cutX.State → ConstraintPolyModel pp.numProofs)
    (yOf : cutX.State → Fp) (vanishingOf : cutX.State → CPoly)
    (hmodelY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
        modelY ((cutY.pre basis).run O))
    (hmodelX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
        modelX ((cutX.pre basis).run O))
    (hy : ∀ basis O, (straightLineRunRecord family basis O).y =
      yOf ((cutX.pre basis).run O))
    (hvanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
          CommitmentId.vanishingH =
        vanishingOf ((cutX.pre basis).run O))
    {epsilonX epsilonY : ENNReal}
    (hbadX : ∀ (_basis : AugmentedIndex actionCircuit.n → VestaG)
      (s : cutX.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(szBadSet (combineConstraints (modelX s).fixedCols (modelX s).adviceCols
        (modelX s).instanceCols (modelX s).gates (modelX s).sets (modelX s).chunks
        (modelX s).lookups (modelX s).beta (modelX s).gamma (modelX s).delta
        (modelX s).theta (yOf s) (modelX s).chunkLen (modelX s).l0 (modelX s).lLast
        (modelX s).lBlind -
        vanishingOf s * (X ^ actionCircuit.n - 1))) ≤ epsilonX)
    (hbadY : ∀ (_basis : AugmentedIndex actionCircuit.n → VestaG)
      (s : cutY.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (⋃ j, ↑(szBadSet (foldSplitWitness (modelY s).constraints actionCircuit.n j))) ≤
        epsilonY) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilonX + (family.Q + 1 : ℕ) * epsilonY := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionXYFailureEvent_subset pp family static inputs hvk hI hchar cutY cutX
      modelY modelX yOf vanishingOf hmodelY hmodelX hy hvanishing))) ?_
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · exact cutX.surfaceEvent_prob_le query _ hbadX
  · exact cutY.surfaceEvent_prob_le query _ hbadY

/-! ## Per-state probability bounds

Each surface's `hbad` premise is a counting statement at one state.  The counts are the staged
remainder's: the row-by-arity budget for `θ`, cell counts for the permutation sets, `(u + 1)`
polynomials of the lookup sets, and `n` times the constraint count for `y`.  The `x` set is one
Schwartz–Zippel exclusion, priced by `uniformChallenge_szBadSet` at its fold degree.
-/

/-- Probability bound for the per-state `θ` bad set: the row-by-arity budget over the field
size. -/
theorem actionThetaBadSet_probability_bound
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (poly : CommitmentId → CPoly) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) poly) ≤
      (TopLevelLookup.thetaBudget actionCircuit pp
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) poly : ℝ≥0∞) /
        (Fintype.card Fp : ℝ≥0∞) :=
  TopLevelLookup.uniformChallenge_thetaBadSet
    poly

/-- Probability bound for the per-state `β` bad sets: permutation cells plus lookup pair
counts. -/
theorem actionBetaBadSets_probability_bound
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (theta : Fp) (poly : CommitmentId → CPoly) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationBetaBadSet pp.numProofs (vkAt basis) poly
        (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupBetaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord theta 0
            (k := actionCircuit.domainExponent)) poly
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) ≤
      ((∑ p : Fin pp.numProofs,
        (Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
          (numProofs := pp.numProofs) (vkAt basis) poly p
          (actionCircuit.usableRowsAt actionCircuit.domainExponent)) + 1) *
          Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
            (numProofs := pp.numProofs) (vkAt basis) poly p
            (actionCircuit.usableRowsAt actionCircuit.domainExponent)) :
            ℕ) : ℝ≥0∞) / Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp :=
  le_trans (measure_union_le _ _)
    (add_le_add
      (allResolverPermutationBetaBadSet_measure_le pp.numProofs (vkAt basis) poly
        (actionCircuit.usableRowsAt actionCircuit.domainExponent))
      (by
        simpa only [TopLevelCircuit.lookupCount] using
          allResolverLookupBetaBadSet_measure_le pp.numProofs (vkAt basis)
            (semanticChRecord theta 0
              (k := actionCircuit.domainExponent)) poly
            (actionCircuit.n - actionCircuit.blindingFactors - 2)))

/-- Probability bound for the per-state `γ` bad sets: doubled permutation cells plus lookup pair
counts. -/
theorem actionGammaBadSets_probability_bound
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (theta beta : Fp) (poly : CommitmentId → CPoly) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord theta beta (k := actionCircuit.domainExponent)) poly
          (actionCircuit.usableRowsAt actionCircuit.domainExponent)) ∪
        ↑(allResolverLookupGammaBadSet pp.numProofs (vkAt basis)
          (semanticChRecord theta beta
            (k := actionCircuit.domainExponent)) poly
          (actionCircuit.n - actionCircuit.blindingFactors - 2))) ≤
      ((∑ p : Fin pp.numProofs,
        2 * Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
          (numProofs := pp.numProofs) (vkAt basis) poly p
          (actionCircuit.usableRowsAt actionCircuit.domainExponent)) :
          ℕ) : ℝ≥0∞) / Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp :=
  le_trans (measure_union_le _ _)
    (add_le_add
      (allResolverPermutationGammaBadSet_measure_le pp.numProofs (vkAt basis)
        (semanticChRecord theta beta (k := actionCircuit.domainExponent)) poly
        (actionCircuit.usableRowsAt actionCircuit.domainExponent))
      (by
        simpa only [TopLevelCircuit.lookupCount] using
          allResolverLookupGammaBadSet_measure_le pp.numProofs (vkAt basis)
            (semanticChRecord theta beta
              (k := actionCircuit.domainExponent))
            poly (actionCircuit.n - actionCircuit.blindingFactors - 2)))

/-- Probability bound for the per-state `y` bad set: `n` times the constraint count over the field
size. -/
theorem actionYBadSet_probability_bound
    (constraints : List (CPoly)) (hn : actionCircuit.n ≠ 0) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (⋃ j, ↑(szBadSet (foldSplitWitness constraints actionCircuit.n j))) ≤
      ((actionCircuit.n * constraints.length : ℕ) : ℝ≥0∞) /
        (Fintype.card Fp : ℝ≥0∞) := by
  have hset : (⋃ j, ↑(szBadSet (foldSplitWitness constraints actionCircuit.n j))) =
      {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness constraints actionCircuit.n j)} := by
    ext y
    simp [Set.mem_iUnion]
  rw [hset]
  exact goodY_failure_measure_le constraints hn

/-! ## The phased Action execution and its generated cuts

The public adversary model supplies executable phases whose *outputs* are the data emitted before
each semantic squeeze.  `ActionSequentialExecution.toCuts` below generates the five cuts and all
state views.  `ActionSequentialCuts` is the internal product consumed by the four counting
lemmas, not an input to the public capstone.
-/

/-- Data emitted before `θ`: the represented query-column polynomials. -/
structure ActionThetaSnapshot where
  polynomial : CommitmentId → CPoly

/-- Data emitted before `β`: the represented query-column polynomials and the earlier `θ`
answer. -/
structure ActionBetaSnapshot where
  polynomial : CommitmentId → CPoly
  theta : Fp

/-- Data emitted before `γ`: the represented query-column polynomials and the earlier `θ` and `β`
answers. -/
structure ActionGammaSnapshot where
  polynomial : CommitmentId → CPoly
  theta : Fp
  beta : Fp

/-- Data emitted before `y`: the accepted constraint model fixed by the earlier challenges. -/
structure ActionYSnapshot (np : ℕ) where
  model : ConstraintPolyModel np

/-- Data emitted before `x`: the accepted model, `y`, and represented vanishing polynomial. -/
structure ActionXSnapshot (np : ℕ) where
  model : ConstraintPolyModel np
  y : Fp
  vanishing : CPoly

/-- Five stopped computations whose snapshots agree with the final decoded run. -/
structure ActionSequentialExecution (Dx L : ℕ) where
  thetaPhase : SequentialPhase family.toComputedAlgebraicFSFamily 0 ActionThetaSnapshot
  betaPhase : SequentialPhase family.toComputedAlgebraicFSFamily 1 ActionBetaSnapshot
  gammaPhase : SequentialPhase family.toComputedAlgebraicFSFamily 2 ActionGammaSnapshot
  yPhase : SequentialPhase family.toComputedAlgebraicFSFamily 3
    (ActionYSnapshot pp.numProofs)
  xPhase : SequentialPhase family.toComputedAlgebraicFSFamily 4
    (ActionXSnapshot pp.numProofs)
  hthetaPolynomial : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isColumnInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        ((thetaPhase.pre basis).run O).polynomial id
  hbetaPolynomial : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isPermutationInput ∨ id.isLookupInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        ((betaPhase.pre basis).run O).polynomial id
  hbetaTheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
    ((betaPhase.pre basis).run O).theta
  hgammaPolynomial : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isPermutationInput ∨ id.isLookupInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        ((gammaPhase.pre basis).run O).polynomial id
  hgammaTheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
    ((gammaPhase.pre basis).run O).theta
  hgammaBeta : ∀ basis O, (straightLineRunRecord family basis O).beta =
    ((gammaPhase.pre basis).run O).beta
  hyModel : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
      ((yPhase.pre basis).run O).model
  ylen : ∀ s : ActionYSnapshot pp.numProofs,
    s.model.constraints.length ≤ L
  hxModel : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
      ((xPhase.pre basis).run O).model
  hxY : ∀ basis O, (straightLineRunRecord family basis O).y =
    ((xPhase.pre basis).run O).y
  hxVanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
        CommitmentId.vanishingH = ((xPhase.pre basis).run O).vanishing
  xdeg : ∀ s : ActionXSnapshot pp.numProofs,
    (combineConstraints s.model.fixedCols s.model.adviceCols s.model.instanceCols
      s.model.gates s.model.sets s.model.chunks s.model.lookups s.model.beta s.model.gamma
      s.model.delta s.model.theta s.y s.model.chunkLen s.model.l0 s.model.lLast
      s.model.lBlind - s.vanishing * (X ^ actionCircuit.n - 1)).natDegree ≤ Dx

/-- Internal generated cuts and views at the five semantic squeeze indices. -/
structure ActionSequentialCuts (Dx L : ℕ) where
  /-- The cut at the `θ` squeeze. -/
  cut0 : SequentialCut family.toComputedAlgebraicFSFamily 0
  /-- The query columns, read off the pre-`θ` state. -/
  view0 : cut0.State → CommitmentId → CPoly
  /-- The `θ` view agrees with the decoded run polynomial on the query columns. -/
  hview0 : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isColumnInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        view0 ((cut0.pre basis).run O) id
  /-- The cut at the `β` squeeze. -/
  cut1 : SequentialCut family.toComputedAlgebraicFSFamily 1
  /-- The permutation and lookup inputs, read off the pre-`β` state. -/
  view1 : cut1.State → CommitmentId → CPoly
  /-- The `θ` answer carried by the pre-`β` state. -/
  theta1 : cut1.State → Fp
  /-- The `β` view agrees with the decoded run polynomial on both input classes. -/
  hview1 : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isPermutationInput ∨ id.isLookupInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        view1 ((cut1.pre basis).run O) id
  /-- The state's `θ` is the run record's. -/
  htheta1 : ∀ basis O, (straightLineRunRecord family basis O).theta =
    theta1 ((cut1.pre basis).run O)
  /-- The cut at the `γ` squeeze. -/
  cut2 : SequentialCut family.toComputedAlgebraicFSFamily 2
  /-- The permutation and lookup inputs, read off the pre-`γ` state. -/
  view2 : cut2.State → CommitmentId → CPoly
  /-- The `θ` answer carried by the pre-`γ` state. -/
  theta2 : cut2.State → Fp
  /-- The `β` answer carried by the pre-`γ` state. -/
  beta2 : cut2.State → Fp
  /-- The `γ` view agrees with the decoded run polynomial on both input classes. -/
  hview2 : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    ∀ id, id.isPermutationInput ∨ id.isLookupInput →
      topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h id =
        view2 ((cut2.pre basis).run O) id
  /-- The state's `θ` is the run record's. -/
  htheta2 : ∀ basis O, (straightLineRunRecord family basis O).theta =
    theta2 ((cut2.pre basis).run O)
  /-- The state's `β` is the run record's. -/
  hbeta2 : ∀ basis O, (straightLineRunRecord family basis O).beta =
    beta2 ((cut2.pre basis).run O)
  /-- The cut at the `y` squeeze. -/
  cut3 : SequentialCut family.toComputedAlgebraicFSFamily 3
  /-- The accepted model, read off the pre-`y` state. -/
  modelY : cut3.State → ConstraintPolyModel pp.numProofs
  /-- The `y` model view agrees with the decoded run model. -/
  hmodelY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
      modelY ((cut3.pre basis).run O)
  /-- The `y` view's constraint count is capped: decoded models carry the key's list shape. -/
  ylen : ∀ s, (modelY s).constraints.length ≤ L
  /-- The cut at the `x` squeeze. -/
  cut4 : SequentialCut family.toComputedAlgebraicFSFamily 4
  /-- The accepted model, read off the pre-`x` state. -/
  modelX : cut4.State → ConstraintPolyModel pp.numProofs
  /-- The `y` answer carried by the pre-`x` state. -/
  yOf : cut4.State → Fp
  /-- The vanishing commitment's polynomial, read off the pre-`x` state. -/
  vanishingOf : cut4.State → CPoly
  /-- The `x` model view agrees with the decoded run model. -/
  hmodelX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h =
      modelX ((cut4.pre basis).run O)
  /-- The state's `y` is the run record's. -/
  hy : ∀ basis O, (straightLineRunRecord family basis O).y =
    yOf ((cut4.pre basis).run O)
  /-- The vanishing view agrees with the decoded run polynomial at the vanishing slot. -/
  hvanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
    topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
        CommitmentId.vanishingH =
      vanishingOf ((cut4.pre basis).run O)
  /-- The `x` fold degree is capped: decoded representations have degree below `2^k`. -/
  xdeg : ∀ s,
    (combineConstraints (modelX s).fixedCols (modelX s).adviceCols
      (modelX s).instanceCols (modelX s).gates (modelX s).sets (modelX s).chunks
      (modelX s).lookups (modelX s).beta (modelX s).gamma (modelX s).delta
      (modelX s).theta (yOf s) (modelX s).chunkLen (modelX s).l0 (modelX s).lLast
      (modelX s).lBlind -
      vanishingOf s * (X ^ actionCircuit.n - 1)).natDegree ≤ Dx

/-- Generate all five cuts and views from one phased Action execution. -/
def ActionSequentialExecution.toCuts {Dx L : ℕ}
    (execution : ActionSequentialExecution pp family static inputs hvk hI hchar Dx L) :
    ActionSequentialCuts pp family static inputs hvk hI hchar Dx L where
  cut0 := execution.thetaPhase.toCut
  view0 := ActionThetaSnapshot.polynomial
  hview0 := execution.hthetaPolynomial
  cut1 := execution.betaPhase.toCut
  view1 := ActionBetaSnapshot.polynomial
  theta1 := ActionBetaSnapshot.theta
  hview1 := execution.hbetaPolynomial
  htheta1 := execution.hbetaTheta
  cut2 := execution.gammaPhase.toCut
  view2 := ActionGammaSnapshot.polynomial
  theta2 := ActionGammaSnapshot.theta
  beta2 := ActionGammaSnapshot.beta
  hview2 := execution.hgammaPolynomial
  htheta2 := execution.hgammaTheta
  hbeta2 := execution.hgammaBeta
  cut3 := execution.yPhase.toCut
  modelY := ActionYSnapshot.model
  hmodelY := execution.hyModel
  ylen := execution.ylen
  cut4 := execution.xPhase.toCut
  modelX := ActionXSnapshot.model
  yOf := ActionXSnapshot.y
  vanishingOf := ActionXSnapshot.vanishing
  hmodelX := execution.hxModel
  hy := execution.hxY
  hvanishing := execution.hxVanishing
  xdeg := execution.xdeg

/-- Probability bound for the bundle's `θ` event: `(Q + 1) · Nθ / |Fp|`, with `Nθ` capping the
row-by-arity budget. -/
theorem ActionSequentialCuts.theta_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    {Dx L : ℕ} (cuts : ActionSequentialCuts pp family static inputs hvk hI hchar Dx L)
    {Ntheta : ℕ}
    (hbudget : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      TopLevelLookup.thetaBudget actionCircuit pp
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) poly ≤ Ntheta) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * ((Ntheta : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) := by
  refine actionThetaFailure_probability_bound pp family static inputs hvk hI hchar query
    cuts.cut0 cuts.view0 cuts.hview0 (fun basis s => ?_)
  refine le_trans (actionThetaBadSet_probability_bound pp basis (cuts.view0 s)) ?_
  gcongr
  exact_mod_cast hbudget basis (cuts.view0 s)

/-- Probability bound for the bundle's `β` event: `(Q + 1) · Nβ / |Fp|`, with `Nβ` capping cells
plus lookup pairs. -/
theorem ActionSequentialCuts.beta_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    {Dx L : ℕ} (cuts : ActionSequentialCuts pp family static inputs hvk hI hchar Dx L)
    {Nbeta : ℕ}
    (hcap : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin pp.numProofs,
        (Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
          (numProofs := pp.numProofs) (vkAt basis) poly p
          (actionCircuit.usableRowsAt actionCircuit.domainExponent)) + 1) *
          Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
            (numProofs := pp.numProofs) (vkAt basis) poly p
            (actionCircuit.usableRowsAt actionCircuit.domainExponent))) +
      pp.numProofs * actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤ Nbeta) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * ((Nbeta : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) := by
  refine actionBetaFailure_probability_bound pp family static inputs hvk hI hchar query
    cuts.cut1 cuts.view1 cuts.theta1 cuts.hview1 cuts.htheta1 (fun basis s => ?_)
  refine le_trans (actionBetaBadSets_probability_bound pp basis (cuts.theta1 s) (cuts.view1 s)) ?_
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  gcongr
  exact_mod_cast hcap basis (cuts.view1 s)

/-- Probability bound for the bundle's `γ` event: `(Q + 1) · Nγ / |Fp|`, with `Nγ` capping
doubled cells plus lookup pairs. -/
theorem ActionSequentialCuts.gamma_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    {Dx L : ℕ} (cuts : ActionSequentialCuts pp family static inputs hvk hI hchar Dx L)
    {Ngamma : ℕ}
    (hcap : ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin pp.numProofs,
        2 * Fintype.card (ResolverPermutationCell (shape := actionCircuit.shape)
          (numProofs := pp.numProofs) (vkAt basis) poly p
          (actionCircuit.usableRowsAt actionCircuit.domainExponent))) +
      pp.numProofs * actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤ Ngamma) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * ((Ngamma : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) := by
  refine actionGammaFailure_probability_bound pp family static inputs hvk hI hchar query
    cuts.cut2 cuts.view2 cuts.theta2 cuts.beta2 cuts.hview2 cuts.htheta2 cuts.hbeta2
    (fun basis s => ?_)
  refine le_trans (actionGammaBadSets_probability_bound pp basis (cuts.theta2 s) (cuts.beta2 s)
    (cuts.view2 s)) ?_
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  gcongr
  exact_mod_cast hcap basis (cuts.view2 s)

/-- Probability bound for the bundle's fused `x`/`y` event:
`(Q + 1) · Dx / |Fp| + (Q + 1) · Ny / |Fp|`, with `Dx` the fold-degree cap and `Ny` capping
`n · L`. -/
theorem ActionSequentialCuts.xy_probability_bound {T : Type*} [DecidableEq T]
    (query : AugmentedIndex actionCircuit.n → T)
    {Dx L : ℕ} (cuts : ActionSequentialCuts pp family static inputs hvk hI hchar Dx L)
    {Ny : ℕ}
    (hn : actionCircuit.n ≠ 0)
    (hyn : actionCircuit.n * L ≤ Ny) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * ((Dx : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        (family.Q + 1 : ℕ) * ((Ny : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) := by
  refine actionXYFailure_probability_bound pp family static inputs hvk hI hchar query
    cuts.cut3 cuts.cut4 cuts.modelY cuts.modelX cuts.yOf cuts.vanishingOf
    cuts.hmodelY cuts.hmodelX cuts.hy cuts.hvanishing
    (fun basis s => ?_) (fun basis s => ?_)
  · refine le_trans (uniformChallenge_szBadSet _) ?_
    gcongr
    exact_mod_cast cuts.xdeg s
  · refine le_trans (actionYBadSet_probability_bound ((cuts.modelY s).constraints)
      hn) ?_
    gcongr
    exact_mod_cast le_trans
      (Nat.mul_le_mul_left _ (cuts.ylen s)) hyn

end ActionTerminal

end Zcash.Snark

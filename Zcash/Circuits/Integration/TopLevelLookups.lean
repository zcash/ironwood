import Zcash.Circuits.Halo2.CompiledLookups
import Zcash.Snark.Soundness.Pricing.TupleCompression
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.Pricing.ChallengePricing
import Zcash.Circuits.Integration.AssignmentEncoding
import Zcash.Circuits.Integration.TopLevelGates

/-! # Polynomial lookup membership in compiled row semantics

Scalar membership holds at all usable rows. Tuple decompression uses only the
compiler's activation schedule, preserving the existing θ collision budget.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Zcash.Arithmetic (omegaOf deltaFp)

open Halo2 CompPoly.CPolynomial Keygen

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}

/-- Mapping a projected lookup tuple into `Expr` does not change its evaluations. -/
theorem map_eval_toExpr
    (fixed advice instanceFeed : ℕ → Fp)
    (expressions : List (RichExpression Fp)) :
    (expressions.map RichExpression.toExpr).map
        (Expr.eval fixed advice instanceFeed) =
      expressions.map
        (RichExpression.eval fixed advice instanceFeed) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro expression _
  exact RichExpression.eval_toExpr
    fixed advice instanceFeed expression

namespace TopLevelLookup

/-- A lookup activation in one proof of the bundle. -/
abbrev ActivationIndex
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) :=
  Fin pp.numProofs × Fin top.lookupActivationRows.length

/-- A comparison of an activated input with one usable table row. -/
abbrev ComparisonIndex
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) :=
  ActivationIndex top pp × Fin (top.usableRowsAt top.domainExponent)

/-- Evaluate a compiled input/table comparison using only column polynomials.
Neither tuple depends on the compression challenge. -/
def comparisonValues
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G) (poly : CommitmentId → CPoly)
    (index : ComparisonIndex top pp) : List Fp × List Fp :=
  let activation := top.lookupActivationRows.get index.1.2
  let env := resolverEnvironment (top.toVerifierKey urs) poly index.1.1
    (top.usableRowsAt top.domainExponent)
  (((top.pinnedCS.lookupInputExprs.getD activation.1 []).map
      ((pinnedQueryState top.pinnedCS).eval env activation.2)),
    ((top.pinnedCS.lookupTableExprs.getD activation.1 []).map
      ((pinnedQueryState top.pinnedCS).eval env index.2)))

/-- All tuple-compression collisions at compiled activation rows across the bundle. -/
def thetaBadSet
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G) (poly : CommitmentId → CPoly) : Finset Fp :=
  tupleCollisionSet
    (fun index : ComparisonIndex top pp => (comparisonValues top pp urs poly index).1)
    (fun index => (comparisonValues top pp urs poly index).2)

/-- Row-by-arity cost, determined entirely by compilation and the proof count. -/
def thetaBudget
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) : ℕ :=
  ∑ index : ActivationIndex top pp, top.usableRowsAt top.domainExponent *
    (top.pinnedCS.lookupInputExprs.getD (top.lookupActivationRows.get index.2).1 []).length

theorem comparisonValues_length (poly : CommitmentId → CPoly)
    (index : ComparisonIndex top pp) :
    (comparisonValues top pp urs poly index).1.length =
      (comparisonValues top pp urs poly index).2.length := by
  simp only [comparisonValues, List.length_map]
  exact top.lookupInputExprs_length_eq_table _

/-- Only compiled activation rows are priced, not every possible input row. -/
theorem uniformChallenge_thetaBadSet (poly : CommitmentId → CPoly) :
    uniformChallenge.toOuterMeasure (thetaBadSet top pp urs poly) ≤
      (thetaBudget top pp : ENNReal) / (Fintype.card Fp : ENNReal) := by
  have h := uniformChallenge_tupleCollisionSet _ _
    (comparisonValues_length (top := top) (pp := pp) (urs := urs) poly)
  simpa only [comparisonValues, List.length_map, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    thetaBadSet, thetaBudget] using h

/-- The three lookup challenge exclusions for the whole bundle. -/
structure ChallengeExclusions
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) : Prop where
  gamma : ch.gamma ∉ allResolverLookupGammaBadSet
    pp.numProofs (top.toVerifierKey urs) ch poly (top.n - top.blindingFactors - 2)
  beta : ch.beta ∉ allResolverLookupBetaBadSet
    pp.numProofs (top.toVerifierKey urs) ch poly (top.n - top.blindingFactors - 2)
  theta : ch.theta ∉ thetaBadSet top pp urs poly

/-- Check tuple collisions at the sampled challenge without enumerating roots. -/
def thetaChecks?
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G) (poly : CommitmentId → CPoly) (theta : Fp) :=
  finForallOption (fun p : Fin pp.numProofs =>
    finForallOption (fun activation : Fin top.lookupActivationRows.length =>
      finForallOption (fun row : Fin (top.usableRowsAt top.domainExponent) =>
        let values := comparisonValues top pp urs poly ((p, activation), row)
        szBadSetAvoidance? (foldPoly values.1 - foldPoly values.2) theta)))

/-- Compute the exclusions over configured arguments and compiled activations. -/
def topLevelLookupChallengeExclusions?
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    Option (PLift (ChallengeExclusions top pp urs ch poly)) :=
  match resolverLookupBundleExclusions? pp.numProofs (top.toVerifierKey urs) ch poly
      (top.n - top.blindingFactors - 2) with
  | none => none
  | some resolver =>
      match thetaChecks? top pp urs poly ch.theta with
      | none => none
      | some theta => some ⟨{
          gamma := resolver.down.1
          beta := resolver.down.2
          theta := (not_mem_tupleCollisionSet_iff _ _ _).2
            fun index => (theta index.1.1 index.1.2 index.2).down }⟩

theorem topLevelLookupChallengeExclusions?_isSome_of
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly)
    (hexclusions : ChallengeExclusions top pp urs ch poly) :
    (topLevelLookupChallengeExclusions? top pp urs ch poly).isSome := by
  have htheta := (not_mem_tupleCollisionSet_iff _ _ _).1 hexclusions.theta
  have hchecks : (thetaChecks? top pp urs poly ch.theta).isSome :=
    finForallOption_isSome_of _ fun p =>
      finForallOption_isSome_of _ fun activation =>
        finForallOption_isSome_of _ fun row =>
          (szBadSetAvoidance?_isSome_iff _ _).2 (htheta ((p, activation), row))
  obtain ⟨checks, hchecks⟩ := Option.isSome_iff_exists.mp hchecks
  obtain ⟨resolver, hresolver⟩ := Option.isSome_iff_exists.mp
    (resolverLookupBundleExclusions?_isSome_of pp.numProofs (top.toVerifierKey urs) ch poly
      (top.n - top.blindingFactors - 2) hexclusions.gamma hexclusions.beta)
  simp only [topLevelLookupChallengeExclusions?, hresolver, hchecks, Option.isSome_some]

/-- Query-feed evaluation identifies the compressed polynomials with compiled row tuples. -/
theorem compressedValues
    {k : ℕ} [CircuitFieldSupport top]
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) (hencoding : top.FixedColumnEncoding poly)
    (index : Fin top.lookupCount) (row : ℕ) :
    (lookupInputPolyOfResolver (top.toVerifierKey urs) ch poly proofIndex index).eval
        (top.omega ^ row) =
      compressValues ch.theta ((top.pinnedCS.lookupInputExprs.getD index []).map
        ((pinnedQueryState top.pinnedCS).eval
          (top.environment (resolverAssignment top.omega poly proofIndex)) row)) ∧
    (lookupTablePolyOfResolver (top.toVerifierKey urs) ch poly proofIndex index).eval
        (top.omega ^ row) =
      compressValues ch.theta ((top.pinnedCS.lookupTableExprs.getD index []).map
        ((pinnedQueryState top.pinnedCS).eval
          (top.environment (resolverAssignment top.omega poly proofIndex)) row)) := by
  have hproject := top.pinnedCS_lookup_eval_of_interprets _ _ _ _ _
    (top.resolverInterpretsPinned (urs := urs) poly proofIndex
      (top.usableRowsAt top.domainExponent) row) index
  rw [top.resolverEnvironment_eq_environment urs poly proofIndex hencoding] at hproject
  constructor
  · rw [lookupInputPolyOfResolver_eq, top.toVerifierKey_lookupInputExprs,
      compress_eval_eq_foldPoly, eval_foldPoly_eq_compressValues,
      top.verifierCS_lookupInputExprs, rowTuple, map_eval_toExpr, hproject.1]
  · rw [lookupTablePolyOfResolver_eq, top.toVerifierKey_lookupTableExprs,
      compress_eval_eq_foldPoly, eval_foldPoly_eq_compressValues,
      top.verifierCS_lookupTableExprs, rowTuple, map_eval_toExpr, hproject.2]

/-- The polynomial lookup argument supplies scalar membership throughout the usable
domain. This step does not mention synthesis activations or selector semantics. -/
theorem scalarSubset
    {k : ℕ} [CircuitFieldSupport top]
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) (index : Fin top.lookupCount)
    (satisfaction : ConstraintSatisfaction (top.constraintModel pp urs ch poly) top.n)
    (hgood : ResolverLookupGoodChallenges (top.toVerifierKey urs) ch poly proofIndex index
      (top.n - top.blindingFactors - 2)) :
    ∀ row < top.usableRowsAt top.domainExponent,
      ∃ tableRow < top.usableRowsAt top.domainExponent,
        (lookupInputPolyOfResolver (top.toVerifierKey urs) ch poly proofIndex index).eval
            (top.omega ^ row) =
          (lookupTablePolyOfResolver (top.toVerifierKey urs) ch poly proofIndex index).eval
            (top.omega ^ tableRow) := by
  let vk := top.toVerifierKey urs
  have husable : vk.blindingFactors + 1 < vk.n := by
    simpa only [vk, top.toVerifierKey_blindingFactors, top.toVerifierKey_n] using
      top.blindingFactors_succ_lt_domainSize
  let canonical := canonicalLagrangePolynomials vk.omega (Nat.lt_of_succ_lt husable)
  have domain := ResolverLookupDomain.ofCanonicalPolynomials vk
  have hsatisfaction := satisfaction
  rw [top.constraintModel_eq_constraintModelOfResolver] at hsatisfaction
  have hsubset := hsatisfaction.resolverLookupSubset vk ch poly
    (permutationSetsOfResolver (numProofs := pp.numProofs) vk poly)
    (permutationChunksOfResolver (numProofs := pp.numProofs) vk poly)
    canonical.1 canonical.2.1 canonical.2.2 proofIndex index domain hgood
  have husableRows : top.usableRowsAt top.domainExponent =
      vk.n - vk.blindingFactors - 2 + 1 := by
    rw [top.usableRowsAt_domainExponent]
    simp only [vk, top.toVerifierKey_n, top.toVerifierKey_blindingFactors] at husable ⊢
    omega
  intro row hrow
  obtain ⟨tableRow, heq⟩ := hsubset ⟨row, by rwa [← husableRows]⟩
  exact ⟨tableRow, by simpa only [husableRows] using tableRow.isLt,
    by simpa only [lookupColumnRows, vk, top.toVerifierKey_omega] using heq⟩

/-- Accepted polynomial constraints imply compiled tuple membership at every
activation, outside exactly the existing activation-by-table-row collision sets. -/
theorem lookupsCompiled_of_constraintSatisfaction
    {k : ℕ} [CircuitFieldSupport top]
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction : ConstraintSatisfaction (top.constraintModel pp urs ch poly) top.n)
    (hencoding : top.FixedColumnEncoding poly)
    (exclusions : ChallengeExclusions top pp urs ch poly) :
    top.LookupsCompiled (resolverAssignment top.omega poly proofIndex) := by
  intro activation hactivation
  have hgood := resolverLookupGoodChallenges_of_not_mem
    pp.numProofs (top.toVerifierKey urs) ch poly
    (top.n - top.blindingFactors - 2)
    exclusions.gamma exclusions.beta proofIndex activation.1
  obtain ⟨row, hrow, heq⟩ := scalarSubset ch poly proofIndex activation.1 satisfaction hgood
    _ (top.lookupActivationRows_row_lt hactivation)
  rw [(compressedValues ch poly proofIndex hencoding activation.1 _).1,
    (compressedValues ch poly proofIndex hencoding activation.1 row).2] at heq
  refine ⟨row, hrow, eq_of_compressValues_eq_of_not_mem ?_ ?_ heq⟩
  · simpa only [List.length_map] using top.lookupInputExprs_length_eq_table activation.1
  · obtain ⟨i, hi, hactivation⟩ := List.mem_iff_getElem.mp hactivation
    have htheta := (not_mem_tupleCollisionSet_iff _ _ _).1 exclusions.theta
      ((proofIndex, ⟨i, hi⟩), ⟨row, hrow⟩)
    simpa only [comparisonValues, List.get_eq_getElem, hactivation,
      top.resolverEnvironment_eq_environment urs poly proofIndex hencoding] using htheta

end TopLevelLookup

end Zcash.Snark

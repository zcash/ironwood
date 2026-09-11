import Zcash.Circuits.Halo2.CompiledLookups
import Zcash.Circuits.Integration.OperationLookups
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

/--
Index every lookup activation in every proof of a top-level bundle. The activation
list is shared by all proofs, while the resolver environment is proof-indexed.
-/
abbrev ActivationIndex
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) :=
  Fin pp.numProofs ×
    Fin (operationEnabledLookups (top.operations) 0).length

/--
The exact bundle-wide `θ` collision surface for a top-level circuit. A single
transcript challenge is shared by every proof and every enabled lookup activation,
so the event must be unioned across both indices.
-/
def thetaBadSet
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) : Finset Fp :=
  enabledLookupThetaBadSetFamily
    (ι := ActivationIndex top pp)
    (fun _ => top.placement)
    (fun index =>
      resolverEnvironment
        (top.toVerifierKey urs) poly index.1
        (top.usableRowsAt top.domainExponent))
    (fun index =>
      (operationEnabledLookups (top.operations) 0).get index.2)

/-- The row-by-arity root budget for the top-level bundle's `θ` surface. -/
def thetaBudget
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly) : ℕ :=
  ∑ index : ActivationIndex top pp,
    (resolverEnvironment
      (top.toVerifierKey urs) poly index.1
      (top.usableRowsAt top.domainExponent)).usableRows *
    (EnabledLookup.inputValues
      top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly index.1
        (top.usableRowsAt top.domainExponent))
      ((operationEnabledLookups
        (top.operations) 0).get index.2)).length

/--
The bundle-wide top-level `θ` surface has exactly the generic
`usableRows × tupleArity` union-bound budget, summed over every proof and
activation.
-/
theorem uniformChallenge_thetaBadSet
    (poly : CommitmentId → CPoly) :
    uniformChallenge.toOuterMeasure
        (thetaBadSet top pp urs poly)
      ≤ (thetaBudget top pp urs poly : ENNReal) /
        (Fintype.card Fp : ENNReal) := by
  unfold thetaBadSet thetaBudget
  apply uniformChallenge_enabledLookupThetaBadSetFamily
  intro index row _hrow
  let lookup :=
    (operationEnabledLookups (top.operations) 0).get index.2
  have harity := lookup.argument.arity
  unfold EnabledLookup.inputValues EnabledLookup.tableValues
  simpa only [List.length_map] using harity

/--
The three lookup challenge exclusions at their natural bundle-wide granularity.
These are transcript/probability-layer facts, independent of fixed-column selector
realization.
-/
structure ChallengeExclusions
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) : Prop where
  gamma :
    ch.gamma ∉ allResolverLookupGammaBadSet
      pp.numProofs (top.toVerifierKey urs) ch poly
      (top.n -
        top.blindingFactors - 2)
  beta :
    ch.beta ∉ allResolverLookupBetaBadSet
      pp.numProofs (top.toVerifierKey urs) ch poly
      (top.n -
        top.blindingFactors - 2)
  theta :
    ch.theta ∉ thetaBadSet top pp urs poly

/-- Compute the three bundle-wide lookup exclusions from finite point checks.  The `β`/`γ`
adapter traverses configured lookup arguments; the `θ` adapter traverses synthesized lookup
activations and their usable rows. -/
def topLevelLookupChallengeExclusions?
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) :
    Option (PLift (ChallengeExclusions top pp urs ch poly)) :=
  let vk := top.toVerifierKey urs
  let u := top.n - top.blindingFactors - 2
  match hresolver : resolverLookupBundleExclusions? pp.numProofs vk ch poly u with
  | none => none
  | some resolver =>
      match htheta : finForallOption
          (fun p : Fin pp.numProofs =>
            finForallOption (fun l : Fin (operationEnabledLookups (top.operations) 0).length =>
              let environment := resolverEnvironment vk poly p
                (top.usableRowsAt top.domainExponent)
              let lookup := (operationEnabledLookups (top.operations) 0).get l
              lookup.thetaAvoidance? top.placement environment ch.theta)) with
      | none => none
      | some theta => some ⟨
          { gamma := resolver.down.1
            beta := resolver.down.2
            theta := by
              apply (not_mem_enabledLookupThetaBadSetFamily_iff
                (ι := ActivationIndex top pp)
                (fun _ => top.placement)
                (fun index => resolverEnvironment vk poly index.1
                  (top.usableRowsAt top.domainExponent))
                (fun index =>
                  (operationEnabledLookups (top.operations) 0).get index.2)
                ch.theta).2
              intro index
              exact (theta index.1 index.2).down }⟩

theorem topLevelLookupChallengeExclusions?_isSome_of
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (hexclusions : ChallengeExclusions top pp urs ch poly) :
    (topLevelLookupChallengeExclusions? top pp urs ch poly).isSome := by
  let vk := top.toVerifierKey urs
  let u := top.n - top.blindingFactors - 2
  obtain ⟨resolver, hresolver⟩ := Option.isSome_iff_exists.mp
    (resolverLookupBundleExclusions?_isSome_of pp.numProofs vk ch poly u
      hexclusions.gamma hexclusions.beta)
  have hthetaSpec : ∀ index : ActivationIndex top pp,
      ch.theta ∉ ((operationEnabledLookups (top.operations) 0).get index.2).thetaBadSet
        top.placement
        (resolverEnvironment vk poly index.1
          (top.usableRowsAt top.domainExponent)) := by
    apply (not_mem_enabledLookupThetaBadSetFamily_iff
      (ι := ActivationIndex top pp)
      (fun _ => top.placement)
      (fun index => resolverEnvironment vk poly index.1
        (top.usableRowsAt top.domainExponent))
      (fun index => (operationEnabledLookups (top.operations) 0).get index.2)
      ch.theta).1
    exact hexclusions.theta
  have hthetaSome : ∀ index : ActivationIndex top pp,
      (((operationEnabledLookups (top.operations) 0).get index.2).thetaAvoidance?
        top.placement
        (resolverEnvironment vk poly index.1
          (top.usableRowsAt top.domainExponent)) ch.theta).isSome :=
    fun index => EnabledLookup.thetaAvoidance?_isSome_of _ _ _ _ (hthetaSpec index)
  obtain ⟨theta, htheta⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ (fun p =>
      finForallOption_isSome_of _ (fun l => hthetaSome (p, l))))
  unfold topLevelLookupChallengeExclusions?
  simp only
  rw [hresolver]
  generalize hresult : finForallOption
      (fun p : Fin pp.numProofs =>
        finForallOption (fun l : Fin (operationEnabledLookups (top.operations) 0).length =>
          let environment := resolverEnvironment vk poly p
            (top.usableRowsAt top.domainExponent)
          let lookup := (operationEnabledLookups (top.operations) 0).get l
          lookup.thetaAvoidance? top.placement environment ch.theta)) = result at htheta ⊢
  cases result <;> simp_all


/-- Query-feed evaluation transports each compressed polynomial to the compiler's
uncompressed tuple evaluated in the circuit-owned environment. -/
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
  obtain ⟨⟨lookup, henabled⟩, _, rfl⟩ := List.mem_map.mp hactivation
  let index := (lookup.topLevelRoute henabled).index
  have hgood := resolverLookupGoodChallenges_of_not_mem
    pp.numProofs (top.toVerifierKey urs) ch poly
    (top.n - top.blindingFactors - 2)
    exclusions.gamma exclusions.beta proofIndex index
  obtain ⟨row, hrow, heq⟩ := scalarSubset ch poly proofIndex index satisfaction hgood
    _ (lookup.activationRow_lt_usableRows henabled)
  rw [(compressedValues ch poly proofIndex hencoding index _).1,
    (compressedValues ch poly proofIndex hencoding index row).2] at heq
  refine ⟨row, hrow, ?_⟩
  have hprojection := top.lookup_values_eq
    (resolverAssignment top.omega poly proofIndex) lookup henabled
  rw [hprojection.1, hprojection.2 row hrow] at heq ⊢
  apply eq_of_compressValues_eq_of_not_mem _ _ heq
  · simpa only [EnabledLookup.inputValues, EnabledLookup.tableValues, List.length_map] using
      lookup.argument.arity
  · obtain ⟨lookupIndex, hindex, hlookup⟩ := List.mem_iff_getElem.mp henabled
    have htheta := (not_mem_enabledLookupThetaBadSetFamily_iff
      (ι := ActivationIndex top pp)
      (fun _ => top.placement)
      (fun index => resolverEnvironment (top.toVerifierKey urs) poly index.1
        (top.usableRowsAt top.domainExponent))
      (fun index => (operationEnabledLookups top.operations 0).get index.2)
      ch.theta).mp exclusions.theta (proofIndex, ⟨lookupIndex, hindex⟩)
    simp only [List.get_eq_getElem, hlookup] at htheta
    rw [top.resolverEnvironment_eq_environment urs poly proofIndex hencoding] at htheta
    exact (lookup.not_mem_thetaBadSet_iff _ _ _).mp htheta row
      (by rwa [top.environment_usableRows_eq])

end TopLevelLookup

end Zcash.Snark

import Zcash.Circuits.Integration.LookupProjection
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelGates

/-!
# Resolver-backed lookup witnesses for top-level circuits

`LookupProjection` proves the compiler walk correct at a selected configured
lookup. This module selects that lookup from an enabled top-level operation and
connects its projected expressions to the resolver polynomials used by the
deployed lookup argument.

The remaining selector premise is stated explicitly. Lookup tuple semantics need
exact selector values, whereas the gate bridge only needs a nonzero selector
scale. The fixed-column compiler will discharge this premise from its complete
packed-selector rows.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (omegaOf)

open Halo2 CompPoly.CPolynomial Keygen

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}

/-- A synthesis-enabled lookup routed to its configured lookup index. -/
structure EnabledLookup.TopLevelRoute
    (top : TopLevelCircuit Fp Config PublicInput)
    (lookup : EnabledLookup Fp) where
  index : Fin top.lookupCount
  argument :
    top.constraintSystem.lookups[index.val] = lookup.argument

/--
Configure/synthesis closure selects a configured lookup index for every enabled
lookup operation.
-/
def EnabledLookup.topLevelRoute
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    lookup.TopLevelRoute top := by
  have hargument :
      lookup.argument ∈ top.constraintSystem.lookups :=
    OperationsKeygenCoherent.lookup top.keygenCoherent henabled
  let index := top.constraintSystem.lookups.idxOf lookup.argument
  have hindex : index < top.constraintSystem.lookups.length :=
    List.idxOf_lt_length_iff.mpr hargument
  have hget : top.constraintSystem.lookups[index] = lookup.argument :=
    List.getElem_idxOf hindex
  refine
    { index := ⟨index, ?_⟩
      argument := hget }
  simpa only [TopLevelCircuit.lookupCount] using hindex

/--
Every extracted lookup activation lies inside the top-level circuit's keygen row
footprint.
-/
theorem EnabledLookup.activationRow_lt_usedRows
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    top.placement lookup.region + lookup.row < top.usedRows := by
  obtain ⟨body, hregion, hoperation⟩ :=
    (mem_operationEnabledLookups_iff lookup (top.operations) 0).mp henabled
  exact
    (absoluteRow_lt_usedRows_of_enableLookup_mem
      (top.operations) lookup.region body hregion
      lookup.argument lookup.enabled lookup.row hoperation).trans_le
      top.operations_usedRows_le_usedRows

/--
A fitting circuit-derived domain places every lookup activation in the usable-row
prefix.
-/
theorem EnabledLookup.activationRow_lt_usableRows
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    top.placement lookup.region + lookup.row <
      top.usableRowsAt top.domainExponent :=
  (lookup.activationRow_lt_usedRows henabled).trans_le
    top.usedRows_le_usableRowsAt_domainExponent

/--
Selector compression covers every configured lookup input of a top-level circuit.

`FormalCircuit.toConstraintSystem` closes selector allocation over every synthesis
lookup input, and the generic selector compiler turns that syntactic bound into
coverage by the circuit-derived compression map.
-/
theorem topLevelLookupInputs_selectorsCovered
    (top : TopLevelCircuit Fp Config PublicInput)
    (argument : LookupArgument Fp)
    (hargument : argument ∈ top.constraintSystem.lookups)
    (expression : Expression Fp Query)
    (hexpression : expression ∈ argument.inputs) :
    expression.selectorsCovered
      (fun selector =>
        (top.selectorMap.lookup selector).isSome) = true := by
  have sourceCoverage :=
    expression.selectorsCovered_lt_of_selectorBound_le
      top.selectorCount
      (top.lookupInputsAllocated
        argument hargument expression hexpression)
  apply Expression.selectorsCovered_mono
    (fun selector =>
      decide (selector <
        top.selectorCount))
  · intro selector hselector
    exact deriveSelCompressMap_lookup_isSome_of_lt
      top.constraintSystem
      top.n
      top.selectorActivations
      (of_decide_eq_true hselector)
  · exact sourceCoverage

/--
Every configured lookup table expression of a top-level circuit is selector-free.
This is intrinsic to `LookupArgument`, not an additional coherence assumption.
-/
theorem lookupTables_selectorFree
    (argument : LookupArgument Fp) :
    argument.tables.Forall Expression.SelectorFree :=
  List.forall_iff_forall_mem.mpr
    (fun table htable => argument.tablesFree table htable)

/--
The exact selector-substitution facts needed by one enabled lookup.

This is stronger than gate activation realization: every source expression must
evaluate with the packed-selector substitution exactly as it does with the
operation's zero/one selector valuation. Tables usually discharge the second
field structurally because Halo 2 tables are selector-free.
-/
structure EnabledLookup.SelectorProjection
    (top : TopLevelCircuit Fp Config PublicInput)
    (environment : Environment Fp) (lookup : EnabledLookup Fp) : Prop where
  input :
    lookup.argument.inputs.map
        (Expression.eval
          (substValuation top.selectorMap.lookup
            (Query.eval environment (fun _ => 0)
              (top.placement lookup.region + lookup.row)))) =
      lookup.inputValues top.placement environment
  table : ∀ row < environment.usableRows,
    lookup.argument.tables.map
        (Expression.eval
          (substValuation top.selectorMap.lookup
            (Query.eval environment (fun _ => 0) row))) =
      lookup.tableValues environment row

/--
Selector-free expressions cannot distinguish selector substitution from an
arbitrary selector valuation. Fixed, advice, and instance queries retain the
same environment and row on both sides.
-/
theorem Expression.eval_substValuation_eq_queryEval_of_selectorFree
    (map : SelCompressMap) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℕ)
    (expression : Expression Fp Query)
    (hfree : expression.SelectorFree) :
    expression.eval
        (substValuation map.lookup
          (Query.eval environment (fun _ => 0) row)) =
      expression.eval (Query.eval environment selectors row) := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp [Expression.SelectorFree] at hfree
      | fixed column rotation =>
          rfl
      | advice column rotation =>
          rfl
      | «instance» column rotation =>
          rfl
  | const value =>
      rfl
  | add left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.eval, ihLeft hfree.1, ihRight hfree.2]
  | mul left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [Expression.eval, ihLeft hfree.1, ihRight hfree.2]

/--
At one enabled lookup's input row, selector substitution agrees with the
operation's zero/one selector valuation on every input expression.

This deliberately does not require the two valuations to agree on unrelated
selectors. A gate selector can legitimately be active on the same absolute row
without occurring in this lookup's inputs.
-/
def EnabledLookup.InputSelectorValuesRealized
    (top : TopLevelCircuit Fp Config PublicInput)
    (environment : Environment Fp) (lookup : EnabledLookup Fp) : Prop :=
  ∀ expression ∈ lookup.argument.inputs,
    expression.eval
        (substValuation top.selectorMap.lookup
          (Query.eval environment (fun _ => 0)
            (top.placement lookup.region + lookup.row))) =
      expression.eval
        (Query.eval environment lookup.selectorValue
          (top.placement lookup.region + lookup.row))

namespace EnabledLookup.SelectorProjection

/--
Exact selector values at the activation row, together with selector-free table
expressions, supply the full lookup selector-projection boundary.
-/
theorem ofInputSelectorValues
    (environment : Environment Fp)
    (lookup : EnabledLookup Fp)
    (realized :
      lookup.InputSelectorValuesRealized top environment)
    (tablesFree :
      lookup.argument.tables.Forall Expression.SelectorFree) :
    lookup.SelectorProjection top environment := by
  constructor
  · unfold EnabledLookup.inputValues
    apply List.map_congr_left
    intro expression hexpression
    exact realized expression hexpression
  · intro row hrow
    unfold EnabledLookup.tableValues
    apply List.map_congr_left
    intro expression hexpression
    exact
      Expression.eval_substValuation_eq_queryEval_of_selectorFree
        top.selectorMap environment lookup.selectorValue row expression
        (List.forall_iff_forall_mem.mp tablesFree expression hexpression)

end EnabledLookup.SelectorProjection

namespace TopLevelGateCoherence

/--
Every synthesis-enabled lookup was present in the raw configure result. The equality
field makes the synthesis-closure membership proof transport back to Halo 2's actual
configuration boundary.
-/
theorem enabledLookup_configured
    (coherence : TopLevelGateCoherence top)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0) :
    lookup.argument ∈
      (top.formalCircuit.configure () {}).2.lookups := by
  rw [← coherence.lookups_eq_configure]
  exact OperationsKeygenCoherent.lookup top.keygenCoherent henabled

/-- The resolver feeds interpret the complete circuit-derived pinned query state. -/
theorem resolverInterpretsPinned
    (coherence : TopLevelGateCoherence top)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (usableRows row : ℕ) :
    Interprets
      (pinnedQueryState top.pinnedCS)
      (fun query =>
        (fixedQueryFeedOfResolver
          (top.toVerifierKey urs) poly query).eval
          (top.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (Query.eval
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex usableRows)
        (fun _ => 0) row) := by
  have homega : top.omega ≠ 0 := by
    have hk : top.domainExponent ≤ 32 :=
      Nat.le_of_lt_succ (by
        simpa using coherence.domainExponent_lt)
    exact top.omega_ne_zero hk
  exact resolverQueryFeeds_interpret
    (top.toVerifierKey urs) poly proofIndex usableRows
    (fun _ => 0) row homega
    (pinnedQueryState top.pinnedCS)
    (by
      simp only [top.toVerifierKey_adviceQueryLayout,
        TopLevelCircuit.adviceQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_fixedQueryLayout,
        TopLevelCircuit.fixedQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_instanceQueryLayout,
        TopLevelCircuit.instanceQueryLayout, pinnedQueryState])
    (top.toVerifierKey_adviceQueryCount urs)
    (top.toVerifierKey_fixedQueryCount urs)
    (top.toVerifierKey_instanceQueryCount urs)

end TopLevelGateCoherence

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

/-- Selector-free lookup tables are covered by every compression map. -/
theorem tablesCovered
    (argument : LookupArgument Fp)
    (expression : Expression Fp Query)
    (hexpression : expression ∈ argument.tables) :
    expression.selectorsCovered
      (fun selector =>
        (top.selectorMap.lookup selector).isSome) = true :=
  Expression.selectorsCovered_of_selectorFree
    (fun selector =>
      (top.selectorMap.lookup selector).isSome)
    expression
    (List.forall_iff_forall_mem.mp
      (lookupTables_selectorFree argument)
      expression hexpression)

/--
The circuit-derived verifying key's selected lookup tuples evaluate like the
enabled Clean lookup's concrete input and table tuples.
-/
theorem projectedValues
    (gateCoherence : TopLevelGateCoherence top)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    let route := lookup.topLevelRoute (top := top) henabled
    let environment :=
      resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    ((top.verifierCS.lookupInputExprs route.index).map
        (Expr.eval
          (fun query =>
            (fixedQueryFeedOfResolver
              (top.toVerifierKey urs) poly query).eval
              (top.omega ^
                (top.placement lookup.region + lookup.row)))
          (fun query =>
            (adviceQueryFeedOfResolver
              (top.toVerifierKey urs) poly proofIndex query).eval
              (top.omega ^
                (top.placement lookup.region + lookup.row)))
          (fun query =>
            (instanceQueryFeedOfResolver
              (top.toVerifierKey urs) poly proofIndex query).eval
              (top.omega ^
                (top.placement lookup.region + lookup.row)))) =
      lookup.inputValues top.placement environment) ∧
    (∀ row < environment.usableRows,
      (top.verifierCS.lookupTableExprs route.index).map
          (Expr.eval
            (fun query =>
              (fixedQueryFeedOfResolver
                (top.toVerifierKey urs) poly query).eval
                (top.omega ^ row))
            (fun query =>
              (adviceQueryFeedOfResolver
                (top.toVerifierKey urs) poly proofIndex query).eval
                (top.omega ^ row))
            (fun query =>
              (instanceQueryFeedOfResolver
                (top.toVerifierKey urs) poly proofIndex query).eval
                (top.omega ^ row))) =
        lookup.tableValues environment row) := by
  dsimp only
  let route :=
    lookup.topLevelRoute (top := top) henabled
  have hlookupConfigured :=
    gateCoherence.enabledLookup_configured lookup henabled
  have hlookupClosed :
      lookup.argument ∈ top.constraintSystem.lookups := by
    rw [gateCoherence.lookups_eq_configure]
    exact hlookupConfigured
  have hrouteMem :
      top.constraintSystem.lookups[route.index.val] ∈
        top.constraintSystem.lookups := by
    rw [route.argument]
    exact hlookupClosed
  have hinputCoverage :=
    topLevelLookupInputs_selectorsCovered top
      top.constraintSystem.lookups[route.index.val]
      hrouteMem
  have htableCoverage :=
    tablesCovered (top := top)
      top.constraintSystem.lookups[route.index.val]
  have projectAt (row : ℕ) :=
    top.lookup_eval
      (fun query =>
        (fixedQueryFeedOfResolver
          (top.toVerifierKey urs) poly query).eval
          (top.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (Query.eval
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (fun _ => 0) row)
      route.index
      hinputCoverage htableCoverage
      (gateCoherence.resolverInterpretsPinned
        (pp := pp) (urs := urs)
        poly proofIndex
        (top.usableRowsAt top.domainExponent) row)
  have inputProjected :=
    (projectAt
      (top.placement lookup.region + lookup.row)).1
  have tableProjected (row : ℕ) :=
    (projectAt row).2
  have hargument := route.argument
  have inputProjected' :=
    inputProjected.trans
      (congrArg
        (fun argument : LookupArgument Fp =>
          argument.inputs.map
            (Expression.eval
              (substValuation top.selectorMap.lookup
                (Query.eval
                  (resolverEnvironment
                    (top.toVerifierKey urs) poly proofIndex
                    (top.usableRowsAt top.domainExponent))
                  (fun _ => 0)
                  (top.placement lookup.region + lookup.row)))))
        hargument)
  constructor
  · rw [← selectors.input]
    rw [top.verifierCS_lookupInputExprs, map_eval_toExpr]
    simpa only [route, Nat.cast_add] using
      inputProjected'
  · intro row hrow
    have tableProjectedRow :=
      (tableProjected row).trans
        (congrArg
          (fun argument : LookupArgument Fp =>
            argument.tables.map
              (Expression.eval
                (substValuation top.selectorMap.lookup
                  (Query.eval
                    (resolverEnvironment
                      (top.toVerifierKey urs) poly proofIndex
                      (top.usableRowsAt top.domainExponent))
                    (fun _ => 0) row))))
          hargument)
    rw [← selectors.table row hrow]
    rw [top.verifierCS_lookupTableExprs, map_eval_toExpr]
    simpa only [route] using tableProjectedRow

/--
The resolver's compressed input and table polynomials evaluate to the concrete
Clean tuples compressed with the transcript challenge.
-/
theorem projectedPolynomialValues
    {k : ℕ}
    (gateCoherence : TopLevelGateCoherence top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    let route := lookup.topLevelRoute (top := top) henabled
    let environment :=
      resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    (lookupInputPolyOfResolver
        (top.toVerifierKey urs) ch poly proofIndex route.index).eval
        (top.omega ^
          (top.placement lookup.region + lookup.row)) =
      compressValues ch.theta
        (lookup.inputValues top.placement environment) ∧
    (∀ row < environment.usableRows,
      (lookupTablePolyOfResolver
          (top.toVerifierKey urs) ch poly proofIndex route.index).eval
          (top.omega ^ row) =
        compressValues ch.theta
          (lookup.tableValues environment row)) := by
  dsimp only
  let route :=
    lookup.topLevelRoute (top := top) henabled
  have projected :=
    projectedValues gateCoherence poly proofIndex
      lookup henabled selectors
  constructor
  · rw [lookupInputPolyOfResolver_eq,
      compress_eval_eq_foldPoly,
      eval_foldPoly_eq_compressValues]
    change compressValues ch.theta
        ((top.verifierCS.lookupInputExprs
          route.index).map _) =
      compressValues ch.theta
        (lookup.inputValues top.placement
          (resolverEnvironment
            (top.toVerifierKey urs) poly proofIndex
            (top.usableRowsAt top.domainExponent)))
    exact congrArg (compressValues ch.theta) projected.1
  · intro row hrow
    rw [lookupTablePolyOfResolver_eq,
      compress_eval_eq_foldPoly,
      eval_foldPoly_eq_compressValues]
    change compressValues ch.theta
        ((top.verifierCS.lookupTableExprs
          route.index).map _) =
      compressValues ch.theta
        (lookup.tableValues
          (resolverEnvironment
            (top.toVerifierKey urs) poly proofIndex
            (top.usableRowsAt top.domainExponent)) row)
    exact congrArg (compressValues ch.theta)
      (projected.2 row hrow)

/--
Full constraint satisfaction constructs the deployed lookup witness once the
static projection, exact selector values, row fit, and explicitly priced
challenge exclusions are supplied.
-/
def deployedWitness
    {k : ℕ}
    (gateCoherence : TopLevelGateCoherence top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (selectors :
      lookup.SelectorProjection top
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (activationRow :
      top.placement lookup.region + lookup.row <
        top.usableRowsAt top.domainExponent)
    (resolverGood :
      let route := lookup.topLevelRoute (top := top) henabled
      ResolverLookupGoodChallenges
        (top.toVerifierKey urs) ch poly proofIndex route.index
        (top.n -
          top.blindingFactors - 2))
    (thetaGood :
      ch.theta ∉ lookup.thetaBadSet top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))) :
    lookup.DeployedWitness top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
  ch.theta := by
  let vk := top.toVerifierKey urs
  let environment :=
    resolverEnvironment vk poly proofIndex
      (top.usableRowsAt top.domainExponent)
  let route :=
    lookup.topLevelRoute (top := top) henabled
  let u := vk.n - vk.blindingFactors - 2
  have hn : vk.n = top.n := by
    simpa only [vk] using top.toVerifierKey_n urs
  have homega : vk.omega = top.omega := by
    simpa only [vk] using top.toVerifierKey_omega urs
  have hblinding :
      vk.blindingFactors = top.blindingFactors := by
    simpa only [vk] using top.toVerifierKey_blindingFactors urs
  have hu :
      u = top.n - top.blindingFactors - 2 := by
    simp only [u, hn, hblinding]
  have husable :
      vk.blindingFactors + 1 < vk.n := by
    rw [hn, hblinding]
    exact top.blindingFactors_succ_lt_domainSize
  have husableRows : environment.usableRows = u + 1 := by
    simp only [environment, resolverEnvironment,
      polynomialEnvironment_usableRows]
    rw [hu, top.usableRowsAt_domainExponent]
    omega
  have hrows : Function.Injective
      fun row : Fin top.n =>
        top.omega ^ (row : ℕ) :=
    TopLevelAssignment.domainRowsInjective
      gateCoherence.domainExponent_lt
  have hroot :
      top.omega ^ top.n = 1 :=
    TopLevelAssignment.domainRoot
      gateCoherence.domainExponent_lt
  have projected :=
    projectedPolynomialValues gateCoherence ch poly
      proofIndex lookup henabled selectors
  have harity' :
      lookup.argument.inputs.length =
        lookup.argument.tables.length :=
    lookup.argument.arity
  have tupleLength : ∀ row < environment.usableRows,
      (lookup.inputValues top.placement environment).length =
        (lookup.tableValues environment row).length := by
    intro row _
    unfold EnabledLookup.inputValues EnabledLookup.tableValues
    simpa only [List.length_map] using harity'
  let canonical :=
    canonicalLagrangePolynomials vk.omega
      (Nat.lt_of_succ_lt husable)
  have hrows' : Function.Injective
      fun row : Fin vk.n =>
        vk.omega ^ (row : ℕ) := by
    simpa only [hn, homega] using hrows
  have hroot' :
      vk.omega ^ vk.n = 1 := by
    simpa only [hn, homega] using hroot
  have domain :
      ResolverLookupDomain vk canonical.1 canonical.2.1 canonical.2.2
        vk.n u := by
    simpa only [canonical] using
      ResolverLookupDomain.ofCanonicalPolynomials
        vk husable hrows' hroot'
  have satisfactionAtVk :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly) vk.n := by
    simpa only [hn] using satisfaction
  have satisfaction' :
      ConstraintSatisfaction
        (constraintModelOfResolver (numProofs := pp.numProofs) vk ch poly
          (permutationSetsOfResolver (numProofs := pp.numProofs) vk poly)
          (permutationChunksOfResolver (numProofs := pp.numProofs) vk poly)
          canonical.1 canonical.2.1 canonical.2.2) vk.n := by
    rw [top.constraintModel_eq_constraintModelOfResolver] at satisfactionAtVk
    simpa only [vk, canonical] using satisfactionAtVk
  have scalarSubset :
      ∀ row : Fin (u + 1), ∃ tableRow : Fin (u + 1),
        lookupColumnRows vk.omega
            (lookupInputPolyOfResolver
              vk ch poly proofIndex route.index)
            (u + 1) row =
          lookupColumnRows vk.omega
            (lookupTablePolyOfResolver
              vk ch poly proofIndex route.index)
            (u + 1) tableRow := by
    exact satisfaction'.resolverLookupSubset
      vk ch poly
      (permutationSetsOfResolver (numProofs := pp.numProofs) vk poly)
      (permutationChunksOfResolver (numProofs := pp.numProofs) vk poly)
      canonical.1 canonical.2.1 canonical.2.2 proofIndex route.index
      domain (by simpa only [hu] using resolverGood)
  simpa only [vk, environment] using
    { omega := vk.omega
      input :=
        lookupInputPolyOfResolver vk ch poly
          proofIndex route.index
      table :=
        lookupTablePolyOfResolver vk ch poly
          proofIndex route.index
      u := u
      usableRows := husableRows
      activationRow := by
        rw [← husableRows]
        exact activationRow
      inputEval := by
        simpa only [homega] using projected.1.symm
      tableEval := fun row hrow =>
        by simpa only [homega] using (projected.2 row hrow).symm
      tupleLength := tupleLength
      scalarSubset := scalarSubset
      thetaGood := thetaGood }

/--
The proof-dependent conditions shared by the deployed witnesses for every lookup
activation in one proof. Static configured-lookup coverage, arity, and activation-row
fit are derived from the top-level circuit; this record contains only selector- and
challenge-dependent facts.
-/
structure WitnessConditions
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) : Prop where
  inputSelectorValues : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    lookup.InputSelectorValuesRealized top
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
  resolverGood : ∀ lookup
      (henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    ResolverLookupGoodChallenges
      (top.toVerifierKey urs) ch poly proofIndex
      (lookup.topLevelRoute (top := top) henabled).index
      (top.n -
        top.blindingFactors - 2)
  thetaGood : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
    ch.theta ∉ lookup.thetaBadSet top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))

/--
Index every lookup activation in every proof of a top-level bundle. The activation
list is shared by all proofs, while the resolver environment is proof-indexed.
-/
abbrev ActivationIndex
    (top : TopLevelCircuit Fp Config PublicInput)
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
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly) :
    Option (PLift (ChallengeExclusions top pp urs ch poly)) :=
  let vk := top.toVerifierKey urs
  let u := vk.n - vk.blindingFactors - 2
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
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (hexclusions : ChallengeExclusions top pp urs ch poly) :
    (topLevelLookupChallengeExclusions? top pp urs ch poly).isSome := by
  let vk := top.toVerifierKey urs
  let u := vk.n - vk.blindingFactors - 2
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

/--
Bundle-wide challenge exclusions and exact selector realization construct the
per-proof conditions consumed by the deployed lookup witnesses.
-/
def WitnessConditions.ofChallengeExclusions
    {k : ℕ}
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (inputSelectorValues : ∀ lookup
      (_henabled :
        lookup ∈ operationEnabledLookups (top.operations) 0),
      lookup.InputSelectorValuesRealized top
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (exclusions :
      ChallengeExclusions top pp urs ch poly) :
    WitnessConditions top pp urs ch poly proofIndex := by
  refine
    { inputSelectorValues := inputSelectorValues
      resolverGood := ?_
      thetaGood := ?_ }
  · intro lookup henabled
    exact resolverLookupGoodChallenges_of_not_mem
      pp.numProofs (top.toVerifierKey urs) ch poly
      (top.n -
        top.blindingFactors - 2)
      exclusions.gamma exclusions.beta proofIndex
      (lookup.topLevelRoute (top := top) henabled).index
  · intro lookup henabled
    obtain ⟨index, hindex, hlookup⟩ :=
      List.mem_iff_getElem.mp henabled
    have hfamily :=
      (not_mem_enabledLookupThetaBadSetFamily_iff
        (ι := ActivationIndex top pp)
        (fun _ => top.placement)
        (fun index =>
          resolverEnvironment
            (top.toVerifierKey urs) poly index.1
            (top.usableRowsAt top.domainExponent))
        (fun index =>
          (operationEnabledLookups (top.operations) 0).get index.2)
        ch.theta).mp exclusions.theta
        (proofIndex, ⟨index, hindex⟩)
    simpa [thetaBadSet, hlookup] using hfamily

/-- Construct the complete deployed-witness family for one top-level proof. -/
def deployedWitnesses
    {k : ℕ}
    (gateCoherence : TopLevelGateCoherence top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (conditions :
      WitnessConditions top pp urs ch poly proofIndex) :
    ∀ lookup ∈ operationEnabledLookups (top.operations) 0,
      lookup.DeployedWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        ch.theta := by
  intro lookup henabled
  let environment :=
    resolverEnvironment
      (top.toVerifierKey urs) poly proofIndex
      (top.usableRowsAt top.domainExponent)
  have selectorProjection :
      lookup.SelectorProjection top environment :=
    EnabledLookup.SelectorProjection.ofInputSelectorValues
      environment lookup
      (conditions.inputSelectorValues lookup henabled)
      (lookupTables_selectorFree lookup.argument)
  exact deployedWitness gateCoherence ch poly proofIndex
    satisfaction lookup henabled
    selectorProjection
    (lookup.activationRow_lt_usableRows henabled)
    (conditions.resolverGood lookup henabled)
    (conditions.thetaGood lookup henabled)

/-- The deployed family discharges Clean's complete lookup constraint family. -/
theorem constraints
    {k : ℕ}
    (gateCoherence : TopLevelGateCoherence top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (conditions :
      WitnessConditions top pp urs ch poly proofIndex) :
    CircuitConstraintFamily.constraints .lookup top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 := by
  apply lookup_constraints_of_deployed_witnesses
  exact deployedWitnesses gateCoherence ch poly proofIndex
    satisfaction conditions

end TopLevelLookup

end Zcash.Snark

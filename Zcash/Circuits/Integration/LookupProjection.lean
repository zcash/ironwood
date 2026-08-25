import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Lookup projection across the Clean boundary

Key generation substitutes the circuit's virtual selectors, then resolves each
configured `LookupArgument` against the authoritative compiler-derived query layout.
This module proves the semantic part of that translation for one selected lookup.

The result deliberately stops at the selector-substitution valuation. A lookup
activation needs the stronger row fact that its complex selectors have their exact
zero/one values; unlike a custom gate, an arbitrary nonzero selector scale is not
enough for tuple membership.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- A selected pinned lookup evaluates like its selector-substituted source argument
whenever all of that argument's queries resolve against the compiler layout. -/
theorem PinnedConstraintSystem.derive_lookup_eval
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookupIndex : ℕ) (hlookup : lookupIndex < cs.lookups.length)
    (hinputCoverage :
      ∀ expression ∈ cs.lookups[lookupIndex].inputs,
        expression.selectorsCovered
          (fun selector => (map.lookup selector).isSome) = true)
    (htableCoverage :
      ∀ expression ∈ cs.lookups[lookupIndex].tables,
        expression.selectorsCovered
          (fun selector => (map.lookup selector).isSome) = true)
    (hinputResolved :
      (cs.lookups[lookupIndex].inputs.map
        (substSelectorMap map.lookup)).Forall
          (·.QueriesResolved (queryWalkInit map cs)))
    (htableResolved :
      (cs.lookups[lookupIndex].tables.map
        (substSelectorMap map.lookup)).Forall
          (·.QueriesResolved (queryWalkInit map cs)))
    (hinterprets :
      Interprets
        (pinnedQueryState (PinnedConstraintSystem.derive cs map))
        fixed advice instanceFeed valuation) :
    (((PinnedConstraintSystem.derive cs map).lookupInputExprs.getD
        lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      cs.lookups[lookupIndex].inputs.map
        (Expression.eval
          (substValuation map.lookup valuation))) ∧
    (((PinnedConstraintSystem.derive cs map).lookupTableExprs.getD
        lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      cs.lookups[lookupIndex].tables.map
        (Expression.eval
          (substValuation map.lookup valuation))) := by
  let argument := cs.lookups[lookupIndex]
  have hinterpretsQueries :
      Interprets (queryWalkInit map cs)
        fixed advice instanceFeed valuation := by
    rw [← PinnedConstraintSystem.derive_queryState_eq cs map]
    exact hinterprets
  have hinputFree :
      ∀ expression ∈ argument.inputs.map
          (substSelectorMap map.lookup),
        expression.SelectorFree := by
    intro expression hexpression
    obtain ⟨source, hsource, hexpression⟩ := List.mem_map.mp hexpression
    subst expression
    exact (substSelectorMap_selectorFree _ source).2
      (hinputCoverage source hsource)
  have htableFree :
      ∀ expression ∈ argument.tables.map
          (substSelectorMap map.lookup),
        expression.SelectorFree := by
    intro expression hexpression
    obtain ⟨source, hsource, hexpression⟩ := List.mem_map.mp hexpression
    subst expression
    exact (substSelectorMap_selectorFree _ source).2
      (htableCoverage source hsource)
  have hinputs := eraseGates_eval fixed advice instanceFeed valuation
    (argument.inputs.map (substSelectorMap map.lookup))
    (queryWalkInit map cs) hinputFree
    (List.forall_iff_forall_mem.mp hinputResolved) hinterpretsQueries
  have htables := eraseGates_eval fixed advice instanceFeed valuation
    (argument.tables.map (substSelectorMap map.lookup))
    (queryWalkInit map cs) htableFree
    (List.forall_iff_forall_mem.mp htableResolved) hinterpretsQueries
  have hpinnedInputs :
      (PinnedConstraintSystem.derive cs map).lookupInputExprs.getD
          lookupIndex [] =
        eraseGates
          (argument.inputs.map (substSelectorMap map.lookup))
          (queryWalkInit map cs) := by
    simpa only [argument] using
      PinnedConstraintSystem.derive_lookupInputExprs_getD
        cs map lookupIndex hlookup
  have hpinnedTables :
      (PinnedConstraintSystem.derive cs map).lookupTableExprs.getD
          lookupIndex [] =
        eraseGates
          (argument.tables.map (substSelectorMap map.lookup))
          (queryWalkInit map cs) := by
    simpa only [argument] using
      PinnedConstraintSystem.derive_lookupTableExprs_getD
        cs map lookupIndex hlookup
  constructor
  · rw [hpinnedInputs]
    apply List.ext_getElem
    · simp only [List.length_map, eraseGates_length, argument]
    · intro index hleft hright
      simp only [List.getElem_map]
      have heval := hinputs index (by simpa using hleft) (by simpa using hright)
      rw [List.getElem_map, substSelectorMap_eval] at heval
      exact heval
  · rw [hpinnedTables]
    apply List.ext_getElem
    · simp only [List.length_map, eraseGates_length, argument]
    · intro index hleft hright
      simp only [List.getElem_map]
      have heval := htables index (by simpa using hleft) (by simpa using hright)
      rw [List.getElem_map, substSelectorMap_eval] at heval
      exact heval

/-- Project one lookup directly through a top-level circuit's owned compilation. -/
theorem _root_.Halo2.TopLevelCircuit.lookup_eval
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookup : Fin top.lookupCount)
    (hinputCoverage :
      ∀ expression ∈ (top.lookupAt lookup).inputs,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (htableCoverage :
      ∀ expression ∈ (top.lookupAt lookup).tables,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (hinterprets :
      Interprets (pinnedQueryState top.pinnedCS)
        fixed advice instanceFeed valuation) :
    ((top.pinnedCS.lookupInputExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.lookupAt lookup).inputs.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) ∧
    ((top.pinnedCS.lookupTableExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.lookupAt lookup).tables.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) := by
  have hlookup : lookup.val < top.constraintSystem.lookups.length := by
    rw [← top.lookupCount_eq_constraintSystem]
    exact lookup.isLt
  let argument := top.lookupAt lookup
  have hargument : argument ∈ top.constraintSystem.lookups :=
    top.lookupAt_mem_constraintSystem lookup
  have hresolved := top.lookupQueriesResolved argument hargument
  exact PinnedConstraintSystem.derive_lookup_eval
    top.constraintSystem top.selectorMap fixed advice instanceFeed valuation
    lookup.val hlookup hinputCoverage htableCoverage hresolved.1 hresolved.2
    hinterprets

end Zcash.Snark

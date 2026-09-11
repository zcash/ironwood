import Zcash.Circuits.Halo2.LookupOperations
import Zcash.Circuits.Halo2.SelectorCompression
import Zcash.Circuits.Halo2.FixedValues

/-! # Exact lookup selector substitution in the circuit-owned environment -/

namespace Zcash.Snark

open Halo2

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  {top : TopLevelCircuit Fp Config PublicInput} [TopLevelShape top]

/-- A synthesis-enabled lookup routed to its configured lookup index. -/
structure EnabledLookup.TopLevelRoute
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (lookup : EnabledLookup Fp) where
  index : Fin top.lookupCount
  argument : top.lookupAt index = lookup.argument

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
      argument := ?_ }
  · rw [top.lookupCount_eq_constraintSystem]
    exact hindex
  · unfold TopLevelCircuit.lookupAt
    exact hget

omit [TopLevelShape top] in
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

The formal circuit's registration laws bound selector indices, and the generic
selector compiler turns that bound into coverage by the compression map.
-/
theorem topLevelLookupInputs_selectorsCovered
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
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

end TopLevelLookup

/-- Substitution only needs to agree on selector indices occurring in the expression. -/
theorem Expression.eval_substValuation_eq_of_selectorIndices
    (map : SelCompressMap) (env : Environment Fp) (selectors : ℕ → Fp) (row : ℤ)
    (expression : Expression Fp Query)
    (hagrees : ∀ selector, selector.index ∈ expression.selectorIndices →
      substValuation map.lookup (Query.eval env (fun _ => 0) row) (.selector selector) =
        selectors selector.index) :
    expression.eval (substValuation map.lookup (Query.eval env (fun _ => 0) row)) =
      expression.eval (Query.eval env selectors row) := by
  induction expression with
  | var query =>
      cases query with
      | selector selector => exact hagrees selector (List.mem_singleton_self _)
      | fixed | advice | «instance» => rfl
  | const => rfl
  | add left right ihLeft ihRight | mul left right ihLeft ihRight =>
      have hleft := ihLeft (fun selector h => hagrees selector (List.mem_append_left _ h))
      have hright := ihRight (fun selector h => hagrees selector (List.mem_append_right _ h))
      simp only [Expression.eval, hleft, hright]

/-- Singleton packing and the circuit-owned fixed columns realize every selector
used by an activated lookup, independently of the proving assignment. -/
theorem EnabledLookup.inputValues_eq
    (lookup : EnabledLookup Fp)
    (henabled : lookup ∈ operationEnabledLookups top.operations 0)
    (assignment : ProofAssignment Fp) :
    lookup.argument.inputs.map (Expression.eval (substValuation top.selectorMap.lookup
      (Query.eval (top.environment assignment) (fun _ => 0)
        (top.placement lookup.region + lookup.row : ℕ)))) =
      lookup.inputValues top.placement (top.environment assignment) := by
  obtain ⟨body, hregion, hlookup⟩ :=
    (mem_operationEnabledLookups_iff lookup top.operations 0).mp henabled
  have hargument := OperationsKeygenCoherent.lookup top.keygenCoherent henabled
  apply List.map_congr_left
  intro expression hexpression
  apply Expression.eval_substValuation_eq_of_selectorIndices
  intro selector hselector
  obtain ⟨compressed, hmap, hlength, hroot, _, hvalue⟩ :=
    top.lookupInputSelectorFixedValue hregion hlookup hargument
      expression hexpression selector.index hselector
  have hrow : top.placement lookup.region + lookup.row < top.n :=
    (lookup.activationRow_lt_usableRows henabled).trans_le
      top.usableRowsAt_domainExponent_le_n
  have hsingle : (selReplacement compressed).eval
      (Query.eval (top.environment assignment) (fun _ => 0)
        (top.placement lookup.region + lookup.row : ℕ)) =
      (top.environment assignment).fixed ⟨compressed.packedCol⟩
        (top.placement lookup.region + lookup.row : ℕ) := by
    rcases compressed with ⟨column, length, root⟩
    simp only at hlength hroot
    subst length
    subst root
    rfl
  simp only [substValuation, hmap]
  rw [hsingle, TopLevelCircuit.environment_fixed, top.fixedValue_eq_fixedRows_getD]
  rw [Int.natMod, ← Int.natCast_mod, Int.toNat_natCast, Nat.mod_eq_of_lt hrow]
  simpa only [TopLevelCircuit.placement_apply, EnabledLookup.selectorValue] using hvalue

end Zcash.Snark

import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Snark.ZeroKnowledge.ActivationTrace
import Zcash.Circuits.Utilities.LookupRangeCheck

/-!
# Exact activation traces of the range-check gadgets

Both running-sum selectors are retained at every running row. Short checks enable
the lookup selector twice and the bitshift gate at the second row. These source
equations do not depend on witness values or on the strict-tail constraint.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
Unlike the gate gadgets, what these enable is mostly lookups, so an activation keeps the lookup
argument that a selector label discards.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The lookup activation at each row of a running-sum check, enabling both running selectors. -/
def runningActivations {K : ℕ} (config : LookupRangeCheck.Config K) (offset count : ℕ) :
    List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin count =>
    [RegionOperation.enableLookup (LookupRangeCheck.rangeCheckLookup K config)
      [config.qLookup, config.qRunning] (offset + i.val)]).flatten

/-- The two selector activations at each row of a running-sum check. -/
def runningSelectorTrace {K : ℕ} (config : LookupRangeCheck.Config K) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qLookup.index, offset + i.val), (config.qRunning.index, offset + i.val)]).flatten

/-- A run of range-check activations projects to the matching run of selector labels. -/
theorem runningActivations_selectorOf {K : ℕ} (config : LookupRangeCheck.Config K)
    (offset count : ℕ) :
    (runningActivations config offset count).flatMap selectorOf =
      runningSelectorTrace config offset count := by
  simp only [runningActivations, runningSelectorTrace, flatten_flatMap, List.map_ofFn,
    Function.comp_def, selectorOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_nil, ComplexSelector.toSelector_index]

/-- The common local trace of a witnessed short check, regardless of bit width. -/
def shortSelectorTrace {K : ℕ} (config : LookupRangeCheck.Config K) : List (ℕ × ℕ) :=
  [(config.qLookup.index, 0), (config.qLookup.index, 1), (config.qBitshift.index, 1)]

/-- One range-check round records its configured lookup at the requested row, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckRound_regionActivations (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (index row : ℕ) (region : RegionIndex) :
    regionActivations ((LookupRangeCheck.rangeCheckRound K config element index row).operations region) =
      [.enableLookup (LookupRangeCheck.rangeCheckLookup K config)
        [config.qLookup, config.qRunning] row] := rfl

@[selector_trace_norm]
theorem rangeCheckRound_regionSelectorTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (index row : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((LookupRangeCheck.rangeCheckRound K config element index row).operations region) =
      [(config.qLookup.index, row), (config.qRunning.index, row)] := rfl

/-- Range-check iterations retain their successive activation rows, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckLoop_regionActivations (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionActivations ((LookupRangeCheck.rangeCheckLoop K config element offset count).operations region) =
      runningActivations config offset count := by
  simp only [LookupRangeCheck.rangeCheckLoop, activation_trace_norm, Nat.mul_one,
    runningActivations]

@[selector_trace_norm]
theorem rangeCheckLoop_regionSelectorTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((LookupRangeCheck.rangeCheckLoop K config element offset count).operations region) =
      runningSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, rangeCheckLoop_regionActivations,
    runningActivations_selectorOf]

/-- A short range check retains its configured gate and lookup activations, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem shortRangeCheck_regionActivations (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((LookupRangeCheck.shortRangeCheck K bits).call config offset input).operations region) =
      [.enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] offset,
        .enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] (offset + 1),
        .enableGate (LookupRangeCheck.bitshiftGate K config) (offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem shortRangeCheck_regionSelectorTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.shortRangeCheck K bits).call config offset input).operations region) =
      [(config.qLookup.index, offset), (config.qLookup.index, offset + 1),
        (config.qBitshift.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A running range check retains its complete configured activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheck_regionActivations (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    regionActivations (((LookupRangeCheck.rangeCheck K count strict).call config offset input).operations region) =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((LookupRangeCheck.rangeCheckBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckBody, activation_trace_norm, Bool.false_eq_true,
      if_false, if_true]

@[selector_trace_norm]
theorem rangeCheck_regionSelectorTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheck K count strict).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, rangeCheck_regionActivations, runningActivations_selectorOf]

/-- Placing a range check shifts its activation rows by the supplied offset, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckAt_regionActivations (K count : ℕ) (strict : Bool)
    (hstrict : strict = true → 0 < count) (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((LookupRangeCheck.rangeCheckAt K count strict hstrict).call config offset input).operations region) =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((LookupRangeCheck.rangeCheckAtBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckAtBody, activation_trace_norm, Bool.false_eq_true,
      if_false, if_true]

@[selector_trace_norm]
theorem rangeCheckAt_regionSelectorTrace (K count : ℕ) (strict : Bool)
    (hstrict : strict = true → 0 < count) (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheckAt K count strict hstrict).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, rangeCheckAt_regionActivations,
    runningActivations_selectorOf]

/-- A decomposed range check retains the activations at its supplied offset, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckAtDecomposed_regionActivations (count : ℕ) (hcount : 13 ≤ count)
    (hpow : 10 * count ≤ 254) (config : LookupRangeCheck.Config 10) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((LookupRangeCheck.rangeCheckAtDecomposed count hcount hpow).call config offset input).operations region) =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((LookupRangeCheck.rangeCheckAtDecomposedBody count config offset input).operations region) = _
  simp only [LookupRangeCheck.rangeCheckAtDecomposedBody, activation_trace_norm]

@[selector_trace_norm]
theorem rangeCheckAtDecomposed_regionSelectorTrace (count : ℕ) (hcount : 13 ≤ count)
    (hpow : 10 * count ≤ 254) (config : LookupRangeCheck.Config 10) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheckAtDecomposed count hcount hpow).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [regionSelectorTrace_eq_project, rangeCheckAtDecomposed_regionActivations,
    runningActivations_selectorOf]

/-- Copying into a range check retains its region trace, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem copyCheck_activationTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    activationTrace (((LookupRangeCheck.copyCheck K count strict).call config input).operations region) =
      [runningActivations config 0 count] := by
  simp only [LookupRangeCheck.copyCheck, activation_trace_norm]

@[selector_trace_norm]
theorem copyCheck_selectorTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((LookupRangeCheck.copyCheck K count strict).call config input).operations region) =
      [runningSelectorTrace config 0 count] := by
  simp only [LookupRangeCheck.copyCheck, selector_trace_norm]

/-- A witnessed short check has one region with its two lookups and bitshift gate. -/
@[activation_trace_norm]
theorem witnessShortCheck_activationTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    activationTrace ((LookupRangeCheck.witnessShortCheck K bits config witness).operations region) =
      [[.enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 0,
        .enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 1,
        .enableGate (LookupRangeCheck.bitshiftGate K config) 1]] := by
  simp only [LookupRangeCheck.witnessShortCheck, activation_trace_norm]

@[selector_trace_norm]
theorem witnessShortCheck_selectorTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    selectorTrace ((LookupRangeCheck.witnessShortCheck K bits config witness).operations region) =
      [[(config.qLookup.index, 0), (config.qLookup.index, 1), (config.qBitshift.index, 1)]] := by
  simp only [LookupRangeCheck.witnessShortCheck, selector_trace_norm]

/-- Witnessing into a range check retains its region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem witnessCheck_activationTrace (K count : ℕ) (strict : Bool) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (hstrict : strict = true → 0 < count) (region : RegionIndex) :
    activationTrace ((LookupRangeCheck.witnessCheck K count strict config witness hstrict).operations region) =
      [runningActivations config 0 count] := by
  simp only [LookupRangeCheck.witnessCheck, activation_trace_norm]

@[selector_trace_norm]
theorem witnessCheck_selectorTrace (K count : ℕ) (strict : Bool) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (hstrict : strict = true → 0 < count) (region : RegionIndex) :
    selectorTrace ((LookupRangeCheck.witnessCheck K count strict config witness hstrict).operations region) =
      [runningSelectorTrace config 0 count] := by
  simp only [LookupRangeCheck.witnessCheck, selector_trace_norm]

/-- Witnessing a decomposed range check retains its region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem witnessCheckDecomposed_activationTrace (config : LookupRangeCheck.Config 10)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    activationTrace ((LookupRangeCheck.witnessCheckDecomposed config witness).operations region) =
      [runningActivations config 0 25] := by
  simp only [LookupRangeCheck.witnessCheckDecomposed, activation_trace_norm]

@[selector_trace_norm]
theorem witnessCheckDecomposed_selectorTrace (config : LookupRangeCheck.Config 10)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    selectorTrace ((LookupRangeCheck.witnessCheckDecomposed config witness).operations region) =
      [runningSelectorTrace config 0 25] := by
  simp only [LookupRangeCheck.witnessCheckDecomposed, selector_trace_norm]

end Zcash.Snark.ZeroKnowledge

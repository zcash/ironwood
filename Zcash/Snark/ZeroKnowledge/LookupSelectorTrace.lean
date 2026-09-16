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

/-- The common local trace of a witnessed short check, regardless of bit width: the lookup at
both rows, then the bitshift gate at the second. -/
def shortCheckActivations {K : ℕ} (config : LookupRangeCheck.Config K) :
    List (RegionOperation Fp) :=
  [.enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 0,
    .enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 1,
    .enableGate (LookupRangeCheck.bitshiftGate K config) 1]

/-- One range-check round records its configured lookup at the requested row, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckRound_regionActivations (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (index row : ℕ) (region : RegionIndex) :
    ((LookupRangeCheck.rangeCheckRound K config element index row).operations region).flatMap activationOf =
      [.enableLookup (LookupRangeCheck.rangeCheckLookup K config)
        [config.qLookup, config.qRunning] row] := rfl

/-- Range-check iterations retain their successive activation rows, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckLoop_regionActivations (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    ((LookupRangeCheck.rangeCheckLoop K config element offset count).operations region).flatMap activationOf =
      runningActivations config offset count := by
  simp only [LookupRangeCheck.rangeCheckLoop, activation_trace_norm, Nat.mul_one,
    runningActivations]

/-- A short range check retains its configured gate and lookup activations, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem shortRangeCheck_regionActivations (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    (((LookupRangeCheck.shortRangeCheck K bits).call config offset input).operations region).flatMap activationOf =
      [.enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] offset,
        .enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] (offset + 1),
        .enableGate (LookupRangeCheck.bitshiftGate K config) (offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A running range check retains its complete configured activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheck_regionActivations (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    (((LookupRangeCheck.rangeCheck K count strict).call config offset input).operations region).flatMap activationOf =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change ((LookupRangeCheck.rangeCheckBody K count strict config offset input).operations
    region).flatMap activationOf = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckBody, activation_trace_norm, Bool.false_eq_true,
      if_false, if_true]

/-- Placing a range check shifts its activation rows by the supplied offset, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckAt_regionActivations (K count : ℕ) (strict : Bool)
    (hstrict : strict = true → 0 < count) (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    (((LookupRangeCheck.rangeCheckAt K count strict hstrict).call
      config offset input).operations region).flatMap activationOf =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change ((LookupRangeCheck.rangeCheckAtBody K count strict config offset input).operations
    region).flatMap activationOf = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckAtBody, activation_trace_norm, Bool.false_eq_true,
      if_false, if_true]

/-- A decomposed range check retains the activations at its supplied offset, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem rangeCheckAtDecomposed_regionActivations (count : ℕ) (hcount : 13 ≤ count)
    (hpow : 10 * count ≤ 254) (config : LookupRangeCheck.Config 10) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    (((LookupRangeCheck.rangeCheckAtDecomposed count hcount hpow).call
      config offset input).operations region).flatMap activationOf =
      runningActivations config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change ((LookupRangeCheck.rangeCheckAtDecomposedBody count config offset input).operations
    region).flatMap activationOf = _
  simp only [LookupRangeCheck.rangeCheckAtDecomposedBody, activation_trace_norm]

/-- Copying into a range check retains its region trace, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem copyCheck_activationTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    trace activationOf (((LookupRangeCheck.copyCheck K count strict).call config input).operations region) =
      [runningActivations config 0 count] := by
  simp only [LookupRangeCheck.copyCheck, activation_trace_norm]

/-- A witnessed short check has one region with its two lookups and bitshift gate. -/
@[activation_trace_norm]
theorem witnessShortCheck_activationTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    trace activationOf ((LookupRangeCheck.witnessShortCheck K bits config witness).operations region) =
      [[.enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 0,
        .enableLookup (LookupRangeCheck.rangeCheckLookup K config) [config.qLookup] 1,
        .enableGate (LookupRangeCheck.bitshiftGate K config) 1]] := by
  simp only [LookupRangeCheck.witnessShortCheck, activation_trace_norm]

/-- Witnessing into a range check retains its region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem witnessCheck_activationTrace (K count : ℕ) (strict : Bool) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (hstrict : strict = true → 0 < count) (region : RegionIndex) :
    trace activationOf ((LookupRangeCheck.witnessCheck K count strict config witness hstrict).operations region) =
      [runningActivations config 0 count] := by
  simp only [LookupRangeCheck.witnessCheck, activation_trace_norm]

/-- Witnessing a decomposed range check retains its region trace, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem witnessCheckDecomposed_activationTrace (config : LookupRangeCheck.Config 10)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    trace activationOf ((LookupRangeCheck.witnessCheckDecomposed config witness).operations region) =
      [runningActivations config 0 25] := by
  simp only [LookupRangeCheck.witnessCheckDecomposed, activation_trace_norm]

end Zcash.Snark.ZeroKnowledge

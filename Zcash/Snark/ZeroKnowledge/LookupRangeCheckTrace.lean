import Zcash.Snark.ZeroKnowledge.LookupTracePrograms
import Zcash.Circuits.Utilities.LookupRangeCheck

/-!
# Exact lookup traces of the range-check gadgets

The range check is one of the two gadget families that enable a lookup; the other
is Sinsemilla, which looks up its generator table once per round. These equations
supply every lookup activation a circuit built from the range check contributes.
Each mirrors the corresponding selector-trace equation in `LookupSelectorTrace`,
keeping only the argument's master selector rather than the auxiliary selectors
the activation also enables.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

set_option maxRecDepth 8192

/-- One lookup activation at each row of a running-sum check. -/
def runningLookupTrace {K : ℕ} (config : LookupRangeCheck.Config K) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count => [(config.qLookup.index, offset + i.val)]).flatten

/-- The local lookup trace of a witnessed short check, regardless of bit width. -/
def shortLookupTrace {K : ℕ} (config : LookupRangeCheck.Config K) : List (ℕ × ℕ) :=
  [(config.qLookup.index, 0), (config.qLookup.index, 1)]

/-- One range-check round enables its lookup at the requested row. -/
@[lookup_trace_norm]
theorem rangeCheckRound_regionLookupTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (index row : ℕ) (region : RegionIndex) :
    regionLookupTrace ((LookupRangeCheck.rangeCheckRound K config element index row).operations region) =
      [(config.qLookup.index, row)] := rfl

/-- Range-check iterations enable the lookup at each successive row. -/
@[lookup_trace_norm]
theorem rangeCheckLoop_regionLookupTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionLookupTrace ((LookupRangeCheck.rangeCheckLoop K config element offset count).operations region) =
      runningLookupTrace config offset count := by
  simp only [LookupRangeCheck.rangeCheckLoop, lookup_trace_norm, Nat.mul_one, runningLookupTrace]

/-- A short range check enables its lookup at two successive rows. -/
@[lookup_trace_norm]
theorem shortRangeCheck_regionLookupTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((LookupRangeCheck.shortRangeCheck K bits).call config offset input).operations region) =
      [(config.qLookup.index, offset), (config.qLookup.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A running range check contributes its complete lookup trace. -/
@[lookup_trace_norm]
theorem rangeCheck_regionLookupTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    regionLookupTrace (((LookupRangeCheck.rangeCheck K count strict).call config offset input).operations region) =
      runningLookupTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((LookupRangeCheck.rangeCheckBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckBody, lookup_trace_norm, Bool.false_eq_true,
      if_false, if_true]

/-- Placing a range check shifts its lookup rows by the supplied offset. -/
@[lookup_trace_norm]
theorem rangeCheckAt_regionLookupTrace (K count : ℕ) (strict : Bool)
    (hstrict : strict = true → 0 < count) (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((LookupRangeCheck.rangeCheckAt K count strict hstrict).call config offset input).operations region) =
      runningLookupTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((LookupRangeCheck.rangeCheckAtBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckAtBody, lookup_trace_norm, Bool.false_eq_true,
      if_false, if_true]

/-- A decomposed range check contributes its lookups at the supplied offset. -/
@[lookup_trace_norm]
theorem rangeCheckAtDecomposed_regionLookupTrace (count : ℕ) (hcount : 13 ≤ count)
    (hpow : 10 * count ≤ 254) (config : LookupRangeCheck.Config 10) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((LookupRangeCheck.rangeCheckAtDecomposed count hcount hpow).call config offset input).operations region) =
      runningLookupTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((LookupRangeCheck.rangeCheckAtDecomposedBody count config offset input).operations region) = _
  simp only [LookupRangeCheck.rangeCheckAtDecomposedBody, lookup_trace_norm]

/-- Copying into a range check contributes one region of lookups. -/
@[lookup_trace_norm]
theorem copyCheck_lookupTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((LookupRangeCheck.copyCheck K count strict).call config input).operations region) =
      [runningLookupTrace config 0 count] := by
  simp only [LookupRangeCheck.copyCheck, lookup_trace_norm]

/-- A witnessed short check has one region with its two lookups. -/
@[lookup_trace_norm]
theorem witnessShortCheck_lookupTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    lookupTrace ((LookupRangeCheck.witnessShortCheck K bits config witness).operations region) =
      [shortLookupTrace config] := by
  simp only [LookupRangeCheck.witnessShortCheck, lookup_trace_norm, shortLookupTrace]

/-- Witnessing into a range check contributes one region of lookups. -/
@[lookup_trace_norm]
theorem witnessCheck_lookupTrace (K count : ℕ) (strict : Bool) (config : LookupRangeCheck.Config K)
    (witness : WitgenIR Fp 1) (hstrict : strict = true → 0 < count) (region : RegionIndex) :
    lookupTrace ((LookupRangeCheck.witnessCheck K count strict config witness hstrict).operations region) =
      [runningLookupTrace config 0 count] := by
  simp only [LookupRangeCheck.witnessCheck, lookup_trace_norm]

/-- Witnessing a decomposed range check contributes one region of lookups. -/
@[lookup_trace_norm]
theorem witnessCheckDecomposed_lookupTrace (config : LookupRangeCheck.Config 10)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    lookupTrace ((LookupRangeCheck.witnessCheckDecomposed config witness).operations region) =
      [runningLookupTrace config 0 25] := by
  simp only [LookupRangeCheck.witnessCheckDecomposed, lookup_trace_norm]

end Zcash.Snark.ZeroKnowledge

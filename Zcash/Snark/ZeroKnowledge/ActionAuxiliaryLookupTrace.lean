import Zcash.Snark.ZeroKnowledge.FixedBaseLookupTrace
import Zcash.Snark.ZeroKnowledge.VariableBaseLookupTrace
import Zcash.Snark.ZeroKnowledge.PoseidonSelectorTrace
import Zcash.Circuits.Action.ValueCommit
import Zcash.Circuits.Action.SpendAuthority
import Zcash.Circuits.Action.AddressIntegrity
import Zcash.Circuits.Action.DeriveNullifier

/-!
# Lookup traces of Action's auxiliary checks

Value commitment and spend authority are built from fixed-base multiplication and
point addition, so neither enables a lookup. Address integrity inherits the
overflow check of variable-base multiplication, and nullifier derivation the
thirteen-window range check of base-field multiplication; those are their only
lookups.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- A full Poseidon round does not enable any lookup. -/
@[lookup_trace_norm]
theorem poseidonFullRound_regionLookupTrace (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((Poseidon.fullRound round).call config offset input).operations region)
      = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A partial Poseidon round does not enable any lookup. -/
@[lookup_trace_norm]
theorem poseidonPartialRound_regionLookupTrace (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((Poseidon.partialRound round).call config offset
      input).operations region) = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The addition chip does not enable any lookup. -/
@[lookup_trace_norm]
theorem addChip_regionLookupTrace (config : AddChip.Config) (offset : ℕ)
    (input : Var AddChip.Inputs Fp) (region : RegionIndex) :
    regionLookupTrace ((AddChip.add.call config offset input).operations region) = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Witnessing a non-identity point does not enable any lookup. -/
@[lookup_trace_norm]
theorem witnessPointNonId_regionLookupTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionLookupTrace ((Ecc.WitnessPoint.pointNonId.call config offset input).operations region)
      = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Poseidon initialization does not enable any lookup. -/
@[lookup_trace_norm]
theorem poseidonInit_regionLookupTrace (capacity : Fp) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionLookupTrace (((Poseidon.initRegion capacity).call config offset
      input).operations region) = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Poseidon input absorption does not enable any lookup. -/
@[lookup_trace_norm]
theorem poseidonInput_regionLookupTrace (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Sponge.AddInputInput Fp) (region : RegionIndex) :
    regionLookupTrace ((Poseidon.addInputRegion.call config offset input).operations region)
      = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The Poseidon permutation does not enable any lookup: its rounds are pure gate activations. -/
@[lookup_trace_norm]
theorem poseidonPermutation_regionLookupTrace (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Permute.State Fp) (region : RegionIndex) :
    regionLookupTrace ((Poseidon.permuteRegion.call config offset input).operations region)
      = [] := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((Poseidon.permuteSynthesize config offset input).operations
    region) = _
  simp only [Poseidon.permuteSynthesize, lookup_trace_norm, Nat.mul_one,
    List.ofFn_const, List.flatten_replicate_nil, List.append_nil]
  rw [Poseidon.operations_readStateRow]
  rfl

/-- All three regions of the constant-length Poseidon hash are lookup-free. Stated here
beside its only consumer, since the Poseidon gadget has no lookup-trace file of its own. -/
@[lookup_trace_norm]
theorem poseidonHash_lookupTrace (capacity : Fp) (config : Poseidon.Config)
    (input : Var Poseidon.Sponge.Rate2 Fp) (region : RegionIndex) :
    lookupTrace (((Poseidon.hash capacity).call config input).operations region)
      = [[], [], []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Poseidon.synthesize capacity config input).operations region) = _
  simp only [Poseidon.synthesize, lookup_trace_norm, synthesis_summary_norm, List.cons_append]

/-- The five value-commitment regions, of which none enables a lookup. -/
def valueCommitLookupTrace : List (List (ℕ × ℕ)) := List.replicate 5 []

/-- Value commitment does not enable any lookup. -/
@[lookup_trace_norm]
theorem valueCommit_lookupTrace (valueBase : Ecc.MulFixed.Short.FixedBase)
    (blindBase : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.ValueCommit.Inputs Fp) (region : RegionIndex) :
    lookupTrace (((Action.ValueCommit.circuit valueBase blindBase).call
      config input).operations region) = valueCommitLookupTrace := by
  rw [FormalCircuit.call_operations]
  simp only [Action.ValueCommit.circuit, Ecc.Add.addFormal, lookup_trace_norm,
    synthesis_summary_norm, valueCommitLookupTrace, List.cons_append]
  rfl

/-- The three spend-authority regions, of which none enables a lookup. -/
def spendAuthorityLookupTrace : List (List (ℕ × ℕ)) := List.replicate 3 []

/-- Spend authority does not enable any lookup. -/
@[lookup_trace_norm]
theorem spendAuthority_lookupTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.SpendAuthority.Input Fp) (region : RegionIndex) :
    lookupTrace (((Action.SpendAuthority.circuit base).call config input).operations region) =
      spendAuthorityLookupTrace := by
  rw [FormalCircuit.call_operations]
  simp only [Action.SpendAuthority.circuit, Ecc.Add.addFormal, lookup_trace_norm,
    synthesis_summary_norm, spendAuthorityLookupTrace, List.cons_append]
  rfl

/-- Address integrity adds a point-witness region and a copy region, neither of which
enables a lookup, to variable-base multiplication's own trace. -/
def addressIntegrityLookupTrace (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    List (List (ℕ × ℕ)) :=
  variableBaseLookupTrace config.1 ++ [[], []]

/-- Address integrity contributes only the overflow check of its multiplication. -/
@[lookup_trace_norm]
theorem addressIntegrity_lookupTrace (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Action.AddressIntegrity.Input Fp) (region : RegionIndex) :
    lookupTrace ((Action.AddressIntegrity.circuit.call config input).operations region) =
      addressIntegrityLookupTrace config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.AddressIntegrity.circuit, Ecc.WitnessPoint.pointNonIdFormal,
    lookup_trace_norm, synthesis_summary_norm, addressIntegrityLookupTrace, List.cons_append]

/-- The nine nullifier regions. Only the seventh, the thirteen-window range check inside
base-field multiplication, enables a lookup. -/
def nullifierLookupTrace (config : LookupRangeCheck.Config 10) : List (List (ℕ × ℕ)) :=
  [[], [], [], [], [], [], runningLookupTrace config 0 13, [], []]

/-- Nullifier derivation contributes only its base-field multiplication's range check. -/
@[lookup_trace_norm]
theorem nullifier_lookupTrace (base : Ecc.MulFixed.FixedBase)
    (config : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    (input : Var Action.DeriveNullifier.Input Fp) (region : RegionIndex) :
    lookupTrace (((Action.DeriveNullifier.circuit base).call config input).operations region) =
      nullifierLookupTrace config.2.2.1.lookupConfig := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Action.DeriveNullifier.synthesize base config input).operations
    region) = _
  simp only [Action.DeriveNullifier.synthesize, AddChip.addFormal, Ecc.Add.addFormal,
    lookup_trace_norm, synthesis_summary_norm, nullifierLookupTrace, List.cons_append]

end Zcash.Snark.ZeroKnowledge

import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Snark.ZeroKnowledge.ActivationTrace
import Zcash.Circuits.Poseidon.Hash

/-!
# Exact activation trace of the Action Poseidon hash

The trace keeps the initial empty region, the input gate at row one, and the
4/28/4 full/partial/full permutation schedule. Round constants and private state
values do not enter the resulting trace.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- A full Poseidon round records its full-round gate, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem poseidonFullRound_regionActivations (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((Poseidon.fullRound round).call config offset input).operations region) =
      [.enableGate (Poseidon.fullRoundGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A partial Poseidon round records its partial-round gate, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem poseidonPartialRound_regionActivations (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((Poseidon.partialRound round).call config offset input).operations region) =
      [.enableGate (Poseidon.partialRoundsGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The exact gate-row schedule of the width-three permutation. -/
def poseidonPermutationActivations (config : Poseidon.Config) (offset : ℕ) :
    List (RegionOperation Fp) :=
  gateRowRun (Poseidon.fullRoundGate config) offset 4 ++
    gateRowRun (Poseidon.partialRoundsGate config) (offset + 4) 28 ++
    gateRowRun (Poseidon.fullRoundGate config) (offset + 32) 4

/-- The Poseidon permutation retains the full and partial round schedule, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem poseidonPermutation_regionActivations (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Permute.State Fp) (region : RegionIndex) :
    regionActivations ((Poseidon.permuteRegion.call config offset input).operations region) =
      poseidonPermutationActivations config offset := by
  rw [FormalRegionCircuit.call_operations]
  change regionActivations ((Poseidon.permuteSynthesize config offset input).operations region) = _
  simp only [Poseidon.permuteSynthesize, activation_trace_norm,
    gateRowRun, poseidonPermutationActivations, Nat.mul_one, List.append_assoc]
  rw [Poseidon.operations_readStateRow]
  simp only [List.flatMap_nil, List.append_nil]

/-- Poseidon initialization adds no activation, so trace extraction can omit its field
assignments. -/
@[activation_trace_norm]
theorem poseidonInit_regionActivations (capacity : Fp) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionActivations (((Poseidon.initRegion capacity).call config offset input).operations region) = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Poseidon input absorption retains its configured activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem poseidonInput_regionActivations (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Sponge.AddInputInput Fp) (region : RegionIndex) :
    regionActivations ((Poseidon.addInputRegion.call config offset input).operations region) =
      [.enableGate (Poseidon.padAndAddGate config) (offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- All three regions of the actual constant-length hash circuit. -/
@[activation_trace_norm]
theorem poseidonHash_activationTrace (capacity : Fp) (config : Poseidon.Config)
    (input : Var Poseidon.Sponge.Rate2 Fp) (region : RegionIndex) :
    activationTrace (((Poseidon.hash capacity).call config input).operations region) =
      [[], [.enableGate (Poseidon.padAndAddGate config) 1],
        poseidonPermutationActivations config 0] := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Poseidon.synthesize capacity config input).operations region) = _
  simp only [Poseidon.synthesize, activation_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge

import Zcash.Snark.ZeroKnowledge.FixedBaseVariantTrace
import Zcash.Snark.ZeroKnowledge.VariableBaseOverflowTrace
import Zcash.Snark.ZeroKnowledge.PoseidonSelectorTrace

/-!
# Selector traces of Action's auxiliary checks

These source equations compose the scalar-multiplication and Poseidon traces for
value commitments, spend authority, address integrity, and nullifier derivation.
Every empty region and final addition remains in the resulting region sequence.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The addition chip enables exactly its addition gate at the requested row, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem addChip_regionActivations (config : AddChip.Config) (offset : ℕ)
    (input : Var AddChip.Inputs Fp) (region : RegionIndex) :
    regionActivations ((AddChip.add.call config offset input).operations region) =
      [.enableGate (AddChip.addGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The five-region value-commitment trace. -/
def valueCommitActivations
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    List (List (RegionOperation Fp)) :=
  [runningFixedInnerActivations config.1.superConfig 0 22,
    [.enableGate (completeAddGate config.1.superConfig.addConfig) 0,
      .enableGate (Ecc.MulFixed.Short.shortGate config.1) 1],
    fullWidthInnerActivations config.2.1 0,
    [.enableGate (completeAddGate config.2.1.superConfig.addConfig) 0],
    [.enableGate (completeAddGate config.2.2) 0]]

/-- Value commitment retains the short-multiplication, blinding-multiplication, and addition
traces, supplying the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem valueCommit_activationTrace (valueBase : Ecc.MulFixed.Short.FixedBase) (blindBase : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.ValueCommit.Inputs Fp) (region : RegionIndex) :
    activationTrace (((Action.ValueCommit.circuit valueBase blindBase).call config input).operations region) =
      valueCommitActivations config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.ValueCommit.circuit, Ecc.Add.addFormal, activation_trace_norm,
    valueCommitActivations, List.cons_append]

/-- The three-region spend-authority trace. -/
def spendAuthorityActivations (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    List (List (RegionOperation Fp)) :=
  [fullWidthInnerActivations config.1 0,
    [.enableGate (completeAddGate config.1.superConfig.addConfig) 0],
    [.enableGate (completeAddGate config.2) 0]]

/-- Spend authority retains its fixed-multiplication and point-addition activations, supplying
the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem spendAuthority_activationTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.SpendAuthority.Input Fp) (region : RegionIndex) :
    activationTrace (((Action.SpendAuthority.circuit base).call config input).operations region) =
      spendAuthorityActivations config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.SpendAuthority.circuit, Ecc.Add.addFormal, activation_trace_norm,
    spendAuthorityActivations, List.cons_append]

/-- Address integrity retains the point-witness region and the final activation-free copy
region. -/
def addressIntegrityActivations (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    List (List (RegionOperation Fp)) :=
  variableBaseActivations config.1 ++
    [[.enableGate (Ecc.WitnessPoint.pointNonIdGate config.2.qPointNonId config.2.x config.2.y) 0],
      []]

/-- Address integrity retains its multiplication and nonidentity-point activations, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem addressIntegrity_activationTrace (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Action.AddressIntegrity.Input Fp) (region : RegionIndex) :
    activationTrace ((Action.AddressIntegrity.circuit.call config input).operations region) =
      addressIntegrityActivations config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.AddressIntegrity.circuit, Ecc.WitnessPoint.pointNonIdFormal,
    activation_trace_norm, addressIntegrityActivations, List.cons_append]

/-- The nine-region nullifier trace, including the Poseidon permutation schedule. -/
def nullifierActivations
    (config : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    List (List (RegionOperation Fp)) :=
  [[], [.enableGate (Poseidon.padAndAddGate config.1) 1],
    poseidonPermutationActivations config.1 0,
    [.enableGate (AddChip.addGate config.2.1) 0],
    runningFixedInnerActivations config.2.2.1.superConfig 0 85,
    [.enableGate (completeAddGate config.2.2.1.superConfig.addConfig) 0],
    runningActivations config.2.2.1.lookupConfig 0 13,
    [.enableGate (Ecc.MulFixed.BaseFieldElem.canonGate config.2.2.1) 1],
    [.enableGate (completeAddGate config.2.2.2) 0]]

/-- Nullifier derivation retains the activations of its hash and point arithmetic, supplying the
source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem nullifier_activationTrace (base : Ecc.MulFixed.FixedBase)
    (config : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Action.DeriveNullifier.Input Fp) (region : RegionIndex) :
    activationTrace (((Action.DeriveNullifier.circuit base).call config input).operations region) =
      nullifierActivations config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Action.DeriveNullifier.synthesize base config input).operations region) = _
  simp only [Action.DeriveNullifier.synthesize, AddChip.addFormal, Ecc.Add.addFormal,
    activation_trace_norm, nullifierActivations, List.cons_append]

end Zcash.Snark.ZeroKnowledge

import Zcash.Circuits.Trace.Programs
import Zcash.Circuits.Sinsemilla.HashToPoint

/-!
# Exact activation traces of Sinsemilla hashing

Lookup and gate activations are both retained, including repeated activation of
the same selector at a row. The formulas preserve piece order and boundary rows
without evaluating generator points, message pieces, or witness programs.

Each gadget has one lemma, stated on activations, and its selector trace follows by projection.
Sinsemilla is where keeping the activations earns the most: a round enables its lookup and its
gate at the same row, and both carry `qS1`, so a selector label cannot tell them apart.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- Each interior Sinsemilla row enables the lookup and then the gate. -/
def sinsemillaRoundsActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) : List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin count =>
    [RegionOperation.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config)
        [config.qS1] (offset + i.val),
      RegionOperation.enableGate (Sinsemilla.HashPiece.sinsemillaGate config)
        (offset + i.val)]).flatten

/-- A piece ends with the boundary lookup; its linking gate belongs to the chain. -/
def sinsemillaPieceActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) : List (RegionOperation Fp) :=
  sinsemillaRoundsActivations generators config offset count ++
    [.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config) [config.qS1]
      (offset + count)]

/-- One Sinsemilla round records its lookup and its gate, supplying the source metadata for Action
activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaRound_regionActivations (generators : Specs.Sinsemilla.Generators) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    (((Sinsemilla.HashPiece.round generators index).call config offset input).operations region).flatMap activationOf =
      [.enableLookup (Sinsemilla.HashPiece.generatorLookup generators config) [config.qS1] offset,
        .enableGate (Sinsemilla.HashPiece.sinsemillaGate config) offset] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Successive Sinsemilla rounds retain their ordered activation rows, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaLoop_regionActivations (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    (((Sinsemilla.HashPiece.loop generators count).call config offset input).operations region).flatMap activationOf =
      sinsemillaRoundsActivations generators config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellVec,
    sinsemillaRoundsActivations, Nat.mul_one]

/-- A Sinsemilla message piece retains its complete activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaPiece_regionActivations (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (final : Bool) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    (((Sinsemilla.HashPiece.circuit generators count final initialY).call
      config offset input).operations region).flatMap activationOf =
      sinsemillaPieceActivations generators config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change ((Sinsemilla.HashPiece.circuitBody generators count final initialY
    config offset input).operations region).flatMap activationOf = _
  simp only [Sinsemilla.HashPiece.circuitBody, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    Sinsemilla.HashPiece.operations_cellVec, sinsemillaPieceActivations]
  rfl

/-- A Sinsemilla slot retains the trace of its message piece, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaSlot_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    (((Sinsemilla.Chain.slot generators widths initialY index).call
      config offset input).operations region).flatMap activationOf =
      sinsemillaPieceActivations generators config offset (widths.getD index 0) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.slot, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt]

/-- Every piece and its boundary linking gate, in the chain's exact loop order. -/
def sinsemillaChainActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (RegionOperation Fp) :=
  (List.ofFn fun i : Fin widths.length =>
    let base := offset + Sinsemilla.Chain.prefixRows widths i.val
    sinsemillaPieceActivations generators config base (widths.getD i.val 0) ++
      [.enableGate (Sinsemilla.HashPiece.sinsemillaGate config)
        (base + widths.getD i.val 0)]).flatten

/-- A chain of Sinsemilla pieces retains their activation order, supplying the source metadata for
Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaChain_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    (((Sinsemilla.Chain.circuit generators widths initialY).call
      config offset input).operations region).flatMap activationOf =
      sinsemillaChainActivations generators config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, activation_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    sinsemillaChainActivations]

/-- The domain-point initialization gate followed by all message-piece activations. -/
def sinsemillaHashActivations (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (RegionOperation Fp) :=
  [.enableGate (Sinsemilla.HashPiece.initialYQGate config) offset] ++
    sinsemillaChainActivations generators config offset widths

/-- The Sinsemilla hash retains its complete source activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaHash_regionActivations (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    (((Sinsemilla.HashToPoint.hashRegion generators widths point honCurve hwidths).call
      config offset input).operations region).flatMap activationOf =
      sinsemillaHashActivations generators config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  change ((Sinsemilla.HashToPoint.hashRegionSynthesize generators widths point
    config offset input).operations region).flatMap activationOf = _
  simp only [Sinsemilla.HashToPoint.hashRegionSynthesize, activation_trace_norm,
    Sinsemilla.HashToPoint.z1Cells_operations, sinsemillaHashActivations]

/-- The Sinsemilla hash retains its complete source activation trace, supplying the source
metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaHash_activationTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    trace activationOf (((Sinsemilla.HashToPoint.hashCircuit generators widths point honCurve hwidths).call
      config input).operations region) = [sinsemillaHashActivations generators config 0 widths] := by
  simp only [Sinsemilla.HashToPoint.hashCircuit, activation_trace_norm]

/-- Witnessing a Sinsemilla message piece preserves its region slot, supplying the source metadata
for Action activation coverage. -/
@[activation_trace_norm]
theorem witnessMessagePiece_activationTrace (config : Sinsemilla.HashPiece.Config)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    trace activationOf ((Sinsemilla.HashToPoint.witnessMessagePiece config witness).operations region) = [[]] := rfl

end Zcash.Snark.ZeroKnowledge

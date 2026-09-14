import Zcash.Snark.ZeroKnowledge.LookupTracePrograms
import Zcash.Circuits.Sinsemilla.HashToPoint

/-!
# Lookup traces of the Sinsemilla hash

Each Sinsemilla round looks up its generator table, whose master selector is
`qS1`, so a round contributes one lookup at its row. The selector trace records
the same activation twice, once for the master and once for the auxiliary
selector; the lookup trace keeps only the master.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- One generator lookup at each round row of a message piece. -/
def sinsemillaRoundsLookupTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count => [(config.qS1.index, offset + i.val)]).flatten

/-- A piece's round lookups followed by its boundary lookup. -/
def sinsemillaPieceLookupTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  sinsemillaRoundsLookupTrace config offset count ++ [(config.qS1.index, offset + count)]

/-- Every piece's lookups in the chain's exact loop order. -/
def sinsemillaChainLookupTrace (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin widths.length =>
    let base := offset + Sinsemilla.Chain.prefixRows widths i.val
    sinsemillaPieceLookupTrace config base (widths.getD i.val 0)).flatten

/-- One Sinsemilla round looks up the generator table at its row. -/
@[lookup_trace_norm]
theorem sinsemillaRound_regionLookupTrace (generators : Specs.Sinsemilla.Generators) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.HashPiece.round generators index).call config offset input).operations region) =
      [(config.qS1.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Successive Sinsemilla rounds each look up the generator table at their own row. -/
@[lookup_trace_norm]
theorem sinsemillaLoop_regionLookupTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.HashPiece.loop generators count).call config offset input).operations region) =
      sinsemillaRoundsLookupTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, lookup_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellVec,
    sinsemillaRoundsLookupTrace, Nat.mul_one]

/-- A Sinsemilla message piece looks up once per round, then once more at its boundary. -/
@[lookup_trace_norm]
theorem sinsemillaPiece_regionLookupTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (final : Bool) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.HashPiece.circuit generators count final initialY).call
      config offset input).operations region) = sinsemillaPieceLookupTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((Sinsemilla.HashPiece.circuitBody generators count final initialY
    config offset input).operations region) = _
  simp only [Sinsemilla.HashPiece.circuitBody, lookup_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    Sinsemilla.HashPiece.operations_cellVec, sinsemillaPieceLookupTrace]
  rfl

/-- A chain slot contributes the lookups of the piece it holds. -/
@[lookup_trace_norm]
theorem sinsemillaSlot_regionLookupTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.Chain.slot generators widths initialY index).call
      config offset input).operations region) =
      sinsemillaPieceLookupTrace config offset (widths.getD index 0) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.slot, lookup_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt]

/-- A chain contributes every piece's lookups, in the chain's loop order. -/
@[lookup_trace_norm]
theorem sinsemillaChain_regionLookupTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.Chain.circuit generators widths initialY).call
      config offset input).operations region) = sinsemillaChainLookupTrace config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, lookup_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    sinsemillaChainLookupTrace]

/-- A Sinsemilla hash region contributes its chain's lookups. -/
@[lookup_trace_norm]
theorem sinsemillaHash_regionLookupTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionLookupTrace (((Sinsemilla.HashToPoint.hashRegion generators widths point honCurve hwidths).call
      config offset input).operations region) = sinsemillaChainLookupTrace config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  change regionLookupTrace ((Sinsemilla.HashToPoint.hashRegionSynthesize generators widths point
    config offset input).operations region) = _
  simp only [Sinsemilla.HashToPoint.hashRegionSynthesize, lookup_trace_norm,
    Sinsemilla.HashToPoint.z1Cells_operations]

/-- The Sinsemilla hash occupies a single region, carrying its chain's lookups. -/
@[lookup_trace_norm]
theorem sinsemillaHash_lookupTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    lookupTrace (((Sinsemilla.HashToPoint.hashCircuit generators widths point honCurve hwidths).call
      config input).operations region) = [sinsemillaChainLookupTrace config 0 widths] := by
  simp only [Sinsemilla.HashToPoint.hashCircuit, lookup_trace_norm]

/-- Witnessing a Sinsemilla message piece preserves its lookup-free region slot. -/
@[lookup_trace_norm]
theorem witnessMessagePiece_lookupTrace (config : Sinsemilla.HashPiece.Config) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    lookupTrace ((Sinsemilla.HashToPoint.witnessMessagePiece config witness).operations region) = [[]] := rfl

end Zcash.Snark.ZeroKnowledge

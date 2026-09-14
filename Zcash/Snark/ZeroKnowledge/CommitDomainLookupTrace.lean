import Zcash.Snark.ZeroKnowledge.SinsemillaLookupTrace
import Zcash.Circuits.Ecc.MulFixed.FullWidth
import Zcash.Circuits.Sinsemilla.CommitDomain

/-!
# Lookup trace of a Sinsemilla commitment

Every lookup in a commitment comes from the Sinsemilla hash. Full-width blinding
multiplication and the two complete additions enable none, so their regions
contribute empty entries and the trace keeps one entry per region.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Both regions of full-width blinding multiplication are lookup-free. The region-level
`regionLookupTrace_eq_nil` does not reach this: a circuit's trace has one entry per region, so
crossing a multi-region call boundary needs the region count as well as the activation count.
Stated here, beside its only consumer. -/
@[lookup_trace_norm]
theorem fullWidth_lookupTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config) (input : Var UnconstrainedNat Fp)
    (region : RegionIndex) :
    lookupTrace (((Ecc.MulFixed.FullWidth.circuit base).call config input).operations region)
      = [[], []] := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.MulFixed.FullWidth.synthesize base.toData config
    (Ecc.MulFixed.FullWidth.scalarWindows input)).operations region) = _
  simp only [Ecc.MulFixed.FullWidth.synthesize, lookup_trace_norm, synthesis_summary_norm,
    List.cons_append]

/-- The exact commitment lookup trace, parameterized by the message's piece widths. Only the
hash configuration appears: it is the sole source of lookups. -/
def sinsemillaCommitLookupTrace (widths : List ℕ) (config : Sinsemilla.HashPiece.Config) :
    List (List (ℕ × ℕ)) :=
  [[], [], sinsemillaChainLookupTrace config 0 widths, []]

/-- Sinsemilla commitment contributes exactly its hash region's lookups. -/
@[lookup_trace_norm]
theorem sinsemillaCommit_lookupTrace (generators : Specs.Sinsemilla.Generators) (widths : List ℕ)
    (base : Ecc.MulFixed.FixedBase) (point : Point Fp) (honCurve : point.OnCurve)
    (hwidths : widths ≠ [])
    (config : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (input : Var (Sinsemilla.CommitDomain.Input widths.length) Fp) (region : RegionIndex) :
    lookupTrace (((Sinsemilla.CommitDomain.commit generators widths base point honCurve
      hwidths).call config input).operations region) =
      sinsemillaCommitLookupTrace widths config.2.1 := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Sinsemilla.CommitDomain.synthesize generators widths base point honCurve
    hwidths config input).operations region) = _
  simp only [Sinsemilla.CommitDomain.synthesize, Ecc.Add.addFormal, lookup_trace_norm,
    synthesis_summary_norm, sinsemillaCommitLookupTrace, List.cons_append]

end Zcash.Snark.ZeroKnowledge

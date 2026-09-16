import Zcash.Snark.ZeroKnowledge.FixedBaseSelectorTrace
import Zcash.Snark.ZeroKnowledge.SinsemillaSelectorTrace

/-!
# Selector trace of a Sinsemilla commitment

The four-region trace joins full-width blinding multiplication, message hashing,
and the final complete addition in the source circuit's order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Trace

/-- The exact commitment trace, parameterized by the message's piece widths. -/
def sinsemillaCommitActivations (generators : Specs.Sinsemilla.Generators) (widths : List ℕ)
    (config : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config) :
    List (List (RegionOperation Fp)) :=
  [fullWidthInnerActivations config.1 0,
    [.enableGate (completeAddGate config.1.superConfig.addConfig) 0],
    sinsemillaHashActivations generators config.2.1 0 widths,
    [.enableGate (completeAddGate config.2.2) 0]]

/-- Sinsemilla commitment retains the hash, fixed-multiplication, and addition region traces,
supplying the source metadata for Action activation coverage. -/
@[activation_trace_norm]
theorem sinsemillaCommit_activationTrace (generators : Specs.Sinsemilla.Generators) (widths : List ℕ)
    (base : Ecc.MulFixed.FixedBase) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (input : Var (Sinsemilla.CommitDomain.Input widths.length) Fp) (region : RegionIndex) :
    activationTrace (((Sinsemilla.CommitDomain.commit generators widths base point honCurve hwidths).call
      config input).operations region) = sinsemillaCommitActivations generators widths config := by
  rw [FormalCircuit.call_operations]
  change activationTrace ((Sinsemilla.CommitDomain.synthesize generators widths base point honCurve hwidths
    config input).operations region) = _
  simp only [Sinsemilla.CommitDomain.synthesize, Ecc.Add.addFormal, activation_trace_norm,
    sinsemillaCommitActivations, List.cons_append]

end Zcash.Snark.ZeroKnowledge

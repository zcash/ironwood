import Zcash.Snark.ZeroKnowledge.LookupRangeCheckTrace
import Zcash.Circuits.Ecc.Mul

/-!
# Lookup traces of variable-base scalar multiplication

The whole double-and-add convergence runs in one region and enables no lookup.
Every lookup comes from the overflow check that follows it, whose middle region
is a copied running range check over the scalar's low 130 bits.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The overflow check's three regions: the witnessed sum, the running range check on the
low words, and the closing gate region. -/
def mulOverflowLookupTrace {K : ℕ} (config : LookupRangeCheck.Config K) :
    List (List (ℕ × ℕ)) :=
  [[], runningLookupTrace config 0 (Ecc.MulOverflow.numWords K), []]

/-- The overflow check contributes exactly its running range check. -/
@[lookup_trace_norm]
theorem mulOverflow_lookupTrace (K : ℕ) (hKW : K * Ecc.MulOverflow.numWords K = 130)
    (cfg : Ecc.MulOverflow.Config K) (input : Var Ecc.MulOverflow.Inputs Fp)
    (region : RegionIndex) :
    lookupTrace (((Ecc.MulOverflow.circuit K hKW).call cfg input).operations region) =
      mulOverflowLookupTrace cfg.lookupConfig := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.MulOverflow.synthesize K cfg input).operations region) = _
  simp only [Ecc.MulOverflow.synthesize, lookup_trace_norm, synthesis_summary_norm,
    mulOverflowLookupTrace, List.cons_append]

/-- Variable-base multiplication's four regions: the lookup-free main convergence region,
then the three of the overflow check. -/
def variableBaseLookupTrace (config : Ecc.Mul.Config) : List (List (ℕ × ℕ)) :=
  [] :: mulOverflowLookupTrace config.overflowConfig.lookupConfig

/-- Variable-base scalar multiplication contributes only its overflow check's lookups. -/
@[lookup_trace_norm]
theorem variableBase_lookupTrace (config : Ecc.Mul.Config)
    (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    lookupTrace ((Ecc.Mul.mul.call config input).operations region) =
      variableBaseLookupTrace config := by
  rw [FormalCircuit.call_operations]
  change lookupTrace ((Ecc.Mul.synthesize config input).operations region) = _
  simp only [Ecc.Mul.synthesize, lookup_trace_norm, synthesis_summary_norm,
    variableBaseLookupTrace, List.cons_append]

/-- The trace holds exactly as many activations as the circuit's own summary counts. -/
theorem variableBaseLookupTrace_length (config : Ecc.Mul.Config) :
    (variableBaseLookupTrace config).flatten.length =
      (Ecc.Mul.mulSynthesisSummary config).lookupActivationCount := by
  rw [Ecc.Mul.mulSynthesisSummary_lookupActivationCount]
  simp only [variableBaseLookupTrace, mulOverflowLookupTrace, runningLookupTrace,
    Ecc.MulOverflow.numWords, List.length_flatten, List.map_ofFn, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rfl

end Zcash.Snark.ZeroKnowledge

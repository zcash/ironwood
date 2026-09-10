import Zcash.Circuits.Integration.OperationCopies
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.OperationGates
import Zcash.Circuits.Integration.OperationFixed

/-! # Reassembling full circuit satisfaction

The four constraint families share one placement, environment, and operation stream.
Copy equalities are already constraints; only gates and lookups need their polynomial
interpretations translated before assembling Clean's satisfaction predicate.
-/

namespace Zcash.Snark

open Halo2

/-- Semantic evidence for the four operation families. -/
structure FullCircuitBridge
    (place : RegionIndex → ℕ) (env : Environment Fp)
    (ops : Operations Fp) (i : RegionIndex) where
  gates : CircuitConstraintFamily.constraints .gate place env ops i
  fixed : CircuitConstraintFamily.constraints .fixed place env ops i
  copies : CircuitConstraintFamily.constraints .copy place env ops i
  theta : Fp
  lookups : ∀ lookup ∈ operationEnabledLookups ops i,
    EnabledLookup.DeployedWitness place env theta lookup

namespace FullCircuitBridge

/-- Reassemble the four semantic families without any further representation step. -/
theorem satisfaction
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {ops : Operations Fp} {i : RegionIndex}
    (bridge : FullCircuitBridge place env ops i) :
    FullCircuitSatisfaction place env ops i :=
  ⟨bridge.gates, bridge.copies,
    lookup_constraints_of_deployed_witnesses place env ops i bridge.theta bridge.lookups,
    bridge.fixed⟩

/-- The same bridge stated at Clean's authoritative constraint predicate. -/
theorem constraints
    {place : RegionIndex → ℕ} {env : Environment Fp}
    {ops : Operations Fp} {i : RegionIndex}
    (bridge : FullCircuitBridge place env ops i) :
    Halo2.Constraints place env ops i :=
  bridge.satisfaction.constraints

end FullCircuitBridge

end Zcash.Snark

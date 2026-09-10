import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelCircuit

/-!
# Circuit-derived full bridge assembly

This module is the generic join between the circuit-derived gate and lookup
adapters and ironwood's `FullCircuitBridge`. It keeps the verifier and soundness
layers in their native polynomial language: Clean-specific reconstruction is
finished here before the resulting bridge is handed to the semantic endpoint.
-/

open Zcash.Arithmetic (omegaOf)

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open Zcash.Arithmetic (deltaFp)

set_option maxHeartbeats 20000

namespace FullCircuitBridge

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}

/--
Assemble the complete operation bridge from the canonical circuit-derived
constraint model.

Gate and lookup witnesses are derived here from `TopLevelCircuit`; callers supply
only the representation boundaries that genuinely come from other streams:

* packed selector activation and exact lookup-selector values from fixed keygen
  rows;
* the complete fixed/table family from those same rows;
* copy constraints from keygen's cell permutation;
* one bundle-wide record of lookup challenge exclusions.
-/
def ofTopLevelCanonical
    {k : ℕ}
    [CircuitFieldSupport top]
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (selectorActivations :
      SelectorActivationsRealized top.selectorMap
        top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (fixed :
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0)
    (copies :
      CircuitConstraintFamily.constraints .copy top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0)
    (lookupConditions :
      TopLevelLookup.WitnessConditions
        top pp urs ch poly proofIndex) :
    FullCircuitBridge top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 := by
  refine
    { gates := ?_
      fixed := fixed
      copies := copies
      theta := ch.theta
      lookups := ?_ }
  · apply top.canonicalConstraints ch poly proofIndex
      satisfaction
    · intro row
      rw [← pow_mul, Nat.mul_comm, pow_mul, top.omega_pow_n, one_pow]
    · exact selectorActivations
  · exact TopLevelLookup.deployedWitnesses ch poly proofIndex
      satisfaction lookupConditions

end FullCircuitBridge

end Zcash.Snark

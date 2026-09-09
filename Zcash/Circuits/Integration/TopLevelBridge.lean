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

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

namespace FullCircuitBridge

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}

/--
Assemble the complete operation bridge from the canonical circuit-derived
constraint model.

Gate and lookup witnesses are derived here from `TopLevelCircuit`; callers supply
only the representation boundaries that genuinely come from other streams:

* packed selector activation and exact lookup-selector values from fixed keygen
  rows;
* the complete fixed/table family from those same rows;
* copy replay from keygen's cell permutation;
* one bundle-wide record of lookup challenge exclusions.
-/
def ofTopLevelCanonical
    {k : ℕ}
    (gateCoherence : TopLevelConstraintBounds top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (hroot :
      top.omega ^
        top.n = 1)
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
      CopyReplayWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) cell Bad)
    (lookupConditions :
      TopLevelLookup.WitnessConditions
        top pp urs ch poly proofIndex) :
    FullCircuitBridge top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 cell Bad := by
  refine
    { gates := ?_
      fixed := fixed
      copies := copies
      theta := ch.theta
      lookups := ?_ }
  · apply gateCoherence.canonicalConstraints ch poly proofIndex
      satisfaction
    · intro row
      rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
    · exact selectorActivations
  · exact TopLevelLookup.deployedWitnesses gateCoherence ch poly proofIndex
      satisfaction lookupConditions

/--
Lift per-proof full bridges to a bundle of circuit-owned statements while
preserving one shared exceptional event.

This is the generic finite-family join used by the Action adapter: the proof does
not inspect the circuit statement and introduces no encoding predicate of its own.
-/
def bundleTopLevelSoundness_or_bad
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    {numProofs : ℕ}
    (assignment : Fin numProofs → ProofAssignment Fp)
    (bridge : ∀ proofIndex,
      FullCircuitBridge
        top.placement
        (top.environment (assignment proofIndex))
        top.operations 0 cell Bad) :
    (∀ proofIndex,
      top.Statement
        (top.extractPublicInput (top.environment (assignment proofIndex)))) ⊕' Bad :=
  finForallOrRelationWitness fun proofIndex =>
    FullCircuitBridge.topLevelSoundness_or_bad
      top (assignment proofIndex) (bridge proofIndex)

end FullCircuitBridge

end Zcash.Snark

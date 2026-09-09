import Zcash.Circuits.Integration.TopLevelBridge
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment

/-!
# Top-level circuit correctness interface

This module packages the named Clean/ironwood representation boundaries consumed
by the generic soundness terminal.  It deliberately contains no final circuit
statement and no opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

/--
The statement owned by a top-level circuit, simultaneously for every polynomial
assignment decoded from one accepted proof bundle.
-/
def TopLevelBundleStatement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (poly : CommitmentId → CPoly) : Prop :=
  ∀ proofIndex : Fin pp.numProofs,
    let environment := ({
        polynomial := poly
      } : TopLevelAssignment top
            pp.numProofs proofIndex).environment
    top.Statement (top.extractPublicInput environment)

/-- Executable private witnesses, with erased validity certificates, for every decoded member. -/
def TopLevelBundleWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (poly : CommitmentId → CPoly) : Type :=
  ∀ proofIndex : Fin pp.numProofs,
    let environment := ({
        polynomial := poly
      } : TopLevelAssignment top
            pp.numProofs proofIndex).environment
    TopLevelSemanticWitness top (top.extractPublicInput environment)

/-- Executable private witnesses for externally supplied bundle inputs. -/
def TopLevelExternalBundleWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp) : Type :=
  ∀ proofIndex, TopLevelSemanticWitness top (inputs proofIndex)

namespace TopLevelBundleStatement

/--
Present the circuit-owned bundle statement at externally supplied public inputs once
the canonical polynomial assignments are known to encode them through the circuit's
declared instance-cell layout.
-/
theorem of_publicInputEncoding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (poly : CommitmentId → CPoly)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hencoding : ∀ proofIndex,
      let assignment : TopLevelAssignment top
          pp.numProofs proofIndex :=
        { polynomial := poly }
      assignment.PublicInputEncoding (inputs proofIndex))
    (htop : TopLevelBundleStatement top pp poly) :
    ∀ proofIndex, top.Statement (inputs proofIndex) := by
  intro proofIndex
  let assignment : TopLevelAssignment top
      pp.numProofs proofIndex :=
    { polynomial := poly }
  have hstatement := htop proofIndex
  change top.Statement
    (top.extractPublicInput assignment.environment) at hstatement
  rw [assignment.extractPublicInput_eq
    (inputs proofIndex) (hencoding proofIndex)] at hstatement
  exact hstatement

end TopLevelBundleStatement

namespace TopLevelBundleWitness

/-- Re-present decoded private witnesses at the verifier's externally supplied inputs. -/
def of_publicInputEncoding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (poly : CommitmentId → CPoly)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hencoding : ∀ proofIndex,
      let assignment : TopLevelAssignment top
          pp.numProofs proofIndex :=
        { polynomial := poly }
      assignment.PublicInputEncoding (inputs proofIndex))
    (witness : TopLevelBundleWitness top pp poly) :
    TopLevelExternalBundleWitness top inputs := fun proofIndex => by
  let assignment : TopLevelAssignment top
      pp.numProofs proofIndex :=
    { polynomial := poly }
  refine
    { w := (witness proofIndex).w
      satisfied := ?_ }
  rw [← assignment.extractPublicInput_eq
    (inputs proofIndex) (hencoding proofIndex)]
  exact (witness proofIndex).satisfied

/-- Forget the retained decoded witnesses and recover the ordinary bundle statement. -/
theorem statement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top]
    {pp : ProofParams}
    {poly : CommitmentId → CPoly}
    (witness : TopLevelBundleWitness top pp poly) :
    TopLevelBundleStatement top pp poly :=
  fun proofIndex => (witness proofIndex).statement

end TopLevelBundleWitness

abbrev TopLevelFixedEncoding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) : Prop :=
  let assignment :
      TopLevelAssignment top pp.numProofs proofIndex :=
    { polynomial := poly }
  assignment.FixedColumnEncoding

abbrev TopLevelFixed
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) : Prop :=
  (SelectorActivationsRealized
      top.selectorMap top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
    ∧ CircuitConstraintFamily.constraints .fixed top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      top.operations 0)

abbrev TopLevelCopies
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type)
    (proofIndex : Fin pp.numProofs) : Type :=
  CopyReplayWitness top.placement
    (resolverEnvironment
      (top.toVerifierKey urs) poly proofIndex
      (top.usableRowsAt top.domainExponent))
    top.operations cell Bad

abbrev TopLevelLookups
    {k : ℕ}
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs) : Prop :=
  TopLevelLookup.WitnessConditions
    top pp urs ch poly proofIndex

namespace TopLevelAssignment

/--
Package one successful set of component witnesses behind abstract environment
and operation values, retaining only their equalities to the circuit-derived
values.
-/
def bridgeWitness_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    [TopLevelShape top]
    {pp : ProofParams} {urs : URS G}
    {k : ℕ} {ch : Challenges k Fp}
    {poly : CommitmentId → CPoly}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (gates : TopLevelConstraintBounds top)
    (fixedEncoding :
      let assignment :
          TopLevelAssignment top
            pp.numProofs proofIndex :=
        { polynomial := poly }
      assignment.FixedColumnEncoding)
    (selectorActivations :
      SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)))
    (fixed :
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        top.operations 0)
    (copies :
      CopyReplayWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        top.operations cell Bad)
    (lookups :
      TopLevelLookup.WitnessConditions
        top pp urs ch poly proofIndex) :
    TopLevelBridgeWitness top
      (({ polynomial := poly } :
        TopLevelAssignment top
          pp.numProofs proofIndex).proofAssignment)
      cell Bad := by
  let assignment :
      TopLevelAssignment top pp.numProofs proofIndex :=
    { polynomial := poly }
  change TopLevelBridgeWitness top assignment.proofAssignment cell Bad
  have hroot :=
    TopLevelAssignment.domainRoot
      (top := top) gates.domainExponent_lt
  let bridge :=
    FullCircuitBridge.ofTopLevelCanonical
      (top := top) (pp := pp) (urs := urs)
      (cell := cell) (Bad := Bad)
      gates ch poly proofIndex satisfaction
      hroot selectorActivations fixed copies lookups
  clear_value bridge
  generalize henvironmentValue :
    resolverEnvironment
      (top.toVerifierKey urs) poly proofIndex
      (top.usableRowsAt top.domainExponent) = environment at bridge
  generalize hoperations : top.operations = operations at bridge
  have henvironment :=
    assignment.resolverEnvironment_eq_environment
      pp urs fixedEncoding
  have henvironment' :
      resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex
          (top.usableRowsAt top.domainExponent) =
        top.environment assignment.proofAssignment :=
    henvironment
  refine
    { environment := environment
      operations := operations
      environment_eq := ?_
      operations_eq := ?_
      bridge := ?_ }
  · exact henvironmentValue.symm.trans henvironment'
  · exact hoperations
  · exact bridge

end TopLevelAssignment

/--
The representation-boundary data needed to interpret one canonical polynomial
assignment as an execution of a top-level circuit.

Each field names one of the four Clean constraint families.  The shared `Bad`
alternative is retained componentwise so that commitment-binding failures can be
joined without turning this record into an opaque statement-level hypothesis, and
is carried as data: a field that cannot be discharged returns the break rather
than asserting one exists.

The copy field carries its witness directly because `Bad` is a type, keeping the
terminal independent of choice.
-/
structure TopLevelCircuitCorrectness
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (pp : ProofParams) (urs : URS G)
    {k : ℕ} (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Type) : Type where
  gates : TopLevelConstraintBounds top
  fixedEncoding : ∀ proofIndex,
    TopLevelFixedEncoding top pp poly proofIndex ⊕' Bad
  fixed : ∀ proofIndex,
    TopLevelFixed top pp urs poly proofIndex ⊕' Bad
  copies : ∀ proofIndex,
    TopLevelCopies top pp urs poly cell Bad proofIndex ⊕' Bad
  lookups : ∀ proofIndex,
    TopLevelLookups top pp urs ch poly proofIndex ⊕' Bad

end Zcash.Snark

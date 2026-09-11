import Zcash.Circuits.Integration.AssignmentEncoding
import Zcash.Common.Satisfying

/-! # Circuit-owned witnesses for decoded polynomial assignments

These types retain executable witnesses and their specification proofs,
at either decoded or externally supplied public inputs.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

/-- A circuit's witness as executable data, with its specification proof. -/
abbrev TopLevelSemanticWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (publicInput : PublicInput Fp) : Type :=
  Zcash.Common.Satisfying top.Spec publicInput

namespace TopLevelSemanticWitness

/-- Forget the retained witness to obtain the circuit's existential statement. -/
theorem statement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {publicInput : PublicInput Fp}
    (witness : TopLevelSemanticWitness top publicInput) :
    top.Statement publicInput :=
  ⟨witness.w, witness.satisfied⟩

end TopLevelSemanticWitness

/-- Executable witnesses for externally supplied bundle inputs. -/
def TopLevelExternalBundleWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInput Fp) : Type :=
  ∀ proofIndex, TopLevelSemanticWitness top (inputs proofIndex)

/-- Witnesses at the public inputs decoded from the polynomial resolver. -/
def TopLevelBundleWitness
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top]
    (numProofs : ℕ) (poly : CommitmentId → CPoly) : Type :=
  TopLevelExternalBundleWitness top fun proofIndex : Fin numProofs =>
    top.extractPublicInput (top.environment (resolverAssignment top.omega poly proofIndex))

end Zcash.Snark

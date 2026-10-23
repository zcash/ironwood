import Zcash.Circuits.Halo2.FieldSupport
import Zcash.Circuits.Integration.PolynomialEnvironment
import Zcash.Snark.Keygen.Pipeline
import Zcash.Common.Satisfying

/-! # Encoding compiled fixed values and public inputs in polynomial assignments

`polynomialAssignment` supplies the proof-varying advice and instance values.
Fixed-column binding identifies its polynomial environment with the circuit-owned
environment; instance-column binding identifies the extracted public input.
-/

namespace Halo2.TopLevelCircuit

open Zcash Zcash.Snark CompPoly.CPolynomial

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
  (top : TopLevelCircuit Fp Config PublicInput) [TopLevelShape top]

/-- The fixed polynomials evaluate to the circuit's compiled fixed values. -/
def FixedColumnEncoding (poly : CommitmentId → CPoly) : Prop :=
  ∀ column row,
    (poly (.fixedCol column.index)).eval (top.omega ^ row) =
      top.fixedValue column row

/-- Binding the fixed columns identifies the polynomial environment with the
circuit-owned environment of the decoded proof assignment. -/
theorem polynomialEnvironmentOfCommitments_eq_environment
    {G : Type} [AddCommGroup G] [Inhabited G]
    (urs : URS G) (poly : CommitmentId → CPoly) (proofIndex : ℕ)
    (hfixed : top.FixedColumnEncoding poly) :
    polynomialEnvironmentOfCommitments (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent) =
      top.environment (polynomialAssignment top.omega poly proofIndex) := by
  apply congrArg₂ Environment.mk
  · funext column row
    cases column.kind with
    | advice =>
        simp only [top.toVerifierKey_omega, polynomialAssignment_advice]
    | fixed =>
        simpa only [top.toVerifierKey_omega] using hfixed ⟨column.index⟩ row
    | «instance» =>
        simp only [top.toVerifierKey_omega, polynomialAssignment_instance]
  · simp only [TopLevelCircuit.usableRowsAt]
    rw [top.domainExponent_eq_compiled]
    rfl

/-- Instance reads agree with the public-input elements at the declared layout cells. -/
def PublicInputEncoding (poly : CommitmentId → CPoly) (proofIndex : ℕ)
    (input : PublicInput Fp) : Prop :=
  ∀ index,
    (polynomialAssignment top.omega poly proofIndex).inst
        (top.publicInputLayout.cells index).1
        (top.publicInputLayout.cells index).2 =
      (toElements input)[index]

/-- Encoded instance values determine the circuit's extracted public input. -/
theorem extractPublicInput_eq_of_encoding
    (poly : CommitmentId → CPoly) (proofIndex : ℕ)
    (input : PublicInput Fp) (hencoding : top.PublicInputEncoding poly proofIndex input) :
    top.extractPublicInput (top.environment (polynomialAssignment top.omega poly proofIndex)) =
      input := by
  apply top.publicInputLayout.extract_eq
  intro index
  simpa only [top.environment_inst] using hencoding index

/-- Binding instance polynomials on the declared public layout recovers the input.
Other instance columns need no polynomial identity. -/
theorem publicInputEncoding_of_publicInputRowPolynomials
    [CircuitFieldSupport top]
    (poly : CommitmentId → CPoly) (proofIndex : ℕ)
    (input : PublicInput Fp)
    (hpoly : ∀ index,
      poly (.instanceCol proofIndex (top.publicInputLayout.cells index).1.index) =
        instanceRowPolynomial top.n top.omega
          (top.publicInputRows input (top.publicInputLayout.cells index).1)) :
    top.PublicInputEncoding poly proofIndex input := by
  intro index
  let cell := top.publicInputLayout.cells index
  let domainRow : Fin top.n :=
    ⟨cell.2, (top.publicInputLayout_cells_snd_lt_usableRowsAt_domainExponent index).trans_le
      top.usableRowsAt_domainExponent_le_n⟩
  rw [polynomialAssignment_instance, hpoly index]
  have hrow := instanceRowPolynomial_eval
    (values := top.publicInputRows input cell.1) top.domainRowsInjective domainRow
  calc
    _ = (top.publicInputRows input cell.1).getD cell.2 0 := by
      simpa only [domainRow, cell] using hrow
    _ = _ := top.publicInputRows_getD_cell input index

end Halo2.TopLevelCircuit

/-! ## Circuit-owned witnesses for decoded polynomial assignments

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
    top.extractPublicInput (top.environment (polynomialAssignment top.omega poly proofIndex))

end Zcash.Snark

import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Keygen.Lagrange
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Circuits.Action.Shape.PlannerTrace
import Mathlib.Util.AssertNoSorry

/-!
# The captured instance commitments are the circuit-derived ones

The Action model commits public inputs the way halo2's `verify_proof` does, through
`actionCircuit.instanceCommitment capturedURS inputs`; the captured artifacts are exercised
against the fixture's own `Fixture.derivedInstanceCommitment`. This module joins the two, so
the circuit model can be instantiated at the captured proof.

**The bases agree.** `commitLagrange_eq_commitInstance` identifies halo2's Lagrange-generator
commitment with the extractor's monomial URS at `capturedURS`. It needs no new fixture check: the
captured Lagrange prefix is certified by `derivedUrsGLagrange_prefix_eq`, and
`LagrangeCommitmentKey` is a subsingleton, so the key a statement names is the key the
certificate discharges.

**The rows agree.** `publicInputRows_capturedActionInputs` checks that the circuit's public-input
serialization reproduces the captured column — the only `native_decide` here, over ten field
elements.
-/

namespace Zcash.Snark.Keygen

open Zcash.Arithmetic (derivedUrsGLagrange omegaOf)
open Zcash.Snark
open Zcash.Snark.Fixture
open Halo2
open Zcash.Circuits.Action

set_option maxHeartbeats 400000
set_option maxRecDepth 8000

/-! ## The captured Lagrange prefix as a commitment key -/

/-- **The captured Lagrange generators satisfy the commitment-key setup obligation.** Each exported
generator is the monomial commitment to its Lagrange row, which is exactly
`derivedUrsGLagrange_prefix_eq` (the certificate's prefix cross-check) composed with the closed-form
generator identity. -/
theorem capturedUrsGLagrange_prefix :
    ∀ i : Fin (2 ^ capturedURS.k), (i : ℕ) < capturedUrsGLagrange.length →
      capturedUrsGLagrange.getD (i : ℕ) 0 =
        commit capturedURS (polynomialCoefficients (2 ^ capturedURS.k)
          (rowPolynomial (omegaOf capturedURS.k) (Pi.single i 1))) := by
  intro i hi
  -- The exported prefix is a prefix of the derived basis, so the two agree entry by entry below
  -- its length.
  have hderived :
      capturedUrsGLagrange.getD (i : ℕ) 0
        = (derivedUrsGLagrange capturedURS).getD (i : ℕ) 0 := by
    conv_lhs => rw [← derivedUrsGLagrange_prefix_eq]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  -- Below the prefix length the derived basis is nonempty there, which is what the closed-form
  -- setup lemma asks for.
  have hlen : (i : ℕ) < (derivedUrsGLagrange capturedURS).length := by
    have hprefix := congrArg List.length derivedUrsGLagrange_prefix_eq
    rw [List.length_take] at hprefix
    omega
  rw [hderived]
  exact ofPrefix_setup_of_closed capturedURS (by decide)
    (fun j => derivedUrsGLagrange_generator_eq capturedURS (by decide) j) i hlen

/-- The captured Lagrange commitment key: the exported prefix, completed by the canonical monomial
commitment beyond it. Every `LagrangeCommitmentKey capturedURS (omegaOf capturedURS.k)` equals this
one (`LagrangeCommitmentKey.instSubsingleton`). -/
def capturedLagrangeKey :
    LagrangeCommitmentKey capturedURS (omegaOf capturedURS.k) :=
  LagrangeCommitmentKey.ofPrefix capturedURS (omegaOf capturedURS.k)
    capturedUrsGLagrange capturedUrsGLagrange_prefix

/-- **Halo2's captured `commit_lagrange` is the abstract Lagrange-key instance commitment.** The
captured computation sums canonical representatives against the exported generators and adds the
default blind `w`; the abstract one commits the zero-padded row vector against the key. They agree
for any column that fits inside the exported prefix — which every captured column does
(`capturedPublicInstances_within_lagrange`).

The key is universally quantified because `LagrangeCommitmentKey` records no choice: this discharges
the identity against whichever key a downstream statement names, once its domain generator is
recognised as the captured one. -/
theorem commitLagrange_eq_commitInstance {omega : Fp} (homega : omega = omegaOf capturedURS.k)
    (key : LagrangeCommitmentKey capturedURS omega)
    (values : List Fp) (hfit : values.length ≤ capturedUrsGLagrange.length) :
    commitLagrange values = key.commitInstance values 1 := by
  subst homega
  have hdomain : values.length ≤ 2 ^ capturedURS.k :=
    le_trans hfit (by decide)
  rw [Subsingleton.elim key capturedLagrangeKey, capturedLagrangeKey,
    LagrangeCommitmentKey.ofPrefix_commitInstance_eq capturedURS (omegaOf capturedURS.k)
      capturedUrsGLagrange capturedUrsGLagrange_prefix values 1 hfit hdomain,
    ← LagrangeCommitmentKey.commitPrefixNat_eq_commitPrefix,
    LagrangeCommitmentKey.commitPrefixNat, commitLagrange]
  -- Only the blind differs in spelling: halo2's default blind is `1`, and `(1 : Fp).val • w = w`.
  congr 1
  rw [show ((1 : Fp).val) = 1 from rfl, one_nsmul]

/-- A column whose every row reads zero commits to the blind alone. Used for the instance columns
the Action layout does not populate: the circuit serializes them as zeros, the capture omits them
entirely, and both commit to `w`. -/
theorem commitInstance_of_rows_zero {omega : Fp}
    (key : LagrangeCommitmentKey capturedURS omega)
    {values : List Fp} (hzero : ∀ i, values.getD i 0 = 0) (blind : Fp) :
    key.commitInstance values blind = blind • capturedURS.w := by
  rw [LagrangeCommitmentKey.commitInstance, LagrangeCommitmentKey.commitRows,
    show zeroPaddedRows (n := 2 ^ capturedURS.k) values = 0 from funext fun i => hzero (i : ℕ)]
  rw [show commitGen key.generators (0 : Fin (2 ^ capturedURS.k) → Fp) = 0 by
    simp [commitGen], zero_add]

/-! ## The captured public inputs as the circuit's own record -/

/-- **The captured public inputs, read back as the Action circuit's public-input record.** The
capture stores one flat column of ten field elements per proof
(`capturedPublicInstances`); the circuit's `PublicInputs` names those ten rows. -/
def capturedActionInputs : Fin Fixture.shape.numProofs → PublicInputs Fp := fun proofIndex =>
  let column := capturedPublicInstances.getD (proofIndex.val * capturedNumInstanceColumns) []
  { anchor := column.getD 0 0
    cvX := column.getD 1 0
    cvY := column.getD 2 0
    nfOld := column.getD 3 0
    rkX := column.getD 4 0
    rkY := column.getD 5 0
    cmx := column.getD 6 0
    enableSpend := column.getD 7 0
    enableOutput := column.getD 8 0
    disableCrossAddress := column.getD 9 0 }

/-- **The captured column is the circuit's serialization of the captured record.** Ten field
elements, checked against the capture. -/
theorem publicInputRows_capturedActionInputs (proofIndex : Fin Fixture.shape.numProofs) :
    actionCircuit.publicInputRows (capturedActionInputs proofIndex) ⟨0⟩ =
      capturedPublicInstances.getD (proofIndex.val * capturedNumInstanceColumns) [] := by
  rw [actionCircuit_publicInputRows_zero]
  fin_cases proofIndex
  native_decide

/-! ## The seam: the capstone's family is the captured one -/

/-- The structurally derived Action domain exponent agrees with the captured URS's `k = 11`. -/
theorem actionCircuit_domainExponent : actionCircuit.domainExponent = capturedURS.k := by
  rw [Halo2.TopLevelCircuit.domainExponent,
    actionCircuit_shape_eq, actionShape_k]
  rfl

/-- The derived verifying key's domain generator is the captured URS's, so a key stated at that key's
`omega` is a key at the captured domain. -/
theorem actionCircuit_omega_captured :
    actionCircuit.omega = omegaOf capturedURS.k := by
  rw [TopLevelCircuit.omega, actionCircuit_domainExponent]

/-- **The circuit-derived public-instance family is the fixture's.**
`actionCircuit.instanceCommitment` computes commitments from the public inputs the way halo2's
`verify_proof` computes them from `instances`. At the captured public inputs that family is
`Fixture.derivedInstanceCommitment`, the family the captured artifacts are exercised against.

This is the join: the circuit model and capture speak of the same
group elements. -/
theorem instanceCommitment_capturedActionInputs :
    actionCircuit.instanceCommitment capturedURS capturedActionInputs =
      Fixture.derivedInstanceCommitment := by
  funext proofIndex column
  show (actionCircuit.instanceCommitmentKey capturedURS).commitInstance
      (actionCircuit.publicInputRows (capturedActionInputs proofIndex) ⟨column⟩) 1 =
    commitLagrange
      (capturedPublicInstances.getD
        (proofIndex.val * capturedNumInstanceColumns + column) [])
  rcases eq_or_ne column 0 with rfl | hcolumn
  · -- The single populated column: the circuit's serialization is the captured column itself.
    rw [Nat.add_zero, publicInputRows_capturedActionInputs proofIndex,
      commitLagrange_eq_commitInstance
        ((actionCircuit.toVerifierKey_omega capturedURS).trans
          actionCircuit_omega_captured) _ _
        (by fin_cases proofIndex; native_decide)]
  · -- Every other column: the circuit serializes zeros, the capture stores nothing, both give `w`.
    rw [commitInstance_of_rows_zero _ (actionCircuit_publicInputRows_ne_zero _ hcolumn),
      List.getD_eq_default _ _ (by
        simp only [capturedPublicInstances, capturedNumInstanceColumns, List.length_cons,
          List.length_nil]
        omega),
      commitLagrange]
    simp

/-- **The circuit model's family is the captured commitment points.** Composing the seam with the
capture's own derivation (`instance_commitments_derived`): at the captured public
inputs, the circuit-derived commitments are exactly the points the deployed verifier used. -/
theorem instanceCommitment_eq_capturedInstanceCommitments
    (proofIndex : Fin Fixture.shape.numProofs) {column : ℕ}
    (hcolumn : column < capturedNumInstanceColumns) :
    actionCircuit.instanceCommitment capturedURS capturedActionInputs
        proofIndex column =
      capturedInstanceCommitments.getD
        (proofIndex.val * capturedNumInstanceColumns + column) 0 := by
  have hzero : column = 0 := by
    simpa only [capturedNumInstanceColumns, Fixture.shape, Nat.lt_one_iff] using hcolumn
  subst hzero
  rw [instanceCommitment_capturedActionInputs, ← instance_commitments_derived]
  fin_cases proofIndex
  have hlt : 0 < capturedPublicInstances.length := by
    simp only [capturedPublicInstances, List.length_cons]
    omega
  simp only [Fixture.derivedInstanceCommitment, List.getD_eq_getElem?_getD, List.getElem?_map,
    Nat.zero_mul, Nat.add_zero]
  rw [List.getElem?_eq_getElem hlt]
  rfl

assert_no_sorry commitLagrange_eq_commitInstance
assert_no_sorry publicInputRows_capturedActionInputs
assert_no_sorry instanceCommitment_capturedActionInputs
assert_no_sorry instanceCommitment_eq_capturedInstanceCommitments

end Zcash.Snark.Keygen

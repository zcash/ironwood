import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Fixtures.PostNu63
import Zcash.Circuits.Action.FieldSupport
import Zcash.Circuits.Integration.PermutationCompiler
import Mathlib.Util.AssertNoSorry

/-!
# The multi-action verifying key, certified derived

The captured multi-action verifying key equals the key derived end-to-end from the ported
`configure`/keygen at the captured URS — transported from the single-action certificate
(`Keygen/Certificate.lean`), never re-evaluating keygen. Two facts make the transport
definitional: the two dumps carry one and the same URS and verifying-key commitment points
(`Fixtures/PostNu63.lean`). Verifying keys are indexed only by the circuit-owned shape, so the
proof count does not enter this transport.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open Zcash.Snark.PostNu63Fixture
open Zcash.Circuits.Action (actionCircuit)

/-- The Action circuit shape is the circuit-owned part of this capture's proof shape. -/
theorem actionCircuitShape_eq : actionCircuit.shape = shape.toCircuitShape :=
  Keygen.actionCircuitShape_eq_fixtureCircuitShape

/-- The Action circuit's derived key at this capture's URS, transported to the fixture shape. -/
def derivedVk : VerifyingKey shape Fp G :=
  actionCircuitShape_eq ▸ actionCircuit.toVerifierKey capturedURS

/-- **The captured multi-action verifying key is fully derived.** -/
theorem vk_eq_derived : vk = derivedVk := by
  unfold derivedVk
  rw [captures_use_same_urs]
  have hshape : actionCircuitShape_eq = Keygen.actionCircuitShape_eq_fixtureCircuitShape :=
    Subsingleton.elim _ _
  rw [hshape]
  exact captures_use_same_vk.trans Keygen.vk_eq_toVerifierKey

/-- Compatibility spelling: the captured key is the circuit's derived verifier key. -/
theorem vk_eq_toVerifierKey : vk = derivedVk := vk_eq_derived

/-- The capture inherits the derived key's domain and coset laws. -/
instance vkFieldSupport : VerifyingKey.FieldSupport vk := by
  rw [vk_eq_derived]
  exact VerifyingKey.fieldSupport_cast actionCircuitShape_eq
    (actionCircuit.toVerifierKey capturedURS)

/-- The capture inherits the compiler's query and permutation layout laws. -/
instance vkWellFormed : VerifyingKey.WellFormed vk := by
  rw [vk_eq_derived]
  exact VerifyingKey.wellFormed_cast actionCircuitShape_eq
    (actionCircuit.toVerifierKey capturedURS)

assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.Fixture2

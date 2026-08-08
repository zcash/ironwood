import Zcash.Snark.Fixtures.SingleAction.Honest.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Soundness.AGM.StraightLineOrchardConsensusBounds
import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.Action.AdaptiveStatementProfile
import Zcash.Snark.Soundness.Action.AdaptiveStatementReads

/-!
# The base of the Action capstone chain

The imports the rest of `Capstones/Action/` is stated over, and the shape identification that
carries merged Action proof parameters onto the captured fixture shape.  The knowledge-failure
sets the endpoints are about are defined with the layer that proves them, in `Soundness/Action/`.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal


/-- Merging Action proof parameters yields the matching fixture shape. -/
theorem actionProofShape_eq_maxShape (numProofs : ℕ) :
    actionCircuit.shape.withProofParams (actionProofParamsFor numProofs) =
      Zcash.Snark.FixtureMax.shape numProofs := by
  rw [actionShapeFor_eq_fixtureShape]
  rfl

end Zcash.Snark.Capstone

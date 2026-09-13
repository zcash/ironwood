import Zcash.Snark.Fixtures.Prover.Division
import Zcash.Snark.Fixtures.Prover.Replay
import Zcash.Snark.Fixtures.Prover.SingleAction
import Zcash.Snark.Fixtures.Prover.MultiAction
import Zcash.Snark.Fixtures.ReducedMask.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.ReducedMask.MultiAction.Honest.Fixture
import Zcash.Snark.ZeroKnowledge.Zakura.Attempt

/-!
# Explicit execution checks for the Rust prover captures

The `Main.lean` runner checks both complete captured executions in
Lean CI. This module is compiled by `FixtureCheck`, outside the production import
root. The generic replay equality is proved in `Replay`; the runner compares
external captured data and introduces no native-decision axioms.

The generated Lean modules come directly from Common's Rust exporter. CI checks
their hashes and regenerates them through the same pipeline as the verifier
fixtures. Expected Rust outputs are supplied only to comparisons after replay.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- A failed fixture comparison fails the check. -/
private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError ("prover capture mismatch: " ++ label))

/-- A bounded read beyond every two-Action commitment slot retains its value and traversal cost. -/
private def checkWideBoundedListRead : IO Unit := do
  let values := List.range 64
  let result := getFinListCosted 7 values ⟨63, by decide⟩
  ensure "wide bounded list read" (result == (63, 134))

/-- A polynomial wider than the constraint numerator exercises the interpreter's normal stack.
For `g = 1 + X + ... + X^19998`, the input is `(X - 7) * g + 3`. -/
private def checkWideSyntheticDivision : IO Unit := do
  let values : List Fp := -4 :: (List.replicate 19998 (-6) ++ [1])
  let result := syntheticDivision 7 values
  ensure "wide synthetic quotient" (result.1 == List.replicate 19999 1 ++ [0])
  ensure "wide synthetic remainder" (result.2 == 3)

/-- The last block crosses the former recursive-read limit and excludes the next coefficient. -/
private def checkWideCoefficientBlocks : IO Unit := do
  let values : List Fp := List.replicate 16383 0 ++ [7, 9]
  let expected := List.replicate 7 (List.replicate 2048 (0 : Fp)) ++
    [List.replicate 2047 0 ++ [7]]
  ensure "wide coefficient blocks" (coefficientBlocks 2048 8 values == expected)
  ensure "coefficient block padding" (coefficientBlocks 4 2 [1] == [[1, 0, 0, 0], [0, 0, 0, 0]])

/-- The largest collapse exponent, `2048 * 7`, fits the interpreter's normal stack for both the
coefficients and the blinds. The domain root `ω` has `ω ^ 2048 = 1`, so collapsing the constant
pieces `1, …, 8` returns their sum, and eight unit blinds collapse to `8`. -/
private def checkWideQuotientCollapse : IO Unit := do
  ensure "wide quotient collapse" (collapsedQuotient (Zcash.Arithmetic.omegaOf 11)
    (List.ofFn fun j : Fin 8 => [((j.val + 1 : ℕ) : Fp)]) == [36])
  ensure "wide quotient blind collapse"
    ((collapsedQuotientBlind (actions := 1) (Zcash.Arithmetic.omegaOf 11) fun _ => (1, 0)).1 == 8)

/-- Identify the first differing emitted message without dumping the private fixture inputs. -/
private def checkMessages (label : String) (actual expected : List (TranscriptElt Fp VestaG)) : IO Unit := do
  ensure (label ++ " message count") (actual.length == expected.length)
  for i in [:actual.length] do
    unless decide (actual[i]? = expected[i]?) do
      throw (IO.userError s!"prover capture mismatch: {label}, message {i}")

/-- Compare the complete encoded buffer with the original Rust output, including its length. -/
private def checkProofBytes (label : String) (actual expected : List UInt8) : IO Unit :=
  ensure (label ++ " proof bytes") (actual == expected)

/-- Exercise the actual comparison routine and require it to reject a tampered transcript. -/
private def expectMismatch (label : String) (check : IO Unit) : IO Unit := do
  let rejected ← try
    check
    pure false
  catch _ => pure true
  ensure (label ++ " was not rejected") rejected

/-- Commit all captured public rows and compare them to the existing captured verification key. -/
private def checkKeyRows {actions : ℕ}
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG) (inputs : CaptureInputs) : IO Unit := do
  let generators : Fin 2048 → VestaG := fun i => inputs.generators[i.val]?.getD 0
  for i in List.finRange 29 do
    let coefficients := rowCoefficients 11 (by decide) (inputFixed inputs i)
    ensure s!"fixed commitment {i.val}"
      (decide (commitPolynomial generators inputs.w coefficients 1 = vk.fixedCommitment i.val))
  for i in List.finRange 15 do
    let coefficients := rowCoefficients 11 (by decide) (inputSigma inputs i)
    ensure s!"permutation commitment {i.val}"
      (decide (commitPolynomial generators inputs.w coefficients 1 = vk.permutationCommonCommitment i))

/-- Check a real proof call against both its own captured outputs and the existing verifier anchor. -/
private def checkCase {actions : ℕ} (name : String) (fixture : ProverFixture)
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG)
    (generators : Fin 2048 → VestaG) (W U : VestaG) (publicInputs : List (List Fp))
    (initial : List (TranscriptElt Fp VestaG)) (ch : Challenges 11 Fp)
    (expected : ProofString (plonkProofShape actions 11) Fp VestaG) (mutate : Bool) : IO Unit := do
  let capture ← match decodeCapture actions fixture with
    | .ok capture => pure capture
    | .error error => throw (IO.userError error)
  let inputs := capture.inputs
  ensure (name ++ " generators") (decide (inputs.generators.toList = List.ofFn generators))
  ensure (name ++ " W/U") (decide (inputs.w = W ∧ inputs.u = U))
  ensure (name ++ " public inputs") (decide (inputs.instances.toList.map Array.toList = publicInputs))
  ensure (name ++ " initialization") (decide (capture.initialization = initial))
  ensure (name ++ " public acceptance") (Zakura.acceptsPublicPrefix capture.initialization)
  ensure (name ++ " challenges") (decide (inputs.challenges.toList = plonkChallengeSequence ch))
  checkMessages (name ++ " verifier anchor") capture.messages (plonkAttemptTrace expected)
  checkProofBytes (name ++ " verifier anchor encoding") (encodedPlonkAttempt (ch, expected)).2.proof
    capture.proof
  expectMismatch (name ++ " empty proof buffer") (checkProofBytes name [] capture.proof)
  expectMismatch (name ++ " changed proof byte")
    (checkProofBytes name (capture.proof.modify 0 (· + 1)) capture.proof)
  expectMismatch (name ++ " truncated proof buffer")
    (checkProofBytes name capture.proof.dropLast capture.proof)
  expectMismatch (name ++ " extra proof byte")
    (checkProofBytes name (capture.proof ++ [0]) capture.proof)
  IO.println (name ++ ": checking public-row commitments")
  (← IO.getStdout).flush
  checkKeyRows vk inputs
  IO.println (name ++ ": replaying the complete private tape")
  (← IO.getStdout).flush
  let proof := replayProof vk inputs
  let trace := plonkAttemptTrace proof
  checkMessages name trace capture.messages
  let attempt := (encodedPlonkAttempt (inputChallenges inputs, proof)).2
  checkProofBytes name attempt.proof capture.proof
  ensure (name ++ " terminal result") (decide (attempt.status = .complete))
  ensure (name ++ " released outcome") (decide (Zakura.observeAttempt attempt = .proof capture.proof))
  expectMismatch (name ++ " changed scalar") (checkMessages name
    (trace.set (trace.length - 1) (.scalar (proof.ipaF + 1))) capture.messages)
  expectMismatch (name ++ " reordered messages") (checkMessages name trace.reverse capture.messages)
  expectMismatch (name ++ " truncated messages") (checkMessages name trace.dropLast capture.messages)
  expectMismatch (name ++ " extra message") (checkMessages name (trace ++ [.scalar 0]) capture.messages)
  if mutate then
    IO.println (name ++ ": checking sensitivity to a changed raw RNG draw")
    (← IO.getStdout).flush
    let changed := { inputs with rawTape := inputs.rawTape.modify (inputs.rawTape.length - 1) (· + 1) }
    let changedTrace := plonkAttemptTrace (replayProof vk changed)
    expectMismatch (name ++ " changed raw draw") (checkMessages name changedTrace capture.messages)
  ensure (name ++ " truncated events rejected")
    (match decodeCapture actions { fixture with events := fixture.events.pop } with
      | .error _ => true | .ok _ => false)
  IO.println (name ++ ": all messages, proof bytes, public anchors, outcome, and negative checks passed")
  (← IO.getStdout).flush

/-- Check the one-Action execution and the wide-input regressions. -/
def checkSingleCapture : IO Unit := do
  checkWideBoundedListRead
  checkWideSyntheticDivision
  checkWideCoefficientBlocks
  checkWideQuotientCollapse
  checkCase "single-honest" SingleAction.captured
    FixtureReduced.vk FixtureReduced.capturedURS.g FixtureReduced.capturedURS.w FixtureReduced.capturedURS.u
    FixtureReduced.capturedPublicInstances FixtureReduced.capturedInit FixtureReduced.ch FixtureReduced.ps true

/-- Check the complete two-Action execution. -/
def checkMultiCapture : IO Unit :=
  checkCase "multi-honest" MultiAction.captured
    FixtureReduced2.vk FixtureReduced2.capturedURS.g FixtureReduced2.capturedURS.w FixtureReduced2.capturedURS.u
    FixtureReduced2.capturedPublicInstances FixtureReduced2.capturedInit FixtureReduced2.ch FixtureReduced2.ps false

/-- Check the complete one- and two-Action executions imported from Rust-generated Lean modules. -/
def checkCaptures : IO Unit := do
  checkSingleCapture
  checkMultiCapture

end Zcash.Snark.Fixtures.Prover

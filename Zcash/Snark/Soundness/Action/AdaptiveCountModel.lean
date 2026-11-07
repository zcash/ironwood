import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge
import Zcash.Snark.Soundness.FiatShamir.ActionCount

/-!
# Adaptive Action-count Fiat--Shamir adversaries

The fixed-count Action theorem gives each action count its own bounded transcript
domain.  That interface is convenient for a single proof, but it cannot model an
adversary that shares one random oracle and one query budget across several counts
before deciding which count to output.

This module supplies that missing game.  `ComputedAdaptiveActionCountFSFamily`
runs one labeled online-AGM adversary over the largest transcript domain and puts
the selected count in the adversary's output.  Consequently the count may depend
on any earlier random-oracle answers and `Q` bounds the whole computation, rather
than one separately sampled computation for every possible count.
-/

namespace Zcash.Snark

open Zcash.Common
open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

/-- Closed form of the bounded Action transcript size.  Making the dependence on
the number of proofs explicit lets differently sized Action proofs inhabit one
common bounded domain. -/
def adaptiveActionCountTranscriptLimit (numProofs : ℕ) : ℕ :=
  72 * numProofs + 106

/-- The fixed-count Action transcript bound is exactly the closed form above. -/
theorem adaptiveActionStatementTranscriptLimit_eq (numProofs : ℕ) :
    preIpaLen (AdaptiveActionStatementShape (actionProofParamsFor numProofs))
        (adaptiveStatementInitLength
          (AdaptiveActionStatementShape (actionProofParamsFor numProofs))) 10 +
      3 * (AdaptiveActionStatementShape (actionProofParamsFor numProofs)).k =
        adaptiveActionCountTranscriptLimit numProofs := by
  simp only [AdaptiveActionStatementShape, actionShapeFor_eq_fixtureShape,
    preIpaLen, adaptiveStatementInitLength]
  norm_num [Zcash.Snark.Fixture.shape]
  simp [adaptiveActionCountTranscriptLimit]
  omega

theorem adaptiveActionCountTranscriptLimit_mono {n m : ℕ} (h : n ≤ m) :
    adaptiveActionCountTranscriptLimit n ≤ adaptiveActionCountTranscriptLimit m := by
  unfold adaptiveActionCountTranscriptLimit
  omega

/-- All Action counts use the same deployed degree-`2^k` augmented basis. -/
abbrev AdaptiveActionCountBasis :=
  AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG

/-- `n : Fin maxActions` denotes a proof containing `n + 1` Actions. -/
abbrev adaptiveActionCountParams (n : ℕ) := actionProofParamsFor (n + 1)

/-- One common random-oracle domain large enough for every permitted Action count. -/
abbrev AdaptiveActionCountTranscript (maxActions : ℕ) :=
  BTranscript Fp VestaG (adaptiveActionCountTranscriptLimit maxActions)

/-- Widen a bounded transcript without changing the transcript seen by the oracle. -/
def BTranscript.widen {F G : Type*} {L L' : ℕ} (h : L ≤ L')
    (t : BTranscript F G L) : BTranscript F G L' :=
  ⟨t.val, t.prop.trans h⟩

@[simp] theorem BTranscript.widen_val {F G : Type*} {L L' : ℕ} (h : L ≤ L')
    (t : BTranscript F G L) : (t.widen h).val = t.val := rfl

/-- Normalize the original shape-indexed bound to its count-indexed closed form. -/
def normalizeAdaptiveActionCountTranscript (numProofs : ℕ)
    (t : AdaptiveActionStatementTranscript (actionProofParamsFor numProofs)) :
    BTranscript Fp VestaG (adaptiveActionCountTranscriptLimit numProofs) :=
  ⟨t.val, by
    rw [← adaptiveActionStatementTranscriptLimit_eq numProofs]
    exact t.prop⟩

@[simp] theorem normalizeAdaptiveActionCountTranscript_val (numProofs : ℕ)
    (t : AdaptiveActionStatementTranscript (actionProofParamsFor numProofs)) :
    (normalizeAdaptiveActionCountTranscript numProofs t).val = t.val := rfl

/-- Embed one selected count's transcript in the shared domain. -/
def widenAdaptiveActionCountTranscript {maxActions : ℕ} (n : Fin maxActions)
    (t : AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) :
    AdaptiveActionCountTranscript maxActions :=
  (normalizeAdaptiveActionCountTranscript (n + 1) t).widen
    (adaptiveActionCountTranscriptLimit_mono (Nat.succ_le_iff.mpr n.isLt))

@[simp] theorem widenAdaptiveActionCountTranscript_val {maxActions : ℕ}
    (n : Fin maxActions)
    (t : AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) :
    (widenAdaptiveActionCountTranscript n t).val = t.val := by
  exact BTranscript.widen_val _ _

/-- A count together with a well-typed output for precisely that selected count. -/
structure AdaptiveActionCountOutput (maxActions : ℕ)
    (components : (n : Fin maxActions) → ComputedAdaptiveActionStatementFSFamily
      (adaptiveActionCountParams n))
    (basis : AdaptiveActionCountBasis) where
  count : Fin maxActions
  output : AdaptiveActionStatementOutput (adaptiveActionCountParams count) basis
    ((components count).fixedRepresentations basis)

/-- One shared-oracle, shared-budget online-AGM game whose Action count is selected
by the adversary's output rather than fixed before the run. -/
structure ComputedAdaptiveActionCountFSFamily (maxActions : ℕ) where
  components : (n : Fin maxActions) → ComputedAdaptiveActionStatementFSFamily
    (adaptiveActionCountParams n)
  adversary : (basis : AdaptiveActionCountBasis) →
    LabeledOracleComp (AdaptiveActionCountTranscript maxActions) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis)
      (AdaptiveActionCountOutput maxActions components basis)
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAdaptiveActionCountFSFamily

abbrev Coins {maxActions : ℕ} (_family : ComputedAdaptiveActionCountFSFamily maxActions) :=
  AdaptiveActionCountTranscript maxActions → Fp

def runOutput {maxActions : ℕ} (family : ComputedAdaptiveActionCountFSFamily maxActions)
    (basis : AdaptiveActionCountBasis) (O : family.Coins) :
    AdaptiveActionCountOutput maxActions family.components basis :=
  (family.adversary basis).run O

end ComputedAdaptiveActionCountFSFamily
end Zcash.Snark

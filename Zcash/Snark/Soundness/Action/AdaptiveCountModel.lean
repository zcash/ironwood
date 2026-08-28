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

`ofFixedCount` proves backwards compatibility constructively: every existing
fixed-count family embeds as the constant-count special case without changing its
run or query budget.
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

theorem widenAdaptiveActionCountTranscript_injective {maxActions : ℕ}
    (n : Fin maxActions) : Function.Injective (widenAdaptiveActionCountTranscript n) := by
  intro a b h
  apply Subtype.ext
  simpa only [widenAdaptiveActionCountTranscript, BTranscript.widen_val,
    normalizeAdaptiveActionCountTranscript_val] using
    congrArg (fun t : AdaptiveActionCountTranscript maxActions => t.val) h

/-- Transport an online-AGM annotation along transcript widening.  The point list is
unchanged, so its algebraic representations are unchanged as well. -/
def widenAdaptiveActionCountQuery {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis}
    {t : AdaptiveActionStatementTranscript (adaptiveActionCountParams n)}
    (query : AlgebraicTranscriptQuery (F := Fp) basis t) :
    AlgebraicTranscriptQuery (F := Fp) basis (widenAdaptiveActionCountTranscript n t) :=
  { representedPoints := query.representedPoints
    points_eq := query.points_eq }

/-- Reindex a fixed-count labeled oracle computation into the shared transcript
domain.  This changes neither its answers nor its adaptive control flow. -/
def liftAdaptiveActionCountComp {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis} {alpha : Type*} :
    LabeledOracleComp
        (AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis) alpha →
      LabeledOracleComp (AdaptiveActionCountTranscript maxActions) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis) alpha
  | .pure a => .pure a
  | .query t label next =>
      .query (widenAdaptiveActionCountTranscript n t)
        (widenAdaptiveActionCountQuery n label)
        (fun answer => liftAdaptiveActionCountComp n (next answer))

theorem erase_liftAdaptiveActionCountComp {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis} {alpha : Type*}
    (A : LabeledOracleComp
      (AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis) alpha) :
    (liftAdaptiveActionCountComp n A).erase =
      A.erase.mapDomain (widenAdaptiveActionCountTranscript n) := by
  induction A with
  | pure => rfl
  | query t label next ih =>
      simp only [liftAdaptiveActionCountComp, LabeledOracleComp.erase_query,
        OracleComp.mapDomain]
      congr
      funext answer
      exact ih answer

@[simp] theorem run_liftAdaptiveActionCountComp {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis} {alpha : Type*}
    (A : LabeledOracleComp
      (AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis) alpha)
    (O : AdaptiveActionCountTranscript maxActions → Fp) :
    (liftAdaptiveActionCountComp n A).run O =
      A.run (fun t => O (widenAdaptiveActionCountTranscript n t)) := by
  unfold LabeledOracleComp.run
  rw [erase_liftAdaptiveActionCountComp]
  simpa only [Function.comp_apply] using
    (OracleComp.run_mapDomain (widenAdaptiveActionCountTranscript n) A.erase O)

theorem queryBound_liftAdaptiveActionCountComp {maxActions : ℕ} (n : Fin maxActions)
    {basis : AdaptiveActionCountBasis} {alpha : Type*}
    {A : LabeledOracleComp
      (AdaptiveActionStatementTranscript (adaptiveActionCountParams n)) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis) alpha}
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (liftAdaptiveActionCountComp n A).QueryBound Q := by
  rw [LabeledOracleComp.QueryBound, erase_liftAdaptiveActionCountComp]
  exact OracleComp.queryBound_mapDomain _ hQ

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

/-- Embed a legacy fixed-count family as a constant-count adversary. -/
def ofFixedCount {maxActions : ℕ}
    (components : (n : Fin maxActions) → ComputedAdaptiveActionStatementFSFamily
      (adaptiveActionCountParams n))
    (n : Fin maxActions) : ComputedAdaptiveActionCountFSFamily maxActions where
  components := components
  adversary := fun basis =>
    (liftAdaptiveActionCountComp n ((components n).adversary basis)).bind fun output =>
      .pure { count := n, output := output }
  Q := (components n).Q
  queryBound := by
    intro basis
    rw [LabeledOracleComp.QueryBound, LabeledOracleComp.erase_bind]
    simpa only [Nat.add_zero] using
      OracleComp.queryBound_bind
        (queryBound_liftAdaptiveActionCountComp n ((components n).queryBound basis))
        (fun output => OracleComp.QueryBound.pure
          ({ count := n, output := output } :
            AdaptiveActionCountOutput maxActions components basis) 0)

/-- The constant-count embedding preserves the complete fixed-family run. -/
@[simp] theorem runOutput_ofFixedCount {maxActions : ℕ}
    (components : (n : Fin maxActions) → ComputedAdaptiveActionStatementFSFamily
      (adaptiveActionCountParams n))
    (n : Fin maxActions) (basis : AdaptiveActionCountBasis)
    (O : AdaptiveActionCountTranscript maxActions → Fp) :
    runOutput (ofFixedCount components n) basis O =
      { count := n
        output := (components n).runOutput basis
          (fun t => O (widenAdaptiveActionCountTranscript n t)) } := by
  simp [runOutput, ofFixedCount, ComputedAdaptiveActionStatementFSFamily.runOutput]
  rfl

end ComputedAdaptiveActionCountFSFamily
end Zcash.Snark

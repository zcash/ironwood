import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkPermutationMasking
import Zcash.Snark.ZeroKnowledge.Observation

/-!
# Usable-row disclosure in the complete reference proof

The scalar below is read from the same typed `ProofString` whose distribution is
bounded by the joint simulation theorem. Its computation includes the complete
private tape, quotient, multi-opening, and IPA tail. At a usable domain row, the
unrotated advice query is exactly the original witness cell on every tape.

This concerns the total reference computation. A zero-knowledge impossibility
claim for the implementation requires two permitted satisfying witnesses for
the same public statement and correspondence for execution, failures, and codecs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The typed proof's current-row advice scalar evaluates the actual constructed row polynomial. -/
theorem plonkVerifierProofFromTape_advice_current {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (tape : Fin (plonkJointSampleCount construct urs.k) → Fp)
    (a : Fin actions) (c : Fin 10) :
    (plonkVerifierProofFromTape construct history urs vk pub ch tape).adviceEvals a
        (c.castLE (by change 10 ≤ 25; decide)) =
      (privateColumnPolynomial
        (plonkMaterialFromTape construct history
          ((splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12)
            (ipaSampleCount urs.k) Fp) tape).1).1 (.advice a c)).eval ch.x := by
  change privateColumnView _ (.advice a (plonkAdviceQueryOrder (c.castLE (by decide))).1)
    (((plonkAdviceQueryOrder (c.castLE (by decide))).2.castLE (by decide : 3 ≤ 4)).castSucc) = _
  rw [plonkAdviceQueryOrder_current]
  exact privateColumnView_observe _ _ (.advice a c) (0 : Fin 5)

/-- Every complete field tape emits the original advice cell when `x` is its usable domain point. -/
theorem plonkVerifierProofFromTape_advice_usable {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness ch) urs.k) → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hx : ch.x = omegaOf 11 ^ row.val) :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch tape).adviceEvals
        a (c.castLE (by change 10 ≤ 25; decide)) = witness a c row := by
  rw [plonkVerifierProofFromTape_advice_current, hx]
  let construct := plonkTotalColumnConstructor vk pub witness ch
  let pre := ((splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12)
    (ipaSampleCount urs.k) Fp) tape).1
  let rowTape := (plonkPreIpaCoinsEquiv construct pre).1
  have hcount := plonkColumnSteps_row_samples construct
  let fixedTape : Fin (126 * actions) → Fp := rowTape ∘ Fin.cast hcount.symm
  have hcast : fixedTape ∘ Fin.cast hcount = rowTape := by
    funext i
    rfl
  change (privateColumnPolynomial (columnRowsFromTape (plonkColumnSteps construct) [] rowTape)
    (.advice a c)).eval (omegaOf 11 ^ row.val) = _
  have hkeep := plonkTotalColumnRows_advice_rows vk pub witness ch fixedTape a c row hrow
  change (privateColumnPolynomial
    (columnRowsFromTape (plonkColumnSteps construct) [] (fixedTape ∘ Fin.cast hcount))
    (.advice a c)).eval (omegaOf 11 ^ row.val) = _ at hkeep
  rwa [hcast] at hkeep

/-- Under wide-reduced prover randomness the disclosed usable-row scalar is a point mass. -/
theorem sampledPlonkVerifierProver_advice_usable {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges urs.k Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hx : ch.x = omegaOf 11 ^ row.val) :
    (sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch).map
        (fun ps => ps.adviceEvals a (c.castLE (by change 10 ≤ 25; decide))) =
      PMF.pure (witness a c row) := by
  have hcell := fun tape =>
    plonkVerifierProofFromTape_advice_usable urs vk pub witness ch tape a c row hrow hx
  rw [sampledPlonkVerifierProver_fromTape, ← sampleFieldsWith_map]
  simpa only [Function.comp_def, hcell] using sampleFieldsWith_const
    (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness ch) urs.k)
    (witness a c row) fieldSample

/-- Different usable cells give different complete reference-proof laws at that domain challenge. -/
theorem sampledPlonkVerifierProver_ne_of_usable_cell {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges urs.k Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hx : ch.x = omegaOf 11 ^ row.val) (hcell : left a c row ≠ right a c row) :
    sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub left ch) [] urs vk pub ch ≠
      sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub right ch) [] urs vk pub ch := by
  intro heq
  have hproject := congrArg (fun law : PMF (ProofString (plonkProofShape actions urs.k) Fp G) =>
    law.map fun ps => ps.adviceEvals a (c.castLE (by change 10 ≤ 25; decide))) heq
  dsimp only at hproject
  rw [sampledPlonkVerifierProver_advice_usable urs vk pub left ch a c row hrow hx,
    sampledPlonkVerifierProver_advice_usable urs vk pub right ch a c row hrow hx] at hproject
  have hmass := congrArg (fun law : PMF Fp => law (left a c row)) hproject
  simp [PMF.pure_apply, hcell] at hmass

/-- Retain the evaluation challenge and one current-row advice scalar from the complete verifier view. -/
def plonkAdviceObservation {actions k : ℕ} (a : Fin actions) (c : Fin 10)
    (view : PlonkFreshView actions k G) : Fp × Fp :=
  (view.1.x, view.2.adviceEvals a (c.castLE (by change 10 ≤ 25; decide)))

/-- Exact disclosure mass, averaging over the full challenge tape and all prover randomness. -/
theorem freshPlonkVerifierProver_advice_mass {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042) (value : Fp) :
    ((freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub witness) [] vk pub).map
      (plonkAdviceObservation a c)) (omegaOf 11 ^ row.val, value) =
        if value = witness a c row then (law.map fun ch => ch.x) (omegaOf 11 ^ row.val) else 0 := by
  rw [freshSampledPlonkVerifierProver, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, plonkAdviceObservation]
  exact projectedKernelView_apply_at_point law
    (fun ch => sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch)
    (fun ch => ch.x) (fun ps => ps.adviceEvals a (c.castLE (by change 10 ≤ 25; decide)))
    (omegaOf 11 ^ row.val) (witness a c row) value
    (fun ch hx => sampledPlonkVerifierProver_advice_usable urs vk pub witness ch a c row hrow hx)

/-- The domain-point mass is a lower bound on event bias between different witness-cell proof laws. -/
theorem freshPlonkVerifierProver_advice_separation {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hcell : left a c row ≠ right a c row) (ε : ℝ≥0∞)
    (happrox : PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub left) [] vk pub)
      (freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub right) [] vk pub) ε) :
    (law.map fun ch => ch.x) (omegaOf 11 ^ row.val) ≤ ε := by
  have h := eventBias_map happrox (plonkAdviceObservation a c)
    {(omegaOf 11 ^ row.val, left a c row)}
  simp only [PMF.toOuterMeasure_apply_singleton] at h
  rw [freshPlonkVerifierProver_advice_mass urs law vk pub left a c row hrow,
    freshPlonkVerifierProver_advice_mass urs law vk pub right a c row hrow,
    if_pos rfl, if_neg hcell, zero_add] at h
  exact h

/-- If the usable point is possible, the complete fresh-challenge proof distributions are different. -/
theorem freshPlonkVerifierProver_ne_of_usable_cell {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hcell : left a c row ≠ right a c row)
    (hpoint : (law.map fun ch => ch.x) (omegaOf 11 ^ row.val) ≠ 0) :
    freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub left) [] vk pub ≠
      freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub right) [] vk pub := by
  intro heq
  have hzero : PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub left) [] vk pub)
      (freshSampledPlonkVerifierProver urs law (plonkTotalColumnConstructor vk pub right) [] vk pub) 0 := by
    intro event
    simp [heq]
  exact hpoint (le_antisymm
    (freshPlonkVerifierProver_advice_separation urs law vk pub left right a c row hrow hcell 0 hzero)
    bot_le)

/-- Wide reduction leaves a positive, explicit lower bound on the complete reference-proof distinction. -/
theorem widePlonkVerifierProver_advice_separation {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hcell : left a c row ≠ right a c row) (ε : ℝ≥0∞)
    (happrox : PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub left) [] vk pub)
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub right) [] vk pub) ε) :
    fieldSample (omegaOf 11 ^ row.val) ≤ ε := by
  simpa only [widePlonkChallenges_x] using
    freshPlonkVerifierProver_advice_separation urs (widePlonkChallenges urs.k) vk pub
      left right a c row hrow hcell ε happrox

/-- The actual wide-reduced reference laws cannot be identical when a usable advice cell differs. -/
theorem widePlonkVerifierProver_ne_of_usable_cell {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hcell : left a c row ≠ right a c row) :
    freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub left) [] vk pub ≠
      freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub right) [] vk pub :=
  freshPlonkVerifierProver_ne_of_usable_cell urs (widePlonkChallenges urs.k) vk pub
    left right a c row hrow hcell (by rw [widePlonkChallenges_x]; exact fieldSample_ne_zero _)

/-- No single exact simulator law can match these two complete reference-prover distributions. -/
theorem widePlonkVerifierProver_no_common_exact_simulator {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Fin actions → Fin 10 → Fin 2048 → Fp)
    (a : Fin actions) (c : Fin 10) (row : Fin 2048) (hrow : row.val < 2042)
    (hcell : left a c row ≠ right a c row) :
    ¬ ∃ simulate : PMF (PlonkFreshView actions urs.k G),
      freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
          (plonkTotalColumnConstructor vk pub left) [] vk pub = simulate ∧
        freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
          (plonkTotalColumnConstructor vk pub right) [] vk pub = simulate := by
  rintro ⟨simulate, hleft, hright⟩
  exact (widePlonkVerifierProver_ne_of_usable_cell urs vk pub left right a c row hrow hcell)
    (hleft.trans hright.symm)

end Zcash.Snark.ZeroKnowledge

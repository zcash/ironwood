import Zcash.Snark.ZeroKnowledge.PlonkOpening
import Zcash.Snark.ZeroKnowledge.PlonkTape
import Zcash.Snark.Verifier.FiatShamir

/-!
# Projecting the joint masks to the pre-IPA messages

The scalar list below is step 5's exact emitted order. The five subsequent scalars are
evaluations of the concrete opening polynomials. Together with all independently blinded
points, they are proved to be a public projection of the joint masking view. In particular,
the simulator does not need the private quotient pieces or a witness to form these messages.

This is an algebraic message computation with supplied challenges and totalized private
constructors. It does not yet model early failures, Fiat–Shamir generation, or establish
that the computed multi-opening gives a valid IPA input for every satisfying circuit witness.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Common
open Zcash.Common.Probability
open CompPoly
open scoped ENNReal

/-- The complete step-5 scalar order, including public evaluations and the retained terminal row. -/
def plonkEvaluationScalars {actions : ℕ} (pub : PlonkPublicPolynomials actions) (x : Fp)
    (column : PrivateColumnId actions → Fin 5 → Fp) (rEval : Fp) : List Fp :=
  (List.finRange actions).map (fun a => (pub.instances a).eval x) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 25).map (fun j =>
    let query := plonkAdviceQueryOrder j
    column (.advice a query.1) (query.2.castLE (by decide)))) ++
  (List.finRange 29).map (fun j => (pub.fixed (plonkFixedQueryOrder j)).eval x) ++ [rEval] ++
  (List.finRange 15).map (fun j => (pub.sigma j).eval x) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).flatMap (fun s =>
    [column (.permutationProduct a s) 0, column (.permutationProduct a s) 1] ++
      if s.val < 2 then [column (.permutationProduct a s) 3] else [])) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).flatMap (fun l =>
    [column (.lookupProduct a l) 0, column (.lookupProduct a l) 1,
     column (.lookupInput a l) 0, column (.lookupInput a l) 2, column (.lookupTable a l) 0]))

/-- The emitted pre-IPA fields; the final commitment is `Q'`, emitted after `evaluations`. -/
@[ext] structure PlonkPreIpaTranscript (columns : ℕ) (G : Type*) where
  points : Fin (columns + 10) → G
  evaluations : List Fp
  groupValues : Fin 5 → Fp

/-- All algebraic proof messages through `v₄`, using the verifier's existing transcript element type. -/
def PlonkPreIpaTranscript.messages {columns : ℕ} {G : Type*}
    (view : PlonkPreIpaTranscript columns G) : List (TranscriptElt Fp G) :=
  ((List.ofFn view.points).take (columns + 9)).map TranscriptElt.point ++
    view.evaluations.map TranscriptElt.scalar ++
    [TranscriptElt.point (view.points ⟨columns + 9, by omega⟩)] ++
    (List.ofFn view.groupValues).map TranscriptElt.scalar

/-- Public projection of the enriched masking trace to precisely these emitted fields. -/
def plonkPreIpaProjection {actions columns : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp) (view : PreIpaMaskView 5 (columns + 10) G) :
    PlonkPreIpaTranscript columns G where
  points := view.1
  evaluations := plonkEvaluationScalars pub x (privateColumnView view.2.1) view.2.2.1
  groupValues := Fin.cons view.2.2.2 (plonkPrivateGroupValues (actions := actions) x1 view.2.1)

/-- Compute the actual scalar messages from the private row polynomials and the five opening polynomials. -/
def honestPlonkPreIpaTranscript {actions columns : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (rows : ColumnHistory 2048)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (points : Fin (columns + 10) → G) :
    PlonkPreIpaTranscript columns G where
  points := points
  evaluations := plonkEvaluationScalars pub x
    (fun id i => (privateColumnPolynomial rows id).eval (plonkObservationPoints (omegaOf 11) x q i))
    ((linearMaskPolynomial coefficients).eval x)
  groupValues := fun i => (plonkOpeningPolynomials pub rows x x1 pieces coefficients i).eval q

section JointLaw

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The honest messages are exactly the projection of the joint mask view, with the actual `Q₀` offset. -/
theorem honestPlonkPreIpaTranscript_projection {actions columns : ℕ}
    (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (W : G)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (cores : ColumnHistory 2048 → Fp × Fp → Fin (columns + 10) → G)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) (blinds : Fin (columns + 10) → Fp) :
    honestPlonkPreIpaTranscript pub x x1 q rows (pieces rows) coefficients
        (blindedCommitments W (cores rows coefficients) blinds) =
      plonkPreIpaProjection pub x x1
        (honestPreIpaMaskView W (omegaOf 11) x q (plonkObservationPoints (omegaOf 11) x q) cores
          (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows)) rows coefficients blinds) := by
  apply PlonkPreIpaTranscript.ext
  · rfl
  · have hcols : privateColumnView (actions := actions)
          (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows) =
        fun id i => (privateColumnPolynomial rows id).eval (plonkObservationPoints (omegaOf 11) x q i) := by
      funext id i
      exact privateColumnView_observe rows _ id i
    simp only [honestPlonkPreIpaTranscript, plonkPreIpaProjection, honestPreIpaMaskView, hcols,
      linearMaskView, addSecondEquiv, linearMaskPair, linearMaskPolynomial, CPolynomial.eval_add,
      CPolynomial.eval_C, CPolynomial.eval_mul, CPolynomial.eval_X]
    rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [honestPlonkPreIpaTranscript, plonkPreIpaProjection, honestPreIpaMaskView,
        Fin.cons_zero, plonkFirstGroup_eval, linearMaskView, addSecondEquiv, linearMaskPair,
        linearMaskPolynomial, CPolynomial.eval_add, CPolynomial.eval_C, CPolynomial.eval_mul,
        CPolynomial.eval_X]
      rfl
    · exact (plonkPrivateGroupValues_observe pub rows x x1 q (pieces rows) coefficients j).symm

/-- Compute the pre-IPA messages using the source's batched mask and blind schedule. -/
def plonkPreIpaTranscriptFromTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (W : G)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (cores : ColumnHistory 2048 → Fp × Fp → Fin ((plonkColumnBatches construct).flatten.length + 10) → G)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) :
    PlonkPreIpaTranscript (plonkColumnBatches construct).flatten.length G :=
  let canonical := batchedPreIpaTapeEquiv (plonkColumnBatches construct) tape
  let coins := preIpaCoinEquiv (plonkColumnBatches construct).flatten canonical
  let rows := columnRowsFromTape (plonkColumnBatches construct).flatten history coins.1
  honestPlonkPreIpaTranscript pub x x1 q rows (pieces rows) coins.2.1
    (blindedCommitments W (cores rows coins.2.1) coins.2.2)

/-- The entire honest scalar computation factors through the public projection after tape conversion. -/
theorem plonkPreIpaTranscriptFromTape_factor {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (W : G)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (cores : ColumnHistory 2048 → Fp × Fp → Fin ((plonkColumnBatches construct).flatten.length + 10) → G) :
    plonkPreIpaTranscriptFromTape construct history pub x x1 q W pieces cores =
      plonkPreIpaProjection pub x x1 ∘
        batchedPreIpaViewFromTape (plonkColumnBatches construct) history W (omegaOf 11) x q
          (plonkObservationPoints (omegaOf 11) x q) cores
          (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows)) := by
  funext tape
  simp only [Function.comp_def, batchedPreIpaViewFromTape, preIpaMaskViewFromTape_factor]
  exact honestPlonkPreIpaTranscript_projection pub x x1 q W pieces cores _ _ _

/-- The simulator uses only public polynomials, challenges, and fresh uniform values. -/
noncomputable def plonkPreIpaSimulator [Fintype G] {actions columns : ℕ}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp) : PMF (PlonkPreIpaTranscript columns G) :=
  (preIpaMaskSimulator (G := G) 5 (22 * actions) (columns + 10)).map (plonkPreIpaProjection pub x x1)

/-- The complete pre-IPA algebraic message law under independent wide-reduced prover samples. -/
noncomputable def sampledPlonkPreIpaTranscript {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (W : G)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (cores : ColumnHistory 2048 → Fp × Fp → Fin ((plonkColumnBatches construct).flatten.length + 10) → G) :
    PMF (PlonkPreIpaTranscript (plonkColumnBatches construct).flatten.length G) :=
  (sampleFieldsWith (batchedColumnSampleCount (plonkColumnBatches construct) + 12)
    (plonkPreIpaTranscriptFromTape construct history pub x x1 q W pieces cores)).runFreshPMF fieldSample

/-- All emitted pre-IPA points, step-5 scalars, and group values are simulated jointly. -/
theorem sampledPlonkPreIpaTranscript_simulation [Fintype G] {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (pub : PlonkPublicPolynomials actions) (x x1 q : Fp) (W : G)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (cores : ColumnHistory 2048 → Fp × Fp → Fin ((plonkColumnBatches construct).flatten.length + 10) → G)
    (hW : Function.Bijective (fun r : Fp => r • W))
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkPreIpaTranscript construct history pub x x1 q W pieces cores)
        (plonkPreIpaSimulator pub x x1) (((148 * actions + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (plonkPreIpaSimulator pub x x1)
        (sampledPlonkPreIpaTranscript construct history pub x x1 q W pieces cores)
        (((148 * actions + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have hq : q ≠ x := by
    have h := hpoints.ne (by decide : (4 : Fin 5) ≠ 0)
    simpa [plonkObservationPoints] using h
  have h := sampledPlonkPreIpa_simulation_error_bound construct history W x q
    (plonkObservationPoints (omegaOf 11) x q) cores
    (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows)) hW hpoints haway hq
  have hforward := eventBias_map h.1 (plonkPreIpaProjection pub x x1)
  have hreverse := eventBias_map h.2 (plonkPreIpaProjection pub x x1)
  have hactual : sampledPlonkPreIpaTranscript construct history pub x x1 q W pieces cores =
      (sampledBatchedPreIpa (plonkColumnBatches construct) history W (omegaOf 11) x q
        (plonkObservationPoints (omegaOf 11) x q) cores
        (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows))).map
          (plonkPreIpaProjection pub x x1) := by
    rw [sampledPlonkPreIpaTranscript, plonkPreIpaTranscriptFromTape_factor, sampledBatchedPreIpa]
    exact sampleFieldsWith_map _ _ _ _
  rw [← hactual] at hforward hreverse
  exact ⟨hforward, hreverse⟩

end JointLaw

end Zcash.Snark.ZeroKnowledge

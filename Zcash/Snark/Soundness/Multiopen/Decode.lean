import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Ipa.IpaSoundness
import Zcash.Snark.Soundness.Relation.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble

/-!
# Polynomial and Vandermonde primitives for the multiopen decode

The current AGM adapters provide explicit coordinate batches and expose them through
`OpenedBatchOpenings`. This module supplies their coefficient-polynomial conversion and the two
Vandermonde inverse identities used by `openedColumnDecode`.

## Scope of the model

The decode states a single-point flat power batch. That is not a modelling gap: the deployed
statement is proven to have exactly this shape in the `x₄` squeeze, over the grouping's own
aggregates (`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), and the `x₁` layer un-batches
the aggregates down to the member commitments.

The live decode is the augmented opened-batch interface in `Multiopen.Opened`; its inputs are
explicit computed algebraic representations.

The gate constraints are `vk` data evaluated generically (`vk.gates.map (Expr.eval …)`); nothing is
transcribed, and the one faithfulness question — does the generic assembly compute what the Rust
verifier computes over the same `vk` — is the fingerprint (`Fingerprint.Match`).

Acceptance-to-decode composition and Action semantics are supplied by the AGM and circuit
integration layers.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial (eval C X toPoly eval_finsetSum)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Interpret a coefficient vector as the corresponding polynomial.

This is ordinary executable data: `Fp` supplies decidable equality and the finite sum is over the
canonical `Fin n` enumeration.  Keeping this a plain `def` is important for reductions that return
commitment collisions as computed coefficient vectors. -/
def coeffsToPoly {n : ℕ} (a : Fin n → Fp) : CPoly :=
  ∑ i, C (a i) * X ^ (i : ℕ)

/-- Evaluating `coeffsToPoly` is the same linear form as committing to the powers evaluation vector. -/
theorem coeffsToPoly_eval {k : ℕ} (a : Fin (2 ^ k) → Fp) (x : Fp) :
    eval x (coeffsToPoly a) = commitGen (evalVector k x) a := by
  rw [coeffsToPoly, eval_finsetSum]
  simp [commitGen, evalVector, smul_eq_mul]

/-- Right inverse of the Vandermonde inverse: the row functional reconstructing a sample. -/
theorem vandermonde_inv_right {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * (Matrix.vandermonde z)⁻¹ k j)
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : Matrix.vandermonde z * (Matrix.vandermonde z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

/-- Left inverse of the Vandermonde inverse, specialized to the explicit inverse coefficients. -/
theorem vandermonde_inv_left {n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z) :
    ∀ (i j : Fin n), (∑ k : Fin n, (Matrix.vandermonde z)⁻¹ i k * z k ^ (j : ℕ))
      = if i = j then 1 else 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  intro i j
  have hmul : (Matrix.vandermonde z)⁻¹ * Matrix.vandermonde z = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.vandermonde_apply, Matrix.one_apply] using h2

end Zcash.Snark

import Zcash.Snark.Soundness.Canonical.PolynomialEnvironment
import Zcash.Snark.ZeroKnowledge.DomainCertificate

/-!
# What row masking hides at an evaluation-domain point

This is the advice-column interpolation used by the pinned honest-prover description.
The coefficients are the repository's existing `CPoly` representation; the polynomial is
the existing `rowPolynomial`, not a replacement interpolation model.

The joint off-domain masking rank is established in `RowMaskRank`. At an earlier domain row, the
evaluation is exactly the original cell for every choice of masks. This fact must be
accounted for in any simulator argument; a polynomial commitment's independent blind
does not change the separately emitted evaluation scalar.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- Fresh values for exactly the rows at or after `firstMasked`. -/
abbrev RowMask (n firstMasked : ℕ) := {i : Fin n // firstMasked ≤ i.val} → Fp

/-- Replace the masked suffix, retaining every preceding witness cell. -/
def maskedRows {n : ℕ} (firstMasked : ℕ) (witness : Fin n → Fp)
    (mask : RowMask n firstMasked) : Fin n → Fp :=
  fun i => if hi : firstMasked ≤ i.val then mask ⟨i, hi⟩ else witness i

/-- Interpolate the masked rows with the same polynomial constructor as the verifier model. -/
def maskedRowPolynomial {n : ℕ} (firstMasked : ℕ) (omega : Fp)
    (witness : Fin n → Fp) (mask : RowMask n firstMasked) : CPoly :=
  rowPolynomial omega (maskedRows firstMasked witness mask)

/-- Masking preserves rows before the boundary, retaining the original usable witness data. -/
@[simp] theorem maskedRows_before {n firstMasked : ℕ} (witness : Fin n → Fp)
    (mask : RowMask n firstMasked) (i : Fin n) (hi : i.val < firstMasked) :
    maskedRows firstMasked witness mask i = witness i := by
  simp [maskedRows, Nat.not_le_of_lt hi]

/-- No distributional assumption about the masks can hide an unmasked domain row. -/
theorem maskedRowPolynomial_eval_before {n firstMasked : ℕ} (omega : Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (witness : Fin n → Fp) (mask : RowMask n firstMasked)
    (i : Fin n) (hi : i.val < firstMasked) :
    (maskedRowPolynomial firstMasked omega witness mask).eval (omega ^ i.val) = witness i := by
  rw [maskedRowPolynomial, rowPolynomial_eval hrows, maskedRows_before witness mask i hi]

/-- The concrete advice polynomial for `n = 2048`, with rows `2042..2047` replaced. -/
def advicePolynomial (witness : Fin 2048 → Fp) (mask : RowMask 2048 2042) : CPoly :=
  maskedRowPolynomial 2042 (omegaOf 11) witness mask

/-- Every usable-row evaluation of the actual-size masked advice polynomial exposes its cell. -/
theorem advicePolynomial_eval_usable (witness : Fin 2048 → Fp)
    (mask : RowMask 2048 2042) (i : Fin 2048) (hi : i.val < 2042) :
    (advicePolynomial witness mask).eval ((omegaOf 11) ^ i.val) = witness i :=
  maskedRowPolynomial_eval_before (omegaOf 11)
    (omegaOf_rows_injective 11 (by decide)) witness mask i hi

end Zcash.Snark.ZeroKnowledge

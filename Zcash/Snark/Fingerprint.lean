import Mathlib
import Zcash.Snark.Field

/-!
# The Schwartz–Zippel soundness bound for the fingerprint

The fingerprint is summarised by a random evaluation: two fingerprints that differ as polynomials in
the proof scalars and challenges agree at a uniformly random point only with small probability. This
module pins that probability down by specialising Mathlib's Schwartz–Zippel lemma to the verifier's
field `F_p`.

For a nonzero polynomial of total degree `d` in `n` variables over `F_p`, the fraction of `F_pⁿ` on
which it vanishes is at most `d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`). So a false match between two
distinct degree-`d` fingerprints occurs with probability `≤ d / p` — negligible for the verifier's
modest degree against `p ≈ 2²⁵⁴`. (Applying this to the concrete fingerprint polynomial — the MSM
coefficients as a polynomial in the challenges and proof scalars — is the next step.)
-/

namespace Zcash.Snark

open MvPolynomial Finset Fintype

/-- **Schwartz–Zippel for the fingerprint field.** A nonzero polynomial `p` of total degree `d` in `n`
variables over `F_p` vanishes on at most a `d / |F_p|` fraction of `F_pⁿ`: the fraction of evaluation
points at which `p` is zero is `≤ p.totalDegree / scalarFieldOrder`. This is the soundness bound of
the random-evaluation fingerprint — the chance a random point fails to witness a nonzero fingerprint. -/
theorem fingerprint_schwartz_zippel {n : ℕ} {p : MvPolynomial (Fin n) Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder := by
  have h := schwartz_zippel_totalDegree hp (univ : Finset Fp)
  simpa only [Finset.card_univ, card_Fp] using h

end Zcash.Snark

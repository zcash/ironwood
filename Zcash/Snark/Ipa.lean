import Mathlib

/-!
# The inner-product-argument opening: the `g`-scalar and `b` computations

The IPA opening (`poly/commitment/verifier.rs`) contributes to the fingerprint MSM through two scalar
computations over the `k` round challenges `uⱼ`:

* `computeS u init` — halo2 `compute_s`: the `2 ^ k` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} X^{2ⁱ})`,
  added to the SRS-generator coefficients (`add_to_g_scalars`, with `init = -c`).
* `computeB x u` — halo2 `compute_b`: the scalar `∏ᵢ (1 + u_{k-1-i} x^{2ⁱ})`, used in the IPA opening's
  `u`-generator coefficient `-c · b · z`.

Both are transcribed structurally from the Rust (the left-half doubling and the squaring fold), so the
assembled MSM matches the captured one without a separate equivalence proof. Generic over `[CommRing F]`.
-/

namespace Zcash.Snark

/-- halo2 `compute_s`: the `2 ^ u.length` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} · X^{2ⁱ})` — the IPA
opening's contribution to the SRS-generator coefficients. Built by the Rust's left-half doubling:
start from `[init]`, then for each round challenge (in reverse) append the current vector scaled by it. -/
def computeS {F : Type*} [CommRing F] (u : List F) (init : F) : List F :=
  u.reverse.foldl (fun v uⱼ => v ++ v.map (· * uⱼ)) [init]

/-- halo2 `compute_b`: `∏ᵢ (1 + u_{k-1-i} · x^{2ⁱ})`, the scalar in the IPA opening's `u`-generator
coefficient `-c · b · z`. The fold squares `x` each round (giving `x^{2ⁱ}`) and multiplies in the
factor `1 + uⱼ · x^{2ⁱ}`. -/
def computeB {F : Type*} [CommRing F] (x : F) (u : List F) : F :=
  (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).1

end Zcash.Snark

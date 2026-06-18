import Mathlib
import Zcash.Snark.Msm

/-!
# The inner-product-argument opening

The IPA opening (`poly/commitment/verifier.rs`) is the last stage of the verifier's MSM assembly. It
contributes to the fingerprint MSM through two scalar computations over the `k` round challenges `uⱼ`
and a fold that accumulates the opening proof's terms:

* `computeS u init` — halo2 `compute_s`: the `2 ^ k` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} X^{2ⁱ})`,
  added to the SRS-generator coefficients (with `init = -c`).
* `computeB x u` — halo2 `compute_b`: the scalar `∏ᵢ (1 + u_{k-1-i} x^{2ⁱ})`, used in the `u`-generator
  coefficient `-c · b · z`.
* `ipaFold` — the IPA opening's transformation of the incoming MSM: `[-v]` into `g₀`, `[ξ] S`, the
  per-round `[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ`, `[-c · b · z] U`, `[-f] W`, and `computeS u (-c)` into the
  `g`-scalars.

All are transcribed structurally from the Rust, so the assembled MSM matches the captured one without a
separate equivalence proof.
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

/-- The inner-product-argument opening's contribution to the MSM (halo2
`poly/commitment/verifier.rs`). Starting from the incoming `msm` — the multiopen commitment to be
opened at `x` to the value `v` — it adds: `[-v]` to `g₀` (`add_constant_term`); `[ξ] S`; for each round
`[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ`; the `u`-generator coefficient `-c · b · z` with `b = computeB x u`; `[-f] W`;
and `computeS u (-c)` into the `g`-scalars (`use_challenges`). `rounds` pairs `(Lⱼ, Rⱼ)` with `u`. -/
def ipaFold {F G : Type*} [Field F] {k : ℕ} (x v c f xi z : F) (u : List F)
    (S : G) (rounds : List (G × G)) (m : Msm k F G) : Msm k F G :=
  let m := m.addToGScalars [-v]
  let m := m.appendTerm xi S
  let m := (rounds.zip u).foldl
    (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m
  let m := m.addToUScalar (-c * computeB x u * z)
  let m := m.addToWScalar (-f)
  m.addToGScalars (computeS u (-c))

end Zcash.Snark

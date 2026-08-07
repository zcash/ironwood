import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Arithmetic
import Zcash.Arithmetic.Msm

/-!
# The inner-product-argument opening

The IPA opening (`poly/commitment/verifier.rs`) is the last stage of the verifier's MSM assembly:
two scalar computations over the `k` round challenges `uⱼ`, and a fold accumulating the opening
proof's terms.

* `computeS` — halo2 `compute_s`: the folded generator's coefficient vector, entering the URS
  `g`-coefficients.
* `computeB` — halo2 `compute_b`: the folded evaluation at the opening point.
* `ipaFold` — the IPA opening's transformation of the incoming MSM, accumulating every term of
  halo2's verification equation (closed form: `eval_ipaFold`).

All are transcribed structurally from the Rust, so the assembled MSM matches the captured one without a
separate equivalence proof.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.eval_addToGScalars Msm.eval_addToUScalar Msm.eval_addToWScalar Msm.eval_appendTerm)

/-- halo2 `compute_s`: the `2 ^ u.length` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} · X^{2ⁱ})`.
With `init = -c` these are the fingerprint's URS-generator coefficients for `[-c] G'`, where `G'`
is the fully folded generator. Built by the same left-half doubling as the Rust. -/
def computeS {F : Type*} [CommRing F] (u : List F) (init : F) : List F :=
  u.reverse.foldl (fun v uⱼ => v ++ v.map (· * uⱼ)) [init]

/-- halo2 `compute_b`: `b = ∏ᵢ (1 + u_{k-1-i} · x^{2ⁱ})` — the `computeS` polynomial evaluated at
the opening point `x`, entering the fingerprint's `u`-generator coefficient as `-c · b · z`. -/
def computeB {F : Type*} [CommRing F] (x : F) (u : List F) : F :=
  (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).1

/-- The inner-product-argument opening's transformation of the incoming MSM (halo2
`poly/commitment/verifier.rs`): starting from the multiopen commitment to be opened at `x` to the
value `v`, it accumulates every term of halo2's IPA verification equation — the value at `g₀`, the
blinding terms, the per-round `Lⱼ`/`Rⱼ`, and the folded generators. The exact term-by-term form is
`eval_ipaFold`; `rounds` pairs `(Lⱼ, Rⱼ)` with `u`. -/
def ipaFold {F G : Type*} [Field F] {k : ℕ} (x v c f xi z : F) (u : List F)
    (S : G) (rounds : List (G × G)) (m : Msm k F G) : Msm k F G :=
  let m := m.addToGScalars [-v]
  let m := m.appendTerm xi S
  let m := (rounds.zip u).foldl
    (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m
  let m := m.addToUScalar (-c * computeB x u * z)
  let m := m.addToWScalar (-f)
  m.addToGScalars (computeS u (-c))

/-- The per-round `[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ` fold contributes exactly `Σⱼ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)` to the
evaluation. By induction over the rounds, using `Msm.eval_appendTerm`. -/
theorem eval_foldl_rounds {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (l : List ((G × G) × F)) (m0 : Msm urs.k F G) :
    (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m0).eval urs
      = m0.eval urs + (l.map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum := by
  induction l generalizing m0 with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih]
    simp only [Msm.eval_appendTerm, List.map_cons, List.sum_cons]
    abel

/-- Evaluating the assembled IPA fold against the URS gives halo2's IPA verification equation in
closed form: the incoming multiopen commitment plus the value, blinding, per-round, and
folded-generator terms (the exact list is the statement). The deployed accept (`eval … = 0`) is
this equation vanishing — a symbolic check of the transcribed assembly, complementing the
one-proof `native_decide` fingerprint match. By `Msm.eval_*` distribution and
`eval_foldl_rounds`. -/
theorem eval_ipaFold {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (x v c f xi z : F) (u : List F) (S : G) (rounds : List (G × G))
    (m : Msm urs.k F G) :
    (ipaFold x v c f xi z u S rounds m).eval urs
      = m.eval urs
        + (∑ i, ([-v].getD i.val 0) • urs.g i)
        + xi • S
        + ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-c * computeB x u * z) • urs.u
        + (-f) • urs.w
        + (∑ i, ((computeS u (-c)).getD i.val 0) • urs.g i) := by
  simp only [ipaFold, Msm.eval_addToGScalars, Msm.eval_appendTerm, Msm.eval_addToUScalar,
    Msm.eval_addToWScalar, eval_foldl_rounds]

end Zcash.Snark

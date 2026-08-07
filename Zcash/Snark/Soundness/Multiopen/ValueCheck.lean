import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Multiopen.RPoly

/-!
# Multiopen vanishing-polynomial algebra

Reusable vanishing-polynomial and denominator-clearing identities used by the deployed AGM
multiopen analysis. The soundness path derives explicit augmented-basis relations from the
algebraic prover's computed representations.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

/-- The vanishing polynomial of a finite point set, `∏_{p ∈ pts} (X − p)`. -/
def vanishingProd (pts : Finset Fp) : CPoly :=
  ∏ p ∈ pts, (X - C p)

@[simp] theorem vanishingProd_eval (pts : Finset Fp) (x : Fp) :
    (vanishingProd pts).eval x = ∏ p ∈ pts, (x - p) := by
  simp [vanishingProd, eval_prod]

/-- The vanishing polynomial vanishes at each of its points. -/
theorem vanishingProd_eval_mem {pts : Finset Fp} {p : Fp} (hp : p ∈ pts) :
    (vanishingProd pts).eval p = 0 := by
  rw [vanishingProd_eval]
  exact Finset.prod_eq_zero hp (by ring)

/-- Off its point set the vanishing polynomial is nonzero. -/
theorem vanishingProd_eval_ne {pts : Finset Fp} {p : Fp} (hp : p ∉ pts) :
    (vanishingProd pts).eval p ≠ 0 := by
  rw [vanishingProd_eval]
  refine Finset.prod_ne_zero_iff.mpr (fun q hq => ?_)
  exact sub_ne_zero.mpr (by rintro rfl; exact hp hq)

/-- The complementary product `Wⱼ = ∏_{p ∈ all \ pts} (X − p)`. -/
def coProd (all pts : Finset Fp) : CPoly :=
  vanishingProd (all \ pts)

/-- The full vanishing polynomial splits as `D = Wⱼ · ∏(pts j)` when `pts j ⊆ all`. -/
theorem vanishingProd_split {all pts : Finset Fp} (hsub : pts ⊆ all) :
    vanishingProd all = coProd all pts * vanishingProd pts := by
  simp only [coProd, vanishingProd]
  rw [← Finset.prod_sdiff hsub]

/-- **Denominator clearing.** Off `pts`' nodes, `D(x) · (∏_{pts}(x − p))⁻¹ = Wⱼ(x)` — the identity
that turns the multiopen fold's `∏(x₃ − node)⁻¹` into the polynomial `Wⱼ`. -/
theorem clear_denom_eval {all pts : Finset Fp} (hsub : pts ⊆ all) {x : Fp}
    (hx : (vanishingProd pts).eval x ≠ 0) :
    (vanishingProd all).eval x * (∏ p ∈ pts, (x - p))⁻¹ = (coProd all pts).eval x := by
  rw [vanishingProd_split hsub, eval_mul, vanishingProd_eval, _root_.mul_assoc,
    mul_inv_cancel₀ (by rw [← vanishingProd_eval]; exact hx), _root_.mul_one]

end Zcash.Snark

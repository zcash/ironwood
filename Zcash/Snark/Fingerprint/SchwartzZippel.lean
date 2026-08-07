import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Zcash.Arithmetic

/-!
# The Schwartz–Zippel soundness bound for the fingerprint

A fingerprint can be summarised more cheaply by a random evaluation: two fingerprints that differ as
polynomials in the proof scalars and challenges agree at a uniformly random point only with small
probability. This module pins that probability down by specialising Mathlib's Schwartz–Zippel lemma to
the verifier's field `F_p`, over `Fin n` and over an arbitrary finite variable index
(`fingerprint_schwartz_zippel_index` — the form the structured sample space of
`Fingerprint/SampleSpace.lean` consumes). The *realized* fingerprint in this development is the
decidable coefficient comparison, `Zcash.Snark.Fingerprint.Match`; the random-evaluation variant is
instantiated at `assemble`'s realized coefficients in `Zcash.Snark.Fingerprint.Epsilon`.

For a nonzero polynomial of total degree `d` in `n` variables over `F_p`, the fraction of `F_pⁿ`
on which it vanishes is at most `d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`) — so a false match
between distinct degree-`d` fingerprints is negligible. (`Zcash.Snark.Fingerprint.Epsilon` applies
this to the concrete coefficient families; the `assemble`-instantiated ε is
`competing_coefficient_family_agreement_le`.)
-/

namespace Zcash.Snark

open Zcash.Arithmetic (card_Fp scalarFieldOrder)

open MvPolynomial Finset Fintype

/-- **Schwartz–Zippel for the fingerprint field.** A nonzero polynomial `p` of total degree `d` in `n`
variables over `F_p` vanishes on at most a `d / |F_p|` fraction of `F_pⁿ`: the fraction of evaluation
points at which `p` is zero is `≤ p.totalDegree / scalarFieldOrder`. This is the SZ bound underlying a
random-evaluation fingerprint — the chance a random point fails to witness a nonzero polynomial. -/
theorem fingerprint_schwartz_zippel {n : ℕ} {p : MvPolynomial (Fin n) Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder := by
  have h := schwartz_zippel_totalDegree hp (univ : Finset Fp)
  simpa only [Finset.card_univ, card_Fp] using h

/-- `fingerprint_schwartz_zippel` over an arbitrary finite variable index — the form the
structured sample space (`ScalarSlot`, `Fingerprint/SampleSpace.lean`) consumes. Transported
along `Fintype.equivFin` by `MvPolynomial.rename`, which preserves nonzeroness and total
degree. -/
theorem fingerprint_schwartz_zippel_index {σ : Type*} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
      ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hq0 : rename (⇑e) p ≠ 0 := fun h =>
    hp (rename_injective (⇑e) e.injective (by simpa using h))
  have hdeg : (rename (⇑e) p).totalDegree = p.totalDegree := totalDegree_renameEquiv e p
  have hcard : #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f p = 0}
      = #{g ∈ piFinset fun _ : Fin (Fintype.card σ) => (univ : Finset Fp) |
          eval g (rename (⇑e) p) = 0} := by
    refine Finset.card_equiv (e.arrowCongr (Equiv.refl Fp)) fun f => ?_
    have hcomp : eval (⇑(e.arrowCongr (Equiv.refl Fp)) f) (rename (⇑e) p) = eval f p := by
      have hfe : (⇑(e.arrowCongr (Equiv.refl Fp)) f) ∘ ⇑e = f := by
        funext v
        simp [Equiv.arrowCongr]
      rw [eval_rename, hfe]
    simp only [Finset.mem_filter, mem_piFinset, Finset.mem_univ, implies_true, true_and, hcomp]
  rw [hcard, ← hdeg]
  exact fingerprint_schwartz_zippel hq0

end Zcash.Snark

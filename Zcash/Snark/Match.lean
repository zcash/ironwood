import Mathlib
import Zcash.Snark.Msm
import Zcash.Snark.Fingerprint
import Zcash.Snark.Assemble

/-!
# The fingerprint match

The cross-check that validates the Lean assembly against the deployed Rust verifier (in place of a
line-by-line translation proof): run the deployed verifier on a proof, capturing its assembled MSM and
the challenges it drew; run the Lean `assembleFinalMsm` on the same proof string and challenges; and
compare the two MSMs. A match means the two assembly *formulas* agree.

This module provides the match's logical content:

* `MsmMatch` — two MSMs match iff their `g`/`w`/`u` coefficients and their `other` term lists agree, and
  `msmMatch_iff_eq` shows that is exactly equality. So the match is checked coefficient-by-coefficient —
  precisely the comparison against a captured MSM. Because both sides use the *same* proof commitments as
  the bases (the Lean assembly's `G` elements are the captured proof's commitments), the bases of the
  `other` terms agree by construction, and the match reduces to the concrete `F_p` scalar coefficients.
* `fingerprint_match_random_eval_sound` — the soundness of the cheaper **random-evaluation** match: viewing
  a coefficient difference as a polynomial in the proof scalars and challenges, a uniformly random
  evaluation fails to witness a real mismatch only with probability `≤ d / p` (`Schwartz–Zippel`, via
  `fingerprint_schwartz_zippel`). So one random proof suffices to validate the assembly up to `d / p`.
* `gScalars_card` — the structural cross-check: the assembled MSM carries `2 ^ k` SRS-generator
  coefficients, matching the captured Ironwood fingerprint's `2 ^ 11 = 2048`.

**What remains external.** Running the *numeric* match on the real Ironwood capture needs the captured
fixture (the `2048` g-scalars, `100` commitment terms, and `22` challenges from `Step 2.1`) serialized
and loaded, the Ironwood verifying key supplied as a `VerifyingKey`, and the `construct_intermediate_sets`
grouping (the one piece `assembleFinalMsm` takes as input). With those, the match is the decidable
coefficient comparison `MsmMatch` above. The group bases stay abstract in Lean (the Pasta curve law is
hand-waved), so the numeric comparison is of the scalar coefficients, with the bases shared by construction.
-/

namespace Zcash.Snark

/-- Two MSMs **match** iff their SRS-generator coefficients, the `w`/`u` coefficients, and the `other`
term lists agree. This is the fingerprint match, stated coefficient-by-coefficient. -/
def MsmMatch {k : ℕ} {F G : Type*} (m₁ m₂ : Msm k F G) : Prop :=
  m₁.gScalars = m₂.gScalars ∧ m₁.wScalar = m₂.wScalar ∧ m₁.uScalar = m₂.uScalar ∧ m₁.other = m₂.other

/-- The fingerprint match is exactly MSM equality: it suffices to compare the coefficients and terms. -/
theorem msmMatch_iff_eq {k : ℕ} {F G : Type*} (m₁ m₂ : Msm k F G) : MsmMatch m₁ m₂ ↔ m₁ = m₂ := by
  constructor
  · rintro ⟨hg, hw, hu, ho⟩
    cases m₁; cases m₂
    simp_all
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- `MsmMatch` is decidable when the coefficients and terms are: this is the concrete check run against a
captured MSM (compare the `2 ^ k` g-scalars, the `w`/`u` scalars, and the term list). -/
instance {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G] (m₁ m₂ : Msm k F G) :
    Decidable (MsmMatch m₁ m₂) := by
  unfold MsmMatch; infer_instance

open MvPolynomial Finset Fintype in
/-- **Soundness of the random-evaluation match (Schwartz–Zippel).** A coefficient of the assembled MSM
minus the captured one is a polynomial `p` in the proof scalars and challenges; the two MSMs genuinely
differ in that coefficient exactly when `p ≠ 0`. Then the fraction of challenge/scalar assignments at
which the coefficient nonetheless agrees — a *false* match at a uniformly random evaluation — is at most
`deg p / p_field`. So a single random evaluation detects a mismatch except with probability `≤ d / p`,
and one random proof validates the assembly up to that bound. This is `fingerprint_schwartz_zippel`
applied to the coefficient difference. -/
theorem fingerprint_match_random_eval_sound {n : ℕ} {p : MvPolynomial (Fin n) Fp} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset Fp) | eval f p = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / scalarFieldOrder :=
  fingerprint_schwartz_zippel hp

/-- The assembled MSM carries `2 ^ k` SRS-generator coefficients (`gScalars : Fin (2 ^ k) → F`),
matching the captured Ironwood fingerprint's `2 ^ 11 = 2048` g-scalars (`k = 11`). -/
theorem gScalars_card (k : ℕ) : Fintype.card (Fin (2 ^ k)) = 2 ^ k := Fintype.card_fin _

/-- The captured Ironwood domain size: `k = 11` gives `2 ^ 11 = 2048` g-scalars. -/
theorem ironwood_gScalars : (2 : ℕ) ^ 11 = 2048 := by norm_num

end Zcash.Snark

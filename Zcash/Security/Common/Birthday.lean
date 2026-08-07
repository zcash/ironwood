import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Common.RandomOracle

/-!
# Birthday-bound counting for random-oracle ±-collisions

Following the counting-fraction style of `Fingerprint/SchwartzZippel.lean`: a "probability" is the
fraction of a finite ambient space on which a bad event occurs, expressed in `ℚ≥0`, with no
probability monad. The ambient space is `F × F` — two independent uniform random-oracle outputs at
distinct queries — and the bad event is the shifted ±-collision `s₁ + o₁ = ±(s₂ + o₂)` that the
key-binding break computes (`RandomOracle.CollisionUpToSign.ofBreak`), the shifts being
non-querying functions of the queries. The per-pair count `≤ 2·|F|` (one outcome per sign) gives
the `2/|F|` per-pair term; summed over the `C(q,2)` pairs of an adversary's `q` queries this is
`ε_kb ≤ q·(q-1)/|F|` (`birthday_closed_form`).
-/

namespace Zcash.Security.Birthday

open Finset Zcash.Security.RandomOracle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- The field's cardinality is nonzero (a field is nonempty). -/
private theorem fintypeCard_ne_zero : (Fintype.card F : ℚ≥0) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

/-- The shifted ±-collision event `s₁ + o₁ = ±(s₂ + o₂)` over `(o₁, o₂) ∈ F × F` has at most
`2·|F|` outcomes: for each `o₂`, only two values of `o₁` collide, one per sign. The shifts do not
change the count, which is what lets the per-pair bound apply to the *shifted* final oracle
(`KeyBinding.shiftedFinalOracle`), whose shift is a non-querying function of the query. -/
theorem card_shifted_pm_collision_le (s₁ s₂ : F) :
    (univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2).card
      ≤ 2 * Fintype.card F := by
  have hsub : (univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2) ⊆
      (univ.image fun o : F => (s₂ + o - s₁, o)) ∪
        (univ.image fun o : F => (-(s₂ + o) - s₁, o)) := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_union]
    rcases hp.2 with h | h
    · exact Or.inl (mem_image.2 ⟨p.2, mem_univ _, Prod.ext (by linear_combination -h) rfl⟩)
    · exact Or.inr (mem_image.2 ⟨p.2, mem_univ _, Prod.ext (by linear_combination -h) rfl⟩)
  calc (univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2).card
      ≤ ((univ.image fun o : F => (s₂ + o - s₁, o)) ∪
          (univ.image fun o : F => (-(s₂ + o) - s₁, o))).card := card_le_card hsub
    _ ≤ (univ.image fun o : F => (s₂ + o - s₁, o)).card
        + (univ.image fun o : F => (-(s₂ + o) - s₁, o)).card := card_union_le _ _
    _ ≤ Fintype.card F + Fintype.card F := by
        gcongr <;> · rw [← card_univ]; exact card_image_le
    _ = 2 * Fintype.card F := (two_mul _).symm

/-- **Shifted per-pair, per-sign fraction.** Over two independent uniform outputs
`(o₁, o₂) ∈ F × F`, the fraction on which the shifted ±-collision `s₁ + o₁ = ±(s₂ + o₂)` holds is
at most `2/|F|`. -/
theorem shifted_pm_collision_fraction_le (s₁ s₂ : F) :
    ((univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2).card : ℚ≥0)
        / (Fintype.card F : ℚ≥0)^2
      ≤ 2 / (Fintype.card F : ℚ≥0) := by
  have hc : ((univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2).card : ℚ≥0)
      ≤ 2 * (Fintype.card F : ℚ≥0) := by exact_mod_cast card_shifted_pm_collision_le s₁ s₂
  calc ((univ.filter fun p : F × F => s₁ + p.1 =± s₂ + p.2).card : ℚ≥0)
        / (Fintype.card F)^2
      ≤ (2 * (Fintype.card F : ℚ≥0)) / (Fintype.card F)^2 := by gcongr
    _ = 2 / (Fintype.card F : ℚ≥0) := by rw [pow_two, mul_div_mul_right _ _ fintypeCard_ne_zero]

omit [Field F] [DecidableEq F] in
/-- **Birthday-bound closed form.** Union-bounding the shifted per-pair bound `2/|F|`
(`shifted_pm_collision_fraction_le`) over the `C(q,2) = q(q-1)/2` unordered pairs of an
adversary's `q` random-oracle queries yields `ε_kb ≤ q·(q-1)/|F|`. The residual case needs no
separate term: it relocates the collision to the `rivk_ext`-derivation queries
(`KeyBinding.residual_of_finalQuery_eq`), a query pair the union bound already counts. (This
states the arithmetic of the union-bound *sum*; the union bound itself — that the break
probability is at most the sum of the per-pair probabilities — is the standard step over the
joint query space, applied to the per-pair bound above.) -/
theorem birthday_closed_form (q : ℕ) :
    (q.choose 2 : ℚ) * (2 / (Fintype.card F : ℚ)) = q * (q - 1) / (Fintype.card F : ℚ) := by
  rw [Nat.cast_choose_two]
  ring

end Zcash.Security.Birthday

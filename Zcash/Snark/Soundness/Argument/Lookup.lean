import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Argument.GrandProduct

/-!
# Lookup argument soundness

The [lookup argument](https://zcash.github.io/halo2/design/proving-system/lookup.html) proves that
every input value occurs in the table — set inclusion {input} ⊆ {table}, ignoring multiplicity.

The prover supplies permuted copies of both columns: A′ of the input and S′ of the table. The
grand-product check forces {A′} = {input} and {S′} = {table} as multisets (`GrandProduct.lean`),
and two further constraints force every A′ value to coincide with some S′ value — the
**run-structure** proved here (`run_structure` lists them). Chaining the three: every input value
is a table value.

This file currently provides `run_structure` (over the usable rows); the step from the grand
product to the multiset equalities, and the final assembly, remain open.
-/

namespace Zcash.Snark

/-- **Run-structure for the lookup argument**: every permuted-input value occurs in the permuted
table (`∀ i, ∃ j, a i = s j`). This verifies part of the abstract argument, not yet the mapping to
constraints. `a`, `s` are the prover-supplied permuted columns (A′, S′ in the Halo 2 book); the
running-product constraint reads the previous row A′_prev = A′(ω⁻¹·), which at row 0 wraps
cyclically to an arbitrary blinding value `aPrev`. The hypotheses are the verifier's checks:

* `a_0 = s_0`, from ℓ_0·(A′ - S′) = 0;
* `a_0 = s_0 ∨ a_0 = aPrev`, from active·(A′ - S′)·(A′ - A′_prev) = 0 at row 0 — subsumed by the
  first, for any `aPrev`;
* `a_{i+1} = s_{i+1} ∨ a_{i+1} = a_i`, the later-row instances of the same constraint.

Indices are `Fin (n + 1)` so the index set is nonempty (row 0 always exists), and the proof uses
`Fin.induction` so the `succ` case's hypothesis is exactly the predecessor row `i.castSucc`. -/
theorem run_structure {F : Type*} {n : ℕ} (a s : Fin (n + 1) → F) (aPrev : F)
    (h0 : a 0 = s 0)
    (hstep0 : a 0 = s 0 ∨ a 0 = aPrev)
    (hstep : ∀ i : Fin n, a i.succ = s i.succ ∨ a i.succ = a i.castSucc) :
    ∀ i, ∃ j, a i = s j := by
  intro i
  induction i using Fin.induction with
  | zero =>
    -- the row-0 running constraint with the arbitrary wrapped predecessor is subsumed by `a 0 = s 0`
    rcases hstep0 with h | _
    · exact ⟨0, h⟩
    · exact ⟨0, h0⟩
  | succ i ih =>
    rcases hstep i with hm | hr
    · exact ⟨i.succ, hm⟩
    · obtain ⟨j, hj⟩ := ih
      exact ⟨j, hr.trans hj⟩

end Zcash.Snark

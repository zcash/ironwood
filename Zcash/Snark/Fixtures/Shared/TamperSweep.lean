import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tamper combinators for the fixture sensitivity sweeps

The per-family `Negative/Sweep.lean` modules state one fingerprint-mismatch theorem per
proof-string slot. These two combinators are the sweep's entire mutation vocabulary: each
tampered record differs from its capture at exactly one index, so a reviewer audits the index
arithmetic here once and every tamper definition is a single line naming its field, indices,
and delta. Indices are `ℕ` compared against `Fin.val`, matching the negative suites' existing
guard idiom; an out-of-range index makes the tamper a no-op, which fails the build loudly —
the sweep theorem then asserts a mismatch that does not exist.
-/

namespace Zcash.Snark

/-- Apply `t` at exactly index `i` of `f`, leaving every other index unchanged. -/
def mapAt {n : ℕ} {α : Type*} (i : ℕ) (t : α → α) (f : Fin n → α) : Fin n → α :=
  fun j => if j.val = i then t (f j) else f j

/-- Apply `t` at exactly index `(p, q)` of `f`, leaving every other index unchanged. -/
def mapAt2 {m n : ℕ} {α : Type*} (p q : ℕ) (t : α → α)
    (f : Fin m → Fin n → α) : Fin m → Fin n → α :=
  fun p' q' => if p'.val = p ∧ q'.val = q then t (f p' q') else f p' q'

end Zcash.Snark

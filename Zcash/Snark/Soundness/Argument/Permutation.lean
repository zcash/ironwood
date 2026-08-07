import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Argument.GrandProduct

/-!
# Permutation argument soundness

The [permutation argument](https://zcash.github.io/halo2/design/proving-system/permutation.html)
proves the copy constraints: cells the circuit declares equal hold equal values.

Each cell has a value and a unique name, and the constraints are encoded as a permutation `σ`
whose cycles are the groups of cells declared equal. The argument hinges on one multiset
identity: the `(value, name)` pairs are unchanged when every cell is renamed to the next one in
its cycle.

This file proves what that identity buys: with names distinct (`label` injective), it holds iff
values are constant on every cycle — the copy constraints. `perm_values_eq_iff` and
`value_const_on_sameCycle` are the two halves, composed in `perm_copy_constraints`;
`prod_pair_inj` (`GrandProduct.lean`) recovers the identity from equal grand products.

Not proved here: that the `δ^j·ω^i` naming really is injective (keygen's δ-coset disjointness),
and that the verifier's product check forces the grand products equal — the telescoping step,
which feeds the `h` hypothesis.
-/

namespace Zcash.Snark

open Finset

/-- Mapping a permutation over the universal multiset leaves it unchanged (`σ` is a bijection of the
index type, so it just reindexes `univ`). -/
theorem univ_val_map_perm {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) :
    Finset.univ.val.map (⇑σ) = Finset.univ.val := by
  simp

/-- **Structural step for the permutation argument.** Cells carry a `value` and an injective name
`label`; the multiset of `(value, label)` pairs is unchanged by permuting the labels through `σ`
iff every cell's value equals the next one's in its cycle (`value c = value (σ c)`).
`prod_pair_inj` delivers the multiset equality, `label` injectivity (δ-coset name distinctness)
turns it into the per-cell relation, and `value_const_on_sameCycle` extends it around whole
cycles. Both proof directions are stepped through in the body. -/
theorem perm_values_eq_iff {ι L V : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {label : ι → L} (hlabel : Function.Injective label) (value : ι → V) :
    Finset.univ.val.map (fun c => (value c, label c))
      = Finset.univ.val.map (fun c => (value c, label (σ c)))
    ↔ ∀ c, value c = value (σ c) := by
  constructor
  · intro h c
    -- the index `σ c` puts `(value (σ c), label (σ c))` in the left multiset
    have hmem : (value (σ c), label (σ c)) ∈
        Finset.univ.val.map (fun c => (value c, label c)) :=
      Multiset.mem_map.mpr ⟨σ c, by simp, rfl⟩
    -- transport it to the right multiset and read off a matching index `e`
    rw [h] at hmem
    obtain ⟨e, _, he⟩ := Multiset.mem_map.mp hmem
    -- `he : (value e, label (σ e)) = (value (σ c), label (σ c))`
    have hee : e = c := σ.injective (hlabel (congrArg Prod.snd he))
    have hval : value e = value (σ c) := congrArg Prod.fst he
    rwa [hee] at hval
  · intro h
    -- value-invariance rewrites the right pairs to `(value (σ c), label (σ c))` …
    have hRHS : Finset.univ.val.map (fun c => (value c, label (σ c)))
        = Finset.univ.val.map (fun c => (value (σ c), label (σ c))) :=
      Multiset.map_congr rfl (fun c _ => by rw [h c])
    -- … which is `(fun c => (value c, label c)) ∘ σ`, so reindexing by `σ` over `univ` closes it
    rw [hRHS, show (fun c => (value (σ c), label (σ c)))
          = (fun c => (value c, label c)) ∘ σ from rfl,
        ← Multiset.map_map, univ_val_map_perm]

/-- A `value` invariant under one application of `σ` is invariant under every integer power of `σ`.
By induction on the exponent: the `value c = value (σ c)` hypothesis also gives invariance under `σ⁻¹`
(`value (σ⁻¹ x) = value (σ (σ⁻¹ x)) = value x`), and the two extend to all of ℤ. (ℕ is logically
sufficient since the permutation is finite, but Mathlib's definition of `SameCycle` uses ℤ to cater
for infinite cases.) -/
theorem value_zpow {ι V : Type*} (σ : Equiv.Perm ι) (value : ι → V)
    (h : ∀ c, value c = value (σ c)) : ∀ (n : ℤ) (x : ι), value ((σ ^ n) x) = value x := by
  have hinv : ∀ x, value (σ⁻¹ x) = value x := by
    intro x; rw [h (σ⁻¹ x)]; simp
  intro n
  induction n using Int.induction_on with
  | zero => intro x; simp
  | succ i ih =>
      intro x
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply, ih (σ x), ← h x]
  | pred i ih =>
      intro x
      rw [zpow_sub, zpow_one, Equiv.Perm.mul_apply, ih (σ⁻¹ x), hinv x]

/-- **Values are constant on σ-cycles** — the copy-constraint relation in full: given the
one-step invariance `value c = value (σ c)`, any two cells in the same cycle of `σ` hold equal
values. -/
theorem value_const_on_sameCycle {ι V : Type*} (σ : Equiv.Perm ι) (value : ι → V)
    (h : ∀ c, value c = value (σ c)) {c d : ι} (hcd : σ.SameCycle c d) :
    value c = value d := by
  obtain ⟨n, rfl⟩ := hcd
  exact (value_zpow σ value h n c).symm

/-- **Soundness of the permutation argument, structural half** (the step from the product check
to the multiset identity is separate): from the multiset-of-pairs identity, with `label`
injective, any two cells in the same cycle of `σ` hold equal values — the copy constraints `σ`
encodes. Composes `perm_values_eq_iff` with `value_const_on_sameCycle`. -/
theorem perm_copy_constraints {ι L V : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {label : ι → L} (hlabel : Function.Injective label) (value : ι → V)
    (h : Finset.univ.val.map (fun c => (value c, label c))
       = Finset.univ.val.map (fun c => (value c, label (σ c))))
    {c d : ι} (hcd : σ.SameCycle c d) :
    value c = value d :=
  value_const_on_sameCycle σ value ((perm_values_eq_iff σ hlabel value).mp h) hcd

end Zcash.Snark

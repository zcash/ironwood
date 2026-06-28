import Zcash.Snark.Soundness.CommitFold

/-!
# Binding as a discrete-log-relation reduction over the augmented generators

`Zcash.Snark.Soundness.CommitFold` models commitment binding at the URS generators `g` as a reduction to
discrete-log-relation (DLR) hardness (`relation_of_collision`, `commitmentBinding_iff_no_relation`):
breaking binding produces a nontrivial relation among the `g`, which DLR hardness forbids.

The deployed verifier additionally folds the inner-product generator `U` and the blinding generator `W`
into one group equation, so soundness there needs binding over the *augmented* system `(g, U, W)`. This
module extends the DLR-reduction view to `(g, U, W)`:

* `HasNontrivialRelation g U W` — a nontrivial discrete-log relation among the augmented generators.
* `separate_or_relation` — a combined `(g, U, W)`-equation is read off coordinate-wise *or* exhibits such
  a relation. This is the reduction form of an augmented-independence assumption; unlike that assumption
  (which is information-theoretically false in a prime-order group, where the generators are always
  dependent), the reduction is non-vacuous: the relation is its *output*. A relation always *exists* here,
  so the combined equation separates unless a feasible adversary *finds* one — which DLR hardness forbids.

`separate_or_relation` is the augmented (`g, U, W`) analog of `relation_of_collision`. Wiring the deployed
binding step through it — a commitment collision yields a nontrivial relation among `(g, U, W)` — is what
ties the extracted opening to binding, rather than feeding a discarded uniqueness conjunct.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial discrete-log relation among the augmented generators `(g, U, W)`: scalars `(a, α, β)`
not all zero with `⟨a, g⟩ + α • U + β • W = 0`. Such a relation always *exists* in a prime-order group;
the content of the reduction below is that breaking binding *produces* one, which DLR hardness forbids. -/
def HasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) : Prop :=
  ∃ (a : Fin n → F) (α β : F), (a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0) ∧ commitGen g a + α • U + β • W = 0

/-- **The augmented binding reduction.** Two `(g, U, W)`-combinations equal as group elements *either*
agree coordinate-wise *or* exhibit a nontrivial discrete-log relation among `(g, U, W)`. This is the
reduction form of the (information-theoretically false) augmented-independence assumption: rather than
assuming the coordinates match, it concludes "they match, or here is a DLR witness". -/
theorem separate_or_relation {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ∨ HasNontrivialRelation (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact Or.inl h
  · refine Or.inr ⟨a - a', α - α', β - β', ?_, ?_⟩
    · -- the difference is nontrivial: otherwise the coordinates would all agree, contradicting `h`
      rcases Classical.em (a = a') with ha | ha
      · rcases Classical.em (α = α') with hα | hα
        · exact Or.inr (Or.inr (sub_ne_zero.mpr (fun hβ => h ⟨ha, hα, hβ⟩)))
        · exact Or.inr (Or.inl (sub_ne_zero.mpr hα))
      · exact Or.inl (sub_ne_zero.mpr ha)
    · -- the difference is a relation: it is the (zero) difference of the two equal combinations
      have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
          = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
        rw [commitGen_sub, sub_smul, sub_smul]; abel
      rw [hrw, e, sub_self]

end Zcash.Snark

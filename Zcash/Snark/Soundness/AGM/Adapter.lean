import Zcash.Common.DiscreteLogRelation
import Zcash.Snark.Soundness.Deployed.Binding

/-!
# The URS as an AGM basis

The relation types and the known-log relation-to-discrete-log dischargers are model-free
and live in `Zcash.Common.DiscreteLogRelation`; this module is the AGM-side entry point to
them. It carries the one piece that is specific to the deployed setup: the deployed URS
`(g, U, W)` and the augmented basis an algebraic prover represents against are the same
public group elements, viewed two ways (`ursOfAugmentedBasis` and its two round trips). A
commitment collision then converts to a relation over the URS generators.

## Computational boundary

`FiatShamir.Adversary.Provenance` and the online AGM modules attach representations to the prover's
emitted points. `StraightLineIpa` and `Composition.StraightLineDeployed` consume one represented
execution and return either decoded opening data or an explicit relation.
`Common.RelationProbabilityCoins` and the finite-security profiles price the reduction's single
programmed-slot miss at `1/|F|` and account separately for random-oracle queries, group work, and
direct-coordinate work.

The relation-to-DLOG path is computable. Its remaining boundary is the online AGM restriction,
finite-security plain-DL hardness, ideal random oracles, and external implementation work bounds.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Split an augmented public basis into its URS generators, `U`, and `W`. -/
def ursOfAugmentedBasis (k : ℕ) (basis : AugmentedIndex (2 ^ k) → G) : URS G :=
  { k := k
    g := fun i => basis (AugmentedIndex.gen i)
    u := basis AugmentedIndex.u
    w := basis AugmentedIndex.w }

omit [AddCommGroup G] in
@[simp] theorem ursOfAugmentedBasis_k (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) :
    (ursOfAugmentedBasis k basis).k = k := by
  simp only [ursOfAugmentedBasis]

omit [AddCommGroup G] in
/-- Splitting an augmented basis into a URS and reassembling it loses no public group element. -/
@[simp] theorem augmentedBasis_ursOfAugmentedBasis (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) :
    augmentedBasis (ursOfAugmentedBasis k basis).g
      ![(ursOfAugmentedBasis k basis).u, (ursOfAugmentedBasis k basis).w] = basis := by
  funext i
  rcases i with i | j
  · rfl
  · fin_cases j <;> simp [augmentedBasis, ursOfAugmentedBasis, AugmentedIndex.u,
      AugmentedIndex.w, BasisIndex.u, BasisIndex.w]

omit [AddCommGroup G] in
/-- The other round trip: every URS *is* the split of an augmented basis, namely its own.

This is what lets a result stated over `ursOfAugmentedBasis k basis` for an arbitrary basis — the
shape the rewind-free and adaptive routes take, since their families are indexed by the augmented
basis the extractor represents against — be instantiated at a URS given as concrete data, such as
a captured fixture's `capturedURS`. Without it the two families of statements cannot be joined:
one quantifies over bases, the other names a record. -/
theorem ursOfAugmentedBasis_augmentedBasis (urs : URS G) :
    ursOfAugmentedBasis urs.k (augmentedBasis urs.g ![urs.u, urs.w]) = urs := by
  cases urs with
  | mk k g w u =>
    simp only [ursOfAugmentedBasis, augmentedBasis, AugmentedIndex.gen, AugmentedIndex.u,
      AugmentedIndex.w, BasisIndex.gen, BasisIndex.u, BasisIndex.w, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A commitment collision gives an explicit nontrivial algebraic relation over the URS generators. -/
def relationWitnessOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    AlgebraicRelationWitness (F := F) urs.g := by
  let r := NontrivialDLRelation.ofCollision urs hcollision hneq
  exact { coeffs := r.coeffs, nontrivial := r.nontrivial, relation := r.relation }

/-- A commitment collision gives an AGM representation of the identity over the URS generators. -/
def groupRepresentationOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    GroupRepresentation (F := F) urs.g (0 : G) :=
  (relationWitnessOfCollision urs hneq hcollision).toGroupRepresentation

end Zcash.Snark

import Zcash.Common.DiscreteLogRelation

/-!
# The programmed-basis relation-to-DL adapter

Relation-finding at a basis programmed from a DL challenge reduces to the discrete log of
the challenge (Jaeger–Tessaro, [Expected-Time Cryptography: Generic Techniques and
Applications to Concrete Soundness](https://eprint.iacr.org/2020/1213), Lemma 3): every
slot presents `x i • B + y i • C`, so a returned relation reads
`0 = (∑ i, aᵢ·xᵢ) • B + (∑ i, aᵢ·yᵢ) • C` and the reduction divides by `∑ i, aᵢ·yᵢ`.
`programmedExtractOrMiss` is its extract-or-miss form, and
`Zcash.Common.RelationProbability` prices its one failing hyperplane at `1/|F|`.

This module is deliberately separate from the relation vocabulary and known-log
dischargers of `Zcash.Common.DiscreteLogRelation`: a programmed basis is inconsistent with
the deployed one, so nothing stated at the deployed bases may assume it. It is also not
required if the discrete-log relation problem itself, for bases output by the group hash,
is accepted as the target hard problem.
-/

namespace Zcash

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A DL challenge programmed into every basis slot: slot `i` presents `x i • B + y i • C`.

For a challenge in the base's span — `C = z • B`, as the DL game supplies — uniform pairs
`(x i, y i)` present uniform slot logs `x i + z * y i`, so the simulation is perfect;
`Common.RelationProbability.programmedRelSet_card` proves that counting. -/
structure ProgrammedBasisEmbedding {ι : Type*} [Fintype ι] (B C : G) (basis : ι → G) where
  x : ι → F
  y : ι → F
  programmed : ∀ i, basis i = x i • B + y i • C

/-- Over a programmed basis, a representation separates into base and challenge components. -/
theorem representationEval_programmed {ι : Type*} [Fintype ι]
    (B C : G) (basis : ι → G) (x y coeffs : ι → F)
    (hprog : ∀ i, basis i = x i • B + y i • C) :
    representationEval basis coeffs =
      (∑ i, coeffs i * x i) • B + (∑ i, coeffs i * y i) • C := by
  calc
    representationEval basis coeffs
        = ∑ i, ((coeffs i * x i) • B + (coeffs i * y i) • C) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hprog i, smul_add, smul_smul, smul_smul]
    _ = (∑ i, coeffs i * x i) • B + (∑ i, coeffs i * y i) • C := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]

/-- Recover the challenge's discrete log from a relation with nonzero challenge component — a
field solve for `C`, with no slot guess. -/
def discreteLogOfChallenge_of_relation {ι : Type*} [Fintype ι]
    (B C : G) (basis : ι → G) (x y : ι → F)
    (r : AlgebraicRelationWitness (F := F) basis)
    (hprog : ∀ i, basis i = x i • B + y i • C)
    (hpair : (∑ i, r.coeffs i * y i) ≠ 0) :
    DiscreteLogWitness (F := F) B C := by
  refine ⟨(∑ i, r.coeffs i * y i)⁻¹ * (-(∑ i, r.coeffs i * x i)), ?_⟩
  have hzero : (∑ i, r.coeffs i * x i) • B + (∑ i, r.coeffs i * y i) • C = 0 := by
    rw [← representationEval_programmed B C basis x y r.coeffs hprog]
    exact r.relation
  have hmul : (∑ i, r.coeffs i * y i) • C = (-(∑ i, r.coeffs i * x i)) • B := by
    calc
      (∑ i, r.coeffs i * y i) • C = -((∑ i, r.coeffs i * x i) • B) :=
        eq_neg_of_add_eq_zero_right hzero
      _ = (-(∑ i, r.coeffs i * x i)) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (∑ i, r.coeffs i * y i)⁻¹ • X)) hmul
  have hlog : C = ((∑ i, r.coeffs i * y i)⁻¹ * (-(∑ i, r.coeffs i * x i))) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hpair] using hscale
  exact hlog.symm

/-- The result of testing one returned relation against the challenge programming. Both branches
retain that same relation: *either* it yields the challenge's discrete log, *or* its component
against `y` is zero. -/
abbrev ProgrammedRelationOutcome {ι : Type*} [Fintype ι] (B C : G) (basis : ι → G)
    (y : ι → F) : Type _ :=
  Σ' r : AlgebraicRelationWitness (F := F) basis,
    DiscreteLogWitness (F := F) B C ⊕' ((∑ i, r.coeffs i * y i) = 0)

/-- Extract the challenge's discrete log, or return proof that the same relation has zero
challenge component. -/
def programmedExtractOrMiss {ι : Type*} [Fintype ι] [DecidableEq F]
    (B C : G) {basis : ι → G}
    (embedding : ProgrammedBasisEmbedding (F := F) B C basis)
    (r : AlgebraicRelationWitness (F := F) basis) :
    ProgrammedRelationOutcome (F := F) B C basis embedding.y := by
  refine ⟨r, ?_⟩
  if hpair : (∑ i, r.coeffs i * embedding.y i) ≠ 0 then
    exact PSum.inl (discreteLogOfChallenge_of_relation B C basis embedding.x embedding.y r
      embedding.programmed hpair)
  else
    exact PSum.inr (not_ne_iff.mp hpair)

end Zcash

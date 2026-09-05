import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-!
# Nontrivial linear (discrete-log) relations, as computed data

Shared primitive for the reduction-style security arguments (breaks as computed data — see
`Zcash.Security.RandomOracle`): a nontrivial `F`-linear relation among the members of a
family of group elements, carried as *data* (the coefficients) so a reduction can compute it
rather than merely assert its existence. In a prime-order group such a relation always
*exists* propositionally, so an ∃-closed `Prop` would be vacuous; the content is that a
reduction produces one, discharged against discrete-log-relation hardness at the
computational layer.

`AlgebraicRelationWitness` is the single underlying type: an explicit nonzero coefficient
vector over an arbitrary finite index whose MSM over the presented basis is zero. Every
basis family in the development has a finite index — a fixed generator family is indexed by
`Fin`, and the group-hash family is indexed by hash inputs of concretely bounded length. No
reduction enumerates an index type: proofs and reductions read coefficients at the slots
they name.

The commitment schemes here present a generator family `g` alongside distinguished points
`V` — the basis `(g, U, W)` of a Pedersen-with-blinding scheme, or `(g, U)` for a
Sinsemilla domain point. `BasisIndex n J` names the slots of such a basis, and
`NontrivialRelation g V` is `AlgebraicRelationWitness` at it. A reducer builds its
relation at the sub-basis that its site presents (e.g. `NontrivialRelation g ![U, W]` or
`NontrivialRelation g ![U]`), and `embed` carries it by zero-extension into a larger
basis — in the ledger layer, the combined deployed basis carrying every deployed point
under a named slot type. Both crypto layers instantiate this: the binding-signature
reduction (`Zcash.Security.BindingSignature`) and the deployed-verifier soundness peel
(`Zcash.Snark`). Each use site documents its own reading of the generators.

The module also carries the representation types of algebraic provers
(`GroupRepresentation`, `AlgebraicPoint`, `DiscreteLogWitness`) and the known-log
dischargers turning a computed relation into a discrete log
(`discreteLogOfBasis_of_relation` and its augmented-basis forms). The programmed-basis
adapter is deliberately elsewhere (`Zcash.Common.ProgrammedBasis`): a programmed basis is
inconsistent with the deployed one, so nothing stated at the deployed bases may assume it.

The representation types borrow basic structure from ArkLib's AGM `Basic.lean`
(<https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/AGM/Basic.lean#L13-L14>).
ArkLib is not a dependency or reference proof: its adversary layer is unfinished. This
repository defines and proves the operational prover, certificate, and reductions used
here.
-/

namespace Zcash

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Evaluate a representation over an arbitrary finite public basis. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- Explicit nonzero coefficients whose MSM over `basis` is zero. -/
structure AlgebraicRelationWitness {ι : Type*} [Fintype ι] (basis : ι → G) where
  coeffs : ι → F
  nontrivial : coeffs ≠ 0
  relation : representationEval basis coeffs = 0

/-- A nontrivial finite relation has a nonzero coefficient at some basis slot.

`Common.RelationProbability` uses this slot as the pivot of its hyperplane counting. -/
theorem AlgebraicRelationWitness.exists_nonzero_coeff {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    ∃ i, r.coeffs i ≠ 0 := by
  by_contra h
  apply r.nontrivial
  funext i
  exact not_not.mp (not_exists.mp h i)

/-- Zero-extension of a relation witness into a larger basis, along a slot injection
presented as a section `f` with a partial inverse `r`. The coefficients transport along
`f` and vanish off its image, so the relation sum and nontriviality carry over. The
partial inverse keeps the definition computable — membership in the image is read off
`r`, with no inverse search. -/
def AlgebraicRelationWitness.embed {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    {basis : ι → G}
    (w : AlgebraicRelationWitness (F := F) basis) {basis' : ι' → G}
    (f : ι → ι') (r : ι' → Option ι) (hr : Function.IsPartialInv f r)
    (hcompat : ∀ i, basis' (f i) = basis i) :
    AlgebraicRelationWitness (F := F) basis' where
  coeffs := fun j => match r j with | some i => w.coeffs i | none => 0
  nontrivial := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp w.nontrivial
    refine Function.ne_iff.mpr ⟨f i, ?_⟩
    simpa [hr.eq i] using hi
  relation := by
    have hvanish : ∀ j ∈ Finset.univ, j ∉ Finset.univ.image f →
        (fun j => match r j with | some i => w.coeffs i | none => 0) j • basis' j = 0 := by
      intro j _ hj
      rcases hj' : r j with _ | i
      · simp [hj']
      · exact absurd
          (by rw [← (hr i j).mp hj']; exact Finset.mem_image_of_mem f (Finset.mem_univ i))
          hj
    rw [representationEval]
    calc ∑ j, (fun j => match r j with | some i => w.coeffs i | none => 0) j • basis' j
        = ∑ j ∈ Finset.univ.image f,
            (fun j => match r j with | some i => w.coeffs i | none => 0) j • basis' j :=
          (Finset.sum_subset (Finset.subset_univ _) hvanish).symm
      _ = ∑ i, (fun j => match r j with | some i => w.coeffs i | none => 0) (f i) •
            basis' (f i) :=
          Finset.sum_image fun a _ b _ h => hr.injective h
      _ = ∑ i, w.coeffs i • basis i :=
          Finset.sum_congr rfl fun i _ => by rw [hcompat i]; simp [hr.eq i]
      _ = 0 := w.relation

/-- The partial inverse of an identity-on-generators slot injection `Sum.map id g`:
generator slots invert to themselves, and distinguished slots invert through `gr`. -/
def sumMapPartialInv {α β γ : Type*} (gr : γ → Option β) : Sum α γ → Option (Sum α β) :=
  fun x => match x with
    | .inl a => some (.inl a)
    | .inr c => (gr c).map .inr

/-- The identity-on-generators sum of a partial inverse is a partial inverse. -/
theorem isPartialInv_sumMap_id {α β γ : Type*} {g : β → γ} {gr : γ → Option β}
    (hg : Function.IsPartialInv g gr) :
    Function.IsPartialInv (Sum.map (id : α → α) g) (sumMapPartialInv gr) := by
  rintro (a | b) (c | d)
  · simpa [sumMapPartialInv] using eq_comm
  · simp [sumMapPartialInv]
  · simp [sumMapPartialInv]
  · simpa [sumMapPartialInv] using hg b d

/-- The constant one-slot map into slot `t` has the evident partial inverse. -/
theorem isPartialInv_const_slot {γ : Type*} [DecidableEq γ] (t : γ) :
    Function.IsPartialInv (fun _ : Fin 1 => t)
      (fun j => if j = t then some 0 else none) := by
  intro x y
  fin_cases x
  by_cases h : y = t
  · simp [h]
  · simp only [h, if_false]
    exact ⟨fun hc => absurd hc (by simp), fun ht => absurd ht.symm h⟩

/-- Coefficients over `basis` whose MSM equals `target`.

Every group element output by an algebraic prover carries this data. -/
structure GroupRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  coeffs : ι → F
  hEq : representationEval basis coeffs = target

/-- A group element bundled with a representation over `basis`. -/
structure AlgebraicPoint {ι : Type*} [Fintype ι] (basis : ι → G) where
  point : G
  repr : GroupRepresentation (F := F) basis point

namespace AlgebraicPoint

/-- The coefficients carried by an algebraic point. -/
def coeffs {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) : ι → F :=
  P.repr.coeffs

/-- An algebraic point's coefficients evaluate back to the point itself:
`representationEval basis P.coeffs = P.point`.

This is the bundled `GroupRepresentation.hEq` restated through the `coeffs` projection, as `simp`,
so a consumer holding an `AlgebraicPoint` can rewrite its MSM away without unfolding `repr`. -/
@[simp] theorem hEq {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) :
    representationEval basis P.coeffs = P.point :=
  P.repr.hEq

end AlgebraicPoint

/-- A relation witness is the same data as a representation of the identity. -/
def AlgebraicRelationWitness.toGroupRepresentation {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    GroupRepresentation (F := F) basis (0 : G) :=
  { coeffs := r.coeffs
    hEq := r.relation }

/-- The commitment over arbitrary generators `g`: `⟨a, g⟩ = Σᵢ aᵢ • gᵢ`. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- Additivity in the witness. -/
theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness. -/
theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators. -/
theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- Subtractivity in the witness. -/
theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Negation in the witness. -/
theorem commitGen_neg {n : ℕ} (g : Fin n → G) (a : Fin n → F) :
    commitGen g (-a) = -commitGen g a := by
  simpa using commitGen_smul_left g (-1) a

/-- `representationEval` specializes to the `commitGen` MSM over `Fin n`. -/
theorem representationEval_fin {n : ℕ} (basis : Fin n → G) (coeffs : Fin n → F) :
    representationEval basis coeffs = commitGen basis coeffs := rfl

/-! ### Presented bases with distinguished slots

The named index type identifies the slots of a basis `(g, V)`, so the fixed shapes below
are instantiations of `AlgebraicRelationWitness` at the corresponding bases. -/

/-- The index of a presented basis: `n` generator slots, plus a distinguished slot for each
member of `J`. -/
abbrev BasisIndex (n : ℕ) (J : Type*) := Sum (Fin n) J

namespace BasisIndex

/-- The slot for a family generator. -/
def gen {n : ℕ} {J : Type*} (i : Fin n) : BasisIndex n J := Sum.inl i

/-- The slot for the first distinguished point (`U` in a `(g, U, W)` basis). -/
def u {n k : ℕ} : BasisIndex n (Fin (k + 1)) := Sum.inr 0

/-- The slot for the second distinguished point (`W` in a `(g, U, W)` basis). -/
def w {n k : ℕ} : BasisIndex n (Fin (k + 2)) := Sum.inr 1

end BasisIndex

/-- The index of a two-point basis `(g, U, W)` — the shape the SNARK soundness layer works
at throughout. -/
abbrev AugmentedIndex (n : ℕ) := BasisIndex n (Fin 2)

namespace AugmentedIndex

/-- The slot for a family generator. -/
abbrev gen {n : ℕ} (i : Fin n) : AugmentedIndex n := BasisIndex.gen i

/-- The slot for `U`. -/
abbrev u {n : ℕ} : AugmentedIndex n := BasisIndex.u

/-- The slot for `W`. -/
abbrev w {n : ℕ} : AugmentedIndex n := BasisIndex.w

end AugmentedIndex

/-- A generator family `g` augmented by the distinguished points `V`, as one indexed
basis. -/
def augmentedBasis {n : ℕ} {J : Type*} (g : Fin n → G) (V : J → G) :
    BasisIndex n J → G :=
  Sum.elim g V

/-- One coefficient vector over the augmented basis, from its generator and distinguished
parts. -/
def augmentedCoeffs {n : ℕ} {J : Type*} (a : Fin n → F) (c : J → F) :
    BasisIndex n J → F :=
  Sum.elim a c

/-- Evaluating an augmented representation is the generator MSM plus the distinguished
combination. -/
theorem representationEval_augmentedBasis {n : ℕ} {J : Type*} [Fintype J]
    (g : Fin n → G) (V : J → G) (a : Fin n → F) (c : J → F) :
    representationEval (augmentedBasis g V) (augmentedCoeffs a c) =
      commitGen g a + ∑ j, c j • V j := by
  simp [representationEval, augmentedBasis, augmentedCoeffs, commitGen, Fintype.sum_sum_type]

/-- A nontrivial `F`-linear (discrete-log) relation among the generators `g` and the
distinguished points `V`: `AlgebraicRelationWitness` at the augmented basis. Build one from
its parts with `NontrivialRelation.ofParts`; at a two-point basis `![U, W]`, read the
distinguished coefficients back with the `α`/`β` accessors. The one-point form
`NontrivialRelation g ![U]` is the shape of a Sinsemilla discrete-log break (protocol spec
Theorem 5.4.4): a relation among the per-chunk generator table and the domain point `Q`,
produced as data by the escape reduction
(`Zcash.Security.Ledger.Bridge.relationOfBreakData`). -/
abbrev NontrivialRelation {n : ℕ} {J : Type*} [Fintype J] (g : Fin n → G) (V : J → G) :
    Type _ :=
  AlgebraicRelationWitness (F := F) (augmentedBasis g V)

/-- Assemble an augmented relation from its parts: generator coefficients `a` and
distinguished coefficients `c`, not all zero, sending the basis to `0`. -/
def NontrivialRelation.ofParts {n : ℕ} {J : Type*} [Fintype J] {g : Fin n → G}
    {V : J → G} (a : Fin n → F) (c : J → F)
    (hnontrivial : a ≠ 0 ∨ c ≠ 0)
    (hrelation : commitGen g a + ∑ j, c j • V j = 0) :
    NontrivialRelation (F := F) g V where
  coeffs := augmentedCoeffs a c
  nontrivial := by
    rcases hnontrivial with ha | hc
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      exact Function.ne_iff.mpr ⟨BasisIndex.gen i,
        by simpa [BasisIndex.gen, augmentedCoeffs] using hi⟩
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
      exact Function.ne_iff.mpr ⟨Sum.inr j, by simpa [augmentedCoeffs] using hj⟩
  relation := by rw [representationEval_augmentedBasis]; exact hrelation

/-- The coefficient at the first distinguished slot (`α` in the classical `(a, α, β)`
coefficient shape). -/
abbrev NontrivialRelation.α {n k : ℕ} {g : Fin n → G} {V : Fin (k + 1) → G}
    (r : NontrivialRelation (F := F) g V) : F :=
  r.coeffs BasisIndex.u

/-- The coefficient at the second distinguished slot (`β` in the classical `(a, α, β)`
coefficient shape). -/
abbrev NontrivialRelation.β {n k : ℕ} {g : Fin n → G} {V : Fin (k + 2) → G}
    (r : NontrivialRelation (F := F) g V) : F :=
  r.coeffs BasisIndex.w

/-- The shared computed-data relation over the augmented basis `(g, U, W)`, in the curried
spelling the SNARK soundness layer uses. -/
abbrev AugmentedRelationWitness {n : ℕ} (g : Fin n → G) (U W : G) :=
  NontrivialRelation (F := F) g ![U, W]

/-- **The combination-collision assembler.** Two `(g, U, W)`-combinations equal as group
elements, with coordinates that do not all agree, compute a nontrivial discrete-log
relation: the coordinate differences `(a − a', α − α', β − β')`. -/
def NontrivialRelation.ofCombinationCollision [DecidableEq F] {n : ℕ} {g : Fin n → G} {U W : G}
    {a a' : Fin n → F} {α α' β β' : F}
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W)
    (hne : ¬(a = a' ∧ α = α' ∧ β = β')) : NontrivialRelation (F := F) g ![U, W] :=
  NontrivialRelation.ofParts (a - a') ![α - α', β - β']
    (by
      by_cases ha : a = a'
      · by_cases hα : α = α'
        · refine Or.inr (Function.ne_iff.mpr ⟨1, ?_⟩)
          simpa using sub_ne_zero.mpr (fun hβ => hne ⟨ha, hα, hβ⟩)
        · refine Or.inr (Function.ne_iff.mpr ⟨0, ?_⟩)
          simpa using sub_ne_zero.mpr hα
      · exact Or.inl (sub_ne_zero.mpr ha))
    (by
      have hrw : commitGen g (a - a') + ∑ j, ![α - α', β - β'] j • ![U, W] j
          = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
        rw [commitGen_sub, Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_smul]
        abel
      rw [hrw, e, sub_self])

/-- Over a zero second distinguished point, a relation with a nonzero generator-slot
coefficient vector or a nonzero `α` converts to the one-point form. The `β` coefficient
contributes nothing —it scales the zero point— so it cannot carry the nontriviality. -/
def NontrivialRelation.toOne {n : ℕ} {g : Fin n → G} {U : G}
    (rel : NontrivialRelation (F := F) g ![U, 0])
    (h : (fun i => rel.coeffs (BasisIndex.gen i)) ≠ 0 ∨ rel.α ≠ 0) :
    NontrivialRelation (F := F) g ![U] :=
  NontrivialRelation.ofParts (fun i => rel.coeffs (BasisIndex.gen i)) ![rel.α]
    (by
      rcases h with ha | hα
      · exact Or.inl ha
      · refine Or.inr (Function.ne_iff.mpr ⟨0, ?_⟩)
        simpa using hα)
    (by
      have hr := rel.relation
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
      simpa [NontrivialRelation.α, representationEval, Fintype.sum_sum_type,
        Fin.sum_univ_two, augmentedBasis, BasisIndex.gen, BasisIndex.u] using hr)

/-! ### The known-log relation-to-DL dischargers

Nothing here restricts the adversary: the dischargers are linear algebra over a public basis
and field solves, and what scopes them is how the basis is *sampled*, not who produced the
relation. The algebraic group model — the claim that a prover emits a representation
alongside every group element it outputs — is a separate layer, stated in
`Zcash.Snark.Soundness.AGM`. -/

/-- A scalar `log` such that `log • B = target`.  The cryptographic reading requires `B ≠ 0`; at
`B = 0` only `target = 0` is representable.

Named `…Witness` rather than `…Representation` because "representation" already carries at least
four unrelated meanings across widely used libraries, per the CompElliptic naming survey
(<https://github.com/daira/CompElliptic/blob/main/design/naming-survey.md>).
`GroupRepresentation` keeps the word: it *is* a representation over a basis. -/
structure DiscreteLogWitness (B target : G) where
  log : F
  hEq : log • B = target

/-- The known-log contribution of every basis slot except the challenge slot. -/
def relationLogExcept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (logs coeffs : ι → F) (challenge : ι) : F :=
  (Finset.univ.erase challenge).sum fun i => coeffs i * logs i

/-- If every non-challenge basis element has a known log over `B`, then a relation separates
into the challenge term plus a known scalar multiple of `B`. -/
theorem representationEval_eq_challenge_add_known {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : G) (basis : ι → G) (logs coeffs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • B) :
    representationEval basis coeffs =
      coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • B := by
  have hsum : ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
      = relationLogExcept logs coeffs challenge • B := by
    calc
      ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
          = (Finset.univ.erase challenge).sum (fun i => coeffs i • (logs i • B)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hknown i (Finset.mem_erase.mp hi).1]
      _ = (Finset.univ.erase challenge).sum (fun i => (coeffs i * logs i) • B) := by
            simp [smul_smul]
      _ = relationLogExcept logs coeffs challenge • B := by
            rw [relationLogExcept, Finset.sum_smul]
  calc
    representationEval basis coeffs
        = ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i)
            + coeffs challenge • basis challenge := by
          rw [representationEval, ← Finset.sum_erase_add _ _ (Finset.mem_univ challenge)]
    _ = coeffs challenge • basis challenge
            + ((Finset.univ.erase challenge).sum fun i => coeffs i • basis i) := by
          abel
    _ = coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • B := by
          rw [hsum]

/-- Recover the challenge slot's discrete log from a relation that has a nonzero coefficient there.

The challenge slot is fixed before the relation is returned, and the logs of every other slot are
known. -/
def discreteLogOfBasis_of_relation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : G) (basis : ι → G) (logs : ι → F) (challenge : ι)
    (r : AlgebraicRelationWitness (F := F) basis)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • B)
    (hcoeff : r.coeffs challenge ≠ 0) :
    DiscreteLogWitness (F := F) B (basis challenge) := by
  let known : F := relationLogExcept logs r.coeffs challenge
  refine ⟨(r.coeffs challenge)⁻¹ * (-known), ?_⟩
  have hsplit := representationEval_eq_challenge_add_known B basis logs r.coeffs challenge hknown
  have hzero : r.coeffs challenge • basis challenge + known • B = 0 := by
    rw [← hsplit]
    exact r.relation
  have hmul : r.coeffs challenge • basis challenge = (-known) • B := by
    calc
      r.coeffs challenge • basis challenge = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.coeffs challenge)⁻¹ • X)) hmul
  have hlog : basis challenge = ((r.coeffs challenge)⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hcoeff] using hscale
  exact hlog.symm

/-- Use an augmented relation to solve DL when it hits the fixed challenge slot. -/
def discreteLogOfAugmentedRelationAtChallenge {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (logs : BasisIndex n (Fin 2) → F) (challenge : BasisIndex n (Fin 2))
    (r : AugmentedRelationWitness (F := F) g U W)
    (hknown : ∀ i, i ≠ challenge → augmentedBasis g ![U, W] i = logs i • B)
    (hcoeff : r.coeffs challenge ≠ 0) :
    DiscreteLogWitness (F := F) B (augmentedBasis g ![U, W] challenge) :=
  discreteLogOfBasis_of_relation B (augmentedBasis g ![U, W]) logs challenge r hknown hcoeff

/-- Recover the discrete log of `U` from an augmented relation with a nonzero `α`
coefficient.

The logs of every family generator and of `W` over `B` must be known. -/
def discreteLogOfU_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (wLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hW : W = wLog • B)
    (hcoeff : r.α ≠ 0) :
    DiscreteLogWitness (F := F) B U :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog ![0, wLog])
    BasisIndex.u r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · exact absurd rfl hi
        · simpa [augmentedBasis, augmentedCoeffs] using hW)
    hcoeff

/-- Recover the discrete log of `W` from an augmented relation with a nonzero `β`
coefficient.

The logs of every family generator and of `U` over `B` must be known. -/
def discreteLogOfW_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (uLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hU : U = uLog • B)
    (hcoeff : r.β ≠ 0) :
    DiscreteLogWitness (F := F) B W :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog ![uLog, 0])
    BasisIndex.w r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · simpa [augmentedBasis, augmentedCoeffs] using hU
        · exact absurd rfl hi)
    hcoeff

end Zcash

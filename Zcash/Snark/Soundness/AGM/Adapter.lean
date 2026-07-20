import Zcash.Snark.Soundness.Deployed.Binding

/-!
# AGM relations and the fixed-slot DL reduction

The deployed soundness code can return `NontrivialRelation g U W`: explicit coefficients for a
relation among `(g, U, W)`. Merely proving that such a relation exists says nothing in a prime-order
group. Computing its coefficients is the security break.

This module turns that relation into a plain discrete-log solution. Following
Fuchsbauer–Kiltz–Loss (<https://eprint.iacr.org/2017/620>), the reduction places its DL challenge in
one basis slot before the adversary runs and knows the logs of all other slots. It solves the
challenge when the returned relation has a nonzero coefficient in that slot.

The representation types borrow basic structure from ArkLib's AGM `Basic.lean`
(<https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/AGM/Basic.lean#L13-L14>). ArkLib is not a
dependency or reference proof: its adversary layer is unfinished. This repository defines and
proves the operational prover, certificate, and reductions used here.

## What is formalized here

* Representations over a public basis (`GroupRepresentation`, `AlgebraicPoint`,
  `AlgebraicRelationWitness`).
* The fixed-slot relation-to-DL adapter (`discreteLogOfBasis_of_relation`) and its collision and
  augmented-basis forms.
* The challenge game (`DLChallengeGame`) and conditional extractor (`solveFromRelation`).
* The finite fact used by the probability proof: every nontrivial relation hits at least one slot.

## Computational boundary

`Soundness.AGM.Prover` adds representations to prover and certificate data.
`Soundness.AGM.Peel` and `.Capstone` compute an IPA opening or relation.
`Soundness.AGM.Probability` proves the slot-loss bound, and `.ProbabilityVesta` applies it to Vesta.

The explicit-certificate path is computable. Its assumptions are the AGM, plain-DL hardness, the
generator random-oracle model for the URS, and the random-oracle execution that produces a fork
certificate.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Evaluate an AGM representation over an arbitrary finite public basis. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- Coefficients over `basis` whose MSM equals `target`.

Every group element output by an algebraic prover carries this data. -/
structure GroupRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  coeffs : ι → F
  hEq : representationEval basis coeffs = target

/-- A group element bundled with an AGM representation over `basis`. -/
structure AlgebraicPoint {ι : Type*} [Fintype ι] (basis : ι → G) where
  point : G
  repr : GroupRepresentation (F := F) basis point

namespace AlgebraicPoint

/-- The coefficients carried by an algebraic point. -/
def coeffs {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) : ι → F :=
  P.repr.coeffs

@[simp] theorem hEq {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) :
    representationEval basis P.coeffs = P.point :=
  P.repr.hEq

end AlgebraicPoint

/-- `representationEval` specializes to the existing `commitGen` MSM over `Fin n`. -/
theorem representationEval_fin {n : ℕ} (basis : Fin n → G) (coeffs : Fin n → F) :
    representationEval basis coeffs = commitGen basis coeffs := rfl

/-- A scalar `log` such that `log • B = target`.

The cryptographic reading requires `B ≠ 0`. If `B = 0`, only `target = 0` is representable. -/
structure DiscreteLogRepresentation (B target : G) where
  log : F
  hEq : log • B = target

/-- Explicit nonzero coefficients whose MSM over `basis` is zero. -/
structure AlgebraicRelationWitness {ι : Type*} [Fintype ι] (basis : ι → G) where
  coeffs : ι → F
  nontrivial : coeffs ≠ 0
  relation : representationEval basis coeffs = 0

namespace AlgebraicRelationWitness

/-- A relation witness is the same data as a representation of the identity. -/
def toGroupRepresentation {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    GroupRepresentation (F := F) basis (0 : G) :=
  { coeffs := r.coeffs
    hEq := r.relation }

/-- A relation witness also gives an algebraic point for the identity. -/
def toAlgebraicPoint {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    AlgebraicPoint (F := F) basis :=
  { point := 0
    repr := r.toGroupRepresentation }

/-- A nontrivial finite relation has a nonzero coefficient at some basis slot. -/
theorem exists_nonzero_coeff {ι : Type*} [Fintype ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    ∃ i, r.coeffs i ≠ 0 := by
  classical
  by_contra h
  apply r.nontrivial
  funext i
  exact not_not.mp (not_exists.mp h i)

/-- Challenge slots where a fixed-slot DL embedding can extract from this relation. -/
noncomputable def nonzeroCoeffSlots {ι : Type*} [Fintype ι] [DecidableEq ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun i => r.coeffs i ≠ 0

@[simp] theorem mem_nonzeroCoeffSlots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {basis : ι → G} (r : AlgebraicRelationWitness (F := F) basis) (i : ι) :
    i ∈ r.nonzeroCoeffSlots ↔ r.coeffs i ≠ 0 := by
  classical
  simp [nonzeroCoeffSlots]

/-- A nontrivial relation has at least one slot from which extraction succeeds. -/
theorem nonzeroCoeffSlots_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    r.nonzeroCoeffSlots.Nonempty := by
  classical
  obtain ⟨i, hi⟩ := r.exists_nonzero_coeff
  exact ⟨i, by simp [nonzeroCoeffSlots, hi]⟩

/-- Count of challenge slots where the relation has nonzero coefficient. -/
noncomputable def challengeHitCount {ι : Type*} [Fintype ι] [DecidableEq ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) : ℕ :=
  r.nonzeroCoeffSlots.card

/-- At least one challenge slot has a nonzero coefficient.

`Soundness.AGM.Probability.hitProb_ge_inv_card` turns this count into a probability bound. -/
theorem challengeHitCount_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    0 < r.challengeHitCount := by
  classical
  exact Finset.card_pos.mpr r.nonzeroCoeffSlots_nonempty

/-- The number of successful challenge placements is bounded by the number of public basis slots. -/
theorem challengeHitCount_le_total {ι : Type*} [Fintype ι] [DecidableEq ι] {basis : ι → G}
    (r : AlgebraicRelationWitness (F := F) basis) :
    r.challengeHitCount ≤ Fintype.card ι := by
  classical
  dsimp [challengeHitCount, nonzeroCoeffSlots]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_univ i

end AlgebraicRelationWitness

/-- Public input to an algebraic relation adversary.

`params` holds non-group protocol data. `basis` contains every public group element available for
representing adversary outputs. -/
structure AlgebraicAdversaryInput (Params ι : Type*) [Fintype ι] where
  params : Params
  basis : ι → G

/-- The known-log contribution of every basis slot except the challenge slot. -/
def relationLogExcept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (logs coeffs : ι → F) (challenge : ι) : F :=
  (Finset.univ.erase challenge).sum fun i => coeffs i * logs i

/-- If every non-challenge basis element has a known log over `B`, then a relation separates into the
challenge term plus a known scalar multiple of `B`. -/
theorem representationEval_eq_challenge_add_known {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : G) (basis : ι → G) (logs coeffs : ι → F) (challenge : ι)
    (hknown : ∀ i, i ≠ challenge → basis i = logs i • B) :
    representationEval basis coeffs =
      coeffs challenge • basis challenge + relationLogExcept logs coeffs challenge • B := by
  classical
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
    DiscreteLogRepresentation (F := F) B (basis challenge) := by
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

/-- A DL challenge placed in one slot, with known logs for every other slot.

The challenge slot is fixed before the adversary runs. -/
structure FixedSlotEmbedding {ι : Type*} [Fintype ι] (base : G) (basis : ι → G) (challenge : ι) where
  logs : ι → F
  known : ∀ i, i ≠ challenge → basis i = logs i • base

/-- A plain-DL game with the challenge placed in a fixed slot of an AGM input.

A solution is the log of that slot, not a slot chosen after seeing the relation. -/
structure DLChallengeGame (Params ι : Type*) [Fintype ι] [DecidableEq ι] where
  input : AlgebraicAdversaryInput (G := G) Params ι
  base : G
  challenge : ι
  embedding : FixedSlotEmbedding (F := F) base input.basis challenge

namespace DLChallengeGame

/-- A solution of the game: the discrete log of the pre-fixed challenge slot. -/
abbrev Solution {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι) : Type _ :=
  DiscreteLogRepresentation (F := F) game.base (game.input.basis game.challenge)

/-- The returned relation has a nonzero coefficient at the challenge slot. -/
def hits {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis) : Prop :=
  r.coeffs game.challenge ≠ 0

theorem hits_iff_mem_nonzeroCoeffSlots {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis) :
    game.hits r ↔ game.challenge ∈ r.nonzeroCoeffSlots :=
  (r.mem_nonzeroCoeffSlots game.challenge).symm

/-- Solve the game when the returned relation hits the challenge slot. -/
def solveFromRelation {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis)
    (hhit : game.hits r) :
    Solution (F := F) game :=
  discreteLogOfBasis_of_relation game.base game.input.basis game.embedding.logs game.challenge r
    game.embedding.known hhit

end DLChallengeGame

/-- The result of testing one returned relation at the fixed challenge slot.

Both branches retain the same relation: either it yields the discrete log, or its coefficient at
that slot is zero. -/
abbrev FixedSlotRelationOutcome {ι : Type*} [Fintype ι] (B : G) (basis : ι → G)
    (challenge : ι) : Type _ :=
  Σ' r : AlgebraicRelationWitness (F := F) basis,
    DiscreteLogRepresentation (F := F) B (basis challenge) ⊕' (r.coeffs challenge = 0)

/-- Extract a discrete log on a hit; otherwise return proof that the same relation missed the slot. -/
def fixedSlotExtractOrMiss {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (B : G) (basis : ι → G) (challenge : ι)
    (embedding : FixedSlotEmbedding (F := F) B basis challenge)
    (r : AlgebraicRelationWitness (F := F) basis) :
    FixedSlotRelationOutcome (F := F) B basis challenge := by
  refine ⟨r, ?_⟩
  if hhit : r.coeffs challenge ≠ 0 then
    exact PSum.inl (discreteLogOfBasis_of_relation B basis embedding.logs challenge r
      embedding.known hhit)
  else
    exact PSum.inr (not_ne_iff.mp hhit)

/-- The URS part of a relation after substituting `g i = gLog i • B`. -/
def relationGLog {n : ℕ} (gLog a : Fin n → F) : F :=
  commitGen gLog a

/-- If `g i = gLog i • B`, the URS relation equals the scalar MSM of those logs times `B`. -/
theorem commitGen_of_base_logs {n : ℕ} (B : G) (gLog a : Fin n → F) :
    commitGen (fun i => gLog i • B) a = relationGLog gLog a • B := by
  simp [relationGLog, commitGen, Finset.sum_smul, smul_smul, smul_eq_mul]

/-- The shared computed-data relation over the augmented basis `(g, U, W)`. -/
abbrev AugmentedRelationWitness {n : ℕ} (g : Fin n → G) (U W : G) :=
  Zcash.NontrivialRelation (F := F) g U W

/-- The augmented basis index: URS-generator slots plus two slots for `U` and `W`. -/
abbrev AugmentedIndex (n : ℕ) := Sum (Fin n) (Fin 2)

namespace AugmentedIndex

/-- The slot for a URS generator. -/
def gen {n : ℕ} (i : Fin n) : AugmentedIndex n := Sum.inl i

/-- The slot for `U`. -/
def u {n : ℕ} : AugmentedIndex n := Sum.inr 0

/-- The slot for `W`. -/
def w {n : ℕ} : AugmentedIndex n := Sum.inr 1

end AugmentedIndex

/-- Interpret the augmented index as the public basis `(g, U, W)`. -/
def augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G) : AugmentedIndex n → G
  | Sum.inl i => g i
  | Sum.inr j => if j = 0 then U else W

/-- Split an augmented public basis into its URS generators, `U`, and `W`. -/
def ursOfAugmentedBasis (k : ℕ) (basis : AugmentedIndex (2 ^ k) → G) : URS G :=
  { k := k
    g := fun i => basis (AugmentedIndex.gen i)
    u := basis AugmentedIndex.u
    w := basis AugmentedIndex.w }

/-- Splitting an augmented basis into a URS and reassembling it loses no public group element. -/
@[simp] theorem augmentedBasis_ursOfAugmentedBasis (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) :
    augmentedBasis (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w = basis := by
  funext i
  rcases i with i | j
  · rfl
  · fin_cases j <;> simp [augmentedBasis, ursOfAugmentedBasis, AugmentedIndex.u,
      AugmentedIndex.w]

/-- Canonical public AGM input for the augmented `(g, U, W)` basis. -/
def augmentedAdversaryInput {n : ℕ} (g : Fin n → G) (U W : G) :
    AlgebraicAdversaryInput (G := G) Unit (AugmentedIndex n) :=
  { params := ()
    basis := augmentedBasis g U W }

/-- DL challenge game with the hidden challenge pre-placed at the augmented basis slot `challenge`. -/
def augmentedDLChallengeGame {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (challenge : AugmentedIndex n)
    (embedding : FixedSlotEmbedding (F := F) B (augmentedBasis g U W) challenge) :
    DLChallengeGame (F := F) (G := G) Unit (AugmentedIndex n) :=
  { input := augmentedAdversaryInput g U W
    base := B
    challenge := challenge
    embedding := embedding }

/-- The coefficients of an augmented relation as one representation vector. -/
def augmentedCoeffs {n : ℕ} (a : Fin n → F) (alpha beta : F) : AugmentedIndex n → F
  | Sum.inl i => a i
  | Sum.inr j => if j = 0 then alpha else beta

/-- Evaluating an augmented representation is the MSM used by `NontrivialRelation`. -/
theorem representationEval_augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G)
    (a : Fin n → F) (alpha beta : F) :
    representationEval (augmentedBasis g U W) (augmentedCoeffs a alpha beta) =
      commitGen g a + alpha • U + beta • W := by
  simp [representationEval, augmentedBasis, augmentedCoeffs, commitGen, Fintype.sum_sum_type,
    add_assoc]

namespace AugmentedRelationWitness

/-- The same relation witness, viewed as a generic algebraic relation over the augmented basis. -/
def toAlgebraicRelationWitness {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  { coeffs := augmentedCoeffs r.a r.α r.β
    nontrivial := by
      intro hzero
      have ha : r.a = 0 := by
        funext i
        have h := congrFun hzero (AugmentedIndex.gen i)
        simpa [AugmentedIndex.gen, augmentedCoeffs] using h
      have halpha : r.α = 0 := by
        have h := congrFun hzero (AugmentedIndex.u)
        simpa [AugmentedIndex.u, augmentedCoeffs] using h
      have hbeta : r.β = 0 := by
        have h := congrFun hzero (AugmentedIndex.w)
        simpa [AugmentedIndex.w, augmentedCoeffs] using h
      rcases r.nontrivial with hnt | hnt
      · exact hnt ha
      · rcases hnt with hnt | hnt
        · exact hnt halpha
        · exact hnt hbeta
    relation := by
      rw [representationEval_augmentedBasis]
      exact r.relation }

/-- The same relation witness, viewed as an AGM representation of zero over the augmented basis. -/
def toGroupRepresentation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    GroupRepresentation (F := F) (augmentedBasis g U W) (0 : G) :=
  r.toAlgebraicRelationWitness.toGroupRepresentation

end AugmentedRelationWitness

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

/-- Use a commitment collision to solve DL when its difference hits the fixed challenge slot. -/
def discreteLogOfCollisionAtChallenge (urs : URS G) (B : G)
    {a a' : Fin (2 ^ urs.k) → F} (logs : Fin (2 ^ urs.k) → F)
    (challenge : Fin (2 ^ urs.k))
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a')
    (hknown : ∀ i, i ≠ challenge → urs.g i = logs i • B)
    (hcoeff : (a - a') challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (urs.g challenge) :=
  discreteLogOfBasis_of_relation B urs.g logs challenge
    (relationWitnessOfCollision urs hneq hcollision) hknown hcoeff

/-- Use an augmented relation to solve DL when it hits the fixed challenge slot. -/
def discreteLogOfAugmentedRelationAtChallenge {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (logs : AugmentedIndex n → F) (challenge : AugmentedIndex n)
    (r : AugmentedRelationWitness (F := F) g U W)
    (hknown : ∀ i, i ≠ challenge → augmentedBasis g U W i = logs i • B)
    (hcoeff : augmentedCoeffs r.a r.α r.β challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (augmentedBasis g U W challenge) :=
  discreteLogOfBasis_of_relation B (augmentedBasis g U W) logs challenge
    r.toAlgebraicRelationWitness hknown hcoeff

/-- Recover the discrete log of `U` from an augmented relation with a nonzero `U` coefficient.

The logs of every URS generator and `W` over `B` must be known. -/
def discreteLogOfU_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (wLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hW : W = wLog • B) (halpha : r.α ≠ 0) :
    DiscreteLogRepresentation (F := F) B U :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog 0 wLog)
    AugmentedIndex.u r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · exact absurd rfl hi
        · simpa [augmentedBasis, augmentedCoeffs] using hW)
    (by simpa [augmentedCoeffs, AugmentedIndex.u] using halpha)

/-- Recover the discrete log of `W` from an augmented relation with a nonzero `W` coefficient.

The logs of every URS generator and `U` over `B` must be known. -/
def discreteLogOfW_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (uLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hU : U = uLog • B) (hbeta : r.β ≠ 0) :
    DiscreteLogRepresentation (F := F) B W :=
  discreteLogOfAugmentedRelationAtChallenge B g U W (augmentedCoeffs gLog uLog 0)
    AugmentedIndex.w r
    (fun i hi => by
      rcases i with i | j
      · simpa [augmentedBasis, augmentedCoeffs] using hg i
      · fin_cases j
        · simpa [augmentedBasis, augmentedCoeffs] using hU
        · exact absurd rfl hi)
    (by simpa [augmentedCoeffs, AugmentedIndex.w] using hbeta)

end Zcash.Snark

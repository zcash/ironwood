import Zcash.Snark.Soundness.BindingReduction

/-!
# Algebraic-group-model layer: fixed-slot DL reductions for the relation branches

The deployed soundness capstones end in
`S ∨ HasNontrivialRelation g U W`: a proof either satisfies the intended relation or exhibits a
nontrivial discrete-log relation among the augmented bases `(g, U, W)`. In a prime-order group such
relations exist propositionally; the security content is computational: an efficient adversary should not
be able to *find* one.

This module records the algebraic core of the AGM/DLR-to-DL reduction that consumes that relation
branch. The model is the standard one (Fuchsbauer–Kiltz–Loss): the reduction receives a DL challenge,
places it in **one basis slot fixed before the adversary runs**, and knows the discrete logs of every
*other* slot. If the relation found by the adversary has a nonzero coefficient at that pre-fixed slot,
the deterministic adapter recovers the challenge's discrete log.

## What is formalized here

* Representations over a public basis (`GroupRepresentation`, `AlgebraicPoint`,
  `AlgebraicRelationWitness`).
* The deterministic fixed-slot DLR-to-DL adapter (`discreteLogOfBasis_of_relation`) and its
  collision / augmented-basis specializations.
* The fixed-slot challenge game (`DLChallengeGame`): the challenge slot is part of the game, fixed
  before any adversary output; extraction (`solveFromRelation`) is *conditional* on the found
  relation hitting that slot (`hits`).
* The finite accounting behind the probability wrapper: a nontrivial relation hits at least one slot
  (`nonzeroCoeffSlots_nonempty`, `challengeHitCount_pos`), and at most all of them
  (`challengeHitCount_le_total`). This is consumed by `Soundness.AGMProbability`, which **formalizes**
  the probability statement — a uniformly placed challenge slot is hit with probability ≥ `1 / |ι|`
  (`hitProb_ge_inv_card`), the advantage-preserving reduction `Pr[relation]/|ι| ≤ Pr[DL solved]`
  (`reduction_advantage_ge`), and binding from discrete-log hardness (`relation_prob_le_of_DL`).
* The capstone trichotomy (`soundnessOrDLAt_of_soundnessOrRelation`): `S`, or the discrete log of the
  pre-fixed challenge slot, or the named failure event `RelationMissesSlot`.

## What is *not* formalized — and the standing vacuity caveat

The probability wrapper *is* now formalized (`Soundness.AGMProbability`), and the algebraic-*prover*
model is provided at the peel level by `Soundness.AlgebraicPeel`: with the prover's representations
supplied as data (`AlgebraicDeployedAcceptV`), the deployed peel returns an **explicit**
`AugmentedRelationWitness` — its coefficients the prover's representation difference — with no
`Classical.choice` (`deployedToAcceptVWitness`, `algebraicRelationOfDeployedAccept`). What remains
outside Lean: (i) discrete-log hardness itself (the `DLAdvantageLE` hypothesis there — an assumption
by definition); and (ii) the AGM idealization. The algebraic prover is wired to the deployed opening
in `Soundness.AlgebraicCapstone` (`deployedAlgebraicRelation`). The top-level *forking* capstones
still conclude the existential `HasNontrivialRelation` (with `relationWitnessOfHasNontrivialRelation`
the bridge there), but that is inherent — the forking layer produces the transcript existentially from
accept-probability, so an explicit witness at that level is not available by the nature of
rewinding-based extraction, not for want of construction.

Consequently the trichotomy conclusions below are still propositionally `True` at a prime-order
curve — with at least two known-log slots a relation missing the challenge slot always *exists*, so
the `RelationMissesSlot` branch is available without any hypothesis, exactly as `Or.inr` discharges
the original `∨ HasNontrivialRelation` capstones. The formal content is the deterministic extraction
chain (witness → hit → discrete log); the "hidden slot is hit with probability ≥ `1/|ι|`" half of the
computational force is now proved in `Soundness.AGMProbability`, and the residual computational
force — that no feasible adversary *finds* a relation (discrete-log hardness) — remains the
out-of-Lean assumption.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Evaluate an AGM representation over an arbitrary finite public basis. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- An AGM representation of `target` over `basis`: coefficients whose MSM evaluates to `target`.

In the algebraic-prover model this is the data every prover-output group element carries; wiring the
deployed prover to actually *emit* these (rather than conjuring them by choice) is the remaining
scope of issue #15. -/
structure GroupRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  coeffs : ι → F
  hEq : representationEval basis coeffs = target

/-- A group element bundled with an AGM representation over `basis`. Awaits the algebraic-prover
model (issue #15): nothing in the present development produces these from an actual prover run. -/
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

/-- A point represented by one scalar multiple of a base. This is the plain discrete-log artifact.

A DL-hardness reading of this artifact presumes `B ≠ 0` (a generator of the prime-order group): for
`B = 0` the type is inhabited only by `target = 0`, and for `target = 0` it is trivially inhabited by
`log = 0`. -/
structure DiscreteLogRepresentation (B target : G) where
  log : F
  hEq : log • B = target

/-- A nontrivial algebraic relation over a finite public basis. This is the AGM object that a binding
attack is reduced to: explicit coefficients, not just the proposition that a relation exists. -/
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

/-- The finite accounting fact behind the random challenge-slot wrapper: a nontrivial relation has at
least one challenge slot where extraction succeeds. -/
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

/-- The random-slot wrapper has a nonzero finite support of successful challenge placements: a
uniformly placed challenge slot is hit with probability at least `1 / |ι|`. The probability statement
is formalized in `Soundness.AGMProbability` (`hitProb_ge_inv_card`), which consumes this lemma. -/
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

The `params` field is for scalar or protocol data that is not itself a group element. The group-valued
material visible to the AGM extractor is isolated in `basis`, so every group output can be represented
over this finite public basis. -/
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

/-- **Fixed-slot AGM DLR-to-DL adapter.** A nontrivial relation whose challenge-slot coefficient is
nonzero, with known logs for every *other* basis element, recovers the discrete log of the challenge
basis element. The challenge slot is a parameter fixed independently of the relation: this is the
deterministic step a DL reduction runs after placing its challenge in slot `challenge` and observing
a hit. -/
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

/-- Fixed-slot known-log embedding: the hidden DL challenge occupies the single slot `challenge`,
fixed *before* the adversary runs, and the reduction knows the discrete logs of every **other** slot
with respect to `base`. This is exactly the data an actual DL reduction possesses — it does *not*
know the log of `basis challenge`, which is the point of the game. -/
structure FixedSlotEmbedding {ι : Type*} [Fintype ι] (base : G) (basis : ι → G) (challenge : ι) where
  logs : ι → F
  known : ∀ i, i ≠ challenge → basis i = logs i • base

/-- Plain discrete-log challenge game associated with an AGM public input.

The challenge slot is part of the game, sampled/fixed before any adversary output; the embedding
knows the logs of the other slots only. A solution is the discrete log of the *pre-fixed* challenge
slot — not of a slot chosen after seeing a relation. -/
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

/-- The extraction-success event: the found relation has a nonzero coefficient at the game's
pre-fixed challenge slot. Over a uniformly placed slot this happens with probability at least
`challengeHitCount / |ι| ≥ 1 / |ι|` (`challengeHitCount_pos`); the probability accounting is
formalized in `Soundness.AGMProbability`. -/
def hits {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis) : Prop :=
  r.coeffs game.challenge ≠ 0

theorem hits_iff_mem_nonzeroCoeffSlots {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis) :
    game.hits r ↔ game.challenge ∈ r.nonzeroCoeffSlots :=
  (r.mem_nonzeroCoeffSlots game.challenge).symm

/-- Conditional extraction: a relation that hits the pre-fixed challenge slot solves the game. A
relation that misses it does **not** — that failure branch is the price of a faithful fixed-slot
game, and is what the probability wrapper in `Soundness.AGMProbability` averages away over the slot
placement. -/
def solveFromRelation {Params ι : Type*} [Fintype ι] [DecidableEq ι]
    (game : DLChallengeGame (F := F) (G := G) Params ι)
    (r : AlgebraicRelationWitness (F := F) game.input.basis)
    (hhit : game.hits r) :
    Solution (F := F) game :=
  discreteLogOfBasis_of_relation game.base game.input.basis game.embedding.logs game.challenge r
    game.embedding.known hhit

end DLChallengeGame

/-- The scalar contribution of the URS-generator part of an augmented relation after substituting known
discrete logs `gLog i` for each `g i = gLog i • B`. -/
def relationGLog {n : ℕ} (gLog a : Fin n → F) : F :=
  commitGen gLog a

/-- If each `gᵢ` is represented as `gLogᵢ • B`, then the URS part of the augmented relation is represented
by the scalar MSM of those logs. -/
theorem commitGen_of_base_logs {n : ℕ} (B : G) (gLog a : Fin n → F) :
    commitGen (fun i => gLog i • B) a = relationGLog gLog a • B := by
  simp [relationGLog, commitGen, Finset.sum_smul, smul_smul, smul_eq_mul]

/-- The explicit witness form of `HasNontrivialRelation`: coefficients plus the proof that their
augmented MSM vanishes. In the AGM this is what an algebraic adversary's output would provide; in
the present development it is recovered from the existential predicate by choice
(`relationWitnessOfHasNontrivialRelation`), which carries no computational content. -/
structure AugmentedRelationWitness {n : ℕ} (g : Fin n → G) (U W : G) where
  a : Fin n → F
  alpha : F
  beta : F
  nontrivial : a ≠ 0 ∨ alpha ≠ 0 ∨ beta ≠ 0
  relation : commitGen g a + alpha • U + beta • W = 0

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

/-- Evaluating an augmented representation is the augmented MSM used by `HasNontrivialRelation`. -/
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
  { coeffs := augmentedCoeffs r.a r.alpha r.beta
    nontrivial := by
      intro hzero
      have ha : r.a = 0 := by
        funext i
        have h := congrFun hzero (AugmentedIndex.gen i)
        simpa [AugmentedIndex.gen, augmentedCoeffs] using h
      have halpha : r.alpha = 0 := by
        have h := congrFun hzero (AugmentedIndex.u)
        simpa [AugmentedIndex.u, augmentedCoeffs] using h
      have hbeta : r.beta = 0 := by
        have h := congrFun hzero (AugmentedIndex.w)
        simpa [AugmentedIndex.w, augmentedCoeffs] using h
      rcases r.nontrivial with hnt | hnt
      · exact hnt ha
      · rcases hnt with hnt | hnt
        · exact hnt halpha
        · exact hnt hbeta
    relation := by
      rw [representationEval_augmentedBasis, r.relation] }

/-- The same relation witness, viewed as an AGM representation of zero over the augmented basis. -/
def toGroupRepresentation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    GroupRepresentation (F := F) (augmentedBasis g U W) (0 : G) :=
  r.toAlgebraicRelationWitness.toGroupRepresentation

end AugmentedRelationWitness

/-- Explicit witnesses and the existential relation predicate are equivalent. -/
theorem augmentedRelationWitness_iff_hasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) :
    Nonempty (AugmentedRelationWitness (F := F) g U W) ↔
      HasNontrivialRelation (F := F) g U W := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.a, r.alpha, r.beta, r.nontrivial, r.relation⟩
  · rintro ⟨a, alpha, beta, hnt, hrel⟩
    exact ⟨⟨a, alpha, beta, hnt, hrel⟩⟩

/-- Proof-level plumbing, **not** an adversary run: extract an explicit witness from the existential
relation predicate by choice. In a prime-order group a witness always exists propositionally, so this
step carries no computational content. The genuine algebraic-prover discharge — obtaining the witness
from prover-output representations, with no choice — is `Soundness.AlgebraicPeel`
(`deployedToAcceptVWitness` / `algebraicRelationOfDeployedAccept`); this def remains the bridge for the
forking capstones, whose relation branch is existential by the nature of rewinding-based extraction
(the transcript is produced existentially from accept-probability), so no data witness is available
there (issue #15). -/
noncomputable def relationWitnessOfHasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G)
    (hrel : HasNontrivialRelation (F := F) g U W) :
    AugmentedRelationWitness (F := F) g U W :=
  Classical.choice ((augmentedRelationWitness_iff_hasNontrivialRelation g U W).mpr hrel)

/-- A commitment collision gives an explicit nontrivial algebraic relation over the URS generators. -/
def relationWitnessOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    AlgebraicRelationWitness (F := F) urs.g :=
  { coeffs := a - a'
    nontrivial := (relation_of_collision urs hcollision hneq).1
    relation := (relation_of_collision urs hcollision hneq).2 }

/-- A commitment collision gives an AGM representation of the identity over the URS generators. -/
def groupRepresentationOfCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a') :
    GroupRepresentation (F := F) urs.g (0 : G) :=
  (relationWitnessOfCollision urs hneq hcollision).toGroupRepresentation

/-- A commitment collision reduces to the plain discrete log of the pre-fixed challenge URS slot,
provided the collision difference hits that slot, assuming known logs for all other URS generators. -/
def discreteLogOfCollisionAtChallenge (urs : URS G) (B : G)
    {a a' : Fin (2 ^ urs.k) → F} (logs : Fin (2 ^ urs.k) → F)
    (challenge : Fin (2 ^ urs.k))
    (hneq : a ≠ a') (hcollision : commit urs a = commit urs a')
    (hknown : ∀ i, i ≠ challenge → urs.g i = logs i • B)
    (hcoeff : (a - a') challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (urs.g challenge) :=
  discreteLogOfBasis_of_relation B urs.g logs challenge
    (relationWitnessOfCollision urs hneq hcollision) hknown hcoeff

/-- An augmented deployed relation reduces to the plain discrete log of the pre-fixed challenge slot
in `(gᵢ, U, W)`, provided its coefficient there is nonzero, assuming known logs for all other
augmented generators. -/
def discreteLogOfAugmentedRelationAtChallenge {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (logs : AugmentedIndex n → F) (challenge : AugmentedIndex n)
    (r : AugmentedRelationWitness (F := F) g U W)
    (hknown : ∀ i, i ≠ challenge → augmentedBasis g U W i = logs i • B)
    (hcoeff : augmentedCoeffs r.a r.alpha r.beta challenge ≠ 0) :
    DiscreteLogRepresentation (F := F) B (augmentedBasis g U W challenge) :=
  discreteLogOfBasis_of_relation B (augmentedBasis g U W) logs challenge
    r.toAlgebraicRelationWitness hknown hcoeff

/-- The fixed-slot reduction's failure event: some nontrivial augmented relation has vanishing
coefficient at the pre-fixed challenge slot. Note that (like `HasNontrivialRelation` itself) this
event holds propositionally whenever at least two other slots exist in a prime-order group, so the
trichotomy below is vacuous *as a statement*; its content is the extraction chain in the middle
branch. This existential is *not* the event `Soundness.AGMProbability` bounds — it holds with
probability `1`. That module instead bounds the probability, over a uniformly placed slot, that the
adversary's *returned* relation misses the challenge slot (the miss half of the found-relation
hit/miss event, complement of `succSet`), whose finite input is `challengeHitCount_pos`. -/
def RelationMissesSlot {n : ℕ} (g : Fin n → G) (U W : G) (challenge : AugmentedIndex n) : Prop :=
  ∃ (a : Fin n → F) (alpha beta : F), (a ≠ 0 ∨ alpha ≠ 0 ∨ beta ≠ 0)
    ∧ commitGen g a + alpha • U + beta • W = 0
    ∧ augmentedCoeffs a alpha beta challenge = 0

/-- **Fixed-slot capstone handoff.** Any theorem ending in `S ∨ HasNontrivialRelation g U W` yields,
for a challenge slot fixed *before* the relation is seen and embedded with known logs elsewhere:
`S`, or the discrete log of the challenge slot, or the named failure event `RelationMissesSlot`.

Caveat (same as the capstones it wraps): at a prime-order curve the disjunction is propositionally
`True` — the failure branch always *exists* — so the statement itself is vacuous; the content is the
deterministic extraction. The hit-probability half of the computational force (a hidden
uniformly-placed slot is hit with probability ≥ 1/|ι|) is formalized in `Soundness.AGMProbability`;
the residual is discrete-log hardness (no feasible adversary finds a relation), an out-of-Lean
assumption. -/
theorem soundnessOrDLAt_of_soundnessOrRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (challenge : AugmentedIndex n)
    (embedding : FixedSlotEmbedding (F := F) B (augmentedBasis g U W) challenge) {S : Prop}
    (h : S ∨ HasNontrivialRelation (F := F) g U W) :
    S ∨ Nonempty (DiscreteLogRepresentation (F := F) B (augmentedBasis g U W challenge))
      ∨ RelationMissesSlot (F := F) g U W challenge := by
  classical
  rcases h with hS | hrel
  · exact Or.inl hS
  · obtain ⟨a, alpha, beta, hnt, hrel'⟩ := hrel
    by_cases hcoeff : augmentedCoeffs a alpha beta challenge = 0
    · exact Or.inr (Or.inr ⟨a, alpha, beta, hnt, hrel', hcoeff⟩)
    · exact Or.inr (Or.inl
        ⟨discreteLogOfAugmentedRelationAtChallenge B g U W embedding.logs challenge
          ⟨a, alpha, beta, hnt, hrel'⟩ embedding.known hcoeff⟩)

/-- Deterministic AGM-to-DL adapter for a relation whose pre-fixed challenge target is `U` — the
`challenge := AugmentedIndex.u` instance of the fixed-slot embedding, with the known logs given
directly on `g` and `W`.

If every URS generator and `W` have known logs over `B`, then an augmented relation
`⟨a,g⟩ + alpha·U + beta·W = 0` with `alpha ≠ 0` recovers the discrete log of `U` over `B`. -/
def discreteLogOfU_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (wLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hW : W = wLog • B) (halpha : r.alpha ≠ 0) :
    DiscreteLogRepresentation (F := F) B U := by
  subst W
  let known : F := relationGLog gLog r.a + r.beta * wLog
  refine ⟨r.alpha⁻¹ * (-known), ?_⟩
  have hgpart : commitGen g r.a = relationGLog gLog r.a • B := by
    calc
      commitGen g r.a = commitGen (fun i => gLog i • B) r.a := by
        congr 1
        funext i
        exact hg i
      _ = relationGLog gLog r.a • B := commitGen_of_base_logs B gLog r.a
  have hknown : commitGen g r.a + r.beta • (wLog • B) = known • B := by
    rw [hgpart]
    dsimp only [known]
    rw [add_smul, smul_smul]
  have hzero : known • B + r.alpha • U = 0 := by
    rw [← hknown]
    simpa [add_assoc, add_left_comm, add_comm] using r.relation
  have hmul : r.alpha • U = (-known) • B := by
    have hzero' : r.alpha • U + known • B = 0 := by
      simpa [add_comm] using hzero
    calc
      r.alpha • U = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero'
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.alpha)⁻¹ • X)) hmul
  have hlog : U = (r.alpha⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ halpha] using hscale
  exact hlog.symm

/-- Deterministic AGM-to-DL adapter for a relation whose pre-fixed challenge target is `W` — the
`challenge := AugmentedIndex.w` instance of the fixed-slot embedding, with the known logs given
directly on `g` and `U`. -/
def discreteLogOfW_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (uLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hU : U = uLog • B) (hbeta : r.beta ≠ 0) :
    DiscreteLogRepresentation (F := F) B W := by
  subst U
  let known : F := relationGLog gLog r.a + r.alpha * uLog
  refine ⟨r.beta⁻¹ * (-known), ?_⟩
  have hgpart : commitGen g r.a = relationGLog gLog r.a • B := by
    calc
      commitGen g r.a = commitGen (fun i => gLog i • B) r.a := by
        congr 1
        funext i
        exact hg i
      _ = relationGLog gLog r.a • B := commitGen_of_base_logs B gLog r.a
  have hknown : commitGen g r.a + r.alpha • (uLog • B) = known • B := by
    rw [hgpart]
    dsimp only [known]
    rw [add_smul, smul_smul]
  have hzero : known • B + r.beta • W = 0 := by
    rw [← hknown]
    simpa [add_assoc, add_left_comm, add_comm] using r.relation
  have hmul : r.beta • W = (-known) • B := by
    have hzero' : r.beta • W + known • B = 0 := by
      simpa [add_comm] using hzero
    calc
      r.beta • W = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero'
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.beta)⁻¹ • X)) hmul
  have hlog : W = (r.beta⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hbeta] using hscale
  exact hlog.symm

end Zcash.Snark

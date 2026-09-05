import Zcash.Snark.Soundness.AGM.OnlineMultiopen
import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.FiatShamir.Assembly
import Zcash.Snark.Soundness.Pricing.GoodChallenge

/-!
# Straight-line AGM extraction for the deployed IPA

One accepting algebraic transcript is classified as a clean opening, an explicit augmented-basis
relation, or a squeeze-pinned bad-challenge event — from a single adversary execution, with no
rewinding.  `straightLineIpaZeroOrRelation` and `straightLineBindingAttackZRootOrRelation` are the
endpoints; the symbolic IPA equation they read is built from the representation-carrying
`AlgebraicWfProof` interface.

No declaration here rewinds the adversary: every endpoint reads one accepting execution.
-/

namespace Zcash.Snark

open Classical

local instance vestaInhabitedStraightLineIpa : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

/-! ## The scalar discrepancy walk -/

open CompPoly.CPolynomial
open scoped ENNReal

/-- Advance the claimed-opening discrepancy through one IPA round. -/
def ipaDiscrepancyStep (current : Fp) (round : Fp × Fp) (challenge : Fp) : Fp :=
  current + challenge⁻¹ * round.1 + challenge * round.2

/-- The quadratic whose root records a nonzero discrepancy becoming zero in one round. -/
def ipaDiscrepancyPolynomial (current : Fp) (round : Fp × Fp) : CPoly :=
  C round.1 + C current * X + C round.2 * X ^ 2

/-- The discrepancy polynomial is nonzero whenever the incoming discrepancy is nonzero. -/
theorem ipaDiscrepancyPolynomial_ne_zero {current : Fp} (round : Fp × Fp)
    (hcurrent : current ≠ 0) : ipaDiscrepancyPolynomial current round ≠ 0 := by
  intro hzero
  apply hcurrent
  have hcoeff := congrArg (fun p : Polynomial Fp => p.coeff 1) (congrArg toPoly hzero)
  simpa [ipaDiscrepancyPolynomial, toPoly_pow] using hcoeff

/-- Every discrepancy polynomial has degree at most two. -/
theorem ipaDiscrepancyPolynomial_natDegree_le (current : Fp) (round : Fp × Fp) :
    (ipaDiscrepancyPolynomial current round).natDegree ≤ 2 := by
  unfold ipaDiscrepancyPolynomial
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C round.1).le.trans (by omega)
    · exact natDegree_mul_le.trans
        ((Nat.add_le_add (natDegree_C current).le natDegree_X_le).trans (by omega))
  · exact natDegree_mul_le.trans
      ((Nat.add_le_add (natDegree_C round.2).le (natDegree_X_pow_le 2)).trans (by omega))

/-- If a nonzero discrepancy becomes zero, the round challenge is a root of its quadratic. -/
theorem ipaDiscrepancyPolynomial_eval_eq_zero {current challenge : Fp} (round : Fp × Fp)
    (hcurrent : current ≠ 0) (hstep : ipaDiscrepancyStep current round challenge = 0) :
    (ipaDiscrepancyPolynomial current round).eval challenge = 0 := by
  have hchallenge : challenge ≠ 0 := by
    intro hzero
    subst challenge
    exact hcurrent (by simpa [ipaDiscrepancyStep] using hstep)
  calc
    (ipaDiscrepancyPolynomial current round).eval challenge =
        challenge * ipaDiscrepancyStep current round challenge := by
      simp only [ipaDiscrepancyPolynomial, ipaDiscrepancyStep, eval_add,
        eval_mul, eval_pow, eval_C, eval_X]
      field_simp
      ring
    _ = 0 := by rw [hstep, MulZeroClass.mul_zero]

/-- A nonzero-to-zero discrepancy transition lands in the quadratic root set. -/
theorem ipaDiscrepancyStep_mem_badSet {current challenge : Fp} (round : Fp × Fp)
    (hcurrent : current ≠ 0) (hstep : ipaDiscrepancyStep current round challenge = 0) :
    challenge ∈ szBadSet (ipaDiscrepancyPolynomial current round) :=
  mem_szBadSet.mpr
    ⟨ipaDiscrepancyPolynomial_ne_zero round hcurrent,
      ipaDiscrepancyPolynomial_eval_eq_zero round hcurrent hstep⟩

/-- One discrepancy transition has at most two bad challenges. -/
theorem ipaDiscrepancyBadSet_measure_le (current : Fp) (round : Fp × Fp) :
    uniformChallenge.toOuterMeasure (szBadSet (ipaDiscrepancyPolynomial current round)) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  exact le_trans (uniformChallenge_szBadSet _) <|
    ENNReal.div_le_div_right
      (by exact_mod_cast ipaDiscrepancyPolynomial_natDegree_le current round) _

/-- Follow the scalar discrepancy through aligned round and challenge lists. -/
def ipaDiscrepancyFold : Fp -> List (Fp × Fp) -> List Fp -> Fp
  | current, round :: rounds, challenge :: challenges =>
      ipaDiscrepancyFold (ipaDiscrepancyStep current round challenge) rounds challenges
  | current, _, _ => current

/-- The challenge and pinned polynomial encountered at every step of the discrepancy walk. -/
def ipaDiscrepancyRootEvents : Fp -> List (Fp × Fp) -> List Fp ->
    List (Fp × CPoly)
  | current, round :: rounds, challenge :: challenges =>
      (challenge, ipaDiscrepancyPolynomial current round) ::
        ipaDiscrepancyRootEvents (ipaDiscrepancyStep current round challenge) rounds challenges
  | _, _, _ => []

/-- The polynomial fixed immediately before the `j`-th discrepancy challenge. -/
def ipaDiscrepancyPolynomialAt :
    Fp -> List (Fp × Fp) -> List Fp -> Nat -> CPoly
  | current, round :: _, _ :: _, 0 => ipaDiscrepancyPolynomial current round
  | current, round :: rounds, challenge :: challenges, j + 1 =>
      ipaDiscrepancyPolynomialAt (ipaDiscrepancyStep current round challenge)
        rounds challenges j
  | _, _, _, _ => 0

/-- Every prefix-selected discrepancy polynomial still has degree at most two. -/
theorem ipaDiscrepancyPolynomialAt_natDegree_le (initial : Fp) (rounds : List (Fp × Fp))
    (challenges : List Fp) (j : Nat) :
    (ipaDiscrepancyPolynomialAt initial rounds challenges j).natDegree ≤ 2 := by
  induction rounds generalizing initial challenges j with
  | nil => simp [ipaDiscrepancyPolynomialAt]
  | cons round rounds ih =>
      cases challenges with
      | nil => simp [ipaDiscrepancyPolynomialAt]
      | cons challenge challenges =>
          cases j with
          | zero => exact ipaDiscrepancyPolynomial_natDegree_le initial round
          | succ j =>
              exact ih (ipaDiscrepancyStep initial round challenge) challenges j

/-- Looking up a recursive root event gives the corresponding challenge and prefix polynomial. -/
theorem ipaDiscrepancyRootEvents_getElem (initial : Fp) (rounds : List (Fp × Fp))
    (challenges : List Fp) (j : Nat)
    (hj : j < (ipaDiscrepancyRootEvents initial rounds challenges).length) :
    (ipaDiscrepancyRootEvents initial rounds challenges)[j] =
      (challenges.getD j 0, ipaDiscrepancyPolynomialAt initial rounds challenges j) := by
  induction rounds generalizing initial challenges j with
  | nil => simp [ipaDiscrepancyRootEvents] at hj
  | cons round rounds ih =>
      cases challenges with
      | nil => simp [ipaDiscrepancyRootEvents] at hj
      | cons challenge challenges =>
          cases j with
          | zero => simp [ipaDiscrepancyRootEvents, ipaDiscrepancyPolynomialAt]
          | succ j =>
              have hj' : j < (ipaDiscrepancyRootEvents
                  (ipaDiscrepancyStep initial round challenge) rounds challenges).length := by
                simpa [ipaDiscrepancyRootEvents] using hj
              simpa [ipaDiscrepancyRootEvents, ipaDiscrepancyPolynomialAt] using
                ih (ipaDiscrepancyStep initial round challenge) challenges j hj'

/-- Equal-length round and challenge lists produce one root event per round. -/
theorem ipaDiscrepancyRootEvents_length (initial : Fp) (rounds : List (Fp × Fp))
    (challenges : List Fp) (hlength : rounds.length = challenges.length) :
    (ipaDiscrepancyRootEvents initial rounds challenges).length = rounds.length := by
  induction rounds generalizing initial challenges with
  | nil => simp [ipaDiscrepancyRootEvents]
  | cons round rounds ih =>
      cases challenges with
      | nil => simp at hlength
      | cons challenge challenges =>
          simp only [List.length_cons] at hlength
          have hlength' : rounds.length = challenges.length := by omega
          simp [ipaDiscrepancyRootEvents,
            ih (ipaDiscrepancyStep initial round challenge) challenges hlength']

/-- If a nonzero initial discrepancy finishes at zero, some round challenge is in its pinned
quadratic root set.  This is the deterministic core of the straight-line IPA error term. -/
theorem ipaDiscrepancyFold_zero_has_root (initial : Fp) (rounds : List (Fp × Fp))
    (challenges : List Fp) (hinitial : initial ≠ 0)
    (hfinal : ipaDiscrepancyFold initial rounds challenges = 0) :
    ∃ event ∈ ipaDiscrepancyRootEvents initial rounds challenges,
      event.1 ∈ szBadSet event.2 := by
  induction rounds generalizing initial challenges with
  | nil =>
      simp [ipaDiscrepancyFold] at hfinal
      exact (hinitial hfinal).elim
  | cons round rounds ih =>
      cases challenges with
      | nil =>
          simp [ipaDiscrepancyFold] at hfinal
          exact (hinitial hfinal).elim
      | cons challenge challenges =>
          let next := ipaDiscrepancyStep initial round challenge
          by_cases hnext : next = 0
          · refine ⟨(challenge, ipaDiscrepancyPolynomial initial round), ?_, ?_⟩
            · simp [ipaDiscrepancyRootEvents]
            · exact ipaDiscrepancyStep_mem_badSet round hinitial hnext
          · obtain ⟨event, hevent, hroot⟩ := ih next challenges hnext hfinal
            refine ⟨event, ?_, hroot⟩
            simp only [ipaDiscrepancyRootEvents, List.mem_cons]
            exact Or.inr hevent

/-! ## Represented IPA round sum -/

/-- Expand represented IPA round pairs into the two scalar-point terms contributed by each
challenge.  Recursing on lists makes the truncation behavior agree definitionally with
`List.zip`, which is used by the deployed verifier. -/
def representedRoundTerms {n : Nat} {basis : AugmentedIndex n -> VestaG} :
    List (AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis) -> List Fp ->
      List (Fp × AlgebraicPoint (F := Fp) basis)
  | (L, R) :: rounds, u :: challenges =>
      (u⁻¹, L) :: (u, R) :: representedRoundTerms rounds challenges
  | _, _ => []

/-- The represented round terms evaluate to the verifier's ordinary IPA round sum. -/
theorem representedRoundTerms_point_sum {n : Nat} {basis : AugmentedIndex n -> VestaG}
    (rounds : List (AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis))
    (challenges : List Fp) :
    (((representedRoundTerms rounds challenges).map fun t => (t.1, t.2.point)).map
        fun t => t.1 • t.2).sum =
      roundSum (rounds.map fun t => (t.1.point, t.2.point)) challenges := by
  induction rounds generalizing challenges with
  | nil => simp [representedRoundTerms]
  | cons round rounds ih =>
      rcases round with ⟨L, R⟩
      cases challenges with
      | nil => simp [representedRoundTerms]
      | cons u challenges =>
          simp only [representedRoundTerms, List.map_cons, List.sum_cons, roundSum_cons]
          rw [ih challenges]
          abel

/-- The scalar mismatch between the generator coordinates and `U` coordinate of one represented
point, at evaluation vector `b` and deployed IPA scale `z`. -/
def representedPointDiscrepancy
    (b : Fin (2 ^ shape.k) -> Fp) (z : Fp)
    (point : AlgebraicPoint (F := Fp) basis) : Fp :=
  z * innerProduct point.gPart b - point.coeffs AugmentedIndex.u

/-- The two scalar discrepancies carried by one represented IPA round pair. -/
def representedRoundDiscrepancy
    (b : Fin (2 ^ shape.k) -> Fp) (z : Fp)
    (round : AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis) : Fp × Fp :=
  (representedPointDiscrepancy b z round.1, representedPointDiscrepancy b z round.2)

/-- Folding the per-round discrepancies is the same as aggregating the represented round
coordinates and then comparing their generator and `U` parts. -/
theorem ipaDiscrepancyFold_representedRounds
    (b : Fin (2 ^ shape.k) -> Fp) (z initial : Fp)
    (rounds : List
      (AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis))
    (challenges : List Fp) :
    ipaDiscrepancyFold initial (rounds.map (representedRoundDiscrepancy b z)) challenges =
      initial + z * innerProduct (repsGPart (representedRoundTerms rounds challenges)) b -
        repsU (representedRoundTerms rounds challenges) := by
  induction rounds generalizing initial challenges with
  | nil => simp [ipaDiscrepancyFold, representedRoundTerms, repsGPart, repsU, innerProduct]
  | cons round rounds ih =>
      rcases round with ⟨L, R⟩
      cases challenges with
      | nil => simp [ipaDiscrepancyFold, representedRoundTerms, repsGPart, repsU, innerProduct]
      | cons challenge challenges =>
          rw [List.map_cons, ipaDiscrepancyFold, representedRoundTerms,
            ih (ipaDiscrepancyStep initial
              (representedRoundDiscrepancy b z (L, R)) challenge) challenges,
            repsGPart_cons, repsGPart_cons, repsU_cons, repsU_cons,
            innerProduct_add, innerProduct_add, innerProduct_smul, innerProduct_smul]
          simp only [ipaDiscrepancyStep, representedRoundDiscrepancy,
            representedPointDiscrepancy]
          ring

namespace AlgebraicWfProof

/-- The represented point opened by the IPA after applying the deployed value and `S` shifts.

Its coordinates are computed from the single algebraic prover output.  The point is extractor
data only: it is not added to the Halo2 proof or transcript. -/
def straightLineAdjustedPoint
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) :
    AlgebraicPoint (F := Fp) basis :=
  let urs := ursOfAugmentedBasis shape.k basis
  let v := multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))
  let a := adjustedWitness (p.aMulti nu) p.s v (nu 9)
  let pU := p.multiU nu + nu 9 * p.sU
  let pW := p.multiBlind nu + nu 9 * p.sBlind
  { point := commit urs a + pU • urs.u + pW • urs.w
    repr :=
      { coeffs := augmentedCoeffs a ![pU, pW]
        hEq := by
          have h := representationEval_augmentedBasis
            (ursOfAugmentedBasis shape.k basis).g
            ![(ursOfAugmentedBasis shape.k basis).u, (ursOfAugmentedBasis shape.k basis).w]
            a ![pU, pW]
          rw [augmentedBasis_ursOfAugmentedBasis] at h
          simpa [commit_eq_commitGen, Fin.sum_univ_two, _root_.add_assoc] using h } }

/-- The straight-line adjusted point is exactly the initial point in Halo2's deployed IPA
verification equation.  In particular, changing only the IPA-round challenge vector does not
change the pre-IPA multiopen commitment or value. -/
theorem straightLineAdjustedPoint_eq_verifierInitial
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) :
    (p.straightLineAdjustedPoint nu).point =
      multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w
          (ursOfAugmentedBasis shape.k basis).u
          vk instanceCommitment p.proof.1 (chRecord nu chi)
        + (∑ i, ([-multiopenValue vk instanceCommitment p.proof.1
            (chRecord nu chi)].getD i.val 0) •
              (ursOfAugmentedBasis shape.k basis).g i)
        + (chRecord nu chi : Challenges shape.k Fp).xi • p.proof.1.ipaS := by
  symm
  dsimp only [straightLineAdjustedPoint, AlgebraicWfProof.proof]
  rw [← chRecord_update nu chi, multiopenValue_ipaRound,
    multiopenCommitment_ipaRound,
    show ({chRecord nu (fun _ => (0 : Fp)) with ipaRound := chi} :
      Challenges shape.k Fp).xi = nu 9 from rfl,
    ← p.multiopen_repr nu,
    show p.algebraicProof.erase.ipaS = p.algebraicProof.ipaS.point from rfl,
    ← p.ipaS_repr,
    sum_getD_single (ursOfAugmentedBasis shape.k basis).g
      (multiopenValue vk instanceCommitment p.algebraicProof.erase
        (chRecord nu (fun _ => 0)))]
  -- Pin the witness index to `2 ^ shape.k` so the rewrite matches the point's own coordinates.
  have hadj : ∀ a s : Fin (2 ^ shape.k) -> Fp, ∀ v xi : Fp,
      commit (ursOfAugmentedBasis shape.k basis) (adjustedWitness a s v xi) =
        commit (ursOfAugmentedBasis shape.k basis) a -
          v • (ursOfAugmentedBasis shape.k basis).g 0 +
          xi • commit (ursOfAugmentedBasis shape.k basis) s :=
    fun a s v xi =>
      commit_adjustedWitness (ursOfAugmentedBasis shape.k basis) a s v xi
  -- Restate the adjusted side in this file's own spelling so `hadj` matches syntactically.
  change _ = commit (ursOfAugmentedBasis shape.k basis)
        (adjustedWitness (p.aMulti nu) p.s
          (multiopenValue vk instanceCommitment p.algebraicProof.erase
            (chRecord nu (fun _ => 0))) (nu 9)) +
      (p.multiU nu + nu 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
      (p.multiBlind nu + nu 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w
  rw [hadj]
  module

/-! ## The symbolic coordinates of the accepted IPA equation -/

/-- The two represented scalar-point terms contributed by every IPA round in one transcript. -/
def straightLineRoundTerms
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (chi : Fin shape.k -> Fp) :
    List (Fp × AlgebraicPoint (F := Fp) basis) :=
  representedRoundTerms (List.ofFn p.rounds) (List.ofFn chi)

/-- The represented round terms are exactly the round sum in the deployed verifier equation. -/
theorem straightLineRoundTerms_point_sum
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (chi : Fin shape.k -> Fp) :
    ((((p.straightLineRoundTerms chi).map fun t => (t.1, t.2.point)).map
        fun t => t.1 • t.2).sum) =
      roundSum (List.ofFn p.proof.1.ipaRounds) (List.ofFn chi) := by
  rw [straightLineRoundTerms, representedRoundTerms_point_sum]
  congr 1
  simp only [List.map_ofFn]
  rfl

/-- The generator coordinates of the adjusted point are the deployed adjusted witness. -/
theorem straightLineAdjustedPoint_gPart
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) :
    (p.straightLineAdjustedPoint nu).gPart =
      adjustedWitness (p.aMulti nu) p.s
        (multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))) (nu 9) := by
  funext i
  rfl

/-- The `U` coordinate of the adjusted point is the aggregate declared `U` component. -/
theorem straightLineAdjustedPoint_coeffs_u
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) :
    (p.straightLineAdjustedPoint nu).coeffs AugmentedIndex.u =
      p.multiU nu + nu 9 * p.sU := rfl

/-- The discrepancy of the adjusted point before the first IPA round. -/
def straightLineInitialDiscrepancy
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) : Fp :=
  representedPointDiscrepancy (evalVector shape.k (nu 7)) (nu 10)
    (p.straightLineAdjustedPoint nu)

/-- Expand the initial discrepancy into the aggregate opening mismatch used by the deployed
binding-attack predicate. -/
theorem straightLineInitialDiscrepancy_eq
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) :
    p.straightLineInitialDiscrepancy nu =
      nu 10 * (innerProduct (p.aMulti nu) (evalVector shape.k (nu 7)) -
        multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) +
        nu 9 * innerProduct p.s (evalVector shape.k (nu 7))) -
      (p.multiU nu + nu 9 * p.sU) := by
  let b := evalVector shape.k (nu 7)
  let v := multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))
  have hsub : innerProduct (p.aMulti nu - Pi.single 0 v) b =
      innerProduct (p.aMulti nu) b - innerProduct (Pi.single 0 v) b := by
    simp only [innerProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hadjusted :
      innerProduct (adjustedWitness (p.aMulti nu) p.s v (nu 9)) b =
        innerProduct (p.aMulti nu) b - v + nu 9 * innerProduct p.s b := by
    rw [adjustedWitness, innerProduct_add, hsub, innerProduct_single, innerProduct_smul]
    simp [b, evalVector_zero]
  unfold straightLineInitialDiscrepancy representedPointDiscrepancy
  rw [p.straightLineAdjustedPoint_gPart nu, p.straightLineAdjustedPoint_coeffs_u nu]
  rw [show evalVector shape.k (nu 7) = b from rfl, hadjusted]

/-- A deployed binding mismatch with `z ≠ 0` starts the discrepancy walk away from zero. -/
theorem straightLineInitialDiscrepancy_ne_zero_of_bindingAttackZ
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (hattack : fullAlgebraicBindingAttackZ basis vk instanceCommitment p nu chi) :
    p.straightLineInitialDiscrepancy nu ≠ 0 := by
  intro hzero
  apply hattack.1.2
  rw [p.straightLineInitialDiscrepancy_eq nu] at hzero
  have hscaled := sub_eq_zero.mp hzero
  have hz := hattack.2
  calc
    innerProduct (p.aMulti nu) (evalVector shape.k (nu 7)) =
        multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) +
          (nu 10)⁻¹ *
            (nu 10 * (innerProduct (p.aMulti nu) (evalVector shape.k (nu 7)) -
              multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) +
              nu 9 * innerProduct p.s (evalVector shape.k (nu 7)))) -
          nu 9 * innerProduct p.s (evalVector shape.k (nu 7)) := by
            rw [← _root_.mul_assoc, inv_mul_cancel₀ hz]
            ring
    _ = multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) +
          (nu 10)⁻¹ * (p.multiU nu + nu 9 * p.sU) -
          nu 9 * innerProduct p.s (evalVector shape.k (nu 7)) := by rw [hscaled]

/-- The pair of represented opening discrepancies fixed at every IPA round. -/
def straightLineRoundDiscrepancies
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp) :
    List (Fp × Fp) :=
  (List.ofFn p.rounds).map
    (representedRoundDiscrepancy (evalVector shape.k (nu 7)) (nu 10))

/-- The challenge-polynomial pairs encountered by the one-run IPA discrepancy walk. -/
def straightLineIpaRootEvents
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) : List (Fp × CPoly) :=
  ipaDiscrepancyRootEvents (p.straightLineInitialDiscrepancy nu)
    (p.straightLineRoundDiscrepancies nu) (List.ofFn chi)

/-- The quadratic fixed before one concrete IPA-round squeeze. -/
def straightLineIpaRootPolynomial
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) (j : Fin shape.k) : CPoly :=
  ipaDiscrepancyPolynomialAt (p.straightLineInitialDiscrepancy nu)
    (p.straightLineRoundDiscrepancies nu) (List.ofFn chi) j.val

/-- There is exactly one recursive root event for every deployed IPA round. -/
theorem straightLineIpaRootEvents_length
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) :
    (p.straightLineIpaRootEvents nu chi).length = shape.k := by
  have hlength : (p.straightLineRoundDiscrepancies nu).length = (List.ofFn chi).length := by
    simp [straightLineRoundDiscrepancies]
  rw [straightLineIpaRootEvents,
    ipaDiscrepancyRootEvents_length _ _ _ hlength]
  simp [straightLineRoundDiscrepancies]

/-- Looking up round `j` yields its actual challenge and its prefix-fixed quadratic. -/
theorem straightLineIpaRootEvents_getElem
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) (j : Fin shape.k) :
    (p.straightLineIpaRootEvents nu chi)[j.val]'(by
      rw [p.straightLineIpaRootEvents_length nu chi]
      exact j.isLt) = (chi j, p.straightLineIpaRootPolynomial nu chi j) := by
  have hj : j.val < (ipaDiscrepancyRootEvents (p.straightLineInitialDiscrepancy nu)
      (p.straightLineRoundDiscrepancies nu) (List.ofFn chi)).length := by
    have hlen := p.straightLineIpaRootEvents_length nu chi
    simp only [straightLineIpaRootEvents] at hlen
    rw [hlen]
    exact j.isLt
  simpa [straightLineIpaRootEvents, straightLineIpaRootPolynomial] using
    ipaDiscrepancyRootEvents_getElem
      (p.straightLineInitialDiscrepancy nu) (p.straightLineRoundDiscrepancies nu)
      (List.ofFn chi) j.val hj

/-- Generator coordinates of the deployed final folded-generator term. -/
def straightLineFoldGCoords (chi : Fin shape.k -> Fp) (c : Fp) :
    Fin (2 ^ shape.k) -> Fp :=
  fun i => (computeS (List.ofFn chi) (-c)).getD i.val 0

/-- Evaluating the folded-generator coordinates at `x` gives Halo2's `computeB`. -/
theorem straightLineFoldGCoords_innerProduct (chi : Fin shape.k -> Fp) (c x : Fp) :
    innerProduct (straightLineFoldGCoords chi c) (evalVector shape.k x) =
      (-c) * computeB x (List.ofFn chi) := by
  have hev :
      (fun j => evalVector shape.k x
        (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) =
        evalVector (List.ofFn chi).length x := by
    funext j
    simp only [evalVector, Fin.val_cast]
  have hfold := deployed_gterm_foldAll chi c (evalVector shape.k x)
  rw [hev, foldAll_evalVector] at hfold
  simpa [straightLineFoldGCoords, innerProduct, smul_eq_mul] using hfold

/-- Generator coordinates of the complete one-run IPA verifier equation. -/
def straightLineIpaGCoords
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) : Fin (2 ^ shape.k) -> Fp :=
  (p.straightLineAdjustedPoint nu).gPart +
    repsGPart (p.straightLineRoundTerms chi) +
    straightLineFoldGCoords chi p.proof.1.ipaC

/-- `U` coordinate of the complete one-run IPA verifier equation. -/
def straightLineIpaUCoord
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) : Fp :=
  (p.straightLineAdjustedPoint nu).coeffs AugmentedIndex.u +
    repsU (p.straightLineRoundTerms chi) +
    (-p.proof.1.ipaC * computeB (nu 7) (List.ofFn chi) * nu 10)

/-- `W` coordinate of the complete one-run IPA verifier equation. -/
def straightLineIpaWCoord
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) : Fp :=
  (p.straightLineAdjustedPoint nu).coeffs AugmentedIndex.w +
    repsW (p.straightLineRoundTerms chi) - p.proof.1.ipaF

/-- The scalar discrepancy walk ends at the discrepancy between the complete verifier equation's
generator and `U` coordinates.  The final `c * computeB` terms cancel exactly. -/
theorem straightLineIpaDiscrepancyFold_eq
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) :
    ipaDiscrepancyFold (p.straightLineInitialDiscrepancy nu)
        (p.straightLineRoundDiscrepancies nu) (List.ofFn chi) =
      nu 10 * innerProduct (p.straightLineIpaGCoords nu chi)
          (evalVector shape.k (nu 7)) -
        p.straightLineIpaUCoord nu chi := by
  rw [straightLineRoundDiscrepancies, ipaDiscrepancyFold_representedRounds]
  change p.straightLineInitialDiscrepancy nu +
        nu 10 * innerProduct (repsGPart (p.straightLineRoundTerms chi))
          (evalVector shape.k (nu 7)) -
        repsU (p.straightLineRoundTerms chi) = _
  unfold straightLineIpaGCoords straightLineIpaUCoord
  rw [innerProduct_add, innerProduct_add,
    straightLineFoldGCoords_innerProduct]
  unfold straightLineInitialDiscrepancy representedPointDiscrepancy
  ring

/-- Zero symbolic generator and `U` coordinates force the discrepancy walk to finish at zero. -/
theorem straightLineIpaDiscrepancyFold_eq_zero
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (hzero : p.straightLineIpaGCoords nu chi = 0 ∧
      p.straightLineIpaUCoord nu chi = 0) :
    ipaDiscrepancyFold (p.straightLineInitialDiscrepancy nu)
        (p.straightLineRoundDiscrepancies nu) (List.ofFn chi) = 0 := by
  rw [p.straightLineIpaDiscrepancyFold_eq nu chi, hzero.1, hzero.2]
  simp [innerProduct]

/-- Evaluating the symbolic coordinates gives the exact closed-form Halo2 IPA equation. -/
theorem straightLineIpaCoordinates_eval
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (p.straightLineIpaGCoords nu chi) +
        (p.straightLineIpaUCoord nu chi) • (ursOfAugmentedBasis shape.k basis).u +
        (p.straightLineIpaWCoord nu chi) • (ursOfAugmentedBasis shape.k basis).w =
      CF (List.ofFn p.proof.1.ipaRounds) (List.ofFn chi)
        (fun j => (ursOfAugmentedBasis shape.k basis).g
          (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
        (p.straightLineAdjustedPoint nu).point p.proof.1.ipaC
        (-p.proof.1.ipaC * computeB (nu 7) (List.ofFn chi) * nu 10)
        (ursOfAugmentedBasis shape.k basis).u
        (-p.proof.1.ipaF) (ursOfAugmentedBasis shape.k basis).w := by
  let urs := ursOfAugmentedBasis shape.k basis
  let adjusted := p.straightLineAdjustedPoint nu
  let terms := p.straightLineRoundTerms chi
  let folded := straightLineFoldGCoords chi p.proof.1.ipaC
  have hadjusted :
      commit urs adjusted.gPart + adjusted.coeffs AugmentedIndex.u • urs.u +
          adjusted.coeffs AugmentedIndex.w • urs.w = adjusted.point := by
    exact adjusted.point_eq_components.symm
  have hrounds :
      commit urs (repsGPart terms) + repsU terms • urs.u + repsW terms • urs.w =
        roundSum (List.ofFn p.proof.1.ipaRounds) (List.ofFn chi) := by
    rw [← p.straightLineRoundTerms_point_sum chi]
    exact (sum_map_smul_point_repr terms).symm
  have hfolded :
      commit urs folded =
        (-p.proof.1.ipaC) • foldAll (List.ofFn chi)
          (fun j => urs.g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
    rw [commit]
    exact deployed_gterm_foldAll chi p.proof.1.ipaC urs.g
  change commit urs (adjusted.gPart + repsGPart terms + folded) +
      (adjusted.coeffs AugmentedIndex.u + repsU terms +
        (-p.proof.1.ipaC * computeB (nu 7) (List.ofFn chi) * nu 10)) • urs.u +
      (adjusted.coeffs AugmentedIndex.w + repsW terms - p.proof.1.ipaF) • urs.w = _
  have hsplitOuter : commit urs (adjusted.gPart + repsGPart terms + folded) =
      commit urs (adjusted.gPart + repsGPart terms) + commit urs folded :=
    commit_add urs _ _
  have hsplitInner : commit urs (adjusted.gPart + repsGPart terms) =
      commit urs adjusted.gPart + commit urs (repsGPart terms) :=
    commit_add urs _ _
  unfold CF gPart
  linear_combination (norm := module)
    hsplitOuter + hsplitInner + hadjusted + hrounds + hfolded

/-- An accepted algebraic transcript makes the complete symbolic IPA MSM vanish. -/
theorem straightLineIpaCoordinates_eval_eq_zero
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (haccept : fullAlgebraicAccept basis vk instanceCommitment p nu chi) :
    commit (ursOfAugmentedBasis shape.k basis) (p.straightLineIpaGCoords nu chi) +
        (p.straightLineIpaUCoord nu chi) • (ursOfAugmentedBasis shape.k basis).u +
        (p.straightLineIpaWCoord nu chi) • (ursOfAugmentedBasis shape.k basis).w = 0 := by
  rw [p.straightLineIpaCoordinates_eval nu chi,
    p.straightLineAdjustedPoint_eq_verifierInitial nu chi]
  apply (deployedVerifierEq_cf
    (ursOfAugmentedBasis shape.k basis).g
    (ursOfAugmentedBasis shape.k basis).w
    (ursOfAugmentedBasis shape.k basis).u
    vk instanceCommitment p.proof.1 (chRecord nu chi)).mp at haccept
  exact haccept

/-- From one accepting algebraic transcript, either every symbolic IPA coordinate is zero or those
coordinates themselves are an explicit nonzero relation over the public `(g,U,W)` basis. -/
def straightLineIpaZeroOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (haccept : fullAlgebraicAccept basis vk instanceCommitment p nu chi) :
    (p.straightLineIpaGCoords nu chi = 0 ∧
        p.straightLineIpaUCoord nu chi = 0 ∧
        p.straightLineIpaWCoord nu chi = 0) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  exact separateOrRelationWitness (ursOfAugmentedBasis shape.k basis).g
    (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w
    (p.straightLineIpaGCoords nu chi) 0
    (p.straightLineIpaUCoord nu chi) 0
    (p.straightLineIpaWCoord nu chi) 0
    (by
      have h := p.straightLineIpaCoordinates_eval_eq_zero nu chi haccept
      rw [commit_eq_commitGen] at h
      simpa [commitGen] using h)

/-- The one-run binding dichotomy: a false accepted opening with `z ≠ 0` exposes either one of the
round-local quadratic root events or an explicit nonzero relation over the public basis. -/
def straightLineBindingAttackZRootOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (hattack : fullAlgebraicBindingAttackZ basis vk instanceCommitment p nu chi) :
    (∃ event ∈ p.straightLineIpaRootEvents nu chi,
        event.1 ∈ szBadSet event.2) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  cases p.straightLineIpaZeroOrRelation nu chi hattack.1.1 with
  | inr relation => exact PSum.inr relation
  | inl hzero =>
      exact PSum.inl <| ipaDiscrepancyFold_zero_has_root
        (p.straightLineInitialDiscrepancy nu)
        (p.straightLineRoundDiscrepancies nu) (List.ofFn chi)
        (p.straightLineInitialDiscrepancy_ne_zero_of_bindingAttackZ nu chi hattack)
        (p.straightLineIpaDiscrepancyFold_eq_zero nu chi ⟨hzero.1, hzero.2.1⟩)

/-- Indexed form of the one-run dichotomy, ready to become a `Fin shape.k` pinned-root family. -/
def straightLineBindingAttackZIndexedRootOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 -> Fp)
    (chi : Fin shape.k -> Fp)
    (hattack : fullAlgebraicBindingAttackZ basis vk instanceCommitment p nu chi) :
    (∃ j : Fin shape.k,
        chi j ∈ szBadSet (p.straightLineIpaRootPolynomial nu chi j)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  cases p.straightLineBindingAttackZRootOrRelation nu chi hattack with
  | inr relation => exact PSum.inr relation
  | inl root =>
      refine PSum.inl ?_
      obtain ⟨event, hevent, hroot⟩ := root
      obtain ⟨j, hj, heventEq⟩ := List.mem_iff_getElem.mp hevent
      have hjk : j < shape.k := by
        rw [← p.straightLineIpaRootEvents_length nu chi]
        exact hj
      let jf : Fin shape.k := ⟨j, hjk⟩
      have hlookup := p.straightLineIpaRootEvents_getElem nu chi jf
      have heq : event = (chi jf, p.straightLineIpaRootPolynomial nu chi jf) := by
        rw [← heventEq]
        exact hlookup
      rw [heq] at hroot
      exact ⟨jf, hroot⟩

end AlgebraicWfProof

end Zcash.Snark

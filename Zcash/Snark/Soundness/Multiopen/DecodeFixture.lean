import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# Fixture: the decoded-column hypotheses are dischargeable

Regression guard for the decoded-column capstones' hypothesis shapes: every hypothesis of the terminal
decoded lemmas is discharged *concretely* on a toy instance, so a future reshape that reintroduces an
unsatisfiable form (the ∀-families `hquot ∧ hgood` vacuity described in the `MultiopenDecode` scope
section) breaks this file instead of passing silently.

The first instance is the smallest single-point, rotation-free one in the model's documented scope:
`k = 0` (one URS generator, over `G := Fp` itself, where `commit` has trivial kernel), one column, all
data zero — the zero column satisfies the one-gate circuit `advice 0` with zero quotient at the opened
point. The terminal entry points are exercised: `decoded_constraint_of_relation_and_batch` on a bare
batch, `decoded_constraint_of_opening_or_relation` with its `hbatch` *derived* from a family of
accepting IPA transcripts (`multiopenRewindForRelation_of_acceptedFamily`), not assumed, and the
`_xgood` form with its good challenge *derived* from a full-measure accept event rather than
supplied as an `hgood` hypothesis.

The second instance (`Prod` section) is multi-column with nonzero data: three columns `2, 3, 6` at
distinct batching challenges `0, 1, 2`, a two-advice/one-instance gate `a₀·a₁ − i₀` satisfied with zero
quotient, and both terminal endpoints discharged again — so the decoded shapes are exercised beyond the
degenerate all-zero point.

The third instance (`Rot` section) exercises the deployed `x₄` power form (`Soundness.Multiopen.Deployed`)
on a minimal *rotated-query* deployed instance: one proof, one advice column queried at rotations `0`
and `1` (points `x` and `ωx`), plus the vanishing queries — two point sets, so the fingerprinted
`constructIntermediateSets` grouping is genuinely multi-set and rotated. The `x₄` pair count and the
batch column values are *computed* (`decide`), and `deployedCommitment_x4_batch` instantiates on it.
-/

namespace Zcash.Snark
namespace MultiopenDecodeFixture

open Polynomial

/-- Toy URS at `k = 0` over the scalar field itself: the single generator is `1`. -/
abbrev toyUrs : URS Fp := ⟨0, fun _ => 1, 0, 0⟩

/-- The toy index type is a singleton. -/
theorem toy_fin_eq_zero (j : Fin (2 ^ toyUrs.k)) : j = 0 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ i => exact i.elim0

/-- At `k = 0` with generator `1`, a commitment is its single coefficient: `commit` has trivial
kernel, so the canonical decode is pinned by its spec alone. -/
theorem toy_commit_eq (a : Fin 1 → Fp) : commit toyUrs a = a 0 := by
  simp [commit, toyUrs]

/-- One column, everything zero: the batch family whose decode the fixture checks. -/
noncomputable def toyBatch :
    BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  batched := fun _ _ => 0
  current := 0
  current_eq := rfl
  commitment := fun r => by simp [commit, toyUrs]
  value := fun r => by simp [commitGen]

/-- Any zero-column batch over the toy URS decodes to the zero columns — from the decode's spec and
the trivial kernel, without unfolding the Vandermonde inverse. -/
theorem toy_decode_zero {bvec : Fin 1 → Fp} {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs bvec (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) w) :
    decodedCols hb = fun _ => 0 := by
  funext i
  have hfam := (decodedCols_spec hb).decodedColumns
  have hz : hfam.coeffs i = fun _ => 0 := by
    funext j
    have h0 : hfam.coeffs i 0 = 0 := by
      have hc := hfam.commitment i
      rwa [toy_commit_eq] at hc
    have hj : j = 0 := toy_fin_eq_zero j
    rw [hj]; exact h0
  rw [hfam.polynomial i, hz]
  simp [coeffsToPoly]

/-- The one-gate circuit: read advice column `0`. -/
def toyGates : Fin 1 → Expr Fp := fun _ => Expr.advice 0

/-- The zero witness opens the zero statement over the toy URS. -/
theorem toy_opens :
    IpaRelation toyUrs (0 : Fp) (evalVector 0 (0 : Fp)) (0 : Fp) (fun _ => (0 : Fp)) := by
  constructor
  · simp [commit, toyUrs]
  · simp [innerProduct]

/-- The combined gate numerator over the decoded (zero) columns is the zero polynomial. -/
theorem toy_numerator {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) w) :
    combineGates (fun _ => 0) (selectedPolys (decodedCols hb) (fun i : Fin 1 => i))
      (selectedPolys (decodedCols hb) (fun i : Fin 1 => i)) 0 toyGates = 0 := by
  rw [toy_decode_zero hb]
  simp [combineGates, gatePolys, toyGates, Expr.toPoly, selectedPolys, finFn]

/-- All hypotheses of `decoded_constraint_of_relation_and_batch` discharged concretely: the
regression guard that the decoded hypothesis shapes stay satisfiable. -/
theorem toy_relation_and_batch_discharged : True :=
  decoded_constraint_of_relation_and_batch (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0 toy_opens toyBatch
    (by rw [toy_numerator toyBatch]; simp [quotientCheck])
    (by rw [toy_numerator toyBatch]; simp [szBadSet])
    (fun _ _ _ => trivial)

/-- Accepting transcripts for every batching challenge of the zero batch: the depth-`0` leaf `0`. -/
noncomputable def toyFamily :
    AcceptedBatchFamily toyUrs 0 (evalVector 0 0) 0 (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  trees := fun _ => .leaf 0
  accepts := fun r => ⟨by simp [commitGen], by simp [commitGen]⟩
  current := 0
  current_P := by simp
  current_v := by simp

/-- The opening-or-relation terminal endpoint discharged end-to-end, with `hbatch` *derived* from
accepting transcripts (`multiopenRewindForRelation_of_acceptedFamily toyFamily`), not assumed. -/
theorem toy_terminal_discharged :
    True ∨ HasNontrivialRelation (F := Fp) toyUrs.g toyUrs.u toyUrs.w :=
  decoded_constraint_of_opening_or_relation (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0
    (Or.inl ⟨fun _ => 0, toy_opens⟩)
    (multiopenRewindForRelation_of_acceptedFamily toyFamily)
    (fun a hrel => by rw [toy_numerator]; simp [quotientCheck])
    (fun a hrel => by rw [toy_numerator]; simp [szBadSet])
    (fun _ _ _ => trivial)

/-- The `_xgood` terminal endpoint discharged concretely: no `hgood`-shaped hypothesis is supplied at
all — the good challenge is *derived* from a full-measure accept event (`accX := fun _ => True`,
whose measure `1` beats the toy budget `1 / p`). The regression guard that the
derived-good-challenge hypothesis shapes (`hquot` at every accepting point, the `hprobX` threshold)
stay satisfiable.

`C = 0` here (the identity holds), and that is *forced*, not incidental: any satisfiable `_xgood`
instance has the identity holding as polynomials. If `C ≠ 0`, `hquot` (the gate check at every
accepting point) confines the accept set to the `≤ deg`-element bad set, contradicting `hprobX`
(measure `> deg/p`). So `C = 0` is full coverage — a "nonzero-`C`" `_xgood` fixture cannot exist. -/
theorem toy_xgood_discharged : True :=
  decoded_constraint_of_relation_and_batch_xgood (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 (fun _ => True) toy_opens toyBatch
    (fun xv _ => by rw [toy_numerator toyBatch]; simp [quotientCheck])
    (by
      rw [toy_numerator toyBatch]
      have hmax : max (0 : Polynomial Fp).natDegree ((0 : Polynomial Fp).natDegree + 1) = 1 := by
        simp
      rw [hmax, Finset.filter_true, uniformChallenge_badSet, Finset.card_univ,
        ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
        ENNReal.div_lt_iff (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
      exact_mod_cast Fintype.one_lt_card)
    (fun _ _ _ => trivial)

/-! ## Multi-column, nonzero data

Three columns holding `2`, `3`, `6`, batched at the distinct challenges `0`, `1`, `2`; the gate
`advice 0 · advice 1 − instance 0` reads columns `0`/`1` as advice and column `2` as instance and is
satisfied (`2·3 = 6`) with zero quotient. The same two terminal endpoints are discharged, so the decoded
hypothesis shapes are exercised on genuinely nonzero, multi-column data. -/

/-- Any batch over the toy URS decodes to the constant polynomials pinned by the column commitments:
at `k = 0` the commitment has trivial kernel, so the canonical decode is determined by its spec alone —
for arbitrary targets, generalizing `toy_decode_zero`. -/
theorem toy_decode_pinned {n : ℕ} {bvec : Fin 1 → Fp} {cc ce : Fin n → Fp} {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs bvec cc ce w) :
    decodedCols hb = fun i => Polynomial.C (cc i) := by
  funext i
  have hfam := (decodedCols_spec hb).decodedColumns
  have hcoeff : hfam.coeffs i = fun _ => cc i := by
    funext j
    have h0 : hfam.coeffs i 0 = cc i := by
      have hc := hfam.commitment i
      rwa [toy_commit_eq] at hc
    rw [toy_fin_eq_zero j]
    exact h0
  rw [hfam.polynomial i, hcoeff]
  simp [coeffsToPoly]

/-- The two-advice/one-instance gate `advice 0 · advice 1 − instance 0`. -/
def toyGatesProd : Fin 1 → Expr Fp :=
  fun _ => .sum (.product (.advice 0) (.advice 1)) (.negated (.instance 0))

/-- The nonzero three-column batch: columns `2`, `3`, `6` at batching challenges `0`, `1`, `2`; the
current witness is the challenge-`0` batch, the column-`0` constant `2`. -/
noncomputable def toyBatchProd :
    BatchOpeningsForWitness toyUrs (evalVector 0 0) (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) (fun _ => 2) where
  batchChallenge := ![0, 1, 2]
  challengesDistinct := by decide
  batched := ![fun _ => 2, fun _ => 11, fun _ => 32]
  current := 0
  current_eq := rfl
  commitment := by decide
  value := by decide

/-- The witness `2` opens the statement `(P, v) = (2, 2)` over the toy URS. -/
theorem toyProd_opens :
    IpaRelation toyUrs (2 : Fp) (evalVector 0 (0 : Fp)) (2 : Fp) (fun _ => (2 : Fp)) := by
  constructor <;> decide

/-- The combined gate numerator over the decoded nonzero columns vanishes: `2·3 − 6 = 0`. -/
theorem toyProd_numerator {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs (evalVector 0 0) (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) w) :
    combineGates (fun _ => 0) (selectedPolys (decodedCols hb) ![0, 1])
      (selectedPolys (decodedCols hb) ![2]) 0 toyGatesProd = 0 := by
  rw [toy_decode_pinned hb]
  have h0 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 0 = Polynomial.C 2 := by
    simp [selectedPolys, finFn]
  have h1 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![0, 1] : Fin 2 → Fin 3) 1 = Polynomial.C 3 := by
    simp [selectedPolys, finFn]
  have h2 : selectedPolys (fun i => Polynomial.C ((![2, 3, 6] : Fin 3 → Fp) i))
      (![2] : Fin 1 → Fin 3) 0 = Polynomial.C 6 := by
    simp [selectedPolys, finFn]
  simp only [combineGates, gatePolys, toyGatesProd, List.ofFn_succ, List.ofFn_zero,
    List.foldl_cons, List.foldl_nil, Expr.toPoly, h0, h1, h2, zero_mul, zero_add]
  simp only [← Polynomial.C_mul, ← Polynomial.C_neg, ← Polynomial.C_add, Polynomial.C_eq_zero]
  norm_num

/-- `decoded_constraint_of_relation_and_batch` discharged concretely on the nonzero multi-column
batch. -/
theorem toyProd_relation_and_batch_discharged : True :=
  decoded_constraint_of_relation_and_batch (urs := toyUrs)
    (![2, 3, 6] : Fin 3 → Fp) (![2, 3, 6] : Fin 3 → Fp) ![0, 1] ![2]
    (fun _ => 0) 0 toyGatesProd 0 1 0 toyProd_opens toyBatchProd
    (by rw [toyProd_numerator toyBatchProd]; simp [quotientCheck])
    (by rw [toyProd_numerator toyBatchProd]; simp [szBadSet])
    (fun _ _ _ => trivial)

/-- Accepting leaf transcripts for the three batching challenges of the nonzero batch: the depth-`0`
leaves carry the batched constants `2`, `11`, `32`. -/
noncomputable def toyFamilyProd :
    AcceptedBatchFamily toyUrs 2 (evalVector 0 0) 2 (![2, 3, 6] : Fin 3 → Fp)
      (![2, 3, 6] : Fin 3 → Fp) where
  batchChallenge := ![0, 1, 2]
  challengesDistinct := by decide
  trees := ![.leaf 2, .leaf 11, .leaf 32]
  accepts := by
    intro r
    fin_cases r <;> exact ⟨by decide, by decide⟩
  current := 0
  current_P := by decide
  current_v := by decide

/-- The opening-or-relation terminal endpoint discharged end-to-end on nonzero multi-column data, with
`hbatch` *derived* from the accepting transcripts. -/
theorem toyProd_terminal_discharged :
    True ∨ HasNontrivialRelation (F := Fp) toyUrs.g toyUrs.u toyUrs.w :=
  decoded_constraint_of_opening_or_relation (urs := toyUrs)
    (![2, 3, 6] : Fin 3 → Fp) (![2, 3, 6] : Fin 3 → Fp) ![0, 1] ![2]
    (fun _ => 0) 0 toyGatesProd 0 1 0
    (Or.inl ⟨fun _ => 2, toyProd_opens⟩)
    (multiopenRewindForRelation_of_acceptedFamily toyFamilyProd)
    (fun a hrel => by rw [toyProd_numerator]; simp [quotientCheck])
    (fun a hrel => by rw [toyProd_numerator]; simp [szBadSet])
    (fun _ _ _ => trivial)

/-! ## The deployed `x₄` power form on a rotated two-set instance

A minimal deployed instance whose fingerprinted grouping is genuinely multi-set and rotated: one proof
with one advice column queried at rotations `0` and `1` (points `x = 2` and `ωx = 6`), plus the two
vanishing queries at `x`. `constructIntermediateSets` derives two point sets — `{x, ωx}` for the advice
column and `{x}` for the vanishing pair — so the `x₄` collapse has two `(qᵢ, uᵢ)` pairs and the batch
three columns: the `{x}` aggregate (`random + x₁·h`, evaluating to `7`), the `{x, ωx}` aggregate (the
advice commitment `10`), and the quotient commitment `q′ = 5` on top. The counts and values are
*computed* (`decide`), and the power-form theorem instantiates — exercising
`Soundness.Multiopen.Deployed` against a rotated deployed grouping. -/

/-- Shape of the rotated toy: `k = 0`, one proof, one advice column with two advice queries, no
lookups/permutations/quotient pieces, two point sets. -/
def rotShape : Shape :=
  { k := 0, numProofs := 1, numAdviceColumns := 1, numLookups := 0, numPermutationSets := 0,
    numPermutationColumns := 0, numQuotientPieces := 0, numInstanceQueries := 0,
    numAdviceQueries := 2, numFixedQueries := 0, numPointSets := 2 }

/-- Verifying key of the rotated toy: domain generator `ω = 3`, the advice column queried at rotations
`0` and `1`, everything else empty. -/
def rotVk : VerifyingKey rotShape Fp Fp :=
  { omega := 3, n := 1, blindingFactors := 0, delta := 1, chunkLen := 1, gates := [],
    instanceQueryLayout := [], adviceQueryLayout := [(0, 0), (0, 1)], fixedQueryLayout := [],
    fixedCommitment := fun _ => 0, instanceCommitment := fun _ _ => 0,
    permutationCommonCommitment := Fin.elim0, permutationChunks := [],
    lookupInputExprs := Fin.elim0, lookupTableExprs := Fin.elim0 }

/-- Proof string of the rotated toy: advice commitment `10` (opened at both rotations, evals `11`/`12`),
vanishing random commitment `7` (eval `13`), quotient commitment `q′ = 5`, claimed set evaluations
`u = (4, 8)`. -/
def rotPs : ProofString rotShape Fp Fp :=
  { adviceCommitments := fun _ _ => 10, lookupPermutedInput := fun _ => Fin.elim0,
    lookupPermutedTable := fun _ => Fin.elim0, permutationProduct := fun _ => Fin.elim0,
    lookupProduct := fun _ => Fin.elim0, vanishingRandom := 7, hPieces := Fin.elim0,
    instanceEvals := fun _ => Fin.elim0, adviceEvals := fun _ => ![11, 12],
    fixedEvals := Fin.elim0, vanishingRandomEval := 13, permutationCommonEvals := Fin.elim0,
    permutationSetEvals := fun _ => Fin.elim0, lookupEvals := fun _ => Fin.elim0,
    multiopenQPrime := 5, multiopenU := ![4, 8], ipaS := 0, ipaRounds := Fin.elim0,
    ipaC := 0, ipaF := 0 }

/-- Challenges of the rotated toy: gate point `x = 2` (so the rotated advice point is `ωx = 6`),
compression challenge `x₁ = 3`. -/
def rotCh : Challenges rotShape.k Fp :=
  { theta := 0, beta := 0, gamma := 0, y := 0, x := 2, x1 := 3, x2 := 0, x3 := 0, x4 := 9,
    xi := 0, z := 0, ipaRound := Fin.elim0 }

/-- The fingerprinted grouping of the rotated toy has two point sets, so the `x₄` collapse has two
`(qᵢ, uᵢ)` pairs — the count is *computed* from `constructIntermediateSets`. -/
theorem rot_pairCount : deployedX4PairCount rotVk rotPs rotCh = 2 := by decide

/-- The `x₄` batch columns of the rotated toy, computed: power `ξ⁰` carries the `{x}` point-set
aggregate (`random 7 + x₁ · h`, with `h` the empty-piece zero MSM), power `ξ¹` the rotated advice
aggregate (`10`), and the top power the quotient commitment `q′ = 5`. -/
theorem rot_x4BatchCommitments :
    x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨0, by decide⟩ = 7
      ∧ x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨1, by decide⟩ = 10
      ∧ x4BatchCommitments toyUrs rfl rotVk rotPs rotCh ⟨2, by decide⟩ = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `x₄` batch evaluations on the `u` slots, computed: the claimed set evaluations in reverse fold
order. -/
theorem rot_x4BatchEvals :
    x4BatchEvals (G := Fp) rotVk rotPs rotCh ⟨0, by decide⟩ = 8
      ∧ x4BatchEvals (G := Fp) rotVk rotPs rotCh ⟨1, by decide⟩ = 4 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The deployed `x₄` power form instantiated on the rotated two-set instance: the pinned deployed
commitment over the rewound runs `{rotCh with x4 := ξ}` is the `ξ`-power batch of the computed
aggregates. -/
theorem rot_deployed_x4_batch (ξ : Fp) :
    deployedCommitment (G := Fp) toyUrs rfl rotVk rotPs {rotCh with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount rotVk rotPs rotCh + 1),
          ξ ^ (j : ℕ) • x4BatchCommitments toyUrs rfl rotVk rotPs rotCh j :=
  deployedCommitment_x4_batch toyUrs rfl rotVk rotPs rotCh ξ

end MultiopenDecodeFixture
end Zcash.Snark

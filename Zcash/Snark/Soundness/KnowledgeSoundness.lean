import Mathlib
import Zcash.Snark.Soundness.InnerProduct
import Zcash.Snark.Soundness.Extraction
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.CommitFold

/-!
# Knowledge-soundness relation

`SnarkRelation` requires one witness to open the IPA commitment and satisfy the circuit. This file
contains the legacy conditional composition and the Schwartz–Zippel error; the computed
Fiat–Shamir/AGM reduction is in `Forking.Adversary.Algebraic`.

The boundary is explicit: DL-relation hardness, an ideal random oracle for Blake2b and challenge
conversion (and, on the generator-RO endpoints, for the hash-to-curve URS derivation),
CompElliptic's Vesta point-count axiom, and correctness of the supplied verifying key.
The computed reduction models oracle queries, reprogramming, and query loss.

Efficiency counts black-box calls and still lacks a field-independent polynomial AFK bound in `Q`
and `2^k`. The fallback is `(2·|F|+1)^k`; adversary PPT time remains external.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Decode gap (closed by the multiopen decode layer): the two conjuncts of `SnarkRelation` share
-- only the symbol `a`, so a free decode function feeding `circuitSatViaGates` could be instantiated
-- independently of `a` and `circuitSat a` would not constrain the extracted witness. The deployed
-- capstones close this by stating `circuitSat` at the canonical decode of the extracted witness —
-- the rewound-opening decode chain of `Soundness.Multiopen.Decode` (the `batch_open_soundV`-shaped
-- premises carried by `OpenedBatchOpenings`, unbatched to member columns by
-- `openedMemberDecode_of_x1Prob`), consumed by
-- `Soundness.Vesta.orchard_verifier_vesta_member_constraint_derived`.
/-- A witness that both opens the IPA commitment and satisfies the circuit predicate. -/
structure SnarkRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (a : Fin (2 ^ urs.k) → Fp) : Prop where
  opens : IpaRelation urs P b v a
  satisfiesCircuit : circuitSat a

/-- Circuit satisfaction through decoded columns and the combined-gate quotient identity. -/
def circuitSatViaGates {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) : Prop :=
  combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates = hpoly * (X ^ deg - 1)

/-- Derive circuit satisfaction from an accepting quotient check at a good challenge. -/
theorem circuitSatViaGates_of_check {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) (x : Fp)
    (hcheck : quotientCheck
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0) :
    circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
  constraint_identity_of_accept _ hpoly deg x hcheck hgood

/-- **Circuit satisfaction through the full constraint list.** `circuitSatViaGates` asks only that
the gate combination is the quotient's multiple. This asks it of the whole list — gates, permutation
argument and lookup argument — so a witness satisfying it satisfies the constraint system the
verifier actually checks, not just its gate part. -/
def circuitSatViaConstraints {k np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : Polynomial Fp)
    (deg : ℕ) (a : Fin (2 ^ k) → Fp) : Prop :=
  combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks lookups
    beta gamma delta theta y chunkLen l0 lLast lBlind = hpoly * (X ^ deg - 1)

/-- Derive constraint-system satisfaction from an accepting quotient check at a good challenge —
`circuitSatViaGates_of_check` with the permutation and lookup arguments folded in. -/
theorem circuitSatViaConstraints_of_check {k np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : Polynomial Fp)
    (deg : ℕ) (a : Fin (2 ^ k) → Fp) (x : Fp)
    (hcheck : quotientCheck (combineConstraints fixedCols (decodeAdvice a) (decodeInstance a)
      gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind) hpoly deg x)
    (hgood : combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks
        lookups beta gamma delta theta y chunkLen l0 lLast lBlind ≠ hpoly * (X ^ deg - 1) →
      (combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind - hpoly * (X ^ deg - 1)).eval x ≠ 0) :
    circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates sets chunks lookups
      beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg a :=
  constraint_identity_of_accept _ hpoly deg x hcheck hgood

/-- **The capstone payload over the full constraint system.** An IPA opening together with the
constraint identity *is* `SnarkRelation` at `circuitSatViaConstraints`. This is the projection the
deployed path needs: the same opening it already computes, paired with satisfaction of the gate,
permutation and lookup constraints rather than of the gates alone. -/
theorem snarkRelation_constraints {np : ℕ} (urs : URS G) {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → Fin np → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : Polynomial Fp)
    (deg : ℕ) {a : Fin (2 ^ urs.k) → Fp}
    (hopen : IpaRelation urs P b v a)
    (hsat : combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks
      lookups beta gamma delta theta y chunkLen l0 lLast lBlind = hpoly * (X ^ deg - 1)) :
    SnarkRelation urs P b v (circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates
      sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg) a :=
  ⟨hopen, hsat⟩

/-- A consistent tree, opening, and circuit witness yield the extracted SNARK relation. -/
theorem knowledge_sound (urs : URS G)
    {t : Tree Fp urs.k} {a : Fin (2 ^ urs.k) → Fp} (hcons : Consistent t a)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} (hopen : IpaRelation urs P b v a)
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hsat : circuitSat a) :
    extract t = a ∧ SnarkRelation urs P b v circuitSat a :=
  ⟨extract_correct t a hcons, ⟨hopen, hsat⟩⟩

/-- Schwartz–Zippel error for an invalid quotient identity. -/
theorem soundness_error (numerator h : Polynomial Fp) (n : ℕ) (hne : numerator ≠ h * (X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) :=
  quotientCheck_sound numerator h n hne

end Zcash.Snark

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Zcash.Snark.Soundness.Constraint.Constraints
import Zcash.Snark.Soundness.Ipa.CommitFold

/-!
# Knowledge-soundness relation

`SnarkRelation` requires one witness to open the IPA commitment and satisfy the circuit. This file
carries that relation and the full constraint-list satisfaction predicate; the
computed Fiat–Shamir/AGM reduction is in `FiatShamir.Adversary.Algebraic`.

The boundary is explicit: DL-relation hardness, an ideal random oracle for Blake2b and challenge
conversion (and, on the generator-RO endpoints, for the hash-to-curve URS derivation),
CompElliptic's Vesta point-count axiom, and correctness of the supplied verifying key.
The computed reduction models oracle queries, represented output, and query loss.

Efficiency counts black-box calls.  The deployed combined finder has a pointwise four-invocation
bound, so no expectation, truncation budget, or Markov tail enters the accounting.  Adversary PPT
time and the concrete DLOG hardness bound remain external.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open CompPoly.CPolynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Decode gap (closed by the multiopen decode layer): the two conjuncts of `SnarkRelation` share
-- only the symbol `a`, so a free decode function feeding `circuitSatViaConstraints` could be instantiated
-- independently of `a` and `circuitSat a` would not constrain the extracted witness. The deployed
-- capstones close this by stating `circuitSat` at the canonical decode of the extracted witness —
-- the opened AGM decode chain carried by `OpenedBatchOpenings`, unbatched to member columns by
-- `DeployedAlgebraicDecode.toMemberDecode`, consumed by the canonical and Action terminals.
/-- A witness that both opens the IPA commitment and satisfies the circuit predicate. -/
structure SnarkRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (a : Fin (2 ^ urs.k) → Fp) : Prop where
  opens : IpaRelation urs P b v a
  satisfiesCircuit : circuitSat a

/-- **The verifier's compressed identity over the full constraint list.** This predicate folds gates,
permutation rules, and lookup rules with the sampled `y`, `beta`, `gamma`, and `theta` challenges.
It is the algebraic identity checked by the verifier, not by itself the row-level semantic
statement: splitting the `y` fold and recovering permutation/lookup semantics additionally require
the good-challenge hypotheses in `ConstraintRelations`. -/
def circuitSatViaConstraints {k np : ℕ} (fixedCols : ℕ → CPoly)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → Fin np → ℕ → CPoly)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : CPoly)
    (deg : ℕ) (a : Fin (2 ^ k) → Fp) : Prop :=
  combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks lookups
    beta gamma delta theta y chunkLen l0 lLast lBlind = hpoly * (X ^ deg - 1)

/-- Derive the compressed full-list identity from an accepting quotient check at a good `x`. -/
theorem circuitSatViaConstraints_of_check {k np : ℕ} (fixedCols : ℕ → CPoly)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → Fin np → ℕ → CPoly)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : CPoly)
    (deg : ℕ) (a : Fin (2 ^ k) → Fp) (x : Fp)
    (hcheck : quotientCheck (combineConstraints fixedCols (decodeAdvice a) (decodeInstance a)
      gates sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind) hpoly deg x)
    (hgood : combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks
        lookups beta gamma delta theta y chunkLen l0 lLast lBlind ≠ hpoly * (X ^ deg - 1) →
      (combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks
        lookups beta gamma delta theta y chunkLen l0 lLast lBlind
          - hpoly * (X ^ deg - 1)).eval x ≠ 0) :
    circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates sets chunks lookups
      beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg a :=
  constraint_identity_of_accept _ hpoly deg x hcheck hgood

/-- **The capstone payload for the compressed full-list identity.** An IPA opening together with
the verifier's constraint identity is `SnarkRelation` at `circuitSatViaConstraints`. Promoting this
payload to row-level gate, permutation, and lookup semantics must separately price the `y`, `beta`,
`gamma`, and `theta` failure surfaces; see `ConstraintRelations` and the semantic capstone in
`Composition.DeployedConstraintContainment`. -/
theorem snarkRelation_constraints {np : ℕ} (urs : URS G) {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → CPoly)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → Fin np → ℕ → CPoly)
    (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (CPoly)))
    (chunks : Fin np →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind hpoly : CPoly)
    (deg : ℕ) {a : Fin (2 ^ urs.k) → Fp}
    (hopen : IpaRelation urs P b v a)
    (hsat : combineConstraints fixedCols (decodeAdvice a) (decodeInstance a) gates sets chunks
      lookups beta gamma delta theta y chunkLen l0 lLast lBlind = hpoly * (X ^ deg - 1)) :
    SnarkRelation urs P b v (circuitSatViaConstraints fixedCols decodeAdvice decodeInstance gates
      sets chunks lookups beta gamma delta theta y chunkLen l0 lLast lBlind hpoly deg) a :=
  ⟨hopen, hsat⟩

/-- Schwartz–Zippel error for an invalid quotient identity. -/
theorem soundness_error (numerator h : CPoly) (n : ℕ) (hne : numerator ≠ h * (X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) :=
  quotientCheck_sound numerator h n hne

end Zcash.Snark

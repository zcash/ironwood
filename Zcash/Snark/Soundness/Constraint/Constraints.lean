import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Arithmetic
import Zcash.Common.CPolynomial
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Assemble

/-!
# The constraint layer: Schwartz–Zippel soundness of the vanishing check

The verifier's vanishing argument checks the quotient identity at the random evaluation point `x`: the
claimed quotient `h` satisfies `numerator = h · (Xⁿ − 1)`, where `numerator` is the gate / permutation /
lookup combination (the constraints combined by the challenge `y`, as assembled into `expected_h_eval`).
This module proves the soundness of that check by univariate Schwartz–Zippel (root counting): the
verifier samples one challenge, so the relevant bound is the number of roots of the constraint
polynomial.

* `quotientCheck` — the verifier's check at `x`: `numerator(x) = h(x) · (xⁿ − 1)`.
* `quotientCheck_sound` — if the identity fails as polynomials (the committed polynomials violate the
  constraint system), the check passes for at most `deg / |F|` of the challenges.
* `quotientCheck_complete` — if it holds as polynomials, the check passes at every challenge.

`numerator` and `h` are the polynomials carried by the proof. The sections below make the connection
to the assembly concrete: `Expr.toPoly` lifts the Orchard gate `Expr`s to polynomials and
`combineGates` assembles them into the actual `numerator` — so the root-counting bound applies to the
verifier's real gate check.

Two algebraic builders appear below. `combineGates` folds just the custom-gate portion of
`numerator` and supports local evaluation lemmas. The deployed path (`combineConstraints` /
`circuitSatViaConstraints`) folds
the permutation and lookup constraint values in too — the same list the verifier's `expected_h_eval`
combines — and those terms *are* connected to the circuit-level copy and lookup constraints: the
row-level results carry them to the combinatorial relations, which `ConstraintRelations` reads back out
of the predicate (the copy-constraint equalities and the lookup inclusion). So "circuit satisfaction"
on the full path covers gates, the permutation argument, and the lookup argument.

## Representation

Polynomials here are `Zcash.CPoly = CompPoly.CPolynomial Fp`: canonical coefficient arrays with an
executable `CommRing` and a proven ring isomorphism to Mathlib's `Polynomial Fp`
(`CPolynomial.ringEquiv`).  `allConstraints` is ring-generic, so one instantiation serves as both
the specification and the executable assembly, and nothing in this file is `noncomputable`.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open CompPoly CompPoly.CPolynomial Finset

/-- The verifier's vanishing/quotient check at the challenge `x`: the claimed quotient `h` satisfies the
constraint identity `numerator(x) = h(x) · (xⁿ − 1)`. `numerator` is the gate/permutation/lookup
combination; the verifier opens `h` to `numerator(x) / (xⁿ − 1)`. -/
@[reducible] def quotientCheck (numerator h : CPoly) (n : ℕ) (x : Fp) : Prop :=
  numerator.eval x = h.eval x * (x ^ n - 1)

/-! ## The Schwartz–Zippel bad set -/

/-- The Schwartz–Zippel bad set of a use site: the roots of the difference polynomial `C`. A
challenge is *good* for `C` when it avoids this set — for `C = 0` (the identity holds as
polynomials) nothing is excluded, and otherwise exactly the `≤ natDegree C` roots are. -/
def szBadSet (C : CPoly) : Finset Fp := roots C

/-- Membership in the bad set: `x` is bad for `C` exactly when the identity fails (`C ≠ 0`) and `x`
fails to witness it (`C.eval x = 0`). -/
theorem mem_szBadSet {C : CPoly} {x : Fp} :
    x ∈ szBadSet C ↔ C ≠ 0 ∧ C.eval x = 0 := by
  rw [szBadSet]
  constructor
  · intro h
    have hC : C ≠ 0 := by
      intro h0
      rw [h0, roots_zero] at h
      simp at h
    exact ⟨hC, (mem_roots hC).mp h⟩
  · rintro ⟨hC, hx⟩
    exact (mem_roots hC).mpr hx

/-- **The good-challenge condition, derived from bad-set avoidance.** `x ∉ szBadSet C` is exactly
the `hgood` shape the constraint layer consumes: if the identity fails as polynomials, the
challenge evaluation does not vanish. -/
theorem not_mem_szBadSet {C : CPoly} {x : Fp} :
    x ∉ szBadSet C ↔ (C ≠ 0 → C.eval x ≠ 0) := by
  rw [mem_szBadSet, not_and]

/-- Bad-set membership is decidable without ever forming the root set: `C = 0` is decidable because
the representation is canonical, and the other conjunct is one evaluation. -/
instance decidableMemSzBadSet (C : CPoly) (x : Fp) : Decidable (x ∈ szBadSet C) :=
  decidable_of_iff _ mem_szBadSet.symm

/-- Compute avoidance of one Schwartz–Zippel bad set without computing the root set itself.
The branch decision uses only polynomial equality and evaluation at the sampled point; the
equivalence with `x ∉ szBadSet C` is retained in the erased proof returned on success.  This is
the executable form reductions should use when a successful branch returns break data. -/
def szBadSetAvoidance? (C : CPoly) (x : Fp) :
    Option (PLift (x ∉ szBadSet C)) :=
  if hzero : C = 0 then
    some ⟨not_mem_szBadSet.mpr fun hne => absurd hzero hne⟩
  else if heval : C.eval x = 0 then
    none
  else
    some ⟨not_mem_szBadSet.mpr fun _ => heval⟩

/-- The computed point test succeeds exactly outside the specification-level root set. -/
theorem szBadSetAvoidance?_isSome_iff (C : CPoly) (x : Fp) :
    (szBadSetAvoidance? C x).isSome ↔ x ∉ szBadSet C := by
  unfold szBadSetAvoidance?
  split <;> rename_i hzero
  · simp [not_mem_szBadSet, hzero]
  · split <;> rename_i heval <;> simp [not_mem_szBadSet, hzero, heval]

/-- **Root counting: the bad set is small.** One Schwartz–Zippel use site over `F_p` excludes at
most `natDegree C` challenges — the `d` of the `d / p` budget (`uniformChallenge_szBadSet` in
`Zcash.Snark.Soundness.Pricing.GoodChallenge`). -/
theorem szBadSet_card_le (C : CPoly) : (szBadSet C).card ≤ C.natDegree :=
  card_roots_le C

/-- The concrete degree bound at the vanishing-check site: the bad set of the constraint difference
`numerator − h · (Xⁿ − 1)` has at most `max (deg numerator) (deg h + n)` elements — the explicit
`d` for the quotient identity's Schwartz–Zippel use. -/
theorem szBadSet_quotient_card_le (numerator h : CPoly) (n : ℕ) :
    (szBadSet (numerator - h * (X ^ n - 1))).card
      ≤ max numerator.natDegree (h.natDegree + n) := by
  refine (szBadSet_card_le _).trans ((natDegree_sub_le _ _).trans ?_)
  refine max_le_max le_rfl (natDegree_mul_le.trans (Nat.add_le_add_left ?_ _))
  exact (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le n) (by simp))

/-! ## The quotient check -/

/-- When the identity fails, the accepting challenges are exactly the bad set: the verifier's check
passes at `x` iff `x` is a root of the constraint difference. This is the set `quotientCheck_sound`
counts and `Zcash.Snark.Soundness.Pricing.GoodChallenge` measures. -/
theorem quotientCheck_filter_eq_szBadSet (numerator h : CPoly) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    (univ.filter fun x => quotientCheck numerator h n x)
      = szBadSet (numerator - h * (X ^ n - 1)) := by
  have hC : numerator - h * (X ^ n - 1) ≠ 0 := sub_ne_zero.mpr hne
  ext x
  simp [mem_szBadSet, hC, quotientCheck, sub_eq_zero]

/-- **Constraint soundness (Schwartz–Zippel, univariate).** If the quotient identity fails as
polynomials — `numerator ≠ h · (Xⁿ − 1)`, i.e. the committed polynomials violate the constraint
system — then the verifier's check passes for at most a `deg / |F|` fraction of the challenges. So a
violated constraint system is accepted with probability `≤ d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem quotientCheck_sound (numerator h : CPoly) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    ((univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0) / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) := by
  rw [quotientCheck_filter_eq_szBadSet numerator h n hne]
  gcongr
  exact_mod_cast szBadSet_card_le _

/-- Completeness, the companion to `quotientCheck_sound`: if the quotient identity holds as
polynomials, the verifier's check passes at every challenge. -/
theorem quotientCheck_complete (numerator h : CPoly) (n : ℕ)
    (heq : numerator = h * (X ^ n - 1)) (x : Fp) : quotientCheck numerator h n x := by
  simp [quotientCheck, heq]

/-- **The constraint identity, derived from acceptance (not assumed).** If the verifier's
quotient check passes at `x` and `x` is not a root of the constraint difference (the "good
challenge" event; its complement is the `≤ deg/p` bad set bounded by `quotientCheck_sound`),
then the identity holds as polynomials. This is the contrapositive that puts
`quotientCheck_sound` on the soundness path. -/
theorem constraint_identity_of_accept (numerator h : CPoly) (n : ℕ) (x : Fp)
    (hcheck : quotientCheck numerator h n x)
    (hgood : numerator ≠ h * (X ^ n - 1) → (numerator - h * (X ^ n - 1)).eval x ≠ 0) :
    numerator = h * (X ^ n - 1) := by
  by_contra hne
  apply hgood hne
  simp only [quotientCheck] at hcheck
  simp [hcheck]

/-- **From the point check to the polynomial identity, with a relation branch.** The derived fold
equations end in a disjunction — the equation, or a nontrivial group relation — and the
good-challenge premise turns the equation half into the identity the constraint layer needs. This is
`constraint_identity_of_accept` shaped for those callers. -/
theorem constraint_identity_of_hfold {numerator hpoly : CPoly} {n : ℕ} {x : Fp} {R : Prop}
    (hfold : numerator.eval x = hpoly.eval x * (x ^ n - 1) ∨ R)
    (hgood : numerator ≠ hpoly * (X ^ n - 1) → (numerator - hpoly * (X ^ n - 1)).eval x ≠ 0) :
    numerator = hpoly * (X ^ n - 1) ∨ R := by
  rcases hfold with h | hr
  · exact Or.inl (constraint_identity_of_accept numerator hpoly n x h hgood)
  · exact Or.inr hr

/-! ## Rotated column polynomials

halo2 opens a query `(column, rotation)` at the rotated point `rotate_omega x rot = ω^rot · x`
(`plonk/verifier.rs`), and its gate evaluator reads the claimed evaluation there. Feeding the
verifier's gate check the *rotated* column polynomial `comp col (C (ω^rot) · X)` reproduces exactly
that: its value at the gate point `x` is `col (ω^rot · x)` — the claimed evaluation the query binds.
The degree is unchanged (the rotation is an invertible rescaling of `X`), so the Schwartz–Zippel
degree bounds for the quotient check carry over. -/

/-- Rotating the argument by an invertible factor `w`: `(col ∘ (w·X))(x) = col (w·x)`. So the rotated
column, evaluated at the gate point `x`, is the column's value at the rotated point `ω^rot · x`. -/
theorem eval_comp_rotate (col : CPoly) (w x : Fp) :
    (comp col (C w * X)).eval x = col.eval (w * x) :=
  eval_comp_C_mul_X col w x

/-- Rotation by a nonzero factor preserves degree (it rescales `X`), so the quotient-check degree
bounds are unchanged by feeding rotated columns. -/
theorem natDegree_comp_rotate (col : CPoly) {w : Fp} (hw : w ≠ 0) :
    (comp col (C w * X)).natDegree = col.natDegree :=
  natDegree_comp_C_mul_X col hw

/-! ## Lifting gate expressions to polynomials

The verifier evaluates each gate `Expr` at the claimed evaluations — the committed column
polynomials at `x`. `Expr.toPoly` lifts a gate to the corresponding univariate polynomial, and
`Expr.eval_toPoly` shows the lift commutes with evaluation. So the verifier's assembled gate
value is a polynomial evaluation — the `numerator` of `quotientCheck` — connecting
`quotientCheck_sound` to the actual Orchard gates. -/

/-- Lift a gate `Expr` to a univariate polynomial, replacing each query with its column polynomial. -/
def Expr.toPoly (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    Expr Fp → CPoly
  | .constant c => C c
  | .fixed i => fixedCols i
  | .advice i => adviceCols i
  | .instance i => instanceCols i
  | .negated a => -(Expr.toPoly fixedCols adviceCols instanceCols a)
  | .sum a b => Expr.toPoly fixedCols adviceCols instanceCols a
      + Expr.toPoly fixedCols adviceCols instanceCols b
  | .product a b => Expr.toPoly fixedCols adviceCols instanceCols a
      * Expr.toPoly fixedCols adviceCols instanceCols b
  | .scaled a c => Expr.toPoly fixedCols adviceCols instanceCols a * C c

/-- The lift commutes with evaluation: the gate polynomial at `x` equals the gate evaluated at the
columns' values at `x` — i.e. the verifier's gate evaluation is a polynomial evaluation. -/
theorem Expr.eval_toPoly (fixedCols adviceCols instanceCols : ℕ → CPoly) (x : Fp)
    (e : Expr Fp) :
    CPolynomial.eval x (Expr.toPoly fixedCols adviceCols instanceCols e)
      = Expr.eval (fun i => CPolynomial.eval x (fixedCols i))
          (fun i => CPolynomial.eval x (adviceCols i))
          (fun i => CPolynomial.eval x (instanceCols i)) e := by
  induction e <;> simp_all [Expr.toPoly, Expr.eval]

/-! ## Combining the gates into the constraint numerator

The verifier combines all gate constraints by the challenge `y` into the single `numerator` of the
quotient identity (the `expected_h_eval` it compares against `h(x)·(xⁿ−1)`). Halo2 folds in list order as
`acc * y + v`; `combineGates` mirrors that order, and `eval_combineGates` shows evaluation commutes with
that fold — so the assembled `numerator` is a polynomial in the column polynomials, whose root count is
what `quotientCheck_sound` bounds. -/

/-- Evaluation commutes with Halo2's `acc * y + v` fold. -/
theorem eval_foldByY (y x : Fp) (acc : CPoly) (ps : List CPoly) :
    (ps.foldl (fun acc p => acc * C y + p) acc).eval x
      = (ps.map (fun p => p.eval x)).foldl (fun acc v => acc * y + v) (acc.eval x) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simpa using ih (acc * C y + p)

/-- The gate expressions lifted to polynomials, in verifier order. -/
def gatePolys {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (gates : Fin n → Expr Fp) : List CPoly :=
  List.ofFn (fun i : Fin n => Expr.toPoly fixedCols adviceCols instanceCols (gates i))

/-- The constraint `numerator`: the gate polynomials (`Expr.toPoly`) combined by the same
`acc * y + v` fold that halo2 uses in `vanishing/verifier.rs`. -/
def combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (y : Fp) (gates : Fin n → Expr Fp) : CPoly :=
  (gatePolys fixedCols adviceCols instanceCols gates).foldl (fun acc p => acc * C y + p) 0

/-- The combined numerator is the Halo2-order `y` fold of the gate evaluations: the verifier's
assembled gate value at `x` is `(combineGates …).eval x`, a single polynomial evaluation. -/
theorem eval_combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (y : Fp) (gates : Fin n → Expr Fp) (x : Fp) :
    (combineGates fixedCols adviceCols instanceCols y gates).eval x
      = ((gatePolys fixedCols adviceCols instanceCols gates).map (fun p => p.eval x)).foldl
          (fun acc v => acc * y + v) 0 := by
  simp [combineGates, eval_foldByY]

/-! ## The permutation and lookup arguments at the polynomial level

`combineGates` folds only the custom gates. The verifier's `expected_h_eval` folds the permutation
and lookup constraint values too, so the polynomial the quotient check is really about is the fold of
*all* the constraints. `constraintPolys` builds that list one level up — the same `allConstraints`
the verifier uses, but over column polynomials instead of claimed values — and `eval_constraintPolys`
says evaluating at `x` lands back on the verifier's own list. -/

/-- Every constraint value across the sub-proofs, as polynomials. The gates and lookup expressions
carry scalar constants, so they are lifted with `C`; the gate point becomes `X`, since evaluating the
result at `x` has to give `x` back.

`allConstraints` is ring-generic, so this instantiation runs on `CPolynomial Fp`'s own executable
`CommRing`; it is both the specification and the implementation. -/
def constraintPolys {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) :
    List CPoly :=
  allConstraints fixedCols adviceCols instanceCols (gates.map (Expr.map C)) sets chunks
    (fun p => (lookups p).map (fun lk =>
      (lk.1, lk.2.1.map (Expr.map C), lk.2.2.map (Expr.map C))))
    (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind

/-- Evaluating the polynomial constraints at `x` gives the verifier's constraint values at the
columns' values at `x`. -/
theorem eval_constraintPolys {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) (x : Fp) :
    (constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind).map (fun q => q.eval x)
      = allConstraints (fun i => (fixedCols i).eval x) (fun p i => (adviceCols p i).eval x)
          (fun p i => (instanceCols p i).eval x) gates
          (fun p => (sets p).map (PermSetEval.map (fun q => q.eval x)))
          (fun p => (chunks p).map (fun c => (c.1.map (fun q => q.eval x),
            c.2.map (fun q => (q.1.eval x, q.2.eval x)))))
          (fun p => (lookups p).map (fun lk => (lk.1.map (fun q => q.eval x), lk.2.1, lk.2.2)))
          beta gamma x delta theta chunkLen (l0.eval x) (lLast.eval x) (lBlind.eval x) := by
  have hmap : (fun q : CPoly => q.eval x) = ⇑(evalRingHom x) := rfl
  rw [constraintPolys, hmap, allConstraints_map (evalRingHom x)]
  simp [List.map_map, Function.comp_def, Expr.map_map, Expr.map_id, PermSetEval.map,
    LookupEval.map]

/-- The constraint numerator with the permutation and lookup arguments folded in: the same `acc·y + v`
order `combineGates` uses, over the full constraint list. -/
def combineConstraints {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) :
    CPoly :=
  (constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
    beta gamma delta theta chunkLen l0 lLast lBlind).foldl (fun acc q => acc * C y + q) 0

/-- The numerator at `x` is the `y` fold of the verifier's own constraint values. -/
theorem eval_combineConstraints {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) (x : Fp) :
    (combineConstraints fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta y chunkLen l0 lLast lBlind).eval x
      = (allConstraints (fun i => (fixedCols i).eval x) (fun p i => (adviceCols p i).eval x)
          (fun p i => (instanceCols p i).eval x) gates
          (fun p => (sets p).map (PermSetEval.map (fun q => q.eval x)))
          (fun p => (chunks p).map (fun c => (c.1.map (fun q => q.eval x),
            c.2.map (fun q => (q.1.eval x, q.2.eval x)))))
          (fun p => (lookups p).map (fun lk => (lk.1.map (fun q => q.eval x), lk.2.1, lk.2.2)))
          beta gamma x delta theta chunkLen (l0.eval x) (lLast.eval x) (lBlind.eval x)).foldl
          (fun acc v => acc * y + v) 0 := by
  rw [combineConstraints, eval_foldByY, eval_constraintPolys]
  simp

/-! ## Reading individual constraints off the assembled list -/

/-- A permutation constraint of one sub-proof is one of the polynomial constraints. This is what
lets a fact proved about the whole list — every constraint vanishes on the domain — be read off for
a single rule. -/
theorem mem_constraintPolys_of_mem_permutationExpressions {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly)
    (p : Fin np) {v : CPoly}
    (h : v ∈ permutationExpressions (sets p) (chunks p) (C beta) (C gamma) X (C delta) chunkLen
      l0 lLast lBlind) :
    v ∈ constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind := by
  rw [constraintPolys]
  apply mem_allConstraints_of_mem_subProofConstraints (p := p)
  apply mem_subProofConstraints_of_mem_permutationExpressions
  exact h

/-- A lookup constraint of one sub-proof is one of the polynomial constraints. -/
theorem mem_constraintPolys_of_mem_lookupExpressions {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly)
    (p : Fin np) {lk : LookupEval CPoly × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ lookups p) {v : CPoly}
    (h : v ∈ lookupExpressions lk.1 (lk.2.1.map (Expr.map C)) (lk.2.2.map (Expr.map C))
      fixedCols (adviceCols p) (instanceCols p) (C theta) (C beta) (C gamma) l0 lLast lBlind) :
    v ∈ constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind := by
  have h1 : v ∈ subProofConstraints fixedCols (adviceCols p) (instanceCols p)
      (gates.map (Expr.map C)) (sets p) (chunks p)
      ((lookups p).map (fun l => (l.1, l.2.1.map (Expr.map C), l.2.2.map (Expr.map C))))
      (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind :=
    mem_subProofConstraints_of_mem_lookupExpressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (List.mem_map_of_mem hlk) h
  rw [constraintPolys]
  exact mem_allConstraints_of_mem_subProofConstraints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p h1

/-! ## The deployed fingerprint -/

/-- **The fingerprint, discharged.** The polynomial constraint numerator at the gate point is the
verifier's own `expected_h_eval` fold: an equation between two things built by the same code. The hypotheses are exactly
the node binding: the fed columns, the permutation sets, the lookups and the Lagrange terms all
evaluate at `ch.x` to the values the proof string claims. -/
theorem eval_combineConstraints_deployed {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin shape.numProofs → ℕ → CPoly)
    (sets : Fin shape.numProofs → List (PermSetEval CPoly))
    (chunks : Fin shape.numProofs → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin shape.numProofs →
      List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (l0 lLast lBlind : CPoly)
    (hfixed : ∀ i, (fixedCols i).eval ch.x = finFn ps.fixedEvals i)
    (hadvice : ∀ p i, (adviceCols p i).eval ch.x = finFn (ps.adviceEvals p) i)
    (hinstance : ∀ p i, (instanceCols p i).eval ch.x = finFn (ps.instanceEvals p) i)
    (hsets : ∀ p, (sets p).map (PermSetEval.map (fun q => q.eval ch.x)) = subProofPermSets ps p)
    (hchunks : ∀ p, (chunks p).map (fun c => (c.1.map (fun q => q.eval ch.x),
        c.2.map (fun q => (q.1.eval ch.x, q.2.eval ch.x)))) = subProofPermChunks vk ps p)
    (hlookups : ∀ p, (lookups p).map (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p)
    (hl0 : l0.eval ch.x = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1)
    (hlLast : lLast.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1)
    (hlBlind : lBlind.eval ch.x
      = (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) :
    (combineConstraints fixedCols adviceCols instanceCols vk.gates sets chunks lookups
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0 lLast lBlind).eval ch.x
      = (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
          (fun acc v => acc * ch.y + v) 0 := by
  rw [eval_combineConstraints, allExpressions_eq, hl0, hlLast, hlBlind]
  simp only [funext hfixed, funext fun p => funext (hadvice p), funext fun p => funext (hinstance p),
    funext hsets, funext hchunks, funext hlookups]

/-- **Gate transport (in-Lean).** The verifier's quotient check holds given two things: the fed
columns evaluate at `x` to the claimed values (`hfixed`/`hadvice`/`hinstance`, the node binding
once `rotatedFeed`'s `ω^rot` is folded in), and the `y`-fold of the gates over those claimed values
is the committed quotient's contribution `hpoly(x)·(xⁿ − 1)` (`hfold`, halo2's `expectedHEval`
identity).

This is the step that turns the multiopen value check's node binding into `hquot`. It is not a
trust surface: `hfold` is definitional in `expectedHEval` once the gate structure is the deployed
one. -/
theorem quotientCheck_of_claimed {ng : ℕ}
    (fixedCols adviceCols instanceCols : ℕ → CPoly) (y : Fp) (gates : Fin ng → Expr Fp)
    (hpoly : CPoly) (deg : ℕ) (x : Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp)
    (hfixed : ∀ i, (fixedCols i).eval x = fixedClaimed i)
    (hadvice : ∀ i, (adviceCols i).eval x = adviceClaimed i)
    (hinstance : ∀ i, (instanceCols i).eval x = instanceClaimed i)
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval x * (x ^ deg - 1)) :
    quotientCheck (combineGates fixedCols adviceCols instanceCols y gates) hpoly deg x := by
  have hf : (fun k => (fixedCols k).eval x) = fixedClaimed := funext hfixed
  have ha : (fun k => (adviceCols k).eval x) = adviceClaimed := funext hadvice
  have hi : (fun k => (instanceCols k).eval x) = instanceClaimed := funext hinstance
  rw [quotientCheck, eval_combineGates]
  simp only [gatePolys, List.map_ofFn, Function.comp_def, Expr.eval_toPoly, hf, ha, hi]
  exact hfold

end Zcash.Snark

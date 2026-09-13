import Zcash.Snark.ZeroKnowledge.PlonkProofString
import Zcash.Snark.Soundness.Canonical.DomainSelectors
import Zcash.Snark.Soundness.Canonical.ConstraintSatisfaction
import Zcash.Snark.Soundness.Constraint.ConstraintRouting

/-!
# The honest constraint numerator and the verifier's quotient claim

The polynomial claims use exactly the proof string's query layout, replacing each
evaluation by the corresponding rotated row polynomial. Gates, permutation expressions,
and lookup expressions then use the existing common constraint builder. The selectors
are the canonical 2048-row Lagrange polynomials, with five blinding rows.

The evaluation theorem identifies this concrete numerator with the verifier's actual
`allExpressions` fold. No quotient agreement is assumed here. Divisibility by the domain
polynomial, and the row algorithms that establish it, are separate correctness obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- The four rotations disclosed before the multi-opening challenge. -/
def plonkQueryFactors : Fin 4 → Fp :=
  ![1, omegaOf 11, (omegaOf 11)⁻¹, (omegaOf 11 ^ 6)⁻¹]

/-- A column claim as a polynomial in the still-symbolic evaluation challenge. -/
def plonkRotatedColumn {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (i : Fin 4) : CPoly :=
  (privateColumnPolynomial rows id).comp (CPolynomial.C (plonkQueryFactors i) * CPolynomial.X)

/-- These polynomial claims evaluate to the first four entries of the existing column view. -/
theorem plonkRotatedColumn_eval {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) (i : Fin 4) (x q : Fp) :
    (plonkRotatedColumn rows id i).eval x =
      privateColumnView (observeColumnRows (omegaOf 11)
        (plonkObservationPoints (omegaOf 11) x q) rows) id i.castSucc := by
  rw [privateColumnView_observe]
  simp only [plonkRotatedColumn, CPolynomial.eval_comp, CPolynomial.eval_mul,
    CPolynomial.eval_C, CPolynomial.eval_X]
  congr 1
  fin_cases i <;> simp [plonkQueryFactors, plonkObservationPoints, mul_comm]

/-- The actual polynomial claims in the existing proof-string layout. -/
def plonkPolynomialClaimProof {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) :
    ProofString (plonkProofShape actions k) CPoly G :=
  plonkClaimProof pub.instances pub.fixed pub.sigma (plonkRotatedColumn rows)

/-- The fixed selector triple; kept folded during elaboration to avoid reducing 2048-row arrays. -/
@[irreducible] def plonkSelectors : CPoly × CPoly × CPoly :=
  canonicalLagrangePolynomials (omegaOf 11) (by decide : 5 < 2048)

/-- The fixed triple evaluates to the verifier's selector calculation outside the row domain. -/
theorem plonkSelectors_eval (x : Fp) (hx : x ^ 2048 ≠ 1) :
    (plonkSelectors.1.eval x, plonkSelectors.2.1.eval x, plonkSelectors.2.2.eval x) =
      lagrangeBasis (omegaOf 11) 2048 5 (x ^ 2048) x := by
  unfold plonkSelectors
  exact canonicalLagrangePolynomials_eval (n := 2048) (blinding := 5)
    (omega := omegaOf 11) (x := x) (by decide : 5 < 2048)
    (omegaOf_rows_injective 11 (by decide)) (omegaOf_primitiveRoot 11 (by decide)).pow_eq_one
    (by decide +kernel) hx

/-- The complete gate, permutation, and lookup polynomial model of the honest columns. -/
def plonkConstraintModel {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) : ConstraintPolyModel actions :=
  let ps : ProofString (plonkProofShape actions k) CPoly G := plonkPolynomialClaimProof pub rows
  let selectors := plonkSelectors
  { fixedCols := finFn ps.fixedEvals
    adviceCols := fun a => finFn (ps.adviceEvals a)
    instanceCols := fun a => finFn (ps.instanceEvals a)
    gates := vk.gates
    sets := fun a => List.ofFn (ps.permutationSetEvals a)
    chunks := fun a => ((List.ofFn (ps.permutationSetEvals a)).zip vk.permutationChunks).map fun sc =>
      (sc.1, sc.2.map fun cr =>
        (cr.1.resolve (finFn (ps.instanceEvals a)) (finFn (ps.adviceEvals a)) (finFn ps.fixedEvals),
          finFn ps.permutationCommonEvals cr.2))
    lookups := fun a => List.ofFn fun l => (ps.lookupEvals a l, vk.lookupInputExprs l, vk.lookupTableExprs l)
    beta := ch.beta
    gamma := ch.gamma
    delta := vk.delta
    theta := ch.theta
    chunkLen := vk.chunkLen
    l0 := selectors.1
    lLast := selectors.2.1
    lBlind := selectors.2.2 }

/-- The actual Horner-combined constraint numerator, before division by `X^2048 - 1`. -/
def plonkConstraintNumerator {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) : CPoly :=
  let model := plonkConstraintModel vk pub ch rows
  combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
    model.sets model.chunks model.lookups ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
    model.l0 model.lLast model.lBlind

/-- The numerator folds exactly the constraints of its packaged polynomial model. -/
theorem plonkConstraintNumerator_eq_fold {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) :
    plonkConstraintNumerator vk pub ch rows =
      plonkPolynomialFold ch.y (plonkConstraintModel vk pub ch rows).constraints := by
  rw [ConstraintPolyModel.constraints_eq_constraintPolys]
  rfl

/-- Polynomial evaluation commutes with zero-default indexed access, connecting polynomial
expressions to their row evaluations. -/
theorem eval_finFn {n : ℕ} (values : Fin n → CPoly) (x : Fp) (i : ℕ) :
    (finFn values i).eval x = finFn (fun j => (values j).eval x) i := by
  by_cases hi : i < n <;> simp [finFn, hi]

/-- Every supplied row state produces exactly the verifier's constraint numerator at `x`. -/
theorem plonkConstraintNumerator_eval {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (q : Fp)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hx : ch.x ^ 2048 ≠ 1) :
    let column := privateColumnView (observeColumnRows (omegaOf 11)
      (plonkObservationPoints (omegaOf 11) ch.x q) rows)
    let ps : ProofString (plonkProofShape actions k) Fp G :=
      plonkClaimProof (fun a => (pub.instances a).eval ch.x) (fun c => (pub.fixed c).eval ch.x)
        (fun c => (pub.sigma c).eval ch.x) (fun id i => column id i.castSucc)
    let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x
    (plonkConstraintNumerator vk pub ch rows).eval ch.x =
      (allExpressions vk ps ch lb.1 lb.2.1 lb.2.2).foldl (fun acc value => acc * ch.y + value) 0 := by
  let column := privateColumnView (actions := actions) (observeColumnRows (omegaOf 11)
    (plonkObservationPoints (omegaOf 11) ch.x q) rows)
  let ps : ProofString (plonkProofShape actions k) Fp G :=
    plonkClaimProof (fun a => (pub.instances a).eval ch.x) (fun c => (pub.fixed c).eval ch.x)
      (fun c => (pub.sigma c).eval ch.x) (fun id i => column id i.castSucc)
  let model := plonkConstraintModel vk pub ch rows
  have hfixed (i : ℕ) : (model.fixedCols i).eval ch.x = finFn ps.fixedEvals i := by
    simp only [model, plonkConstraintModel, eval_finFn, plonkPolynomialClaimProof,
      plonkClaimProof, plonkProofString, ps]
  have hadvice (a : Fin actions) (i : ℕ) :
      (model.adviceCols a i).eval ch.x = finFn (ps.adviceEvals a) i := by
    simp only [model, plonkConstraintModel, eval_finFn, plonkPolynomialClaimProof,
      plonkClaimProof, plonkProofString, plonkRotatedColumn_eval rows _ _ ch.x q, ps, column]
  have hinstance (a : Fin actions) (i : ℕ) :
      (model.instanceCols a i).eval ch.x = finFn (ps.instanceEvals a) i := by
    simp only [model, plonkConstraintModel, eval_finFn, plonkPolynomialClaimProof,
      plonkClaimProof, plonkProofString, ps]
  have hcommon (i : ℕ) :
      (finFn (plonkPolynomialClaimProof (G := G) (k := k) pub rows).permutationCommonEvals i).eval ch.x =
        finFn ps.permutationCommonEvals i := by
    simp only [eval_finFn, plonkPolynomialClaimProof, plonkClaimProof, plonkProofString, ps]
    rfl
  have hsets (a : Fin actions) :
      (model.sets a).map (PermSetEval.map (fun poly => poly.eval ch.x)) = subProofPermSets ps a := by
    simp only [model, plonkConstraintModel, subProofPermSets, List.map_ofFn, Function.comp_def]
    congr 1
    funext s
    simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString, PermSetEval.map, ps,
      plonkRotatedColumn_eval rows _ _ ch.x q, column]
    split <;> simp only [Option.map_some, Option.map_none, plonkRotatedColumn_eval rows _ _ ch.x q]
  have hchunks (a : Fin actions) :
      (model.chunks a).map (fun c => (c.1.map (fun poly => poly.eval ch.x),
        c.2.map (fun pair => (pair.1.eval ch.x, pair.2.eval ch.x)))) = subProofPermChunks vk ps a := by
    exact permChunks_bind_of_feeds vk ps ch a (model.sets a) (hsets a)
      model.fixedCols (model.adviceCols a) (model.instanceCols a)
      (finFn (plonkPolynomialClaimProof (G := G) (k := k) pub rows).permutationCommonEvals)
      hfixed (hadvice a) (hinstance a) hcommon
  have hlookups (a : Fin actions) :
      (model.lookups a).map (fun lk => (lk.1.map (fun poly => poly.eval ch.x), lk.2.1, lk.2.2)) =
        subProofLookups vk ps a := by
    simp only [model, plonkConstraintModel, subProofLookups, List.map_ofFn, Function.comp_def]
    congr 1
    funext l
    simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString, LookupEval.map, ps,
      plonkRotatedColumn_eval rows _ _ ch.x q, column]
  have hselectors : (model.l0.eval ch.x, model.lLast.eval ch.x, model.lBlind.eval ch.x) =
      lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x := by
    simp only [model, plonkConstraintModel, homega, hn, hblind]
    exact plonkSelectors_eval ch.x hx
  have hl0 := congrArg (fun v : Fp × Fp × Fp => v.1) hselectors
  have hlLast := congrArg (fun v : Fp × Fp × Fp => v.2.1) hselectors
  have hlBlind := congrArg (fun v : Fp × Fp × Fp => v.2.2) hselectors
  exact eval_combineConstraints_deployed vk ps ch model.fixedCols model.adviceCols model.instanceCols
    model.sets model.chunks model.lookups model.l0 model.lLast model.lBlind
    hfixed hadvice hinstance hsets hchunks hlookups hl0 hlLast hlBlind

/-- Dividing the computed numerator's evaluation gives the actual public verifier callback. -/
theorem plonkConstraintNumerator_eval_div {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (q : Fp)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hx : ch.x ^ 2048 ≠ 1) :
    (plonkConstraintNumerator vk pub ch rows).eval ch.x / (ch.x ^ 2048 - 1) =
      plonkVerifierHx vk pub ch (privateColumnView (observeColumnRows (omegaOf 11)
        (plonkObservationPoints (omegaOf 11) ch.x q) rows)) := by
  rw [plonkConstraintNumerator_eval vk pub ch rows q homega hn hblind hx]
  simp only [plonkVerifierHx, expectedHEval, hn, div_eq_mul_inv]

end Zcash.Snark.ZeroKnowledge

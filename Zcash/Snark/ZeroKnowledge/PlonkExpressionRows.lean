import Zcash.Snark.ZeroKnowledge.ExpressionMasking
import Zcash.Snark.ZeroKnowledge.PlonkAdviceRotations

/-!
# The actual gate and lookup expression values on domain rows

Public fixed and instance feeds and the rotated advice feed reproduce the existing
polynomial proof's expression evaluation. The mask checker depends only on those
public feeds and the query layout; its theorem compares the concrete masked rows
with the supplied original advice on every construction tape.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Fixed-query values at a domain row in the pinned query order. -/
def plonkFixedRowValues {actions : ℕ} (pub : PlonkPublicPolynomials actions) (row : Fin 2048) : ℕ → Fp :=
  finFn fun query : Fin 29 => (pub.fixed (plonkFixedQueryOrder query)).eval (omegaOf 11 ^ row.val)

/-- The public instance query at a domain row, retaining the verifier's out-of-range zero fallback. -/
def plonkInstanceRowValues {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (a : Fin actions) (row : Fin 2048) : ℕ → Fp :=
  finFn fun _ : Fin 1 => (pub.instances a).eval (omegaOf 11 ^ row.val)

/-- A gate or lookup expression evaluated through the actual public and rotated private feeds. -/
def plonkExpressionRowValue {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (row : Fin 2048) (expr : Expr Fp) : Fp :=
  expr.eval (plonkFixedRowValues pub row) (plonkAdviceRowValues rows a row) (plonkInstanceRowValues pub a row)

/-- A finite public check that the expression ignores the advice cells replaced by masks. -/
def plonkExpressionMaskCheck {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (row : Fin 2048) (expr : Expr Fp) : Bool :=
  exprMaskInvariant (plonkFixedRowValues pub row) (plonkAdviceQueryRetained row) expr

/-- The fixed row feed agrees with the existing polynomial proof. -/
theorem plonkPolynomialClaimProof_fixedRowValues {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (row : Fin 2048) (query : ℕ) :
    (finFn (plonkPolynomialClaimProof (k := k) (G := G) pub rows).fixedEvals query).eval
        (omegaOf 11 ^ row.val) = plonkFixedRowValues pub row query :=
  eval_finFn (fun j : Fin 29 => pub.fixed (plonkFixedQueryOrder j)) _ _

/-- The instance row feed agrees with the existing polynomial proof. -/
theorem plonkPolynomialClaimProof_instanceRowValues {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (a : Fin actions) (row : Fin 2048) (query : ℕ) :
    (finFn ((plonkPolynomialClaimProof (k := k) (G := G) pub rows).instanceEvals a) query).eval
        (omegaOf 11 ^ row.val) = plonkInstanceRowValues pub a row query :=
  eval_finFn (fun _ : Fin 1 => pub.instances a) _ _

/-- The public mask check proves equality with original expression values on every tape. -/
theorem plonkExpressionRowValue_masked {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (a : Fin actions) (row : Fin 2048) (expr : Expr Fp)
    (hcheck : plonkExpressionMaskCheck pub row expr = true) :
    plonkExpressionRowValue pub (plonkTotalColumnRows vk pub witness ch tape) a row expr =
      plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) a row expr :=
  exprMaskInvariant_sound _ _ _ _ _
    (plonkAdviceRowValues_masked vk pub witness ch tape a row) expr hcheck

/-- Polynomial gate evaluation is the same expression value on the domain row. -/
theorem plonkGatePolynomial_eval_row {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (a : Fin actions)
    (expr : Expr Fp) (row : Fin 2048) :
    let model := plonkConstraintModel vk pub ch rows
    ((expr.map CPolynomial.C).eval model.fixedCols (model.adviceCols a) (model.instanceCols a)).eval
        (omegaOf 11 ^ row.val) = plonkExpressionRowValue pub rows a row expr := by
  let model := plonkConstraintModel vk pub ch rows
  have h := Expr.eval_map (CPolynomial.evalRingHom (omegaOf 11 ^ row.val)) model.fixedCols
    (model.adviceCols a) (model.instanceCols a) (expr.map CPolynomial.C)
  simp only [CPolynomial.coe_evalRingHom, Expr.map_map, CPolynomial.eval_C, Expr.map_id] at h
  refine h.trans ?_
  have hfixed : (fun j => (model.fixedCols j).eval (omegaOf 11 ^ row.val)) = plonkFixedRowValues pub row := by
    funext j
    exact plonkPolynomialClaimProof_fixedRowValues (k := k) (G := G) pub rows row j
  have hadvice : (fun j => (model.adviceCols a j).eval (omegaOf 11 ^ row.val)) = plonkAdviceRowValues rows a row := by
    funext j
    exact plonkPolynomialClaimProof_adviceRowValues (k := k) (G := G) pub rows a row j
  have hinst : (fun j => (model.instanceCols a j).eval (omegaOf 11 ^ row.val)) = plonkInstanceRowValues pub a row := by
    funext j
    exact plonkPolynomialClaimProof_instanceRowValues (k := k) (G := G) pub rows a row j
  rw [hfixed, hadvice, hinst]
  rfl

/-- Compression is Horner evaluation of the actual expression-value tuple. -/
theorem plonkLookupCompressedRows_eq_values {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (theta : Fp) (a : Fin actions) (exprs : List (Expr Fp)) (row : Fin 2048) :
    plonkLookupCompressedRows pub rows theta a exprs row.val =
      (exprs.map (plonkExpressionRowValue pub rows a row)).foldl (fun acc value => acc * theta + value) 0 := by
  simp only [plonkLookupCompressedRows, plonkPolynomialClaimProof_fixedRowValues,
    plonkPolynomialClaimProof_adviceRowValues, plonkPolynomialClaimProof_instanceRowValues,
    compressExprs, List.foldl_map]
  rfl

end Zcash.Snark.ZeroKnowledge

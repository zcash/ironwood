import Mathlib
import Zcash.Snark.Group

/-!
# The fingerprint multiscalar multiplication

The verifier collapses its whole check into one multiscalar multiplication (MSM) and accepts iff that
MSM is the group identity. `Msm` is that object, mirroring halo2's `MSM<C>`
(`poly/commitment/msm.rs`): a coefficient for each of the `2 ^ k` SRS generators (`gScalars`), one for
the blinding generator (`wScalar`) and one for the inner-product generator (`uScalar`), and a list of
`(scalar, point)` terms (`other`) for the proof's own commitments. `eval` reads it against an `SRS` as
the linear combination

  `(∑ᵢ gScalarsᵢ • gᵢ) + wScalar • w + uScalar • u + Σ (c • P)`,

and the verifier's verdict is `eval srs m = 0`. This is the *polynomial-coefficient* form of the
fingerprint — the exact symbolic combination; a random evaluation of it is a separate soundness tool.

`zero`, `appendTerm`, `scale`, and `add` are the accumulation operations the verifier builds the MSM
with (halo2 `MSM::{append_term, scale, add_msm}`). Everything stays generic over `[Field F]` and an
`F`-module `G`; the concrete instantiation is `F = F_p`, `G = E_q`.
-/

namespace Zcash.Snark

/-- The fingerprint MSM (halo2 `MSM<C>`): `gScalars` are the coefficients of the `2 ^ k` SRS
generators, `wScalar` and `uScalar` the coefficients of the blinding and inner-product generators, and
`other` the `(scalar, point)` terms for the proof's commitment group elements. -/
structure Msm (k : ℕ) (F G : Type*) where
  gScalars : Fin (2 ^ k) → F
  wScalar : F
  uScalar : F
  other : List (F × G)

namespace Msm

/-- The all-zero MSM — the additive identity the batch accumulator folds from. -/
def zero (k : ℕ) (F G : Type*) [Zero F] : Msm k F G :=
  { gScalars := fun _ => 0, wScalar := 0, uScalar := 0, other := [] }

/-- Append a `(scalar, point)` term for a proof commitment (halo2 `append_term`). -/
def appendTerm {k : ℕ} {F G : Type*} (c : F) (P : G) (m : Msm k F G) : Msm k F G :=
  { m with other := (c, P) :: m.other }

/-- Scale every coefficient by `c` (halo2 `scale`). -/
def scale {k : ℕ} {F G : Type*} [Mul F] (c : F) (m : Msm k F G) : Msm k F G :=
  { gScalars := fun i => c * m.gScalars i
    wScalar := c * m.wScalar
    uScalar := c * m.uScalar
    other := m.other.map fun t => (c * t.1, t.2) }

/-- Add two MSMs coefficientwise (halo2 `add_msm`). -/
def add {k : ℕ} {F G : Type*} [Add F] (m₁ m₂ : Msm k F G) : Msm k F G :=
  { gScalars := fun i => m₁.gScalars i + m₂.gScalars i
    wScalar := m₁.wScalar + m₂.wScalar
    uScalar := m₁.uScalar + m₂.uScalar
    other := m₁.other ++ m₂.other }

/-- Add a list of scalars to the SRS-generator coefficients by position (halo2 `add_to_g_scalars`;
also covers `add_constant_term c` as `addToGScalars [c]`). Entries past the list default to `0`. -/
def addToGScalars {k : ℕ} {F G : Type*} [Add F] [Zero F] (l : List F) (m : Msm k F G) : Msm k F G :=
  { m with gScalars := fun i => m.gScalars i + l.getD i.val 0 }

/-- Add to the inner-product-generator coefficient (halo2 `add_to_u_scalar`). -/
def addToUScalar {k : ℕ} {F G : Type*} [Add F] (c : F) (m : Msm k F G) : Msm k F G :=
  { m with uScalar := m.uScalar + c }

/-- Add to the blinding-generator coefficient (halo2 `add_to_w_scalar`). -/
def addToWScalar {k : ℕ} {F G : Type*} [Add F] (c : F) (m : Msm k F G) : Msm k F G :=
  { m with wScalar := m.wScalar + c }

/-- Evaluate the MSM against an `SRS` as
`(∑ᵢ gScalarsᵢ • gᵢ) + wScalar • w + uScalar • u + Σ (c • P)`. The verifier accepts iff this is `0`. -/
def eval {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (srs : SRS G) (m : Msm srs.k F G) : G :=
  (Finset.univ.sum fun i => m.gScalars i • srs.g i)
    + m.wScalar • srs.w + m.uScalar • srs.u
    + (m.other.map fun t => t.1 • t.2).sum

/-- The zero MSM evaluates to the group identity. -/
theorem eval_zero {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (srs : SRS G) :
    (zero srs.k F G).eval srs = 0 := by
  simp [eval, zero]

/-- `eval` is additive (halo2 `add_msm`): the batch accumulator's sum of MSMs evaluates to the sum of
their evaluations. -/
theorem eval_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (srs : SRS G) (m₁ m₂ : Msm srs.k F G) :
    (m₁.add m₂).eval srs = m₁.eval srs + m₂.eval srs := by
  simp only [eval, add, add_smul, Finset.sum_add_distrib, List.map_append, List.sum_append]
  abel

private theorem smul_list_sum {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (c : F) (l : List (F × G)) :
    (l.map fun t => c • (t.1 • t.2)).sum = c • (l.map fun t => t.1 • t.2).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.map_cons, List.sum_cons, ih, smul_add]

/-- Scaling an MSM scales its evaluation (halo2 `scale`): `eval (scale c m) = c • eval m`. With
`eval_add`, this is the linearity the batch random-linear-combination argument rests on. -/
theorem eval_scale {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (srs : SRS G) (c : F) (m : Msm srs.k F G) :
    (m.scale c).eval srs = c • m.eval srs := by
  simp only [eval, scale, List.map_map, Function.comp_def, mul_smul, smul_add, Finset.smul_sum,
    smul_list_sum]

end Msm

end Zcash.Snark

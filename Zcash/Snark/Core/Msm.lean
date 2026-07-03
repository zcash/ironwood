import Mathlib
import Zcash.Snark.Core.Group

/-!
# The fingerprint multiscalar multiplication

The verifier collapses its whole check into one multiscalar multiplication (MSM) and accepts iff that
MSM is the group identity. `Msm` is that object, mirroring halo2's `MSM<C>`
(`poly/commitment/msm.rs`): a coefficient for each of the `2 ^ k` URS generators (`gScalars`), one for
the blinding generator (`wScalar`) and one for the inner-product generator (`uScalar`), and a list of
`(scalar, point)` terms (`other`) for the proof's own commitments. `eval` reads it against an `URS` as
the linear combination

  `(∑ᵢ gScalarsᵢ • gᵢ) + wScalar • w + uScalar • u + Σ (c • P)`,

and the verifier's verdict is `eval urs m = 0`. This is the exact symbolic combination — the
polynomial-coefficient form of the fingerprint; a random evaluation of it is a separate soundness tool.

`zero`, `appendTerm`, `scale`, and `add` are the accumulation operations the verifier builds the MSM
with (halo2 `MSM::{append_term, scale, add_msm}`). Everything stays generic over `[Field F]` and an
`F`-module `G`; the concrete instantiation is `F = F_p`, `G = E_q`.
-/

namespace Zcash.Snark

/-- The fingerprint MSM (halo2 `MSM<C>`): `gScalars` are the coefficients of the `2 ^ k` URS
generators, `wScalar` and `uScalar` the coefficients of the blinding and inner-product generators, and
`other` the `(scalar, point)` terms for the proof's commitment group elements. -/
structure Msm (k : ℕ) (F G : Type*) where
  gScalars : Fin (2 ^ k) → F
  wScalar : F
  uScalar : F
  other : List (F × G)
  deriving DecidableEq

namespace Msm

/-- The all-zero MSM — the additive identity the batch accumulator folds from. -/
def zero (k : ℕ) (F G : Type*) [Zero F] : Msm k F G :=
  { gScalars := fun _ => 0, wScalar := 0, uScalar := 0, other := [] }

/-- Append a `(scalar, point)` term for a proof commitment (halo2 `append_term`). Unlike halo2's `MSM`,
this models no container-level dedup — it neither drops identity points nor merges same-base terms. The
fingerprint compares term lists up to reordering, which is eval-equivalent, so a passing match means the
captured proof's bases are distinct and non-identity. -/
def appendTerm {k : ℕ} {F G : Type*} (c : F) (P : G) (m : Msm k F G) : Msm k F G :=
  { m with other := (c, P) :: m.other }

/-- Scale every coefficient by `c` (halo2 `scale`). -/
def scale {k : ℕ} {F G : Type*} [Mul F] (c : F) (m : Msm k F G) : Msm k F G :=
  { gScalars := fun i => c * m.gScalars i
    wScalar := c * m.wScalar
    uScalar := c * m.uScalar
    other := m.other.map fun t => (c * t.1, t.2) }

/-- Add two MSMs: the `g`/`w`/`u` coefficients pairwise, the `other` terms concatenated (halo2 `add_msm`). -/
def add {k : ℕ} {F G : Type*} [Add F] (m₁ m₂ : Msm k F G) : Msm k F G :=
  { gScalars := fun i => m₁.gScalars i + m₂.gScalars i
    wScalar := m₁.wScalar + m₂.wScalar
    uScalar := m₁.uScalar + m₂.uScalar
    other := m₁.other ++ m₂.other }

/-- Add a list of scalars to the URS-generator coefficients by position (halo2 `add_to_g_scalars`;
also covers `add_constant_term c` as `addToGScalars [c]`). Entries past the list default to `0`. -/
def addToGScalars {k : ℕ} {F G : Type*} [Add F] [Zero F] (l : List F) (m : Msm k F G) : Msm k F G :=
  { m with gScalars := fun i => m.gScalars i + l.getD i.val 0 }

/-- Add to the inner-product-generator coefficient (halo2 `add_to_u_scalar`). -/
def addToUScalar {k : ℕ} {F G : Type*} [Add F] (c : F) (m : Msm k F G) : Msm k F G :=
  { m with uScalar := m.uScalar + c }

/-- Add to the blinding-generator coefficient (halo2 `add_to_w_scalar`). -/
def addToWScalar {k : ℕ} {F G : Type*} [Add F] (c : F) (m : Msm k F G) : Msm k F G :=
  { m with wScalar := m.wScalar + c }

/-- Evaluate the MSM against an `URS` as
`(∑ᵢ gScalarsᵢ • gᵢ) + wScalar • w + uScalar • u + Σ (c • P)`. The verifier accepts iff this is `0`. -/
def eval {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (m : Msm urs.k F G) : G :=
  (Finset.univ.sum fun i => m.gScalars i • urs.g i)
    + m.wScalar • urs.w + m.uScalar • urs.u
    + (m.other.map fun t => t.1 • t.2).sum

/-- The zero MSM evaluates to the group identity. -/
theorem eval_zero {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G) :
    (Msm.zero urs.k F G).eval urs = 0 := by
  simp [eval, zero]

/-- Scaling an MSM scales its evaluation. -/
theorem eval_scale {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.scale c).eval urs = c • m.eval urs := by
  simp only [eval, scale, smul_add, Finset.smul_sum, List.smul_sum, List.map_map,
    Function.comp_def, mul_smul]

/-- Adding two MSMs adds their evaluations. -/
theorem eval_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (m₁ m₂ : Msm urs.k F G) :
    (m₁.add m₂).eval urs = m₁.eval urs + m₂.eval urs := by
  simp only [eval, add, add_smul, Finset.sum_add_distrib, List.map_append, List.sum_append]
  abel

/-- Appending a `(c, P)` term adds `c • P` to the evaluation. -/
theorem eval_appendTerm {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (P : G) (m : Msm urs.k F G) :
    (m.appendTerm c P).eval urs = m.eval urs + c • P := by
  simp only [eval, appendTerm, List.map_cons, List.sum_cons]
  abel

/-- Adding `c` to the inner-product-generator coefficient adds `c • u` to the evaluation. -/
theorem eval_addToUScalar {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.addToUScalar c).eval urs = m.eval urs + c • urs.u := by
  simp only [eval, addToUScalar, add_smul]
  abel

/-- Adding `c` to the blinding-generator coefficient adds `c • w` to the evaluation. -/
theorem eval_addToWScalar {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.addToWScalar c).eval urs = m.eval urs + c • urs.w := by
  simp only [eval, addToWScalar, add_smul]
  abel

/-- Adding a coefficient list to the URS-generator scalars adds `∑ᵢ lᵢ • gᵢ` to the evaluation. -/
theorem eval_addToGScalars {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (l : List F) (m : Msm urs.k F G) :
    (m.addToGScalars l).eval urs = m.eval urs + ∑ i, (l.getD i.val 0) • urs.g i := by
  simp only [eval, addToGScalars, add_smul, Finset.sum_add_distrib]
  abel

end Msm

end Zcash.Snark

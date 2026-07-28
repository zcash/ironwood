import Zcash.Snark.Soundness.Deployed.Fold

/-!
# The closed form of the deployed IPA verifier equation

halo2's IPA verifier checks one group identity, the *closed form*:

`P' + Σⱼ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀ = 0`

`Lⱼ`/`Rⱼ` are the round points and `uⱼ` the round challenges; `c` and `f` are the prover's final
scalar and blinding; `b` is the folded eval vector; `G'₀` is the fully folded generator; `U` and `W`
are the inner-product and blinding generators.

## What this module names

* `adjustedCommitment` — the *adjusted commitment* `P' = P − [v]g₀ + [ξ]S`: the commitment being
  opened, with the claimed value `v` folded into the first generator and the opening's synthetic
  blinding `[ξ]S` added.
* `VerifierIpa` — the identity's whole left side as a structure with named fields, read against the
  generators by `VerifierIpa.eval`. Its `U` and `W` coefficients are *abstract*, which is what lets
  the forking proof feed it round points represented over `(g, U, W)`. `eval_peel` folds one round
  into the commitment exactly as the recursive verifier does, and `leaf` is the depth-zero shape the
  fork tree checks.

The structure indexes its rounds and challenges by `Fin d`, while halo2's code — and so `foldAll`,
`computeB`, and the multiopen assembly — is list-shaped. `roundSum`/`roundSumFin_eq` and
`foldAllFin`/`foldAllFin_eq` are the two crossings, and `Deployed.Verification` pays them once when
it reads the assembly's output as a `VerifierIpa`.

Nothing here mentions the halo2 assembly: `Deployed.Verification` instantiates the equation at it,
and `Forking.Assembly` runs the fold.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The *adjusted commitment* the IPA verifier opens: `P' = P − [v]g₀ + [ξ]S`, for a commitment `P`
claimed to open to `v`, blinded by `[ξ]S` (halo2 `poly/commitment/verifier.rs`). The value term is
spelled as the singleton-list sum `Msm.eval` produces — `[-v]` read at index `0` and zero elsewhere
— so the deployed assembly's evaluation matches it term for term. -/
def adjustedCommitment {n : ℕ} (g : Fin n → G) (P : G) (v ξ : F) (S : G) : G :=
  P + (∑ i, ([-v].getD i.val 0) • g i) + ξ • S

/-- The sum `Σⱼ ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)` contributed by the IPA rounds, over lists — the shape the
multiopen assembly produces. `roundSumFin_eq` reads it as the depth-indexed `roundSumFin`. -/
def roundSum (rounds : List (G × G)) (u : List F) : G :=
  ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum

/-- Split the first round's contribution from `roundSum`. -/
theorem roundSum_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F) :
    roundSum ((L, R) :: rounds) (u₀ :: u) = (u₀⁻¹ • L + u₀ • R) + roundSum rounds u := by
  simp [roundSum]

/-! ## The generator fold over a `Fin`-indexed challenge vector

`foldAll` takes its challenges as a list, so its generator argument has type
`Fin (2 ^ u.length) → G` — a type that mentions a *projection* of the challenges. Every crossing
from the `Fin d`-indexed tree side therefore has to transport along `List.length_ofFn`.
`foldAllFin` runs the same fold on a `Fin d → F` challenge vector, where the generator type
`Fin (2 ^ d) → G` mentions only `d`, and `foldAllFin_eq` pays the transport once.
-/

/-- `foldGens` commutes with reindexing by `Fin.cast`. -/
theorem foldGens_comp_cast {m n : ℕ} (h : n = m) (g : Fin (2 ^ (m + 1)) → G) (u : F) :
    foldGens (fun j : Fin (2 ^ (n + 1)) => g (Fin.cast (by rw [h]) j)) u
      = fun i : Fin (2 ^ n) => foldGens g u (Fin.cast (by rw [h]) i) := by
  subst h; rfl

/-- Fold `g` through a `Fin`-indexed challenge vector without dependent casts. -/
def foldAllFin : {d : ℕ} → (Fin d → F) → (Fin (2 ^ d) → G) → G
  | 0, _, g => g 0
  | _ + 1, χ, g => foldAllFin (Fin.tail χ) (foldGens g (χ 0)⁻¹)

/-- Reindex `foldAll` along an equality of challenge lists. -/
theorem foldAll_congr_cast {u u' : List F} (h : u = u') (g : Fin (2 ^ u.length) → G) :
    foldAll u g = foldAll u' (fun j => g (Fin.cast (by rw [h]) j)) := by
  subst h; rfl

/-- `foldAllFin` equals the deployed list-based `foldAll`. -/
theorem foldAllFin_eq : {d : ℕ} → (χ : Fin d → F) → (g : Fin (2 ^ d) → G) →
    foldAllFin χ g = foldAll (List.ofFn χ) (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0
  | 0, _, g => by simp only [foldAllFin]; rfl
  | d + 1, χ, g => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      rw [foldAllFin, foldAllFin_eq (Fin.tail χ) (foldGens g (χ 0)⁻¹), foldAll_congr_cast hchal, foldAll]
      simp only [Fin.cast_cast]
      exact congrArg (fun gen => foldAll (List.ofFn (Fin.tail χ)) gen 0)
        (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-! ## The equation as a syntax object

The equation's six pieces live in named fields, and `eval` reads them against generators — the same
split `Msm` (`Core.Msm`) gives the fingerprint MSM: the scalars live in the object, the URS data
arrives at the interpretation.
-/

/-- The IPA verifier equation at depth `d` as a syntax object: `commitment` is the adjusted
commitment `P'`, `rounds` the round points `(Lⱼ, Rⱼ)` and `challenges` the round challenges `uⱼ`,
`final` the prover's final scalar `c`, and `uScalar`/`wScalar` the coefficients of the inner-product
and blinding generators. The generators themselves are supplied to `eval`.

Rounds and challenges are indexed by `Fin d` rather than carried as lists, so `eval`'s generator
argument has type `Fin (2 ^ d) → G` — mentioning only the depth, never a projection of the object.
That is what lets `eval_peel` fold a round with no reindexing. -/
structure VerifierIpa (d : ℕ) (F G : Type*) where
  commitment : G
  rounds : Fin d → G × G
  challenges : Fin d → F
  final : F
  uScalar : F
  wScalar : F

/-- The round total `Σⱼ ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)` over a `Fin`-indexed round family — `roundSum` with the
rounds and challenges indexed rather than zipped. -/
def roundSumFin : {d : ℕ} → (Fin d → G × G) → (Fin d → F) → G
  | 0, _, _ => 0
  | _ + 1, R, χ => ((χ 0)⁻¹ • (R 0).1 + χ 0 • (R 0).2) + roundSumFin (Fin.tail R) (Fin.tail χ)

/-- `roundSumFin` is `roundSum` on the corresponding lists. -/
theorem roundSumFin_eq : {d : ℕ} → (R : Fin d → G × G) → (χ : Fin d → F) →
    roundSumFin R χ = roundSum (List.ofFn R) (List.ofFn χ)
  | 0, _, _ => by simp [roundSumFin, roundSum]
  | d + 1, R, χ => by
      have hR : List.ofFn R = ((R 0).1, (R 0).2) :: List.ofFn (Fin.tail R) := by
        rw [List.ofFn_succ]; rfl
      have hχ : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      rw [roundSumFin, roundSumFin_eq (Fin.tail R) (Fin.tail χ), hR, hχ, roundSum_cons]

namespace VerifierIpa

/-- Read the equation's left side against the generators: `P' + Σⱼ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ) + [Uc]U +
[Wc]W + [-c]G'₀`, where `U` is the inner-product generator, `W` the blinding generator, and
`G'₀ = foldAllFin`. The verifier accepts iff this is `0`. -/
def eval {d : ℕ} (e : VerifierIpa d F G) (g : Fin (2 ^ d) → G) (U W : G) : G :=
  e.commitment + roundSumFin e.rounds e.challenges + e.uScalar • U + e.wScalar • W
    + (-e.final) • foldAllFin e.challenges g

/-- Absorb the first round into the commitment: `P' ↦ P' + [u₀⁻¹]L₀ + [u₀]R₀`, dropping that round
and challenge. This is the recursive verifier's commitment update. -/
def peel {d : ℕ} (e : VerifierIpa (d + 1) F G) : VerifierIpa d F G where
  commitment := e.commitment + (e.challenges 0)⁻¹ • (e.rounds 0).1 + e.challenges 0 • (e.rounds 0).2
  rounds := Fin.tail e.rounds
  challenges := Fin.tail e.challenges
  final := e.final
  uScalar := e.uScalar
  wScalar := e.wScalar

/-- Peeling a round changes nothing, once the generators are folded by that round's challenge. This
is the same commitment recursion `DeployedIpaAcceptV` runs, and it carries no reindexing because the
generator type mentions only the depth. -/
theorem eval_peel {d : ℕ} (e : VerifierIpa (d + 1) F G) (g : Fin (2 ^ (d + 1)) → G) (U W : G) :
    e.eval g U W = e.peel.eval (foldGens g (e.challenges 0)⁻¹) U W := by
  simp only [eval, peel, roundSumFin, foldAllFin]
  abel

/-- The depth-zero equation: no rounds and no challenges, so `eval` reduces to
`P + [Uc]U + [Wc]W + [-c]g₀`. This is the shape the fork tree's leaves check. -/
def leaf (P : G) (c Uc Wc : F) : VerifierIpa 0 F G where
  commitment := P
  rounds := Fin.elim0
  challenges := Fin.elim0
  final := c
  uScalar := Uc
  wScalar := Wc

end VerifierIpa

end Zcash.Snark

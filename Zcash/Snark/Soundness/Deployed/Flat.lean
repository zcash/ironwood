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
* `roundSum` — the round total `Σⱼ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)`.
* `CF` — the identity's whole left side, with *abstract* `U` and `W` coefficients. Keeping them
  abstract is what lets the forking proof feed `CF` round points represented over `(g, U, W)`;
  `CF_cons` folds one such round into the commitment and those two coefficients exactly as the
  recursive verifier folds it.

Nothing here mentions the halo2 assembly: `Deployed.Verification` instantiates `CF` at it, and
`Forking.Assembly` runs the fold. Challenge vectors are lists, mirroring halo2's list-shaped code;
`foldAllFin` and `foldAllFin_eq` are where the `Fin d`-indexed tree side crosses over.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The *adjusted commitment* the IPA verifier opens: `P' = P − [v]g₀ + [ξ]S`, for a commitment `P`
claimed to open to `v`, blinded by `[ξ]S` (halo2 `poly/commitment/verifier.rs`). The value term is
spelled as the singleton-list sum `Msm.eval` produces — `[-v]` read at index `0` and zero elsewhere
— so the deployed assembly's evaluation matches it term for term. -/
def adjustedCommitment {n : ℕ} (g : Fin n → G) (P : G) (v ξ : F) (S : G) : G :=
  P + (∑ i, ([-v].getD i.val 0) • g i) + ξ • S

/-- The sum `Σⱼ ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)` contributed by the IPA rounds. -/
def roundSum (rounds : List (G × G)) (u : List F) : G :=
  ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum

@[simp] theorem roundSum_nil_rounds (u : List F) : roundSum ([] : List (G × G)) u = 0 := by
  simp [roundSum]

@[simp] theorem roundSum_nil_challenges (rounds : List (G × G)) : roundSum rounds ([] : List F) = 0 := by
  simp [roundSum, List.zip_nil_right]

/-- Split the first round's contribution from `roundSum`. -/
theorem roundSum_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F) :
    roundSum ((L, R) :: rounds) (u₀ :: u) = (u₀⁻¹ • L + u₀ • R) + roundSum rounds u := by
  simp [roundSum]

/-- The closed-form verifier equation's left side, with abstract coefficients for `U` and `W`:
`P + Σⱼ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ) + [Uc]U + [Wc]W + [-c]G'₀`, where `P` is the adjusted commitment and the
folded generator is `G'₀ = foldAll u g 0`. -/
def CF (rounds : List (G × G)) (u : List F) (g : Fin (2 ^ u.length) → G) (P : G) (c : F)
    (Uc : F) (U : G) (Wc : F) (W : G) : G :=
  P + roundSum rounds u + Uc • U + Wc • W + (-c) • foldAll u g 0

/-- Fold one represented round point through the closed form. With `Lⱼ` and `Rⱼ` given as
`Lg + [Lv]U + [Lw]W` and `Rg + [Rv]U + [Rw]W`, the round's `g`-parts move into the commitment
(`P + [u₀⁻¹]Lg + [u₀]Rg`) and its `U`- and `W`-parts into those coefficients, while one challenge
leaves both the round sum and the generator fold. This is the same commitment, value, and blinding
recursion `DeployedIpaAcceptV` runs. -/
theorem CF_cons (Lg Rg U W : G) (Lv Lw Rv Rw : F) (rounds : List (G × G)) (u₀ : F) (u : List F)
    (g : Fin (2 ^ (u₀ :: u).length) → G) (P : G) (c Uc Wc : F) :
    CF ((Lg + Lv • U + Lw • W, Rg + Rv • U + Rw • W) :: rounds) (u₀ :: u) g P c Uc U Wc W
      = CF rounds u (foldGens g u₀⁻¹) (P + u₀⁻¹ • Lg + u₀ • Rg) c
          (Uc + u₀⁻¹ * Lv + u₀ * Rv) U (Wc + u₀⁻¹ * Lw + u₀ * Rw) W := by
  simp only [CF, roundSum_cons, foldAll]
  module

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

end Zcash.Snark

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Fingerprint.Rational.Representation

/-!
# The rational coefficient family

The object the representation walk builds and the ε theorem consumes: a rational function per
coefficient position of the assembled MSM, over denominators drawn from the enumerated factor
closure, agreeing with `assemble?`'s output on the good event.

It lives here rather than beside the ε theorem so the dependency runs one way. The walk
(`Capstone.lean`) constructs a family; `Fingerprint/Epsilon.lean` prices one. Both import this
module, and neither imports the other.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)
open MvPolynomial

/-- A rational representation of the assembled MSM's whole coefficient family on the good
event: per coefficient position, a polynomial numerator over a denominator from the enumerated
factor closure, with uniform degree bounds, agreeing with `assemble?`'s output — which the
`represents` field also pins to `some` with a fixed `other` length. The representation walk
(`Fingerprint/Rational/`) constructs a term of this structure per capture family; the ε theorem
consumes one. -/
structure RationalCoeffFamily {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (base : ProofString shape Fp G) (L D Dden : ℕ) where
  num : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp
  den : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp
  den_mem : ∀ c, den c ∈ Submonoid.closure {φ | φ ∈ denFactors vk}
  num_totalDegree_le : ∀ c, (num c).totalDegree ≤ D
  den_totalDegree_le : ∀ c, (den c).totalDegree ≤ Dden
  represents : ∀ pt : Point shape, GoodEvent vk pt →
    ∃ m : Msm shape.k Fp G,
      assemble? vk ic (Point.toProofString pt base) (Point.toChallenges pt) = some m
        ∧ m.other.length = L
        ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval pt (den c) = eval pt (num c)

/-- Multiply a family through by an extra denominator: numerator and denominator at each
coordinate pick up `den' c`, the budgets add, and the cleared identities `coeff · den = num`
survive the multiplication — no nonvanishing is consumed. The reduction step behind the
cross-denominator ε theorems below. -/
noncomputable def RationalCoeffFamily.mulDen {shape : Shape} {G : Type*}
    [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden Dden' : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden)
    (den' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hmem : ∀ c, den' c ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hdeg : ∀ c, (den' c).totalDegree ≤ Dden') :
    RationalCoeffFamily vk ic base L (D + Dden') (Dden + Dden') where
  num c := fam.num c * den' c
  den c := fam.den c * den' c
  den_mem c := mul_mem (fam.den_mem c) (hmem c)
  num_totalDegree_le c :=
    le_trans (totalDegree_mul _ _) (add_le_add (fam.num_totalDegree_le c) (hdeg c))
  den_totalDegree_le c :=
    le_trans (totalDegree_mul _ _) (add_le_add (fam.den_totalDegree_le c) (hdeg c))
  represents pt hgood := by
    obtain ⟨m, hm, hlen, hrep⟩ := fam.represents pt hgood
    refine ⟨m, hm, hlen, fun c => ?_⟩
    show m.coeffAt c * eval pt (fam.den c * den' c) = eval pt (fam.num c * den' c)
    rw [map_mul, map_mul, ← hrep c]
    ring

end Zcash.Snark

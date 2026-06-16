import Mathlib

/-!
# The verifier group `E_q` and the structured reference string

The halo2 verifier operates over the **Vesta** curve `E_q` (`vesta::Affine`): every commitment in the
proof, every reference-string generator, and the final multiscalar-multiplication (MSM) check live in
this group. We model the group abstractly as an `F`-module `G` — the only structure the verifier's MSM
uses is the `F`-linear combination of group elements (`F = F_p`, the scalar field). The Pasta group
*law* is hand-waved; the development never reaches into curve arithmetic.

We keep `G` abstract rather than instantiating it at CompElliptic's concrete Vesta curve
(`SWPoint Vesta`) on purpose. The MSM needs only the `F`-linear (module) structure, which the abstract
`F`-module already supplies; and CompElliptic's curve is an `AddCommGroup` but *not* (yet) a
`Module (ZMod p)` — its prime-order structure (group order `= p`) is not established, and proving it
is precisely the curve-arithmetic work this project hand-waves. If a `Module (ZMod p)` instance on the
Vesta curve later lands, `G` can be instantiated there with no change to the fingerprint argument.
-/

namespace Zcash.Snark

/-- The structured reference string, mirroring halo2 `Params` (`poly/commitment.rs`): `k` is the
`log₂` of the domain size, `g` the `n = 2 ^ k` generators `g₀, …, g_{n-1}`, `w` the blinding
generator, and `u` the inner-product-argument generator. The Lagrange basis `g_lagrange` is omitted:
the verifier's MSM is expressed over the monomial basis `g`. -/
structure SRS (G : Type*) where
  k : ℕ
  g : Fin (2 ^ k) → G
  w : G
  u : G

end Zcash.Snark

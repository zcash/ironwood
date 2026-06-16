import Mathlib
import CompElliptic.Fields.Pasta

/-!
# The verifier's scalar field `F_p`

An Ironwood proof is a halo2 proof over the **Vesta** curve (the README's `E_q`): commitments are
Vesta points, and challenges and evaluations are elements of Vesta's scalar field `F_p`. By the Pasta
construction `F_p = vesta::Scalar = pallas::Base = ZMod p`, where `p = PALLAS_BASE_CARD ≈ 2²⁵⁴`. The
proof system lives over Vesta (`zcash/orchard#504`), so the field is the Pallas *base* order
`PALLAS_BASE_CARD` — not the Pallas *scalar* order `PALLAS_SCALAR_CARD` of the value commitment.

`F_p` is where the fingerprint MSM's scalars live. The development stays generic over `[Field F]`;
this module just pins the instantiation `F_p = ZMod p` and records `|F_p| = p`, the cardinality the
Schwartz–Zippel bound (`Zcash.Snark.Fingerprint`) divides by. We use `F_p` abstractly; its primality
is CompElliptic's certified fact, and the Pasta arithmetic is hand-waved.
-/

namespace Zcash.Snark

/-- The verifier's scalar field order `p = |E_q|`: the Vesta scalar field order, equal to the Pallas
base field order `PALLAS_BASE_CARD`. Imported from `CompElliptic.Fields.Pasta`, where it carries a
machine-checked Lucas/Pratt primality certificate. -/
@[reducible] def scalarFieldOrder : ℕ := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD

/-- The verifier's scalar field `F_p = ZMod p` (the Vesta scalar field). A field, since `p` is prime
(instance supplied by CompElliptic). -/
abbrev Fp := ZMod scalarFieldOrder

instance : Fact (Nat.Prime scalarFieldOrder) :=
  inferInstanceAs (Fact (Nat.Prime CompElliptic.Fields.Pasta.PALLAS_BASE_CARD))

instance : NeZero scalarFieldOrder :=
  ⟨(Fact.out : Nat.Prime scalarFieldOrder).pos.ne'⟩

/-- `F_p` is finite of cardinality `p` — the quantity the Schwartz–Zippel soundness bound divides by. -/
theorem card_Fp : Fintype.card Fp = scalarFieldOrder :=
  ZMod.card scalarFieldOrder

end Zcash.Snark

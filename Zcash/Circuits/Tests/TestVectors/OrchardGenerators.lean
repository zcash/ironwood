import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Tests.TestVectors.OrchardGeneratorsData
import Zcash.Circuits.Tests.TestVectors.PointEncoding
import Zcash.Meta.AxiomCheck

/-!
# Orchard generators against zcash-test-vectors

Checks the model's nine Orchard generators against the `orchard_generators` vector of
[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors), at the revision pinned in
`OrchardGeneratorsData.lean`. The nine are the six fixed bases (`Ecc.MulFixed.Certs`) and the
three Sinsemilla domain points `noteQ`, `ivkQ`, `merkleQ` (`Action`). The vector's generator
computes the points by hash-to-curve, independently of the constants the model ports.

## What is checked

Each `*_encoding` theorem states `IsEncodingOf n X`: the model's point `X` is on the curve,
compresses (`PointEncoding.encode`, the integer of CompElliptic's `toBytes`) to the vector's
encoding `n`, and is the only curve point that does.

## Method

The encodings are evaluated by `decide +kernel`; the on-curve facts are the model's own
(`FixedBase.onCurve`, `noteQ_onCurve`, …). The six fixed bases are `FixedBase` values whose
construction carries certificates checked by `native_decide` (owner
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`, named in `Zcash.TrustBoundary`), so the
theorems that mention them inherit that owner and are pinned with it, although the check itself
is about coordinates only. The three domain points use standard axioms only.
-/

namespace Zcash.Circuits.Tests.TestVectors.OrchardGenerators

open Zcash.Circuits
open Zcash.Circuits.Ecc.MulFixed.Certs
open Zcash.Circuits.Action (noteQ ivkQ merkleQ noteQ_onCurve ivkQ_onCurve merkleQ_onCurve)
open Zcash.Circuits.Tests.TestVectors.PointEncoding

theorem spendAuthG_encoding : IsEncodingOf generators.skb spendAuthG.point :=
  .of_encode spendAuthG.onCurve (by decide +kernel)
theorem nullifierK_encoding : IsEncodingOf generators.nkb nullifierK.point :=
  .of_encode nullifierK.onCurve (by decide +kernel)
theorem valueCommitV_encoding : IsEncodingOf generators.vcvb valueCommitV.point :=
  .of_encode valueCommitV.onCurve (by decide +kernel)
theorem valueCommitR_encoding : IsEncodingOf generators.vcrb valueCommitR.point :=
  .of_encode valueCommitR.onCurve (by decide +kernel)
theorem noteCommitR_encoding : IsEncodingOf generators.cmb noteCommitR.point :=
  .of_encode noteCommitR.onCurve (by decide +kernel)
theorem noteQ_encoding : IsEncodingOf generators.cmq noteQ :=
  .of_encode noteQ_onCurve (by decide +kernel)
theorem commitIvkR_encoding : IsEncodingOf generators.ivkb commitIvkR.point :=
  .of_encode commitIvkR.onCurve (by decide +kernel)
theorem ivkQ_encoding : IsEncodingOf generators.ivkq ivkQ :=
  .of_encode ivkQ_onCurve (by decide +kernel)
theorem merkleQ_encoding : IsEncodingOf generators.mcq merkleQ :=
  .of_encode merkleQ_onCurve (by decide +kernel)

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.spendAuthG_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.nullifierK_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.valueCommitV_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.valueCommitR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.noteCommitR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.noteQ_encoding
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.commitIvkR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.ivkQ_encoding
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.merkleQ_encoding

end Zcash.Circuits.Tests.TestVectors.OrchardGenerators

# zcash-test-vectors fixtures

The Lean models of the deployed primitives mirror the Rust sources they port. These
fixtures check them against [zcash-test-vectors](https://github.com/zcash/zcash-test-vectors),
the cross-implementation anchor, so that a transcription faithfully mirroring a wrong or
drifted source still fails (ironwood#204).

| File | What it is |
|---|---|
| `OrchardPoseidonData.lean` | Generated: the `orchard_poseidon` and `orchard_poseidon_hash` vectors, and the round constants, MDS matrix and capacity element of their generator `zcash_test_vectors/orchard/poseidon.py`. |
| `OrchardPoseidon.lean` | Hand-written: the ported constants equal the generator's; `Permute.concreteValue` and the two-input `Hash.ConstantLength.value` reproduce every vector. |
| `OrchardGeneratorsData.lean` | Generated: the `orchard_generators` vector, the compressed encodings of the six fixed bases and the three Sinsemilla domain points. |
| `OrchardGenerators.lean` | Hand-written: each of those points of the model is on the curve, compresses to the vector's encoding, and is the only curve point that does. |
| `PointEncoding.lean` | Hand-written, shared: point compression `encode` (the integer of CompElliptic's `toBytes`), its injectivity on the curve, and `IsEncodingOf`, for the checks whose vectors carry points. |
| `MANIFEST.tsv` | Per-artifact provenance: path, sha256, generator, source revision, invocation. |

Generated files open with the converter's header and must not be edited by hand.
`scripts/regenerate-test-vectors.sh` checks them against `MANIFEST.tsv`, then fetches the
pinned commit, regenerates them and diffs them byte-for-byte; `--check-manifest` checks the
digests without a fetch (CI runs it in `fixtures.yml`), and `--write` rewrites the fixtures
and the manifest. The full regeneration is run by hand when the pin moves. A new fixture is
a renderer in `scripts/test_vectors_to_lean.py` and an entry in the script's `FIXTURES` list.

The comparison is at the field-element and point level. A field element is the integer its
canonical 32-byte little-endian encoding denotes; the converter rejects a non-canonical
encoding, and the check modules prove that the data is canonical and that every vector is
present. A point is compared through its compressed encoding, which is injective on the
curve, so no decompression is needed.

Byte-level residue: the canonicity of field-element encodings and the point compression
(`PointEncoding.LEOS2IP_toBytes`) are checked; no other byte-level encoding is. Clean carries
two further copies of the `P128Pow5T3` constants (`Clean/Orchard/Poseidon/`,
`Clean/Ironwood/Poseidon/`); ironwood's circuit and security model use its own, which are the
ones checked.

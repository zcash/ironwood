# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- The Fiat–Shamir byte layer: an executable BLAKE2b (`Zcash/Common/Hash/Blake2b.lean`), halo2's
  transcript encoding and the concrete oracle `halo2Transcript` (`Zcash/Snark/Verifier/
  Transcript.lean`), and per-family checks that recompute every captured challenge from bytes
  (`Fixtures/*/*/Transcript.lean`), with the encoding proved injective and prefix-free.
- The proof-string byte layer: canonical `read_point`/`read_scalar` decoders and the reader and
  serializer in the verifier's read order (`Zcash/Snark/Verifier/ProofBytes.lean`), checked
  against the exporters' exact consumed proof bytes (`Fixtures/*/*/ProofBytes.lean`), plus
  byte-level negatives.
- Fiat–Shamir separation across action counts (`Zcash/Snark/Soundness/FiatShamir/
  ActionCount.lean`): oracle locality of the schedule and disjointness of the pre-`θ` cones.
- The verifying-key digest derived rather than captured (`Zcash/Snark/Verifier/KeyDigest.lean`,
  `Fixtures/PinnedKey.lean`): halo2's `Halo2-Verify-Key` BLAKE2b over the pinned key description
  reproduces every capture's `transcript_repr`, the description's fields are read back against
  the captured key, and each family's statement of record opens the transcript with the derived
  digest. Each generated fixture carries the exact compact description the pinned exporter hashed.

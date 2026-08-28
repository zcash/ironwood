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
  byte-level negatives. Each family anchors one native parse; the length, truncation,
  non-canonical-tail, and sign-bit facts are theorems over that anchor, through a byte-accounting
  lemma fixing every accepted parse at `proofLength` and a head-replacement lemma binding the
  sign bit to `y`.
- Fiat–Shamir separation across action counts (`Zcash/Snark/Soundness/FiatShamir/
  ActionCount.lean`): oracle locality of the schedule and disjointness of the pre-`θ` cones.
- The verifying-key digest derived rather than captured (`Zcash/Snark/Verifier/KeyDigest.lean`,
  `Fixtures/PinnedKey.lean`): halo2's `Halo2-Verify-Key` BLAKE2b over the pinned key description
  reproduces every capture's `transcript_repr`, the description's fields are read back against
  the captured key, and each family's statement of record opens the transcript with the derived
  digest. Each generated fixture carries the exact compact description the pinned exporter hashed.
- `DeployedAcceptsBytes` requires the pinned description to describe the key (`Describes`, a
  relation between the description, a designated canonical key, and the key the verifier uses:
  the represented fields read back to the canonical key under an exact compact derived-`Debug`
  syntax, and the used key agrees with it on every verifier-reachable field — `blindingFactors`,
  `delta`, `chunkLen`, and the permutation partition included) and, as halo2's `common_point`
  does, refuses identity instance commitments; each honest capture discharges both by evaluation,
  and mutation witnesses show a key differing on an omitted field is rejected.
- `DeployedAcceptsRawBytes` (`Zcash/Snark/Soundness/Main.lean`): the raw entry point — halo2's
  instance column-count and usable-row checks first, commitments derived internally, then the
  exact parse — with its rejection paths as theorems; both honest captures reach it
  (`capture_deployedAcceptsRawBytes`).
- Byte acceptance for the adaptive Action family (`Zcash/Snark/Soundness/Action/
  ByteAcceptance.lean`): the concrete BLAKE2b table `halo2Coins`, at which the family's challenge
  record is the deployed schedule, and `accepts_of_acceptsBytes`, the bridge from Lean raw-byte
  acceptance into the family's typed acceptance. `ActionDeploymentInstantiation` gains the
  Rust-facing fields `pinnedVkDescription`, `deployedProofBytes`, and `deployedRustAccepts`, the
  one-way `rustAcceptsRefinesLeanRaw` refinement assumption, and the AGM edge
  `rustAcceptedProofRepresented`, consumed by `rustAccepts_halo2Coins_implies_familyAccepts`.
- The description parser is hardened: exact struct names and field sequences
  (`hasStructFields`), canonical in-range 64-digit field literals (`canonicalFieldNat?`), typed
  query column kinds, query metadata cross-checked against the layouts, and no tolerance for a
  missing separator, each with a kernel-checked regression.
- BLAKE2b carries its full 128-bit byte counter (`counterLow`/`counterHigh` into words 12 and
  13), with a kernel-checked compression vector at `t = 2^64` that a low-word-only
  implementation fails.
- A mutation test for the transcript tags (`Zcash/Snark/Soundness/FiatShamir/TagMutation.lean`):
  with halo2's domain tags deleted, the encoding collides a point with two scalars and a
  transcript with its pre-squeeze extension, so its injectivity fails; the deployed tags separate
  the same witnesses.

### Changed
- `scripts/regenerate-fingerprint-fixtures.sh` fetches the pinned Orchard commit by SHA when
  `refs/pull/544/head` has moved past it, and names the pin in its failure otherwise.
- `Describes` takes the designated canonical key and the verifier-used key, and
  `DeployedAcceptsBytes` takes both keys.
- `ActionDeploymentInstantiation` renames `deployedTypedAccepts` and `acceptsFaithful` to
  `deployedIdealizedAccepts` and `idealizedAcceptsFaithful`: they identify the injectable-oracle
  observer's typed core, not Rust acceptance.

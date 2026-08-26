# Build and CI checks

Building the Lean development re-elaborates every proof reachable from the build
targets — a successful build *is* the verification. This page lists what CI runs on
top of that build, and what each additional check guards. The workflow files under
`.github/workflows/` are the mechanism; the substance of what they do is described
here.

## The build

CI builds with

```sh
lake build --wfail Zcash FixtureCheck CircuitCheck MetaCheck SecurityCheck CensusCheck
```

The named targets are exactly the lakefile's default set, so `lake build --wfail`
is equivalent. The `--wfail` treats warnings as errors. `sorry` elaborates with a
warning, so among other things this causes any use of `sorry` to fail CI even where
no census entry reaches it.

The targets:

* **`Zcash`** — the library: everything reachable from `Zcash.lean`, which imports
  `Zcash.TrustBoundary`, the library-wide axiom census. Building this target enforces
  every census entry in that file.
* **`FixtureCheck`** — the captured fixtures, the knowledge soundness capstones, and
  the keygen certificate. The fixture-local trust boundaries and the `native_decide`
  fingerprint faithfulness checks run here; this target is separate because the
  captures are large and slow.
* **`CircuitCheck`** — `Zcash.Circuits.Tests`: comparisons of the pinned verifying-key
  and layout dumps against the Lean circuit model.
* **`MetaCheck`** — tests of `Zcash.Meta.AxiomCheck` itself: forged axioms exercising
  its rejection paths, kept out of the production import graph.
* **`SecurityCheck`** — `Zcash.Security.Ledger.BridgeTests`: regression checks
  guarding the protocol distinctions a type-correct refinement could silently erase.
* **`CensusCheck`** — the endpoint census enforced a second time, from the elaborated
  environment: every endpoint-named declaration in the census files' import closure
  must carry a direct pin.

The build also re-elaborates proofs in the CompElliptic library that it depends on,
but *not* necessarily every proof in that library, and *not* CompElliptic's
[additional CI checks](https://github.com/daira/CompElliptic/blob/main/.github/workflows/ci.yml).

## Source-level checks

Each of these is a standalone script under `scripts/`, run by CI on every
Lean-relevant change. All of them can be run locally from the repository root.

* **`check_build_coverage.sh`** — CI and the lakefile agree on the target list, and
  every Lean module is reachable from it. A module no target reaches is not elaborated
  at all: its `sorry`s, its axiom drift, and even a failure to compile would be
  invisible to a green build.
* **`check_endpoint_census.sh`** — every deliverable soundness endpoint is named in a
  census pin. The census commands traverse a declaration's *dependencies*, so an
  endpoint that nothing pinned depends on would otherwise be invisible to every census
  entry.
* **`check_csimp_census.sh`** — every `@[csimp]` replacement lemma has its own
  `assert_axioms` entry. The compiler applies a csimp substitution in all downstream
  compiled code, but the lemma's own axioms are not propagated into downstream
  `native_decide` axiom tracking
  ([lean4#7463](https://github.com/leanprover/lean4/issues/7463)).
* **`check_costed_group_work_census.sh`** — the staged Vesta work model's host
  callbacks (`pure`/`map` payloads) carry non-group computation at no charge to the
  group-work counter. The cost language is shallow, so Lean cannot check that an
  opaque payload performs no Vesta group law; each such definition is therefore
  pinned, and a new one must join the census to be reviewed against that condition.
* **`check_no_umbrella_imports.sh`** — no Lean file imports a Mathlib umbrella module.
  `import Mathlib` pulls in all of Mathlib, and several such processes in a parallel
  build create severe memory pressure.
* **`check_fixture_manifest.sh`** — every machine-generated capture artifact matches
  its recorded digest and provenance entry in `Zcash/Snark/Fixtures/MANIFEST.tsv`.
  This binds the committed artifacts to their provenance on every run, with no Rust
  toolchain needed.
* **`render-proof-bytes.sh --check`** — each match-only family's `ProofHex.lean`, the
  raw proof bytes as Lean data, re-renders identically from its `proof-bytes.hex`
  artifact, so the bytes the proof-string decoder is checked against are the captured
  ones.

## Fixture regeneration

**`scripts/regenerate-fingerprint-fixtures.sh`** proves the committed captures
regenerate byte-for-byte from their sources: it clones the pinned Orchard release,
asserts the tag and its published lockfile checksums, regenerates every capture family
plus the proof-byte siblings, and diffs each committed artifact. CI runs the full
regeneration when a fixture-relevant path changes; on every other run, the manifest
check above still binds the artifacts to their recorded digests.

The circuit-side layout dumps have no regeneration pipeline: their generator is
unpublished one-off instrumentation in local halo2/orchard checkouts
(`Zcash/Circuits/Fixtures/PROVENANCE.md` records the lineage). This should not be
confused with the *verifier-fingerprint* exporter above, which is published and
pinned. Publishing the layout instrumentation is
[#207](https://github.com/zcash/ironwood/issues/207). CI instead pins the bytes of
the layout dumps: `SHA256SUMS` must list exactly the committed dumps, each digest
must match, and the `Stamp.lean` rendering of those pins —which carries a fixture
change into Lake's import graph— must be current.

## Book checks

The book workflow validates the proof-journey page's graph data before building:
`book/validate-proof-journey.py` checks the recorded edges against the checked-out
Lean tree, so a renamed or deleted anchor fails CI rather than silently pointing at
nothing. The book itself is then built with `mdbook`, which resolves every included
file and internal link.

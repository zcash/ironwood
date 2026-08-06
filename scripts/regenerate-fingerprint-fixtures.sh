#!/usr/bin/env bash
# Regenerate every verifier-fingerprint fixture family from pinned public releases, and
# diff the results against the committed artifacts.
#
# The honest families (SingleAction, MultiAction) are captures of accepting runs of the
# deployed verifier; the random match-only families come from the same pipeline plus the
# capture tooling — a match-only exporter mode and `numInstanceColumns` shape emission in
# halo2_proofs (zcash/halo2#924), and fabricate→replay random-capture drivers in orchard
# (zcash/orchard#541). Both are upstream and released: the tooling ships in halo2_proofs
# 0.3.5 and orchard 0.15.5, so the single pin below is a release tag of zcash/orchard and
# nothing here depends on a fork or an unreleased branch. Orchard's own committed
# Cargo.lock resolves halo2_proofs 0.3.5 from crates.io by checksum, so every cargo
# invocation runs --locked against the published crate; the capture tooling is reached
# through orchard's `verifier-fingerprint` feature, which forwards to halo2_proofs'
# `unstable-verifier-fingerprint`. CI runs this script (fixtures.yml), enforcing that all
# four families are byte-reproducible from released sources alone.
#
# Sources are cloned from the public repository at the pinned release; set ORCHARD_SRC to
# a local checkout path to clone from that instead (fully offline). Set REGEN_WORK_DIR to
# keep/reuse the build tree across runs (much faster); it is reset hard to the pinned
# commit each run. All four families are committed, so every generated artifact is diffed
# byte-for-byte; a generated artifact with no committed counterpart (a future
# not-yet-ingested shape) is copied to REGEN_OUT_DIR (default scripts/generated/,
# gitignored). See Zcash/Snark/Fixtures/PROVENANCE.md.
#
# Every run first asserts the committed capture-artifact set equals the pinned list below
# (so a new or renamed family cannot sit in the tree unregenerated) and that each capture
# opens with the exporter's header. `--check-set` runs only those repo-local assertions —
# no clone, no cargo — which is what CI runs on every event, outside the regeneration's
# path filter.
#
# Run from anywhere; exits non-zero on any violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# The pinned Orchard release carrying the capture drivers, and the tag its commit must
# be. CI (fixtures.yml) runs this script, so this is the CI pin. Asserting the tag rather
# than trusting the commit alone is what makes "released, not a branch head" checkable:
# a branch commit that merely descends from a release would fail this.
ORCHARD_COMMIT=29d1d55db62153dcaeef8ef631c8991c53ed1248 # zcash/orchard tag 0.15.5
ORCHARD_TAG=0.15.5
ORCHARD_URL=${ORCHARD_SRC:-https://github.com/zcash/orchard.git}
# The released halo2_proofs the pinned Orchard lockfile must resolve, by version and
# crates.io checksum: the exporter's provenance, asserted rather than assumed.
HALO2_PROOFS_VERSION=0.3.5
HALO2_PROOFS_LOCK_CHECKSUM=f5aca1c66059a919227dec97444a11a4350d2f9c820ca48690988f0aa0e81cbf

REPO_ROOT=$PWD
OUT_DIR=${REGEN_OUT_DIR:-scripts/generated}

# generated-file : committed-path : requirement
# "required": the committed file must exist and match byte-for-byte. Every committed
# family is required — a mismatch means the committed artifact drifted from what the
# pinned release regenerates, or went missing. "optional" (currently unused) is for
# generated artifacts with no committed counterpart yet — a future not-yet-ingested
# shape — which are stashed in $OUT_DIR instead of failing.
pairs=(
  "SingleAction.Honest.Fixture.lean:Zcash/Snark/Fixtures/SingleAction/Honest/Fixture.lean:required"
  "MultiAction.Honest.Fixture.lean:Zcash/Snark/Fixtures/MultiAction/Honest/Fixture.lean:required"
  "SingleAction.Random.Fixture.lean:Zcash/Snark/Fixtures/SingleAction/Random/Fixture.lean:required"
  "MultiAction.Random.Fixture.lean:Zcash/Snark/Fixtures/MultiAction/Random/Fixture.lean:required"
  "SingleAction.Random.proof-bytes.hex:Zcash/Snark/Fixtures/SingleAction/Random/proof-bytes.hex:required"
  "MultiAction.Random.proof-bytes.hex:Zcash/Snark/Fixtures/MultiAction/Random/proof-bytes.hex:required"
)

# The committed capture-artifact set must be exactly the pinned pairs list above. Without this,
# a new or renamed family would compile under `FixtureCheck` while matching no fixtures.yml
# filter path and no diff entry here — carried in the tree as a "capture" that nothing
# regenerates. Every committed capture must also open with the exporter's header, so a
# hand-authored file cannot pose as generated output. The check runs in both directions:
# canonically named artifacts (`Fixture.lean`, any `*.hex`) must equal the pinned list, and —
# because the pinned basenames are only a convention — every `.lean` under `Fixtures/` that
# carries the exporter header must be in the pinned list, whatever it is named. A capture
# smuggled in under a novel basename either carries the header (caught here) or claims to be
# hand-written Lean (a lie review can see, with no regeneration pipeline to hide behind).
EXPORTER_HEADER_RE='^-- Auto-generated by halo2 `dump_vesta_lean_fixture(_match_only)?`\. Do not edit by hand\.$'
check_artifact_set() {
  local committed expected f
  committed=$(find Zcash/Snark/Fixtures -type f \
    \( -name 'Fixture.lean' -o -name '*.hex' \) | LC_ALL=C sort)
  expected=$(printf '%s\n' "${pairs[@]}" | cut -d: -f2 | LC_ALL=C sort)
  if [[ "$committed" != "$expected" ]]; then
    echo "VIOLATION: committed capture artifacts do not match the pinned regeneration list:" >&2
    diff <(printf '%s\n' "$expected") <(printf '%s\n' "$committed") >&2 || true
    exit 1
  fi
  while IFS= read -r f; do
    [[ "$f" == *.lean ]] || continue
    if ! head -n 1 "$f" | grep -qE "$EXPORTER_HEADER_RE"; then
      echo "VIOLATION: $f lacks the generated-exporter header" >&2
      exit 1
    fi
  done <<< "$committed"
  while IFS= read -r f; do
    if head -n 1 "$f" | grep -qE "$EXPORTER_HEADER_RE"; then
      if ! grep -qxF "$f" <<< "$expected"; then
        echo "VIOLATION: $f carries the exporter header but is not in the pinned regeneration list" >&2
        exit 1
      fi
    fi
  done < <(find Zcash/Snark/Fixtures -type f -name '*.lean' | LC_ALL=C sort)
  echo "capture-artifact set matches the pinned regeneration list, with exporter headers."
}

# `--check-set` runs the repo-local assertions alone — no clone, no cargo — so CI can run them
# on every event, outside the expensive regeneration's path filter.
if [[ "${1:-}" == "--check-set" ]]; then
  check_artifact_set
  exit 0
fi

check_artifact_set

if [[ -n "${REGEN_WORK_DIR:-}" ]]; then
  WORK_DIR=$REGEN_WORK_DIR
  mkdir -p "$WORK_DIR"
else
  WORK_DIR=$(mktemp -d)
  trap 'rm -rf "$WORK_DIR"' EXIT
fi

# Clone (or reuse) the Orchard source tree and force it to exactly the pinned release
# commit, asserting that the commit is the release tag rather than merely descended from
# one. `git clean` keeps target/ so a reused REGEN_WORK_DIR stays warm.
prepare_orchard() {
  local dest="$WORK_DIR/orchard"
  if [[ ! -d "$dest/.git" ]]; then
    echo "Cloning orchard from $ORCHARD_URL"
    git clone --quiet "$ORCHARD_URL" "$dest"
  fi
  if ! git -C "$dest" cat-file -e "${ORCHARD_COMMIT}^{commit}" 2>/dev/null; then
    git -C "$dest" fetch --quiet --tags origin
  fi
  git -C "$dest" checkout --quiet --detach "$ORCHARD_COMMIT"
  git -C "$dest" reset --hard --quiet "$ORCHARD_COMMIT"
  git -C "$dest" clean -fdxq --exclude=target
  if [[ "$(git -C "$dest" rev-parse HEAD)" != "$ORCHARD_COMMIT" ]]; then
    echo "VIOLATION: orchard is not at pinned commit $ORCHARD_COMMIT" >&2
    exit 1
  fi
  local tagged
  tagged=$(git -C "$dest" rev-parse --verify --quiet "refs/tags/$ORCHARD_TAG^{commit}" || true)
  if [[ "$tagged" != "$ORCHARD_COMMIT" ]]; then
    echo "VIOLATION: pinned commit is not the orchard $ORCHARD_TAG release tag" >&2
    echo "  tag $ORCHARD_TAG -> ${tagged:-<absent>}" >&2
    echo "  pinned commit    -> $ORCHARD_COMMIT" >&2
    exit 1
  fi
  if [[ -n "$(git -C "$dest" status --porcelain)" ]]; then
    echo "VIOLATION: orchard working tree is not clean at the pinned release" >&2
    exit 1
  fi
  echo "orchard is at the $ORCHARD_TAG release tag ($ORCHARD_COMMIT)."
}

prepare_orchard

# Assert the pinned release's own lockfile resolves the released halo2_proofs from
# crates.io by checksum -- the exporter's provenance. No patching: the lockfile is used
# as published, and every cargo invocation below runs --locked against it.
lock_entry=$(grep -A3 '^name = "halo2_proofs"$' "$WORK_DIR/orchard/Cargo.lock")
expected_entry='name = "halo2_proofs"
version = "'"$HALO2_PROOFS_VERSION"'"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "'"$HALO2_PROOFS_LOCK_CHECKSUM"'"'
if [[ "$lock_entry" != "$expected_entry" ]]; then
  echo "VIOLATION: orchard's lockfile does not resolve the expected released halo2_proofs:" >&2
  echo "$lock_entry" >&2
  exit 1
fi
echo "Cargo.lock resolves halo2_proofs $HALO2_PROOFS_VERSION from crates.io by checksum."

# Install orchard's pinned toolchain (mirrors fixtures.yml), then run every capture
# driver in one pass. The unanchored filter matches every upstream capture driver, and
# deliberately not the Rust-only rejected:: capture. The released orchard also ships a
# three-action match-only driver; it runs here but its output is not ingested, so only the
# four committed families below are diffed.
if command -v rustup >/dev/null 2>&1; then
  (cd "$WORK_DIR/orchard" && rustup show >/dev/null)
fi
mkdir -p "$WORK_DIR/out"
(
  cd "$WORK_DIR/orchard" &&
    env ORCHARD_LEAN_SINGLE_FIXTURE_OUT="$WORK_DIR/out/SingleAction.Honest.Fixture.lean" \
      ORCHARD_LEAN_MULTI_FIXTURE_OUT="$WORK_DIR/out/MultiAction.Honest.Fixture.lean" \
      ORCHARD_LEAN_SINGLE_RANDOM_FIXTURE_OUT="$WORK_DIR/out/SingleAction.Random.Fixture.lean" \
      ORCHARD_LEAN_MULTI_RANDOM_FIXTURE_OUT="$WORK_DIR/out/MultiAction.Random.Fixture.lean" \
      ORCHARD_LEAN_SINGLE_RANDOM_PROOF_OUT="$WORK_DIR/out/SingleAction.Random.proof-bytes.hex" \
      ORCHARD_LEAN_MULTI_RANDOM_PROOF_OUT="$WORK_DIR/out/MultiAction.Random.proof-bytes.hex" \
      cargo test --locked --lib --features verifier-fingerprint \
      circuit::fingerprint::fingerprint_capture -- --nocapture
)

status=0
stashed=0
for pair in "${pairs[@]}"; do
  generated="$WORK_DIR/out/${pair%%:*}"
  rest=${pair#*:}
  committed=${rest%%:*}
  requirement=${rest#*:}
  if [[ ! -f "$generated" ]]; then
    echo "VIOLATION: capture run did not produce $generated" >&2
    status=1
    continue
  fi
  if [[ -f "$committed" ]]; then
    if cmp -s "$generated" "$committed"; then
      echo "OK: $committed matches the regenerated capture byte-for-byte."
    else
      echo "VIOLATION: $committed differs from the regenerated capture ($generated)" >&2
      status=1
    fi
  elif [[ "$requirement" == "required" ]]; then
    echo "VIOLATION: committed fixture $committed is missing" >&2
    status=1
  else
    mkdir -p "$OUT_DIR"
    cp "$generated" "$OUT_DIR/${pair%%:*}"
    echo "Generated, no committed counterpart yet: $OUT_DIR/${pair%%:*}"
    stashed=$((stashed + 1))
  fi
done

if [[ $status -eq 0 ]]; then
  echo "fingerprint fixtures: all committed artifacts match; ${stashed} pending artifact(s) stashed in $OUT_DIR."
fi
exit $status

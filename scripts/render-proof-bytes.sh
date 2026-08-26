#!/usr/bin/env bash
# Render each match-only family's raw `proof-bytes.hex` into a Lean module carrying the same
# hex string, so the proof-string decoder (`Zcash/Snark/Verifier/ProofBytes.lean`) can be checked
# against the exact bytes the deployed verifier consumed in that capture.
#
# The `.hex` artifacts are pinned by the fixture manifest and regenerated from the released
# Orchard pipeline; this rendering is a deterministic function of them. `--check` re-renders and
# diffs against the committed modules, which is what CI runs (fixtures.yml) on every event, so a
# committed rendering can never drift from its `.hex`. Run from anywhere; exits non-zero on any
# violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# family directory : Lean namespace : description
families=(
  "Zcash/Snark/Fixtures/SingleAction/Random:FixtureRandom:random single-action"
  "Zcash/Snark/Fixtures/MultiAction/Random:FixtureRandom2:random two-action"
)

render() {
  local dir=$1 ns=$2 desc=$3 hex
  hex=$(tr -d '\n\r' < "$dir/proof-bytes.hex")
  if [[ ! "$hex" =~ ^[0-9a-f]+$ || $(( ${#hex} % 2 )) -ne 0 ]]; then
    echo "VIOLATION: $dir/proof-bytes.hex is not an even-length lowercase hex string" >&2
    exit 1
  fi
  cat <<LEAN
-- Rendered from $dir/proof-bytes.hex by scripts/render-proof-bytes.sh. Do not edit by hand.
import Zcash.Snark

/-!
# Raw proof bytes of the $desc capture

The fabricated proof string the deployed verifier consumed in this capture, hex-encoded: the
content of the \`proof-bytes.hex\` sibling, carried as Lean data so the proof-string decoder can be
checked against it (this family's \`ProofBytes.lean\`). CI re-renders this module from the \`.hex\`
artifact and diffs it, so the two cannot drift apart.
-/

namespace Zcash.Snark.$ns

/-- The captured proof string, hex-encoded, exactly as \`proof-bytes.hex\` holds it. -/
def capturedProofHex : String :=
  "$hex"

end Zcash.Snark.$ns
LEAN
}

status=0
for entry in "${families[@]}"; do
  dir=${entry%%:*}
  rest=${entry#*:}
  ns=${rest%%:*}
  desc=${rest#*:}
  out="$dir/ProofHex.lean"
  if [[ "${1:-}" == "--check" ]]; then
    if [[ ! -f "$out" ]]; then
      echo "VIOLATION: $out is missing; run scripts/render-proof-bytes.sh" >&2
      status=1
      continue
    fi
    if ! diff -u "$out" <(render "$dir" "$ns" "$desc"); then
      echo "VIOLATION: $out is stale against $dir/proof-bytes.hex; run scripts/render-proof-bytes.sh" >&2
      status=1
    else
      echo "OK: $out matches $dir/proof-bytes.hex."
    fi
  else
    render "$dir" "$ns" "$desc" > "$out"
    echo "Rendered $out"
  fi
done
exit $status

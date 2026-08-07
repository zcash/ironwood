#!/usr/bin/env bash
# Check that every `@[csimp]` declaration in the library is covered by an
# `assert_axioms` entry in Zcash/TrustBoundary.lean. The compiler applies a
# csimp substitution in all downstream compiled code, but the axioms of the lemma's
# own proof are not propagated into downstream `native_decide` axiom tracking (
# lean4#7463), so a csimp lemma whose axioms go unchecked would be an
# axiom-smuggling channel.
#
# Robustness: every line containing "csimp" is scanned. Documentation must quote
# mentions as exactly `@[csimp]` (backtick-quoted); that exact string is removed
# before testing, so any remaining attribute syntax (`@[..., csimp, ...]` or
# `attribute [csimp] name`) is treated as real and must name its declaration on
# the same line. Matching against the census is by the declaration's final name
# component.
#
# Scope: this guards against accidental omissions, NOT adversarial code. Run from
# the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# Every "csimp" line in the library (the census file itself included: a csimp
# declared there is enforced like any other, and its comments follow the same
# quoting rule).
matches=$(grep -rn "csimp" Zcash/ --include="*.lean" || true)

status=0
count=0
while IFS=: read -r file lineno line; do
  [[ -z "$file" ]] && continue
  stripped=${line//'`@[csimp]`'/}
  if ! printf '%s' "$stripped" | grep -qE '@\[[^]]*\bcsimp\b|attribute[[:space:]]*\[[^]]*\bcsimp\b'; then
    continue  # only quoted documentation mentions on this line
  fi
  name=$(printf '%s' "$stripped" | sed -nE "s/.*(theorem|def)[[:space:]]+([A-Za-z0-9_'.]+).*/\2/p")
  if [[ -z "$name" ]]; then
    name=$(printf '%s' "$stripped" | sed -nE "s/.*attribute[[:space:]]*\[[^]]*csimp[^]]*\][[:space:]]+([A-Za-z0-9_'.]+).*/\1/p")
  fi
  if [[ -z "$name" ]]; then
    echo "VIOLATION: $file:$lineno: csimp attribute syntax must name its declaration on the same line (write \`@[csimp] theorem <name>\`), and documentation mentions must be quoted as exactly \`@[csimp]\`" >&2
    status=1
    continue
  fi
  count=$((count + 1))
  # Any census file counts, not just Zcash/TrustBoundary.lean. Census entries are spread across
  # the per-fixture boundaries and the test-only libraries, and a lemma is pinned wherever its
  # entry sits; requiring the main file would reject a legitimate pin in a fixture boundary, and
  # cannot be satisfied at all by a csimp lemma in a test-only library that production must not
  # import (`Zcash/Meta/Tests/`, the `MetaCheck` target).
  if ! grep -rqE "^assert_axioms .*\.${name}( |\$)|^assert_axioms ${name}( |\$)" Zcash/ --include="*.lean"; then
    echo "VIOLATION: csimp declaration ${name} ($file:$lineno) has no assert_axioms entry in any census file" >&2
    status=1
  fi
done <<< "$matches"

if [[ $status -eq 0 ]]; then
  echo "csimp census: ${count} csimp declaration(s), all covered."
fi
exit $status

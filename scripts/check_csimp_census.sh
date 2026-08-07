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
# quoting rule). `Zcash/Meta/Tests/` is excluded, as in
# `scripts/check_endpoint_census.sh`: it holds forged adversarial declarations that
# exercise the rejection paths of the census macros themselves, including a csimp
# lemma resting on a bespoke axiom. Censusing those would assert the very axiom set
# the fixture exists to be rejected for.
matches=$(find Zcash -name '*.lean' -not -path 'Zcash/Meta/Tests/*' -print0 \
  | xargs -0 grep -n "csimp" /dev/null || true)

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
  if ! grep -qE "^assert_axioms .*\.${name}( |\$)|^assert_axioms ${name}( |\$)" Zcash/TrustBoundary.lean; then
    echo "VIOLATION: csimp declaration ${name} ($file:$lineno) has no assert_axioms entry in Zcash/TrustBoundary.lean" >&2
    status=1
  fi
done <<< "$matches"

if [[ $status -eq 0 ]]; then
  echo "csimp census: ${count} csimp declaration(s), all covered."
fi
exit $status

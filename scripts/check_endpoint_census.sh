#!/usr/bin/env bash
# Check that every deliverable soundness endpoint is named in a census pin.
#
# `assert_axioms` / `assert_computable` (and Mathlib's `assert_no_sorry`) are built on
# `Lean.collectAxioms`, which traverses a declaration's transitive *dependencies*. An endpoint
# that nothing pinned depends on is therefore invisible to every census entry: a `sorry` or a
# stray `native_decide` in its own proof reaches no assertion, and the build stays green. That
# is the "trusted-base escape the census fails to catch" failure mode, and it applies exactly to
# the top-level leaves — which is what the advertised capstones are.
#
# The rule this script enforces: a declaration whose base name matches one of the endpoint
# naming patterns below must be named directly in an `assert_axioms` or `assert_computable`
# entry in one of the census files. Direct, not transitive: an endpoint states the trust tier of
# its own conclusion, and coverage that happens to flow through some other pin disappears
# silently the moment that dependent is refactored.
#
# `assert_no_sorry` does NOT satisfy the rule. It bounds only sorries, while the census claim is
# a bound on the whole trusted base; an endpoint carrying only `assert_no_sorry` can still reach
# an unexpected axiom. Endpoints may carry both.
#
# Names are compared fully qualified. The enclosing namespace is reconstructed from the
# `namespace`/`end` pairs above the declaration, which is what the census entries must also
# write (`Zcash.Meta.AxiomCheck.checkFullyQualified`).
#
# Scope: this guards against accidental omissions, NOT adversarial code. A declaration whose
# name does not match a pattern is not an endpoint as far as this check is concerned; keeping
# the patterns in step with the capstone naming convention is a review responsibility. The
# declaration's name must be on the same line as its `theorem`/`def` keyword. Run from the
# repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# A declaration is a deliverable endpoint when its base name matches this pattern. These are the
# capstone families: the verifier-soundness rungs (`orchard_verifier_*`), the composed Action
# probability endpoints (`orchard_action_*`), the captured knowledge-error endpoints
# (`orchard_deployed_*`), the two Lean → Rocq Action bridge capstones named exactly below, and the
# concrete-statement terminals (`*bundleStatement_or_relation*`).
ENDPOINT_RE="^(orchard_verifier_|orchard_action_|orchard_deployed_|validActionInputs_iff_exists_proverAssumptionsPost$|proverAssumptionsPost_implies_gardenOrchardAction_output$)|bundleStatement_or_relation"

# Sources scanned for endpoint declarations. `Zcash/Meta/Tests/` is excluded: it holds forged
# adversarial declarations that exercise the rejection paths of the census macros themselves.
# `find` rather than `git ls-files`, so a new endpoint in a not-yet-staged file is still checked.
sources=$(find Zcash -name '*.lean' -not -path 'Zcash/Meta/Tests/*' | sort)
census=$(find Zcash -name 'TrustBoundary.lean' | sort)

if [[ -z "$census" ]]; then
  echo "VIOLATION: no census (TrustBoundary.lean) files found" >&2
  exit 1
fi

# Every pinned name, fully qualified, one per line. An optional `_root_.` prefix is accepted by
# the macros, so strip it here too.
pins=$(echo "$census" | xargs grep -hE '^assert_(axioms|computable) ' \
  | sed -E 's/^assert_(axioms|computable)[[:space:]]+//; s/^_root_\.//; s/[[:space:]].*$//' \
  | sort -u)

status=0
count=0

while IFS= read -r file; do
  # Reconstruct the namespace prefix while scanning, so declarations can be reported fully
  # qualified. `stack` holds the open namespace segments, space separated (Lean identifiers
  # cannot contain spaces). `end <id>` pops only when it matches the innermost open namespace,
  # so a named `section ... end` cannot corrupt the stack.
  stack=""
  prefix=""
  while IFS= read -r line || [[ -n "$line" ]]; do
    if [[ $line =~ ^namespace[[:space:]]+([A-Za-z0-9_.\']+) ]]; then
      stack="$stack ${BASH_REMATCH[1]}"
      prefix="${prefix}${BASH_REMATCH[1]}."
      continue
    fi
    if [[ $line =~ ^end[[:space:]]+([A-Za-z0-9_.\']+) ]]; then
      top="${stack##* }"
      if [[ -n $top && $top == "${BASH_REMATCH[1]}" ]]; then
        stack="${stack% *}"
        prefix="${prefix%"$top".}"
      fi
      continue
    fi
    # A top-level declaration: column 0, optional modifiers, then the name.
    [[ $line =~ ^(private[[:space:]]+|protected[[:space:]]+)?(noncomputable[[:space:]]+|partial[[:space:]]+|unsafe[[:space:]]+)?(theorem|lemma|def|abbrev)[[:space:]]+([A-Za-z0-9_\']+) ]] || continue
    # A private helper is not a deliverable endpoint.
    if [[ ${BASH_REMATCH[1]} == private* ]]; then continue; fi
    name=${BASH_REMATCH[4]}
    # Bash-native match, not a `grep` spawn: this runs once per declaration in the library.
    [[ $name =~ $ENDPOINT_RE ]] || continue

    qualified="${prefix}${name}"
    count=$((count + 1))
    # A here-string, not `printf ... | grep -q`: `grep -q` exits at the first match, the writer
    # takes SIGPIPE, and `pipefail` would report that as a failed lookup — turning a pinned
    # endpoint into an intermittent false violation.
    if ! grep -qxF "$qualified" <<< "$pins"; then
      echo "VIOLATION: endpoint ${qualified} (${file}) has no assert_axioms/assert_computable entry in any TrustBoundary.lean" >&2
      status=1
    fi
  done < "$file"
# A here-string, not a pipe: a piped `while` would run in a subshell and lose `status`/`count`.
done <<< "$sources"

if [[ $status -eq 0 ]]; then
  echo "endpoint census: ${count} endpoint declaration(s), all pinned."
fi
exit $status

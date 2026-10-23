#!/usr/bin/env bash
# Check that every deliverable soundness endpoint is named in a census pin.
#
# `assert_axioms`, `assert_computable`, and `assert_efficient` (and Mathlib's `assert_no_sorry`)
# are built on `Lean.collectAxioms`, which traverses a declaration's transitive *dependencies*.
# An endpoint that nothing pinned depends on is therefore invisible to every census entry: a
# `sorry` or a stray `native_decide` in its own proof reaches no assertion, and the build stays
# green. That is the "trusted-base escape the census fails to catch" failure mode, and it applies
# exactly to the top-level leaves — which is what the advertised capstones are.
#
# The rule this script enforces: a declaration whose base name matches one of the endpoint
# naming patterns below must be named directly in an `assert_axioms`, `assert_computable`, or
# `assert_efficient` entry in one of the census files. Direct, not transitive: an endpoint states
# the trust tier of its own conclusion, and coverage that happens to flow through some other pin
# disappears silently the moment that dependent is refactored.
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
# name does not match a pattern is not an endpoint as far as this check is concerned. New endpoint
# families must either extend the protocol-family alternatives below or carry one of the semantic
# markers `_error_bound`, `_finite_security`, `_prob_le`, or `_capstone` — in any position, so a
# qualifier such as `_of_<premise>` or `_at_<instance>` may follow it. The declaration's name must
# be on the same line as its declaration keyword. Run from the repository root; exits non-zero on
# violation.
#
# The same rule is enforced a second time from the elaborated environment:
# `Zcash/Meta/EndpointCensus.lean` ports the pattern below to a Lean predicate, the census
# commands record every pin they elaborate, and `Zcash/CensusCheck.lean` (the `CensusCheck`
# default target) asserts that no endpoint in the census files' import closure is unpinned. That
# closes what this line parser cannot see — declarations emitted by custom commands, unrecognized
# modifiers, or multiline syntax — while this scan keeps the whole file tree in scope, census
# imports or not. Keep `ENDPOINT_RE` and `Zcash.Meta.isEndpointBaseName` in sync.
set -euo pipefail
cd "$(dirname "$0")/.."

# A declaration is a deliverable endpoint when its base name matches this pattern. The leading
# alternatives retain the established endpoint families: the verifier-soundness rungs
# (`orchard_verifier_*`), the composed Action probability endpoints (`orchard_action_*`), the
# captured knowledge-error endpoints (`orchard_deployed_*`), the concrete-statement terminals
# (`*bundleStatement_or_relation*`), and the profiled work-factor packages (`*workFactor*`). The
# final alternative is deliberately protocol-independent: the standardized semantic markers keep a
# new capstone family inside the census without requiring another prefix to be added here.
# `_measure_le` and `_probability_bound` are the two older spellings for a probability bound, kept
# matching so a capstone that still carries either is demanded rather than silently unpinned; they
# also match surface, root-set, and per-challenge measures inside the AGM, Action, and pricing
# layers, which are pinned for that reason rather than as independent claims. `_capstone` is the
# explicit marker for endpoints that are neither an error formula nor a concrete finite-security
# statement.
#
# The Rust-to-Lean boundary contributes three more families, all leaves in the same sense: the
# per-family statements of record (`nonInteractiveFingerprint_matches_derived*`), the quantified
# match's generic and per-capture epsilon bounds (`competing_*`, covering both
# `competing_coefficient_family_agreement_le*` in `Zcash.Snark` and the
# `competing_family_agreement_le*` headliners beside each random fixture), and the `Perm`→positional
# bridges (`fingerprint_matches_positional`) that join the two.
#
# `orchard_verifier_*` and `*workFactor*` both currently match nothing and are retained as guards,
# so a reintroduced name in either family is demanded rather than silently unpinned. The
# `orchard_verifier_*` rungs were retired with the legacy rewind paths; `*workFactor*` named the
# Action knowledge capstone's `2^123` instantiation, the consensus-maximum packages, and the
# deployment-record transport, until all three were renamed onto the
# `orchard_deployed_*`/`orchard_action_*` prefixes and the `_finite_security` suffix, which is
# what matches them now.
#
# `_prob_le` is the current spelling for a probability bound, alongside the two older ones; it is
# matched for the same reason they are.
#
# A semantic marker matches in any position, provided what follows it is the end of the name or a
# non-alphanumeric character (`_` or `'`): `attack_prob_le`, `attack_prob_le'`,
# `bound_measure_le_for`, and `attack_prob_le_of_textbookDL` all carry a marker;
# `attack_prob_lemma` does not. The marker used to be anchored at the end of the name, and that
# anchor lost endpoints twice. A `_measure_le` endpoint disappeared from this check the moment it
# was generalized over `numProofs` and gained a `_for` suffix, so `_for` was admitted (and later
# `_experiment` and `_idealizedks`, the experiment-placement and idealization qualifiers, in the
# same way). The anchor then deliberately kept the `_prob_le_of_<premise>` spellings out, on the
# reasoning that a bound conditional on a named premise is consumed by some unconditional
# capstone and is never itself a leaf — which is false: the straight-line AGM binding and
# deployed-root capstones are stated exactly in that form, as a probability bound *of*
# textbook-DL hardness, nothing consumes them, and no census entry disclosed their
# `native_decide` base until they were pinned. Generalizing, instantiating, or conditioning an
# endpoint must never retire its census obligation: a name that carries a marker states a
# probability, error, or security claim, and its pin states that claim's trusted base whatever
# qualifier follows.
ENDPOINT_RE='(^orchard_(verifier|action|deployed)_)|(^competing_)|(^nonInteractiveFingerprint_matches_derived)|(bundleStatement_or_relation)|(workFactor)|(fingerprint_matches_positional)|(_(error_bound|finite_security|measure_le|probability_bound|prob_le|capstone)([^A-Za-z0-9]|$))'

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
# the macros, so strip it here too. A pin may wrap its name onto the following line (the
# assert command alone, then the indented name) to keep long names within the line-width
# convention; accept both layouts.
# A name that fails to parse (an empty continuation, or a token carrying syntax like
# `+native(`) is reported as a violation rather than skipped: a silently dropped pin would
# make a pinned endpoint read as unpinned — or, combined with a declaration-side parse gap,
# read as nothing at all. The elaborated `CensusCheck` remains the backstop for the
# declaration side.
pins=$(echo "$census" | xargs awk '
  /^assert_(axioms|computable|efficient)[[:space:]]+[^[:space:]]/ {
    name = $2
    sub(/^_root_\./, "", name)
    if (name == "" || name ~ /[+(),]/) name = "PARSE_ERROR"
    print name
    next
  }
  /^assert_(axioms|computable|efficient)[[:space:]]*$/ { pending = 1; next }
  pending {
    name = $1
    sub(/^_root_\./, "", name)
    if (name == "" || name ~ /[+(),]/) name = "PARSE_ERROR"
    print name
    pending = 0
  }
  END { if (pending) print "PARSE_ERROR" }
' | sort -u)

# A herestring rather than a pipe: `grep -q` exits at the first match, and under
# `pipefail` the SIGPIPE it sends a still-writing `echo` would turn a MATCH into a
# failed pipeline, silently skipping this guard.
if grep -q '^PARSE_ERROR$' <<< "$pins"; then
  echo "VIOLATION: unparseable assert_axioms/assert_computable/assert_efficient entry layout in census files" >&2
  exit 1
fi

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
    # A top-level declaration: column 0, optional modifiers, then the name. The name class is
    # ASCII-only, so a declaration whose name carries a Unicode character before its marker
    # escapes this scan. A Unicode character after the marker instead truncates the extracted
    # name, so the pin lookup fails loud on the truncated spelling. The elaborated
    # `CensusCheck` sees the real names and remains the backstop that demands a name this
    # scan misses.
    [[ $line =~ ^(private[[:space:]]+|protected[[:space:]]+)?(noncomputable[[:space:]]+|partial[[:space:]]+|unsafe[[:space:]]+)?(theorem|lemma|def|abbrev|instance|axiom|opaque|inductive|structure|class)[[:space:]]+([A-Za-z0-9_\']+) ]] || continue
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
      echo "VIOLATION: endpoint ${qualified} (${file}) has no assert_axioms/assert_computable/assert_efficient entry in any TrustBoundary.lean" >&2
      status=1
    fi
  done < "$file"
# A here-string, not a pipe: a piped `while` would run in a subshell and lose `status`/`count`.
done <<< "$sources"

if [[ $status -eq 0 ]]; then
  echo "endpoint census: ${count} endpoint declaration(s), all pinned."
fi
exit $status

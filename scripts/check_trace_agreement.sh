#!/usr/bin/env bash
# Rebuild every check that a compositional trace agrees with the certified walk it replaced.
#
# Each of the three Action source certificates is retired in its own step, and the check that
# corroborated it against the compositional trace is retired with it. So no single commit holds
# all three checks, and a reviewer who wants to see them cannot simply build the branch tip.
# This script finds the commit that introduced each check, builds that module there, and
# restores the checkout it started from.
#
# This is expensive, and deliberately so. Each check compares the compositional trace against
# the certificate's own entries, so building it rebuilds that certificate — the very thing the
# branch retires, at its original cost of tens of minutes to hours apiece. That is the point:
# the comparison is only worth anything if the certified side is genuinely recomputed. Run it
# as an audit, with time to spare, not as a CI check.
#
# Run from anywhere in the repository. Exits non-zero if any check fails to build. Each build's
# output is kept under work/, so a run that takes hours can be followed with `tail -f` and a
# failure can be diagnosed without repeating it.
set -euo pipefail
cd "$(dirname "$0")/.."

readonly PATTERN='Zcash/Snark/ZeroKnowledge/Action*TraceAgreement.lean'
readonly LAKE="$HOME/.elan/bin/lake"
readonly LOGDIR=work

if [ ! -x "$LAKE" ]; then
  echo "VIOLATION: $LAKE not found; this project pins its toolchain with elan." >&2
  exit 1
fi

# Checking out other commits would discard uncommitted work, so refuse to start on a dirty tree.
if [ -n "$(git status --porcelain)" ]; then
  echo "VIOLATION: the working tree has uncommitted changes; commit or stash them first." >&2
  git status --short >&2
  exit 1
fi

# Remember where to come back to: a branch name if we are on one, otherwise the detached commit.
start_ref=$(git symbolic-ref --quiet --short HEAD || git rev-parse HEAD)
restore() {
  local current
  current=$(git symbolic-ref --quiet --short HEAD || git rev-parse HEAD)
  if [ "$current" != "$start_ref" ]; then
    echo "--- restoring $start_ref"
    git checkout --quiet "$start_ref"
  fi
}
trap restore EXIT

# Every path that has ever matched the pattern on this history, and the commit that added it.
mapfile -t paths < <(git log --diff-filter=A --format= --name-only -- "$PATTERN" | sort -u)

if [ ${#paths[@]} -eq 0 ]; then
  echo "VIOLATION: no agreement check found in this history (pattern: $PATTERN)." >&2
  echo "  Either none has been written yet, or the naming convention has changed." >&2
  exit 1
fi

mkdir -p "$LOGDIR"

status=0
for path in "${paths[@]}"; do
  commit=$(git log --diff-filter=A --format=%H -1 -- "$path")
  module=$(printf '%s' "${path%.lean}" | tr '/' '.')
  log="$LOGDIR/$module.log"
  echo "=== $module"
  echo "    introduced by $(git log --format='%h %s' -1 "$commit")"
  echo "    build log: $log"
  git checkout --quiet "$commit"
  if "$LAKE" build "$module" >"$log" 2>&1; then
    echo "    OK"
  else
    echo "    FAILED to build at $commit; see $log" >&2
    status=1
  fi
done

if [ "$status" -eq 0 ]; then
  printf 'trace agreement: %d check(s), all rebuilt.\n' "${#paths[@]}"
fi
exit "$status"

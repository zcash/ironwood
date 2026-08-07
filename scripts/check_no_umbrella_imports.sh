#!/usr/bin/env bash
# Check that no Lean file imports the Mathlib umbrella modules.
#
# `import Mathlib` pulls in all of Mathlib, which peaks around 6.5 GB RSS per Lean process.
# During a parallel Lake build several such processes create severe memory and GC pressure —
# one observed `PermutationInstantiation` build took 648 seconds despite compiling in about
# five seconds in isolation. PR #144 replaced every umbrella import with `Mathlib.Tactic` or
# narrower module imports.
#
# `import Mathlib.Tactic` is the same failure mode at smaller scale: it transitively pulls a
# large slice of Mathlib's theory (measured for issue #153 at roughly +1.6 s import-load time
# and +1.3 GB RSS per Lean process against the narrow tactic modules a file actually needs).
# It was the accepted broad-import compromise until issue #153 swept the last 83 uses; the
# sweep holds only if the umbrella cannot creep back in, since nothing else fails when it
# does — builds just quietly get slow again.
#
# The rule: no tracked `.lean` file may contain a bare `import Mathlib` or a bare
# `import Mathlib.Tactic` (with or without a trailing comment). Specific submodule imports
# such as `import Mathlib.Tactic.Ring` are fine. If an umbrella import is ever legitimately
# needed, extend this script with an explicit allowlist rather than deleting the check.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail

# One-or-more whitespace after `import` (not exactly one space), and optional
# `public`/`meta` modifiers, so spacing variants and module-system prefixes
# cannot slip a banned umbrella past the anchor.
violations=$(git ls-files '*.lean' | xargs grep -nE '^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+Mathlib(\.Tactic)?([[:space:]]|$)' || true)

if [ -n "$violations" ]; then
  echo "::error::bare 'import Mathlib' / 'import Mathlib.Tactic' umbrella imports are not allowed; import the specific Mathlib modules instead (see scripts/check_no_umbrella_imports.sh):"
  echo "$violations"
  exit 1
fi

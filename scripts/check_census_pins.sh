#!/usr/bin/env bash
# Check that every census file pins each declaration once.
#
# A `TrustBoundary.lean` (or any census module) records a declaration's axiom or
# computability footprint with one `assert_axioms` or `assert_computable` entry. A second
# entry for the same name checks nothing new, and a duplicated block is exactly what a
# careless copy or a census split leaves behind, so its presence usually means a stale or
# missing entry is hiding behind a passing build. `assert_computable` already checks the
# axiom footprint, so a definition pinned with it does not also get `assert_axioms`.
#
# The rule: within one file, a pinned name appears in at most one entry, whichever form.
# `Zcash/Meta/Tests/` is excluded because its census tests pin a name twice on purpose.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail

python3 - <<'PY'
import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path

paths = subprocess.check_output([
    "find", "Zcash", "-name", "*.lean", "-not", "-path", "Zcash/Meta/Tests/*", "-print0",
]).split(b"\0")
entry = re.compile(r"^assert_(axioms|computable)\s+(\S+)")
violations = []
for raw in sorted(set(paths) - {b""}):
    path = Path(os.fsdecode(raw))
    seen = defaultdict(list)
    for number, line in enumerate(path.read_text().splitlines(), 1):
        match = entry.match(line)
        if match:
            seen[match.group(2)].append((number, match.group(1)))
    for name, entries in seen.items():
        if len(entries) > 1:
            where = ", ".join(f"line {number} ({form})" for number, form in entries)
            violations.append(f"{path}: {name} pinned {len(entries)} times: {where}")
if violations:
    print("::error::a census file pins a declaration more than once; keep one entry per name, "
          "and only assert_computable where a definition has both forms "
          "(see scripts/check_census_pins.sh):")
    print("\n".join(violations))
    raise SystemExit(1)
PY

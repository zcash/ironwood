#!/usr/bin/env python3
"""Split the `assert_computable` pins into development and evaluation halves, and pin by role.

`split` enumerates every `assert_computable` pin outside test modules. It scans this repository
and each extra root, by default the CompElliptic package that lake checked out. In each file it
assigns half of the pins to the evaluation set with a seeded shuffle, and it writes one TSV row
per pin.

`apply` reads that TSV and pins one role with `assert_efficient`. By default (`--mode replace`)
it rewrites each pin as `assert_efficient <name> <flags>`; `assert_efficient` takes the same
flags and makes the same checks before its own. With `--mode add` it keeps the pin and inserts
`assert_efficient <name>` after it. `list` prints one role.

`apply` locates each pin by its name, so the TSV stays valid after lines move. In `add` mode it
is idempotent. In `replace` mode a pin already rewritten is no longer found, and is reported as
not located.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import random
import re
import subprocess
import sys

REPO = Path(__file__).resolve().parent.parent
# The split is tracked beside this script, so that the experiment is reproducible from a
# checkout; its header records the revisions it was drawn from.
SPLIT_FILE = REPO / "scripts" / "efficient-split.tsv"
DEFAULT_ROOTS = {
    "ironwood": REPO,
    "CompElliptic": REPO / ".lake" / "packages" / "CompElliptic",
}
SKIP_DIRS = {".lake", ".git", "work", "keep", "docbuild"}
# A pin under one of these directories, or in a module named `...Tests.lean`, exercises the pin
# machinery itself (`Zcash/Meta/Tests/`, CompElliptic's `MetaCheck/`) or is a regression-check
# module; the experiment is about the pins on the formalization proper.
TEST_DIR_NAMES = {"Tests", "MetaCheck"}
ROLES = ("development", "evaluation")
PIN_RE = re.compile(r"^(?P<indent>\s*)assert_computable\s+(?P<name>[^\s+]+)(?P<flags>.*)$")
COLUMNS = ("role", "root", "path", "line", "name", "flags")


@dataclass(frozen=True)
class Pin:
    root: str
    path: str  # relative to the root, with `/` separators
    line: int  # 1-based line of the pin command
    name: str
    flags: str  # the pin's flags, joined across lines, e.g. `+choice +native(A.b, C.d)`
    role: str = ""

    @property
    def key(self) -> tuple[str, str, int]:
        return (self.root, self.path, self.line)


def is_test_path(rel: Path) -> bool:
    return any(part in TEST_DIR_NAMES for part in rel.parts[:-1]) or rel.name.endswith("Tests.lean")


def lean_files(root: Path):
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root)
        if any(part in SKIP_DIRS for part in rel.parts):
            continue
        yield path, rel


def paren_balance(text: str) -> int:
    return text.count("(") - text.count(")")


def find_pins(lines: list[str]) -> list[tuple[int, str, str, int]]:
    """Each pin outside block comments: (first line index, name, flags, last line index), 0-based.

    Block comments nest in Lean, so a depth counter follows `/-` and `-/`; a prose line that
    happens to start with the keyword is also excluded by requiring a name after it.
    """
    pins = []
    depth = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if depth == 0:
            m = PIN_RE.match(line)
            if m:
                flags = m["flags"].strip()
                end = i
                balance = paren_balance(flags)
                while balance > 0 and end + 1 < len(lines):
                    end += 1
                    flags += " " + lines[end].strip()
                    balance += paren_balance(lines[end])
                pins.append((i, m["name"], " ".join(flags.split()), end))
                i = end + 1
                continue
        depth = max(0, depth + line.count("/-") - line.count("-/"))
        i += 1
    return pins


def scan_root(label: str, root: Path) -> tuple[list[Pin], dict[str, int]]:
    """The pins of one root outside test modules, and the per-file counts of the test pins."""
    pins: list[Pin] = []
    skipped: dict[str, int] = {}
    for path, rel in lean_files(root):
        found = find_pins(path.read_text(encoding="utf-8").splitlines())
        if not found:
            continue
        if is_test_path(rel):
            skipped[rel.as_posix()] = len(found)
            continue
        for start, name, flags, _end in found:
            pins.append(Pin(label, rel.as_posix(), start + 1, name, flags))
    return pins, skipped


def assign_roles(pins: list[Pin], fraction: float, seed: int) -> list[Pin]:
    """Per file, a seeded shuffle puts `fraction` of the pins in the evaluation set.

    The fractional part of `n * fraction` is rounded up with that probability, so single-pin
    files land in either set and the overall share stays unbiased.
    """
    rng = random.Random(seed)
    by_file: dict[tuple[str, str], list[Pin]] = {}
    for pin in sorted(pins, key=lambda p: p.key):
        by_file.setdefault((pin.root, pin.path), []).append(pin)
    out: list[Pin] = []
    for _key, group in sorted(by_file.items()):
        order = list(group)
        rng.shuffle(order)
        exact = len(order) * fraction
        k = int(exact)
        if rng.random() < exact - k:
            k += 1
        evaluation = {p.key for p in order[:k]}
        for pin in group:
            role = "evaluation" if pin.key in evaluation else "development"
            out.append(Pin(pin.root, pin.path, pin.line, pin.name, pin.flags, role))
    return out


def git_head(root: Path) -> str:
    try:
        out = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                             capture_output=True, text=True, check=True).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(root), "status", "--porcelain",
                                "--untracked-files=no"],
                               capture_output=True, text=True, check=True).stdout.strip()
        return out + (" (with uncommitted changes)" if dirty else "")
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def write_split(path: Path, pins: list[Pin], seed: int, fraction: float,
                roots: dict[str, Path]) -> None:
    with path.open("w", encoding="utf-8") as f:
        f.write(f"# assert_efficient experiment split: seed={seed} fraction={fraction}; "
                "generated by scripts/efficient_split.py\n")
        for label, root in sorted(roots.items()):
            if root.is_dir():
                f.write(f"# {label} at {git_head(root)}\n")
        f.write("\t".join(COLUMNS) + "\n")
        for pin in sorted(pins, key=lambda p: p.key):
            f.write(f"{pin.role}\t{pin.root}\t{pin.path}\t{pin.line}\t{pin.name}\t{pin.flags}\n")


def read_split(path: Path) -> list[Pin]:
    pins = []
    header = None
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw or raw.startswith("#"):
            continue
        if header is None:
            header = raw.split("\t")
            if tuple(header) != COLUMNS:
                sys.exit(f"{path}: unexpected columns {header}")
            continue
        fields = raw.split("\t")
        role, root, rel, line, name, flags = fields
        pins.append(Pin(root, rel, int(line), name, flags, role))
    return pins


def summarize(pins: list[Pin]) -> str:
    rows = []
    by_file: dict[tuple[str, str], list[Pin]] = {}
    for pin in pins:
        by_file.setdefault((pin.root, pin.path), []).append(pin)
    width = max(len(f"{root}:{rel}") for root, rel in by_file)
    rows.append(f"{'file':<{width}}  dev  eval")
    for (root, rel), group in sorted(by_file.items()):
        dev = sum(p.role == "development" for p in group)
        rows.append(f"{root + ':' + rel:<{width}}  {dev:>4} {len(group) - dev:>5}")
    dev = sum(p.role == "development" for p in pins)
    rows.append(f"{'total':<{width}}  {dev:>4} {len(pins) - dev:>5}")
    return "\n".join(rows)


def parse_roots(items: list[str] | None) -> dict[str, Path]:
    roots = dict(DEFAULT_ROOTS)
    for item in items or []:
        label, _, value = item.partition("=")
        if not value:
            sys.exit(f"--root takes LABEL=PATH, got {item!r}")
        roots[label] = Path(value).expanduser().resolve()
    return roots


def cmd_split(args: argparse.Namespace) -> int:
    roots = parse_roots(args.root)
    pins: list[Pin] = []
    for label, root in sorted(roots.items()):
        if not root.is_dir():
            print(f"skipping {label}: {root} is not a directory", file=sys.stderr)
            continue
        found, skipped = scan_root(label, root)
        pins.extend(found)
        for rel, n in sorted(skipped.items()):
            print(f"excluded as tests: {label}:{rel} ({n} pins)", file=sys.stderr)
    if not pins:
        sys.exit("no pins found")
    pins = assign_roles(pins, args.fraction, args.seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    write_split(args.out, pins, args.seed, args.fraction, roots)
    print(summarize(pins))
    print(f"wrote {args.out}")
    return 0


def locate(pin: Pin, pins_here: list[tuple[int, str, str, int]]) -> tuple[int, int]:
    """The (first, last) 0-based lines of the pin's command in the file as it is now."""
    at_line = [p for p in pins_here if p[0] == pin.line - 1 and p[1] == pin.name]
    if at_line:
        return at_line[0][0], at_line[0][3]
    by_name = [p for p in pins_here if p[1] == pin.name]
    if len(by_name) == 1:
        return by_name[0][0], by_name[0][3]
    if not by_name:
        raise LookupError(f"{pin.root}:{pin.path}: no `assert_computable {pin.name}` found")
    raise LookupError(f"{pin.root}:{pin.path}: `assert_computable {pin.name}` is pinned "
                      f"{len(by_name)} times and none is at line {pin.line}")


def cmd_apply(args: argparse.Namespace) -> int:
    roots = parse_roots(args.root)
    selected = [p for p in read_split(args.split)
                if p.role == args.role and (args.only is None or p.root == args.only)]
    by_file: dict[tuple[str, str], list[Pin]] = {}
    for pin in selected:
        by_file.setdefault((pin.root, pin.path), []).append(pin)
    added = skipped = 0
    failures = []
    for (label, rel), group in sorted(by_file.items()):
        if label not in roots:
            sys.exit(f"no root for {label}; pass --root {label}=PATH")
        path = roots[label] / rel
        lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        pins_here = find_pins([l.rstrip("\n") for l in lines])
        edits = []
        for pin in group:
            try:
                first, last = locate(pin, pins_here)
            except LookupError as e:
                failures.append(str(e))
                continue
            m = PIN_RE.match(lines[first])
            assert m is not None
            indent = m["indent"]
            if args.mode == "add":
                after = lines[last + 1].strip() if last + 1 < len(lines) else ""
                if after == f"assert_efficient {pin.name}":
                    skipped += 1
                    continue
                edits.append((last + 1, "insert", f"{indent}assert_efficient {pin.name}\n"))
            else:
                edits.append((first, "replace",
                              lines[first].replace("assert_computable", "assert_efficient", 1)))
            added += 1
        for index, kind, text in sorted(edits, reverse=True):
            if kind == "insert":
                lines.insert(index, text)
            else:
                lines[index] = text
        if edits and not args.dry_run:
            path.write_text("".join(lines), encoding="utf-8")
    verb = "would add" if args.dry_run else "added"
    if args.mode == "replace":
        verb = "would replace" if args.dry_run else "replaced"
    print(f"{verb} {added} pins for role {args.role}; {skipped} already present; "
          f"{len(failures)} not located")
    for failure in failures:
        print(f"  {failure}", file=sys.stderr)
    return 1 if failures else 0


def cmd_list(args: argparse.Namespace) -> int:
    for pin in read_split(args.split):
        if args.role in (None, pin.role):
            print(f"{pin.role}\t{pin.root}:{pin.path}:{pin.line}\t{pin.name}\t{pin.flags}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    parser.add_argument("--root", action="append", metavar="LABEL=PATH",
                        help="a root to scan or edit, overriding or adding to the defaults "
                             f"({', '.join(DEFAULT_ROOTS)})")
    sub = parser.add_subparsers(dest="command", required=True)

    p_split = sub.add_parser("split", help="enumerate the pins and assign roles")
    p_split.add_argument("--seed", type=int, default=20261014)
    p_split.add_argument("--fraction", type=float, default=0.5,
                         help="share of each file's pins in the evaluation set")
    p_split.add_argument("--out", type=Path, default=SPLIT_FILE)
    p_split.set_defaults(func=cmd_split)

    p_apply = sub.add_parser("apply", help="pin one role with assert_efficient")
    p_apply.add_argument("--split", type=Path, default=SPLIT_FILE)
    p_apply.add_argument("--role", choices=ROLES, required=True)
    p_apply.add_argument("--mode", choices=("add", "replace"), default="replace")
    p_apply.add_argument("--only", metavar="LABEL", help="apply to the pins of this root only")
    p_apply.add_argument("--dry-run", action="store_true")
    p_apply.set_defaults(func=cmd_apply)

    p_list = sub.add_parser("list", help="print the pins of one role, or all")
    p_list.add_argument("--split", type=Path, default=SPLIT_FILE)
    p_list.add_argument("--role", choices=ROLES)
    p_list.set_defaults(func=cmd_list)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())

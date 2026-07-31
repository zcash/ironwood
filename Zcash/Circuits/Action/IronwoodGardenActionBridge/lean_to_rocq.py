#!/usr/bin/env python3
"""Generate the Rocq ActionGarden translation from Lean parser syntax.

The companion ``actionGardenToIR`` executable asks Lean's own parser for a
complete syntax tree.  ``action_garden_rocq`` then accepts a closed subset of
that tree and emits every declaration body.  Unsupported or unconsumed syntax
fails before any destination is changed.
"""

from __future__ import annotations

import argparse
import difflib
import os
from pathlib import Path
import re
import sys
import tempfile

from action_garden_rocq import TranslationError, translate


FORBIDDEN_ROCQ = re.compile(
    r"^[ \t]*(?:Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|"
    r"Variable|Variables|Theorem|Lemma|Fact|Remark|Corollary)\b|"
    r"\b(?:Admitted|admit)\s*\.",
    re.MULTILINE,
)


def generated_pair(constants: str, main: str) -> str:
    return (
        "(* action_garden_constants.v *)\n"
        + constants
        + "\n(* action_garden_generated.v *)\n"
        + main
    )


def rendered_diff(source: str, constants: str, main: str) -> str:
    return "".join(
        difflib.unified_diff(
            source.splitlines(keepends=True),
            generated_pair(constants, main).splitlines(keepends=True),
            fromfile="ActionGarden.lean",
            tofile=(
                "action_garden_constants.v + action_garden_generated.v"
            ),
        )
    )


def validate_outputs(main: str, constants: str) -> None:
    for label, output in (("main", main), ("constants", constants)):
        forbidden = FORBIDDEN_ROCQ.search(output)
        if forbidden:
            raise TranslationError(
                f"unsupported Rocq proof shortcut in {label} output: "
                f"{forbidden.group(0).strip()}"
            )
    declarations = re.findall(
        r"^(?:Definition|Fixpoint|Inductive|Record)\s+"
        r"ActionGardenZ_[A-Za-z][A-Za-z0-9_]*\b",
        main,
        flags=re.MULTILINE,
    )
    if len(declarations) != 119:
        raise TranslationError(
            "internal emitter error: expected 119 generated main "
            f"declarations; found {len(declarations)}"
        )


def atomic_write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "w") as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def check_current(path: Path, expected: str) -> None:
    if not path.exists() or path.read_text() != expected:
        raise TranslationError(f"stale generated file: {path}")


def repository_root(source: Path) -> Path:
    for start in (source.resolve(), Path(__file__).resolve()):
        for candidate in (start, *start.parents):
            if (candidate / "lakefile.toml").is_file():
                return candidate
    raise TranslationError("cannot locate repository lakefile.toml")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--constants-output",
        type=Path,
        help=(
            "generated large-table file "
            "(default: action_garden_constants.v beside output)"
        ),
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail without writing when any generated artifact is stale",
    )
    parser.add_argument(
        "--diff",
        type=Path,
        help="also check or write the complete source-to-output diff",
    )
    args = parser.parse_args()

    constants_output = (
        args.constants_output
        or args.output.with_name("action_garden_constants.v")
    )
    repository = repository_root(args.input)

    # Render and validate all artifacts before checking or changing any path.
    main_output, constants, _, source = translate(args.input, repository)
    if args.input.read_text() != source:
        raise TranslationError(
            "ActionGarden source changed while it was being translated"
        )
    validate_outputs(main_output, constants)
    diff = rendered_diff(source, constants, main_output)

    if args.check:
        check_current(args.output, main_output)
        check_current(constants_output, constants)
        if args.diff is not None:
            check_current(args.diff, diff)
        return

    atomic_write(args.output, main_output)
    atomic_write(constants_output, constants)
    if args.diff is not None:
        atomic_write(args.diff, diff)


if __name__ == "__main__":
    try:
        main()
    except (BrokenPipeError, TranslationError) as error:
        if str(error):
            print(error, file=sys.stderr)
        sys.exit(1)

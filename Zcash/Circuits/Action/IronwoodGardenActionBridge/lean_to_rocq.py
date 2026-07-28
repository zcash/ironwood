#!/usr/bin/env python3
"""Generate and audit the Rocq mirror of the restricted ActionGarden source.

The Lean and Rocq concrete syntaxes differ most around records and structural
recursion, so the translation is maintained as a declaration-for-declaration
Rocq mirror (`ActionGarden.v.in`).  This tool makes that mirror mechanical and
fail-closed:

* comments are removed before checking the Lean subset;
* axioms, theorem dependencies, extra imports, notation, and type classes are
  rejected;
* every top-level Lean declaration must occur exactly once and in the same
  order in the Rocq mirror;
* proof shortcuts and extra Rocq declarations are rejected as well;
* both generated files are stamped with the exact Lean SHA-256;
* `--check` rejects either stale generated output;
* `--diff` writes the complete source-to-generated unified diff for review.

This is intentionally a small checked source mirror, not a general Lean parser.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
from pathlib import Path
import re
import sys


LEAN_DECLARATION = re.compile(
    r"^(?:abbrev|def|inductive|structure)\s+([A-Za-z][A-Za-z0-9_]*)\b",
    re.MULTILINE,
)
ROCQ_DECLARATION = re.compile(
    r"^(?:Definition|Fixpoint|Inductive|Record)\s+"
    r"([A-Za-z][A-Za-z0-9_]*)\b",
    re.MULTILINE,
)

DATA_BODY_MARKERS = {
    "@ORCHARD_POSEIDON_ROUND_CONSTANTS@": (
        "orchardPoseidonRoundConstants",
        "State3",
        64,
    ),
    "@ORCHARD_SINSEMILLA_GENERATORS@": (
        "orchardSinsemillaGenerators",
        "Point",
        1024,
    ),
}
FORBIDDEN_LEAN = re.compile(
    r"^(?:axiom|theorem|lemma|class|instance|opaque|noncomputable|"
    r"notation|macro|syntax)\b",
    re.MULTILINE,
)
FORBIDDEN_ROCQ = re.compile(
    r"^(?:Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|"
    r"Variable|Variables|Theorem|Lemma|Fact|Remark|Corollary)\b|"
    r"\b(?:Admitted|admit)\s*\.",
    re.MULTILINE,
)


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments."""
    out: list[str] = []
    depth = 0
    index = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            out.append("\n")
            index = newline + 1
        else:
            out.append(source[index])
            index += 1
    if depth:
        raise SystemExit("unterminated Lean block comment")
    return "".join(out)


def lean_declarations(source: str) -> list[str]:
    code = strip_lean_comments(source)
    imports = re.findall(r"^import\s+(.+)$", code, flags=re.MULTILINE)
    if imports != ["Init.Prelude"]:
        raise SystemExit(
            "standalone source must import exactly Init.Prelude; found "
            + repr(imports)
        )
    forbidden = FORBIDDEN_LEAN.search(code)
    if forbidden:
        raise SystemExit(
            f"unsupported Lean construct: {forbidden.group(0).strip()}"
        )
    if "namespace ActionGarden" not in code or "end ActionGarden" not in code:
        raise SystemExit("expected one ActionGarden namespace")
    declarations = LEAN_DECLARATION.findall(code)
    if not declarations:
        raise SystemExit("no Lean declarations found")
    duplicates = sorted(
        name for name in set(declarations) if declarations.count(name) != 1
    )
    if duplicates:
        raise SystemExit(f"duplicate Lean declarations: {duplicates}")
    return declarations


def lean_definition_body(source: str, name: str) -> str:
    """Extract one top-level `def` body, ending at the next declaration.

    The two large deployed tables deliberately use only constructor
    applications and integer literals.  Keeping their bodies in Lean and
    applying the tiny constructor-name map below avoids maintaining a second
    1,088-entry copy by hand.
    """
    declaration = re.search(
        rf"^def\s+{re.escape(name)}\b[\s\S]*?^\s*:=\s*",
        source,
        flags=re.MULTILINE,
    )
    if declaration is None:
        # The `:=` is on the declaration line in the current source.
        declaration = re.search(
            rf"^def\s+{re.escape(name)}\b[^\n]*:=\s*",
            source,
            flags=re.MULTILINE,
        )
    if declaration is None:
        raise SystemExit(f"cannot find Lean body for {name}")
    start = declaration.end()
    following = re.search(
        r"^(?:abbrev|def|structure)\s+[A-Za-z]",
        source[start:],
        flags=re.MULTILINE,
    )
    if following is None:
        raise SystemExit(f"cannot find declaration following {name}")
    body = source[start : start + following.start()]
    # Documentation for the following declaration belongs to neither body.
    comment = body.find("/-")
    if comment >= 0:
        body = body[:comment]
    return body.strip()


def expand_data_bodies(source: str, template: str) -> str:
    for marker, (name, constructor, expected_count) in DATA_BODY_MARKERS.items():
        if template.count(marker) != 1:
            raise SystemExit(f"template must contain {marker} exactly once")
        body = lean_definition_body(source, name)
        arity = 3 if constructor == "State3" else 2
        number = r"(-?[0-9]+)"
        arguments = r"\s+".join([number] * arity)
        rows = re.findall(
            rf"{constructor}\.mk\s+{arguments}",
            body,
        )
        if len(rows) != expected_count:
            raise SystemExit(
                f"expected {expected_count} {constructor} rows in {name}; "
                f"found {len(rows)}"
            )
        if constructor == "State3":
            rendered_rows = [
                "  Build_ActionGardenState3Data "
                f"{row[0]} {row[1]} {row[2]}"
                for row in rows
            ]
            default = "Build_ActionGardenState3Data 0 0 0"
        else:
            rendered_rows = [
                f"  Build_ActionGardenPointData {row[0]} {row[1]}"
                for row in rows
            ]
            default = "Build_ActionGardenPointData 0 0"
        rendered = (
            "[|\n"
            + ";\n".join(rendered_rows)
            + f"\n| {default} |]"
        )
        template = template.replace(marker, rendered)
    return template


def stamp_source_hash(source: str, template: str) -> str:
    source_hash = hashlib.sha256(source.encode()).hexdigest()
    marker = "@LEAN_SHA256@"
    if template.count(marker) != 1:
        raise SystemExit(f"template must contain {marker} exactly once")
    return template.replace(marker, source_hash)


def record_field_names(template: str) -> list[str]:
    fields: list[str] = []
    lines = template.splitlines(keepends=True)
    index = 0
    while index < len(lines):
        if not lines[index].startswith("Record "):
            index += 1
            continue
        block = lines[index]
        while "}." not in block:
            index += 1
            if index >= len(lines):
                raise SystemExit("unterminated Rocq Record in template")
            block += lines[index]
        body_start = block.find("{")
        body_end = block.rfind("}.")
        if body_start < 0 or body_end < 0:
            raise SystemExit("unsupported Rocq Record shape in template")
        body = block[body_start : body_end + 1]
        fields.extend(
            re.findall(r"(?:\{|;)\s*([A-Za-z][A-Za-z0-9_]*)\s*:", body)
        )
        index += 1
    return fields


def flatten_action_module(template: str) -> str:
    """Replace the Rocq module with a uniform textual namespace prefix.

    Packaging the explicit 1,088-row data dependency into a Rocq module causes
    module sealing to duplicate tens of gigabytes.  Top-level prefixed names
    give the same collision-free API and are also closer to the requested
    sed-like, auditable translation.
    """
    declaration_names = ROCQ_DECLARATION.findall(template)
    names = set(declaration_names + record_field_names(template))
    flattened = re.sub(
        r"^Module ActionGardenZ\.\n",
        "",
        template,
        flags=re.MULTILINE,
    )
    flattened = re.sub(
        r"^End ActionGardenZ\.\n?",
        "",
        flattened,
        flags=re.MULTILINE,
    )
    for name in sorted(names, key=len, reverse=True):
        flattened = re.sub(
            rf"(?<![A-Za-z0-9_.]){re.escape(name)}"
            rf"(?![A-Za-z0-9_]|\.[A-Za-z_])",
            f"ActionGardenZ_{name}",
            flattened,
        )
    point_record = re.compile(
        r"Record ActionGardenZ_Point : Type := \{\s*"
        r"ActionGardenZ_x : ActionGardenZ_Z;\s*"
        r"ActionGardenZ_y : ActionGardenZ_Z;\s*"
        r"\}\.",
        flags=re.MULTILINE,
    )
    flattened, count = point_record.subn(
        "Definition ActionGardenZ_Point : Type := ActionGardenPointData.",
        flattened,
    )
    if count != 1:
        raise SystemExit("expected exactly one flattened Point record")
    flattened = re.sub(
        r"\bActionGardenZ_x\b",
        "actionGardenPointX",
        flattened,
    )
    flattened = re.sub(
        r"\bActionGardenZ_y\b",
        "actionGardenPointY",
        flattened,
    )
    state_record = re.compile(
        r"Record ActionGardenZ_State3 : Type := \{\s*"
        r"ActionGardenZ_x0 : ActionGardenZ_Z;\s*"
        r"ActionGardenZ_x1 : ActionGardenZ_Z;\s*"
        r"ActionGardenZ_x2 : ActionGardenZ_Z;\s*"
        r"\}\.",
        flags=re.MULTILINE,
    )
    flattened, count = state_record.subn(
        "Definition ActionGardenZ_State3 : Type := ActionGardenState3Data.",
        flattened,
    )
    if count != 1:
        raise SystemExit("expected exactly one flattened State3 record")
    return flattened.rstrip() + "\n"


def render(source_path: Path, template_path: Path) -> str:
    source = source_path.read_text()
    template = template_path.read_text()
    lean_names = lean_declarations(source)
    forbidden_rocq = FORBIDDEN_ROCQ.search(template)
    if forbidden_rocq:
        raise SystemExit(
            "unsupported Rocq proof/declaration shortcut: "
            + forbidden_rocq.group(0).strip()
        )
    rocq_names = ROCQ_DECLARATION.findall(template)
    if lean_names != rocq_names:
        mismatch = "\n".join(
            difflib.unified_diff(
                [name + "\n" for name in lean_names],
                [name + "\n" for name in rocq_names],
                fromfile="Lean declarations",
                tofile="Rocq declarations",
            )
        )
        raise SystemExit("declaration inventory mismatch:\n" + mismatch)
    return stamp_source_hash(source, flatten_action_module(template))


def render_constants(source_path: Path, template_path: Path) -> str:
    source = source_path.read_text()
    template = expand_data_bodies(source, template_path.read_text())
    forbidden_rocq = FORBIDDEN_ROCQ.search(template)
    if forbidden_rocq:
        raise SystemExit(
            "unsupported Rocq proof/declaration shortcut in constants: "
            + forbidden_rocq.group(0).strip()
        )
    return stamp_source_hash(source, template)


def generated_pair(constants: str, main: str) -> str:
    return (
        "(* action_garden_constants.v *)\n"
        + constants
        + "\n(* action_garden_generated.v *)\n"
        + main
    )


def write_diff(
    source_path: Path, constants: str, rendered: str, diff_path: Path
) -> None:
    source_lines = source_path.read_text().splitlines(keepends=True)
    rendered_lines = generated_pair(constants, rendered).splitlines(keepends=True)
    diff = "".join(
        difflib.unified_diff(
            source_lines,
            rendered_lines,
            fromfile="ActionGarden.lean",
            tofile="action_garden_constants.v + action_garden_generated.v",
        )
    )
    diff_path.write_text(diff)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--template",
        type=Path,
        help="Rocq mirror template (default: ActionGarden.v.in beside input)",
    )
    parser.add_argument(
        "--constants-template",
        type=Path,
        help=(
            "large-table template "
            "(default: ActionGardenConstants.v.in beside input)"
        ),
    )
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
        help="fail instead of writing when output is stale",
    )
    parser.add_argument(
        "--diff",
        type=Path,
        help="also write the full Lean-to-Rocq unified diff",
    )
    args = parser.parse_args()
    template = args.template or args.input.with_name("ActionGarden.v.in")
    constants_template = (
        args.constants_template
        or args.input.with_name("ActionGardenConstants.v.in")
    )
    constants_output = (
        args.constants_output
        or args.output.with_name("action_garden_constants.v")
    )
    rendered = render(args.input, template)
    constants = render_constants(args.input, constants_template)
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale generated file: {args.output}")
        if (
            not constants_output.exists()
            or constants_output.read_text() != constants
        ):
            raise SystemExit(f"stale generated file: {constants_output}")
    else:
        args.output.write_text(rendered)
        constants_output.write_text(constants)
    if args.diff is not None:
        expected = "".join(
            difflib.unified_diff(
                args.input.read_text().splitlines(keepends=True),
                generated_pair(constants, rendered).splitlines(keepends=True),
                fromfile="ActionGarden.lean",
                tofile=(
                    "action_garden_constants.v + "
                    "action_garden_generated.v"
                ),
            )
        )
        if args.check:
            if not args.diff.exists() or args.diff.read_text() != expected:
                raise SystemExit(f"stale generated diff: {args.diff}")
        else:
            write_diff(args.input, constants, rendered, args.diff)


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        sys.exit(1)

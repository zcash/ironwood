#!/usr/bin/env python3
"""Render the pinned Post-NU6.3 verifying-key description into a Lean module.

`Zcash/Snark/Fixtures/circuit_description_post_nu6_3` is orchard's committed pinned key
description at the commit the captures regenerate from: the pretty (`{:#?}`) `Debug` rendering
of `VerifyingKey::pinned()`. What halo2 hashes into `transcript_repr` is the compact (`{:?}`)
rendering of the same value, so this script parses the pretty text as Rust's derived-`Debug`
value language and re-renders it compactly — `Name { f: v, g: w }`, `Name(a, b)`, `[a, b]`,
`(a, b)`, bare `Name` when there is nothing inside — into `PinnedKeyDescription.lean` as one
string literal. The Lean side hashes that string and checks the digest against every capture's
`capturedVkTranscriptRepr`, which is what pins this conversion: a rendering that differed from
halo2's by one byte would fail that theorem.

`--check` re-renders and diffs against the committed module (CI runs it on every event). Once the
exporter emits the compact text itself (`capturedPinnedKeyDescription`), this rendering retires.
Run from anywhere; exits non-zero on any violation.
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "Zcash/Snark/Fixtures/circuit_description_post_nu6_3")
TARGET = os.path.join(ROOT, "Zcash/Snark/Fixtures/PinnedKeyDescription.lean")


class Parser:
    """Rust derived-`Debug` values, whitespace-insensitive."""

    def __init__(self, text):
        self.t = text
        self.i = 0

    def ws(self):
        while self.i < len(self.t) and self.t[self.i] in " \n\r\t":
            self.i += 1

    def peek(self):
        self.ws()
        return self.t[self.i] if self.i < len(self.t) else ""

    def token(self):
        self.ws()
        j = self.i
        while self.i < len(self.t) and self.t[self.i] not in " \n\r\t,(){}[]:":
            self.i += 1
        return self.t[j:self.i]

    def string(self):
        j = self.i
        self.i += 1
        while self.t[self.i] != '"':
            if self.t[self.i] == "\\":
                self.i += 1
            self.i += 1
        self.i += 1
        return ("atom", self.t[j:self.i])

    def value(self):
        c = self.peek()
        if c == '"':
            return self.string()
        if c == "[":
            self.i += 1
            return ("list", self.seq("]"))
        if c == "(":
            self.i += 1
            return ("tuple", "", self.seq(")"))
        name = self.token()
        if not name:
            raise ValueError("expected a value at offset %d" % self.i)
        c = self.peek()
        if c == "{":
            self.i += 1
            fields = []
            while self.peek() != "}":
                f = self.token()
                if self.peek() != ":":
                    raise ValueError("expected ':' after field %r" % f)
                self.i += 1
                fields.append((f, self.value()))
                if self.peek() == ",":
                    self.i += 1
            self.i += 1
            return ("struct", name, fields)
        if c == "(":
            self.i += 1
            return ("tuple", name, self.seq(")"))
        return ("atom", name)

    def seq(self, close):
        xs = []
        while self.peek() != close:
            xs.append(self.value())
            if self.peek() == ",":
                self.i += 1
        self.i += 1
        return xs


def render(v):
    kind = v[0]
    if kind == "atom":
        return v[1]
    if kind == "list":
        return "[" + ", ".join(render(x) for x in v[1]) + "]"
    if kind == "tuple":
        name, xs = v[1], v[2]
        if not xs and name:
            return name
        return name + "(" + ", ".join(render(x) for x in xs) + ")"
    name, fields = v[1], v[2]
    if not fields:
        return name
    return name + " { " + ", ".join(f + ": " + render(x) for f, x in fields) + " }"


def lean_string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def rendered():
    with open(SOURCE, encoding="ascii") as f:
        pretty = f.read()
    if any(ord(c) < 0x20 and c not in "\n" for c in pretty):
        raise ValueError("the description must be printable ASCII")
    p = Parser(pretty)
    v = p.value()
    p.ws()
    if p.i != len(p.t):
        raise ValueError("trailing text after the description")
    compact = render(v)
    return (
        "-- Rendered from Zcash/Snark/Fixtures/circuit_description_post_nu6_3 by "
        "scripts/render-pinned-key-description.py. Do not edit by hand.\n"
        "\n"
        "/-!\n"
        "# The pinned Post-NU6.3 verifying-key description\n"
        "\n"
        "The compact `Debug` rendering of orchard's pinned Post-NU6.3 verifying key — the exact text\n"
        "halo2's `VerifyingKey::from_parts` hashes into `transcript_repr` — carried as Lean data.\n"
        "Rendered from the vendored pretty description at the pinned Orchard commit;\n"
        "`Fixtures/PinnedKey.lean` hashes it and reads its fields. CI re-renders this module from\n"
        "the vendored text and diffs it, so the two cannot drift apart.\n"
        "-/\n"
        "\n"
        "namespace Zcash.Snark.PinnedKey\n"
        "\n"
        "/-- The pinned key description, compact, exactly the `transcript_repr` preimage text. -/\n"
        "def pinnedKeyDescription : String :=\n"
        "  " + lean_string(compact) + "\n"
        "\n"
        "end Zcash.Snark.PinnedKey\n"
    )


def main():
    out = rendered()
    if len(sys.argv) > 1 and sys.argv[1] == "--check":
        if not os.path.exists(TARGET):
            print("VIOLATION: %s is missing; run scripts/render-pinned-key-description.py" % TARGET, file=sys.stderr)
            return 1
        with open(TARGET, encoding="utf-8") as f:
            committed = f.read()
        if committed != out:
            print("VIOLATION: %s is stale against %s; run scripts/render-pinned-key-description.py" % (TARGET, SOURCE), file=sys.stderr)
            return 1
        print("OK: %s matches %s." % (os.path.relpath(TARGET, ROOT), os.path.relpath(SOURCE, ROOT)))
        return 0
    with open(TARGET, "w", encoding="utf-8") as f:
        f.write(out)
    print("Rendered %s" % os.path.relpath(TARGET, ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main())

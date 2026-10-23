#!/usr/bin/env python3
"""Render pinned zcash-test-vectors data as a Lean module.

Usage:
  python3 -I scripts/test_vectors_to_lean.py <zcash-test-vectors checkout> <revision> <fixture>

Writes the Lean module of one fixture to stdout:

  poseidon    `test-vectors/json/orchard_poseidon.json`, `orchard_poseidon_hash.json`, and the
              round constants, MDS matrix and capacity element of the generator
              `zcash_test_vectors/orchard/poseidon.py`;
  generators  `test-vectors/json/orchard_generators.json`, the compressed point encodings.

Nothing from the checkout is imported or executed: the JSON is parsed with `json`, and the
generator's constants are read from its syntax tree with `ast`. Field elements in the JSON are
32-byte little-endian encodings; each is decoded to an integer and must be canonical (below the
Pallas base-field modulus), otherwise the script fails; so must the x-coordinate of each point
encoding.

`<revision>` is only recorded in the output; `regenerate-test-vectors.sh` checks that the
checkout is at that revision.
"""

import ast
import json
import os
import sys

PALLAS_P = 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001


def die(msg):
    sys.stderr.write(f"test_vectors_to_lean.py: {msg}\n")
    sys.exit(1)


def le_int(hexstr, what):
    """The integer a 32-byte hex string denotes little-endian."""
    try:
        raw = bytes.fromhex(hexstr)
    except (TypeError, ValueError):
        die(f"{what}: not a hex string: {hexstr!r}")
    if len(raw) != 32:
        die(f"{what}: expected 32 bytes, got {len(raw)}")
    return int.from_bytes(raw, "little")


def decode(hexstr, what):
    """A canonical field element."""
    n = le_int(hexstr, what)
    if n >= PALLAS_P:
        die(f"{what}: non-canonical encoding (>= p)")
    return n


def load_rows(path, header):
    with open(path) as f:
        rows = json.load(f)
    if len(rows) < 2 or rows[1] != [header]:
        die(f"{path}: unexpected header {rows[1] if len(rows) > 1 else None!r}")
    return rows[2:]


def pair(row, what):
    """A JSON row of exactly two fields, as `(first, second)`."""
    if not (isinstance(row, list) and len(row) == 2):
        die(f"{what}: expected two fields, got {row!r}")
    return row


def int_of(node, what):
    """Evaluate the integer literals the generator uses: `0x..`, `Fp(..)`, `1 << k`."""
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "Fp" \
            and len(node.args) == 1 and not node.keywords:
        return int_of(node.args[0], what)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return int_of(node.left, what) << int_of(node.right, what)
    die(f"{what}: unsupported expression {ast.dump(node)}")


def generator_constants(path):
    with open(path) as f:
        tree = ast.parse(f.read(), filename=path)
    assigns = {}
    for stmt in tree.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 \
                and isinstance(stmt.targets[0], ast.Name):
            assigns[stmt.targets[0].id] = stmt.value
    for name in ("R_F", "R_P", "t", "ROUND_CONSTANTS", "MDS_MATRIX", "CAPACITY_ELEMENT"):
        if name not in assigns:
            die(f"{path}: no top-level assignment to {name}")
    r_f, r_p, t = (int_of(assigns[n], n) for n in ("R_F", "R_P", "t"))
    # ROUND_CONSTANTS = [Fp(x) for x in chain.from_iterable([[..], [..], ...])]
    rc = assigns["ROUND_CONSTANTS"]
    it = rc.generators[0].iter if isinstance(rc, ast.ListComp) else None
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute)
            and isinstance(it.func.value, ast.Name) and it.func.value.id == "chain"
            and it.func.attr == "from_iterable"
            and len(it.args) == 1 and isinstance(it.args[0], ast.List)):
        die("ROUND_CONSTANTS: expected [Fp(x) for x in chain.from_iterable([...])]")
    round_constants = []
    for i, row in enumerate(it.args[0].elts):
        if not (isinstance(row, ast.List) and len(row.elts) == t):
            die(f"ROUND_CONSTANTS row {i}: expected {t} entries")
        round_constants.append([int_of(e, f"ROUND_CONSTANTS[{i}]") for e in row.elts])
    if len(round_constants) != r_f + r_p:
        die(f"ROUND_CONSTANTS: {len(round_constants)} rows, expected R_F + R_P = {r_f + r_p}")
    mds_node = assigns["MDS_MATRIX"]
    if not (isinstance(mds_node, ast.List) and len(mds_node.elts) == t):
        die("MDS_MATRIX: unexpected shape")
    mds = []
    for i, row in enumerate(mds_node.elts):
        if not (isinstance(row, ast.List) and len(row.elts) == t):
            die(f"MDS_MATRIX row {i}: unexpected shape")
        mds.append([int_of(e, f"MDS_MATRIX[{i}]") for e in row.elts])
    capacity = int_of(assigns["CAPACITY_ELEMENT"], "CAPACITY_ELEMENT")
    flat = [x for row in round_constants + mds for x in row] + [capacity]
    if any(v >= PALLAS_P for v in flat):
        die("generator constant not reduced mod p")
    return r_f, r_p, t, round_constants, mds, capacity


def hex64(n):
    return f"0x{n:064x}"


NAMESPACE = "Zcash.Circuits.Tests.TestVectors"


def module_header(rev, name, title, doc, imports=()):
    """The opening lines shared by every generated module: the converter's header (which
    `regenerate-test-vectors.sh` keys on), imports, the module docstring and the namespace."""
    out = ["-- Auto-generated by `scripts/regenerate-test-vectors.sh` from"
           f" zcash/zcash-test-vectors@{rev}. Do not edit by hand.", ""]
    out += [f"import {imp}" for imp in imports]
    if imports:
        out.append("")
    out += ["/-!", f"# zcash-test-vectors: {title}", ""] + doc + ["-/", ""]
    out += [f"namespace {NAMESPACE}.{name}", ""]
    return out


def render_poseidon(root, rev):
    perm_rows = load_rows(os.path.join(root, "test-vectors/json/orchard_poseidon.json"),
                          "initial_state, final_state")
    hash_rows = load_rows(os.path.join(root, "test-vectors/json/orchard_poseidon_hash.json"),
                          "input, output")
    r_f, r_p, t, rc, mds, capacity = generator_constants(
        os.path.join(root, "zcash_test_vectors/orchard/poseidon.py"))

    perm = []
    for i, row in enumerate(perm_rows):
        inp, out = pair(row, f"orchard_poseidon[{i}]")
        if len(inp) != 3 or len(out) != 3:
            die(f"orchard_poseidon[{i}]: expected width-3 states")
        perm.append(([decode(x, f"orchard_poseidon[{i}].initial_state") for x in inp],
                     [decode(x, f"orchard_poseidon[{i}].final_state") for x in out]))
    hashes = []
    for i, row in enumerate(hash_rows):
        inp, out = pair(row, f"orchard_poseidon_hash[{i}]")
        if len(inp) != 2:
            die(f"orchard_poseidon_hash[{i}]: expected two inputs")
        hashes.append(([decode(x, f"orchard_poseidon_hash[{i}].input") for x in inp],
                       decode(out, f"orchard_poseidon_hash[{i}].output")))

    out = module_header(rev, "OrchardPoseidon", "Orchard Poseidon", [
        "The `orchard_poseidon` and `orchard_poseidon_hash` vectors of",
        "[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors) at revision",
        f"`{rev}`, and the round constants, MDS matrix and capacity",
        "element of their generator `zcash_test_vectors/orchard/poseidon.py`.",
        "",
        "Each field element is the integer its 32-byte little-endian encoding denotes; the",
        "converter rejects a non-canonical encoding, and `OrchardPoseidon.data_canonical` proves",
        "every value here is below the Pallas base-field modulus.",
        "`scripts/regenerate-test-vectors.sh` regenerates this file byte-for-byte.",
    ], imports=["Zcash.Circuits.Poseidon.Constants"])
    w = out.append
    w("open Zcash.Circuits.Poseidon.Permute (State)")
    w("")
    w("/-- One `orchard_poseidon` vector: the permutation maps `input` to `output`. -/")
    w("structure PermutationVector where")
    w("  input : State Nat")
    w("  output : State Nat")
    w("")
    w("/-- One `orchard_poseidon_hash` vector: the two-input hash maps `(x, y)` to `output`. -/")
    w("structure HashVector where")
    w("  x : Nat")
    w("  y : Nat")
    w("  output : Nat")
    w("")
    w("/-- The generator's full-round count `R_F`. -/")
    w(f"def generatorFullRounds : Nat := {r_f}")
    w("")
    w("/-- The generator's partial-round count `R_P`. -/")
    w(f"def generatorPartialRounds : Nat := {r_p}")
    w("")
    w("/-- The generator's state width `t`. -/")
    w(f"def generatorWidth : Nat := {t}")
    w("")

    def state(row):
        return f"{{ x0 := {hex64(row[0])}, x1 := {hex64(row[1])}, x2 := {hex64(row[2])} }}"

    def items(name, typ, rows):
        w(f"def {name} : List {typ} := [")
        for i, row in enumerate(rows):
            w(f"  {row}{',' if i + 1 < len(rows) else ''}")
        w("]")
        w("")

    w(f"/-- The generator's `ROUND_CONSTANTS`, one row per round ({len(rc)} rows). -/")
    items("generatorRoundConstants", "(State Nat)", [state(r) for r in rc])
    w("/-- The generator's `MDS_MATRIX`, row by row. -/")
    items("generatorMds", "(List Nat)", ["[" + ", ".join(hex64(x) for x in r) + "]" for r in mds])
    w("/-- The generator's `CAPACITY_ELEMENT`, the capacity word of the two-input hash. -/")
    w(f"def generatorCapacity : Nat := {hex64(capacity)}")
    w("")
    w(f"/-- `orchard_poseidon.json` ({len(perm)} vectors). -/")
    items("permutationVectors", "PermutationVector",
          [f"{{ input := {state(a)},\n    output := {state(b)} }}" for a, b in perm])
    w(f"/-- `orchard_poseidon_hash.json` ({len(hashes)} vectors). -/")
    items("hashVectors", "HashVector",
          [f"{{ x := {hex64(a[0])}, y := {hex64(a[1])},\n    output := {hex64(b)} }}"
           for a, b in hashes])
    w(f"end {NAMESPACE}.OrchardPoseidon")
    return out


GENERATOR_COLUMNS = ["skb", "nkb", "vcvb", "vcrb", "cmb", "cmq", "ivkb", "ivkq", "mcq"]


def render_generators(root, rev):
    rows = load_rows(os.path.join(root, "test-vectors/json/orchard_generators.json"),
                     ", ".join(GENERATOR_COLUMNS))
    if len(rows) != 1 or len(rows[0]) != len(GENERATOR_COLUMNS):
        die(f"orchard_generators: expected one row of {len(GENERATOR_COLUMNS)} encodings")
    enc = []
    for name, hexstr in zip(GENERATOR_COLUMNS, rows[0]):
        n = le_int(hexstr, f"orchard_generators.{name}")
        if n % 2 ** 255 >= PALLAS_P:
            die(f"orchard_generators.{name}: non-canonical x-coordinate (>= p)")
        enc.append((name, n))

    out = module_header(rev, "OrchardGenerators", "Orchard generators", [
        "The `orchard_generators` vector of",
        "[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors) at revision",
        f"`{rev}`: the compressed encodings of the Orchard fixed bases and",
        "Sinsemilla domain points.",
        "",
        "Each encoding is the integer its 32 bytes denote little-endian: the x-coordinate in the",
        "low 255 bits and the parity of the y-coordinate in bit 255.",
        "`scripts/regenerate-test-vectors.sh` regenerates this file byte-for-byte.",
    ])
    w = out.append
    w("/-- The `orchard_generators` columns, each a compressed point encoding. -/")
    w("structure Encodings where")
    for name, _ in enc:
        w(f"  {name} : Nat")
    w("")
    w("/-- `orchard_generators.json` (one vector). -/")
    w("def generators : Encodings where")
    for name, n in enc:
        w(f"  {name} := {hex64(n)}")
    w("")
    w(f"end {NAMESPACE}.OrchardGenerators")
    return out


FIXTURES = {"poseidon": render_poseidon, "generators": render_generators}


def main():
    if len(sys.argv) != 4 or sys.argv[3] not in FIXTURES:
        die("usage: test_vectors_to_lean.py <zcash-test-vectors checkout> <revision> "
            f"<{'|'.join(FIXTURES)}>")
    root, rev, fixture = sys.argv[1:]
    sys.stdout.write("\n".join(FIXTURES[fixture](root, rev)) + "\n")


if __name__ == "__main__":
    main()

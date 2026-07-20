#!/usr/bin/env python3

import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


BOOK_DIR = Path(__file__).resolve().parent
REPO_DIR = BOOK_DIR.parent
FV_DIR = BOOK_DIR / "src" / "formal-verification"
SOURCE_CACHE = {}
FETCHED_SOURCES = set()


def fail(errors, message):
    errors.append(message)


def duplicates(items):
    return sorted(item for item, count in Counter(items).items() if count > 1)


def validate_graph(errors, map_text):
    node_ids = re.findall(r"\{ id:'([^']+)', c:\d+,r:\d+", map_text)
    edges = re.findall(
        r"\['([^']+)','([^']+)','([^']+)'(?:,'([^']*)')?\]",
        map_text,
    )
    node_set = set(node_ids)

    for node_id in duplicates(node_ids):
        fail(errors, f"duplicate map node: {node_id}")
    for source, target, kind, anchor in edges:
        if source not in node_set:
            fail(errors, f"edge source is not a map node: {source}")
        if target not in node_set:
            fail(errors, f"edge target is not a map node: {target}")
        if kind not in {"entails", "discharges", "rests", "gap"}:
            fail(errors, f"unknown edge kind: {kind}")
        if kind in {"entails", "discharges"} and not anchor:
            fail(errors, f"formal edge has no theorem anchor: {source} -> {target}")
        if kind in {"rests", "gap"} and anchor:
            fail(errors, f"assumption edge unexpectedly has a theorem anchor: {source} -> {target}")

    adjacency = {node_id: [] for node_id in node_ids}
    for source, target, _, _ in edges:
        if source in adjacency:
            adjacency[source].append(target)
    state = {}

    def visit(node_id, path):
        if state.get(node_id) == 1:
            fail(errors, "graph cycle: " + " -> ".join(path + [node_id]))
            return
        if state.get(node_id) == 2:
            return
        state[node_id] = 1
        for target in adjacency[node_id]:
            visit(target, path + [node_id])
        state[node_id] = 2

    for node_id in node_ids:
        visit(node_id, [])
    return node_set, len(edges)


def fetch_source_if_missing(source):
    source_ref = source["ref"]
    if source_ref in FETCHED_SOURCES:
        return
    FETCHED_SOURCES.add(source_ref)
    present = subprocess.run(
        ["git", "cat-file", "-e", f"{source_ref}^{{commit}}"],
        cwd=REPO_DIR,
        check=False,
        capture_output=True,
        text=True,
    )
    if present.returncode == 0:
        return
    subprocess.run(
        ["git", "fetch", "--no-tags", "--depth=100", "origin", source["fetch"]],
        cwd=REPO_DIR,
        check=False,
        capture_output=True,
        text=True,
    )


def source_text(errors, source, source_path):
    key = (source["ref"], source_path)
    if key in SOURCE_CACHE:
        return SOURCE_CACHE[key]
    fetch_source_if_missing(source)
    result = subprocess.run(
        ["git", "show", f"{source['ref']}:{source_path}"],
        cwd=REPO_DIR,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        fail(errors, f"source file is unavailable at {source['label']}: {source_path}")
        SOURCE_CACHE[key] = None
    else:
        SOURCE_CACHE[key] = result.stdout
    return SOURCE_CACHE[key]


def validate_timeline(errors, data, node_set):
    stages = data.get("stages", [])
    prs = data.get("prs", {})
    sources = data.get("sources", {})
    default_source = data.get("defaultSource")
    if not stages:
        fail(errors, "timeline has no stages")
    if default_source not in sources:
        fail(errors, "defaultSource does not name a pinned source")
    for source_id, source in sources.items():
        if not re.fullmatch(r"[0-9a-f]{40}", source.get("ref", "")):
            fail(errors, f"source {source_id} does not use a full pinned commit")
        if not source.get("fetch"):
            fail(errors, f"source {source_id} has no fetch ref")
    referenced_prs = set()

    required = {"id", "chapter", "title", "claim", "summary", "nodes", "theorems",
                "prs", "proves", "residuals", "durationMs"}
    stage_ids = [stage.get("id") for stage in stages]
    for stage_id in duplicates(stage_ids):
        fail(errors, f"duplicate stage: {stage_id}")
    covered = set()
    for stage in stages:
        stage_id = stage.get("id", "<missing>")
        missing = sorted(required - set(stage))
        if missing:
            fail(errors, f"{stage_id} missing fields: {', '.join(missing)}")
            continue
        if stage["durationMs"] <= 0:
            fail(errors, f"{stage_id} has a non-positive duration")
        if not stage["proves"] or not stage["residuals"]:
            fail(errors, f"{stage_id} must expose established and residual facts")
        for node_id in stage["nodes"]:
            covered.add(node_id)
            if node_id not in node_set:
                fail(errors, f"{stage_id} references unknown node: {node_id}")
        for node_id in duplicates(stage["nodes"]):
            fail(errors, f"{stage_id} repeats node: {node_id}")
        for theorem in stage["theorems"]:
            symbol = theorem.get("symbol", "")
            source_path = theorem.get("path", "")
            source_id = theorem.get("source", default_source)
            if not symbol or not source_path:
                fail(errors, f"{stage_id} has an incomplete theorem anchor")
            elif source_id not in sources:
                fail(errors, f"{stage_id} references unknown source: {source_id}")
            else:
                text = source_text(errors, sources[source_id], source_path)
                if text is not None and symbol not in text:
                    fail(errors, f"{stage_id} symbol not found in {source_path}: {symbol}")
        for pr_id in stage["prs"]:
            referenced_prs.add(pr_id)
            if pr_id not in prs:
                fail(errors, f"{stage_id} references unknown PR: {pr_id}")

    missing_nodes = sorted(node_set - covered)
    if missing_nodes:
        fail(errors, "timeline does not cover map nodes: " + ", ".join(missing_nodes))

    for pr_id, pr in prs.items():
        if pr_id not in referenced_prs:
            fail(errors, f"unreferenced PR metadata: {pr_id}")
        if not re.fullmatch(r"[0-9a-f]{7,40}", pr.get("sha", "")):
            fail(errors, f"PR {pr_id} has an invalid pinned SHA")
        if pr.get("lane") not in {"merged", "stack", "parallel"}:
            fail(errors, f"PR {pr_id} has an invalid lane")


def validate_capstone_ledger(errors, data):
    ledger = FV_DIR / "ledger.md"
    source = data["sources"][data["defaultSource"]]
    vesta_text = source_text(errors, source, "Zcash/Snark/Soundness/Vesta.lean")
    if vesta_text is None:
        return
    theorem_names = re.findall(
        r"^theorem (orchard_verifier_vesta_[A-Za-z0-9_]+)",
        vesta_text,
        flags=re.MULTILINE,
    )
    if len(theorem_names) != 36:
        fail(errors, f"expected 36 Vesta capstones, found {len(theorem_names)}")
    if not ledger.exists():
        return
    ledger_text = ledger.read_text(encoding="utf-8")
    for theorem_name in theorem_names:
        short_name = theorem_name.removeprefix("orchard_verifier_vesta_")
        if f"[`{short_name}`]" not in ledger_text:
            fail(errors, f"capstone missing from ledger: {theorem_name}")


def main():
    errors = []
    data_path = FV_DIR / "proof-journey-data.json"
    map_path = FV_DIR / "proof-map-embed.html"
    try:
        data = json.loads(data_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"proof journey data error: {error}", file=sys.stderr)
        return 1

    node_set, edge_count = validate_graph(errors, map_path.read_text(encoding="utf-8"))
    validate_timeline(errors, data, node_set)
    validate_capstone_ledger(errors, data)

    if errors:
        for error in errors:
            print(f"proof journey validation: {error}", file=sys.stderr)
        return 1
    stage_count = len(data["stages"])
    print(f"proof journey valid: {len(node_set)} nodes, {edge_count} edges, {stage_count} stages, 36 capstones")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

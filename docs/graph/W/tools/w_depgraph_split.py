#!/usr/bin/env python3
"""W copy (docs/graph/W/tools): draft globs accept any part-file prefix (w0-..., w1-...), not only p*.

Split a pre-extraction draft into per-slice packets (tracks I, N, P).

usage: inp_depgraph_split.py --draft DRAFT_DIR --slices PACKETS/slices.json --out PACKETS [--force]

slices.json maps each slice name to either
  {"ranges": [{"part": "p6", "lines": [1, 1000000000]}, {"part": "p7", "lines": [1, 259]}], ...}  (one or more ranges)
or {"part": "p1", "lines": [1, 498]}                                                                (track-K form)
or {"imports": true}                                                                                (imported nodes)
A node belongs to the slice whose range contains the first line of its STATEMENT_SOURCE (in the part file named by
that locator); a coverage item likewise by its SOURCE. Imported nodes (DRAFT/imports.md, coverage-imports.md) go to
the imports slice. Every block must land in exactly one slice. Writes PACKETS/<slice>.nodes.md and
<slice>.coverage.md (refusing to overwrite existing packets unless --force) and records node/coverage counts in
slices.json.
"""
import argparse
import json
import re
import sys
from pathlib import Path

LOC = re.compile(r"^(?P<path>[^#\s]+)#[^@\s]+@L(?P<x>\d+)-L(?P<y>\d+)$")


def blocks(text, key):
    return [b.strip("\n") for b in re.split(r"\n\s*\n(?=" + key + ": )", text.strip()) if b.strip()]


def field(b, k):
    m = re.search(r"^" + k + r": (.*)$", b, re.M)
    return m.group(1).strip() if m else ""


def part_of(path):
    m = re.match(r"(p\d+[a-z]?\d*)", Path(path).stem)
    return m.group(1) if m else Path(path).stem


def ranges_of(spec):
    if "ranges" in spec:
        return [(r["part"], r["lines"][0], r["lines"][1]) for r in spec["ranges"]]
    if "part" in spec:
        return [(spec["part"], spec["lines"][0], spec["lines"][1])]
    return []


ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
ap.add_argument("--draft", required=True)
ap.add_argument("--slices", required=True)
ap.add_argument("--out", required=True)
ap.add_argument("--force", action="store_true")
a = ap.parse_args()
draft, out = Path(a.draft), Path(a.out)
spec = json.loads(Path(a.slices).read_text())
imports_slice = [s for s, v in spec.items() if v.get("imports")]
assert len(imports_slice) <= 1, "at most one imports slice"


def slice_for(locator, what):
    m = LOC.match(locator)
    if not m:
        sys.exit(f"{what}: malformed locator {locator!r}")
    part, x = part_of(m.group("path")), int(m.group("x"))
    hits = [s for s, v in spec.items() for (p, lo, hi) in ranges_of(v) if p == part and lo <= x <= hi]
    if len(hits) != 1:
        sys.exit(f"{what}: locator {locator} lies in {len(hits)} slices {hits}")
    return hits[0]


nodes = {s: [] for s in spec}
cov = {s: [] for s in spec}
for f in sorted(x for x in draft.glob("*.md") if not x.name.startswith(("coverage-", "imports"))):
    for b in blocks(f.read_text(), "NODE"):
        nodes[slice_for(field(b, "STATEMENT_SOURCE"), field(b, "NODE"))].append(b)
for f in sorted(x for x in draft.glob("coverage-*.md") if x.name != "coverage-imports.md"):
    for b in blocks(f.read_text(), "ITEM"):
        cov[slice_for(field(b, "SOURCE"), field(b, "ITEM"))].append(b)
if imports_slice:
    s = imports_slice[0]
    if (draft / "imports.md").exists():
        nodes[s] += blocks((draft / "imports.md").read_text(), "NODE")
        cov[s] += blocks((draft / "coverage-imports.md").read_text(), "ITEM")
out.mkdir(parents=True, exist_ok=True)
for s in spec:
    for kind, data in (("nodes", nodes[s]), ("coverage", cov[s])):
        p = out / f"{s}.{kind}.md"
        if p.exists() and not a.force:
            sys.exit(f"{p} exists; pass --force to overwrite")
for s in spec:
    (out / f"{s}.nodes.md").write_text("\n\n".join(nodes[s]) + "\n")
    (out / f"{s}.coverage.md").write_text("\n\n".join(cov[s]) + "\n")
    spec[s]["nodes"], spec[s]["coverage"] = len(nodes[s]), len(cov[s])
    print(f"{s}: {len(nodes[s])} nodes, {len(cov[s])} coverage items")
Path(a.slices).write_text(json.dumps(spec, indent=1) + "\n")

#!/usr/bin/env python3
"""Apply a slice review's replacement fragments to the slice packet (track LP copy).

Copy of /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_apply_review.py with three fixes for the R1 small
slices (package LP-GRAPH-R1APPLY); the shared tool is unchanged.

usage: lp_depgraph_apply_review.py PACKETS_DIR SLICE REVIEW.md REVIEWER_TAG [--dry-run]

Behaviour of the shared tool, kept:
- Every complete `NODE:` block and `ITEM:` block in a fenced block of the review replaces the block with the same ID
  in `<SLICE>.nodes.md` / `<SLICE>.coverage.md`, or is appended if the ID is new.
- A replaced or added node gets `TOPOLOGY_STATUS: PROPOSED`, `REVIEWER: -`, `EXTRACTOR: <old base>+<REVIEWER_TAG>`;
  a replaced item gets `COVERAGE_STATUS: PROPOSED`, `REVIEWER: -`.
- FAIL rows without a replacement block are listed as unresolved.
- `<SLICE>.repaired.json` records {replaced, added, items, unresolved, passes}.

Fixes:
1. Empty `<SLICE>.nodes.md` or `<SLICE>.coverage.md` (LP-ext coverage, LP-amend and LP-m78 nodes) no longer crash
   (the shared tool calls `.group` on the match of an empty block). An empty file is written back empty.
2. A review with no node rows or no fences still writes `<SLICE>.repaired.json`, so the mark tool has its input.
3. A `NODE:` block whose ID belongs to ANOTHER slice of PACKETS_DIR is not appended to this slice (that would create a
   duplicate ID). It is listed under `cross_slice` {id: owner slice} in repaired.json and printed; the writer applies
   it in the owner slice (by hand, or by re-running this tool on the owner slice with a review file holding it).
The `passes` list is de-duplicated (order kept).
"""
import json
import re
import sys
from pathlib import Path

d, sl, review, tag = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3]), sys.argv[4]
dry = "--dry-run" in sys.argv
text = review.read_text()
fences = re.findall(r"^```[a-z]*\n(.*?)^```", text, re.M | re.S)


def split_blocks(t, key):
    return [b for b in re.split(r"\n\s*\n(?=" + key + r": )", t.strip()) if b.strip()]


new_nodes, new_items = {}, {}
for f in fences:
    for b in re.split(r"\n(?=NODE: )", f.strip()):
        if b.startswith("NODE: "):
            b = b.strip()
            new_nodes[re.match(r"NODE: (\S+)", b).group(1)] = b
    for b in re.split(r"\n(?=ITEM: )", f.strip()):
        if b.startswith("ITEM: "):
            b = re.split(r"\n\s*\n", b.strip())[0]
            new_items[re.match(r"ITEM: (\S+)", b).group(1)] = b
rows = re.findall(r"^\|\s*`?([^`|]+?)`?\s*\|(?:\s*(?:node|item|coverage)\s*\|)?\s*(PASS|FAIL)\s*\|(.*)$", text, re.M)
fails = {r[0].strip(): r[2] for r in rows if r[1] == "FAIL"}
passes = list(dict.fromkeys(r[0].strip() for r in rows if r[1] == "PASS"))

owner = {}
for p in sorted(d.glob("*.nodes.md")):
    s = p.name[: -len(".nodes.md")]
    if s == sl or ".draft-" in p.name:
        continue
    for b in split_blocks(p.read_text(), "NODE"):
        m = re.match(r"NODE: (\S+)", b)
        if m:
            owner[m.group(1)] = s

nodes_p, cov_p = d / f"{sl}.nodes.md", d / f"{sl}.coverage.md"
blocks = split_blocks(nodes_p.read_text(), "NODE")
ids = [re.match(r"NODE: (\S+)", b).group(1) for b in blocks]
replaced, added, cross = [], [], {}
for nid, b in new_nodes.items():
    if nid not in ids and nid in owner:
        cross[nid] = owner[nid]
        continue
    old = blocks[ids.index(nid)] if nid in ids else None
    old_ex = re.search(r"^EXTRACTOR: (.*)$", old, re.M).group(1) if old else "new"
    b = re.sub(r"^TOPOLOGY_STATUS: .*$", "TOPOLOGY_STATUS: PROPOSED", b, flags=re.M)
    b = re.sub(r"^REVIEWER: .*$", "REVIEWER: -", b, flags=re.M)
    b = re.sub(r"^EXTRACTOR: .*$", f"EXTRACTOR: {old_ex.split('+')[0]}+{tag}", b, flags=re.M)
    if nid in ids:
        blocks[ids.index(nid)] = b
        replaced.append(nid)
    else:
        blocks.append(b)
        ids.append(nid)
        added.append(nid)
cblocks = split_blocks(cov_p.read_text(), "ITEM")
cids = [re.match(r"ITEM: (\S+)", b).group(1) for b in cblocks]
items = []
for iid, b in new_items.items():
    b = re.sub(r"^REVIEWER: .*$", "REVIEWER: -", b, flags=re.M)
    b = re.sub(r"^COVERAGE_STATUS: .*$", "COVERAGE_STATUS: PROPOSED", b, flags=re.M)
    if iid in cids:
        cblocks[cids.index(iid)] = b
    else:
        cblocks.append(b)
        cids.append(iid)
    items.append(iid)
unresolved = {k: v.strip()[:200] for k, v in fails.items() if k not in new_nodes and k not in new_items}
out = dict(replaced=replaced, added=added, items=items, unresolved=unresolved, cross_slice=cross,
           passes=[p for p in passes if p in ids and p not in new_nodes])
if not dry:
    nodes_p.write_text("\n\n".join(blocks) + "\n" if blocks else "")
    cov_p.write_text("\n\n".join(cblocks) + "\n" if cblocks else "")
    (d / f"{sl}.repaired.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
print(f"{sl}: {len(replaced)} replaced, {len(added)} added, {len(items)} coverage items, "
      f"{len(unresolved)} unresolved FAILs, {len(cross)} cross-slice blocks, {len(out['passes'])} PASS nodes"
      + (" (dry run)" if dry else ""))
for k, v in unresolved.items():
    print(f"  UNRESOLVED {k}: {v}")
for k, v in cross.items():
    print(f"  CROSS-SLICE {k}: owned by {v}; not applied here")

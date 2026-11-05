#!/usr/bin/env python3
"""Mark the records a slice review PASSED as reviewed (track LP copy).

Copy of /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_mark_reviewed.py with two fixes for the R1 small
slices (package LP-GRAPH-R1APPLY); the shared tool is unchanged.

usage: lp_depgraph_mark_reviewed.py PACKETS_DIR SLICE REVIEW.md REVIEWER_TAG
- Nodes: every ID in <SLICE>.repaired.json "passes" (written by lp_depgraph_apply_review.py) whose EXTRACTOR does not
  contain REVIEWER_TAG gets TOPOLOGY_STATUS: REVIEWED and REVIEWER: REVIEWER_TAG.
- Coverage items: every review table row `| <item> | PASS | ...` whose item exists in <SLICE>.coverage.md and whose
  record was not replaced by the reviewer gets COVERAGE_STATUS: REVIEWED and REVIEWER: REVIEWER_TAG.
Records rewritten by the reviewer stay PROPOSED for a different (delta) reviewer.

Fixes:
1. A missing <SLICE>.repaired.json (node-less slice) means no node passes, instead of a crash.
2. Coverage items listed in repaired.json "items" (replaced by the reviewer) are never marked, even if a PASS row
   names them (the shared tool reads a non-existent key "items_ids" for this).
Deferred coverage (`<SLICE>.deferred-coverage.md`, DEFER-OK rows) is not touched, as in the shared tool.
"""
import json
import re
import sys
from pathlib import Path

d, sl, review, tag = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3]), sys.argv[4]
rp = d / f"{sl}.repaired.json"
rep = json.loads(rp.read_text()) if rp.exists() else {}
passes = set(rep.get("passes", rep.get("pass", [])))
replaced_items = set(rep.get("items", []))


def mark(path, key, ids, status_field):
    text = path.read_text()
    blocks = re.split(r"(?m)^(?=" + key + r": )", text)
    n = 0
    out = []
    for b in blocks:
        m = re.match(key + r": (\S+)", b)
        ex = re.search(r"(?m)^EXTRACTOR: (.*)$", b)
        if m and m.group(1) in ids and tag not in (ex.group(1) if ex else ""):
            b2 = re.sub(r"(?m)^" + status_field + r": .*$", f"{status_field}: REVIEWED", b)
            b2 = re.sub(r"(?m)^REVIEWER: .*$", f"REVIEWER: {tag}", b2)
            n += b2 != b
            b = b2
        out.append(b)
    path.write_text("".join(out))
    return n


nn = mark(d / f"{sl}.nodes.md", "NODE", passes, "TOPOLOGY_STATUS")
rows = re.findall(r"(?m)^\|\s*`?([^|`]+?)`?\s*\|\s*PASS\s*\|", review.read_text())
cov_ids = set(r.strip() for r in rows) - replaced_items
ci = mark(d / f"{sl}.coverage.md", "ITEM", cov_ids, "COVERAGE_STATUS")
print(f"{sl}: {nn} nodes and {ci} coverage items marked REVIEWED by {tag}")

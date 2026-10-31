#!/usr/bin/env python3
"""Mark the coverage items a slice review passed wholesale ("all other coverage items PASS") as REVIEWED (track W).

usage: w_depgraph_mark_coverage_rest.py PACKETS_DIR SLICE REVIEW.md REVIEWER_TAG
inp_depgraph_mark_reviewed.py marks only coverage items with an explicit `| item | PASS |` row. Reviews that state
"all other coverage items PASS" pass the remaining items without rows. This tool marks every coverage item of the
slice that is still PROPOSED, has no FAIL row in the review, was not replaced by the review (<SLICE>.repaired.json
"items"), and whose EXTRACTOR does not contain REVIEWER_TAG. It refuses if the review lacks the phrase.
"""
import json, re, sys
from pathlib import Path
d, sl, review, tag = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3]), sys.argv[4]
text = review.read_text()
if not re.search(r"all other coverage items PASS", text, re.I):
    sys.exit(f"{review}: no 'all other coverage items PASS' statement; nothing marked")
fails = {r.strip() for r in re.findall(r"(?m)^\|\s*`?([^|`]+?)`?\s*\|\s*FAIL\s*\|", text)}
rep = json.loads((d / f"{sl}.repaired.json").read_text())
replaced = set(rep.get("items", []))
p = d / f"{sl}.coverage.md"
blocks = re.split(r"(?m)^(?=ITEM: )", p.read_text())
n = 0
out = []
for b in blocks:
    m = re.match(r"ITEM: (\S+)", b)
    if m and m.group(1) not in fails and m.group(1) not in replaced and "COVERAGE_STATUS: PROPOSED" in b \
            and tag not in (re.search(r"(?m)^EXTRACTOR: (.*)$", b) or [None, ""])[1]:
        b = re.sub(r"(?m)^COVERAGE_STATUS: .*$", "COVERAGE_STATUS: REVIEWED", b)
        b = re.sub(r"(?m)^REVIEWER: .*$", f"REVIEWER: {tag}", b)
        n += 1
    out.append(b)
p.write_text("".join(out))
print(f"{sl}: {n} further coverage items marked REVIEWED by {tag} ('all other coverage items PASS')")

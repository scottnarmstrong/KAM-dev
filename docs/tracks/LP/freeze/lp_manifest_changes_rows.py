#!/usr/bin/env python3
"""S7 (RUNBOOK §3, §7): the docs/MANIFEST-CHANGES.md rows of the LP freeze and seal (D62), one per new entry.

usage: lp_manifest_changes_rows.py --root <tree> --plan rebase-plan.json [--append]

Each row: date, decision, "Froze and sealed" with id, export, path and (theorems) the sealed body read from the
installed file between the markers, and the provider / closing theorem; the evidence column cites the checks of
docs/tracks/LP/FREEZE.md. Prints the rows; --append adds them to docs/MANIFEST-CHANGES.md (refusing if any LP row is
already present).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402

DEC = ("D62 (owner: \"approve draft 7\", 2026-11-01; freeze and seals); D59 (rulings); D26 (procedure); "
       "one pass as track R")
EVID = ("byte identity with the approved draft at `inp-lp-freeze7`@de343000 modulo `<APPROVAL-DATE>`/`<DECISION>` "
        "and the proof body (`lp_identity_check.py`: ALL IDENTICAL, `docs/tracks/LP/freeze/identity-check.txt`); "
        "hashes by the guard's own code (`lp_manifest_add.py`); ABI by `abi_hashes.py` (two identical runs); "
        "FROZEN-ANCHOR GUARD OK; lint; `#print axioms` and provider type probe (`lp_axioms.py`); leanchecker replay "
        "of `docs/tracks/LP/freeze/replay-modules.txt`; statement audits STATEMENT-AUDIT-DRAFT7-1 (RETURN), -2 (PASS "
        "WITH NOTES); seal audit pending (`docs/tracks/LP/audits/LP-SEAL-audit-1.md`); `docs/tracks/LP/FREEZE.md`")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--plan", required=True)
    ap.add_argument("--append", action="store_true")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    guard = L.load_guard(root)
    plan = json.loads(Path(a.plan).read_text())
    moved = {c["export"]: c for c in plan["characterizations"]}
    m = json.loads((root / "manifest/frozen-anchors.json").read_text())
    rows = []
    for e in m["anchors"]:
        if not e["id"].startswith("planetary.d59."):
            continue
        if e["kind"] == "definition":
            change = (f"Froze and sealed `{e['id']}` (definition `{e['export']}`, `{e['path']}`), state SEALED "
                      f"(whole-file). No existing entry changed")
        else:
            text = (root / e["path"]).read_text()
            _pre, body, _suf = L.split_theorem(guard, root, text)
            b = " ".join(body.split())
            how = (f"proof of the former implementation lemma moved verbatim from `{moved[e['export']]['module']}`"
                   + (" (sibling inlined)" if moved[e["export"]]["sibling"] else "")) if e["export"] in moved \
                else "one-line application of the closing implementation theorem (FREEZE-PROPOSAL §2)"
            change = (f"Froze and sealed `{e['id']}` (theorem `{e['export']}`, `{e['path']}`): body `{b}`; state "
                      f"SEALED. Provider `{e['implementation']['module']}`: {how}. No existing entry changed")
        rows.append(f"| 2026-11-01 | {DEC} | {change} | n/a (new entry) | {EVID} |")
    print("\n".join(rows))
    if a.append:
        mc = root / "docs/MANIFEST-CHANGES.md"
        t = mc.read_text()
        assert "planetary.d59." not in t, "LP rows already present"
        mc.write_text(t.rstrip("\n") + "\n" + "\n".join(rows) + "\n")
        print(f"appended {len(rows)} rows to {mc}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

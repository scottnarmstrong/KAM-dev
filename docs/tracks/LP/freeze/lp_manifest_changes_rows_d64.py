#!/usr/bin/env python3
"""The docs/MANIFEST-CHANGES.md rows of the LP3 freeze and seal (draft 8, D64), one per new entry.

usage: lp_manifest_changes_rows_d64.py --root <tree> --approved <sha>:<draft dir> [--append]

The D64 counterpart of lp_manifest_changes_rows.py (whose decision/evidence text and `planetary.d59.` filter are
D62's): the rows cover exactly the entry ids of the approved draft-8 `manifest-entries.json`, in the D62 row format.
The sealed body is read from the installed file between the markers (split by the guard's own code). --append adds
the rows to docs/MANIFEST-CHANGES.md, refusing if any of these ids already has a row.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402

DEC = ("D64 (owner: \"approve draft 8\", 2026-11-01; freeze and seals, one pass as D62); D59 (rulings); "
       "D26 (procedure)")
EVID = ("byte identity with the approved draft at `inp-lp-freeze8r`@6c168945 modulo `<APPROVAL-DATE>`/`<DECISION>` "
        "and the proof body (`lp_identity_check.py`: ALL IDENTICAL, `docs/tracks/LP/freeze/identity-check-d64.txt`); "
        "hashes by the guard's own code (`lp_manifest_add.py`, `approval-D64.json`); ABI by `abi_hashes.py` (two "
        "identical runs, `abi-check-d64.txt`); FROZEN-ANCHOR GUARD OK; lint; `#print axioms` and provider type probe "
        "(`seal-probe-verify-d64.txt`); leanchecker replay of `docs/tracks/LP/freeze/replay-modules-d64.txt`; "
        "statement audit STATEMENT-AUDIT-DRAFT8-1 (PASS WITH NOTES); dedicated seal audit pending; "
        "`docs/tracks/LP/FREEZE.md` (D64 section)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--approved", required=True)
    ap.add_argument("--append", action="store_true")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    guard = L.load_guard(root)
    ids = [e["id"] for e in L.approved_entries(root, a.approved)]
    m = {e["id"]: e for e in json.loads((root / "manifest/frozen-anchors.json").read_text())["anchors"]}
    rows = []
    for i in ids:
        e = m[i]
        assert e["kind"] == "theorem" and e["state"] == "SEALED", i
        _pre, body, _suf = L.split_theorem(guard, root, (root / e["path"]).read_text())
        b = " ".join(body.split())
        change = (f"Froze and sealed `{e['id']}` (theorem `{e['export']}`, `{e['path']}`): body `{b}`; state SEALED. "
                  f"Provider `{e['implementation']['module']}`: one-line application of the closing implementation "
                  f"theorem (FREEZE-PROPOSAL-DRAFT8 §6). No existing entry changed")
        rows.append(f"| 2026-11-01 | {DEC} | {change} | n/a (new entry) | {EVID} |")
    print("\n".join(rows))
    if a.append:
        mc = root / "docs/MANIFEST-CHANGES.md"
        t = mc.read_text()
        assert not any(f"`{i}`" in t for i in ids), "D64 rows already present"
        mc.write_text(t.rstrip("\n") + "\n" + "\n".join(rows) + "\n")
        print(f"appended {len(rows)} rows to {mc}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

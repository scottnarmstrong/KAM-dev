#!/usr/bin/env python3
"""S4 (RUNBOOK §7): byte identity of every installed LP frozen file with its approved draft.

usage: lp_identity_check.py --root <tree> --approved <sha>:<draft dir> --date <YYYY-MM-DD> --decision <Dnn>
                            [--kind definition|theorem|all] [--pin] [--show-diff]

For each manifest-entry draft: the installed file must equal the approved draft with exactly the two placeholders
filled. For a theorem the proof body between the markers (split by the guard's own `check_theorem_region`) is
replaced by the draft's body (`  by sorry`) first, so a sealed file is checked the same way. Additionally the
line diff draft -> installed is computed and must consist only of the lines carrying the two placeholders (and,
for a sealed theorem, the body lines). Prints IDENTICAL/DIFFERS per file and `ALL IDENTICAL` (exit 0) or
`MISMATCH` (exit 1). `--pin` prints the sha256 of every approved draft file and of manifest-entries.json (P4).
"""
from __future__ import annotations

import argparse
import difflib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--approved", required=True, action="append")
    ap.add_argument("--date", required=True)
    ap.add_argument("--decision", required=True)
    ap.add_argument("--kind", default="all", choices=["definition", "theorem", "all"])
    ap.add_argument("--pin", action="store_true")
    ap.add_argument("--show-diff", action="store_true")
    ap.add_argument("--repo", help="git repository holding the approved commit (default: --root)")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    repo = Path(a.repo).resolve() if a.repo else root
    guard = L.load_guard(repo)
    ok, n = True, 0
    for spec in a.approved:
        sha, d = L.parse_approved(spec)
        if a.pin:
            for e in L.approved_entries(repo, spec):
                print(f"{L.digest(guard, L.git_show(repo, sha, d + '/' + e['path'] + '.txt'))}  {d}/{e['path']}.txt")
            print(f"{L.digest(guard, L.git_show(repo, sha, d + '/manifest-entries.json'))}  {d}/manifest-entries.json")
        for e in L.approved_entries(repo, spec):
            if a.kind != "all" and e["kind"] != a.kind:
                continue
            n += 1
            draft = L.approved_text(repo, spec, e["path"])
            p = root / e["path"]
            if not p.is_file():
                print(f"MISSING    {e['path']}")
                ok = False
                continue
            inst = p.read_bytes().decode("utf-8")
            expect = L.fill(draft, a.date, a.decision)
            if e["kind"] == "theorem":
                ip, ib, isuf = L.split_theorem(guard, repo, inst)
                dp, db, dsuf = L.split_theorem(guard, repo, draft)
                assert db == "  by sorry\n", (e["path"], db)
                cmp = ip + db + isuf
                body = "sorry" if ib == db else "sealed"
            else:
                cmp, body = inst, "-"
            good = cmp == expect
            # independent line-level evidence: only placeholder lines (and a sealed body) differ
            dl = [l for l in difflib.unified_diff(draft.splitlines(), inst.splitlines(), lineterm="", n=0)
                  if l[:1] in "+-" and not l.startswith(("+++", "---"))]
            olds = [l[1:] for l in dl if l.startswith("-")]
            news = [l[1:] for l in dl if l.startswith("+")]
            allowed_old = [l for l in olds if any(ph in l for ph in L.PLACEHOLDERS)]
            body_old = [l for l in olds if l not in allowed_old]
            if e["kind"] == "theorem" and body == "sealed":
                good &= body_old == ["  by sorry"]
            else:
                good &= not body_old
            good &= len(news) == len(olds) or body == "sealed"
            ok &= good
            print(f"{'IDENTICAL ' if good else 'DIFFERS   '} {e['path']}  (body: {body}; changed lines: "
                  f"{len(allowed_old)} placeholder line(s))")
            if a.show_diff or not good:
                for l in dl:
                    print("    " + l)
    print(f"{n} files checked")
    print("ALL IDENTICAL" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

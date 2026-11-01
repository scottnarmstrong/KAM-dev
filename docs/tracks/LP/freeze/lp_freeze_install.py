#!/usr/bin/env python3
"""S1 (RUNBOOK §7): install approved LP frozen files from the approved draft texts.

usage: lp_freeze_install.py --root <worktree> --approved <sha>:<draft dir> --date <YYYY-MM-DD> --decision <Dnn>
                            --kind definition|theorem [--out <scratch dir>]

For every manifest-entry draft of the requested kind, writes `<path>` = the approved `<path>.txt` with only
`<APPROVAL-DATE>` and `<DECISION>` filled (each exactly once; the result differs from the draft in exactly those
two substrings). For theorems it also writes the quarantined provider stub at `implementation.module` (template:
`KAM/Provider/Wave/Nlw2.lean` at d7aae35d). Refuses to overwrite an existing file. `--out` redirects every write to
a scratch tree (dry run). Prints the installed frozen modules in import order (for `lp_build.sh`).
"""
from __future__ import annotations

import argparse
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
    ap.add_argument("--kind", required=True, choices=["definition", "theorem"])
    ap.add_argument("--out")
    ap.add_argument("--sealed", action="store_true",
                    help="theorems: install with the sealed body `by exact <provider export> <explicit binders>` "
                         "(froze and sealed in one pass, as track R; D62) and no provider stub")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    out = Path(a.out).resolve() if a.out else root
    written, entries, texts = [], [], {}
    guard = L.load_guard(root)
    for spec in a.approved:
        for e in L.approved_entries(root, spec):
            if e["kind"] != a.kind:
                continue
            draft = L.approved_text(root, spec, e["path"])
            text = L.fill(draft, a.date, a.decision)
            assert _only_placeholders(draft, text, a.date, a.decision), e["path"]
            if a.kind == "theorem" and a.sealed:
                pre, body, suf = L.split_theorem(guard, root, text)
                assert body == "  by sorry\n", e["path"]
                binders = L.explicit_binders(guard, root, pre)
                sealed = L.seal_body(e["implementation"]["export"], binders)
                doc = L.docstring_seal(text)
                assert doc == " ".join(sealed.split()), (e["path"], doc, sealed)
                assert sealed.count("\n") <= 3 and len(sealed.encode()) <= 240, e["path"]
                assert max(len(l) for l in sealed.split("\n")) <= 100, e["path"]
                text = pre + sealed + suf
            dest = out / e["path"]
            if dest.exists() or (root / e["path"]).exists():
                raise SystemExit(f"refusing to overwrite {e['path']}")
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(text, encoding="utf-8")
            written.append(e["path"])
            entries.append(e)
            texts[e["path"]] = text
            if a.kind == "theorem" and not a.sealed:
                imp = e["implementation"]
                rel = imp["module"].replace(".", "/") + ".lean"
                pdest = out / rel
                if pdest.exists() or (root / rel).exists():
                    raise SystemExit(f"refusing to overwrite provider {rel}")
                pdest.parent.mkdir(parents=True, exist_ok=True)
                pdest.write_text(L.provider_stub(e["export"], imp["export"], L.COPYRIGHT), encoding="utf-8")
                written.append(rel)
    stubs = a.kind == "theorem" and not a.sealed
    print(f"installed {len(entries)} {a.kind} files" + (" (sealed bodies)" if a.sealed else "")
          + (f" and {len(entries)} provider stubs" if stubs else "") + f" into {out}")
    print("modules in import order:")
    for m in L.frozen_import_order(entries, texts):
        print("  " + m)
    return 0


def _only_placeholders(draft: str, text: str, date: str, decision: str) -> bool:
    i, j = draft.index("<APPROVAL-DATE>"), draft.index("<DECISION>")
    first, second = sorted([(i, "<APPROVAL-DATE>", date), (j, "<DECISION>", decision)])
    expect = (draft[:first[0]] + first[2] + draft[first[0] + len(first[1]):second[0]] + second[2]
              + draft[second[0] + len(second[1]):])
    return expect == text


if __name__ == "__main__":
    raise SystemExit(main())

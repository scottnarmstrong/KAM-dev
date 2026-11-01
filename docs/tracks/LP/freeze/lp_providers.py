#!/usr/bin/env python3
"""LP providers at freeze (D62; FREEZE-PROPOSAL §2 and §7 points 3-4; RUNBOOK (d).1).

usage: lp_providers.py --root <worktree> --staged <sha> --plan rebase-plan.json --moved <moved-proofs.json>
                       [--out <scratch>]

* The 5 anchor providers are copied byte for byte from the staging branch commit `--staged` (inp-lp-providers,
  f2fa9f88): one-line applications of the closing implementation theorems, which stay in the implementation.
* The 34 characterization providers take the staged file (same header, imports, namespace, opens and the anchor's
  exact statement text) and replace the one-line proof by the implementation lemma's proof moved verbatim
  (`lp_rebase.py --phase characterizations` deletes the lemma from the implementation; the frozen theorem has the
  lemma's fully qualified name, so both cannot coexist). The two proofs that use a sibling characterization
  (`sourceOscPeri_pos`, `orderedStrongThreshold_isLeast`) get the sibling's statement and proof verbatim as a
  `private theorem` of the same name in the provider (no provider-to-provider and no frozen-theorem import). An
  import of a deleted implementation module is replaced by that module's own imports.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402

PARA_OLD = re.compile(r"\nThe theorem `[^`]+` states\sthe\sanchor's\sexact\stype\s.*?\(AGENTS\srule\s9\)\.\n", re.S)


def statement_of(provider_text: str, name: str) -> tuple[int, int]:
    """Span [start, end) of `theorem <name> ... :=` up to and excluding the proof in a staged provider."""
    s = provider_text.index(f"\ntheorem {name} ") + 1
    e = provider_text.index(" := by\n  exact _root_.", s)
    return s, e


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--staged", required=True)
    ap.add_argument("--plan", required=True)
    ap.add_argument("--moved", required=True)
    ap.add_argument("--approved", default="de343000:docs/tracks/LP/freeze/draft7")
    ap.add_argument("--out")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    out = Path(a.out).resolve() if a.out else root
    plan = json.loads(Path(a.plan).read_text())
    moved = json.loads(Path(a.moved).read_text())
    chars = {c["export"]: c for c in plan["characterizations"]}
    deleted = set(plan["delete_modules"])
    n = 0
    for e in L.approved_entries(root, a.approved):
        if e["kind"] != "theorem":
            continue
        rel = e["implementation"]["module"].replace(".", "/") + ".lean"
        staged = L.git_show(root, a.staged, rel).decode()
        dest = out / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        if e["export"] not in chars:
            dest.write_text(staged)
            n += 1
            print(f"anchor provider (staged copy)  {rel}")
            continue
        c = chars[e["export"]]
        name = c["name"]
        s, t = statement_of(staged, name)
        stmt = staged[s:t]
        proof = moved[e["export"]]["proof"]
        helper = ""
        if c["sibling"]:
            sib = c["sibling"]
            sname = sib.split(".")[-1]
            srel = chars[sib]["provider_module"].replace(".", "/") + ".lean"
            sstaged = L.git_show(root, a.staged, srel).decode()
            ss, st = statement_of(sstaged, sname)
            sst = "private " + sstaged[ss:st]
            first, _, rest = sst.partition("\n")
            if len(first) > 100:  # whitespace only: re-break the first line at the last binder boundary
                cut = max(m.start() for m in re.finditer(r" [({]", first[:101]))
                first = first[:cut] + "\n    " + first[cut + 1:]
                first, more = first.split("\n", 1)
                if rest.startswith("    ") and len(more) + 1 + len(rest.split("\n", 1)[0].strip()) <= 100:
                    head, _, tail = rest.partition("\n")
                    rest = more + " " + head.strip() + ("\n" + tail if tail else "")
                else:
                    rest = more + "\n" + rest
            sst = first + "\n" + rest
            helper = ("/-- The sibling characterization, inlined verbatim (FREEZE-PROPOSAL §7 point 3). -/\n"
                      + sst + " :=" + moved[sib]["proof"] + "\n\n")
        text = staged[:s] + helper + stmt + " :=" + proof + staged[staged.index("\n", staged.index(
            "  exact _root_.", t)):]
        # imports: a deleted implementation module is replaced by its own imports
        for mod in deleted:
            line = f"public import {mod}\n"
            if line in text:
                repl = "".join(i + "\n" for i in moved[e["export"]]["imports"])
                text = text.replace(line, repl, 1)
        para = (f"\nThe theorem `{c['provider_export']}` states the anchor's exact type text (its draft file under "
                f"`docs/tracks/LP/freeze/draft7/`). Its proof is the proof of the former implementation lemma "
                f"`{e['export']}` (`{c['module']}`), moved verbatim at the freeze (D62; FREEZE-PROPOSAL §7 point 3)"
                + (f"; the sibling `{c['sibling'].split('.')[-1]}` it uses is inlined verbatim as a private theorem"
                   if c["sibling"] else "") + ". No module other than the anchor imports this module (AGENTS rule 9).")
        import textwrap
        new_para = "\n" + textwrap.fill(para.strip(), 100, break_on_hyphens=False) + "\n"
        assert len(PARA_OLD.findall(text)) == 1, rel
        text = PARA_OLD.sub(lambda _m: new_para, text, count=1)
        assert "exact _root_." not in text, rel
        assert max(len(l) for l in text.split("\n")) <= 100, rel
        dest.write_text(text)
        n += 1
        print(f"characterization provider (moved proof{', sibling inlined' if c['sibling'] else ''})  {rel}")
    assert n == 39, n
    print(f"{n} providers written to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

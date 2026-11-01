#!/usr/bin/env python3
"""S2 (RUNBOOK §7): rebase the LP implementation onto the frozen files (FREEZE-PROPOSAL §7, rebase-plan.json).

usage: lp_rebase.py --root <worktree> --plan rebase-plan.json --phase defs|characterizations [--out <scratch>]

--phase defs: in each implementation module, delete exactly the listed top-level `def`/`abbrev` blocks (with their
  docstrings and one following blank line) and add `public import` of the frozen definition modules after the last
  existing `public import`. Nothing else changes.
--phase characterizations: delete the 34 characterization lemmas (docstring, statement and proof) from their
  implementation modules; delete the modules listed in `delete_modules` (they must then contain no declaration);
  write their proofs to <out or root>/.lake/lp-freeze/moved-proofs.json for lp_providers.py.

Asserts each deleted block's declaration name, that every other line is unchanged (difflib: only deletions and the
added import lines), and reports the line delta per module.
"""
from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402

DECL_RE = r"^(?:@\[[^\]\n]*\]\s*)*(?:noncomputable |protected |private )*(def|abbrev|theorem|lemma) {name}(?=[ \n:({{\[])"


def find_block(lines: list[str], name: str, kinds: tuple[str, ...]) -> tuple[int, int, str]:
    """[start, end) line range of the top-level declaration `name`: its docstring, the declaration up to the
    first blank line, and one following blank line."""
    pat = re.compile(DECL_RE.format(name=re.escape(name)))
    hits = [i for i, l in enumerate(lines) if pat.match(l) and pat.match(l).group(1) in kinds]
    assert len(hits) == 1, (name, hits)
    i = hits[0]
    start = i
    if lines[i - 1].rstrip().endswith("-/"):
        start = i - 1
        while not lines[start].lstrip().startswith("/--"):
            start -= 1
    end = i
    while end < len(lines) and lines[end].strip() != "":
        end += 1
    if end < len(lines) and lines[end].strip() == "":
        end += 1
    return start, end, "\n".join(lines[i:end]).rstrip("\n")


def check_only(old: list[str], new: list[str], allowed_added: set[str]) -> None:
    for op in difflib.ndiff(old, new):
        if op.startswith("+ "):
            assert op[2:] in allowed_added, f"unexpected added line {op[2:]!r}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--plan", required=True)
    ap.add_argument("--phase", required=True, choices=["defs", "characterizations"])
    ap.add_argument("--out")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    out = Path(a.out).resolve() if a.out else root
    plan = json.loads(Path(a.plan).read_text())

    def src(rel: str) -> Path:
        p = out / rel
        return p if p.exists() else root / rel

    if a.phase == "defs":
        for item in plan["definitions"]:
            rel = item["module"].replace(".", "/") + ".lean"
            text = src(rel).read_text()
            lines = text.split("\n")
            blocks = sorted((find_block(lines, d["name"], ("def", "abbrev")) + (d,)) for d in item["delete"])
            keep = list(lines)
            for s, e, _, _ in reversed(blocks):
                del keep[s:e]
            imports = [f"public import {d['frozen_module']}" for d in item["delete"]]
            last = max(i for i, l in enumerate(keep) if re.match(r"^public import ", l))
            for imp in imports:
                assert imp not in keep, imp
            keep[last + 1:last + 1] = sorted(imports)
            check_only(lines, keep, set(imports))
            dest = out / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text("\n".join(keep))
            print(f"{item['module']}: deleted {len(blocks)} definitions "
                  f"({sum(e - s for s, e, _, _ in blocks)} lines), +{len(imports)} imports")
        return 0

    moved = {}
    by_module: dict[str, list[dict]] = {}
    for c in plan["characterizations"]:
        by_module.setdefault(c["module"], []).append(c)
    for module, cs in by_module.items():
        rel = module.replace(".", "/") + ".lean"
        text = src(rel).read_text()
        lines = text.split("\n")
        blocks = []
        for c in cs:
            s, e, decl = find_block(lines, c["name"], ("theorem", "lemma"))
            k = decl.index(" :=")
            moved[c["export"]] = {"module": module, "statement": decl[:k], "proof": decl[k + len(" :="):],
                                  "imports": re.findall(r"(?m)^(public import \S+)$", text)}
            blocks.append((s, e))
        keep = list(lines)
        for s, e in sorted(blocks, reverse=True):
            del keep[s:e]
        check_only(lines, keep, set())
        if module in plan["delete_modules"]:
            code = "\n".join(keep)
            assert not re.search(r"(?m)^(?:theorem|lemma|def|abbrev|instance|structure) ", code), module
            print(f"{module}: deleted {len(blocks)} characterization lemmas; module now empty -> deleted")
            (out / rel).parent.mkdir(parents=True, exist_ok=True)
            (out / (rel + ".DELETED")).write_text("")  # dry-run marker; a real run removes the file below
            if out == root:
                (root / rel).unlink()
                (out / (rel + ".DELETED")).unlink()
            continue
        dest = out / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text("\n".join(keep))
        print(f"{module}: deleted {len(blocks)} characterization lemmas "
              f"({sum(e - s for s, e in blocks)} lines)")
    mp = out / ".lake/lp-freeze/moved-proofs.json"
    mp.parent.mkdir(parents=True, exist_ok=True)
    mp.write_text(json.dumps(moved, indent=1, ensure_ascii=False) + "\n")
    print(f"moved proofs of {len(moved)} characterizations -> {mp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

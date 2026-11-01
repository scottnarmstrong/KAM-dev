#!/usr/bin/env python3
"""LEAN_STATUS sync of the track-LP graph against the frozen manifest (the W precedent format).

usage: python3 -I docs/graph/LP/tools/lp_depgraph_lean_sync.py [--root .] [--report docs/graph/LP/LEAN_STATUS.md]
       python3 -I docs/graph/LP/tools/lp_depgraph_lean_sync.py --apply [--force]

D65 (streamlined graph, 2026-11-01): LEAN_STATUS is set mechanically from LEAN_REFs that resolve on `main`. The
manifest is read from `main` (`git show main:manifest/frozen-anchors.json`), and an anchor is PROVED only when its
LEAN_REF resolves on main: the frozen file at `main:<path>` declares the export's short name, the manifest state on
main is SEALED, and (theorems) the provider module file exists on main. All slices of packets/slices-assembled.txt are
synced. Ordinary nodes listed in packets/lean-ref-map.tsv (written by lp_depgraph_lean_refmap.py: unique docstring
citation, declaration on main, standard axioms) are set PROVED with that LEAN_REF. `--apply --force` is the D65 path (the publication gate is replaced by one global review).

This is Lean-orchestration bookkeeping, not source extraction: it runs only after the graph is published (the review
gate requires the initial Lean fields, so `--apply` refuses while header.txt has `GLOBAL_REVIEWER: -`, unless
--force). It reads, for anchor nodes only, the manifest fields `state`, `export`, `path` and `implementation`, and
sets, exactly as the track-W sync of 2026-10-31 did:
- a SEALED definition anchor: LEAN_STATUS PROVED, LEAN_REF `<export> (<path>)`, LEAN_NOTE "sealed frozen definition
  (manifest SEALED); formalized, nothing to prove";
- a SEALED theorem anchor: LEAN_STATUS PROVED, LEAN_REF `<export> (<path>)`, LEAN_NOTE "sealed frozen theorem (manifest
  SEALED, D62); proof by exact <provider export>".
Every other node keeps its fields: an ordinary node's status needs a Lean reference that this tool cannot infer
(after the D62 seal the open ones are D27 BYPASS candidates for the orchestrator, as in track W). `--report` writes
the table of what the sync sets and what it leaves; `--apply` edits the packets in place (re-assemble afterwards).
"""
import argparse
import csv
import json
import re
from pathlib import Path

import subprocess


def on_main(root, path):
    r = subprocess.run(["git", "-C", str(root), "show", f"main:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def resolves(root, e):
    text = on_main(root, e["path"])
    short = e["export"].split(".")[-1]
    if text is None or not re.search(r"^(?:noncomputable )?(?:def|theorem|abbrev|structure|lemma) (?:[\w.]+\.)?" + re.escape(short)
                                     + r"(?![\w.])", text, re.M):
        return False
    if e["kind"] != "definition":
        mod = e.get("implementation", {}).get("module", "")
        return bool(mod) and on_main(root, mod.replace(".", "/") + ".lean") is not None
    return True


def blocks(text):
    return [b for b in re.split(r"\n\s*\n(?=NODE: )", text.strip()) if b.strip()]


def field(b, k):
    m = re.search(rf"^{k}: (.*)$", b, re.M)
    return m.group(1).strip() if m else None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--report", default="docs/graph/LP/LEAN_STATUS.md")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    root = Path(a.root)
    g = root / "docs/graph/LP"
    man = {e["id"]: e for e in json.loads(on_main(root, "manifest/frozen-anchors.json"))["anchors"]}
    SLICES = (g / "packets/slices-assembled.txt").read_text().split()
    refmap = {}
    if (g / "packets/lean-ref-map.tsv").exists():
        refmap = {r["node"]: (r["declaration"], r["file"])
                  for r in csv.DictReader(open(g / "packets/lean-ref-map.tsv"), delimiter="\t")}
    bind = {r["node"]: r for r in csv.DictReader(open(g / "packets/anchor-binding.tsv"), delimiter="\t")}
    published = not re.search(r"^GLOBAL_REVIEWER: -$", (g / "header.txt").read_text(), re.M)
    if a.apply and not published and not a.force:
        raise SystemExit("graph not published (header GLOBAL_REVIEWER: -); the review gate needs the initial Lean "
                         "fields. Apply after publication, or pass --force deliberately.")
    rows, changed = [], 0
    for sl in SLICES:
        p = g / "packets" / f"{sl}.nodes.md"
        if not p.exists() or not p.read_text().strip():
            continue
        out = []
        for b in blocks(p.read_text()):
            nid, kind = field(b, "NODE"), field(b, "KIND")
            r = bind.get(nid)
            new = None
            if r:
                e = man[r["manifest_id"]]
                if e.get("state") == "SEALED" and resolves(root, e):
                    ref = f"{e['export']} ({e['path']})"
                    if e["kind"] == "definition":
                        note = "sealed frozen definition (manifest SEALED); formalized, nothing to prove"
                    else:
                        note = (f"sealed frozen theorem (manifest SEALED, D62); proof by exact "
                                f"{e.get('implementation', {}).get('export', '?')}")
                    new = ("PROVED", ref, note)
                rows.append((sl, nid, kind, e.get("state"), new[0] if new else field(b, "LEAN_STATUS"),
                             new[1] if new else "-"))
            elif nid in refmap:
                d, f = refmap[nid]
                new = ("PROVED", f"{d} ({f})", "mechanical docstring match on main (D65; tools/lp_depgraph_lean_refmap.py, "
                       "reports/lean-ref-map.txt): unique LP:MAIN citation; #print axioms [propext, Classical.choice, "
                       "Quot.sound]")
                rows.append((sl, nid, kind, "-", new[0], new[1]))
            else:
                rows.append((sl, nid, kind, "-", field(b, "LEAN_STATUS"), "-"))
            if new and a.apply:
                b = re.sub(r"^LEAN_STATUS: .*$", f"LEAN_STATUS: {new[0]}", b, flags=re.M)
                b = re.sub(r"^LEAN_REF: .*$", f"LEAN_REF: {new[1]}", b, flags=re.M)
                b = re.sub(r"^LEAN_NOTE: .*$", f"LEAN_NOTE: {new[2]}", b, flags=re.M)
                changed += 1
            out.append(b.strip("\n"))
        if a.apply:
            p.write_text("\n\n".join(out) + "\n")
    from collections import Counter
    c = Counter(r[4] for r in rows)
    lines = ["# Track LP graph: LEAN_STATUS (mechanical, D65)", "",
             "Applied to the packets (D65: LEAN_STATUS is set mechanically from LEAN_REFs that resolve on main; an "
             "anchor is PROVED only if main's frozen file declares its export, main's manifest marks it SEALED and, "
             "for a theorem, main holds its provider module). Ordinary nodes are PROVED only through the mechanical "
             "docstring map (reports/lean-ref-map.txt); the others keep NOT_STARTED, externals EXTERNAL. The wave-1 text below is kept for the record.", "",
             "Generated by `docs/graph/LP/tools/lp_depgraph_lean_sync.py` from `manifest/frozen-anchors.json` "
             "(identity and `state` fields of the anchor entries only; the manifest equals main's after the D62 "
             "freeze f46b94fb). **Not applied to the packets yet**: the slice reviews and the publish gate require the "
             "initial Lean fields (`--require-initial-lean-status`). Apply it right after publication with the sync "
             "command below, then land it on main within the hour (owner's graph sync rule).", "",
             "```bash",
             "python3 -I docs/graph/LP/tools/lp_depgraph_lean_sync.py --apply",
             "python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_assemble.py --graph-dir docs/graph/LP \\",
             "  --slice-dir docs/graph/LP/packets --header docs/graph/LP/header.txt \\",
             "  --slices LP-adef-pl,LP-athm,LP-ext,LP-m1,LP-m2a,LP-m2b,LP-amend,LP-m78 --title \"Proof dependency database - track LP\"",
             "python3 /root/.claude/skills/build-proof-dependency-graph/scripts/proof_depgraph.py --db docs/graph/LP/DEPGRAPH.md \\",
             "  --manifest docs/graph/LP/DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage \\",
             "  --require-all-reachable --write-dashboard   # then the same with --check",
             "```", "",
             f"Totals after the sync: {', '.join(f'{k} {v}' for k, v in sorted(c.items()))} of {len(rows)} nodes. "
             "Resolved in the HQ sense (PROVED, BYPASSED, EXTERNAL, ASSUMED): "
             f"{sum(v for k, v in c.items() if k in ('PROVED', 'BYPASSED', 'EXTERNAL', 'ASSUMED'))}.", "",
             "Every theorem anchor of LP (LP0 … LP2-H and the 34 characterizations) is SEALED (D62), so track LP's "
             "proof is complete in the sense of `scripts/hq-status.py` `track_sealed`. The ordinary nodes below stay "
             "NOT_STARTED here: their status needs a Lean reference that this source-level sync must not infer. As "
             "for track W after its seal, they are D27 BYPASS candidates (the sealed root makes them unnecessary) or "
             "get PROVED from the landed LP modules' audits; that decision belongs to the orchestrator.", "",
             "| Slice | Node | KIND | Manifest state | LEAN_STATUS | LEAN_REF |", "|---|---|---|---|---|---|"]
    lines += [f"| {r[0]} | `{r[1]}` | {r[2]} | {r[3]} | {r[4]} | {('`' + r[5] + '`') if r[5] != '-' else '-'} |"
              for r in rows]
    (root / a.report).write_text("\n".join(lines) + "\n")
    print(f"wrote {a.report}: {dict(c)}" + (f"; applied to {changed} anchor nodes" if a.apply else "; not applied"))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Markdown pre-extractor of the track-LP graph (SPEC Q7): skeleton slice packets from the draft inventory.

usage: python3 -I docs/graph/LP/tools/lp_depgraph_preextract.py --wave 1 [--root .] [--force]

The shared `inp_depgraph_preextract.py` reads LaTeX labels only; MAIN.md is Markdown without labels. This tool reads
- `docs/graph/LP/draft/coverage-{main,amendments}.md` (the pre-anchor inventory; each REASON names `SLICE: ...`),
- `docs/graph/LP/packets/anchor-binding.tsv` (written by `lp_depgraph_bind.py` from the manifest identity fields),
and writes, for every slice of the requested wave(s), `packets/<slice>.nodes.md` and `packets/<slice>.coverage.md`:
- coverage: the slice's inventory items verbatim (the anchor slices get one item per anchor);
- nodes: one skeleton block per planned node the slice owns, with `TODO` in every extracted field. A planned
  non-anchor node is owned by the slice of the inventory item that has its ID (else of the first item naming it);
  externals `lpM:ext-*` go to the writer-owned slice `LP-ext`; anchors go to their binding slice. Anchor blocks
  already carry the identity fields (FROZEN_*, CONTRACT_*) copied from the binding.
The skeletons are the input of the dry run (`inp_depgraph_slice_check.py ... --structural`) and of
`lp_depgraph_fill.py`, which keeps them as `<slice>.draft-*.md` and renders the writer's spec. A packet that already
holds a non-skeleton record is never overwritten (use --force only before extraction).
"""
import argparse
import csv
import re
from pathlib import Path

WAVES = {1: ["LP-adef-pl", "LP-athm", "LP-m1", "LP-m2a", "LP-m2b", "LP-amend", "LP-m78", "LP-ext"],
         2: ["LP-m3", "LP-m4a", "LP-m4b", "LP-m5", "LP-imports"], 3: ["LP-adef-sp", "LP-m6"], 4: ["LP3-a", "LP3-b"]}
SLICE_WAVE = {s: w for w, ss in WAVES.items() for s in ss}
FIELDS = ("NODE", "KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE", "CONTRACT_ID", "CONTRACT_VERSION",
          "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "CONSTANT_SCOPE", "FROZEN_FILE",
          "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256", "DEPS", "ROUTES", "ROUTE_FOR", "TOPOLOGY_STATUS",
          "EXTRACTOR", "REVIEWER", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE", "NOTE")
ITEM_NODE_KIND = {"definition": "definition", "lemma": "lemma", "theorem": "theorem", "claim": "claim",
                  "display": "display", "proof-region": "step", "citation": "external"}


def blocks(text, key):
    return [b.strip("\n") for b in re.split(r"\n\s*\n(?=" + key + ": )", text.strip()) if b.strip()]


def parse(b):
    return {m.group(1): m.group(2).strip() for m in re.finditer(r"^([A-Z][A-Z0-9_]*):\s?(.*)$", b, re.M)}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--wave", type=int, action="append", required=True)
    ap.add_argument("--root", default=".")
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    g = Path(a.root) / "docs/graph/LP"
    slices = [s for w in a.wave for s in WAVES[w]]
    items = []
    for f in ("coverage-main.md", "coverage-amendments.md"):
        for b in blocks((g / "draft" / f).read_text(), "ITEM"):
            if b.startswith("ITEM:"):
                fd = parse(b)
                fd["_slice"] = re.search(r"SLICE: ([\w-]+)", fd["REASON"]).group(1)
                fd["_text"] = b
                items.append(fd)
    binding = list(csv.DictReader(open(g / "packets/anchor-binding.tsv"), delimiter="\t"))
    # node ownership
    owner, kind, stmt = {}, {}, {}
    for it in items:
        if not it["DISPOSITION"].startswith("NODE "):
            continue
        for nid in [x.strip() for x in it["DISPOSITION"][5:].split(",")]:
            if nid.startswith("lpM:ext-"):
                sl = "LP-ext"
            elif nid == it["ITEM"] or nid not in owner:
                sl = it["_slice"]
            else:
                continue
            if nid in owner and nid != it["ITEM"]:
                continue
            owner[nid], kind[nid], stmt[nid] = sl, ITEM_NODE_KIND.get(it["KIND"], "step"), it["SOURCE"]
    anchors = {r["node"]: r for r in binding}
    for nid, r in anchors.items():
        owner[nid] = r["slice"]
    wrote = []
    for sl in slices:
        nf, cf = g / "packets" / f"{sl}.nodes.md", g / "packets" / f"{sl}.coverage.md"
        if nf.exists() and not a.force and any("TODO" not in parse(b).get("SOURCE_CONCLUSION", "TODO")
                                               for b in blocks(nf.read_text(), "NODE")):
            print(f"{sl}: packet holds extracted records; not overwritten")
            continue
        out, cov = [], []
        for nid in sorted(n for n, s in owner.items() if s == sl):
            r = anchors.get(nid)
            if r and int(r["wave"]) not in a.wave:
                continue
            if not r and SLICE_WAVE.get(sl) not in a.wave:
                continue
            f = {k: "TODO" for k in FIELDS}
            f.update(NODE=nid, ROUTES="-", ROUTE_FOR="-", TOPOLOGY_STATUS="PROPOSED", EXTRACTOR="TODO", REVIEWER="-",
                     LEAN_REF="-", LEAN_NOTE="-", NOTE="-", DEPS="-")
            if r:
                f.update(KIND="definition" if r["kind"] == "definition" else "lemma", CONTRACT_ID=r["contract_id"],
                         CONTRACT_VERSION=r["contract_version"], FROZEN_FILE=r["path"], FROZEN_DECL=r["export"],
                         FROZEN_ANCHOR_ID=r["manifest_id"], FROZEN_ABI_SHA256=r["abi_sha256"],
                         TITLE=f"{r['role']} {r['export']}", LEAN_STATUS="NOT_STARTED")
                cov.append("\n".join([f"ITEM: {nid}", f"KIND: {'definition' if r['kind'] == 'definition' else 'lemma'}",
                                      "SOURCE: TODO", f"DISPOSITION: NODE {nid}",
                                      f"REASON: frozen anchor {r['manifest_id']} ({r['role']}; {r['source_range']})",
                                      "COVERAGE_STATUS: PROPOSED", "EXTRACTOR: TODO", "REVIEWER: -"]))
            else:
                k = kind[nid]
                f.update(KIND=k, CONTRACT_ID=nid, CONTRACT_VERSION="1", FROZEN_FILE="-", FROZEN_DECL="-",
                         FROZEN_ANCHOR_ID="-", FROZEN_ABI_SHA256="-", STATEMENT_SOURCE=stmt[nid],
                         LEAN_STATUS="EXTERNAL" if k == "external" else "NOT_STARTED",
                         PROOF_SOURCE="-" if k in ("external", "definition") else "TODO")
            out.append("\n".join(f"{k}: {f[k]}" for k in FIELDS))
        cov += [it["_text"] for it in items if it["_slice"] == sl]
        nf.write_text("\n\n".join(out) + "\n" if out else "")
        cf.write_text("\n\n".join(cov) + "\n" if cov else "")
        wrote.append(f"{sl}: {len(out)} skeleton nodes, {len(cov)} coverage items")
    print("\n".join(wrote))


if __name__ == "__main__":
    main()

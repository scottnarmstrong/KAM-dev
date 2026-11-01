#!/usr/bin/env python3
"""Render one track-LP slice packet from the writer's compact spec (single-writer extraction, SPEC §8).

usage: python3 -I docs/graph/LP/tools/lp_depgraph_fill.py SLICE [--tag kam-lp] [--root .]

Reads `docs/graph/LP/specs/<SLICE>.py` and writes `docs/graph/LP/packets/<SLICE>.{nodes,coverage}.md` (plus
`<SLICE>.deferred-coverage.md` for inventory items whose nodes belong to a later wave). On the first run the
pre-extractor skeletons (`lp_depgraph_preextract.py`) are kept as `<SLICE>.draft-{nodes,coverage}.md`; every
skeleton node must then be rendered or listed in DELETE with a reason. A packet holding a reviewed or
reviewer-written record is never re-rendered: after review the packet is the source of truth.

Spec names (a Python file; `M`, `A` locator helpers are predefined):
- NODES = {id: dict(kind, title, stmt, proof, H, Q, C, S, deps=[(target, lines, why[, unit])], routes=[...],
           route_for, note)}; `stmt`/`proof` are locators 'L5:164-164' (MAIN) or 'A:N11:20-20' (AMENDMENTS) or '-';
  an EDGE locator is `<file>#<unit>@Lx-Ly`, with file and unit those of the node's PROOF_SOURCE (else
  STATEMENT_SOURCE) unless the 4th tuple element gives a unit ('s1', 'L3', or 'A:N2' for AMENDMENTS).
  Anchor nodes (IDs in docs/graph/LP/packets/anchor-binding.tsv) get FROZEN_* and CONTRACT_* from the binding.
- DELETE = {id: reason}: skeleton nodes not rendered (e.g. owned by a later wave).
- COV = {item: (disposition, reason)}: overrides of inventory items; DEFER = {item: reason}: inventory items moved
  to the deferred file until their nodes exist; NEWCOV = [(item, kind, source, disposition, reason)].
- Anchor coverage items (ITEM = anchor node ID) get SOURCE = the node's STATEMENT_SOURCE automatically.
"""
import csv
import re
import runpy
import sys
from pathlib import Path

MAIN, AMEND = "docs/tracks/LP/source/MAIN.md", "docs/tracks/LP/source/AMENDMENTS.md"
FIELDS = ("NODE", "KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE", "CONTRACT_ID", "CONTRACT_VERSION",
          "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "CONSTANT_SCOPE", "FROZEN_FILE",
          "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256", "DEPS", "ROUTES", "ROUTE_FOR")
TAIL = ("TOPOLOGY_STATUS", "EXTRACTOR", "REVIEWER", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE", "NOTE")
CFIELDS = ("ITEM", "KIND", "SOURCE", "DISPOSITION", "REASON", "COVERAGE_STATUS", "EXTRACTOR", "REVIEWER")


def loc(spec):
    """'L5:164-170' -> MAIN locator; 'A:N11:20-20' -> AMENDMENTS locator; '-' stays."""
    if spec in ("-", None):
        return "-"
    if "#" in spec and "@" in spec:  # a complete locator (imported nodes: blueprint-N/..., wave 2)
        return spec
    parts = spec.split(":")
    path = AMEND if parts[0] == "A" else MAIN
    if parts[0] == "A":
        parts = parts[1:]
    unit, rng = parts[0], parts[1]
    x, _, y = rng.partition("-")
    return f"{path}#{unit}@L{int(x)}-L{int(y or x)}"


def blocks(text, key):
    return [b.strip("\n") for b in re.split(r"\n\s*\n(?=" + key + ": )", text.strip()) if b.strip()]


def parse(b):
    return {m.group(1): m.group(2).strip() for m in re.finditer(r"^([A-Z][A-Z0-9_]*):\s?(.*)$", b, re.M)
            if m.group(1) != "EDGE"}


def clean(s):
    return re.sub(r"\s+", " ", str(s)).replace("|", "¦").strip()


def main():
    sl = sys.argv[1]
    tag = sys.argv[sys.argv.index("--tag") + 1] if "--tag" in sys.argv else "kam-lp"
    root = Path(sys.argv[sys.argv.index("--root") + 1]) if "--root" in sys.argv else Path(".")
    g = root / "docs/graph/LP"
    spec = runpy.run_path(str(g / "specs" / f"{sl}.py"), init_globals={"M": MAIN, "A": AMEND})
    NODES, DELETE = spec.get("NODES", {}), spec.get("DELETE", {})
    COV, DEFER, NEWCOV = spec.get("COV", {}), spec.get("DEFER", {}), spec.get("NEWCOV", [])
    binding = {r["node"]: r for r in csv.DictReader(open(g / "packets/anchor-binding.tsv"), delimiter="\t")}
    P = g / "packets"
    nf, cf = P / f"{sl}.nodes.md", P / f"{sl}.coverage.md"
    dnf, dcf = P / f"{sl}.draft-nodes.md", P / f"{sl}.draft-coverage.md"
    for b in (blocks(nf.read_text(), "NODE") if nf.exists() else []):
        f = parse(b)
        if f.get("REVIEWER", "-") != "-" or "+" in f.get("EXTRACTOR", ""):
            sys.exit(f"{nf} holds reviewed or reviewer-written records ({f['NODE']}); edit the packet, not the spec")
    if not dnf.exists():
        dnf.write_text(nf.read_text() if nf.exists() else "")
        dcf.write_text(cf.read_text() if cf.exists() else "")
    draft_nodes = [parse(b) for b in blocks(dnf.read_text(), "NODE")] if dnf.read_text().strip() else []
    draft_ids = [f["NODE"] for f in draft_nodes]
    errs = [f"skeleton node {i} neither in NODES nor in DELETE" for i in draft_ids if i not in NODES and i not in DELETE]
    out = []
    for i, v in NODES.items():
        r = binding.get(i)
        f = dict(NODE=i, KIND=v.get("kind"), TITLE=clean(v.get("title", "")), STATEMENT_SOURCE=loc(v.get("stmt")),
                 PROOF_SOURCE=loc(v.get("proof", "-")), CONTRACT_ID=i, CONTRACT_VERSION="1",
                 SOURCE_HYPOTHESES=clean(v.get("H", "TODO")), SOURCE_QUANTIFIERS=clean(v.get("Q", "TODO")),
                 SOURCE_CONCLUSION=clean(v.get("C", "TODO")), CONSTANT_SCOPE=clean(v.get("S", "TODO")),
                 FROZEN_FILE="-", FROZEN_DECL="-", FROZEN_ANCHOR_ID="-", FROZEN_ABI_SHA256="-",
                 ROUTE_FOR=v.get("route_for", "-"), TOPOLOGY_STATUS="PROPOSED", EXTRACTOR=tag, REVIEWER="-",
                 LEAN_REF="-", LEAN_NOTE="-", NOTE=clean(v.get("note", "-")))
        if r:
            f.update(CONTRACT_ID=r["contract_id"], CONTRACT_VERSION=r["contract_version"], FROZEN_FILE=r["path"],
                     FROZEN_DECL=r["export"], FROZEN_ANCHOR_ID=r["manifest_id"], FROZEN_ABI_SHA256=r["abi_sha256"])
        k = f["KIND"]
        f["LEAN_STATUS"] = "EXTERNAL" if k == "external" else "ASSUMED" if k == "assumption" else "NOT_STARTED"
        for key in ("H", "Q", "C", "S", "kind", "title", "stmt"):
            if key not in v:
                errs.append(f"{i}: missing {key}")
        src = f["PROOF_SOURCE"] if f["PROOF_SOURCE"] != "-" else f["STATEMENT_SOURCE"]
        m = re.match(r"^([^#]+)#([^@]+)@", src)
        file0, unit0 = m.group(1), m.group(2)
        edges, names = [], {"deps": [], "routes": []}
        for key in ("deps", "routes"):
            for t in v.get(key, []):
                tgt, ln, why = t[0], str(t[1]), t[2]
                fl, un = file0, unit0
                if len(t) > 3:
                    un = t[3]
                    fl = MAIN
                    if un.startswith("A:"):
                        fl, un = AMEND, un[2:]
                x, _, y = ln.partition("-")
                names[key].append(tgt)
                edges.append(f"EDGE: {tgt} | {fl}#{un}@L{int(x)}-L{int(y or x)} | {clean(why)}")
        if len(set(names["deps"] + names["routes"])) != len(names["deps"] + names["routes"]):
            errs.append(f"{i}: repeated dependency")
        f["DEPS"] = ", ".join(names["deps"]) or "-"
        f["ROUTES"] = ", ".join(names["routes"]) or "-"
        out.append("\n".join([f"{k}: {f[k]}" for k in FIELDS] + edges + [f"{k}: {f[k]}" for k in TAIL]))
    # coverage
    stmts = {i: loc(v.get("stmt")) for i, v in NODES.items()}
    cov, deferred = [], []
    draft_cov = [parse(b) for b in blocks(dcf.read_text(), "ITEM")] if dcf.read_text().strip() else []
    seen = set()
    for it in draft_cov:
        iid = it["ITEM"]
        seen.add(iid)
        if iid in DEFER:
            it = dict(it, REASON=clean(it["REASON"] + "; DEFERRED: " + DEFER[iid]))
            deferred.append(it)
            continue
        if iid in COV:
            it = dict(it, DISPOSITION=COV[iid][0], REASON=clean(COV[iid][1]))
        if it.get("SOURCE") == "TODO":
            it["SOURCE"] = stmts.get(iid, "TODO")
        it.update(COVERAGE_STATUS="PROPOSED", EXTRACTOR=tag, REVIEWER="-")
        cov.append(it)
    for iid in list(COV) + list(DEFER):
        if iid not in seen:
            errs.append(f"COV/DEFER names {iid}, which is not an inventory item of {sl}")
    for iid, kind, source, disp, reason in NEWCOV:
        cov.append(dict(ITEM=iid, KIND=kind, SOURCE=loc(source), DISPOSITION=disp, REASON=clean(reason),
                        COVERAGE_STATUS="PROPOSED", EXTRACTOR=tag, REVIEWER="-"))
    for i in NODES:
        if i in binding and not any(c["ITEM"] == i for c in cov):
            r = binding[i]
            cov.append(dict(ITEM=i, KIND="definition" if r["kind"] == "definition" else "lemma", SOURCE=stmts[i],
                            DISPOSITION=f"NODE {i}", REASON=f"frozen anchor {r['manifest_id']} ({r['role']})",
                            COVERAGE_STATUS="PROPOSED", EXTRACTOR=tag, REVIEWER="-"))
    if errs:
        sys.exit("\n".join(errs))
    nf.write_text("\n\n".join(out) + "\n" if out else "")
    cf.write_text("\n\n".join("\n".join(f"{k}: {c[k]}" for k in CFIELDS) for c in cov) + "\n" if cov else "")
    df = P / f"{sl}.deferred-coverage.md"
    if deferred:
        df.write_text("# Deferred coverage items of " + sl + " (their nodes belong to a later wave; not assembled)\n\n"
                      + "\n\n".join("\n".join(f"{k}: {c[k]}" for k in CFIELDS) for c in deferred) + "\n")
    elif df.exists():
        df.unlink()
    print(f"{sl}: {len(out)} nodes, {sum(b.count(chr(10) + 'EDGE: ') for b in out)} edges, {len(cov)} coverage items"
          f", {len(deferred)} deferred, {len(DELETE)} skeletons not rendered")


if __name__ == "__main__":
    main()

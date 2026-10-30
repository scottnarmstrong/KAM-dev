#!/usr/bin/env python3
"""Fill one slice packet of the track-W graph from a writer spec (single-writer extraction, track W).

usage: w_depgraph_fill.py PACKETS_DIR SLICE SPEC.py [--tag claude-suborch-W]

The writer extracts each slice by hand into a compact spec file (`docs/graph/W/specs/<slice>.py`), and this tool
renders it into the packet `<slice>.nodes.md` / `<slice>.coverage.md` in the database format. The packet must hold
the split draft (`w_depgraph_split.py`); the spec is re-applied to the *draft* blocks kept in
`<slice>.draft-nodes.md` / `<slice>.draft-coverage.md` (created on first run), so re-running is idempotent.

SPEC defines:
- NODES = {id: {...}}: for every node of the slice (draft node or new node):
    H, Q, C, S        SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION, CONSTANT_SCOPE (required)
    deps              list of (target, lines, rationale): lines is "L12", "L12-L14" or an int; the EDGE locator is
                      `<file of the use>#<id base>@Lx-Ly`, where the file is that of PROOF_SOURCE (else
                      STATEMENT_SOURCE) unless a 4th tuple element names the file
    routes            same form as deps, for ROUTES
    kind, title, stmt, proof, note, route_for, contract   optional overrides
    new               True for a node absent from the draft (then kind, title, stmt, proof are required)
- DELETE = [ids]: draft nodes removed (their coverage item must be given in COV)
- COV = {item: (disposition, reason)}: disposition "NODE a, b" or "EXCLUDED"; items absent keep the draft text
- NEWCOV = {item: (kind, source, disposition, reason)}: extra coverage items
Every draft node must be in NODES or DELETE. The frozen fields and anchor CONTRACT_* fields are never changed.
"""
import re
import runpy
import sys
from pathlib import Path

FIELDS = ("NODE", "KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE", "CONTRACT_ID", "CONTRACT_VERSION",
          "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "CONSTANT_SCOPE", "FROZEN_FILE",
          "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256", "DEPS", "ROUTES", "ROUTE_FOR")
TAIL = ("TOPOLOGY_STATUS", "EXTRACTOR", "REVIEWER", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE", "NOTE")
CFIELDS = ("ITEM", "KIND", "SOURCE", "DISPOSITION", "REASON", "COVERAGE_STATUS", "EXTRACTOR", "REVIEWER")


def blocks(text, key):
    return [b.strip("\n") for b in re.split(r"\n\s*\n(?=" + key + ": )", text.strip()) if b.strip()]


def parse(b):
    f = {}
    for line in b.split("\n"):
        m = re.match(r"^([A-Z][A-Z0-9_]*):\s?(.*)$", line)
        if m and m.group(1) != "EDGE":
            f[m.group(1)] = m.group(2).strip()
    return f


def clean(s):
    return re.sub(r"\s+", " ", str(s)).replace("|", "¦").strip()


def lines(x):
    if isinstance(x, int):
        return x, x
    m = re.fullmatch(r"L?(\d+)(?:-L?(\d+))?", str(x).strip())
    assert m, f"bad line spec {x!r}"
    return int(m.group(1)), int(m.group(2) or m.group(1))


SYMBOLS = [
    ("bpW:w0:basis#lam", r"\\lambda(?![a-zA-Z])|\\hat\\lambda|\\Lean\{lam ", "lambda occurs directly here (frozen lam)"),
    ("bpW:w0:basis#sineMode", r"\\phi_|\\phi\^|\\Lean\{sineMode", "the sine modes phi_j occur directly here (frozen sineMode)"),
    ("bpW:w0:reconstruction#reconU", r"U_m|\\Lean\{reconU|U\^\{\(k\)\}|D\^0y", "U_m occurs directly here (frozen reconU)"),
    ("bpW:w0:reconstruction#reconV", r"V_m|\\Lean\{reconV|V\^\{\(k\)\}", "V_m occurs directly here (frozen reconV)"),
    ("bpW:w0:Gq#cubicGrad", r"\\Gq|\\Lean\{cubicGrad|\\mathcal G", "the cubic gradient G_q occurs directly here (frozen cubicGrad)"),
    ("bpW:w0:ellap#coeff", r"\\Lean\{coeff", "the frozen coeff occurs directly here"),
    ("bpW:w0:ellap#WaveSpace", r"\\Lean\{WaveSpace|KAM\.Wave\.WaveSpace", "the frozen WaveSpace occurs directly here"),
    ("bpW:w0:periodone#linearTorus", r"\\Lean\{linearTorus|K\^0_I", "the linear torus K^0_I occurs directly here (frozen linearTorus)"),
    ("bpW:w0:nlw#IsClassicalSolution", r"IsClassicalSolution", "the frozen IsClassicalSolution occurs directly here"),
    ("bpW:wh:embedding#IsAnalyticTorusEmbedding", r"IsAnalyticTorusEmbedding", "the frozen IsAnalyticTorusEmbedding occurs directly here"),
]


def main():
    d, sl, spec_path = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
    tag = sys.argv[sys.argv.index("--tag") + 1] if "--tag" in sys.argv else "claude-suborch-W"
    spec = runpy.run_path(spec_path)
    NODES, DELETE = spec.get("NODES", {}), set(spec.get("DELETE", []))
    COV, NEWCOV = spec.get("COV", {}), spec.get("NEWCOV", {})
    nf, cf = d / f"{sl}.nodes.md", d / f"{sl}.coverage.md"
    dnf, dcf = d / f"{sl}.draft-nodes.md", d / f"{sl}.draft-coverage.md"
    if not dnf.exists():
        dnf.write_text(nf.read_text())
        dcf.write_text(cf.read_text())
    draft = [parse(b) for b in blocks(dnf.read_text(), "NODE")]
    ids = [f["NODE"] for f in draft]
    errs = []
    for i in ids:
        if i not in NODES and i not in DELETE:
            errs.append(f"draft node {i} neither in NODES nor in DELETE")
    for i, v in NODES.items():
        if i not in ids and not v.get("new"):
            errs.append(f"{i}: not a draft node (set new=True)")
        if i in ids and v.get("new"):
            errs.append(f"{i}: new=True but it is a draft node")
    # refuse to overwrite a reviewed packet: after a slice review the packet is the source of truth
    for b in blocks(nf.read_text(), "NODE"):
        g = parse(b)
        if g.get("REVIEWER", "-") != "-" or "+" in g.get("EXTRACTOR", ""):
            sys.exit(f"{nf} holds reviewed or reviewer-written records ({g['NODE']}); edit the packet, not the spec")
    src_lines = {}

    def text_of(loc):
        m = re.match(r"^([^#\s]+)#[^@\s]+@L(\d+)-L(\d+)$", loc or "")
        if not m:
            return []
        path = Path(spec.get("ROOT", ".")) / m.group(1)
        if m.group(1) not in src_lines:
            src_lines[m.group(1)] = path.read_text(encoding="utf-8").split("\n")
        L = src_lines[m.group(1)]
        return [(k, L[k - 1]) for k in range(int(m.group(2)), int(m.group(3)) + 1)]
    # parents of proof steps (for STEP_CONTEXT)
    parent = {}
    for pid, pv in NODES.items():
        for t in pv.get("deps", []):
            if t[2] == "proof step":
                parent[t[0]] = pid
    out = []
    order = [i for i in ids if i not in DELETE] + [i for i, v in NODES.items() if v.get("new")]
    byid = {f["NODE"]: f for f in draft}
    for i in order:
        v = NODES[i]
        f = dict(byid.get(i, {}))
        if v.get("new"):
            f = dict(NODE=i, CONTRACT_ID=i, CONTRACT_VERSION="1", FROZEN_FILE="-", FROZEN_DECL="-",
                     FROZEN_ANCHOR_ID="-", FROZEN_ABI_SHA256="-", ROUTES="-", ROUTE_FOR="-",
                     TOPOLOGY_STATUS="PROPOSED", REVIEWER="-", LEAN_REF="-", LEAN_NOTE="-", NOTE="-")
        for key, fld in (("kind", "KIND"), ("title", "TITLE"), ("stmt", "STATEMENT_SOURCE"),
                         ("proof", "PROOF_SOURCE"), ("note", "NOTE"), ("route_for", "ROUTE_FOR")):
            if key in v:
                f[fld] = clean(v[key])
        if "contract" in v and f.get("FROZEN_DECL", "-") == "-":
            f["CONTRACT_ID"] = v["contract"]
        if spec.get("STEP_CONTEXT") and f.get("KIND", v.get("kind")) == "step" and i in parent:
            pv = NODES[parent[i]]
            bad = re.compile(r"Step|Lemma|Theorem|Corollary|Proposition|conclusion|^\s*\((?:i|ii|iii|iv|v|a|b)\)\s*$|^\s*the hypotheses|^\s*the consequences")
            local = [x.strip() for x in str(v.get("H", "")).split(";") if x.strip() and not bad.search(x)
                     and x.strip() not in str(pv.get("H", ""))]
            v = dict(v)
            v["H"] = "context of the proof of " + parent[i] + ": " + str(pv.get("H", "none")) + (
                "; local data: " + "; ".join(local) if local else "")
            v["Q"] = "for every choice of the data of " + parent[i] + " (" + str(pv.get("Q", "-")) + ")" + (
                "; within the step: " + str(v["Q"]) if v.get("Q") and v.get("Q") not in ("none", "-") else "") + \
                "; m > 0 fixed (standing assumption)"
        for key, fld in (("H", "SOURCE_HYPOTHESES"), ("Q", "SOURCE_QUANTIFIERS"), ("C", "SOURCE_CONCLUSION"),
                         ("S", "CONSTANT_SCOPE")):
            if key not in v:
                errs.append(f"{i}: missing {key}")
            f[fld] = clean(v.get(key, "TODO"))
        for fld in ("KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE"):
            if fld not in f:
                errs.append(f"{i}: missing {fld}")
        kind = f.get("KIND", "")
        f["LEAN_STATUS"] = "EXTERNAL" if kind == "external" else "ASSUMED" if kind == "assumption" else "NOT_STARTED"
        f["EXTRACTOR"] = tag
        src = f.get("PROOF_SOURCE", "-")
        if src in ("-", "") or "#" not in src:
            src = f.get("STATEMENT_SOURCE", "")
        file0 = src.split("#")[0]
        base = i.split("#")[0]
        edges = []

        def edge_lines(lst):
            names = []
            for t in lst:
                tgt, ln, why = t[0], t[1], t[2]
                fl = t[3] if len(t) > 3 else file0
                x, y = lines(ln)
                names.append(tgt)
                edges.append(f"EDGE: {tgt} | {fl}#{base}@L{x}-L{y} | {clean(why)}")
            return names
        if "deps" not in v:
            errs.append(f"{i}: missing deps")
        dl = list(v.get("deps", []))
        if spec.get("SYMBOL_EDGES") and f.get("FROZEN_DECL", "-") == "-" and f.get("KIND") not in ("external", "route"):
            have = {t[0] for t in dl}
            txt = text_of(f.get("STATEMENT_SOURCE"))
            if f.get("PROOF_SOURCE") not in ("-", f.get("STATEMENT_SOURCE")):
                txt += text_of(f.get("PROOF_SOURCE"))
            for tgt, pat, why in SYMBOLS:
                if tgt in have or tgt == i or tgt in spec.get("NO_SYMBOL", {}).get(i, ()):
                    continue
                hit = next((k for k, line in txt if re.search(pat, line) and not line.lstrip().startswith("%")), None)
                if hit:
                    sf = (f.get("PROOF_SOURCE") if f.get("PROOF_SOURCE") not in ("-", None) and
                          not any(k == hit for k, _ in text_of(f.get("STATEMENT_SOURCE"))) else
                          f.get("STATEMENT_SOURCE")).split("#")[0]
                    dl.append((tgt, hit, why, sf))
                    have.add(tgt)
        deps = edge_lines(dl)
        routes = edge_lines(v.get("routes", []))
        f["DEPS"] = ", ".join(deps) if deps else "-"
        f["ROUTES"] = ", ".join(routes) if routes else "-"
        if len(set(deps + routes)) != len(deps + routes):
            errs.append(f"{i}: repeated dependency")
        body = [f"{k}: {f.get(k, '-')}" for k in FIELDS] + edges + [f"{k}: {f.get(k, '-')}" for k in TAIL]
        out.append("\n".join(body))
    # coverage
    citems = [parse(b) for b in blocks(dcf.read_text(), "ITEM")]
    cids = [c["ITEM"] for c in citems]
    for k in COV:
        if k not in cids:
            errs.append(f"COV {k}: not a draft coverage item (use NEWCOV)")
    cout = []
    for c in citems:
        it = c["ITEM"]
        if it in COV:
            disp, why = COV[it][0], COV[it][1]
            c["DISPOSITION"], c["REASON"] = clean(disp), clean(why)
            if len(COV[it]) > 2:
                c["SOURCE"] = COV[it][2]
        elif it in DELETE:
            errs.append(f"coverage {it}: node deleted but no COV disposition")
        elif c.get("DISPOSITION", "").startswith("NODE "):
            for t in c["DISPOSITION"][5:].split(","):
                if t.strip() in DELETE:
                    errs.append(f"coverage {it}: maps to deleted node {t.strip()}")
        if c.get("DISPOSITION") == "TODO":
            errs.append(f"coverage {it}: DISPOSITION TODO")
        c["EXTRACTOR"] = tag
        c["COVERAGE_STATUS"] = "PROPOSED"
        cout.append("\n".join(f"{k}: {c.get(k, '-')}" for k in CFIELDS))
    for it, (kind, source, disp, why) in NEWCOV.items():
        cout.append("\n".join(f"{k}: {v}" for k, v in (("ITEM", it), ("KIND", kind), ("SOURCE", source),
                    ("DISPOSITION", clean(disp)), ("REASON", clean(why)), ("COVERAGE_STATUS", "PROPOSED"),
                    ("EXTRACTOR", tag), ("REVIEWER", "-"))))
    nf.write_text("\n\n".join(out) + "\n")
    cf.write_text("\n\n".join(cout) + "\n")
    print(f"{sl}: {len(out)} nodes, {len(cout)} coverage items written; {len(errs)} spec problems")
    for e in errs:
        print("  " + e)
    sys.exit(1 if errs else 0)


if __name__ == "__main__":
    main()

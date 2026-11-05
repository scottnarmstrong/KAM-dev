#!/usr/bin/env python3
"""Mechanical LEAN_REF resolution for the ordinary (non-anchor, non-external) nodes of the track-LP graph (D65).

usage: python3 -I docs/graph/LP/tools/lp_depgraph_lean_refmap.py [--root .] [--build-wt /root/code/KAM-inp]
           [--lean-wrapper /root/code/KAM-inp/.drafts/LP/lp_lean.sh] [--scratch DIR] [--no-axioms]

No inference beyond the docstring citations:
1. Declarations: every public declaration with a docstring in the LP implementation modules on `main`
   (KAM/Planetary/{StrongAMD,Spatial}/** and KAM/Provider/Planetary/{StrongAMD,Spatial}/**, frozen files excluded),
   read with `git show main:<path>`: full name (namespace stack + name), kind, module, and the citations
   `LP:MAIN <unit> (<group>) ...` in its docstring. Units: L<k>, T<k> (L15 = T15, L19 = T19, as the modules write
   them), §1 = s1; a parenthesized group with a range or a number > 47 is a line set, otherwise display numbers; a
   unit-less line group continues the preceding unit of the same citation ('L7 (205), (226)'); otherwise a citation
   without a unit cites displays only.
2. Matching ("cites exactly that node's MAIN item"), by node kind; a node is matched only by declarations of the
   matching kind (definition nodes by def/abbrev/structure, every other kind by theorem/lemma):
   - a lemma/theorem/corollary node without '#' (lpM:L14, lpM:T15): a citation of its unit with no line group, or
     whose cited lines span the node's statement start and proof end (tolerance 3 lines for line drift);
   - a step/claim/application/definition node (ID with '#', or a §1 definition): a citation of its unit whose cited
     lines all lie within the node's proof range (its statement range when it has none; tolerance 2);
   - a display node: a citation of a display number whose coverage item lpM:eq<N> maps to exactly this node;
   - route nodes are not matched (alternative wrappers; no declaration is expected).
3. A node is proposed when exactly one declaration matches it and that declaration matches no other node; or (step
   B, rule (a)) when it is d-generic (its MAIN unit is not L7, L8, T15, L17, L18, T19) and its matches are exactly one
   KAM.Planetary.StrongAMD.* and one KAM.Planetary.Spatial.* declaration, neither matching another node (LEAN_REF
   '<planar> ; <spatial>'); or when its own TITLE/SOURCE_CONCLUSION names one of the matching declarations. It is PROVED only if, in addition, the declaration exists on main by name (step 1) and
   `#print axioms` gives exactly {propext, Classical.choice, Quot.sound}: one scratch file, one process, through the
   LP wrapper in the build worktree. The build worktree's tree must equal main's on the whole transitive KAM import
   closure of the scratch file (checked blob by blob), so its build answers for main.
Writes docs/graph/LP/reports/lean-ref-map.txt (mapping table, reasons, axioms output) and
docs/graph/LP/packets/lean-ref-map.tsv (the PROVED rows; consumed by lp_depgraph_lean_sync.py).
"""
import argparse
import csv
import re
import subprocess
from collections import defaultdict
from pathlib import Path

DIRS = ("KAM/Planetary/StrongAMD/", "KAM/Planetary/Spatial/", "KAM/Provider/Planetary/StrongAMD/",
        "KAM/Provider/Planetary/Spatial/")
STD = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"/--(.*?)-/\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
                  r"(theorem|lemma|def|abbrev|structure|instance|irreducible_def)\s+([^\s(:{\[]+)", re.S)
UNIT = {"L15": "T15", "L19": "T19", "§1": "s1"}
DIM_UNITS = {"L7", "L8", "T15", "L17", "L18", "T19"}  # planar-only and spatial-only MAIN units; all others are d-generic
PAIR = "d-generic pair: exactly one planar and one spatial matching declaration (step B, rule (a))"


def git(root, *args):
    r = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def parse_citations(doc):
    """[(unit or None, lines:set, displays:set)] for every 'LP:MAIN ...' item (chained by ', ' or ' with ')."""
    out = []
    for m in re.finditer(r"LP:MAIN((?:\s*(?:,|with|;)?\s*(?:L\d+|T\d+|§1)?(?:\s*\([^()]*\))*)+)", doc):
        prev = None
        for part in re.finditer(r"(L\d+|T\d+|§1)?((?:\s*\([^()]*\))+)|(L\d+|T\d+|§1)(?!\s*\()", m.group(1)):
            unit = part.group(1) or part.group(3)
            unit = UNIT.get(unit, unit)
            if unit is None and prev is not None and out and out[-1][0] == prev:
                # a unit-less line group continues the preceding unit of the same citation: 'L7 (205), (226)'
                g = part.group(2) or ""
                if "–" in g or any(int(x) > 47 for x in re.findall(r"\d+", g)):
                    for x, y in re.findall(r"(\d+)(?:\s*[–-]\s*(\d+))?", g):
                        out[-1][1].update(range(int(x), int(y or x) + 1))
                    continue
            prev = unit if unit else prev
            lines, disps = set(), set()
            for g in re.findall(r"\(([^()]*)\)", part.group(2) or ""):
                nums = re.findall(r"(\d+)(?:\s*[–-]\s*(\d+))?", g)
                if not nums or not re.fullmatch(r"[\d\s,–-]+", g.strip()):
                    continue
                is_lines = "–" in g or "-" in g or any(int(a) > 47 for a, _ in nums)
                for a, b in nums:
                    rng = range(int(a), int(b or a) + 1)
                    (lines if is_lines else disps).update(rng)
            if unit or disps:
                out.append((unit, lines, disps))
    return out


def scan_decls(root):
    files = [f for f in (git(root, "ls-tree", "-r", "--name-only", "main") or "").split()
             if f.startswith(DIRS) and f.endswith(".lean")]
    decls = []
    for f in files:
        text = git(root, "show", f"main:{f}")
        stack, pos = [], 0
        events = [(m.start(), m.group(0)) for m in re.finditer(
            r"^(?:(?:public|noncomputable|private)\s+)*(?:namespace\s+\S+|section(?:\s+\S+)?|end(?:\s+\S+)?)\s*$",
            text, re.M)]
        ei = 0
        for m in DECL.finditer(text):
            while ei < len(events) and events[ei][0] < m.start():
                ev = events[ei][1].split()
                ev = [w for w in ev if w not in ("public", "noncomputable", "private")]
                if ev[0] == "namespace":
                    stack.append(("ns", ev[1]))
                elif ev[0] == "section":
                    stack.append(("sec", ev[1] if len(ev) > 1 else ""))
                elif ev[0] == "end" and stack:
                    stack.pop()
                ei += 1
            if "private" in m.group(2):
                continue
            ns = ".".join(n for k, n in stack if k == "ns")
            name = m.group(4)
            full = name[1:] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
            decls.append(dict(name=full, kind=m.group(3), file=f, module=f[:-5].replace("/", "."),
                              cites=parse_citations(m.group(1)), doc=re.sub(r"\s+", " ", m.group(1)).strip()))
    return decls


def span(loc):
    m = re.match(r"^docs/tracks/LP/source/MAIN\.md#([^@]+)@L(\d+)-L(\d+)$", loc or "")
    return (m.group(1), int(m.group(2)), int(m.group(3))) if m else None


def blocks(text, key):
    return [b for b in re.split(r"\n\s*\n(?=" + key + ": )", text.strip()) if b.strip()]


def fields(b):
    return {m.group(1): m.group(2).strip() for m in re.finditer(r"^([A-Z_]+): ?(.*)$", b, re.M) if m.group(1) != "EDGE"}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    ap.add_argument("--build-wt", default="/root/code/KAM-inp")
    ap.add_argument("--lean-wrapper", default="/root/code/KAM-inp/.drafts/LP/lp_lean.sh")
    ap.add_argument("--scratch", default=None, help="directory for the one scratch .lean file")
    ap.add_argument("--no-axioms", action="store_true")
    a = ap.parse_args()
    root = Path(a.root)
    g = root / "docs/graph/LP"
    slices = (g / "packets/slices-assembled.txt").read_text().split()
    nodes, display_owner = [], defaultdict(set)
    for s in slices:
        t = (g / "packets" / f"{s}.nodes.md").read_text()
        nodes += [fields(b) for b in blocks(t, "NODE")] if t.strip() else []
        c = (g / "packets" / f"{s}.coverage.md").read_text()
        for b in (blocks(c, "ITEM") if c.strip() else []):
            f = fields(b)
            m = re.fullmatch(r"lpM:eq(\d+)", f["ITEM"])
            if m and f["DISPOSITION"].startswith("NODE "):
                tg = [x.strip() for x in f["DISPOSITION"][5:].split(",")]
                if len(tg) == 1:
                    display_owner[int(m.group(1))].add(tg[0])
    ordinary = [n for n in nodes if n["FROZEN_FILE"] == "-" and n["KIND"] not in ("external", "assumption")]
    decls = scan_decls(root)
    by_name = {d["name"]: d for d in decls}
    rows = []
    for n in ordinary:
        nid, kind = n["NODE"], n["KIND"]
        if kind == "route":
            rows.append((nid, kind, [], None, "route node: alternative wrapper, no declaration expected"))
            continue
        locs = [x for x in (span(n["STATEMENT_SOURCE"]), span(n["PROOF_SOURCE"])) if x]
        if not locs:
            rows.append((nid, kind, [], None, "no MAIN locator"))
            continue
        want_def = kind == "definition"
        whole = "#" not in nid and kind in ("lemma", "theorem", "corollary", "proposition")
        if not whole and span(n["PROOF_SOURCE"]):  # a step's statement locator often repeats the enclosing statement
            locs = [span(n["PROOF_SOURCE"])]
        unit = locs[0][0]
        lo, hi = min(x[1] for x in locs), max(x[2] for x in locs)
        disp = {k for k, v in display_owner.items() if v == {nid}} if kind == "display" else set()
        cand = []
        for d in decls:
            if (d["kind"] in ("def", "abbrev", "structure", "irreducible_def")) != want_def or d["kind"] == "instance":
                continue
            hit = None
            for (cu, cl, cd) in d["cites"]:
                if disp and cd & disp:
                    hit = (cu, cl, cd)
                elif kind != "display" and cu == unit:
                    if whole:
                        if not cl and not cd:
                            hit = (cu, cl, cd)
                        elif cl and min(cl) <= lo + 3 and max(cl) >= hi - 3:
                            hit = (cu, cl, cd)
                    elif cl and min(cl) >= lo - 2 and max(cl) <= hi + 2:
                        hit = (cu, cl, cd)
                if hit:
                    break
            if hit:
                cand.append(d["name"])
        named = [c for c in cand if c.split(".")[-1] in (n.get("TITLE", "") + " " + n.get("SOURCE_CONCLUSION", ""))]
        pl = [c for c in cand if c.startswith("KAM.Planetary.StrongAMD.")]
        sp = [c for c in cand if c.startswith("KAM.Planetary.Spatial.")]
        dgeneric = unit not in DIM_UNITS
        if len(cand) == 1:
            rows.append((nid, kind, cand, cand[0], "unique docstring match"))
        elif named:
            rows.append((nid, kind, cand, named[0], "the node's own statement names the declaration"))
        elif dgeneric and len(cand) == 2 and len(pl) == 1 and len(sp) == 1:
            rows.append((nid, kind, cand, pl[0] + " ; " + sp[0], PAIR))
        elif cand:
            rows.append((nid, kind, cand, None, f"{len(cand)} matching declarations: not unique"))
        else:
            rows.append((nid, kind, [], None, "no declaration on main cites this MAIN item"))
    # declaration-side uniqueness: a declaration proposed for several nodes cites none of them exactly
    used = defaultdict(list)
    for r in rows:
        for c in (r[3].split(" ; ") if r[3] else []):
            used[c].append(r[0])

    def shared(prop, nid):
        return [x for c in prop.split(" ; ") for x in used[c] if x != nid]
    rows = [(nid, kind, cand, None, f"{why}, but {prop} is also the match of {', '.join(shared(prop, nid))}"
             " (its citation is coarser than this node)") if prop and shared(prop, nid) else (nid, kind, cand, prop, why)
            for nid, kind, cand, prop, why in rows]
    proposed = sorted({c for r in rows if r[3] for c in r[3].split(" ; ")})
    axioms, axlog, closure_ok, closure_note = {}, "", True, ""
    if proposed and not a.no_axioms:
        mods = sorted({by_name[p]["module"] for p in proposed})
        # transitive KAM import closure on main, compared blob by blob with the build worktree's HEAD tree
        seen, todo = set(), list(mods)
        while todo:
            mod = todo.pop()
            if mod in seen:
                continue
            seen.add(mod)
            txt = git(root, "show", f"main:{mod.replace('.', '/')}.lean") or ""
            todo += [x for x in re.findall(r"^(?:public\s+)?import\s+(KAM\S*)", txt, re.M)]
        diff = []
        for mod in sorted(seen):
            p = mod.replace(".", "/") + ".lean"
            bm = (git(root, "rev-parse", f"main:{p}") or "").strip()
            bw = (git(a.build_wt, "rev-parse", f"HEAD:{p}") or "").strip()
            if bm != bw:
                diff.append(p)
        dirty = git(a.build_wt, "status", "--porcelain", "--", *[m.replace(".", "/") + ".lean" for m in sorted(seen)])
        closure_ok = not diff and not (dirty or "").strip()
        closure_note = (f"import closure: {len(seen)} KAM modules; identical to main in {a.build_wt} (HEAD, clean)"
                        if closure_ok else f"import closure differs from main: {diff[:10]} dirty: {(dirty or '')[:200]}")
        scratch = Path(a.scratch or "/tmp") / "lp_refmap_axioms.lean"
        scratch.write_text("".join(f"import {m}\n" for m in mods) + "\n"
                           + "".join(f"#print axioms {p}\n" for p in proposed))
        r = subprocess.run([a.lean_wrapper, a.build_wt, str(scratch)], capture_output=True, text=True)
        axlog = r.stdout + r.stderr
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axlog):
            axioms[m.group(1)] = {x.strip() for x in m.group(2).split(",") if x.strip()}
        for m in re.finditer(r"'([^']+)' does not depend on any axioms", axlog):
            axioms[m.group(1)] = set()
    out, tsv = [], []
    for nid, kind, cand, prop, why in rows:
        status, reason = "NOT_STARTED", why
        if prop:
            parts = prop.split(" ; ")
            bad = [c for c in parts if c not in by_name]
            axbad = [c for c in parts if axioms.get(c) != STD]
            if bad:
                reason = why + f"; declaration not found on main: {bad}"
            elif not closure_ok:
                reason = why + "; axioms not checked: " + closure_note
            elif axbad:
                reason = why + "; axioms not exactly [propext, Classical.choice, Quot.sound] (or missing) for " + \
                    ", ".join(f"{c} {sorted(axioms[c]) if c in axioms else 'no output'}" for c in axbad)
            else:
                status = "PROVED"
                tsv.append((nid, prop, " ; ".join(by_name[c]["file"] for c in parts), why))
        out.append((nid, kind, status, prop or "-", reason, ", ".join(cand[:6]) + (" …" if len(cand) > 6 else "")))
    head = git(root, "rev-parse", "main").strip()
    lines = [f"# Track LP graph: mechanical LEAN_REF map of the ordinary nodes (D65), main {head}", "",
             f"declarations scanned on main: {len(decls)} (with docstrings, public); ordinary nodes: {len(ordinary)}",
             f"PROVED: {sum(1 for o in out if o[2] == 'PROVED')}; NOT_STARTED: "
             f"{sum(1 for o in out if o[2] != 'PROVED')}", closure_note, "",
             "| node | kind | status | LEAN_REF | reason | candidates |", "|---|---|---|---|---|---|"]
    lines += [f"| {o[0]} | {o[1]} | {o[2]} | {o[3]} | {o[4]} | {o[5]} |" for o in out]
    lines += ["", "## #print axioms output (one scratch file, one process)", "", "```", axlog.strip(), "```"]
    (g / "reports/lean-ref-map.txt").write_text("\n".join(lines) + "\n")
    with open(g / "packets/lean-ref-map.tsv", "w") as fh:
        w = csv.writer(fh, delimiter="\t", lineterminator="\n")
        w.writerow(("node", "declaration", "file", "match"))
        w.writerows(tsv)
    print(lines[2] + "\n" + lines[3] + "\n" + lines[4])


if __name__ == "__main__":
    main()

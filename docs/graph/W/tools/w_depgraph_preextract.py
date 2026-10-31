#!/usr/bin/env python3
"""Mechanical first pass of the source dependency graph of one track blueprint (tracks I, N, P).

Generalises `scripts/depgraph_preextract.py` (track K) to blueprints in `blueprint-<X>/` that cite other tracks'
blueprints with `\\Kref`, `\\Iref`, `\\Nref`, `\\Pref`.

usage:
  inp_depgraph_preextract.py --root REPO --blueprint blueprint-I --track I --manifest manifest/frozen-anchors.json
                             --out DIR [--anchor-part p0] [--proved-in ANCHOR=pA+pB,...] [--parts p0-x.tex,...]
                             [--owner K=blueprint,N=blueprint-N,P=blueprint-P,I=blueprint-I]
                             [--owner-graph K=docs/graph/K] [--writer claude-suborch-INP]
                             [--external-pattern ':(?:ext|x)-'] [--all-prose]
                             [--prose-anchor NODE=EXPORT@LX-LY ...]

Reads the blueprint only, never Lean (the manifest supplies anchor identity). As in track K:
- every labelled result environment, labelled external-input item and `\\proofstep` becomes a draft node with exact
  line locators and candidate DEPS read from the `\\ref`-family commands in the node's own text;
- Part 0's `\\frozen{...}` definitions become one node per frozen declaration (`<label>#<LeanName>`, ASCII), bound to
  the manifest; a Part 0 theorem with `\\frozen{...}` is an anchor node;
- a result elsewhere whose `\\frozen{...}` names a frozen theorem anchor becomes a candidate dependency of that anchor.
New for tracks I, N, P:
- `\\<self>ref{label}` (e.g. `\\Iref` in blueprint-I) is an internal reference;
- `\\Xref{label}` for another track X becomes a candidate dependency on an IMPORTED node `X:<node>` (KIND external,
  LEAN_STATUS EXTERNAL). The label is resolved in X's owning graph when one exists (`docs/graph/X/DEPGRAPH.md` and its
  coverage manifest): a graph node is used as is; an item/equation label is replaced by the graph node that covers it;
  a label whose graph nodes are frozen definitions that this track transcribes as its own anchors resolves to those
  anchors (never an import); a section label, a wildcard (`*`, `\\dots`) or an unknown label is skipped and reported.
  Without an owning graph, the label must be a result/step/external label of X's blueprint;
- `\\frozen{...}` on a result outside the anchor part that names a frozen definition anchor of this track yields a
  candidate dependency on that definition node; a name that is a frozen declaration of an owning graph yields a
  candidate dependency on the imported node;
- references inside `\\source{...}` are kept as candidates, tagged as provenance, except in the anchor part, where
  they are pure provenance and are dropped (counted in the report);
- unlabelled prose outside every node that contains references becomes a coverage item `<part>:prose-Lx-Ly`
  (DISPOSITION TODO), so that bridge paragraphs (e.g. "this is exactly Assumption K ... with h := H") are inspected;
- the imported nodes are written to DIR/imports.md and DIR/coverage-imports.md: one block per distinct imported node
  cited ANYWHERE in the corpus (prose included), with source fields copied from the owning graph when it exists and
  TODO otherwise. Prune unreferenced imports after extraction with `inp_depgraph_imports.py`.

Added for track N (2026-10-27):
- `\\frozen{...}` names may carry line-breaking hints (`KAM.Nekhoroshev.\\allowbreak actionBall`), which are ignored;
- a remark (or other environment) of the anchor part whose `\\frozen{...}` names only manifest definitions is a
  definition anchor like a definition environment (blueprint-N `bpN:p0:strip`);
- `--prose-anchor NODE=EXPORT@LX-LY` binds a frozen definition that the anchor part transcribes in unlabelled prose
  (no `\\frozen` tag) to a definition anchor NODE with that statement locator (no candidate DEPS);
- a label of an owning graph whose split definition nodes are only partly transcribed as own anchors resolves to those
  anchors; the others are not nodes of this graph (reported as skipped);
- while an owner has no graph, a `\\frozen{...}` name that is a frozen definition of the owner's Part 0 yields the import
  `X:<label>#<LeanName>` (its future anchor node); imports from graph-less owners carry `IMPORTED (pending X graph)`;
- `--all-prose` inventories every unlabelled prose paragraph outside the nodes, not only those with references;
- a result whose proof is written inside its own environment (`\\emph{Proof:}`, `\\qed`) gets PROOF_SOURCE = its
  statement locator.
Writes DIR/nodes.json, DIR/<part>.md, DIR/coverage-<part>.md, DIR/imports.{md,json}, DIR/coverage-imports.md and
DIR/report.json (skipped references, unresolved names, candidate cycles). Prints per-part counts.

W copy (docs/graph/W/tools, 2026-10-30, writer claude-suborch-W): the shared original is unchanged. Changes:
- `convention` environments are result environments (KIND definition);
- `--anchor-part` takes a comma-separated list of part keys (blueprint-W transcribes its frozen declarations in
  w0-conventions and w-headline);
- `--anchor-map LABEL=EXPORT[+EXPORT...]` (repeatable) binds a labelled environment of an anchor part to frozen
  manifest exports, as if it carried `\frozen{...}` (blueprint-W has no `\frozen` tags);
- part keys are file stems for any prefix (w0-conventions, w1-sequences, ...).
"""
import argparse
import json
import re
from pathlib import Path

RESULT_ENVS = ("theorem", "proposition", "lemma", "corollary", "definition", "assumption", "remark", "convention")
BEGIN = re.compile(r"\\begin\{(" + "|".join(RESULT_ENVS) + r")\}(?:\[(.*)\])?")
LABEL = re.compile(r"\\label\{([^}]+)\}")
SECTION = re.compile(r"\\(?:sub)*section\*?\{")
FROZEN = re.compile(r"\\frozen\{")
SOURCEGAP = re.compile(r"\\sourcegap\{")
SOURCE = re.compile(r"\\source\{")
WRAPPER = re.compile(r"^\\(?:begin|end)\{(?:enumerate|itemize|center|tabular)\}(?:\[[^\]]*\])?(?:\{[^}]*\})?$"
                     r"|^\\(?:begin|end)group\b|^\\par\\endgroup$|^\\providecommand\b")
INLINE_PROOF = re.compile(r"\\(?:emph|textit|textbf)\{Proof[.:]?\}|\\qed\b")
SUBDIGIT = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
FIELD_ORDER = ("NODE", "KIND", "TITLE", "STATEMENT_SOURCE", "PROOF_SOURCE", "CONTRACT_ID", "CONTRACT_VERSION",
               "SOURCE_HYPOTHESES", "SOURCE_QUANTIFIERS", "SOURCE_CONCLUSION", "CONSTANT_SCOPE", "FROZEN_FILE",
               "FROZEN_DECL", "FROZEN_ANCHOR_ID", "FROZEN_ABI_SHA256", "DEPS", "ROUTES", "ROUTE_FOR")
TAIL_ORDER = ("TOPOLOGY_STATUS", "EXTRACTOR", "REVIEWER", "LEAN_STATUS", "LEAN_REF", "LEAN_NOTE", "NOTE")


def braced(text, start):
    """Return the contents of the brace group opening at text[start] == '{'."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1:i]
    return text[start + 1:]


def brace_span_lines(lines, pattern):
    """Line numbers (1-based) covered by every `\\cmd{...}` group matching pattern (multi-line aware)."""
    text = "\n".join(lines)
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln) + 1)
    covered = set()
    for m in pattern.finditer(text):
        depth, i = 0, m.end() - 1
        while i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        a = next(k for k in range(len(starts)) if starts[k + 1] > m.start())
        b = next(k for k in range(len(starts)) if starts[k + 1] > i)
        covered.update(range(a + 1, b + 2))
    return covered


def ascii_id(name):
    return name.replace("ℂ", "C").translate(str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789"))


def norm_frozen(name):
    # line-breaking hints (blueprint-N writes `KAM.Nekhoroshev.\allowbreak actionBall`) carry no name content
    name = re.sub(r"\\allowbreak\b|\\-|\\linebreak\b", "", name)
    name = re.sub(r"\s+", "", name).replace("\\_", "_")
    name = re.sub(r"\$_\{?(\d+)\}?\$", lambda m: m.group(1).translate(SUBDIGIT), name)
    return name


def part_key(path):
    m = re.match(r"(p\d+[a-z]?\d*)", Path(path).stem)
    return m.group(1) if m else Path(path).stem


def ref_regexes(self_track):
    internal = r"\\(?:ref|eqref|cref|Cref|autoref" + (f"|{self_track}ref" if self_track else "") + r")\{([^}]+)\}"
    internal += r"|\\hyperref\[([^\]]+)\]"
    others = "".join(t for t in "KINP" if t != self_track)
    external = r"\\([" + others + r"])ref\{([^}]+)\}"
    return re.compile(internal), re.compile(external)


def parse_part(path, rel, ext_pattern):
    lines = path.read_text(encoding="utf-8").split("\n")
    n = len(lines)
    results, steps, externals, labels, sections, gaps, sources, missing_owner = [], [], [], {}, [], [], [], []
    ext_item = re.compile(r"\s*\\item\s*\\label\{([^}]*" + ext_pattern + r"[^}]*)\}")
    i = 0
    last_result = None
    while i < n:
        line = lines[i]
        m = BEGIN.search(line)
        if m and not line.lstrip().startswith("%"):
            env = m.group(1)
            j = i
            while j < n and f"\\end{{{env}}}" not in lines[j]:
                j += 1
            lab = None
            for k in range(i, min(i + 2, j + 1)):
                lm = LABEL.search(lines[k])
                if lm:
                    lab = lm.group(1)
                    break
            title = (m.group(2) or "").strip()
            r = dict(kind=env, label=lab, title=title, first=i + 1, last=j + 1, proof=None, file=rel)
            text = "\n".join(lines[i:j + 1])
            for fm in FROZEN.finditer(text):
                names = [norm_frozen(x) for x in braced(text, fm.end() - 1).split(",")]
                r.setdefault("frozen", []).extend(x for x in names if x)
            results.append(r)
            last_result = r
            i = j + 1
            continue
        if line.lstrip().startswith("\\begin{proof}"):
            owner = last_result["label"] if last_result else None
            om = re.match(r"\s*\\begin\{proof\}\[[^\]]*?\\(?:[KINP])?ref\{([^}]+)\}", line)
            if om:
                owner = om.group(1)
            j = i
            while j < n and "\\end{proof}" not in lines[j]:
                j += 1
            proof = dict(owner=owner, first=i + 1, last=j + 1, file=rel)
            starts = [k for k in range(i, j + 1) if "\\proofstep{" in lines[k]]
            for idx, k in enumerate(starts):
                end = (starts[idx + 1] - 1) if idx + 1 < len(starts) else j - 1
                while end > k and not lines[end].strip():
                    end -= 1
                text = lines[k]
                ps = text.index("\\proofstep{")
                title = braced(text, ps + len("\\proofstep"))
                lm = LABEL.search(text[ps:])
                steps.append(dict(kind="step", label=lm.group(1) if lm else None, title=title, first=k + 1,
                                  last=end + 1, owner=owner, file=rel))
            proof["steps"] = [s["label"] for s in steps if s["first"] - 1 in starts]
            if owner is not None:
                for r in results:
                    if r["label"] == owner:
                        r.setdefault("proofs", []).append(proof)
                        break
                else:
                    missing_owner.append(proof)
            i = j + 1
            continue
        em = ext_item.match(line)
        if em:
            lab = em.group(1)
            j = i + 1
            while j < n and not re.match(r"\s*\\item\b|\s*\\end\{enumerate\}", lines[j]):
                j += 1
            tm = re.search(r"\\emph\{([^}]*)\}", line)
            externals.append(dict(kind="external", label=lab, title=tm.group(1).rstrip(".") if tm else lab,
                                  first=i + 1, last=j, file=rel))
        i += 1
    for k, line in enumerate(lines):
        for lm in LABEL.finditer(line):
            labels[lm.group(1)] = k + 1
        if SECTION.match(line.lstrip()):
            lm = LABEL.search(line)
            sections.append(dict(label=lm.group(1) if lm else None, line=k + 1, text=line.strip()))
        if SOURCEGAP.search(line):
            gaps.append(k + 1)
        if SOURCE.search(line):
            sources.append(k + 1)
    unlabelled_steps = [s for s in steps if not s["label"]]
    return dict(lines=lines, rel=rel, results=results, steps=steps, externals=externals, labels=labels,
                sections=sections, gaps=gaps, sources=sources, missing_owner=missing_owner,
                source_lines=brace_span_lines(lines, SOURCE), gap_lines=brace_span_lines(lines, SOURCEGAP),
                unlabelled_steps=unlabelled_steps, unlabelled_results=[r for r in results if not r["label"]])


def parse_graph_blocks(path, key):
    """Parse NODE or ITEM blocks of a Markdown database into {id: fields}."""
    out = {}
    if not path.exists():
        return out
    cur = None
    for line in path.read_text(encoding="utf-8").split("\n"):
        m = re.match(r"^([A-Z][A-Z0-9_]*):\s?(.*)$", line)
        if not m:
            if not line.strip():
                cur = None
            continue
        k, v = m.group(1), m.group(2).strip()
        if k == key:
            cur = out.setdefault(v, {key: v, "EDGES": []})
        elif cur is not None:
            if k == "EDGE":
                cur["EDGES"].append(v)
            else:
                cur.setdefault(k, v)
    return out


class Owner:
    """Another track's blueprint (and graph, when one exists), used to resolve its labels."""

    def __init__(self, letter, root, bp_dir, graph_dir, ext_pattern):
        self.letter, self.root, self.bp_dir = letter, root, bp_dir
        self.parts = {}
        pdir = root / bp_dir / "parts"
        if pdir.is_dir():
            for p in sorted(pdir.glob("p*.tex")):
                rel = f"{bp_dir}/parts/{p.name}"
                self.parts[rel] = parse_part(p, rel, ext_pattern)
        self.envs, self.sections, self.labels = {}, set(), {}
        for rel, P in self.parts.items():
            for r in P["results"] + P["steps"] + P["externals"]:
                if r["label"]:
                    self.envs[r["label"]] = r
            for s in P["sections"]:
                if s["label"]:
                    self.sections.add(s["label"])
            for lab, ln in P["labels"].items():
                self.labels[lab] = (rel, ln)
        # frozen definitions transcribed in the owner's Part 0: export -> (anchor node id <label>#<LeanName>, env);
        # they name the owner's future anchor nodes while the owner has no graph yet
        self.frozen_defs = {}
        for rel, P in self.parts.items():
            if part_key(rel) != "p0":
                continue
            for r in P["results"]:
                if r["label"] and r.get("frozen") and r["kind"] in ("definition", "remark"):
                    for name in r["frozen"]:
                        self.frozen_defs[name] = (f"{r['label']}#{ascii_id(name.split('.')[-1])}", r)
        self.frozen_def_ids = {nid: (name, r) for name, (nid, r) in self.frozen_defs.items()}
        self.graph_dir = graph_dir
        self.nodes = parse_graph_blocks(root / graph_dir / "DEPGRAPH.md", "NODE") if graph_dir else {}
        self.cov = parse_graph_blocks(root / graph_dir / "DEPGRAPH_COVERAGE.md", "ITEM") if graph_dir else {}

    def enclosing_env(self, label):
        if label not in self.labels:
            return None
        rel, ln = self.labels[label]
        cands = [r for r in self.parts[rel]["results"] + self.parts[rel]["steps"] if r["label"]
                 and r["first"] <= ln <= r["last"]]
        for r in self.parts[rel]["results"]:
            for p in r.get("proofs", []):
                if p["first"] <= ln <= p["last"] and r["label"]:
                    cands.append(dict(r, first=p["first"], last=p["last"]))
        cands.sort(key=lambda r: (r["kind"] != "step", r["last"] - r["first"]))
        return cands[0]["label"] if cands else None

    def resolve(self, label, own_anchor_by_export):
        """Return (status, [targets], info). Targets are owning-graph node IDs, or own anchor IDs (status 'own')."""
        if "*" in label or "\\" in label:
            return "wildcard", [], ""
        if label in self.sections:
            return "section", [], ""
        if not self.nodes and label in self.frozen_def_ids:
            return "node", [label], "frozen definition of the owner's Part 0 (pending owner graph)"
        if self.nodes:
            if label in self.nodes:
                return "node", [label], ""
            defs = [k for k in self.nodes if k.startswith(label + "#")]
            if defs:
                own = [own_anchor_by_export.get(self.nodes[k].get("FROZEN_DECL", "")) for k in defs]
                if all(own):
                    return "own", sorted(set(own)), f"{self.letter} frozen definitions transcribed as own anchors"
                if any(own):
                    # only some of the label's frozen definitions are transcribed here: the others are not nodes of
                    # this graph (as for definitions the anchor part does not transcribe at all)
                    rest = [k for k, o in zip(defs, own) if not o]
                    return "own", sorted(set(o for o in own if o)), (
                        f"{self.letter} frozen definitions transcribed as own anchors; not transcribed here, hence not "
                        f"nodes of this graph: {', '.join(rest)}")
                return "node", defs, "split definition nodes"
            item = self.cov.get(label)
            if item:
                disp = item.get("DISPOSITION", "")
                if disp.startswith("NODE "):
                    tg = [x.strip() for x in disp[5:].split(",")]
                    return "alias", tg, f"coverage item {label} -> {', '.join(tg)}"
                return "excluded", [label], f"EXCLUDED in the {self.letter} graph: {item.get('REASON', '-')}"
            enc = self.enclosing_env(label)
            if enc and enc in self.nodes:
                return "alias", [enc], f"inner label {label} of {enc}"
            if label in self.labels:
                return "unresolved", [label], f"label exists in {self.bp_dir} but has no {self.letter} graph node"
            return "unknown", [], ""
        if label in self.envs:
            return "node", [label], ""
        enc = self.enclosing_env(label)
        if enc:
            return "alias", [enc], f"inner label {label} of {enc}"
        if label in self.labels:
            return "unresolved", [label], f"label exists in {self.bp_dir} but is not a result, step or external"
        return "unknown", [], ""

    def import_block(self, target, cited_as, writer):
        """Draft node fields for the imported node X:<target>."""
        nid = f"{self.letter}:{target}"
        g = self.nodes.get(target)
        if g:
            kind = g.get("KIND", "?")
            stmt = g.get("STATEMENT_SOURCE", "TODO")
            fields = dict(TITLE=f"[{self.letter}] {g.get('TITLE', target)}", STATEMENT_SOURCE=stmt,
                          SOURCE_HYPOTHESES=g.get("SOURCE_HYPOTHESES", "TODO"),
                          SOURCE_QUANTIFIERS=g.get("SOURCE_QUANTIFIERS", "TODO"),
                          SOURCE_CONCLUSION=g.get("SOURCE_CONCLUSION", "TODO"),
                          CONSTANT_SCOPE=g.get("CONSTANT_SCOPE", "TODO"),
                          CONTRACT_VERSION=g.get("CONTRACT_VERSION", "1"))
            extra = f" There: KIND {kind}, contract {g.get('CONTRACT_ID', '-')} v{g.get('CONTRACT_VERSION', '-')}"
            if g.get("FROZEN_DECL", "-") != "-":
                extra += f", frozen anchor {g['FROZEN_DECL']} ({g.get('FROZEN_ANCHOR_ID', '-')}); not an anchor of this graph"
            if kind == "external":
                head = (f"IMPORTED: external input of the track-{self.letter} graph, node {target} (Mathlib-level; "
                        f"not re-proved there either); shared Lean provider.")
            else:
                head = f"IMPORTED: proved in the track-{self.letter} graph, node {target}; shared Lean provider."
            fields["NOTE"] = head + extra + "." + (f" Cited as {cited_as}." if cited_as else "")
            fields["SOURCE_FIELDS"] = f"copied from docs/graph/{self.letter}/DEPGRAPH.md"
        else:
            r = self.envs.get(target)
            fdef = self.frozen_def_ids.get(target)
            if fdef:
                name, r = fdef
                title = f"{r['title'] or r['label']}: {name}"
                stmt = f"{r['file']}#{r['label']}@L{r['first']}-L{r['last']}"
            elif r:
                rng = (r["first"], r["last"])
                title = r["title"] or target
                stmt = f"{r['file']}#{target}@L{rng[0]}-L{rng[1]}"
            elif target in self.labels:
                rel, ln = self.labels[target]
                title, stmt = target, f"{rel}#{target}@L{ln}-L{ln}"
            else:
                title, stmt = target, "TODO"
            fields = dict(TITLE=f"[{self.letter}] " + re.sub(r"\s+", " ", title), STATEMENT_SOURCE=stmt,
                          SOURCE_HYPOTHESES="TODO", SOURCE_QUANTIFIERS="TODO", SOURCE_CONCLUSION="TODO",
                          CONSTANT_SCOPE="TODO", CONTRACT_VERSION="1",
                          NOTE=((f"IMPORTED (pending {self.letter} graph): frozen definition {fdef[0]}, anchor node "
                                 f"{target} of the track-{self.letter} graph; not an anchor of this graph."
                                 if fdef else
                                 f"IMPORTED{'' if self.nodes else f' (pending {self.letter} graph)'}: proved in the "
                                 f"track-{self.letter} graph, node {target}; shared Lean provider.")
                                + (f" Cited as {cited_as}." if cited_as else "")),
                          SOURCE_FIELDS=f"to be filled from {stmt.split('#')[0]}")
        fields.update(NODE=nid, KIND="external", PROOF_SOURCE="-", CONTRACT_ID=nid, FROZEN_FILE="-", FROZEN_DECL="-",
                      FROZEN_ANCHOR_ID="-", FROZEN_ABI_SHA256="-", DEPS="-", ROUTES="-", ROUTE_FOR="-",
                      TOPOLOGY_STATUS="PROPOSED", EXTRACTOR=writer, REVIEWER="-", LEAN_STATUS="EXTERNAL", LEAN_REF="-",
                      LEAN_NOTE="-")
        return fields


def render_block(f, edges=()):
    txt = "\n".join(f"{k}: {f[k]}" for k in FIELD_ORDER) + "\n"
    for e in edges:
        txt += f"EDGE: {e}\n"
    txt += "\n".join(f"{k}: {f[k]}" for k in TAIL_ORDER) + "\n"
    return txt


def render_item(c):
    return (f"ITEM: {c['item']}\nKIND: {c['kind']}\nSOURCE: {c['source']}\nDISPOSITION: {c['disp']}\n"
            f"REASON: {c.get('reason', 'mechanical inventory of a labelled unit')}\nCOVERAGE_STATUS: PROPOSED\n"
            f"EXTRACTOR: {c.get('extractor', 'mechanical-preextract')}\nREVIEWER: -\n")


def default_parts(root, bp):
    def order(p):
        m = re.match(r"p(\d+)([a-z]?)", p.stem)
        return (int(m.group(1)), m.group(2)) if m else (10 ** 6, p.stem)
    return [f"{bp}/parts/{p.name}" for p in sorted((root / bp / "parts").glob("p*.tex"), key=order)]


def load_owners(root, spec, graphs, self_track, ext_pattern):
    owners = {}
    gmap = dict(x.split("=", 1) for x in graphs.split(",") if x) if graphs else {}
    for item in spec.split(","):
        letter, bp = item.split("=", 1)
        if letter == self_track:
            continue
        gdir = gmap.get(letter)
        if gdir is None and (root / f"docs/graph/{letter}/DEPGRAPH.md").exists():
            gdir = f"docs/graph/{letter}"
        owners[letter] = Owner(letter, root, bp, gdir, ext_pattern)
    return owners


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", required=True)
    ap.add_argument("--blueprint", required=True, help="blueprint directory, e.g. blueprint-I")
    ap.add_argument("--track", required=True, help="this track's letter (its \\<X>ref is internal)")
    ap.add_argument("--parts", default="", help="comma-separated part files (default: all <blueprint>/parts/p*.tex)")
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--anchor-part", default="p0")
    ap.add_argument("--proved-in", default="",
                    help="anchor=pA+pB,...: parts proving (or setting up the proof of) an anchor; their references to "
                         "that anchor are statement references (its hypotheses or conclusion), never uses, and are "
                         "dropped")
    ap.add_argument("--owner", default="K=blueprint,I=blueprint-I,N=blueprint-N,P=blueprint-P")
    ap.add_argument("--owner-graph", default="", help="X=docs/graph/X,... (default: docs/graph/X if it exists)")
    ap.add_argument("--writer", default="claude-suborch-INP", help="EXTRACTOR tag of the imported nodes")
    ap.add_argument("--external-pattern", default=r":(?:ext|x)-")
    ap.add_argument("--all-prose", action="store_true",
                    help="inventory every unlabelled prose paragraph outside the nodes as a coverage item, not only "
                         "those with cross-references (list wrappers and macro lines are skipped)")
    ap.add_argument("--prose-anchor", action="append", default=[],
                    help="NODE=EXPORT@LX-LY (repeatable): a frozen definition that the anchor part transcribes in "
                         "unlabelled prose (no \\frozen tag) becomes the definition anchor NODE (ID <label>#<LeanName>) "
                         "with statement locator LX-LY of the anchor part; no candidate DEPS are read for it")
    ap.add_argument("--anchor-map", action="append", default=[],
                    help="LABEL=EXPORT[+EXPORT...] (repeatable): bind a labelled environment of an anchor part to "
                         "frozen manifest exports (as if it carried \\frozen{...})")
    a = ap.parse_args()
    anchor_parts = set(x for x in a.anchor_part.split(",") if x)
    anchor_map = {}
    for spec in a.anchor_map:
        lab, exps = spec.split("=", 1)
        anchor_map[lab.strip()] = [x.strip() for x in exps.split("+") if x.strip()]
    root = Path(a.root).resolve()
    REF, XREF = ref_regexes(a.track)
    manifest = {e["export"]: e for e in json.loads((root / a.manifest).read_text())["anchors"]}
    rels = [x for x in a.parts.split(",") if x] or default_parts(root, a.blueprint)
    rels = [r if "/" in r else f"{a.blueprint}/parts/{r}" for r in rels]
    parts = {part_key(rel): parse_part(root / rel, rel, a.external_pattern) for rel in rels}
    owners = load_owners(root, a.owner, a.owner_graph, a.track, a.external_pattern)
    report = dict(skipped=[], unresolved=[], frozen_unresolved=[], source_dropped=0, cycles=[], unlabelled=[],
                  aliases={}, missing_proof_owner=[])

    nodes, alias, owner_of, frozen_theorem_node, own_anchor_by_export = {}, {}, {}, {}, {}

    def loc(file, label, first, last):
        return f"{file}#{label}@L{first}-L{last}"

    missing_owner = [p for P in parts.values() for p in P["missing_owner"]]
    for key, P in parts.items():
        for r in P["unlabelled_results"]:
            report["unlabelled"].append(f"{P['rel']}:L{r['first']} unlabelled {r['kind']} {r['title']!r}")
        for s in P["unlabelled_steps"]:
            report["unlabelled"].append(f"{P['rel']}:L{s['first']} unlabelled proofstep {s['title']!r}")
        for r in P["results"]:
            if not r["label"]:
                continue
            base = dict(part=key, title=r["title"] or r["label"], kind=r["kind"] if r["kind"] != "remark" else "claim",
                        env=r["kind"], statement=loc(r["file"], r["label"], r["first"], r["last"]),
                        proof="-", file=r["file"], first=r["first"], last=r["last"], proofs=r.get("proofs", []),
                        frozen=None)
            if r["kind"] == "assumption":
                base["kind"] = "definition"
                base["note"] = "standing hypotheses of a part (a local hypothesis package, KIND definition; see SPEC)"
            if r.get("proofs"):
                p = r["proofs"][0]
                base["proof"] = loc(p["file"], r["label"], p["first"], p["last"])
            elif r["kind"] == "remark":
                base["proof"] = base["statement"]
                base["note"] = "remark: its justification is inline (confirm, or exclude if not a mathematical claim)"
            elif r["kind"] not in ("definition", "assumption") and INLINE_PROOF.search(
                    "\n".join(P["lines"][r["first"] - 1:r["last"]])):
                # a result whose proof is written inside its own environment (blueprint-N `bpN:p11:ext-part4`)
                base["proof"] = base["statement"]
                base["note"] = "inline proof inside the statement environment (no proof environment)"
            fz = r.get("frozen") or anchor_map.get(r["label"], [])
            if r["kind"] == "convention":
                base["kind"] = "definition"
                base["note"] = "convention environment (KIND definition)"
            if key in anchor_parts and fz:
                if r["kind"] == "definition" or all(manifest[x].get("kind") == "definition" for x in fz):
                    # a remark that transcribes a frozen definition (blueprint-N `bpN:p0:strip`) is a definition node
                    if r["kind"] != "definition":
                        base = dict(base, kind="definition", note="-", proof="-")
                    for name in fz:
                        e = manifest[name]
                        nid = f"{r['label']}#{ascii_id(name.split('.')[-1])}"
                        nodes[nid] = dict(base, id=nid, title=f"{r['title']}: {name}", frozen=e)
                        own_anchor_by_export[name] = nid
                    alias[r["label"]] = [f"{r['label']}#{ascii_id(x.split('.')[-1])}" for x in fz]
                    continue
                assert len(fz) == 1, r["label"]
                base["frozen"] = manifest[fz[0]]
                frozen_theorem_node[fz[0]] = r["label"]
                own_anchor_by_export[fz[0]] = r["label"]
            elif fz:
                base["frozen_names"] = fz
            nodes[r["label"]] = dict(base, id=r["label"])
            alias[r["label"]] = [r["label"]]
        for s in P["steps"]:
            if not s["label"]:
                continue
            nodes[s["label"]] = dict(part=key, id=s["label"], kind="step", title=s["title"], file=s["file"],
                                     statement=loc(s["file"], s["label"], s["first"], s["last"]),
                                     proof=loc(s["file"], s["label"], s["first"], s["last"]), first=s["first"],
                                     last=s["last"], frozen=None)
            owner_of[s["label"]] = s["owner"]
            alias[s["label"]] = [s["label"]]
        for x in P["externals"]:
            nodes[x["label"]] = dict(part=key, id=x["label"], kind="external", title=x["title"], file=x["file"],
                                     statement=loc(x["file"], x["label"], x["first"], x["last"]), proof="-",
                                     first=x["first"], last=x["last"], frozen=None)
            alias[x["label"]] = [x["label"]]

    anchor_rel = next((P["rel"] for k, P in parts.items() if k in anchor_parts), None)
    for spec in a.prose_anchor:
        m = re.fullmatch(r"(?P<nid>[^=]+)=(?P<exp>[^@]+)@L(?P<x>\d+)-L(?P<y>\d+)", spec.strip())
        assert m and anchor_rel, f"bad --prose-anchor {spec!r} (or no anchor part)"
        nid, exp, x, y = m.group("nid"), m.group("exp"), int(m.group("x")), int(m.group("y"))
        e = manifest[exp]
        assert e.get("kind") == "definition", f"--prose-anchor {exp} is not a frozen definition"
        nodes[nid] = dict(part=sorted(anchor_parts)[0], id=nid, kind="definition", title=f"prose transcription: {exp}",
                          file=anchor_rel, statement=loc(anchor_rel, nid.split("#")[0], x, y), proof="-", first=x,
                          last=y, proofs=[], frozen=e, prose_anchor=True,
                          note="frozen definition transcribed in unlabelled Part-0 prose (no \\frozen tag); "
                               "anchor bound by the SPEC")
        own_anchor_by_export[exp] = nid
        alias[nid] = [nid]

    for p in missing_owner:
        nid = p["owner"]
        if nid in nodes:
            nodes[nid].setdefault("proofs", []).append(p)
            if nodes[nid]["proof"] == "-":
                nodes[nid]["proof"] = loc(p["file"], nid, p["first"], p["last"])
        else:
            report["missing_proof_owner"].append(f"{p['file']}:L{p['first']} proof of unknown {nid}")

    # inner labels (items, equations) -> enclosing node; innermost wins (steps before results)
    ranges = []
    for nid, nd in nodes.items():
        ranges.append((nd["file"], nd["first"], nd["last"], nid, nd["kind"] == "step"))
        for p in nd.get("proofs", []):
            ranges.append((p["file"], p["first"], p["last"], nid, False))
    section_labels = {s["label"] for P in parts.values() for s in P["sections"] if s["label"]}
    for key, P in parts.items():
        for lab, ln in P["labels"].items():
            if lab in alias or lab in section_labels:
                continue
            cands = [r for r in ranges if r[0] == P["rel"] and r[1] <= ln <= r[2]]
            cands.sort(key=lambda r: (not r[4], r[2] - r[1]))
            if cands:
                tgt = cands[0][3]
                alias[lab] = alias.get(tgt, [tgt]) if "#" not in tgt else [tgt]

    # cross-track resolution
    imports = {}   # import id -> dict(owner, target, cited set, status, info)

    def resolve_x(letter, lab, where):
        o = owners.get(letter)
        if o is None:
            report["unresolved"].append(f"{where}: \\{letter}ref{{{lab}}}: no owning blueprint for {letter}")
            return []
        status, targets, info = o.resolve(lab, own_anchor_by_export)
        if status in ("wildcard", "section", "unknown"):
            report["skipped" if status != "unknown" else "unresolved"].append(
                f"{where}: \\{letter}ref{{{lab}}} ({status})")
            return []
        if status == "own":
            report["aliases"][f"{letter}:{lab}"] = targets
            if "not transcribed here" in info:
                report["skipped"].append(f"{where}: \\{letter}ref{{{lab}}} ({info})")
            return targets
        out = []
        for t in targets:
            iid = f"{letter}:{t}"
            imp = imports.setdefault(iid, dict(owner=letter, target=t, cited=set(), status=status, info=info,
                                               users=set()))
            imp["cited"].add(f"\\{letter}ref{{{lab}}}")
            if status in ("excluded", "unresolved"):
                report["unresolved"].append(f"{where}: \\{letter}ref{{{lab}}} -> {iid} ({info})")
            if t != lab:
                report["aliases"][f"{letter}:{lab}"] = [iid]
            out.append(iid)
        return out

    def resolve(lab):
        return alias.get(lab, [])

    def refs_in(P, first, last, skip=(), keep_source=True):
        out = []
        for k in range(first - 1, last):
            if any(s[0] <= k + 1 <= s[1] for s in skip):
                continue
            in_source = (k + 1) in P["source_lines"]
            if in_source and not keep_source:
                n_drop = len(REF.findall(P["lines"][k])) + len(XREF.findall(P["lines"][k]))
                report["source_dropped"] += n_drop
                continue
            tag = "; in \\source: provenance unless consumed" if in_source else ""
            for m in REF.finditer(P["lines"][k]):
                for lab in (m.group(1) or m.group(2)).split(","):
                    out.append(("int", lab.strip(), k + 1, tag))
            for m in XREF.finditer(P["lines"][k]):
                for lab in m.group(2).split(","):
                    out.append((m.group(1), lab.strip(), k + 1, tag))
        return out

    by_file = {P["rel"]: P for P in parts.values()}
    for nid, nd in nodes.items():
        deps = {}
        P = by_file[nd["file"]]
        keep_src = nd["part"] not in anchor_parts
        if nd["kind"] == "step":
            uses = [(t, lab, ln, "step", tag) for t, lab, ln, tag in refs_in(P, nd["first"], nd["last"])]
        elif nd["kind"] == "external":
            uses = []
            cited = [f"\\{t}ref{{{lab}}}" if t != "int" else f"\\ref{{{lab}}}"
                     for t, lab, ln, tag in refs_in(P, nd["first"], nd["last"])]
            if cited:
                nd["note"] = ("external item that cites " + ", ".join(cited) + ": if it only restates the cited "
                              "external, exclude it as an alias and point its consumers at the cited node (SPEC)")
            for t, lab, ln, tag in refs_in(P, nd["first"], nd["last"]):
                if t != "int":
                    resolve_x(t, lab, f"{nd['file']}:L{ln}")
        elif nd.get("prose_anchor"):
            uses = []
        else:
            uses = [(t, lab, ln, "statement", tag)
                    for t, lab, ln, tag in refs_in(P, nd["first"], nd["last"], keep_source=keep_src)]
            for p in nd.get("proofs", []):
                PP = by_file[p["file"]]
                step_ranges = [(nodes[s]["first"], nodes[s]["last"]) for s in p.get("steps", []) if s in nodes]
                uses += [(t, lab, ln, "proof", tag) for t, lab, ln, tag in
                         refs_in(PP, p["first"], p["last"], step_ranges,
                                 keep_source=part_key(PP["rel"]) not in anchor_parts)]
                for s in p.get("steps", []):
                    if s in nodes:
                        deps.setdefault(s, (p["file"], nodes[s]["first"], "proof step of this result"))
        for t, lab, ln, where, tag in uses:
            f = nd["file"]
            if where == "proof":
                f = next((p["file"] for p in nd.get("proofs", []) if p["first"] <= ln <= p["last"]), f)
            if t == "int":
                targets, cite = resolve(lab), f"\\ref{{{lab}}}"
            else:
                targets, cite = resolve_x(t, lab, f"{f}:L{ln}"), f"\\{t}ref{{{lab}}}"
            for tgt in targets:
                if tgt == nid or tgt == owner_of.get(nid):
                    continue
                if owner_of.get(nid) and tgt in alias.get(owner_of[nid], []):
                    continue
                deps.setdefault(tgt, (f, ln, f"cited at this line ({where}; {cite}{tag})"))
        nd["deps"] = deps

    # \frozen{...} outside the anchor part
    for nid, nd in nodes.items():
        for name in nd.get("frozen_names", []):
            if name in frozen_theorem_node:
                anchor = frozen_theorem_node[name]
                if anchor != nid:
                    nodes[anchor]["deps"].setdefault(nid, (nd["file"], nd["first"],
                                                           f"this result carries \\frozen{{{name}}}: it proves the anchor"))
                    if nodes[anchor]["proof"] == "-":
                        nodes[anchor]["proof"] = nd["statement"]
                continue
            if name in own_anchor_by_export:
                tgt = own_anchor_by_export[name]
                if tgt != nid:
                    nd["deps"].setdefault(tgt, (nd["file"], nd["first"],
                                                f"this result carries \\frozen{{{name}}} (a statement about it)"))
                continue
            hit = None
            for letter, o in owners.items():
                for gid, g in o.nodes.items():
                    if g.get("FROZEN_DECL") == name:
                        hit = (letter, gid)
            if not hit:
                for letter, o in owners.items():
                    if not o.nodes and name in o.frozen_defs:
                        hit = (letter, o.frozen_defs[name][0])
            if hit:
                iid = f"{hit[0]}:{hit[1]}"
                imp = imports.setdefault(iid, dict(owner=hit[0], target=hit[1], cited=set(), status="node", info="",
                                                   users=set()))
                imp["cited"].add(f"\\frozen{{{name}}}")
                nd["deps"].setdefault(iid, (nd["file"], nd["first"],
                                            f"this result carries \\frozen{{{name}}}, a track-{hit[0]} frozen declaration"))
            else:
                report["frozen_unresolved"].append(f"{nid}: \\frozen{{{name}}}")

    def proved_parts(spec):
        out = {}
        for x in spec.split(","):
            if x:
                anchor, ps = x.split("=", 1)
                out[anchor] = set(ps.split("+"))
        return out

    for anchor, ps in proved_parts(a.proved_in).items():
        for nid, nd in nodes.items():
            if nd["part"] in ps and anchor in nd["deps"] and nid != anchor:
                del nd["deps"][anchor]
                nd["note"] = (nd.get("note", "-") if nd.get("note", "-") != "-" else "") + \
                    f" [pre-extract: dropped reference to {anchor}, which part {nd['part']} proves or sets up]"
    for nid, nd in nodes.items():
        nd["deps"].pop(nid, None)

    # imports cited anywhere in the corpus (prose, externals, \source included), so every candidate target exists
    for key, P in parts.items():
        for k, line in enumerate(P["lines"]):
            if key in anchor_parts and (k + 1) in P["source_lines"]:
                continue
            for m in XREF.finditer(line):
                for lab in m.group(2).split(","):
                    resolve_x(m.group(1), lab.strip(), f"{P['rel']}:L{k + 1}")
    report["skipped"] = sorted(set(report["skipped"]))
    report["unresolved"] = sorted(set(report["unresolved"]))
    for nid, nd in nodes.items():
        for d in nd["deps"]:
            if d in imports:
                imports[d]["users"].add(nid)

    # candidate cycles (informational)
    graph = {nid: [d for d in nd["deps"] if d in nodes] for nid, nd in nodes.items()}
    color, stack = {}, []

    def dfs(u):
        color[u] = 1
        stack.append(u)
        for v in graph[u]:
            if color.get(v) == 1:
                cyc = stack[stack.index(v):] + [v]
                report["cycles"].append(" -> ".join(cyc))
            elif v not in color:
                dfs(v)
        stack.pop()
        color[u] = 2

    import sys
    sys.setrecursionlimit(100000)
    for u in graph:
        if u not in color:
            dfs(u)

    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    serial = {k: {kk: vv for kk, vv in v.items() if kk not in ("proofs",)} for k, v in nodes.items()}
    for v in serial.values():
        v["deps"] = {k: list(x) for k, x in v["deps"].items()}
        if v.get("frozen"):
            v["frozen"] = {k: v["frozen"][k] for k in ("id", "path", "export", "contract", "abi_sha256")}
    (out / "nodes.json").write_text(json.dumps(serial, indent=1, ensure_ascii=False))

    def block(nd):
        fz = nd.get("frozen")
        f = dict(NODE=nd["id"], KIND=nd["kind"], TITLE=re.sub(r"\s+", " ", nd["title"]), STATEMENT_SOURCE=nd["statement"],
                 PROOF_SOURCE=nd["proof"], CONTRACT_ID=fz["contract"]["id"] if fz else nd["id"],
                 CONTRACT_VERSION=fz["contract"]["version"] if fz else "1", SOURCE_HYPOTHESES="TODO",
                 SOURCE_QUANTIFIERS="TODO", SOURCE_CONCLUSION="TODO", CONSTANT_SCOPE="TODO",
                 FROZEN_FILE=fz["path"] if fz else "-", FROZEN_DECL=fz["export"] if fz else "-",
                 FROZEN_ANCHOR_ID=fz["id"] if fz else "-", FROZEN_ABI_SHA256=fz["abi_sha256"] if fz else "-",
                 DEPS=", ".join(nd["deps"]) if nd["deps"] else "-", ROUTES="-", ROUTE_FOR="-",
                 TOPOLOGY_STATUS="PROPOSED", EXTRACTOR="mechanical-preextract", REVIEWER="-",
                 LEAN_STATUS="EXTERNAL" if nd["kind"] == "external" else "NOT_STARTED", LEAN_REF="-", LEAN_NOTE="-",
                 NOTE=(nd.get("note", "-") or "-").strip() or "-")
        edges = [f"{d} | {fl}#{nd['id'].split('#')[0]}@L{ln}-L{ln} | {why}" for d, (fl, ln, why) in nd["deps"].items()]
        return render_block(f, edges)

    for key, P in parts.items():
        ids = sorted((v for v in nodes.values() if v["part"] == key), key=lambda v: (v["first"], v["kind"] != "step"))
        (out / f"{key}.md").write_text("\n".join(block(v) for v in ids))
        cov = []
        for v in ids:
            cov.append(dict(item=v["id"], kind=v["kind"] if v["kind"] not in ("step", "claim") else
                            ("proof-region" if v["kind"] == "step" else "claim"),
                            source=v["statement"], disp=f"NODE {v['id']}"))
        rel = P["rel"]
        for s in P["sections"]:
            sid = s["label"] or f"{key}:heading-L{s['line']}"
            cov.append(dict(item=f"heading:{sid}", kind="heading", source=f"{rel}#{sid}@L{s['line']}-L{s['line']}",
                            disp="EXCLUDED", reason="section heading; its results are inventoried separately"))
        for ln in P["gaps"]:
            cov.append(dict(item=f"{key}:sourcegap-L{ln}", kind="proof-region", source=f"{rel}#sourcegap@L{ln}-L{ln}",
                            disp="TODO", reason="a \\sourcegap note: model as a node with SOURCE_GAP: in NOTE, map it "
                            "to the node(s) that supply the bridge, or exclude with reason"))
        for ln in P["sources"]:
            cov.append(dict(item=f"{key}:source-L{ln}", kind="citation", source=f"{rel}#source@L{ln}-L{ln}",
                            disp="EXCLUDED", reason="provenance note for a result proved in the blueprint (confirm; an "
                            "unproved cited input must instead become an external node)"))
        # prose with references outside every node
        covered = set()
        for v in nodes.values():
            if v["file"] == rel:
                covered.update(range(v["first"], v["last"] + 1))
            for p in v.get("proofs", []):
                if p["file"] == rel:
                    covered.update(range(p["first"], p["last"] + 1))
        covered |= P["source_lines"] | P["gap_lines"] | {s["line"] for s in P["sections"]}
        L = P["lines"]
        para = []

        def flush():
            has_ref = any(REF.search(L[k - 1]) or XREF.search(L[k - 1]) for k in para)
            if para and (has_ref or (a.all_prose and any(not WRAPPER.match(L[k - 1].strip()) for k in para))):
                a0, b0 = para[0], para[-1]
                cov.append(dict(item=f"{key}:prose-L{a0}-L{b0}", kind="proof-region",
                                source=f"{rel}#prose@L{a0}-L{b0}", disp="TODO",
                                reason="unlabelled prose with cross-references outside every node: map it to the "
                                "node(s) whose statement or proof relies on it (with EDGEs located here), or exclude "
                                "with a reason (motivation, pointer, provenance)" if has_ref else
                                "unlabelled prose without cross-references outside every node (--all-prose): map it "
                                "to the node(s) that rely on a fact or datum it states (or make it a node), or exclude "
                                "with a reason (motivation, outline, notation only)"))
            para.clear()
        for k in range(1, len(L) + 1):
            line = L[k - 1].strip()
            if k in covered or not line or line.startswith("%"):
                flush()
                continue
            para.append(k)
        flush()
        (out / f"coverage-{key}.md").write_text("\n".join(render_item(c) for c in cov))
        nk = {}
        for v in ids:
            nk[v["kind"]] = nk.get(v["kind"], 0) + 1
        print(key, "nodes", len(ids), nk, "edges", sum(len(v["deps"]) for v in ids), "coverage", len(cov))

    # imported nodes
    blocks, citems, ijson = [], [], {}
    for iid in sorted(imports):
        imp = imports[iid]
        o = owners[imp["owner"]]
        f = o.import_block(imp["target"], ", ".join(sorted(imp["cited"])), a.writer)
        if imp["status"] in ("excluded", "unresolved"):
            f["NOTE"] += f" WARNING: {imp['info']}."
        ijson[iid] = dict(owner=imp["owner"], target=imp["target"], status=imp["status"], info=imp["info"],
                          cited=sorted(imp["cited"]), candidate_users=sorted(imp["users"]),
                          source_fields=f.pop("SOURCE_FIELDS"))
        blocks.append(render_block(f))
        citems.append(dict(item=iid, kind="external", source=f["STATEMENT_SOURCE"], disp=f"NODE {iid}",
                           reason=f"imported node (track {imp['owner']}): its statement is proved, or is an external "
                           f"input, in the track-{imp['owner']} graph; not extracted here", extractor=a.writer))
    (out / "imports.md").write_text("\n".join(blocks))
    (out / "coverage-imports.md").write_text("\n".join(render_item(c) for c in citems))
    (out / "imports.json").write_text(json.dumps(ijson, indent=1, ensure_ascii=False))
    (out / "report.json").write_text(json.dumps(report, indent=1, ensure_ascii=False))
    by = {}
    for v in ijson.values():
        by[v["owner"]] = by.get(v["owner"], 0) + 1
    print("imports", len(ijson), by, "with candidate users", sum(1 for v in ijson.values() if v["candidate_users"]))
    print("report: skipped", len(report["skipped"]), "unresolved", len(report["unresolved"]), "frozen_unresolved",
          len(report["frozen_unresolved"]), "source refs dropped in anchor part", report["source_dropped"],
          "candidate cycles", len(report["cycles"]), "unlabelled", len(report["unlabelled"]),
          "missing proof owners", len(report["missing_proof_owner"]))


if __name__ == "__main__":
    main()

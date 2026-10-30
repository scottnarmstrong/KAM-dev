#!/usr/bin/env python3
"""SO-DATA-2: emit one lunar torus (SO-DATA-1's `<which>_cert.json` + `<which>_advice.json`) as option-A Lean data
modules under KAM/SpinOrbit/Data/<Torus>/ (untrusted tooling; the kernel checks whatever the data denotes).

    python3 sofx_lean.py lower|upper GENDIR WITNESS.json [ROOT]

SO-DATA3 (v2 certifier, D-ruling of the SO-V2PKG addendum): backend `SoBackendV2 = CertFixed 96`, parameters
`lunarR2` at the literals of `KAM.SpinOrbit.LunarConstsR2` (which must equal the JSON's), Hamiltonian
`soRotHamExprScaled lunarR2TimeScale`; the routeARefined witness (sodata3_witness.py) is emitted as
`Data/<Torus>/Witness.lean`.

Format (design §7.2, option A): at most `ROWS` rows per `def`, at most `MAXLINES` lines per file, every line at most
100 columns.  A Fourier term is the row `tm k₀ k₁ re im` (`Data/Format.lean`); advice windows are run-length coded
token lists (`unzero`: a zero is followed by its run length), as SO-DATA-1 emits them.  An integer is written in
decimal or hex, whichever is shorter.  The module tree is deterministic.
"""
import json
import os
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(0)

HERE = os.path.dirname(os.path.abspath(__file__))
ROWS = 32
MAXLINES = 1400
COLS = 100

HEADER = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

{imports}

/-!
# {title}

{doc}
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.{torus}

open {opens}
"""


def num(v):
    v = int(v)
    a = abs(v)
    s = str(a)
    h = "0x%x" % a
    t = h if len(h) < len(s) else s
    return "(-%s)" % t if v < 0 else t


def nat_lit(v):
    """a ℕ literal that fits a line (natChunks for long ones): list of lines."""
    s = str(v)
    if len(s) <= 80:
        return [s]
    cs = []
    head = len(s) % 80 or 80
    cs = [s[:head]] + [s[i:i + 80] for i in range(head, len(s), 80)]
    return ["(natChunks [" + cs[0] + ","] + ["  " + c + ("," if i + 2 < len(cs) else "])")
                                               for i, c in enumerate(cs[1:])]


def rat_lit(q):
    """a ℚ term as lines."""
    q = F(q)
    a, b = q.numerator, q.denominator
    one = ("(%d / %d)" % (a, b)) if b != 1 else ("(%d)" % a)
    if len(one) <= 90:
        return [one]
    na = nat_lit(abs(a))
    nb = nat_lit(b)
    sign = "-" if a < 0 else ""
    return ["(ratOf " + ("true" if a < 0 else "false")] + ["  " + l for l in na] + ["  " + l for l in nb] + [")"]


class Tree:
    """collects files"""

    def __init__(self, root, torus):
        self.root, self.torus = root, torus
        self.files = {}

    @staticmethod
    def cap(rel):
        return rel[0].upper() + rel[1:]

    def path(self, rel):
        return os.path.join(self.root, "KAM", "SpinOrbit", "Data", self.torus, self.cap(rel) + ".lean")

    def module(self, rel):
        return "KAM.SpinOrbit.Data.%s.%s" % (self.torus, self.cap(rel))

    def write(self, rel, imports, title, doc, body, opens="KAM.Certificate"):
        text = HEADER.format(imports="\n".join("public import " + i for i in imports), title=title, doc=doc,
                             torus=self.torus, opens=opens) + "\n" + "\n".join(body).rstrip() + \
            "\n\nend KAM.SpinOrbit.Data.%s\n" % self.torus
        for i, l in enumerate(text.splitlines()):
            assert len(l) <= COLS, (rel, i, l)
        n = text.count("\n")
        assert n <= 1500, (rel, n)
        self.files[rel] = text


FORMAT = "KAM.SpinOrbit.Data.Format"


def row_lines(parts, indent="  "):
    """parts: tokens of one row; pack greedily into lines of <= COLS (with trailing comma room)."""
    lines, cur = [], indent
    for p in parts:
        cand = (cur + " " + p) if cur.strip() else (cur + p)
        if len(cand) <= COLS - 1:
            cur = cand
        else:
            lines.append(cur)
            cur = indent + "  " + p
    lines.append(cur)
    return lines


def emit_blob(tree, name, typ, rows, title):
    """rows: list of line-lists (one row each).  Writes chunk files `<name>NN` with defs `name.cJ` of <= ROWS rows,
    and the index `<name>` defining `name : typ := List.flatten [...]`.  Returns the index module."""
    chunks = [rows[i:i + ROWS] for i in range(0, len(rows), ROWS)] or [[]]
    files, cur, curlen = [], [], 0
    for j, ch in enumerate(chunks):
        body = ["def %s.c%d : %s := [" % (name, j, typ)]
        for r_i, r in enumerate(ch):
            ls = list(r)
            ls[-1] = ls[-1] + ("," if r_i + 1 < len(ch) else "]")
            body += ls
        if not ch:
            body[-1] += "]"
        body.append("")
        if curlen + len(body) > MAXLINES and cur:
            files.append(cur)
            cur, curlen = [], 0
        cur.append(body)
        curlen += len(body)
    files.append(cur)
    mods = []
    j0 = 0
    for fi, defs in enumerate(files):
        rel = "%s%02d" % (name.replace(".", ""), fi)
        body = [l for d in defs for l in d]
        tree.write(rel, [FORMAT], "%s, part %d (generated)" % (title, fi),
                   "Generated by `scripts/spin_orbit/sofx_lean.py` from SO-DATA3's data. Do not edit.", body)
        mods.append(tree.module(rel))
    names = ["%s.c%d" % (name, j) for j in range(len(chunks))]
    body = row_lines(["def %s : %s := List.flatten [" % (name, typ)], "")
    lst = row_lines([n + "," for n in names[:-1]] + [names[-1] + "]"], "  ")
    body = body + lst
    rel = name.replace(".", "")
    tree.write(rel, mods, "%s (generated)" % title,
               "The concatenation of the chunks.\nGenerated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", body)
    return tree.module(rel)


def term_row(t):
    (k0, k1), (re, im) = t[0], t[1]
    return row_lines(["tm", num(k0), num(k1), num(re), num(im)])


def emit_poly(tree, name, terms, title):
    return emit_blob(tree, name, "List (CertKey × CC SoBackendV2)", [term_row(t) for t in terms], title)


def tokens_rows(toks):
    """token list → rows of one line each, packed."""
    rows, cur = [], "  "
    for t in toks:
        s = num(t)
        cand = cur + (" " if cur.strip() else "") + s + ","
        if len(cand) <= COLS - 1:
            cur = cand
        else:
            rows.append([cur.rstrip(",")])
            cur = "  " + s + ","
    if cur.strip():
        rows.append([cur.rstrip(",")])
    return rows


def lay(l):
    lo, dims, stride, width, br = l
    return "⟨[%s], [%s], [%s], %d, %d⟩" % (", ".join(num(x) for x in lo), ", ".join(str(x) for x in dims),
                                           ", ".join(str(x) for x in stride), width, br)


def emit_advice(tree, book_name, entries):
    """entries: [(key, adv)].  Returns (index module, def name)."""
    files, cur, curlen = [], [], 0
    prods = []
    for pi, (key, adv) in enumerate(entries):
        pname = "%s.p%d" % (book_name, pi)
        if adv[0] == "direct":
            prods.append((key, None))
            continue
        P = adv[1]
        defs = []
        parts = []
        for part, a in zip(("rr", "ii", "ri", "ir"), adv[2:]):
            wins = []
            for wi, w in enumerate(a["rounded"]):
                rows = tokens_rows(w)
                if len(rows) <= 2:
                    ts = [num(t) for t in w]
                    ts = [x + "," for x in ts[:-1]] + [ts[-1] + "]"]
                    ts[0] = "unzero [" + ts[0]
                    wins.append(ts)
                else:
                    chunks = [rows[i:i + ROWS] for i in range(0, len(rows), ROWS)]
                    cn = []
                    for ci, ch in enumerate(chunks):
                        dn = "%s.%sW%dC%d" % (pname, part, wi, ci)
                        body = ["def %s : List ℤ := [" % dn]
                        for r_i, r in enumerate(ch):
                            body.append(r[0] + ("," if r_i + 1 < len(ch) else "]"))
                        defs.append(body + [""])
                        cn.append(dn)
                    toks = [c + "," for c in cn[:-1]] + [cn[-1] + "])"]
                    toks[0] = "unzero (List.flatten [" + toks[0]
                    wins.append(toks)
            body = ["def %s.%s : PackedAdvice where" % (pname, part),
                    "  la := " + lay(a["la"]), "  lb := " + lay(a["lb"]), "  target := " + lay(a["target"]),
                    "  scale := %d" % a["scale"], "  outLog := %d" % a["outLog"],
                    "  rounded := [" if wins else "  rounded := []"]
            for wi, w in enumerate(wins):
                ls = row_lines(w[:-1] + [w[-1] + ("," if wi + 1 < len(wins) else "]")], "    ")
                body += ls
            defs.append(body + [""])
            parts.append("%s.%s" % (pname, part))
        prods.append((key, (P, parts)))
        for d in defs:
            if curlen + len(d) > MAXLINES and cur:
                files.append(cur)
                cur, curlen = [], 0
            cur.append(d)
            curlen += len(d)
    if cur:
        files.append(cur)
    mods = []
    for fi, defs in enumerate(files):
        rel = "%s%03d" % (book_name.replace(".", ""), fi)
        tree.write(rel, [FORMAT] + mods[-1:], "Advice book `%s`, part %d (generated)" % (book_name, fi),
                   "Packed-product advice (run-length coded windows).\n"
                   "Generated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", [l for d in defs for l in d])
        mods.append(tree.module(rel))
    body = ["def %s : AdviceBook := [" % book_name]
    for i, (key, p) in enumerate(prods):
        end = "," if i + 1 < len(prods) else "]"
        k = "[" + ", ".join(str(x) for x in key) + "]"
        if p is None:
            body.append("  (%s, .direct)%s" % (k, end))
        else:
            P, parts = p
            body += row_lines(["(%s, .packed %d" % (k, P)] + parts[:-1] + [parts[-1] + ")" + end], "  ")
    rel = book_name.replace(".", "")
    tree.write(rel, mods, "Advice book `%s` (generated)" % book_name,
               "Generated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", body)
    return tree.module(rel)


def cc(c):
    return "⟨⟨%s⟩, ⟨%s⟩⟩" % (num(c[0]), num(c[1]))


CONSTS = {"lower": ("lunarR2LowerErr", "lunarR2LowerDisp"), "upper": ("lunarR2UpperErr", "lunarR2UpperDisp")}
PKG_R2 = dict(tau="1", rho="1/140", rhoInf="1/140000", M="54/25", sK="1873/1000", sB="2689/500", sT="13/25",
              mu="1/160", gbar="2000000/67000067", som="2", nu="1/1000000", gamma="2000000/67000067",
              s="1000001/1000000", E0="0")


def consts_lean(witness):
    """the literal values of `KAM/SpinOrbit/LunarConstsR2.lean` (checked against it by `emit_cert`)."""
    return {CONSTS[o["which"]][0]: F(o["err"]) for o in witness} | \
        {CONSTS[o["which"]][1]: F(o["disp"]) for o in witness}


def emit_cert(tree, which, d, consts):
    """`Cert.lean`: the torus certificate and the graph certificate (params through `lunarR2` and the
    literal constants of `KAM.SpinOrbit.LunarConstsR2`, which must equal the JSON's)."""
    en, dn = CONSTS[which]
    p = d["params"]
    assert F(p["err"]) == consts[en] and F(p["disp"]) == consts[dn], (p["err"], p["disp"])
    for k, v in PKG_R2.items():
        assert F(p[k]) == F(v), (k, p[k], v)
    assert int(d["precision"]) == 96
    root5 = __import__("math").isqrt(5 * 10 ** 220)
    body = ["/-- The enclosure `√5 ∈ [rootLo, rootHi]`. -/", "def rootLo : ℚ :="]
    body += ["  " + l for l in rat_lit(F(root5, 10 ** 110))]
    body += ["", "def rootHi : ℚ :="] + ["  " + l for l in rat_lit(F(root5 + 1, 10 ** 110))]
    fb = d["freqBox"]
    body += ["", "/-- The frequency box. -/", "def freqBox : FreqBox := ["]
    for i, (c, r) in enumerate(fb):
        body += ["  ("] + ["    " + l for l in rat_lit(c)] + ["  ,"] + ["    " + l for l in rat_lit(r)]
        body += ["  )" + ("," if i + 1 < len(fb) else "]")]

    def wt(w):
        return ["⟨" + rat_lit(w[0])[0] + ","] + ["  " + l for l in rat_lit(w[1])] + ["⟩"]

    body += ["", "def weight : CertWeight :="] + ["  " + l for l in wt(d["weight"])]
    body += ["", "def weightH : CertWeight :="] + ["  " + l for l in wt(d["weightH"])]
    cf, cl = d["cfgFull"], d["cfgLow"]
    body += ["", "def cfgFull : ModelConfig SoBackendV2 :=",
             "  ⟨%d, %d, %d, CertFixed.toMant soPrecisionV2, advFull⟩" % (cf["cutoff"], cf["taylorN"],
                                                                         cf["halvings"]),
             "", "def cfgLow : ModelConfig SoBackendV2 :=",
             "  ⟨%d, %d, %d, CertFixed.toMant soPrecisionV2, advLow⟩" % (cl["cutoff"], cl["taylorN"], cl["halvings"])]
    body += ["", "/-- The torus certificate. -/", "def base : TorusCertificate 2 SoBackendV2 where",
             "  params := lunarR2 %s %s" % (en, dn), "  ham := soRotHamExprScaled lunarR2TimeScale",
             "  weightH := weightH",
             "  centre := [%s]" % ", ".join(rat_lit(x)[0] for x in d["centre"]),
             "  radius := [%s]" % ", ".join(rat_lit(x)[0] for x in d["radius"]),
             "  freqBox := freqBox", "  emb := emb", "  weight := weight", "  wit := wit",
             "  gramInv := gramInv", "  torsInv := torsInv", "  cfgFull := cfgFull", "  cfgLow := cfgLow",
             "  piEnc := piEnc", "  expHalvings := %d" % d["expHalvings"], "  expOrder := %d" % d["expOrder"]]
    g = d["graph"]
    body += ["", "/-- The graph certificate. -/", "def cert : SoGraphCert SoBackendV2 where", "  base := base"]
    for k in ("mono", "mono0", "pLo", "pLo0", "pHi", "pHi0"):
        body += ["  %s := %s" % (k.replace("0", "₀"), rat_lit(g[k])[0])]
    body += ["  sosMono := sosMonoPoly", "  sosLo := sosLoPoly", "  sosHi := sosHiPoly"]
    tree.write("Cert", [tree.module("Pieces"), "KAM.SpinOrbit.LunarConstsR2"],
               "The lunar %s torus: the certificate (generated)" % which,
               "Parameters `lunarR2` at the literal constants of `KAM.SpinOrbit.LunarConstsR2`, the frequency\n"
               "box, weights, model configurations and graph data.\n"
               "Generated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", body)


def q_lit(x):
    q = F(x)
    return ("%d / %d" % (q.numerator, q.denominator)) if q.denominator != 1 else str(q.numerator)


def emit_witness(tree, which, o):
    """`Witness.lean`: the routeARefined witness `refinedWit` (sodata3_witness.py)."""
    w = o["witness"]
    R = w["R"]
    bites = o["bites"]
    bw = lambda t: "some ⟨%s, %d, %d, %s⟩" % (q_lit(bites[t]["E1"]), bites[t]["l"], bites[t]["J"],
                                              q_lit(bites[t]["B"]))
    site = lambda t: bw(t) if t in bites else "none"
    body = ["/-- The refined claim: the Ham sums and frame majorants of this torus, rounded up (exact mirrors",
            "of `checkHamClaim` and `checkFrameMajorants`). -/", "def refClaim : RefClaim where"]
    body += ["  %s := %s" % (k, q_lit(R[k])) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT")]
    body += ["", "/-- The routeARefined witness (configuration d01b: certified bites at `δ₀, δ₁, b₀, b₁, b₂`). -/",
             "def refinedWit : RefinedWit where", "  core :="]
    core = [("Xs", w["Xs"]), ("kp", str(w["kp"])), ("th", q_lit(w["th"]))]
    core += [("c", "[" + ", ".join(q_lit(x) for x in w["c"]) + "]"),
             ("cbar", "[" + ", ".join(q_lit(x) for x in w["cbar"]) + "]")]
    core += [(k, q_lit(w[k])) for k in ("ctail", "sB", "sT", "sLt", "sN", "sNt", "t")] + [("J", str(w["J"]))]
    for i, (k, v) in enumerate(core):
        body += row_lines([("{ " if i == 0 else "  ") + "%s := %s" % (k, v) + (" }" if i + 1 == len(core) else "")],
                          "    ")
    body += ["  R := refClaim", "  κ := lunarR2Kappa", "  sites :="]
    sts = [(site("d%d" % s), site("b%d" % s)) for s in range(int(w["kp"]))]
    for i, (a, b) in enumerate(sts):
        body += row_lines([("[" if i == 0 else " ") + "(%s," % a, "%s)" % b + ("," if i + 1 < len(sts) else "]")],
                          "    ")
    tree.write("Witness", ["KAM.CertificateSharp.V2.RouteARefined", "KAM.SpinOrbit.LunarParamsR2"],
               "The lunar %s torus: the v2 refined-route witness (generated)" % which,
               "The witness `Sum.inr (Sum.inr refinedWit)` of `checkTorusCertificateV2 routeAV2`.\n"
               "Generated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", body,
               opens="KAM.Certificate KAM.CertificateSharp.V2 KAM.SpinOrbit")


def main(which, gdir, wpath, root):
    torus = which.capitalize()
    d = json.load(open(os.path.join(gdir, "%s_cert.json" % which)))
    a = json.load(open(os.path.join(gdir, "%s_advice.json" % which)))
    wit = json.load(open(wpath))
    o = [x for x in wit if x["which"] == which][0]
    assert F(o["err"]) == F(d["params"]["err"]) and F(o["disp"]) == F(d["params"]["disp"])
    tree = Tree(root, torus)
    imps = []
    e = d["emb"]
    polys = {}
    for k in ("angle", "action"):
        for i, x in enumerate(e[k]):
            nm = "%s%d" % (k, i)
            if x["half"]:
                imps.append(emit_poly(tree, nm, x["half"], "Embedding `%s` half terms" % nm))
                polys[nm] = (x["zero"], nm)
            else:
                polys[nm] = (x["zero"], None)
    cw = d["wit"]["charWit"]
    assert len(cw) == 1 and not d["wit"]["expWit"] and not d["wit"]["invWit"]
    ckey, E = cw[0]
    imps.append(emit_poly(tree, "charE", E["poly"], "Character witness `E`"))
    G = d["gramInv"]
    gnames = {}
    for i in range(2):
        for j in range(2):
            if j < i and G[i][j] == G[j][i]:
                gnames[(i, j)] = gnames[(j, i)]
                continue
            nm = "gram%d%d" % (i, j)
            imps.append(emit_poly(tree, nm, G[i][j], "Gram witness `B%d%d`" % (i, j)))
            gnames[(i, j)] = nm
    g = d["graph"]
    for nm in ("sosMono", "sosLo", "sosHi"):
        if g[nm]:
            imps.append(emit_poly(tree, nm, g[nm], "SOS witness `%s`" % nm))
    imps.append(emit_advice(tree, "advFull", a["cfgFull"]))
    imps.append(emit_advice(tree, "advLow", a["cfgLow"]))
    # the assembly of the pieces (no params, ham, box: those live in `KAM/SpinOrbit/Lunar*.lean`)
    body = []

    def rp(nm):
        z, h = polys[nm]
        return "⟨%sZero, %s⟩" % (nm, h if h else "[]")

    for nm in ("angle0", "angle1", "action0", "action1"):
        body.extend(row_lines(["def %sZero : SoBackendV2 :=" % nm, "⟨%s⟩" % num(polys[nm][0])], ""))
    body.append("")

    body += ["/-- The embedding. -/", "def emb : CertEmbedding SoBackendV2 where",
             "  angleDeg := [%s]" % ", ".join(str(x) for x in e["angleDeg"])]
    body += row_lines(["angle := [" + rp("angle0") + ",", rp("angle1") + "]"], "  ")
    body += ["  actionDeg := [%s]" % ", ".join(str(x) for x in e["actionDeg"])]
    body += row_lines(["action := [" + rp("action0") + ",", rp("action1") + "]"], "  ")
    body += ["", "/-- The witnesses: one character witness under the normalized key. -/",
             "def wit : Witnesses SoBackendV2 where", "  expWit := []", "  invWit := []",
             "  charWit := [([%s], ⟨⟨charE⟩, %d, %d⟩)]" % (", ".join(str(x) for x in ckey), E["pinHalvings"],
                                                         E["pinOrder"])]
    body += ["", "/-- The Gram witness. -/", "def gramInv : List (List (CertPoly SoBackendV2)) :=",
             "  [[⟨%s⟩, ⟨%s⟩], [⟨%s⟩, ⟨%s⟩]]" % (gnames[(0, 0)], gnames[(0, 1)], gnames[(1, 0)], gnames[(1, 1)])]
    body += ["", "/-- The torsion witness. -/", "def torsInv : List (List (CC SoBackendV2)) := ["]
    for i, r in enumerate(d["torsInv"]):
        for j, c in enumerate(r):
            end = "," if j + 1 < len(r) else ("]," if i + 1 < len(d["torsInv"]) else "]]")
            st = ("[" if j == 0 else " ") + cc(c) + end
            body += row_lines([st], "  ")
    pe = d["piEnc"]
    body += ["", "/-- The `π` enclosure. -/", "def piEnc : PiEnclosure SoBackendV2 where"]
    body += row_lines(["centre := ⟨%s⟩" % num(pe["centre"])], "  ")
    body += ["  rad := ⟨%s⟩" % num(pe["rad"]), "  machinK := %d" % pe["machinK"], "  machinJ := %d" % pe["machinJ"]]
    for nm in ("sosMono", "sosLo", "sosHi"):
        body += ["", "/-- The SOS witness `%s`. -/" % nm,
                 "def %sPoly : CertPoly SoBackendV2 := ⟨%s⟩" % (nm, nm if g[nm] else "[]")]
    tree.write("Pieces", imps + [FORMAT], "The lunar %s torus: data pieces (generated)" % which,
               "Embedding, witnesses, `π` enclosure and the two advice books.\n"
               "Generated by `scripts/spin_orbit/sofx_lean.py`. Do not edit.", body)
    emit_cert(tree, which, d, consts_lean(wit))
    emit_witness(tree, which, o)
    outdir = os.path.join(root, "KAM", "SpinOrbit", "Data", torus)
    os.makedirs(outdir, exist_ok=True)
    for rel, text in sorted(tree.files.items()):
        with open(tree.path(rel), "w") as f:
            f.write(text)
    print(len(tree.files), "files", sum(t.count("\n") for t in tree.files.values()), "lines",
          sum(len(t.encode()) for t in tree.files.values()), "bytes")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else os.path.join(HERE, "..", ".."))

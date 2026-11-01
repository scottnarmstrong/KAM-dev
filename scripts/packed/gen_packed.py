#!/usr/bin/env python3
"""V2-PACKED-GEN: the whole-torus packed generator (untrusted tooling; the kernel re-checks everything).

From an LG00-format certificate tree (`gen_cert.Cert`: LG00 T' = `applications/lg00/LG00/TP`, T'' = `TPP`), emits
the packed modules of the kernel proof into the scratch package of `gen_pkg.py` (library `LG00Packed`, modules
`LG00Packed.<TREE>.**`, namespace `LG00.<TREE>`, names prefixed `pk`), and writes the module list in emission
order (`modules_<TREE>.json`) for the run harness `run_packed.py`.

Stages (`--stages`, comma-separated; default `frames,gram,tors,sharp`):
  data    the shared data modules: the Gram book and memo (B2), the torsion boundary memo and the rounded node
          memo with its book and tables (B3b), the Gram radius; one definition per entry, split under the line cap;
  frames  the packed frame tests at the route witness's claims (`trFrameLOk`, `trFrameNOk`, `trFrameTOk`);
  gram    the packed Gram stage (B2): the 8 boundary entries, the core, the assembly `checkGramPacked`;
  tors    the rounded packed torsion stage (B3b) without its composition: the 36 boundary entries, the guards,
          the 7 stages (`DN`, `XN` entry by entry), the averages and the final test;
  sharp   the A gate: `refinedCoreS` (LG00's own `Final.RefinedCore`, reused) and the frame tests, with the
          one-ulp attacks (`Gate/*`: the largest packed sum is accepted, one ulp below it is rejected).
The assembly through the landed `cfgLow` composition (`torsRBase`) and the jet-fed route (`jetBase`) are emitted by
`--stages assembly` once their inputs exist (see the handoff: the Low chain of the tree, the branch APIs).

`--prefix LG00` (default) writes on LG00's real certificate (library `LG00Packed`, reusing LG00's built data);
`--prefix LG00P` on kamx-packed's certificate copy (`LG00P.<T>.Data.Cert`, modules `LG00P.<T>.PK.**`), the format
of the production route (V2-PACKED-PROD-API §3); the numbers are read from LG00's tree either way.
Usage: python3 -I scripts/packed/gen_packed.py [--tree TP] [--prefix LG00] [--cert DIR] [--pkg DIR] [--stages LIST]
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_cert as GC          # noqa: E402
import gen_pkg as GP           # noqa: E402
T, R, G, A, C, M, SP = GC.T, GC.R, GC.G, GC.A, GC.C, GC.M, GC.SP
P, Q, n = GC.P, GC.Q, GC.n
MAXLINES = 1400                # the 1,500-line cap, with room for the header
COPY = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

"""
OPEN = ("open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2\n"
        "  CertArith\n")


def wrapdoc(text, width=100):
    out = []
    for para in text.split("\n"):
        words, cur = para.split(), ""
        for w in words:
            if cur and len(cur) + 1 + len(w) > width:
                out.append(cur)
                cur = w
            else:
                cur = (cur + " " + w) if cur else w
        out.append(cur)
    return "\n".join(out)


def wrap_long(txt, width=100):
    """Break every over-long line at its last space before the limit; the continuation is indented 4 more than the
    line (Lean reads an indented continuation as the same term or tactic). Doc comments are left alone."""
    out = []
    for line in txt.split("\n"):
        while len(line) > width and not line.lstrip().startswith(("/-", "-/", "--")):
            k = line.rfind(" ", 0, width)
            ind = len(line) - len(line.lstrip())
            if k <= ind:
                break
            out.append(line[:k].rstrip())
            line = " " * (ind + 4) + line[k + 1:]
        out.append(line)
    return "\n".join(out)


class Emit:
    """Writes modules into the package and records them (with their imports) in emission order."""

    def __init__(self, pkg, tree, cert_root, prefix="LG00"):
        self.pkg, self.tree, self.cert_root, self.pre = pkg, tree, cert_root, prefix
        self.ns = "%s.%s" % (prefix, tree)
        # LG00's real certificate: library `LG00Packed`; a copy `<P>` (kamx-packed's format): `<P>.<T>.PK`
        self.root = "LG00Packed.%s" % tree if prefix == "LG00" else "%s.%s.PK" % (prefix, tree)
        self.fmt = "LG00Packed.Format" if prefix == "LG00" else "%s.PKFormat" % prefix
        self.mods = []

    def mod(self, rel):
        return "%s.%s" % (self.root, rel)

    def lg(self, rel):
        """A module of the certificate's own tree (`<P>.<T>.rel`)."""
        return "%s.%s.%s" % (self.pre, self.tree, rel)

    def sh(self, rel):
        """A shared module of the certificate's package (`<P>.rel`)."""
        return "%s.%s" % (self.pre, rel)

    def write(self, rel, imports, title, doc, body, ns=None, modname=None):
        name = modname or self.mod(rel)
        ns = ns or self.ns
        if "KAM.CertificateSharp.Packed.RouteSharp" not in imports:   # every namespace `OPEN` names exists
            imports = list(imports) + ["KAM.CertificateSharp.Packed.RouteSharp"]
        imps = "\n".join("public import %s" % m for m in imports)
        txt = COPY + imps + "\n\n/-!\n# LG00 %s packed: %s (generated)\n\n%s\n\nGenerated by " \
            "`scripts/packed/gen_packed.py` (V2-PACKED-GEN) from `LG00/%s`.\n-/\n\n" \
            "@[expose] public noncomputable section\n\nnamespace %s\n\n%s\n%s\nend %s\n" % (
                self.tree, title, wrapdoc(doc), self.tree, ns, OPEN, body.rstrip() + "\n", ns)
        txt = wrap_long(txt)
        lines = txt.split("\n")
        long_ = [l for l in lines if len(l) > 100]
        assert not long_, (name, long_[:2])
        assert len(lines) <= 1500, (name, len(lines))
        path = os.path.join(self.pkg, *name.split(".")) + ".lean"
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if not os.path.exists(path) or open(path, encoding="utf-8").read() != txt:
            with open(path, "w", encoding="utf-8") as f:
                f.write(txt)
        self.mods.append((name, list(imports)))
        return name

    def chunks(self, rel, imports, title, doc, defs):
        """Definitions `(name, text)` split into modules of at most MAXLINES lines; returns the module names."""
        out, cur, cl = [], [], 0
        for d in defs:
            k = d[1].count("\n") + 2
            if cur and cl + k > MAXLINES:
                out.append(cur)
                cur, cl = [], 0
            cur.append(d)
            cl += k
        if cur:
            out.append(cur)
        names = []
        for i, part in enumerate(out):
            names.append(self.write("%s%d" % (rel, i), imports, "%s, part %d of %d" % (title, i + 1, len(out)),
                                    doc, "\n".join(t for _, t in part)))
        return names

    def list_file(self):
        path = os.path.join(self.pkg, "modules_%s.json" % self.tree)
        json.dump(self.mods, open(path, "w"), indent=0)
        return path


# ---------------------------------------------------------------------------------------------- literal text
def zlist(ts):
    """`List (CertKey × ℤ)` in the zigzag format `tz k₀ k₁ v` (`LG00.Packed.Format`)."""
    return T.wrap("[" + ", ".join("tz %d %d %d" % (G.zz(k[0]), G.zz(k[1]), G.zz(v)) for k, v in ts) + "]")


def qlit(q):
    return T.qlit(F(q))


def qlines(q, ind):
    """A rational literal, its numerator and denominator on separate lines when long."""
    q = F(q)
    one = "(%d / %d : ℚ)" % (q.numerator, q.denominator)
    if ind + len(one) <= 98:
        return one
    num, den = str(q.numerator), str(q.denominator)
    assert ind + len(num) + 3 <= 100 and ind + 2 + len(den) + 5 <= 100, "rational too long for one line"
    return "(%s /\n%s%s : ℚ)" % (num, " " * (ind + 2), den)


def swrap(st, first=4, cont=6, width=100):
    """A statement over several lines (continuation lines indented by `cont`)."""
    out, cur, ind = [], "", first
    for w in st.split(" "):
        if cur and ind + len(cur) + 1 + len(w) > width:
            out.append(" " * ind + cur)
            cur, ind = w, cont
        else:
            cur = (cur + " " + w) if cur else w
    out.append(" " * ind + cur)
    return "\n".join(out)


def thm(name, st):
    return "theorem %s :\n%s\n  decide +kernel\n" % (name, swrap(st + " := by"))


def ldef(name, typ, val):
    return "def %s : %s :=\n%s\n" % (name, typ, val)


def gram_book(D):
    """`PGramBook` of the tree (the Lean formulas of `Gram.lean`, as `gram_gate_gen.py` with the tree's weight)."""
    w = D["w"]
    kk = [(0, 0)]
    for nm in D["comps"]:
        for k, _ in T.parse_cc_terms(D["texts"][nm]):
            kk += [k, (-k[0], -k[1])]
    loK, dK = G.box(kk)
    loB, dB = G.box([k for nm in D["grams"] for k, _ in T.parse_cc_terms(D["texts"][nm])] + [(0, 0)])
    d2 = (2 * dK[0] - 1, 2 * dK[1] - 1)
    lo2 = (2 * loK[0], 2 * loK[1])
    d3 = (dB[0] + d2[0] - 1, dB[1] + d2[1] - 1)
    lo3 = (loB[0] + lo2[0], loB[1] + lo2[1])
    s0 = d3[1]
    st = (s0, 1)
    N1, NB, N2 = G.dense_len(dK, st), G.dense_len(dB, st), G.dense_len(d2, st)
    BK, BB = 2 ** 136, 2 ** 132
    bG = 2 * n * G.mul_load(N1, N1, BK, BK)
    bE = n * G.mul_load(NB, N2, BB, bG)
    bD = 2 ** (3 * P) + bE
    lK, lB, lD = BK.bit_length(), BB.bit_length(), bD.bit_length()
    need = []
    for lo, dims, l in ((loK, dK, lK), (loB, dB, lB), (lo3, d3, lD)):
        r, c = G.maxes(w, Q, lo, dims, s0)
        need.append(max(l + 2, (dims[0] * s0 * 2 ** l * r * c).bit_length() + 1))
    width = max(need)
    return dict(L1=(loK, dK), LB=(loB, dB), s0=s0, width=width, lK=lK, lB=lB, lD=lD, BK=BK, BB=BB)


def lean_gbook(name, gb):
    lay = lambda L: "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L[0][0], L[0][1], L[1][0], L[1][1], gb["s0"],
                                                           gb["width"])
    return ("def %s : PGramBook where\n  P := %d\n  L1 := %s\n  LB := %s\n  bK := 2 ^ %d\n  bB := 2 ^ %d\n"
            "  q := %d\n  lK := %d\n  lB := %d\n  lD := %d\n" % (
                name, P, lay(gb["L1"]), lay(gb["LB"]), gb["BK"].bit_length() - 1, gb["BB"].bit_length() - 1, Q,
                gb["lK"], gb["lB"], gb["lD"]))


# ---------------------------------------------------------------------------------------------- the stages
SHAPE = dict(N=(2 * n, n), DL=(2 * n, n), DG=(n, n), C=(n, n), DGi=(n, n), DN=(2 * n, n), XN=(2 * n, n))
NODES = ("N", "DL", "DG", "C", "DGi", "DN", "XN")


def emit_format(E):
    body = ("/-- A term of a packed real array: zigzag-coded key and integer (`LG00.Format`). -/\n"
            "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n")
    return E.write("", [E.sh("Format"), "KAM.CertificateSharp.Packed.RouteSharp"], "the literal format",
                   "The packed memo terms `tz`; shared by every tree.", body, ns=E.pre, modname=E.fmt)


def emit_data(E, S, jet=False):
    """The shared data modules of the Gram and torsion stages. Returns the names of the umbrella modules.
    `jet`: the torsion reads `DX_H ∘ K` and `DH ∘ K` from the jet (`checkTorsionJ`), so the boundary memo keeps
    only the `D²K` entries (`ax`, `d1` empty: `ptPackOk` reads them through `getD`, the empty entry packs)."""
    D, rb, memos = S["D"], S["rb"], S["memos"]
    fmt = E.fmt
    out = {}
    # the Gram memo (B2) and book
    gb = gram_book(D)
    S["gbook"] = gb
    defs = []
    for (r, a), e in sorted(D["gm"].items()):
        defs.append(("re", ldef("pkGMre_%d_%d" % (r, a), "List (CertKey × ℤ)", zlist(e[0]))))
        defs.append(("im", ldef("pkGMim_%d_%d" % (r, a), "List (CertKey × ℤ)", zlist(e[1]))))
    parts = E.chunks("Data.GMemo", [fmt], "the Gram memo (the landed DK models' mantissas)",
                     "The memoized `DK` entries of the packed Gram stage (B2), checked entry by entry against the "
                     "landed `dkModel` by `pgEntryOk`.", defs)
    rows = lambda pf: "[" + ", ".join("[" + ", ".join("%s_%d_%d" % (pf, r, a) for a in range(n)) + "]"
                                      for r in range(2 * n)) + "]"
    rads = "[" + ", ".join("[" + ", ".join(qlit(D["gm"][(r, a)][2]) for a in range(n)) + "]"
                           for r in range(2 * n)) + "]"
    body = lean_gbook("pkGBook", gb) + "\n" + "def pkGMemo : PGramMemo where\n  re :=\n%s\n  im :=\n%s\n  rad :=\n%s\n" % (
        T.wrap(rows("pkGMre")), T.wrap(rows("pkGMim")), T.wrap(rads))
    db, eps = D["db"], D["eps"]
    body += "\n/-- The Gram core's `(δ, β)` (mirror). -/\ndef pkGDB : LGF × LGF := (⟨%d⟩, ⟨%d⟩)\n" % db
    body += "\n/-- `gramInvRadius pkGDB` (mirror). -/\ndef pkEps : LGF := ⟨%d⟩\n" % eps
    out["G"] = E.write("Data.Gram", parts, "the Gram book and memo",
                       "`pkGBook`, `pkGMemo` (B2) and the Gram core's value `pkGDB`, `pkEps` (re-checked).", body)
    # the torsion boundary memo (B3b)
    defs = []
    names = {}
    for kind in ("d2", "ax", "d1"):
        names[kind] = []
        for i, e in enumerate(D[kind] if kind == "d2" or not jet else []):
            nm = "pkT%s_%d" % (kind, i)
            names[kind].append(nm)
            defs.append((nm, ldef(nm + "_re", "List (CertKey × ℤ)", zlist(e[0])) + "\n" +
                         ldef(nm + "_im", "List (CertKey × ℤ)", zlist(e[1])) + "\n" +
                         "def %s : MemoEntry :=\n  (%s_re, %s_im,\n    %s)\n" % (nm, nm, nm, qlit(e[2]))))
    parts = E.chunks("Data.TMemo", [fmt], "the torsion boundary memo",
                     "The memoized boundary entries of the rounded packed torsion stage (B3b): `D²K`, `DX_H ∘ K`, "
                     "`DH ∘ K`, checked entry by entry against the landed models (`ptD2Ok`, `ptAOk`, `ptD1Ok`).",
                     defs)
    body = "def pkTMemo : PTorsMemo where\n" + "".join(
        "  %s :=\n%s\n" % (k, T.wrap("[" + ", ".join(names[k]) + "]")) for k in ("d2", "ax", "d1"))
    out["T"] = E.write("Data.Tors", parts, "the torsion boundary memo", "`pkTMemo` (B3b).", body)
    # the rounded node memo, its book and tables (B3b)
    defs = []
    for nm in NODES:
        memo, mats = memos[nm]
        Rr, Cc = SHAPE[nm]
        for i in range(Rr):
            for j in range(Cc):
                re_, im_ = R.node_lists(memo[(i, j)])
                e = "pkR%s_%d_%d" % (nm, i, j)
                defs.append((e, ldef(e + "_re", "List (CertKey × ℤ)", zlist(re_)) + "\n" +
                             ldef(e + "_im", "List (CertKey × ℤ)", zlist(im_)) + "\n" +
                             "def %s : NodeEntry :=\n  (%s_re, %s_im,\n    %s,\n    %s)\n" % (
                                 e, e, e, qlit(F(mats[(i, j)][1], 2 ** P)), qlit(F(mats[(i, j)][2], 2 ** P)))))
    parts = E.chunks("Data.RMemo", [fmt], "the rounded node memo",
                     "The memoized nodes `N`, `D L`, `DG`, `C`, `D(G⁻¹)`, `DN`, `X_N` of the rounded packed torsion "
                     "chain (B3b), each checked by its exact residual on the window (`stageOk`).", defs)
    tab = lambda nm: T.wrap("[" + ", ".join("[" + ", ".join("pkR%s_%d_%d" % (nm, i, j) for j in range(SHAPE[nm][1]))
                                            + "]" for i in range(SHAPE[nm][0])) + "]")
    CT, RT, CY, RY = S["CT"], S["RT"], S["CY"], S["RY"]
    body = R.lean_rbook("pkRBook", rb).replace("noncomputable def", "def") + "\n"
    for i in range(n):
        for j in range(n):
            body += "def pkCT_%d_%d : ℚ × ℚ :=\n  (%s,\n    %s)\n\n" % (i, j, qlines(CT[i][j][0], 4),
                                                              qlines(CT[i][j][1], 4))
            body += "def pkRT_%d_%d : ℚ :=\n  %s\n\n" % (i, j, qlines(RT[i][j], 2))
    for j in range(n):
        body += "def pkCY_%d : ℚ × ℚ :=\n  (%s,\n    %s)\n\n" % (j, qlines(CY[j][0], 4), qlines(CY[j][1], 4))
        body += "def pkRY_%d : ℚ :=\n  %s\n\n" % (j, qlines(RY[j], 2))
    body += "def pkRMemo : PRMemo where\n" + "".join("  %s :=\n%s\n" % (nm, tab(nm)) for nm in NODES)
    body += "  CT := %s\n" % ("[" + ", ".join("[" + ", ".join("pkCT_%d_%d" % (i, j) for j in range(n)) + "]"
                                             for i in range(n)) + "]")
    body += "  RT := %s\n" % ("[" + ", ".join("[" + ", ".join("pkRT_%d_%d" % (i, j) for j in range(n)) + "]"
                                             for i in range(n)) + "]")
    body += "  CY := %s\n" % ("[" + ", ".join("pkCY_%d" % j for j in range(n)) + "]")
    body += "  RY := %s\n" % ("[" + ", ".join("pkRY_%d" % j for j in range(n)) + "]")
    out["R"] = E.write("Data.Nodes", parts, "the rounded node memo, its book and tables",
                       "`pkRBook` and `pkRMemo` (B3b): the box of half-width 25, its window, the loads, the nodes, "
                       "the averages of `T` and `Y`.", body)
    return out


def emit_frames(E, S, data, fr):
    """The packed frame tests at the claims of the route witness, and the one-ulp attacks (gate)."""
    imp = [data["G"], data["R"], E.lg("Final.Wit")]
    W = "lg00Cert.weight"
    stL = "trFrameLOk (α := LGF) 2 %s pkRBook pkGMemo %s = %s"
    stN = "trFrameNOk (α := LGF) 2 pkRBook pkRMemo %s %s = %s"
    stT = "trFrameTOk (α := LGF) 2 %s pkRBook pkRMemo %s = %s"
    cl = "lg00RW.base.R."
    mods = {}
    mods["L"] = E.write("FrameL", imp, "`|Lᵀ| ≤ bL`", "The packed `|Lᵀ|` test at the route witness's claim `bL` "
                        "(`trFrameLOk`: column sums of the packed `DK` entries).",
                        thm("pkFrameL", stL % (W, cl + "bL", "true")))
    mods["N"] = E.write("FrameN", imp, "`|N| ≤ bN`, `|Nᵀ| ≤ bNt`", "The packed `|N|`, `|Nᵀ|` tests at the claims "
                        "(`trFrameNOk`: row and column sums of the node memo of `N`).",
                        thm("pkFrameN", stN % (cl + "bN", cl + "bNt", "true")))
    mods["T"] = E.write("FrameT", imp, "`sup |T| ≤ bT`", "The packed `sup |T|` test at the claim `bT` (`trFrameTOk`: "
                        "the guard `aT ≤ aW` and the row sums of the packed weighted norms of `T` on the window).",
                        thm("pkFrameT", stT % (W, cl + "bT", "true")))
    ed = fr["edges"]
    ulp = F(1, 2 ** P)
    gate = {}
    for key, st, args in (("L", stL, lambda q: (W, qlit(q))), ("N", stN, lambda q: (qlit(q), cl + "bNt")),
                          ("Nt", stN, lambda q: (cl + "bN", qlit(q))), ("T", stT, lambda q: (W, qlit(q)))):
        e = ed[key]
        gate[key + "_hi"] = E.write("Gate.Frame%sHi" % key, imp, "control: the largest packed sum is accepted",
                                    "Sharp control of the A gate: the packed test with the bound at its largest sum "
                                    "(mirror, exact) decides `true`.",
                                    thm("pkFrame%sHi" % key, st % (args(e) + ("true",))))
        gate[key + "_lo"] = E.write("Gate.Frame%sLo" % key, imp, "attack: one ulp below is rejected",
                                    "Negative control (one-ulp attack) of the A gate: the bound one ulp (2⁻¹²⁸) below "
                                    "the largest packed sum decides `false`.",
                                    thm("pkFrame%sLo" % key, st % (args(e - ulp) + ("false",))))
    return mods, gate


def emit_sharp(E, frames_mods):
    """The A gate's assembly: the frame tests and `refinedCoreS` on the tree's data, as one theorem."""
    imp = list(frames_mods.values()) + [E.lg("Final.RefinedCore")]
    body = ("/-- **The A gate** (V2-PACKED-SHARP): the final packed frame sums at the route witness's claims\n"
            "and `refinedCoreS` (the certified sharp sites), decided on the tree's data. It establishes neither\n"
            "`refinedTestPackedS … lg00Cert lg00RW = true` nor the frame bounds (`FrameMajorants`): the sums run\n"
            "on memos (`pkRBook`, `pkGMemo`, `pkRMemo`) verified only by the stage conjuncts the packed frames\n"
            "share with `checkTorsionR` (`gramPackedCheck`, `ptPackOk`, `trStN`, …), which are left, with\n"
            "`checkHamClaim` and `checkFrameOmega`, to the B3b route (`refinedTestPackedS_of`,\n"
            "`checkFrameMajorantsR_of`). -/\n"
            "theorem pkGateA :\n"
            "    trFrameLOk (α := LGF) 2 lg00Cert.weight pkRBook pkGMemo lg00RW.base.R.bL = true ∧\n"
            "    trFrameNOk (α := LGF) 2 pkRBook pkRMemo lg00RW.base.R.bN lg00RW.base.R.bNt = true ∧\n"
            "    trFrameTOk (α := LGF) 2 lg00Cert.weight pkRBook pkRMemo lg00RW.base.R.bT = true ∧\n"
            "    refinedCoreS 2 lg00Cert.params lg00Cert.freqBox lg00RW = true :=\n"
            "  ⟨pkFrameL, pkFrameN, pkFrameT, lg00_refinedCore⟩\n")
    return E.write("GateA", imp, "the A gate", "The packed frame tests and the certified sharp sites on the tree's "
                   "data (V2-PACKED-SHARP).", body)


def emit_gram(E, data):
    """The packed Gram stage (B2): entries, core, assembly."""
    imp = [data["G"], E.lg("Data.Cert")]
    args = "2 lg00Cert.emb lg00Cert.weight lg00Cert.cfgLow lg00Cert.piEnc pkGBook pkGMemo"
    ents = []
    for r in range(2 * n):
        for a in range(n):
            ents.append(E.write("Gram.E%d_%d" % (r, a), imp, "Gram entry (%d, %d)" % (r, a),
                                "One boundary entry of the packed Gram stage: the landed `dkModel` against the memo.",
                                thm("pkGramE_%d_%d" % (r, a), "pgEntryOk %s %d %d = true" % (args, r, a))))
    sig = "(lg00Cert.params.σB - lg00Cert.params.μ)"
    core = E.write("Gram.Core", imp + ["KAM.CertificateSharp.Kernel.SegDefs"], "the Gram core", "The core of the packed Gram check (`gramPackedCore`): it "
                   "returns the mirror's `(δ, β)`.",
                   thm("pkGramCore", "gramPackedCore 2 lg00Cert.gramInv lg00Cert.weight lg00Cert.cfgLow pkGBook "
                       "pkGMemo %s = some pkGDB" % sig) + "\n" +
                   thm("pkEps_eq", "gramInvRadius pkGDB = some pkEps"))
    hs = "\n".join("  · exact pkGramE_%d_%d" % (r, a) for r in range(2 * n) for a in range(n))
    body = ("theorem pkGramEntries :\n%s\n"
            "  refine pgEntries_of (h := fun r hr a ha => ?_)\n"
            "  have hr' : r < 4 := hr\n  have ha' : a < 2 := ha\n"
            "  interval_cases r <;> interval_cases a\n%s\n\n"
            "/-- The packed Gram check of the certificate returns the core's `(δ, β)`. -/\n"
            "theorem pkGram :\n    gramPackedCheck 2 lg00Cert.emb lg00Cert.gramInv lg00Cert.weight lg00Cert.cfgLow "
            "lg00Cert.piEnc\n      pkGBook pkGMemo %s = some pkGDB := by\n"
            "  rw [gramPackedCheck_eq_core (h := pkGramEntries)]\n  exact pkGramCore\n\n"
            "/-- **The packed Gram sub-check passes** (B2). -/\n"
            "theorem pkCheckGram : checkGramPacked pkGBook pkGMemo lg00Cert = true := by\n"
            "  simp only [checkGramPacked, pkGram, Option.isSome_some]\n") % (
        swrap("pgEntries %s = true := by" % args), hs, sig)
    return E.write("Gram", ents + [core, "Mathlib.Tactic.IntervalCases"], "the packed Gram stage (B2)",
                   "`checkGramPacked pkGBook pkGMemo lg00Cert = true` from its entries and its core.", body)


def cached(f, pkg, tag, cert):
    """A computation cached in the package by a tag (pickled)."""
    import pickle
    path = os.path.join(pkg, "cache_%s.pkl" % tag)
    if os.path.exists(path):
        S = pickle.load(open(path, "rb"))
        S["D"]["cert"] = cert
        return S
    S = f()
    pickle.dump(S, open(path, "wb"))
    return S


def cached_compute(cert, pkg, tree):
    """`gen_cert.compute`, cached in the package (keyed by the certificate tree's input files)."""
    import hashlib
    import pickle
    h = hashlib.sha256()
    for rel in ("Data/Cert.lean", "Data/DCoeffs.lean", "Data/E0.lean", "Data/W8.lean", "Torsion/D0.lean",
                "Final/Wit.lean"):
        h.update(open(os.path.join(cert.root, rel), "rb").read())
    for nm in sorted(os.listdir(cert.tors)):
        if nm.startswith("V"):
            h.update(open(os.path.join(cert.tors, nm), "rb").read())
    path = os.path.join(pkg, "cache_%s_%s.pkl" % (tree, h.hexdigest()[:16]))
    if os.path.exists(path):
        S = pickle.load(open(path, "rb"))
        S["D"]["cert"] = cert
        return S
    S = GC.compute(cert)
    pickle.dump(S, open(path, "wb"))
    return S


def emit_tms(E, D):
    """The 20 jet slot models read by the torsion (the landed `cfgLow` composition), copied from the tree's
    `Torsion/{D0, V*}.lean` and renamed `pkTMs*` (re-proved equal to the composition by `--stages assembly`)."""
    import re
    cert = D["cert"]
    d0 = os.path.join(cert.tors, "D0.lean")
    nodoc = lambda t: re.sub(r"\n/--(?:(?!-/).)*-/\s*$", "\n", t, flags=re.S)   # a next definition's docstring
    defs = []
    for i in range(20):
        mdef = G.grab(d0, "lg00TMs_%d" % i)
        lst = re.search(r"⟨(lg00TMs_\d+t_\d+)⟩", GC.flat(mdef)).group(1)
        ttext = T.grab_any(cert.tors, r"V\d+\.lean", lst)
        defs.append((lst, re.sub(r"\blg00TMs", "pkTMs", nodoc(ttext).replace("noncomputable def", "def"))))
        defs.append(("m%d" % i, re.sub(r"\blg00TMs", "pkTMs", nodoc(mdef).replace("noncomputable def", "def"))))
    top = re.sub(r"\blg00TMs", "pkTMs", G.grab(d0, "lg00TMs").replace("noncomputable def", "def"))
    parts = E.chunks("Data.TMs", [E.fmt], "the jet slot models of the torsion",
                     "The models of the `2n` first and `(2n)²` second derivatives of `H` along `K` at `cfgLow`, as "
                     "the tree's landed composition returns them (`Torsion/D0.lean`).", defs)
    return E.write("Data.TMsAll", parts, "the jet slot models of the torsion", "`pkTMs`.", top)


def emit_tors(E, data, tms):
    """The rounded packed torsion stage (B3b) without its composition: entries, guards, stages, tables."""
    imp = [data["G"], data["T"], data["R"], E.lg("Data.Cert")]
    c = "lg00Cert"
    W, Bi, cfg, box, sv = c + ".weight", c + ".gramInv", c + ".cfgLow", c + ".freqBox", c + ".params.s"
    mods = {}
    ents = []
    for r in range(2 * n):
        for j in range(n):
            for l in range(n):
                ents.append(E.write("Tors.ED2_%d_%d_%d" % (r, j, l), imp, "torsion entry D²K (%d, %d, %d)" % (r, j, l),
                                    "One boundary entry: the landed `d2kModel` against the memo.",
                                    thm("pkTorsD2_%d_%d_%d" % (r, j, l),
                                        "ptD2Ok 2 %s.emb %s %s %s.piEnc pkRBook.toT pkTMemo %d %d %d = true"
                                        % (c, W, cfg, c, r, j, l))))
    for a in range(2 * n):
        for b in range(2 * n):
            ents.append(E.write("Tors.EA_%d_%d" % (a, b), imp + [tms], "torsion entry DX_H ∘ K (%d, %d)" % (a, b),
                                "One boundary entry: the landed `DX_H ∘ K` entry at degree 0 against the memo.",
                                thm("pkTorsA_%d_%d" % (a, b), "ptAOk 2 %s %s %s.piEnc pkRBook.toT pkTMemo pkTMs %d %d "
                                    "= true" % (W, cfg, c, a, b))))
        ents.append(E.write("Tors.ED1_%d" % a, imp + [tms], "torsion entry DH ∘ K (%d)" % a,
                            "One boundary entry: the landed `DH ∘ K` entry at degree 0 against the memo.",
                            thm("pkTorsD1_%d" % a, "ptD1Ok 2 %s %s %s.piEnc pkRBook.toT pkTMemo pkTMs %d = true"
                                % (W, cfg, c, a))))
    import itertools
    body = ("theorem pkTorsEntries :\n%s\n"
            "  refine ptEntries_of (fun r hr j hj l hl => ?_) (fun a ha b hb => ?_) (fun a ha => ?_)\n"
            "  · have hr' : r < 4 := hr\n    have hj' : j < 2 := hj\n    have hl' : l < 2 := hl\n"
            "    interval_cases r <;> interval_cases j <;> interval_cases l\n%s\n"
            "  · have ha' : a < 4 := ha\n    have hb' : b < 4 := hb\n"
            "    interval_cases a <;> interval_cases b\n%s\n"
            "  · have ha' : a < 4 := ha\n    interval_cases a\n%s\n") % (
        swrap("ptEntries 2 %s.emb %s %s %s.piEnc pkRBook.toT pkTMemo pkTMs = true := by" % (c, W, cfg, c)),
        "\n".join("    · exact pkTorsD2_%d_%d_%d" % ix for ix in itertools.product(range(4), range(2), range(2))),
        "\n".join("    · exact pkTorsA_%d_%d" % ix for ix in itertools.product(range(4), range(4))),
        "\n".join("    · exact pkTorsD1_%d" % a for a in range(4)))
    mods["E"] = E.write("Tors.Entries", ents + ["KAM.CertificateSharp.Packed.TorsRAsm", "Mathlib.Tactic.IntervalCases"],
                        "the torsion boundary entries", "`ptEntries` of the certificate from its 36 entries.", body)
    st = {}
    st["Lay"] = E.write("Tors.Lay", imp, "the layouts and loads", "`trLayOk`, `trNormOk`.",
                        thm("pkTrLay", "trLayOk 2 pkRBook = true") + "\n" +
                        thm("pkTrNorm", "trNormOk 2 %s %s %s pkRBook = true" % (W, box, sv)))
    st["Pack"] = E.write("Tors.Pack", imp, "the packing of the boundary", "`ptPackOk`.",
                         thm("pkTrPack", "ptPackOk 2 %s %s pkRBook.toT pkGMemo pkTMemo = true" % (Bi, cfg)))
    stmts = dict(N="trStN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                 DL="trStDL (α := LGF) 2 %s %s %s pkRBook pkTMemo pkRMemo" % (W, box, sv),
                 DG="trStDG (α := LGF) 2 %s pkRBook pkGMemo pkRMemo" % W,
                 C="trStC 2 %s %s %s pkRBook pkRMemo pkEps" % (Bi, W, cfg),
                 DGi="trStDGi 2 %s %s %s pkRBook pkRMemo pkEps" % (Bi, W, cfg))
    for nm, stt in stmts.items():
        st[nm] = E.write("Tors.St%s" % nm, imp, "the node %s" % nm, "The node `%s` against the exact product of "
                         "its memoized inputs on the window (`stageAll`)." % nm, thm("pkTrSt%s" % nm, stt + " = true"))
    mats = dict(DN="trMDN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                XN="trMXN (α := LGF) 2 %s pkRBook pkTMemo pkRMemo" % W)
    full = dict(DN="trStDN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                XN="trStXN (α := LGF) 2 %s pkRBook pkTMemo pkRMemo" % W)
    for nm in ("DN", "XN"):
        es = []
        for i in range(2 * n):
            for j in range(n):
                es.append(E.write("Tors.St%s_%d_%d" % (nm, i, j), imp, "the node %s, entry (%d, %d)" % (nm, i, j),
                                  "One entry of the node `%s` against the exact product of its inputs (`stageOk`)."
                                  % nm, thm("pkTrSt%s_%d_%d" % (nm, i, j),
                                            "stageOk 2 %s pkRBook.q pkRBook.lW pkRBook.lR pkRBook.Lw pkRBook.Lb "
                                            "pkRBook.Lu pkRBook.bR (2 * pkRBook.P) pkRBook.P ((%s).x %d %d) "
                                            "((%s).r %d %d) (nodeAt pkRMemo.%s %d %d) = true"
                                            % (W, mats[nm], i, j, mats[nm], i, j, nm, i, j))))
        body = ("theorem pkTrSt%s :\n%s\n  refine stageAll_of fun i hi j hj => ?_\n"
                "  have hi' : i < 4 := hi\n  have hj' : j < 2 := hj\n"
                "  interval_cases i <;> interval_cases j\n%s\n") % (
            nm, swrap(full[nm] + " = true := by"),
            "\n".join("  · exact pkTrSt%s_%d_%d" % (nm, i, j) for i in range(4) for j in range(2)))
        st[nm] = E.write("Tors.St%s" % nm, es + ["KAM.CertificateSharp.Packed.TorsRAsm",
                                                 "Mathlib.Tactic.IntervalCases"],
                         "the node %s" % nm, "`%s` from its eight entries." % full[nm].split()[0], body)
    st["T"] = E.write("Tors.T", imp, "the averages of T", "`trTCheck`.",
                      thm("pkTrT", "trTCheck (α := LGF) 2 pkRBook pkRMemo = true"))
    st["Y"] = E.write("Tors.Y", imp, "the averages of Y", "`trYCheck`.",
                      thm("pkTrY", "trYCheck (α := LGF) 2 %s pkRBook pkTMemo pkRMemo = true" % W))
    sig = "(%s.params.σT - %s.params.μ)" % (c, c)
    st["F"] = E.write("Tors.Final", imp, "the averaged test", "The landed averaged test on the tables (`tabFinal`).",
                      thm("pkTrFinal", "tabFinal 2 %s pkRBook.P (trCentre 2 %s %s pkRMemo) (trRad 2 %s %s pkRMemo) "
                          "%s.torsInv %s = true" % (cfg, box, sv, box, sv, c, sig)))
    body = ("/-- **The core of the rounded packed torsion check** (B3b) of the certificate. -/\n"
            "theorem pkTorsCore :\n%s\n"
            "  torsRCore_of pkTrLay pkTrNorm pkTrPack pkTrStN pkTrStDL pkTrStDG pkTrStC pkTrStDGi pkTrStDN\n"
            "    pkTrStXN pkTrT pkTrY pkTrFinal\n") % swrap(
        "torsRCore 2 %s %s %s %s %s pkRBook pkGMemo pkTMemo pkRMemo pkEps %s.torsInv %s = true"
        % (Bi, W, cfg, box, sv, c, sig) + " :=")
    mods["C"] = E.write("Tors.Core", list(st.values()) + ["KAM.CertificateSharp.Packed.TorsRAsm"],
                        "the torsion core", "`torsRCore` of the certificate from its thirteen parts.", body)
    return mods


def emit_assembly(E, data, gram, tors, frames, tms, sharp_engine="routeARefinedPackedS"):
    """End to end through B3b's `torsRBase` and the packed sharp-site engine, with the tree's landed `cfgLow`
    composition (its `Low` chain) for the torsion boundary and the frames, and the tree's landed `Final` facts for
    the other sub-checks; then the tree's main statement (`Main.lean`'s `lg00_kamTorus`, verbatim), re-proved."""
    import re
    t = E.tree
    bk = "pkGBook pkGMemo pkRBook pkTMemo pkRMemo"
    comp = E.write("Asm.Compose", [tms, E.lg("Low.T1931"), E.lg("Low.Ckpt"), E.sh("JetBridge"),
                                   E.sh("Kernel.StageTwo")],
                   "the landed cfgLow composition", "The tree's landed `cfgLow` composition (`lg00ComposeLow`, the "
                   "`Low` chain) returns the torsion's jet slot models `pkTMs`.",
                   "theorem pkTMs_eq :\n    (torsionSlots 2 lg00Jet).map (fun i => (lg00CkptLow.slotPair "
                   "lg00Cert.weight i).1) =\n      pkTMs :=\n  eq_of_modelsBeq (by decide +kernel)\n\n"
                   "theorem pkComposeLow :\n    Slp.compose 2 lg00Cert.ham.jet.prog lg00Cert.emb lg00Cert.wit "
                   "lg00Cert.weight lg00Cert.cfgLow\n      lg00Cert.piEnc (torsionSlots 2 lg00Cert.ham.jet) = "
                   "some pkTMs := by\n"
                   "  rw [show lg00Cert.ham.jet = lg00Jet from lg00Ham_jet, lg00ComposeLow, pkTMs_eq]\n")
    ctors = E.write("Asm.Tors", [gram, tors["E"], tors["C"], comp], "the packed torsion sub-check",
                    "`checkTorsionR` of the certificate (B3b).",
                    "/-- **The rounded packed torsion sub-check passes** (B3b). -/\n"
                    "theorem pkCheckTorsion : checkTorsionR %s lg00Cert = true :=\n"
                    "  checkTorsionR_of pkGram pkEps_eq pkComposeLow rfl pkTorsEntries pkTorsCore\n" % bk)
    om = "checkFrameOmega lg00Cert (lg00RW.base.R.frame lg00Cert.freqBox).bOm = true"
    fr = E.write("Asm.Frames", list(frames.values()) + [ctors], "the packed frame majorants",
                 "`checkFrameMajorantsR` at the route witness's claims, from the facts shared with the torsion "
                 "stage and the three frame tests.",
                 thm("pkFrameOm", om) + "\n"
                 "theorem pkFrames :\n    checkFrameMajorantsR %s lg00Cert\n"
                 "      (lg00RW.base.R.frame lg00Cert.freqBox) = true :=\n"
                 "  checkFrameMajorantsR_of pkGram pkEps_eq pkComposeLow rfl pkTorsEntries pkTrLay pkTrNorm pkTrPack\n"
                 "    pkTrStN pkTrStDL pkTrStDG pkTrStC pkTrStDGi pkTrStDN pkTrStXN pkFrameL pkFrameN pkFrameT\n"
                 "    pkFrameOm\n" % bk)
    eng = E.write("Asm.Engine", [fr, E.lg("Final.HamClaim"), E.lg("Final.RefinedCore")],
                  "the packed sharp-site engine", "The test of `routeARefinedPackedS` on the certificate and its "
                  "route witness: the landed disc pass, the packed frames, the certified sharp sites.",
                  "theorem pkEngine :\n    refinedTestPackedS %s lg00Cert lg00RW = true :=\n"
                  "  refinedTestPackedS_of %s\n    lg00_hamClaim pkFrames lg00_refinedCore\n" % (bk, bk))
    base = E.write("Asm.Base", [gram, ctors, E.lg("Final.Static"), E.lg("Final.Embedding"),
                                E.lg("Final.Invariance"), E.lg("Balls.HamBounds")],
                   "the packed base checker", "`torsRBase`: the landed static, Hamiltonian, embedding, invariance and "
                   "energy sub-checks (the tree's `Final` facts) with the packed Gram and torsion sub-checks.",
                   "theorem pkBase : (torsRBase %s).check lg00Cert = true := by\n"
                   "  show (checkStatic lg00Cert && checkHamBounds lg00Cert && checkEmbedding lg00Cert &&\n"
                   "    checkInvariance lg00Cert && checkEnergy lg00Cert && checkGramPacked pkGBook pkGMemo lg00Cert &&\n"
                   "    checkTorsionR %s lg00Cert) = true\n"
                   "  rw [lg00_checkStatic, lg00_hamBounds, lg00_checkEmbedding, lg00_checkInvariance, "
                   "lg00_checkEnergy,\n    pkCheckGram, pkCheckTorsion]\n  rfl\n" % (bk, bk))
    chk = E.write("Asm.Check", [eng, base], "the v2 certifier on the packed route",
                  "The certifier with B3b's base checker and the packed sharp-site engine passes on the certificate.",
                  "/-- **The v2 certifier passes on `lg00Cert` through the packed route** (`torsRBase`,\n"
                  "`routeARefinedPackedS`, witness `lg00RW`). -/\n"
                  "theorem pk_check :\n    checkV2With (torsRBase %s)\n"
                  "      (routeARefinedPackedS %s) lg00Cert lg00RW = true :=\n"
                  "  checkV2With_packedS_of %s pkBase pkEngine\n" % (bk, bk, bk))
    main_src = open(os.path.join(E.cert_root, "Main.lean"), encoding="utf-8").read()
    ren = lambda x: re.sub(r"\bLG00\b", E.pre, x)
    st = ren(re.search(r"theorem lg00_kamTorus :\n(.*?) := by\n", main_src, re.S).group(1))
    opens = ren(re.search(r"^open .*$", main_src, re.M).group(0))
    body = ("%s KAM.CertificateSharp.Packed\n\n"
            "/-- **The tree's torus theorem through the packed route** (`lg00_kamTorus`'s statement, verbatim;\n"
            "proved from `pk_check` and `checkV2With_packedS_sound`). -/\n"
            "theorem pk_kamTorus :\n%s := by\n"
            "  refine ⟨lg00Ham_identity, by decide +kernel, ?_⟩\n"
            "  obtain ⟨Kinf, sinf, h⟩ := (lg00_certifiedTorus_iff lg00Cert lg00OmegaStar).mp\n"
            "    (checkV2With_packedS_sound %s pk_check lg00_freqEncloses\n      lg00_diophantine)\n"
            "  exact ⟨Kinf, sinf, h, lg00_window h.2.2.2.2.2.2.2.2.2.2⟩\n") % (opens, st, bk)
    body += stmt_form(main_src, ren)
    return E.write("Main", [chk, E.lg("Final.Freq"), E.sh("Physical.HamIdentity")],
                   "the torus theorem through the packed route",
                   "`pk_kamTorus`: the statement of the tree's `Main.lean`, from the packed route.", body)


def stmt_form(main_src, ren):
    """`pk_kamTorusStatement`: the confinement form of the tree's `Main.lean` (`lg00_kamTorusStatement`)."""
    import re
    m = re.search(r"theorem lg00_kamTorusStatement : (.*?) :=\n  ⟨lg00_kamTorus\.1, lg00_kamTorus\.2\.2⟩", main_src,
                  re.S)
    assert m, "the tree's Main.lean has no lg00_kamTorusStatement of the expected form"
    return ("\n/-- `pk_kamTorus` in the form of LG00-CONF's assembly (`lg00_kamTorusStatement`'s statement). -/\n"
            "theorem pk_kamTorusStatement : %s :=\n  ⟨pk_kamTorus.1, pk_kamTorus.2.2⟩\n" % ren(m.group(1)))


def i_book(D, wfull, bfull, hb=48):
    """`PIBook` of the invariance and energy on the jet (kamx-pk-cons, `JetConsInv.lean`): the Full chain's box and
    width, its largest wanted load `bJ`, the Gram memo's bound, the frequency mantissas' bound (Lean formulas)."""
    s0 = 4 * hb + 1
    Lb = ((-hb, -hb), (2 * hb + 1, 2 * hb + 1))
    bK = 2 ** 136
    bF = D["bk"]["b"]["bF"]
    aI = 2 * 1 * bfull * 2 ** P + n * 2 * 1 * bK * bF          # mulLoad Lb LU0 (min dense = 1)
    lK, lI = bK.bit_length(), aI.bit_length()
    for l, B_ in ((lK, bK), (lI, aI)):
        r, c = G.maxes(D["w"], Q, Lb[0], Lb[1], s0)
        assert B_ < 2 ** l and l + 2 <= wfull and Lb[1][0] * s0 * 2 ** l * r * c < 2 ** wfull, "normOk fails"
    lay = lambda L: "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L[0][0], L[0][1], L[1][0], L[1][1], s0, wfull)
    txt = ("def pkIBook : PIBook where\n  P := %d\n  Lb := %s\n  LU0 := %s\n  bJ := %d\n  bK := 2 ^ %d\n"
           "  bF := %s\n  q := %d\n  lK := %d\n  lI := %d\n" % (
               P, lay(Lb), lay(((0, 0), (1, 1))), bfull, bK.bit_length() - 1, T.pow2(bF), Q, lK, lI))
    return txt


def emit_front(E, jet):
    """The chains with their wanted nodes in front of the ledger (`JetFront.lean`): `jdLowW`, `jdFullW`, and the
    check that every front entry is the ledger's own (one lookup per entry, five entries per module)."""
    v0, d1, d2 = GC.ham_jet(E.cert)
    sets = dict(Low=d1 + [x for row in d2 for x in row], Full=[v0] + d1)
    lit = lambda C, js: T.wrap("[" + ", ".join("(slotK %d, n%s_s%d)" % (j, C, j) for j in js) + "]")
    body = ("def frontLow : JLedger :=\n%s\n\ndef frontFull : JLedger :=\n%s\n\n"
            "/-- The `cfgLow` chain with its wanted nodes in front of the ledger. -/\n"
            "def jdLowW : JetData := jdLow.withFront frontLow\n\n"
            "/-- The `cfgFull` chain with its wanted nodes in front of the ledger. -/\n"
            "def jdFullW : JetData := jdFull.withFront frontFull\n") % (lit("Low", sets["Low"]), lit("Full", sets["Full"]))
    dmod = E.write("Data.Front", [jet["low_data"], jet["full_data"], "KAM.CertificateSharp.Packed.JetFront",
                                  "KAM.CertificateSharp.Packed.RouteSharpJ"],
                   "the chains with their wanted nodes in front",
                   "`frontLow`, `frontFull` (kamx-packed's own wanted nodes, by name) and `jdLowW`, `jdFullW`.", body)
    out = dict(data=dmod)
    for C in ("Low", "Full"):
        js, parts = sets[C], []
        for t in range(0, len(js), 5):
            parts.append(E.write("Front.%s%d" % (C, t // 5), [dmod], "front entries of the %s chain" % C,
                                 "Each front entry is the ledger's own (one ledger lookup each).",
                                 "\n".join(thm("pkFront%s_%d" % (C, j), "lookOk jd%s (slotK %d) n%s_s%d = true"
                                                % (C, j, C, j)) for j in js[t:t + 5])))
        body = ("theorem pkFront%sOk : frontOk jd%s front%s = true := by\n"
                "  simp only [frontOk, front%s, List.all_cons, List.all_nil, %s, Bool.and_self]\n") % (
            C, C, C, C, ", ".join("pkFront%s_%d" % (C, j) for j in js))
        out[C.lower()] = E.write("Front.%s" % C, parts, "the front of the %s chain" % C,
                                 "`frontOk` from its entries.", swrapl(body))
    return out


def swrapl(txt, width=100):
    """Wrap the over-long lines of a proof body at commas (continuation indented by 4 more)."""
    out = []
    for line in txt.split("\n"):
        while len(line) > width:
            k = line.rfind(", ", 0, width - 1)
            ind = len(line) - len(line.lstrip()) + 4
            out.append(line[:k + 1])
            line = " " * ind + line[k + 2:]
        out.append(line)
    return "\n".join(out)


def emit_j(E, SJ, jet):
    """The jet route (V2-PACKED-PROD-API, kamx-pk-cons' consumers): the torsion, invariance, energy and frames on
    the jet's chains, `jetBase`, the packed sharp-site engine on the jet's torsion (`RouteSharpJ`), the certifier,
    the tree's statement. `jet`: the chain modules and names of kamx-packed's `jet_prod_gen.py` (`<P>.<T>.Jet.<C>`)."""
    import itertools
    import re
    data = emit_data(E, SJ, jet=True)
    gram = emit_gram(E, data)
    front = emit_front(E, jet)
    c = "lg00Cert"
    W, Bi, cfg, box, sv = c + ".weight", c + ".gramInv", c + ".cfgLow", c + ".freqBox", c + ".params.s"
    # the jet literal `lg00Jet`, never `lg00Cert.ham.jet`: reading the certificate's jet makes the kernel compile the
    # Hamiltonian's jet (`lg00Ham_jet`'s cost, ≈ 7.5 GB); the assemblies rewrite with the proved `lg00Ham_jet`
    J, jsL, jsF = "lg00Jet", "(jetSlots (α := LGF) jdLowW)", "(jetSlots (α := LGF) jdFullW)"
    RWJ = "rw [pkHamJet]"
    hamjet = E.write("HamJet", [E.lg("Data.Cert"), E.sh("JetBridge"), E.sh("Jet")], "the certificate's jet",
                     "`pkHamJet`: the certificate's jet is the literal `lg00Jet` (the jet bridge `lg00Ham_jet`).",
                     "theorem pkHamJet : lg00Cert.ham.jet = lg00Jet := lg00Ham_jet\n")
    low, full = jet["low"], jet["full"]                  # the chain theorems (`…ChainCert`)
    lowd, fulld = jet["low_data"], jet["full_data"]      # the chain data (`jdLowW`, `jdFullW`) only
    imp = [data["G"], data["T"], data["R"], E.lg("Data.Cert"), "KAM.CertificateSharp.Packed.RouteSharpJ", front["data"],
           E.sh("Jet")]
    # the torsion on the jet
    d2 = []
    for r, j, l in itertools.product(range(2 * n), range(n), range(n)):
        d2.append(E.write("TorsJ.ED2_%d_%d_%d" % (r, j, l), imp, "torsion entry D²K (%d, %d, %d)" % (r, j, l),
                          "One boundary entry: the landed `d2kModel` against the memo.",
                          thm("pkTorsD2_%d_%d_%d" % (r, j, l), "ptD2Ok 2 %s.emb %s %s %s.piEnc pkRBook.toT pkTMemo "
                              "%d %d %d = true" % (c, W, cfg, c, r, j, l))))
    body = ("theorem pkD2All :\n%s\n  refine ptD2All_of fun r hr j hj l hl => ?_\n"
            "  have hr' : r < 4 := hr\n  have hj' : j < 2 := hj\n  have hl' : l < 2 := hl\n"
            "  interval_cases r <;> interval_cases j <;> interval_cases l\n%s\n") % (
        swrap("ptD2All 2 %s.emb %s %s %s.piEnc pkRBook.toT pkTMemo = true := by" % (c, W, cfg, c)),
        "\n".join("  · exact pkTorsD2_%d_%d_%d" % ix for ix in itertools.product(range(4), range(2), range(2))))
    d2all = E.write("TorsJ.D2All", d2 + ["Mathlib.Tactic.IntervalCases"], "the D²K entries",
                    "`ptD2All` from its 16 entries.", body)
    lowok = E.write("TorsJ.LowOk", imp + [low, front["low"]], "the jet's Low chain at the torsion",
                    "`jetLowOk`: the jet's box and scale are the torsion's (`layoutEq`, checked), and the chain "
                    "theorem of kamx-packed (`jetLow_check_cert`) at the load `pkRBook.bA = bLow`.",
                    "theorem pkLowOk : jetLowOk pkRBook jdLowW lg00Cert = true := by\n"
                    "  simp only [jetLowOk, Bool.and_eq_true]\n"
                    "  exact ⟨⟨by decide +kernel, by decide +kernel⟩,\n"
                    "    (jetCheck_withFront pkFrontLowOk _ _).trans jetLow_check_cert⟩\n")
    st = {}
    st["Lay"] = E.write("TorsJ.Lay", imp, "the layouts and loads", "`trLayOk`, `trNormOk`.",
                        thm("pkTrLay", "trLayOk 2 pkRBook = true") + "\n" +
                        thm("pkTrNorm", "trNormOk 2 %s %s %s pkRBook = true" % (W, box, sv)))
    st["Pack"] = E.write("TorsJ.Pack", imp, "the packing of the boundary", "`ptPackOk`.",
                         thm("pkTrPack", "ptPackOk 2 %s %s pkRBook.toT pkGMemo pkTMemo = true" % (Bi, cfg)))
    stmts = dict(N="trStN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                 DL="trStDL (α := LGF) 2 %s %s %s pkRBook pkTMemo pkRMemo" % (W, box, sv),
                 DG="trStDG (α := LGF) 2 %s pkRBook pkGMemo pkRMemo" % W,
                 C="trStC 2 %s %s %s pkRBook pkRMemo pkEps" % (Bi, W, cfg),
                 DGi="trStDGi 2 %s %s %s pkRBook pkRMemo pkEps" % (Bi, W, cfg))
    for nm, stt in stmts.items():
        st[nm] = E.write("TorsJ.St%s" % nm, imp, "the node %s" % nm, "The node `%s` against the exact product of "
                         "its memoized inputs on the window (`stageAll`)." % nm, thm("pkTrSt%s" % nm, stt + " = true"))
    mats = dict(DN="trMDN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                XN="trMXNJ 2 %s %s pkRBook pkRMemo" % (J, jsL))
    full_ = dict(DN="trStDN 2 %s %s %s pkRBook pkGMemo pkRMemo pkEps" % (Bi, W, cfg),
                 XN="trStXNJ 2 %s %s %s pkRBook pkRMemo" % (J, jsL, W))
    for nm in ("DN", "XN"):
        es = []
        for i, j in itertools.product(range(2 * n), range(n)):
            es.append(E.write("TorsJ.St%s_%d_%d" % (nm, i, j), imp + ([lowd] if nm == "XN" else []),
                              "the node %s, entry (%d, %d)" % (nm, i, j),
                              "One entry of the node `%s` against the exact product of its inputs (`stageOk`)." % nm,
                              thm("pkTrSt%s_%d_%d" % (nm, i, j),
                                  "stageOk 2 %s pkRBook.q pkRBook.lW pkRBook.lR pkRBook.Lw pkRBook.Lb pkRBook.Lu "
                                  "pkRBook.bR (2 * pkRBook.P) pkRBook.P ((%s).x %d %d) ((%s).r %d %d) "
                                  "(nodeAt pkRMemo.%s %d %d) = true" % (W, mats[nm], i, j, mats[nm], i, j, nm, i, j))))
        body = ("theorem pkTrSt%s :\n%s\n  refine stageAll_of fun i hi j hj => ?_\n"
                "  have hi' : i < 4 := hi\n  have hj' : j < 2 := hj\n"
                "  interval_cases i <;> interval_cases j\n%s\n") % (
            nm, swrap(full_[nm] + " = true := by"),
            "\n".join("  · exact pkTrSt%s_%d_%d" % (nm, i, j) for i in range(4) for j in range(2)))
        st[nm] = E.write("TorsJ.St%s" % nm, es + ["KAM.CertificateSharp.Packed.TorsRAsm",
                                                  "Mathlib.Tactic.IntervalCases"],
                         "the node %s" % nm, "`%s` from its eight entries." % full_[nm].split()[0], body)
    st["T"] = E.write("TorsJ.T", imp, "the averages of T", "`trTCheck`.",
                      thm("pkTrT", "trTCheck (α := LGF) 2 pkRBook pkRMemo = true"))
    st["Y"] = E.write("TorsJ.Y", imp + [lowd], "the averages of Y", "`trYCheckJ` (`DH` from the jet).",
                      thm("pkTrY", "trYCheckJ 2 %s %s pkRBook pkRMemo = true" % (J, jsL)))
    sig = "(%s.params.σT - %s.params.μ)" % (c, c)
    st["F"] = E.write("TorsJ.Final", imp, "the averaged test", "The landed averaged test on the tables (`tabFinal`).",
                      thm("pkTrFinal", "tabFinal 2 %s pkRBook.P (trCentre 2 %s %s pkRMemo) (trRad 2 %s %s pkRMemo) "
                          "%s.torsInv %s = true" % (cfg, box, sv, box, sv, c, sig)))
    core = E.write("TorsJ.Core", list(st.values()) + [lowd], "the torsion core on the jet",
                   "`torsRCoreJ` of the certificate from its thirteen parts.",
                   "theorem pkTorsCoreJ :\n%s\n  torsRCoreJ_of pkTrLay pkTrNorm pkTrPack pkTrStN pkTrStDL pkTrStDG "
                   "pkTrStC pkTrStDGi\n    pkTrStDN pkTrStXN pkTrT pkTrY pkTrFinal\n" % swrap(
                       "torsRCoreJ 2 %s %s %s %s %s %s %s pkRBook pkGMemo pkTMemo pkRMemo pkEps %s.torsInv %s = true :="
                       % (Bi, W, cfg, box, sv, J, jsL, c, sig)))
    tors = E.write("TorsJ", [gram, d2all, lowok, core, hamjet], "the packed torsion on the jet",
                   "`checkTorsionJ` of the certificate.",
                   "theorem pkCheckTorsionJ :\n    checkTorsionJ pkGBook pkGMemo pkRBook pkTMemo pkRMemo jdLowW lg00Cert "
                   "= true :=\n  checkTorsionJ_of pkGram pkEps_eq rfl pkLowOk pkD2All (by %s; exact pkTorsCoreJ)\n" % RWJ)
    # the frames on the jet's torsion
    fimp = [data["G"], data["R"], E.lg("Final.Wit"), "KAM.CertificateSharp.Packed.RouteSharpJ", front["data"]]
    cl = "lg00RW.base.R."
    fL = E.write("FramesJ.L", fimp, "`|Lᵀ| ≤ bL`", "`trFrameLOk` at the claim.",
                 thm("pkFrameL", "trFrameLOk (α := LGF) 2 %s pkRBook pkGMemo %sbL = true" % (W, cl)))
    fN = E.write("FramesJ.N", fimp, "`|N| ≤ bN`, `|Nᵀ| ≤ bNt`", "`trFrameNOk` at the claims.",
                 thm("pkFrameN", "trFrameNOk (α := LGF) 2 pkRBook pkRMemo %sbN %sbNt = true" % (cl, cl)))
    fT = E.write("FramesJ.T", fimp, "`sup |T| ≤ bT`", "`trFrameTOk` at the claim (`T` from the jet's `X_N`).",
                 thm("pkFrameT", "trFrameTOk (α := LGF) 2 %s pkRBook pkRMemo %sbT = true" % (W, cl)))
    om = "checkFrameOmega lg00Cert (lg00RW.base.R.frame lg00Cert.freqBox).bOm = true"
    frames = E.write("FramesJ", [fL, fN, fT, tors, E.lg("Final.Wit")], "the packed frames on the jet's torsion",
                     "`checkFrameMajorantsRJ` at the route witness's claims.",
                     thm("pkFrameOm", om) + "\n"
                     "theorem pkFramesJ :\n    checkFrameMajorantsRJ pkGBook pkGMemo pkRBook pkTMemo pkRMemo jdLowW "
                     "lg00Cert\n      (lg00RW.base.R.frame lg00Cert.freqBox) = true :=\n"
                     "  checkFrameMajorantsRJ_of pkGram pkEps_eq rfl pkLowOk pkD2All pkTrLay pkTrNorm pkTrPack pkTrStN\n"
                     "    pkTrStDL pkTrStDG pkTrStC pkTrStDGi pkTrStDN (by %s; exact pkTrStXN) pkFrameL pkFrameN\n"
                     "    pkFrameT pkFrameOm\n" % RWJ)
    # the invariance and the energy on the Full chain
    ib = E.write("Data.IBook", [E.fmt, "KAM.CertificateSharp.Packed.RouteSharpJ"], "the invariance book",
                 "`pkIBook`: the Full chain's box and width, its largest wanted load, the loads and norm offsets.",
                 i_book(SJ["D"], jet["wfull"], jet["bfull"]))
    iimp = [ib, data["G"], E.lg("Data.Cert"), fulld, front["data"], E.sh("Jet")]
    guard = E.write("InvJ.Guard", iimp, "the invariance guard", "`ivGuard`.",
                    thm("pkIvGuard", "ivGuard 2 %s %s %s pkIBook pkGMemo = true" % (W, box, sv)))
    rows = [E.write("InvJ.Row%d" % a, iimp, "invariance row %d" % a, "`ivRowOk`: the packed weighted norm of the "
                    "invariance array plus its radius is at most `err`.",
                    thm("pkIvRow%d" % a, "ivRowOk 2 %s %s %s %s %s pkIBook pkGMemo %s.params.err %d = true"
                        % (W, box, sv, J, jsF, c, a))) for a in range(2 * n)]
    fullok = E.write("InvJ.FullOk", iimp + [full, front["full"]], "the jet's Full chain at the invariance",
                     "`jetFullOk`: the box and scale (checked), and the chain theorem `jetFull_check_cert`.",
                     "theorem pkFullOk : jetFullOk pkIBook jdFullW lg00Cert = true := by\n"
                     "  simp only [jetFullOk, Bool.and_eq_true]\n"
                     "  exact ⟨⟨by decide +kernel, by decide +kernel⟩,\n"
                     "    (jetCheck_withFront pkFrontFullOk _ _).trans jetFull_check_cert⟩\n")
    inv = E.write("InvJ", [gram, guard, fullok, hamjet] + rows + ["Mathlib.Tactic.IntervalCases"],
                  "the packed invariance on the jet", "`checkInvarianceJ` of the certificate.",
                  "theorem pkCheckInvJ : checkInvarianceJ pkGBook pkGMemo pkIBook jdFullW lg00Cert = true := by\n"
                  "  refine checkInvarianceJ_of pkGram rfl pkFullOk pkIvGuard fun a ha => ?_\n"
                  "  %s\n  have ha' : a < 4 := ha\n  interval_cases a\n%s\n" % (RWJ, "\n".join(
                      "  · exact pkIvRow%d" % a for a in range(4))))
    enp = E.write("EnJ.Parts", iimp, "the energy's guard and value", "`enGuard`, `enOk` (the zero mode of the "
                  "`v0` node, minus `E0`, plus its radius, at most `err`).",
                  thm("pkEnGuard", "enGuard 2 pkIBook = true") + "\n" +
                  thm("pkEnOk", "enOk 2 %s %s pkIBook %s.params.E0 %s.params.err = true" % (J, jsF, c, c)))
    en = E.write("EnJ", [enp, fullok, hamjet], "the packed energy on the jet", "`checkEnergyJ` from its parts.",
                 "theorem pkCheckEnJ : checkEnergyJ pkIBook jdFullW lg00Cert = true :=\n"
                 "  checkEnergyJ_of pkFullOk pkEnGuard (by %s; exact pkEnOk)\n" % RWJ)
    bk = "pkGBook pkGMemo pkRBook pkTMemo pkRMemo"
    base = E.write("Asm.BaseJ", [tors, inv, en, E.lg("Final.Static"), E.lg("Final.Embedding"),
                                 E.lg("Balls.HamBounds")], "the jet base checker",
                   "`jetBase`: the landed static, Hamiltonian and embedding checks (the tree's facts, on the copy) "
                   "with the packed Gram, torsion, invariance and energy on the jet.",
                   "theorem pkBaseJ :\n    (jetBase %s jdLowW pkIBook jdFullW).check lg00Cert = true :=\n"
                   "  jetBase_check_of lg00_checkStatic lg00_hamBounds lg00_checkEmbedding pkGram pkCheckTorsionJ\n"
                   "    pkCheckInvJ pkCheckEnJ\n" % bk)
    eng = E.write("Asm.EngineJ", [frames, E.lg("Final.HamClaim"), E.lg("Final.RefinedCore")],
                  "the packed sharp-site engine on the jet", "The test of `routeARefinedPackedSJ`.",
                  "theorem pkEngineJ :\n    refinedTestSWith (framesRJ %s jdLowW) lg00Cert lg00RW =\n      true :=\n"
                  "  refinedTestPackedSJ_of %s jdLowW\n    lg00_hamClaim pkFramesJ lg00_refinedCore\n" % (bk, bk))
    chk = E.write("Asm.CheckJ", [eng, base], "the v2 certifier on the jet route",
                  "The certifier with `jetBase` and the packed sharp-site engine on the jet passes.",
                  "/-- **The v2 certifier passes on `lg00Cert` through the jet route.** -/\n"
                  "theorem pk_checkJ :\n    checkV2With (jetBase %s jdLowW pkIBook jdFullW)\n"
                  "      (routeARefinedPackedSJ %s jdLowW) lg00Cert lg00RW =\n      true :=\n"
                  "  checkV2With_jetSharp_of %s jdLowW pkBaseJ pkEngineJ\n" % (bk, bk, bk))
    main_src = open(os.path.join(E.cert_root, "Main.lean"), encoding="utf-8").read()
    ren = lambda x: re.sub(r"\bLG00\b", E.pre, x)
    stt = ren(re.search(r"theorem lg00_kamTorus :\n(.*?) := by\n", main_src, re.S).group(1))
    opens = ren(re.search(r"^open .*$", main_src, re.M).group(0))
    body = ("%s KAM.CertificateSharp.Packed\n\n"
            "/-- **The tree's torus theorem through the jet route** (`lg00_kamTorus`'s statement, on the\n"
            "packed route's certificate; proved from `pk_checkJ`). -/\n"
            "theorem pk_kamTorus :\n%s := by\n"
            "  refine ⟨lg00Ham_identity, by decide +kernel, ?_⟩\n"
            "  obtain ⟨Kinf, sinf, h⟩ := (lg00_certifiedTorus_iff lg00Cert lg00OmegaStar).mp\n"
            "    (checkV2With_jetSharp_sound %s jdLowW pk_checkJ\n      lg00_freqEncloses lg00_diophantine)\n"
            "  exact ⟨Kinf, sinf, h, lg00_window h.2.2.2.2.2.2.2.2.2.2⟩\n") % (opens, stt, bk)
    body += stmt_form(main_src, ren)
    return E.write("MainJ", [chk, E.lg("Final.Freq"), E.sh("Physical.HamIdentity")],
                   "the torus theorem through the jet route",
                   "`pk_kamTorus`: the statement of the tree's `Main.lean`, from the jet route.", body)


def main():
    args = sys.argv[1:]

    def opt(k, d):
        if k in args:
            i = args.index(k)
            v = args[i + 1]
            del args[i:i + 2]
            return v
        return d
    tree = opt("--tree", "TP")
    prefix = opt("--prefix", "LG00")
    cert_root = opt("--cert", os.path.join(GP.LG00, "LG00", tree))
    pkg = opt("--pkg", GP.PKG)
    stages = opt("--stages", "frames,sharp").split(",")
    lowc, fullc = opt("--jet-low", None), opt("--jet-full", None)
    cert = GC.Cert(cert_root)
    assert cert.ns == "LG00.%s" % tree, cert.ns
    E = Emit(pkg, tree, cert_root, prefix)
    E.cert = cert
    emit_format(E)
    info = dict(tree=tree, prefix=prefix, cert=cert_root, stages=stages)
    if "jet" in stages:
        # the jet route (exclusive: its data modules carry the jet-fed torsion memos)
        assert lowc and fullc, "--jet-low and --jet-full: kamx-packed's mirror caches of the two chains"
        SJ = cached(lambda: GC.compute_j(cert, lowc), pkg, "J_%s_%d" % (tree, os.path.getsize(lowc)), cert)
        fr = GC.frames(SJ)
        assert all(fr["ok"].values()), fr["ok"]
        v0, d1, _ = GC.ham_jet(cert)
        fn, wf = GC.jet_nodes(fullc, [v0] + d1, 48)
        jet = dict(low=E.lg("Jet.Low.ChainCert"), full=E.lg("Jet.Full.ChainCert"), low_data=E.lg("Jet.Low.Data"),
                   full_data=E.lg("Jet.Full.Data"), wfull=wf,
                   bfull=max(v[3] for v in fn.values()))
        ie = GC.inv_energy(SJ, fullc)
        assert all(r["ok"] for r in ie["rows"]) and ie["energy"]["ok"], ie
        emit_j(E, SJ, jet)
        S = SJ
        info.update(invariance_energy=ie)
        info.update(jet=dict(width_low=SJ["jet"]["width"], width_torsion=SJ["rb"]["width"],
                             bA_bits=SJ["jet"]["bA"].bit_length(), width_full=wf,
                             bfull_bits=jet["bfull"].bit_length()))
        assert SJ["rb"]["width"] == SJ["jet"]["width"], "regenerate the Low chain at --width=%d" % SJ["rb"]["width"]
    else:
        S = cached_compute(cert, pkg, tree)
        fr = GC.frames(S)
        assert all(fr["ok"].values()), fr["ok"]
        data = emit_data(E, S)
        fm = None
        if "frames" in stages or "sharp" in stages or "assembly" in stages:
            fm, gate = emit_frames(E, S, data, fr)
            if "sharp" in stages:
                emit_sharp(E, fm)
        gram = tors = tms = None
        if "gram" in stages or "assembly" in stages:
            gram = emit_gram(E, data)
        if "tors" in stages or "assembly" in stages:
            tms = emit_tms(E, S["D"])
            tors = emit_tors(E, data, tms)
        if "assembly" in stages:
            assert prefix == "LG00", "the torsRBase assembly reads the tree's landed Low chain (LG00's data only)"
            emit_assembly(E, data, gram, tors, fm, tms)
        info.update(gram_book={k: (v if not isinstance(v, int) or v < 2 ** 63 else v.bit_length())
                               for k, v in S["gbook"].items()})
    lst = E.list_file()
    info.update(modules=len(E.mods), claims={k: str(v) for k, v in fr["claims"].items()},
                edges={k: str(v) for k, v in fr["edges"].items()},
                edges_float={k: float(v) for k, v in fr["edges"].items()}, torsion_final=S["info"],
                torsion_width=S["rb"]["width"])
    json.dump(info, open(os.path.join(pkg, "packed_%s_%s.json" % (prefix, tree)), "w"), indent=1, default=str)
    print(json.dumps(info, indent=1, default=str))
    print("module list:", lst)

if __name__ == "__main__":
    main()

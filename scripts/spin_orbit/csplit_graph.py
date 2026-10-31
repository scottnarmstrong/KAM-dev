#!/usr/bin/env python3
"""SO-DATA3: the graph check's SOS sides by row chunks (untrusted tooling; the kernel checks everything).

    python3 -B csplit_graph.py lower|upper GENDIR [ROOT]

`checkRealLowerBound` squares the SOS witness `g` by the direct product (`directItems`, one evaluation of all
`|g|²` term pairs; over the 10 GB cap at 271-325 terms). The data store `g` in chunks of 32 = 2^5 rows
(`sosLo.cK`), and the landed `directItems` merges its rows positionally as a balanced tree, so its first five
levels are the chunk-wise ones (`levelNCseg_flatten`, `KAM/SpinOrbit/Data/CsegGraph.lean`). Emitted per side
(Lo: `pLo`, Hi: `pHi`) under KAM/SpinOrbit/Data/<Torus>/Pass/:

  Graph{S}Lit{k}    the chunk results `L_k` (mirror, self-checked against the mirror's whole `directItems`)  data
  Graph{S}C{k}      `levelNCseg 5 (chunk k rows) = [L_k]`                                                 heavy
  Graph{S}          the side's `checkRealLowerBound … = true` from the memoized square                    heavy
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
D3 = "/mnt/HC_Volume_106379410/kam-data/so-data3"
for k, v in dict(OMP_NUM_THREADS="1", SO_N="65", SO_DATA_DIR=D3 + "/L20", SO_PREC="96", SO_PKG=D3 + "/pkgR2.json",
                 SO_SHARP="1", SO_BUDGET_FULL="20", SO_CUT_LOW="160").items():
    os.environ.setdefault(k, v)
import sofx_model as M  # noqa: E402
import sofx_check as C  # noqa: E402
import sofx_arith as A  # noqa: E402
import sofx_lean as SL  # noqa: E402
import csplit_emit as E  # noqa: E402

ROWS = 32
LEVELS = 5


def level(B, rows):
    out = []
    for i in range(0, len(rows), 2):
        out.append(M.mergeErrTerms(B, rows[i], rows[i + 1]) if i + 1 < len(rows) else rows[i])
    return out


def tree(B, rows, fuel=64):
    for _ in range(fuel):
        if len(rows) <= 1:
            break
        rows = level(B, rows)
    return rows[0] if rows else []


def et(t):
    (k0, k1), (re, im), e = t
    return "etF 96 %s %s %s %s %s" % (SL.num(k0), SL.num(k1), SL.num(re), SL.num(im), SL.num(e))


def lit_defs(name, terms):
    chunks = [terms[i:i + ROWS] for i in range(0, len(terms), ROWS)] or [[]]
    out = []
    for k, ch in enumerate(chunks):
        out.append("def %s.c%d : List (ErrTerm SoBackendV2) := [" % (name, k))
        for i, t in enumerate(ch):
            out.append("  " + et(t) + ("," if i + 1 < len(ch) else "]"))
        if not ch:
            out[-1] += "]"
        out.append("")
    nm = ["%s.c%d" % (name, k) for k in range(len(chunks))]
    out += E.wrap(["def %s : List (ErrTerm SoBackendV2) := List.flatten [" % name] +
                  [x + "," for x in nm[:-1]] + [nm[-1] + "]"], "") + [""]
    return out


def main(which, gdir, root):
    T, t = which.capitalize(), which
    d = json.load(open(os.path.join(gdir, "%s_cert.json" % which)))
    B = A.FixedB(96)
    tree_ = E.Tree(root, T)
    pdir = os.path.join(root, "KAM", "SpinOrbit", "Data", T, "Pass")
    base = ["KAM.SpinOrbit.Data.%s.Cert" % T, "KAM.SpinOrbit.Data.CsegGraph", "KAM.SpinOrbit.Graph.Cert"]
    files = {}
    heavy = []
    for S, key, fexpr, m0, m in (("Lo", "sosLo", "(soGraphActionModel cert)", "cert.pLo₀", "cert.pLo"),
                                 ("Hi", "sosHi", "(soGraphActionModel cert).negM", "(-cert.pHi₀)", "(-cert.pHi)")):
        g = [((int(k[0]), int(k[1])), (int(c[0]), int(c[1]))) for k, c in d["graph"][key]]
        conj = C.conjSorted(B, g)
        chunks = [g[i:i + ROWS] for i in range(0, len(g), ROWS)]
        Ls = []
        for ch in chunks:
            rows = [M.rowItems(B, s, conj) for s in ch]
            for _ in range(LEVELS):
                rows = level(B, rows)
            assert len(rows) == 1
            Ls.append(rows[0])
        whole = M.directItems(B, g, conj)
        assert tree(B, list(Ls), 64 - LEVELS) == whole, "chunked tree differs from the mirror's directItems"
        # data
        for k, L in enumerate(Ls):
            files["Graph%sLit%d" % (S, k)] = (base, "SOS side %s: chunk result %d" % (S, k),
                                              "The chunk result `L_k` of `g g*`.", lit_defs("%sG%sL%d" % (t, S, k), L),
                                              False)
        # chunk theorems
        conjT = "%sPoly.conjSorted.terms" % key
        for k in range(len(chunks)):
            st = ("levelNCseg 5 (%s.c%d.map fun s => rowItems s %s) = [%sG%sL%d] :="
                  % (key, k, conjT, t, S, k))
            files["Graph%sC%d" % (S, k)] = (base + ["KAM.SpinOrbit.Data.%s.Pass.Graph%sLit%d" % (T, S, k)],
                                           "SOS side %s: chunk %d" % (S, k), "Five merge levels of one 32-row chunk.",
                                           ["theorem %s_g%sc%d :" % (t, S, k)] + E.wrap(st.split(" "), "    ") +
                                           ["  eq_singleton_of_beq_cseg (by decide +kernel)"], True)
        n = len(chunks)
        Lz = "[" + ", ".join("%sG%sL%d" % (t, S, k) for k in range(n)) + "]"
        cfg7 = "{ base.cfgLow with advice := base.cfgLow.advice ++ [([7], ProductAdvice.direct)] }"
        cl = "[" + ", ".join("%s.c%d" % (key, k) for k in range(n)) + "]"
        body = ["theorem %s_g%sDirect :" % (t, S),
                "    directItems %sPoly.terms %s = mergeRowsTree 59 %s := by" % (key, conjT, Lz),
                "  unfold directItems",
                "  rw [show (64 : ℕ) = 59 + 5 from rfl, mergeRowsTree_add_cseg,",
                "    show %sPoly.terms = List.flatten %s from rfl," % (key, cl),
                "    levelNCseg_flatten 5 _ %s (by decide +kernel)]" % cl,
                "  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]"]
        body += ["  rw [" + " ".join(["%s_g%sc%d," % (t, S, k) for k in range(n - 1)] + ["%s_g%sc%d]" % (t, S, n - 1)])]
        body += ["  rfl", "",
                 "theorem %s_g%sSq :" % (t, S),
                 "    CertModel.polyProduct base.weight %s [7] %sPoly %sPoly.conjSorted =" % (cfg7, key, key),
                 "      some (mergeRowsTree 59 %s, ofInt 0) := by" % Lz,
                 "  unfold CertModel.polyProduct",
                 "  rw [if_neg (by decide +kernel), if_neg (by decide +kernel),",
                 "    adviceLookup_append_cseg _ _ _ (by decide +kernel), %s_g%sDirect]" % (t, S), "",
                 "theorem %s_graph%s :" % (t, "L" if S == "Lo" else "H"),
                 "    checkRealLowerBound cert.base.weight cert.base.cfgLow %s %s %s" % (fexpr, m0, m),
                 "      cert.%s = true := by" % key,
                 "  unfold checkRealLowerBound",
                 "  rw [realLowerModel_eq_of_sq_cseg cert.base.weight cert.base.cfgLow %s %s cert.%s" % (fexpr, m0, key),
                 "    (mul_eq_of_polyProduct_cseg base.weight %s [7] _ _ %s_g%sSq)]" % (cfg7, t, S),
                 "  decide +kernel"]
        files["Graph%s" % ("L" if S == "Lo" else "H")] = (
            base + ["KAM.SpinOrbit.Data.%s.Pass.Graph%sC%d" % (T, S, k) for k in range(n)],
            "the graph check: p%s by row chunks" % S, "The SOS side from its chunk theorems (CsegGraph).", body, True)
    for rel, (imps, title, doc, body, hv) in files.items():
        text = E.HEADER.replace("csplit_emit.py", "csplit_graph.py").format(imports="\n".join("public import " + i for i in sorted(set(imps))),
                               title="The lunar %s torus: %s" % (which, title), doc=doc,
                               ns="KAM.SpinOrbit.Data.%s" % T, body="\n".join(E.autowrap(body)).rstrip())
        for i, l in enumerate(text.splitlines()):
            assert len(l) <= 100, (rel, i, l)
        assert text.count("\n") <= 1500, (rel, text.count("\n"))
        open(os.path.join(pdir, rel + ".lean"), "w").write(text)
        if hv:
            heavy.append("KAM.SpinOrbit.Data.%s.Pass.%s" % (T, rel))
    print(which, len(files), "modules", sum(len(f[3]) for f in files.values()), "lines")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "..", ".."))

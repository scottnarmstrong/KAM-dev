#!/usr/bin/env python3
"""LOCK-DATA, SOS option (a): the graph assemblies Pass.GraphL / Pass.GraphH by literal parts (untrusted tooling;
the kernel checks everything).

    lock_graphk_lit.py GDIR SEGPROD ROOT

The pLo/pHi checks `checkRealLowerBoundK` in one kernel run (the model with its 14817-term square, the scaled
square, the action model and their sum) were OOM-killed at 10 GB, each alone (tp12). Here every model of the check
is a literal from the mirror (`lock_sosk.realLowerModelK`), proved equal to its expression in its own module
(poly terms and radius separately), and `checkRealLowerBoundK_of_parts` (RealLowerKSq.lean) assembles them:

  GraphK/Lit{A,LGG,LG,LH,HGG,HG,HH}NN   the literal models (data)
  GraphK/Out{L,H}                       the square's product `out` (verbatim from Seg/Prod/M2016, M2017) by name
  GraphK/A{P,R}                         soGraphActionModel cert.graph = lockGKA (terms; radius)
  GraphK/{L,H}{GGP,GGR,GP,GR,HP,HR}     the square's model, the scaled square, the whole model = their literals
  GraphK/{L,H}                          the three model equations (certModel_eq_of_parts)
The pass modules Pass/GraphL, Pass/GraphH (lock-owned, hand-written) then close the check with one `exact` and one
kernel run on the final literal's supBound.

SEGPROD: the Seg/Prod directory holding M2016.lean and M2017.lean. ROOT: output root (files under
ROOT/KAM/SpinOrbit/Data/LockN65/GraphK).
"""
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import lock_cseg  # noqa: E402,F401  (sets CE.TY = LockBackend)
import csplit_emit as CE     # noqa: E402
import lock_seg as LSG       # noqa: E402
import sofx_model as M       # noqa: E402
import sofx_check as C       # noqa: E402
import lock_sosk as K        # noqa: E402

NS = "KAM.SpinOrbit.Data.LockN65"
P = NS + ".GraphK."


class GTree(CE.Tree):
    def mod(self, rel):
        return P + rel.replace("/", ".")

    def save(self):
        base = os.path.join(self.root, "KAM", "SpinOrbit", "Data", "LockN65", "GraphK")
        for rel, text in self.files.items():
            path = os.path.join(base, rel + ".lean")
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, "w").write(text)
        open(os.path.join(base, "heavy_modules.txt"), "w").write("\n".join(self.heavy) + "\n")


def out_text(path, name):
    """the `some …` right side of `theorem name :` in a generated product module (verbatim, one line)"""
    t = open(path).read()
    i = t.index("theorem %s :\n" % name)
    j = t.index(" := by\n", i)
    stmt = " ".join(l.strip() for l in t[i:j].splitlines()[1:])
    k = stmt.index(" = some ")
    return stmt[k + len(" = some "):]


def main(gdir, segprod, root):
    c, _ = LSG.lock_cert(gdir)
    B, W, gr = c.B, c.weight, c.graph
    T = GTree(root, "LockN65")
    base = [NS + ".Cert", NS + ".RealLowerKSq", NS + ".FallbackMul", NS + ".SegSupport"]
    fa = C.soGraphActionModel(B, c)
    data = {"A": fa}
    sides = {"L": ("pLo", fa, gr["pLo0"], gr["pLo"], gr["sosLo"], (7, 1), "2016", "cert.graph.sosLo",
                   "soGraphActionModel cert.graph"),
             "H": ("pHi", M.negM(B, fa), -gr["pHi0"], -gr["pHi"], gr["sosHi"], (7, 2), "2017", "cert.graph.sosHi",
                   "(soGraphActionModel cert.graph).negM")}
    for x, (side, f, m0, m, sos, key, mk, g, fexpr) in sides.items():
        gp = [((int(k[0]), int(k[1])), (int(v[0]), int(v[1]))) for k, v in sos]
        cfg2 = c.cfgLow.withExtra(key, ("direct",))
        gg = M.model_mul(B, W, cfg2, key, M.Model(0, gp, B.ofInt(0)), M.Model(0, C.conjSorted(B, gp), B.ofInt(0)))
        G = M.model_mul(B, W, cfg2, key, gg, C.ofConst(B, C.keyLen(gp), B.ofInt(-2), B.ofInt(0)))
        H = K.realLowerModelK(B, W, cfg2, key, f, m0, gp)
        sb = M.supBound(B, W, H)
        rhs = B.ofRatDown(2 * (F(m0) - F(m)))
        assert B.ble(sb, rhs), (side, "the mirror check fails")
        print(side, "gg %d G %d H %d terms; margin %.6e" % (len(gg.poly), len(G.poly), len(H.poly),
                                                          float(C.val(B, rhs) - C.val(B, sb))), flush=True)
        data[x + "GG"], data[x + "G"], data[x + "H"] = gg, G, H
    lit = {}
    for nm, mdl in data.items():
        items = []
        name = "lockGK%s" % nm
        lines = CE.model_defs(name, mdl)
        # pack the chunk defs (each `def …` block) into files of <= MAXLINES lines
        blocks, cur = [], []
        for l in lines:
            if l.startswith("def ") and cur:
                blocks.append(cur)
                cur = []
            cur.append(l)
        if cur:
            blocks.append(cur)
        items = [("%s#%d" % (name, i), b) for i, b in enumerate(blocks)]
        mods = T.data("Lit%s" % nm, "Graph check (option (a)): the literal model %s" % name,
                      "A mirror model of the keyed graph check (`lock_sosk.realLowerModelK`).", items,
                      [NS + ".Cert", NS + ".ZRows"])
        lit[nm] = mods[-1]
    W_, cfg = "cert.graph.base.weight", "cert.graph.base.cfgLow"
    cfgp = "{ %s with advice := %s.advice ++ [([%%d, %%d], ProductAdvice.direct)] }" % (cfg, cfg)
    pre = ["open SoGraph", ""]
    # the action model
    am = []
    for tag, st, pf in (("P", "(soGraphActionModel cert.graph).poly.terms = lockGKA.poly.terms :=",
                         "  eq_of_termsBeq (by decide +kernel)"),
                        ("R", "(soGraphActionModel cert.graph).rad = lockGKA.rad := by", "  decide +kernel")):
        am.append(T.write("A%s" % tag, base + [lit["A"]], "Graph check: the action model, %s" % (
            "terms" if tag == "P" else "radius"), "One kernel run against the literal.",
            pre + ["theorem lock_gkA%s :" % tag] + CE.wrap(st.split(" "), "    ") + [pf], heavy=True))
    amod = T.write("A", am, "Graph check: the action model", "Its literal (two parts).",
                   pre + ["theorem lock_gkA : soGraphActionModel cert.graph = lockGKA :=",
                          "  certModel_eq_of_parts (by decide +kernel) lock_gkAP lock_gkAR"])
    for x, (side, f, m0, m, sos, key, mk, g, fexpr) in sides.items():
        ot = out_text(os.path.join(segprod, "M%s.lean" % mk), "lockM%s" % mk)
        outn = "lockGK%sOut" % x
        ob = ["/-- The product of the square (the right side of `lockM%s`). -/" % mk]
        ob += CE.wrap(("def %s : List (ErrTerm LockBackend) × LockBackend := %s" % (outn, ot)).split(" "), "")
        ob += ["", "theorem lock_gk%sOut :" % x]
        ob += CE.wrap(("CertModel.polyProduct base.weight base.cfgLow [%d, %d] sos%sPoly sos%sPoly.conjSorted = some %s :="
                       % (key[0], key[1], "Lo" if x == "L" else "Hi", "Lo" if x == "L" else "Hi", outn)).split(" "),
                      "    ")
        ob += ["  lockM%s" % mk]
        omod = T.write("Out%s" % x, base + [NS + ".Seg.Prod.M%s" % mk], "Graph check: the square's product (%s)" % side,
                       "The memoized packed product, by name.", ob)
        sq = "sqModelOf %s %s [%d, %d] %s %s" % (W_, cfg, key[0], key[1], g, outn)
        cf = cfgp % key
        mulx = "CertModel.mul %s %s [%d, %d] lockGK%sGG (CertModel.ofConst %s.keyLen (ofInt (-2)) (ofInt 0))" % (
            W_, cf, key[0], key[1], x, g)
        m0s, ms = "cert.graph.%s₀" % side, "cert.graph.%s" % side
        m0e = m0s if x == "L" else "(-%s)" % m0s
        fl = "lockGKA" if x == "L" else "lockGKA.negM"
        parts = "realLowerModelKParts %s %s %s %s lockGK%sG" % (W_, fl, g, m0e, x)
        mods = {}
        for tag, lhs, rhs_, dep in (("GG", "(%s)" % sq, "lockGK%sGG" % x, [omod, lit[x + "GG"]]),
                                    ("G", "(%s)" % mulx, "lockGK%sG" % x, [lit[x + "GG"], lit[x + "G"]]),
                                    ("H", "(%s)" % parts, "lockGK%sH" % x, [lit["A"], lit[x + "G"], lit[x + "H"]])):
            two = []
            for pt, st, pf in (("P", "%s.poly.terms = %s.poly.terms :=" % (lhs, rhs_), "  eq_of_termsBeq (by decide +kernel)"),
                               ("R", "%s.rad = %s.rad := by" % (lhs, rhs_), "  decide +kernel")):
                two.append(T.write("%s%s%s" % (x, tag, pt), base + dep,
                                   "Graph check (%s): %s, %s" % (side, tag, "terms" if pt == "P" else "radius"),
                                   "One kernel run against the literal.",
                                   pre + ["theorem lock_gk%s%s%s :" % (x, tag, pt)] + CE.wrap(st.split(" "), "    ") +
                                   [pf], heavy=True))
            eq = "%s = %s :=" % (lhs, rhs_)
            mods[tag] = T.write("%s%s" % (x, tag), two, "Graph check (%s): %s" % (side, tag), "Its literal (two parts).",
                                pre + ["theorem lock_gk%s%s :" % (x, tag)] + CE.wrap(eq.split(" "), "    ") +
                                ["  certModel_eq_of_parts (by decide +kernel) lock_gk%s%sP lock_gk%s%sR" % (x, tag, x, tag)])
        hf = "lock_gkA" if x == "L" else "(congrArg CertModel.negM lock_gkA)"
        fin = ("checkRealLowerBoundK_of_parts lock_gk%sOut' lock_gk%sGG lock_gk%sG %s lock_gk%sH (by decide +kernel)"
               % (x, x, x, hf, x))
        print(x, "final:", fin)
    T.save()
    print("graphk", len(T.files), "modules", sum(len(t.encode()) for t in T.files.values()), "bytes",
          len(T.heavy), "heavy", flush=True)


if __name__ == "__main__":
    main(*sys.argv[1:])

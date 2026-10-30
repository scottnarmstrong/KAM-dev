#!/usr/bin/env python3
"""Emit the SO toy certificates (certificates/so-toys/<toy>.json) as Lean `TorusCertificate n ℚ` data.

Untrusted tooling (SO-TEST-A).  Each rational is written as a plain literal `(a / b)` when short, and otherwise
as `toyQ (toyInt …) (toyNat […])` with decimal chunks of `CHUNK` digits (KAM/Certificate/Tests/ToyLit.lean), so
that every line stays within 100 columns.  A long Fourier polynomial is written over its common denominator
(`toyScaledPoly D [(key, re·D, im·D)]`); `mkRat` normalizes, so the denoted ℚ values are identical.

    python3 toy_lean_cert.py TOY.json PREFIX            # prints `def PREFIX… ` declarations to stdout
"""
import json, sys
from fractions import Fraction as F
from math import lcm

CHUNK = 90
COLS = 100


def nat_chunks(v):
    s = str(v)
    head = len(s) % CHUNK or CHUNK
    return [s[:head]] + [s[i:i + CHUNK] for i in range(head, len(s), CHUNK)]


def chunked(head, v):
    """`head [c₀, c₁, …]` over decimal chunks, one chunk per line."""
    cs = nat_chunks(v)
    if len(cs) == 1:
        return ["(" + head + " [" + cs[0] + "])"]
    return ["(" + head + " [" + cs[0] + ","] + [c + ("," if i + 2 < len(cs) else "])")
                                                for i, c in enumerate(cs[1:])]


def big_nat(v):
    """a ℕ term (a line list)."""
    return [str(v)] if len(str(v)) <= 60 else chunked("toyNat", v)


def big_int(v):
    """a ℤ term (a line list)."""
    if len(str(abs(v))) <= 60:
        return ["(%d)" % v] if v < 0 else [str(v)]
    return chunked("toyNeg", -v) if v < 0 else chunked("toyPos", v)


def rat(q):
    """a ℚ term (a line list)."""
    q = F(q)
    if q.denominator == 1 and len(str(q.numerator)) <= 60:
        return ["(%d)" % q.numerator if q < 0 else "%d" % q.numerator]
    if len(str(q.numerator)) + len(str(q.denominator)) <= 60:
        return ["(%d / %d)" % (q.numerator, q.denominator)]
    return term("(toyQ ", big_int(q.numerator), " ", big_nat(q.denominator), ")")


def join(parts):
    """concatenate line-lists with single spaces where they meet."""
    out = []
    for p in parts:
        if not out:
            out = list(p)
        else:
            out[-1] = out[-1] + p[0]
            out += p[1:]
    return out


def term(*pieces):
    """pieces: str or line-list; joined on one logical term."""
    return join([[p] if isinstance(p, str) else p for p in pieces])


def key(k):
    return "[" + ", ".join(str(x) for x in k) + "]"


def cc(c):
    return term("⟨", rat(c[0]), ", ", rat(c[1]), "⟩")


def lst(items):
    """a list term from item line-lists."""
    if not items:
        return ["[]"]
    parts = ["["]
    for i, it in enumerate(items):
        parts.append(it)
        if i + 1 < len(items):
            parts.append(", ")
    parts.append("]")
    return term(*parts)


SPLIT = 40
EXTRA = []        # chunk declarations emitted before the declaration that uses them
PREFIX = [""]


def poly_terms(ts):
    if len(ts) > 8:
        L = 1
        for t in ts:
            L = lcm(L, F(t[1][0]).denominator, F(t[1][1]).denominator)
        items = []
        for t in ts:
            a, b = F(t[1][0]) * L, F(t[1][1]) * L
            items.append(term("(" + key(t[0]) + ", ", big_int(int(a)), ", ", big_int(int(b)), ")"))
        if len(items) > SPLIT:
            # long literals elaborate slowly: one declaration per SPLIT terms, concatenated
            names = []
            for i in range(0, len(items), SPLIT):
                nm = "%sTerms%d" % (PREFIX[0], len(EXTRA) + 1)
                EXTRA.append(decl(nm, "List (CertKey × ℤ × ℤ)", lst(items[i:i + SPLIT])))
                names.append(nm)
            return term("toyScaledPoly ", big_nat(L), " (" + " ++ ".join(names) + ")")
        return term("toyScaledPoly ", big_nat(L), " ", lst(items))
    return term("⟨", lst([term("(" + key(t[0]) + ", ", cc(t[1]), ")") for t in ts]), "⟩")


def realpoly(p):
    return term("⟨", rat(p["zero"]), ", ", lst([term("(" + key(t[0]) + ", ", cc(t[1]), ")")
                                               for t in p["half"]]), "⟩")


def expwit(w):
    return term("⟨", poly_terms(w["poly"]), ", %d, %d⟩" % (w["pinHalvings"], w["pinOrder"]))


def cfg(c):
    adv = lst([[("(" + key(k) + ", .%s)") % a] for k, a in c["advice"]])
    return term("⟨%d, %d, %d, fun _ _ => none, " % (c["cutoff"], c["taylorN"], c["halvings"]), adv, "⟩")


def wrap(lines, indent="  "):
    """reflow a term (list of logical pieces) into lines of at most COLS columns, breaking at spaces."""
    out, cur = [], indent
    text = " ".join(lines) if False else None
    for ln in lines:
        for w in ln.split(" "):
            if not w:
                continue
            if len(cur) + 1 + len(w) > COLS and cur.strip():
                out.append(cur.rstrip())
                cur = indent
            cur += w + " "
    if cur.strip():
        out.append(cur.rstrip())
    return out


def decl(name, typ, t, doc=None):
    out = []
    if doc:
        out.append("/-- %s -/" % doc)
    out.append("def %s : %s :=" % (name, typ))
    out += wrap(t)
    for ln in out:
        assert len(ln) <= COLS, ln
    return out + [""]


def emit(path, P):
    d = json.load(open(path))["certificate"]
    n = d["n"]
    p = d["params"]
    out = []
    fields = [("tau", str(p["tau"])), ("rho", p["rho"]), ("rhoInf", p["rhoInf"]), ("M", p["M"]),
              ("σK", p["sK"]), ("σB", p["sB"]), ("σT", p["sT"]), ("μ", p["mu"]), ("γbar", p["gbar"]),
              ("σω", p["sigma_omega"]), ("nuRay", p["nuRay"]), ("γ", p["gamma"]), ("s", p["s"]),
              ("err", p["err"]), ("E0", p["E0"]), ("disp", p["disp"])]
    pt = ["{"]
    for i, (f, v) in enumerate(fields):
        pt.append(term(f + " := ", [v] if f == "tau" else rat(v), "," if i + 1 < len(fields) else " }"))
    out += decl(P + "Params", "CertParams", join([[x] if isinstance(x, str) else x for x in pt]))
    out += decl(P + "Ham", "HamExpr %d" % n, [d["ham"]["lean"].replace("\n", " ")])
    w = lambda W: term("⟨", rat(W["rho"]), ", ", rat(W["w"]), "⟩")
    out += decl(P + "WeightH", "CertWeight", w(d["weightH"]))
    out += decl(P + "Weight", "CertWeight", w(d["weight"]))
    out += decl(P + "Centre", "List ℚ", lst([rat(x) for x in d["centre"]]))
    out += decl(P + "Radius", "List ℚ", lst([rat(x) for x in d["radius"]]))
    out += decl(P + "Box", "FreqBox", lst([term("(", rat(a), ", ", rat(b), ")") for a, b in d["freqBox"]]))
    e = d["emb"]
    out += decl(P + "Emb", "CertEmbedding ℚ", term(
        "⟨" + key(e["angleDeg"]) + ", ", lst([realpoly(q) for q in e["angle"]]),
        ", " + key(e["actionDeg"]) + ", ", lst([realpoly(q) for q in e["action"]]), "⟩"))
    wt = d["wit"]
    PREFIX[0] = P + "Wit"
    EXTRA.clear()
    wl = decl(P + "Wit", "Witnesses ℚ", term(
        "⟨", lst([expwit(x) for x in wt["expWit"]]), ", ", lst([poly_terms(x) for x in wt["invWit"]]),
        ", ", lst([term("(" + key(k) + ", ", expwit(x), ")") for k, x in wt["charWit"]]), ", []⟩"))
    for x in EXTRA:
        out += x
    out += wl
    out += decl(P + "GramInv", "List (List (CertPoly ℚ))",
                lst([lst([poly_terms(x) for x in row]) for row in d["gramInv"]]))
    out += decl(P + "TorsInv", "List (List (CC ℚ))", lst([lst([cc(x) for x in row]) for row in d["torsInv"]]))
    out += decl(P + "CfgFull", "ModelConfig ℚ", cfg(d["cfgFull"]))
    out += decl(P + "CfgLow", "ModelConfig ℚ", cfg(d["cfgLow"]))
    pe = d["piEnc"]
    out += decl(P + "Pi", "PiEnclosure ℚ", term("⟨", rat(pe["centre"]), ", ", rat(pe["rad"]),
                                               ", %d, %d⟩" % (pe["machinK"], pe["machinJ"])))
    fp = d.get("freqProvider")
    if fp:
        m, dd, lo, hi = fp["checkRootEnclosure"]
        out += decl(P + "RootLo", "ℚ", rat(lo), "lower end of the enclosure of `%d^(1/%d)`" % (dd, m))
        out += decl(P + "RootHi", "ℚ", rat(hi), "upper end of the enclosure of `%d^(1/%d)`" % (dd, m))
        out += decl(P + "AlgCoeffs", "List (List ℚ)",
                    lst([lst([rat(a) for a in row]) for row in fp["checkAlgBox_coeffs"]]))
    return out, d


if __name__ == "__main__":
    lines, _ = emit(sys.argv[1], sys.argv[2])
    print("\n".join(lines))

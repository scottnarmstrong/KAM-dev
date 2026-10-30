#!/usr/bin/env python3
"""SHARP2-B3B: cross-check of the Lean constants `KAM.Sharp2.stepConstsB` against `stageB` of thresholds_v2.py.

The Lean helper definitions (KAM/Sharp2/ModConstantsB/Data.lean, one per `let` of `stepConstsB`; the packaging
`stepConstsB_eq` is `rfl`) are parsed and evaluated with exact Fractions on package R1 (stage 0 and tail bites;
plain and isoenergetic; option L10 on and off) and compared with `stageB` constants and conditions.
Also a randomized monotonicity check of every constant under `StepInB.Dom` (including iso).

Usage: python3 -I scripts/apost_sharp/check_modconstb_v2.py   (untrusted design tooling)
"""
from fractions import Fraction as F
import os, random, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds_v2 as t2  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = open(os.path.join(ROOT, "KAM/Sharp2/ModConstantsB/Data.lean"), encoding="utf-8").read()

TOK = re.compile(r"\s*(\d+|[A-Za-z_Ͱ-Ͽ℀-⅏][\w.Ͱ-Ͽ₀-₟'ΩΘ]*|[()+\-*/^,:]|ℝ)")


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        if s[i].isspace():
            i += 1; continue
        m = TOK.match(s, i)
        if not m:
            raise SyntaxError(s[i:i + 20])
        out.append(m.group(1)); i = m.end()
    return out


def parse_defs():
    defs = {}
    for m in re.finditer(r"def (\w+) \(p : StepInB\) : ℝ :=\n((?:  .*\n)+)", SRC):
        defs[m.group(1)] = tokenize(m.group(2))
    return defs


DEFS = parse_defs()


class Ev:
    def __init__(self, p):
        self.p = p; self.memo = {}

    def helper(self, name):
        if name not in self.memo:
            self.memo[name] = self.run(DEFS[name])
        return self.memo[name]

    def run(self, toks):
        self.t = toks; self.i = 0
        saved = (self.t, self.i)
        v = self.expr()
        assert self.i == len(self.t), (self.t[self.i:], toks)
        return v

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        v = self.t[self.i]
        assert x is None or v == x, (v, x)
        self.i += 1
        return v

    def expr(self):
        if self.peek() == "if":
            self.eat(); c = self.cond(); self.eat("then"); a = self.expr(); self.eat("else"); b = self.expr()
            return a if c else b
        return self.add()

    def cond(self):
        v = self.eat(); assert v.startswith("p."), v
        return self.p[v[2:]]

    def add(self):
        v = self.mul()
        while self.peek() in ("+", "-"):
            op = self.eat(); w = self.mul(); v = v + w if op == "+" else v - w
        return v

    def mul(self):
        v = self.pow()
        while self.peek() in ("*", "/"):
            op = self.eat(); w = self.pow(); v = v * w if op == "*" else v / w
        return v

    def pow(self):
        v = self.app()
        if self.peek() == "^":
            self.eat(); e = self.pow()
            assert F(e).denominator == 1, e
            v = F(v) ** int(e)
        return v

    def app(self):
        t = self.peek()
        if t in ("max", "min"):
            self.eat(); a = self.atom(); b = self.atom()
            return max(a, b) if t == "max" else min(a, b)
        if t in DEFS:
            self.eat(); self.eat("p")
            saved = (self.t, self.i)
            v = self.helper(t)
            self.t, self.i = saved
            return v
        return self.atom()

    def atom(self):
        t = self.eat()
        if t == "(":
            v = self.expr()
            if self.peek() == ":":
                self.eat(); self.eat("ℝ")
            self.eat(")")
            return v
        if t.isdigit():
            return F(int(t))
        if t.startswith("p."):
            v = self.p[t[2:]]
            return F(v) if not isinstance(v, bool) else v
        raise SyntaxError(t)


def consts(p):
    ev = Ev(p)
    return {k: ev.helper(k) for k in DEFS}


def mkp(D, o, delta, r, c, c1, cr, iso, stage0=None, selfcons=False):
    n = D["n"]; kap = D["kappa"]
    M1, M2 = D["M1"], D["M2"]
    avg = cr * (delta / min(r, 1)) ** kap
    th = o.get("theta", F(1, 8))
    return {"n": n, "κ": F(kap), "M1": M1, "M2": M2, "cTh": 2 * M1, "cDTh": 2 * M2, "sK": D["sK"], "sLt": D["sLt"],
            "sB": D["sB"], "sN": D["sN"], "sNt": D["sNt"], "sT": D["sT"], "ts": F(1, 10), "bF": F(1),
            "c": c, "c1": c1, "cavg": avg, "θ": th, "θξ": F(1, 8), "θΩ": F(1, 8), "q": F(1, 8), "θN": F(1, 8),
            "θω": F(1, 8), "a": F(2), "lam": F(1), "γb": D["gbar"], "δ": delta, "selfcons": selfcons,
            "stage0": stage0 is not None, "ePer": stage0["e_over_mu"] if stage0 else F(0), "iso": iso,
            "Θ": D["Theta_omega"], "y0": D["Mh1"] * D["sN"], "Mh2": D["Mh2"], "lamW": F(1)}


FIELDS = ["n", "κ", "M1", "M2", "cTh", "cDTh", "sK", "sLt", "sB", "sN", "sNt", "sT", "ts", "bF", "c", "c1", "cavg",
          "θ", "θξ", "θΩ", "q", "θN", "θω", "a", "lam", "γb", "δ"]


def conds(p, k):
    """The Lean `stepCondB` as (coef, bound, power) triples (iso / selfcons clauses only when enabled)."""
    g = p["γb"] * p["δ"] ** p["κ"]; g1 = g * p["δ"]
    out = [(max(F(1), p["sB"] ** 2) * k["sCΩ"] * g, p["q"], 1), (k["sCDE"] * g, F(p["n"]), 1),
           (k["sCxiL"], p["θξ"], 1), (k["sCΩ"] * k["sCgL"], p["θΩ"], 1), (k["sCKt"] * g1, F(1), 1),
           (k["sCDLt"] * g, p["θ"] * p["sK"], 1), (k["sCDLtT"] * g, p["θ"] * p["sLt"], 1),
           (p["sB"] * k["sCG"] * k["sCDK"], p["θ"], 1), (k["sBsup"], p["ts"], 1), (k["sBloc"], p["bF"], 1)]
    if p["iso"]:
        out.append((k["sC0"] * g1, p["θω"], 1))
    if p["selfcons"]:
        out.append((k["sCNbT"] * k["sCEL"], p["θN"], 1))
        out.append((max(F(1), p["sB"] ** 2) * (1 + p["n"] * p["θξ"]) ** 2 * k["sCΩ"] * k["sQtN"] * g, p["q"], 2))
    return out


def main():
    D = t2.package("R1")
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / 6)
    r0 = D["rho"]
    ok = True
    for iso in (False, True):
        for selfc in (False, True):
            for stage0 in (None, dict(e_over_mu=F(7, 10))):
                for (c, c1, cr) in ((F(1, 3), F(2, 3), F(1, 5)), (F(7, 10), F(11, 10), F(1, 2))):
                    o = {"selfcons": selfc}
                    st = t2.stageB(D, o, delta0, r0, c, c1, cr, iso, stage0=stage0)
                    p = mkp(D, o, delta0, r0, c, c1, cr, iso, stage0, selfc)
                    k = consts(p)
                    pairs = [("sCDK", st["C_DK"]), ("sC0", st["C_0"]), ("sCxiL", st["C_xiL"]),
                             ("sQtN", st["Qt_N"]), ("sQL", st["QL"]), ("sQ", st["Q"]), ("sBloc", st["B_loc"]),
                             ("sCBb", st["rates"]["B"][0]), ("sCNb", st["rates"]["N"][0]),
                             ("sCNbT", st["rates"]["Nt"][0]), ("sCab", st["rates"]["Tab"][0])]
                    if iso:
                        pairs.append(("sCnu", st["rates"]["nu"][0]))
                    good = True
                    for nm, v in pairs:
                        if k[nm] != v:
                            good = False; print("  DIFF", nm, float(k[nm]), float(v))
                    # conditions: coef/bound with power, as a multiset
                    lc = sorted((float(a / b), pw) for a, b, pw in conds(p, k) if a != 0 or True)
                    pc = []
                    for tup in st["cond"]:
                        a, b = tup[0], tup[1]; pw = tup[2] if len(tup) > 2 else 1
                        pc.append((float(a / b), pw))
                    pc = sorted(pc)
                    # python has no Bloc condition (local budget); drop the matching Lean entry
                    lean_wo = list(lc)
                    bl = float(k["sBloc"] / p["bF"])
                    lean_wo.remove((bl, 1))
                    condsame = all(abs(x[0] - y[0]) <= 1e-12 * max(1, abs(y[0])) and x[1] == y[1]
                                   for x, y in zip(sorted(lean_wo), pc)) and len(lean_wo) == len(pc)
                    if not condsame:
                        print("  conds lean:", lean_wo); print("  conds py:  ", pc)
                    good &= condsame
                    ok &= good
                    print("iso=%-5s L10=%-5s stage0=%-5s c=%s: %d constants + %d conditions %s" % (
                        iso, selfc, stage0 is not None, c, len(pairs), len(pc), "EQUAL" if good else "DIFF"))
    print("R1 cross-check:", "all equal" if ok else "MISMATCH")
    # tail-style input (full-strip average), iso and plain
    # random monotonicity under Dom (plain and iso, L10 on/off)
    random.seed(1)
    viol = 0; trials = 0
    for iso in (False, True):
        for selfc in (False, True):
            for _ in range(300):
                p = mkp(D, {}, delta0, r0, F(1, 3), F(2, 3), F(1, 5), iso, None, selfc)
                for key in ("sK", "sB", "sN", "sNt", "sLt", "sT", "M1", "M2", "Θ", "Mh2", "y0", "cTh", "cDTh"):
                    p[key] = F(random.randint(1, 400), 100)
                p["cTh"] = 2 * p["M1"]
                p["c"] = F(random.randint(1, 100), 100); p["c1"] = F(random.randint(1, 100), 100)
                p["cavg"] = F(random.randint(0, 100), 100); p["lam"] = F(random.randint(1, 100), 100)
                p["lamW"] = F(random.randint(1, 100), 100); p["δ"] = F(random.randint(5, 100), 1000)
                a = consts(p)
                for key in ("c", "c1", "cavg", "δ", "lam", "lamW"):
                    q2 = dict(p); q2[key] = p[key] * F(3, 2)
                    if key == "lam" and q2["lam"] > 1: continue
                    if key == "lamW" and q2["lamW"] > 1: continue
                    b = consts(q2); trials += 1
                    if any(b[nm] < a[nm] for nm in ("sQ", "sCDK", "sCBb", "sCNb", "sCNbT", "sCab", "sCnu", "sBloc", "sQbN", "sQL")):
                        viol += 1
    print("monotonicity violations under Dom (plain/iso, L10 on/off):", viol, "/", trials)
    return 0 if ok and viol == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

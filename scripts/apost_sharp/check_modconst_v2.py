#!/usr/bin/env python3
"""SHARP2-B3: cross-check of the Lean constants `KAM.Sharp2.stepConsts` against `stageB` of thresholds_v2.py.

The Lean text of `stepConsts` (KAM/Sharp2/ModConstants.lean) is translated mechanically to exact Fractions and
evaluated on package R1 (stage 0 bite, plain and isoenergetic) and on random rational inputs.  Also searches for
non-monotonicity of the isoenergetic `QbN` in the small-divisor constant c and in the bite.

Usage: python3 -I scripts/apost_sharp/check_modconst_v2.py   (untrusted design tooling)
"""
from fractions import Fraction as F
import os, random, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds_v2 as t2  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = open(os.path.join(ROOT, "KAM/Sharp2/ModConstants.lean"), encoding="utf-8").read()


def translate():
    body = SRC[SRC.index("def stepConsts"):]
    body = body[:body.index("/-- The step conditions")]
    lines = body.split("\n")[1:]
    stmts, cur = [], None
    for ln in lines:
        if ln.startswith("  let "):
            if cur: stmts.append(cur)
            cur = ln.strip()[4:]
        elif ln.startswith("  ⟨"):
            if cur: stmts.append(cur)
            cur = None
            ret = ln.strip()
            ret_lines = [ln]
        elif cur is not None and ln.strip():
            cur += " " + ln.strip()
        elif cur is None and ln.startswith("    max"):
            ret_lines.append(ln)
    ret = " ".join(x.strip() for x in ret_lines)
    code = []
    def fix_max(s):
        while True:
            i = s.find("max ")
            if i < 0: return s
            j = i + 4
            def arg(j):
                while s[j] == " ": j += 1
                if s[j] == "(":
                    d = 0
                    for k in range(j, len(s)):
                        if s[k] == "(": d += 1
                        elif s[k] == ")":
                            d -= 1
                            if d == 0: return j, k + 1
                m = re.match(r"[\w.]+", s[j:])
                return j, j + m.end()
            a0, a1 = arg(j)
            b0, b1 = arg(a1)
            s = s[:i] + "MAX(" + s[a0:a1] + ", " + s[b0:b1] + ")" + s[b1:]
    def conv(e):
        e = e.replace("(n : ℝ)", "n")
        e = fix_max(e)
        e = re.sub(r"p\.(\w+)", lambda m: "p_" + m.group(1), e)
        e = e.replace("^", "**").replace("γ", "g_").replace("κ", "kap").replace("θ", "th").replace("Ω", "Om")
        e = e.replace("σ", "s_")
        # if A then B else C  ->  (B if A else C)   (innermost, one level)
        def fix_if(s):
            while True:
                m = re.search(r"\(if (\w+) then ", s)
                if not m: break
                start = m.start()
                # find matching paren
                depth = 0
                for i in range(start, len(s)):
                    if s[i] == "(": depth += 1
                    elif s[i] == ")":
                        depth -= 1
                        if depth == 0: end = i; break
                inner = s[m.end():end]
                k = inner.index(" else ")
                s = s[:start] + "((" + inner[:k] + ") if " + m.group(1) + " else (" + inner[k + 6:] + "))" + s[end + 1:]
            return s
        return fix_if(e)
    for s in stmts:
        name, rhs = s.split(":=", 1)
        name = name.strip().split(":")[0].strip()
        rhs = rhs.strip()
        if rhs.startswith("if p.iso then "):
            rhs = "(" + rhs + ")"
            rhs = rhs.replace("(if p.iso then ", "(if p.iso then ")
        if rhs.startswith("(if p.iso then ") and rhs.endswith(")"):
            inner = rhs[1:-1][len("if p.iso then "):]
            k = inner.index(" else ")
            rhs = "((" + inner[:k] + ") if p.iso else (" + inner[k + 6:] + "))"
        code.append(conv(name) + " = " + conv(rhs))
    r = ret.strip()[1:-1]
    return code, conv(r)


CODE, RET = translate()
NAMES = ["COm", "CE", "CDE", "CNN", "C0", "CxiN", "CKt", "CDLt", "CDLtT", "CEt", "QtN", "CgL", "CxiL", "CDK", "CEb",
         "CG", "CBb", "CNb", "CNbT", "CDT", "QbN", "QL", "Q"]


def lean_consts(p):
    env = {k: v for k, v in p.items()}
    env = {("p_" + k): v for k, v in p.items()}
    env["n"] = F(p["n"])
    env["max"] = max
    for line in CODE:
        exec(line, {}, env) if False else None
    loc = dict(env)
    for line in CODE:
        exec(line, {"MAX": max}, loc)
    vals = eval("[" + RET + "]", {"MAX": max}, loc)
    return dict(zip(NAMES, vals))


def mkp(D, delta, r, c, c1, cr, iso, t, lamL=F(1), lamW=F(1)):
    return dict(n=D["n"], kap=D["kappa"], M1=D["M1"], M2=D["M2"], sK=D["sK"], sLt=D["sLt"], sB=D["sB"], sN=D["sN"],
                sNt=D["sNt"], sT=D["sT"], t=t, c=c, c1=c1, cbar=cr, th=F(1, 8), thξ=F(1, 8), thΩ=F(1, 8), q=F(1, 8),
                lam=lamL, g_b=D["gbar"], δ=delta, r=r, iso=iso, Θ=D["Theta_omega"], y0=D["Mh1"] * D["sN"],
                Mh2=D["Mh2"], lamW=lamW)


def fix_names(p):
    m = {"kap": "κ", "th": "θ", "thξ": "θξ", "thΩ": "θΩ", "g_b": "γb"}
    return {("p_" + m.get(k, k)): v for k, v in p.items()}


def run(p):
    q = {k: v for k, v in p.items()}
    loc = {("p_" + {"kap": "kap", "th": "th", "thξ": "thξ", "thΩ": "thΩ", "g_b": "g_b"}.get(k, k)): v for k, v in q.items()}
    loc["p_g_b"] = p["g_b"]
    return None


def translate_name(k):
    return k.replace("γ", "g_").replace("κ", "kap").replace("θ", "th").replace("Ω", "Om").replace("σ", "s_")


def lean_eval(p):
    loc = {"p_" + translate_name(k): v for k, v in p.items()}
    loc["n"] = F(p["n"])
    for line in CODE:
        exec(line, {"MAX": max}, loc)
    return dict(zip(NAMES, eval("[" + RET + "]", {"MAX": max}, loc)))


def main():
    D = t2.package("R1")
    kap = D["kappa"]; n = D["n"]
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / 6)
    r0 = D["rho"]
    ok = True
    for iso in (False, True):
        for (c, c1, cr) in ((F(1, 3), F(2, 3), F(1, 5)), (F(7, 10), F(11, 10), F(1, 2))):
            delta = delta0; r = r0
            Nt, Nn, cTh = D["sNt"], D["sN"], 2 * D["M1"]
            t = cTh * Nt * Nn + F(1, 10)
            st = t2.stageB(D, {}, delta, r, c, c1, cr, iso, stage0=None)
            p = mkp(D, delta, r, c, c1, cr, iso, t)
            p["n"] = n
            lv = lean_eval(p)
            pairs = [("CDK", st["C_DK"]), ("C0", st["C_0"]), ("CxiL", st["C_xiL"]), ("QtN", st["Qt_N"]),
                     ("Q", st["Q"])]
            for nm, v in pairs:
                same = lv[nm] == v
                ok &= same
                print("iso=%-5s c=%s %-5s lean=%.12g python=%.12g %s" % (iso, c, nm, float(lv[nm]), float(v),
                                                                       "EQUAL" if same else "DIFF"))
    print("R1 cross-check:", "all equal" if ok else "MISMATCH")
    # non-monotonicity of iso QbN
    random.seed(1)
    bad_c = bad_d = 0; ex = None
    base = mkp(D, delta0, r0, F(1, 3), F(2, 3), F(1, 5), True, F(3, 2)); base["n"] = n
    for _ in range(2000):
        p = dict(base)
        for key in ("sK", "sB", "sN", "sNt", "sLt", "sT", "M1", "M2", "t", "lam", "Θ", "c1", "cbar"):
            p[key] = F(random.randint(1, 400), 100)
        p["c"] = F(random.randint(1, 100), 100)
        p["δ"] = F(random.randint(5, 100), 1000)
        p["r"] = F(1, 2)
        p["lamW"] = F(random.randint(1, 100), 100)
        a = lean_eval(p)["QbN"]
        q2 = dict(p); q2["c"] = p["c"] * 2
        if lean_eval(q2)["QbN"] < a:
            bad_c += 1
            if ex is None: ex = (p, q2)
        q3 = dict(p); q3["δ"] = p["δ"] * 2
        if lean_eval(q3)["QbN"] < a: bad_d += 1
    print("iso QbN decreases when c doubles: %d / 2000 random inputs; when delta doubles: %d / 2000" % (bad_c, bad_d))
    if ex:
        p, q2 = ex
        print("example (iso): c=%s -> %s: QbN %.6g -> %.6g; other inputs:" % (p["c"], q2["c"],
              float(lean_eval(p)["QbN"]), float(lean_eval(q2)["QbN"])), {k: float(v) for k, v in p.items() if k != "iso"})
    # plain step: monotone (sanity)
    viol = 0
    for _ in range(500):
        p = dict(base); p["iso"] = False
        for key in ("sK", "sB", "sN", "sNt", "sLt", "sT", "M1", "M2", "t", "lam", "c1", "cbar", "c"):
            p[key] = F(random.randint(1, 400), 100)
        p["δ"] = F(random.randint(5, 100), 1000); p["r"] = F(1, 2)
        a = lean_eval(p)
        for key in ("c", "c1", "cbar", "δ", "sK", "sT", "t", "M2", "lam"):
            q2 = dict(p); q2[key] = p[key] * F(3, 2)
            b = lean_eval(q2)
            if any(b[k] < a[k] for k in NAMES): viol += 1
    print("plain step: monotonicity violations in 500 x 9 random trials:", viol)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

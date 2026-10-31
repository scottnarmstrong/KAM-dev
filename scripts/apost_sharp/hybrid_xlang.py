#!/usr/bin/env python3
"""Cross-language regression of the hybrid mirror against the Lean checker (package SHARP2-C8DFIX).

Cases: the two accepted files (docs/campaign/design/hybrid/hybrid-T2.json, hybrid-R1-L8.json) and mutations of them,
each aimed at one check (with boundary pairs: a claim at its exact Lean value is accepted, 10^-40 below it rejected).
For every case the mirror (hybrid_mirror.check) and the Lean definitions (`#eval` in a generated probe) evaluate the
same sub-checks of `checkHybrid`:
  transferOk, hybWeightsOk, hybPolyOk, hybCauchyOk, the d_omega check, and the conjuncts of refinedCoreR except
  sitesOk (Xs > 0, wfOk, okR, budgetOk, classicalOk tail, finalOkA);
for T2 the probe also runs the complete `checkHybrid toyCert2H w` (hybOmegaOk, hybCompOk and sitesOk included).
The R1 cases use a certificate stub `{ toyCert2H with params, freqBox, weight, expHalvings, expOrder, piEnc }`: the
sub-checks above read only these fields (R1's TorusCertificate is not in Lean).  Exact intermediate values (the
transfer numbers, the step sup bounds and derivative matrices, ratExpUp to 10^-60) are compared as strings on the
accepted files and on synthetic nonzero fixtures (all transfer fields distinct; a polynomial step with complex
coefficients, degrees -1, 1, 0, 2 and a missing component; AUDIT-C8C-1's scalar counterexample, tA = 503/100000).

Usage:
  python3 -I scripts/apost_sharp/hybrid_xlang.py                 # mirror against the recorded Lean results
  python3 -I scripts/apost_sharp/hybrid_xlang.py --lean          # also run the Lean probe (< 4 GB) and compare live
  python3 -I scripts/apost_sharp/hybrid_xlang.py --lean --record # rewrite the recorded results (xlang-lean.json)
Exit status 0 iff every comparison agrees.
"""
import copy, json, math, os, subprocess, sys, time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import hybrid_mirror as HM   # noqa: E402

sys.set_int_max_str_digits(0)
DATA = os.path.join(ROOT, "docs", "campaign", "design", "hybrid")
RECORD = os.path.join(DATA, "xlang-lean.json")
PROBE_DIR = os.path.join(ROOT, ".drafts", "c8dfix", "xlang")
RSS_LIMIT_KB = 4_000_000
GROUPS = ("transfer", "weights", "poly", "cauchy", "dw", "xs", "wf", "okR", "budget", "tail", "final")
CORE = {"Xs > 0": "xs", "wfOk": "wf", "okR": "okR", "budgetOk": "budget", "classicalOk tail": "tail",
        "finalOkA": "final"}


def fq(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else "%d/%d" % (x.numerator, x.denominator)


# ============================================================================================ the cases
def tiny(k=40):
    return F(1, 10 ** k)


def mutate(data, fn):
    d = copy.deepcopy(data)
    fn(d)
    return d


def setp(sec, key, val):
    def f(d):
        if sec == "p1":
            d["restart"]["params1"][key] = fq(val)
        elif sec == "bp":
            d["base"]["params"][key] = fq(val)
        elif sec == "cl":
            d["step"]["claims"][key] = fq(val)
        elif sec == "R1":
            d["restart"]["witness1"]["base"]["R"][key] = fq(val)
        elif sec == "core":
            d["restart"]["witness1"]["base"]["core"][key] = fq(val)
        elif sec == "W":
            d["step"]["weights"][key] = {"rho": fq(val[0]), "w": fq(val[1])}
        elif sec == "step":
            d["step"][key] = fq(val)
    return f


def cases():
    t2 = json.load(open(os.path.join(DATA, "hybrid-T2.json")))
    r1 = json.load(open(os.path.join(DATA, "hybrid-R1-L8.json")))
    out = [("t2-ok", t2), ("r1-ok", r1)]
    # --- T2
    rT = HM.check(t2, margins=False)
    vT, p1, bp = rT["values"], HM.params_from(t2["restart"]["params1"]), HM.params_from(t2["base"]["params"])
    cl = {k: F(v) for k, v in t2["step"]["claims"].items()}
    W1 = HM.weight_from(t2["step"]["weights"]["rho1"])
    a, b = HM.rat_exp_up(2 * HM.PI_UP_Q * 10, 8, 24)
    out += [
        ("t2-w1-audit", mutate(t2, setp("W", "rho1", (F(1), F(536))))),
        ("t2-w1-below", mutate(t2, setp("W", "rho1", (W1[0], W1[1] - 1)))),
        ("t2-winf-rho0", mutate(t2, setp("W", "rhoinf", (F(0), F(1))))),
        ("t2-wt-low", mutate(t2, setp("W", "torsion", (vT["rhoT"] - F(1, 10 ** 6),
                                                       F(t2["step"]["weights"]["torsion"]["w"]))))),
        ("t2-w1-wide", mutate(t2, setp("W", "rho1", (F(10), F(-((-a) // b)))))),
        ("t2-dE0", mutate(t2, setp("cl", "dE0", cl["dE0"] - tiny(60)))),
        ("t2-nuRay", mutate(t2, setp("p1", "nuRay", bp["nuRay"] - cl["dw"] + F(1, 10 ** 9)))),
        ("t2-disp", mutate(t2, setp("bp", "disp", max(cl["dinf"], cl["dw"]) + p1["disp"] - tiny(60)))),
        ("t2-sK", mutate(t2, setp("p1", "sK", p1["sK"] + tiny(30)))),
        ("t2-bT", mutate(t2, setp("R1", "bT", vT["t1"] - tiny(30)))),
        ("t2-err", mutate(t2, setp("p1", "err", vT["e1"] - tiny(60)))),
        ("t2-s1", mutate(t2, setp("step", "s1", F(t2["step"]["s1"]) + tiny(30)))),
        ("t2-d0neg", mutate(t2, setp("cl", "d0", -tiny(30)))),
        ("t2-xs0", mutate(t2, setp("core", "Xs", F(0)))),
        ("t2-mu-big", mutate(t2, setp("p1", "mu", bp["mu"] + F(1, 10 ** 9)))),
    ]
    # --- R1: boundary pairs at the exact Lean values (declared Machin parameters)
    rR = HM.check(r1, margins=False)
    vR, p1, bp = rR["values"], HM.params_from(r1["restart"]["params1"]), HM.params_from(r1["base"]["params"])
    cl = {k: F(v) for k, v in r1["step"]["claims"].items()}
    exact = dict(d0=max(vR["sup_d0"]), dinf=max(vR["sup_dinf"]), d0R=max(vR["sup_d0R"]), d1=vR["sum_d1"],
                 d1t=vR["sum_d1t"], d1R=vR["sum_d1R"], d1tR=vR["sum_d1tR"],
                 dE0=2 * bp["err"] / (bp["rho"] - vR["rhoT"]))
    for k, v in exact.items():
        out += [("r1-%s-exact" % k, mutate(r1, setp("cl", k, v))),
                ("r1-%s-below" % k, mutate(r1, setp("cl", k, v - tiny())))]
    out += [("r1-sT-exact", mutate(r1, setp("p1", "sT", vR["mT"] + p1["mu"]))),
            ("r1-sT-below", mutate(r1, setp("p1", "sT", vR["mT"] + p1["mu"] - tiny()))),
            ("r1-bT-exact", mutate(r1, setp("R1", "bT", vR["t1"]))),
            ("r1-bT-below", mutate(r1, setp("R1", "bT", vR["t1"] - tiny())))]
    old = dict(rho1=(F(1, 70), F(546955746057597, 500000000000000)),
               rhoinf=(F(1, 70000), F(62505610239141, 62500000000000)),
               torsion=(F(1667, 140000), F(538842267979699, 500000000000000)))
    def oldw(d):
        for k, v in old.items():
            setp("W", k, v)(d)
    out.append(("r1-weights-c8d", mutate(r1, oldw)))
    for k in ("rho1", "rhoinf", "torsion"):
        W = HM.weight_from(r1["step"]["weights"][k])
        a, b = HM.rat_exp_up(2 * HM.PI_UP_Q * W[0], 8, 24)
        lo, hi = F(a * 10 ** 40 // b, 10 ** 40), F(-((-a * 10 ** 40) // b), 10 ** 40)
        out += [("r1-%s-w-ceil40" % k, mutate(r1, setp("W", k, (W[0], hi)))),
                ("r1-%s-w-floor40" % k, mutate(r1, setp("W", k, (W[0], lo))))]
    out.append(("r1-wt-rho-low", mutate(r1, setp("W", "torsion", (vR["rhoT"] - tiny(), F(r1["step"]["weights"]
                                                                                       ["torsion"]["w"]))))))
    return out


def mirror_groups(res):
    g = res["groups"]
    out = {"transfer": all(v for _, v in g["transferOk"]), "weights": all(v for _, v in g["hybWeightsOk"]),
           "poly": all(v for _, v in g["hybPolyOk"]), "cauchy": all(v for _, v in g["hybCauchyOk"]),
           "dw": all(v for _, v in g["dw"])}
    for nm, v in g["refinedCoreR"]:
        if nm in CORE:
            out[CORE[nm]] = bool(v)
    return out


# ============================================================================================ Lean emission
def lq(x):
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℚ)" % (x.numerator, x.denominator)


def lean_params(d):
    p = HM.params_from(d)
    names = [("tau", "tau"), ("rho", "rho"), ("rhoInf", "rhoInf"), ("M", "M"), ("σK", "sK"), ("σB", "sB"),
             ("σT", "sT"), ("μ", "mu"), ("γbar", "gbar"), ("σω", "sigma_omega"), ("nuRay", "nuRay"), ("γ", "gamma"),
             ("s", "s"), ("err", "err"), ("E0", "E0"), ("disp", "disp")]
    return "{ " + ", ".join("%s := %s" % (a, p[b] if a == "tau" else lq(p[b])) for a, b in names) + " }"


def lean_claim(R):
    return "{ " + ", ".join("%s := %s" % (k, lq(R[k])) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt",
                                                                  "bT")) + " }"


def lean_poly_defs(name, P):
    """a CertRealPoly as chunked term lists (heartbeats are per declaration: at most 40 terms each)."""
    zero, half = P
    lines, parts = [], []
    for j in range(0, len(half), 40):
        nm = "%sP%d" % (name, j // 40)
        parts.append(nm)
        lines.append("def %s : List (CertKey × CC ℚ) :=\n  [%s]" % (nm, ",\n   ".join(
            "([%s], ⟨%s, %s⟩)" % (", ".join(str(x) for x in k), lq(re), lq(im)) for k, re, im in half[j:j + 40])))
    return lines, "⟨%s, %s⟩" % (lq(zero), " ++ ".join(parts) if parts else "[]")


def lean_emb_defs(name, E):
    lines, ang, act = [], [], []
    for i, P in enumerate(E["angle"]):
        L, t = lean_poly_defs("%sA%d" % (name, i), P)
        lines += L
        ang.append(t)
    for i, P in enumerate(E["action"]):
        L, t = lean_poly_defs("%sB%d" % (name, i), P)
        lines += L
        act.append(t)
    lines.append("def %s : CertEmbedding ℚ := ⟨[%s], [%s], [%s], [%s]⟩" % (
        name, ", ".join(str(x) for x in E["angleDeg"]), ", ".join(ang), ", ".join(str(x) for x in E["actionDeg"]),
        ", ".join(act)))
    return lines


def lean_case(name, data, dK_name, t2, values=False):
    w = HM.hybwit_from(data)
    st, p1, w1 = w["step"], w["p1"], w["w1"]
    cert = HM.cert_from(data)
    core = w1["base"]["core"]
    sites = "toyRefinedWit.sites" if t2 else "[]"
    ns = name.replace("-", "_")
    box = "[" + ", ".join("(%s, %s)" % (lq(c), lq(r)) for c, r in HM.box_from(data["base"]["freqBox"])) + "]"
    clv = ", ".join(lq(st["cl"][k]) for k in HM.CLAIMS)
    L = ["namespace %s" % ns,
         "def hbp : CertParams := %s" % lean_params(data["base"]["params"]),
         "def hbox : FreqBox := %s" % box,
         "def hR0 : RefClaim := %s" % lean_claim(w["R0"]),
         "def hst : HybStep := { dK := %s, s1 := %s, W1 := ⟨%s, %s⟩, Winf := ⟨%s, %s⟩, WT := ⟨%s, %s⟩," % (
             dK_name, lq(st["s1"]), lq(st["W1"][0]), lq(st["W1"][1]), lq(st["Winf"][0]), lq(st["Winf"][1]),
             lq(st["WT"][0]), lq(st["WT"][1])),
         "  cl := ⟨%s⟩, lH := %s, dw := %s }" % (clv, lq(st["lH"]), lq(st["dw"])),
         "def hp1 : CertParams := %s" % lean_params(data["restart"]["params1"]),
         "def hw1 : RefinedWitR := { base := { core := { Xs := %s, kp := %d, th := %s, c := [%s], cbar := [%s]," % (
             lq(core["Xs"]), core["kp"], lq(core["th"]), ", ".join(lq(x) for x in core["c"]),
             ", ".join(lq(x) for x in core["cbar"])),
         "  ctail := %s, sB := %s, sT := %s, sLt := %s, sN := %s, sNt := %s, t := %s, J := %d }," % (
             lq(core["ctail"]), lq(core["sB"]), lq(core["sT"]), lq(core["sLt"]), lq(core["sN"]), lq(core["sNt"]),
             lq(core["t"]), core["J"]),
         "  R := %s, κ := %s, sites := %s }, bF := %s, bT := %s }" % (
             lean_claim(w1["base"]["R"]), lq(w1["base"]["kappa"]), sites, lq(w1["bF"]), lq(w1["bT"])),
         "def hw : HybWit := ⟨hR0, hst, hp1, hw1⟩",
         "def hc : TorusCertificate 2 ℚ := { toyCert2H with params := hbp, freqBox := hbox,",
         "  weight := ⟨%s, toyCert2H.weight.w⟩, expHalvings := %d, expOrder := %d," % (
             lq(cert["weightRho"]), cert["expHalvings"], cert["expOrder"]),
         "  piEnc := { toyCert2H.piEnc with machinK := %d, machinJ := %d } }" % cert["pe"],
         "def hQ : NumQ := hw1.base.num 2 hp1 hbox",
         '#eval IO.println s!"CASE %s transfer={transferOk 2 hbp hbox hw} weights={hybWeightsOk hc hst hp1.rho '
         'hp1.rhoInf (hw.ρT 2 hbox)} poly={hybPolyOk (n := 2) hst hc.piEnc} cauchy={hybCauchyOk hc hst '
         '(hw.ρT 2 hbox)} dw={decide (|hst.s1 - hbp.s| * boxNormUp hbox ≤ hst.dw)} '
         'xs={decide (0 < hw1.base.core.Xs)} wf={hQ.wfOk} okR={hQ.okR hw1.bF (capRQ hQ hp1.μ hp1.nuRay hw1.bT) '
         '(initRQ hw1.base.R.bL hw1.base.R.bN hw1.base.R.bNt hp1.σK hp1.σB hp1.μ) hw1.base.core.Xs} '
         'budget={hQ.budgetOk (hp1.σT - hp1.μ) hw1.base.R.bT hw1.bF hw1.bT} '
         'tail={classicalOk 2 hp1.tau hw1.base.core.J (hQ.δ hw1.base.core.kp) hQ.ctail} '
         'final={finalOkA hQ hp1 hbox hw1.base.core.Xs}"' % name]
    if t2:
        L.append('#eval IO.println s!"FULL %s omega={hybOmegaOk hc hst} comp={hybCompOk hc hst} sites={sitesOk hQ '
                 'hw1.base.core.J hbox hw1.base.κ hp1.γ hw1.base.sites} check={checkHybrid hc hw}"' % name)
    if values:
        for key, e in VALUE_EXPRS:
            L.append('#eval IO.println s!"VAL %s %s {%s}"' % (name, key, e))
    L.append("end %s" % ns)
    out = []                 # one line per structure instance (its fields are `sepByIndent`: no shallower lines)
    for x in L:
        if x.startswith("  ") and out:
            out[-1] += " " + x.strip()
        else:
            out.append(x)
    return out


VALUE_EXPRS = [  # (key in the mirror's values, Lean expression in a case namespace)
    ("tAx", "hw.tAx 2 hbp hbox"), ("t1", "hw.t1 2 hbp hbox"), ("mT", "hw.mT 2 hbp hbox"), ("delta1", "hw.δ1 2 hbox"),
    ("rhoT", "hw.ρT 2 hbox"), ("tA", "hst.cl.tA (hw.kq hbp) 2 hR0.dx hR0.d2x (hw.δ1 2 hbox) (2 * hR0.dx)"),
    ("e1", "hst.cl.e1 hR0.d2x"), ("e1iso", "(hw.qq).e1 hst.cl hR0.d2x"),
    ("dabS", "dABQ (hst.cl.frS (hw.kq hbp)) (2 * hR0.dx) (2 * hR0.d2x) hst.cl.d0"),
    ("dabR", "dABQ (hst.cl.frR (hw.kq hbp)) (2 * hR0.dx) (2 * hR0.d2x) hst.cl.d0R"),
    ("lam0S", "hst.cl.lam0 (hw.kq hbp) 2 hR0.dx false"), ("lam0R", "hst.cl.lam0 (hw.kq hbp) 2 hR0.dx true"),
    ("lam1S", "hst.cl.lam1 (hw.kq hbp) 2 hR0.dx hR0.d2x (hw.δ1 2 hbox) false"),
    ("lam1R", "hst.cl.lam1 (hw.kq hbp) 2 hR0.dx hR0.d2x (hw.δ1 2 hbox) true"),
    ("sK1", "hst.cl.sK1 (hw.kq hbp) hp1.μ"), ("sB1", "hst.cl.sB1 (hw.kq hbp) hp1.μ"),
] + [("%s.%s" % (f, x), "(hst.cl.%s (hw.kq hbp)).%s" % (f, y)) for f in ("frS", "frR")
     for x, y in (("g", "g"), ("b1", "β1"), ("b", "b"), ("nD", "nΔ"), ("nDt", "nΔt"))] + [
    ("sup_d0", "(List.range 4).map fun a => (stepModel 2 (ratE (α := ℚ) hst.dK) a).supBound hst.W1"),
    ("sup_dinf", "(List.range 4).map fun a => (stepModel 2 (ratE (α := ℚ) hst.dK) a).supBound hst.Winf"),
    ("sup_d0R", "(List.range 4).map fun a => (stepModel 2 (ratE (α := ℚ) hst.dK) a).supBound realWeight"),
    ("lv_strip", "(List.range 4).map fun a => (List.range 2).map fun j => "
                 "(dstepModel 2 hst.W1 hc.piEnc (ratE (α := ℚ) hst.dK) a j).supBound hst.W1"),
    ("lv_real", "(List.range 4).map fun a => (List.range 2).map fun j => "
                "(dstepModel 2 hst.Winf hc.piEnc (ratE (α := ℚ) hst.dK) a j).supBound realWeight")] + [
    ("rexp60_" + k, "(ratExpUp (2 * piUpQ * hst.%s.rho) hc.expHalvings hc.expOrder * 10 ^ 60).floor" % W)
    for k, W in (("W1", "W1"), ("Winf", "Winf"), ("WT", "WT"))]


def mirror_values(name, data):
    v = HM.check(data, margins=False)["values"]
    st, cert = HM.hybwit_from(data)["step"], HM.cert_from(data)
    out = {}
    for key, _ in VALUE_EXPRS:
        if key.startswith("rexp60_"):
            a, b = HM.rat_exp_up(2 * HM.PI_UP_Q * st[key[7:]][0], cert["expHalvings"], cert["expOrder"])
            out["%s %s" % (name, key)] = str(a * 10 ** 60 // b)
        else:
            out["%s %s" % (name, key)] = canon(v[key])
    return out


def canon(x):
    if isinstance(x, list):
        return "[" + ",".join(canon(y) for y in x) + "]"
    return fq(x)


# --- synthetic fixtures: transfer numbers with distinct nonzero values; AUDIT-C8C-1's tA; a polynomial step
SYN_B = dict(d0=F(3, 1000), dinf=F(5, 1000), d1=F(7, 100), d1t=F(11, 100), d0R=F(13, 10000), d1R=F(17, 1000),
             d1tR=F(19, 1000), lE=F(23, 10 ** 5), dE0=F(29, 1000), o0=F(31, 1000), dE0R=F(37, 1000), o0R=F(41, 1000),
             o1=F(43, 1000), o1R=F(47, 1000))
SYN_K = dict(l=F(53, 50), lt=F(59, 50), beta=F(61, 100), nu=F(67, 50), nut=F(71, 50), t=F(73, 20), m=F(79, 100))
SYN_Q = dict(lH=F(83, 10 ** 6), dw=F(89, 10 ** 6), Mh1=F(97, 50), Mh2=F(101, 50))
SYN_ARGS = (F(2), F(103, 50), F(107, 100), F(1, 300), F(109, 50))       # nn, M1, M2, δ, cTh
AUD_B = dict(d0=F(0), dinf=F(0), d1=F(1, 10), d1t=F(1, 10), d0R=F(0), d1R=F(0), d1tR=F(0), lE=F(1, 100), dE0=F(0),
             o0=F(0), dE0R=F(0), o0R=F(0), o1=F(0), o1R=F(1))
AUD_K = dict(l=F(1), lt=F(1), beta=F(1, 10), nu=F(1), nut=F(1), t=F(0), m=F(0))
AUD_ARGS = (F(1), F(1), F(0), F(1), F(2))
SYN_P = dict(angleDeg=[-1], angle=[(F(3, 7), [((1, 0), F(1, 3), F(-2, 5)), ((0, 2), F(-5, 11), F(0)),
                                              ((2, -1), F(0), F(7, 13))])],
             actionDeg=[0, 2], action=[(F(-1, 9), [((1, 1), F(2, 3), F(1, 4)), ((3, -2), F(-1, 6), F(5, 17))]),
                                       (F(0), [((0, 1), F(1, 8), F(-1, 8)), ((1, -1), F(9, 10), F(0))])])
SYN_W, SYN_WB = (F(1, 3), F(7, 2)), (F(1, 5), F(9, 4))


def synthetic_values():
    out = {}
    for tag, b, k, args in (("syn", SYN_B, SYN_K, SYN_ARGS), ("aud", AUD_B, AUD_K, AUD_ARGS)):
        nn, M1, M2, dl, cTh = args
        fS, fR = HM.frS(b, k), HM.frR(b, k)
        vals = {"frS.g": fS["g"], "frS.b1": fS["b1"], "frS.nDt": fS["nDt"], "frR.b": fR["b"], "frR.nD": fR["nD"],
                "dabS": HM.dABQ(fS, cTh, 2 * M2, b["d0"]), "lam0S": HM.lam0(b, k, nn, M1, False),
                "lam0R": HM.lam0(b, k, nn, M1, True), "lam1S": HM.lam1(b, k, nn, M1, M2, dl, False),
                "lam1R": HM.lam1(b, k, nn, M1, M2, dl, True), "t1": HM.t1_of(b, k, nn, M1, M2, dl, cTh),
                "tA": HM.tA_of(b, k, nn, M1, M2, dl, cTh), "e1": HM.e1_step(b, M2),
                "tAext": HM.tAext_of(SYN_Q, b, k, nn, M1, M2, dl, cTh), "e1iso": HM.e1_iso(SYN_Q, b, M2),
                "sK1": k["l"] + b["d1"] + F(1, 100), "sB1": fS["b1"] + F(1, 100)}
        out.update({"%s.%s" % (tag, kk): fq(v) for kk, v in vals.items()})
    for pe in ((2, 1), (4, 4), (0, 0)):
        out["poly.sup.%d%d" % pe] = canon(HM.step_sups(2, SYN_W, SYN_P))
        out["poly.lv.%d%d" % pe] = canon(HM.dstep_matrix(2, SYN_W, SYN_WB, pe, SYN_P))
    return out


def lean_synthetic():
    def numq(b):
        return "⟨" + ", ".join(lq(b[k]) for k in HM.CLAIMS) + "⟩"
    def kq(k):
        return "⟨" + ", ".join(lq(k[x]) for x in ("l", "lt", "beta", "nu", "nut", "t", "m")) + "⟩"
    L = ["def isoQ : IsoNumQ := ⟨%s⟩" % ", ".join(lq(SYN_Q[x]) for x in ("lH", "dw", "Mh1", "Mh2"))]
    for tag, b, k, args in (("syn", SYN_B, SYN_K, SYN_ARGS), ("aud", AUD_B, AUD_K, AUD_ARGS)):
        nn, M1, M2, dl, cTh = (lq(x) for x in args)
        L += ["def %sB : StepNumQ := %s" % (tag, numq(b)), "def %sK : KDataQ := %s" % (tag, kq(k))]
        ex = {"frS.g": "(%sB.frS %sK).g", "frS.b1": "(%sB.frS %sK).β1", "frS.nDt": "(%sB.frS %sK).nΔt",
              "frR.b": "(%sB.frR %sK).b", "frR.nD": "(%sB.frR %sK).nΔ"}
        for kk, e in ex.items():
            L.append('#eval IO.println s!"VAL - %s.%s {%s}"' % (tag, kk, e % (tag, tag)))
        more = {"dabS": "dABQ (%sB.frS %sK) %s (2 * %s) %sB.d0" % (tag, tag, cTh, M2, tag),
                "lam0S": "%sB.lam0 %sK %s %s false" % (tag, tag, nn, M1),
                "lam0R": "%sB.lam0 %sK %s %s true" % (tag, tag, nn, M1),
                "lam1S": "%sB.lam1 %sK %s %s %s %s false" % (tag, tag, nn, M1, M2, dl),
                "lam1R": "%sB.lam1 %sK %s %s %s %s true" % (tag, tag, nn, M1, M2, dl),
                "t1": "%sB.t1 %sK %s %s %s %s %s" % (tag, tag, nn, M1, M2, dl, cTh),
                "tA": "%sB.tA %sK %s %s %s %s %s" % (tag, tag, nn, M1, M2, dl, cTh),
                "e1": "%sB.e1 %s" % (tag, M2),
                "tAext": "isoQ.tAext %sB %sK %s %s %s %s %s" % (tag, tag, nn, M1, M2, dl, cTh),
                "e1iso": "isoQ.e1 %sB %s" % (tag, M2),
                "sK1": "%sB.sK1 %sK (1 / 100)" % (tag, tag), "sB1": "%sB.sB1 %sK (1 / 100)" % (tag, tag)}
        for kk, e in more.items():
            L.append('#eval IO.println s!"VAL - %s.%s {%s}"' % (tag, kk, e))
    L += lean_emb_defs("synP", SYN_P)
    W, Wb = "(⟨%s, %s⟩ : CertWeight)" % tuple(lq(x) for x in SYN_W), "(⟨%s, %s⟩ : CertWeight)" % tuple(
        lq(x) for x in SYN_WB)
    for pe in ((2, 1), (4, 4), (0, 0)):
        pen = "{ toyCert2H.piEnc with machinK := %d, machinJ := %d }" % pe
        L.append('#eval IO.println s!"VAL - poly.sup.%d%d {(List.range 4).map fun a => (stepModel 2 synP a).supBound '
                 '%s}"' % (pe + (W,)))
        L.append('#eval IO.println s!"VAL - poly.lv.%d%d {(List.range 4).map fun a => (List.range 2).map fun j => '
                 '(dstepModel 2 %s %s synP a j).supBound %s}"' % (pe + (W, pen, Wb)))
    return L


def write_probes(cs):
    """two probes, each one niced Lean process under the RSS limit: the T2 cases (with the complete checkHybrid),
    then the R1 cases, the accepted files' values and the synthetic fixtures."""
    head = ["import KAM.CertificateSharp.Hybrid.Tests.T2",
            "open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.CertificateSharp.Hybrid", ""]
    r1 = json.load(open(os.path.join(DATA, "hybrid-R1-L8.json")))
    t2 = json.load(open(os.path.join(DATA, "hybrid-T2.json")))
    A = head + lean_emb_defs("t2dK", HM.emb_from(t2["step"]["dK"], int(t2["scale_bits"])))
    B = head + lean_emb_defs("r1dK", HM.emb_from(r1["step"]["dK"], int(r1["scale_bits"])))
    for name, data in cs:
        t = name.startswith("t2")
        (A if t else B).extend(lean_case(name, data, "t2dK" if t else "r1dK", t, values=name in ("t2-ok", "r1-ok")))
    B += lean_synthetic()
    os.makedirs(PROBE_DIR, exist_ok=True)
    paths = []
    for tag, L in (("T2", A), ("R1", B)):
        path = os.path.join(PROBE_DIR, "Xlang%s.lean" % tag)
        open(path, "w").write("\n".join(L) + "\n")
        paths.append(path)
    return paths


# ============================================================================================ running Lean
def descendants(pid):
    kids = {}
    for p in os.listdir("/proc"):
        if p.isdigit():
            try:
                kids.setdefault(int(open("/proc/%s/stat" % p).read().rsplit(")", 1)[1].split()[1]), []).append(int(p))
            except (OSError, IndexError, ValueError):
                pass
    out, todo = [], [pid]
    while todo:
        q = todo.pop()
        for c in kids.get(q, []):
            out.append(c)
            todo.append(c)
    return out


def run_lean(path):
    proc = subprocess.Popen(["nice", "-n", "5", "lake", "env", "lean", path], cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    peak, t0 = 0, time.time()
    import threading
    buf = []
    th = threading.Thread(target=lambda: buf.append(proc.stdout.read()))
    th.start()
    while proc.poll() is None:
        for c in descendants(proc.pid):
            try:
                st = open("/proc/%d/status" % c).read()
                if "\nName:\tlean\n" not in "\n" + st:
                    continue
                rss = int(st.split("VmRSS:")[1].split()[0])
            except (OSError, IndexError, ValueError):
                continue
            peak = max(peak, rss)
            if rss > RSS_LIMIT_KB:
                os.kill(c, 9)
                raise SystemExit("lean above %d kB: killed (a design signal: split the probe)" % RSS_LIMIT_KB)
        time.sleep(0.5)
    th.join()
    return proc.returncode, buf[0] if buf else "", peak, time.time() - t0


def parse_lean(out):
    cases, full, vals = {}, {}, {}
    for line in out.splitlines():
        if line.startswith("CASE ") or line.startswith("FULL "):
            parts = line.split()
            d = {k: v == "true" for k, v in (p.split("=", 1) for p in parts[2:])}
            (cases if line.startswith("CASE ") else full)[parts[1]] = d
        elif line.startswith("VAL "):
            _, case, key, val = line.split(" ", 3)
            vals["%s %s" % (case, key)] = val.replace(" ", "")
    return cases, full, vals


# ============================================================================================ main
def main():
    args = sys.argv[1:]
    cs = cases()
    mirror = {}
    for name, data in cs:
        res = HM.check(data, margins=False)
        mirror[name] = dict(groups=mirror_groups(res), ok=res["ok"], fails=["%s/%s" % f for f in res["fails"]])
    mvals = {}
    for name, data in cs[:2]:
        mvals.update(mirror_values(name, data))
    mvals.update({"- " + k: v for k, v in synthetic_values().items()})
    if "--lean" in args:
        out, runs = "", []
        for path in write_probes(cs):
            rc, o, peak, wall = run_lean(path)
            if rc != 0:
                print(o[-4000:])
                raise SystemExit("lean probe %s failed (exit %d)" % (os.path.basename(path), rc))
            out += o
            runs.append(dict(probe=os.path.basename(path), peak_rss_kb=peak, wall_s=round(wall, 1)))
            print("lean probe %s: %.1f s, peak RSS %.2f GB" % (os.path.basename(path), wall, peak / 1e6))
        lcases, lfull, lvals = parse_lean(out)
        rec = dict(cases=lcases, full=lfull, values=lvals, runs=runs)
        print("lean: %d cases, %d values" % (len(lcases), len(lvals)))
        if "--record" in args:
            json.dump(rec, open(RECORD, "w"), indent=1, sort_keys=True)
            print("recorded %s" % os.path.relpath(RECORD, ROOT))
    else:
        rec = json.load(open(RECORD))
        lcases, lfull, lvals = rec["cases"], rec["full"], rec["values"]
        print("recorded Lean results: %s" % os.path.relpath(RECORD, ROOT))
    bad = 0
    for name, _ in cs:
        lc, mg = lcases.get(name), mirror[name]["groups"]
        if lc is None:
            print("  MISSING lean result for %s" % name)
            bad += 1
            continue
        diff = [g for g in GROUPS if lc[g] != mg[g]]
        lean_all = all(lc[g] for g in GROUPS)
        tag = "agree" if not diff else "DISAGREE " + ",".join(diff)
        extra = ""
        if name in lfull:
            f = lfull[name]
            ok_full = f["check"] == (mirror[name]["ok"] and f["omega"] and f["comp"] and f["sites"])
            extra = "; full checkHybrid %s (omega %s, comp %s, sites %s)%s" % (
                f["check"], f["omega"], f["comp"], f["sites"], "" if ok_full else " DISAGREES")
            bad += not ok_full
        bad += bool(diff)
        print("  %-22s mirror %-6s lean %-6s %s%s%s" % (name, "accept" if mirror[name]["ok"] else "reject",
                                                       "accept" if lean_all else "reject", tag, extra,
                                                       "" if mirror[name]["ok"] else "  [" + "; ".join(
                                                           mirror[name]["fails"][:3]) + "]"))
    vbad = [k for k in mvals if lvals.get(k) != mvals[k]]
    for k in vbad[:10]:
        print("  VALUE MISMATCH %s: mirror %s... lean %s..." % (k, mvals[k][:80], str(lvals.get(k))[:80]))
    print("values: %d compared, %d mismatches (accepted files: transfer numbers, step bounds, ratExpUp to 10^-60; "
          "synthetic fixtures)" % (len(mvals), len(vbad)))
    print("aud.tA (AUDIT-C8C-1 counterexample; Lean's value 503/100000): mirror %s" % mvals["- aud.tA"])
    bad += len(vbad)
    print("XLANG %s (%d cases)" % ("PASS" if bad == 0 else "FAIL (%d)" % bad, len(cs)))
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()

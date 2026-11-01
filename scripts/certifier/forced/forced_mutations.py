#!/usr/bin/env python3
"""V2-TOOLS #6: the mutation suite of a forced toy (rejections that must hold).  Untrusted tooling.

    python3 -I scripts/certifier/forced/forced_mutations.py TAG

Every mutation changes one input of the passing certificate or witness and names the one check that must reject
it.  The check runs alone in the kernel (`... = false := by decide +kernel`, through the memoized stages where the
landed check would recompute them), and, where the mirror covers it, the Python mirror must reject it too: the
verdicts are written to scripts/certifier/fixtures/forced-toy/<TAG>_mutations.json.  Families (V2-TOOLS brief):
  coefficients    a forcing amplitude, a Fourier coefficient of the torus, of the character witness;
  residual claims err, the energy level E0;
  frame bounds    bL, bN (and bNt), bT below the measured rows; the Hamiltonian claim dx;
  ray room        nuRay above (s - 1)|ω*|; disp above the room (σω - s)|ω*|;
  schedules       θ = 1 in route A; a = 1 in route B; X* ten times the passing value;
  denominator separation   a frequency box reaching a resonance fiber (small divisors); a site bound below
                  balBound; a Hamiltonian denominator whose ball contains 0 (with its separated control);
  square-root domains      a square-root operand whose ball reaches Re <= 0 (with its separated control);
  advice          a missing product key (full and low stage);
  conventions     angle degree 0 for u = 2πU; the ray scalar s; the time scale of H; swapped actions.
"""
import copy
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.setrecursionlimit(100000)

import sofx_check as C               # noqa: E402
import sofx_model as M               # noqa: E402
import sodata3_v2checks as V2C       # noqa: E402
import v2_q as V                     # noqa: E402
import forced_cert as FC             # noqa: E402
import forced_emit as FE             # noqa: E402
import forced_model as FM            # noqa: E402
import forced_witness as FW          # noqa: E402
import forced_lean as FL             # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
LEAN_DIR = os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced")
MOD = "KAM.CertificateSharp.V2.Tests.Forced."


def q(x):
    return FM.lean_q(F(x))


# ---------------------------------------------------------------------------------------------- mirror runs
def mirror_check(c, name):
    info = {}
    ok = dict(C.SUBCHECKS)[name](c.B, c, info)
    return ok, info


def safe(f, *a):
    """a mirror verdict; Python's division by zero (Lean totalizes x / 0 = 0 and its wf test rejects) is a
    rejection, recorded as such."""
    try:
        return f(*a)
    except ZeroDivisionError:
        return False


def with_ham(c, modes=None, scale=None):
    d = copy.deepcopy(c)
    if modes is not None:
        d.toy = FM.Toy(N=c.toy.N, c=c.toy.c, beta=c.toy.beta, s=c.toy.s, modes=modes, name=c.toy.name)
    if scale is not None:
        d.toy = FM.Toy(N=c.toy.N, c=c.toy.c * scale, beta=c.toy.beta, s=c.toy.s, modes=c.toy.modes, name=c.toy.name)
    d.jet = FC.jet_of(d.toy)
    d.jetOps = d.jet["prog"]
    d.jetOps_toy = FC.toy_ops(d.jetOps)
    return d


def bump(terms, rel):
    """the polynomial with its largest coefficient multiplied by 1 + rel (mantissas)."""
    i = max(range(len(terms)), key=lambda j: abs(terms[j][1][0]) + abs(terms[j][1][1]))
    k, (re, im) = terms[i]
    out = list(terms)
    out[i] = (k, (re + int(re * rel), im + int(im * rel)))
    return out, i


# ---------------------------------------------------------------------------------------------- catalogue
def catalogue(tag, c, W, WB):
    """list of dicts: name, family, doc, lean (the false Bool), defs (Lean text), heavy, mirror (verdict|None)."""
    B = c.B
    p = c.params
    out = []

    def add(name, family, doc, lean, defs="", heavy=False, mirror=None):
        out.append(dict(name=name, family=family, doc=doc, lean=lean, defs=defs, heavy=heavy, mirror=mirror))

    # -- coefficients
    (k0, e0) = c.toy.modes[0]
    modes = [(k0, e0 * F(1001, 1000))] + c.toy.modes[1:]
    d = with_ham(c, modes=modes)
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_hamCoef", "coefficients", "the amplitude of the mode `%s` times `1 + 10⁻³`" % (list(k0),),
        "checkInvariance { cert with ham := hamCoef }",
        "/-- `ham` with the amplitude of `%s` times `1 + 10⁻³`. -/\ndef hamCoef : HamExpr 2 :=\n%s\n" % (
            list(k0), FE.wrap("  ", FE.FM.ham_lean(d.toy.ham()).split(" "), indent="    ", sep="", close="")),
        heavy=True, mirror=dict(ok=ok, rows=[float(x) for x in info.get("rows", [])]))
    uh, i = bump(c.emb.angle[0].half, F(1, 10 ** 4))
    d = copy.deepcopy(c)
    d.emb.angle[0] = M.RealPoly(c.emb.angle[0].zero, uh)
    d.DKc = C.dkCache(B, 2, d.emb, d.weight, d.piEnc)
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_torusCoef", "coefficients", "the largest Fourier coefficient of `u` times `1 + 10⁻⁴`",
        "checkInvariance { cert with emb := ⟨[-1, 0], [⟨⟨0⟩, uHalfMut⟩, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩ }",
        FE.poly_def("uHalfMut", uh, "`uHalf` with its largest coefficient times `1 + 10⁻⁴`"), heavy=True,
        mirror=dict(ok=ok, rows=[float(x) for x in info.get("rows", [])]))
    (ck, (Et, ph, po)) = c.wit.charWit[0]
    Em, i = bump(Et, F(1, 10 ** 3))
    d = copy.deepcopy(c)
    d.wit = M.Witnesses([], [], [(ck, (Em, ph, po))] + c.wit.charWit[1:])
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_witnessCoef", "coefficients", "the largest coefficient of the character witness times `1 + 10⁻³`",
        "checkInvariance { cert with wit := ⟨[], [], [([%d, 0], ⟨⟨E%dTermsMut⟩, %d, %d⟩)], []⟩ }" % (
            ck[0], ck[0], ph, po),
        FE.poly_def("E%dTermsMut" % ck[0], Em, "the witness with its largest coefficient times `1 + 10⁻³`"),
        heavy=True, mirror=dict(ok=ok, rows=[float(x) for x in info.get("rows", [])]))
    # -- residual claims
    d = copy.deepcopy(c)
    d.params = dict(p, err=p["err"] / 2)
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_err", "residual claims", "the residual claim `err` halved",
        "checkInvariance { cert with params := { cert.params with err := cert.params.err / 2 } }", heavy=True,
        mirror=dict(ok=ok, margin=float(info.get("margin", 0))))
    d = copy.deepcopy(c)
    d.params = dict(p, E0=p["E0"] + 2 * p["err"])
    ok, info = mirror_check(d, "checkEnergy")
    add("mut_E0", "residual claims", "the energy level `E0` moved by `2 err`",
        "checkEnergy { cert with params := { cert.params with E0 := cert.params.E0 + 2 * cert.params.err } }",
        heavy=True, mirror=dict(ok=ok))
    # -- frame bounds (mirror: the frame rows)
    R = W["R"]
    fv = W["claim_values"]["frame"]
    for nm, key, lean in (("mut_frameL", "bL", "checkFrameL cert (Rclaim.bL * 99 / 100)"),
                          ("mut_frameT", "bT", "checkFrameT cert (Rclaim.bT * 99 / 100)")):
        fam = {"bL": "L", "bT": "T"}[key]
        add(nm, "frame bounds", "the frame bound `%s` times `0.99`" % key, lean,
            mirror=dict(ok=max(F(x) for x in fv[fam]) <= R[key] * F(99, 100)))
    add("mut_frameN", "frame bounds", "the frame bound `bN` times `0.99`",
        "checkFrameN cert (Rclaim.bN * 99 / 100) Rclaim.bNt",
        mirror=dict(ok=max(F(x) for x in fv["N"]) <= R["bN"] * F(99, 100)))
    hv = W["claim_values"]["ham"]
    add("mut_hamClaim", "frame bounds", "the Hamiltonian claim `dx` times `0.99`",
        "checkHamClaim cert { Rclaim with dx := Rclaim.dx * 99 / 100 }",
        mirror=dict(ok=F(hv["dx"]) <= R["dx"] * F(99, 100)))
    # -- ray room
    d = copy.deepcopy(c)
    d.params = dict(p, nu=F(1, 10 ** 5))
    ok, info = mirror_check(d, "checkStatic")
    add("mut_nuRay", "ray room", "`nuRay = 10⁻⁵`, above `(s - 1)|ω*| ≈ 10⁻⁶`",
        "checkStatic { cert with params := { cert.params with nuRay := 1 / 10 ^ 5 } }", mirror=dict(ok=ok))
    w = dict(W["core"], R=R)
    add("mut_dispRoom", "ray room", "`disp = 1`, above the room `(σω - s)|ω*|` of the ray",
        "finalOkA (refinedWit.num 2 { cert.params with disp := 1 } cert.freqBox) { cert.params with disp := 1 } "
        "cert.freqBox refinedWit.core.Xs",
        mirror=dict(ok=safe(V.refinedCore, 2, dict(p, disp=F(1)), c.freqBox, w)))
    # -- schedules
    add("mut_theta", "schedules", "route A with `θ = 1`",
        "refinedCore 2 cert.params cert.freqBox { refinedWit with core := { refinedWit.core with th := 1 } }",
        mirror=dict(ok=safe(V.refinedCore, 2, p, c.freqBox, dict(w, th=F(1))), note="mirror: 1 - θ = 0"))
    add("mut_Xs", "schedules", "route A with ten times the passing `X⋆`",
        "refinedCore 2 cert.params cert.freqBox { refinedWit with core := { refinedWit.core with Xs := "
        "refinedWit.core.Xs * 10 } }",
        mirror=dict(ok=safe(V.refinedCore, 2, p, c.freqBox, dict(w, Xs=w["Xs"] * 10))))
    if WB is not None:
        add("mut_scheduleB", "schedules", "route B with the schedule ratio `a = 1`",
            "refinedBCore 2 cert.params cert.freqBox { refinedBWit with core := { refinedBWit.core with a := 1 } }")
    # -- denominator separation
    add("mut_boxFiber", "denominator separation",
        "the frequency box widened to radius `1/20`: the fibers reach the resonance, the sites fail",
        "sitesOk (refinedWit.num 2 cert.params boxWide) refinedWit.core.J boxWide refinedWit.κ cert.params.γ "
        "refinedWit.sites",
        "/-- The box with radius `1/20` in coordinate 0. -/\ndef boxWide : FreqBox :=\n"
        "  [((cert.freqBox.getD 0 (0, 0)).1, 1 / 20), cert.freqBox.getD 1 (0, 0)]\n")
    s0 = W["sites"][0][0]
    add("mut_siteBound", "denominator separation", "the first site with its bound `B` halved",
        "siteOk 2 1 refinedWit.core.J cert.freqBox refinedWit.κ cert.params.γ "
        "((refinedWit.num 2 cert.params cert.freqBox).δ 0) (refinedWit.core.c.getD 0 0) "
        "(some ⟨%s, %d, %d, %s⟩)" % (q(s0["E1"]), s0["l"], s0["J"], q(F(s0["B"]) / 2)))
    pc = c.centre[0]
    add("mut_denominator", "denominator separation",
        "a term `10⁻⁹ / (p - p_c)` whose denominator ball contains `0` on the domain",
        "checkHamBounds { cert with ham := .add ham (.div (.const (1 / 10 ^ 9)) "
        "(.add (.action 0) (.const %s))) }" % q(-pc))
    # -- square-root domains
    add("mut_sqrtDomain", "square-root domains",
        "a term `10⁻⁹ √(p - p_c)` whose operand reaches `Re ≤ 0` on the domain",
        "checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9)) "
        "(.sqrt (.add (.action 0) (.const %s)))) }" % q(-pc))
    # -- advice
    d = copy.deepcopy(c)
    d.cfgFull = M.Cfg("cfgFull", c.cfgFull.cutoff, c.cfgFull.taylorN, c.cfgFull.halvings, c.books["cfgFull"][1:],
                      FC.DirectEngine())
    ok, info = mirror_check(d, "checkEnergy")
    add("mut_adviceFull", "advice",
        "the first full-stage advice key removed: the crude enclosure of `p²` breaks the energy row",
        "checkEnergy { cert with cfgFull := { cert.cfgFull with advice := cert.cfgFull.advice.tail } }",
        heavy=True, mirror=dict(ok=ok))
    d = copy.deepcopy(c)
    d.cfgLow = M.Cfg("cfgLow", c.cfgLow.cutoff, c.cfgLow.taylorN, c.cfgLow.halvings, c.books["cfgLow"][1:],
                     FC.DirectEngine())
    ok, info = mirror_check(d, "checkGram")
    add("mut_adviceLow", "advice", "the first low-stage advice key removed (crude Gram entry)",
        "checkGram { cert with cfgLow := { cert.cfgLow with advice := cert.cfgLow.advice.tail } }", heavy=True,
        mirror=dict(ok=ok))
    # -- conventions
    d = copy.deepcopy(c)
    d.emb.angleDeg = [0, 0]
    d.DKc = C.dkCache(B, 2, d.emb, d.weight, d.piEnc)
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_angleDeg", "conventions", "`u = 2πU` read at angle degree `0` (as `U`)",
        "checkInvariance { cert with emb := ⟨[0, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩ }", heavy=True,
        mirror=dict(ok=ok))
    d = copy.deepcopy(c)
    d.params = dict(p, s=F(1001, 1000))
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_rayScalar", "conventions", "the ray scalar `s = 1 + 10⁻³` against the box of `c / s`",
        "checkInvariance { cert with params := { cert.params with s := 1001 / 1000 } }", heavy=True,
        mirror=dict(ok=ok))
    d = with_ham(c, scale=F(2))
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_timeScale", "conventions", "the Hamiltonian doubled without rescaling the box",
        "checkInvariance { cert with ham := .mul (.const 2) ham }", heavy=True, mirror=dict(ok=ok))
    d = copy.deepcopy(c)
    d.emb.action = [c.emb.action[1], c.emb.action[0]]
    d.DKc = C.dkCache(B, 2, d.emb, d.weight, d.piEnc)
    ok, info = mirror_check(d, "checkInvariance")
    add("mut_swapActions", "conventions", "the actions `(p, J)` emitted in the order `(J, p)`",
        "checkInvariance { cert with emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [J, p]⟩ }", heavy=True,
        mirror=dict(ok=ok))
    return out


CONTROLS = [
    ("ctl_denominator", "the same term with the separated denominator `p + 1` passes",
     "checkHamBounds { cert with ham := .add ham (.div (.const (1 / 10 ^ 9)) (.add (.action 0) (.const 1))) }"),
    ("ctl_sqrtDomain", "the same term with the operand `p + 1` passes",
     "checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9)) (.sqrt (.add (.action 0) "
     "(.const 1)))) }"),
]


def module(tag, muts, heavy, controls):
    T = tag
    imports = ["%s%sRouteA" % (MOD, T)]
    if any("refinedBWit" in m["lean"] for m in muts):
        imports.append("%s%sRouteB" % (MOD, T))
    kind = "composition" if heavy else "claims, cores, sites, ball pass"
    lines = [FE.HEADER] + ["public import %s\n" % i for i in imports]
    lines.append("""
/-!
# Mutations of the forced toy `%s` that must be rejected (%s)

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it, alone in the kernel. The families and the producer's mirror verdicts
are listed in `scripts/certifier/forced/forced_mutations.py` and
`scripts/certifier/fixtures/forced-toy/%s_mutations.json`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%s

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

""" % (T, kind, T, T))
    for m in muts:
        if m["defs"]:
            lines.append(m["defs"] + "\n")
        body = "theorem %s : %s = false := by\n  decide +kernel\n" % (m["name"], m["lean"])
        if m["name"] == "mut_frameN":
            body = ("theorem mut_frameN : %s = false := by\n  rw [checkFrameN_eq_of gram_eq eps_eq "
                    "(frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps\n    cert.weight cert.cfgLow cert.piEnc "
                    "L_eq Gi_eq N0_eq)]\n  decide +kernel\n") % m["lean"]
        if m["name"] == "mut_frameT":
            body = ("theorem mut_frameT : %s = false := by\n  rw [checkFrameT_eq_of gram_eq T_eq]\n"
                    "  decide +kernel\n") % m["lean"]
        lines.append(wrap_doc("/-- Rejected: %s (%s). -/" % (m["doc"], m["family"])) + "\n" + wrap_thm(body) + "\n")
    for nm, doc, lean in controls:
        lines.append(wrap_doc("/-- Control: %s. -/" % doc) + "\n" + wrap_thm("theorem %s : %s = true := by\n  decide +kernel\n"
                                                             % (nm, lean)) + "\n")
    lines.append("end KAM.CertificateSharp.V2.Forced.%s\n\nend\n" % T)
    text = "".join(lines)
    for ln in text.split("\n"):
        assert len(ln) <= 100, ln
    return text


def wrap_doc(text):
    """a docstring wrapped at spaces to 100 columns."""
    words, lines, cur = text.split(" "), [], ""
    for w in words:
        if cur and len(cur) + 1 + len(w) > 100:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + " " + w) if cur else w
    lines.append(cur)
    return "\n".join(lines)


def wrap_thm(body):
    """break the statement line of a theorem at spaces to fit 100 columns (continuation indent 4)."""
    out = []
    for ln in body.split("\n"):
        while len(ln) > 100:
            cut = ln.rfind(" ", 0, 100)
            while ln[:cut].count("(") - ln[:cut].count(")") < 0 or cut <= 4:
                cut = ln.rfind(" ", 0, cut)
            out.append(ln[:cut])
            ln = "    " + ln[cut + 1:]
        out.append(ln)
    return "\n".join(out)


def main(tag):
    c = FW.load(tag)
    Wj = json.load(open(os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy", "%s_witness.json" % tag)))
    WA = Wj["refinedA"]
    W = dict(core={k: (F(v) if isinstance(v, str) and k not in () else v) for k, v in WA["core"].items()},
             R={k: F(v) for k, v in WA["R"].items()}, claim_values=Wj["claim_values"], sites=WA["sites"])
    W["core"]["c"] = [F(x) for x in WA["core"]["c"]]
    W["core"]["cbar"] = [F(x) for x in WA["core"]["cbar"]]
    W["core"]["kp"] = int(WA["core"]["kp"])
    W["core"]["J"] = int(WA["core"]["J"])
    muts = catalogue(tag, c, W, Wj.get("refinedB"))
    for m in muts:
        if m["mirror"] is not None:
            assert not m["mirror"]["ok"], (m["name"], m["mirror"])
    heavy = [m for m in muts if m["heavy"]]
    light = [m for m in muts if not m["heavy"]]
    with open(os.path.join(LEAN_DIR, "%sMutationsInv.lean" % tag), "w") as fh:
        fh.write(module(tag, heavy, True, []))
    with open(os.path.join(LEAN_DIR, "%sMutations.lean" % tag), "w") as fh:
        fh.write(module(tag, light, False, CONTROLS))
    rep = [dict(name=m["name"], family=m["family"], doc=m["doc"], check=m["lean"], mirror=m["mirror"],
                module="%sMutations%s" % (tag, "Inv" if m["heavy"] else "")) for m in muts]
    with open(os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy", "%s_mutations.json" % tag), "w") as fh:
        json.dump(rep, fh, indent=1, default=str)
    print(len(muts), "mutations;", sum(1 for m in muts if m["mirror"] is not None), "with a mirror verdict (all false)")


if __name__ == "__main__":
    main(sys.argv[1])

#!/usr/bin/env python3
"""V2-TOOLS #6: the forced toy's `TorusCertificate 2 (CertFixed P)`, built and checked with the backend-generic
mirror of the landed checker (scripts/spin_orbit/sofx_*.py).  Untrusted producer tooling: the kernel decides.

    python3 -I scripts/certifier/forced/forced_cert.py [--json OUT]

`generate(spec)` runs the producer for one spec (dict, see DEFAULT_SPEC):
  1. the candidate torus (forced_model.solve_torus) on a box support, pruned by weighted size on the strip;
  2. the embedding (angleDeg -1 for u = 2 pi U, actions p and J at degree 0), the character witnesses
     E_k0 = exp(i k0 u) under the normalized keys (k0, 0), the domain (rho_H, centre, radius) from the embedding's
     sup bounds, M from the ball pass, sigma_K from DK, a constant Gram inverse and sigma_B, the torsion inverse S
     and sigma_T, err from the invariance and energy rows (each rounded up with a stated relative slack);
  3. GENERATE (every genuine product key is recorded with advice `direct`), then CHECK from scratch with exactly
     the recorded books; the report lists every sub-check's verdict and margin.
The v2 witnesses are chosen afterwards (forced_witness.py) from this certificate's numbers.
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
SO = os.path.join(HERE, "..", "..", "spin_orbit")
sys.path.insert(0, HERE)
sys.path.insert(1, SO)
sys.set_int_max_str_digits(0)

import numpy as np                                   # noqa: E402

import sofx_arith as A                               # noqa: E402
import sofx_model as M                               # noqa: E402
import sofx_check as C                               # noqa: E402
import adv_jet                                       # noqa: E402
import forced_model as FM                            # noqa: E402

DEFAULT_SPEC = dict(
    name="forced", N=8, c="1", beta="1", s="1000001/1000000",
    modes=[[[1, 0], "1/10000"], [[1, 1], "1/5000"], [[2, -1], "1/10000"]],
    P=96, L0=10, L1=5, rho="1/8", rhoInf="1/800", mu="1/100", nuRay="1/10000000", som="2",
    prune_digits=16, R=140, gramTol="1/10000000", expHalvings=8, expOrder=30, pinOrder=30, cutLow=40, cutFull=1000000,
    err_slack="11/10", disp="1/1000", room="1/100", sqrt5_digits=40, machin=(24, 8))


def up_sig(x, sig=3):
    """the least rational >= x > 0 with `sig` significant decimal digits."""
    x = F(x)
    if x <= 0:
        return F(0)
    e = math.floor(math.log10(float(x))) - (sig - 1)
    D = F(10) ** e
    return math.ceil(x / D) * D


def q_of(x):
    return F(x) if not isinstance(x, F) else x


class DirectEngine:
    """GENERATE engine: every genuine product gets advice `direct` (the Lean fallback for a missing key is the
    crude enclosure, so each key must be emitted)."""
    last_info = None

    def generate(self, B, W, root, fk, a, b):
        return ("direct",)

    def mulPacked(self, B, W, adv, a, b):
        raise RuntimeError("no packed advice in the forced toy")


def make_cfgs(spec, books=None):
    eng = DirectEngine()
    bf = None if books is None else books["cfgFull"]
    bl = None if books is None else books["cfgLow"]
    return (M.Cfg("cfgFull", spec["cutFull"], spec["expOrder"], spec["expHalvings"], bf, eng),
            M.Cfg("cfgLow", spec["cutLow"], spec["expOrder"], spec["expHalvings"], bl, eng))


def toy_of(spec):
    return FM.Toy(N=spec["N"], c=F(spec["c"]), beta=F(spec["beta"]), s=F(spec["s"]),
                  modes=[(tuple(k), F(e)) for k, e in spec["modes"]], name=spec["name"])


def jet_of(toy):
    J = adv_jet.jet(2, toy.ham())
    J["prog"] = [tuple(op) if op[0] != "char" else ("char", tuple(op[1])) for op in J["prog"]]
    return J


def toy_ops(prog):
    out = []
    for op in prog:
        t = op[0]
        if t == "const":
            out.append(("C", op[1], op[2], op[3]))
        elif t == "action":
            out.append(("A", op[1]))
        elif t == "char":
            out.append(("X", list(op[1])))
        elif t == "add":
            out.append(("+", op[1], op[2]))
        elif t == "mul":
            out.append(("*", op[1], op[2]))
        else:
            raise ValueError(op)
    return out


def mant(B, q):
    """nearest mantissa of an exact rational."""
    q = F(q)
    return round(q * B.D)


def realpoly(B, S):
    z, half = FM.half_poly(S)
    return M.RealPoly(mant(B, z), [(k, (mant(B, v[0]), mant(B, v[1]))) for k, v in half
                                   if mant(B, v[0]) != 0 or mant(B, v[1]) != 0])


def series_poly(B, S):
    """a CertPoly (ascending keys) of a series."""
    out = []
    for k in sorted(S):
        v = S[k]
        re, im = mant(B, v[0]), mant(B, v[1])
        if re or im:
            out.append((k, (re, im)))
    return out


def weight_for(rho, s, N, digits=12):
    x = M.ratExpUp(2 * A.PI_UP * F(rho), s, N)
    D = 10 ** digits
    return F(-((-x.numerator * D) // x.denominator), D)


def pi_enclosure(B, k, j):
    lo, up = A.piLowRat(k, j), A.piUpRat(k, j)
    centre = B.ofRatDown((lo + up) / 2)
    rad = B.upAdd(B.ofRatUp((up - lo) / 2), 4)
    return A.PiEnclosure(centre, rad, k, j)


def char_keys(jet):
    ks = set()
    for op in jet["prog"]:
        if op[0] == "char":
            k0 = op[1][0] if len(op[1]) > 0 else 0
            ks.add(k0)
    return ks


# ---------------------------------------------------------------------------------------------- the build
class Built:
    pass


def solve(spec, toy):
    box, root = FM.freq_box(toy, spec["sqrt5_digits"])
    w0 = box[0][0] / toy.kappa
    rho = F(spec["rho"])
    wv = math.exp(2 * math.pi * float(rho))
    tol = 10.0 ** (-spec["prune_digits"])
    prune = lambda m, a: float(a) * wv ** (abs(m[0]) + abs(m[1])) < tol
    T = FM.solve_torus(toy, w0, spec["L0"], spec["L1"], R=spec["R"], tol=F(1, 10 ** (spec["prune_digits"] + 4)),
                       prune=prune)
    return box, root, T


def assemble(spec, toy, box, T, params, cfgs, centre, radius, rhoH, gramInv, torsInv):
    B = A.FixedB(spec["P"])
    c = C.Cert()
    c.B, c.n, c.which = B, 2, spec["name"]
    c.params = params
    c.jet = jet_of(toy)
    c.jetOps = c.jet["prog"]
    c.jetOps_toy = toy_ops(c.jetOps)
    c.expHalvings, c.expOrder = spec["expHalvings"], spec["expOrder"]
    c.weightH = M.Weight(rhoH, weight_for(rhoH, c.expHalvings, c.expOrder))
    c.weight = M.Weight(params["rho"], weight_for(params["rho"], c.expHalvings, c.expOrder))
    c.centre, c.radius = list(centre), list(radius)
    c.freqBox = box
    c.emb = M.Embedding([-1, 0], [realpoly(B, T.u), M.RealPoly(0, [])], [0, 0], [realpoly(B, T.p), realpoly(B, T.J)])
    keep = lambda m: abs(m[0]) <= spec["L0"] + 6 and abs(m[1]) <= spec["L1"] + 3
    rho = float(params["rho"])
    wv = math.exp(2 * math.pi * rho)
    tol = 10.0 ** (-spec["prune_digits"] - spec.get("char_extra_digits", 4))
    if spec.get("char_tol"):
        tol = float(F(spec["char_tol"]))            # E keeps the terms of weighted size >= char_tol
    cw = []
    for k0 in sorted(char_keys(c.jet)):
        if k0 <= 0:
            continue
        pr = (lambda m, a: float(a) * wv ** (abs(m[0]) + abs(m[1])) < tol * 1e-3)
        E = FM.sexp_i(T.u, k0, keep, spec["R"], F(1, 10 ** (spec["prune_digits"] + 10)), pr)
        E = {m: v for m, v in E.items() if float(abs(v[0]) + abs(v[1])) * wv ** (abs(m[0]) + abs(m[1])) >= tol}
        cw.append(((k0, 0), (series_poly(B, E), 0, spec["pinOrder"])))
    c.wit = M.Witnesses([], [], cw)
    c.gramInv = gramInv
    c.piEnc = pi_enclosure(B, *spec["machin"])
    c.cfgFull, c.cfgLow = cfgs
    c.torsInv = torsInv
    c.DKc = C.dkCache(B, 2, c.emb, c.weight, c.piEnc)
    c.toy, c.torus, c.spec = toy, T, spec
    return c


def base_params(spec, toy, M_=F(100), sK=F(100), sB=F(100), sT=F(100), err=F(1), disp=None):
    return dict(tau=1, rho=F(spec["rho"]), rhoInf=F(spec["rhoInf"]), M=M_, sK=sK, sB=sB, sT=sT, mu=F(spec["mu"]),
                gbar=toy.gamma, som=F(spec["som"]), nu=F(spec["nuRay"]), gamma=toy.gamma, s=toy.s, err=err,
                E0=F(0), disp=F(spec["disp"]) if disp is None else disp)


def gram_const_inverse(c):
    """B = the inverse of the average of G = DK^T DK (a constant approximate inverse), rounded at 2^-40."""
    B = c.B
    DKm = C.dkModels(B, 2, c.DKc)
    G = np.zeros((2, 2))
    for a in range(2):
        for b in range(2):
            s = 0.0
            for r in range(4):
                ma, mb = C.entry(DKm, r, a, B), C.entry(DKm, r, b, B)
                da = {tuple(k): complex(float(B.val(v[0])), float(B.val(v[1]))) for k, v in ma.poly}
                db = {tuple(k): complex(float(B.val(v[0])), float(B.val(v[1]))) for k, v in mb.poly}
                fa = (2 * math.pi) ** ma.deg
                fb = (2 * math.pi) ** mb.deg
                for k, z in da.items():
                    w = db.get((-k[0], -k[1]) if len(k) == 2 else k)
                    if w is not None:
                        s += (fa * fb * z * w).real
            G[a, b] = s
    Gi = np.linalg.inv(G)
    sc = 2 ** 40
    out = []
    for i in range(2):
        row = []
        for j in range(2):
            x = F(round(Gi[i, j] * sc), sc)
            row.append([((0, 0), (B.ofRatDown(x), 0))] if x != 0 else [])
        out.append(row)
    return out, G


def gram_fourier_inverse(c, tolB, bits=48, N0=64, N1=32):
    """B(theta) ~ G(theta)^-1 on a real grid (G = DK^T DK from the torus series), Fourier coefficients kept when
    their weighted size on the strip is >= tolB, rounded at 2^-bits.  checkGram verifies whatever is sent."""
    Bk = c.B
    T = c.torus
    rho = float(c.params["rho"])
    wv = math.exp(2 * math.pi * rho)

    def grid(S, dj):
        """the series sum_m f(m) S_m e_m on the grid, f = 2 pi i m_j (dj = j) or 1 (dj = None)."""
        A_ = np.zeros((N0, N1), dtype=np.complex128)
        for m, v in S.items():
            z = complex(float(v[0]), float(v[1]))
            if dj is not None:
                z *= 2j * math.pi * m[dj]
            A_[m[0] % N0, m[1] % N1] += z
        return np.fft.ifft2(A_) * (N0 * N1)

    U = {m: (v[0] / (2 * F(math.pi)), v[1] / (2 * F(math.pi))) for m, v in T.u.items()}
    DK = np.zeros((4, 2, N0, N1))
    for j in range(2):
        DK[0, j] = (1.0 if j == 0 else 0.0) + grid(U, j).real
        DK[1, j] = 1.0 if j == 1 else 0.0
        DK[2, j] = grid(T.p, j).real
        DK[3, j] = grid(T.J, j).real
    G = np.einsum("raxy,rbxy->abxy", DK, DK)
    det = G[0, 0] * G[1, 1] - G[0, 1] * G[1, 0]
    Gi = np.array([[G[1, 1], -G[0, 1]], [-G[1, 0], G[0, 0]]]) / det
    sc = 2 ** bits
    out = []
    for i in range(2):
        row = []
        for j in range(2):
            Ch = np.fft.fft2(Gi[i, j]) / (N0 * N1)
            terms = []
            for a in range(N0):
                for b in range(N1):
                    m = (a if a <= N0 // 2 else a - N0, b if b <= N1 // 2 else b - N1)
                    z = Ch[a, b]
                    if abs(z) * wv ** (abs(m[0]) + abs(m[1])) < tolB:
                        continue
                    re, im = round(z.real * sc), round(z.imag * sc)
                    if re == 0 and im == 0:
                        continue
                    terms.append((m, (Bk.ofRatDown(F(re, sc)), Bk.ofRatDown(F(im, sc)))))
            terms.sort()
            row.append(terms)
        out.append(row)
    Gavg = [[float(np.mean(G[a, b])) for b in range(2)] for a in range(2)]
    return out, np.array(Gavg)


def torsion_witness(c, T):
    B = c.B
    k = 3
    Cm = np.zeros((k, k), dtype=np.complex128)
    for l in range(k):
        for j in range(k):
            z = C.zeroModeBall(B, 2, C.entry(T, l, j, B))[0]
            Cm[l, j] = complex(float(B.val(z[0])), float(B.val(z[1])))
    S = np.linalg.inv(Cm)
    sc = 2 ** 40
    rows = []
    for i in range(k):
        r = []
        for j in range(k):
            re = F(round(S[i, j].real * sc), sc)
            im = F(round(S[i, j].imag * sc), sc)
            r.append((B.ofRatDown(re), B.ofRatDown(im)))
        rows.append(r)
    return rows, Cm


def run(c, names):
    out = {}
    for name, f in C.SUBCHECKS:
        if name not in names:
            continue
        t = time.time()
        info = {}
        ok = f(c.B, c, info)
        out[name] = dict(ok=ok, seconds=round(time.time() - t, 2), info=info)
    return out


def books_of(cfg):
    seen, out = set(), []
    for k, adv in cfg.generated:
        if k not in seen:
            seen.add(k)
            out.append((k, adv))
    return out


def generate(spec=None, log=print):
    spec = dict(DEFAULT_SPEC, **(spec or {}))
    toy = toy_of(spec)
    t0 = time.time()
    box, root, T = solve(spec, toy)
    log("torus", T.info, "%.1fs" % (time.time() - t0))
    rho, mu = F(spec["rho"]), F(spec["mu"])
    room = F(spec["room"])
    # pass 1: the embedding's sup bounds fix the domain
    cfgs = make_cfgs(spec)
    p = base_params(spec, toy)
    c = assemble(spec, toy, box, T, p, cfgs, [T.p[(0, 0)][0], T.J[(0, 0)][0]], [F(1), F(1)], rho + F(1),
                 [[[((0, 0), (c_one(spec), 0))], []], [[], [((0, 0), (c_one(spec), 0))]]],
                 [[(0, 0)] * 3] * 3)
    r = run(c, ["checkEmbedding"])["checkEmbedding"]["info"]
    iota = max(min(a, b) for a, b in r["iota"])
    rhoH = up_sig(rho + iota + mu + room * rho, 3)
    centre = [FM.rnd(T.p[(0, 0)][0], 40), FM.rnd(T.J[(0, 0)][0], 40)]
    acts = [s for s, _ in r["action"]]
    # the action sups are measured from the provisional centre; re-measure after recentring below
    radius = [up_sig(a * F(11, 10) + mu + room * mu + F(1, 10 ** 6), 2) for a in acts]
    c = assemble(spec, toy, box, T, p, make_cfgs(spec), centre, radius, rhoH, c.gramInv, c.torsInv)
    r = run(c, ["checkEmbedding", "checkHamBounds"])
    e, h = r["checkEmbedding"]["info"], r["checkHamBounds"]["info"]
    radius = [up_sig(s * F(11, 10) + mu + F(1, 10 ** 6), 2) for s, _ in e["action"]]
    c = assemble(spec, toy, box, T, p, make_cfgs(spec), centre, radius, rhoH, c.gramInv, c.torsInv)
    h = run(c, ["checkHamBounds"])["checkHamBounds"]["info"]
    M_ = up_sig(max(h["bounds"]) * F(101, 100), 3)
    sK = up_sig(max(e["dkRows"]) * F(101, 100) + mu, 3)
    p = base_params(spec, toy, M_=M_, sK=sK)
    gi, G = (gram_fourier_inverse(c, F(spec["gramTol"])) if spec.get("gramTol") else gram_const_inverse(c))
    c = assemble(spec, toy, box, T, p, make_cfgs(spec), centre, radius, rhoH, gi, c.torsInv)
    g = run(c, ["checkGram"])["checkGram"]
    if not g["ok"]:
        raise RuntimeError("Gram check fails with the constant inverse: %r" % g["info"])
    gi_info = g["info"]
    d_, b_ = max(gi_info["dRows"]), max(gi_info["bRows"])
    sB = up_sig(b_ / (1 - d_) * F(101, 100) + mu, 3)
    p = base_params(spec, toy, M_=M_, sK=sK, sB=sB)
    c = assemble(spec, toy, box, T, p, make_cfgs(spec), centre, radius, rhoH, gi, c.torsInv)
    db = C.gramCheck(c.B, 2, c.emb, c.gramInv, c.weight, c.cfgLow, c.piEnc, p["sB"] - p["mu"], c.DKc)
    Tm = C.torsionModels(c.B, 2, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], c.weight, c.cfgLow,
                         c.piEnc, c.DKc)
    S, Cm = torsion_witness(c, Tm)
    c.torsInv = S
    ti = {}
    C.torsionAvgCheck(c.B, 2, Tm, S, F(10 ** 6), ti)
    sT = up_sig(ti["b"] / (1 - ti["deltaT"]) * F(101, 100) + mu, 3)
    p = base_params(spec, toy, M_=M_, sK=sK, sB=sB, sT=sT)
    c = assemble(spec, toy, box, T, p, make_cfgs(spec), centre, radius, rhoH, gi, S)
    r = run(c, ["checkInvariance", "checkEnergy"])
    rows = r["checkInvariance"]["info"].get("rows")
    if rows is None:
        raise RuntimeError("composition failed: %r" % r["checkInvariance"]["info"].get("compose"))
    en = r["checkEnergy"]["info"]["value"]
    err = up_sig(max(max(rows), en) * F(spec["err_slack"]), 3)
    p = base_params(spec, toy, M_=M_, sK=sK, sB=sB, sT=sT, err=err)
    # GENERATE then CHECK with the recorded books
    cf, cl = make_cfgs(spec)
    c = assemble(spec, toy, box, T, p, (cf, cl), centre, radius, rhoH, gi, S)
    run(c, [n for n, _ in C.SUBCHECKS])
    books = {"cfgFull": books_of(cf), "cfgLow": books_of(cl)}
    c2 = assemble(spec, toy, box, T, p, make_cfgs(spec, books), centre, radius, rhoH, gi, S)
    t1 = time.time()
    chk = run(c2, [n for n, _ in C.SUBCHECKS if n != "checkSmallness"])
    c2.books = books
    c2.root = root
    c2.report = dict(spec={k: (str(v) if isinstance(v, F) else v) for k, v in spec.items()},
                     toy=toy.describe(), torus=T.info, check_seconds=round(time.time() - t1, 1),
                     gram_avg=G.tolist(), torsion_centre=[[str(z) for z in r] for r in Cm],
                     checks={k: dict(ok=v["ok"], info=summ(v["info"])) for k, v in chk.items()},
                     params={k: str(v) for k, v in p.items()},
                     misses={nm: [list(x) if isinstance(x, tuple) else x for x in cfg.misses][:5]
                             for nm, cfg in (("cfgFull", c2.cfgFull), ("cfgLow", c2.cfgLow))},
                     sizes=sizes(c2))
    c2.report["passes_base"] = all(v["ok"] for v in chk.values())
    return c2


def c_one(spec):
    return 1 << spec["P"]


def sizes(c):
    e = c.emb
    return dict(angle0=len(e.angle[0].half), action0=len(e.action[0].half), action1=len(e.action[1].half),
                charWit=[len(E[0]) for _, E in c.wit.charWit], adviceFull=len(c.books["cfgFull"]) if hasattr(
                    c, "books") else None, adviceLow=len(c.books["cfgLow"]) if hasattr(c, "books") else None)


def summ(info):
    out = {}
    for k, v in info.items():
        if k in ("G", "compose", "T"):
            continue
        if isinstance(v, F):
            out[k] = float(v)
        elif isinstance(v, (list, tuple)):
            out[k] = [summ({"x": x})["x"] if not isinstance(x, (int, float, str, bool, type(None))) else x
                      for x in v]
        elif isinstance(v, dict):
            out[k] = summ(v)
        else:
            out[k] = v
    return out


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--spec", help="JSON overrides of DEFAULT_SPEC")
    a = ap.parse_args()
    sp = json.loads(a.spec) if a.spec else {}
    c = generate(sp)
    print(json.dumps(c.report, indent=1, default=str)[:6000])
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(c.report, fh, indent=1, default=str)

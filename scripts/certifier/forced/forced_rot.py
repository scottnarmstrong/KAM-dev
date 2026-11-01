#!/usr/bin/env python3
"""V2-CONSOL: the rotated-coordinate normalization `MicroRot` of the forced toy `Micro`.  Untrusted producer tooling.

    python3 -I scripts/certifier/forced/forced_rot.py [--work DIR] [--no-lean]

The linear symplectic unimodular change of variables of the lunar client (`soRotMap`, `KAM/SpinOrbit/Rotated.lean`;
generic form `KAM.CertificateSharp.Linear.shearMap`, `KAM/CertificateSharp/LinearShear.lean`)

    L ((Q0, Q1), (P0, P1)) = ((Q0 + Q1, Q1), (P0, P1 - P0)),    angle block S = [[1, 1], [0, 1]],

turns `Micro` (H, K, omega*) into the same physical torus in the rotated variables:
  * H' = H o L: the mode k becomes S^T k = (k0, k0 + k1), the action J becomes P1 - P0 (`hamShear`);
  * K' = L^-1 o K o S: K'(phi) = (phi + (U0(S phi), 0), p(S phi), p(S phi) + J(S phi)) (`embShear`): the angle and
    action data are Micro's mantissas at the keys S^T k, and the action P1 = p + J merges the two key-sorted lists
    (`addTerms`), so the data are exact transforms of Micro's emitted data (no rounding);
  * the character witness exp(i u') at the normalized key (1, 0) is Micro's, relabelled (exact, `shearTerms`);
  * omega' = S^-1 omega* = (w0 - w1, w1) with the exact box (`shearBox`: centre (c0 - c1, c1), radius (r0 + r1, r1)),
    and the Diophantine constant gamma/2 (`isDiophantine_shear`: |T k|_1 <= 2 |k|_1 for T k = (k0, k1 - k0)).
Everything else (domain, M, the sigmas, the Gram and torsion witnesses, err, the advice books, the stage memos and the
route witnesses) is computed afresh by the landed-checker mirror, exactly as forced_cert.generate does for Micro.

Writes KAM/CertificateSharp/V2/Tests/Forced/MicroRot{Data,Stages,ChecksA,ChecksB,Gram,Torsion1,Torsion2,Torsion3,Base,
Routes}.lean (Micro's layout: the per-theorem kernel times of MicroRot are 0.8x-1.4x Micro's under the same load),
scripts/certifier/fixtures/forced-toy/MicroRot.json (the mirror's report, every number, the witnesses and the drift
mutations' mirror verdicts) and a pickle in the work directory.  The transformation theorems
(`MicroRotFreq`, `MicroRotTransform`, `MicroRotLunar`) and the mutation module (`MicroRotMut`) are hand-written Lean.
"""
import argparse
import json
import os
import pickle
import re
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))
sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(0)

import sofx_arith as A              # noqa: E402
import sofx_model as M              # noqa: E402
import sofx_check as C              # noqa: E402
import forced_model as FM           # noqa: E402
import forced_cert as FC            # noqa: E402
import forced_emit as FE            # noqa: E402
import forced_stages as FS          # noqa: E402
import forced_build as FB           # noqa: E402

TAG, BASE = "MicroRot", "Micro"
LEAN_DIR = FB.LEAN_DIR
JSON_DIR = FB.JSON_DIR
MOD = FB.MOD


# ---------------------------------------------------------------------------------------------- the shear
def shear_key(k):
    """`shearKey`: k -> S^T k = (k0, k0 + k1)."""
    k = tuple(k)
    return (k[0], k[0] + k[1])


def key_lt2(a, b):
    """`keyLt2`: lexicographic order of 2-keys (only the output order of `insertAddTerm` depends on it)."""
    return a[0] < b[0] or (a[0] == b[0] and a[1] < b[1])


def insert_add(t, l):
    """`insertAddTerm t l`: add t into the key-sorted list l (mantissas add at an equal key)."""
    out = []
    for i, a in enumerate(l):
        if tuple(a[0]) == tuple(t[0]):
            return out + [(a[0], (a[1][0] + t[1][0], a[1][1] + t[1][1]))] + list(l[i + 1:])
        if key_lt2(t[0], a[0]):
            return out + [t] + list(l[i:])
        out.append(a)
    return out + [t]


def add_terms(l1, l2):
    """`addTerms l1 l2 = l2.foldl (fun acc t => insertAddTerm t acc) l1`."""
    acc = list(l1)
    for t in l2:
        acc = insert_add(t, acc)
    return acc


def shear_terms(l):
    return [(shear_key(k), v) for k, v in l]


def shear_ham(e):
    """`hamShear`: `.action 1 -> .add (.action 1) (.mul (.const (-1)) (.action 0))`, modes k -> S^T k."""
    t = e[0]
    if t == "action":
        return e if e[1] == 0 else ("add", ("action", e[1]), ("mul", ("const", F(-1)), ("action", 0)))
    if t in ("cosMode", "sinMode"):
        return (t, shear_key(e[1]))
    if t in ("add", "mul", "div"):
        return (t, shear_ham(e[1]), shear_ham(e[2]))
    if t == "pow":
        return (t, shear_ham(e[1]), e[2])
    if t in ("exp", "sin", "cos", "sqrt"):
        return (t, shear_ham(e[1]))
    return e


def shear_box(box):
    """`shearBox`: the exact box of (w0 - w1, w1)."""
    (c0, r0), (c1, r1) = box
    return [(c0 - c1, r0 + r1), (c1, r1)]


class RotToy(FM.Toy):
    """Micro's toy in the rotated variables: H' = H o L, omega' = S^-1 omega*, gamma' = gamma / 2."""

    @property
    def gamma(self):
        return FM.Toy.gamma.fget(self) / 2

    def ham(self):
        return shear_ham(FM.Toy.ham(self))

    def alg_coeffs(self):
        (a, b), (k,) = FM.Toy.alg_coeffs(self)
        return [[a - k, b], [k]]

    def describe(self):
        d = FM.Toy.describe(self)
        d.update(name=TAG, rotated_from=BASE, gamma=str(self.gamma),
                 map="L((Q0,Q1),(P0,P1)) = ((Q0+Q1,Q1),(P0,P1-P0)), omega' = (w0 - w1, w1)")
        return d


# ---------------------------------------------------------------------------------------------- Micro's data
def base_cert():
    with open(os.path.join(JSON_DIR, "%s.json" % BASE)) as fh:
        return json.load(fh)


def rp_of(d):
    return (int(d["zero"]), [(tuple(k), (int(v[0]), int(v[1]))) for k, v in d["half"]])


def rot_data(bj):
    """The rotated embedding, character witness and box, exactly from Micro's emitted certificate."""
    ce = bj["certificate"]
    e = ce["emb"]
    assert e["angleDeg"] == [-1, 0] and e["actionDeg"] == [0, 0], e
    (uz, uh), (az, ah) = rp_of(e["angle"][0]), rp_of(e["angle"][1])
    assert az == 0 and ah == [], "Micro's angle 1 is zero"
    (pz, ph), (Jz, Jh) = rp_of(e["action"][0]), rp_of(e["action"][1])
    u2, p2 = M.RealPoly(uz, shear_terms(uh)), M.RealPoly(pz, shear_terms(ph))
    P1 = M.RealPoly(pz + Jz, add_terms(shear_terms(ph), shear_terms(Jh)))
    emb = M.Embedding([-1, 0], [u2, M.RealPoly(0, [])], [0, 0], [p2, P1])
    cw = []
    for k, E in ce["charWit"]:
        poly = [(tuple(kk), (int(v[0]), int(v[1]))) for kk, v in E["poly"]]
        cw.append((tuple(k), (shear_terms(poly), E["pinHalvings"], E["pinOrder"])))
        assert tuple(k) == (1, 0)
    wit = M.Witnesses([], [], cw)
    box = shear_box([(F(c), F(r)) for c, r in ce["freqBox"]])
    return emb, wit, box


def sorted_ok(l):
    return all(key_lt2(l[i][0], l[i + 1][0]) for i in range(len(l) - 1))


# ---------------------------------------------------------------------------------------------- the build
def assemble_rot(spec, toy, box, emb, wit, params, cfgs, centre, radius, rhoH, gramInv, torsInv):
    """forced_cert.assemble with the embedding and the character witness given (not solved)."""
    B = A.FixedB(spec["P"])
    c = C.Cert()
    c.B, c.n, c.which = B, 2, spec["name"]
    c.params = params
    c.jet = FC.jet_of(toy)
    c.jetOps = c.jet["prog"]
    c.jetOps_toy = FC.toy_ops(c.jetOps)
    c.expHalvings, c.expOrder = spec["expHalvings"], spec["expOrder"]
    c.weightH = M.Weight(rhoH, FC.weight_for(rhoH, c.expHalvings, c.expOrder))
    c.weight = M.Weight(params["rho"], FC.weight_for(params["rho"], c.expHalvings, c.expOrder))
    c.centre, c.radius = list(centre), list(radius)
    c.freqBox = box
    c.emb = emb
    c.wit = wit
    c.gramInv = gramInv
    c.piEnc = FC.pi_enclosure(B, *spec["machin"])
    c.cfgFull, c.cfgLow = cfgs
    c.torsInv = torsInv
    c.DKc = C.dkCache(B, 2, c.emb, c.weight, c.piEnc)
    c.toy, c.torus, c.spec = toy, None, spec
    return c


def generate_rot(log=print):
    bj = base_cert()
    spec = dict(FC.DEFAULT_SPEC, **FB.SPECS[BASE])
    spec["name"] = TAG
    toy = RotToy(N=spec["N"], c=F(spec["c"]), beta=F(spec["beta"]), s=F(spec["s"]),
                 modes=[(tuple(k), F(e)) for k, e in spec["modes"]], name=TAG)
    emb, wit, box = rot_data(bj)
    for P in (emb.angle[0], emb.action[0], emb.action[1]):
        assert sorted_ok(P.half) and all(k > (0, 0) for k, _ in P.half), P.half
    abox, root = FM.freq_box(toy, spec["sqrt5_digits"])
    assert abox == box, (abox, box)                  # the A-image of Micro's box is the checkAlgBox box of omega'
    assert [str(x) for x in root] == bj["certificate"]["sqrt5"]
    D = 1 << spec["P"]
    pbar, P1bar = F(emb.action[0].zero, D), F(emb.action[1].zero, D)
    rho, mu = F(spec["rho"]), F(spec["mu"])
    room = F(spec["room"])
    one = [[[((0, 0), (FC.c_one(spec), 0))], []], [[], [((0, 0), (FC.c_one(spec), 0))]]]
    # pass 1: the embedding's sup bounds fix the domain (forced_cert.generate, verbatim steps)
    p = FC.base_params(spec, toy)
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), [pbar, P1bar], [F(1), F(1)], rho + F(1), one,
                     [[(0, 0)] * 3] * 3)
    r = FC.run(c, ["checkEmbedding"])["checkEmbedding"]["info"]
    iota = max(min(a, b) for a, b in r["iota"])
    rhoH = FC.up_sig(rho + iota + mu + room * rho, 3)
    centre = [FM.rnd(pbar, 40), FM.rnd(P1bar, 40)]
    acts = [s for s, _ in r["action"]]
    radius = [FC.up_sig(a * F(11, 10) + mu + room * mu + F(1, 10 ** 6), 2) for a in acts]
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), centre, radius, rhoH, c.gramInv, c.torsInv)
    r = FC.run(c, ["checkEmbedding", "checkHamBounds"])
    e, h = r["checkEmbedding"]["info"], r["checkHamBounds"]["info"]
    radius = [FC.up_sig(s * F(11, 10) + mu + F(1, 10 ** 6), 2) for s, _ in e["action"]]
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), centre, radius, rhoH, c.gramInv, c.torsInv)
    h = FC.run(c, ["checkHamBounds"])["checkHamBounds"]["info"]
    M_ = FC.up_sig(max(h["bounds"]) * F(101, 100), 3)
    sK = FC.up_sig(max(e["dkRows"]) * F(101, 100) + mu, 3)
    p = FC.base_params(spec, toy, M_=M_, sK=sK)
    assert not spec.get("gramTol")
    gi, G = FC.gram_const_inverse(c)
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), centre, radius, rhoH, gi, c.torsInv)
    g = FC.run(c, ["checkGram"])["checkGram"]
    if not g["ok"]:
        raise RuntimeError("Gram check fails with the constant inverse: %r" % g["info"])
    d_, b_ = max(g["info"]["dRows"]), max(g["info"]["bRows"])
    sB = FC.up_sig(b_ / (1 - d_) * F(101, 100) + mu, 3)
    p = FC.base_params(spec, toy, M_=M_, sK=sK, sB=sB)
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), centre, radius, rhoH, gi, c.torsInv)
    db = C.gramCheck(c.B, 2, c.emb, c.gramInv, c.weight, c.cfgLow, c.piEnc, p["sB"] - p["mu"], c.DKc)
    Tm = C.torsionModels(c.B, 2, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], c.weight, c.cfgLow,
                         c.piEnc, c.DKc)
    S, Cm = FC.torsion_witness(c, Tm)
    ti = {}
    C.torsionAvgCheck(c.B, 2, Tm, S, F(10 ** 6), ti)
    sT = FC.up_sig(ti["b"] / (1 - ti["deltaT"]) * F(101, 100) + mu, 3)
    p = FC.base_params(spec, toy, M_=M_, sK=sK, sB=sB, sT=sT)
    c = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec), centre, radius, rhoH, gi, S)
    r = FC.run(c, ["checkInvariance", "checkEnergy"])
    rows = r["checkInvariance"]["info"].get("rows")
    if rows is None:
        raise RuntimeError("composition failed: %r" % r["checkInvariance"]["info"].get("compose"))
    en = r["checkEnergy"]["info"]["value"]
    err = FC.up_sig(max(max(rows), en) * F(spec["err_slack"]), 3)
    p = FC.base_params(spec, toy, M_=M_, sK=sK, sB=sB, sT=sT, err=err)
    cf, cl = FC.make_cfgs(spec)
    c = assemble_rot(spec, toy, box, emb, wit, p, (cf, cl), centre, radius, rhoH, gi, S)
    FC.run(c, [n for n, _ in C.SUBCHECKS])
    books = {"cfgFull": FC.books_of(cf), "cfgLow": FC.books_of(cl)}
    c2 = assemble_rot(spec, toy, box, emb, wit, p, FC.make_cfgs(spec, books), centre, radius, rhoH, gi, S)
    t1 = time.time()
    chk = FC.run(c2, [n for n, _ in C.SUBCHECKS if n != "checkSmallness"])
    c2.books, c2.root = books, root
    c2.report = dict(spec={k: (str(v) if isinstance(v, F) else v) for k, v in spec.items()},
                     toy=toy.describe(), check_seconds=round(time.time() - t1, 1), gram_avg=G.tolist(),
                     torsion_centre=[[str(z) for z in r] for r in Cm],
                     checks={k: dict(ok=v["ok"], info=FC.summ(v["info"])) for k, v in chk.items()},
                     params={k: str(v) for k, v in p.items()},
                     misses={nm: [list(x) if isinstance(x, tuple) else x for x in cfg.misses][:5]
                             for nm, cfg in (("cfgFull", c2.cfgFull), ("cfgLow", c2.cfgLow))},
                     sizes=FC.sizes(c2), base_params=bj["certificate"]["params"],
                     err_ratio=float(err / F(bj["certificate"]["params"]["err"])))
    c2.report["passes_base"] = all(v["ok"] for v in chk.values())
    return c2


# ---------------------------------------------------------------------------------------------- mutations
def mutations(c, bj):
    """Mirror verdicts of the drift mutations of MicroRotMut.lean (the rejecting sub-check)."""
    out = {}
    ce = bj["certificate"]
    # (1) the rotated Hamiltonian and torus with Micro's (unrotated) box
    mbox = [(F(a), F(b)) for a, b in ce["freqBox"]]
    c1 = assemble_rot(c.spec, c.toy, mbox, c.emb, c.wit, c.params, FC.make_cfgs(c.spec, c.books), c.centre,
                      c.radius, c.weightH.rho, c.gramInv, c.torsInv)
    out["unrotatedBox"] = FC.run(c1, ["checkInvariance"])["checkInvariance"]["ok"]
    # (2) the rotated Hamiltonian with Micro's (unrotated) torus and witness
    e = ce["emb"]
    uz, uh = rp_of(e["angle"][0])
    pz, ph = rp_of(e["action"][0])
    Jz, Jh = rp_of(e["action"][1])
    memb = M.Embedding([-1, 0], [M.RealPoly(uz, uh), M.RealPoly(0, [])], [0, 0], [M.RealPoly(pz, ph),
                                                                                 M.RealPoly(Jz, Jh)])
    cw = [(tuple(k), ([(tuple(kk), (int(v[0]), int(v[1]))) for kk, v in E["poly"]], E["pinHalvings"],
                      E["pinOrder"])) for k, E in ce["charWit"]]
    c2 = assemble_rot(c.spec, c.toy, c.freqBox, memb, M.Witnesses([], [], cw), c.params,
                      FC.make_cfgs(c.spec, c.books), c.centre, c.radius, c.weightH.rho, c.gramInv, c.torsInv)
    out["unrotatedTorus"] = FC.run(c2, ["checkInvariance"])["checkInvariance"]["ok"]
    return out


# ---------------------------------------------------------------------------------------------- Lean
DATA_DOC = """The forced toy `Micro` in the rotated variables of the lunar client: the linear
symplectic unimodular change of variables `L ((Q₀, Q₁), (P₀, P₁)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))`
(`shearMap`, the lunar `soRotMap`). The Hamiltonian is `H ∘ L` (modes `k ↦ (k₀, k₀ + k₁)`, the
action `J` becomes `P₁ - P₀`); the torus is `L⁻¹ ∘ K ∘ S`, `S (φ₀, φ₁) = (φ₀ + φ₁, φ₁)`, whose
data are `Micro`'s mantissas at the sheared keys, the action `P₁ = p + J` merging the two
key-sorted lists; the character witness is `Micro`'s, relabelled; the box is the exact image of
`Micro`'s under `ω ↦ (ω₀ - ω₁, ω₁)` and `γ` is halved. The domain, `M`, the `σ`'s, the Gram and
torsion witnesses, `err` and the advice books are computed afresh by the mirror.
`MicroRotTransform` proves that these data are exactly the transforms (`ham_eq`, `emb_eq`,
`box_eq`). Emitted by `scripts/certifier/forced/forced_rot.py`; the producer's report is
`scripts/certifier/fixtures/forced-toy/MicroRot.json`."""


def data_text(c):
    text = FE.emit_data(c, TAG, "The forced toy `Micro` in rotated coordinates (data)", DATA_DOC)
    reps = [("/-- the half keys of action 1, `J` -/\ndef JHalf", "/-- the half keys of action 1, `P₁ = p + J` -/\n"
             "def P1Half"),
            ("/-- action 1, `J` -/\ndef J : CertRealPoly FB := ⟨⟨", "/-- action 1, `P₁ = p + J` -/\n"
             "def P1 : CertRealPoly FB := ⟨⟨"),
            ("⟩, JHalf⟩", "⟩, P1Half⟩"), ("[0, 0], [p, J]⟩", "[0, 0], [p, P1]⟩")]
    for a, b in reps:
        assert text.count(a) == 1, a
        text = text.replace(a, b)
    return text


CHECK_MODULES = ["ChecksA", "ChecksB", "Gram", "Torsion1", "Torsion2", "Torsion3", "Base"]


def check_texts():
    """The landed sub-check modules of MicroRot: Micro's, with the tag renamed (they are generic in the data)."""
    out = {}
    for nm in CHECK_MODULES:
        src = open(os.path.join(LEAN_DIR, "%s%s.lean" % (BASE, nm))).read()
        txt = re.sub(r"\bMicro(?=[A-Z.` ]|\b)", TAG, src)
        assert BASE + "Rot" + "Rot" not in txt
        out[nm] = FB.checked(txt)
    return out


def write_lean(c, st, A_, B_):
    import forced_routes as FR
    files = {"Data": data_text(c), "Stages": FS.emit_stages(c, st, TAG, MOD + TAG + "Data")}
    files.update(check_texts())
    files["Routes"] = FR.frozen_module(TAG, A_, B_)
    for nm, text in files.items():
        for ln in text.split("\n"):
            assert len(ln) <= 100, (nm, ln)
        with open(os.path.join(LEAN_DIR, "%s%s.lean" % (TAG, nm)), "w") as fh:
            fh.write(text)
    return sorted(files)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", default=None)
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    t0 = time.time()
    c = generate_rot()
    print(TAG, "generated in %.1fs, base passes in the mirror: %s" % (time.time() - t0, c.report["passes_base"]))
    assert c.report["passes_base"], c.report["checks"]
    st = FS.stages(c)
    c.stages = st
    wd = FB.work_dir(a.work)
    with open(os.path.join(wd, "forced_%s.pkl" % TAG), "wb") as fh:
        pickle.dump(c, fh)
    import forced_witness as FW
    import sharp_q as SQ
    A_ = FW.frozen_A(c)
    A_["err"], A_["esharp"] = c.params["err"], SQ.sharp(dict(c.params))["threshold"]
    B_ = FW.route_B(c, TAG, None, frozen=True)
    bj = base_cert()
    mut = mutations(c, bj)
    print("mutations (mirror verdict of checkInvariance):", mut)
    assert not any(mut.values())
    rep = dict(spec=c.report["spec"], toy=c.report["toy"], report=c.report, certificate=FB.cert_json(c),
               witness=FW.jsonable(dict(sharp=dict(threshold=A_["esharp"]), frozenA=A_,
                                        frozenB={k: v for k, v in B_.items() if k != "I"})),
               mutations=dict(unrotatedBox=dict(check="checkInvariance", mirror_ok=mut["unrotatedBox"]),
                              unrotatedTorus=dict(check="checkInvariance", mirror_ok=mut["unrotatedTorus"])))
    with open(os.path.join(JSON_DIR, "%s.json" % TAG), "w") as fh:
        json.dump(rep, fh, indent=1, sort_keys=True, default=str)
    print(json.dumps(dict(sizes=c.report["sizes"], params=c.report["params"], err_ratio=c.report["err_ratio"],
                          esharp=float(A_["esharp"]), estarA=float(A_["estar"]), estarB=float(B_["estar"])),
                     default=str))
    if not a.no_lean:
        print("wrote", write_lean(c, st, A_, B_))


if __name__ == "__main__":
    main()

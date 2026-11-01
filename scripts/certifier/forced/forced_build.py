#!/usr/bin/env python3
"""V2-TOOLS #6: build one forced-toy certificate and write its Lean modules.  Untrusted producer tooling.

    python3 -I scripts/certifier/forced/forced_build.py TAG [--spec JSON] [--work DIR] [--no-lean]

Writes, for TAG (a Lean identifier, e.g. `Tiny`):
  KAM/CertificateSharp/V2/Tests/Forced/<TAG>Data.lean     the certificate `<TAG>.cert` (CertFixed 96)
  KAM/CertificateSharp/V2/Tests/Forced/<TAG>Stages.lean   the memoized Gram and torsion stages (literals)
  KAM/CertificateSharp/V2/Tests/Forced/<TAG>Base.lean     every landed sub-check, one kernel run each, and
                                                          `<TAG>.base_ok : landedBase.check <TAG>.cert = true`
and scripts/certifier/fixtures/forced-toy/<TAG>.json (the spec, the mirror's report and every number of the certificate), and a
pickle of the mirror objects in the work directory (default: $FORCED_WORK or /tmp) for forced_witness.py.
"""
import argparse
import json
import os
import pickle
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.setrecursionlimit(100000)

import forced_cert as FC            # noqa: E402
import forced_emit as FE            # noqa: E402
import forced_stages as FS          # noqa: E402

LEAN_DIR = os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced")
JSON_DIR = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy")
MOD = "KAM.CertificateSharp.V2.Tests.Forced."

# the named specs of the regression suite (overrides of forced_cert.DEFAULT_SPEC)
SPECS = {
    "Tiny": dict(modes=[[[1, 0], "1/10000000"], [[1, 1], "1/5000000"]], prune_digits=13, char_tol="1/100000000",
                 gramTol=None, cutLow=4, L0=4, L1=3, machin=[6, 3]),
    # near-integrable control: residual small enough for the sharp and the frozen routes
    "Micro": dict(modes=[[[1, 0], "1/1000000000000"], [[1, 1], "1/500000000000"]], prune_digits=27,
                  char_tol="1/100000000000000000", gramTol=None, cutLow=4, L0=4, L1=3, machin=[8, 3],
                  sqrt5_digits=45),
}


def base_module(tag):
    T = tag
    return FE.HEADER + """public import %(mod)s%(T)sStages
public import %(mod)s%(T)sChecks
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.V2.Engine

/-!
# The landed sub-checks of the forced toy `%(T)s`, one kernel run each

`static_ok` … `energy_ok` (`%(T)sChecks`) decide the landed sub-checks directly. The Gram
and torsion checks go through the memoized stages of `%(T)sStages` (`Kernel/Stage.lean`):
each stage literal, computed by the Python mirror, is re-proved here by its own
`decide +kernel` on a Boolean equality, then rewritten into the landed `gramCheck` and
`torsionModels` (`gramCheck_eq_of_rows`, `torsionModels_eq_of_stages`). A mirror that drifted
from the landed checker would fail these equalities: the stage theorems are the cross-language
agreement test of the producer. `base_ok` assembles `landedBase.check`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-! ### Gram -/

theorem G_eq : gramModels 2 cert.emb cert.weight cert.cfgLow cert.piEnc = G :=
  eq_of_matBeq (by decide +kernel)

theorem dRows_eq : gramDefectRows 2 cert.gramInv G cert.weight cert.cfgLow cert.piEnc = dRows := by
  decide +kernel

theorem gram_eq : gramCheck 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc
    (cert.params.σB - cert.params.μ) = some db :=
  (gramCheck_eq_of_rows 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc _
    (by decide +kernel) (by rewrite [G_eq]; exact dRows_eq)).trans (by decide +kernel)

theorem gram_ok : checkGram cert = true := checkGram_of_gramCheck gram_eq

/-! ### Torsion, stage by stage -/

theorem eps_eq : gramInvRadius db = some eps := by decide +kernel

theorem ms_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow cert.piEnc
    (torsionSlots 2 cert.ham.jet) = some ms :=
  eq_of_optModelsBeq (by decide +kernel)

theorem L_eq : dkModels 2 cert.emb cert.weight cert.piEnc = L := eq_of_matBeq (by decide +kernel)

theorem Gi_eq : gramInvModels 2 cert.gramInv eps = Gi := eq_of_matBeq (by decide +kernel)

theorem DL_eq : dkwModels 2 cert.emb cert.freqBox cert.params.s cert.weight cert.cfgLow
    cert.piEnc = DL :=
  eq_of_matBeq (by decide +kernel)

theorem N0_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 0] (2 + 2) 2 2 L Gi = N0 :=
  eq_of_matBeq (by decide +kernel)

theorem DG1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 1] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 DL) L = DG1 :=
  eq_of_matBeq (by decide +kernel)

theorem DG2_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 2] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 L) DL = DG2 :=
  eq_of_matBeq (by decide +kernel)

theorem DGi0_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 3] 2 2 2 Gi
    (modelMatAdd cert.weight cert.piEnc 2 2 DG1 DG2) = DGi0 :=
  eq_of_matBeq (by decide +kernel)

theorem DGi1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 4] 2 2 2 DGi0 Gi = DGi1 :=
  eq_of_matBeq (by decide +kernel)

theorem DN1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 5] (2 + 2) 2 2 DL Gi = DN1 :=
  eq_of_matBeq (by decide +kernel)

theorem DN2_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 6] (2 + 2) 2 2 L
    (modelMatNeg 2 2 DGi1) = DN2 :=
  eq_of_matBeq (by decide +kernel)

theorem XN1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 7] (2 + 2) (2 + 2) 2
    (dxhModels 2 ms) (modelMatOmega 2 2 N0) = XN1 :=
  eq_of_matBeq (by decide +kernel)

theorem Tb_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 8] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 N0))
    (modelMatOmega 2 2 (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 XN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2
        (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 DN1 DN2))))) = Tb :=
  eq_of_matBeq (by decide +kernel)

theorem Y_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 9] 1 (2 + 2) 2 (d1Models 2 ms)
    (modelMatOmega 2 2 N0) = Y :=
  eq_of_matBeq (by decide +kernel)

/-- The torsion check from the stages: `torsionAvgCheck` on the assembled literal matrix. -/
theorem torsion_ok : checkTorsion cert = true := by
  rw [checkTorsion_eq_of gram_eq (torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit
    cert.gramInv db cert.freqBox cert.params.s cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq
    Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq)]
  decide +kernel

/-- **Every landed sub-check passes** on `%(T)s.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=T)


def checks_module(tag):
    return FE.HEADER + """public import %(mod)s%(T)sData
public import KAM.CertificateSharp.V2.Engine

/-!
# The direct landed sub-checks of the forced toy `%(T)s`

`checkStatic`, `checkHamBounds`, `checkEmbedding`, `checkInvariance`, `checkEnergy` on `%(T)s.cert`,
one `decide +kernel` each. The Gram and torsion checks are in `%(T)sBase` (memoized stages).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM.Certificate

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=tag)


def checked(text):
    for ln in text.split("\n"):
        assert len(ln) <= 100, ln
    return text


def cert_json(c):
    B, e = c.B, c.emb
    rp = lambda R: dict(zero=str(R.zero), half=[[list(k), [str(v[0]), str(v[1])]] for k, v in R.half])
    pj = lambda P: [[list(k), [str(v[0]), str(v[1])]] for k, v in P]
    return dict(precision=B.P, mantissas="integers m denoting m / 2^%d (CertFixed %d)" % (B.P, B.P),
                params={k: str(v) for k, v in c.params.items()}, ham=FE.FM.ham_lean(c.toy.ham()),
                weightH=[str(c.weightH.rho), str(c.weightH.w)], weight=[str(c.weight.rho), str(c.weight.w)],
                centre=[str(x) for x in c.centre], radius=[str(x) for x in c.radius],
                freqBox=[[str(a), str(b)] for a, b in c.freqBox],
                sqrt5=[str(c.root[0]), str(c.root[1])], algCoeffs=[[str(x) for x in r] for r in c.toy.alg_coeffs()],
                emb=dict(angleDeg=e.angleDeg, angle=[rp(R) for R in e.angle], actionDeg=e.actionDeg,
                         action=[rp(R) for R in e.action]),
                charWit=[[list(k), dict(poly=pj(E[0]), pinHalvings=E[1], pinOrder=E[2])] for k, E in c.wit.charWit],
                gramInv=[[pj(P) for P in r] for r in c.gramInv],
                torsInv=[[[str(z[0]), str(z[1])] for z in r] for r in c.torsInv],
                advice={nm: [list(k) for k, _ in c.books[nm]] for nm in ("cfgFull", "cfgLow")},
                cfg=dict(cutFull=c.cfgFull.cutoff, cutLow=c.cfgLow.cutoff, taylorN=c.cfgFull.taylorN,
                         halvings=c.cfgFull.halvings),
                piEnc=[str(c.piEnc.centre), str(c.piEnc.rad), c.piEnc.machinK, c.piEnc.machinJ],
                expHalvings=c.expHalvings, expOrder=c.expOrder)


def work_dir(a):
    d = a or os.environ.get("FORCED_WORK") or "/tmp"
    os.makedirs(d, exist_ok=True)
    return d


def build(tag, spec=None, work=None, lean=True, log=print):
    spec = dict(SPECS.get(tag, {}), **(spec or {}))
    spec["name"] = tag
    t0 = time.time()
    c = FC.generate(spec, log=lambda *a: None)
    log(tag, "generated in %.1fs, base passes in the mirror: %s" % (time.time() - t0, c.report["passes_base"]))
    assert c.report["passes_base"], c.report["checks"]
    st = FS.stages(c)
    c.stages = st
    wd = work_dir(work)
    with open(os.path.join(wd, "forced_%s.pkl" % tag), "wb") as fh:
        pickle.dump(c, fh)
    os.makedirs(JSON_DIR, exist_ok=True)
    with open(os.path.join(JSON_DIR, "%s.json" % tag), "w") as fh:
        json.dump(dict(spec=c.report["spec"], toy=c.report["toy"], report=c.report, certificate=cert_json(c)),
                  fh, indent=1, sort_keys=True, default=str)
    if lean:
        os.makedirs(LEAN_DIR, exist_ok=True)
        with open(os.path.join(LEAN_DIR, "Format.lean"), "w") as fh:
            fh.write(FE.format_text(c.B.P))
        doc = ("The periodically forced toy `%s` of the V2-TOOLS regression suite,\n"
               "`H = c (J + β p²/2 + Σ ε_j cos 2π k_j·θ)`, reference vector `κ (ν₋(%d) - 1, 1)`, `κ = c/s`.\n"
               "Emitted by `scripts/certifier/forced/forced_build.py %s`; the producer's report is\n"
               "`scripts/certifier/fixtures/forced-toy/%s.json`.") % (tag, c.toy.N, tag, tag)
        with open(os.path.join(LEAN_DIR, "%sData.lean" % tag), "w") as fh:
            fh.write(FE.emit_data(c, tag, "The forced toy `%s` (data)" % tag, doc))
        with open(os.path.join(LEAN_DIR, "%sStages.lean" % tag), "w") as fh:
            fh.write(FS.emit_stages(c, st, tag, MOD + tag + "Data"))
        with open(os.path.join(LEAN_DIR, "%sChecks.lean" % tag), "w") as fh:
            fh.write(checked(checks_module(tag)))
        with open(os.path.join(LEAN_DIR, "%sBase.lean" % tag), "w") as fh:
            fh.write(checked(base_module(tag)))
    return c


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("tag")
    ap.add_argument("--spec", default=None)
    ap.add_argument("--work", default=None)
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    c = build(a.tag, json.loads(a.spec) if a.spec else None, a.work, not a.no_lean)
    r = c.report
    print(json.dumps(dict(sizes=r["sizes"], params=r["params"], torus=r["torus"]), default=str))

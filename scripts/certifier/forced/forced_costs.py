#!/usr/bin/env python3
"""V2-CONSOL #3: measure the kernel cost of the l1 entry and the hybrid restart on the forced toy `Tiny` (the
calibration of `scripts/certifier/route_select.py`'s `extra` terms).  Untrusted tooling.

    python3 -I scripts/certifier/forced/forced_costs.py --write DIR            # the probe files (one per group)
    python3 -I scripts/certifier/forced/forced_costs.py --run DIR --rounds 5   # run them (each one Lean process,
                                                                                # LEAN_NUM_THREADS=1, /usr/bin/time)
    python3 -I scripts/certifier/forced/forced_costs.py --reduce LOG [--fixture]  # medians, ratios -> fixture

A probe is a scratch Lean file importing the built forced-toy modules (TinyGram, TinyFreq, TinyL1HybData, Lemmas,
the bridges Kernel/Stage*.lean, Hybrid.Iso) and holding one group of `decide +kernel` theorems; a stage a theorem
depends on (the torsion models, a composition) enters as a hypothesis, so a probe measures only its own kernel work.
The groups:
  none    an empty theorem (the import baseline, subtracted from every group);
  base    the landed sub-checks of Tiny.cert (static, ham bounds, embedding, invariance, energy, the Gram stages,
          the low composition, the eight torsion stages, the torsion residual);
  refA    the refined-A test without its sites: checkHamClaim, the four frame majorants, refinedCore;
  Rcore   refinedCore alone (without its sites);
  L1      the l1 entry without its sites: the guards and the residuals of checkL1L, checkL1N, checkL1T, checkL1E
          (memoized stages), and l1Core;
  hyb     the hybrid without its sites: transferOk, hybWeightsOk, hybPolyOk, hybOmegaOk, hybCauchyOk, the residual
          of hybCompOk (memoized compositions), the d_omega check, refinedCoreR at the restart;
  omega   hybOmegaOk alone (the Lagrange matrices: direct products of the derivative models);
  stagesF the two full-stage composition literals msF, mvF (shared with checkInvariance / checkEnergy when those
          are memoized too);
  refR    refinedCoreR at the base L8' witness (lever L8');
  raw     hybCompOk and checkL1E without memoization.
Each round runs every group once; `--reduce` takes per round the user CPU minus the round's baseline, forms the
ratios within the round, then the median over the rounds (refinedCore: the median of its own rounds):
  D          = base + refA                       (the refined-A certificate without sites: route_select's C_ref)
  extra_l1   = (L1 - Rcore) / D                  (the l1 entry's additional kernel work)
  extra_hyb  = (hyb - omega - Rcore) / D         (the hybrid's work other than the Lagrange matrices)
  omega_s    = median(omega / D) median(D)       (CPU of the direct products of hybOmegaOk at the toy's support)
  extra_L8   = (refR - Rcore) / D.
Sites are excluded everywhere (route_select adds the measured site costs c(l) separately).  A toy measurement
extrapolates to an application only as far as the operations measured: route_select scales extra_l1 and
extra_hyb with the base and the direct products (omega) quadratically in the support (estimated).
"""
import argparse
import json
import os
import re
import shlex
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
FIXTURE = os.path.join(ROOT, "scripts", "certifier", "fixtures", "route-select", "forced_costs.json")

HDR = """module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram
public import KAM.CertificateSharp.V2.Tests.Forced.TinyFreq
public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1HybData
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.Kernel.StageL1
public import KAM.CertificateSharp.Kernel.StageHyb
public import KAM.CertificateSharp.Hybrid.Iso

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

noncomputable def TmatP : ModelMatrix FB := buildMat (2 + 1) (2 + 1) fun i j =>
  if i < 2 then
    (if j < 2 then modelMatrixEntry Tb i j else freqModel 2 cert.freqBox cert.params.s i)
  else (if j < 2 then modelMatrixEntry Y 0 j else zeroModel)

namespace Probe

"""
FTR = "\nend Probe\n\nend KAM.CertificateSharp.V2.Forced.Tiny\n\nend\n"
HT = ("(hT : torsionModels 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox "
      "cert.params.s cert.weight cert.cfgLow cert.piEnc = some TmatP)")
HMS = ("(hms : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull "
       "cert.piEnc (d1Slots 2 cert.ham.jet) = some msF)")
HMT = ("(hmt : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow "
       "cert.piEnc (torsionSlots 2 cert.ham.jet) = some ms)")
HMV = ("(hmv : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull "
       "cert.piEnc [cert.ham.jet.v0] = some mvF)")
NM = "(frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)"
P = {}
# ---- base
P["B_static"] = "theorem t : checkStatic cert = true := by decide +kernel"
P["B_hamBounds"] = "theorem t : checkHamBounds cert = true := by decide +kernel"
P["B_embedding"] = "theorem t : checkEmbedding cert = true := by decide +kernel"
P["B_invariance"] = "theorem t : checkInvariance cert = true := by decide +kernel"
P["B_energy"] = "theorem t : checkEnergy cert = true := by decide +kernel"
P["B_gram"] = """theorem t1 : gramModels 2 cert.emb cert.weight cert.cfgLow cert.piEnc = G :=
  eq_of_matBeq (by decide +kernel)
theorem t2 : gramDefectRows 2 cert.gramInv G cert.weight cert.cfgLow cert.piEnc = dRows := by
  decide +kernel
theorem t3 : gramCheck 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc
    (cert.params.σB - cert.params.μ) = some db :=
  (gramCheck_eq_of_rows 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc _
    (by decide +kernel) (by rewrite [G_eq]; exact dRows_eq)).trans (by decide +kernel)
theorem t4 : gramInvRadius db = some eps := by decide +kernel
theorem t5 : dkModels 2 cert.emb cert.weight cert.piEnc = L := eq_of_matBeq (by decide +kernel)
theorem t6 : gramInvModels 2 cert.gramInv eps = Gi := eq_of_matBeq (by decide +kernel)
theorem t7 : dkwModels 2 cert.emb cert.freqBox cert.params.s cert.weight cert.cfgLow
    cert.piEnc = DL :=
  eq_of_matBeq (by decide +kernel)
theorem t8 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 0] (2 + 2) 2 2 L Gi = N0 :=
  eq_of_matBeq (by decide +kernel)"""
P["B_ms"] = """theorem t : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow cert.piEnc
    (torsionSlots 2 cert.ham.jet) = some ms := eq_of_optModelsBeq (by decide +kernel)"""
P["B_stages"] = """theorem t1 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 1] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 DL) L = DG1 := eq_of_matBeq (by decide +kernel)
theorem t2 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 2] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 L) DL = DG2 := eq_of_matBeq (by decide +kernel)
theorem t3 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 3] 2 2 2 Gi
    (modelMatAdd cert.weight cert.piEnc 2 2 DG1 DG2) = DGi0 := eq_of_matBeq (by decide +kernel)
theorem t4 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 4] 2 2 2 DGi0 Gi = DGi1 :=
  eq_of_matBeq (by decide +kernel)
theorem t5 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 5] (2 + 2) 2 2 DL Gi = DN1 :=
  eq_of_matBeq (by decide +kernel)
theorem t6 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 6] (2 + 2) 2 2 L
    (modelMatNeg 2 2 DGi1) = DN2 := eq_of_matBeq (by decide +kernel)
theorem t7 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 7] (2 + 2) (2 + 2) 2
    (dxhModels 2 ms) (modelMatOmega 2 2 N0) = XN1 := eq_of_matBeq (by decide +kernel)
theorem t8 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 8] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 N0))
    (modelMatOmega 2 2 (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 XN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2
        (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 DN1 DN2))))) = Tb :=
  eq_of_matBeq (by decide +kernel)
theorem t9 : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 9] 1 (2 + 2) 2 (d1Models 2 ms)
    (modelMatOmega 2 2 N0) = Y := eq_of_matBeq (by decide +kernel)"""
P["B_torsion"] = ("theorem t %s : checkTorsion cert = true := by\n"
                  "  rw [checkTorsion_eq_of gram_eq hT]\n"
                  "  decide +kernel") % HT
# ---- refined A (Tiny.refinedWit): the claim and frames (shared by the l1 and hybrid routes), the core
P["R_hamClaim"] = "theorem t : checkHamClaim cert Rclaim = true := by decide +kernel"
P["R_frameL"] = "theorem t : checkFrameL cert Rclaim.bL = true := by decide +kernel"
P["R_frameN"] = ("theorem t : checkFrameN cert Rclaim.bN Rclaim.bNt = true := by\n"
                 "  rw [checkFrameN_eq_of gram_eq eps_eq %s]\n"
                 "  decide +kernel") % NM
P["R_frameT"] = ("theorem t %s : checkFrameT cert Rclaim.bT = true := by\n"
                 "  rw [checkFrameT_eq_of gram_eq hT]\n"
                 "  decide +kernel") % HT
P["R_frameOm"] = "theorem t : checkFrameOmega cert (freqNormUp cert.freqBox) = true := by decide +kernel"
P["R_sites"] = """theorem t : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true := by decide +kernel"""
P["R_core"] = """theorem t (hs : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true) :
    refinedCore 2 cert.params cert.freqBox refinedWit = true :=
  refinedCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) hs
    (by decide +kernel) (by decide +kernel)"""
# ---- l1 entry
P["L_guards"] = """theorem t1 : checkWeight l1Claim.W1 cert.expHalvings cert.expOrder = true := by decide +kernel
theorem t2 : checkWeight l1Claim.WT cert.expHalvings cert.expOrder = true := by decide +kernel
theorem t3 : decide (l1Claim.W1.rho < cert.params.rho) = true := by decide +kernel
theorem t4 : decide (l1Claim.WT.rho < cert.params.rho) = true := by decide +kernel"""
P["L_L"] = "theorem t : L1.checkL1L cert l1Claim = true := by\n  rw [L1.checkL1L_eq_of L_eq]\n  decide +kernel"
P["L_N"] = ("theorem t : L1.checkL1N cert l1Claim = true := by\n"
            "  rw [L1.checkL1N_eq_of gram_eq eps_eq %s]\n"
            "  decide +kernel") % NM
P["L_T"] = ("theorem t %s : L1.checkL1T cert l1Claim = true := by\n"
            "  rw [L1.checkL1T_eq_of gram_eq hT]\n"
            "  decide +kernel") % HT
P["L_E"] = "theorem t %s : L1.checkL1E cert l1Claim = true := by\n  rw [L1.checkL1E_eq_of hms]\n  decide +kernel" % HMS
P["L_Eraw"] = "theorem t : L1.checkL1E cert l1Claim = true := by decide +kernel"
P["S_msF"] = """theorem t : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull
    cert.piEnc (d1Slots 2 cert.ham.jet) = some msF := eq_of_optModelsBeq (by decide +kernel)"""
P["S_mvF"] = """theorem t : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull
    cert.piEnc [cert.ham.jet.v0] = some mvF := eq_of_optModelsBeq (by decide +kernel)"""
P["L_sites"] = """theorem t : sitesOk (l1Wit.num 2 cert.params cert.freqBox) l1Wit.base.core.J cert.freqBox
    l1Wit.base.κ cert.params.γ l1Wit.base.sites = true := by decide +kernel"""
P["L_core"] = """theorem t (hs : sitesOk (l1Wit.num 2 cert.params cert.freqBox) l1Wit.base.core.J cert.freqBox
    l1Wit.base.κ cert.params.γ l1Wit.base.sites = true) : L1.l1Core 2 cert.params cert.freqBox l1Wit = true :=
  L1.l1Core_of (by decide +kernel) (by decide +kernel) (by decide +kernel) hs
    (by decide +kernel) (by decide +kernel) (by decide +kernel)"""
# ---- hybrid
P["H_transfer"] = "theorem t : Hybrid.transferOk 2 cert.params cert.freqBox hybWit = true := by decide +kernel"
P["H_weights"] = """theorem t : Hybrid.hybWeightsOk cert hybWit.step hybWit.p1.rho hybWit.p1.rhoInf
    (hybWit.ρT 2 cert.freqBox) = true := by decide +kernel"""
P["H_poly"] = "theorem t : Hybrid.hybPolyOk (n := 2) hybWit.step cert.piEnc = true := by decide +kernel"
P["H_omega"] = "theorem t : Hybrid.hybOmegaOk cert hybWit.step = true := by decide +kernel"
P["H_cauchy"] = "theorem t : Hybrid.hybCauchyOk cert hybWit.step (hybWit.ρT 2 cert.freqBox) = true := by decide +kernel"
P["H_comp"] = ("theorem t %s %s %s : Hybrid.hybCompOk cert hybWit.step = true := by\n"
               "  rw [Hybrid.hybCompOk_eq_of hms hmt hmv]\n"
               "  decide +kernel") % (HMS, HMT, HMV)
P["H_compraw"] = "theorem t : Hybrid.hybCompOk cert hybWit.step = true := by decide +kernel"
P["H_dw"] = ("theorem t : decide (|hybWit.step.s1 - cert.params.s| * boxNormUp cert.freqBox ≤ hybWit.step.dw) "
             "= true := by decide +kernel")
P["H_core"] = """theorem t (hs : sitesOk (hybWit.w1.base.num 2 hybWit.p1 cert.freqBox) hybWit.w1.base.core.J
    cert.freqBox hybWit.w1.base.κ hybWit.p1.γ hybWit.w1.base.sites = true) :
    refinedCoreR 2 hybWit.p1 cert.freqBox hybWit.w1 = true :=
  refinedCoreR_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hs (by decide +kernel) (by decide +kernel)"""
P["H_refRcore"] = """theorem t (hs : sitesOk (refinedWitR.base.num 2 cert.params cert.freqBox) refinedWitR.base.core.J
    cert.freqBox refinedWitR.base.κ cert.params.γ refinedWitR.base.sites = true) :
    refinedCoreR 2 cert.params cert.freqBox refinedWitR = true :=
  refinedCoreR_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hs (by decide +kernel) (by decide +kernel)"""
P["Z_baseline"] = "theorem t : True := trivial"

GROUPS = {
    "none": ["Z_baseline"],
    "base": ["B_static", "B_hamBounds", "B_embedding", "B_invariance", "B_energy", "B_gram", "B_ms", "B_stages",
             "B_torsion"],
    "refA": ["R_hamClaim", "R_frameL", "R_frameN", "R_frameT", "R_frameOm", "R_core"],
    "Rcore": ["R_core"],
    "L1": ["L_guards", "L_L", "L_N", "L_T", "L_E", "L_core"],
    "hyb": ["H_transfer", "H_weights", "H_poly", "H_omega", "H_cauchy", "H_comp", "H_dw", "H_core"],
    "omega": ["H_omega"],
    "stagesF": ["S_msF", "S_mvF"],
    "refR": ["H_refRcore"],
    "raw": ["H_compraw", "L_Eraw"],
    "sitesR": ["R_sites"],
    "sitesL": ["L_sites"],
}


def group_text(g):
    body = [re.sub(r"\btheorem (t\d*)\b", lambda m, k=k: "theorem %s_%s" % (k, m.group(1)), P[k]) for k in GROUPS[g]]
    return HDR + "\n\n".join(body) + "\n" + FTR


def write(d):
    os.makedirs(d, exist_ok=True)
    for g in GROUPS:
        with open(os.path.join(d, "G_%s.lean" % g), "w") as fh:
            fh.write(group_text(g))


def run(d, rounds, groups, log, first=0):
    """each group once per round, one Lean process each: $FORCED_LEAN_PREFIX lake env lean, LEAN_NUM_THREADS=1,
    under /usr/bin/time -v; appends `group round user wall maxrss` lines to `log`."""
    pre = shlex.split(os.environ.get("FORCED_LEAN_PREFIX", "nice -n 5"))
    for r in range(first, first + rounds):
        for g in groups:
            tf = os.path.join(d, "G_%s.time" % g)
            tm = ["env", "LEAN_NUM_THREADS=1", "/usr/bin/time", "-v", "-o", tf]
            # a `flock LOCK` prefix keeps the lock outermost: flock LOCK env ... time ... <rest of the prefix>
            cmd = pre[:2] + tm + pre[2:] if pre[:1] == ["flock"] else tm + pre
            rr = subprocess.run(cmd + ["lake", "env", "lean", os.path.join(d, "G_%s.lean" % g)], cwd=ROOT,
                                capture_output=True, text=True)
            t = open(tf).read()
            u = float(re.search(r"User time \(seconds\): ([0-9.]+)", t).group(1))
            w = re.search(r"Elapsed \(wall clock\) time.*: (\S+)", t).group(1)
            m = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", t).group(1))
            line = "G_%s_r%d\trc=%d\tuser=%.2f\twall=%s\tmaxrss_kB=%d" % (g, r, rr.returncode, u, w, m)
            print(line, flush=True)
            with open(log, "a") as fh:
                fh.write(line + "\n")


def parse(logs):
    """{round: {group: user}} from measure lines `G_<group>_r<round> rc=0 user=U ...`."""
    out = {}
    for path in logs:
        for ln in open(path):
            m = re.match(r"(?:\S+\t)?G_(\w+?)_r(\d+)\trc=(\d+)\tuser=([0-9.]+)", ln.strip())
            if m and m.group(3) == "0":
                out.setdefault(int(m.group(2)), {})[m.group(1)] = float(m.group(4))
    return out


def reduce(logs, Rcore_logs=()):
    data = parse(logs)
    per = {}
    for r, g in sorted(data.items()):
        if "none" not in g:
            continue
        b = g["none"]
        per[r] = {k: v - b for k, v in g.items() if k != "none"}
        per[r]["baseline"] = b
    med = lambda k: statistics.median([v[k] for v in per.values() if k in v])
    rng = lambda k: [round(min(v[k] for v in per.values() if k in v), 2), round(max(v[k] for v in per.values()
                                                                                     if k in v), 2)]
    keys = sorted({k for v in per.values() for k in v})
    groups = {k: dict(median_s=round(med(k), 2), range_s=rng(k), rounds=sum(1 for v in per.values() if k in v))
              for k in keys}
    # ratios within each round (the load drifts between rounds; a ratio of groups run back to back is steadier),
    # then the median over the rounds; refinedCore (small) is the median of its own rounds
    Rc = med("Rcore")
    rr = {}
    for r, v in per.items():
        if not all(k in v for k in ("base", "refA")):
            continue
        D = v["base"] + v["refA"]
        q = dict(D_s=D)
        if "L1" in v:
            q["extra_l1"] = (v["L1"] - Rc) / D
        if "hyb" in v and "omega" in v:
            q["extra_hyb"] = (v["hyb"] - v["omega"] - Rc) / D
            q["omega_over_D"] = v["omega"] / D
            q["hyb_over_D"] = (v["hyb"] - Rc) / D
        if "refR" in v:
            q["extra_L8"] = (v["refR"] - Rc) / D
        if "stagesF" in v:
            q["stagesF_over_D"] = v["stagesF"] / D
        if "raw" in v:
            q["raw_over_D"] = v["raw"] / D
        rr[r] = q
    mr = lambda k: statistics.median([q[k] for q in rr.values() if k in q])
    rngr = lambda k: [round(min(q[k] for q in rr.values() if k in q), 4), round(max(q[k] for q in rr.values()
                                                                                     if k in q), 4)]
    rk = ("D_s", "extra_l1", "extra_hyb", "omega_over_D", "hyb_over_D", "extra_L8", "stagesF_over_D", "raw_over_D")
    ratios = {k: round(mr(k), 4) for k in rk}
    ratios["omega_s"] = round(mr("omega_over_D") * mr("D_s"), 2)
    ratios["ranges"] = {k: rngr(k) for k in rk}
    ratios["Rcore_s"] = round(Rc, 2)
    return dict(groups=groups, ratios=ratios, per_round={str(k): {kk: round(vv, 2) for kk, vv in v.items()}
                                                         for k, v in per.items()},
                per_round_ratios={str(k): {kk: round(vv, 4) for kk, vv in q.items()} for k, q in rr.items()})



def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", metavar="DIR")
    ap.add_argument("--run", metavar="DIR")
    ap.add_argument("--rounds", type=int, default=5)
    ap.add_argument("--first-round", type=int, default=0,
                    help="the index of the first round (logs are merged by round)")
    ap.add_argument("--groups", default=",".join(GROUPS))
    ap.add_argument("--log", default=None)
    ap.add_argument("--reduce", nargs="*", metavar="LOG")
    ap.add_argument("--fixture", action="store_true", help="with --reduce: write " + FIXTURE)
    a = ap.parse_args()
    if a.write:
        write(a.write)
    if a.run:
        write(a.run)
        run(a.run, a.rounds, a.groups.split(","), a.log or os.path.join(a.run, "rounds.log"), a.first_round)
    if a.reduce:
        rep = reduce(a.reduce)
        print(json.dumps(rep["ratios"], indent=1))
        print(json.dumps(rep["groups"], indent=1))
        if a.fixture:
            rep.update(toy=dict(tag="Tiny", support_u_half_terms=5, P=96, err="41/10000000000000",
                                omega_direct_pairs=2208),
                       method="user CPU of one `lake env lean` process per group and round, LEAN_NUM_THREADS=1, minus "
                              "the round's import baseline; median over rounds (machine load 25-50 on 16 cores, so "
                              "the per-round values scatter; ratios use groups of the same rounds)",
                       source="scripts/certifier/forced/forced_costs.py; kernel-tests/CertificateSharp/V2/"
                              "ForcedL1Hybrid.lean")
            rep["log"] = [ln.rstrip("\n") for path in a.reduce for ln in open(path) if ln.startswith("G_")]
            with open(FIXTURE, "w") as fh:
                json.dump(rep, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()

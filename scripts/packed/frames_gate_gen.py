#!/usr/bin/env python3
"""V2-PACKED-FRAMES gate: the packed frame tests on LG00's data (untrusted tooling; the kernel re-checks everything).

Reuses `torsr_gate_gen.compute()` (LG00's data, the rounded chain, the book: bit-exact mirror) and mirrors the three
frame tests of `KAM/CertificateSharp/Packed/Frames.lean` with the kernel's backend arithmetic (`sofx_arith.FixedB`,
`sumUp`):
  - `trFrameLOk`: column sums over `r < 2n` of `pmBound (ptK …) r j = nb + r` (the packed `DK` entries);
  - `trFrameNOk`: row and column sums of `pmBound (trN …)` (the memo of `N` through `Ω₀`);
  - `trFrameTOk`: the guard `aT ≤ aW` and the row sums of `pnorm (T entry on the window) + radius`, `T = Nᵀ Ω₀ X_N`.
The claims are LG00's (`lg00RW.R`, read from `<lg00-cert>/KAM/LG00Cert/Final/Wit.lean`).
Writes the probes (into $V2P_GATE_DIR, default .lake/v2-packed-gate), each with the data it reads:
  FRData (control: the data of FRT), FRL, FRN, FRT (the tests at LG00's claims), FRT_0, FRT_1 (the rows of FRT,
  for a split proof) and the sharp controls FRLEdge_hi / FRLEdge_lo, FRNEdge_hi / FRNEdge_lo (the largest sum, and
  one ulp 2^-128 below it: true, false), FRTEdge_lo (one ulp below the largest row of T: false).
Usage: python3 -I scripts/packed/frames_gate_gen.py
"""
import json
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import torsr_gate_gen as R    # noqa: E402
T, M = R.T, R.M
n, P = R.n, R.P


def claims(cert):
    """LG00's frame claims `bL`, `bN`, `bNt`, `bT` (exact rationals) from `Final/Wit.lean`."""
    txt = " ".join(open(os.path.join(cert, "Final", "Wit.lean"), encoding="utf-8").read().split())
    out = {}
    for k in ("bL", "bN", "bNt", "bT"):
        m = re.search(r"\b%s := (\((\d+) / (\d+) : ℚ\)|(\d+))" % k, txt)
        out[k] = F(int(m.group(2)), int(m.group(3))) if m.group(2) else F(int(m.group(4)))
    return out


def mirror(S):
    """The sums the kernel computes (backend mantissas at scale 2^P)."""
    ctx, K, memos, Tm, rb = S["ctx"], S["K"], S["memos"], S["Tm"], S["rb"]
    B = ctx.B
    colL = [M.sumUp(B, [B.upAdd(K[(r, j)][2], K[(r, j)][1]) for r in range(2 * n)]) for j in range(n)]
    Nm = memos["N"][1]
    trN = {(r, j): (Nm[(n + r, j)] if r < n else Nm[(r - n, j)]) for r in range(2 * n) for j in range(n)}
    rowN = [M.sumUp(B, [B.upAdd(trN[(r, j)][2], trN[(r, j)][1]) for j in range(n)]) for r in range(2 * n)]
    colN = [M.sumUp(B, [B.upAdd(trN[(r, j)][2], trN[(r, j)][1]) for r in range(2 * n)]) for j in range(n)]
    rowT = [M.sumUp(B, [B.upAdd(ctx.pnorm(Tm[(i, j)][0], 2 * P), Tm[(i, j)][1]) for j in range(n)])
            for i in range(n)]
    guard = rb["loads"]["aT"] <= rb["aW"]
    return dict(colL=colL, rowN=rowN, colN=colN, rowT=rowT, guardT=guard)


def main():
    S = R.compute()
    cl = claims(T.CERT)
    mv = mirror(S)
    B = S["ctx"].B
    val = lambda x: F(x, 2 ** P)
    ok = dict(L=all(B.ble(x, B.ofRatDown(cl["bL"])) for x in mv["colL"]),
              N=all(B.ble(x, B.ofRatDown(cl["bN"])) for x in mv["rowN"]) and
              all(B.ble(x, B.ofRatDown(cl["bNt"])) for x in mv["colN"]),
              T=mv["guardT"] and all(B.ble(x, B.ofRatDown(cl["bT"])) for x in mv["rowT"]))
    info = dict(claims={k: str(v) for k, v in cl.items()},
                packed={k: [float(val(x)) for x in mv[k]] for k in ("colL", "rowN", "colN", "rowT")},
                guard_aT_le_aW=mv["guardT"], aT_log2=S["rb"]["loads"]["aT"].bit_length(),
                aW_log2=S["rb"]["aW"].bit_length(), mirror_ok=ok)
    print(json.dumps(info, indent=1))
    assert all(ok.values()), "a frame test fails in the mirror"
    pt = R.parts(S["D"], S["rb"], S["memos"], S["CT"], S["RT"], S["CY"], S["RY"])
    base, node_defs, rmemo = pt["base"], pt["node_defs"], pt["rmemo"]
    q = T.qlit
    dN = base + node_defs("N") + rmemo(["N"])
    dT = base + node_defs("N") + node_defs("XN") + rmemo(["N", "XN"])
    stL = "trFrameLOk (α := LGF) 2 gW rBook gMemo %s = %s"
    stN = "trFrameNOk (α := LGF) 2 rBook rMemo %s %s = %s"
    stT = "trFrameTOk (α := LGF) 2 gW rBook rMemo %s = %s"
    rowT = ("(open KAM.Certificate.CertArith in ble (sumUp (fun j => upAdd (pnorm gW rBook.q rBook.lW rBook.Lw\n"
            "      (2 * rBook.P) ((trT (α := LGF) 2 rBook rMemo).x %d j)) ((trT (α := LGF) 2 rBook rMemo).r %d j))\n"
            "      (List.range 2)) (ofRatDown %s)) = true")
    mL, mN, mT = max(mv["colL"]), max(mv["rowN"]), max(mv["rowT"])
    probes = {
        "FRData": ("Data-only control (the data of FRT).", dT, "True"),
        "FRL": ("The packed |L^T| test at LG00's claim bL (`trFrameLOk`).", base,
                stL % (q(cl["bL"]), "true")),
        "FRN": ("The packed |N|, |N^T| tests at LG00's claims bN, bNt (`trFrameNOk`).", dN,
                stN % (q(cl["bN"]), q(cl["bNt"]), "true")),
        "FRT": ("The packed sup |T| test at LG00's claim bT (`trFrameTOk`: the guard aT <= aW and every row).",
                dT, stT % (q(cl["bT"]), "true")),
        "FRLEdge_hi": ("Control (sharp): `trFrameLOk` at the largest packed column sum is true.", base,
                       stL % (q(val(mL)), "true")),
        "FRLEdge_lo": ("Negative control (sharp): `trFrameLOk` one ulp (2^-128) below the largest packed column sum "
                       "is false.", base, stL % (q(val(mL - 1)), "false")),
        "FRNEdge_hi": ("Control (sharp): `trFrameNOk` with bN at the largest packed row sum is true.", dN,
                       stN % (q(val(mN)), q(cl["bNt"]), "true")),
        "FRNEdge_lo": ("Negative control (sharp): `trFrameNOk` with bN one ulp below the largest packed row sum is "
                       "false.", dN, stN % (q(val(mN - 1)), q(cl["bNt"]), "false")),
        "FRTEdge_lo": ("Negative control (sharp): `trFrameTOk` one ulp below the largest packed row sum of T is "
                       "false.", dT, stT % (q(val(mT - 1)), "false")),
    }
    for i in range(n):
        probes["FRT_%d" % i] = ("Row %d of the packed sup |T| test at LG00's claim bT (for a split proof)." % i, dT,
                                rowT % (i, i, q(cl["bT"])))
    R.emit(probes, imp="Frames", task="V2-PACKED-FRAMES", script="frames_gate_gen.py", ns="FGate")
    import subprocess
    try:
        commit = subprocess.run(["git", "-C", T.CERT, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    info.update(lg00_cert_commit=commit, edges=dict(L=str(val(mL)), N=str(val(mN)), T=str(val(mT))))
    with open(os.path.join(R.OUT, "FramesGate.json"), "w") as f:
        json.dump(info, f, indent=1)


if __name__ == "__main__":
    main()

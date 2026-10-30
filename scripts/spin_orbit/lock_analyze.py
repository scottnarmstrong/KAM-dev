#!/usr/bin/env python3
"""SO-LOCK-SCOPE: summarise lock_tori.py output (untrusted tooling).

For each librational torus: decay rate (decades per harmonic) of the polar data U, I and of V - V* in the
libration index k (sup over the orbital index l) and of U in l, fitted 2 decades above the double round-off floor;
the support K needed for a 1e-35 truncation tail (R2-level residual, sharp threshold 10^-31.8) and the
resulting half-support term count K*L of the anisotropic diamond |k|/K + |l|/L <= 1 (area 2KL, parity
halves it).  The decay is measured in double precision (to ~1e-16) and EXTRAPOLATED to 1e-35.

    python3 lock_analyze.py tori_A.json [tori_B.json ...]
"""
import sys, json, math
import numpy as np

TARGET = 35  # decades below the leading coefficient


def rate(dec):
    ks = sorted(int(k) for k in dec)
    vals = {int(k): v for k, v in dec.items()}
    floor = float(np.median([vals[k] for k in ks[len(ks) // 2:]]))
    sel = [k for k in ks if k >= 2 and vals[k] > floor + 2]
    if len(sel) < 3:
        return None
    b, _ = np.polyfit(sel, [vals[k] for k in sel], 1)
    return -b


def main(paths):
    rows = []
    for p in paths:
        rec = json.load(open(p))
        for t in rec["tori"]:
            if t["resid"] > 1e-12:
                continue
            rk = {n: rate(t["decay_" + n]) for n in ("U", "I", "V")}
            lt = t["decay_U_theta2"]
            ls = [l for l in range(1, 6)]
            rl = -np.polyfit(ls, [lt[l] for l in ls], 1)[0]
            r = min(rk["U"], rk["I"])  # the certificate carries the polar data U, I
            K = math.ceil(TARGET / r)
            Ll = math.ceil(TARGET / rl)
            rows.append((t["a"], t["omega"], 1 / t["omega"] - (math.sqrt(5) - 1) / 2, t["psi_amp_deg"],
                         t["pm1_total"], t["I_min"], t["I_max"], rk["U"], rk["I"], rk["V"], rl, K, Ll,
                         K * Ll))
    print("| a | omega | 1/omega - g | amplitude (deg) | max abs(p-1) | I range | decades/k U, I, V | decades/l | "
          "K, L for 1e-35 | half-diamond terms K*L |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for r in sorted(rows):
        print("| %.2f | %.6f | %.2f | %.1f | %.4f | %.2e-%.2e | %s | %.2f | %d, %d | %d |" % (
            r[0], r[1], r[2], r[3], r[4], r[5], r[6],
            ", ".join("%.2f" % x if x else "-" for x in r[7:10]), r[10], r[11], r[12], r[13]))


if __name__ == "__main__":
    main(sys.argv[1:])

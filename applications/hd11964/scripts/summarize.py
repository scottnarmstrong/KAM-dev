#!/usr/bin/env python3
"""HD11964-PILOT: the horizon ladder from the gate samples.  Untrusted (Apache-2.0).

Reads validation/gate-N4.jsonl (and rigor-N3.json for the l1 factors), writes validation/ladder.json and prints the
markdown tables of the report.

For each order N: eta_i = sampled sup over centres and fast angles of |{F_i, H}|; osc_i = (max over the region of
F_i - Lam_i) - (min over the region), the range that enters |Lam_i(t) - Lam_i(0)| <= eta_i |t| + osc_i.
Margin at T: d / max_i (eta_i T + osc_i); "closes with margin 2" iff margin >= 2.
Rigorous-design variant: eta x FR, osc x FO (FR, FO given; see the report section 5).
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import hd11964_model as HM  # noqa: E402

RUNGS = [1e3, 1e6, 1e9]


def load(path):
    rows, head = [], None
    with open(path) as fh:
        for line in fh:
            r = json.loads(line)
            if "region" in r:
                head = r
            else:
                rows.append(r)
    return head, rows


def ladder(head, rows, FR=1.0, FO=1.0):
    d = head["region"]["d"]
    N = head["N"]
    m = HM.Model()
    yu = float(m.years_per_unit())
    out = {}
    for k in range(N + 1):
        key = str(k)
        eta = [max(r["orders"][key]["rate"][i] for r in rows) * FR for i in range(2)]
        if k == 0:
            osc = [0.0, 0.0]
        else:
            osc = [(max(r["orders"][key]["Gmax"][i] for r in rows) - min(r["orders"][key]["Gmin"][i] for r in rows))
                   * FO for i in range(2)]
        worst = [max(rows, key=lambda r: r["orders"][key]["rate"][i])["tag"] for i in range(2)]
        Tmax = min((d / 2 - osc[i]) / eta[i] for i in range(2)) if all(d / 2 > o for o in osc) else 0.0
        rung = {}
        for Ty in RUNGS:
            T = Ty / yu
            marg = d / max(eta[i] * T + osc[i] for i in range(2))
            rung[f"{Ty:.0e}"] = dict(margin=marg, closes=marg >= 2,
                                     d_needed=2 * max(eta[i] * T + osc[i] for i in range(2)))
        out[k] = dict(eta=eta, osc=osc, worst=worst, Tmax_units=Tmax, Tmax_years=Tmax * yu, rungs=rung)
    return out


def main():
    head, rows = load(os.path.join(ROOT, "validation", "gate-N4.jsonl"))
    FR = float(sys.argv[1]) if len(sys.argv) > 1 else 5.0
    FO = float(sys.argv[2]) if len(sys.argv) > 2 else 1.45
    res = dict(region=head["region"], samples=len(rows), sampled=ladder(head, rows),
               rigorous_design=dict(FR=FR, FO=FO, ladder=ladder(head, rows, FR, FO)))
    with open(os.path.join(ROOT, "validation", "ladder.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    for name, L in (("sampled", res["sampled"]), (f"rigorous-design (eta x {FR}, osc x {FO})",
                                                    res["rigorous_design"]["ladder"])):
        print(f"\n### {name}\n")
        print("| order | eta_c | eta_b | osc_c | osc_b | T_max (yr), margin 2 | 1e3 yr | 1e6 yr | 1e9 yr |")
        print("|---:|---:|---:|---:|---:|---:|---|---|---|")
        for k, v in L.items():
            cells = []
            for Ty in RUNGS:
                g = v["rungs"][f"{Ty:.0e}"]
                cells.append(f'{"yes" if g["closes"] else "no"} ({g["margin"]:.2g})')
            print(f'| {k} | {v["eta"][0]:.2e} | {v["eta"][1]:.2e} | {v["osc"][0]:.2e} | {v["osc"][1]:.2e} | '
                  f'{v["Tmax_years"]:.2e} | ' + " | ".join(cells) + " |")
    print("\nworst samples:", {k: v["worst"] for k, v in res["sampled"].items()})


if __name__ == "__main__":
    main()

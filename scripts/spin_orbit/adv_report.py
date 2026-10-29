#!/usr/bin/env python3
"""SO-ADVCOUNT: totals, packaging counts (design §7.2 options A, B, C) and volume levers from adv_count output.

usage: adv_report.py adv_lower.json adv_upper.json OUT.json [OUT.md]
Also simulates ONE scalar x model product at full precision (what each of the jet's scalar `mul` slots would cost
if `Slp.compose` sent constants through `CertModel.mul`'s packed route) and reads the embedding / witness data of
<which>_rot.json for its share of the volume.  Untrusted tooling.
"""
import sys, os, json, math
from fractions import Fraction as F
import rotlib
from rotlib import Weights
import adv_pack, adv_jet, model

FILE_LINES = 1450            # data lines per lint-clean file (option A)
LINE_CHARS = 97              # usable characters per 100-column line (option A, greedy packing)
FILE_BYTES_B = 6e6           # bytes per file under option B (design §7.2: ~6 MB, ~2 min elaboration)

AGAINST_DATA = ("energy", "exp witness residual", "graph SOS", "Gram check B G")
ZERO_MODE = ("torsion block N^T Omega W", "torsion last row DH(K) N")


def embedding_bytes(which):
    d = json.load(open(os.path.join(rotlib.CERT, "%s_rot.json" % which)))
    tot = lines = coeffs = 0
    for key in ("v_sin", "p_cos", "J_cos", "E_re"):
        for row in d[key]:
            s = len(str(row[0])) + len(str(row[1])) + len(row[2]) + 8      # "(k, l, c), "
            tot += s; lines += 1; coeffs += 1
    for key in ("B11", "B12", "B22"):
        for row in d["gram_inverse"][key]:
            tot += len(str(row[0])) + len(str(row[1])) + len(row[2]) + 8; lines += 1; coeffs += 1
    tot += sum(len(x) + 2 for r in d["torsion_witness"] for x in r); coeffs += 9; lines += 3
    return dict(bytes=tot, lines=lines, coefficients=coeffs)


def scalar_product_cost(which):
    """p~ (8475 terms, 319 bits) times the one-term constant -eps A_1 at 318 bits, budget 1e-80."""
    d = json.load(open(os.path.join(rotlib.CERT, "%s_rot.json" % which)))
    S = d["scale_bits"]
    p = {(0, 0): 2 * int(d["p0"])}
    for k, l, n in d["p_cos"]:
        p[(k, l)] = int(n); p[(-k, -l)] = int(n)
    c = model.EPS * model.A_EXACT[1]
    cm = {(0, 0): int(round(c * (1 << S)))}
    st = adv_pack.simulate(p, cm, S + 1, S, Weights(F(1, 70)), 1e-80, label="scalar x p~")
    st.pop("rows_per_window", None)
    return st


def agg(rows):
    out = dict(products=0, nominal_real=0, nonzero_real=0, advice_slots=0, dec=0, hexb=0, fixed=0, shards=0,
               pairs=0, kernel=[0.0, 0.0], elab=0.0, lines_one=0, filesA_one=0, filesA_greedy=0, filesB_perprod=0)
    for r in rows:
        st = r["packed"]
        out["products"] += 1; out["nominal_real"] += 4; out["nonzero_real"] += 1
        out["advice_slots"] += st["advice_slots"]; out["dec"] += st["advice_dec_bytes"]
        out["hexb"] += st["advice_hex_bytes"]; out["fixed"] += st["advice_fixedwidth_hex_bytes"]
        out["shards"] += st["shards"]; out["pairs"] += st["pairs"]
        out["kernel"][0] += st["kernel_s"][0]; out["kernel"][1] += st["kernel_s"][1]
        out["elab"] += st["elab_s"]
        b = min(st["advice_dec_bytes"], st["advice_hex_bytes"])
        out["lines_one"] += st["advice_slots"]
        out["filesA_one"] += -(-st["advice_slots"] // FILE_LINES)
        out["filesA_greedy"] += -(-(-(-b // LINE_CHARS)) // FILE_LINES)
        out["filesB_perprod"] += max(1, math.ceil(b / FILE_BYTES_B))
    return out


def scenario(rows, drop_against=False, drop_zero=False, sym=False):
    keep = []
    dg_seen = 0
    for r in rows:
        f = r["family"]
        if drop_against and any(f.startswith(x) for x in AGAINST_DATA):
            continue
        if drop_zero and f in ZERO_MODE:
            continue
        if sym and f.startswith("torsion DG"):
            dg_seen += 1
            if dg_seen > 12:            # A2 = A1^T: the second 12 products of DG are transposes
                continue
        keep.append(r)
    return keep


def main(lo, up, out, md=None):
    res = {}
    jet, *_ = adv_jet.report()
    res["jet"] = jet
    per = {}
    for path in (lo, up):
        d = json.load(open(path))
        which = d["which"]
        rows = [r for r in d["products"] if r["cls"] == "model"]
        other = {}
        for r in d["products"]:
            if r["cls"] != "model":
                other[r["cls"]] = other.get(r["cls"], 0) + 1
        fam = {}
        for r in rows:
            fam.setdefault(r["family"], []).append(r)
        famagg = {f: agg(rs) for f, rs in fam.items()}
        for f, rs in fam.items():
            p0 = rs[0]["packed"]
            famagg[f].update(precision=rs[0]["precision"],
                             terms=[min(r["packed"]["terms_a"] for r in rs), max(r["packed"]["terms_b"] for r in rs)],
                             bits=[p0["bits_a"], p0["bits_b"]], w=[min(r["packed"]["w"] for r in rs),
                                                                   max(r["packed"]["w"] for r in rs)],
                             pout=[min(r["packed"]["pout"] for r in rs), max(r["packed"]["pout"] for r in rs)],
                             block_slots=[min(r["packed"]["block_slots"] for r in rs),
                                          max(r["packed"]["block_slots"] for r in rs)],
                             shards_each=[min(r["packed"]["shards"] for r in rs), max(r["packed"]["shards"] for r in rs)])
        emb = embedding_bytes(which)
        scen = {
            "S1 as designed (scalars specialised, zero re/im parts free)": rows,
            "S2 = S1 + against-data checks (energy, witness residuals, SOS, B G)": scenario(rows, True),
            "S3 = S2 + zero-mode-only torsion block and last row": scenario(rows, True, True),
            "S4 = S3 + DG symmetry (A2 = A1^T)": scenario(rows, True, True, True),
        }
        scen_agg = {k: agg(v) for k, v in scen.items()}
        sc = scalar_product_cost(which)
        per[which] = dict(families=famagg, non_model=other, total=agg(rows), embedding=emb, scenarios=scen_agg,
                          scalar_product=sc, sos=[r.get("sos") for r in d["products"] if r.get("sos")],
                          norms_check=d["norms_check"])
    res["per_torus"] = per
    # both tori
    both = {}
    for k in per["lower"]["scenarios"]:
        a, b = per["lower"]["scenarios"][k], per["upper"]["scenarios"][k]
        both[k] = {x: (a[x] + b[x] if not isinstance(a[x], list) else [a[x][0] + b[x][0], a[x][1] + b[x][1]])
                   for x in a}
    res["both"] = both
    embB = per["lower"]["embedding"]["bytes"] + per["upper"]["embedding"]["bytes"]
    embL = per["lower"]["embedding"]["lines"] + per["upper"]["embedding"]["lines"]
    pack = {}
    for k, t in both.items():
        bytes_ = min(t["dec"], t["hexb"]) + embB
        pack[k] = dict(
            advice_MB=min(t["dec"], t["hexb"]) / 1e6, data_MB=bytes_ / 1e6,
            A_files_one_per_line=t["filesA_one"] + -(-embL // FILE_LINES),
            A_files_greedy=t["filesA_greedy"] + -(-(-(-embB // LINE_CHARS)) // FILE_LINES),
            B_files_per_product=t["filesB_perprod"] + 2, B_files_packed=math.ceil(bytes_ / FILE_BYTES_B),
            C_data_files=t["products"] + 2, C_lean_modules_est=30, shard_theorems=t["shards"],
            kernel_cpu_h=[t["kernel"][0] / 3600, t["kernel"][1] / 3600],
            elab_cpu_h=(t["elab"] + adv_pack.ELAB_S_PER_MB * embB / 1e6) / 3600)
    res["packaging"] = pack
    # what the naive compose (scalars through packed products) would add
    njet = sum(jet["per_call"][c]["CM"] + jet["per_call"][c]["CC"] for c in
               ("invariance (d1)", "energy (v0)", "torsion (d1, d2)"))
    sc = per["lower"]["scalar_product"]
    res["naive_scalar_route"] = dict(products_per_torus=njet, advice_MB_each=min(sc["advice_dec_bytes"],
                                     sc["advice_hex_bytes"]) / 1e6, kernel_s_each=sc["kernel_s"],
                                     advice_MB_per_torus=njet * min(sc["advice_dec_bytes"], sc["advice_hex_bytes"]) / 1e6)
    json.dump(res, open(out, "w"), indent=1, default=float)
    print(json.dumps(dict(packaging=pack, naive=res["naive_scalar_route"]), indent=1, default=float))


if __name__ == "__main__":
    main(*sys.argv[1:])

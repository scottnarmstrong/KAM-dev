#!/usr/bin/env python3
"""LP-QUANT: turn results/*.json into the markdown tables of docs/campaign/studies/LP-QUANT.md (results/summary.md)."""
import glob
import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
ORDER = ["SJ", "SJcal", "SJs", "JSUN", "JSUNs", "E2w", "E3w", "E2c", "E3c", "HD109271", "HD1461", "HD11964", "HD69830", "HD96700"]


def e(x, d=2):
    if x is None:
        return "—"
    return f"{x:.{d}e}"


def f(x, d=2):
    if x is None:
        return "—"
    return f"{x:.{d}f}"


def lg(x):
    return "—" if x is None or x <= 0 else f"{math.log10(x):.1f}"


SHORT = dict(SJ="SJS, Standish axes", SJcal="SJS, calibrated", SJs="SJS, spatial", JSUN="JSUN", JSUNs="JSUN, spatial",
             E2w="2 Earths wide", E3w="3 Earths wide", E2c="2 Earths compact", E3c="3 Earths compact", HD109271="HD 109271",
             HD1461="HD 1461", HD11964="HD 11964", HD69830="HD 69830", HD96700="HD 96700")


def main():
    D = {}
    for k in ORDER:
        p = os.path.join(RES, k + ".json")
        if os.path.exists(p):
            D[k] = json.load(open(p))
            D[k]["name"] = SHORT[k]
    REACH = json.load(open(os.path.join(RES, "reach.json"))) if os.path.exists(os.path.join(RES, "reach.json")) else {}
    L = []
    L.append("### Table A. AMD geometry\n")
    L.append("| System | n | μ | C (norm.) | B (norm.) | active | C/B | strong? | δ = B − C | d⋆ (41) | d⋆ sharp | d_pair sharp |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|")
    for k, d in D.items():
        g = d["geometry"]
        ok = "yes" if g["strong_stable"] else "**no**"
        L.append(f"| {d['name']} | {g['n']} | {e(g['mu'])} | {e(g['C'])} | {e(g['B'])} | {g['active_pair']} | {f(g['beta'], 3)} | {ok} | "
                 f"{e(g['delta'])} | {e(g.get('dstar_formula'))} | {f(g.get('dstar_sharp'), 3)} | {f(g.get('dpair_sharp'), 3)} |")
    L.append("\n### Table B. Λ budgets\n")
    L.append("| System | r: n r+Ω_B ≤ δ/2 | δa/a of that r (innermost tightest) | r: n r+Ω_B ≤ δ/4 | r signed (δ/2) | r on energy shell (δ/2) | true osc. amp (μ sup ∂χ) |")
    L.append("|---|---:|---:|---:|---:|---:|---:|")
    for k, d in D.items():
        g = d["geometry"]
        if "budgets" not in g:
            continue
        b = g["budgets"]
        amp = d.get("lambda", {}).get("amp")
        L.append(f"| {d['name']} | {e(b['r_lit_half'])} | {e(g['budget_da_over_a'])} | {e(b['r_lit_q'])} | {e(b['r_signed'])} | {e(b['r_energy'])} | {e(amp)} |")
    L.append("\n### Table C. Constant chain, μ thresholds (log10 μ)\n")
    L.append("| System | actual | Lean literal μ₀ | Lean literal, 5 Gyr | paper, 5 Gyr | engine best μ₀ | engine best, 1 Myr | 1 Gyr | 5 Gyr | hypothetical engine, 5 Gyr | gap at 5 Gyr (orders) | Gronwall, 5 Gyr | first order, 5 Gyr | T at actual μ |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    for k, d in D.items():
        if "chain" not in d:
            continue
        c = d["chain"]
        g = d["geometry"]
        lit = c["literal"] or {}
        tg = c["engine_targets"]
        w = c["waterfall_5Gyr"]
        hyp = w[-1].get("log10_mu")
        m5 = tg["5000000000.0"]["log10_mu"] if tg.get("5000000000.0") else None
        act = c["engine_at_actual"]
        ta = "none" if act is None else f"{act['years']:.2e} yr"
        R = REACH.get(k, {})
        L.append(f"| {d['name']} | {math.log10(g['mu']):.1f} | {f(lit.get('log10_mu0'), 1)} | {f(lit.get('log10_mu_5Gyr'), 1)} | "
                 f"{f(c['paper_log10_mu_5Gyr'], 1)} | {f((c['engine_mu0'] or {}).get('log10_mu'), 1)} | "
                 f"{f((tg.get('1000000.0') or {}).get('log10_mu'), 1)} | {f((tg.get('1000000000.0') or {}).get('log10_mu'), 1)} | {f(m5, 1)} | {f(hyp, 1)} | "
                 f"{f(None if m5 is None else math.log10(g['mu']) - m5, 1)} | {f(R.get('log10_mu_gronwall'), 1)} | {f(R.get('log10_mu_first'), 1)} | {ta} |")
    L.append("\n### Table D. Waterfalls (log10 μ reaching 5 Gyr, cumulative)\n")
    steps = None
    keys = [k for k in ["SJ", "JSUN", "E3w", "E3c", "HD1461", "HD69830"] if k in D and "chain" in D[k]]
    if keys:
        L.append("| Step | " + " | ".join(D[k]["name"] for k in keys) + " |")
        L.append("|---|" + "---:|" * len(keys))
        lit_row = ["Lean literal"] + [f(D[k]["chain"]["literal"]["log10_mu_5Gyr"] if D[k]["chain"]["literal"] else None, 1) for k in keys]
        L.append("| " + " | ".join(lit_row) + " |")
        names = []
        for k in keys:
            for w in D[k]["chain"]["waterfall_5Gyr"]:
                if w["step"] not in names:
                    names.append(w["step"])
        for nm in names:
            row = [nm]
            for k in keys:
                v = [w for w in D[k]["chain"]["waterfall_5Gyr"] if w["step"] == nm]
                row.append(f(v[0]["log10_mu"], 1) if v else "—")
            L.append("| " + " | ".join(row) + " |")
    L.append("\n### Table E. Λ-only route: rates (normalized action per time unit)\n")
    L.append("| System | r budget | η for 5 Gyr at budget r | Gronwall T (yr) | first-order T (yr) | θ₁ | secular g | g / nearest divisor |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for k, d in D.items():
        l = d.get("lambda")
        if not l:
            continue
        r = l["rates"]["budget"]
        rm = l["rates"]["mid"]
        nd = min(x["div"] for x in l["resonances"]) if l["resonances"] else None
        L.append(f"| {d['name']} | {e(l['r_budget'])} | {e(l['eta_budget_5Gyr'])} | {e(r['T0_yr'], 1)} | {e(rm['T1_yr'], 1)} | {f(rm['theta'], 2)} | {e(l['secular'])} | {e(l['secular'] / nd if nd else None)} |")
    L.append("\n### Table E2. Pair normal form with the actual coefficients (fast angles only, slow variables frozen): rate after t Newton steps\n")
    L.append("| System | pair | samples | t=0 | 1 | 2 | 3 | 4 | 5 | 6 | samples not converged |")
    L.append("|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for k, d in D.items():
        l = d.get("lambda")
        if not l:
            continue
        for pr, nw in l["newton"].items():
            if "median_actual" not in nw:
                continue
            bad = sum(1 for row in nw["rows"] if not (row[-1] <= row[1]))
            for nm, key in (("median, actual AMD", "median_actual"), ("worst, ball sphere", "worst_sphere")):
                vals = " | ".join(e(x, 1) for x in nw[key])
                L.append(f"| {d['name']} | {pr} | {nm} | {vals} | {bad}/{len(nw['rows'])} |")
    L.append("\n### Table F. Λ-only route: resonance closure\n")
    L.append("| System | records (order: k, |k·ω|, action distance) | divisor with first-order shift; strength; converged (actual, sphere) | closure 1 Myr (r, K) | closure 1 Gyr | closure 5 Gyr (r, K, rate) | with effective ω, 5 Gyr |")
    L.append("|---|---|---|---|---|---|---|")
    for k, d in D.items():
        l = d.get("lambda")
        if not l:
            continue
        rs = "; ".join(f"{x['order']}: {tuple(x['k'])}, {x['div']:.1e}, {x['dist']:.1e}" for x in l["resonances"][-3:])
        cl = l["closure"]
        ce = l.get("closure_eff") or {}
        sh = l.get("resonance_shift")
        shs = "—" if sh is None else (f"{sh['eff_min']:.2e}–{sh['eff_max']:.2e}; strength {sh['strength_actual']:.2f} (actual), {sh['strength_sphere']:.2f} (sphere); "
                                      f"converged {sh['converged_actual']}/{sh['samples_each']}, {sh['converged_sphere']}/{sh['samples_each']}")

        def cc(c):
            return "—" if c is None else f"{c['r']:.1e}, {c['K']}"

        c5 = cl.get("5000000000.0")
        c5s = "—" if c5 is None else f"{c5['r']:.1e}, {c5['K']}, {c5['eta']:.1e}"
        L.append(f"| {d['name']} | {rs} | {shs} | {cc(cl.get('1000000.0'))} | {cc(cl.get('1000000000.0'))} | {c5s} | {cc(ce.get('5000000000.0'))} |")
    L.append("\n### Table H. What a Λ-only certificate needs for 5 Gyr (pair normal form; estimates)\n")
    L.append("| System | rate needed (closure) | tube r | modes up to K | Newton steps, actual AMD | Newton steps, ball sphere | budget r / tube r |")
    L.append("|---|---:|---:|---:|---:|---:|---:|")
    for k, d in D.items():
        l = d.get("lambda")
        if not l:
            continue
        c5 = (l.get("closure_eff") or {}).get("5000000000.0") or l["closure"].get("5000000000.0")
        if c5 is None or not any("median_actual" in v for v in l["newton"].values()):
            continue
        eta = c5["eta"]

        def steps(key):
            out = 0
            for v in l["newton"].values():
                row = v[key]
                t = next((i for i, x in enumerate(row) if x <= eta), None)
                if t is None:
                    return None
                out = max(out, t)
            return out

        a, b = steps("median_actual"), steps("worst_sphere")
        L.append(f"| {d['name']} | {e(eta, 1)} | {e(c5['r'], 1)} | {c5['K']} | {"no convergence" if a is None else a} | {"diverges at some points" if b is None else b} | {e(l['r_budget'] / c5['r'], 1)} |")
    L.append("\n### Table I. n = 2, exact integrals only (energy and angular momentum, no averaging)\n")
    L.append("| System | inward walk along the energy curve | outward walk |")
    L.append("|---|---|---|")
    for k, d in D.items():
        h = d["geometry"].get("hill")
        if not h:
            continue

        def hh(x):
            a2 = x.get("a2")
            return f"{x['stop']}" + (f" at a₂ = {a2:.3f}" if a2 else "")

        L.append(f"| {d['name']} | {hh(h['inward'])} | {hh(h['outward'])} |")
    if "SJ" in D and "low_mass" in D["SJ"]:
        L.append("\n### Table G. Mass-scaled SJS shape, best engine tier\n")
        L.append("| log10 μ | T (yr) | K | r |")
        L.append("|---:|---:|---:|---:|")
        for x in D["SJ"]["low_mass"][:22]:
            L.append(f"| {math.log10(x['mu']):.0f} | {e(x['engine_years'], 1)} | {x['K'] if x['K'] else '—'} | {e(x['r'], 1)} |")
    out = "\n".join(L) + "\n"
    with open(os.path.join(RES, "summary.md"), "w") as fo:
        fo.write(out)
    print(out)


if __name__ == "__main__":
    main()

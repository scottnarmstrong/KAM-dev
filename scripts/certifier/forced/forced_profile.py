#!/usr/bin/env python3
"""V2-PUBLIC: the route-selection profile of a forced toy, for route_select.py.  Untrusted producer tooling.

    python3 -I scripts/certifier/forced/forced_profile.py TAG [--spec JSON|@FILE] [--L 15,17,...]
                                                              [--cost-s SECONDS] [--out FILE]

The model: with --spec, the overrides of forced_build.py's named spec of TAG (as `forced_build.py TAG --spec`
takes them; `@FILE` reads them from a file); without it, the spec forced_build.py recorded for TAG
(scripts/certifier/fixtures/forced-toy/<TAG>.json).  Nothing is built and no Lean is needed.  Output:
scripts/certifier/fixtures/route-select/forced_<tag>.json (tag in lower case), the profile `forced_<tag>` of

    python3 -I scripts/certifier/route_select.py forced_<tag> --beta 1

The profile holds, with the keys and meaning of route_profiles.py's lunar65 and lg00:
  params, box  the CertParams and frequency box of the certificate the producer makes from the spec
               (forced_cert.generate, deterministic: forced_build.py TAG makes the same one);
  R            the refined claim of that certificate (forced_witness.refined_claim, the exact mirror);
  err_L        the truncation L of the toy is `prune_digits` (the candidate torus is pruned at 10^-L by
               weighted size on the strip).  For every L of the grid the producer is rerun in the mirror with
               prune_digits = L and char_tol = 10^-(L - e + 2), e = ceil(-log10 max |eps_j|) (the rule of Tiny
               and Micro: the character witness enters the residual multiplied by eps); err_L[L] is that
               certificate's err, measured (err_L_measured).  An L whose base checks fail in the mirror is left
               out, and the failing checks are named on stdout;
  support_L    the genuine product pairs of the energy, Gram and torsion checks at that L (forced_sweep's
               product_pairs).  The toy's kernel cost is about linear in them (README: about 1 ms per pair),
               hence `--beta 1` above rather than the LG00 fit;
  cost_ref     the kernel cost at the spec's own L: --cost-s (CPU seconds of the tag's modules, measured),
               otherwise the README's 1 ms per product pair (source "estimate");
  P_grid       the spec's precision only: every forced-toy tag shares one Format.lean, written at its P;
  hand         the sharp route at the spec's own L, rho and P (`forced_routes.py TAG --frozen` emits the
               sharp, frozen-A and frozen-B witnesses in one module, so it needs the sharp margin);
  site costs   SO-V2PKG's certified-site costs and l rule, transferred (flagged as such).
The thresholds of every route are evaluated at the params of the spec's own certificate (as the lunar profile
evaluates them at the package's).
"""
import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))
sys.path.insert(2, os.path.join(HERE, "..", "..", "apost_sharp"))
sys.setrecursionlimit(100000)

import forced_build as FB           # noqa: E402
import forced_cert as FC            # noqa: E402
import forced_sweep as FSW          # noqa: E402
import forced_witness as FW         # noqa: E402
import sharp_q as SQ                # noqa: E402

FIX = os.path.join(ROOT, "scripts", "certifier", "fixtures")
S_PER_PAIR = 1e-3


def js(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): js(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [js(v) for v in x]
    return x


def eps_digits(spec):
    """e = ceil(-log10 max |eps_j|): char_tol = 10^-(L - e + 2) gives Tiny's (L 13, e 7) and Micro's (27, 12)."""
    return math.ceil(-math.log10(max(abs(float(F(e))) for _, e in spec["modes"])))


def model_spec(tag, spec_arg):
    """the full spec (DEFAULT_SPEC, the named spec of TAG, the overrides), as forced_build.build merges it."""
    if spec_arg is None:
        with open(os.path.join(FIX, "forced-toy", "%s.json" % tag)) as fh:
            over = json.load(fh)["spec"]
    else:
        txt = open(spec_arg[1:]).read() if spec_arg.startswith("@") else spec_arg
        over = dict(FB.SPECS.get(tag, {}), **json.loads(txt))
    spec = dict(FC.DEFAULT_SPEC, **over)
    spec["name"] = tag
    return spec


def profile(tag, spec, Ls=None, cost_s=None, log=print):
    e = eps_digits(spec)
    L0 = int(spec["prune_digits"])
    want = F(1, 10 ** (L0 - e + 2))
    if spec.get("char_tol") is None or F(spec["char_tol"]) != want:
        log("note: the spec's char_tol %s is not the grid's rule 10^-(L - e + 2) = %s at its own L = %d; the other "
            "grid points use the rule" % (spec["char_tol"], want, L0))
    Ls = sorted(set(Ls or range(max(e + 1, L0 - 12), L0 + 1, 2)) | {L0})
    err_L, support_L, measured, own = {}, {}, [], None
    for L in Ls:
        sp = dict(spec) if L == L0 else dict(spec, prune_digits=L, char_tol="1/%d" % 10 ** (L - e + 2))
        t0 = time.time()
        c = FC.generate(sp, log=lambda *a: None)
        dt = time.time() - t0
        r = c.report
        if not r["passes_base"]:
            bad = ["%s (margin %s)" % (k, v.get("info", {}).get("margin")) for k, v in sorted(r["checks"].items())
                   if not v["ok"]]
            log("L = %2d: FAILS in the mirror, left out of the profile: %s" % (L, "; ".join(bad)))
            continue
        if L == L0:
            own = c
        pairs = sum(FSW.product_pairs(c).values())
        err_L[str(L)] = "%.3g" % float(c.params["err"])
        support_L[str(L)] = pairs
        measured.append(str(L))
        log("L = %2d: err %s, product pairs %d (producer %.1fs)" % (L, err_L[str(L)], pairs, dt))
    if own is None:
        raise SystemExit("forced_profile: the spec's own certificate (L = %d) fails its base checks in the mirror; "
                         "see forced_build.py %s for the failing check" % (L0, tag))
    p = dict(own.params)
    R, _ = FW.refined_claim(own)
    esharp = SQ.sharp(dict(p))["threshold"]
    margin = math.log10(float(esharp)) - math.log10(float(p["err"]))
    P = int(spec["P"])
    if cost_s is None:
        cost = dict(cpu_h=repr(support_L[str(L0)] * S_PER_PAIR / 3600), L=L0, P=P,
                    source="estimate: 1 ms per product pair (scripts/certifier/forced/README.md), not measured")
    else:
        cost = dict(cpu_h=repr(cost_s / 3600), cpu_s=cost_s, L=L0, P=P,
                    source="measured: CPU seconds of %s's modules (--cost-s %s)" % (tag, cost_s))
    return dict(
        name="forced_%s" % tag.lower(),
        title="forced toy %s: H = c (J + β p²/2 + Σ ε_j cos 2π k_j·θ), N = %s, c = %s, β = %s, modes %s" % (
            tag, spec["N"], spec["c"], spec["beta"], json.dumps(spec["modes"])),
        params={k: (int(v) if k == "tau" else v) for k, v in p.items()}, box=own.freqBox, R=R,
        rho_fixed=True, rho_grid=[str(p["rho"])],
        err_L=err_L, err_L_measured=measured, support_L=support_L,
        support_unit="genuine product pairs of checkEnergy, checkGram, checkTorsion (forced_sweep.product_pairs)",
        truncation="L = prune_digits; char_tol = 10^-(L - %d + 2) off the spec's own L" % e,
        precision_rule=None, P_grid=[P], P_ref=P, cost_ref=cost,
        site_cost_s={"8": 2.4, "9": 6.1, "10": 10.8, "11": 34.3, "12": 85.2},
        site_l_rule=dict(delta="2.4", b="1.8", source="SO-V2PKG §2.2 rule, transferred (not measured on the toy)"),
        site_l_max=12, A_meas=None, A_meas_source="not measured for the forced toy",
        hand=dict(route="sharp", kp=0, L=L0, rho=str(p["rho"]), P=P, margin=round(margin, 2),
                  note="forced_routes.py %s --frozen: sharp, frozen A and frozen B in one module" % tag),
        margin_rule=1.0,
        provenance=dict(spec=js(spec), generator="scripts/certifier/forced/forced_profile.py"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tag")
    ap.add_argument("--spec", default=None, help="JSON overrides of the named spec of TAG, or @FILE")
    ap.add_argument("--L", default=None, help="comma-separated prune_digits grid (default: L0-12 .. L0, step 2)")
    ap.add_argument("--cost-s", type=float, default=None, help="measured CPU seconds of the tag's modules")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    Ls = [int(x) for x in a.L.split(",")] if a.L else None
    prof = profile(a.tag, model_spec(a.tag, a.spec), Ls, a.cost_s)
    out = a.out or os.path.join(FIX, "route-select", "%s.json" % prof["name"])
    with open(out, "w") as fh:
        json.dump(js(prof), fh, indent=1, sort_keys=True)
    out = os.path.abspath(out)
    print("wrote", os.path.relpath(out, ROOT) if out.startswith(ROOT + os.sep) else out)


if __name__ == "__main__":
    main()

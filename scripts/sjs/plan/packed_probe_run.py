#!/usr/bin/env python3
"""SJS-PLAN E1 runner: one Lean process per (size, theorem), ascending; stops a theorem's ladder above the RSS limit.
Records kernel seconds (profiler 'type checking took', summed for the theorem), wall, user, peak RSS to a JSONL file.
Usage: packed_probe_run.py OUT.jsonl --sizes 1e4 1e5 ... [--w 460 --p 212] [--thms t_gen,t_mul,...] [--limit-gb 3.6]
"""
import argparse, json, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def run(n, thm, w, p, timeout):
    f = ".drafts/PK_%d_%d_%s.lean" % (n, w, thm)
    subprocess.check_call([sys.executable, "-I", "scripts/sjs/plan/packed_probe_gen.py", f, "--n", str(n), "--w", str(w),
                           "--p", str(p), "--only", thm], cwd=ROOT, stdout=subprocess.DEVNULL)
    cmd = ["/usr/bin/time", "-f", "TIME %e %U %S %M", "nice", "-n", "5", "timeout", str(timeout), "lake", "env", "lean", f]
    t0 = time.time()
    p_ = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    out = p_.stdout + p_.stderr
    os.remove(os.path.join(ROOT, f))
    m = re.search(r"TIME ([0-9.]+) ([0-9.]+) ([0-9.]+) ([0-9]+)", out)
    tc = 0.0
    for v, u in re.findall(r"type checking took ([0-9.]+)(ms|s)\b", out):
        tc += float(v) / (1000.0 if u == "ms" else 1.0)
    m2 = re.search(r"type checking ([0-9.]+)(ms|s)\b", out)
    cum = float(m2.group(1)) / (1000.0 if m2.group(2) == "ms" else 1.0) if m2 else None
    errs = [l for l in out.splitlines() if "error" in l][:3]
    return dict(n=n, w=w, p=p, bits=n * w, thm=thm, exit=p_.returncode, kernel_s=cum, wall=float(m.group(1)) if m else None,
                user=float(m.group(2)) if m else None, sys=float(m.group(3)) if m else None,
                rss_gb=int(m.group(4)) / 1e6 if m else None, errors=errs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--sizes", nargs="+", type=float, required=True)
    ap.add_argument("--w", type=int, default=460)
    ap.add_argument("--p", type=int, default=212)
    ap.add_argument("--thms", default="t_gen,t_mul,t_round,t_full,t_mid")
    ap.add_argument("--limit-gb", type=float, default=3.6)
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    dead = set()
    for s in a.sizes:
        for t in a.thms.split(","):
            if t in dead:
                continue
            r = run(int(s), t, a.w, a.p, a.timeout)
            print(json.dumps(r), flush=True)
            open(a.out, "a").write(json.dumps(r) + "\n")
            if r["exit"] != 0 or (r["rss_gb"] or 0) > a.limit_gb / 1.9:   # the next size is ~2-3x: stop before the limit
                dead.add(t)


if __name__ == "__main__":
    main()

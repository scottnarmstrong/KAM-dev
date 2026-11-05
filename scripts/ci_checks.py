#!/usr/bin/env python3
"""V2-PUBLIC #4: the inexpensive checks of the certifier workflow, one named check at a time (untrusted tooling).

    python3 -I scripts/ci_checks.py [--group mirror|lint|lean|all] [--only NAME,...] [--list] [--keep DIR]

Groups (the jobs of .github/workflows/certifier-ci.yml; the same command runs them locally):
  mirror  Python only, no Lean: the exact mirrors against the Lean text and their recorded fixtures, and the
          producers regenerating the checked-in certificates byte for byte;
  lint    file-based guards: scripts/lint_sources.sh with its one Lean-dependent step (the ABI hashes of the
          frozen anchors, which need the built frozen modules) stubbed out, as guard_mutation_suite.py does, and
          the pin check of scripts/requirements.txt;
  lean    after `lake build` of the light Lean fixtures: the compiled-Lean half of the forced-toy
          cross-language comparisons (forced_xlang.py) and of the route-B diagnostics mirror
          (forced_diag.py --xlang Micro).
Every check prints PASS or FAIL with its wall time; a failing check prints the tail of its output.  The exit
status is 1 if any check failed.  No check writes into the checkout: checks that regenerate files work in a
temporary copy of the inputs they read (scripts/ and KAM/Sharp2/), and the stubbed lint runs from memory
(`sh -c`); --keep DIR keeps that copy (and FORCED_WORK, if unset, is DIR/work, so the pickles are reusable).
"""
import argparse
import ast
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
FORCED = "KAM/CertificateSharp/V2/Tests/Forced"
FIXF = "scripts/certifier/fixtures/forced-toy"
FIXR = "scripts/certifier/fixtures/route-select"
TIMING_KEYS = {"check_seconds", "seconds", "producer_seconds"}
OUT_OF_TREE = {"lg00_gen", "lg00_chart"}      # LG00 producer modules of the lg00 worktrees, imported lazily
OPTIONAL = {"scipy": {"scripts/spin_orbit/dsolve.py"}}   # scripts/requirements-scipy.txt: package -> its importers
PRODUCER_DIRS = ["scripts/certifier", "scripts/certifier/forced", "scripts/apost_sharp", "scripts/packed"]


def run(args, cwd=ROOT, env=None, timeout=1800):
    e = dict(os.environ, **(env or {}))
    r = subprocess.run(args, cwd=cwd, env=e, capture_output=True, text=True, timeout=timeout)
    return r.returncode, r.stdout, r.stderr


def py(script, *args, **kw):
    return run([PY, "-I", script] + list(args), **kw)


def expect_rc0(script, *args):
    def check(ctx):
        rc, out, err = py(script, *args)
        return rc == 0, out + err
    return check


# ---------------------------------------------------------------------------------------------- mirror
def hybrid_numq(ctx):
    rc, out, err = py("scripts/apost_sharp/hybrid_numq.py")      # validate() reports, its exit status does not
    return rc == 0 and "validate: PASS" in out, out + err


def route_select(ctx):
    out_json = os.path.join(ctx["tmp"], "validation.json")
    rc, out, err = py("scripts/certifier/route_select.py", "--validate", "--json", out_json)
    if rc != 0:
        return False, out + err
    same_json = open(out_json).read() == open(os.path.join(ROOT, FIXR, "validation.json")).read()
    same_log = out == open(os.path.join(ROOT, FIXR, "validation.log")).read()
    return same_json and same_log, "validation.json %s, validation.log %s\n%s" % (
        "identical" if same_json else "DIFFERS", "identical" if same_log else "DIFFERS", out[-2000:])


def strip_timing(x):
    if isinstance(x, dict):
        return {k: strip_timing(v) for k, v in x.items() if k not in TIMING_KEYS}
    if isinstance(x, list):
        return [strip_timing(v) for v in x]
    return x


def copy_inputs(ctx):
    """scripts/ and KAM/Sharp2/ (the Lean text the mirrors read) into ctx['copy'], once."""
    if ctx.get("copy"):
        return ctx["copy"]
    dst = os.path.join(ctx["tmp"], "repo")
    shutil.copytree(os.path.join(ROOT, "scripts"), os.path.join(dst, "scripts"),
                    ignore=shutil.ignore_patterns("__pycache__"))
    shutil.copytree(os.path.join(ROOT, "KAM", "Sharp2"), os.path.join(dst, "KAM", "Sharp2"))
    os.makedirs(os.path.join(dst, FORCED), exist_ok=True)
    ctx["copy"] = dst
    return dst


def forced_regen(ctx):
    """forced_build.py Tiny, Micro, TinyC2, forced_routes.py Micro --frozen and gen_stepbq.py in the copy; every
    emitted Lean file equal byte for byte, every JSON fixture equal up to its wall-clock fields."""
    dst = copy_inputs(ctx)
    env = dict(FORCED_WORK=ctx["work"])
    log = []
    for args in (["scripts/certifier/forced/forced_build.py", "Tiny"],
                 ["scripts/certifier/forced/forced_build.py", "Micro"],
                 ["scripts/certifier/forced/forced_build.py", "TinyC2"],
                 ["scripts/certifier/forced/forced_routes.py", "Micro", "--frozen"],
                 ["scripts/apost_sharp/gen_stepbq.py"]):
        rc, out, err = py(*args, cwd=dst, env=env)
        log.append("$ %s -> %d\n%s%s" % (" ".join(args), rc, out[-600:], err[-1500:]))
        if rc != 0:
            return False, "\n".join(log)
    bad, n = [], 0
    lean = ["Format"] + ["%s%s" % (t, k) for t in ("Tiny", "Micro", "TinyC2") for k in ("Data", "Stages")] + [
        "MicroFreq", "MicroRoutes"]
    for f in ["%s/%s.lean" % (FORCED, x) for x in lean] + ["KAM/CertificateSharp/V2/StepBQ.lean"]:
        n += 1
        if open(os.path.join(dst, f), "rb").read() != open(os.path.join(ROOT, f), "rb").read():
            bad.append(f)
    for j in ("Tiny", "Micro", "TinyC2", "Micro_witness"):
        f = "%s/%s.json" % (FIXF, j)
        n += 1
        a, b = (strip_timing(json.load(open(os.path.join(d, f)))) for d in (dst, ROOT))
        if a != b:
            bad.append(f)
    return not bad, "%d files compared; %s\n%s" % (n, "differ: " + ", ".join(bad) if bad else "all equal",
                                                  "\n".join(log)[-3000:] if bad else "")


def forced_profile(ctx):
    ref = json.load(open(os.path.join(ROOT, FIXR, "forced_micro.json")))
    out = os.path.join(ctx["tmp"], "forced_micro.json")
    args = ["Micro", "--out", out]
    if "cpu_s" in ref["cost_ref"]:
        args += ["--cost-s", repr(ref["cost_ref"]["cpu_s"])]
    rc, so, se = py("scripts/certifier/forced/forced_profile.py", *args)
    if rc != 0:
        return False, so + se
    same = open(out).read() == open(os.path.join(ROOT, FIXR, "forced_micro.json")).read()
    return same, ("forced_micro.json identical" if same else "forced_micro.json DIFFERS") + "\n" + so


def failure_diagnostics(ctx):
    """the named failure lines of the producer (V2-PUBLIC #3) still fire: forced_routes --frozen on Tiny (whose
    err is above all three thresholds) stops with FAIL lines and writes nothing; route_select explains why no
    candidate is admissible at an unreachable margin."""
    dst = copy_inputs(ctx)
    env = dict(FORCED_WORK=ctx["work"])
    if not os.path.exists(os.path.join(ctx["work"], "forced_Tiny.pkl")):
        rc, out, err = py("scripts/certifier/forced/forced_build.py", "Tiny", "--no-lean", cwd=dst, env=env)
        if rc != 0:
            return False, out + err
    target = os.path.join(dst, FORCED, "TinyRoutes.lean")
    if os.path.exists(target):
        os.remove(target)
    rc, out, err = py("scripts/certifier/forced/forced_routes.py", "Tiny", "--frozen", cwd=dst, env=env)
    want = ["FAIL route=sharp check=sharpTest.smallness", "FAIL route=A.frozen check=frozenCore.final",
            "FAIL route=B.frozen check=finalB.smallness", "nothing written"]
    ok1 = rc == 1 and all(w in err for w in want) and not os.path.exists(target)
    rc2, out2, err2 = py("scripts/certifier/route_select.py", "forced_micro", "--beta", "1", "--margin", "30")
    ok2 = rc2 == 0 and "no admissible exact candidate" in out2 and "FAIL route=sharp check=margin" in out2
    return ok1 and ok2, "forced_routes Tiny --frozen: rc %d\n%s\nroute_select --margin 30: rc %d\n%s" % (
        rc, err[-1200:], rc2, "\n".join(ln for ln in out2.splitlines() if "FAIL" in ln or "no admissible" in ln))


# ---------------------------------------------------------------------------------------------- lint
def lint_files(ctx):
    src = os.path.join(ROOT, "scripts", "lint_sources.sh")
    text = open(src, encoding="utf-8").read()
    stub, n = re.subn(r'^(\s*)python3 -I "\$project_root/scripts/abi_hashes\.py".*$', r"\1true", text, flags=re.M)
    if n != 1:
        return False, "cannot stub the ABI step: scripts/lint_sources.sh changed shape (%d matches)" % n
    # run the stubbed text with $0 set to the original path, from which lint_sources.sh finds the root: nothing is
    # written into the checkout, and concurrent runs do not collide
    rc, out, err = run(["sh", "-c", stub, src])
    return rc == 0, out + err


def third_party(paths):
    std = set(sys.stdlib_module_names)
    local = {}
    for d, _, fs in os.walk(os.path.join(ROOT, "scripts")):
        for f in fs:
            if f.endswith(".py"):
                local.setdefault(f[:-3], os.path.join(d, f))
    seen, stack, found, unresolved = set(), list(paths), {}, {}
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        for n in ast.walk(ast.parse(open(p, encoding="utf-8").read())):
            names = ([a.name for a in n.names] if isinstance(n, ast.Import) else
                     [n.module] if isinstance(n, ast.ImportFrom) and n.level == 0 and n.module else [])
            for m in (x.split(".")[0] for x in names):
                if m in std:
                    continue
                if m in local:
                    stack.append(local[m])
                elif m in OUT_OF_TREE:
                    unresolved.setdefault(m, set()).add(os.path.relpath(p, ROOT))
                else:
                    found.setdefault(m, set()).add(os.path.relpath(p, ROOT))
    return found, unresolved, len(seen)


def pins_of(name):
    """{package: version} and the set of packages with at least one sha256, of scripts/<name>."""
    txt = open(os.path.join(ROOT, "scripts", name), encoding="utf-8").read()
    pins = dict(re.findall(r"^([A-Za-z0-9_.-]+)==(\S+) \\$", txt, flags=re.M))
    blocks = re.split(r"^(?=[A-Za-z0-9_.-]+==)", txt, flags=re.M)[1:]
    return pins, {b.split("==")[0] for b in blocks if "--hash=sha256:" in b}, txt


def requirements_pins(ctx):
    """every third-party module imported (transitively) by the producer tools is pinned with `==` and at least one
    sha256: in scripts/requirements.txt, or, for the optional packages, in scripts/requirements-scipy.txt (which
    includes the core file) and imported only by the modules named in OPTIONAL (offline;
    scripts/lock_requirements.py --check compares the hashes with PyPI)."""
    roots = [os.path.join(ROOT, d, f) for d in PRODUCER_DIRS for f in sorted(os.listdir(os.path.join(ROOT, d)))
             if f.endswith(".py")]
    found, unresolved, n = third_party(roots)
    core, core_h, _ = pins_of("requirements.txt")
    opt, opt_h, opt_txt = pins_of("requirements-scipy.txt")
    missing = sorted(m for m in found if m not in core and m not in opt)
    unhashed = sorted(m for m in core if m not in core_h) + sorted(m for m in opt if m not in opt_h)
    stray = {m: sorted(set(found[m]) - OPTIONAL.get(m, set())) for m in found if m in opt and m not in core}
    stray = {m: v for m, v in stray.items() if v}
    unexpected = sorted(m for m in opt if m in core or m not in OPTIONAL)
    included = re.search(r"^-r requirements\.txt$", opt_txt, flags=re.M) is not None
    msg = ("%d producer modules scanned; third-party: %s; core pins: %s; optional pins: %s; out-of-tree local "
           "modules (lazy): %s" % (n, sorted(found), core, opt, sorted(unresolved)))
    if missing:
        msg += "\nNOT PINNED: %s" % {m: sorted(found[m])[:3] for m in missing}
    if unhashed:
        msg += "\nNO HASH: %s" % unhashed
    if stray:
        msg += "\nOPTIONAL PACKAGE IMPORTED ELSEWHERE (pin it in the core file or extend OPTIONAL): %s" % stray
    if unexpected:
        msg += "\nOPTIONAL FILE PINS %s (in the core file too, or not in OPTIONAL)" % unexpected
    if not included:
        msg += "\nscripts/requirements-scipy.txt does not include `-r requirements.txt`"
    return not (missing or unhashed or stray or unexpected) and included, msg


# ---------------------------------------------------------------------------------------------- lean
def pickles(ctx):
    """the producer pickles of Tiny, Micro, TinyC2 in ctx['work'] (forced-regen makes them when missing)."""
    for t in ("Tiny", "Micro", "TinyC2"):
        if not os.path.exists(os.path.join(ctx["work"], "forced_%s.pkl" % t)):
            ok, msg = forced_regen(ctx)
            return ok, "" if ok else "forced-regen (for the pickles) failed:\n" + msg
    return True, ""


def forced_xlang(ctx):
    ok, msg = pickles(ctx)
    if not ok:
        return False, msg
    rc, out, err = py("scripts/certifier/forced/forced_xlang.py", env=dict(FORCED_WORK=ctx["work"]), timeout=3600)
    return rc == 0, out[-3000:] + err[-2000:]


def routeB_xlang(ctx):
    ok, msg = pickles(ctx)
    if not ok:
        return False, msg
    rc, out, err = py("scripts/certifier/forced/forced_diag.py", "--xlang", "Micro",
                      env=dict(FORCED_WORK=ctx["work"]), timeout=1800)
    return rc == 0, out[-3000:] + err[-2000:]


CHECKS = [
    ("modconstb", "mirror", "route-B constants: Lean text of stepConstsB against thresholds_v2 (exact)",
     expect_rc0("scripts/apost_sharp/check_modconstb_v2.py")),
    ("smalldiv-shapes", "mirror", "shape guards of the two-frequency design routines",
     expect_rc0("scripts/apost_sharp/check_smalldiv_shapes.py")),
    ("hybrid-numq", "mirror", "hybrid route-A' numbers against the recorded kernel facts", hybrid_numq),
    ("route-b-mirror", "mirror", "route-B Lean predicate mirror against the design numbers",
     expect_rc0("scripts/apost_sharp/route_b_lean_mirror.py")),
    ("v2-adapter", "mirror", "the v2 adapter's module loading (fresh processes)",
     expect_rc0("scripts/certifier/check_v2_adapter.py")),
    ("fiber3-xlang", "mirror", "three-frequency mirror values equal the literals of Tests/Fiber3XLang.lean",
     expect_rc0("scripts/certifier/fiber3_xlang.py", "--check")),
    ("route-select", "mirror", "route_select --validate reproduces validation.json and validation.log", route_select),
    ("forced-regen", "mirror", "forced-toy producer and gen_stepbq regenerate the checked-in files", forced_regen),
    ("forced-profile", "mirror", "forced_profile.py Micro reproduces route-select/forced_micro.json", forced_profile),
    ("failure-diagnostics", "mirror", "named route/check failure lines (forced_routes, route_select)",
     failure_diagnostics),
    ("lint-files", "lint", "scripts/lint_sources.sh without the Lean-dependent ABI-hash step", lint_files),
    ("requirements-pins", "lint", "every third-party import of the producer tools is pinned with hashes",
     requirements_pins),
    ("forced-xlang", "lean", "forced-toy mirror against the compiled Lean checker (needs the built fixtures)",
     forced_xlang),
    ("routeB-xlang", "lean", "the --frozen pre-check's route-B mirror (c1Q-c3Q, finalB/F two-sided) against Lean",
     routeB_xlang),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", default="all", choices=["mirror", "lint", "lean", "all"])
    ap.add_argument("--only", default=None, help="comma-separated check names")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--keep", default=None, help="keep the temporary copy here")
    a = ap.parse_args()
    if a.list:
        for name, grp, doc, _ in CHECKS:
            print("%-20s %-6s %s" % (name, grp, doc))
        return 0
    only = set(a.only.split(",")) if a.only else None
    sel = [c for c in CHECKS if (only is None and (a.group == "all" and c[1] != "lean" or c[1] == a.group))
           or (only is not None and c[0] in only)]
    if only and len(sel) != len(only):
        raise SystemExit("unknown check(s): %s" % sorted(only - {c[0] for c in sel}))
    tmp = a.keep or tempfile.mkdtemp(prefix="kam-ci-")
    os.makedirs(tmp, exist_ok=True)
    ctx = dict(tmp=tmp, work=os.environ.get("FORCED_WORK") or os.path.join(tmp, "work"))
    os.makedirs(ctx["work"], exist_ok=True)
    rows, t_all = [], time.time()
    try:
        for name, grp, doc, fn in sel:
            t0 = time.time()
            try:
                ok, msg = fn(ctx)
            except Exception as e:                    # noqa: BLE001  (a crashing check fails, with its error)
                ok, msg = False, "%s: %s" % (type(e).__name__, e)
            dt = time.time() - t0
            rows.append((name, ok, dt))
            print("%s %-20s %7.1fs  %s" % ("PASS" if ok else "FAIL", name, dt, doc), flush=True)
            if not ok:
                print("    " + "\n    ".join(msg.strip().splitlines()[-40:]), flush=True)
    finally:
        if not a.keep:
            shutil.rmtree(tmp, ignore_errors=True)
    nf = sum(1 for _, ok, _ in rows if not ok)
    print("%d checks, %d failed, %.1fs" % (len(rows), nf, time.time() - t_all))
    return 1 if nf else 0


if __name__ == "__main__":
    sys.exit(main())

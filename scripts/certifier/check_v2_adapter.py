#!/usr/bin/env python3
"""Regression check of `v2_adapter._load` (CERTIFIER-V2-FIXES F3).  Untrusted design tooling.

Each case runs in a fresh process, on a copy of the adapter and the mirror relocated to a temporary directory:
default directory without KAM_V2_DIR, a valid override, invalid overrides, a mirror whose import fails, and modules
of the mirror's names already cached.  Exit 0 iff every case passes.

Usage: python3 -B -I scripts/certifier/check_v2_adapter.py
"""
import json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = os.path.dirname(HERE)
MIRROR = ("thresholds_v2.py", "thresholds.py", "smalldiv.py", "smalldiv_sup.py", "smalldiv_sum.py")

PRELUDE = r"""
import importlib.util, json, os, sys, types
def adapter(root):
    spec = importlib.util.spec_from_file_location("v2_adapter", os.path.join(root, "scripts/certifier/v2_adapter.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod
root = sys.argv[1]
V = adapter(root)
before = list(sys.path)
out = {}
"""


def run(body, root, env=None):
    """Run PRELUDE + body in a fresh interpreter; returns the JSON object printed by the body."""
    e = {k: v for k, v in os.environ.items() if k != "KAM_V2_DIR"}
    e.update(env or {})
    r = subprocess.run([sys.executable, "-B", "-I", "-c", PRELUDE + body, root], env=e, cwd="/",
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise AssertionError("subprocess failed:\n" + r.stderr)
    return json.loads(r.stdout.strip().splitlines()[-1])


def relocate(dst):
    os.makedirs(os.path.join(dst, "scripts/certifier"))
    os.makedirs(os.path.join(dst, "scripts/apost_sharp"))
    shutil.copy(os.path.join(HERE, "v2_adapter.py"), os.path.join(dst, "scripts/certifier"))
    shutil.copy(os.path.join(HERE, "smalldiv.py"), os.path.join(dst, "scripts/certifier"))
    for f in MIRROR:
        shutil.copy(os.path.join(SCRIPTS, "apost_sharp", f), os.path.join(dst, "scripts/apost_sharp"))
    return os.path.realpath(dst)


LOAD = r"""
T = V._load()
out.update(t2=T.__file__, sd=T.sd.__file__, v1=T.v1.__file__, sds=T.sds.__file__, path_ok=sys.path == before,
           again=V._load() is T, marker=getattr(T, "MARKER", None))
print(json.dumps(out))
"""

BAD = r"""
try:
    V._load()
    out.update(raised=None)
except ImportError as e:
    out.update(raised=str(e))
out.update(path_ok=sys.path == before)
print(json.dumps(out))
"""


def main():
    fails = []

    def check(name, cond, info=""):
        print("%-46s %s" % (name, "ok" if cond else "FAIL %s" % (info,)))
        if not cond:
            fails.append(name)

    with tempfile.TemporaryDirectory() as tmp:
        root = relocate(os.path.join(tmp, "relocated"))
        mirror = os.path.join(root, "scripts/apost_sharp")

        # 1. relocated checkout, no override
        r = run(LOAD, root)
        check("relocated: mirror of the adapter's own checkout", r["t2"].startswith(mirror), r)
        check("relocated: its siblings from the same directory", all(r[k].startswith(mirror) for k in ("sd", "v1", "sds")), r)
        check("relocated: sys.path restored, module memoized", r["path_ok"] and r["again"], r)

        # 2. usable after the restore: the functions of the mirror need no directory on sys.path
        r = run(r"""
T = V._load()
D = T.package("R1")
out.update(c_inf=float(T.c_inf_fn(D)(0.01)), st=len(T.c_stages(D, "freq")[0](0)))
print(json.dumps(out))
""", root)
        check("relocated: l^1 and frequency constants evaluate", r["c_inf"] > 0 and r["st"] == 3, r)

        # 3. unrelated modules of the same names are neither reused nor displaced
        r = run(r"""
for name in ("thresholds_v2", "thresholds", "smalldiv_sup"):
    sys.modules[name] = types.ModuleType(name)
spec = importlib.util.spec_from_file_location("smalldiv", os.path.join(root, "scripts/certifier/smalldiv.py"))
other = importlib.util.module_from_spec(spec); spec.loader.exec_module(other); sys.modules["smalldiv"] = other
decoys = {m: sys.modules[m] for m in ("thresholds_v2", "thresholds", "smalldiv", "smalldiv_sup")}
T = V._load()
out.update(t2=T.__file__, sd=T.sd.__file__, v1=T.v1.__file__, sds=T.sds.__file__, kept=all(sys.modules[m] is d for m, d in decoys.items()),
           c=T.sd.c_freq((0.5, 1.25), 0.01, 1, 0.05, N=20)[0] > 0)
print(json.dumps(out))
""", root)
        check("cached same-name modules: not reused", all(r[k].startswith(mirror) for k in ("t2", "sd", "v1", "sds")) and r["c"], r)
        check("cached same-name modules: left in place", r["kept"], r)

        # 4. a valid override wins, and is a different module from the default
        alt = relocate(os.path.join(tmp, "override"))
        alt_mirror = os.path.join(alt, "scripts/apost_sharp")
        with open(os.path.join(alt_mirror, "thresholds_v2.py"), "a", encoding="utf-8") as f:
            f.write('\nMARKER = "override"\n')
        r = run(LOAD, root, {"KAM_V2_DIR": alt_mirror})
        check("valid override: loaded from it", r["t2"].startswith(alt_mirror) and r["marker"] == "override", r)
        check("valid override: siblings from it", all(r[k].startswith(alt_mirror) for k in ("sd", "v1", "sds")), r)
        r = run(r"""
T = V._load()
os.environ["KAM_V2_DIR"] = sys.argv[2]
U = V._load()
out.update(a=T.__file__, b=U.__file__)
print(json.dumps(out))
""".replace("sys.argv[2]", repr(alt_mirror)), root)
        check("override set later: not the memoized default", r["a"].startswith(mirror) and r["b"].startswith(alt_mirror), r)

        # 5. invalid overrides
        empty = os.path.join(tmp, "empty"); os.makedirs(empty)
        for name, d in (("missing", os.path.join(tmp, "nowhere")), ("no mirror", empty), ("empty string", "")):
            r = run(BAD, root, {"KAM_V2_DIR": d})
            msg = r["raised"] or ""
            check("invalid override (%s): clear error" % name,
                  "KAM_V2_DIR" in msg and "thresholds_v2.py" in msg and (d in msg), r)
            check("invalid override (%s): sys.path restored" % name, r["path_ok"], r)

        # 6. a mirror that fails during import, after extending sys.path
        broken = os.path.join(tmp, "broken"); os.makedirs(broken)
        with open(os.path.join(broken, "thresholds_v2.py"), "w", encoding="utf-8") as f:
            f.write('import sys\nsys.path.insert(0, "/extended/by/the/mirror")\nimport thresholds\nraise RuntimeError("boom")\n')
        with open(os.path.join(broken, "thresholds.py"), "w", encoding="utf-8") as f:
            f.write("X = 1\n")
        r = run(r"""
sentinel = types.ModuleType("thresholds"); sys.modules["thresholds"] = sentinel
try:
    V._load()
    out.update(raised=None)
except ImportError as e:
    out.update(raised=str(e))
out.update(path_ok=sys.path == before, cached="thresholds_v2" in sys.modules, kept=sys.modules.get("thresholds") is sentinel)
print(json.dumps(out))
""", root, {"KAM_V2_DIR": broken})
        check("failing import: clear error", "boom" in (r["raised"] or "") and broken in r["raised"], r)
        check("failing import: sys.path and sys.modules restored", r["path_ok"] and r["kept"] and not r["cached"], r)

    print("v2_adapter checks:", "all passed" if not fails else "FAILED: %s" % ", ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""V2-PACKED-GEN: the run harness of the packed modules (untrusted tooling).

Builds target modules of the scratch package (`gen_pkg.py`, `gen_packed.py`) bottom-up, ONE Lean process at a time,
each `lake build <module>` alone (its imports are built first, so Lake compiles exactly one module) in a capped scope:
  systemd-run --user --scope -p MemoryMax=CAP -p MemorySwapMax=0, nice -n 5, LEAN_NUM_THREADS=1, /usr/bin/time -v,
  the scope's cgroup charge sampled every 0.2 s.
Before each start: the user cgroup's anonymous memory (memory.stat of user-1004.slice) at most 20 GB (else wait: an
LG00 kernel run holds up to 3 processes) and at least 30 GB free on / (else stop: `BLOCKED disk`).
The module list: the targets and their imports inside the package (`public import LG00*`), in dependency order.
The modules Lake finds up to date (LG00 modules reused from LG00's run, or built earlier) are found by one batched
`lake build --no-build` (bisected to the few stale ones) and get a ledger row of kind `reused`, with no cost.
Ledger (LOGDIR/ledger.tsv, one row per module, appended): module, user s, sys s, wall, max RSS kB, cgroup peak
bytes, exit, kind (`built` | `reused`), kernel s (the sum of the profiler's `type checking took` lines: the
`LG00Packed` modules only), cap. Resumable: a module whose last row has exit 0 is skipped. A failed module's
dependants are not started; the run goes on with the others and stops when nothing is left.
Usage: python3 -I scripts/packed/run_packed.py LOGDIR CAP TARGET_MODULE... [--pkg DIR] [--dry]
       python3 -I scripts/packed/run_packed.py --summary LOGDIR      (totals per stage)
"""
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CORE = os.path.abspath(os.path.join(HERE, "..", ".."))
PKG = os.path.join(CORE, ".lake", "lg00-packed")
CG = "/sys/fs/cgroup/user.slice/user-%d.slice/memory.stat" % os.getuid()
LG00_CORE = "/home/scott/KAM-dev-worktrees/lg00-app"     # the core LG00's reused artifacts were built against
ANON_MAX = 20 * 10 ** 9
MIN_DISK = 30
IMP = re.compile(r"^public import (\S+)", re.M)

PROBE = r'''
cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
pkf="$2.peak"
( pk=0; while true; do c=$(cat $cg/memory.current 2>/dev/null || echo 0); [ "$c" -gt "$pk" ] && pk=$c;
    echo $pk > "$pkf"; sleep 0.2; done ) &
smp=$!
LEAN_NUM_THREADS=1 /usr/bin/time -v nice -n 5 lake build "$1" > "$2" 2> "$2.time"
echo "exit $?" >> "$2.time"
kill $smp 2>/dev/null
echo "cgroup_sampled_peak_bytes $(cat "$pkf")" >> "$2.time"; rm -f "$pkf"
echo "oom_kill $(grep oom_kill $cg/memory.events | awk '{print $2}')" >> "$2.time"
'''


def src(pkg, m):
    return os.path.join(pkg, *m.split(".")) + ".lean"


def order(pkg, targets):
    """The targets and their package imports, dependencies first."""
    seen, out = set(), []

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in IMP.findall(open(src(pkg, m), encoding="utf-8").read()):
            if d.split(".")[0] in ("LG00", "LG00Packed") and os.path.exists(src(pkg, d)):
                visit(d)
        out.append(m)
    sys.setrecursionlimit(100000)
    for t in targets:
        visit(t)
    return out


def no_build(pkg, mods):
    r = subprocess.run(["lake", "build", "--no-build"] + list(mods), cwd=pkg, capture_output=True, text=True)
    return r.returncode == 0


def stale_set(pkg, mods):
    """The modules Lake would rebuild (one batched `--no-build` check, bisected; stale modules are few)."""
    mods = list(mods)
    if not mods or no_build(pkg, mods):
        return set()
    if len(mods) == 1:
        return set(mods)
    h = len(mods) // 2
    return stale_set(pkg, mods[:h]) | stale_set(pkg, mods[h:])


def predict_stale(pkg, mods, deps, lg00_core):
    """The modules Lake will rebuild, predicted from the import graph: a module is stale if its olean is missing,
    if it imports a stale package module, or if it imports (transitively) a core module whose source differs from
    the core LG00's artifacts were built against (`lg00_core`, the `lg00-app` worktree)."""
    changed = {}

    def core_changed(m):
        if m in changed:
            return changed[m]
        changed[m] = False
        path = os.path.join(CORE, *m.split(".")) + ".lean"
        if not os.path.exists(path):          # Mathlib / other packages: shared, unchanged
            return False
        other = os.path.join(lg00_core, *m.split(".")) + ".lean"
        res = not os.path.exists(other) or open(path, "rb").read() != open(other, "rb").read()
        if not res:
            res = any(core_changed(d) for d in IMP.findall(open(path, encoding="utf-8").read()))
        changed[m] = res
        return res
    stale = set()
    for m in mods:                            # dependency order
        olean = os.path.join(pkg, ".lake", "build", "lib", "lean", *m.split(".")) + ".olean"
        imps = IMP.findall(open(src(pkg, m), encoding="utf-8").read())
        ours = m.split(".")[0] in ("LG00Packed", "LG00P")     # built here, against this core
        if not os.path.exists(olean) or any(d in stale for d in deps[m]) or (not ours and any(
                core_changed(d) for d in imps if d.split(".")[0] not in ("LG00", "LG00Packed", "LG00P"))):
            stale.add(m)
    return stale


def anon():
    try:
        return int(dict(l.split() for l in open(CG)).get("anon", 0))
    except (OSError, ValueError):
        return 0


def free_gb():
    return shutil.disk_usage("/").free // 10 ** 9


def row(m, log, kind, cap):
    t = open(log + ".time").read() if os.path.exists(log + ".time") else ""
    out = open(log).read() if os.path.exists(log) else ""

    def g(pat):
        x = re.search(pat, t, re.M)
        return x.group(1) if x else "?"
    own = re.search(r"Built %s \(.*?\n(.*?)(?=\n\S+ \[\d+/\d+\]|\Z)" % re.escape(m), out, re.S)
    kern = sum(float(v) * (0.001 if u == "ms" else 1.0)          # the module's own lines (Lake replays others)
               for v, u in re.findall(r"type checking took ([0-9.]+)(m?s)", own.group(1) if own else ""))
    return "\t".join([m, g(r"User time \(seconds\): (\S+)"), g(r"System time \(seconds\): (\S+)"),
                      g(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"),
                      g(r"Maximum resident set size \(kbytes\): (\S+)"), g(r"cgroup_sampled_peak_bytes (\S+)"),
                      g(r"^exit (\S+)"), kind, "%.2f" % kern, cap])


def stage_of(m):
    """The stage of a module, for the summary: the packed modules by their first component after the tree, the
    LG00 modules by theirs (`Data`, `Final`, `Balls`, …), with the `Final` sites and the refined core apart."""
    parts = m.split(".")
    if parts[0] == "LG00Packed" or (len(parts) > 2 and parts[2] == "PK"):
        rest = parts[2:] if parts[0] == "LG00Packed" else parts[3:]
        head = rest[0] if rest else "Format"
        return "packed." + ("Frames" if head.startswith("Frame") else head)
    if len(parts) > 2 and parts[2] == "Final":
        last = parts[3] if len(parts) > 3 else ""
        if last.startswith(("Site", "RC", "RefinedCore")):
            return "landed.Final.sites"
        if last.startswith(("HC", "HamClaim")):
            return "landed.Final.hamClaim"
        return "landed.Final.other"
    if len(parts) > 2 and parts[1] in ("TP", "TPP"):
        return "landed." + parts[2]
    return "landed.shared"


def summary(logdir):
    """Totals per stage from the ledger (the last row of each module), kernel times re-read from the logs."""
    rows = {}
    for l in open(os.path.join(logdir, "ledger.tsv")):
        f = l.rstrip("\n").split("\t")
        rows[f[0]] = f
    tot = {}
    for m, f in rows.items():
        st = stage_of(m)
        t = tot.setdefault(st, dict(built=0, reused=0, cpu=0.0, kern=0.0, peak=0, failed=0))
        if f[7] == "reused":
            t["reused"] += 1
            continue
        t["built"] += 1
        t["failed"] += f[6] != "0"
        t["cpu"] += float(f[1]) + float(f[2])
        log = os.path.join(logdir, m + ".log")
        if os.path.exists(log):
            t["kern"] += float(row(m, log, "built", "")[:-1].split("\t")[8])
        t["peak"] = max(t["peak"], int(f[5]) if f[5].isdigit() else 0)
    print("%-26s %6s %6s %9s %9s %8s %6s" % ("stage", "built", "reused", "CPU-s", "kernel-s", "peak GB", "failed"))
    for st in sorted(tot):
        t = tot[st]
        print("%-26s %6d %6d %9.1f %9.1f %8.2f %6d" % (st, t["built"], t["reused"], t["cpu"], t["kern"],
                                                       t["peak"] / 1e9, t["failed"]))
    a = {k: sum(t[k] for t in tot.values()) for k in ("built", "reused", "cpu", "kern", "failed")}
    print("%-26s %6d %6d %9.1f %9.1f %8.2f %6d" % ("total", a["built"], a["reused"], a["cpu"], a["kern"],
                                                   max(t["peak"] for t in tot.values()) / 1e9, a["failed"]))
    return tot


def main():
    args = sys.argv[1:]
    if args and args[0] == "--summary":
        summary(os.path.abspath(args[1]))
        return 0
    pkg = PKG
    if "--pkg" in args:
        i = args.index("--pkg")
        pkg = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    dry = "--dry" in args
    args = [a for a in args if a != "--dry"]
    logdir, cap, targets = os.path.abspath(args[0]), args[1], args[2:]
    os.makedirs(logdir, exist_ok=True)
    ledger = os.path.join(logdir, "ledger.tsv")
    mods = order(pkg, targets)
    deps = {m: [d for d in IMP.findall(open(src(pkg, m), encoding="utf-8").read()) if d in set(mods)]
            for m in mods}
    done, failed = set(), set()
    if os.path.exists(ledger):
        for l in open(ledger):
            f = l.rstrip("\n").split("\t")
            if len(f) >= 7:
                (done.add if f[6] == "0" else done.discard)(f[0])
    print("%d modules, %d already passed" % (len(mods), len(done)), flush=True)
    core = sorted({d for m in mods for d in IMP.findall(open(src(pkg, m), encoding="utf-8").read())
                   if d.split(".")[0] not in ("LG00", "LG00Packed")})
    r = subprocess.run(["lake", "build", "--no-build"] + core, cwd=CORE, capture_output=True, text=True)
    if r.returncode != 0:
        print("STOP: core modules out of date (build them in the core worktree, one at a time):\n" +
              "\n".join(l for l in r.stdout.splitlines() if "✖" in l or l.startswith("- ")), flush=True)
        return 2
    if dry:
        for m in mods:
            print(m, "passed" if m in done else "")
        return 0
    todo = [m for m in mods if m not in done]
    stale = predict_stale(pkg, todo, deps, LG00_CORE)
    fresh = [m for m in todo if m not in stale]
    if fresh and not no_build(pkg, fresh):     # the prediction is checked by Lake; bisect if it was wrong
        stale |= stale_set(pkg, fresh)
    print("%d to do, %d stale (to build), %d up to date (reused)" % (len(todo), len(stale), len(todo) - len(stale)),
          flush=True)
    for m in todo:
        if m not in stale:
            open(ledger, "a").write("\t".join([m, "0", "0", "0", "0", "0", "0", "reused", "0", cap]) + "\n")
            done.add(m)
    for m in mods:
        if m in done:
            continue
        if any(d in failed for d in deps[m]):
            failed.add(m)
            print("SKIP (a dependency failed) %s" % m, flush=True)
            continue
        while anon() > ANON_MAX:
            time.sleep(30)
        if free_gb() < MIN_DISK:
            print("V2-PACKED-GEN BLOCKED disk (%d GB free)" % free_gb(), flush=True)
            return 3
        log = os.path.join(logdir, m + ".log")
        subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=%s" % cap, "-p",
                        "MemorySwapMax=0", "bash", "-c", PROBE, "_", m, log], cwd=pkg)
        built = re.search(r"Built %s\b" % re.escape(m), open(log).read()) if os.path.exists(log) else None
        r = row(m, log, "built" if built else "reused", cap)
        open(ledger, "a").write(r + "\n")
        print(r, flush=True)
        if r.split("\t")[6] == "0":
            done.add(m)
        else:
            failed.add(m)
    print("DONE: %d passed, %d failed %s" % (len(done & set(mods)), len(failed), sorted(failed)[:10]), flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""V2-PACKED-GEN: the run harness of the packed modules (untrusted tooling).

Builds target modules of the scratch package (`gen_pkg.py`, `gen_packed.py`) bottom-up, ONE Lean process at a time,
each `lake build <module>` alone (its imports are built first, so Lake compiles exactly one module) in a capped scope:
  systemd-run --user --scope -p MemoryMax=CAP -p MemorySwapMax=0, nice -n 5, LEAN_NUM_THREADS=1, /usr/bin/time -v,
  the scope's cgroup charge sampled every 0.2 s.
Before each start: the user cgroup's anonymous memory (memory.stat of user-1004.slice) at most 20 GB (else wait: an
LG00 kernel run holds up to 3 processes) and at least 30 GB free on / (else stop: `BLOCKED disk`).
The module list: the targets and their imports inside the package (`public import LG00*`), in dependency order.
A module that `lake build --no-build` reports up to date (an LG00 module reused from LG00's run, or one built
earlier) gets a ledger row of kind `reused` and no cost.
Ledger (LOGDIR/ledger.tsv, one row per module, appended): module, user s, sys s, wall, max RSS kB, cgroup peak
bytes, exit, kind (`built` | `reused`), kernel s (the sum of the profiler's `type checking took` lines: the
`LG00Packed` modules only), cap. Resumable: a module whose last row has exit 0 is skipped. A failed module's
dependants are not started; the run goes on with the others and stops when nothing is left.
Usage: python3 -I scripts/packed/run_packed.py LOGDIR CAP TARGET_MODULE... [--pkg DIR] [--dry]
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


def anon():
    try:
        return int(dict(l.split() for l in open(CG)).get("anon", 0))
    except (OSError, ValueError):
        return 0


def free_gb():
    return shutil.disk_usage("/").free // 10 ** 9


def up_to_date(pkg, m):
    r = subprocess.run(["lake", "build", "--no-build", m], cwd=pkg, capture_output=True, text=True)
    return r.returncode == 0


def row(m, log, kind, cap):
    t = open(log + ".time").read() if os.path.exists(log + ".time") else ""
    out = open(log).read() if os.path.exists(log) else ""

    def g(pat):
        x = re.search(pat, t, re.M)
        return x.group(1) if x else "?"
    kern = sum(float(v) * (0.001 if u == "ms" else 1.0)
               for v, u in re.findall(r"type checking took ([0-9.]+)(m?s)", out))
    return "\t".join([m, g(r"User time \(seconds\): (\S+)"), g(r"System time \(seconds\): (\S+)"),
                      g(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"),
                      g(r"Maximum resident set size \(kbytes\): (\S+)"), g(r"cgroup_sampled_peak_bytes (\S+)"),
                      g(r"^exit (\S+)"), kind, "%.2f" % kern, cap])


def main():
    args = sys.argv[1:]
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
    for m in mods:
        if m in done:
            continue
        if any(d in failed for d in deps[m]):
            failed.add(m)
            print("SKIP (a dependency failed) %s" % m, flush=True)
            continue
        if up_to_date(pkg, m):
            r = "\t".join([m, "0", "0", "0", "0", "0", "0", "reused", "0", cap])
            open(ledger, "a").write(r + "\n")
            done.add(m)
            continue
        while anon() > ANON_MAX:
            time.sleep(30)
        if free_gb() < MIN_DISK:
            print("V2-PACKED-GEN BLOCKED disk (%d GB free)" % free_gb(), flush=True)
            return 3
        log = os.path.join(logdir, m + ".log")
        subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=%s" % cap, "-p",
                        "MemorySwapMax=0", "bash", "-c", PROBE, "_", m, log], cwd=pkg)
        r = row(m, log, "built", cap)
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

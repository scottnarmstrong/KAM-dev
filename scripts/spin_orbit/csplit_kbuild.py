#!/usr/bin/env python3
"""SO-CSEG-GEN: build the segmented proof serially (untrusted tooling; restartable).

    python3 csplit_kbuild.py LOGDIR ROOTMODULE [ROOTMODULE ...]

Walks the import closure of the root modules inside `KAM.SpinOrbit.Data` in topological order. A module listed
in a `heavy_modules.txt` (the generator's list, plus `KAM.SpinOrbit.Data.CsegJetEq` and the `Pass/*` modules) is
built ALONE under the kernel-probe lock with `MemoryMax=10G`, `MemorySwapMax=0` (`lake build M`; its imports are
already built, so only M is elaborated); every other module goes through the compile gate. A module that lake reports
up to date (`lake build --no-build`) is skipped. One line per module is appended to LOGDIR/kbuild.tsv:
module, kind, rc, wall seconds, max RSS (kB).  Stops at the first failure (rc != 0) or when / has < 6 GB free.
"""
import os
import re
import shutil
import subprocess
import sys
import time

WT = "/root/code/KAM-inp-sodata3"
LOCK = os.environ.get("CSPLIT_LOCK", "/mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock")
MEMMAX = os.environ.get("CSPLIT_MEMMAX", "10G")
MINAVAIL = int(os.environ.get("CSPLIT_MINAVAIL_GB", "0")) * 10 ** 9   # lane 2: wait while MemAvailable is lower
# modules measured above a lane's cap (the l = 12 bite: 9.5 GB) run under the SHARED probe lock at 10G, i.e.
# serialized with lane 1, never beside another capped run
BIG = [x for x in os.environ.get("CSPLIT_BIG", "").split(",") if x]
SHARED_LOCK = "/mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock"
GATE = "/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh"
FLOOR = 6 * 10 ** 9


def path_of(m):
    return os.path.join(WT, *m.split(".")) + ".lean"


def olean_of(m):
    return os.path.join(WT, ".lake", "build", "lib", "lean", *m.split(".")) + ".olean"


def imports(m):
    out = []
    for l in open(path_of(m)):
        r = re.match(r"\s*(?:public\s+)?import\s+(\S+)", l)
        if r and r.group(1).startswith("KAM.SpinOrbit.Data.") and os.path.exists(path_of(r.group(1))):
            out.append(r.group(1))
    return out


def topo(roots):
    seen, order = set(), []

    def go(m):
        stack = [(m, iter(imports(m)))]
        seen.add(m)
        while stack:
            cur, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                order.append(cur)
                stack.pop()
            elif nxt not in seen:
                seen.add(nxt)
                stack.append((nxt, iter(imports(nxt))))
    for r in roots:
        if r not in seen:
            go(r)
    return order


def heavy_set():
    h = {"KAM.SpinOrbit.Data.CsegJetEq"}
    for T in ("Lower", "Upper"):
        f = os.path.join(WT, "KAM", "SpinOrbit", "Data", T, "Seg", "heavy_modules.txt")
        if os.path.exists(f):
            h |= {l.strip() for l in open(f) if l.strip()}
        pd = os.path.join(WT, "KAM", "SpinOrbit", "Data", T, "Pass")
        if os.path.isdir(pd):
            h |= {"KAM.SpinOrbit.Data.%s.Pass.%s" % (T, x[:-5]) for x in os.listdir(pd) if x.endswith(".lean")}
    return h


def mem_available():
    for l in open("/proc/meminfo"):
        if l.startswith("MemAvailable:"):
            return int(l.split()[1]) * 1024
    return 0


def up_to_date(m):
    """lake's own verdict (a stale import makes a module stale even if its source is unchanged)."""
    o = olean_of(m)
    if not os.path.exists(o):
        return False
    return subprocess.call(["lake", "build", "--no-build", m], cwd=WT, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL) == 0


def main(logdir, roots):
    os.makedirs(logdir, exist_ok=True)
    heavy = heavy_set()
    order = topo(roots)
    tsv = open(os.path.join(logdir, os.environ.get("CSPLIT_TSV", "kbuild.tsv")), "a")
    print(len(order), "modules,", sum(1 for m in order if m in heavy), "heavy", flush=True)
    for m in order:
        if up_to_date(m):
            continue
        while m in heavy and MINAVAIL and mem_available() < MINAVAIL:
            time.sleep(30)
        if shutil.disk_usage("/").free < FLOOR:
            print("STOP: / below 6 GB", flush=True)
            return 2
        log = os.path.join(logdir, m + ".log")
        t0 = time.time()
        if m in heavy:
            kind = "heavy"
            big = any(m.endswith(b) for b in BIG)
            cmd = ["flock", SHARED_LOCK if big else LOCK, "systemd-run", "--user", "--scope", "-p",
                   "MemoryMax=" + ("10G" if big else MEMMAX), "-p",
                   "MemorySwapMax=0", "/usr/bin/time", "-v", "nice", "-n", "5", "lake", "build", m]
        else:
            kind = "light"
            cmd = [GATE, WT, m]
        with open(log, "w") as fh:
            rc = subprocess.call(cmd, cwd=WT, stdout=fh, stderr=subprocess.STDOUT)
        dt = time.time() - t0
        rss = ""
        for l in open(log):
            if "Maximum resident set size" in l:
                rss = l.split()[-1]
        tsv.write("%s\t%s\t%d\t%.1f\t%s\n" % (m, kind, rc, dt, rss))
        tsv.flush()
        print("%s %s rc=%d %.0fs %skB" % (kind, m, rc, dt, rss), flush=True)
        if rc != 0:
            print("STOP: failure", flush=True)
            return 1
    print("DONE", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2:]))

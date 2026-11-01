#!/usr/bin/env python3
"""LOCK-DATA: multi-lane kernel driver for the lock's modules (untrusted tooling; LOCK-REMOTE step 4).

`lock_kbuild.sh` generalized to L lanes:

* the modules are the import closure of the TARGETS within `KAM.SpinOrbit.Data.LockN65` (sources read from the
  worktree), in topological order;
* a module starts only when every module it imports is done (rc 0), the lane count allows, and MemAvailable is at
  least LOCK_GATE kB;
* each module is ONE `lake build <module>` in its own scope (`MemoryMax=LOCK_MEM`, `MemorySwapMax=0`,
  `LEAN_NUM_THREADS=1`, nice 5), so Lake builds only that module;
* a failure does not stop the run: its dependents are recorded as skipped, independent modules continue;
* per-module logs `LOGDIR/<module>.log` and one summary line per module on stdout, in `lock_kbuild.sh`'s format
  (`<module> rc=… cpu=… wall=… peak=… oom=… lane=…`), then a final tally.

    LOCK_MEM=10G LOCK_GATE=12582912 python3 lock_mlane.py LOGDIR LANES TARGET [TARGET ...]
    (TARGET: a module name, or @FILE with one module per line)

Mixed lanes (this machine): LOCK_HEAVY=FILE (one module per line) sends those modules to LOCK_HEAVY_LANES (default 1)
heavy lanes with LOCK_HEAVY_MEM (default 10G) and LOCK_HEAVY_GATE kB (default 12 GiB); every other module runs on
the LANES light lanes (LOCK_MEM, LOCK_GATE).  With LOCK_RETRY_HEAVY=1 a light module killed by its cap is retried
once on a heavy lane.  LOCK_DONE=FILE marks the listed modules done (verify them first with one
`lake build --no-build $(cat FILE)`, rc 0).

Already-built modules are rebuilt by Lake only if their traces changed (a replay takes a few seconds).
"""
import os
import re
import subprocess
import sys
import threading
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
PFX = "KAM.SpinOrbit.Data.LockN65"
IMP = re.compile(r"^(?:public )?import (\S+)", re.M)
MISSING = []


def src(m):
    return os.path.join(ROOT, *m.split(".")) + ".lean"


def closure(targets):
    deps, order, seen = {}, [], set()
    stack = [(t, False) for t in reversed(targets)]
    while stack:
        m, done = stack.pop()
        if done:
            order.append(m)
            continue
        if m in seen:
            continue
        seen.add(m)
        if not os.path.exists(src(m)):
            print("MISSING source %s" % m, flush=True)
            MISSING.append(m)
            continue
        ds = [i for i in IMP.findall(open(src(m)).read()) if i.startswith(PFX)]
        deps[m] = ds
        stack.append((m, True))
        stack.extend((d, False) for d in reversed(ds) if d not in seen)
    return order, deps


def mem_available_kb():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable"):
            return int(line.split()[1])
    return 0


def run(m, logdir, lane, mem=None):
    mem = mem or os.environ.get("LOCK_MEM", "10G")
    log = os.path.join(logdir, m + ".log")
    head = subprocess.run("date -u; git -C %s rev-parse HEAD; df -h / | tail -1" % ROOT, shell=True,
                          capture_output=True, text=True).stdout
    script = ('cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); '
              '/usr/bin/time -v nice -n 5 env LEAN_NUM_THREADS=1 lake build %s; rc=$?; '
              'echo "MEMPEAK $(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED)"; '
              'echo "OOMKILL $(grep oom_kill $cg/memory.events 2>/dev/null | awk \'{print $2}\')"; '
              'echo "rc=$rc"' % m)
    with open(log, "w") as f:
        f.write(head + "lane %s mem %s\n" % (lane, mem))
        f.flush()
        subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" + mem,
                        "-p", "MemorySwapMax=0", "bash", "-c", script], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
    t = open(log).read()

    def grab(pat):
        r = re.findall(pat, t, re.M)
        return r[-1] if r else ""
    rc = grab(r"^rc=(\S+)") or "OOM-or-killed"
    u, s = grab(r"User time \(seconds\): (\S+)"), grab(r"System time \(seconds\): (\S+)")
    cpu = "%.2f" % (float(u) + float(s)) if u and s else ""
    line = "%s rc=%s cpu=%s wall=%s peak=%s oom=%s lane=%s" % (
        m, rc, cpu, grab(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"), grab(r"^MEMPEAK (\S+)"),
        grab(r"^OOMKILL (\S+)"), lane)
    return rc == "0", line


def main(argv):
    logdir, lanes = argv[0], int(argv[1])
    targets = []
    for t in argv[2:]:
        targets += [l.strip() for l in open(t[1:]) if l.strip()] if t.startswith("@") else [t]
    os.makedirs(logdir, exist_ok=True)
    order, deps = closure(targets)
    if MISSING:
        print("missing sources: %d (first: %s); not building" % (len(MISSING), MISSING[0]), flush=True)
        return 2
    gate = int(os.environ.get("LOCK_GATE", "8388608"))
    heavy = set()
    if os.environ.get("LOCK_HEAVY"):
        heavy = {l.strip() for l in open(os.environ["LOCK_HEAVY"]) if l.strip()}
    hmem = os.environ.get("LOCK_HEAVY_MEM", "10G")
    hgate = int(os.environ.get("LOCK_HEAVY_GATE", "12582912"))
    hfree = ["H%d" % i for i in range(1, int(os.environ.get("LOCK_HEAVY_LANES", "1")) + 1)] if heavy else []
    retry = os.environ.get("LOCK_RETRY_HEAVY") == "1" and bool(heavy)
    state = {m: "todo" for m in order}            # todo / run / ok / fail / skip
    if os.environ.get("LOCK_DONE"):
        # modules already verified up to date (one batch `lake build --no-build …` rc 0): not re-invoked
        done = {l.strip() for l in open(os.environ["LOCK_DONE"]) if l.strip()}
        for m in order:
            if m in done:
                state[m] = "ok"
        print("pre-verified up to date: %d" % sum(1 for m in order if m in done), flush=True)
    lock = threading.Lock()
    free = list(range(1, lanes + 1))
    print("modules %d lanes %d mem %s gate %d kB" % (len(order), lanes, os.environ.get("LOCK_MEM", "10G"), gate),
          flush=True)
    if os.environ.get("LOCK_DRY") == "1":
        # the schedule only: topological levels (a module's level = 1 + its deepest import), no builds
        lv = {}
        for m in order:
            lv[m] = 1 + max([lv[d] for d in deps[m]], default=-1)
        width = {}
        for m in order:
            width[lv[m]] = width.get(lv[m], 0) + 1
        print("levels %d widest %d" % (len(width), max(width.values()) if width else 0))
        for m in order:
            print("%d %s" % (lv[m], m))
        return 0

    def worker(m, lane):
        isH = isinstance(lane, str)
        ok, line = run(m, logdir, lane, hmem if isH else None)
        with lock:
            (hfree if isH else free).append(lane)
            if not ok and not isH and retry and ("OOM" in line or "oom=1" in line):
                heavy.add(m)
                state[m] = "todo"
                print(line + " (retry on a heavy lane)", flush=True)
                return
            state[m] = "ok" if ok else "fail"
            print(line, flush=True)

    while True:
        with lock:
            # dependents of a failed or skipped module are skipped
            for m in order:
                if state[m] == "todo" and any(state[d] in ("fail", "skip") for d in deps[m]):
                    state[m] = "skip"
                    print("%s rc=SKIP (a dependency failed)" % m, flush=True)
            ready = [m for m in order if state[m] == "todo" and all(state[d] == "ok" for d in deps[m])]
            running = sum(1 for m in order if state[m] == "run")
            if not ready and running == 0:
                break
            launch = []
            for m in [x for x in ready if x in heavy]:
                if not hfree or mem_available_kb() < hgate:
                    break
                state[m] = "run"
                launch.append((m, hfree.pop(0)))
            ready = [x for x in ready if x not in heavy]
            while ready and free and mem_available_kb() >= gate:
                m = ready.pop(0)
                lane = free.pop(0)
                state[m] = "run"
                launch.append((m, lane))
        for m, lane in launch:
            threading.Thread(target=worker, args=(m, lane), daemon=True).start()
            time.sleep(2)          # let the new scope's memory show before the next gate check
        time.sleep(5)
    tally = {k: sum(1 for v in state.values() if v == k) for k in ("ok", "fail", "skip", "todo")}
    print("done %s ok=%d fail=%d skip=%d todo=%d" % (time.strftime("%H:%M:%S", time.gmtime()), tally["ok"],
                                                     tally["fail"], tally["skip"], tally["todo"]), flush=True)
    return 0 if tally["fail"] == 0 and tally["skip"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

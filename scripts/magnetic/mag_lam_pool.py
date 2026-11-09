#!/usr/bin/env python3
"""MAG-LAM: build the magnetic certificate chain on a big machine (untrusted tooling; derived from
scripts/spin_orbit/remote_pool.py and lock_mlane.py).

    mag_lam_pool.py ROOT LOGDIR LANES TARGET [TARGET ...]

* The modules are the import closure of the TARGETS within `KAM.Magnetic.Data` (sources under ROOT), each built by
  ONE `lake build <module>` in its own systemd scope (`MemoryMax=cap`, `MemorySwapMax=0`, `LEAN_NUM_THREADS=1`,
  nice 5), starting only when every import is done and MemAvailable >= cap + 2 GB.
* Caps come from COMPLETED runs only. The modules listed in MAG_PROBES (env, comma separated) are built first at
  MAG_PROBE_CAP (default 48G). A module of a probed class (`classify`) starts once ONE probe of its class has
  completed with rc 0; its cap is ceil(1.3 x the largest completed probe peak of the class), at least MAG_CAP_FLOOR
  (default 5G). Other modules get MAG_DEFAULT_CAP (default 16G). A module killed at its cap (oom) is retried once
  at MAG_PROBE_CAP; a probe that does not finish with rc 0 (killed, failed or timed out) stops the run (STOP line).
* MAG_TIMEOUT (default 1800 s): the wall-clock limit of one module (per class: MAG_TIMEOUTS, default `Prod:5400`;
  the product assembly M0 measured 636 s at the 10 GB cap); past it the build's process group is killed and the
  module is recorded with the distinct rc=TIMEOUT (a hang is not filed as an OOM; no retry).
* A cap kill records the cap itself as the (lower-bound) peak when the cgroup is gone before its peak is read.
* MAG_DONE=FILE: modules already verified up to date (one `lake build --no-build $(cat FILE)`, rc 0): not
  re-invoked.
* A module passes iff `lake build` returns 0. Failures do not stop the run: dependents are skipped.
* Outputs: LOGDIR/<module>.log, LOGDIR/results.tsv (module, rc, verdict, wall_s, peak_bytes, cap, oom, attempt,
  olean_sha256, lane), LOGDIR/STATUS (rewritten every minute), and a final `done … ok= fail= skip= todo=` line.
* MAG_DRY=1: the closure, the classes and the levels only.
"""
import hashlib
import math
import os
import re
import subprocess
import sys
import threading
import time

PFX = "KAM.Magnetic.Data"
IMP = re.compile(r"^(?:public )?import (\S+)", re.M)
PROBE_CAP = os.environ.get("MAG_PROBE_CAP", "48G")
DEFAULT_CAP = os.environ.get("MAG_DEFAULT_CAP", "16G")
CAP_FLOOR = int(os.environ.get("MAG_CAP_FLOOR", "5"))
TIMEOUT = int(os.environ.get("MAG_TIMEOUT", "1800"))
TIMEOUTS = {c: int(t) for c, t in (x.split(":") for x in os.environ.get("MAG_TIMEOUTS", "Prod:5400").split(",") if x)}
CLASSES = [("ShG", re.compile(r"\.Seg\.Prod\.M\d+ShG\d+$")), ("Sh", re.compile(r"\.Seg\.Prod\.M\d+Sh$")),
           ("DecW", re.compile(r"\.Seg\.Prod\.M\d+DecW$")),
           ("DecP", re.compile(r"\.Seg\.Prod\.M\d+DecP\d+$")), ("Dec", re.compile(r"\.Seg\.Prod\.M\d+Dec$")),
           ("Prod", re.compile(r"\.Seg\.Prod\.M\d+$")), ("RemR", re.compile(r"\.Seg\.Prod\.M\d+RemR\d+$")),
           ("Full", re.compile(r"\.Seg\.Full\.S\d+$")), ("Low", re.compile(r"\.Seg\.Low\.S\d+$"))]


def classify(m):
    for c, r in CLASSES:
        if r.search(m):
            return c
    return None


def gb(cap):
    assert cap.endswith("G"), cap
    return int(cap[:-1])


def src(root, m):
    return os.path.join(root, *m.split(".")) + ".lean"


def olean(root, m):
    return os.path.join(root, ".lake", "build", "lib", "lean", *m.split(".")) + ".olean"


def closure(root, targets):
    deps, order, seen, missing = {}, [], set(), []
    stack = [(t, False) for t in reversed(targets)]
    while stack:
        m, done = stack.pop()
        if done:
            order.append(m)
            continue
        if m in seen:
            continue
        seen.add(m)
        if not os.path.exists(src(root, m)):
            missing.append(m)
            continue
        ds = [i for i in IMP.findall(open(src(root, m)).read()) if i.startswith(PFX + ".")]
        deps[m] = ds
        stack.append((m, True))
        stack.extend((d, False) for d in reversed(ds) if d not in seen)
    return order, deps, missing


def mem_available_kb():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable"):
            return int(line.split()[1])
    return 0


def sha(path):
    h = hashlib.sha256()
    try:
        with open(path, "rb") as f:
            for b in iter(lambda: f.read(1 << 20), b""):
                h.update(b)
    except OSError:
        return ""
    return h.hexdigest()


def build(root, m, logdir, lane, cap):
    log = os.path.join(logdir, m + ".log")
    tmo = TIMEOUTS.get(classify(m), TIMEOUT)
    script = ('cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); '
              '/usr/bin/time -v timeout -k 30 %d nice -n 5 env LEAN_NUM_THREADS=1 lake build %s; rc=$?; '
              'echo "MEMPEAK $(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED)"; '
              'echo "OOMKILL $(grep oom_kill $cg/memory.events 2>/dev/null | awk \'{print $2}\')"; '
              'echo "rc=$rc"' % (tmo, m))
    t0 = time.time()
    with open(log, "w") as f:
        f.write("%s lane %s cap %s\n" % (time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), lane, cap))
        f.flush()
        subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" + cap, "-p", "MemorySwapMax=0",
                        "bash", "-c", script], cwd=root, stdout=f, stderr=subprocess.STDOUT)
    wall = time.time() - t0
    t = open(log).read()

    def grab(pat):
        r = re.findall(pat, t, re.M)
        return r[-1] if r else ""
    rc = grab(r"^rc=(\S+)") or "killed"
    peak = grab(r"^MEMPEAK (\S+)")
    oom = grab(r"^OOMKILL (\S+)") not in ("", "0") or rc == "killed"
    if rc in ("124", "137") and wall >= tmo and not oom:
        rc = "TIMEOUT"          # `timeout` killed the process group: a hang, not a memory kill
    peak = int(peak) if peak.isdigit() else -1
    if oom and peak < 0:
        peak = gb(cap) * 2 ** 30    # the cgroup was torn down before its peak was read: the cap is a lower bound
    return rc, wall, peak, oom


def main(argv):
    root, logdir, lanes, targets = os.path.abspath(argv[0]), argv[1], int(argv[2]), argv[3:]
    os.makedirs(logdir, exist_ok=True)
    order, deps, missing = closure(root, targets)
    if missing:
        print("STOP: %d missing sources (first %s)" % (len(missing), missing[0]), flush=True)
        return 2
    probes = [p for p in os.environ.get("MAG_PROBES", "").split(",") if p]
    for p in probes:
        assert p in deps, "probe %s is not in the closure" % p
    done = set()
    if os.environ.get("MAG_DONE"):
        done = {l.strip() for l in open(os.environ["MAG_DONE"]) if l.strip()} & set(order)
    state = {m: ("ok" if m in done else "todo") for m in order}
    attempt = {m: 0 for m in order}
    lv = {}
    for m in order:
        lv[m] = 1 + max([lv[d] for d in deps[m]], default=-1)
    cls = {m: classify(m) for m in order}
    pcls = {cls[p] for p in probes}
    print("modules %d (pre-done %d, to build %d), levels %d, lanes %d, probes %d, classes %s" % (
        len(order), len(done), len(order) - len(done), max(lv.values()) + 1, lanes, len(probes),
        {c: sum(1 for m in order if cls[m] == c and m not in done) for c, _ in CLASSES}), flush=True)
    if os.environ.get("MAG_DRY") == "1":
        return 0
    peaks = {}                      # class -> [completed probe peaks]
    lock = threading.Lock()
    free = list(range(1, lanes + 1))
    stop = threading.Event()
    res = open(os.path.join(logdir, "results.tsv"), "a")
    t_start = time.time()

    def cap_of(m):
        if m in probes or attempt[m] > 0:
            return PROBE_CAP
        c = cls[m]
        if c in pcls:
            mx = max(peaks.get(c, [0]))
            return "%dG" % max(CAP_FLOOR, math.ceil(1.3 * mx / 2 ** 30))
        return DEFAULT_CAP

    def ready_cap(m):
        """the cap if m may start now, else None (no probe of its class has completed yet)"""
        if m in probes or attempt[m] > 0 or cls[m] not in pcls:
            return cap_of(m)
        if any(state[p] == "ok" for p in probes if cls[p] == cls[m]):
            return cap_of(m)
        return None

    def worker(m, lane, cap):
        rc, wall, peak, oom = build(root, m, logdir, lane, cap)
        digest = sha(olean(root, m)) if rc == "0" else ""
        with lock:
            free.append(lane)
            attempt[m] += 1
            line = "%s rc=%s wall=%.0fs peak=%.2fGB cap=%s oom=%d attempt=%d lane=%s" % (
                m, rc, wall, peak / 2 ** 30, cap, oom, attempt[m], lane)
            res.write("\t".join([m, rc, "pass" if rc == "0" else "fail", "%.1f" % wall, str(peak), cap,
                                 str(int(oom)), str(attempt[m]), digest, str(lane)]) + "\n")
            res.flush()
            if rc == "0":
                state[m] = "ok"
                if m in probes:
                    peaks.setdefault(cls[m], []).append(peak)
            elif m in probes:
                state[m] = "fail"
                print("STOP: probe %s did not finish (rc=%s%s) at %s" % (m, rc, ", oom" if oom else "", cap),
                      flush=True)
                stop.set()
            elif oom and attempt[m] == 1 and cap != PROBE_CAP:
                state[m] = "todo"
                line += " (retry at %s)" % PROBE_CAP
            else:
                state[m] = "fail"
            print(line, flush=True)

    last = 0
    prio = {m: (0 if m in probes else 1, lv[m]) for m in order}
    while not stop.is_set():
        launch = []
        with lock:
            for m in order:
                if state[m] == "todo" and any(state[d] in ("fail", "skip") for d in deps[m]):
                    state[m] = "skip"
                    print("%s rc=SKIP (a dependency failed)" % m, flush=True)
            ready = sorted((m for m in order if state[m] == "todo" and all(state[d] == "ok" for d in deps[m])),
                           key=lambda x: prio[x])
            running = sum(1 for v in state.values() if v == "run")
            if not ready and running == 0:
                break
            avail = mem_available_kb()
            for m in ready:
                if not free:
                    break
                cap = ready_cap(m)
                if cap is None:
                    continue
                if avail < (gb(cap) + 2) * 2 ** 20:
                    if m in probes:
                        break           # a probe waits for memory; nothing overtakes it
                    continue
                state[m] = "run"
                avail -= (gb(cap) + 2) * 2 ** 20
                launch.append((m, free.pop(0), cap))
        for m, lane, cap in launch:
            threading.Thread(target=worker, args=(m, lane, cap), daemon=True).start()
            time.sleep(1)
        if time.time() - last > 60:
            with lock:
                t = {k: sum(1 for v in state.values() if v == k) for k in ("ok", "fail", "skip", "todo", "run")}
                caps = {c: cap_of(next(m for m in order if cls[m] == c)) for c in pcls if c in peaks}
            open(os.path.join(logdir, "STATUS"), "w").write(
                "%s elapsed %.0f min %s caps %s MemAvailable %d GB\n" % (
                    time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()), (time.time() - t_start) / 60,
                    " ".join("%s=%d" % kv for kv in t.items()), caps, mem_available_kb() >> 20))
            last = time.time()
        time.sleep(3)
    while any(v == "run" for v in state.values()):
        time.sleep(5)
    t = {k: sum(1 for v in state.values() if v == k) for k in ("ok", "fail", "skip", "todo")}
    print("done %s ok=%d fail=%d skip=%d todo=%d wall=%.0fmin%s" % (
        time.strftime("%H:%M:%S", time.gmtime()), t["ok"], t["fail"], t["skip"], t["todo"],
        (time.time() - t_start) / 60, " (stopped)" if stop.is_set() else ""), flush=True)
    return 0 if t["fail"] + t["skip"] + t["todo"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

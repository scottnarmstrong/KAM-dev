#!/usr/bin/env python3
"""LOCK-REMOTE: one lane pool over several kernel chains (untrusted tooling; PKG-LOCK-DATA-RUN UPDATE 2).

Each job is a chain in its own worktree: the import closure of its TARGETS within its module prefix, built one
module per `lake build` in its own scope (`lock_mlane.run`: MemoryMax, no swap, LEAN_NUM_THREADS=1, per-module
log and summary line), a module starting only once its imports are done.

    remote_pool.py JOBS.json LANES (--par | --seq)
    JOBS.json: [{"name": "lock", "root": "/root/kam-lock", "pfx": "KAM.SpinOrbit.Data.LockN65",
                 "targets": ["KAM.SpinOrbit.Data.LockN65.AssemblyN65"], "logdir": "/root/chain/lock"}, ...]

* `--par`: one shared pool of LANES lanes; whenever a lane is free the first job in file order with a ready
  module gets it (the first job has priority; the others fill the idle lanes).
* `--seq`: the jobs one after another, each with all LANES lanes.

Failures do not stop a job (dependents are skipped). Per job `<logdir>/summary.out` (one line per module) and a
`STATUS` file next to JOBS.json (combined counts, rewritten every minute). LOCK_MEM, LOCK_GATE as in
lock_mlane.py. LOCK_DRY=1: closures, levels and widths only.
"""
import json
import os
import sys
import threading
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lock_mlane as LM     # noqa: E402


def load(path):
    jobs = json.load(open(path))
    for j in jobs:
        LM.MISSING.clear()
        order, deps = LM.closure(j["targets"], j["root"], j["pfx"])
        if LM.MISSING:
            raise SystemExit("job %s: %d missing sources (first %s)" % (j["name"], len(LM.MISSING), LM.MISSING[0]))
        j["order"], j["deps"] = order, deps
        j["state"] = {m: "todo" for m in order}
        os.makedirs(j["logdir"], exist_ok=True)
    return jobs


def levels(j):
    lv, width = {}, {}
    for m in j["order"]:
        lv[m] = 1 + max([lv[d] for d in j["deps"][m]], default=-1)
        width[lv[m]] = width.get(lv[m], 0) + 1
    return len(width), max(width.values()) if width else 0


def tally(j):
    return {k: sum(1 for v in j["state"].values() if v == k) for k in ("ok", "fail", "skip", "todo", "run")}


def pool(jobs, lanes, status_path, everyone=None):
    everyone = everyone or jobs
    gate = int(os.environ.get("LOCK_GATE", "8388608"))
    lock = threading.Lock()
    free = list(range(1, lanes + 1))
    outs = {j["name"]: open(os.path.join(j["logdir"], "summary.out"), "a") for j in jobs}

    def worker(j, m, lane):
        ok, line = LM.run(m, j["logdir"], lane, root=j["root"])
        with lock:
            j["state"][m] = "ok" if ok else "fail"
            free.append(lane)
            outs[j["name"]].write(line + "\n")
            outs[j["name"]].flush()
            print("[%s] %s" % (j["name"], line), flush=True)

    last = 0
    while True:
        launch = []
        with lock:
            busy = False
            for j in jobs:
                st, deps = j["state"], j["deps"]
                for m in j["order"]:
                    if st[m] == "todo" and any(st[d] in ("fail", "skip") for d in deps[m]):
                        st[m] = "skip"
                        outs[j["name"]].write("%s rc=SKIP (a dependency failed)\n" % m)
                j["ready"] = [m for m in j["order"] if st[m] == "todo" and all(st[d] == "ok" for d in deps[m])]
                busy = busy or bool(j["ready"]) or any(v == "run" for v in st.values())
            if not busy:
                break
            for j in jobs:                      # file order = priority
                while j["ready"] and free and LM.mem_available_kb() >= gate:
                    m = j["ready"].pop(0)
                    j["state"][m] = "run"
                    launch.append((j, m, free.pop(0)))
        for j, m, lane in launch:
            threading.Thread(target=worker, args=(j, m, lane), daemon=True).start()
            time.sleep(2)
        if time.time() - last > 60:
            with lock:
                txt = "%s\n" % time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()) + "".join(
                    "%s %s\n" % (j["name"], " ".join("%s=%d" % kv for kv in tally(j).items())) for j in everyone)
            open(status_path, "w").write(txt)
            last = time.time()
        time.sleep(5)
    for f in outs.values():
        f.close()


def main(argv):
    path, lanes, mode = argv[0], int(argv[1]), argv[2]
    assert mode in ("--par", "--seq"), mode
    jobs = load(path)
    for j in jobs:
        nl, w = levels(j)
        print("job %s: %d modules, %d levels, widest %d, root %s" % (j["name"], len(j["order"]), nl, w, j["root"]),
              flush=True)
    print("mode %s lanes %d mem %s gate %s kB" % (mode, lanes, os.environ.get("LOCK_MEM", "10G"),
                                                 os.environ.get("LOCK_GATE", "8388608")), flush=True)
    if os.environ.get("LOCK_DRY") == "1":
        return 0
    status = os.path.join(os.path.dirname(os.path.abspath(path)), "STATUS")
    for batch in ([jobs] if mode == "--par" else [[j] for j in jobs]):
        pool(batch, lanes, status, jobs)
    rc = 0
    for j in jobs:
        t = tally(j)
        print("done %s %s ok=%d fail=%d skip=%d todo=%d" % (time.strftime("%H:%M:%S", time.gmtime()), j["name"],
                                                           t["ok"], t["fail"], t["skip"], t["todo"]), flush=True)
        rc |= int(t["fail"] + t["skip"] + t["todo"] > 0)
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

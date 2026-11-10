#!/usr/bin/env python3
"""Job pool for the SJSU-FULL gates on one big machine (lam).

usage: pool.py JOBS.tsv RUNDIR   (env: LANES, BUDGET_GB, PY, LEAN, G5, REPO)
JOBS.tsv: id <TAB> cap (e.g. 40G) <TAB> timeout_s <TAB> kind <TAB> command (with {PY} {LEAN} {G5} {REPO} {RES}).
Each job runs in its own systemd --user scope (MemoryMax = cap, no swap) under nice -n 5; the sum of the caps of
running jobs never exceeds BUDGET_GB and at most LANES run at once.  Jobs with a passing result are skipped, so a
rerun retries only failed or missing jobs.  Result per job: RUNDIR/res/<id>.json (rc, verdict, wall, peak RSS).
Verdict pass iff rc == 0 and, for kinds g1/g3/g6, the job's JSON output exists and parses (extra output is fine).
"""
import json, os, signal, subprocess, sys, threading, time
jobs_file, rundir = sys.argv[1], os.path.abspath(sys.argv[2])
LANES = int(os.environ.get('LANES', '24'))
BUDGET = int(os.environ.get('BUDGET_GB', '220'))
SUB = {k: os.environ[k] for k in ('PY', 'LEAN', 'G5', 'REPO')}
RES = os.path.join(rundir, 'out'); SUB['RES'] = RES
resd = os.path.join(rundir, 'res'); logd = os.path.join(rundir, 'log')
for d in (resd, logd, RES, os.path.join(RES, 'g1'), os.path.join(RES, 'g3'), os.path.join(RES, 'g6')):
    os.makedirs(d, exist_ok=True)
lock = threading.Lock()
utc = lambda: time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def log(m):
    with lock:
        print(utc(), m, flush=True)


def gb(c):
    assert c.endswith('G'); return int(c[:-1])


def passed(jid):
    try:
        return json.load(open(os.path.join(resd, jid + '.json')))['verdict'] == 'pass'
    except (OSError, ValueError, KeyError):
        return False


jobs = []
for line in open(jobs_file):
    if line.strip() and not line.startswith('#'):
        jid, cap, tmo, kind, cmd = line.rstrip('\n').split('\t')
        jobs.append((jid, cap, int(tmo), kind, cmd.format(**SUB)))
todo = [j for j in jobs if not passed(j[0])]
log(f'start: {len(jobs)} jobs, {len(jobs) - len(todo)} already passed, {len(todo)} to run, lanes {LANES}, budget {BUDGET} GB')
running = {}
stop = threading.Event()
signal.signal(signal.SIGTERM, lambda *a: stop.set())


def run(job):
    jid, cap, tmo, kind, cmd = job
    t0 = time.time()
    out, err, tf = (os.path.join(logd, jid + s) for s in ('.out', '.err', '.time'))
    full = ['systemd-run', '--user', '--scope', '-q', '-p', f'MemoryMax={cap}', '-p', 'MemorySwapMax=0',
            '/usr/bin/time', '-v', '-o', tf, 'timeout', str(tmo), 'nice', '-n', '5', 'bash', '-c', cmd]
    with open(out, 'w') as fo, open(err, 'w') as fe:
        p = subprocess.Popen(full, stdout=fo, stderr=fe, start_new_session=True)
        with lock:
            running[jid] = (p, gb(cap))
        rc = p.wait()
    peak = None
    try:
        for l in open(tf):
            if 'Maximum resident set size' in l:
                peak = int(l.split()[-1])
    except OSError:
        pass
    ok = rc == 0
    if ok and kind in ('g1', 'g3', 'g6'):
        outs = [w for w in cmd.split() if w.endswith('.json') and RES in w]
        try:
            for o in outs:
                json.load(open(o))
        except (OSError, ValueError):
            ok = False
    if ok and kind.startswith('g5'):
        txt = open(out).read() + open(err).read()
        if kind == 'g5exe':
            ok = 'TOTAL ok=true' in txt
        else:                       # Lean prints `error:` on any failed check; profiler lines are fine
            ok = 'error:' not in txt
    r = {'id': jid, 'kind': kind, 'cap': cap, 'rc': rc, 'verdict': 'pass' if ok else 'fail',
         'wall_s': round(time.time() - t0, 1), 'peak_rss_kb': peak, 'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t0)),
         'cmd': cmd}
    json.dump(r, open(os.path.join(resd, jid + '.json'), 'w'))
    log(f'{"PASS" if ok else "FAIL"} {jid} rc={rc} wall={r["wall_s"]}s peak={peak}KB')
    with lock:
        running.pop(jid, None)


threads = []
queue = list(todo)
while queue and not stop.is_set():
    with lock:
        used = sum(c for _, c in running.values()); n = len(running)
    job = next((j for j in queue if n < LANES and used + gb(j[1]) <= BUDGET), None)
    if job is None:
        time.sleep(5); continue
    queue.remove(job)
    log(f'launch {job[0]} cap={job[1]} (committed {used + gb(job[1])} GB, {n + 1} running)')
    t = threading.Thread(target=run, args=(job,)); t.start(); threads.append(t)
    time.sleep(2)
if stop.is_set():
    log('stop requested: terminating running jobs by exact PID')
    with lock:
        for jid, (p, _) in running.items():
            try:
                os.killpg(p.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
for t in threads:
    t.join()
log('done')

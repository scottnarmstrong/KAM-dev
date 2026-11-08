#!/usr/bin/env python3
"""Verify a returned lam archive (sjsu-full-gates-results-*.tar.zst) against jobs.tsv of this package.

usage: python3 -I verify_return.py ARCHIVE [--jobs jobs.tsv]
Checks (in memory, nothing extracted): the .sha256 sidecar if present; one result per job of jobs.tsv, every
verdict pass with rc 0; every g1/g3/g6 JSON output named in a job command present and parseable; the G5 exe log
reports TOTAL ok=true; the smoke outputs are present.  Exit 0 iff all hold.  Extra files are accepted.
"""
import argparse, hashlib, io, json, subprocess, sys, tarfile
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('archive', type=Path)
ap.add_argument('--jobs', type=Path, default=Path(__file__).resolve().parent / 'jobs.tsv')
a = ap.parse_args()
errs = []
raw = a.archive.read_bytes()
side = a.archive.with_name(a.archive.name + '.sha256')
h = hashlib.sha256(raw).hexdigest()
if side.exists() and side.read_text().split()[0] != h:
    errs.append('archive sha256 differs from its sidecar')
print('archive sha256', h)
tb = subprocess.run(['zstd', '-dcq'], input=raw, stdout=subprocess.PIPE, check=True).stdout
mem = {}
with tarfile.open(fileobj=io.BytesIO(tb), mode='r:') as tf:
    for ti in tf:
        if ti.isfile():
            mem[ti.name.removeprefix('./')] = tf.extractfile(ti).read()
jobs = [l.split('\t') for l in a.jobs.read_text().splitlines() if l.strip() and not l.startswith('#')]
for jid, cap, tmo, kind, cmd in jobs:
    r = mem.get('res/%s.json' % jid)
    if r is None:
        errs.append('no result for ' + jid); continue
    r = json.loads(r)
    if r.get('verdict') != 'pass' or r.get('rc') != 0:
        errs.append('%s: verdict %s rc %s' % (jid, r.get('verdict'), r.get('rc')))
    for w in cmd.split():
        if w.startswith('{RES}/') and w.endswith('.json'):
            key = 'out/' + w[len('{RES}/'):]
            try:
                json.loads(mem[key])
            except (KeyError, ValueError):
                errs.append('%s: output %s missing or unreadable' % (jid, key))
exe = mem.get('log/g5exe.out', b'').decode()
if 'TOTAL ok=true' not in exe:
    errs.append('G5 exe log does not report TOTAL ok=true')
for s in ('smoke/g1.json', 'smoke/g3.json', 'smoke/g6.json'):
    if s not in mem:
        errs.append('missing ' + s)
peaks = {}
for k, v in mem.items():
    if k.startswith('res/'):
        r = json.loads(v)
        peaks.setdefault(r['kind'], []).append((r.get('peak_rss_kb') or 0) / 1048576)
for k, v in sorted(peaks.items()):
    print('%-6s %3d jobs, peak RSS max %.1f GB' % (k, len(v), max(v)))
print('FAIL:' if errs else 'OK: all %d jobs passed' % len(jobs))
for e in errs[:40]:
    print('  ', e)
sys.exit(1 if errs else 0)

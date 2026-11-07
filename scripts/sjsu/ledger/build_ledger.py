#!/usr/bin/env python3
"""Serial capped build of the KAMSJSU ledger (T2-CONF, N7; kam-g2/kam-18 driver ruling 2026-11-06).

`scripts/prebuild_heavy.py --lib KAMSJSU` re-runs `lake build --no-build` over all ~4450 modules of the
library before each single-module build (120 s per round, about 150 h in all). This driver instead
parses the import DAG once, walks it in topological order and builds it in batches:

* the modules: every module of the opt-in library KAMSJSU (scripts/build_roots.json, as
  prebuild_heavy.py) under `KAM.EffectiveStability.SJSU.Ledger` together with every KAMSJSU module
  they import transitively (`--scope ledger`, the default), or the whole library (`--scope lib`);
  the ordered list is written to scripts/sjsu/ledger/kamsjsu-modules.txt;
* each batch (`--batch`, default 100 consecutive modules of the order) is first re-checked with
  `lake build --no-build` (oleans built elsewhere, e.g. on lam, may be merged in mid-run): if it is
  up to date it is skipped; otherwise it is built by one `lake build <batch> --fail-fast` call;
* every lake call runs under the machine's heavy lane and the worktree's lake lock:
  `flock .kernel-probe.lock flock .drafts/g2/lake.lock`, then a wait for MemAvailable >= 12 GB, then
  `systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0 nice -n 5 env LEAN_NUM_THREADS=1`
  (the g2heavy settings). With LEAN_NUM_THREADS=1 Lake runs one lean process at a time (tested: three
  ready modules in one call never overlapped), so a batch is as serial as single-module calls;
* the log (`--log`) gets one line per module: UTC time, module, status (built / replayed / skipped /
  FAILED), lake's wall time, the lean process's peak RSS (VmHWM, sampled every 0.5 s), rc. On a
  failure the driver stops with exit status 1 and logs the tail of lake's output.

Usage: python3 scripts/sjsu/ledger/build_ledger.py [--scope ledger|lib] [--batch 100] [--log PATH]
       [--list-only] [--start MODULE]
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIB = 'KAMSJSU'
LEDGER = 'KAM.EffectiveStability.SJSU.Ledger'
HEAVY_LOCK = '/mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock'
LAKE_LOCK = str(ROOT / '.drafts/g2/lake.lock')
MEM_GATE_KB = 12 * 1024 * 1024
LAKE = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')  # systemd units lack ~/.elan/bin
SCOPE = ['systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryMax=10G', '-p', 'MemorySwapMax=0',
         'nice', '-n', '5', 'env', 'LEAN_NUM_THREADS=1']
IMPORT_RE = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
DONE_RE = re.compile(r'^\S+\s+\[\d+/\d+\]\s+(Built|Replayed)\s+(\S+)(?:\s+\(([^)]*)\))?')
FAIL_RE = re.compile(r'^\S+\s+\[\d+/\d+\]\s+Building\s+(\S+)')

_spec = importlib.util.spec_from_file_location('gen_root_imports', ROOT / 'scripts' / 'gen_root_imports.py')
roots = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(roots)


def utc() -> str:
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def path_of(mod: str) -> Path:
    return ROOT / (mod.replace('.', '/') + '.lean')


def module_order(scope: str) -> list[str]:
    """The KAMSJSU modules of `scope` in a topological order (imports first; ties by name)."""
    lib_of, errors = roots.classify(roots.load_config())
    if errors:
        raise SystemExit('build_ledger: scripts/gen_root_imports.py --check fails:\n' + '\n'.join(errors))
    lib = {m for m, l in lib_of.items() if l == LIB}
    deps = {m: sorted({i for i in IMPORT_RE.findall(path_of(m).read_text()) if i in lib}) for m in lib}
    if scope == 'ledger':
        todo = [m for m in lib if m == LEDGER or m.startswith(LEDGER + '.')]
        keep: set[str] = set()
        while todo:
            m = todo.pop()
            if m not in keep:
                keep.add(m)
                todo.extend(deps[m])
    else:
        keep = lib
    order: list[str] = []
    state: dict[str, int] = {}
    for root in sorted(keep):  # iterative DFS post-order: every import precedes its importers
        if root in state:
            continue
        stack = [(root, iter(deps[root]))]
        state[root] = 1
        while stack:
            m, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop()
                state[m] = 2
                order.append(m)
            elif nxt not in state:
                state[nxt] = 1
                stack.append((nxt, iter(deps[nxt])))
            elif state[nxt] == 1:
                raise SystemExit(f'build_ledger: import cycle through {nxt}')
    return order


def gated(cmd: list[str]) -> list[str]:
    """`cmd` under the heavy lane, the worktree lake lock, the memory gate and the capped scope."""
    gate = (f'until awk "/MemAvailable/{{exit !(\\$2 >= {MEM_GATE_KB})}}" /proc/meminfo; do sleep 30; done; '
            'exec "$@"')
    return ['flock', HEAVY_LOCK, 'flock', LAKE_LOCK, 'sh', '-c', gate, 'build_ledger', *SCOPE, *cmd]


class Sampler(threading.Thread):
    """Peak RSS (VmHWM) of every running `lean` process, keyed by the module it compiles."""

    def __init__(self, mods: set[str]):
        super().__init__(daemon=True)
        self.peak: dict[str, int] = {}
        self.paths = {str(path_of(m).relative_to(ROOT)): m for m in mods}
        self.stop = threading.Event()

    def run(self) -> None:
        while not self.stop.wait(0.5):
            for pid in os.listdir('/proc'):
                if not pid.isdigit():
                    continue
                try:
                    args = Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
                    if not args or not args[0].endswith(b'lean'):
                        continue
                    rel = [a.decode().removeprefix(str(ROOT) + '/') for a in args[1:]]
                    mod = next((self.paths[a] for a in rel if a in self.paths), None)
                    if mod is None:
                        continue
                    for line in Path(f'/proc/{pid}/status').read_text().splitlines():
                        if line.startswith('VmHWM:'):
                            kb = int(line.split()[1])
                            self.peak[mod] = max(self.peak.get(mod, 0), kb)
                except (OSError, UnicodeDecodeError, ValueError):
                    continue


def log_line(log, *fields) -> None:
    log.write('\t'.join(str(f) for f in fields) + '\n')
    log.flush()


def up_to_date(batch: list[str]) -> bool:
    r = subprocess.run(['flock', LAKE_LOCK, LAKE, 'build', '--no-build', *batch], cwd=ROOT,
                       capture_output=True, text=True)
    return r.returncode == 0


def build_batch(batch: list[str], log) -> int:
    sampler = Sampler(set(batch))
    sampler.start()
    t0 = time.time()
    proc = subprocess.Popen(gated([LAKE, 'build', '--fail-fast', *batch]), cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    tail: list[str] = []
    errors: list[str] = []
    seen: set[str] = set()
    building: str | None = None
    assert proc.stdout is not None
    for line in proc.stdout:
        tail = (tail + [line.rstrip()])[-60:]
        if line.startswith('error') and len(errors) < 40:
            errors.append(line.rstrip())
        if (m := DONE_RE.match(line)) and m.group(2) in sampler.paths.values():
            kind, mod, wall = m.groups()
            seen.add(mod)
            log_line(log, utc(), mod, kind.lower(), wall or '-', f'{sampler.peak.get(mod, 0) // 1024}MB', 0)
        elif m := FAIL_RE.match(line):
            building = m.group(1)
    rc = proc.wait()
    sampler.stop.set()
    if rc != 0:
        bad = building or '?'
        log_line(log, utc(), bad, 'FAILED', f'{time.time() - t0:.0f}s(batch)',
                 f'{sampler.peak.get(bad, 0) // 1024}MB', rc)
        log.write('# lake errors:\n' + '\n'.join('#   ' + l for l in errors) + '\n')
        log.write('# lake output tail:\n' + '\n'.join('#   ' + l for l in tail) + '\n')
        log.flush()
        return rc
    for mod in batch:  # modules lake did not mention were up to date already
        if mod not in seen:
            log_line(log, utc(), mod, 'uptodate', '-', '-', 0)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--scope', choices=['ledger', 'lib'], default='ledger')
    ap.add_argument('--batch', type=int, default=100)
    ap.add_argument('--log', default=str(ROOT / '.drafts/g2/scratch/n7b/build_ledger.log'))
    ap.add_argument('--list-only', action='store_true')
    ap.add_argument('--start', help='skip the modules before this one in the order')
    args = ap.parse_args()
    if not os.access(LAKE, os.X_OK):
        raise SystemExit(f'build_ledger: no lake executable ({LAKE})')
    order = module_order(args.scope)
    (HERE / 'kamsjsu-modules.txt').write_text('\n'.join(order) + '\n')
    print(f'build_ledger: {len(order)} modules ({args.scope}), list in {HERE / "kamsjsu-modules.txt"}', flush=True)
    if args.list_only:
        return 0
    if args.start:
        order = order[order.index(args.start):]
    with open(args.log, 'a') as log:
        log.write(f'# build_ledger start {utc()}: {len(order)} modules, batch {args.batch}\n')
        log.write('# utc\tmodule\tstatus\twall\tpeakRSS\trc\n')
        log.flush()
        for k in range(0, len(order), args.batch):
            batch = order[k:k + args.batch]
            if up_to_date(batch):
                for mod in batch:
                    log_line(log, utc(), mod, 'skipped', '-', '-', 0)
                continue
            if rc := build_batch(batch, log):
                log.write(f'# build_ledger STOPPED {utc()} rc={rc} (batch from {batch[0]})\n')
                return 1
        log.write(f'# build_ledger done {utc()}\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())

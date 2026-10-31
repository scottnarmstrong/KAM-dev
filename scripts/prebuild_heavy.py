#!/usr/bin/env python3
"""Build or confirm a certificate application (an opt-in Lake library, decision D51) without letting
Lake build its heavy modules in parallel.

usage:
  scripts/prebuild_heavy.py --lib LIB [--dry-run]   build application LIB serially
  scripts/prebuild_heavy.py --since BEFORE          confirm every application changed since BEFORE

The applications and their modules are declared in scripts/build_roots.json. Their certificate data
carry kernel checks of several GB each (`decide +kernel` over the data); Lake would build them in
parallel and exhaust memory (SO-CSPLIT owner item O3, 2026-10-30).

`--lib LIB`: if every module of LIB is up to date (one `lake build --no-build` over them), only the
generated root and its parts are built (`lake build LIB`, cheap). Otherwise the stale modules are
built one at a time, each with `flock .kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G
-p MemorySwapMax=0`: `lake build --no-build` names the stale modules whose imports are all built,
the first of them is built alone, and this repeats until nothing is stale; then the root. With
`--dry-run`, only the first round of stale modules is printed. Exit status 1 on the first failure.

`--since BEFORE` (scripts/land-branch.sh): for each application with a module changed since the
commit BEFORE, confirm that every module of the application is up to date, then build its root and
parts. It never builds an application module: if one is stale, it prints them and exits 3, so the
landing stops before any heavy rebuild (run `--lib LIB` deliberately, then land again).
"""
from __future__ import annotations

import argparse
import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOCK = '/mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock'
CAP = ['flock', LOCK, 'systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryMax=10G',
       '-p', 'MemorySwapMax=0', 'env', 'LEAN_NUM_THREADS=1', 'nice', '-n', '5']

_spec = importlib.util.spec_from_file_location('gen_root_imports', ROOT / 'scripts' / 'gen_root_imports.py')
roots = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(roots)


def stale(modules: list[str]) -> list[str]:
    """The stale modules among `modules` whose imports are built (Lake's failure list), or []."""
    if not modules:
        return []
    r = subprocess.run(['lake', 'build', '--no-build', *modules], cwd=ROOT, capture_output=True, text=True)
    if r.returncode == 0:
        return []
    out = r.stdout + r.stderr
    tail = out.split('Some required targets logged failures:', 1)
    names = [l[2:].strip() for l in tail[1].splitlines() if l.startswith('- ')] if len(tail) == 2 else []
    if not names:
        raise SystemExit('prebuild_heavy: lake build --no-build failed without a failure list:\n' + out[-3000:])
    return names


def capped_build(target: str) -> None:
    print(f'prebuild_heavy: building {target} (capped, alone)', flush=True)
    if subprocess.run(CAP + ['lake', 'build', target], cwd=ROOT).returncode != 0:
        print(f'prebuild_heavy: FAILED at {target}', flush=True)
        sys.exit(1)


def members(lib: str, cfg: dict) -> list[str]:
    lib_of, errors = roots.classify(cfg)
    if errors:
        raise SystemExit('prebuild_heavy: scripts/gen_root_imports.py --check fails:\n' + '\n'.join(errors))
    return [m for m in sorted(lib_of) if lib_of[m] == lib]


def build_lib(lib: str, cfg: dict, dry: bool) -> None:
    mods = members(lib, cfg)
    print(f'prebuild_heavy: {lib}: {len(mods)} modules', flush=True)
    rounds = 0
    while todo := stale(mods):
        if dry:
            print('DRY stale (imports built): ' + ' '.join(todo))
            return
        rounds += 1
        capped_build(todo[0])
    print(f'prebuild_heavy: {lib}: every module up to date ({rounds} built)', flush=True)
    if not dry:
        capped_build(lib)


def confirm_since(before: str, cfg: dict) -> int:
    out = subprocess.run(['git', 'diff', '--name-only', before, 'HEAD', '--', 'KAM'], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    core = cfg['core']['lib']
    libs = sorted({roots.library_of(p[:-len('.lean')].replace('/', '.'), cfg) for p in out if p.endswith('.lean')}
                  - {core})
    print(f'prebuild_heavy: applications changed since {before[:8]}: {", ".join(libs) or "none"}', flush=True)
    for lib in libs:
        todo = stale(members(lib, cfg))
        if todo:
            print(f'prebuild_heavy: {lib}: heavy modules would rebuild (stale: {" ".join(todo[:20])}); '
                  f'run scripts/prebuild_heavy.py --lib {lib} deliberately, then land again', flush=True)
            return 3
        print(f'prebuild_heavy: {lib}: every module up to date (lake build --no-build)', flush=True)
        capped_build(lib)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--lib', help='application library to build serially')
    group.add_argument('--since', metavar='BEFORE', help='confirm the applications changed since BEFORE')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    cfg = roots.load_config()
    if args.since:
        return confirm_since(args.since, cfg)
    apps = [a['lib'] for a in cfg['applications']]
    if args.lib not in apps:
        print(f'unknown application {args.lib}; known: {", ".join(apps)}', file=sys.stderr)
        return 2
    build_lib(args.lib, cfg, args.dry_run)
    return 0


if __name__ == '__main__':
    sys.exit(main())

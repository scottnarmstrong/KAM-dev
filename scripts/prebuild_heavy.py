#!/usr/bin/env python3
"""Build or confirm a certificate application (an opt-in Lake library, decision D51) without letting
Lake build its heavy modules in parallel.

usage:
  scripts/prebuild_heavy.py --lib LIB [--dry-run]   build application LIB serially
  scripts/prebuild_heavy.py --check-all             landing check of every application

The applications and their modules are declared in scripts/build_roots.json. Their certificate data
carry kernel checks of several GB each (`decide +kernel` over the data); Lake would build them in
parallel and exhaust memory (SO-CSPLIT owner item O3, 2026-10-30).

`--lib LIB`: if every module of LIB is up to date (one `lake build --no-build` over them), only the
generated root and its parts are built (`lake build LIB`, cheap). Otherwise the stale modules are
built one at a time, each with `flock .kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G
-p MemorySwapMax=0`: `lake build --no-build` names the stale modules whose imports are all built,
the first of them is built alone, and this repeats until nothing is stale; then the root. With
`--dry-run`, only the first round of stale modules is printed. Exit status 1 on the first failure.

`--check-all` (scripts/land-branch.sh, after the core `lake build`): every application is checked,
whatever the landing changed (BUILD-OPTIN audit 1, F1: a change to a core module in an application's
import closure, to lakefile.lean, the toolchain, the Lake manifest or scripts/build_roots.json makes
an application stale without touching its files). For each application, `lake build --no-build LIB`
names the stale modules whose imports are built. If none, it is up to date. If any of them is heavy
(under an `application_only` prefix of scripts/build_roots.json: certificate data), the check stops
with exit 3, naming the application and the stale data modules: build it deliberately with
`--lib LIB`, then land again. Otherwise (generated root and parts, LunarFinalR2V2 and other light
modules) the first is built alone under the cap and the check repeats. A landing that leaves every
application up to date builds nothing.
Applications listed in CHECK_ALL_SKIP (each with its owner ruling) are not checked; a WARNING line names
each one.
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


def heavy(module: str, cfg: dict) -> bool:
    return any(roots.extends(module, p) for p in cfg.get('application_only', []))


# Applications that --check-all skips, each with the owner ruling that allows it. Every other application is
# checked. 2026-11-07: a disk cleanup deleted the build artifacts of the two lunar libraries (the SpinOrbit/Data
# overlay); their sources and sealed theorems are unchanged on main. Owner ruling (via the main orchestrator,
# 2026-11-07): land with the check skipped for these two only; rebuilding them is a separate, later job. Remove an
# entry once `scripts/prebuild_heavy.py --lib LIB` has rebuilt that library.
CHECK_ALL_SKIP = {
    'KAMLunarBand': 'build artifacts lost in the 2026-11-07 cleanup; owner ruling 2026-11-07, rebuild pending',
    'KAMLunarLock': 'build artifacts lost in the 2026-11-07 cleanup; owner ruling 2026-11-07, rebuild pending',
}


def check_all(cfg: dict) -> int:
    for app in cfg['applications']:
        lib, built, seen = app['lib'], 0, set()
        if lib in CHECK_ALL_SKIP:
            print(f'prebuild_heavy: WARNING: {lib}: NOT CHECKED ({CHECK_ALL_SKIP[lib]})', flush=True)
            continue
        while todo := stale([lib]):
            data = [m for m in todo if heavy(m, cfg)]
            if data:
                print(f'prebuild_heavy: {lib}: heavy modules would rebuild (stale data: {" ".join(data[:20])}); '
                      f'run scripts/prebuild_heavy.py --lib {lib} deliberately, then land again', flush=True)
                return 3
            if todo[0] in seen:
                print(f'prebuild_heavy: {lib}: {todo[0]} still stale after building it', flush=True)
                return 1
            seen.add(todo[0])
            capped_build(todo[0])
            built += 1
        print(f'prebuild_heavy: {lib}: up to date ({built} light modules built)', flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--lib', help='application library to build serially')
    group.add_argument('--check-all', action='store_true', help='landing check of every application')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    cfg = roots.load_config()
    if args.check_all:
        return check_all(cfg)
    apps = [a['lib'] for a in cfg['applications']]
    if args.lib not in apps:
        print(f'unknown application {args.lib}; known: {", ".join(apps)}', file=sys.stderr)
        return 2
    build_lib(args.lib, cfg, args.dry_run)
    return 0


if __name__ == '__main__':
    sys.exit(main())

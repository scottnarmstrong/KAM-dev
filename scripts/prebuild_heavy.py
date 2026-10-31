#!/usr/bin/env python3
"""Build the heavy certificate-data modules one at a time, each under the kernel-probe lock and a 10 GB cap.

usage: scripts/prebuild_heavy.py BEFORE [--dry-run]

Called by scripts/land-branch.sh before the parallel `lake build` (SO-CSPLIT owner item O3, 2026-10-30). The
data modules under KAM/SpinOrbit/Data/ carry kernel checks of several GB each (`decide +kernel` over certificate
data). Lake would build them in parallel and exhaust memory, so every such module changed since BEFORE is built
alone, after the modules it imports (topological order from the import lines), with
`flock .kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0`. Exit status 1 on the
first failure.
"""
import re
import subprocess
import sys

HEAVY = 'KAM/SpinOrbit/Data/'
LOCK = '/mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock'
IMPORT = re.compile(r'^(?:public\s+)?import\s+(KAM\.[\w.]+)', re.M)


def changed(before):
    out = subprocess.run(['git', 'diff', '--name-only', '--diff-filter=AM', before, 'HEAD', '--', HEAVY],
                         capture_output=True, text=True, check=True).stdout
    return sorted(p for p in out.split() if p.endswith('.lean'))


def module(path):
    return path[:-len('.lean')].replace('/', '.')


def order(paths):
    mods = {module(p): p for p in paths}
    deps = {}
    for m, p in mods.items():
        with open(p, encoding='utf-8') as f:
            deps[m] = [d for d in IMPORT.findall(f.read()) if d in mods]
    done, seq = set(), []

    def visit(m, stack=()):
        if m in done:
            return
        if m in stack:
            raise SystemExit(f'import cycle through {m}')
        for d in deps[m]:
            visit(d, stack + (m,))
        done.add(m)
        seq.append(m)

    for m in sorted(mods):
        visit(m)
    return seq


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    before, dry = sys.argv[1], '--dry-run' in sys.argv[2:]
    seq = order(changed(before))
    print(f'prebuild_heavy: {len(seq)} heavy module(s) changed since {before[:8]}')
    # Fast path (2026-10-31, SO-DATA3: about 1,650 data modules whose verified builds are reused via the HC build
    # overlay): one `lake build --no-build` over all of them; if every module is up to date, nothing to do.
    if seq and not dry and subprocess.run(['lake', 'build', '--no-build'] + seq,
                                          capture_output=True).returncode == 0:
        print('prebuild_heavy: all up to date (lake build --no-build)', flush=True)
        return
    for m in seq:
        cmd = ['flock', LOCK, 'systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryMax=10G',
               '-p', 'MemorySwapMax=0', 'env', 'LEAN_NUM_THREADS=1', 'nice', '-n', '5', 'lake', 'build', m]
        print(('DRY ' if dry else '') + m, flush=True)
        if dry:
            continue
        if subprocess.run(cmd).returncode != 0:
            print(f'prebuild_heavy: FAILED at {m}', flush=True)
            sys.exit(1)
    print('prebuild_heavy: done', flush=True)


if __name__ == '__main__':
    main()

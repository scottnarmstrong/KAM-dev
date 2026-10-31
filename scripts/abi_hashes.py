#!/usr/bin/env python3
"""Compute ABI hashes of frozen declarations with `pp.all true`: for a definition the sha256 of
`#print` (type and body), for a theorem the sha256 of `#check @name` (the statement only, so that
sealing the proof does not change it).

usage: abi_hashes.py <repo root> <manifest.json> [--check] [--lib LIB ...]
Without --check, prints {export: sha256} as JSON. With --check, compares against the manifest's
abi_sha256 fields and exits 1 on drift.

Decision D51: the frozen anchors whose modules belong to a certificate application (an opt-in
library, scripts/build_roots.json) need that library's build, which a plain `lake build` does not
make. By default only the anchors of the core library `KAM` are hashed, and the others are listed
as checked by file hash only (scripts/check_frozen_anchors.py covers every frozen file). `--lib
LIB` (repeatable; `all` for every library) hashes the anchors of LIB instead; it first runs `lake
build --no-build LIB` and exits 2, building nothing, if LIB is not fully built. The elaborated form includes every instance and definition
the statement uses, so it catches meaning changes that the file hashes alone cannot see.
Adapted from Critical2DKPZ-dev; the scratch file lives under `.lake/` so that no source checker
sees it.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import argparse
import importlib.util

parser = argparse.ArgumentParser()
parser.add_argument('root')
parser.add_argument('manifest')
parser.add_argument('--check', action='store_true')
parser.add_argument('--lib', action='append', default=[])
cli = parser.parse_args()
root, manifest_path = Path(cli.root).resolve(), Path(cli.manifest)
check = cli.check
manifest = json.loads(manifest_path.read_text())
spec = importlib.util.spec_from_file_location('gen_root_imports', root / 'scripts' / 'gen_root_imports.py')
roots = importlib.util.module_from_spec(spec)
spec.loader.exec_module(roots)
config = roots.load_config()
known = roots.libraries(config)
libs = set(cli.lib or [config['core']['lib']])
if 'all' in libs:
    libs = set(known)
unknown = libs - set(known)
if unknown:
    print(f'unknown library {", ".join(sorted(unknown))}; known: {", ".join(known)}', file=sys.stderr)
    sys.exit(2)


def anchor_lib(a):
    return roots.library_of('.'.join(Path(a['path']).with_suffix('').parts), config)


skipped = [a for a in manifest['anchors'] if anchor_lib(a) not in libs]
anchors = [a for a in manifest['anchors'] if anchor_lib(a) in libs]
for lib in sorted(libs - {config['core']['lib']}):
    if any(anchor_lib(a) == lib for a in anchors):
        r = subprocess.run(['lake', 'build', '--no-build', lib], cwd=root, capture_output=True, text=True)
        if r.returncode != 0:
            print(f'{lib} is not fully built; build it first (`lake build {lib}` through the capped driver, '
                  f'scripts/prebuild_heavy.py --lib {lib}); nothing was built', file=sys.stderr)
            sys.exit(2)
modules = sorted({'.'.join(Path(a['path']).with_suffix('').parts) for a in anchors})
exports = [a['export'] for a in anchors]
lines = [f'import {m}' for m in modules] + ['set_option pp.all true', 'set_option pp.oneline false']
marker = 'ABI_HASH_BOUNDARY'
for a in anchors:
    e = a['export']
    lines.append(f'#eval IO.println "{marker} {e}"')
    lines.append(f'#print {e}' if a['kind'] == 'definition' else f'#check @{e}')
scratch = root / '.lake' / 'abi-scratch'
scratch.mkdir(parents=True, exist_ok=True)
with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=scratch, delete=False) as f:
    f.write('\n'.join(lines) + '\n')
    tmp = Path(f.name)
try:
    # elan writes its override notice to stderr; it must never reach the hashed text
    env = os.environ | {'ELAN_NO_OVERRIDE_NOTICE': '1'}
    out = subprocess.run(['lake', 'env', 'lean', str(tmp)], cwd=root, capture_output=True, text=True, env=env)
finally:
    tmp.unlink()
if out.returncode != 0:
    print((out.stdout + out.stderr)[-4000:], file=sys.stderr)
    sys.exit(2)
text = out.stdout   # Lean prints every message on stdout; stderr is tool noise (elan, throttle)
chunks = re.split(rf'^{marker} (\S+)\s*$', text, flags=re.M)
hashes = {}
for i in range(1, len(chunks), 2):
    body = re.sub(r'^\S+\.lean:\d+:\d+: ', '', chunks[i + 1].strip(), flags=re.M)
    hashes[chunks[i]] = hashlib.sha256(body.encode()).hexdigest()
missing = [e for e in exports if e not in hashes]
if missing:
    print('no #print output for: ' + ', '.join(missing), file=sys.stderr)
    sys.exit(2)
if not check:
    print(json.dumps(hashes, indent=1, ensure_ascii=False))
    sys.exit(0)
drift = [a['export'] for a in anchors if hashes[a['export']] != a['abi_sha256']]
if drift:
    print('ABI DRIFT: ' + ', '.join(drift), file=sys.stderr)
    sys.exit(1)
note = ''
if skipped:
    by_lib = {}
    for a in skipped:
        by_lib.setdefault(anchor_lib(a), []).append(a['export'])
    note = ('; checked by file hash only, not built by this run: '
            + '; '.join(f'{lib}: {len(e)} declarations (run without --lib)' if lib == config['core']['lib']
                        else f'{lib}: {", ".join(sorted(e))} (--lib {lib})' for lib, e in sorted(by_lib.items())))
print(f'ABI HASHES OK ({len(anchors)} frozen declarations of {", ".join(sorted(libs))}{note})')

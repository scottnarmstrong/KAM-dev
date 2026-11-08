#!/usr/bin/env python3
"""Write applications/sjsu/data/MANIFEST.sha256 (sha256 of every file in data/ except itself)."""
import hashlib
import os

DATA = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data'))
lines = []
for name in sorted(os.listdir(DATA)):
    if name == 'MANIFEST.sha256' or os.path.isdir(os.path.join(DATA, name)):
        continue
    h = hashlib.sha256(open(os.path.join(DATA, name), 'rb').read()).hexdigest()
    lines.append(f'{h}  {name}\n')
with open(os.path.join(DATA, 'MANIFEST.sha256'), 'w') as fh:
    fh.writelines(lines)
print(''.join(lines), end='')

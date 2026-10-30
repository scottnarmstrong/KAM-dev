#!/usr/bin/env python3
"""W copy (docs/graph/W/tools): the locator path may also lie in blueprint-W/.

Remap `path#anchor@Lx-Ly` locators after edits to the source files (tracks K, I, N, P).

Copy of scripts/depgraph_remap_locators.py (track K); the locator path may lie in blueprint/, blueprint-I/,
blueprint-N/ or blueprint-P/ (imported nodes point into other tracks' blueprints). Run it from the repository root.

usage: inp_depgraph_remap_locators.py OLD_REV FILE.md [FILE.md ...]
For every locator whose path changed between git revision OLD_REV and the working tree, maps Lx and Ly through a
line diff (difflib).
- A line in an unchanged block maps to its new number.
- A line inside a replaced block maps to the start (for x) or end (for y) of the replacement.
Rewrites the given Markdown files in place and prints, per source file, how many locators moved.
"""
import difflib
import re
import subprocess
import sys
from pathlib import Path

rev, files = sys.argv[1], sys.argv[2:]
LOC = re.compile(r"(?P<path>blueprint(?:-[INPW])?/[^#\s|]+)#(?P<anchor>[^@\s|]+)@L(?P<x>\d+)-L(?P<y>\d+)")
maps = {}


def line_map(path):
    if path in maps:
        return maps[path]
    old = subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True).stdout.split("\n")
    new = Path(path).read_text().split("\n")
    if old == new:
        maps[path] = None
        return None
    fwd_start, fwd_end = {}, {}
    sm = difflib.SequenceMatcher(a=old, b=new, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        for k in range(i1, i2):
            if tag == "equal":
                fwd_start[k + 1] = fwd_end[k + 1] = j1 + (k - i1) + 1
            else:
                fwd_start[k + 1] = j1 + 1
                fwd_end[k + 1] = max(j2, j1 + 1)
    maps[path] = (fwd_start, fwd_end)
    return maps[path]


moved = {}
for f in files:
    p = Path(f)
    text = p.read_text()

    def sub(m):
        lm = line_map(m.group("path"))
        if lm is None:
            return m.group(0)
        x, y = int(m.group("x")), int(m.group("y"))
        nx, ny = lm[0].get(x, x), lm[1].get(y, y)
        if (nx, ny) != (x, y):
            moved[m.group("path")] = moved.get(m.group("path"), 0) + 1
        return f"{m.group('path')}#{m.group('anchor')}@L{nx}-L{ny}"

    p.write_text(LOC.sub(sub, text))
for k, v in sorted(moved.items()):
    print(f"{k}: {v} locators moved")

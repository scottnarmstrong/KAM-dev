#!/usr/bin/env python3
"""LOCK-DATA DELTA-LAM-2: apply the emitter's DELTA-LAM-2 transforms (`lock_cseg._delta2`) to an emitted tree
(untrusted tooling).

The emitter runs `_delta2` on every module it writes (`lock_cseg._tree_write`); this tool runs the same function on
the files of an already emitted tree, so the result equals a re-emission byte for byte (the transforms keep every
line within the emitter's column limit, so its `autowrap` leaves them alone, and they never touch the header).

    python3 lock_delta2.py SRC DST [--list OUT]
        SRC, DST: tree roots (DST a copy of SRC); every `.lean` under SRC/KAM/SpinOrbit/Data/LockN65/Seg whose text
        the transforms change is written to the same path under DST (a new file, never through a link).
    python3 lock_delta2.py --check ROOT
        rc 0 iff the transforms change nothing under ROOT (idempotence / an applied tree).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lock_cseg as LC        # noqa: E402

SEG = os.path.join("KAM", "SpinOrbit", "Data", "LockN65", "Seg")
IMP = re.compile(r"^public import (\S+)$", re.M)


def apply_text(text):
    """the transformed file text (the import of MemoBridge added to the sorted import block where needed)"""
    t, mb = LC._delta2(text)
    if mb and ("public import %s\n" % LC.MEMOBRIDGE) not in t:
        imps = IMP.findall(t)
        first, last = re.search(r"^public import \S+$", t, re.M), list(IMP.finditer(t))[-1]
        block = "\n".join("public import " + i for i in sorted(set(imps + [LC.MEMOBRIDGE])))
        t = t[:first.start()] + block + t[last.end():]
    for i, line in enumerate(t.split("\n")):
        assert len(line) <= 100, (i, len(line), line)
    assert t.count("\n") <= 1500
    return t


def files(root):
    for d, _, fs in os.walk(os.path.join(root, SEG)):
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.relpath(os.path.join(d, f), root)


def main(argv):
    if argv[0] == "--check":
        bad = [r for r in files(argv[1]) if apply_text(open(os.path.join(argv[1], r)).read()) !=
               open(os.path.join(argv[1], r)).read()]
        print("changed by the transforms: %d" % len(bad))
        for r in bad[:20]:
            print("  " + r)
        return 1 if bad else 0
    src, dst = argv[0], argv[1]
    out = argv[argv.index("--list") + 1] if "--list" in argv else None
    changed = []
    for r in files(src):
        old = open(os.path.join(src, r)).read()
        new = apply_text(old)
        if new != old:
            p = os.path.join(dst, r)
            changed.append(r)
            if os.path.isfile(p) and not os.path.islink(p) and open(p).read() == new:
                continue                  # already applied: the file is left as it is
            if os.path.lexists(p):
                os.remove(p)              # a new file: never write through a link or into a shared inode
            with open(p, "w") as f:
                f.write(new)
    print("changed %d" % len(changed))
    if out:
        with open(out, "w") as f:
            f.write("".join(r + "\n" for r in changed))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

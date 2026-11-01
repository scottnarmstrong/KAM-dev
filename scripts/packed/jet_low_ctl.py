#!/usr/bin/env python3
"""V2-PACKED-JET-LOW (untrusted tooling): a failing control of a packed Low-chain probe.

Copies PROBE.lean to OUT.lean with the radius of the node `NAME` (a `def NAME : JNode LGF := ⟨…, ⟨r⟩, ⟨nb⟩⟩`)
lowered by one ulp and the statement's `= true` turned into `= false`. Every exported radius is emitted exactly
as the kernel computes it, so the control must decide `= false`: the check is not vacuous.
Usage: python3 -I scripts/packed/jet_low_ctl.py PROBE.lean NAME OUT.lean
"""
import re
import sys


def main():
    src, name, out = sys.argv[1], sys.argv[2], sys.argv[3]
    s = open(src).read()
    m = re.search(r"def %s : JNode LGF :=\n(.*?)⟩, ⟨(\d+)⟩, ⟨(\d+)⟩⟩\n" % re.escape(name), s, re.S)
    assert m, "node %s not found" % name
    r = int(m.group(2))
    assert r > 0, "zero radius"
    s = s[:m.start(2)] + str(r - 1) + s[m.end(2):]
    i = s.rindex("= true := by")
    s = s[:i] + "= false := by" + s[i + len("= true := by"):]
    mod = re.search(r"namespace (\S+)", s).group(1)
    s = s.replace(mod, mod + "Ctl")
    open(out, "w").write(s)
    print("%s: %s radius %d -> %d" % (out, name, r, r - 1))


if __name__ == "__main__":
    main()

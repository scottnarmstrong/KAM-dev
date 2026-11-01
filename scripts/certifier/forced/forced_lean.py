#!/usr/bin/env python3
"""V2-TOOLS: run Lean `#eval`s against the built forced-toy modules (the compiled checker as a fast oracle for
witness search and for the cross-language comparisons).  Untrusted tooling: the kernel re-decides everything.

`lean_eval(imports, opens, exprs)` writes a scratch file into a fresh temporary directory, runs it with
`nice -n 5 lake env lean` from the repository root, and returns the printed value of each expression (one `#eval`
per expression, each wrapped so that its output line is tagged).  Values are parsed by `parse_*` helpers.
"""
import os
import re
import subprocess
import tempfile
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))


def lean_eval(imports, opens, exprs, timeout=900, prelude=""):
    tag = "@@V2T@@"
    lines = ["import %s" % m for m in imports]
    lines.append("open %s" % " ".join(opens) if opens else "")
    lines.append(prelude)
    for i, e in enumerate(exprs):
        lines.append('#eval IO.println ("%s%d " ++ toString (%s))' % (tag, i, e))
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "Probe.lean")
        with open(path, "w") as fh:
            fh.write("\n".join(lines) + "\n")
        r = subprocess.run(["nice", "-n", "5", "lake", "env", "lean", path], cwd=ROOT, capture_output=True,
                           text=True, timeout=timeout)
    out = {}
    for ln in (r.stdout + r.stderr).splitlines():
        m = re.match(r"%s(\d+) (.*)$" % tag, ln)
        if m:
            out[int(m.group(1))] = m.group(2)
    errs = [ln for ln in (r.stdout + r.stderr).splitlines() if "error" in ln]
    if len(out) != len(exprs):
        raise RuntimeError("lean_eval: %d of %d values; errors: %s" % (len(out), len(exprs), "\n".join(errs[:10])))
    return [out[i] for i in range(len(exprs))]


def parse_q(s):
    """a Lean `toString` of a ℚ: `p/q` or `p`."""
    s = s.strip()
    return F(s)


def parse_bool(s):
    s = s.strip()
    assert s in ("true", "false"), s
    return s == "true"


def lq(x):
    """a Lean ℚ literal."""
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "((%d : ℚ) / %d)" % (x.numerator, x.denominator)

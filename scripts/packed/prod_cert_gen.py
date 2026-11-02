#!/usr/bin/env python3
"""V2-PACKED-PROD (untrusted tooling): the shared certificate data of the packed route, copied from LG00's application.

Copies, from `lg00-app`'s package `applications/lg00/LG00` (read only), the modules the packed route reads, renamed
`LG00.` -> `<P>.` (default `LG00P`), into OUT/<P>/:
  - shared: `Format`, `FormatK`, `FormatQ`, `Coeffs0`, `Coeffs1`, `Ham`, `JetOps0..6`, `Jet`, `JetBridge`;
  - the torus tree (default `TP`, LG00's T'): `Data/DCoeffs`, `Data/E0` (the embedding), `Data/W8` (the Gram inverse),
    and `Data/Cert`, the certificate WITHOUT the landed composition's advice (`cfgLow`/`cfgFull` advice `[]`) and
    WITHOUT witnesses (`wit` empty): the packed route reads neither, and `CertifiedTorus` reads only `params`, `ham`,
    `weightH`, `centre`, `radius` and `emb`, so the copy certifies the same torus.
Writes OUT/<P>/... (a file already holding its text is left untouched, so a second tree, e.g. `--tree=TPP`, does
not touch the shared modules) and prints the module list. The text is otherwise byte-identical to the source
(checked: every copied definition outside `lg00Wit`, `lg00CfgFull.advice`, `lg00CfgLow.advice` and the imports is
unchanged).
Usage: python3 -I scripts/packed/prod_cert_gen.py OUT [--app=APP_ROOT] [--tree=TP] [--prefix=LG00P]
"""
import os
import re
import sys

SHARED = ["Format", "FormatK", "FormatQ", "Coeffs0", "Coeffs1", "Ham"] + ["JetOps%d" % i for i in range(7)] + \
    ["Jet", "JetBridge"]
TREE_DATA = ["Data/DCoeffs", "Data/E0", "Data/W8"]


def opt(name, default):
    return next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--%s=" % name)), default)


def rename(text, pre):
    return re.sub(r"\bLG00\b", pre, text)


def cert_text(src, pre, tree):
    s = src
    keep = {"%s.%s.Data.DCoeffs" % (pre, tree), "%s.Ham" % pre, "%s.%s.Data.E0" % (pre, tree),
            "%s.%s.Data.W8" % (pre, tree)}
    lines = []
    for line in s.split("\n"):
        m = re.match(r"public import (\S+)$", line)
        if m and m.group(1).startswith(pre + ".") and m.group(1) not in keep:
            continue
        lines.append(line)
    s = "\n".join(lines)
    # the witnesses: empty (the packed route computes the characters, `inv` and `sqrt` in the kernel)
    s, k = re.subn(r"def lg00Wit : Witnesses LGF where\n(  .*\n|      .*\n)*?(?=\n)",
                   "def lg00Wit : Witnesses LGF where\n  expWit := []\n  invWit := []\n  charWit := []\n"
                   "  sqrtWit := []\n", s)
    assert k == 1, "lg00Wit"
    # the advice of the landed composition: none
    s, k = re.subn(r"(  toMant := CertFixed\.toMant lgP\n  advice :=\n)    \([^)]*\)\n", r"\1    []\n", s)
    assert k == 2, "advice %d" % k
    s2 = s.replace("its torus, witnesses, advice and parameters.",
                   "its torus and parameters. The packed route's copy\n(V2-PACKED-PROD, "
                   "`scripts/packed/prod_cert_gen.py`): no advice, no witnesses.")
    assert s2 != s, "docstring"
    s = s2
    return s


def put(dst, text):
    """Write `text` to `dst` unless it already holds it (a second tree leaves the shared modules untouched)."""
    if os.path.exists(dst) and open(dst).read() == text:
        return
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, "w").write(text)


def main():
    out = sys.argv[1]
    app = opt("app", "/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00")
    tree, pre = opt("tree", "TP"), opt("prefix", "LG00P")
    mods = []
    for m in SHARED:
        src = open(os.path.join(app, "LG00", m + ".lean")).read()
        put(os.path.join(out, pre, m + ".lean"), rename(src, pre))
        mods.append("%s.%s" % (pre, m))
    for m in TREE_DATA + ["Data/Cert"]:
        src = rename(open(os.path.join(app, "LG00", tree, m + ".lean")).read(), pre)
        if m == "Data/Cert":
            src = cert_text(src, pre, tree)
        put(os.path.join(out, pre, tree, m + ".lean"), src)
        mods.append("%s.%s.%s" % (pre, tree, m.replace("/", ".")))
    print("\n".join(mods))


if __name__ == "__main__":
    main()

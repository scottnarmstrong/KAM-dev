#!/usr/bin/env python3
"""D68 identity check: the installed KAM/Frozen/Magnetic files equal the approved drafts of
mag-pilot@a48eb432 (docs/explorations/mag/draft/*.lean.txt) up to exactly the allowed edits: the module
docstring (date/decision placeholders), the anchor marker comments, the quarantined provider import of the
theorem anchor, and the theorem body `sorry` -> `by sorry`; a whitespace-only reflow (lint: 100 columns) is reported as
TOKEN-IDENTICAL.  Exit 0 iff every file passes."""
import re
import subprocess
import sys

REF = "a48eb432"
FILES = {"Defs/MagEps": "MagEps", "Defs/MagH0": "MagH0", "Defs/MagAlpha": "MagAlpha", "Defs/MagV": "MagV",
         "Defs/MagField": "MagField", "Defs/MagHamC": "MagHamC", "Theorems/MagneticBarrier": "MagneticBarrier"}


def norm(s):
    s = re.sub(r"/-!.*?-/\n", "", s, count=1, flags=re.S)                 # the module docstring
    s = re.sub(r"(?m)^[ \t]*-- FROZEN_ANCHOR_[A-Z_]+\n", "", s)            # marker comments
    s = s.replace("import KAM.Provider.Magnetic.MagneticBarrier\n", "")
    s = s.replace("  by sorry\n", "  sorry\n")
    return s


def tokens(s):
    return norm(s).split()


ok = True
for inst, draft in FILES.items():
    a = open("KAM/Frozen/Magnetic/%s.lean" % inst).read()
    b = subprocess.check_output(["git", "show", "%s:docs/explorations/mag/draft/%s.lean.txt" % (REF, draft)]).decode()
    same = norm(a) == norm(b)
    tok = tokens(a) == tokens(b)
    ok &= tok
    print("%-28s %s" % (inst, "IDENTICAL (allowed edits only)" if same else
                         ("TOKEN-IDENTICAL (whitespace reflow only)" if tok else "DIFFERS")))
sys.exit(0 if ok else 1)

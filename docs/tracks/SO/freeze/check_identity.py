#!/usr/bin/env python3
"""Self-check: each frozen SO file against the approved text, byte for byte.

Approved text: FREEZE-PROPOSAL.md §1.1-§1.8 (definitions, complete blocks) and FREEZE-PROPOSAL-2.md §1.2-§1.3
(window and theorems), with only the D47/D49 literal substitutions. From each frozen file the header lines
added at freeze time are removed (copyright, module docstring, FROZEN_ANCHOR_PREFIX_BEGIN), the D-SOF-5 line
splits are undone and the proof body (`by sorry`, D-SOF-6, or the sealing body) is read as `sorry`; the result must contain the approved block
exactly (B and window: A's wrapper, complete file). Exit status 1 on any mismatch.
Run from the repository root."""
import re
from pathlib import Path
P1 = Path("docs/tracks/SO/FREEZE-PROPOSAL.md").read_text()
P2 = Path("docs/tracks/SO/FREEZE-PROPOSAL-2.md").read_text()
blocks1 = dict(re.findall(r"### 1\.\d+ `KAM/Frozen/SpinOrbit/Defs/(\w+)\.lean`\n\n```lean\n(.*?)```", P1, re.S))
p2 = re.findall(r"```lean\n(.*?)```", P2.split("### 1.2 The window")[1].split("### 1.4")[0], re.S)
SUBS = [("9933 / 10000      -- interim candidate; fixed by rule W of §1.4", "9934 / 10000"),
        ("10067 / 10000     -- interim candidate; fixed by rule W of §1.4", "10066 / 10000"),
        ("97286 / 100000", "97245 / 100000"), ("102714 / 100000", "102755 / 100000"),
        ("2714 / 100000", "2755 / 100000"), ("2714/100000", "2755/100000"), ("2.714 %", "2.755 %"),
        ("[0.97286, 1.02714]", "[0.97245, 1.02755]")]
def sub(t):
    for a, b in SUBS:
        t = t.replace(a, b)
    return t
def normalize(path):
    t = Path(path).read_text()
    t = re.sub(r"\A/-\nCopyright.*?-/\n", "", t, flags=re.S)
    t = t.replace("-- FROZEN_ANCHOR_PREFIX_BEGIN\n", "", 1)
    t = re.sub(r"\n/-!\n# Frozen .*?-/\n", "", t, count=1, flags=re.S)
    # the proof body (D-SOF-6 `by sorry`, or the sealing `by exact ...`) is outside the frozen prefix/suffix;
    # it is read as the approved `sorry`
    t = re.sub(r"(  -- FROZEN_ANCHOR_PROOF_BEGIN\n).*?(  -- FROZEN_ANCHOR_PROOF_END\n)", r"\1  sorry\n\2", t,
               count=1, flags=re.S)
    return t
SPLITS = {  # D-SOF-5: (file, first part) -> the line was split at the one space after it
    "SoCoeffPoly": ["/-- The coefficient polynomials `A_m(e)` of the model (zero outside `1 ≤ m ≤ 7`);"],
    "LunarBarriers": ["/-- **Theorem A (continuous form).** In the seven-mode lunar spin–orbit model there are two",
                      "continuous barrier graphs with values in the band `[0.97245, 1.02755]`, the lower one strictly below"],
    "LunarSpinConfinement": ["`lunarPLo < p₀ < lunarPHi` (any angles) has a global solution, unique among global solutions, and"]}
def unsplit(stem, t):
    for first in SPLITS.get(stem, []):
        assert first + "\n" in t, (stem, first)
        t = t.replace(first + "\n", first + " ", 1)
    return t
ok = True
D = "KAM/Frozen/SpinOrbit/Defs/"
for stem in ["SoEcc", "SoEps", "SoCoeffPoly", "SoA", "SoModes", "SoV", "SoField", "SoBarrier"]:
    good = unsplit(stem, normalize(D + stem + ".lean")) == blocks1[stem]
    ok &= good; print(f"{stem:22s} {'IDENTICAL' if good else 'DIFFERS'} (FREEZE-PROPOSAL §1, complete file body)")
# window: P2 §1.2 gives the two declarations; the file shape is FREEZE-PROPOSAL §1.9-1.10
win1 = re.search(r"### 1\.9–1\.10.*?```lean\n(.*?)```", P1, re.S).group(1)
for stem, decl in [("LunarPLo", p2[0]), ("LunarPHi", p2[1])]:
    d = sub(decl).strip("\n")
    exp = re.sub(r"/-- Lower end.*?\n.*?\n", d + "\n", win1, flags=re.S)
    good = normalize(D + stem + ".lean") == exp
    ok &= good; print(f"{stem:22s} {'IDENTICAL' if good else 'DIFFERS'} (P2 §1.2 declaration in the P1 §1.9 file shape)")
T = "KAM/Frozen/SpinOrbit/Theorems/"
A = sub(p2[2])
# the approved block carries the prefix marker and a docstring placeholder; normalize() strips both kinds of line
Aexp = A.replace("-- FROZEN_ANCHOR_PREFIX_BEGIN\n", "", 1).replace(
    "/-! # Frozen theorem `KAM.SpinOrbit.lunar_barriers` (docstring as in the precedent) -/\n\n", "")
good = unsplit("LunarBarriers", normalize(T + "LunarBarriers.lean")) == Aexp
ok &= good; print(f"{'LunarBarriers':22s} {'IDENTICAL' if good else 'DIFFERS'} (P2 §1.3 complete block, minus the docstring placeholder)")
# B and window: "same wrapper as A", with the imports listed in §1.3 and their own declaration block.
# The expected complete file is A's wrapper with A's import lines and A's declaration region (docstring
# through FROZEN_ANCHOR_PROOF_END) replaced; the frozen file must equal it exactly (no substring test).
A_IMPORTS = ("public import KAM.Frozen.SpinOrbit.Defs.SoBarrier\npublic import KAM.Frozen.SpinOrbit.Defs.LunarPLo\n"
             "public import KAM.Frozen.SpinOrbit.Defs.LunarPHi\nimport KAM.Provider.SpinOrbit.LunarBarriers\n")
i0 = Aexp.index("/-- **Theorem A")
i1 = Aexp.index("  -- FROZEN_ANCHOR_PROOF_END\n") + len("  -- FROZEN_ANCHOR_PROOF_END\n")
assert Aexp.count(A_IMPORTS) == 1
for stem, blk, defs in [("LunarSpinConfinement", p2[3], ["SoField", "LunarPLo", "LunarPHi"]),
                        ("LunarWindow", p2[4], ["LunarPLo", "LunarPHi"])]:
    imports = "".join(f"public import KAM.Frozen.SpinOrbit.Defs.{d}\n" for d in defs)
    imports += f"import KAM.Provider.SpinOrbit.{stem}\n"
    exp = (Aexp[:i0] + sub(blk) + Aexp[i1:]).replace(A_IMPORTS, imports, 1)
    good = unsplit(stem, normalize(T + stem + ".lean")) == exp
    ok &= good; print(f"{stem:22s} {'IDENTICAL' if good else 'DIFFERS'} (A's wrapper with the §1.3 imports and declaration block)")
print("ALL IDENTICAL" if ok else "MISMATCH")
raise SystemExit(0 if ok else 1)

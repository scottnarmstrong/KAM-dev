#!/usr/bin/env python3
"""Freeze the twelve D41-approved W drafts (docs/tracks/W/drafts @ ffcbdb93) into KAM/Frozen/Wave.
Declaration blocks (`namespace KAM.Wave` .. `end KAM.Wave`) are copied byte for byte; only the header changes:
draft marker comment dropped, `KAM.Wave.Defs.X` imports -> `KAM.Frozen.Wave.Defs.X`, module docstring retitled with
a frozen/approval paragraph, and for the theorem the anchor markers and the provider import."""
import json, re, subprocess, sys, textwrap
from pathlib import Path
root = Path(sys.argv[1])
def show(p): return subprocess.run(["git", "-C", str(root), "show", f"ffcbdb93:{p}"], capture_output=True, text=True, check=True).stdout
D = "docs/tracks/W/drafts/KAM/Wave"
names = {"Lam": "lam", "SineMode": "sineMode", "EllWeight": "ellWeight", "WaveSpace": "WaveSpace", "Coeff": "coeff",
         "ReconU": "reconU", "ReconV": "reconV", "CubicGrad": "cubicGrad", "LinearTorus": "linearTorus",
         "IsAnalyticTorusEmbedding": "IsAnalyticTorusEmbedding", "IsClassicalSolution": "IsClassicalSolution"}
APPROVAL = ("Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit "
            "ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an "
            "owner-approved versioned successor.")
out = {}
# Deviation D-WF2 (main orchestrator ruling, 2026-10-30): two docstring-only fixes, ABI unchanged.
DOCFIX = {"ReconV": {"`q = coeff y` (P96-W p. 277). -/": "`p = coeff y` (P96-W p. 277). -/"},
          "Nlw2": {"/-- **W-NLW2 (proposed).** For": "/-- **W-NLW2.** For"}}
# Deviation D-WF1 (lint: lines over 100 characters): one space -> newline in three declaration docstrings.
WRAP = {"(positivity is part of the carrier, W-ST1), period-one angle": "(positivity is part of the carrier, W-ST1),\nperiod-one angle",
        "φ_j(x)`, where `q = coeff y` (P96-W p. 277). -/": "φ_j(x)`, where\n`q = coeff y` (P96-W p. 277). -/"}
def convert(sub, stem, name, thm):
    src = show(f"{D}/{sub}/{stem}.lean.txt")
    lines = src.split("\n")
    assert lines[5].startswith("-- DRAFT (W-STMT rev1)"), stem
    copyright = "\n".join(lines[:5]) + "\n"
    ns = src.index("\nnamespace KAM.Wave\n") + 1
    head = "\n".join(lines[6:]) [: ns - len("\n".join(lines[:6])) - 1]
    block = src[ns:]
    assert block.endswith("end KAM.Wave\n\nend\n"), stem
    for a, b in WRAP.items():
        if a in block: block = block.replace(a, b, 1)
    for a, b in DOCFIX.get(stem, {}).items():
        assert block.count(a) == 1, (stem, a); block = block.replace(a, b, 1)
    head = re.sub(r"(?m)^public import KAM\.Wave\.Defs\.", "public import KAM.Frozen.Wave.Defs.", head)
    m = re.search(r"/-!\n# (.*?)\n\n(.*?)\n-/\n", head, re.S)
    body = m.group(2)
    if thm:
        assert body.endswith(" The proof body is `sorry` in this draft only.")
        body = body[: -len(" The proof body is `sorry` in this draft only.")]
        extra = (f" Only the proof body between the markers may change, and only to "
                 f"`by exact KAM.Provider.Wave.{name} hm` when the provider `KAM.Provider.Wave.{stem}` is complete "
                 f"(sealing).")
        title = f"Frozen theorem `KAM.Wave.{name}` (W-NLW2)"
    else:
        extra = ""
        title = f"Frozen definition `KAM.Wave.{name}`"
    newdoc = f"/-!\n# {title}\n\n{body}\n\n" + textwrap.fill(APPROVAL + extra, 100, break_on_hyphens=False) + "\n-/\n"
    head = head[: m.start()] + newdoc + head[m.end():]
    if thm:
        head = head.replace("public import KAM.Frozen.Wave.Defs.ReconV\n",
                            "public import KAM.Frozen.Wave.Defs.ReconV\nimport KAM.Provider.Wave.Nlw2\n")
        assert "import KAM.Provider.Wave.Nlw2" in head
        stmt, tail = block.split(" := by\n  sorry\n\nend KAM.Wave\n\nend\n")
        assert tail == ""
        text = (copyright + "-- FROZEN_ANCHOR_PREFIX_BEGIN\n" + head + stmt +
                " :=\n  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by sorry\n  -- FROZEN_ANCHOR_PROOF_END\n"
                "-- FROZEN_ANCHOR_SUFFIX_BEGIN\n\nend KAM.Wave\n\nend\n-- FROZEN_ANCHOR_SUFFIX_END\n")
        rel = f"KAM/Frozen/Wave/Theorems/{stem}.lean"
    else:
        text = copyright + head + block
        rel = f"KAM/Frozen/Wave/Defs/{stem}.lean"
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text, encoding="utf-8")
    out[name] = ["theorem" if thm else "def", rel, "KAM.Wave"]
for stem, name in names.items(): convert("Defs", stem, name, False)
convert("Theorems", "Nlw2", "nlw2", True)
prov = root / "KAM/Provider/Wave/Nlw2.lean"; prov.parent.mkdir(parents=True, exist_ok=True)
prov.write_text(show(f"{D}/Defs/Lam.lean.txt").split("-- DRAFT")[0] + "module\n\n/-!\n# Provider for the frozen theorem `KAM.Wave.nlw2`\n\n" + textwrap.fill(
    "The proof of `KAM.Wave.nlw2` is assembled here as `KAM.Provider.Wave.nlw2`, from graph predecessors and "
    "approved external inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module "
    "other than the anchor may import it.", 100, break_on_hyphens=False) + "\n-/\n", encoding="utf-8")
print(json.dumps(out, indent=1))

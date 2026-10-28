# E1 prover handoff (branch inp-p14-e1, 122dbaee; off inp; offloaded P14 package run by the main orchestrator)


**Files:** new `KAM/Planetary/Exponential/Dictionary.lean` (91 lines). No other file touched.

**Declarations (namespace KAM.Planetary):**
- `sec_domain_chart_facts` (`bpP:p14:sec-domain#chart-facts`), statement copied verbatim from P14Signatures.lean.
- `poincareProd_planet_facts` (helper, per-planet dictionary: action, axis, cross product).
- `poincareProd_image_prograde`: general-n prograde onto bridge,
  `poincareProd m 1 '' poincareProdDom n = {z | ProgradeElliptic m z}`. The signature file has no
  declaration for this bridge (design row E1 lists it only as "general-n prograde onto bridge"), so
  this name and statement are mine; it is a two-line corollary of `poincareProd_image` and
  `regionProd_one_iff`. Both new names were grepped: unused elsewhere in KAM.

**Approach:** componentwise from `poincare_elements` (per planet i) via `poincareProd_block`;
keplerEnergy/Axis/Action unfold to energyMK/axisMK/actionMK at kappa = 1. Prograde from
`regionProd_one_iff` + `poincareProd_mem_regionProd`. AMD: sum of (action - cross) = sum of Gamma_i.

**Checks:**
- Gate build `KAM.Planetary.Exponential.Dictionary`: "Build completed successfully", no warnings in my file.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK, no over-100-char lines in my file.
  It reports "KAM.lean is out of date" (generated; not edited, orchestrator regenerates).
- `#print axioms` of both theorems: propext, Classical.choice, Quot.sound.

**Uncertainties / errata / deviations:** none. No heartbeat issues. No frozen/provider imports
(frozen Defs only). No `EuclideanSpace`.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E1 and its proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean): (1) sec_domain_chart_facts = signature file EXACTLY, and the E1 slice COMPLETE (read the design row and proof plan line by line; a sibling package failed for an omitted proof-plan obligation); (2) the unsigned general-n prograde onto bridge poincareProd_image_prograde: is it exactly what the design's E1 row means, at the generality later consumers (E3/E4, Exponential) need? (3) proof soundness; no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/Exponential/Dictionary.lean.

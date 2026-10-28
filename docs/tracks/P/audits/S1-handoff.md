# S1 prover handoff (branch inp-p14-s1, ab0cbaf7; off inp; offloaded P14 package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/Chart.lean` (~143 lines). KAM.lean untouched (lint reports it out of date; generated, orchestrator regenerates).

**Declarations:** `KAM.Planetary.sb_chart` (bpP:p14:sb-chart), statement copied verbatim from P14Signatures.lean. Internal steps sb-ch-a..d are
inline obligations (a: radicand/|v|^2=1-k^2/e<1/k=sqrt/Gamma identity; b: Cauchy-Schwarz via `abs_planeDot_le`; c: identity via private
`sbChart_identity` and squaring; d: radial bounds). Private helpers `sbChart_*` (names grep-checked unique). This is the only S1 declaration and
only S1 graph rows (bpP:p14:sb-chart, stepP:p14:sb-ch-a..d); no row belongs elsewhere.

**Approach:** write k=1-G/L, R=(1-G/(2L))/L, show |v|^2=R*2G=1-k^2, then planeSq of (k c - v + s v) = (1-x)^2 with s=x/(1+k), take roots.

**Checks:** `inp_lake_build.sh ... KAM.Planetary.SecularBox.Chart`: Built successfully, no warnings/sorry. `scripts/lint_sources.sh`: passes for my file
(initial >100-char lines fixed); only "KAM.lean is out of date" remains (generated file, not mine). Frozen guard and ABI hashes OK.
`#print axioms KAM.Planetary.sb_chart`: [propext, Classical.choice, Quot.sound].

**Imports:** Frozen Defs only (no providers/theorem anchors) + KAM.Kepler.Plane.
**Uncertainties / errata / deviations / design signals:** none. No heartbeat overrides. `hm` is used only for axis positivity.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row S1 and node rows bpP:p14:sb-chart, stepP:p14:sb-ch-a..d; its proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~412): (1) sb_chart = signature file EXACTLY, and the S1 slice COMPLETE: each step sb-ch-a..d is inline; check that every literal conclusion of those graph rows is actually established (the design may treat them as local obligations; confirm against the node table and blueprint b, and fail if a graph row's conclusion is absent); (2) proof soundness: radicand and |v|^2 = 1-k^2 identity, Cauchy-Schwarz via abs_planeDot_le, the squaring/root step with s = x/(1+k), the radial bounds; hm used only for axis positivity: confirm it is a signature premise; no added premises; (3) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/SecularBox/Chart.lean.

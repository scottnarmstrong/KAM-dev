# E8 prover handoff (branch inp-p14-e8, ef224888; off inp; offloaded P14 package run by the main orchestrator)


**Files:** KAM/Planetary/Exponential/UniformData.lean (new, ~167 lines).

**Declarations:** `KAM.Planetary.uniform_data` (verbatim from P14Signatures.lean, proved). Helpers (all new,
grepped for clashes): `udZero_fst`, `udZero_fst_natAdd`, `udZero_snd`, `udShift_fst_castAdd`,
`udShift_fst_natAdd`, `udShift_snd`, `udAngle`, `udAngle_continuous`, `udCell_isCompact`.
Graph steps: `stepP:p14:ud-cell` = `udCell_isCompact` + cell inclusion `C ⊆ W`/`hmemC` in the proof;
`stepP:p14:ud-transl` = the `key`/`hW'` translation by `fastShift ⌊λ/2π⌋` in the proof. `bpP:p14:uniform-data` = the theorem.

**Approach:** adapt `gen_uniform_periodic`. Compact cell C = image of [-π,3π]ⁿ × Q under (λ,z) ↦ z + (append λ 0, 0);
C ⊆ W by hQW/hQ0. δ = min δ₀ π with δ₀ from `exists_cthickening_subset_open`; D = cthickening δ C compact; `gen_lip` on D
gives M,L. For x in the cylinder, shift by fastShift ⌊x.1_i/2π⌋ lands x in C and the δ-ball in D; periodicity (hWp,hFp)
transfers membership, norm and Lipschitz bounds. delta ≤ π by construction.

**Checks:** gate build `KAM.Planetary.Exponential.UniformData` succeeded (exit 0, no warnings in my file);
`scripts/lint_sources.sh`: my file passes (line-length fixed); only reported item is "KAM.lean out of date" (generated, not mine).
`#print axioms KAM.Planetary.uniform_data`: [propext, Classical.choice, Quot.sound].

**Uncertainties / design signals:** none; no heartbeat overrides. Whole-file elaboration with `import Mathlib` is slow standalone (minutes) but builds in 15s through gate.
No errata, no deviations. No other-package graph steps found in the E8 node table.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E8 and node rows bpP:p14:uniform-data, stepP:p14:ud-cell, ud-transl; its proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~333): (1) uniform_data = signature file EXACTLY, and the E8 slice COMPLETE: the steps ud-cell and ud-transl are inside the proof (udCell_isCompact exported; the translation by fastShift floor(lambda/2pi) inline): decide whether each graph row's literal conclusion is established (siblings failed for unexported cuts; fail only if a literal conclusion is absent); (2) proof soundness: the compact fundamental cell, the translation argument, delta <= pi; gen_lip and the compact-neighborhood API consumed as designed; no added premises; (3) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/Exponential/UniformData.lean.

# P4-LT prover handoff (branch inp-p4lt, 2001d8f; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGMeasure/LatticeTail.lean` (178 lines), commit 2001d8f on inp-p4lt. No other file touched (KAM.lean not regenerated: lint notes "out of date", expected).

**Declarations** (namespace `KAM.Planetary`, signatures verbatim from P45Signatures.lean):
`latticeWeight`, `lattice_tail` (bpP:p4:lattice-tail), `latticeS`. Helpers: `rpow_neg_succ_le`, `sum_Ioc_rpow_neg_le`, `tail_finset_le`.

**Approach:** parts 1–2: `KAM.Measure.lattice_sum` with τ := tau-1 (exponent and constant rewritten by ring). Tail (stepP:p4:lt-b): fibre the finite sums over ℓ¹-radius r > ⌊m⌋₊, shell bound `KAM.Measure.sum_sphere_le` (2·3^(n-1) r^-(q+1), q=tau+1-n), telescoping `q x^(-q-1) ≤ (x-1)^-q - x^-q` (Bernoulli, `one_add_mul_self_le_rpow_one_add`, needs q ≥ 1, true as tau>n), then ⌊m⌋₊ ≥ m/2. Finite-set bounds pass to tsum via `tsum_le_of_sum_le'`.

**Checks:** `inp_lake_build.sh ... KAM.Planetary.PGMeasure.LatticeTail`: Build completed successfully, no warnings. `scripts/lint_sources.sh`: only "KAM.Lean out of date" note; check_lean_modules, frozen-anchor guard, ABI hashes PASS.
`#print axioms KAM.Planetary.lattice_tail` and `latticeS`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat overrides; no signature changes; no quarantined imports (imports Mathlib, KAM.Measure.Lattice). Statement is true as written.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-LT and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures (lattice_tail, latticeS), consuming KAM.Measure.lattice_count / lattice_sum as designed; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/LatticeTail.lean.

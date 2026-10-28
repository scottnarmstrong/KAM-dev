# S7-1 prover handoff (branch inp-s71, 6e9abdd; off inp (N67 design merged); offloaded package run by the main orchestrator; prover on claude-12)


**Files (new):** `KAM/Nekhoroshev/Stability/Setting.lean` (≈250 lines), `KAM/Nekhoroshev/Stability/RealSystem.lean` (≈120 lines).
Module path follows the brief (`KAM/Nekhoroshev/Stability/...`); namespace `KAM.Stability` as in the signatures. Also on the
branch (identical blob, copied with `git checkout inp-n61 -- KAM/Nekhoroshev/NormalForm/Setting.lean`): N6-1's
`KAM/Nekhoroshev/NormalForm/Setting.lean` (commit 2fd6a16), needed only for `freq` in `freq_realInclusion`. It is byte-identical to
inp-n61's, so merging inp-n61 should be conflict-free; if N6-1 changes before landing, take N6-1's version.

**Nodes / declarations proved (statements verbatim from `NPart67Signatures.lean`, `IsActionNorm` as revised in v2):**
- p7 setting: `cpx`, `realNbhd`, `realStrip`, `realH`, `IsOrbit`, `reMap`, `thetaGradR`, `hessR` (defs); `isOpen_realNbhd`,
  `realNbhd_mono`, `realInclusion₂_mem_Dom_iff`, `realHamiltonian_eq_realH` (`rfl`), `freq_realInclusion`.
- `IsActionNorm` (with `map_zero`, `smul`), `isActionNorm_norm`, `isActionNorm_euclid` (Minkowski via Cauchy-Schwarz, no `EuclideanSpace`).
- `exit_ball`: IVT-style first-hit lemma (`first_hit`, private) on `[0,b]`; negative `t₁` by time reversal of the same lemma.
  Uses only `continuous`, `map_zero` of the norm (as predicted by audit F1).
- `real_system` (a)-(d): `holomorphic_regularity_of_finiteDimensional` + `restrict_scalars` + composition with `realInclusion₂` and `reCLM`;
  periodicity via `KAM.periodic_int_shift`; (b) `hamiltonian_real_fderiv`/`hamiltonianVectorField_eq_of_real`; (c) `ham_smooth_c1`,
  `ham_periodic`; (d) `ham_energy`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-s71 KAM.Nekhoroshev.Stability.Setting` and `...RealSystem`: `Build completed successfully (3182 jobs)`, no warnings, no sorry.
- `#print axioms` for `real_system`, `exit_ball`, `freq_realInclusion`, `isActionNorm_euclid`, `isActionNorm_norm`,
  `realInclusion₂_mem_Dom_iff`, `realHamiltonian_eq_realH`, `isOpen_realNbhd`, `realNbhd_mono`: all `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: no complaints about my files (after wrapping 3 long lines); the only remaining message is
  `KAM.lean is out of date; run scripts/gen_root_imports.py` (generated root file; not edited, orchestrator regenerates). Module check PASS,
  frozen-anchor guard OK, ABI hashes OK.

**Uncertainties / deviations:** none in statements. No heartbeat issues; no `set_option`. Files well below 1500 lines.
**Suspected errata:** none.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-1 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md, esp. F1 (IsActionNorm must exclude shifted norms; exit_ball true as revised); blueprint-N p7 setting, real-system, exit-ball): (1) statements = design v2 signatures and blueprint; IsActionNorm is the revised structure and exit_ball holds for it; (2) definitions are the intended objects; (3) hygiene (lint incl. 100-char lines). Audit ONLY the S7-1 module(s) (KAM/Nekhoroshev/Stability/Setting*, RealSystem*).

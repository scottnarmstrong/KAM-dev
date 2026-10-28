# N6-4 prover handoff (branch inp-n64, 1258c59; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/NormalForm/Telescope.lean` (130 lines). No other file touched (KAM.lean not edited; lint reports it out of date, as expected — orchestrator regenerates).

**Nodes:** `bpN:p6:telescope` -> `KAM.NormalForm.chain` and `KAM.NormalForm.telescope`, signatures copied verbatim from NPart67Signatures.lean A.5 (namespace `KAM.NormalForm`, module path under `Nekhoroshev/NormalForm`).

**Approach:** three private helper lemmas, each by induction on `m` (`chain_mapsTo`: MapsTo.comp; `chain_disp`: split `chain(m+1) z - z` and use `map_add_le_add` plus `Finset.sum_range_succ` (audit N5, no `map_sum_le`); `chain_diff_sympl`: `DifferentiableOn.comp`, `fderiv_comp` at points of the open sets, symplectic identity applied twice, using the openness convention of audit N4). Injectivity by induction with `InjOn.comp`. Imports only `KAM.Canonical.SymplecticForm`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n64 KAM.Nekhoroshev.NormalForm.Telescope`: Build completed successfully, no warnings.
- `scripts/lint_sources.sh`: no long lines; check_lean_modules PASS; FROZEN-ANCHOR GUARD OK; ABI HASHES OK; only message is "KAM.lean is out of date" (generated file, not edited per rules).
- `#print axioms KAM.NormalForm.telescope`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. No heartbeat problems; no overrides used.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-4 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 telescope): (1) statements = design v2 signatures and blueprint; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N6-4 module(s) (KAM/Nekhoroshev/NormalForm/Telescope*).

# N2-KERNEL prover handoff (branch inp-n2k, 75d8421; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/QcZero/Kernel.lean` (about 140 lines). Nothing else changed. `KAM.lean` not regenerated (rule 10); the orchestrator must run `scripts/gen_root_imports.py`.

**Nodes proved** (signatures verbatim from N2Signatures.lean):
- `bpN:p2:qc-kernel` -> `KAM.Nekhoroshev.bordered_map` (def), `qc_kernel`
- application formula -> `bordered_map_apply`
- `stepN:p2:qk-eqs` -> `qk_eqs`; `stepN:p2:qk-pair` -> `qk_pair`; `stepN:p2:qk-scalar` -> `qk_scalar`
- `stepN:p2:qk-bij` -> second conjunct of `qc_kernel`

**Approach:**
- `bordered_map_apply`: `Prod.ext` plus `simp [bordered_map, mul_comm]`.
- `qk_eqs`: `Prod.mk_eq_zero`.
- `qk_pair`: pair the second equation with `v` and sum. The first equation cancels the `u` term, leaving `lam * Q = 0`, so `Q = 0`. The hypothesis `hA` then forces `v = 0`.
- `qk_scalar`: with `v = 0`, a nonzero coordinate of `freq` gives `u = 0`.
- `qc_kernel`: trivial kernel via `LinearMap.ker_eq_bot'`. Surjectivity from `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, with finrank n+1 = 1+n by `Module.finrank_prod`.
- Symmetry of `A` is not used.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n2k KAM.Nekhoroshev.QcZero.Kernel`: "Build completed successfully (2173 jobs)", no warnings in my file.
- `#print axioms` of `qc_kernel`, `bordered_map_apply` and `qk_scalar`: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/lint_sources.sh`: `check_lean_modules` PASS, frozen-anchor guard OK, ABI hashes OK. It reports "KAM.lean is out of date" (expected, since I may not edit it). It also reports one over-100-character line at `KAM/Planetary/Hamiltonian/Liouville.lean:35`, which predates my work.

**Uncertainties / errata / deviations:** none. No statement was changed or needed an extra hypothesis. No heartbeat issues, no `set_option` overrides.

AUDIT FOCUS (design docs/tracks/N/design/N2-LEAN-DESIGN.md row N2-KERNEL and proof plan; its audit DESIGN-N2-design-audit-1.md; signatures .drafts/design/N2Signatures.lean; blueprint-N p2 bordered map / qc kernel nodes): (1) statements = design signatures and blueprint (bordered_map, application formula, qk equations/pair/scalar, qc_kernel); (2) proofs sound (finite-dimensional injective <-> surjective used correctly); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N2-KERNEL module(s) listed in the handoff.

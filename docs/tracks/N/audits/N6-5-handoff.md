# N6-5 prover handoff (branch inp-n65, 52bb0ed; contains inp-n62 (N6-1, N6-2) and inp-c510 (C5-10), all delivered; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/NormalForm/IterativeMap.lean` (~165 lines). Nothing else changed (KAM.lean not regenerated).

**Declarations (signatures copied verbatim from NPart67Signatures.lean A.4):** `iterMap`, `iterG`, `iterF`,
`IterHyp`, `iterU`, `iterative_direct_a`, `iterative_direct_b`, `iterHyp_of_source`. Helpers (new, namespace
`KAM.NormalForm.IterHyp`): `conjExp_pos`, `iterU_le` (`iterU ≤ 1/4`), `canon` (`CanonData` for `homGen` from
`homological_direct`: class, bound `qδ/(2πα)`, `ρ<r/2`, `σ<s/2`, `Φ/(ρσ) ≤ 1/4 ≤ 1/2`), `phi_div`.

**Approach:** `iterMap` is `flow … (Dom (r-ρ)(s-σ)) 1`, definitionally `hd.omega`. (a) = `canonical_map_a` (diff./maps-to),
`_d` (symplectic), `_b.1` (integer translations), `_e.1` (left inverse); InjOn by applying the left inverse `flow(-1)`
to `Φ x = Φ y`. (b) = `canonical_map_a` (scaled norm and components), `canonical_map_c` (derivative), with
`Φ/(ρσ) = iterU` and `field_simp` for components. `iterHyp_of_source` = constructor with `divisor` (N6-1) `.2`.

**Checks:** `inp_lake_build.sh /root/code/KAM-inp-n65 KAM.Nekhoroshev.NormalForm.IterativeMap` → success, no warnings in file
(after renaming an unused binder). `#print axioms` of iterative_direct_a, iterative_direct_b, iterHyp_of_source:
`[propext, Classical.choice, Quot.sound]` each. `scripts/lint_sources.sh`: my file clean; reported items are pre-existing/not mine:
`KAM/Planetary/Hamiltonian/Liouville.lean:35` >100 chars, and `KAM.lean is out of date` (generated; the orchestrator regenerates).
check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK. No `sorry`, no maxHeartbeats, no frozen imports/providers.

**Uncertainties / errata / deviations:** none. No design signals (builds in ~3 s). Statements `iterative_direct_c,d,e` belong to N6-6/N6-7.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-5 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 iterative (a),(b)): (1) statements = design v2 signatures and blueprint; iterHyp_of_source discharges the source hypotheses (no added premises); (2) proofs sound, consuming C5-10 canonical_map and N6-2 homological as designed; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N6-5 module(s) (KAM/Nekhoroshev/NormalForm/IterativeMap*).

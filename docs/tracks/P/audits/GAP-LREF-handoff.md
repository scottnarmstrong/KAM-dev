# GAP-LREF prover handoff (branch inp-glref, 65b96b5b; off inp; graph-gap programme package run by the main orchestrator)


Files (new): KAM/Planetary/Hamiltonian/PeriodOneNodes.lean, KAM/Planetary/Newtonian/LeftoverNodes.lean,
KAM/Planetary/Nondegeneracy/ConvNodes.lean; KAM.lean regenerated with scripts/gen_root_imports.py.

| Node | Declaration |
|---|---|
| stepP:p1:pc-c | KAM.Planetary.period_convert_bundle (PeriodOneNodes) |
| stepP:p6:pl-a | KAM.Planetary.planeLength_algebra |
| stepP:p6:pl-b | KAM.Planetary.planeLength_norm_bounds |
| stepP:p6:pl-c | KAM.Planetary.planeLength_smooth_deriv (C^infinity, `v ≠ 0` only guard) |
| stepP:p6:dom-smooth | KAM.Planetary.hamiltonians_contDiffOn (C^infinity literal form, from analyticity) |
| stepP:p6:rc-pack | KAM.Planetary.reconstruction_pack |
| stepP:p6:ot-apply | KAM.Planetary.orbit_transfer_pack |
| bpP:p10:conv#data (cone clause) | KAM.Planetary.SecularForm.smul_mem_axes (ConvNodes; `0<c`, `a ∈ axes n` ⇒ `c • a ∈ axes n`; no prior lemma existed) |

Approach: statements as proposed in LREF-P-audit-1.md (names changed). Six are pairings of landed
declarations. pc-c re-proves locally the injectivity and symplectic-pullback conjuncts from
`fderiv_periodOne` (no private-lemma export needed); uses `fastShift_eq_angleScale` for (d).
dom-smooth uses `AnalyticOnNhd.contDiffOn` with `isOpen_collisionFreeDomain`.

Checks: `inp_lake_build.sh` on the three modules: "Build completed successfully (9125 jobs)", no
warnings in new files. `#print axioms` of all eight: [propext, Classical.choice, Quot.sound].
`scripts/lint_sources.sh`: check_lean_modules PASS (1226 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK
(after regenerating KAM.lean).

Uncertainties: none. Errata: none. Deviations: none (no heartbeat issues).

ORCHESTRATOR RULING (OVERNIGHT 03:15, 03:20): seven one-line bundles for step nodes whose content is proved but split across landed declarations, from the proposed statements in the LEAN_REF audit (branch inp-lrefaud, docs/tracks/P/audits/LREF-P-audit-1.md, section 'Exact one-line bundle statements'), plus the positive-dilation (cone) lemma that the definitions audit DEFS-P2 found missing for bpP:p10:conv#data.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites; compare the export with the LREF-P report's proposed statement and with the node; give a per-node verdict: does the ONE named declaration state that node's literal conclusion under only the source's hypotheses, quantifiers in source order? (dom-smooth and pl-c: C^infinity literal form.) Audit ONLY KAM/Planetary/Hamiltonian/PeriodOneNodes.lean, KAM/Planetary/Newtonian/LeftoverNodes.lean and KAM/Planetary/Nondegeneracy/ConvNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

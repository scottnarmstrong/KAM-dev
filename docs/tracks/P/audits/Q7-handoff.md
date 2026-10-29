# Q7 prover handoff (branch inp-p11c-q7, b3dc2a0c; contains Q6 (in audit) and B20; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/Quantitative/Physical.lean` (~165 lines). Commit "Q7: physical_interface". No other file touched.

**Declarations:** `KAM.Planetary.physical_interface` (verbatim signature; graph node `bpP:p11a:physical-interface`,
local steps pi-zero/pi-a/pi-b/pi-c/pi-d all covered by the 13 conjuncts). Private helpers only:
`volume_eq_hausdorff`, `volume_image_lipschitzOn`, `exists_fract_decomp`.

**Approach:** measure clauses from `Q.measure`, `Q.cell_lower`, `Q.borel`, `NumericalValid` (`epsLoss < vol K`);
upper bound via Lipschitz image under `μH[2N]` (isometry `sumArrowIsometryEquivProdArrow`, `hausdorffMeasure_pi_real`);
curves from `IsLatticeTorus` flow clause; local uniqueness by `KAM.ODE.gen_uniqueness` with `ham_smooth_c1`
(realDomain open via `Head.isOpen_actionNbhd`); b = b' from equivariance + `Q.lower`; compact fundamental
domain and saturation by integer/fractional decomposition. No Q6 import needed (Interface only).

**Checks:** `inp_lake_build.sh ... KAM.Planetary.Quantitative.Physical` -> success, no warnings in my file.
`scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only note: "KAM.lean is out of date"
(generated; orchestrator regenerates; I did not edit it). Lines <= 100 cols.
`#print axioms KAM.Planetary.physical_interface`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none; no statement changed. Coverage note (already in design): node
`bpP:p11a:physical-interface` is absent from the graph slice. Statement conjunct 2 (0 < vol S) is derived from
conjunct 4 + 5; `d.Valid` supplies `ofReal epsLoss < vol K`. No heartbeat issues.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q7 (physical_interface; Q6, U1 measure/saturation/orbit, ODE uniqueness) and its node table incl. bpP:p11a:physical-interface and pi-* steps; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/Quantitative/Physical.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

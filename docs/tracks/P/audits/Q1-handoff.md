# Q1 prover handoff (P11C; branch inp-p11c-q1, 90e233c5; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Quantitative/Thresholds.lean` (108 lines). Nothing else changed.

**Declarations (copied verbatim from P11CSignatures.lean L45-L121):** QuantitativeData, NumericalValid, Valid, p11c_bump,
p11c_mollifier, p11c_mollifierMass, p11c_cutoffDerivative, p11c_cutoffConstant, diameter, varpi, cN, A0, cDio, gamma,
tbar, tflat, xibar, thetaMax, lambdaFlat, thresholds, p11c_oldThreshold. All are definitions; no proofs needed.
Not included (belong to other packages, as I read the Q1 row): BudgetOrder (Q2), unitCube/IsChart/IsLatticeTorus
(already in KAM, `PG/Setting`, `Hamiltonian/Chart`, `Hamiltonian/Transport`).

**Adapter added (no signature existed, so flag for review):** `QuantitativeData.cN_eq_p11C (N) : cN N = p11C N := rfl`,
identifying cN with the upstream `p11C` (MaximalStep/Constants, used by `fourier_cutoff`). Only import beyond Mathlib is
`KAM.Planetary.MaximalStep.Constants`. No upstream mollifier/cutoff-constant definition exists in KAM (grep "mollif" empty),
so `p11c_cutoffConstant` etc. have no identification lemma.
The signature file's `open KAM KAM.Kepler KAM.ODE` line was dropped (unneeded, namespace KAM.Kepler not imported).

**Checks:** gate build `KAM.Planetary.Quantitative.Thresholds`: success (no warnings). `scripts/lint_sources.sh`:
check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; only message "KAM.lean is out of date" (expected; not edited per rules).
Name-collision grep: none of the new public names exist elsewhere in KAM. No heartbeat overrides, no EuclideanSpace, no sorry.
`#print axioms`: not run (no theorem besides `rfl` adapter; definitions only).

**Uncertainties / errata / deviations:** none beyond the above. Statements untouched. No design signals.

AUDIT FOCUS (design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q1 and Appendix; audit DESIGN-P11C-design-audit-1.md; signatures .drafts/design/P11CSignatures.lean L45-L121): DEFINITIONS package: (1) every declaration = signature file exactly (the dropped 'open KAM KAM.Kepler KAM.ODE' line must not change any elaborated term); (2) each body means the source object on its whole carrier (constants and thresholds exactly as the source; no fallback branches); the added adapter QuantitativeData.cN_eq_p11C is true by rfl and identifies the right upstream object; (3) NAME CLASHES: several names are generic (diameter, varpi, cN, A0, cDio, gamma, tbar, thresholds...): confirm their fully qualified names do not collide with anything in KAM (whole-library co-import); (4) hygiene. Audit ONLY KAM/Planetary/Quantitative/Thresholds.lean.

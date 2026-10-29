# P11A-W3 prover handoff (branch inp-p11aw3, 1ebccee; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/WeakMeasure/DividedDifference.lean` (~130 lines). No other files; KAM.lean not edited
(lint reports "KAM.lean is out of date", expected: the orchestrator regenerates it).

**Proved:** `bpP:p11a:divided-difference` = `KAM.Planetary.divided_difference`, signature verbatim (incl. the unused `hab`,
which triggers an unused-variable linter warning only).
Helpers (distinct names): `P11RolleIcc`, `p11Rolle_step`, `p11Rolle_Icc` (iterated Rolle, `bpP:p11a:f-rolle`),
`p11_iteratedDeriv_eval`, `p11_iterate_derivative_interpolate` (interpolation coefficient, `stepP:p11a:dd-interp`).

**Approach:** interpolate f at the nodes with `Lagrange.interpolate`; its q-th derivative is the constant q!·(divided difference)
(`Lagrange.iterate_derivative_interpolate`). Rolle (`exists_deriv_eq_zero`) is applied q times to u = f − P by induction on the
number of nodes; Leibniz-free: `iteratedDeriv_fun_sub` at an interior point (f is C^q near ξ ∈ (a,b)).

**Checks:** gate build `KAM.Planetary.WeakMeasure.DividedDifference` succeeds (only the unused `hab` warning, no sorry);
`scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected); check_lean_modules PASS, frozen guard OK, ABI hashes OK.
`#print axioms KAM.Planetary.divided_difference`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations / design signals:** none. No heartbeat issues; no overrides used.
Module path: `KAM/Planetary/WeakMeasure/DividedDifference.lean` (design §6: paths under `KAM/Planetary/`).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W3 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (divided differences, the interpolation coefficient helper; Lagrange.interpolate and Rolle used correctly); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/WeakMeasure/DividedDifference*.lean.

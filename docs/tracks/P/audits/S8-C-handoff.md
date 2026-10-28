# S8-C prover handoff (branch inp-s8c, fcf9972; contains inp-s8l, inp-s9n (audited); offloaded package run by the main orchestrator; prover on claude-12; last commit is an orchestrator whitespace-only wrap)


**Files:** new `KAM/Planetary/SecularForm/Coefficients.lean` (~125 lines). Nothing else changed (KAM.lean untouched).

**Declarations (verbatim from P810Signatures.lean):** `pairA`, `pairB`, `constantTerm`, `qhat`, `coeffs`, `quad`,
`coeffs_hermitian`, `coeffs_analytic`; `SecularSpectrum.sigma` (after `coeffs_hermitian`, using S9-N `sorted`).
Helper: `pairB_comm` (public), private analyticity helpers.

**Approach:** Hermitian: `qhat` off-diagonal symmetric via `pairB_comm` (min/max commute), diagonal trivial.
Analytic: entrywise via `analyticAt_pi_iff`; ratio a_p/a_q lies in (0,1) on axes (StrictMono), composed with
S8-L `analyticOnNhd_laplace_def` (s=3/2); `√(action)` analytic since action>0 (`ContDiffAt.sqrt`); diagonal uses
`Finset.analyticAt_fun_sum` over `univ.erase i` (so i≠k).

**Checks:** gate build `KAM.Planetary.SecularForm.Coefficients`: success, no sorry/errors; only 3 deprecation
warnings (`ite_cond_eq_false`, lines 54, 111). `#print axioms` of `coeffs_hermitian`, `coeffs_analytic`, `sigma`:
all `[propext, Classical.choice, Quot.sound]` (check run, then the print lines removed).
`scripts/lint_sources.sh`: module check PASS, frozen guard OK, ABI hashes OK; only the expected
"KAM.lean is out of date" (generated, not edited by me; orchestrator regenerates).

**Uncertainties / errata / deviations:** none; no signature changed, no extra hypotheses. No heartbeat issues.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-C and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (pairA, pairB, constantTerm, qhat, coeffs, quad, coeffs_hermitian, coeffs_analytic, SecularSpectrum.sigma); (2) proofs sound (S8-L Laplace and S9-N sorted consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/SecularForm/Coefficients.lean.

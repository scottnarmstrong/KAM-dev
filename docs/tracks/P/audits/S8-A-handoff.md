# S8-A prover handoff (branch inp-s8a, d8edd6b; contains inp-s8p (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Planetary/SecularForm/AnalyticGeometry.lean` (258 lines): `planetC`, `separationC` (verbatim from the signatures), polydisc = ball around `center`, `rho` facts, `blockC` chart-neighbourhood membership, joint continuity of `planetC`, `2π`-periodic reduction to the cell, circular value of the chart and `(a_j-a_i)^2 ≤ Re s_ij` at the circular point, `exists_radius` (pa-circ, pa-unif: compactness of `cell ×ˢ closedBall`, uniform continuity, finite intersection of radii via `Filter.eventually_all` on `𝓝[>] 0`).
- `KAM/Planetary/SecularForm/AnalyticRegularity.lean` (146): `perturbationC`, `secularC` (verbatim), holomorphy/continuity of `planetC`, `separationC`, `perturbationC` on the polydisc (principal cpow on the slit plane from `Re s ≥ gap²/2 > 0`).
- `KAM/Planetary/SecularForm/AnalyticReal.lean` (118): `planetBlock_assemble`; restriction to real points via `poincare_holomorphic` (5th component), `poincareProd_block`; `s^(-1/2) = 1/planeLength`; `perturbationC_inclusion` (both models).
- `KAM/Planetary/SecularForm/Analytic.lean` (120): `inclusionCLM`, `isOpen_realDisc`, `secularC_inclusion`, `perturbation_analytic` (statement verbatim). pa-avg uses `e_param_cslow` (S8-P) and `KAM.analyticOnNhd_of_differentiableOn` (KAM/Strip/AnalyticTaylor, existing; Mathlib's version is one-variable only), then `AnalyticAt.restrictScalars`, composition with `inclusionCLM` and `Re`.
Facade: `KAM.Planetary.SecularForm.Analytic` (imports the three helpers). KAM.lean not touched (lint reports it is out of date; the orchestrator regenerates).

## Proved
`bpP:p8:perturbation-analytic` = `KAM.Planetary.SecularForm.perturbation_analytic`; steps pa-circ/pa-unif = `exists_radius` (with `re_separationC_center`, `separation_pair`), pa-hol = `differentiableOn_perturbationC`, `continuousOn_perturbationC`, `perturbationC_inclusion`, pa-avg = `perturbation_analytic` (secularC part).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-s8a KAM.Planetary.SecularForm.Analytic`: Build completed successfully (9120 jobs); no warnings in the S8-A files.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected; generated file); check_lean_modules PASS, frozen guard OK, ABI hashes OK; no >100 char lines.
- `#print axioms KAM.Planetary.SecularForm.perturbation_analytic`: [propext, Classical.choice, Quot.sound].
- No `set_option`, no `sorry`; all files < 260 lines. No frozen theorem or provider imported.

## Notes / uncertainties
- Signature unchanged; no extra hypotheses needed. `0 < n` (D.hn) used only to get nonemptiness for `rho`.
- No errata found; no deviations. The `rho`/poincareNbhd match (`‖ξ‖ < r ≤ √Λ/16`, `|Λ-Λ*| < r ≤ Λ/2`) is exact, so no slack was needed.
- Design signal: none (no heartbeat issues at defaults; one `isDefEq` timeout in an early draft was removed by not ascribing the composed `ContinuousOn` type).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-A and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures (perturbation_analytic, pa-circ/unif/hol/avg); (2) proofs sound (Poincare/Holomorphic, Models analytic formulas consumed as designed); no added premises; (3) hygiene. Audit ONLY SecularForm/Analytic*.lean (compare with branch inp-s8p).

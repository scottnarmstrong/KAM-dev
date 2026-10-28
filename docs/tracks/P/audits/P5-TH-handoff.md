# P5-TH prover handoff (branch inp-p5th, afb6301a; contains inp-p5fi and inp-p5par (audited); offloaded package run by the main orchestrator; prover on claude-10)


## Files (new)
- `KAM/Planetary/PGAssembly/Threshold.lean` (511 lines): `rstar`, `pgRstar`, `param_facts`, `r_k` (signatures verbatim,
  only line-wrapped), plus `ThrStatic`, `ThrSmall`, `eventually_static/small`, `thr_dynamic`, `thr_volumes`,
  `thrRange_of_admissible`, `pgAnalytic_dio`, `gammaBar_pos`, `pgBoundary_spec`, `volume_V_pos`, ...
- `KAM/Planetary/PGAssembly/ThresholdAlg.lean` (338): `pgCgamma` (+ `pgCgamma_pos`), `ThrRange`, parameter algebra
  (`gammaBar_le`, `gammaBar_ratio`, `rhoBar_le`, `l1_le_rhoBar`, `chat_Ehat_lt`, `rK_lt`, `params_*` unfolding lemmas).
- `KAM/Planetary/PGAssembly/ThresholdLimits.lean` (91): `tendsto_rpow_mul_log_rpow`, `sq_log_mono`,
  `le_log_inv_of_le_exp_neg`, `eventually_exists_radius`.
`Threshold` is the facade (public imports the other two). `pgCgamma` lives in ThresholdAlg (reached via Threshold).

## Approach
Every `rstar` requirement is a limit condition as r→0+. `ThrStatic d r` is exactly the 11 static conjuncts;
`ThrSmall d r` collects explicit r-only smallness (continuity/`r^m log^q → 0`). Both hold eventually in `𝓝[>] 0`,
so one radius `R = R0/2` works; the admissible-range conjuncts follow from `thr_dynamic` (pure algebra using
`PGScaleSpec`, `PGAnalyticSpec`, `collar`, the one-scale Diophantine measure bound). `ĉ Ê < 1` is evaluated
exactly (Ê = max{9C1⁴K0^{2τ+2}/κ0², 4C1²/κ1²}). `param_facts`/`r_k` only use the exported conclusions of `rstar`;
`r² (log 1/r)^{τ+1} ≤ 1` below R is recovered by `sq_log_mono` (monotone for r<R<e^{-(τ+1)}).
`(1+x)^b<2` via `1+x ≤ exp x`, `exp(1/768) < 1/(1-1/768) < 2`.

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-p5th KAM.Planetary.PGAssembly.Threshold`: success
  (9133 jobs), no warnings in my files, no sorry.
- `sh scripts/lint_sources.sh`: all my checks pass (line length, module, frozen-anchor, ABI hashes). The only
  non-zero item is "KAM.lean is out of date; run scripts/gen_root_imports.py" (new modules not yet in the generated
  root; orchestrator must regenerate; I did not edit KAM.lean).
- `#print axioms` rstar / pgRstar / param_facts / r_k: `[propext, Classical.choice, Quot.sound]` each.
- No `maxHeartbeats`, no `EuclideanSpace`; names checked against the whole of KAM for clashes (one clash,
  `rhoHat_pos` in TwoScale, avoided by renaming mine `params_rhoHat_pos`).

## Uncertainties / design signals
- No heartbeat problems at defaults. One big `nlinarith` in the first draft of `thr_dynamic` timed out; resolved by
  splitting into `thr_e5`, `thr_e6` with `linarith` (design note only).
- `pgCgamma` placed in ThresholdAlg rather than Threshold (reachable through the facade).

## Errata / deviations
- No suspected defect in the pinned source or signatures; signatures unchanged (line-wrapped only).
- Note: the source (r3) condition `C_γ √r* ≤ 2 M̄0 ρ_c` is reflected here as `Cγ√r/2 ≤ (pgAnalytic d).rho`
  (since M0 ≥ 1 and Kbar^{τ+1} ≥ 1) — internal to `ThrSmall`, not in any signature.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-TH, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) rstar, pgRstar, param_facts, r_k (and pgCgamma if signed) = signature file exactly (line wraps whitespace-only); (2) proofs sound (P5-PAR, P4-ONE, P4-CO, P5-FI consumed as designed; static/small/dynamic threshold and volume lemmas proved, not assumed; the heartbeat issue was fixed by splitting, confirm no budget override); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM: check the many new helper names such as gammaBar_*, params_*, thr_*). Audit ONLY KAM/Planetary/PGAssembly/Threshold*.lean.

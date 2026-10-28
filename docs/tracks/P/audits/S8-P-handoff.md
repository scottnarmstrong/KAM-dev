# S8-P prover handoff (branch inp-s8p, 8ed5fd2; contains inp-s8b (S8-B, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Branch** inp-s8p. **File (new):** `KAM/Planetary/SecularForm/ParameterIntegral.lean` (311 lines). All edits committed.

## Declarations (signatures verbatim from P810Signatures.lean)
- `SecularForm.e_param` (bpP:p8:e-param) — holomorphic parameter integral over `cell n`.
- `SecularForm.e_diff` (bpP:p8:e-diff) — finite-order (`k : ℕ`) version as in the audit-2 signature.
- `SecularForm.compact_uniform` (G1) — `IsCompact.uniformContinuousOn_of_continuous`.
- `SecularForm.periodic_derivative_integral` (G2) — FTC + periodicity.

## Extra helpers (new, not signature declarations)
`isCompact_cell`, `measurableSet_cell`, `hasFDerivAt_cell_integral` (real, jointly continuous derivative),
`aestronglyMeasurable_fderiv_cell`, `norm_fderiv_le_cell` (Cauchy estimate), `cslowEquiv`
(`CSlow n ≃L[ℂ] CVec (n+(n+n))`) and `e_param_cslow` (the CSlow carrier adapter the design assigns to S8-P).

## Approach
- `e_param`: `hasFDerivAt_integral_of_dominated_of_fderiv_le` (𝕜 = ℂ, μ = volume.restrict cell). Uniform
  bound on `fderiv` by a Cauchy estimate along each direction on a compact cell × closedBall; measurability of
  `t ↦ fderiv ℂ (f t) x` from difference quotients with a real sequence tending to 0.
- `e_diff`: induction on `j ≤ k`, step via `hasFDerivAt_cell_integral` applied to `iteratedFDeriv j (f t)`;
  `fderiv ∘ iteratedFDeriv j = curryLeftEquiv ∘ iteratedFDeriv (j+1)`; integral commutes with the isometry.
- `periodic_derivative_integral`: `intervalIntegral.integral_deriv_eq_sub`, `q (0+2π) = q 0`.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-s8p KAM.Planetary.SecularForm.ParameterIntegral` → Build completed successfully (no warnings from my file).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" — because the new module is not yet in the
  generated root (I did not edit KAM.lean; orchestrator to regenerate).
- `#print axioms` of e_param, e_diff, compact_uniform, periodic_derivative_integral, e_param_cslow: all
  `[propext, Classical.choice, Quot.sound]`.
- No sorry, no maxHeartbeats; no provider / frozen-theorem imports (imports: Mathlib, SecularForm.Basic).

## Uncertainties / errata / deviations
None. No statement was changed or needed extra hypotheses; no heartbeat design signals. Extras above are additive.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-P and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures (e_param, e_diff, compact_uniform, periodic_derivative_integral); (2) proofs sound (dominated calculus, FTC); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the SecularForm/ParameterIntegral module(s).

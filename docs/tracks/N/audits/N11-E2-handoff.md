# N11-E2 prover handoff (branch inp-n11e2, a9899974; contains N11-C and N11-A (passed); offloaded package run by the main orchestrator)


## Files (new)
- KAM/Nekhoroshev/Partial/Lie.lean (~190 lines): `ext_taylor_regular`, `ext_taylor`, `ext_taylor_bound`
  (signatures verbatim from N11Signatures.lean; the unused hypotheses of `ext_taylor_bound` are kept verbatim,
  giving unused-variable linter warnings only).
- KAM/Nekhoroshev/Partial/Adjoint.lean (~270 lines): `adjoint` (verbatim).
Graph steps are internal: et-one = `hasDerivAt_comp`, et-ind = `differentiableOn_extAd`/`contDiffOn_comp`/
`iteratedDerivWithin_comp`, et-taylor = `ext_taylor` via Mathlib `taylor_integral_remainder`;
ad-setup/ad-step/ad-prod = `ad_iter`/`ad_step`/`factorial_est`+`adjoint`. No unsigned exports.

## Approach
Lie: d/dt v(γ t) = extBracket c v φ (γ t) (chain rule, ℂ-fderiv restricted to ℝ); holomorphic regularity
(`KAM.holomorphic_regularity_of_finiteDimensional`) gives all `extAd` differentiable; C^∞ by induction with
`contDiffOn_succ_iff_derivWithin`; Taylor from Mathlib. Bound: norm_integral_le + ∫(1-t)^(N-1)/(N-1)! = 1/N!.
Adjoint: used `bracket` with u:=ad^{i-1}u (radius R_{i-1}), v:=φ (R'), losses R'-R_i, s'-s_i (so no
antisymmetry lemma is needed; the output radius is exactly R_i); the constant is bounded by 1/((j+i)κλ)
directly (`step_const`, using e⁻¹ ≤ 3/8 and 16kcλ ≤ κ), not through `bracket_dominated` (SL for the enlarged
losses is not available). Product and (2j)! ≥ (2j/e)^{2j} from `Real.pow_div_factorial_le_exp`.

## Checks
- `inp_lake_build.sh ... KAM.Nekhoroshev.Partial.Lie` and `...Adjoint`: Build completed successfully (only
  unused-variable warnings in Lie.lean's ext_taylor_bound).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; reports
  "KAM.lean is out of date" (generated file, not edited per rules; orchestrator regenerates).
- No line > 100 columns; no sorry/axiom/maxHeartbeats.
- #print axioms for ext_taylor, ext_taylor_bound, ext_taylor_regular, adjoint: [propext, Classical.choice, Quot.sound].

## Uncertainties / deviations / errata
- Private helper `wbound_adjoint_const_mul` duplicates public `KAM.Canonical.wbound_const_mul` (KAM/Canonical/Adjoint.lean,
  stated for the non-extended base); I did not import KAM.Canonical.Adjoint to avoid pulling that module; could be
  deduplicated later. Private `continuous_slice'` duplicates a private lemma in Bracket.lean.
- Source locator B L69-86 for adjoint is stale (noted in design). No source defects found; the source proof of
  `adjoint` swaps the roles in `bracket` via antisymmetry; here the roles are not swapped (equivalent estimate).
- No heartbeat design signals.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-E2 (ext_taylor, its derivatives and remainder; the adjoint product) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node mapped to Lie/Adjoint established (in the proof or as an export); an UNSIGNED export named after a graph node states its literal conclusion; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Nekhoroshev/Partial/{Lie,Adjoint}.lean.

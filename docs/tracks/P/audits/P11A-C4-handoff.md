# P11A-C4 prover handoff (branch inp-p11ac4, d8186af; contains inp-p11aw8 (audited), C0..C3 on inp; offloaded package run by the main orchestrator; prover on claude-10)


## Files
- new `KAM/Planetary/MaximalStep/Cutoff.lean` (~125 lines)
- new `KAM/Planetary/MaximalStep/Divisor.lean` (~110 lines)
(KAM.lean untouched; it reports out of date until the orchestrator regenerates it.)

## Declarations (signatures verbatim from P11ASignatures.lean)
- `bpP:p11a:cutoff` -> `KAM.Planetary.cutoff`. Approach: `taylor_cutoff` (M = eps) then `fourier_cutoff` (M = 2 eps)
  on the Taylor part. The bounds compose as `2(1+E)eps`. For `R - cutoff` on `D(r-d, qs; B)` the triangle
  inequality splits it into the Taylor remainder (`eps q²/(1-q)`) and the Fourier tail on the Taylor part
  (`E * 2eps`). Reality goes through the new helper `p11_taylor_real`: the real derivative of a
  real-valued slice is real (real-line chain rule + uniqueness of derivatives).
- helper `p11_taylor_real` (reality of `p11Taylor`; not in the signature file; a new helper, no deviation).
- `bpP:p11a:x-duality` -> `p11_norm_dotC_le` (`‖k·v‖ ≤ |k|₁ ‖v‖`).
- `divisor_wide`: `limit_bridge` plus `T^(-τ) ≤ |k|^(-τ)` (uses `1 ≤ |k|₁`).
- `bpP:p11a:divisor-perturb` -> `divisor_perturb`: mean value inequality on the convex ball around the
  real point `realInclusion J` (contained in `E+t`, which is open), then `‖k·(w b - w b0)‖ ≤ T L t ≤ D/2`.
  A named `divisor_wide` anchor is in `Divisor`, not `Bridge`.

## Checks
- `inp_lake_build.sh` on `KAM.Planetary.MaximalStep.Cutoff` and `...Divisor`: "Build completed successfully"
  (re-run after the line-wrap lint edits: also successful; lint then clean apart from the generated-KAM.lean note).
- Only warnings: unused-variable for `hT` in `divisor_wide` and `hD` in `divisor_perturb` (hypotheses
  kept verbatim from the signatures).
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; the only
  non-passing lines were two over-100-char lines (fixed in place) and "KAM.lean is out of date"
  (generated; not edited, per rule 10).
- `#print axioms` for `cutoff`, `p11_taylor_real`, `divisor_wide`, `divisor_perturb`, `p11_norm_dotC_le`:
  `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
None. No heartbeat issues; no `set_option`; no sorry. Signatures unchanged.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C4 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures exactly (cutoff, p11_taylor_real, divisor_wide, divisor_perturb); (2) proofs sound (C1, C3 and W8 consumed as designed; mean value on each polydisc); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/MaximalStep/Cutoff.lean and Divisor.lean.

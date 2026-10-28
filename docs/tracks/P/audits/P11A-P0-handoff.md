# P11A-P0 prover handoff (branch inp-p11ap0, 06f3d39; off inp (P11A-C0, C3 audited); offloaded package run by the main orchestrator; prover on claude-10)


## Files (new)
- `KAM/Planetary/Preparation/AnalyticExtension.lean` (214 lines)
- `KAM/Planetary/Preparation/Schwarz.lean` (128 lines)
No other file touched (KAM.lean not regenerated; the orchestrator must run gen_root_imports.py).

## Declarations (namespace KAM.Planetary; statements verbatim from P11ASignatures.lean)
- `p11_complexification` (hc-rot): real power series of f at x, each real multilinear coefficient complexified
  coordinatewise (`p11CMap`, helper defs/lemmas `p11CMap_apply`, `p11CMap_real`, `norm_p11CMap_le` with
  `‖q_n‖ ≤ a^n‖p_n‖`), radius shrunk by max(a,1); F = q.sum(· - ι x); real slice via uniqueness of sums.
- `p11_real_slice_identity` (hc-rot): induction freeing one coordinate at a time, 1-D identity theorem on a disc
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`).
- `p11_radial_schwarz` (hc-mean): helpers `p11_iterate_dslope_zero`, `p11_schwarz_one` (k-fold dslope factorisation,
  max modulus on circles, ρ→R), then restriction to the line ζ ↦ F(ζ•z) using `iteratedDeriv_line_eq_iteratedFDeriv`.
- (`p11_bounded_global_flow`, `p11_global_variational`, `real_lipschitz` of the same signature section are not in P0's row.)

## Checks
- `inp_lake_build.sh ... KAM.Planetary.Preparation.AnalyticExtension KAM.Planetary.Preparation.Schwarz`: Build completed
  successfully (9086 jobs). Only warning: `Schwarz.lean:89` unused variable `hM` (kept: signature is verbatim).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS (651 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms` of all three main theorems: `[propext, Classical.choice, Quot.sound]`.
- No heartbeat overrides, no sorry; files far below 1500 lines. Imports: Mathlib, KAM.Strip.Analytic,
  KAM.Strip.AnalyticTaylor, KAM.Planetary.MaximalStep.Basic (no provider/anchor).

## Uncertainties / errata / deviations
- None: no signature changed, no extra hypothesis. `hM : 0 ≤ M` in `p11_radial_schwarz` is unused (it follows from hb).
- Design note: C3 modules were not needed; only MaximalStep.Basic (carriers, `p11Bound`).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P0 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures exactly (real analytic coefficient complexification p11_complexification, identity theorem, radial Schwarz); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY KAM/Planetary/Preparation/AnalyticExtension.lean and Schwarz.lean.

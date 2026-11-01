# Package LP-SP-DOMX: the remaining clauses of MAIN Lemma 18 (spatial chart/momenta/derivative bounds, denominators)

Wave 4 supplement. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers,
handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spdomx` = `inp-lp` + the spatial packages
through SP-DOM (and SP-NRR).

## Why

By the campaign's bookkeeping rule (PROGRESS "Carried requirements"), the L18 source node counts PROVED only if the
full conclusion is proved. Like planar LP-DOM before LP-DOMX, LP-SP-DOM proved the scalar extension, sup bound, real
trace and containment, but not L8/L18's "chart, momenta, f and all their first derivatives have bound M" and "every
Newtonian denominator has a single holomorphic branch, bounded away from zero". MAIN L18 line 591: "every
`(q_i − q_j)·(q_i − q_j)` still has positive real part on the chosen complex tube; spatial rotations do not replace
this check."

## Template

The planar LP-DOMX (landed: `KAM/Planetary/StrongAMD/AnalyticDomain/Bounds*`, `lemma8_complete`; audit LP-W3C-1).
Mirror it with:
- `tubeNM` / `complexTubeNM` (SP-TUBE) applied to the `6n·2` real coordinates of `spatialPoincareProd`;
- `Fin 3` body blocks and the bilinear `cDot` on complex 3-vectors;
- SP-GEO's barrier bounds `dS`, `dP`, `R`.

## Owned files

`KAM/Planetary/Spatial/AnalyticDomain/Bounds.lean` (and parts). Do not edit SP-DOM's files; report if the
facade should import the new module (the orchestrator adds it at landing).

## Statements (spatial twins of LP-DOMX items 1–4)

1. Holomorphic, periodic chart extension `Ψc` with real trace `spatialPoincareProd`, and its sup bound.
2. First-derivative bounds of `fc` and `Ψc` on a quarter tube (Cauchy; reuse the planar `norm_fderiv_le_cauchyBall`
   if its statement is dimension-free, otherwise a twin).
3. Denominators: `Re(w·w) ≥ d²/2` for all star and pair 3-vectors on a uniform smaller tube; the principal-branch
   reciprocal square root is holomorphic with bound `√2/d`.
4. `lemma18_complete`: the collected statement as MAIN L18 (constants before `I⁰`, `μ`), citing SP-DOM's outputs.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 500–1,100 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-DOMX-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-DOMX.md`,
then `touch .drafts/READY-LP-SP-DOMX`.

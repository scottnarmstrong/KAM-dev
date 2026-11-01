# Package LP3-KEP: the Kepler part as a partial-convexity fast Hamiltonian (LP3 interface, plan-independent)

LP3 (stretch: no arithmetic hypothesis). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp` (LP3 plan merged:
`docs/tracks/LP/lp3/LP3-PLAN.md`; its LP3-KEP row, line 424). Started ahead of the plan review on root-b8's direction:
these lemmas are needed by any partial-convexity route, whatever the review says.

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4; root-b8, 2026-11-01; overrides the common prover brief's ban on frozen theorem anchors)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` (AGENTS
rule 9 quarantines only providers and DRAFT_SORRY anchors; precedent: track P's `Exponential/Stopped.lean:9`). Never
import any `KAM/Provider/*` module. This package needs only the frozen **definitions** in
`KAM/Frozen/Nekhoroshev/Defs/` (`HasDefiniteFastPart`, `HasComplexHessianBound`, `realPart`, `actionNbhd`, …), not the
theorem.

## Goal

Every premise of `partialConvex_nekhoroshev` that concerns only the fast Hamiltonian, for
`h = planetaryKeplerC ν` (`= −Σ ν_i³/(2 I_i²)`, radian convention, as in track P), and for `−h` (the time-reversal
case), on arbitrary convex open fast sets `G ⊆ G'` inside a compact `U ⊆ chamber ν`, with a uniform collar `ρ`.
Match the sealed definitions EXACTLY (read `KAM/Frozen/Nekhoroshev/Defs/*.lean` and the theorem's binder list
`KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:48–77`).

## Reuse

Track P's `KAM/Planetary/Exponential/KeplerData.lean` (`keplerSumGen_contDiffOn`, `keplerSumGen_hasFDerivAt`,
`keplerSumGen_fderiv2_apply`, `keplerSumGen_hess_norm_le`, `planetaryKeplerC_ofReal`, `planetaryKeplerC_eq`,
`keplerSumGen_real_freq`, `keplerSumGen_real_hess`), and how `Exponential/Stopped.lean` (around line 256) obtains
`hhol`, `hC2`, `hreal`, `hHess`, `hdef`, `hdefn` for its `AMDBox` fast box. Generalize that to sharp LP cells. Do not
import `Stopped.lean` itself.

## Owned files

`KAM/Planetary/StrongAMD/Nek/Kepler.lean` (new directory `Nek/`, as in the plan). Do not edit other files.

## Statements (for `hν : ∀ i, 0 < ν i`, compact `U ⊆ chamber ν`)

1. **Positivity margin.** `∃ Imin > 0` with `Imin ≤ I_i` on `U`, and a collar `ρ₀ > 0` (e.g. `Imin/2`) such that on
   `actionNbhd (cthickening ρ₀ U) ρ₀` every complex coordinate satisfies `‖I_i‖ ≥ Imin/4 > 0`.
2. For every `G' ⊆ cthickening ρ₀ U` and `0 < ρ ≤ ρ₀`, on `KAM.actionNbhd G' ρ`, for `h = planetaryKeplerC ν`:
   - `DifferentiableOn ℂ h`;
   - `ContDiffOn ℂ 2 h`;
   - reality on real points: `(h (fun i => (I i : ℂ))).im = 0`;
   - the Hessian bound `‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mcomplex`, with explicit `Mcomplex` depending only on
     `(ν, Imin)`.
   The same for `−h`.
3. **`HasDefiniteFastPart G' ρ g m h` with `σ = −1`**, and `HasDefiniteFastPart G' ρ g m (−h)` with `σ = 1`. The
   real Hessian of `realPart h` is `diag(−3ν_i³/I_i⁴)`, negative definite, with `m = min 3ν_i³/Imax⁴` (uniform
   over the real points of the neighbourhood). Also give `g ≤ ‖frequencyMap h I‖` with explicit `g > 0`, and
   `ContDiffOn ℝ 3 (realPart h)`.
4. A packaged corollary `lp3_kepler_data` giving every fast premise of `partialConvex_nekhoroshev` at once, with
   constants chosen before `G`, `G'` (only `(ν, U)`).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 150–400 lines.

## Handoff

`docs/tracks/LP/audits/LP3-KEP-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-KEP.md`, then
`touch .drafts/READY-LP3-KEP`.

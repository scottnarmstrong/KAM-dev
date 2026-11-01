# LP-W5B: combined audit handoff for LP3-SP-COVER + LP3-SP-DRIFT (LP3, the spatial drift supplier with no arithmetic hypothesis, `k = n + n`)

Branch `inp-lp-w5b` (worktree `/root/code/KAM-inp-lp-w5b`) = `inp-lp-lp3spdrift` (SP-COVER b8994a7c, SP-DRIFT
01622857) + `inp-lp` (through W5A, audited). Nothing in track LP is frozen.

**Package diff:** `git diff inp-lp HEAD -- KAM` (6 files, about 900 lines). Five new modules under
`KAM/Planetary/Spatial/Nek/` (`Cover`, `Perturbation`, `Drift/Kepler`, `Drift/Slow`, `Drift`) plus the regenerated
root.

**Prover handoffs:** `docs/tracks/LP/audits/LP3-{SP-COVER,SP-DRIFT}-handoff.md`. **Briefs:**
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP3-{SP-COVER,SP-DRIFT}.md`.

**Plan:** `docs/tracks/LP/lp3/LP3-PLAN.md`, §2.4 and **§2.5 (the spatial version)**.

**Twins:** the planar twins LP3-COVERPERT and LP3-DRIFT were audited as LP-W5A (`LP-W5A-audit-1.md`, PASS WITH NOTES),
and the spatial modules reuse their planar cells verbatim. The spatial ingredients (SP-DOM, SP-LIFT, SP-CONF) are
audited and landed (W4B, W4D).

**Import ruling:** D58 (`git show main:docs/DECISIONS.md`). The sealed anchor is reached only through the planar
`Nek.Cells` and track P's `Exponential.Stopped`. No provider is imported.

## Orchestrator checks (kam-lp)

- `lp_build.sh` of the 5 modules: built. `lp_lint.sh`: exit 0. Short-name check: OK.
- `#print axioms` of the main declarations (in the prover handoffs): `[propext, Classical.choice, Quot.sound]`.

## REPORT FORMAT

Two sections (LP3-SP-COVER, LP3-SP-DRIFT), each with a verdict, then a combined verdict.

## AUDIT FOCUS

**LP3-SP-COVER:**
- The slow cell `D_j = slowBall (n+n) (B(c) − 5δ/16)`.
- The containment `partialComplexDomain ⊆ complexTubeNM (spatialStrongCore) (R/2)`.
- The sum split linking `slowBall (n+n)` to `spatialSecularBall`.
- The slow gap with constant `√(2(n+n))`.
- `IsPartialPerturbation` of `±P`.
- The `V_j` identity with `spLiftChartHam` (`B₀ μ`, no time conversion, as W5A N1 confirmed for the planar case).
- The quantifier order of `exists_spatialNekPerturbation`.

**LP3-SP-DRIFT:**
- **Deviation from the planar twin.** It calls CELL's `cell_drift_two_sided` directly and does not use
  `kepler_cell_drift`, because that lemma's collar `ρ₀ = Imin/4` is below the fixed spatial cell widths. Instead it
  proves the Kepler premises on the cells itself (`nekCell_nbhd_re_mem_ball`, `spatialNek_kepler_premises`).
  - Check the margin `‖Re z − c‖ < 2η + ρ = 5rs/8 < rs` and `closedBall c rs ⊆ cthickening (4 r_g) 𝓛_δ`.
  - Check the constants `g = νmin³/Imax³`, `m = 3νmin³/Imax⁴`, `M = keplerHessConst ν Imin` on the right sets.
- **`spatial_stopped_drift_nek`.** Its last conjunct must be literally the `hstop` antecedent of
  `spatialStrongFirstExit_of_stopped_drift` (`Spatial/Confinement.lean`), with `r := (B₀μ)^{b_n}`. The prover
  checked this with a scratch `exact`. The first three conjuncts are the `hr`, `hball` and `hbudget` inputs.
- **Typing datum `Λ(z₀) ∈ L`.** It is the counterpart of the planar `hAz`; it must not be a drift, AMD or alignment
  premise.
- The sharp slow bound `C < B(c) − 3δ/8` through the aligned chart deficit.
- The `V_j` solution premise.
- The exponent bridges from `planetary*` to `partial*`.
- `μ ≤ μ₀`, non-strict, from `B₀μ ≤ ε*/2 < ε*`.

## Source defects, deviations, design signals

No MAIN defect reported. Deviations:
- the generated root;
- the direct use of `cell_drift_two_sided` described above.

No design signals: every file is under 280 lines.

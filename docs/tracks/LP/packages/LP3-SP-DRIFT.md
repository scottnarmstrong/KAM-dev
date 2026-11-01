# Package LP3-SP-DRIFT: the spatial stopped-drift supplier for LP3 in the exact spatial `hstop` shape (`k = n + n`)

LP3, spatial. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3spdrift` = `inp-lp-lp3spcov`, which holds every
spatial LP package (proved, under audit) and LP3-SP-COVER, plus `inp-lp-lp3cell` (LP3-CELL, KEP, COVERPERT).

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Read first

- `docs/tracks/LP/lp3/LP3-PLAN.md` §2.4 (the planar statement and its eight proof steps) and **§2.5 (the spatial
  version)**, plus §3 and §6, and `lp3/LP3-PLAN-REVIEW-1.md`.
- The handoffs `docs/tracks/LP/audits/LP3-{KEP,CELL,SP-COVER}-handoff.md`. CELL's `kepler_cell_drift` is generic in
  `k`; use it with `k = n + n`. SP-COVER supplies the cells, `P`, the region `V_j`, the identity with
  `spLiftChartHam`, and the slow gap with constant `√(2(n+n))`.
- The spatial lift and confinement interfaces:
  - `KAM/Planetary/Spatial/ChartLift/{Stopped,Lift,Setting,Premises}.lean` (`SpatialLiftData`, `SpatialStoppedOn`, the
    lift on a stopped interval, `spLiftChartHam`, the slow erosion lemma);
  - `KAM/Planetary/Spatial/Confinement.lean` (`spatialStrongFirstExit_of_stopped_drift`, whose `hstop` antecedent is
    your target).
- **Twin in progress:** the planar LP3-DRIFT is being proved in parallel on branch `inp-lp-lp3drift` (worktree
  `/root/code/KAM-inp-lp-lp3drift`, files `KAM/Planetary/StrongAMD/Nek/Drift*.lean`). You may READ it for alignment
  (read-only; never edit or build in that worktree). Keep the structure parallel where the interfaces allow, but do
  not wait for it.

## Statement

`spatial_stopped_drift_nek`: the spatial twin of the plan's `lp_stopped_drift_nek`. Constants are chosen from
`(n, ν, U, δ)` only, before `μ` and the orbit: `μ₀ > 0`, the scale `r(μ) = (B₀ μ)^{partialDriftExponent n}` (or the
plan's exact form; state it), and the time `T(μ)`. Then for every `0 < μ < μ₀`, the spatial lift data with radius
`r μ`, an order-connected `J ∋ 0`, a spatial moving solution, and `t ∈ J` with `|t| ≤ T(μ)` and
`SpatialStoppedOn … t`: `‖Λ(z t) − Λ(z₀)‖ ≤ r μ / 2`. This is literally the `hstop` antecedent of
`spatialStrongFirstExit_of_stopped_drift` with `r := r μ`; match it by `exact`.

Include as separate lemmas:
- the sharpened slow bound, `C < B(c_j) − 3δ/8` (spatial: through the aligned chart deficit, as SP-LIFT does);
- the `V_j`-form of the solution premise;
- the budget lemma, if the confinement interface needs one.

## Owned files

`KAM/Planetary/Spatial/Nek/Drift.lean` and `Spatial/Nek/Drift/*.lean`. New files only (the generated
`KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`: standard.

If an interface does not fit, STOP and report the exact mismatch. Never add a drift, AMD, alignment or confinement
premise (alignment is SP-LIFT's typing datum, unchanged). Expected size 300–450 lines.

## Handoff

`docs/tracks/LP/audits/LP3-SP-DRIFT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-SP-DRIFT.md`,
then `touch .drafts/READY-LP3-SP-DRIFT`.

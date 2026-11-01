# Package LP3-DRIFT: the planar stopped-drift supplier for LP3 in the exact `hstop` shape (no Diophantine premise)

LP3. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff; module
docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3drift` = `inp-lp-lp3cell`, which contains LP3-KEP
(`Nek/Kepler.lean`), LP3-COVERPERT (`Nek/Cover.lean`, `Nek/Perturbation.lean`) and LP3-CELL (`Nek/Cells.lean`), on
`inp-lp`.

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Read first

- `docs/tracks/LP/lp3/LP3-PLAN.md` §2.2 (fixed data, chosen before `μ`), §2.3, and **§2.4 (the statement and its
  eight proof steps; follow them)**, plus §3 and §6, and the review `lp3/LP3-PLAN-REVIEW-1.md`.
- The four handoffs: `docs/tracks/LP/audits/LP3-{KEP,COVERPERT,CELL}-handoff.md` (CELL's `kepler_cell_drift` is the
  engine you call; COVERPERT's `exists_nekPerturbation`, `IsNekCover`, `nekCell_*` supply the cells, the perturbation
  and the `V_j` identity).
- The planar LP ingredients the plan cites:
  - `KAM/Planetary/StrongAMD/ChartLift/{Stopped,Lift}.lean` (`LiftData`, `StoppedOn`, `lpChartLift_of_stopped`,
    `strongAMD_le_of_stopped`, `stopped_slow_erosion`);
  - `PlanarDictionary.lean` (`lpChart_action`, `lpChart_strongAMD`);
  - `Modulus.lean` (`abs_strongThreshold_sub_le_modulus`);
  - `Confinement.lean` (`strongFirstExit_of_stopped_drift`, whose `hstop` is your target).
- Track P's `KAM/Planetary/Exponential/Stopped.lean`, as the template of the same assembly with a common-eccentricity
  box.

## Statement

`lp_stopped_drift_nek` (plan §2.4). Constants chosen from `(n, ν, U/𝒜, δ)` only, before `μ` and the orbit:
`μ₀ > 0`, the scale `r(μ) = (B₀ μ)^{partialDriftExponent n}` (or the plan's exact form; state it), and the time
`T(μ) = (B₀μ)⁻¹ exp((B₀μ)^{−partialTimeExponent n})` converted to physical time as the plan says. Then for every
`0 < μ < μ₀` and every `LiftData ν U z₀ δ (r μ)`, `OrdConnected J ∋ 0`, moving solution `z` on `J` with `z 0 = z₀`, and
`t ∈ J` with `|t| ≤ T(μ)` and `StoppedOn ν z₀ δ (r μ) z t`: `‖Λ(z t) − Λ(z₀)‖ ≤ r μ / 2`. This is literally the
`hstop` antecedent of `strongFirstExit_of_stopped_drift` with `r := r μ`; match it by `exact`.

Include the sharpened slow bound of §2.4 step 4 as its own lemma (`chartAMD (w u) < B(c_j) − 3δ/8`), and the
`V_j`-form of the solution premise (step 6). Also state the budget lemma the assembly will need:
`n r(μ) + Ω_B(r(μ)) ≤ δ/4` for `μ < μ₀` (plan §3), if it is not already in the confinement interface.

## Owned files

`KAM/Planetary/StrongAMD/Nek/Drift.lean` and `Nek/Drift/*.lean` (split as the plan suggests: e.g. `Drift/Stopped.lean`).
New files only (the generated `KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`: standard.

If an interface does not fit (for example `LiftData`'s radius premises vs `r(μ)`, or the erosion constants), STOP and
report the exact mismatch. Never add a drift, AMD or confinement premise. Expected size 300–450 lines.

## Handoff

`docs/tracks/LP/audits/LP3-DRIFT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-DRIFT.md`, then
`touch .drafts/READY-LP3-DRIFT`.

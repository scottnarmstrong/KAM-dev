# LP-W3C: combined audit handoff for LP-LIFT + LP-DOMX (track LP, waves 2–3)

Branch `inp-lp-w3c` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-lift` (26ac101c) + `inp-lp` (landed through
W3B) + `inp-lp-domx` (36459396), plus one orchestrator edit: `KAM/Planetary/StrongAMD/AnalyticDomain.lean` (the DOM
facade) now imports `AnalyticDomain.Bounds` (the DOMX handoff asked the orchestrator to add it; no cycle, since
Bounds imports only DOM's parts). The package diff is `git diff inp-lp...HEAD -- KAM`: the ChartLift facade
and parts (Stopped, Lift, Premises), the AnalyticDomain.Bounds facade and parts (Cauchy, TubeBound, Algebra,
Chart, Denominator), the facade import line and the regenerated root. About 1,330 lines. Nothing in track LP is
frozen.

Prover handoffs:
- `docs/tracks/LP/audits/LP-LIFT-handoff.md`: MAIN L14, chart part. The chart lift on the stopped interval and the
  D1 premises of the Lemma-13 adapter. Brief `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-LIFT.md`.
- `docs/tracks/LP/audits/LP-DOMX-handoff.md`: the remaining clauses of MAIN L8 (chart/momenta/derivative bounds,
  holomorphic denominators), `lemma8_complete`. Brief `…/packages/LP-DOMX.md`.

Source: `docs/tracks/LP/source/MAIN.md` L8 (244–271), L14 (468–500), T15 (502–506), with
`docs/tracks/LP/source/AMENDMENTS.md` (N2, N3, N6). Context: LP-W1B-1 note D1 (PROGRESS "Carried requirements");
LP-CONF's strict `hstop` (landed, `Confinement.lean`).

## Orchestrator checks (kam-lp)

- `lp_build.sh` of all 11 new modules plus the DOM facade: built.
- `lp_lint.sh`: exit 0. Short-name check: OK. `git diff --check`: clean.

## REPORT FORMAT

One section per package (LP-LIFT first, then LP-DOMX), each with a verdict, then a combined verdict.

## AUDIT FOCUS (beyond the prover handoffs)

LP-LIFT:
- `StoppedOn` is definitionally the antecedent of LP-CONF's `hstop` (strict).
- `LiftData` has only source premises, typing data and the orientation `0 < totalMomentum z₀`. No drift or
  confinement conclusion is assumed.
- The D1 premises are DERIVED, not assumed. The restriction of solutions and of the lift ODE to `uIcc 0 t` is
  legitimate (two-sided derivatives inside an open interval).
- `lpStopped_drift_of_chartData` is conditional on the L8 analytic data. Check it is named and documented as
  such.

LP-DOMX:
- `StrongTubeData` / `lemma8_complete` against MAIN L8 line 253 in full: chart and momenta bounds; first
  derivatives (Cauchy); denominators with the bilinear `cDot`, the principal branch, `Re ≥ d²/2` and the
  `√2/d` bound.
- Constants come before `I⁰` and `μ`. The (22) containment is cited from D5 with `rStar ≤ 4 r` (N3).
- Whether `lemma8_complete` now entitles the L8 source node to PROVED (the campaign's bookkeeping rule).

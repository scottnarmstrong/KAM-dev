# LP-W3B: combined audit handoff for LP-CONF + LP-NRR (track LP, waves 2–3)

Branch `inp-lp-w3b` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-conf` (d62be160) + `inp-lp` (landed
waves 1–2 plus OSC) + `inp-lp-nrr` (15304d89), at 0716638a plus this handoff. The package diff is
`git diff inp-lp...HEAD -- KAM`: `Confinement.lean` and the `NonresonantReuse` facade with its parts
(Kepler, Pert, PertClass, Hyp, Drift), plus the regenerated `KAM/Root/Planetary.lean`, about 1,030 lines.
Everything else is already audited. Nothing in track LP is frozen.

Prover handoffs:
- `docs/tracks/LP/audits/LP-CONF-handoff.md`: MAIN L14, the sharp first exit as a **conditional** helper with
  the explicit stopped-drift hypothesis `hstop` (strict stopped conditions, review round 1). Brief:
  `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-CONF.md`.
- `docs/tracks/LP/audits/LP-NRR-handoff.md`: MAIN L13 (`ExtNFHyp` per centre, trace identity, `lp_stopped_drift`).
  Brief: `…/packages/LP-NRR.md`.

Source: `docs/tracks/LP/source/MAIN.md` L13 (429–464) and L14 (468–500) with `source/AMENDMENTS.md` (**N6**
binding for both; **N2** shared `U`; **N4**). The LP-W1B-1 note **D1** defines the intended split. NRR's helper
premises (chart lift, `realDom` along `J`, stopped slow membership) are discharged by LP-LIFT (in progress)
together with CONF's strict stopped conditions, in the planar assembly. The LP-W2A-1 note on `ρ` strictly inside
`r_*` is addressed in NRR (see its handoff, "Fixed widths").

## Orchestrator checks (kam-lp, on 0716638a)

- `lp_build.sh` of Confinement and NonresonantReuse.{Kepler, Pert, PertClass, Hyp, Drift} plus the facade: all
  built.
- `lp_lint.sh`: exit 0. Short-name check: OK. `git diff --check`: clean.

## REPORT FORMAT

One section per package (LP-NRR first, then LP-CONF), each with a verdict, then a combined verdict.

## AUDIT FOCUS (beyond the prover handoffs)

LP-NRR:
- `lpExtNFHyp`: every field against `KAM/Nekhoroshev/Partial/Setting.lean`.
- `lp_stopped_drift`: constants before `μ`, `I⁰` and the solution. Premises exactly the engine's plus the
  physical solution and its chart lift (D1); no drift/AMD premise. The strict `ρ < r_*` (N6).
- Period and time conversions (`lpKepler = planetaryKeplerC/(2π)`, `lpPert = (μ/2π) fc ∘ unrescale`).

LP-CONF:
- `strongFirstExit_of_stopped_drift` is a distinctly named conditional helper whose only extra premise is
  `hstop`. Check `hstop` is a source-faithful stopped estimate (MAIN (40) and the L12/L13 conclusion shape), not
  a smuggled confinement conclusion: its antecedent is the stopped set and its conclusion is only the `r/2`
  action drift.
- The first-exit argument (open/closed pair, closedness of the core among limits), and uniqueness in the
  frozen `MovingUniqueOn` form.

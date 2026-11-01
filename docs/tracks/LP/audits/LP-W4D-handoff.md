# LP-W4D: combined audit handoff for LP-SP-DOM + LP-SP-DOMX + LP-SP-NRR + LP-SP-LIFT (track LP, wave 4: MAIN Lemma 18, the spatial Lemma 13 step and the spatial chart lift)

Branch `inp-lp-w4d` (worktree `/root/code/KAM-inp-lp-w4d`) = `inp-lp` (through W4B) + `inp-lp-spprod` (SP-CHART and
SP-PROD, under audit as LP-W4C) + SP-DOM (e57e5a6c), SP-DOMX (0aaed69c), SP-NRR (8e2ccbed) and SP-LIFT (80e1e1dd),
plus one orchestrator commit (7b533d99: the `AnalyticDomain` facade also imports `AnalyticDomain.Bounds`, as SP-DOMX's
handoff requested). Nothing in track LP is frozen.

**Package diff.** SP-CHART/SP-PROD are audited separately (LP-W4C), so this package's diff is
`git diff inp-lp-w4c HEAD -- KAM` (23 files, about 3,150 lines). It covers `Spatial/AnalyticDomain` with its parts
`Core`, `Safety`, `Extension`, `Containment`, `Alignment` and `Bounds/{Tube,Algebra,Chart,Denominator}` + `Bounds`;
`Spatial/NonresonantReuse` with `Pert`, `PertClass`, `Hyp`, `Drift`; `Spatial/ChartLift` with `Stopped`, `Uniform`,
`Setting`, `Lift`, `Premises`; and the regenerated root. If LP-W4C lands first, `git diff inp-lp...HEAD -- KAM` shows
the same.

Prover handoffs: `docs/tracks/LP/audits/LP-SP-{DOM,DOMX,NRR,LIFT}-handoff.md`. Briefs:
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-SP-{DOM,DOMX,NRR,LIFT}.md`.

Source: `docs/tracks/LP/source/MAIN.md`: Lemma 18 (580–597), with L8 (244–271), (21)/(22), (47); Lemma 13
(MAIN L12/L13, the nonresonant engine step) for `k = 2n` slow pairs; Lemma 14 (468–500); Theorem 19 (599–603). Read
them with `source/AMENDMENTS.md` (N2, N3, N6, N12). Planar templates (landed and audited):
`KAM/Planetary/StrongAMD/{AnalyticDomain,NonresonantReuse,ChartLift}/*`.

## Orchestrator checks (kam-lp)

- `lp_build.sh` of all spatial modules in import order: built.
- `lp_lint.sh`: exit 0. Short-name check: OK.
- Every module docstring carries the SPEC §4 sentence.
- `#print axioms` of the main declarations of each package (in the prover handoffs): `[propext, Classical.choice,
  Quot.sound]`.

## REPORT FORMAT

Four sections (LP-SP-DOM, LP-SP-DOMX, LP-SP-NRR, LP-SP-LIFT), each with a verdict, then a combined verdict.

## AUDIT FOCUS

**LP-SP-DOM:**
- `spatialSlowDeficit` vs MAIN (47): `|z|₂²/2` over all `4n` real slow coordinates. The core uses the closed
  `≤ B(I⁰) − δ/4`.
- D3 uses only `spatialStrongAMD ≤ spatialFixedPlaneDeficit`, with no `L ∥ e₃` (MAIN 593: "including points whose
  total angular momentum is not parallel").
- D5: the index blocks `Fin.castAdd (n+n)` / `Fin.natAdd n`; the angle cell via `⌊Re λ/2π⌋`.
- `exists_spatialStrongTube` hypotheses.
- The alignment lemmas take `L = |L| e₃` / `L ≠ 0` as typing premises (MAIN 597), not conclusions.

**LP-SP-DOMX:**
- The `SpatialTubeData` field list vs MAIN L8/L18: sup bounds on `R/2`, derivative bounds on `R/4`, denominators on
  `ρ ≤ R/4`.
- `re_cDot3_ge` (the loss `3ε(ε+2Q)`) and the choice of `ε`.
- The `Fin (n*3)` block conventions.
- The quantifier order of `lemma18_complete` (constants before `I⁰`, `μ` absent); `rStar ≤ 4r` (N3).

**LP-SP-NRR:**
- The index arithmetic of `lpUnrescaleCNM`.
- All `2n` slow pairs enter the `4b` condition.
- N6 strictness (`ρ = min rs Imin / 2`, stopped radius `D₀√μ ≤ ρ < r_*`).
- `lpTraceNM` (the Kepler part uses the `n` fast actions only).
- The premises of `spatial_stopped_drift` are only the solution, lift and localization: no drift, AMD or confinement
  bound. Its constants are chosen before `μ`, `I⁰` and the solution.
- (5) in the radian form.

**LP-SP-LIFT:**
- `SpatialLiftData.aligned` is the only orientation datum (a typing premise per MAIN L18).
  `spatialStopped_drift_of_chartData` is explicitly conditional (a distinct name, not a source result).
- `SpatialStoppedOn` is literally SP-CONF's `hstop` antecedent.
- The chart deficit equals the strong AMD only through alignment. Chart-domain membership uses only `C ≤` the
  fixed-plane deficit.
- `uniformDataNM` is a verbatim retyping of track P's `uniform_data`.
- `spLiftChartHam` vs `spatialPulledHam`.
- The index arithmetic of `lpRescaleNM_mem_realDom`.

**Cross-package:**
- **Duplicate ball.** SP-DOM's `spatialSecularBall` (`Containment.lean:36`,
  `((Σ y.1²) + Σ y.2²)/2 ≤ B(I0) − δ/4`) and SP-LIFT's `spLiftSecularBall` (`ChartLift/Stopped.lean:43`,
  `Σ (y.1 k² + y.2 k²)/2 ≤ …`) are the same set of MAIN (47), written two ways; they were proved in parallel. Report
  whether they are equal (they should be, by `Finset.sum_add_distrib` and `sum_div`). Recommend whether to join them
  (an equality lemma, or one definition) before LP2 is assembled for freeze; a NOTE is enough.
- The interfaces chain SP-DOM → SP-NRR → SP-LIFT → SP-CONF's `hstop` as LP-SP-SAFE consumes them. No ingredient
  carries a conclusion-shaped hypothesis.

## Source defects, deviations, design signals

No MAIN defect was reported by any of the four provers. Deviations: generated `KAM/Root/Planetary.lean`; the
`spLift`/`lpChartHamNM` names (from the short-name check); `Phase (n + (n + n))` rather than `n + 2n`; generic `m` in the
NRR unrescaling lemmas. No design signals: every module builds in under 30 s under the 4 GB cap, and the largest file
has 302 lines.

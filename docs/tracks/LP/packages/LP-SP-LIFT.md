# Package LP-SP-LIFT: the spatial chart lift on a stopped interval and the spatial D1 premises (MAIN L14, L18 alignment, d = 3)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-splift` = `inp-lp` + LP-SP-MODEL, SP-GEO, SP-ROT,
SP-CHART, SP-PROD, SP-TUBE, SP-CONF, SP-ADAPT.

## Template

The planar LP-LIFT (landed, `KAM/Planetary/StrongAMD/ChartLift/*`; audit LP-W3C-1): `LiftData`, `StoppedOn`,
`prograde_of_stopped`, `strongAMD_le_of_stopped`, `lpChartLift_of_stopped`, `lpChartLift_premises`. Mirror it with:
- the spatial product chart `spatialPoincareProd` (SP-PROD), its local diffeomorphism and inverse;
- SP-CONF's strict `StoppedOn` antecedent (copy it literally from `KAM/Planetary/Spatial/Confinement.lean`);
- SP-ADAPT's generic `lpRescaleNM`, `lpRealDomNM`, and `PartialBlock n (n + n)`;
- the spatial Hamiltonian field, with chart Hamiltonian `spatialHProd + μ · fSpatial ∘ Ψ` (SP-PROD split).

## The spatial differences (MAIN L18 lines 595–597, T19)

- **Orientation is alignment, not reflection.** `LiftData` takes `angularMomentum3 z₀ = |L₀| • e₃` (aligned) as
  the orientation datum, in place of the planar `0 < totalMomentum z₀`. LP-SP-SAFE reduces to it with
  SP-MODEL's `exists_rotation_align_angularMomentum3` and `isSpatialMovingSolutionOn_rotate_iff`.
- **Positive projections.** On the stopped interval, conservation of `L` (SP-MODEL `angularMomentum3_const`) and
  SP-MODEL's `proj_margin` (with `m = δ/2`) give `L_i · e₃ ≥ δ/2 > 0`. Every state therefore lies in the image of
  the spatial chart (SP-PROD `spatialPoincareProd_image`), and `spatialStrongAMD = spatialFixedPlaneDeficit`
  (aligned).
- **Ball (47).** `Σ(Γ_i + Z_i) ≤ B(I⁰) − δ/4` along the stopped interval (budget, as planar item 2). LP-SP-DOM (in
  progress) names this ball; define it locally with a clear name, and the orchestrator joins the names at landing.

## Statements (spatial items 1–4 of LP-LIFT)

1. Stopped states are aligned-prograde barrier states (`SpatialBarrierState ν U (δ/2)`).
2. Whole-ball membership `Σ(Γ + Z) ≤ B(I⁰) − δ/4` of their chart points.
3. **Chart lift.** `∃ w` on an open interval containing `uIcc 0 t` with: `w u ∈` the collision-free chart domain,
   `spatialPoincareProd ν (w u) = z u`, `HasDerivAt w (X_{chart Hamiltonian} (w u)) u`, and fast actions of
   `w 0` equal to `I⁰`.
4. **D1 premises** for `PartialBlock n (n + n)` with `Ic = I⁰`, `S =` the ball (47) (in physical slow
   coordinates), `rB = r`, width `wS`: `lpRescaleNM b.lam (w u) ∈ b.realDom b.rB`, initial fast action, and
   stopped slow membership. State them in the exact shape of SP-ADAPT's `nonresonant_drift_of_chartDataNM`.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 600–1,300 lines. Stop when done or blocked (report any interface mismatch with SP-ADAPT or SP-PROD).

## Handoff

`docs/tracks/LP/audits/LP-SP-LIFT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-LIFT.md`,
then `touch .drafts/READY-LP-SP-LIFT`.

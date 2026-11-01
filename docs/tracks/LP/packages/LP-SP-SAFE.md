# Package LP-SP-SAFE: the spatial theorem LP2 (MAIN Theorem 19 with Lemma 16 for d = 3), assembly

Wave 4, the spatial milestone. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spsafe`, which holds every LP
package (planar landed; spatial SP-MODEL, ROT, CHART, PROD, TUBE, GEO, OSC, CONF, ADAPT, DOM, NRR, LIFT).

## Template

The planar LP-PS (landed: `KAM/Planetary/StrongAMD/PlanarSafety/*`; audit LP-PS-1 PASS WITH NOTES), with its exact
structure:
- Constants: fixed before `μ`, `z₀`.
- Orientation: the planar reflection becomes the spatial **rotation alignment**: SP-MODEL's
  `exists_rotation_align_angularMomentum3` and `isSpatialMovingSolutionOn_rotate_iff`, plus the invariance lemmas.
  Every conclusion quantity is rotation-invariant: lengths, energies, axes, actions, `|𝐞|`, `spatialStrongAMD`, the
  osculating elements (`spatialOscVelocity` rotates with `R`), and `SpatialMovingUniqueOn`. Prove any missing
  invariance.
- Confinement: SP-CONF's `spatialStrongFirstExit_of_stopped_drift`, with `hstop` discharged by SP-LIFT's
  `spatialChartLift_premises` and SP-NRR's `spatial_stopped_drift` (or SP-LIFT's `spatialStopped_drift_of_chartData`
  fed with SP-NRR's `ExtNFHyp`, trace and `hsmall`).
- Conclusions: SP-GEO (separations), SP-OSC (osculating validity and estimates, half-gaps), and SP-MODEL L1
  (`isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn`).

## Source

`docs/tracks/LP/source/MAIN.md` Theorem 19 (599–603), Lemmas 14, 16, 18, §1 (6)–(9) with `d = 3`, and
`source/AMENDMENTS.md` (N2, N6, N7, N10, N12).

## Target statements (state them; they become the LP2 freeze-proposal text)

`lp2_spatial_strongAMD_safety` and `lp2_spatial_strongAMD_safety_normalized`: the exact spatial twins of the
landed `lp1_planar_strongAMD_safety` and `…_normalized`, i.e. FREEZE-PROPOSAL draft-2 LP1 with:
- `Phase (n * 3)`, `bodyVector3`, `spaceLength`;
- `spatialKeplerEnergy/Axis/Action/EccVector`, `spatialStrongAMD` (Euclidean `|L|`), `orderedStrongThreshold` of the
  spatial actions;
- `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`, `IsSpatialNewtonSolutionOn` with the spatial barycentric
  maps and masses;
- the spatial osculating elements (`spatialOscEnergy`, …, `spatialOscPeri/Apo`, `spatialKeplerPeri/Apo`), with the same
  F2 clauses (`Aelem`, validity, N10 inequalities).

Same premises, nothing added: **no** prograde, small-inclination, nonzero-total-angular-momentum,
secular-confinement or alignment premise. Roadmap §2: "It must not add prograde, small-inclination, nonzero total
angular momentum, secular-domain confinement, normal-form existence or stopped-action hypotheses." Also prove
`lp2_…_halfInteger` (`τ = n − 1/2`).

## Owned files

`KAM/Planetary/Spatial/SpatialSafety.lean` (facade) and parts `KAM/Planetary/Spatial/SpatialSafety/*.lean`. Nothing
else.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of the LP2 theorems: exactly `[propext, Classical.choice, Quot.sound]`.

If an ingredient interface does not fit, STOP and report the exact mismatch; never add a hypothesis to LP2.
Expected size 800–1,600 lines.

## Handoff

`docs/tracks/LP/audits/LP-SP-SAFE-handoff.md` (committed, with AUDIT FOCUS and the full elaborated LP2 signatures) and
`.drafts/handoff-LP-SP-SAFE.md`, then `touch .drafts/READY-LP-SP-SAFE`.

# Package LP-SP-CONF: the spatial sharp first exit, conditional on the stopped drift (MAIN Lemma 14, d = 3)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spconf` = `inp-lp` + LP-SP-MODEL + LP-SP-GEO + LP-SP-OSC.

## Template

The planar LP-CONF (landed: `KAM/Planetary/StrongAMD/Confinement.lean`, `strongFirstExit_of_stopped_drift`;
audit LP-W3B-1, PASS WITH NOTES). Mirror it exactly, with the spatial objects:
- `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`;
- `spatialActionVector`, `spatialStrongAMD`;
- `SpatialBarrierState`, `exists_spatialBarrierCompact`, `spatial_maximal_global_of_barrier`;
- `spatialStrongAMD_le_of_tube` (SP-GEO), `spatial_moving_ode` (SP-GEO).

The thresholds and modulus are the dimension-free THR and Modulus packages.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 14 (468–500) and Theorem 19 (599–603: "These facts discharge every condition
of Lemma 14"), with `source/AMENDMENTS.md` N2 and N6.

## Owned files

`KAM/Planetary/Spatial/Confinement.lean`. Do not edit other files.

## Statement

`spatialStrongFirstExit_of_stopped_drift`: a distinctly named conditional helper, not the public theorem. Its
data, premises and conclusion are those of the planar helper with the spatial objects:
- the budget `n r + strongThresholdModulus ν U r ≤ δ/4`;
- a physical spatial `z₀` whose closed `r`-action ball lies in `U`, with `C₀ ≤ B(Λ z₀) − δ`;
- `hstop` in the **strict** form (drift `< r`, margin `< B − δ/2`, on `uIcc 0 t`), exactly as the planar one.

Conclusion: `∃ z` with `z 0 = z₀`, `IsSpatialMovingSolutionOn` and `SpatialMovingUniqueOn` on `Icc (−T) T`; and for
every `t` there: a physical state, drift `≤ r/2`, `C ≤ B − δ/2`, and `SpatialBarrierState ν U (δ/2)`.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 300–700 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-CONF-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-CONF.md`,
then `touch .drafts/READY-LP-SP-CONF`.

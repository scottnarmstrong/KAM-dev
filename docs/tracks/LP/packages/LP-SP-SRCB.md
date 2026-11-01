# Package LP-SP-SRCB: LP2 restated through the spatial source carriers (OD-11 (b), part B)

Freeze preparation (spatial). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spsrcb` = LP-SP-SRC (part A:
`KAM/Planetary/Spatial/SourceCarrier.lean`) + LP-SP-SAFE (`lp2_spatial_strongAMD_safety_normalized`).

## Template

The planar `KAM/Planetary/StrongAMD/PlanarSafety/Source.lean` (`lp1_planar_strongAMD_safety_source{,_general}`;
FREEZE-PROPOSAL §3b; statement review 3 PASS). Do exactly the same for LP2:
- `lp2_spatial_strongAMD_safety_source` (normalized) and `…_source_general`: the LP2 text (FREEZE-PROPOSAL §3c) with
  every conclusion occurrence of `spatialStrongAMD`, the spatial Kepler elements (axis, action, eccentricity
  vector, peri/apo, as meaning-carrying) and `spatialOsc*` replaced by the source versions of part A / SP-OSC;
- subtype proofs existential in the conclusion; the initial AMD hypothesis through the source AMD with a typing
  binder `h₀`;
- proved from `lp2_spatial_strongAMD_safety_normalized` (the guards come from its conclusions).

Elaborate the restated statements and print them (`#check`) into the handoff for FREEZE-PROPOSAL §3d.

## Owned files

`KAM/Planetary/Spatial/SpatialSafety/Source.lean`. Do not edit other files (the facade import is added at landing).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 200–450 lines.

## Handoff

`docs/tracks/LP/audits/LP-SP-SRCB-handoff.md` (committed) and `.drafts/handoff-LP-SP-SRCB.md`, then
`touch .drafts/READY-LP-SP-SRCB`.

# Package LP3-SRC: LP3-1 and LP3-2 restated through the source carriers (OD-11 (b), D59), the planar and spatial twins of §3b and §3d

LP3, freeze preparation for the later delta (draft 8). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md`
(hard rules, capped wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3src` =
`inp-lp-lp3spsafe` (LP3-SP-SAFE proved) + `inp-lp-lp3ps` (LP3-PS proved) + `inp-lp`.

These are the plan's additional packages LP3-SRC and LP3-SP-SRC (review C3), done together.

## Rulings (D59; binding)

OD-11 (b): every meaning-carrying definition in an anchor goes through its source carrier. For the planar statement,
follow §3b exactly (it keeps the frozen raw `keplerAxis/keplerAction/keplerEccVector`). For the spatial statement,
follow §3d exactly (every canonical element through `spatialSource*`, review 4 resolution (A)). OD-3: the anchors keep
`hνmax`, `hνle`.

## Templates (follow them token for token)

- **Planar:** `KAM/Planetary/StrongAMD/PlanarSafety/Source.lean`. It holds the LP1 (b) theorem (FREEZE-PROPOSAL §3b),
  proved from LP1.
- **Spatial:** `KAM/Planetary/Spatial/SpatialSafety/Source.lean`. It holds the LP2 (b) theorem after SRCB2
  (FREEZE-PROPOSAL §3d), proved from LP2. Reviews 4 and 5 are in `docs/tracks/LP/freeze/STATEMENT-REVIEW-{4,5}.md`.
- The LP3 theorems to restate are `lp3_planar_strongAMD_safety{,_normalized}` (`Nek/PlanarSafety`) and
  `lp3_spatial_strongAMD_safety{,_normalized}` (`Spatial/Nek/SpatialSafety`), with their handoffs
  `docs/tracks/LP/audits/LP3-{PS,SP-SAFE}-handoff.md`.

## Statements

`lp3_planar_strongAMD_safety_source{,_general}` and `lp3_spatial_strongAMD_safety_source{,_general}`. The `_general`
forms drop `hνmax` and `hνle`.

Each is the corresponding (b) template text with exactly the three LP3 changes:
1. **Removed:** `γ τ`, `hγ hτ` and the Diophantine premise.
2. **Time:** `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))`.
3. **Drift:** `μ ^ planetaryDriftExponent n` in the action, axis and AMD lines.

Everything else must be token-identical to the template. Prove each one from the LP3 theorem, as the templates prove
theorems from LP1 and LP2.

## Owned files

`KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean` and `KAM/Planetary/Spatial/Nek/SpatialSafety/Source.lean`
(new). Do not edit other files (the generated `KAM/Root/Planetary.lean` excepted). Also write the elaborated texts
to `docs/tracks/LP/freeze/odb-LP3-PlanarSource.lean.txt` and `odb-LP3-SpatialSource.lean.txt`.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of all four theorems: standard.
- In the handoff, a token diff of each new theorem type against its template, showing only the three changes.

Never add a premise. If a template clause cannot be transported, STOP and report. Expected size 300–500 lines.

## Handoff

`docs/tracks/LP/audits/LP3-SRC-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-SRC.md`, then
`touch .drafts/READY-LP3-SRC`.

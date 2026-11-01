# Package LP-SP-SRCB2: LP2 under OD-11 (b) with every canonical element through `spatialSource*` (review 4, R4.1 (A))

Freeze preparation (spatial). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spsrcb2` = `inp-lp-spsrcb` (SP-SAFE,
SP-SRC and SP-SRCB, built in this worktree).

## Why

Statement review 4 (`docs/tracks/LP/freeze/STATEMENT-REVIEW-4.md`, finding **R4.1, BLOCKING**): the §3d anchor text
(`KAM/Planetary/Spatial/SpatialSafety/Source.lean`, theorem and its `_general` sibling) still applies the unfrozen
total helpers `spatialKeplerAxis`, `spatialKeplerAction` and `spatialKeplerEccVector` to `z₀` and `z t`. Under OD-11
(b) every physical quantity must be exposed through a source subtype. Resolution (A), recommended, gives the exact
replacement text (report lines 290–435).

## Task

1. Restate both theorems in `SpatialSafety/Source.lean` (the main one and the `_general` sibling, minus `hνmax`,
   `hνle`) **literally as the R4.1 (A) replacement text**:
   - `h₀` immediately after the physical premise;
   - every canonical element at `z₀` and `z t` is the `spatialSource*` restriction;
   - the canonical (9) clauses use `spatialSourceKeplerPeri/Apo`;
   - the per-time block scoped under one `∃ hs`.
   No premise added, none removed; every conclusion of the current text is recovered definitionally. Prove them from
   the existing LP2 theorems (`lp2_spatial_strongAMD_safety{,_normalized}`) and the SourceCarrier `rfl` equations.
2. If the replacement text does not elaborate as written (a typo, a dependent-type mismatch from `hs`/`h₀`), make the
   **minimal** repair, and list every character-level change in the handoff with the reason. Never add a hypothesis;
   if a premise appears to be needed, STOP and report.
3. Fix the SourceCarrier docstring (`KAM/Planetary/Spatial/SourceCarrier.lean`:20–22) only if it is no longer
   accurate after the change (it should become accurate). Also apply review notes R4.6 (the two docstring misnomers)
   if they lie in your files.
4. Write the fully elaborated signatures to `docs/tracks/LP/freeze/odb-Spatial-SpatialSafety-Source.lean.txt` (the
   same format as the existing `odb-*` files), replacing the old text.

## Owned files

`KAM/Planetary/Spatial/SpatialSafety/Source.lean`, the docstring of `KAM/Planetary/Spatial/SourceCarrier.lean`, and
the `odb-*` text file above. Do not edit other files.

## Checks and stop condition

- `lp_build.sh` of `KAM.Planetary.Spatial.SpatialSafety.Source` (and `SourceCarrier` if touched).
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of both theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- `grep` of the two theorem types shows no `spatialKeplerAxis`, `spatialKeplerAction` or `spatialKeplerEccVector`
  (only `spatialSource*`).

Expected change: 50–200 lines.

## Handoff

`docs/tracks/LP/audits/LP-SP-SRCB2-handoff.md` (committed, with AUDIT FOCUS and the elaborated signatures) and
`.drafts/handoff-LP-SP-SRCB2.md`, then `touch .drafts/READY-LP-SP-SRCB2`.

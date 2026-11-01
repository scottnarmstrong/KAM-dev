# Handoff LP-SP-SRCB2 (statement review 4, R4.1 (A))

## Files
- `KAM/Planetary/Spatial/SpatialSafety/Source.lean` (restated both theorems; module docstring updated; 247 lines)
- `docs/tracks/LP/freeze/odb-Spatial-SpatialSafety-Source.lean.txt` (copy of the final file, the existing odb format)
- SourceCarrier docstring: untouched (lines 20-22 are now accurate, since no §3d type mentions the helpers).

## Declarations
`KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source` and `..._source_general` (no `hνmax`, `hνle`), text =
R4.1 (A) replacement, extracted programmatically from STATEMENT-REVIEW-4.md lines 290-435, with NO character-level
changes (it elaborated as written). The `_general` sibling is the same text minus the two binders. No premise
added or removed; `h₀` is right after the physical premise; per-time block under one `∃ hs`.
Proofs: from `lp2_spatial_strongAMD_safety{,_normalized}`; guards come from its conclusions; the `spatialSource*`
quantities are accepted by `exact` through the `rfl` definitional unfolding (no extra lemma needed).

## Checks
- `lp_build.sh $PWD KAM.Planetary.Spatial.SpatialSafety.Source`: Build completed successfully (9360 jobs), no
  warnings in Source.lean (other stale spatial modules replayed/rebuilt, expected).
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- `main_shortname_check.py ... Source`: exit 0 ("short-name check OK").
- `#print axioms` (both theorems, via lp_lean.sh): [propext, Classical.choice, Quot.sound].
- grep of `#check` output of the `_source` type: 0 occurrences of spatialKeplerAxis / spatialKeplerAction /
  spatialKeplerEccVector (the only remaining raw helper is `spatialKeplerEnergy` and `spatialOscEnergy/Ecc` inside
  the typing predicates, as the review states).

## AUDIT FOCUS
- Compare the two theorem types to STATEMENT-REVIEW-4.md R4.1 (A) verbatim (the `_general` one minus hνmax/hνle).
- Dependent types: `hch`, `hcht`, `orderedStrongThreshold hn ⟨_, hch⟩` depend on `h₀`/`hs` (proof irrelevance).
- The per-time conclusion no longer states the raw guard `∀ i, 0<|q_i| ∧ E_i<0` separately; it is `∃ hs`
  (which also contains `0 < ν_i`), as the review prescribes.

## Not done / notes
- R4.6: the `Elements.lean:35` docstring ("Osculating semimajor axis" for the canonical axis) and `Model:21` are
  outside my owned files; not edited. Please assign. SourceCarrier docstring needed no edit.
- No errata, no deviations, no design signals.

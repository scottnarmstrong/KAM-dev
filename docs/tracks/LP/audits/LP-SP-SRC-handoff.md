# LP-SP-SRC handoff (spatial source carriers, OD-11 (b), answering LP-W4A-1 N1)

## Files
- New: `KAM/Planetary/Spatial/SourceCarrier.lean` (about 270 lines; namespace `KAM.Planetary.Spatial`).
- Generated: one added import line in `KAM/Root/Planetary.lean` (output of `scripts/gen_root_imports.py`;
  required for `lp_lint.sh` to exit 0). No other file touched.

## Declarations
- Carriers (abbrevs, no duplication): `SpatialSourceCanonicalPhase n ν := SpatialElliptic ν` (the subtype of
  SP-MODEL's `SpatialNegativeEnergy`); `SpatialSourceOsculatingPhase n ν μ := SpatialOscPhase n ν μ` (SP-OSC).
  Membership lemmas `spatialSourceCanonicalPhase_property`, `spatialSourceOsculatingPhase_property`.
- Canonical source definitions (each with a `_def` equation, `rfl`): `spatialSourceKeplerAxis`, `…Action`,
  `…EccVector`, `…Ecc`, `spatialSourcePlanetAngularMomentum`, `spatialSourceAngularMomentum`,
  `spatialSourceStrongAMD` (+ `spatialSourceStrongAMD_eq_on` to `spatialStrongAMDOn`;
  `spatialSourceKeplerPeri/Apo_eq_source` restate SP-OSC's `spatialSourceKeplerPeri/Apo` in source quantities).
- Canonical characterizations (from `spatial_orbital_identities` and L3): `…Axis_pos`, `…Action_pos`, `…Action_sq`
  (Λ² = ν² a), `…Ecc_sq`, `…Ecc_nonneg`, `…Ecc_le_one`, `spatialSourcePlanetAngularMomentum_length`
  (|L_i| = Λ√(1−e²)), `…_length_le`, `spatialSourceKeplerPeri_le_length`, `spatialSourceKeplerApo_ge_length`,
  `spatialSourceStrongAMD_nonneg`, `spatialSourceAction_mul_eccDeficit_le` (Σ Λ_i(1−√(1−e_i²)) ≤ C).
- Osculating (reuse of SP-OSC's `spatialSourceOsc*` and its `_eq` equations, none duplicated): added
  `spatialSourceOscParam_pos`, `…OscEnergy_neg`, `…OscEcc_lt_one`, `…OscEcc_nonneg`, `…OscAxis_pos`,
  `…OscPeri_pos`, `…OscPeri_le_length`, `…OscApo_ge_length` (the last four from `spatialOscPhase_ellipse`).

## Not done
Part B (LP2 restatement through these definitions): later package, per the brief.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-spsrc KAM.Planetary.Spatial.Osculating.Basic` (stale module), then
  `… KAM.Planetary.Spatial.SourceCarrier`: `Build completed successfully (9112 jobs).`, no warnings in the file.
- `lp_lint.sh`: exit 0 (after `gen_root_imports.py`; first run exit 1 only because the root was stale);
  tail: `ABI HASHES OK (177 frozen declarations of KAM; …)`.
- `main_shortname_check.py … SourceCarrier.lean`: `short-name check OK`, exit 0.
- `#print axioms` (via `lp_lean.sh`, scratch `.drafts/axSRC.lean`) for every characterization theorem:
  `[propext, Classical.choice, Quot.sound]` only.

## AUDIT FOCUS
- That the canonical carrier is exactly `SpatialNegativeEnergy` (positive ν, |q_i|>0, E_i<0); it allows radial
  e = 1, so `…Ecc_le_one` is non-strict, unlike the osculating carrier (e^osc < 1 by definition).
- That the source quantities are thin `rfl` restrictions of the total helpers, which stay internal (N1).
- `spatialSourceStrongAMD` is stated with source angular momentum and equals `spatialStrongAMDOn` by `rfl`.
- Osculating carrier requires 0 < μ (SP-OSC), the canonical one has no μ.

## Source defects / deviations / design signals
- No errata. Deviations: the generated root import line (above). The planar template
  `KAM/Planetary/StrongAMD/SourceCarrier.lean` and `LP-SRC-handoff.md` are not present in this worktree, so the
  design follows the brief and SP-OSC's existing carrier pattern. No design signals.

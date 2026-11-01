# Package LP-SP-SRC: spatial source carriers for OD-11 (b) (audit LP-W4A-1, note N1)

Freeze preparation (spatial). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spsrc` = `inp-lp` + the spatial
packages (SP-MODEL landed; SP-OSC, SP-GEO, …).

## Why

Audit LP-W4A-1, note N1: "`spatialKeplerAxis`, `spatialKeplerAction`, etc. remain public total helpers, with no
separately named subtype restrictions/characterizations … do not freeze the unrestricted helpers as physical
quantities." Under OD-11 option (b) (recommended), the LP2 freeze must expose spatial physical quantities through
source subtypes, as LP-SRC did for the planar ones (`KAM/Planetary/StrongAMD/SourceCarrier.lean`; FREEZE-PROPOSAL
§3b; statement review 3, PASS).

## Template

`KAM/Planetary/StrongAMD/SourceCarrier.lean` (planar; handoff `LP-SRC-handoff.md`).

## Owned files

`KAM/Planetary/Spatial/SourceCarrier.lean`. Do not edit other files.

## Statements (part A, now)

1. **Carriers.** `SpatialSourceCanonicalPhase n ν` (positive masses, `0 < |q_i|`, negative energy; reuse or alias
   SP-MODEL's `SpatialNegativeEnergy` / `SpatialElliptic`). Also `SpatialSourceOsculatingPhase n ν μ`: SP-OSC's
   `SpatialOscPhase` already exists, so reuse it and document the identification.
2. **Source definitions**, each with a `_def` equation (`rfl`):
   - canonical: `spatialSourceKeplerAxis`, `…Action`, `…EccVector`, `…Ecc`, `…Peri`, `…Apo`,
     `spatialSourceStrongAMD`, and the angular momenta;
   - osculating: SP-OSC's `spatialSourceOsc*` (reuse, do not duplicate).
3. **Characterizations** (the semantic unit), from SP-MODEL's `spatial_orbital_identities` and L3:
   - `0 < a`, `Λ² = ν² a`, `e ≤ 1`, `|L_i| = Λ √(1 − e²)`, `a(1−e) ≤ |q| ≤ a(1+e)`;
   - `0 ≤ C`, `Σ Λ_i D(e_i) ≤ C`;
   - the osculating ones from SP-OSC.

Part B (the LP2 restatement through these definitions) is a later package, after LP-SP-SAFE lands its LP2 text.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 200–450 lines.

## Handoff

`docs/tracks/LP/audits/LP-SP-SRC-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-SRC.md`, then
`touch .drafts/READY-LP-SP-SRC`.

# Package LP-SRC: source-carrier definitions and the LP1 restatement for OD-11 option (b)

Freeze preparation (planar). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff; module docstrings carry the SPEC §4 sentence). Base: `inp-lp-src` = `inp-lp` + `inp-lp-ps` (the
proved planar theorem, under audit).

## Why

The freeze-proposal statement reviews (`docs/tracks/LP/freeze/STATEMENT-REVIEW-{1,2}.md`, finding F4) require that
new physical formulas be frozen either as total expressions with a guarded interpretation (OD-11 (a)) or on source
subtypes (OD-11 (b), the orchestrator's recommendation). This package makes (b) concrete: the exact source-subtype
definitions with their characterizations, and the LP1 statement restated through them, **proved** from the
existing `lp1_planar_strongAMD_safety_normalized`. The owner can then choose between two proved texts.

## Owned files

`KAM/Planetary/StrongAMD/SourceCarrier.lean` (and `KAM/Planetary/StrongAMD/PlanarSafety/Source.lean` for the
restatement, or one file if small). Do not edit other files.

## Statements

1. **Carriers and source definitions** (exact text of review 1, F4; read it):
   - `SourceCanonicalPhase n ν` (positive masses; every planet has `0 < |q_i|` and negative energy) and
     `SourceOsculatingPhase n ν μ` (`0 < ν`, `0 < μ`, `0 < |q_i|`, `oscEnergy < 0`, `oscEcc < 1`);
   - `sourceStrongAMD`, `sourceKeplerPeri/Apo`, and `sourceOscVelocity/Param/Energy/Axis/EccVector/Ecc/Peri/Apo`;
   - each with its defining equation to the total helper (`rfl`).
2. **Characterizations (the semantic unit, as for the thresholds).**
   - `sourceStrongAMD z = Σ Λ_i − |L|`, with `0 ≤ sourceStrongAMD z` and `Σ Λ_i D(e_i) ≤ sourceStrongAMD z`
     (MOM).
   - On `SourceCanonicalPhase`: `0 < keplerAxis`, `e_i ≤ 1`, and `keplerPeri ≤ |q_i| ≤ keplerApo` (MOM's
     `orbital_identities`).
   - On `SourceOsculatingPhase`: `0 < oscAxis`, `0 < oscPeri`, and `oscPeri ≤ |q_i| ≤ oscApo` (OSC's
     `osc_tangency`): the osculating ellipse is a genuine ellipse through the current position.
3. **LP1 through the source definitions.** `lp1_planar_strongAMD_safety_source`: the draft-2 LP1 text with every
   conclusion occurrence of `strongAMD`, `keplerPeri/Apo` and `osc*` replaced by the source versions.
   - The subtype proof of each occurrence is existential in the conclusion, e.g.
     `∃ h : … ∈ SourceOsculatingPhase …, sourceOscPeri ⟨z t, h⟩ i …`, mirroring `∃ hcht` for the thresholds.
   - The initial-state hypothesis `strongAMD ν z₀ ≤ …` becomes `sourceStrongAMD ⟨z₀, h₀⟩ ≤ …`, with
     `h₀ : z₀ ∈ SourceCanonicalPhase` as a typing binder (from the existing physical-state premise).
   - Prove it from `lp1_planar_strongAMD_safety_normalized` (the guards come from its conclusions).
   - Also state it with `hνmax`/`hνle`, as draft 2 does.
4. **Elaboration record.** Elaborate the restated text and print it with `#check` into the handoff, so the
   orchestrator can put it in FREEZE-PROPOSAL draft 3 as the OD-11 (b) text.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 300–700 lines. This runs on an account with little quota: commit early and often, and hand off as
soon as items 1–3 build.

## Handoff

`docs/tracks/LP/audits/LP-SRC-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SRC.md`, then
`touch .drafts/READY-LP-SRC`.

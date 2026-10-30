# SHARP-A8 handoff: the engine-agnostic sharp certifier

## Files (new, `KAM/CertificateSharp/`; nothing under `KAM/Certificate/` touched)
- `Engine.lean`: `AposterioriEngine` (field `test`, theorem field `sound`), `checkTorusCertificateWith`,
  `checkTorusCertificateWith_sound`, instance `oldEngine` (`checkSmallness`, sealed `g1_explicit`),
  regression `checkTorusCertificateWith_old` (`rfl`) and `checkTorusCertificate_sound_via_engine`.
- `Constants.lean`: `sqrtUpQ`, `cRRQ`, `cohConstR_le_cRRQ` (rational upper bound of `cohConstR`;
  `cRRQ 2 1 ≈ 0.31622`, true value `0.31628`... see note below).
- `ConstantsQ.lean`: `Q` mirrors of every constant of `KAM/Sharp/Constants.lean` and
  `KAM/Iso/Sharp/Constants.lean` at `κ = τ ∈ ℕ`; `sharpIsoC1Q/2Q/3Q`.
- `ConstantsDom.lean` (generated layers `Pos`, `DomA/B/C`): each real constant (data = exact casts,
  `c_R ≤ cRq`) is positive and ≤ its mirror.
- `Sharp.lean`: `sharpIsoC{1,2,3}_le`, `sharpTest`, `sharpTest_arith`, `checkTorusCertificateSharp`
  (sub-checks unchanged + `sharpTest`), `checkTorusCertificateSharp_of_old`.
- `SharpEngine.lean`: `IsoSharpG1` (the type of `KAM.Iso.Sharp.g1_sharp`), `sharpEngineOf (G : IsoSharpG1)`,
  `checkTorusCertificateWith_sharp` (`rfl`), `checkTorusCertificateSharp_sound_of G` (conditional helper).
- `Tests/Margin.lean`: toys T2, T3 through both certifiers, kernel-checked margins.

## Approach
Interface: the engine's `sound` says a passing test on a statically valid certificate gives
`C₁ C₂ C₃` with `C₁ e/(γ⁴ρ^{4τ}) < 1`, `max{C₂,C₃} e/(γ²ρ^{2τ}) ≤ disp` and `IG1Body … C₁ C₂ C₃` for every
`ωstar ≠ 0`. The generic soundness assembles the unchanged sub-check lemmas and applies the body.
Dominance of constants: only `c_R` is inexact, so the comparisons are `gcongr` chains over the real
constants at the casts of the rational data, positivity as a separate structure.

## Evidence (toys, `decide +kernel`; log10 values from `.drafts/margin.lean`, exact inequalities in Tests/Margin)
| toy | γ⁴ρ^{4τ} / (C₁ e): old | sharp | disp γ²ρ^{2τ}/(C₂ e): old | sharp (max C₂,C₃) |
|---|---|---|---|---|
| T2 (n=2,τ=1) | 10^4.26 | 10^19.44 | 10^0.0004 (tuned) | 10^5.63 |
| T2d | 10^3.77 | 10^18.95 | 10^0.0004 | 10^5.63 |
| T3 (n=3,τ=2) | 10^4.30 | 10^27.9 | 10^0.0004 | 10^9.24 |
Both certifiers pass; the sharp one passes with the claimed `disp` unchanged. (`cRRQ 2 1`: log10 −0.49988,
i.e. 0.31628 to 4 digits, so the rational bound is tight.)

## Checks
- Builds: `nice -n 5 lake build KAM.CertificateSharp.{Engine,Constants,ConstantsQ,ConstantsDom,Sharp,SharpEngine,Tests.Margin}` success,
  no heartbeat options.
- `lint_sources.sh`: no complaint on `KAM/CertificateSharp`; only the known ABI-scratch failure remains.
- `#print axioms` of `checkTorusCertificateWith_sound`, `checkTorusCertificate_sound_via_engine`,
  `cohConstR_le_cRRQ`, `domC`, `sharpIsoC1_le`, `sharpIsoC3_le`, `sharpTest_arith`,
  `checkTorusCertificateSharp_sound_of`, `toyCert2_sharp_passes`, `toyCert3_margin_sharp`: `[propext, Classical.choice, Quot.sound]`.

## Open item
`KAM.Iso.Sharp.g1_sharp` is not committed on `sharp-a7` yet (branch at the A6B integration). When it is,
`git merge sharp-a7` and add the one-line
`def sharpEngine : AposterioriEngine := sharpEngineOf KAM.Iso.Sharp.g1_sharp` (type-checks iff the A7 statement is the
signature-file one, `IsoSharpG1`), then
`theorem checkTorusCertificateSharp_sound := checkTorusCertificateWith_sound sharpEngine` is unconditional.
Until then the sharp soundness is the conditional helper `checkTorusCertificateSharp_sound_of`
(distinct name, the hypothesis is the A7 theorem itself, not a premise of any source result).

## Uncertainties / deviations
- Mirror-only: `sharpTest` uses `κ = τ ∈ ℕ` (Rüssmann); Parseval/crude would need their own mirrors.
- `cRRQ` uses `sqrtUpQ` (AM–GM with `s = (⌊√⌈10⁶x⌉⌋+1)/1000`), tight to ~1e-3.

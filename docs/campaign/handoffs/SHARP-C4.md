# SHARP-C4 handoff: frame-object majorants (checker side)

## Files (new; nothing under `KAM/Certificate/` touched)
- `KAM/CertificateSharp/Frame/Majorants.lean` (~330 lines): `FrameBounds`, `freqNormUp`
  (`norm_le_freqNormUp`), `frameNModels` (`N = Ω₀ L G⁻¹` as `modelMatMul [4,0]`, `frameNModels_encloses`
  proved from the landed enclosure lemmas, as in `torsionModels_sound`), the checks `checkFrameL`,
  `checkFrameN`, `checkFrameT`, `checkFrameOmega`, `checkFrameMajorants`, the real statement
  `FrameMajorants` and `checkFrameMajorants_sound`; generic helpers `list_norm_sum_le`, `col_sum_le`,
  `row_sum_le` (joint corner passes of C1 over a row or a column).
- `KAM/CertificateSharp/Tests/Frame.lean`: toys T2, T3 and a non-flat column.

## What is certified (on `T_ρ`, real objects)
`Σ_r |DK_{rj}| ≤ bL` (`|Lᵀ|`), `Σ_j |N_{rj}| ≤ bN` (`|N|`), `Σ_r |N_{rj}| ≤ bNt` (`|Nᵀ|`),
`Σ_j |extendedTorsion … (inl i) (inl j)| ≤ bT` (sup |T|, the torsion block of the landed bordered
torsion models), `‖ω*‖ ≤ bOm` (box). Each row/column sum uses the **joint** vertex bound
`rowCornerLeq` (C1), i.e. one vertex for the whole row.
Premises of `checkFrameMajorants_sound`: `checkStatic`, the Hamiltonian-bounds and embedding contracts
(exactly `hH`, `hE` of `checkTorsion_sound_of`), a frequency in the box; the Gram certificate is
re-run inside the checks (as `checkTorsion` does). No conclusion-shaped premise.

## Decisions
- The claimed bounds are data (`FrameBounds`) outside the landed `TorusCertificate` (which is
  SO-owned and unchanged); the checker only verifies them. The producer (python) takes the max over
  the vertex rows; a Lean-side `max` is not available in `CertArith`.
- `|ω*|` bound is `max_i (|c_i| + r_i)`; no `s` factor (the engine multiplies by `σω`).
- Not done: the cosh primitive for the Hamiltonian bounds (C3) and the separate `M₀, M₁, M₂`.

## Measured comparison (landed per-entry `ℓ¹` of `supBound` vs joint corner; `.drafts/fm.lean`)
- T2: `|Lᵀ| = 1`, `|N| = 1`, `|Nᵀ| = 1`, `sup|T| = 1` landed = corner (flat toys), `|ω*| ≤ 0.5`.
- T3: all four `= 1` landed = corner, `|ω*| ≤ 0.7937`.
- Non-flat column `e_{(1,1)}, e_{(1,-1)}` (`ρ = 1/100`): landed `2.268`, corner `2.134`
  (kernel-checked: the corner row check passes at `2.2`, the landed per-entry sum fails).
- The lunar numbers (|Lᵀ| 1.33, |N| 1.35, |Nᵀ| 1.38, sup|T| 3.60, |ω| 1.90) are the study's (§2.7);
  no lunar data was run.
Kernel: `checkFrameMajorants` on T2 and T3 by `decide +kernel` (a few seconds); the check rejects
`bL = 0.99` (`toyCert2_frame_rejects`).

## Checks
- `nice -n 5 lake build KAM.CertificateSharp.Frame.Majorants KAM.CertificateSharp.Tests.Frame`:
  success, no heartbeat options.
- `lint_sources.sh`: nothing on `KAM/CertificateSharp`; only the known ABI-scratch failure.
- `#print axioms` of `norm_le_freqNormUp`, `list_norm_sum_le`, `frameNModels_encloses`, `col_sum_le`,
  `row_sum_le`, `checkFrameMajorants_sound`, `toyCert2_frameMajorants`, `toyCert3_frame_passes`,
  `col_corner_passes`: `[propext, Classical.choice, Quot.sound]`. `KAM.lean` regenerated.

## Uncertainties
- `frameNModels` repeats the `[4,0]` product of `torsionModels`; if SO changes that key the enclosure
  proof would need the same change (it is a direct copy of the corresponding lines).

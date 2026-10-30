# Handoff SHARP2-DOMPLUS: the dominance claim completed (closeness constants, wider ranges)

30 October 2026, branch `sharp-fix`.
- `sharp-v2` was merged first (SHARP2-FIX integrated, SHARP2-LINT).
- Python and documents only. Two exceptions, both for the signature file: one niced `lake env lean` elaboration check of the edited
  probe (5 s), as the re-audits required signature edits.
- Main text: `docs/campaign/design/APOST-SHARP-V2.md` **§12 "The dominance claim, precisely"** (the text the README can cite).

## Outcome
- **Closeness constants compared.** These are the bounds on ‖K∞ − K‖ and, iso, |ω∞ − ω|.
  - Each theorem's best admissible bound is compared at the common error e_c = ½ min{e*_v2, e*_comp}, and as e → 0 (the linear
    coefficient).
  - The fair data rules of SHARP2-FIX apply, plus FH24's sharper split-bite c¹_R (re-audit F2).
  - Against FH24 (Thm 2.18, corrected) and HL19 (Thm 3.1/3.6, with E-HL19-1/8/12/13): **no loss at any point** of 1176 (720 extended
    + 348 wider ranges at fixed frequency + 108 isoenergetic).
- **Minimum margins** (orders):

  | Quantity | Min margin |
  |---|---|
  | threshold | **+0.845** |
  | closeness at e_c vs FH24 | **+0.29** |
  | closeness at e_c vs HL19 | **+1.9** |
  | small-error closeness vs HL19 | **+1.65** |
  | small-error closeness vs FH24 | **+0.003** (see the caveat below) |
  | iso vs HL19 Thm 3.6: threshold / C₂ / C₃ | **+3.65 / +1.62 / +1.10** |

- **Caveat: the small-error closeness against FH24 is essentially a tie.** Both bounds are the first displacement of the same
  modified step, at the same bite in the strip limit.
  - v2 is ahead at every point: +0.64 or more at size 1, but only +0.003–+0.01 at sizes ≥ 10.
  - §12 says exactly this and does not call it a meaningful win.
- **The levers for closeness**, found as for the thresholds:
  - FH24 was ahead by 0.90 orders at the audit's point, because its bite may approach (ρ−ρ∞)/3 while v2's ratios stopped at 2.
    Fix: free schedule ratios up to 4096, with the same near-limit bites offered to FH24.
  - The torus displacement bound σ_K|ξᴸ| + |Nξᴺ|, without the factor 1 + ϑ (blueprint and `stepConstsB`).
  - The theorem's own |DK| cap σ_K − μ/2 in the mirror's constants.
  - Small ϑ and torsion slack, and optional tight internal caps (free parameters).
- **Wider ranges.** n ∈ {8, 10}, τ ∈ {n−1, n}, ρ up to 1, γ down to 10⁻¹⁰: no lost region. Threshold minima: n ≥ 8 +0.87, ρ ≥ 0.6
  +0.84.
- **Re-audit items folded in.**
  - iso F1 = fixed F1: `modified_stepB` gets `hE0 : p.stage0 = true → |E| ≤ p.ePer·μ` on T_r (signature file, blueprint).
  - iso F2: the mirror validates the full numeric contract and rejects illegal data (`IllegalData`); no grid row is affected
    (0 skipped).
  - fixed F2: FH24 gets c¹_R = (τ+1)^{τ+1}/τ^τ·c♮(τ/(τ+1)·δ) in its float search and its exact evaluation. The full grid was rerun
    afterwards. FH24 gains 0.0026 orders at the old worst point, matching the audit's +0.003.

## Files

| File | Change |
|---|---|
| `scripts/apost_sharp/dominance.py` | closeness comparison: `hl19_scan`, `fh24_scan`, `fh24_close`, `hl19_close`, `v2_threshold`, `v2_close`, `compare_close`, `compare_iso`, `grid_data_iso`, `wide_points`, `--closeness --grid {ext,wide,iso,quick}`; FH24 split-bite c¹_R; HL19 iso |
| `scripts/apost_sharp/thresholds_v2.py` | `at_e` closeness mode (engine sums), `theta_given`, `dk_cap`, `tight_caps`, `xlo`; displacement bound C_ΔK = σ_K C_ξL + g C_K̃; numeric contract (`IllegalData`, `check_data`, `check_options`) |
| `blueprint/parts/p2s2-modified.tex` | C_ΔK without (1+ϑ) and its proof; the stage-0 replacement as a hypothesis (`hE0`) |
| `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` | `hE0` in `modified_stepB`; `CDK := p.sK * CxiL + g * CKt` (re-elaborates: 17 sorry, no error) |
| `docs/campaign/design/APOST-SHARP-V2-DELTA.md` | addendum (the two signature changes, the mirror's caps and contract) |
| `docs/campaign/design/APOST-SHARP-V2.md` | §12; superseding note at §0 |
| `docs/campaign/design/dominance/closeness-{ext,wide,iso}.md` | new: per-point results of the three grids |

## Checks and their output
- `dominance.py --closeness --grid ext --jobs 3`: exit 0, 1558 s, "points 720 (skipped 0), threshold losses 0, closeness losses 0";
  threshold min +0.888, closeness min +0.003.
- `--grid wide`: exit 0, 1114 s, "points 348 (skipped 0), threshold losses 0, closeness losses 0"; threshold min +0.845, closeness
  min +0.004.
- `--grid iso`: exit 0, "points 108 … losses 0"; threshold min +3.646, closeness min +1.096.
- `--point 2 1 1/10 3/10 1` (the old worst threshold point, threshold-only path): v2 −9.474, FH24 (fair, split-bite c¹) −10.361,
  margin +0.888.
- Illegal-data tests: ȳ ≥ 1, a ≤ 1, c_DTh < 0, aniso with k = 0, n = 0, t_s ≤ 0, ϑ = 1, γ > γ̄; route A η ≤ 0, n = 0. All are
  rejected with a reason; legal data are accepted.
- `nice -n 10 lake env lean .drafts/sharp2fix/Signatures.lean`: exit 0, 17 "declaration uses `sorry`", no error.
- `latexmk` on `blueprint/sharp2.tex` (out of tree): exit 0, no undefined reference.
- `thresholds_v2.py`, `--plasmalean`, `--fh25`: exit 0, see "Updated numbers" below.
- Per-point tables: `docs/campaign/design/dominance/closeness-{ext,wide,iso}.md`.

## Updated numbers (the mirror's DK cap and the displacement bound; v1 reproduction intact)

- **R1** (fixed / iso):
  - v1 (A0) −24.72 / −24.98, reproduced exactly. k = 0 keeps v1's own σ_K: a regression to −24.70 found in the rerun was fixed.
  - Route A A7 −10.71 / −10.95; route B B6 −12.25 / −12.33.
  - Hybrid (heuristic extrapolation assuming certified first-step transfer): A −4.18 / −4.42, B −4.97 / −5.01.
  - The intermediate rows improve by 0.01–0.04; for example B3 −14.83 / −15.05 and B1 −15.72 / −15.92.
- **H50**: v1 −27.19 / −27.37; route A −11.73 / −11.90; route B −13.04 / −13.12.
- **PlasmaLean** (its tolerance 10^{−18.24}): v2 route A 10^{−17.02} (+1.22); ℓ¹ entry step up to +3.05.
- **FH25**: scale of (10⁻³⁸, 10⁻⁴⁴) 10^{−6.17} (FH24 weight), 10^{−5.92} (anisotropic), 10^{−5.50} (ratio 4). Still short; a
  reproducibility note.

## Axioms
No Lean result.

## Uncertainties
- **Finite parameter study.** Both sides' free parameters are searched on finite grids; route B and FH24's searches are in floating
  point. Margins of a few thousandths (the small-error closeness against FH24) are within what a finer search on either side could
  move.
- **Like-for-like data.** Single-size default data and assigned inverse-twist bounds (FH24's torsion is not the frozen one). Refined
  data were not compared on the grid.
- **Closeness at e_c** depends on the choice e_c = ½ min of the thresholds. The linear coefficient is choice-free.
- **v2's frozen-form C₂** (a sup over the admissible range at a certified X⋆) is not the compared object (§12.5).
- Only HL19 and FH24 are on the grid (§12.5 lists the others).

## Suspected errata
None new in pinned sources. The HL19 corrections used are E-HL19-1, -8, -12, -13 and the FH24 one is (3.72), all already in the
ledger.

## Deviations introduced
- The displacement bound without the factor 1 + ϑ (an improvement, proved in the blueprint).
- The stage-0 hypothesis `hE0` (a repair).
- Free large schedule ratios, small ϑ and t_s, and tight internal caps, as free parameters of the existing theorem.
- The mirror uses the theorem's |DK| cap σ_K − μ/2.

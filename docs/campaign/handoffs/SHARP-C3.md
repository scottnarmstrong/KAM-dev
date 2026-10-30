# SHARP-C3: ball primitives and split H bounds (checker side)

Branch `sharp-c3` (from `sharp-v2`). Additive: nothing under `KAM/Certificate/**` or any SO path is touched.

## Files (all new, all < 410 lines)
- `KAM/CertificateSharp/Ham/TrigBound.lean`: `trig_pair_le` (real inequality), `expLoQ`/`expNegUpQ` (rational
  upper bound of `e^{-x}` from the Taylor partial sum), `trigRad`, `charNorm` lemmas.
- `KAM/CertificateSharp/Ham/BallsTrig.lean`: `ballsTrig` (the cosh ball pass), `stepT_sound`, `val_mem_ballsTrig`,
  `norm_val_le_slotMagQ_trig`, `invGood_of_ballsTrig`, `nonvanishingOn_of_ballsTrig`.
- `KAM/CertificateSharp/Ham/SplitBounds.lean`: `HamSplit` (five rationals), `hamBoundsOkSplit`, `hamSums`,
  `HamBoundsConclusion`, `ham_bounds_of_mags`, `checkHamBoundsTrig` (+ `_sound`, drop-in), `checkHamBoundsTrigSplit`,
  `checkHamBoundsSplit` (landed disc pass, split constants), `HamBoundsConclusion.mono`.
- `KAM/CertificateSharp/Ham/TrigCertifier.lean`: `checkTorusCertificateTrigWith E` and its soundness.
- `KAM/CertificateSharp/Tests/BallsTrig.lean`: kernel tests (toys T2, T3, and a cosine test model).
- `KAM.lean` regenerated (5 import lines).

## Approach
Each slot carries a shape `term k a` meaning `‖v‖ ≤ a‖χ_k‖` on the domain (`char k` is `term k 1`; times a slot of
magnitude m gives `term k (a m)`; sum of two `term k` stays `term k`). The sum of a `term k a` and a `term (-k) b`
(what every cos/sin mode and each derivative compiles to) gets radius `max(aL+bW, aW+bL)`, `W = w^{|k|}`,
`L = 1/Taylor(2 π_lo ρ |k|)` ≥ `e^{-A}`, from `a s + b/s ≤ …` for `s ∈ [e^{-A}, e^{A}]` (convexity, chord bound).
This is `(a+b)cosh` for `a = b`, instead of `(a+b)w^{|k|}`. No program pattern matching: the shape is a norm inequality,
so soundness is local to each op. Everything else delegates to the landed `ballStep`/`ballStep_sound`.
`checkHamBoundsTrig` proves exactly the conclusion of `checkHamBounds_sound` (same `G1Hyps` field `hbd`), so
`checkTorusCertificateTrigWith_sound` is the engine theorem with the `_of` lemmas (`checkTorsion_sound_of`, etc.).
`checkHamBoundsTrigSplit` / `checkHamBoundsSplit` prove the five bounds with separate rationals (M₀, M₁, M₂, dh, d2h)
for SHARP-PLUS's v2 / C6; `HamBoundsConclusion.mono` recovers the single-M form.

## Checks
- `nice -n 5 lake build KAM.CertificateSharp.Tests.BallsTrig`: OK, no errors (builds all four Ham modules).
- `#print axioms` of trig_pair_le, trig_add_bound, stepT_sound, val_mem_ballsTrig, invGood_of_ballsTrig,
  nonvanishingOn_of_ballsTrig, ham_bounds_of_mags, checkHamBoundsTrig_sound, checkHamBoundsTrigSplit_sound,
  checkHamBoundsSplit_sound, checkTorusCertificateTrigWith_sound and the kernel tests: all
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`axiom`/heartbeat options (grep). `scripts/gen_root_imports.py` run.
- `scripts/lint_sources.sh`: `check_lean_modules` PASS, frozen-anchor guard OK, no >100-char lines in my files; its final
  ABI step errors with a missing olean `KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM` (the worktree snapshot does
  not contain it, and building the whole library is forbidden). Not caused by my files; rerun on main.

## Measured comparison (landed disc pass vs cosh pass)
Kernel-checked (`Tests/BallsTrig.lean`):
- T2 and T3 (polynomial H): `ballsTrig` returns exactly the landed balls (`toyCert*_trig_eq`); `checkHamBoundsTrig` passes.
- `cosCert` (T2 data, ρ_H = 451/50, `H = p₂ + p₁²/2 + (1/10)cos 2π(3θ₁+θ₂)`): all five jet sums are 0.49–0.51 of the
  disc sums (`‖D²X_H‖` sum 1.69e101 vs 3.38e101). With M = 2e101 the cosh check passes and `checkHamBounds` fails.
Probe (not committed, ρ_H = 1/70, same H with one mode k; cosh/disc ratio of the DH, DX, D²X sums):
k=[1,1]: 0.935, 0.849, 0.849; [2,0]: same; [9,0]: 0.654, 0.599, 0.599; [30,10]: 0.501, 0.500, 0.500;
ρ_H = 1/160, k=[9,0]: 0.797, 0.747, 0.747. The lunar H mixes small and large modes (design doc: D²H sum −1.7 %,
|D²X_H| −27 % ). I did not run lunar data (rule).

## Uncertainties
- Gain is only on cos/sin *modes* (`cosMode`/`sinMode`), not on `HamExpr.cos a` of a general operand (those go through
  `exp`). Lunar H uses modes.
- `trigRad` could exceed the disc bound only if `L > W`; impossible when `w ≥ 1`, but it is not proved (not needed
  for soundness). I did not prove "disc passes ⇒ cosh passes" (would need that monotonicity plus the shape-less
  steps matching); it holds on all tests.
- Taylor order for `L` reuses `expOrder`.
- Dependency problem (T2d, `N·N⁻¹`) not addressed (design says lunar does not need it).

## Errata / deviations
No errata found. Deviation: new definitions are in `KAM.CertificateSharp` as plain functions (`ballsTrig`,
`val_mem_ballsTrig`, …) rather than `Slp.*`/`HamExpr.*` dot-notation, to avoid adding names to `KAM.Certificate`.

## Remaining
Wire `HamSplit` into SHARP-PLUS's v2 signatures (C6); compose C3 with C1 (corner) if the engine variant wants both.

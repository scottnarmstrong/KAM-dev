# Handoff SO-DEFS (track SO): the certificate and the checker

Branch `inp-sodefs` (off `inp-sotors`), worktree /root/code/KAM-inp-sodefs.

## Files
- NEW `KAM/Certificate/Defs.lean` (370 lines): `CertParams`, `TorusCertificate` and `.D/.H/.K`,
  the eight sub-checks, `checkTorusCertificate`, `G1Hyps`, `CertifiedTorus`: all types and fully
  qualified names exactly as signed in SOSignatures §G (the signed statements of `G1Hyps`,
  `CertifiedTorus`, the structures and `checkTorusCertificate` are copied verbatim). Public helpers
  (new, documented): `freqNormLo`, `ballMagQ`, `slotMagQ`, `sumRangeQ`, `hamBoundsOk`, `angleModel`,
  `actionShiftModel`, `angleImOk`, `dkRowUp`, `d1Slots`, `dkFreqModel`, `invarianceModel`,
  `energyOk`.
- NEW `KAM/Certificate/Tests/Defs.lean` (128 lines): the n = 1 toy of Tests/Torsion as a full
  `TorusCertificate 1 ℚ`; positive and fail-closed tests per sub-check by `decide +kernel`.
  (Data copied: Tests/Torsion's defs are not `@[expose]`d, so their bodies do not reduce across
  modules.)

## Sub-check bodies (all kernel-reducible, structural recursion over lists only)
- `checkStatic`: `freqBox/centre/radius` lengths `= n`; `2 ≤ n`; `n ≤ τ + 1`; positivity of ρ∞, M,
  σK, σB, σT, μ, γbar, ν, γ; `ρ∞ < ρ`; `1 < σω`; `1 < s < σω`; `γ ≤ γbar`; `0 ≤ e`;
  `weight.rho = rho`; `checkWeight` of `weight` and `weightH` at `(expHalvings, expOrder)`;
  `checkPiEnclosure`; with `L := freqNormLo box = max_i (|c_i| - r_i)` (foldr, 0 base): `0 < L`,
  `ν ≤ (s-1) L`, `ν ≤ (σω-s) L`. (Sound: `‖ω‖ ≥ |ω_i| ≥ |c_i| - r_i`.)
- `checkHamBounds`: `c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder`; `none` ⇒ false
  (so success gives `HamExpr.nonvanishingOn_of_balls`). Slot magnitude `|re|+|im|+r`. With
  `m = 2n`, natural phase numbering (`d1.getD a`, `(d2.getD a []).getD b`, `d3` likewise):
  `Σ_a|d1 a| ≤ M` (DH, `norm_fderiv_le_sum_partials`), `|d1 a| ≤ M ∀a` (X_H: coordinates
  `± ∂_{swap a}H`), `∀a Σ_b|d2 a b| ≤ M` (DX_H bridge; all rows a so the `Sum.swap` is covered),
  `∀a Σ_b Σ_c |d3 a b c| ≤ M` (D²X_H bridge), `Σ_a Σ_b |d2 a b| ≤ M` (D²H). All in ℚ.
- `checkEmbedding` (weight `c.weight`, `piEnc`): for i < n, `angleImOk`:
  `supBound(angleModel i) ≤ ρ_H - ρ - μ` OR `ρ · Σ_j supBound(compDerivModel … angle[i]? j) ≤
  ρ_H - ρ - μ`; `supBound(addMixed (realCompModel dA_i A_i) (constModel (-c_i) 0 0)) ≤ r_i - μ`;
  for rows r < 2n, `Σ_j supBound(modelMatrixEntry (dkModels …) r j) ≤ σK - μ` (sumUp). Comparisons
  `ble x (ofRatDown q)`.
- `checkInvariance`: `Slp.compose n jet.prog emb wit weight cfgFull piEnc (d1Slots)`; for a < 2n:
  `invarianceModel a = addMixed (± ms[swapNat n a]) (negM (dkFreqModel a))` (+ for a < n, as
  `dxhModels`), `dkFreqModel a = toDeg 0 (modelSum [mul [5,a,l] (freqModel box s l) DK_{al}])`;
  `supBound ≤ e`.
- `checkEnergy`: compose `[jet.v0]` at `cfgFull`; `d := addMixed (toDeg 0 m) (constModel (-E0) 0 0)`;
  requires `d.deg == 0` and `|zeroModeBall n d|.c.normUp + .r + d.rad ≤ e`.
- `checkGram`: `(gramCheck n emb gramInv weight cfgLow piEnc (σB-μ)).isSome`.
- `checkTorsion`: re-runs `gramCheck` (same args) for `δβ`, then `torsionModels n ham emb wit
  gramInv δβ freqBox s weight cfgLow piEnc`, then `torsionAvgCheck n T torsInv (σT-μ)`.
- `checkSmallness`: `decide (isoC1Q n τ ρ ρ∞ M σK σB σT μ ν γbar * e < γ^4 * ρ^(4τ))` and
  `decide (isoC2Q n τ ρ ρ∞ M σK σB σT * e ≤ disp * (γ^2 * ρ^(2τ)))` (ℚ, `Nat` powers).

## Advice key layout (for SO-DATA)
- `cfgFull` (invariance, energy): composition keys `[0, slot]` (engine), witness sub-advice via
  `cfg.forWitness` (engine), and NEW invariance keys `[5, a, l]` (`a < 2n` row of DK, `l < n`
  frequency coordinate; scalar product `freqModel l × DK_{al}`).
- `cfgLow` (Gram, torsion): Gram `[3, 0, a, b, r]`, `[3, 1, i, j, k]`; torsion `[4, t, …]`,
  `[4, 10, i, j, l]`; composition `[0, slot]` for the torsion slots (engine, unchanged).
- Ball arithmetic Taylor order: `expOrder`; weights checked at `(expHalvings, expOrder)`.

## Checks
- Gate: `inp_lake_build.sh … KAM.Certificate.Defs KAM.Certificate.Tests.Defs` →
  `✔ Built KAM.Certificate.Tests.Defs (11s)`, `Build completed successfully (3250 jobs)`; no sorry,
  no warnings in my files.
- `main_shortname_check.py … KAM.Certificate.Defs KAM.Certificate.Tests.Defs` → `short-name check OK`.
- `scripts/lint_sources.sh` → exit 1 ONLY because `KAM.lean is out of date; run
  scripts/gen_root_imports.py` (generated root; rule 10 forbids my editing it — the orchestrator
  regenerates it on landing; the two new modules must be added). check_lean_modules PASS,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK. All lines ≤ 100 columns.
- Kernel timings (profiler, Tests/Defs, toy n = 1, ℚ): type checking per theorem 0.13, 0.22, 0.31,
  0.36, 0.62, 0.75, 1.31, 1.75, 2.57, 6.35, 6.35 s; whole file 10.3 s wall.
- `#print axioms`: `checkTorusCertificate`, `G1Hyps`, `CertifiedTorus`, `defsTest_torsion`,
  `defsTest_inv`, `defsTest_static_fail`: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / notes for SO-SOUND
- `checkTorsion` recomputes `gramCheck` (the kernel pays it twice in a full run; the soundness
  route gets `δβ` by the same match). If SO-SOUND prefers, it can be reshaped without changing
  signatures.
- `checkHamBounds` reads table slots with default `0` (`getD`); soundness relies on the jet tables
  being well formed (`jet_d1/d2/d3` for all phase indices), as the torsion engine already does.
- `checkEnergy` bounds `|coeff₀(m) - E0|` + model radius; `energyAverage` is the average on the real
  unit cube, inside `T_ρ` (real points), so `Encloses.average` applies.
- Smallness: the signed `hC1`/`hdisp` use `ρ^(4·(τ:ℝ))` (rpow); SO-SOUND bridges to the ℚ `ρ^(4τ)`
  via `Real.rpow_natCast` and `isoC1_le_isoC1Q`/`isoC2_le_isoC2Q` (premises all from StaticFacts).
- `checkStatic` does not check `emb`/`wit` list lengths (missing data denote `0`, F2).
- No signed definition was underspecified enough to stop; the bodies follow design §1/§4.

## Errata / deviations
- None in pinned sources. Deviation: Tests data duplicated from Tests/Torsion (bodies unexposed).

AUDIT FOCUS: (1) every signed declaration (CertParams, TorusCertificate and .D/.H/.K, the eight sub-checks, checkTorusCertificate, G1Hyps, CertifiedTorus) byte-identical to /root/code/KAM-inp/.drafts/design/SOSignatures.lean §G; (2) G1Hyps states exactly the hypotheses of the sealed frozen theorem KAM.Iso.Apost.g1_explicit (no hypothesis weakened, strengthened, dropped or added; carriers and norms as in the frozen file), and CertifiedTorus says what design §1/§G says; (3) SUFFICIENCY: for each G1Hyps hypothesis, name the sub-check conjunct(s) that SO-SOUND must use to establish it, and flag any hypothesis that no conjunct can establish (a checker too weak for its soundness theorem is a FAIL, not a note); (4) fail-closed behaviour: every getD/default read (checkHamBounds tables, d1/d2/d3, emb/wit lengths, F2) is either computed by the checker itself or provably harmless; a malformed or short advice list must never make a bound pass that the true data would fail; (5) checkSmallness in ℚ with Nat powers versus the signed rpow forms, and the direction of isoC1Q/isoC2Q; (6) freqNormLo soundness (‖ω‖ ≥ |c_i| − r_i in the sup norm used by the frozen statement); (7) advice key families: the new invariance keys [5, a, l] are disjoint from [0,…], [3,…], [4,…]; (8) kernel reducibility (structural recursion only) and the decide +kernel tests, positive and fail-closed; (9) deviation: Tests data duplicated from Tests/Torsion. Report suspected design or source defects as errata candidates.

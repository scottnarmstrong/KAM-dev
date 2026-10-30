# Handoff W0-ANALYSIS (branch inp-wpe)

Modules (all `KAM/Wave/Normal/Analysis/`, namespace `KAM.Wave`, 3601 lines total, each file < 400 lines):
EllSeq, SineSeries, SineProducts, Gradient, SelectionRule, RealAlgebra, EvenMajorant, SeqBridge,
CubicSelect, CubicTools, CubicBound, CubicLinear, CubicHeadline, CubicAnalytic, PdeBase, PdeForce,
PdeForward, PdeConverse (the last written by a forked sub-agent, reviewed/built by me).
Imports only Mathlib, frozen Wave Defs, and `KAM.Wave.Recon.*` (SineFeature, ReconAnalytic, SineCompleteness).
No Wave/Seq, Wave/Normal(other), no inp-wpf, no Provider/Theorems.

## Labels proved -> Lean declarations
- `bpW:w0n:recon-bounded`: `waveEll_summable_pow_mul`, `waveEll_tsum_pow_mul_le` (Σ|c_j|j^k ≤ M‖c‖, `waveEllMajorant`),
  `waveSineSeries_abs_le` (|S_k c(x)| ≤ √(2/π) M ‖c‖), `waveSineSeries_tendstoUniformly`, `waveSineSeries_add/_smul`,
  `hasDerivAt_waveSineSeries`, `contDiff_waveSineSeries`, `iteratedDeriv_waveSineSeries`, `waveSineSeries_zero_apply`,
  `waveSineSeries_pi`, `integral_waveSineSeries_mul_sineMode`, `waveEll_mul_poly` (multiplier lowers p),
  `integral_sineMode_mul_sineMode` (orthonormality). Sequences: `WaveEll a p c`, `waveEllNorm`.
  "Bounded linear map into C^k" is stated as: sup bound for each derivative order + additivity/homogeneity (no C^k norm space).
- `bpW:w0n:gradient`: `waveU`, `waveCubic`, `waveG` (sequence level; `reconU_eq_waveU`, `cubicGrad_eq_waveCubic` link to frozen),
  `waveG_hasSum`, `waveCubic_hasSum` (absolutely convergent quadruple/triple series; `waveQuartic` = g_ijkl),
  `integral_waveU_cube_mul_sineMode` (∫U³φ_l = √λ_l 𝒢_l), `hasDerivAt_waveG_coord` (∂G/∂q_l = 𝒢_l along `waveCoordShift`).
  Deviation (strengthening): proved for every p ∈ ℝ, a>0 (blueprint states p ≥ 0).
- `bpW:w0n:cubic-bound`: `waveTrilinear` (T), `wave_trilinear_bound` (a ≥ 0, p ≥ 1/2: abs. convergence, T ∈ ℓ^{a,p+1},
  ‖T‖ ≤ C_* ∏‖·‖, `waveCubicConst p = K_{p+1/2}²/π`, carries the √2 of E-W-N-1), linearity `waveTrilinear_add_left/_mid/_right`,
  `_smul_*`, symmetry `waveTrilinear_swap_left_mid/_mid_right`, `waveCubic_eq_trilinear` (𝒢 = T(q,q,q), a>0),
  headline `wave_cubic_bound`, `cubicGrad_mem_ell`, `cubicGrad_norm_le` with `waveCubicHeadlineConst = 8(1+2ζ(3))/π`
  (ζ(3) := Σ n⁻³), analyticity in ℓ² coordinates: `waveCubicMultilinear` (ContinuousMultilinearMap, norm ≤ C_m),
  `waveCubicLp`, `waveCubicLp_apply`, `waveCubicLp_norm_le`, `waveCubicLp_analyticOnNhd`.
- `bpW:w0n:pde-equiv`: `IsClassicalSolutionWith` (+ `isClassicalSolution_iff_with_univ` = frozen for I = ℝ), `waveV`, `waveEllToLp`,
  force identity `wave_force_identity` (U³ = Σ√λ_l 𝒢_l φ_l on [0,π], via cubic bound + sine completeness),
  (i) `wave_coeff_to_pde`, (ii) `wave_pde_to_coeff`. Hypotheses: I open (not nec. an interval); continuity into ℓ^{1,1} kept as
  (unused) hypotheses `_hqc/_hpc` of (i); C¹ into ℓ^{1,0} is `ContDiffOn ℝ 1` of `waveEllToLp 1 0 (q t)`, system as `deriv` identities in ℓ^{1,0}.
  The second identity of `bpW:w0n:force` appears as `sineModeIter_two` + `wave_pde_identity` (series form), not as a separate statement.

## Not done / caveats
- `bpW:w0n:algebra` is the landed `KAM.Wave.wave_algebra`; `RealAlgebra.lean` only bridges it to real nonnegative sequences. `bpW:w0n:quartic-coeff` closed form not proved as such: `SelectionRule.lean` proves the signed form
  (`waveQuartic_eq_signed`) and `abs_waveQuartic_le_signs` needed here (may be replaced by the quartic-coeff package).
- Names: generic helper names were prefixed (`wave_…`/`w0a…`); a scan against all other KAM files found no clash.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-wpe <all 18 Analysis modules>` -> "Build completed successfully (3163 jobs)".
- `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpe`: exit 0 (tail: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
  `gen_root_imports.py` was run and committed (KAM/Root/Wave.lean).
- `#print axioms` (propext, Classical.choice, Quot.sound only): waveSineSeries_abs_le, contDiff_waveSineSeries,
  integral_waveSineSeries_mul_sineMode, waveG_hasSum, waveCubic_hasSum, hasDerivAt_waveG_coord, integral_waveU_cube_mul_sineMode,
  wave_trilinear_bound, wave_cubic_bound, cubicGrad_norm_le, waveCubicLp_analyticOnNhd, waveCubicLp_norm_le,
  waveTrilinear_swap_left_mid, wave_force_identity, wave_coeff_to_pde, wave_pde_to_coeff.
- No `sorry`, no heartbeat overrides.

## Suspected errata / deviations
- Blueprint Lemma bpW:w0n:gradient needs p ≥ 0 only cosmetically (a>0 suffices); recon-bounded's continuity hypothesis in pde-equiv (i) is unnecessary.
- No blueprint defect found; constant carries √2 as in E-W-N-1 (verified: ‖x‖ ≤ √2‖q‖ in `waveEvenAbs_weighted`).

## Design signals
- `waveQuartic_eq_signed` first timed out at default heartbeats as one theorem; split into 4 lemmas (no override).
- `Fin 3` update lemmas inside `MultilinearMap` fields use a local `DecidableEq` instance: `decide` must be done in standalone lemmas (`wave_fin3_ne_*`).

## Refactor (after landing of W0-NORMAL and W1-SEQ on `inp`)
- Merged `inp` into `inp-wpe`; `KAM/Root/Wave.lean` conflict resolved by `gen_root_imports.py`.
- `waveQuartic` is now an `abbrev` for the landed `sineQuarticCoeff` (same integral), `waveSign` an `abbrev` for `boolSign`;
  `SelectionRule.lean` shrank to one theorem `abs_waveQuartic_le_signs := abs_quarticCoeff_le`. Deleted duplicates:
  `waveQuartic_eq_signed`, `waveQuartic_eq_brackets`, `sineMode_mul4_eq`, `waveSigned_indicator_alg`, `integral_cos_mul_cos_int`,
  `abs_waveSign_prod` (the landed `sineQuarticCoeff_signed` replaces the former).
- New `SeqBridge.lean`: `waveEll_iff_isEll` (WaveEll ↔ `IsEll`), `waveEllNorm_eq_ellNorm`, `waveEllToLp_eq_tauLp`,
  `coeff_isEll_one_one`, connecting to `KAM.Wave.Seq` (`IsEll`, `ellNorm`, `tauLp`). Nothing else was rewritten.
- Second refactor (W1-ALGEBRA landed): deleted `ConvAlgebra.lean` and `ConvYoung.lean` (all `w0a` duplicates of Young/weights/constants).
  New `RealAlgebra.lean` bridges real nonnegative sequences to the landed complex `wave_algebra` (`w0a_convAlgebra_nonneg`,
  `w0a_summable_of_weighted` via `wave_l1_le_of_mem`). Landed `waveConv`, `waveTwoWeight`, `waveJap`, `waveAlgConst` are used directly;
  the former tsum-defined constant is replaced by `waveCubicHeadlineConst = 8(1 + 2 Re ζ(3))/π` (ζ = `riemannZeta`).

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure (blueprint w0-normalization.tex: `recon-bounded`,
`gradient`, `cubic-bound`, `pde-equiv`/force identity). W2 and W3 consume it. It has no provider and no seal, so skip
audit item 1.
1. Statement fidelity against the CURRENT inp blueprint. After the cleanup, G and G_q are defined on ℓ^{a,p} for a > 0
   (`bpW:w0:Gq`, `bpW:w0:H`); the cubic bound is for p ≥ ½ with the √2 of E-W-N-1; C_m = 8(1+2ζ(3))/π.
2. Links to the frozen definitions: `reconU_eq_waveU` and `cubicGrad_eq_waveCubic` must hold for exactly the frozen
   functions; `isClassicalSolution_iff_with_univ` must match frozen `IsClassicalSolution` at I = ℝ.
3. `pde-equiv` (i): the unused hypotheses `_hqc`/`_hpc` (continuity into ℓ^{1,1}). Are they an extra premise?
   (ii): the hypothesis forms (ContDiffOn ℝ 1 into ℓ^{1,0}).
4. The refactor bridges `SeqBridge.lean` (to KAM.Wave.Seq) and `RealAlgebra.lean` (to KAM.Wave.Algebra): check that
   they are correct and that no duplicate of a landed definition remains.
5. Hygiene. This is a SLIM worktree, so run lint only via `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpe`.
   Run the kernel replay of all modules. Regenerated roots are authorized. Memory is tight: one lean process at a time,
   LEAN_NUM_THREADS=1.

# W2-RECON handoff

Package: `blueprint-W/parts/w2-reconstruction.tex`, all of it. Branch `inp-wpi`. Off-frontier infrastructure,
consumed later by the `nlw2` provider (no frozen theorem or provider imported).

## Files (new, all under `KAM/Wave/Recon2/`, namespace `KAM.Wave`)
| file | lines | content |
|---|---|---|
| `Functionals.lean` | 328 | `bpW:w2:derived`, `bpW:w2:functionals` |
| `Force.lean` | 103 | `bpW:w2:force` |
| `Orbit.lean` | 110 | `bpW:w2:coeffsol`, `bpW:w2:orbit`, `bpW:w2:curve-deriv` |
| `Curve.lean` | 220 | `bpW:w2:curve` |
| `Main.lean` | 127 | `bpW:w2:main`, `bpW:w2:clause5` |

## Labels and Lean declarations
- `bpW:w2:derived`: `reconUx`, `reconUxx` (+ `reconUx_eq_iter`, `reconUxx_eq_iter`), constants `reconWaveC0` (`c₀`),
  `reconWaveBound` (`M_m`, with `(1+m)^{1/4}` written `√√(1+m)`).
- `bpW:w2:functionals`: `reconWave_functionals` (analytic features `reconFeatureU m hm 0/1/2`, `reconFeatureV m hm 0`;
  pairings; norm bounds `norm_reconFeatureU_le`, `norm_reconFeatureV_le`; `abs_reconU_le`, `abs_reconUx_le`,
  `abs_reconV_le`; derivatives; boundary values `reconU_apply_zero`, `reconU_apply_pi`).
- `bpW:w2:force`: `reconWave_force` (`reconWave_force_summable_lin/_cub`, `reconWave_force_lin`, `reconWave_force_cub`);
  built on `wave_force_identity`, `summable_abs_sqrtLam_waveCubic`.
- `bpW:w2:coeffsol`: `IsAnalyticCoeffSolution`. `bpW:w2:orbit`: `isAnalyticCoeffSolution_orbit`.
  `bpW:w2:curve-deriv`: `hasDerivAt_coeffSol_fst/_snd`, `coeff_deriv_coeffSol_fst/_snd` (via `hasDerivAt_coeffW`,
  `coeffW_one_one` from `KAM/Wave/Seq`).
- `bpW:w2:curve`: `reconWave_curve` (parts `analyticAt_reconWave_*`, `hasDerivAt_reconWave_ut/_utt/_ux`,
  `isClassicalSolution_reconWave`, `reconWave_bound`).
- `bpW:w2:main`: `reconWave_main` (bound `M_m * B`) and `reconWave_main_le` (bound any `R ≥ M_m * B`; with
  `R := C * Real.sqrt (I 0 + I 1)` the fourth conjunct is the frozen text). Hypotheses (H1) `IsAnalyticTorusEmbedding K`
  (only `.2.1` used), (H2) the frozen clause (4) for all `θ, j` (for `K I := K, ν I := ν`), (H3) `‖K θ‖ ≤ B`.
- `bpW:w2:clause5`: `reconWave_clause5`, `C = max 1 M_m * C₃`; delivers `C₃ ≤ C`, the clause (3) norm bound with `C`
  and clause (5) with `K I`, `ν I`, `Γ`, `C * Real.sqrt (I 0 + I 1)`.
- Remarks (`hidden`, `hyp`, `constants`) carry no statements to formalise.

## Checks
- Verbatim check (scratch file, not committed): a theorem whose hypotheses/conclusion are the frozen clauses (3)
  [analyticity-of-embedding and norm-bound conjuncts], (4), (5) copied from `KAM/Frozen/Wave/Theorems/Nlw2.lean`
  closes by `obtain ⟨C, -, h0, -, hb, h5⟩ := reconWave_clause5 …; exact ⟨C, h0, hb, h5⟩`. So the conclusions are
  syntactically the frozen conjuncts.
- Gate builds: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpi KAM.Wave.Recon2.Main`
  → `✔ Built KAM.Wave.Recon2.Main`, `Build completed successfully (3292 jobs)`. No warnings from Recon2 files.
- `#print axioms` of `reconWave_functionals`, `reconWave_force`, `isAnalyticCoeffSolution_orbit`, `reconWave_curve`,
  `reconWave_main`, `reconWave_main_le`, `reconWave_clause5`: `[propext, Classical.choice, Quot.sound]`.
- Lint: see the bottom of this file.

## Uncertainties / deviations
- None of the statements was changed. The blueprint bound `(1+m)^{1/4}` is written `Real.sqrt (Real.sqrt (1 + m))`
  (equal; no rpow lemma stated). `M_m` is stated exactly as in the blueprint (`c₀ (2 + (1+m)^{1/4})`).
- In `reconWave_main` the fourth conjunct has `reconWaveBound m * B` (as in the blueprint), not
  `C * Real.sqrt (I 0 + I 1)`; use `reconWave_main_le` or `reconWave_clause5` for the frozen text.
- `reconWave_bound` does not need the coefficient-solution hypothesis (the bound is pure functional analysis); the
  blueprint lists it under the theorem's `Y`, which is harmless.
- Slim worktree: I copied the `inp` build artifacts of `KAM/Wave`, `KAM/Strip`, `KAM/Fourier` into `.lake/build`
  (same commit e6a84492) so that the imported Wave modules were not rebuilt; builds went through the gate.

## Blueprint defects / errata
- None found. (Remark `bpW:w2:norms` says the factor for `Ψ^V` is `λ_j j^{-2} ≤ (1+m)^{1/2} j^{-1}`; the Lean proof
  uses `λ_j ≤ √(1+m) j`, which is the same bound and is correct.)

## Design signals
- None. Largest file 328 lines; every file builds in under 10 s; no heartbeat issues.

## Lint
`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpi` (after `python3 scripts/gen_root_imports.py`, which added 5 lines to `KAM/Root/Wave.lean`): exit 0.
```
check_lean_modules: PASS (1720 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is on the path to the headline: blueprint W2 (w2-reconstruction.tex) proves frozen nlw2 clause (5)
from clauses (3)–(4). It has no provider and no seal, so skip audit item 1.
1. PRIORITY: `reconWave_main` and `reconWave_clause5`. Compare their conclusions conjunct by conjunct with clause (5)
   of /root/code/KAM/KAM/Frozen/Wave/Theorems/Nlw2.lean:
   - AnalyticAt on Set.univ ×ˢ Icc 0 π;
   - IsClassicalSolution m hm (fun t x => reconU m hm (K I (θ₀ + t • ν I)).1 x);
   - the HasDerivAt identity with reconV;
   - the bound with derivWithin and C·√(I₀+I₁).
   Ideally elaborate a scratch probe whose statement is the frozen clause-(5) text, closed by these theorems (no frozen
   import needed: copy the text). Check that the hypotheses are exactly (H1) the analyticity conjunct of
   IsAnalyticTorusEmbedding, (H2) frozen clause (4), and (H3) the norm bound, with nothing conclusion-shaped. Check the
   common-C rule C = max(1, M_m)·C₃.
2. The dropped coefficient-solution hypothesis in `reconWave_bound`, and the √√(1+m) form of (1+m)^{1/4}.
3. Hygiene. This is a SLIM worktree (plus copied inp artifacts for KAM/Wave, Strip, Fourier), so run lint only via
   `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpi`. Run the kernel replay of the 5 modules. Regenerated
   roots are authorized. Memory is tight: one lean process at a time.

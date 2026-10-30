# Handoff W1-ANALYTIC (branch inp-wpd)

Status: all labels of `bpW:w1:analytic` done (modulo the notes below). Off the frontier infrastructure; dependency graph still being built.

## Files (all new, KAM/Wave/Analytic/)
Cauchy, Complexification, ComplexificationLp, DegreeSeries, Separable, HoloAnalytic, UniformLimit, TorusAnalytic,
Flow/{Integral, Gronwall, Picard, PicardHolo, Limit, Holomorphic}. Also regenerated `KAM.lean` and `KAM/Root/Wave.lean` (gen_root_imports.py). Max file length 201 lines.

## Labels -> declarations (namespace KAM.Wave)
- complexification: `complexifyLp`, `reLp`, `conjLp` (ℓ²_ℝ/ℓ²_ℂ over ℕ+), `complexifyWave`, `reWave`, `WaveSpaceC`.
- complexification-lemma: (i) `norm_complexifyLp`, `norm_reLp_le`, `norm_conjLp`, `conjLp_smul`, `norm_sq_complexify_add_I_smul` (+ `reWave_complexifyWave`); (ii) `analyticAt_comp_realLinear`; (iii) `analyticAt_real_part`.
- holomorphic: no definition needed (`DifferentiableOn ℂ`).
- cauchy: `norm_fderiv_le_div_of_ball`, `norm_fderiv_le_div_of_ball_subset`, `lipschitz_of_margin`.
- deriv-continuous: `norm_fderiv_sub_le_holoMargin`, `continuousOn_fderiv_of_holomorphic`.
- uniform-limit: `holomorphic_of_tendstoUniformlyOn` ((i), incl. derivative convergence), `mem_of_tendstoUniformlyOn` (reality, closed set R), `norm_fderiv_le_div_of_tendstoUniformlyOn` ((ii)).
- holo-analytic-fd: `analyticOnNhd_of_differentiableOn_banach` (all n incl. 0), `holomorphic_fd_power_series` (n ≥ 1, quantitative, HasFPowerSeriesOnBall, binomial bound), `holomorphic_real_part_analytic` (real clause).
- torus-analytic: `torus_analytic` (analyticity, periodicity, derivative formula; uses `KAM.complexStrip`, `KAM.realInclusion` from track K).
- flow: `FlowHyp` (hypotheses), `wavePicard`, `holoFlow`; (i) `hasDerivWithinAt_holoFlow`, `holoFlow_zero`, `norm_holoFlow_sub_le`, `holoFlow_mem_ball`, `holoFlow_eq_integral`, uniqueness `eq_holoFlow_of_solution`; (ii) `holomorphicOn_holoFlow`, `norm_fderiv_holoFlow_le`; (iii) `holoFlow_mem_range` (abstract: `ι : G →L[ℝ] F` with closed range, left inverse `re`, X preserves range); (iv) `norm_holoFlow_sub_holoFlow_le`. Steps: lipschitz region `FlowHyp.lipschitzOn_ball`, picard iterates `norm_wavePicard_succ_sub_le`, holomorphy of iterates `picard_holo`, Gronwall `norm_sub_le_of_solutions`.

## Not done / caveats
- complexification-lemma (i) "commutes with τ_{a,p}, κ_{a,p}, D_μ": not formalized (those operators are defined in other, unmerged W packages); the norm/isometry facts are.
- Complexification only instantiated for ℓ²(ℕ+) and WaveSpace; flow reality (iii) is stated abstractly via (ι, re, closed range); instantiating with `complexifyLp` (closed range as isometry) is a one-liner left to consumers.
- FlowHyp requires `0 < M` (blueprint 0<M<δ). Flow conclusion (i) is stated as HasDerivWithinAt on [-1,1] plus continuity (`continuousOn_X_holoFlow`).

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-wpd <all 14 modules>` -> "Build completed successfully (2902 jobs)", no sorry, no errors (earlier unused-variable linter warnings in Limit.lean only).
- `w_lint.sh /root/code/KAM-inp-wpd` exit 0 (check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK).
- `#print axioms` of hasDerivWithinAt_holoFlow, eq_holoFlow_of_solution, holomorphicOn_holoFlow, norm_fderiv_holoFlow_le, holoFlow_mem_range, norm_holoFlow_sub_holoFlow_le, torus_analytic, holomorphic_fd_power_series, analyticOnNhd_of_differentiableOn_banach, holomorphic_real_part_analytic, continuousOn_fderiv_of_holomorphic, holomorphic_of_tendstoUniformlyOn: all only [propext, Classical.choice, Quot.sound].
- Public names renamed to avoid clashes (picard -> wavePicard, continuousOn_primitive -> continuousOn_wavePrimitive, norm_fderiv_sub_le -> ..._holoMargin, FlowHyp.{lipschitz, fderiv_le, ball_subset, mem_V} -> {lipschitzOn_ball, norm_fderiv_le_ball, ball_subset_V, mem_V_of_ball}); grep of all KAM + Mathlib finds no other declarations with these names. No maxHeartbeats anywhere.

## Blueprint defects / errata
None found. Note: in flow (iii)/(iv) F's real structure is the one induced from ℂ (NormedSpace.complexToReal), avoiding an instance diamond. Design signals: none.

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure (blueprint-W/parts/w1-sequences.tex, subsection
`bpW:w1:analytic`). It has no provider and no seal, so skip audit item 1 and the seal-body probe.
1. Statement fidelity against the CURRENT blueprint text of that subsection on inp. Check the guards of `cauchy` and
   `uniform-limit` (r > 0, δ > 0, M ≥ 0; (i) qualitative without boundedness; (ii) under a pointwise bound), and the
   `holo-analytic-fd` statement for Banach targets (n ≥ 1 quantitative, n = 0).
2. `flow`: `FlowHyp` adds `0 < M`, while the blueprint has 0 < M < δ. Is that an extra premise or harmless? Is (i)
   stated faithfully as HasDerivWithinAt on [−1,1] plus continuity? Check the ball-margin hypotheses (the repair of
   P96-K A.4).
3. `torus_analytic` uses track K's `KAM.complexStrip` and `KAM.realInclusion`. Check that the conclusion matches
   what the frozen `IsAnalyticTorusEmbedding` analyticity conjunct needs (AnalyticOnNhd ℝ on `Fin 2 → ℝ`).
4. Definitions on their whole carrier: `complexifyLp`, `reLp`, `conjLp`, `wavePicard`, `holoFlow` (any junk branch
   that a theorem relies on).
5. Hygiene. This is a SLIM worktree, so run lint only via `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpd`.
   Run the kernel replay of all 14 modules.

## Round 2

- Merged `inp` (Seq landed); the only conflict was `KAM/Root/Wave.lean`, resolved by re-running `scripts/gen_root_imports.py`.
- F1 closed: new module `KAM/Wave/Analytic/ComplexificationCommute.lean` (≈130 lines), using the `RCLike`-generic Seq maps `coeffW`, `tauLp`, `weightedDiagCLM` at `ℝ` and `ℂ`; no new Seq definitions were needed. A real multiplier `μ` acts on `ℓ²_ℂ` as `fun j => (μ j : ℂ)`.
  - κ: `coeffW_complexifyLp`, `coeffW_reLp`, `coeffW_conjLp`.
  - τ: `isEll_complexify_of_isEll`, `isEll_re_of_isEll`, `isEll_conj_of_isEll`, `complexifyLp_tauLp`, `reLp_tauLp`, `conjLp_tauLp`.
  - D_μ: `weightedDiagCLM_complexifyLp`, `weightedDiagCLM_reLp`, `weightedDiagCLM_conjLp`; also `coeffW_weightedDiagCLM` (κ(D_μ y) = μ·κ y, for any RCLike K).
- F2: no action (regenerated roots authorized by the orchestrator).
- Gate: `inp_lake_build.sh ... KAM.Wave.Analytic.ComplexificationCommute` -> Build completed successfully; `w_lint.sh` exit 0 (check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK). `#print axioms` of all ten new theorems: only propext, Classical.choice, Quot.sound. No maxHeartbeats; all files far below 1500 lines.

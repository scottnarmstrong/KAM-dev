# SHARP2-ENGPAR handoff: the parameter limit of the ratio engine (B7 erratum 1)

## Files (`KAM/Sharp2/`)
- `EngineRatioPar.lean` (434 lines): defs `engX`, `engMu` (`μ_s = X_s γ δ_s^{κ+1}`), `engBeta`
  (`β₀ - ∑_{t<s} CDK_t δ_t X_t`), `engCap` (`m₀ + ∑ rate wt X`), `parSumR` (prefix `∑ Cp_s μ_s` plus
  `Cp_∞ μ_k/(1-ȳ)`), and **`StageScheme.converge_ratio_par`**.
- `EngineRatioParCor.lean` (~100): `StageScheme.noPar`, `StageConsts.noCp`, `IsNewton.noPar`, and
  **`StageScheme.converge_ratio_of_par`**: `converge_ratio` from `converge_ratio_par`.
- `KAM/Root/Sharp2.lean` regenerated (`gen_root_imports.py`); `KAM.lean` did not change.
`converge_ratio` and `converge_checked` are untouched.

## Statement
`converge_ratio_par` = the hypotheses of `converge_ratio` plus
- `hκ : 0 ≤ κ + 1` (so `δ_s^{κ+1} ≤ δ_k^{κ+1}` along the tail),
- `hCp0 : ∀ δ, 0 < δ → δ ≤ bite0R a ρ ρinf → 0 ≤ (C δ).Cp` (same nature as `hnn`),
and concludes everything `converge_ratio` does (with the same `Kinf`, `pinf` now a genuine limit) plus
- `Tendsto (fun s => S.par (stageIterR S a ρ ρinf x₀ s)) atTop (𝓝 pinf)`,
- `|pinf - S.par x₀| ≤ parSumR …`,
- `∀ s`, `S.Adm (stripSR s) (engBeta s) (engMu s) (engCap s) (iter s)`, the ball room
  `β₀ - stageBallR … ≤ engBeta s`, `ρinf < stripSR s`, and the caps `engCap s i ≤ σ i`.

## Approach
B5R's proof, plus: the step's third conjunct gives `|Δpar_s| ≤ Cp_s μ_s = (Cp_s γ δ_s^{κ+1}) X_s`; with
`Cp_s ≤ Cp_∞` and the monotonicity of `δ^{κ+1}` the coefficients are bounded by
`Cp_∞ γ δ_k^{κ+1}` for `s ≥ k`, so `partial_sum_leR`/`summable_mul_decayR` give summability of
`Δpar` (`par` of the iterates converges) and the partial-sum bound, passed to the limit.
`converge_ratio_of_par`: apply the par theorem to `S.noPar` (`par := 0`) and `Cp := 0`, for which
`IsNewton` is inherited, and project.

## Deviations / conservative choices (overnight; no owner decision needed)
- The extra hypotheses `hκ`, `hCp0` above. Without `hCp0` the prefix/tail comparison fails for
  negative `Cp`; without `hκ`, `δ_s^{κ+1}` grows along the tail.
- `converge_ratio_of_par` therefore needs `0 ≤ κ + 1` (it is not recovered for `κ + 1 < 0`, where
  `converge_ratio` itself remains true by its own proof). `hCp0` is not needed there (`Cp := 0`).

## Checks
- `nice -n 5 lake build KAM.Sharp2.EngineRatioParCor`: success, no heartbeat options.
- `lint_sources.sh`: `check_lean_modules` PASS; only the known ABI-scratch failure.
- `#print axioms` of `converge_ratio_par` and `converge_ratio_of_par` (`.drafts/engpar.lean`):
  `[propext, Classical.choice, Quot.sound]`.
- Name clash: `import KAM` is not possible in the worktree (no `KAM.olean`, a full build is
  forbidden), so I grepped all of `KAM/**/*.lean` for `engX engMu engBeta engCap parSumR noCp noPar
  converge_ratio_par converge_ratio_of_par`: no hits outside the two new files.

## Errata
None new.

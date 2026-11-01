# LP-NRS handoff (track LP, non-frozen)

## Files
- NEW `KAM/Planetary/StrongAMD/NonresonantScale.lean` (≈300 lines; imports Mathlib, `KAM.Fourier.Derivative`,
  `KAM.Nekhoroshev.NormalForm.Setting` for `conjExp`/`modeSize`).
- Regenerated (by `scripts/gen_root_imports.py`): `KAM/Root/Planetary.lean`.

## Declarations (namespace `KAM.Planetary.StrongAMD`)
- Data: `scaleExponent τ = 1/(2(τ+1))`; `scaledCutoff κ τ μ = (⌊κ μ^(-a)⌋₊ : ℝ)`; `stoppedRadius D₀ μ = D₀ √μ`;
  `divisorGap γ τ κ μ = γ/(2π) K^(-τ)`; `perturbSize M₂ μ = M₂ μ`.
- Helpers: `rpow_neg_scale_mul_sqrt`, `cutoff_rpow_mul_sqrt_le` (`K^(τ+1)√μ ≤ κ^(τ+1)`), `scaledCutoff_lower`,
  `exists_scale_kappa` (`L D₀ κ^(τ+1) ≤ γ/(4π)`, `M₂ κ^(τ+1) ≤ γ D₀/(512π)`).
- Item 1 `lp_scale_choice` (`LP:MAIN L13 (444–458)`, N6): hypotheses `0<γ, 0<τ, 0≤L, 0<M₂, 0<D₀, 0<s, 0<w, 0<ρ, 1≤k`;
  `∃ κ μ₀ c T₀, 0<κ ∧ 0<μ₀ ∧ 0<c ∧ 0<T₀ ∧ ∀ μ, 0<μ → μ ≤ μ₀ →` (a) `1 ≤ K ∧ κμ^(-a)/2 ≤ K ∧ K ≤ κμ^(-a)`;
  (b) `K*L*r ≤ α/2`; (c) `ε ≤ α*r/(2^7*conjExp 2*K)`; (d) `64*π*k*s*r ≤ w^2`; (e) `6 ≤ 2*π*K*s`; (f) `r ≤ ρ`;
  (g) `T₀*exp(c*μ^(-a)) ≤ s*r/(5*ε)*exp(2*π*K*s/6)`. Explicit: `c = π s κ/6`, `T₀ = s D₀/(5 M₂)`;
  `κ, μ₀, c, T₀` depend only on the data. Full signature: see `#check` output reproduced below.
- Item 2 `diophantine_to_period_one`: `0≤γ, 0≤τ`, `hdio : ∀ k ≠ 0, γ*modeSize k^(-τ) ≤ |∑ k i * ω i|`,
  `1 ≤ K`, `k ≠ 0`, `modeSize k ≤ K` ⊢ `γ/(2π)*K^(-τ) ≤ |∑ k i * (ω i/(2π))|`. `KAM.Fourier.modeSize` is the ℓ¹
  size (`∑ |k j|`), and `KAM.NormalForm.zBall n K = {k | modeSize k ≤ K}`: **`zBall` IS ℓ¹**, so LP-NRR can use this directly.
- Item 3 `scaleExponent_planar n (hτ : τ = n - 1/2) : scaleExponent τ = 1/(2n+1)`.

## Not done
Nothing in the brief is omitted. The engine's `IsNonresonant` form (`zBall`, `dotC`, `freq`) is left to LP-NRR.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-nrs KAM.Planetary.StrongAMD.NonresonantScale` → `Build completed successfully (9080 jobs)`.
- `lp_lint.sh` → exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- `main_shortname_check.py` → `short-name check OK`, exit 0.
- `#print axioms` (run via `lp_lean.sh` on `.drafts/ax_nrs.lean`): `lp_scale_choice`, `diophantine_to_period_one`,
  `scaleExponent_planar` all depend only on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`axiom`/heartbeat options; no design signals (build 22–26 s).

## AUDIT FOCUS
- (c): `conjExp 2` is the engine's `p/(p-1)`; unfolded to `2`. The form matches `Nonresonant.lean:341` `hsmall`
  (`ε ≤ α*rB/(2^7*conjExp p*K)`), with `r` for `b.rB`.
- (b)/(d)/(e) are the engine numerics `divisor_size` (`K*L*rB ≤ α/p`, p=2), `SL` (`64πk s rB ≤ w²`), `cutoff`;
  `k` plays the role of `m` in MAIN (37) (the engine's slow-pair count).
- (g): exponent `2πKs/6` as in the engine's time bound; needs `μ ≤ 1` (included in `μ₀`).
- `K` is a floor cast to ℝ; (a) gives `K ≥ 1` via `κμ^(-a) ≥ 2`.
- Hypotheses are positivity of data only (no conclusion-shaped premises).

## Source defects / deviations
- No errata found in (37). Deviation: MAIN (37) writes `ε ≤ αr/(256K)`, equal to the engine form since `2^7*2 = 256`.
- `L ≥ 0` allowed (L = 0 permitted), `κ` chosen with `+1` slack (`γ/(4π(L D₀+1))`) so no case split.

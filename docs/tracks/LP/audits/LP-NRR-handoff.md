# LP-NRR handoff (MAIN Lemma 13; track LP, non-frozen)

Branch `inp-lp-nrr`. All six items done; no `sorry`/axiom/heartbeat override; no existing file edited
(only the generated `KAM/Root/Planetary.lean`, via `scripts/gen_root_imports.py`).

## Files (726 lines total, largest 213)
`KAM/Planetary/StrongAMD/NonresonantReuse.lean` (facade) and `NonresonantReuse/{Kepler,Pert,PertClass,Hyp,Drift}.lean`.

## Declarations (namespace `KAM.Planetary.StrongAMD`)
- Item 1/2 (`Kepler`): `lpKepler ν I = planetaryKeplerC ν I / ((2π:ℝ):ℂ)`; `lpKeplerLip ν Imin = ∑ i, 3 ν_i³/(2π (Imin/2)⁴)`
  (sum, not max; uniform in `I⁰`); `lpKepler_differentiableOn`, `lpKepler_real`, `lpKepler_freq` / `lpKepler_freq_real`
  (`freq lpKepler I⁰ i = ν_i³/I⁰_i³/(2π)`), `lpKepler_freqLipschitz`, `lpFrequency`, `lpKepler_isNonresonant`
  (`IsNonresonant {I⁰} K (γ/(2π) K^{-τ}) {0} lpKepler` from (5) via `diophantine_to_period_one`).
- Item 3 (`Pert`, `PertClass`): `lpUnrescaleC`, `lpPert μ ℓ fc = (μ/2π) fc ∘ lpUnrescaleC ℓ` (ν not needed),
  `structure LPChartTube` (the output of `exists_strongTube`, repackaged), `lpUnrescaleC_mem_complexTube`
  (containment into `complexTube core (R/2)` via `strongCore_containment`), `lpPert_extClass`, `lpPert_sup_le`,
  `lpPert_wbound` (`WBound b.base b.rB s lpPert (lpM₂ n σ M * μ)`, `lpM₂ = coth(πσ)ⁿ M/(2π)`, via `wbound_of_sup_bound`).
- Item 4/5 (`Hyp`): `lpExtNFHyp` (full `ExtNFHyp b s K α L 2 ε {0} lpKepler lpPert`, every field), `lpTrace`
  (`((liftFast lpKepler + lpPert) (extCx y)).re = lpRescaleHam b.lam (liftChartHam ν μ) y` on `b.realDom b.rB`).
  `hsmall` is the item (c) of `lp_scale_choice`, used directly in `Drift`.
- Item 6 (`Drift`): `lpBlock ν δ I0 r w := ⟨I0, secularBall ν δ I0, r, w⟩`, `lp_exists_lower_bound`, and
  `lp_stopped_drift` (signature: `#check` output in `.drafts/axioms_nrr.txt`): for `ν, L, δ, γ>0, τ>0, D₀>0`,
  `∃ μ₀ c T₀ s σ w >0`, then for `0<μ≤μ₀`, `I0 ∈ strongLevelSet ν L δ`, (5), `b = lpBlock ν δ I0 (D₀√μ) w`, `J`, `z`, chart lift `wc`
  with DICT item-9 premises, `|t1| ≤ T₀ exp(c μ^{-scaleExponent τ})`, stopped slow membership:
  `‖keplerAction ν (z u) − I0‖ ≤ D₀√μ/2` on `uIcc 0 t1`.

## Fixed widths (chosen before μ; N6)
`R, M, fc, r_g` from D4/D1; `s₀ = b₀ = R/16`, `r_s = min(4 r_g, R/4)`, `s = σ = s₀/π` (so `2π(s+σ) = 4 s₀`), `w = 2 b₀ < 4 b₀`;
`Imin` = compactness lower bound of coordinates over `𝓛_δ`; `ρ = min(r_s, Imin)/2` (strictly inside the tube radii,
per the LP-W2A-1 note: `D₀√μ ≤ ρ < r_*`, never a silent `≤ r_*`); `L = lpKeplerLip ν Imin`, `M₂ = lpM₂ n σ (max M 1)`; then `lp_scale_choice` gives `κ, μ₀, c, T₀`.

## Not done
Nothing in the brief omitted. (First exit L14 and planar theorem T15 out of scope.) Stale merged modules (NRS, DOM, DICT) were rebuilt through `lp_build.sh` first.

## Checks
- `lp_build.sh` (import order) `…NonresonantReuse.{Kepler,Pert,PertClass,Hyp,Drift}` and the facade: all `Build completed successfully`.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- `main_shortname_check.py` on the six modules: `short-name check OK`, exit 0.
- `#print axioms` (`.drafts/ax_nrr.lean` → `.drafts/axioms_nrr.txt`): `lpKepler_differentiableOn`, `lpKepler_real`, `lpKepler_freq_real`,
  `lpKepler_freqLipschitz`, `lpKepler_isNonresonant`, `lpUnrescaleC_mem_complexTube`, `lpPert_extClass`, `lpPert_wbound`, `lpExtNFHyp`, `lpTrace`,
  `lp_stopped_drift`: all exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- `lp_stopped_drift` statement: premises are only the physical solution, chart lift, `realDom` membership, initial action, time bound, stopped
  membership; quantifier order (constants before `μ`, `I0`, solution). Hypothesis (5) written with `ν i^3 / I0 i^3`.
- `lpUnrescaleC_mem_complexTube`: the three D5 conditions (hact via `rB ≤ r_s`; hang via `2π t ≤ 4 s₀`; hslow via `ℓ·rB = w < 4 b₀`).
- `lpTrace`: uses a width `t = 2 s₀/π` only to place the real point in the tube (reality of θ makes the width irrelevant).
- `lpExtNFHyp`: `p = 2`, `k = n`, `α = γ/(2π) K^{-τ}`, `ε = M₂ μ`; `pert` at width `s`, `bound` through width `s+σ`.
- `LPChartTube` is exactly the D4 output (not an extra hypothesis); `max M 1` makes `M₂ > 0`.

## Source defects / deviations / design signals
- No errata. Deviations: `lpKeplerLip` is a sum over coordinates (not max); `lpPert` omits the unused `ν` argument; `M` replaced by `max M 1`.
- No heartbeat or size issues (all files build in ≤ 20 s, ≤ 213 lines).

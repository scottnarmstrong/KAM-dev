# Handoff SHARP-BOX

## Files (all new; plus regenerated `KAM.lean`)
- `KAM/Sharp/BoxTorsion.lean`: `torsion_sub_param` (`T_{h'} - T_h = Nᵀ Ω₀ (A'-A) N`), `norm_torsion_sub_param_le`,
  `norm_torsionAverage_sub_param_le`, `inv_rowSum_of_perturb` (index-generic row-sum Neumann step).
- `KAM/Sharp/Box.lean`: `KAM.Sharp.BoxH1`, `torsionShift`, **`KAM.Sharp.g1_box`**.
- `KAM/Iso/Sharp/BoxLemmas.lean`: `energyRow_sub_param`, `sum_norm_energyRow_sub_param_le`,
  `norm_extendedTorsion_sub_param_le`, `norm_extendedTorsionAverage_sub_param_le`, `norm_energyAverage_sub_param_le`.
- `KAM/Iso/Sharp/Box.lean`: `KAM.Iso.Sharp.BoxH1`, `extShift`, **`KAM.Iso.Sharp.g1_box`**.
Largest file 211 lines.

## Approach
Both corollaries apply `g1_explicit` (resp. `Iso.Apost.g1_explicit`, body `IG1Body`) as a black box at the parameter `l`,
with the same `K`, `ω` (`s • ω*`), `γ`, `E₀`, and the enlarged error `e_l = e + L·dist l l₀`; no iteration is re-proved.
- Λ is an arbitrary `PseudoMetricSpace` (covers `Fin m → ℝ` with sup norm; only `dist l l₀` is used).
- H1 for each `l ∈ S` is the def `BoxH1` (the first nine hypotheses of the frozen body; five M-bounds in the iso case).
- Lipschitz data (on the domain): `‖X_l - X_{l₀}‖ ≤ L₀ δ`, `‖DX_l - DX_{l₀}‖ ≤ L₁ δ`; iso additionally
  `|H_l - H_{l₀}| ≤ L_E δ` (energy) and `‖DH_l - DH_{l₀}‖ ≤ L_Y δ` (last row of the bordered torsion).
- Invariance error: `E_l = E_{l₀} + (X_l - X_{l₀}) ∘ K`. Energy (iso): average of `H_l∘K - H_{l₀}∘K`, error `e + max{L₀,L_E} δ`.
- Torsion: `N` depends on `K` only, so `T_l - T_{l₀} = Nᵀ Ω₀ (A_l - A_{l₀}) N`, pointwise bound `2n((σK-μ)(σB-μ))² L₁ δ`
  (`torsionShift`); iso: bordered block `max{torsionShift, (σK-μ)(σB-μ) L_Y δ}` (`extShift`, frequency column unchanged).
  Averages via continuity on the real torus (`continuous_torsion_real`, `extended_regular`).
- Neumann (exact, not the factor-2 version): `‖T_l⁻¹‖ ≤ b₀/(1 - b₀Δ)`, stated as `b₀Δ ≤ 1/2` and `b₀ ≤ (σT-μ)(1 - b₀Δ)`.
- Conclusions: exactly those of `g1_explicit`, with `C₂ (e + L·dist l l₀)/(γ² ρ^{2τ})` (and `C₃` in the iso case).

## Statements (explicit smallness of d, dist l l₀ ≤ d)
Fixed frequency, extra hypotheses: `0 ≤ d`, `b₀ Δ ≤ 1/2`, `b₀ ≤ (σT-μ)(1-b₀Δ)` with `Δ = torsionShift n σK σB μ L₁ d`,
`C_1 (e + L₀ d)/(γ⁴ρ^{4τ}) < 1`, and at `l₀`: twist row sums `≤ b₀`, error `≤ e`. Iso: same with `extShift`, `isoC1`, `max L₀ L_E`.
Draft statements were elaborated by building; no conclusion-shaped hypotheses (only data, Lipschitz bounds, H1, hypotheses of
`g1_explicit` at `l₀` and explicit smallness of `d`).

## Checks
- `nice -n 5 lake build KAM.Sharp.BoxTorsion KAM.Sharp.Box KAM.Iso.Sharp.BoxLemmas KAM.Iso.Sharp.Box`: succeeded, no errors.
- `#print axioms KAM.Sharp.g1_box` and `KAM.Iso.Sharp.g1_box`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: line length OK, `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`; the final ABI scratch
  step errors with `.lake/build/lib/lean/KAM/Frozen/Iso/Defs/BorderedHessian.olean ... does not exist` (module not in this
  worktree's build snapshot; unrelated to the new files).
- `python3 -I scripts/gen_root_imports.py` run; `KAM.lean` gains the four new modules.

## Uncertainties
- Hypotheses `hopen₀ …` of H1 at `l₀` are only used via `l₀ ∈ S`; unused-variable lint notes may appear.
- `L₀` and `L_E` are merged by `max` in the iso error; a sharper split (separate error budgets) is possible.
- The conditions are stated in terms of the radius `d`; the monotone case `dist l l₀ < d` follows.

## Errata / deviations
None found. Deviation: `L₁`-Lipschitz hypothesis is on `fderiv ℂ X_h` directly (no differentiability of `X_h` needed).

# SHARP-A5 handoff: fixed-frequency scheme and the sharp G1

## Files (new)
`KAM/Sharp/Scheme.lean` (310 lines), `KAM/Sharp/G1.lean` (~310 lines); `KAM.lean` regenerated.

## Approach
- `fixedScheme`, `fixedConsts` as in the signatures. `fixedScheme_isNewton`: (N1) from `Admissible`;
  (N2) from `step_spec` applied to `Admissible σK σB σT` obtained by weakening `m_i ≤ cap_i ≤ σ_i`
  (from the cap hypothesis and `rate ≥ 0`); new bounds by the triangle inequality from the `rateD/B/T`
  increments (`norm_le_add_of_sub_le`); `r - 3δ` strips by `strip_mono`.
- `engine_hyps`: helper `fixed_arith` (`q e/(γ² δ₀^{2κ+j}) ≤ μ/4` from `4γ̄² q ≤ 𝔠_sum ≤ μ 𝔠_*` and
  `absorb`); (I1),(I2) from `2^{2a}C_E, 𝔠_step ≤ 𝔠_*`.
- `delta0s = Engine.delta0 3` is `rfl` (`delta0_fixed_eq`).
- `g1_core` (internal, new name): conclusion of G1 with closeness `2 C_ΔK e/(γ² δ₀^a)` from
  `e ≤ 1`, `𝔠_* e/(γ⁴ δ₀^{2a}) ≤ 1`; runs `Engine.Scheme.iterate/limit`, then the ball clause by
  `lim_margins`, `‖DK_∞‖` by the cap and `le_of_tendsto`, invariance by `lim_invariance`.
- `g1_gen` from `g1_core` + `KAM.Apost.g1_error_small_aux` + `g1_closeness_eq`; the three instances
  from `cohData_russmann/parseval/crude`; `g1_sharp_uniform` from `g1_core` directly (it states the
  closeness in the `2 C_ΔK e/(γ² δ₀^a)` form).
- All signatures copied verbatim from `APOST-SHARP-SIGNATURES.lean.txt`.

## Checks
- `nice -n 5 lake build KAM.Sharp.G1` (builds Scheme too): success, no heartbeat options.
- `sh scripts/lint_sources.sh`: no complaint on my files; remaining long-line reports are in
  `TorsionBound.lean`, `TorsionPoly.lean` (A3, not mine) and the known ABI-scratch failure.
- `#print axioms` of `fixedScheme_isNewton`, `engine_hyps`, `g1_gen`, `g1_sharp`,
  `g1_sharp_parseval`, `g1_sharp_crude`, `g1_sharp_uniform`: `[propext, Classical.choice, Quot.sound]`.
- Probe `.drafts/a5b.lean`: `mkAppN g1_sharp (binders of KAM.Apost.g1_explicit)` type-checks, i.e. the
  20 binders are identical; the conclusion is `0 < C₁♯ ∧ 0 < C₂♯ ∧ G1Body …` with `G1Body` copied
  verbatim from `g1_explicit`.

## Uncertainties / errata / deviations
- None: no signature signal. Extra helper names: `delta0_fixed_eq`, `fixed_consts_pos`,
  `fixedConsts_j`, `norm_le_add_of_sub_le`, `fixed_arith`, `g1_core`.
- `fixedScheme_isNewton` calls `consts_pos` with `μ := 1` (its `μ` argument is unused), since the
  signature only has `0 ≤ μ`.

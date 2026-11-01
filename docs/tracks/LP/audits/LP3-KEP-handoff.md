# Handoff LP3-KEP (Kepler part as partial-convexity fast Hamiltonian)

## Files
- New: `KAM/Planetary/StrongAMD/Nek/Kepler.lean` (253 lines). Regenerated (generator output only): `KAM/Root/Planetary.lean`.
- Imports: frozen DEFINITIONS (`HasDefiniteFastPart`, `RealPart`, `FrequencyMap`, `ActionNbhd`), track P's `Exponential/KeplerData.lean` (reuse; not `Stopped.lean`), `StrongAMD/Threshold/Defs` (for `chamber`). No provider, no theorem anchor.

## Declarations (namespace `KAM.Planetary.StrongAMD`)
- `exists_pos_le_forall_fin`, `exists_chamber_bounds`, `actionNbhd_re_near`: helpers (finite positive min; compact `U ⊆ chamber ν` has `0<Imin≤I_i≤Imax`; real parts of `actionNbhd G' ρ` within `ρ₀+ρ` of one `u ∈ U` when `G' ⊆ cthickening ρ₀ U`).
- `exists_keplerMargin` (statement 1): `∃ Imin Imax, 0<Imin ∧ 0<Imax ∧ (∀ I∈U,∀ i, Imin ≤ I i ≤ Imax) ∧ ∀ G' ⊆ cthickening (Imin/4) U, ∀ ρ ≤ Imin/4, (∀ z ∈ actionNbhd G' ρ, ∀ i, Imin/2 ≤ (z i).re ∧ Imin/4 ≤ ‖z i‖) ∧ ∀ real I in the nbhd, Imin/2 ≤ I i ≤ Imax+Imin/2`.
- `keplerHessConst ν c := ∑ 3 ν_i³ / c⁴` (`= Mcomplex`, `c = Imin/2`); `keplerHessConst_pos`.
- `keplerC_clauses`, `keplerCNeg_clauses` (statement 2, for `h` and `-h`): `DifferentiableOn ℂ`, `ContDiffOn ℂ 2`, reality on real points, `‖fderiv ℂ (fderiv ℂ h) z‖ ≤ keplerHessConst ν c`, under only `∀ z ∈ actionNbhd G' ρ, ∀ i, c ≤ (z i).re`.
- `keplerC_definite` (statement 3): `HasDefiniteFastPart G' ρ (νmin³/Ibar³) (3νmin³/Ibar⁴) (planetaryKeplerC ν)` (σ = -1) from real-point bounds `0<I_i≤Ibar`, `0<νmin≤ν_i`, `1 ≤ n`; `-h` via track P's `hasDefiniteFastPart_neg` (σ = 1). The frequency bound `g ≤ ‖frequencyMap h I‖` and `ContDiffOn ℝ 3 (realPart h)` are components of the sealed definition.
- `lp3_kepler_data` (statement 4): for `1 ≤ n`, `∀ i, 0<ν i`, compact `U ⊆ chamber ν`: `∃ ρ₀ g m Mcomplex`, all positive, depending only on `(ν,U)` (`ρ₀=Imin/4`, `g=νmin³/(Imax+Imin/2)³`, `m=3νmin³/(Imax+Imin/2)⁴`, `Mcomplex=keplerHessConst ν (Imin/2)`), such that for every `G' ⊆ cthickening ρ₀ U` and `0<ρ≤ρ₀` the premises `hhol, hC2, hreal, hHess, hdef` of `partialConvex_nekhoroshev` hold for `planetaryKeplerC ν` and for `-planetaryKeplerC ν`. Convexity/openness of `G, G'`, `hcollar`, `hn`, `hk` are not fast-Hamiltonian premises and are left to the caller.

## Checks
- `lp_build.sh … KAM.Planetary.StrongAMD.Nek.Kepler`: `Build completed successfully (9133 jobs)`; no warning in this file (an initial `haveI` style warning was fixed).
- `lp_lint.sh`: exit 0 (after `python3 scripts/gen_root_imports.py`, whose `KAM/Root/Planetary.lean` change is committed).
- `main_shortname_check.py … KAM.Planetary.StrongAMD.Nek.Kepler`: `short-name check OK`, exit 0.
- `#print axioms` of `lp3_kepler_data`, `exists_keplerMargin`, `keplerC_clauses`, `keplerCNeg_clauses`, `keplerC_definite`: `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- Collar choice `ρ₀ = Imin/4` (brief suggested `Imin/2`; with `Imin/2` the real part margin would only be `> 0`, not `≥ Imin/4`): margin proved is `Re z_i ≥ Imin/2`, strictly stronger than the brief's `‖z_i‖ ≥ Imin/4`, which is also stated.
- Reuse of `G' ⊆ cthickening ρ₀ U` (not just `= cthickening`) with `ρ ≤ ρ₀`: check `actionNbhd_re_near`.
- `m` and `g` use `Ibar = Imax + Imin/2` (real points lie within `2ρ₀` of `U`), not `Imax`.
- `hn : 1 ≤ n` (weaker than the theorem's `2 ≤ n`); needed only so the frequency norm has a coordinate.
- Exact match of `hHess`/`hdef` statement shapes to the theorem's binders (including `-h` as `-planetaryKeplerC ν`, function negation).

## Errata / deviations / design signals
- No source defects. Deviation: `ρ₀ = Imin/4` instead of the example `Imin/2` (see above). No heartbeat or size issues (253 lines, builds in ~7 s).

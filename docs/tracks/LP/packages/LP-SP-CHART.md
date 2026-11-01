# Package LP-SP-CHART: regular spatial Poincaré coordinates (MAIN Lemma 17), one body

Wave 4, the largest spatial package. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff). Base: `inp-lp-spchart` = `inp-lp` + LP-SP-ROT (`KAM/Planetary/Spatial/Rotation46.lean`;
handoff `docs/tracks/LP/audits/LP-SP-ROT-handoff.md`). LP-SP-MODEL (the spatial `Phase (n*3)` model and elements)
is in progress in parallel. This package works with raw one-body vectors `q p : Fin 3 → ℝ` and does not need it.
The product over `n` bodies and the `Phase (n*3)` packaging come in a later package.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 17, lines 533–578: (44), (45), (46), the symplectic computation
(562–569), and the inverse (571–576). Read with `source/AMENDMENTS.md`. The planar chart is reused unchanged:
`KAM/Planetary/Poincare/*` (`poincare`, `poincareDom`, `poincare_elements`, `poincare_symplectic`, `poincareInv`,
`analyticOnNhd_poincare`, `poincare_periodic`).

## Definitions (one body, mass `ν`, `κ = 1`)

- **Domain (44).** `spatialPoincareDom : Set (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)` (or `Phase 3` with a documented coordinate
  order `(λ, x, u ; I, y, v)`): `I > 0` and `Γ + Z < I`, where `Γ = (x² + y²)/2` and `Z = (u² + v²)/2`.
- **Chart (46).** `spatialPoincare ν w := (R ·(Q, 0), R ·(P, 0))`, where `(Q, P) = poincare ν 1 (λ, x; I, y)`
  (the planar chart, embedded with `planarEmbed`), `R = incRotation u v G` and `G = I − Γ`. Write it literally;
  no `if`.

## Theorems

1. **Well-definedness on the carrier.** On (44), `G > 0` and `Z < G`, so LP-SP-ROT's carrier holds. The planar
   point lies in `poincareDom`.
2. **(45).**
   - The Kepler energy of `(q, p)` (specific or total, consistent with the planar convention) is
     `−ν³/(2I²)`. Rotation invariance plus `poincare_elements`.
   - `|q ⨯₃ p| = G`.
   - `(q ⨯₃ p) ⬝ᵥ e₃ = I − Γ − Z` (LP-SP-ROT `incRotation_cross_dot_e₃`).
   - The eccentricity vector is `R` applied to the planar one.
3. **Image.** `spatialPoincare` maps (44) into the negative-energy spatial states with `(q ⨯₃ p) ⬝ᵥ e₃ > 0`,
   and onto them (MAIN 571–576). The inverse is analytic, and the chart is injective modulo `λ ↦ λ + 2π`.
   - Use LP-SP-ROT item 5 (recovery of `u`, `v`).
   - `R⁻¹ = Rᵀ` maps the state to a planar state with positive angular momentum.
   - Then apply `poincareInv`.
4. **Analyticity and periodicity.** `AnalyticOnNhd ℝ spatialPoincare` on (44), and `2π`-periodicity in `λ`.
5. **Symplecticity (MAIN 562–569).** The pullback of `dp ∧ dq` (sum over the three coordinates) is
   `dI ∧ dλ + dx ∧ dy + du ∧ dv`, in the repository's convention: compare `poincare_symplectic` and
   `KAM/Planetary/Poincare/Symplectic.lean`, and state it the same way, with the explicit symplectic bilinear
   form on derivatives.
   - Route (MAIN): the rotation contributes `L · (infinitesimal rotation vector)`, so
     `p · dq = I dλ + Γ d(−ϖ) + Z d(−h_n) + exact`. Equality holds on the dense set `e > 0`, `Z > 0`, and
     extends by analyticity.
   - Any correct route is acceptable. A direct derivative computation with the planar result plus the rotation
     algebra may be cleaner in Lean: write `DΨ = R·DΦ + (DR)·Φ` and use `Rᵀ DR` skew.
   - If this item proves very long, finish items 1–4 first, commit, and split item 5 into its own module.

## Owned files

`KAM/Planetary/Spatial/Chart.lean` (facade) and `KAM/Planetary/Spatial/Chart/*.lean`. Do not edit
`Rotation46.lean` or LP-SP-MODEL files; if you need a change there, report it.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–5.

Expected size 2,000–5,000 lines; split into focused modules and commit after each item. Stop when done or
blocked; report exactly what remains.

## Handoff

`docs/tracks/LP/audits/LP-SP-CHART-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-CHART.md`,
then `touch .drafts/READY-LP-SP-CHART`.

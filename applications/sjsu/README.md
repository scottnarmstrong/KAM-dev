# SJSU18: planar secular Sun–Jupiter–Saturn–Uranus Hamiltonian (open dataset)

A machine-readable **degree-18 polynomial secular Hamiltonian** of the planar
Sun–Jupiter–Saturn–Uranus (SJSU) system in the secular Poincaré variables, regenerated from
the recipe of Sansottera, Locatelli and Giorgilli
([SLG13](https://doi.org/10.1016/j.matcom.2010.11.018), §§2–3;
[arXiv:1010.2609v1](https://arxiv.org/abs/1010.2609v1)) and used again by Giorgilli, Locatelli
and Sansottera ([GLS17](https://doi.org/10.1134/S156035471701004X), §2;
[arXiv:1702.04894v1](https://arxiv.org/abs/1702.04894v1)), together with its generator, the
averaged reference semi-major axes, and validation tables against the published numbers.

This directory is the project root of the SJSU application of KAM-dev (decision D51); the
future Lean certificate package will live here too. **Nothing here is a Lean result.** The
model is a *reconstruction*: the authors' coefficient file was not available, and the
published description leaves several choices open. Every known difference from the
published numbers is listed below and in the report
[`docs/explorations/sjsu-model-recovery.md`](../../docs/explorations/sjsu-model-recovery.md).

| | |
|---|---|
| Dataset version | 0.1.0 (1 November 2026) |
| Size | 7,941 complex = 38,466 real coefficients (every invariant reversible monomial of degrees 2–18), 25 significant digits, 3.2 MB |
| Model file | [`data/sjsu18-o2.json`](data/sjsu18-o2.json) (see `data/MANIFEST.sha256`, `data/sjsu18-o2.SOURCE.txt`) |
| Data license | CC BY 4.0 ([`data/LICENSE`](data/LICENSE)); scripts Apache-2.0 (repository [LICENSE](../../LICENSE)) |
| How to cite | [`CITATION.cff`](CITATION.cff), and cite SLG13 and GLS17 |
| Status labels | *measured*: computed here; *literature*: stated in SLG13/GLS17; *estimated*: judgement |

## What the model is

`SJSU18-O2` is the secular Hamiltonian H^(sec)(ξ, η) obtained from the planar four-body
Hamiltonian in canonical heliocentric (Poincaré) variables by:

1. **Classical expansion** (SLG13 §2): translate the fast actions, L = Λ − Λ\*, keep the
   Kepler part to order L² and the perturbation (direct and indirect parts of all three pairs)
   to order L¹, to total degree 18 in (ξ, η) and trigonometric degree |k₁|+|k₂|+|k₃| ≤ 16
   (Table 1 elements read as Poincaré elements).
2. **Two Kolmogorov-like steps** (SLG13 §3.1, eqs. (6)–(7)): χ₁ removes every harmonic
   0 < |k| ≤ 8 of the L-independent part up to degree 6; χ₂ removes the same harmonics of the
   L-linear part. H^(O2) = exp(L_χ₂) exp(L_χ₁) H^(T) is kept **strictly to order two in the
   masses** (all Lie-series terms of order ≤ 2; see "Differences" for why this matters).
3. **Average and set L = 0** (SLG13 eq. (9)), then the **resonant step** for 3λ₁ − 5λ₂ − 7λ₃
   (SLG13 eqs. (10)–(12)): χ_res of degree 9 and the μ⁴ terms of eq. (12), as printed
   (weight ½ on the whole resonant L-independent part).

Parameters:

* masses m_j = m₀/M_j, M_j = 1047.355, 3498.5, 22902.98, m₀ = 4π², G = 1 (AU, yr);
* reference semi-major axes a\*_j (hence Λ\*_j = β_j √(μ_j a\*_j)): **measured** here by
  SLG13's stated procedure, the time average of the Poincaré semi-major axes along the planar
  N-body flow from Table 1 (1 Myr; [`validation/astar.json`](validation/astar.json));
* frequencies n\* in the homological equations: the Kepler frequencies plus the first-order
  correction ⟨∂h/∂L⟩ at zero eccentricity — SLG13 eq. (5) separates "the term which is both
  linear in the actions and independent of all the other canonical variables". With this
  reading 2n₁\* − 5n₂\* agrees with the N-body great-inequality frequency to 1.4 %.

## Conventions

| Item | Convention |
|---|---|
| Units | AU, year, G = 1, m₀ = 4π² (SLG13 Table 1) |
| Planets | 1, 2, 3 = Jupiter, Saturn, Uranus (array index 0, 1, 2) |
| Poincaré variables | Λ_j = β_j √(μ_j a_j), β_j = m₀m_j/(m₀+m_j), μ_j = G(m₀+m_j); λ_j = M_j + ϖ_j; ξ_j = √(2Γ_j) cos ϖ_j, η_j = −√(2Γ_j) sin ϖ_j, Γ_j = Λ_j(1 − √(1 − e_j²)) (SLG13 eq. (2)) |
| Symplectic structure | coordinates (λ_j, η_j), momenta (Λ_j, ξ_j): {η_j, ξ_j} = 1, so dη/dt = ∂H/∂ξ, dξ/dt = −∂H/∂η |
| Complex form | z_j = (ξ_j − iη_j)/√2 = √Γ_j e^{iϖ_j}; {z_j, z̄_j} = −i; dz/dt = −i ∂H/∂z̄ |
| Real monomial order | (ξ_J, ξ_S, ξ_U, η_J, η_S, η_U) — the order of `scripts/sjsu/slg13_quartic.json` |
| Complex monomial order | (z_J, z̄_J, z_S, z̄_S, z_U, z̄_U) |
| Secular variables | the (ξ, η) *after* χ₁, χ₂, χ_res at L = 0; they differ from the osculating Poincaré (ξ, η) by O(μ) (see `scripts/initial_map.py`) |
| Symmetries (exact in the file) | rotation invariance (every complex monomial has equal z and z̄ degree), reversibility (c_PQ = c_QP, real form even in η), reality |

## Files

| Path | Content |
|---|---|
| `data/sjsu18-o2.json` | the model: metadata, conventions, truncations, parameters, precision, census, provenance; `complex_form.terms` = `[p_J, q_J, p_S, q_S, p_U, q_U, "coef"]` for c·z^p z̄^q; `real_form.terms` = `[a_J, a_S, a_U, b_J, b_S, b_U, "coef"]` for c·ξ^a η^b; `components_complex_form` (first order, χ₁ and χ₂ parts of order two, resonant μ⁴ part) |
| `data/MANIFEST.sha256`, `data/*.SOURCE.txt` | hashes; generator, commit and command of every data file |
| `validation/` | comparison tables: Appendix A (78 coefficients), frequencies, Table 2 and eq. (24), GLS17 eq. (37), a\* determination, order study, precision |
| `scripts/` | generators and validators (Python 3, numpy, mpmath); see below |

Large intermediates (the first-order Fourier–Taylor expansion, about 1.1 million complex
terms) are **not committed**; they are regenerated by `build_model.py --work DIR`, and their
hashes are recorded in `data/sjsu18-o2.SOURCE.txt`.

## How to regenerate

From the repository root. Heavy steps should run under a memory cap, for example
`systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 …`.

```sh
# 1. reference semi-major axes (about 10 CPU-min): writes the N-body averages
python3 -I applications/sjsu/scripts/nbody.py --years 1e6 --dt 0.5 --ic poincare --out nbody.json
# 2. the model (strict order two, degree 18; mpmath 40 digits, about 3 CPU-min, 1 GB)
python3 -I applications/sjsu/scripts/build_model.py --variant O2 --backend mp \
    --out applications/sjsu/data/sjsu18-o2.json --work ~/kam-data/sjsu/build-o2
python3 -I applications/sjsu/scripts/make_manifest.py
# 3. regression test (fast; add --full to recompute everything)
python3 -I applications/sjsu/scripts/test_regression.py
# 4. validation tables
python3 -I applications/sjsu/scripts/compare_appendix_a.py --astar A1 A2 A3 --csv out.csv
python3 -I applications/sjsu/scripts/initial_map.py --astar A1 A2 A3
python3 -I applications/sjsu/scripts/freq_check.py --model applications/sjsu/data/sjsu18-o2.json --initial table2
python3 -I applications/sjsu/scripts/validation_tables.py
python3 -I applications/sjsu/scripts/table2_analysis.py
python3 -I applications/sjsu/scripts/sensitivity.py
python3 -I applications/sjsu/scripts/precision_check.py
```

| Script | Role |
|---|---|
| `kepler_series.py` | exact rational Kepler series (r/a)e^{i(f−M)} in Poincaré variables (degree 18) |
| `laplace.py` | Laplace coefficients b_{1/2}^{(k)} and (α d/dα)ⁿ b, mpmath |
| `expansion.py` | first-order pair expansion (direct + indirect parts, L-derivatives) |
| `sparse.py` | sparse Fourier–Taylor series and Poisson brackets (vectorized, bounded memory) |
| `secular.py` | the secular model strictly at order two (+ resonant step), complex→real conversion |
| `lie_mimic.py` | the same Lie steps to any mass order N (used for the order study) |
| `nbody.py` | planar N-body integrator (Wisdom–Holman, democratic heliocentric, 4th order) |
| `fit_astar.py`, `compare_appendix_a.py` | comparisons and a\* fits against SLG13 Appendix A |
| `initial_map.py` | Table 1 → secular coordinates → Table 2 and eq. (24) |
| `freq_check.py` | frequency analysis of the secular flow from Table 2 (GLS17 eq. (37)) |
| `check_expansion.py` | harmonic-by-harmonic check of the expansion against an exact DFT |
| `build_model.py`, `make_manifest.py`, `test_regression.py` | the model file, its manifest and its regression test |
| `order_study.py`, `sensitivity.py`, `precision_check.py`, `validation_tables.py`, `table2_analysis.py` | validation tables in `validation/` |

## Validation and differences from the published model (summary)

Measured; details, tables and every source issue are in the
[report](../../docs/explorations/sjsu-model-recovery.md) and in `validation/`.

| Test | Result |
|---|---|
| First-order expansion vs exact DFT of the Hamiltonian (all pairs, values and ∂/∂Λ) | ≤ 3.4·10⁻¹⁹ of the mean |
| Secular quadratic part vs Laplace–Lagrange formula | ≤ 2.4·10⁻¹⁹ (long double); 2.3·10⁻⁴⁰ (mpmath) |
| SLG13 Appendix A, 12 quadratic coefficients | ≤ 7.7·10⁻⁴ (median 3.2·10⁻⁴) |
| SLG13 Appendix A, 66 quartic coefficients | J–S 5.5–8 %; J–U, S–U up to 19 %; three-planet terms absent (they need order ≥ 3) |
| Table 2 linear secular frequencies ν | 9.2·10⁻⁵, 5.8·10⁻⁴, 7.5·10⁻⁵ |
| GLS17 eq. (37) nonlinear frequencies, from the Table 2 data | 3.9 %, 0.48 %, 0.043 % (printed quartic alone: 11 %, 1.6 %, 0.22 %) |
| Regression test (`test_regression.py --full`) | all 7,941 coefficients recomputed to 4.7·10⁻²⁵ |

Why the printed coefficients are not reproduced exactly:

* **Higher-order terms.** The printed Appendix A contains terms of third order in the masses
  (its three-planet quartic coefficients appear only at order ≥ 3; at order 3 they agree to a
  median 2.9 %), although it is described as order two. SJSU18-O2 is strictly order two, the
  well-defined reading of the recipe. The order-3–5 values at degree 4 are in
  `validation/order_study_d4.csv`.
* **Undisclosed parameters.** a\*, the integration used to average it, the frequency vector of
  the homological equations, and the Lie-series truncation are not published. Our choices are
  stated above, and their effect is in `validation/sensitivity.json`. The degree ≥ 12
  coefficients depend strongly on the χ degree (6 versus 9: the source is inconsistent) and on
  n\*. The degree-18 coefficients are dominated by the resonant μ⁴ terms (κ·n\* = −9.8·10⁻⁴).
* **Source defects.** The printed quartic has a small component that breaks rotation invariance
  (charge ±4, about 10⁻⁸, `validation/appendixA_noninvariant.csv`); SJSU18-O2 is exactly
  invariant, so the AMD Σ z_j z̄_j is an exact first integral. Table 2 and eq. (24) are
  inconsistent with Table 1 and with each other (`validation/table2_analysis.json`).

**Use it as what it is:** an exactly specified, reproducible degree-18 polynomial in the SLG13
family, close to but not identical with the authors' model, and not the full secular dynamics.
Missing bodies, the planar restriction, the averaging and the truncations are modelling choices
of the source, not errors bounded here.

## Version history

* 0.1.0 (1 November 2026): first public reconstruction (strict order two in the masses).

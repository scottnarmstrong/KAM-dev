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
   masses** (all Lie-series terms of order ≤ 2). This is **our chosen truncation**: SLG13 and
   GLS17 expand the full Lie series within the polynomial truncations, and their printed
   numbers contain higher mass orders (see "Differences").
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
  reading 2n₁\* − 5n₂\* = −0.0070996 rad/yr agrees with the N-body great-inequality frequency
  (−0.0071145 rad/yr) to 0.21 %.

## Quickstart

Python standard library only (run from the repository root). Both forms give the same
Hamiltonian; the real form is exact when evaluated in rational arithmetic.

```python
import json
from fractions import Fraction

model = json.load(open('applications/sjsu/data/sjsu18-o2.json'))

def H_real(xi, eta):
    """SJSU18-O2 at (xi_J, xi_S, xi_U), (eta_J, eta_S, eta_U); exact if the inputs are Fractions."""
    v = (*xi, *eta)
    total = 0
    for *powers, coef in model['real_form']['terms']:
        term = Fraction(coef)
        for x, p in zip(v, powers):
            term *= x ** p
        total += term
    return total

def H_complex(z):
    """Same Hamiltonian from the complex form, z_j = (xi_j - i eta_j)/sqrt 2 (floating point)."""
    total = 0
    for pJ, qJ, pS, qS, pU, qU, coef in model['complex_form']['terms']:
        total += float(coef) * (z[0]**pJ * z[0].conjugate()**qJ * z[1]**pS * z[1].conjugate()**qS
                                * z[2]**pU * z[2].conjugate()**qU)
    return total.real

xi, eta = (0.034, -0.001, -0.010), (-0.009, -0.026, -0.002)
z = [complex(a, -b) / 2 ** 0.5 for a, b in zip(xi, eta)]
print(float(H_real([Fraction(x) for x in xi], [Fraction(e) for e in eta])), H_complex(z))
# -5.182958389258055e-08 -5.182958389258028e-08
```

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
| `data/sjsu18-o2.json` | the model: metadata, conventions, truncations, parameters, precision, census, sources (static, byte-reproducible; the build record is in `data/sjsu18-o2.SOURCE.txt`); `complex_form.terms` = `[p_J, q_J, p_S, q_S, p_U, q_U, "coef"]` for c·z^p z̄^q; `real_form.terms` = `[a_J, a_S, a_U, b_J, b_S, b_U, "coef"]` for c·ξ^a η^b; `components_complex_form` (first order, χ₁ and χ₂ parts of order two, resonant μ⁴ part) |
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
# 1. reference semi-major axes a* (about 10 + 1 CPU-min): two N-body runs, then
#    validation/astar.json (a* = the t = 1e6 checkpoint of aP_mean, copied as written)
python3 -I applications/sjsu/scripts/nbody.py --years 1e6 --dt 0.5 --ic poincare --out run1e6.json
python3 -I applications/sjsu/scripts/nbody.py --years 1e5 --dt 0.5 --ic poincare --out run1e5.json
python3 -I applications/sjsu/scripts/write_astar.py run1e6.json run1e5.json
# 2. the model (strict order two, degree 18; mpmath 40 digits, about 3.5 CPU-min, 1.7 GB peak RSS)
python3 -I applications/sjsu/scripts/build_model.py --variant O2 --backend mp \
    --out applications/sjsu/data/sjsu18-o2.json --work ~/kam-data/sjsu/build-o2-mp
python3 -I applications/sjsu/scripts/make_manifest.py
# 3. regression test (fast; add --full to recompute everything)
python3 -I applications/sjsu/scripts/test_regression.py
# 4. validation tables (A = the three values of "astar" in validation/astar.json)
A=$(python3 -I -c "import json; print(*json.load(open('applications/sjsu/validation/astar.json'))['astar'])")
python3 -I applications/sjsu/scripts/compare_appendix_a.py --astar $A --csv out.csv
python3 -I applications/sjsu/scripts/initial_map.py --astar $A --ic poincare --order 1 \
    --json applications/sjsu/validation/table2_map_poincare_order1.json
python3 -I applications/sjsu/scripts/freq_check.py --model applications/sjsu/data/sjsu18-o2.json \
    --table scripts/sjsu/slg13_quartic.json --initial table2 --sign-classes
python3 -I applications/sjsu/scripts/checks_log.py
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
| `write_astar.py` | writes `validation/astar.json` from the two N-body runs |
| `order_study.py`, `sensitivity.py`, `precision_check.py`, `validation_tables.py`, `table2_analysis.py`, `nbody_secular_freq.py`, `checks_log.py` | validation tables in `validation/` |

## Nominal initial point

The secular initial point used with this model is the SLG13 Table 1 data read as Poincaré
elements and mapped to the secular variables by the first-order Lie map of χ₁ and χ₂
(`scripts/initial_map.py --astar $A --ic poincare --order 1`, see "How to regenerate";
`validation/table2_map_poincare_order1.json`):

* (ξ_J, ξ_S, ξ_U) = (0.03446271128616895, −0.0014352339355918572, −0.010122263133599879),
* (η_J, η_S, η_U) = (−0.009080669615926963, −0.025602508346796338, −0.0016540224121661881),
* modal amplitudes R = (0.025264, 0.036570, 0.007567).

These amplitudes match the time-averaged modal amplitudes of the full planar N-body flow to
≤ 1 %. The initial data of SLG13 Table 2 do not: they are not used here (source issue SJSU-E2
in the report).

## Validation and differences from the published model (summary)

Measured; details, tables and every source issue are in the
[report](../../docs/explorations/sjsu-model-recovery.md) and in `validation/`.

| Test | Result |
|---|---|
| First-order expansion vs exact DFT of the Hamiltonian (all pairs, values and ∂/∂Λ) | ≤ 3.4·10⁻¹⁹ of the mean |
| Secular quadratic part (all six first-order coefficients) vs Laplace–Lagrange formula | ≤ 2.4·10⁻¹⁹ (long double); 2.3·10⁻⁴⁰ (mpmath) |
| SLG13 Appendix A, 12 quadratic coefficients | ≤ 7.7·10⁻⁴ (median 3.2·10⁻⁴) |
| SLG13 Appendix A, 66 quartic coefficients | J–S 5.5–8 %; J–U, S–U up to 19 %; three-planet terms nearly absent (≤ 20 % of the printed values; they need order ≥ 3) |
| Table 2 linear secular frequencies ν | 9.2·10⁻⁵, 5.8·10⁻⁴, 7.5·10⁻⁵ |
| GLS17 eq. (37) nonlinear frequencies, from the Table 2 data | ω₁ 2.3–3.9 %, ω₂ 0.30–0.50 %, ω₃ 0.04–0.08 % over the four eigenvector sign classes that Table 2 leaves open (printed quartic alone: ω₁ 10.9–11.4 %); sign rule in `scripts/freq_check.py` |
| Secular frequencies of the full planar N-body flow (3 Myr), from the mapped Table 1 point | 1.6 %, 0.35 %, 0.053 %; mean modal amplitudes ≤ 1 % |
| Regression test (`test_regression.py --full`) | all 7,941 coefficients recomputed to 4.7·10⁻²⁵ |
| Rebuild of the model file | byte-identical (the file holds no commit, path, version or timing; those are in `data/sjsu18-o2.SOURCE.txt`) |

Why the printed coefficients are not reproduced exactly:

* **Higher-order terms.** SLG13 and GLS17 expand the full Lie series and gather the terms by
  degree ("order two in the masses" names the approximation), so their printed Appendix A
  contains terms of third order in the masses: its three-planet quartic coefficients appear only
  at order ≥ 3, and at order 3 they agree to a median 2.9 %. SJSU18-O2 is kept strictly to order
  two: our chosen, explicitly defined truncation. The order-3–5 values at degree 4 are in
  `validation/order_study_d4.csv`.
* **Undisclosed parameters.** a\*, the integration used to average it, the frequency vector of
  the homological equations, and the Lie-series truncation are not published. Our choices are
  stated above, and their effect is in `validation/sensitivity.json`. The degree ≥ 12
  coefficients depend strongly on the χ degree (SLG13 says 9 in one place and 6 in its
  equations; GLS17 fixes 6, which we use) and on n\*. The degree-18 coefficients are dominated by the resonant μ⁴ terms (κ·n\* = −9.8·10⁻⁴).
* **Source defects.** The printed quartic has a small component that breaks rotation invariance
  (charge ±4, about 10⁻⁸, `validation/appendixA_noninvariant.csv`); SJSU18-O2 is exactly
  invariant, so the AMD Σ z_j z̄_j is an exact first integral. Table 2 and eq. (24) are
  inconsistent with Table 1 and with each other (`validation/table2_analysis.json`).

**Use it as what it is:** an exactly specified, reproducible degree-18 polynomial in the SLG13
family, close to but not identical with the authors' model, and not the full secular dynamics.
Missing bodies, the planar restriction, the averaging and the truncations are modelling choices
of the source, not errors bounded here.

## Version history

* 0.1.0 (1 November 2026): first public reconstruction (strict order two in the masses), with
  its nominal initial point.

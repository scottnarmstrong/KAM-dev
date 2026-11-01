# Validation tables for SJSU18 (CC BY 4.0)

The numbers quoted in `applications/sjsu/README.md` and in
`docs/explorations/sjsu-model-recovery.md` come from these files, from the model file itself
(census, components, parameters) or from the cited papers (marked *literature*). Values marked
"printed" are quoted from SLG13/GLS17 for comparison. Everything else is *measured* (this
project's computations).

| File | Content | Generator |
|---|---|---|
| `astar.json` | reference semi-major axes a\* (1 Myr N-body average), window dependence, measured mean motions | `nbody.py` runs, then `write_astar.py` |
| `nbody_readings.json` | N-body averages and mean motions for the two readings of Table 1 (Poincaré vs heliocentric elements) | `nbody.py` |
| `appendixA_comparison.csv` | the 78 printed coefficients vs SJSU18-O2 (with first-order, χ₁ and χ₂ parts), and the printed value's rotation-invariant projection | `validation_tables.py` |
| `appendixA_noninvariant.csv` | the non-invariant (charge ±4) complex monomials of the printed quartic (source issue SJSU-E1) | `validation_tables.py` |
| `order_study_d4.csv` | degree ≤ 4 coefficients when the Lie steps are kept to mass order N = 2…5 | `order_study.py` |
| `fits/fit_*_corrected.json` | least-squares fits of a\* to the printed quadratic / two-planet coefficients with the order-two model | `fit_astar.py` |
| `table2_map_*.json` | Table 1 → secular coordinates → modal (x, y); ν, R_j vs Table 2 and eq. (24) | `initial_map.py` |
| `table2_analysis.json` | invariants (AMD, Gram matrix, R_j) of Table 1, Table 2, eq. (24) (source issue SJSU-E2) | `table2_analysis.py` |
| `frequencies_*.json` | nonlinear secular frequencies of SJSU18-O2 and of the printed quartic from three initial points, vs GLS17 eq. (37) | `freq_check.py` |
| `frequencies_table2_sign_classes.json` | the same from the Table 2 data for the four inequivalent eigenvector sign classes | `freq_check.py --sign-classes` |
| `nbody_secular_frequencies.json` | secular frequencies of the full planar N-body flow (3 Myr, sampled every 50 yr), vs the model | `nbody_secular_freq.py` |
| `precision.json` | float64 / long double / mpmath-40 vs mpmath-50, maximal relative difference per degree | `precision_check.py` |
| `sensitivity.json` | change of the coefficients under the open recipe choices (χ degree, n\*, eq. (12) weight, a\* window) | `sensitivity.py` |
| `checks.json` | spot checks: Kepler-series error scaling, Laplace coefficients vs quadrature, order-tracked Lie engine (N = 2) vs `secular.py`, N-body step size | `checks_log.py` |
| `check_expansion.log` | harmonic-by-harmonic comparison of the first-order expansion with an exact DFT of the Hamiltonian | `check_expansion.py` |

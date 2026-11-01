# Validation tables for SJSU18 (CC BY 4.0)

Every number quoted in `applications/sjsu/README.md` and in
`docs/explorations/sjsu-model-recovery.md` comes from one of these files. All are *measured*
(this project's computations) unless a column says "printed" or "literature".

| File | Content | Generator |
|---|---|---|
| `astar.json` | reference semi-major axes a\* (1 Myr N-body average), window dependence, measured mean motions | `nbody.py` |
| `nbody_readings.json` | N-body averages and mean motions for the two readings of Table 1 (Poincaré vs heliocentric elements) | `nbody.py` |
| `appendixA_comparison.csv` | the 78 printed coefficients vs SJSU18-O2 (with first-order, χ₁ and χ₂ parts), and the printed value's rotation-invariant projection | `validation_tables.py` |
| `appendixA_noninvariant.csv` | the non-invariant (charge ±4) complex monomials of the printed quartic (source issue SJSU-E1) | `validation_tables.py` |
| `order_study_d4.csv` | degree ≤ 4 coefficients when the Lie steps are kept to mass order N = 2…5 | `order_study.py` |
| `fits/fit_*_corrected.json` | least-squares fits of a\* to the printed quadratic / two-planet coefficients with the order-two model | `fit_astar.py` |
| `table2_map_*.json` | Table 1 → secular coordinates → modal (x, y); ν, R_j vs Table 2 and eq. (24) | `initial_map.py` |
| `table2_analysis.json` | invariants (AMD, Gram matrix, R_j) of Table 1, Table 2, eq. (24) (source issue SJSU-E2) | `table2_analysis.py` |
| `frequencies_*.json` | nonlinear secular frequencies of SJSU18-O2 and of the printed quartic from three initial points, vs GLS17 eq. (37) | `freq_check.py` |
| `nbody_secular_frequencies.json` | secular frequencies of the full planar N-body flow (10 Myr), vs the model | `nbody_secular_freq.py` |
| `precision.json` | float64 / long double / mpmath-40 vs mpmath-50, maximal relative difference per degree | `precision_check.py` |
| `sensitivity.json` | change of the coefficients under the open recipe choices (χ degree, n\*, eq. (12) weight, a\* window) | `sensitivity.py` |

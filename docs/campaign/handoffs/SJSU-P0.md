# Handoff SJSU-P0: recovery of the degree-18 secular SJSU model

Branch `sjsu-p0` (from `origin/main` at `e3e05498`), local commits only, not pushed. Numerical
research and data production; **no Lean written or built.** Report:
[`docs/explorations/sjsu-model-recovery.md`](../../explorations/sjsu-model-recovery.md). Dataset
and pipeline: [`applications/sjsu/`](../../../applications/sjsu/README.md) (new project root,
per the owner's mid-task change; data CC BY 4.0, scripts Apache-2.0).

## Results in brief

- **SJSU18-O2 published**: `applications/sjsu/data/sjsu18-o2.json` (3.2 MB). It is the planar
  secular SJSU Hamiltonian, regenerated from SLG13 §§2–3 strictly at order two in the masses,
  with the resonant μ⁴ step of eq. (12). It has all 7,941 complex (38,466 real) invariant
  reversible monomials of degrees 2–18, written to 25 digits. mpmath 40 versus 50 digits:
  ≤ 7.4·10⁻³⁶. Regression test: all coefficients recomputed to 4.7·10⁻²⁵.
- **Validation (measured):** first-order expansion vs an exact DFT ≤ 3.4·10⁻¹⁹; Appendix A
  quadratic ≤ 7.7·10⁻⁴; Table 2 ν ≤ 5.8·10⁻⁴; GLS17 eq. (37) from the Table 2 data: 3.9 %,
  0.48 %, 0.043 % (the printed quartic alone: 11 %, 1.6 %, 0.22 %). Against the **full planar
  N-body flow** (3 Myr frequency analysis), the secular frequencies from the mapped Table 1
  point agree to 1.6 %, 0.35 %, 0.053 %, and the mean modal amplitudes to ≤ 1 %. Quartic: J–S 5.5–8 %; J–U
  and S–U up to 19 %; three-planet terms absent at order two.
- **Why not digit-exact:** the printed table contains **third-order** Lie terms. Its
  three-planet quartic is reproduced to a median 2.9 % at order 3, which beats the converged
  series (orders 4–5); the 5:2-dominated J–S quartic stays 3–7 % off at every order. a\*, the
  integration length, n\* and the Lie truncation are unpublished.
- **n\* interpretation:** SLG13 eq. (5)'s n\* includes ⟨∂f/∂L⟩ at zero eccentricity. That gives
  2n₁ − 5n₂ = −0.007099 against the N-body −0.007115, and 3n₁ − 5n₂ − 7n₃ = −0.000982 against
  −0.001002. Kepler n\* (−0.004374) inflates the J–S quartic by about 40 %.
- **a\*** by the stated procedure (1 Myr N-body average of the Poincaré axes):
  (5.202374655793598, 9.554443730484715, 19.21504720877541). Reading Table 1 as heliocentric
  osculating elements instead puts J–S at exact 5:2, so Table 1 is Poincaré.
- **SJSU-E1 resolved in kind:** the printed quartic carries a charge-±4 (rotation-breaking)
  component of 30 monomials up to 7.8·10⁻⁸, impossible for any d'Alembert-respecting
  computation. SJSU18-O2 is exactly invariant, so the AMD is an exact integral.
- **SJSU-E2 sharpened:** Table 2 is an orthogonal image of the raw Table 1 point (its AMD
  agrees to 3.8·10⁻¹⁴), but its modal amplitudes contradict the printed quadratic part by
  15–64 %, and the N-body amplitudes by 15–68 %; our Table 1 map matches the N-body to ≤ 1 %.
  Eq. (24) is a third set, with AMD 8.58·10⁻⁴. GLS17's ω₁ (from Table 2) is 10.6 % faster than
  the true N-body secular frequency.

## Files

New:
- `applications/sjsu/README.md`, `CITATION.cff`, `data/LICENSE` (CC BY 4.0),
  `data/sjsu18-o2.json`, `data/sjsu18-o2.SOURCE.txt`, `data/MANIFEST.sha256`.
- `applications/sjsu/scripts/`: `sjsu_common.py`, `kepler_series.py`, `laplace.py`,
  `expansion.py`, `sparse.py`, `secular.py`, `lie_mimic.py`, `nbody.py`, `fit_astar.py`,
  `compare_appendix_a.py`, `initial_map.py`, `freq_check.py`, `check_expansion.py`,
  `build_model.py`, `make_manifest.py`, `test_regression.py`, `order_study.py`,
  `sensitivity.py`, `precision_check.py`, `validation_tables.py`, `table2_analysis.py`,
  `nbody_secular_freq.py`.
- `applications/sjsu/validation/`: 18 small tables (index in its `README.md`).
- `docs/explorations/sjsu-model-recovery.md` and this handoff. Nobody was contacted.
- Outside the repository: `/home/scott/kam-tools/papers/slg13-sjsu-arxiv-1010.2609v1/` and
  `…/gls17-sjsu-arxiv-1702.04894v1/` (pdf, text, `SHA256SUMS`; the PDFs match the scoping
  pins), and regenerable runs under `~/kam-data/sjsu/` (N-body, fits, order study, builds,
  first-order expansion npz with hash in the SOURCE file).

Changed: `scripts/sjsu/README.md` (a pointer to the new root only; the prototype is
unchanged and `scripts/sjsu/validate.py` still passes). Nothing else outside my scope.

## Approach

Exact rational Kepler series and mpmath Laplace coefficients give the first-order pair
expansion (direct and indirect, with L-derivatives). A vectorized, bounded-memory sparse
Poisson-bracket engine computes SLG13's χ₁/χ₂ steps strictly at order two, plus the resonant
step. An order-tracked Lie series (any N) is used as an independent check and for the order
study. A Wisdom–Holman N-body integrator gives a\* and the mean motions. All comparisons
with the printed numbers are tests, never inputs.

## Checks and output

```text
$ python3 -I applications/sjsu/scripts/test_regression.py            # 1.5 s
PASS: data/MANIFEST.sha256: 3 files match
PASS: SJSU18-O2: all 7941 complex monomials charge-balanced
PASS: even degrees in [2, D]
PASS: reversibility: c_PQ = c_QP
PASS: real form (38466 terms) even in eta
PASS: components sum to the total (max rel 4.39e-22)
PASS: real form = expansion of complex form, degree <= 6 (max diff/scale 2.18e-20)
PASS: recomputed degree <= 4: max rel diff 5.21e-17 over 45 terms, 0 missing
PASS: Laplace-Lagrange off-diagonal secular coefficients (max rel 2.38e-19)
STATUS: all checks passed
$ python3 -I applications/sjsu/scripts/test_regression.py --full     # about 3 min
PASS: recomputed degree <= 18: max rel diff 4.65e-25 over 7941 terms, 0 missing
PASS: Laplace-Lagrange off-diagonal secular coefficients (max rel 2.32e-40)
STATUS: all checks passed
$ python3 -I applications/sjsu/scripts/check_expansion.py             # 31 s
worst relative harmonic discrepancy: 3.43e-19
$ python3 -I scripts/sjsu/validate.py                                  # prototype untouched
STATUS: numerical consistency checks only; no interval proof or Lean theorem.   (all PASS)
```

`scripts/lint_sources.sh`, run under `systemd-run … MemoryMax=8G`, gave **exit 1, partial**:
`check_lean_modules: PASS (4164 Lean files)`, the 25 frozen-anchor tests OK,
`FROZEN-ANCHOR GUARD OK`. The ABI step (`abi_hashes.py --check`) failed with
`unknown module prefix 'KAM'`: this worktree has no KAM build, and the step began fetching
the Lake dependencies into a new `.lake/` (196 MB of sources, no builds). I removed that
`.lake/`, which my run had created (every entry post-dated the run), to restore the worktree's
prior state. No Lean module was changed, so no targeted build and no `#print axioms`
apply. Heavy steps ran under `MemoryMax=8G`, on ≤ 2 cores; peak RSS about 1.7 GB.

## Uncertainties

- The printed coefficients are not reproduced to their digits, and cannot be without the
  authors' a\*, n\* and Lie truncation. The remaining J–S quartic gap (3–7 %) is unexplained.
- Degrees ≥ 12 depend strongly on choices the sources leave open (`validation/sensitivity.json`):
  the χ degree (6 versus 9), n\*, and at degree 18 the eq. (12) weight.
- The origin of Table 2 / eq. (24) remains unknown. GLS17's eq. (37) agrees with the Table 2
  point, while the true N-body flow agrees with our Table 1 map.
- A degree-18 model at order 3, which would be closer to the printed numbers, is estimated at
  4–5 CPU-h and 6–10 GB with the current producer (measured 27/78/221 s and 0.8/1.1/1.7 GB at
  degrees 6/8/10); not attempted.

## Suspected errata (for `docs/errata/ledger.json`) and deviations

| id | source, location | printed | claim | kind |
|---|---|---|---|---|
| SJSU-E1 | SLG13 Appendix A (journal p. 12; arXiv v1 identical) | quartic coefficients, e.g. η_S²η_U², ξ_S²η_U², ξ_Sξ_Uη_Sη_U | the polynomial has a charge-±4 component (30 complex monomials, ≤ 7.84·10⁻⁸; `validation/appendixA_noninvariant.csv`), forbidden by the d'Alembert rules at any order; it alone causes the nonzero AMD bracket | defect in printed data |
| SJSU-E2 | SLG13 Table 2 (p. 8) and eq. (24) (p. 11); GLS17 Table 2 | x_j(0), y_j(0); R_j "= √(x_j²(0)+y_j²(0))" | Table 2 preserves the raw Table 1 AMD to 3.8·10⁻¹⁴, but its modal amplitudes (0.02964, 0.03103, 0.01273) contradict Table 1 in the eigenbasis of the printed quadratic part (0.02501, 0.03630, 0.00775; with the first-order Lie correction 0.02526, 0.03657, 0.00757) and the time-averaged modal amplitudes of the full N-body flow (0.02551, 0.03668, 0.00759). Eq. (24) neither follows from its stated formula nor shares Table 2's AMD (8.58·10⁻⁴) | inconsistent data |
| SJSU-E3 | SLG13 §3.2, last paragraph (journal p. 7) | "we decided to calculate the generating functions χ₁ and χ₂ up to degree 9 (recall Eqs. (6) and (7))" | eqs. (6)–(7) sum j₂ ≤ 6, and GLS17 §2.2 says "up to degree 6"; the choice changes the coefficients of degree ≥ 12 by a median of 22–69 % | internal inconsistency |
| SJSU-E4 | SLG13 eq. (12) (p. 7); GLS17 eq. (12) | ½{χ₁^(res), Σ_{j₂≥0} h^(res)_{0,j₂}}_{ξ,η} | χ^(res) removes only degree 9 (eq. (11)); on the unremoved part the second-order Lie coefficient is 1, not ½ (affects degree 18 only) | possible imprecision |
| SJSU-E5 | SLG13 Appendix A title, §3.1; GLS17 §2.2 | "up to order 2 in the masses" | the printed three-planet quartic coefficients exist only at third order in the masses (reproduced at order 3, median 2.9 %), so the computed H^(O2) kept higher-order Lie terms | description inconsistent with data |
| (typo) | SLG13 p. 7 (three times) and arXiv v1; GLS17 p. 12 | "3λ₁ − 5λ₅ − 7λ₃" | should read 3λ₁ − 5λ₂ − 7λ₃ (index 5 does not exist) | typo (extends the inherited GLS17 entry) |

Deviations introduced (all stated in the dataset): strict order two; corrected n\*; our a\*;
Table 1 read as Poincaré elements; χ degree 6; eq. (12) as printed; the additive constant
dropped and reversibility/reality enforced exactly after a round-off check.

## Owner decisions

Recorded owner decisions (Scott, 1 November 2026, 15:50 UTC):

1. Phase 1 certifies **SJSU18-O2 as published** (strictly second order in the masses).
2. The nominal initial point of later phases is **our Table 1 map**: Table 1 read as Poincaré
   elements, then the first-order Lie map to the secular variables (report §5.3). Table 2's mismatch
   remains erratum candidate SJSU-E2.
3. `CITATION.cff`: Zohar Komargodski, Simons Center for Geometry and Physics, Stony Brook
   University; repository https://github.com/scottnarmstrong/KAM-dev.
4. The source authors are not contacted.

Applied in one commit: `CITATION.cff` updated, decision 4 applied, and the decisions recorded
in this handoff, the README and the report §10.

## Open items for the orchestrator

- Add a catalogue entry for the report in `docs/explorations/README.md` (outside my write
  scope), and record the errata above in `docs/errata/ledger.json`.

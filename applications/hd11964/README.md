# HD 11964: a planned certified no-crossing time (pilot, phases 1–2)

This directory is the project root of the HD 11964 application of KAM-dev (decision D51). It holds the pinned
inputs of a planar Newtonian model of the HD 11964 planetary system, the numerical gate of a planned Lean
certificate, the validation tables, and the opt-in Lean package `HD11964` (`lakefile.lean`, root
`HD11964.lean`; never part of the core build).

**There is no certificate yet.** Phase 1 is data, design and a sampled numerical gate. Phase 2, part A adds
Lean: the margin lemmas for HD 11964 (`HD11964.Threshold`: `B = Λ_c` on the action box, the data of LP-LIFT)
and the statement of no orbit crossing *given* the certificate's bounds on the region `R(d)`
(`HD11964.NoCrossing`, conditional); the general bridge is in the core (`KAM.Application.LambdaDrift`). The
bounds themselves (the cell checks) are phase 2, part B.
The design is [`docs/campaign/design/HD11964-PILOT.md`](../../docs/campaign/design/HD11964-PILOT.md); the
report is [`docs/explorations/hd11964-pilot.md`](../../docs/explorations/hd11964-pilot.md).

| | |
|---|---|
| Dataset version | 0.1.0 (1 November 2026) |
| Pinned inputs | [`data/hd11964-pilot.json`](data/hd11964-pilot.json), exact decimal rationals |
| Source extract | [`data/nasa-exoplanet-archive-ps-20261101.csv`](data/nasa-exoplanet-archive-ps-20261101.csv) (SHA-256 in the JSON) |
| Data license | CC BY 4.0 ([`data/LICENSE`](data/LICENSE)); scripts Apache-2.0 (repository [LICENSE](../../LICENSE)) |
| How to cite | [`CITATION.cff`](CITATION.cff), and Rosenthal et al. 2021 |
| Status labels | *proved*: a Lean theorem on main; *checked*: decided here in exact rationals, Lean pending; *measured*: computed here (floating point, sampled); *estimated*: judgement; *literature*: the catalogue |

## The system and the model

- **The system.** HD 11964 has two planets on wide orbits (period ratio 51.03):
  - c: P = 37.92 d, e = 0.106, m sin i = 24.3 M⊕;
  - b: P = 1935 d, e = 0.101, m sin i = 200.5 M⊕;
  - star: 1.151 M☉.
  Fit: Rosenthal et al. 2021, *ApJS* 255, 8 (California Legacy Survey), as tabulated by the NASA Exoplanet
  Archive on 1 November 2026.
- **The model.**
  - The frozen `KAM.Planetary.movingHamiltonian 1 1 ν μ` of track LP: heliocentric positions, rescaled
    barycentric momenta, `G = 1`, star mass 1.
  - Planet masses `μ ν_i` with `μ = m_b/M⋆` and `ν = (m_c/m_b, 1)`, exact rationals derived from the catalogue
    decimals.
  - Masses are **minimum masses**: the orbits are taken coplanar and seen edge-on (`sin i = 1`, no mutual
    inclination). Point masses; no tides, relativity or stellar radius.
- **Units.** Length AU; time unit `1 yr/(2π√(M⋆/M☉)) = 0.148326 yr`; axes from the periods by Kepler's third
  law with `G M⋆ = 1`.
- **Conventions.**
  - Planet index 0 = c (inner), 1 = b (outer). The chart is LP's Poincaré chart: `(λ, ξ; Λ, η)` per planet,
    `(ξ, η) = √(2Γ)(cos ϖ, sin ϖ)`.
  - RV conventions: `ω` is the stellar argument of periastron (the planet's is `ω + π`); `t_c` is the time of
    inferior conjunction (radvel).
  - Mean anomalies at the epoch BJD 2455500.0.

## What is (planned to be) claimed, and what is not

- **The planned theorem** (phase 2). Every solution of the model that starts with actions `Λ` in an explicit
  box, strong AMD `C ≤ 0.0100` and positive total angular momentum `L > 0` (prograde; bound Kepler orbits
  with nonzero positions) exists and is unique for `|t| ≤ T`, for **every** phase and perihelion
  orientation. On that interval the orbits keep LP0's perihelion and annulus separations, so they never cross.
  `T` is planned on the ladder 10³, 10⁶, 10⁹ yr. The gate closes 10³ and 10⁶ yr; 10⁹ yr is provisional, since
  the order-4 normal form it needs is not resolved in float64.
- **Not claimed.**
  - Anything about true masses or mutual inclination.
  - Anything about physical effects outside the model.
  - Anything about the observational uncertainty beyond the stated initial set: the eccentricity error bars
    are wider; see the design's owner questions.

## Files

| Path | Content |
|---|---|
| `data/hd11964-pilot.json` | pinned inputs: catalogue values with errors, constants, model and conventions |
| `data/nasa-exoplanet-archive-ps-20261101.csv` | the archive query (all HD 11964 rows; the Rosenthal rows are the pin) |
| `lakefile.lean`, `lean-toolchain`, `HD11964.lean` | the opt-in Lean package (requires the core `kam` by path) |
| `HD11964/Threshold.lean` | the masses, the action box `U`, `U ⊆ 𝒬`, `B = Λ_c` on `U` (monotone pair-threshold bound), `liftData` |
| `HD11964/NoCrossing.lean` | the region `R(d)`, its inclusion and rotation invariance, `noCrossing_of_regionBounds` (conditional on the certificate's bounds) |
| `scripts/hd11964_model.py` | the model in exact rationals and mpmath: nominal state, chart, AMD; `threshold_ok` (exact rational mirror of the planned Lean threshold check) |
| `scripts/jets.py` | truncated multivariate Taylor jets with grid-valued coefficients |
| `scripts/normal_form.py` | the chart and `f` in jet arithmetic, the fast-angle Lie normal form with slow variables, and the residual `{F_i, H}` against the exact gradient of the original Hamiltonian |
| `scripts/gate.py` | the gate sweep over the region `R(d)` (sampled centres × full fast-angle grids) |
| `scripts/checks.py` | convention self-checks: chart dictionary, symplecticity, rotation invariance, flow check against a direct N-body integration |
| `scripts/rigor.py` | the l1-versus-sup loss factors of the residuals (rigorous-design estimate) |
| `scripts/summarize.py` | the horizon ladder |
| `scripts/threshold.py` | runs `threshold_ok` on the baseline region (writes `threshold.json`) |
| `scripts/kscan.py` | the Fourier cutoff the normal form needs at the `e_c`-max corner (`kscan-N3-s1.0.json`) |
| `scripts/conv.py` | grid convergence of the order-3 and order-4 rates (`conv-N4-ec044.json`) |
| `scripts/hiprec.py` | the mass-scaling test, and the long-double rerun that did not finish in time (`hiprec-*.json`) |
| `scripts/census.py` | the census of jet products per cell, the input of the cost estimate (`product-census.json`) |
| `scripts/slow_radius.py` | analyticity radii of c's chart in the slow variables, the input of the cell count (`slow-radius.json`) |
| `scripts/prod2.py` | phase 2: the order-2 producer in the exact form of the Lean identity (float64): the five terms `T1..T5` and `F − Λ` on kamx-hd-layer's worst cell, the identity check against the exact-gradient rate, the phase-1 cross-check (`validation/prod2-cell-f64.json`) |
| `scripts/prod2_hp.py` | phase 2: the generators `χ₁`, `χ₂` at 2^-184 fixed point (exact sliced DFT), written as 2^-160 integers (gzipped JSON, `~/kam-data/hd11964/prod2/`, not in git); `load_box` expands them for the cell check |
| `scripts/cover2.py` | phase 2: the order-2 cover of `R(d)` modulo rotation (float64): per cell `a₁..a₅`, `η`, the `F − Λ` range, the 10³ yr margin; `--d=` sets `d` (`validation/cover2-order2-pass1.json`, `cover2-order2.json` at `d = 10⁻³`, `cover2-order2-d1.5e-3.json`, `cover2-order2-d2e-3.json`; raw records in `~/kam-data/hd11964/cover2/`) |
| `scripts/cover2_fit.py` | phase 2: the order-2 cover with b-cells fitted to `R(d)` (sectors carried by rotated boxes; `--kappa=` sets the effective-radius target, `--nmult=4` makes sector counts multiples of 4); the jets are rotated into each cell frame before the l1 bounds (`validation/cover2-fit-*.json`) |
| `scripts/cover2_plan_lean.py` | phase 2: the exact rational plan of a fitted cover for the Lean cover lemma (`CoverPlan`, checked in fractions; Lean source and `validation/cover2-plan-*.json`) |
| `scripts/cover2_inregion.py` | phase 2: the sampled `F − Λ` range on `R(d)` against the range over the whole cell boxes, on one `ξ_c` interval (`validation/cover2-inregion-d2e-3.json`) |
| `validation/` | `gate-N4.jsonl` (all samples), `ladder.json`, `rigor-N3.json`, `checks.json`, `threshold.json`, `kscan-N3-s1.0.json`, `conv-N4-ec044.json`, `hiprec-N4-s0.85-f1.0-352x64-nolong.json`, `product-census.json`, `slow-radius.json` |

## How to regenerate

From the repository root. Heavy runs go under the memory cap; numpy and mpmath only.

```sh
CAP="systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10"
python3 -I applications/hd11964/scripts/hd11964_model.py              # nominal state, geometry (seconds)
OMP_NUM_THREADS=1 python3 -I applications/hd11964/scripts/checks.py   # self-checks (about 5 min)
$CAP python3 -I applications/hd11964/scripts/gate.py --N 4 --procs 2 \
    --out applications/hd11964/validation/gate-N4.jsonl               # the sweep (2.6 CPU-h, <= 3 GB per process)
$CAP python3 -I applications/hd11964/scripts/rigor.py 3 0.0,0.5,0.85,1.0
python3 -I applications/hd11964/scripts/summarize.py 5 1.45            # the ladder
python3 -I applications/hd11964/scripts/threshold.py                   # exact-rational threshold check
$CAP python3 -I applications/hd11964/scripts/kscan.py 3 1.0 20,30,40,50,60,73,90,110,143
$CAP python3 -I applications/hd11964/scripts/conv.py 1.0 0.5 224x64,320x64,224x96
$CAP python3 -I applications/hd11964/scripts/hiprec.py 4 0.85 352 64 nolong 1.0471975511965976  # mass scaling, φ = π/3 (5 min)
$CAP python3 -I applications/hd11964/scripts/census.py                 # product census (minutes)
python3 -I applications/hd11964/scripts/slow_radius.py                 # slow radii (seconds)
$CAP python3 -I applications/hd11964/scripts/prod2.py applications/hd11964/validation/prod2-cell-f64.json   # 1 min
$CAP python3 -I applications/hd11964/scripts/prod2_hp.py --out=$HOME/kam-data/hd11964/prod2/generators-cell-ec06.json.gz --check
$CAP python3 -I applications/hd11964/scripts/cover2.py OUT.jsonl --procs=2 --hb=0.04 --d=2e-3   # the cover (43 min wall)
python3 -I applications/hd11964/scripts/cover2.py --summary OUT.jsonl SUMMARY.json --d=2e-3      # same --d
$CAP python3 -I applications/hd11964/scripts/cover2_fit.py OUT.jsonl --d=2e-3 --kappa=0.2 --procs=2  # fitted cells (22 min)
python3 -I applications/hd11964/scripts/cover2_fit.py --summary OUT.jsonl SUMMARY.json --d=2e-3 --kappa=0.2
$CAP python3 -I applications/hd11964/scripts/cover2_inregion.py OUT.jsonl --d=2e-3 --hb=0.04      # in-region range (9 min)
```

## Version history

- 0.1.0 (1 November 2026): pinned inputs, gate and validation tables (phase 1).
- Phase 2, part A (1 November 2026): the opt-in Lean package `HD11964` (margin lemmas, conditional
  no-crossing statement). The data and tables are unchanged (still 0.1.0).

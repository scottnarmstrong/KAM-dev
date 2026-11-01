# HD 11964: a planned certified no-crossing time (pilot, phase 1)

This directory is the project root of the HD 11964 application of KAM-dev (decision D51). It holds the pinned
inputs of a planar Newtonian model of the HD 11964 planetary system, the numerical gate of a planned Lean
certificate, and the validation tables. The future Lean package (`applications/hd11964/lakefile.lean`,
namespace `HD11964`) will live here too.

**Nothing here is a Lean result or a certificate yet.** Phase 1 is data, design and a sampled numerical gate.
The design is [`docs/campaign/design/HD11964-PILOT.md`](../../docs/campaign/design/HD11964-PILOT.md); the
report is [`docs/explorations/hd11964-pilot.md`](../../docs/explorations/hd11964-pilot.md).

| | |
|---|---|
| Dataset version | 0.1.0 (1 November 2026) |
| Pinned inputs | [`data/hd11964-pilot.json`](data/hd11964-pilot.json), exact decimal rationals |
| Source extract | [`data/nasa-exoplanet-archive-ps-20261101.csv`](data/nasa-exoplanet-archive-ps-20261101.csv) (SHA-256 in the JSON) |
| Data license | CC BY 4.0 ([`data/LICENSE`](data/LICENSE)); scripts Apache-2.0 (repository [LICENSE](../../LICENSE)) |
| How to cite | [`CITATION.cff`](CITATION.cff), and Rosenthal et al. 2021 |
| Status labels | *measured*: computed here (floating point, sampled); *estimated*: judgement; *literature*: the catalogue |

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
  box and strong AMD `C ≤ 0.0100` exists and is unique for `|t| ≤ T`, for **every** phase and perihelion
  orientation. On that interval the orbits keep LP0's perihelion and annulus separations, so they never cross.
  `T` is planned on the ladder 10³, 10⁶, 10⁹ yr.
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
| `scripts/hd11964_model.py` | the model in exact rationals and mpmath: nominal state, chart, AMD; `threshold_ok` (exact rational mirror of the planned Lean threshold check) |
| `scripts/jets.py` | truncated multivariate Taylor jets with grid-valued coefficients |
| `scripts/normal_form.py` | the chart and `f` in jet arithmetic, the fast-angle Lie normal form with slow variables, and the residual `{F_i, H}` against the exact gradient of the original Hamiltonian |
| `scripts/gate.py` | the gate sweep over the region `R(d)` (sampled centres × full fast-angle grids) |
| `scripts/checks.py` | convention self-checks: chart dictionary, symplecticity, rotation invariance, flow check against a direct N-body integration |
| `scripts/rigor.py` | the l1-versus-sup loss factors of the residuals (rigorous-design estimate) |
| `scripts/summarize.py` | the horizon ladder |
| `validation/` | `gate-N4.jsonl` (all samples), `ladder.json`, `rigor-N3.json`, `checks.json`, `threshold.json`, `product-census.json`, `slow-radius.json` |

## How to regenerate

From the repository root. Heavy runs go under the memory cap; numpy and mpmath only.

```sh
CAP="systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10"
python3 -I applications/hd11964/scripts/hd11964_model.py              # nominal state, geometry (seconds)
OMP_NUM_THREADS=1 python3 -I applications/hd11964/scripts/checks.py   # self-checks (about 5 min)
$CAP python3 -I applications/hd11964/scripts/gate.py --N 4 --procs 2 \
    --out applications/hd11964/validation/gate-N4.jsonl               # the sweep (about 2.5 h, <= 2 GB per process)
$CAP python3 -I applications/hd11964/scripts/rigor.py 3 0.0,0.5,0.85,1.0
python3 -I applications/hd11964/scripts/summarize.py 5 1.45            # the ladder
```

## Version history

- 0.1.0 (1 November 2026): pinned inputs, gate and validation tables (phase 1).

# HD11964-PILOT: data, design and numerical gate (phase 1 report)

Date: 1 November 2026. Branch `hd11964`. Design: [`docs/campaign/design/HD11964-PILOT.md`](../campaign/design/HD11964-PILOT.md).
Data and scripts: [`applications/hd11964/`](../../applications/hd11964/).

**Status labels.**
- *proved*: a Lean theorem on main.
- *checked*: decided in exact rational arithmetic here, mirroring a planned Lean Bool check.
- *measured*: computed here in floating point at sampled points; a sampled supremum is a lower estimate of the
  true supremum.
- *estimated*: a judgement or an extrapolation.
- *literature*: the catalogue.

Nothing here is a certificate.

## 1. Verdict

**The gate passes for 10³ and 10⁶ yr, and for 10⁹ yr on the sampled supremum.** Margin 2 is required
throughout.

- **The route works as designed for HD 11964.**
  - The AMD barrier is the star threshold of planet c, `B = Λ_c`. It is certified by a one-line monotone bound
    (*checked*: pair threshold ≥ 0.792 against `Λ_c ≤ 0.0625` on the whole action box).
  - The margin `δ = 0.0483` leaves the helper's tube `r = 4.0·10⁻³`, ten times the certified drift needed.
- **Drift rates** (*measured*). A fast-angle Lie normal form with the slow variables (not frozen) brings
  `sup |{F_i, H}|` over the whole AMD ball (`e_c` up to 0.61) from 5·10⁻⁴ down by about 10³ per order. The
  rates are measured against the exact gradient of the original Newtonian Hamiltonian.
- **Ladder** (margin ≥ 2; `d = 10⁻³`; region `Γ_c + Γ_b ≤ 0.012`):

  | horizon | order needed (sampled sup) | order needed (×5 rigorous-design factor) |
  |---|---:|---:|
  | 10³ yr | 2 | 2 |
  | 10⁶ yr | 3 | 3 |
  | 10⁹ yr | 4 (margin ≈ 4.5) | 4 (margin ≈ 2.7) |

  The largest `T` that closes at margin 2 is ≈ 2·10¹⁰ yr at order 4 on the sampled sup, and ≈ 3·10⁹ yr with
  the rigorous-design factor.
- **What limits it.**
  1. **The order**, i.e. the kernel cost. Each order gains ≈ 10³ in `T` and costs ≈ 7× more products per cell.
  2. **The oscillation of `Λ_b` itself** (`F_b − Λ_b` ranges over 2.1·10⁻⁴). LP's Kepler split leaves the
     reduced-mass term `μ|p_b|²/2` in the perturbation. That caps the margin at `d/osc ≈ 4.8` for every `T`.
  3. **The high-`e_c` part of the AMD ball**: the rates are 3–5× those at the nominal eccentricities, and the
     Fourier cutoff grows to `K_c ≈ 90–140`.
- **Cost** (*estimated*, design §7).
  - 10³ yr: 70–300 CPU-h in the packed kernel engine;
  - 10⁶ yr: 500–2,000 CPU-h;
  - 10⁹ yr: 2.5–10·10³ CPU-h before pruning.
  - Without the packed layer only order 1 is practical: about 10² yr.

## 2. Data and model

Pinned in [`applications/hd11964/data/hd11964-pilot.json`](../../applications/hd11964/data/hd11964-pilot.json)
(*literature*). The source is the Rosenthal et al. 2021 rows of the NASA Exoplanet Archive (extract committed,
SHA-256 recorded); they agree with A7's §5 row to the digits shown there. The CDS catalogue J/ApJS/255/8 did not
answer on 1 November.

| quantity | value | label |
|---|---|---|
| `μ = m_b/M⋆` | 2005497248200/3833351025484041 ≈ 5.2317·10⁻⁴ | exact rational of the pins |
| `ν = (m_c/m_b, 1)` | (1217282799/10027486241, 1) ≈ (0.121395, 1) | exact rational |
| `a` (AU) | 0.231518, 3.185142 | *measured* (Kepler III with `G M⋆ = 1`) |
| `Λ̂`, `Γ̂` | (0.0584106, 1.7846965), (3.291·10⁻⁴, 9.126·10⁻³) | *measured* |
| `Ĉ = Σ Γ̂`, `C/B` | 9.4553·10⁻³, 0.1619 | *measured* (LP-QUANT: 0.163 at `M⋆ = 1.12`) |
| mean motions, ratio | 8.9769, 0.17592 per unit; 51.029 | *measured* |
| time unit | 0.148326 yr | exact formula |

The model is LP's frozen `movingHamiltonian 1 1 ν μ`, planar, with minimum masses. The README states what is and
is not claimed.

## 3. AMD geometry (*checked* in exact rationals: `validation/threshold.json`)

- **Initial set.** `Λ ∈ [Λ̂ − (10⁻⁴, 3·10⁻³), Λ̂ + (10⁻⁴, 3·10⁻³)]` (rational endpoints), `C ≤ Cbar = 1/100`, `L > 0`.
- **`U = box ± r`, with `r = 4/1000`:**
  - the chamber holds (`a_c ≤ 0.265 < 3.160 ≤ a_b`);
  - `Λ_b ≥ Λ_c`;
  - `v_min = 1 − 2a_c/a_b ≥ 0.832`;
  - `pairThreshold ≥ Λ_b D(v_min) ≥ 0.792 > 0.0625 ≥ Λ_c`.
  So `B = Λ_c` on `U` and `Ω_B(r) ≤ r`.
- **Margin and budget.** `δ = min Λ_c − Cbar = 0.04831`. The budget `3r ≤ δ/4` holds (`r ≤ 4.03·10⁻³`), and
  `2d ≤ r` holds with `d = 10⁻³`.
- **The certificate region.** `R(d)`: `Λ` in the box ± `d`, `Γ_c + Γ_b ≤ Cbar + 2d = 0.012`, every fast angle
  and perihelion. So `e_c ≤ 0.612` and `e_b ≤ 0.116`. The design (§3) explains why `d`, not `r`.
- **Per-planet budget** (LP-QUANT's flag). The margin `B − C = |L| − Λ_b` erodes only through `Λ_b`, and the
  helper's sup-norm budget is not binding here (design §5).

## 4. Method of the gate

**The normal form** (`scripts/normal_form.py`, `jets.py`).
- Every function is a truncated Taylor jet in the six local variables
  `(ΔΛ_c, ΔΛ_b, Δξ_c, Δη_c, Δξ_b, Δη_b)` to degree `N + 1`, with values on an `N_1 × N_2` grid of the two fast
  angles.
- The chart (LP's Poincaré chart, the Kepler equation solved by Newton in jet arithmetic) and the exact
  `f = |p_c + p_b|²/2 − ν_c/|q_c − q_b|` are evaluated in that arithmetic.
- A Lie series with one generator per order:
  - every mode of the 2/3-filter box is solved, with the divisors `k·ω(Λ)` of the actual actions, Taylor-expanded;
  - the brackets include the slow pairs `(ξ, η)`.
- `F^{(N)}_i = exp(L_{−χ_1})⋯exp(L_{−χ_N}) Λ_i`, truncated at order `μ^N`.

**What is measured.**
- The residual is `{F_i, H∘Ψ}` at the centre on the whole fast-angle grid.
- `∂F` comes from the series. `∂(H∘Ψ)` comes from the **exact** gradient of the original Hamiltonian:
  degree-1 automatic differentiation of the chart and of the Newtonian `f` in all eight chart directions.
- The residual therefore includes the unsolved Fourier tail, aliasing and every truncation.
- `F_i − Λ_i` is recorded on the same grid.

**Grids.**
- Inner angle: `K_c = ⌈40/σ(e_c)⌉`, with `σ(e) = ln((1+√(1−e²))/e) − √(1−e²)` (the Kepler strip).
- Outer angle: `⌈40/min(σ(e_b), ln(1/α))⌉`, `α` the largest axis ratio. The pair harmonics in `λ_b` decay with
  the multipole order. A first rule that used `e_b` alone stalled order 4 at `e_b = 0`; it was caught and fixed.
- Grid sizes `3K + 3` rounded up: 64 × 64 at low `e` to 432 × 64 at `e_c = 0.61`.

**Sampling** (`scripts/gate.py`). 48 centres, each a full fast-angle grid:
- the AMD sphere `Γ_c + Γ_b = 0.012` at shares `s = Γ_c/0.012 ∈ {0, 0.15, 0.3, 0.5, 0.7, 0.85, 1}`, times 6
  relative perihelion angles;
- interior points at 0 and ½ of the AMD;
- the four corners of the action box at `s ∈ {0, 1}`;
- two centres on finer grids (tolerance 60).
`ϖ_b = 0` by rotation invariance (checked: the rates agree to 7·10⁻⁴ relative, `validation/checks.json`, which
is grid sampling).

**Self-checks** (`scripts/checks.py`, `validation/checks.json`).
- The chart reproduces `keplerAction`, the strong AMD and the prograde sign to 10⁻⁴¹ (mpmath, 40 digits).
- The chart is symplectic for the pairs `(λ, Λ)`, `(ξ, η)` (error 6·10⁻²⁶).
- **Against the true flow.** Along a 20-year direct integration of the Newtonian equations (RK4 in Cartesian
  coordinates):

  | quantity | planet c | planet b |
  |---|---:|---:|
  | `Λ` moves | 1.9·10⁻⁵ | 1.9·10⁻⁴ |
  | `F⁽¹⁾` moves | 8·10⁻⁹ | 6.4·10⁻⁸ |
  | `F⁽²⁾` moves | 5.6·10⁻⁹ | 6.2·10⁻¹⁰ |

  `F⁽²⁾_c` sits at the integrator's error level. This confirms the signs and conventions end to end.

## 5. Results

### 5.1 Drift rate by order and by inner eccentricity (*measured*, worst over perihelion angles, `Λ = Λ̂`)

TABLE_BY_SHARE

### 5.2 The ladder

TABLE_LADDER

- `η_i` is the sampled sup of `|{F_i, H}|` over all 48 centres.
- `osc_i` is the range of `F_i − Λ_i` over all centres.
- The margin at `T` is `d / max_i (η_i T + osc_i)`; a rung closes when the margin is ≥ 2.
- The region needed is `R(10⁻³)` for every rung.
- The smallest `d` that would close each rung is in `validation/ladder.json`. With `d` smaller the region
  shrinks only slightly (`Cmax = Cbar + 2d`), so the rates hardly change.

### 5.3 Convergence and precision

CONVERGENCE

### 5.4 Rigorous-design estimate

A certificate replaces the sampled sup by a bound over each cell. Three factors separate the two.

1. **ℓ¹ against sup** (*measured*, `validation/rigor-N3.json`).
   - The cell check bounds the residual by the ℓ¹ norm of its Fourier coefficients. The identity of design §6.2
     sums all terms as exact models before the norm, so there is no product-of-norms loss.
   - At `s ∈ {0, 0.5, 0.85, 1}` the ratio ℓ¹/sup is 1.0–1.7 at every order.
   - The ℓ¹ bound on the range of `F − Λ` is within 1.45× of the sampled range.
2. **Sampling against sup.** Within each cell the sup can sit between samples (*estimated* 1.2–2×). The
   rates vary smoothly with the perihelion angle (≤ 1.3× over 6 angles), and the worst point is on the AMD
   sphere at `s ≥ 0.85`.
3. **Radii** (*estimated* 1.1–1.5×): the cell Taylor remainder at `h = 0.3R` (≤ 1 %), the Kepler, `sqrt` and
   `inv` witnesses, the rounding of the packed models, and the Fourier tails from strip bounds.

The product is 1.5–5. The ladder's second table uses ×5 on `η` and ×1.45 on the oscillation.

## 6. Comparison with LP-QUANT

- **Divergence check.** LP-QUANT's frozen-slow Newton steps at HD 11964 gave `2.7·10⁻⁴ → 1.5·10⁻⁷ → 5.3·10⁻¹⁴
  → 2.3·10⁻²⁷` (worst on its ball sphere, `K ≈ 73`, 3 steps). With the slow variables in the brackets and a
  plain Lie series:
  - the per-order gain is linear, ≈ 10³ ≈ `1/(2μ)` per order, not quadratic;
  - two orders give `3.5·10⁻¹⁰`, not `5·10⁻¹⁴`.
  This is LP-QUANT §5.5's caveat 1 (slow coupling) made quantitative. The order needed per rung is about one
  more than its "3 steps" suggests, for 10⁹ yr.
- **Cutoff.** At the `e_c = 0.61` corner the rates saturate at `K_c ≈ 40` (order 1), `≈ 73` (order 2) and
  `≈ 90` (order 3) (*measured*, `validation/kscan-N3-s1.0.json`). LP-QUANT's `K ≈ 73` is the order-2 cutoff.
- **Margin.** The AMD margin is not binding, as LP-QUANT found: the certified drift `≤ 5·10⁻⁴` uses an eighth
  of `r`.

## 7. Kernel engine and cost

Design §7 answers the orchestrator's addendum. In short:
- the packed Fourier models on main (`PEnc`, `jMul`/`reduceZ`, `packNorm`, the `inv`/`sqrt`/`exp` witnesses and
  the jet chain) evaluate every two-angle product, sum and bound of a cell;
- the new layer is Taylor × Fourier models over cells, an axis-ramp primitive for `∂_λ`, a Kepler witness, the
  Lie remainder identity and a cover modulo rotation;
- the census of products per cell (*measured*, unpruned) is 1.0·10³, 1.0·10⁴, 7.2·10⁴ and 3.8·10⁵ at orders
  1–4. The packed costs above follow from it.

## 8. Owner questions

1. **Neighbourhood size.**
   - Baseline: `Cbar = 0.0100` (nominal AMD + 6 %) and the 1σ period box.
   - The catalogue's 1σ eccentricities (`e_c ≤ 0.194`, `e_b ≤ 0.145`) give `C ≈ 0.020`. The region would then
     reach `e_c ≈ 0.76`, past the Laplace limit: longer tails and higher rates at every order (*estimated*
     3–10× per order).
   - Taken: the baseline.
2. **T target.** Taken: 10³ yr (order 2) as the first certificate; 10⁶ next; 10⁹ only after pruning is measured.
3. **Masses as m sin i against assumed inclinations.**
   - The theorem is exact for the stated (minimum) masses.
   - For a common inclination `i`, `μ → μ/sin i`. Each order's rate scales like `μ^{N+1}`, so `sin i = 0.5`
     multiplies the order-`N` rate by `2^{N+1}`: roughly one extra order for 10⁹ yr.
   - Spatial (mutually inclined) configurations need LP2's spatial lane and are not covered.
   - Taken: `m sin i`, coplanar.
4. **Where the headline is anchored** (application manifest or core manifest). Open; nothing is frozen.
5. **A weighted or signed LP helper.** Not needed for these rungs (design §5).

## 9. Errata, deviations, uncertainties

- **Errata in pinned sources:** none found. The archive's Rosenthal rows reproduce A7's §5 values.
- **Deviations from the brief.**
  - *Order and steps.* The brief's "K ≈ 73, 3 steps" was taken as the starting point. The gate runs a plain Lie
    series to order 4 with the slow variables, because frozen-slow Newton steps overstate the gain (§6).
  - *High precision.* The sweep is float64. The high-precision leg reruns sample centres in 80-bit long double
    with explicit DFTs and compares (§5.3); a 30-digit rerun was not done. The geometry and threshold checks
    are exact rationals and 40-digit mpmath.
  - *Region.* The certificate region is built on the certified drift `d`, not on the helper's `r` (design §3).
    This keeps `e_c ≤ 0.61`, below the Laplace limit.
  - *Addition:* the "Kernel engine" section (orchestrator addendum).
- **Uncertainties.**
  - Sampled sups are lower estimates. The ×5 rigorous-design factor is an estimate, of which 1.7 is measured.
  - The kernel costs are extrapolated from LG00's measured packed rates. Box sizes and precision differ, and
    production assembly is unmeasured. A measured cell is phase 2's first step.
  - The cell count (50–200) rests on root-test radii from degree-12 jets of one planet's chart.

## 10. Reproduce

See [`applications/hd11964/README.md`](../../applications/hd11964/README.md#how-to-regenerate). numpy and mpmath
only. Peak charge ≤ 2 GB per gate process (measured at 432 × 64, order 4).

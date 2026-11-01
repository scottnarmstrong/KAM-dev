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
- **Ladder** (margin ≥ 2; `d = 10⁻³`; region `Γ_c + Γ_b ≤ 0.012`; §5.2):

  | horizon | order needed, sampled sup (margin) | with the ×5 rigorous-design factor (margin) |
  |---|---:|---:|
  | 10³ yr | 2 (4.7) | 2 (3.3) |
  | 10⁶ yr | 3 (4.7) | 3 (3.2) |
  | 10⁹ yr | 4 (3.8) | 4 (≈ 3.2 on the extrapolated order-4 rate; 1.8 on the float64 floor, closed by `d = 1.5·10⁻³`) |

  The largest `T` that closes at margin 2:
  - order 2: 1.9·10⁵ yr;
  - order 3: 2.1·10⁸ yr;
  - order 4: ≥ 5.9·10⁹ yr on the sampled sup. Order 4 is float64-limited (§5.3); its measured values are upper
    estimates.
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

Centre actions `Λ = Λ̂`; on the AMD sphere `Γ_c + Γ_b = 0.012`, with `s = Γ_c/0.012`. Each entry is the worst over
the two planets and the six perihelion angles.

| s | e_c | e_b | grid | order 0 | order 1 | order 2 | order 3 | order 4 (upper estimate, §5.3) | range of F_b − Λ_b |
|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 0 | 0.000 | 0.116 | 64×80 | 1.0e-04 | 5.6e-08 | 3.8e-11 | 1.6e-14 | 9.9e-17 | 2.1e-04 |
| 0.15 | 0.246 | 0.107 | 128×80 | 1.4e-04 | 6.5e-08 | 4.5e-11 | 2.6e-14 | 3.7e-16 | 2.0e-04 |
| 0.3 | 0.346 | 0.097 | 160×64 | 1.9e-04 | 9.3e-08 | 5.9e-11 | 3.7e-14 | 6.6e-16 | 1.8e-04 |
| 0.5 | 0.441 | 0.082 | 224×64 | 2.6e-04 | 1.5e-07 | 1.1e-10 | 7.5e-14 | 1.9e-15 | 1.6e-04 |
| 0.7 | 0.517 | 0.063 | 288×64 | 3.5e-04 | 2.3e-07 | 1.8e-10 | 1.4e-13 | 1.5e-15 | 1.3e-04 |
| 0.85 | 0.565 | 0.045 | 352×64 | 4.3e-04 | 3.1e-07 | 2.6e-10 | 2.2e-13 | 2.2e-15 | 1.0e-04 |
| 0.85, fine | 0.565 | 0.045 | 528×96 | 4.3e-04 | 3.1e-07 | 2.5e-10 | 2.1e-13 | 7.0e-15 | 9.4e-05 |
| 1 | 0.607 | 0.000 | 432×64 | 5.1e-04 | 4.0e-07 | 3.5e-10 | 3.1e-13 | 6.7e-16 | 2.7e-05 |
| 1, fine | 0.607 | 0.000 | 640×96 | 5.1e-04 | 4.0e-07 | 3.5e-10 | 3.1e-13 | 1.9e-15 | 2.7e-05 |

- **The corners of the action box** change the rates by ≤ 5 %. The worst sampled point at orders 0–3 is the
  low-`Λ_c` corner at `s = 1` (`e_c = 0.612`): `5.4·10⁻⁴, 4.2·10⁻⁷, 3.7·10⁻¹⁰, 3.25·10⁻¹³`.
- **The interior** (half the AMD, or none) is lower everywhere. At circular orbits the rates are
  `7.3·10⁻⁵, 2.9·10⁻⁸, 1.8·10⁻¹¹, 4.2·10⁻¹⁵`.
- **Per order**, the gain is a factor 1,100–2,400, close to `1/(2μ) = 956` at high `e_c` and larger at low
  `e_c`.
- **The range of `F_b − Λ_b`** is the reduced-mass oscillation of LP's split. It grows with `e_b` and is
  largest at `s = 0` (`2.1·10⁻⁴`). The range of `F_c − Λ_c` is ≤ 3.5·10⁻⁵.

### 5.2 The ladder

Sampled sup over all 48 centres (*measured*). Region `R(10⁻³)`; margin `= d / max_i(η_i T + osc_i)`.

| order | η_c | η_b | osc_c | osc_b | largest T at margin 2 | 10³ yr | 10⁶ yr | 10⁹ yr |
|---:|---:|---:|---:|---:|---:|---|---|---|
| 0 | 5.35e-04 | 1.55e-04 | 0 | 0 | 0.14 yr | no | no | no |
| 1 | 4.20e-07 | 6.66e-08 | 3.45e-05 | 2.10e-04 | 1.6·10² yr | no (0.35) | no | no |
| 2 | 3.70e-10 | 7.41e-11 | 3.45e-05 | 2.10e-04 | 1.9·10⁵ yr | **yes (4.7)** | no (0.39) | no |
| 3 | 3.25e-13 | 9.80e-14 | 3.45e-05 | 2.10e-04 | 2.1·10⁸ yr | yes (4.8) | **yes (4.7)** | no (0.45) |
| 4 | ≤ 4.8e-15 | ≤ 7.3e-15 | 3.45e-05 | 2.10e-04 | ≥ 5.9·10⁹ yr | yes (4.8) | yes (4.8) | **yes (3.8)** |

The same with the rigorous-design factors of §5.4 (η × 5, osc × 1.45; *estimated*):

| order | largest T at margin 2 | 10³ yr | 10⁶ yr | 10⁹ yr |
|---:|---:|---|---|---|
| 1 | 32 yr | no | no | no |
| 2 | 3.6·10⁴ yr | **yes (3.3)** | no | no |
| 3 | 4.1·10⁷ yr | yes (3.3) | **yes (3.2)** | no |
| 4, floor values | 7.9·10⁸ yr | yes | yes | no (1.8) |
| 4, extrapolated true rate | ≈ 2·10¹⁰ yr | yes | yes | **yes (≈ 3.2)** |

**Order 4, read with §5.3.** Its sampled values are float64- and truncation-limited upper estimates, not
order-5 remainders. Extrapolating the measured per-order gain gives true order-4 rates near
`η_3 (η_3/η_2) ≈ 2.9·10⁻¹⁶` (c) and `1.3·10⁻¹⁶` (b). With them, 10⁹ yr closes with the ×5 factor at margin ≈ 3.2.
On the floor values alone it needs `d = 1.5·10⁻³`, which is still `≤ r/2`. That gives margin ≈ 2.7 on a region
with `Cmax = 0.013` and `e_c ≤ 0.635`, below the Laplace limit; the rates there are estimated ≤ 1.3× higher.

- `η_i` is the sampled sup of `|{F_i, H}|` over all 48 centres.
- `osc_i` is the range of `F_i − Λ_i` over all centres.
- The margin at `T` is `d / max_i (η_i T + osc_i)`; a rung closes when the margin is ≥ 2.
- The region needed is `R(10⁻³)` for every rung.
- The smallest `d` that would close each rung is in `validation/ladder.json`. With `d` smaller the region
  shrinks only slightly (`Cmax = Cbar + 2d`), so the rates hardly change.

### 5.3 Convergence and precision

- **Fourier cutoff** (`validation/kscan-N3-s1.0.json`, `e_c = 0.61`). Solving only `|k_c| ≤ K`, the rate
  saturates at `K ≈ 40` (order 1), `≈ 73` (order 2) and `≈ 90` (order 3). The sweep's grids (`K_c` = 144 there)
  are past saturation for orders ≤ 3.
- **Grid refinement** (fine centres, ×1.5 cutoffs). Orders 0–3 agree to ≤ 4 % at `s = 0.85` and to ≤ 0.3 %
  at `s = 1`.
- **Order 4 is not resolved by float64.** Three tests show it.
  1. At `e_c = 0.44`, `e_b = 0` (`validation/conv-N4-ec044.json`): raising the inner cutoff from 74 to 106 drops
     b's order-4 rate from 1.8·10⁻¹⁵ to 3.8·10⁻¹⁷. That is truncation at the coarse grid. c stays at
     2–3·10⁻¹⁶.
  2. At the fine centres (cutoffs 176–213) order 4 **rises** (2.2→7.0·10⁻¹⁵ at `s = 0.85`, 0.7→1.9·10⁻¹⁵ at
     `s = 1`), while order 3 agrees to 3 digits. Rounding in the highest modes, amplified by four nested
     spectral derivatives (about `(K/ω)⁴`), sets a floor of 10⁻¹⁵–10⁻¹⁴.
  3. **Mass scaling** (`validation/hiprec-N4-s0.85-…-nolong.json`). With `μ/2` the order-`N` residual must scale
     by `2^{N+1}`. Measured: 2.0, 4.0, 8.0, 15.8–16.0 for orders 0–3, i.e. genuine. Order 4 gives 2.0–2.9
     instead of 32: dominated by `∝ μ` terms, that is the floor and the unsolved tail.

  Hence orders 0–3 are reliable to a few per cent, and order 4 is an upper estimate. A certificate does not
  inherit this: its models carry ≥ 128-bit coefficients, and the tail term is bounded separately (design §6.2).
- **80-bit long double: did not complete.** `hiprec.py` reruns a centre with explicit long-double DFTs (numpy
  has no long-double FFT), which cost about 10³ times the float64 `rfft2`. The order-4 run at circular orbits on
  48 × 48 (`hiprec.py 4 0.0 48 48 long 0.0 0.0`) hit its 5,400 s limit. An order-3 run on 64 × 48 was stopped
  by hand: its float64 leg took 4.8 s. No long-double value exists, so the order-4 precision question rests on
  tests 1–3 above. The order 0–3 values, which set the 10³ and 10⁶ yr rungs, do not depend on it. The 10⁹ yr
  rung uses the order-4 upper estimate.

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
  - *High precision.* The sweep is float64. The high-precision leg is a mass-scaling test and grid refinement
    (§5.3). The 80-bit long-double rerun did not finish within its time limit, and a 30-digit rerun was not
    attempted. The geometry and threshold checks use exact rationals and 40-digit mpmath.
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
only. Peak RSS per gate process: 1.7 GB at 432 × 64 and about 3 GB at the fine 640 × 96 grids (order 4).

# SJSU-FULL go/no-go gates G1–G6 (research plan §4.3)

8 November 2026, branch `sjsu-full-gates` (off `main` at `8b8611000`). Research and measurement only: no KAM Lean,
nothing frozen. Scripts: [`scripts/sjsu/full/`](../../scripts/sjsu/full/). The large runs (G1, G3, G5, the G6
confirmation) ran on the owner's workstation (lam) through the package
[`scripts/sjsu/full/lam/`](../../scripts/sjsu/full/lam/): 305 jobs, 305 passed, no memory-cap kills, 28.1 CPU-h,
pool 14:41–20:24 UTC. Archive `sjsu-full-gates-results-20261108T202411Z.tar.zst` (sha256 `4d39bba5…79a6cb`),
checked by `verify_return.py`; verdicts from `analyze_gates.py`. Every number is **measured** (float64 unless
stated, sampled at the stated points); none is an enclosure. Labels as in
[`sjsu-full-research-plan.md`](sjsu-full-research-plan.md) §1.

## 0. Verdict table

| Gate | Literal criterion (§4.3) | Measured (57 points of the R4 tube) | Verdict | Failing term |
|---|---|---|---|---|
| G1 | F₁, Λ_U gains ≥ 20 per order at orders 3–5 at every point; order-3 rate ≤ 2·10⁻⁹ | gains at orders 3, 4, 5: F₁ min 45.5, 17.6, 15.8 (median 53.8, 50.5, 18.0); Λ_U min 15.1, 19.6, 16.8 (median 18.6, 22.9, 18.8). Order-3 rate ≤ 1.07·10⁻⁹ | **FAIL** | gains: Λ_U at order 3 (43 of 57 points), F₁ and Λ_U at order 5 (39 and 47 points); the rate clause passes |
| G2 | normalized divisors ≥ 3·10⁻³ at osculating Λ for the R4 orders; floor × 10⁴ yr ≤ 10⁻⁵ | min normalized divisor 4.13·10⁻³; floor × 10⁴: F₁ 6.4·10⁻⁶, Λ_U 9.7·10⁻⁶ | **PASS** (Λ_U floor at 97 % of the limit) | — |
| G3 | Stage-II gains ≥ 6 per order through order 4; ε₅₂ ≤ 0.15 over the tube | Λ_S gains at orders 1–4: min 11.2, 4.45, 5.18, 3.56 (median 12.5, 6.8, 7.1, 4.2); ε₅₂ ∈ [0.043, 0.108] | **FAIL** | order 4 at all 57 points (gain 3.6–5.0); also order 2 at 13 and order 3 at 18 points; ε₅₂ passes |
| G4 | R4 certificate ≤ 10⁸ coefficients after pruning | 1.0–3.0·10⁶ per cell (τ = 10⁻¹⁴) × 36–96 cells = 1.1–2.9·10⁸ | **FAIL** (marginal, ×1.1–2.9) | the cell count; ≤ 10⁸ only with ≤ 33 cells of radius 10⁻² |
| G5 | measurement: kernel/native ratio on one real-size product | 91 blocks: kernel 5,183 s; `native_decide` 39.6 s evaluation (246 s with its type checking); compiled 7.4 s. Ratios ×131 (×21), ×698; file wall ×7.9 | measured | kernel 58.8 s per real-size 2-D block (plan: 0.5–1 s) |
| G6 | H̄ at mass order 3: secular frequencies ≤ 10⁻⁴; torus inside δ/3 | g: −1.18 %, −0.63 %, −0.39 % (degree 10); mass order 4: −0.90 %, −0.61 %, −0.38 %; torus ≤ 2.2·10⁻⁶ < 3.3·10⁻⁶ | **FAIL** | frequencies, ×39–118 |

**In one sentence.** The gates do not support R4 as designed. The Stage-I ladder stalls near ×15–20 per order
from order 3 on. Stage II falls to ×4 per order by order 4. A mass-order-3 (or 4) H̄ misses the secular
frequencies by ~1 %. The R4 certificate is about 10⁸ coefficients. By the plan's own FAIL clause (G1), R4 drops to
10³–3·10³ yr and R5/R6 are abandoned. R3 (10³ yr) is untouched by G1/G3/G6, but G5 multiplies its kernel cost.

## 1. Method

### 1.1 The producer (`jets.py`, `model.py`, `nf.py`)

- **Model.** SLG13 eq. (1) in canonical heliocentric Poincaré variables, as `harmonics.py` of the research plan.
  Positions use the eccentric longitude F (λ = F − k sin F + h cos F), which is analytic in (ξ, η) at e = 0.
- **Slow variables as jets.** Every function is a truncated Taylor jet in the nine slow variables
  (ΔΛ_j, Δξ_j, Δη_j) at the sample point, on a grid of the three mean longitudes (pair-structured at grade 1, a
  3-D grid from grade 2). Derivatives are exact; the nested finite differences of E6 are gone.
- **Normal form.** Lie series exp(L_χ_N)…exp(L_χ_1) with the Kolmogorov-like split of E6 (h₀ = H_Kep(Λ) + DN·ΔΛ).
  The homological equation is solved with the exact divisors k·n(Λ), n = n_Kep(Λ) + DN, as jets in ΔΛ. Grade s
  is carried to jet degree N + 1 − s, so the order-r rate (the grade-(r+1) term plus the kept parts, E6's
  definition) is exact in the slow variables.
- **Kept set (Stage I, `keep52nr`).** k = 0, the 5:2 family m(2,−5,0), and every harmonic whose divisor can come
  within 3·10⁻³ of zero at osculating Λ: |k·n| − Σ_j |k_j| (3n_j/Λ_j) M_j < 3·10⁻³, with M = (1.95, 2.5, 0.38)·10⁻⁴
  (G2's measured maxima × 1.1). Gains are quoted on the normalized remainder; the kept near-resonant harmonics are
  quoted separately as the floor (G2).
- **Stage II (`stage2.py`).** The 5:2-family-and-secular part of the Stage-I normal form Z₁ + Z₂ + Z₃ (Stage I of
  order 3, the R4 order) is normalized in φ₅₂ with the same exact divisors; kept: k = 0 only.

### 1.2 Validation

- **E6 reproduced** (`validate_e6.py`, 128×128×64, E6's linear divisor): orders 0, 1, 2 agree with `order3.json`
  to ≤ 1.0·10⁻¹⁴, ≤ 4.2·10⁻¹⁰ and ≤ 1.3·10⁻⁶ relative for (Λ_J, Λ_S, Λ_U, F₁). The order-2 residual is E6's
  finite-difference error.
- **E7 reproduced** (`stage2.py --proxy`): Λ_S rates 2.126·10⁻⁷ → 1.585·10⁻⁸ → 1.688·10⁻⁹ (E7: 2.13, 1.59,
  1.69); ε₅₂ = 0.0711.
- **Precision.** The order-5 ladder in float64 and in 80-bit extended precision (numpy `longdouble`, also in the
  FFTs) agree to ≤ 1.6·10⁻¹⁴ relative at every order (24×24×12 grid). Rounding is not a limitation, so float64 is
  used. **Deviation:** the gate asked for double-double or 128-bit; the jets remove the cancellation that motivated
  it, and the 80-bit comparison bounds the rounding effect.
- **Jets against finite differences** of the reference `pair_f`: first and second derivatives agree to the FD error
  (≤ 6·10⁻⁷).

### 1.3 Sample points: the R4 tube (`make_points.py`, `points.json`)

- 48 block means (ξ, η, Λ) of the 1-Gyr N-body run, every 24 blocks (106 kyr) over the first 5.1 Myr (≥ 9 cycles
  of the slowest secular mode);
- the 8 corners ΔΛ_j = ±5·10⁻⁵ (Λ''-windows of width 10⁻⁴) at the first block mean;
- the nominal point (Table-1 secular (ξ, η) at Λ\*, E6's point). In all 57 points.

## 2. G2 — frequency modulation (local, `g2_modulation.py`)

**Criterion.** PASS iff every normalized divisor stays ≥ 3·10⁻³ at osculating Λ for the R4 orders, and the floor
× 10⁴ yr ≤ 10⁻⁵.

**Osculating offsets.** First-order Λ − Λ' = ∂_λχ₁ at each point (128×128×64), scaled by the N-body/first-order
ratio at the nominal point (1.13, 1.21, 1.21; E9's N-body ranges 3.2, 4.0, 0.56·10⁻⁴). max |Λ_j − ⟨Λ_j⟩| over the
57 points: 1.77·10⁻⁴, 2.26·10⁻⁴, 3.42·10⁻⁵. **These exceed the plan's half-ranges** (1.6, 2.0, 0.28·10⁻⁴): the
offsets are not symmetric. The kept set of §1.1 is sized from the measured maxima × 1.1.

**Divisors.**
- Over every harmonic of the G1 box (|k_J| ≤ 32, |k_S| ≤ 32, |k_U| ≤ 16) that the normal form divides by:
  min_points min_k (|k·n| − Σ|k_j| A_j max|ΔΛ_j|) = **4.13·10⁻³** (point 27, k = (−3, 6, 4)) ≥ 3·10⁻³.
- The kept near-resonant set has 150–166 harmonics (75–83 ± pairs) per point.
- Named harmonics, over the 57 points (sampled minimum over the fast torus):

  | k | mean k·n over the points | min \|k·n\| at osculating Λ | status |
  |---|---|---|---|
  | (2,−5,0) | −8.2 … −6.1·10⁻³ | 2.0·10⁻³ | kept (5:2) |
  | (2,−6,3) | 2.1 … 5.8·10⁻³ | crosses 0 (7·10⁻¹¹) | kept |
  | (4,−11,3) | −6.1 … −0.25·10⁻³ | crosses 0 | kept |
  | (3,−5,−7) | −3.8 … +1.8·10⁻³ | crosses 0 | kept |
  | (6,−17,6) | −4.0 … +5.6·10⁻³ | crosses 0 | kept |
  | (1,0,−7) | 4.3 … 7.9·10⁻³ | 3.0·10⁻³ | kept at some window corners, normalized elsewhere |
  | (0,1,−3) | −12.0 … −10.2·10⁻³ | 9.4·10⁻³ | normalized |
  | (1,−4,4) | −26.0 … −22.7·10⁻³ | 2.0·10⁻² | normalized |

- The Λ''-window corners move the mean divisors by up to ±1.9·10⁻³ for (2,−6,3): at two corners it sits at
  1.0–1.6·10⁻³ from zero over the whole fast torus.

**Floor** (from the G1 ladders on lam: the kept near-resonant harmonics through order 3, sampled sup over the fast
torus, 64×64×32). Over the 57 points: F₁ 5.3·10⁻¹¹ … 6.4·10⁻¹⁰ per yr, Λ_U 7.9·10⁻¹¹ … 9.7·10⁻¹⁰ per yr. Times
10⁴ yr: 6.4·10⁻⁶ and 9.7·10⁻⁶ ≤ 10⁻⁵.

**Verdict: PASS**, with no margin on Λ_U (97 % of the limit). The kept set grew from the plan's "(2,−6,3) and
weaker" to 75–83 ± pairs, because the measured osculating swings are 10–20 % wider than the plan's half-ranges.

## 3. G6 — model gap (local and lam, `g6_model_gap.py`)

**Criterion.** PASS iff H̄ at mass order 3 gives the secular frequencies to ≤ 10⁻⁴ and places the torus inside δ/3
(δ = 10⁻⁵, the R4 tube).

**Method.** H̄ = the repository's SLG13 Lie steps kept to mass order N (`lie_mimic.lie_secular`, n\* corrected,
a\* of `validation/astar.json`), secular part to degree D in (z, z̄). Its secular flow (RK4, dt = 50 yr) starts at
the first N-body block mean and runs 10 Myr. Frequencies: Hann-windowed peak of the modal signals, the same
analysis applied to the N-body block means of the same 10 Myr (g_NB = 1.371988·10⁻⁴, 2.037893·10⁻⁵,
1.152688·10⁻⁵). Torus: modal actions I_j in SJSU18-O2's eigenbasis (as `torus_offset.py`), mean, min and max over
the window.

| Mass order N | Degree D | g₁ rel. | g₂ rel. | g₃ rel. | max \|ΔI\| (mean, min, max) | Freq. ≤ 10⁻⁴ | Torus ≤ 3.3·10⁻⁶ |
|---:|---:|---:|---:|---:|---:|---|---|
| 2 | 4 | −7.16 % | −1.69 % | −0.54 % | 1.35·10⁻⁵ | no | no |
| 3 | 4 | −6.88 % | −1.55 % | −0.52 % | 1.25·10⁻⁵ | no | no |
| 2 | 6 | −1.78 % | −0.76 % | −0.41 % | 3.4·10⁻⁶ | no | no |
| 2 | 8 | −1.91 % | −0.83 % | −0.41 % | 3.6·10⁻⁶ | no | no |
| 2 | 10 | −1.91 % | −0.83 % | −0.41 % | 3.6·10⁻⁶ | no | no |
| 3 | 8 | −1.20 % | −0.63 % | −0.39 % | 2.2·10⁻⁶ | no | yes |
| **3** | **10** | **−1.18 %** | **−0.63 %** | **−0.39 %** | **2.2·10⁻⁶** | **no** | **yes** |
| 4 | 6 | −0.89 % | −0.56 % | −0.39 % | 1.8·10⁻⁶ | no | yes |
| 4 | 8 | −0.90 % | −0.61 % | −0.38 % | 1.8·10⁻⁶ | no | yes |

(Degrees ≤ 8 at orders 2–3 ran locally; degree 10 and mass order 4 on lam, ≤ 76 min and ≤ 3.2 GB each.)

**Verdict: FAIL.** At mass order 3 (degree 10, converged in degree to ≤ 2·10⁻⁴) the frequencies are off by
1.18·10⁻², 6.3·10⁻³ and 3.9·10⁻³: 118, 63 and 39 times the criterion. The torus clause passes
(2.2·10⁻⁶ ≤ 3.3·10⁻⁶).

**Reading.**
- Degree in (z, z̄) matters up to 6 (−7.2 % → −1.8 % in g₁) and is converged by 8–10.
- In the masses: g₁ moves −1.91 → −1.18 → −0.90 % from order 2 to 4, i.e. by 0.73 % and then 0.28 %. If the
  series kept that ratio (≈ 0.4), the limit would still sit near −0.7 %; g₃ does not move at all (−0.39 %). So the
  residual is not only mass order: these H̄ carry SLG13's truncations (|k| ≤ 16 in the perturbation, ≤ 8 per
  generator step, L-degree ≤ 1 in the perturbation), and the comparison starts the secular flow at the N-body block
  mean, not at mean variables (an O(μ²) offset). Which of these dominates is not decided here.
- Either way, the gate's question has a negative answer for this producer of H̄.

**Consequence.** A 1 % frequency error dephases the model torus from the true orbit at 0.012 g₁ ≈ 1.6·10⁻⁶ rad/yr:
0.016 rad over R4's 10⁴ yr (harmless, consistent with the torus clause passing), a full radian by 6·10⁵ yr. R4's
tube on a mass-order-3 H̄ is usable only as a location tube over ≲ 10⁴–10⁵ yr. Beyond that H̄ must be built without
the source truncations (an exact-f H̄, as the jets of §1.1 allow) and checked again.

## 4. G1 — resonant ladder (lam, `ladder.py`)

**Criterion.** PASS iff the F₁ and Λ_U gains at orders 3–5 are ≥ 20 per order at every sampled point, and the
order-3 rate is ≤ 2·10⁻⁹ per yr.

**Run.** keep52nr Stage-I normal form to order 5 at the 57 points, 64×64×32 grid, exact divisors (9.3 min and
≤ 19.6 GB per point). Gains are ratios of the normalized remainders; the order-3 rate is the full order-3 rate
(remainder plus the kept near-resonant floor).

Rates (per yr, SLG13 action units) and gains over the 57 points:

| Order | F₁ remainder (median; max) | gain min / median / max | Λ_U remainder (median; max) | gain min / median / max |
|---:|---|---|---|---|
| 0 | 1.98·10⁻⁴; 2.01·10⁻⁴ | — | 7.82·10⁻⁶; 7.95·10⁻⁶ | — |
| 1 | 1.22·10⁻⁶; 1.34·10⁻⁶ | 148 / 163 / 500 | 3.12·10⁻⁸; 6.27·10⁻⁸ | 127 / 249 / 575 |
| 2 | 2.92·10⁻⁸; 3.17·10⁻⁸ | 14.1 / 40.8 / 50.1 | 1.02·10⁻⁹; 2.28·10⁻⁹ | 25.2 / 30.6 / 46.2 |
| 3 | 5.26·10⁻¹⁰; 6.59·10⁻¹⁰ | **45.5** / 53.8 / 108 | 5.79·10⁻¹¹; 1.18·10⁻¹⁰ | **15.1** / 18.6 / 25.2 |
| 4 | 1.11·10⁻¹¹; 2.21·10⁻¹¹ | **17.6** / 50.5 / 75.2 | 2.64·10⁻¹²; 5.50·10⁻¹² | **19.6** / 22.9 / 29.1 |
| 5 | 6.11·10⁻¹³; 1.30·10⁻¹² | **15.8** / 18.0 / 53.1 | 1.37·10⁻¹³; 3.16·10⁻¹³ | **16.8** / 18.8 / 22.2 |

- Order-3 rate including the floor: max 1.04·10⁻⁹ (F₁) and 1.07·10⁻⁹ (Λ_U) ≤ 2·10⁻⁹. **This clause passes.**
- Failing terms (gain < 20): Λ_U at order 3 at 43 points, F₁ at order 5 at 39, Λ_U at order 5 at 47, F₁ and Λ_U
  at order 4 at 6 and 4. Only points 15, 23, 24, 25, 35 pass everything.
- The nominal point reproduces E6's orders 0–2 (F₁ 2.00·10⁻⁴, 1.30·10⁻⁶, 3.02·10⁻⁸; Λ_U 7.82·10⁻⁶, 3.26·10⁻⁸,
  1.05·10⁻⁹) and continues 6.24·10⁻¹⁰, 1.11·10⁻¹¹, 6.27·10⁻¹³ (F₁) and 6.56·10⁻¹¹, 2.76·10⁻¹², 1.56·10⁻¹³ (Λ_U).
- **Grid check** (nominal point and point 0 at 128×128×64, orders 0–4): the remainders agree with 64×64×32 to
  ≤ 1.4 % (Λ_U, order 4) and ≤ 0.7 % (F₁). The gains are not a grid artefact.

**Verdict: FAIL** on the gains (Λ_U at order 3, both at order 5); the rate clause passes.

**Reading.** The plan's extrapolation (gains ≈ 1/(εN), F₁ ≈ 10⁻⁹, 3·10⁻¹¹, 2·10⁻¹² at orders 3–5) was right at
order 3 for F₁ and optimistic beyond: measured median F₁ 5.3·10⁻¹⁰, 1.1·10⁻¹¹, 6.1·10⁻¹³. Λ_U gains ×19–23 from
order 2 on. The series behaves like an asymptotic series with a ratio ≈ 1/20 per order.

## 5. G3 — Stage-II ladder (lam, `stage2.py`)

**Criterion.** PASS iff the Stage-II gains are ≥ 6 per order through order 4 and ε₅₂ ≤ 0.15 over the tube.

**Run.** Stage I keep52nr to order 3 (the R4 order) with jets of degree 6; its 5:2-family-and-secular part
Z₁ + Z₂ + Z₃ is normalized in φ₅₂ to order 6; 48×48×24 grid, 57 points (14.7 min and ≤ 24.4 GB each).

| Stage-II order | Λ_S remainder, median (min … max) per yr | gain min / median / max |
|---:|---|---|
| 0 | 2.16·10⁻⁷ (1.28 … 3.23·10⁻⁷) | — |
| 1 | 1.70·10⁻⁸ (0.57 … 2.80·10⁻⁸) | 11.2 / 12.5 / 22.6 |
| 2 | 2.71·10⁻⁹ (1.28 … 3.87·10⁻⁹) | **4.45** / 6.77 / 7.26 |
| 3 | 3.80·10⁻¹⁰ (1.28 … 7.48·10⁻¹⁰) | **5.18** / 7.12 / 10.2 |
| 4 | 8.83·10⁻¹¹ (2.79 … 20.9·10⁻¹¹) | **3.56** / 4.21 / 5.01 |
| 5 | 1.75·10⁻¹¹ (0.42 … 5.01·10⁻¹¹) | 4.16 / 5.04 / 6.70 |
| 6 | 4.68·10⁻¹² (0.08 … 1.61·10⁻¹¹) | 3.11 / 3.74 / 5.04 |

- ε₅₂ over the 57 points: 0.043 … 0.108 ≤ 0.15. **This clause passes.**
- Failing terms (gain < 6): order 4 at all 57 points (Λ_S and Λ_J alike); order 2 at 13 points; order 3 at 18.
- Λ_J's ladder is Λ_S's divided by 2.5 (the 5:2 direction): same gains.
- **Grid check** (nominal point and point 0 at 64×64×32): the Stage-II remainders agree with 48×48×24 to ≤ 0.3 %.
- In Stage-I variables the gains are lower than E7's "great inequality alone" proxy (13.4, 9.4): the Stage-I
  terms Z₂, Z₃ add their own 5:2-family content.

**Verdict: FAIL** (order 4, everywhere).

## 6. G4 — support census (lam, `ladder.py --census`)

**Criterion.** PASS iff the R4 certificate is ≤ 10⁸ coefficients after pruning.

**Metric (my definition, stated so it can be challenged).** A coefficient is a jet coefficient c_{k,α} (complex,
counted once) of one certificate function. It is kept iff |c| ρ^α max(1, |k|₁) > τ, with ρ = 5·10⁻⁵ in Λ (the
window) and ρ_z in ξ, η (the cell radius): a bound on its contribution to a rate over a cell. Jets have total
degree ≤ 5, the grid is 64×64×32. R4's Stage-I functions are f, χ₁, χ₂, χ₃ (plus the much smaller remainder and
Stage-II generators, which live on the 5:2 family only).

Per cell, f + χ₁ + χ₂ + χ₃, at the nominal point and point 0:

| τ | ρ_z = 3·10⁻³ | ρ_z = 10⁻² | largest harmonic count per function |
|---|---:|---:|---:|
| 10⁻¹² | 1.4–1.5·10⁵ | 5.7–6.0·10⁵ | 3.6–5.1·10³ |
| **10⁻¹⁴** | **0.94–1.00·10⁶** | **2.85–3.01·10⁶** | 1.0–1.5·10⁴ |
| 10⁻¹⁶ | 4.1–4.4·10⁶ | 8.8–9.3·10⁶ | 2.2–3.2·10⁴ |

χ₂ dominates (45–52 %). The harmonic counts agree with E10's 10³–10⁴ per function at 10⁻¹²–10⁻¹⁴.

**Cells (estimate).** Modal radii |w_j| = √(2I_j) ≈ 0.025, 0.037, 0.0076, so circumferences 0.157, 0.231, 0.048.
Cells of diameter 2ρ_z = 0.02 need about 8, 12 and 3 per circle. Modulo rotation a 2-torus is left, i.e. 36–96
cells. At ρ_z = 3·10⁻³: 200–1,000 cells.

**R4 certificate at τ = 10⁻¹⁴:** 2.9·10⁶ × 36–96 ≈ 1.1–2.9·10⁸ (ρ_z = 10⁻²), or 0.2–1·10⁹ (ρ_z = 3·10⁻³).

**Verdict: FAIL, marginal** (×1.1–2.9). It passes only with ≤ 33 cells of radius 10⁻². That is the plan's own
10–50 range, but cells of radius 10⁻² need Taylor degree > 5 in z (|z| changes by 30–100 % across a cell for
Uranus), which raises the count. Two cheaper alternatives are not measured here: τ = 10⁻¹² (×5 fewer, if R4's
budget allows it) or a global Poisson series in (z, z̄) around z = 0.

## 7. G5 — kernel vs native shard (lam)

**Design.** One real-size pair-structured Fourier × Taylor product, f_JS × χ₁,JS at the nominal point, with:
- Taylor degree 2 in the six J–S slow variables, weighted as in G4 (ρ_z = 3·10⁻³);
- CertFixed 128 mantissas, pruned at 10⁻¹⁴.

That gives 91 2-D blocks (one per monomial pair):
- factors of 689–2,250 harmonics;
- products of up to 45,173 slots (12.2 Mbit); 3,585,607 product slots and 754,535 read-back terms in all.

Each block is checked by `gmpCheck`, a core-only mirror of the computational part of the landed `gmpRealProduct`
(guard, both boundary checks, one packed multiplication, advice-free rounding, read-back). The ℚ remainder is
omitted. The source is `scripts/sjsu/full/g5_sources.py`, which follows `KAM/CertificateSharp/Packed/Product.lean`
and its imports at `7cdc184ee`, unchanged on `main`. Every block is checked three ways:
- in the kernel (`decide +kernel`, one Lean file per block);
- with `native_decide` (one file per block; the mirror runs in the IR interpreter with the GMP runtime);
- by a compiled executable `g5check` on all blocks (best of three).

A mutated read-back term is rejected by the kernel (local smoke).

| Path | Total over 91 blocks | Per block (median / max) | Peak memory | Ratio to kernel |
|---|---:|---:|---:|---:|
| `decide +kernel` (type checking of the theorem) | 5,183 s | 58.8 s / 74 s | 8.9 GB | 1 |
| `native_decide`: evaluation only | 39.6 s | 0.4 s | 0.9 GB | ×131 |
| `native_decide`: evaluation + the file's other type checking | 246 s | 2.7 s | | ×21 |
| compiled executable (check only) | 7.43 s | 0.08 s | 0.1 GB | ×698 |
| whole Lean files (wall, incl. literal elaboration) | 5,707 s vs 724 s | 63 s vs 8 s | | ×7.9 |

**Reading.**
- The kernel costs 1.45 ms per product slot. The plan's "0.5–1 s per 2-D product" was for much smaller blocks: a
  real SJSU block at τ = 10⁻¹⁴ costs about 59 s, ×60–120 more.
- The native/kernel ratio depends on what is counted. Evaluation alone is ×131; with the type checking that a
  `native_decide` file still pays (the data literals) it is ×21, close to gate 2's measured ×24 end to end. The
  compiled checker is ×700.
- The whole-file wall ratio (×7.9) is dominated by elaborating the literal data, which a production certificate
  would also pay unless the data are packed (as `Packed/` does) or generated.
- All 91 blocks pass in all three paths: the mirror and the Python producer agree bit for bit.

## 8. Consequences for the rung table (§4.2)

| Rung | T | Gates | Verdict before | Verdict after the gates |
|---|---|---|---|---|
| R3 | 10³ yr | none of G1/G3/G6 needed (Stage I order 2, Stage II order 1, no secular model); G5 | go after G1–G5 | **go, re-cost first.** Kernel ≈ 59 s per real-size 2-D block product, not 0.5–1 s. The 10²–2·10³ kernel CPU-h estimate (§4.4) is ×60–120 low, unless R3's products are far smaller (τ = 10⁻¹², fewer slow monomials) or the native tier is accepted (÷21–700). |
| R4 | 10⁴ yr | G1 FAIL, G3 FAIL, G4 FAIL (marginal), G6 FAIL, G2 PASS | research program, go if G1–G3 pass | **no-go as designed.** By the plan's G1 clause: drops to 10³–3·10³ yr. |
| R5 | 10⁵ yr | G1, G3 FAIL; floor × 10⁵ = 6.4·10⁻⁵ / 9.7·10⁻⁵ > window 5·10⁻⁵ | stretch | **abandoned** (G1 clause) |
| R6 | 10⁶ yr | as R5, plus G6 (1 % frequency error dephases by 1 rad at 6·10⁵ yr) | research problem | **abandoned** |
| R9 | 10⁹ yr | — | no-go | no-go |

**What the measurements say about R4 beyond the literal verdict** (estimate, from the measured rates; not a
re-opening of the gate):
- *Fast windows.* The order-3 rate with the floor (≤ 1.07·10⁻⁹) × 10⁴ yr = 1.1·10⁻⁵ is within the window
  10⁻⁴/2 by ×4.7. Stage I at order 3 is enough for 10⁴ yr; the failing gains matter only for orders ≥ 4, i.e.
  R5/R6.
- *Secular budget.* The 5:2 forcing on the secular observables, 0.03 × 5.1·10⁻⁶ per yr, divided by the Stage-II
  gains through order 3 is:
  - 2.5·10⁻¹⁰ per yr at the median gains (12.5 · 6.8 · 7.1 ≈ 600);
  - 5.9·10⁻¹⁰ per yr at the worst point (11.2 · 4.45 · 5.18 ≈ 260).

  The budget δ/(2T) = 5·10⁻¹⁰ per yr (δ = 10⁻⁵) fits at the median with ×2, and fails at the worst points.
- *H̄.* G6's 1 % frequency error is tolerable over 10⁴ yr (0.016 rad), not beyond.
- *Size.* ~10⁸ coefficients, native only.

So a 10⁴-yr theorem is not excluded by the measurements. It would need re-designed gates: a tube of half-width
≥ 2·10⁻⁵ or Stage II of order 4, a location-only use of H̄, and a native certificate of ~10⁸ coefficients. As
gated, R4 does not go.

**Recommended next step.** Fix R3 (10³ yr) as the full-problem target and re-cost it with G5's per-slot kernel
figure before S2/S3. Decide the trust tier for R3 with the ×21–700 native factor in hand (owner decision 1).

## 9. Uncertainties, errata, deviations

**Uncertainties.**
- All rates are sampled sups (fast grids 64×64×32 and 48×48×24) at 57 points. Region sups are likely larger (HD:
  ×3–5). The verdicts that fail would fail more clearly; G2's Λ_U floor (97 % of its limit) could flip to FAIL.
- The osculating offsets of G2 are first order, scaled by one N-body ratio measured at the nominal point.
- G4's metric and cell count are my definitions and estimates, with jets truncated at degree 5.
- G6's H̄ carries the SLG13 source truncations and starts at block means, not mean variables. The 1 % gap may be
  partly truncation (§3).
- G5's native evaluation ran in the IR interpreter (no precompiled module). The compiled executable bounds the
  native tier from the other side.

**Suspected errata in pinned sources: none.**

**Repository notes (not pinned-source errata).**
- [`sjsu-full-research-plan.md`](sjsu-full-research-plan.md) §2.5/E9 quotes N-body ranges of Λ − Λ' (3.2, 4.0,
  0.56·10⁻⁴). The swings are asymmetric: max |Λ − ⟨Λ⟩| is 1.77, 2.26, 0.34·10⁻⁴, 10–22 % above half the ranges.
- §4.4's "kernel time per product 0.5–1 s for 2-D blocks" is superseded by G5: about 59 s per real-size block
  (1.45 ms per product slot).
- §4.3's G1/G3 extrapolations (gains 20–40 and 7.5–5.8 per order) are superseded by §§4–5 here.

**Deviations from the brief and the gate texts.**
- *Precision.* float64 instead of double-double or 128-bit, because the jets remove the cancellation. The 80-bit
  comparison agrees to 1.6·10⁻¹⁴ (§1.2).
- *Kept set.* The Stage-I kept set adds every near-resonant harmonic whose osculating divisor can fall below
  3·10⁻³ (sized from G2's measurements). G1's gains are on the normalized remainder; the kept harmonics are G2's
  floor and are included in G1's order-3 rate clause.
- *G3.* The Stage-II input is the Stage-I normal form of order 3 (R4's order), truncated at grade 3. G3 ran at
  48×48×24 (checked against 64×64×32 to ≤ 0.3 %).
- *G5.* It used a core-only mirror of the landed product (ℚ remainder omitted) rather than the library definition,
  so that a compiled executable was possible without building Mathlib. The local smoke used five short core-only
  `lean` runs (each < 1 s, < 600 MB), approved by kam-bb as one smoke test. The G5 Lean sources are kept as
  strings in `g5_sources.py`: the repository lint scans every `.lean` file, and these are not KAM modules (same
  precedent as `kernel-tests/Packed`'s generated probes).
- *G6.* It used the repository's SLG13-mimic H̄, not a new exact-f H̄.
- *Compute.* 28.1 CPU-h on lam plus about 1.5 CPU-h locally, against the plan's ≤ 10 CPU-h for all gates. The
  lam caps were 1.6–24× the measured peaks (recorded per job in the archive) for a future batch.
- *Sample set.* Not shrunk: 57 points throughout (48 orbit block means, 8 window corners, the nominal point).

## Appendix. Reproduction

From `scripts/sjsu/full/` (`nice -n 10`, Python 3 with numpy ≥ 1.26; G6 also mpmath):

```sh
python3 make_points.py MAIN_1E9.bin points.json                 # the 57 points (MAIN_1E9.bin: E2's 1-Gyr run)
python3 validate_e6.py 128,128,64 linear OUT.json                 # E6 check (E6_REF=.../order3.json)
python3 stage2.py points.json -1 OUT.json --grid 128,128,64 --M 2 --proxy   # E7 check
python3 g2_modulation.py points.json g2.json                      # G2 divisors (local, 6 s)
python3 g6_model_gap.py MAIN.bin g6.json --orders 3 --dfinal 8    # G6 (local, 2 min)
python3 ladder.py points.json I OUT.json --grid 64,64,32 --N 5 [--census]    # G1/G4, one point (lam)
python3 stage2.py points.json I OUT.json --grid 48,48,24 --NI 3 --M 6        # G3, one point (lam)
python3 g5_gen.py OUTDIR && python3 g5_sources.py OUTDIR          # G5 data + scratch Lake package
lam/make_package.sh MAIN_1E9.bin G5_REAL G5_TINY SMOKE_REF        # the lam package; lam/run.sh runs it
python3 analyze_gates.py RESULTS G2.json G6_DIR analysis.json     # verdicts
```

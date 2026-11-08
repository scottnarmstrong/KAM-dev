# SJSU-FULL go/no-go gates G1–G6 (research plan §4.3)

8 November 2026, branch `sjsu-full-gates` (off `main` at `8b8611000`). Research and measurement only: no KAM Lean,
nothing frozen. Scripts: [`scripts/sjsu/full/`](../../scripts/sjsu/full/). Large runs on the owner's workstation
(lam) through the package [`scripts/sjsu/full/lam/`](../../scripts/sjsu/full/lam/). Every number is **measured**
(float64 unless stated, sampled at the stated points); none is an enclosure. Labels as in
[`sjsu-full-research-plan.md`](sjsu-full-research-plan.md) §1.

STATUS: DRAFT — the lam sections (G1, G3, G4, G5, the G6 confirmation) are pending.

## 0. Verdict table

| Gate | Literal criterion (§4.3) | Measured | Verdict | Failing term |
|---|---|---|---|---|
| G1 | F₁, Λ_U gains ≥ 20 per order at orders 3–5 at every point; order-3 rate ≤ 2·10⁻⁹ | pending (lam) | pending | |
| G2 | normalized divisors ≥ 3·10⁻³ at osculating Λ for the R4 orders; floor × 10⁴ yr ≤ 10⁻⁵ | divisors ≥ 4.13·10⁻³ (by the kept set); floor pending | pending | |
| G3 | Stage-II gains ≥ 6 per order through order 4; ε₅₂ ≤ 0.15 over the tube | pending (lam) | pending | |
| G4 | R4 certificate ≤ 10⁸ coefficients after pruning | pending (lam) | pending | |
| G5 | (measurement) kernel/native ratio on one real-size product | pending (lam) | — | |
| G6 | H̄ at mass order 3: secular frequencies ≤ 10⁻⁴; torus inside δ/3 | g: −1.20 %, −0.63 %, −0.39 %; torus ≤ 2.2·10⁻⁶ < 3.3·10⁻⁶ | **FAIL** | frequencies, by ×39–120 |

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

**Floor.** pending (G1 lam ladders: kept near-resonant harmonics through order 3, F₁ and Λ_U).

## 3. G6 — model gap (local, `g6_model_gap.py`)

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
| **3** | **8** | **−1.20 %** | **−0.63 %** | **−0.39 %** | **2.2·10⁻⁶** | **no** | **yes** |
| 4 | 6, 8 | pending (lam) | | | | | |
| 2, 3 | 10 | pending (lam) | | | | | |

**Verdict: FAIL.** At mass order 3 the frequencies are off by 1.2·10⁻², 6.3·10⁻³ and 3.9·10⁻³, i.e. 120, 63 and
39 times the 10⁻⁴ criterion. The torus location passes (2.2·10⁻⁶ ≤ δ/3 = 3.3·10⁻⁶; the order-2 model does not).

**Reading.**
- Degree in (z, z̄) matters up to degree 6 (−7.2 % → −1.8 % in g₁) and has converged to ~10⁻³ by degree 8.
- Mass order 2 → 3 moves g₁ by 0.7 %. The series in the masses converges too slowly for 10⁻⁴ at order 3; the
  order-4 runs on lam test whether order 4 closes the gap.
- These H̄ carry SLG13's truncations (|k| ≤ 16 in the perturbation, ≤ 8 per generator step, L-degree ≤ 1). Part of
  the residual may be truncation rather than mass order; the gate's question (is a mass-order-3 H̄ good to 10⁻⁴?) is
  answered negatively for this H̄ either way.

**Consequence for the rungs.** R4's design (tube δ ≈ 10⁻⁵ on a certified H̄ at mass order 3, §4.2) cannot place
the tube's frequencies: a 1 % frequency error dephases the model torus from the true orbit by 2π within
~1/(0.012 g₁) ≈ 6·10⁵ yr. Over R4's 10⁴ yr the phase error is 0.016 rad, so the tube still covers the orbit if its
half-width absorbs the location error (the torus clause passes). Beyond 10⁵ yr H̄ must reach the true
frequencies (mass order ≥ 4–5 and degree ≥ 8, or a tube rebuilt on a fitted torus).

## 4. G1 — resonant ladder (lam)

pending.

Preview at coarse grids (local, not the gate): nominal point at 24×24×12 and point 0 at 32×32×16, F₁ gains
(orders 1–5) 159–164, 43–44, 51–55, 46–54, 17–22; Λ_U 242–272, 32–33, 15–18, 24, 19–20. Λ_U at order 3 and both
observables at order 5 sit at or below 20.

## 5. G3 — Stage-II ladder (lam)

pending. Coarse preview (point 0, 24×24×12): Λ_S Stage-II gains 14.0, 6.2, 8.2, 4.6, 5.5, 4.2 at orders 1–6.

## 6. G4 — support census (lam)

pending. Metric: number of jet coefficients (k, α) of f, χ₁…χ₃ and the order-3 remainder with
|c| ρ^α max(1, |k|₁) > τ, ρ = (5·10⁻⁵ in Λ, ρ_z in ξ, η), Taylor degree ≤ 5, times the plan's 10–50 cells.

## 7. G5 — kernel vs native shard (lam)

pending. Design: one real-size pair-structured Fourier × Taylor product f_JS × χ₁,JS at the nominal point (Taylor
degree 2 in the six J–S slow variables, weighted as in G4, CertFixed 128 mantissas, pruned at 10⁻¹⁴): 91 2-D
blocks, factors 689–2,250 harmonics, products up to 45,173 slots (12.2 Mbit). Each block is checked by a
core-only mirror of the computational part of the landed `gmpRealProduct` (`scripts/sjsu/full/g5/G5/Mirror.lean`;
the ℚ remainder omitted) in three ways: `decide +kernel`, `native_decide` (interpreted IR with GMP runtime), and a
compiled executable.

## 8. Consequences for the rung table (§4.2)

pending.

## 9. Uncertainties, errata, deviations

pending.

# SJSU-FULL research plan: long-time stability of the full planar Sun–Jupiter–Saturn–Uranus problem

8 November 2026, written against `main` at `cc725a791`. Research only: no Lean, no `lake build`, nothing frozen. The
experiments of §5 are float64/mpmath scratch computations under `nice -n 10` (each ≤ 30 CPU-min, ≤ 2 GB; total
about 1.5 CPU-h). Their scripts and JSON outputs are in the uncommitted `.drafts/sjsu-full-research/`; Appendix A
lists them so they can be rerun.

## 0. Summary

1. **Verdict.** "The full SJSU system is stable for 10⁹ yr" cannot be proved with methods in reach. Honest ladder: 10³ yr (kernel), 10⁴ yr (native, research program), 10⁵–10⁶ yr (stretch).
2. **The gap is proof technology, not physics.** Measured, 1 Gyr: no detectable chaos (T_L ≳ 10⁹ yr); secular frequencies drift by ≤ 2·10⁻⁷ relative; 100-Myr means of Λ_j stay constant to 7·10⁻¹⁰.
3. **Gate 2 does not transfer.** SJSU18-O2's torus has the right centre (mean modal actions within 3·10⁻⁷) but the wrong shape: the true orbit reaches 3.5·10⁻⁶ beyond it, past gate 2's face distance 2·10⁻⁶. Its g₁ is 1.6 % off.
4. **Fast averaging gains little per order here.** Measured: ×154 then ×43 per order on F₁ = 5Λ_J + 2Λ_S, ×236 then ×31 on Λ_U, with the 5:2 family kept unnormalized. HD 11964 gained ×10³ per order.
5. **The 5:2 great inequality.** Cosine amplitude 4.25·10⁻⁸, divisor −7.11·10⁻³ rad/yr, pendulum parameter ε = 0.071 (0.042–0.110 along the orbit). Averaging it with the fast terms gains only ×19, then ×3.6; averaging it alone gains ×13, then ×9.4.
6. **Frequency modulation.** Short-period swings of the osculating Λ move near-resonant divisors by about their own size: (2,−6,3) by ±3.7·10⁻³ against 4.0·10⁻³. Beyond about 10⁵ yr, generators must therefore live in mean variables, which needs a certified first-order canonical map.
7. **The AMD ball is too big for SJSU.** It contains 5:2-resonant states (ε up to 0.53) and states with e_U up to 0.22, where order-2 gains collapse to ×2–5. A pure AMD route (FULL-A2) stalls near 10³ yr whatever its budget; longer rungs need a secular tube, that is, FULL-B machinery.
8. **Recommended route: nested resonant averaging.** Stage I is a fast normal form keeping the 5:2 family. Stage II averages the great inequality. The secular tube uses gate-2-type observables built on a certified averaged Hamiltonian. All of it feeds one first exit, with exact L, through `hamiltonian_approxIntegrals_confinement`.
9. **Orders per rung (estimate; Stage I, Stage II).** 10³ yr: (2, 1) on a small secular box. 10⁴ yr: (3, 3), tube δ ≈ 10⁻⁵. 10⁵ yr: (4, 4). 10⁶ yr: (5–6, 5–6) plus an explicit Stage-I map. 10⁹ yr: (≥ 7–8, ≥ 10), beyond where the gains still improve.
10. **Rejected.** A KAM torus of the full problem: its 5-D Fourier certificate is ≫ X1's 55–140 GB, and it confines nothing. Analytic Nekhoroshev: mass thresholds of order 10⁻¹³. The energy trick for the 5:2 direction: it turns drift δ in F₁ into ΔΛ_S ≈ 75δ.
11. **Trust.** The 10³-yr rung fits kernel checking (est. 10²–2·10⁴ CPU-h). Every rung from 10⁴ yr up needs native checking (est. 10–10⁴ CPU-h each); that is an owner decision.
12. **First actions (≤ 10 CPU-h; G5 is one throwaway build, the rest Python).** G1: high-precision resonant rate ladder to order 5 over the tube. G2: frequency-modulation census. G3: Stage-II ladder in Stage-I variables. G4: support census. G5: one real-size 3-D product in kernel and in native.
13. **Owner decisions.** Trust level, planar, target rung, model of record and data, initial set, element convention, compute envelope, wording, and whether to fund the research producer (§6).
14. **Novelty.** No published rigorous result bounds the full SJS or SJSU problem over a stated horizon. A sealed 10³–10⁴-yr theorem would be a first.
15. **Gigayear statements stay with the secular model:** gate 2's 5·10⁹ yr theorem.

## 1. Scope, labels, what was done

**Labels.**

| Label | Meaning |
|---|---|
| **proved** | a compiled Lean theorem at the cited path |
| **literature** | a published claim, cited (author, year) |
| **measured** | computed in this task, float64 unless stated, sampled; a sampled supremum is a lower estimate of the true one |
| **estimate** | arithmetic or judgement; the method is stated next to it |

**Units.** SLG13 units throughout: AU, yr, G = 1, m₀ = 4π². Masses are m_j = m₀/(1047.355, 3498.5, 22902.98).
Actions are Λ_j = β_j√(μ_j a_j), with Λ\* = (0.53993, 0.21913, 0.047474). Energies and rates are in these units.

**Read.**
- [`sjsu-full-problem-scope.md`](sjsu-full-problem-scope.md), the scoping note this plan updates.
- [`sjsu-gate2.md`](sjsu-gate2.md), [`sjsu-near-torus-gate.md`](sjsu-near-torus-gate.md),
  [`sjs-rigor-plan.md`](sjs-rigor-plan.md), [the independent rigor review](sjsu-lean-rigor-astra.md),
  [`sjsu-model-recovery.md`](sjsu-model-recovery.md), [`sjsu-effective-stability.md`](sjsu-effective-stability.md).
- [`hd11964-pilot.md`](hd11964-pilot.md) and [`../campaign/design/HD11964-PILOT.md`](../campaign/design/HD11964-PILOT.md).
- `docs/results/{SJSU,HD11964,LP}.md`.
- The native branch `lemma/sjsu-native`: `numerical-certificate.lean` and `SJSUNumericalCertificate/BUILDING.txt`.

**Run.** Eleven experiments (§5):
- a C port of the repository's N-body map, validated against `applications/sjsu/scripts/nbody.py`;
- a 1-Gyr integration;
- tangent-map Lyapunov exponents;
- frequency-map analysis of the secular modes;
- a harmonic census of the full perturbation;
- order-0/1/2 Lie-series residual rates, at the nominal point and at six corners of the AMD sphere;
- a great-inequality-only ladder;
- a divisor-modulation census;
- a Fourier support census;
- the 5:2 strength over the AMD sphere.

## 2. The obstruction, decomposed (question 1)

### 2.1 Three time scales, and the size of everything (measured)

| Quantity | Value | Source |
|---|---|---|
| Mean motions n (rad/yr) | 0.52973, 0.21331, 0.074802 | N-body (`astar.json`) |
| Great inequality 2n_J − 5n_S | −7.1145·10⁻³ rad/yr (883 yr) | N-body |
| Secular frequencies g (rad/yr) | 1.371996·10⁻⁴, 2.037895·10⁻⁵, 1.152687·10⁻⁵ (45.8, 308, 545 kyr) | E4, 1 Gyr |
| Mean perturbation ⟨f⟩ | −5.31·10⁻⁵ | E5 |
| Largest short-period harmonic, (1,−1,0) J–S synodic | cosine amplitude 3.26·10⁻⁵, divisor 0.316 | E5 |
| 5:2 harmonic (2,−5,0) | 4.25·10⁻⁸, divisor −7.11·10⁻³ | E5 |
| Variation of the secular Hamiltonian over the AMD ball (C ≤ 1.2·10⁻³) | ≈ 1.2·10⁻⁷ | estimate, quadratic part |
| Three-body (2,−6,3), order 2 | 1.2–1.45·10⁻¹⁰, divisor 3.98·10⁻³ | E6 |
| Three-body (3,−5,−7), order 2 | 2.5–2.9·10⁻¹⁵, divisor −1.00·10⁻³ | E6 |
| Raw rates sup\|Λ̇_j\| | 6.2·10⁻⁵, 6.7·10⁻⁵, 7.8·10⁻⁶ per yr | E5; N-body gives 6.05, 6.45, 0.784·10⁻⁵ |
| Raw short-period rate of the secular variables, sup\|∇_{ξη} f̃\| | 5.5·10⁻⁴ per yr | E5 |
| Secular rate \|∇⟨f⟩\| | 2.8·10⁻⁶ per yr | E5 |

A secular observable confined to a tube of half-width δ = 10⁻⁶ for T = 10⁹ yr must drift by less than
δ/(2T) = 5·10⁻¹⁶ per yr. That is 10⁻¹² of the raw short-period rate and 2·10⁻¹⁰ of the genuine secular rate. A
fast action with window d = 10⁻⁴ over 10⁹ yr needs a rate of 5·10⁻¹⁴, about 10⁻⁹ of its raw rate. Every
obstruction below is a statement about how fast these ratios can be reached.

### 2.2 Gate 2 cannot be transported (measured; E2, E4)

- **The torus has the right centre but the wrong shape.** The 1-Gyr N-body run (block means over 4416 yr ≈ 5
  great-inequality periods) was projected on SJSU18-O2's eigenmodes (`torus_offset.json`).
  - The true modal actions range over [2.863, 3.391]·10⁻⁴, [6.466, 7.021]·10⁻⁴ and [2.443, 3.396]·10⁻⁵.
  - SJSU18-O2's own 4-Myr orbit spans [2.898, 3.370]·10⁻⁴, [6.489, 6.994]·10⁻⁴ and [2.497, 3.305]·10⁻⁵
    (`scripts/sjsu/gate2/results/orbit.json`).
  - The means agree to (−3.3, +1.8, +0.17)·10⁻⁷. The excursions differ: the true orbit oscillates 10–18 % wider,
    reaching (3.5, 2.3, 0.54)·10⁻⁶ below and (2.1, 2.7, 0.91)·10⁻⁶ above the model torus's extremes.
  - Gate 2's tube has F-half-width δ = 10⁻⁶ and face distance κδ = 2·10⁻⁶. **The true orbit leaves the model's
    tube**: pulled-back F_j fail within a fraction of a secular cycle (≲ 10⁴ yr), consistent with the scoping note's
    estimate of about 10³ yr (§2.5).
  - Beyond that, no horizon is possible without rebuilding the tube on the true torus.
- **The frequencies differ.** Model against 1-Gyr N-body: −1.57 %, −0.47 % and −0.05 %. The model-recovery report
  had −0.35 % for g₂ from a 3-Myr run; the 10-Myr windows here agree with each other to 4·10⁻⁷.
- **Osculating elements leave the bands.** The heliocentric osculating e_S ranges over [0.0073, 0.0899] in the
  N-body run. That is outside gate 2's band [0.009, 0.085], which is a band for the secular-model e, not for
  osculating elements. A full-problem band must absorb short-period terms and the model error.

### 2.3 Fast averaging: measured remainders and gains (E5, E6)

**Method.** Lie series exp(L_χ₂)exp(L_χ₁) of the full perturbation f(λ; Λ, ξ, η) at the nominal slow point.
- The physical divisors k·n(Λ) are used, with the first-order frequency correction moved into the unperturbed part
  (Kolmogorov-like split, as in SLG13).
- Every bracket is computed, slow (η, ξ) channel included.
- The rate of an order-N averaged action is the sup over the fast 3-torus of the λ-derivative of the unnormalized
  remainder.
- "keep52" leaves the 5:2 family m(2,−5,0) in the normal form. F₁ = 5Λ_J + 2Λ_S is orthogonal to it.

Rates in Λ units per yr:

| Variant | Observable | Order 0 | Order 1 | Order 2 | Gain 0→1 | Gain 1→2 |
|---|---|---:|---:|---:|---:|---:|
| keep52 | F₁ = 5Λ_J + 2Λ_S | 2.00·10⁻⁴ | 1.30·10⁻⁶ | 3.01·10⁻⁸ | 154 | 43 |
| keep52 | Λ_U | 7.82·10⁻⁶ | 3.32·10⁻⁸ | 1.08·10⁻⁹ | 236 | 31 |
| keep52 | Λ_S (kept 5:2 forcing dominates) | 6.67·10⁻⁵ | 4.98·10⁻⁷ | 2.24·10⁻⁷ | 134 | 2.2 |
| full | F₁ | 2.00·10⁻⁴ | 9.31·10⁻⁶ | 2.47·10⁻⁶ | 22 | 3.8 |
| full | Λ_S | 6.67·10⁻⁵ | 3.49·10⁻⁶ | 1.07·10⁻⁶ | 19 | 3.3 |

- **What limits keep52 at order 2 (measured, E6).** The term ⅓{{b, χ₁}, χ₁}, through the J–S synodic chain:
  harmonics (5,−5), (6,−6), (2,−2) and (7,−7), with amplitudes 1–3·10⁻¹⁰ and large divisors (0.6–2.2 rad/yr).
  - This is the near-conjunction structure of a compact pair (α = 0.545). It is not a small divisor.
  - **Estimate (interpretation):** the decline 154 → 43 is the factorial-type loss of an asymptotic series.
  - **Estimate:** the gains continue roughly as 1/(εN) with ε ≈ 10⁻². That gives F₁ ≈ 10⁻⁹, 3·10⁻¹¹, 2·10⁻¹² and
    10⁻¹³ at orders 3–6. G1 must measure it.
- **What limits "full" (measured).** The 5:2 generator's Λ-derivative scales as 1/ν₅₂² = 2·10⁴. Multiplied by
  the large short-period terms, it puts the cross terms {χ₅₂, f_sp} into every next order.
- **Secular direction (measured).**
  - sup|∇_{ξη}| of the oscillating remainder: 5.5·10⁻⁴ at order 0; 6.1·10⁻⁶ at order 1 with keep52; 9.2·10⁻⁵ at
    order 1 with full.
  - The kept 5:2 forcing on the secular variables is 5.1·10⁻⁶ per yr.
  - The order-2 secular correction |∇⟨K₂⟩| = 2.1·10⁻⁷ (keep52) is 7 % of the order-1 secular field; it is 22 % if
    the 5:2 is normalized too.
- **Scoping estimate superseded.** The scoping note's "gain 10²–10³ per order" was an estimate; it is replaced by
  the table above.

### 2.4 The 5:2 great inequality (E5, E7, E8)

- **Pendulum parameter.** ε = F·kᵀ|A|k/ν² with F the cosine amplitude, A = diag(−3n_j/Λ_j) and k = (2,−5,0).
  - In pendulum terms, the resonance half-width in frequency is 2√ε·|ν|.
  - **Measured at the nominal point:** ε = 0.071, so the half-width is 0.53 |ν|. The slow-channel analogue is 0.086.
  - **Along the true orbit** (block means, first 2 Myr): ε ∈ [0.042, 0.110], so the system stays outside the
    separatrix (threshold ε ≈ 1/4) by a factor 1.5–2.4 in frequency.
  - This agrees with Michtchenko–Ferraz-Mello (2001): J–S lies near the 5:2 chaotic zone.
- **Forced oscillation.** Semi-amplitudes of 1.2·10⁻⁵ in Λ_J and 3.0·10⁻⁵ in Λ_S. Rate amplitudes of 8.5·10⁻⁸
  and 2.1·10⁻⁷ per yr.
- **Averaging the 5:2 alone** (Stage II proxy, secular part plus the 5:2 family, E7):
  - Λ_S rates are 2.13·10⁻⁷ → 1.59·10⁻⁸ → 1.69·10⁻⁹, gains ×13.4 then ×9.4.
  - The (2,−5) harmonic goes 4.25·10⁻⁸ → 2.0·10⁻⁹ → 3.1·10⁻¹⁰.
  - The second harmonic (4,−10) is dominated by the second-order term {χ₅₂, f₅₂} (7.6·10⁻¹⁰ against the
    first-order 1.1·10⁻¹⁰).
- **Consequence.** Every rate the 5:2 touches must be divided by about 10 per order. That means individual Λ_J and
  Λ_S, and every secular observable through the 5.1·10⁻⁶ forcing. 10⁹ yr would need about 10–11 Stage-II orders
  (estimate, extrapolating the declining gains).

### 2.5 Frequency modulation of near-resonant divisors (E9)

- **Divisors at osculating actions.** The first-order Λ − Λ' (the generator's λ-derivative) has ranges 2.8·10⁻⁴,
  3.3·10⁻⁴ and 4.6·10⁻⁵ over the fast torus. The N-body gives 3.2·10⁻⁴, 4.0·10⁻⁴ and 5.6·10⁻⁵.
- **Shifts at the nominal point (measured):**

  | k | Mean k·n | Shift k·A·(Λ − Λ') | min \|divisor\| over the torus |
  |---|---:|---|---:|
  | (2,−5,0) | −7.11·10⁻³ | [−2.98, +3.37]·10⁻³ | 3.75·10⁻³ |
  | (2,−6,3) | +3.98·10⁻³ | [−3.63, +3.84]·10⁻³ | 3.5·10⁻⁴ |
  | (4,−11,3) | −3.14·10⁻³ | ±7·10⁻³ | crosses 0 |
  | (3,−5,−7) | −1.00·10⁻³ | ±4·10⁻³ | crosses 0 |
  | (6,−17,6) | +8.4·10⁻⁴ | ±1.1·10⁻² | crosses 0 |
  | (1,0,−7), (0,1,−3), (1,−4,4) | 6.1, −11.1, −24.3 (·10⁻³) | ≤ 2.5·10⁻³ | safe |

- **Why it matters.** HD 11964's design evaluates every generator at the actual state ("direct observables").
  - A near-resonant generator χ_k = K_k/(i k·n(Λ)) then sees its divisor oscillate by 50–100 % on the synodic
    time scale. For three of the harmonics above it vanishes inside the region.
  - In mean variables Λ' the divisors are steady: Λ' moves only at O(μ²).
- **Consequence.**
  - Up to about 10⁵ yr: leave these harmonics in the remainder. (2,−6,3) contributes 2.4·10⁻¹⁰ (F₁) and 3.6·10⁻¹⁰
    (Λ_U) per yr; (4,−11,3) adds about 1.6·10⁻¹²; (3,−5,−7) and (6,−17,6) stay ≤ 2·10⁻¹⁴.
  - Beyond that: (2,−6,3) must be normalized, in mean variables. That needs a certified first-order canonical map
    (Lie time-one map or flow, with inverse coverage), the "explicit Φ" the scoping note set aside.

### 2.6 The resonance web, the AMD ball and the region (E8)

**The AMD ball** {Σ Γ_j ≤ C_max}, the region of LP and HD 11964, is far larger than the set the true orbit visits.
- **Measured over 1 Gyr:** e_J ∈ [0.026, 0.062], e_S ∈ [0.0073, 0.090], e_U ∈ [0.0025, 0.067].
- **The AMD caps at C_max = 1.2·10⁻³:** 0.067, 0.105 and 0.224.
- **5:2 strength on the AMD sphere (E8):** with anti-aligned perihelia, ε passes the separatrix threshold 1/4 from
  e_S ≈ 0.057 (e_J ≈ 0.056) and reaches 0.53 near e_S ≈ 0.095; every state with e_S = 0.105 has ε = 0.44. Those
  states are inside the 5:2 resonance zone; the true orbit stays at ε ≤ 0.11.
- **Uranus-rich corners.** The order-2 normal form loses its gains there:

  | Slow point (C = 1.2·10⁻³) | e (J, S, U) | Order-2 rate, F₁ | Order-2 rate, Λ_U | Gain 1→2 (F₁, Λ_U) |
  |---|---|---:|---:|---|
  | nominal ×1.087 | 0.053, 0.059, 0.051 | 3.5·10⁻⁸ | 1.2·10⁻⁹ | 43, 30 |
  | all in J | 0.067, 0, 0 | 2.1·10⁻⁸ | 2.8·10⁻¹⁰ | 53, 39 |
  | all in S | 0, 0.105, 0 | 5.2·10⁻⁸ | 2.9·10⁻⁹ | 24, 14 |
  | J, S half, anti-aligned | 0.047, 0.074, 0 | 5.4·10⁻⁸ | 2.4·10⁻⁹ | 32, 13 |
  | S, U half, anti-aligned | 0, 0.074, 0.158 | 5.7·10⁻⁸ | 4.3·10⁻⁸ | 18, 5.0 |
  | all in U | 0, 0, 0.223 | 1.0·10⁻⁷ | 1.2·10⁻⁷ | 4.3, 2.0 |

- **Ceiling of the AMD-ball route (estimate).** With a window of 10⁻⁴ on Λ_U, the U-corner rate 1.2·10⁻⁷ caps the
  AMD-ball route at about 800 yr at order 2 (sampled; about 200–400 yr after the rigour factor).
- **Exact integrals do not exclude these corners.** Energy plus AMD still allow I₃ up to 6.4·10⁻⁴, i.e. e_U up to
  about 0.16 (estimate, quadratic part). The reason is that modes 2 and 3 have close frequencies (1.97 against
  1.11·10⁻⁵).
- **Conclusion.** FULL-A2 (AMD ball, 10⁶ yr) is not viable, whatever the compute budget. Beyond about 10³ yr the
  region must be a **secular tube** around the true torus. Only secular approximate integrals provide one.
- **Window width.** Inside the tube, the windows on the mean Λ' must still avoid the web: |Δν| ≲ 2·10⁻³ for
  (2,−6,3), whose ∂ν/∂Λ_S = 17.5 per action unit. So d ≲ 10⁻⁴ once (2,−6,3) is normalized.

### 2.7 The secular normal form at higher mass order

- **The model is order two.** SJSU18-O2 is strictly order two. The printed three-planet quartic terms need order 3
  ([`sjsu-model-recovery.md`](sjsu-model-recovery.md) §6.1).
- **The mass-order series converges slowly at first** (degree-4 order study,
  `applications/sjsu/validation/order_study_d4.csv`, re-read here). For the J–S quartic, successive relative changes
  are:
  - order 2→3: 1.1–2.8 %;
  - order 3→4: 0.2–0.8 %;
  - order 4→5: 0.013–0.016 %.

  For the quadratic part they are ≤ 3·10⁻⁴, ≤ 7·10⁻⁴ and ≤ 7·10⁻⁶. So the ratio per order is about 10⁻¹–10⁻² up to
  order 4 and about 2·10⁻² after; the 5:2 dominates orders 2–4.
- **Required mass order (estimate).** The angle-dependent secular error must stay below the tube budget divided by
  |∇F| ≈ 0.03. That means mass order 3 for 10⁴ yr, about 4–5 for 10⁵–10⁶ yr and ≥ 6 for 10⁹ yr.
- **Cost.** At degree 18 none of this exists even in floating point. The order-5 degree-4 study took 56 CPU-min.

### 2.8 Coupling: the drift budget of a secular observable (estimate)

For a near-torus observable F, with |∇_z F| ≈ 0.03, of the certified averaged Hamiltonian H̄:

  {F∘Φ⁻¹, H} = {F, H̄_secular} + {F, Stage-I residual} + {F, residual great inequality} + {F, H̄ − H̄_poly}.

- **First term.** The gate-2-type tube check. In the secular model it is about 10⁻¹⁹ per yr for δ ≤ 3·10⁻⁶.
  - Gate 2 measured T = 1.9·10⁶ yr at δ = 10⁻⁵ and 2.3·10¹¹ yr at δ = 3·10⁻⁶. The near-torus series stop converging
    near δ = 10⁻⁵, where κδ/B_U,min = 0.8.
  - So **the tube can be no wider than about 10⁻⁵**, and the budget is δ/(2T) ≤ 5·10⁻¹⁰/T per yr.
- **Second term.** About 0.03·r_N, with r₁ = 6.1·10⁻⁶ measured. Estimated r₂ ≈ 1.5·10⁻⁷, r₃ ≈ 5·10⁻⁹,
  r₄ ≈ 2·10⁻¹⁰, r₅ ≈ 10⁻¹¹, r₆ ≈ 6·10⁻¹³.
- **Third term.** About 0.03·5.1·10⁻⁶ divided by the product of the Stage-II gains (13.4, 9.4, then about 7.5,
  6.5, 5.8, …).
- **Fourth term.** The mass-order truncation of §2.7.

Matching the terms to the budget gives the orders of §4.2.

### 2.9 Spatial case, Neptune, other physics

- **Spatial, for the no-crossing part.**
  - The planar subspace is invariant, so a planar theorem is an honest theorem about the planar model.
  - In space, inclinations add about 4.5 % to the AMD (C/B goes from 0.17 to about 0.19; estimate in the scoping
    note §4.3).
  - LP's spatial lane exists (`KAM/Planetary/Spatial/`, LP2 sealed).
- **Spatial, for the certificate.**
  - Stage I gains 6 slow variables (12 local in all): about ×3–10 in products (estimate).
  - The secular part becomes 4 dof after SO(3) reduction, with nodal frequencies and mixed g–s secular resonances.
  - A gate-2-type tube in 4 secular dof (3 angles) is a new problem.
- **Neptune.** Not in SJSU: U–N near 2:1, and C/B rises to 0.35 (scoping note §4.4). The real outer Solar System
  needs SJSUN.
- **Relativity.** 1PN shifts the secular frequencies by about 0.15 %; irrelevant to FULL-A, a model choice for B.

### 2.10 What the true dynamics does (measured; E2–E4)

**Planar SJSU from Table 1, Poincaré reading, over 1 Gyr** (Wisdom–Holman map, order 4, dt = 1 yr):
- relative energy error 3·10⁻⁶;
- semi-major axes in [5.2011, 5.2047], [9.5125, 9.5922] and [19.103, 19.324] AU;
- minimum distances J–S 3.678 AU, J–U 12.58 AU, S–U 7.676 AU;
- AMD in [9.62·10⁻⁴, 1.094·10⁻³], so C/B ≤ 0.181.

**No drift is detectable:**
- The 1-Myr means of Λ_j vary by 4.8·10⁻⁸, 1.2·10⁻⁷ and 1.5·10⁻⁸; the 100-Myr means by ≤ 7·10⁻¹⁰.
- The secular frequencies in 100 windows of 10 Myr have relative scatter 4·10⁻⁶, 4·10⁻⁷ and 6·10⁻⁷. Their trend
  over 1 Gyr is 2·10⁻⁷, 2·10⁻⁸ and −2·10⁻⁸.

**Tangent-map Lyapunov (exact linearization of the same map by forward automatic differentiation).**
- The sum of log-growths follows ≈ 1.08 ln t up to 10⁹ yr, with residual ≤ 0.43, and ≈ 1.000 ln t at dt = 0.5 to
  2·10⁸ yr. That is linear tangent growth: regular motion.
- **Bounds:** λ ≤ 1.3·10⁻⁹ per yr, i.e. T_L ≳ 8·10⁸ yr (dt = 1 run) and ≳ 1.2·10⁹ yr (dt = 0.5).
- **Control.** A finite-difference shadow orbit in float64 reports T_L ≈ 2·10⁴ yr even with every planet mass
  scaled by 10⁻¹². Kepler shear amplifies the rounding noise. That artifact is archived in
  `artifact_shadow_lyap/`, so that nobody repeats it.

**Literature.**
- Murray–Holman (1999): chaos in the four giant planets from overlapping J–S–U three-body resonances, T_L ≈ 10 Myr.
- Hayes (2007, 2008): chaos or near-integrability depends on initial data within the ephemeris uncertainty; DE405
  gives T_L ≈ 200–400 Myr. Hayes also warns that WH steps above about 10 days can mislead.
- Guzzo (2005, 2006): a dense web of three-planet resonances, with the real system marginally inside it.

**This model, at this initial datum, is numerically regular.** No KAM-type obstruction stands in the way of
finite-time confinement. The obstruction is the order of the normal forms.

## 3. Candidate routes compared (question 2)

| Route | Theorem it yields | Horizon in reach (estimate) | Size / compute | New Lean | Main risk |
|---|---|---|---|---|---|
| (a) Fast averaging + secular confinement on the averaged system (FULL-B) | no crossing, a-windows, two-sided e-bands | 10³ yr (box); 10⁴ yr (tube, orders (3, 3)); 10⁹ needs (≥ 7–8, ≥ 10) plus secular mass order ≥ 6 | 10⁴ yr: native 10–10³ CPU-h; kernel 10³–10⁵ | N-generator identity, Poisson-series checker, tube on certified H̄ | gains decline; frequency modulation |
| (b) Resonant normal form keeping the 5:2 | ingredient of (a), (e), (f) | — | Stage I ×154/×43 instead of ×19/×3.6 | kept-part lemma (small) | 5:2 strength along the orbit up to ε = 0.11 |
| (c) KAM torus of the full problem | invariance of one 5-torus (reduced); confines nothing; near-torus Birkhoff gives exponential times in the distance | all time, on the torus only | 5-D Fourier support ≫ X1's 55–140 GB for planar SJS; FH (2024) SJS still not rigorous | v2 certifier in 5-D | infeasible near term |
| (d) Nekhoroshev with explicit constants | exponential stability | analytic constants: none at μ = 10⁻³ (thresholds about 10⁻¹³, Niederman 1996 via Barbieri–Niederman 2018) | — | — | constants useless; computer-assisted versions reduce to (a)/(f) |
| (e) AMD + fast-action drift on the AMD ball (FULL-A2, HD design) | no crossing, AMD e-caps, a-windows | ≈ 10² –10³ yr (measured corner rates, §2.6) | as FULL-A1 | A1-S helper | non-convergence in AMD corners, not cost |
| (f) Nested resonant averaging + secular tube + exact L (recommended) | as (a), from one first exit | 10³ (box), 10⁴, 10⁵, then 10⁶ with an explicit Stage-I map | §4.4 | §7 | per-order gains at orders 3–6 unmeasured |
| (f′) Energy trick for the 5:2 direction | no crossing without Stage II | **rejected:** ΔΛ_S ≈ 75δ₁ (§3.6) | — | — | needs F₁ windows of about 10⁻⁶ |
| (g) Validated ODE integration (Taylor models) | box enclosure of the true flow | ≤ 10³–10⁴ yr (wrapping, shear) | 10⁵ steps × 10⁴ interval operations | a validated integrator in Lean | no long-time future |

### 3.1 Route (a): fast averaging plus secular confinement (FULL-B)

**Theorem.** For every initial state in a ball (or a positive-measure tube cross-section), the Newtonian solution
exists on [−T, T]. Along it, semi-major axes and osculating eccentricities stay in explicit two-sided intervals and
the orbits stay separated.

**Mechanics.**
- Stage I is the resonant fast normal form; Stage II is great-inequality averaging; the secular part is a gate-2
  near-torus normal form of the certified averaged Hamiltonian H̄.
- One first exit uses the observables (F₁, Λ''_U, Λ''_S, F^sec_1..3), with L exact.

**Achievable T.**
- 10³ yr needs no secular normal form (box, scoping FULL-A1).
- 10⁴ yr needs orders (3, 3) and H̄ at mass order 3 with δ ≈ 10⁻⁵ (§2.8).
- 10⁹ yr needs (≥ 7–8, ≥ 10) with δ ≤ 3·10⁻⁶ and H̄ at mass order ≥ 6. The measured gains (Stage I 154 → 43,
  Stage II 13 → 9.4) are already falling, so the optimal order may come first.

**Risk.** A floating-point producer at these orders does not exist. SLG13 and GLS17 stop at order two.

### 3.2 Route (b): resonant normal form

Keeping the 5:2 family is not optional: it is the difference between ×154 and ×19 at order 1, and between ×43
and ×3.6 at order 2. Its Lean cost is one algebraic lemma: for b·k = 0 on the kept modes, (b·∂_λ) of the kept part
vanishes. The resonant secular model then has four angles (three secular plus φ₅₂), unless Stage II averages φ₅₂.
Averaging φ₅₂ is cheaper: one angle, and the circulation (ν = 7.1·10⁻³) is fifty times faster than g₁.

### 3.3 Route (c): KAM torus of the full problem

- **Why the target exists.** The orbit looks regular (§2.10), so a nearby KAM torus is plausible.
- **Why it is out of reach.**
  - The certificate is a 5-torus (planar, reduced) whose Fourier support is a product of fast pair supports
    (|k| ≲ 40–60) and secular supports (about 2,000 modes). That is at least 10⁷–10⁹ coefficients per component.
  - Figueras–Haro (2024) verified the KAM conditions for the planar SJS only numerically, and announce the rigorous
    phase as future work. X1 sized that SJS certificate at 55–140 GB of ledger ([`sjs-rigor-plan.md`](sjs-rigor-plan.md)).
  - Even proved, an n ≥ 3 torus confines nothing. B5's near-torus layer gives about 10² yr
    ([`sjs-rigor-plan.md`](sjs-rigor-plan.md) §2.3), and a near-torus Birkhoff layer would need route (a)'s
    machinery anyway.
- **Verdict:** not a route to a time bound.

### 3.4 Route (d): Nekhoroshev with explicit constants

- **Analytic constants.** LP1 and LP3 are sealed, but their constants are existential. Explicit analytic constants
  (Niederman 1996; sharpened by Barbieri–Niederman 2018) need planetary masses far below 10⁻³ for Solar-System
  times.
- **Computer-assisted Nekhoroshev** (Giorgilli–Locatelli–Sansottera 2009 for SJS, not rigorous; GLS17 for secular
  SJSU) is a finite-order normal form plus a remainder: routes (a) and (f).
- **No exponential needed.** Exponential estimates are not required for 10⁹ yr; the finite orders of §4.2 decide.

### 3.5 Route (e): AMD plus fast-action drift on the AMD ball

- **Strengths.** Cheap at short T. It is HD 11964's design, and the cleanest statement: all phases, all perihelion
  orientations, AMD ≤ C₀.
- **For SJSU it fails on the region (§2.6), not on cost.**
  - The AMD ball contains 5:2-resonant states (ε up to 0.53) and Uranus-rich states where order-2 gains are ×2–5.
  - Measured worst order-2 rates: 1.2·10⁻⁷ (Λ_U) and 1.0·10⁻⁷ (F₁) per yr. With windows of 10⁻⁴ that caps T near
    10³ yr.
- **Keep:** LP0's geometry and the sharpened helper A1-S. They turn any certified window into no crossing.

### 3.6 Route (f′): the energy trick, and why it is rejected

- **The idea.** Keep the 5:2 unnormalized and confine its direction p (Λ = Λ₀ + p(2,−5,0) + …) by exact energy
  conservation, since ν₅₂ ≠ 0 and Kepler energy is concave.
- **Measured inputs:** kᵀ|A|k = 84.6, and the secular energy varies by 1.2·10⁻⁷ over the AMD ball.
- **The bound.** It gives |p| ≤ (ΔZ + 0.106 δ₁ + 0.075 δ₂)/|ν₅₂|, with δ₁, δ₂ the windows of F₁ and Λ_U.
  Crossing the 5:2 resonance costs at most |p| ≤ 2|ν|/kᵀ|A|k = 1.7·10⁻⁴.
- **Why it fails.** The Kepler term amplifies F₁-drift into ΔΛ_S ≈ 75δ₁. The resonance-web window (ΔΛ_S ≲ 10⁻⁴)
  then needs δ₁ ≲ 10⁻⁶, i.e. two more Stage-I orders than Stage II costs.
- **What it is still good for:** a cross-check of the Stage-II rung, and a no-crossing argument (AMD tolerates
  ΔΛ ≈ 10⁻³) at rungs where the web is not normalized.

### 3.7 Route (g): validated numerical integration

Taylor-model integrators can enclose the N-body flow over about 10³ orbits; Berz–Makino-type solar-system
integrations are of that kind. Shear and wrapping grow at least linearly, and the Lean side would need a verified
integrator: about 10⁵ steps × 10⁴ interval operations, i.e. 10⁹ certified operations. That is native-only, and it
reaches no further than FULL-A1. Not recommended.

## 4. Recommendation and staged plan (question 3)

### 4.1 The route

**Nested resonant averaging with a secular tube and exact angular momentum**, in one first exit.

**Engine (proved).** `KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement`
(`KAM/Application/Confinement/ApproxIntegral.lean:295`), on the Poincaré chart through `liftChartHam` and LP's
chart lift, as in `KAM/Application/LambdaDrift/Bridge.lean:85`.

**Observables:**
- **F₁ = 5Λ''_J + 2Λ''_S and F₂ = Λ''_U:** Stage-I resonant normal form of order N, with the 5:2 family and the
  near-resonant three-body harmonics kept unnormalized.
- **Λ''_S:** Stage II, great-inequality averaging of order M, in Stage-I variables.
- **F^sec_j:** near-torus Kolmogorov–Birkhoff observables of the certified H̄ (the gate-2 construction). They are
  pulled back through Stages I and II as direct observables up to 10⁵ yr. From 10⁶ yr they go through an explicit
  Stage-I map.
- **L:** exact. It gives C = ΣΛ − |L| in all charts (the generators are rotation invariant).

**Region.** The secular tube × the Λ''-windows × all fast angles, mod rotation (`Rotation.lean`). It contains
neither the AMD corners nor the 5:2 zone.

**Conclusion.**
- The windows give explicit semi-major-axis intervals and two-sided osculating eccentricity bands (the tube plus
  enclosed short-period offsets).
- Explicit separations follow from the frozen LP element lemmas (`SourceKeplerPeriLePlaneLength`,
  `PlaneLengthLeSourceKeplerApo`).
- LP0 and AMD give a redundant no-crossing clause.

### 4.2 Rungs and orders (estimate, from the measured gains of §2.3–2.4)

| Rung | T | Region | Stage I N | Stage II M | Secular part | Unnormalized near-resonances | Trust | Verdict |
|---|---|---|---:|---:|---|---|---|---|
| R3 | 10³ yr | small secular box (FULL-A1), ρ ≈ 10⁻⁷ ball | 2 | 1 (z-observables) | none | all three-body; (1,0,−7) | kernel | **go** after G1–G5 |
| R4 | 10⁴ yr | tube δ ≈ 10⁻⁵ | 3 | 3 | H̄ at mass order 3, gate-2 tube | (2,−6,3) and weaker | native | **research program**, go if G1–G3 pass |
| R5 | 10⁵ yr | tube δ ≈ 10⁻⁵ | 4 | 4 | mass order 4 | (2,−6,3) at the margin (3.6·10⁻⁵ against window 10⁻⁴) | native | stretch |
| R6 | 10⁶ yr | tube δ ≈ 3·10⁻⁶ | 5–6 | 5–6 | mass order 5 | (2,−6,3) normalized in mean variables, needs the explicit map | native | research problem |
| R9 | 10⁹ yr | tube δ ≤ 3·10⁻⁶ | ≥ 7–8 | ≥ 10–11 | mass order ≥ 6 | three-body web to 10⁻¹⁵ | — | **no-go** |

**How the orders were matched.**
- **Fast windows:** F₁ rate × T ≤ 10⁻⁴/2.
- **Secular budget:** 0.03·r_N + 0.03·5.1·10⁻⁶/Π(Stage-II gains) ≤ δ/(2T).
- **R3 checked against measured rates.**
  - Order-2 keep52 rates (9.6·10⁻⁸, 2.2·10⁻⁷, 1.1·10⁻⁹) over 10³ yr add (0.96, 2.2, 0.011)·10⁻⁴. With the measured
    oscillation ranges (3.2, 4.0, 0.56)·10⁻⁴, that fits the scoping windows (7, 8, 1)·10⁻⁴ with margin 1.3–1.8.
  - One Stage-II order lowers the 5:2 forcing from 2.1·10⁻⁷ to 1.6·10⁻⁸ and raises the margin to about 1.9–2.1. As
    in HD 11964, the oscillation range, not the rate, then sets the margin.
  - **Box drift:** the averaged z moves at ≤ 2.5·10⁻⁶ per yr (measured, block means). The order-1 averaged
    z-observable carries 2.8·10⁻⁶ (secular) + 5.1·10⁻⁶ (5:2) + 6.1·10⁻⁶ (residual) per yr; after one Stage-II order
    and Stage I at order 2 it is about 3·10⁻⁶, i.e. 3·10⁻³ over 10³ yr inside a box of half-width 10⁻².

### 4.3 Go/no-go gates before any Lean (cheap experiments first)

E1-report style: literal criteria; report the failing term; never shrink the initial set silently.

- **G0 REUSE (done here).** The measured inputs of §5: rates, gains, ε₅₂, divisor modulation, corners, support.
- **G1 RESONANT LADDER** (≤ 4 CPU-h, ≤ 4 GB).
  - A Poisson-series producer (3 fast angles, pair-structured; polynomial in z, z̄ to degree 8; Taylor in L to
    degree 2) in double-double or 128-bit, for the keep52 normal form to order 5. Rates against the exact
    Newtonian gradient at ≥ 50 slow points of the R4 tube.
  - **PASS iff** the F₁ and Λ_U gains at orders 3–5 are ≥ 20 per order at every sampled point, and the order-3 rate is
    ≤ 2·10⁻⁹ per yr.
  - **FAIL:** R4 drops to 10³–3·10³ yr; R5/R6 are abandoned.
- **G2 FREQUENCY MODULATION** (≤ 30 CPU-min).
  - Over the R4 tube, min |k·n(Λ)| at osculating Λ for every harmonic the order-N generators divide by. Rate floor of
    every unnormalized near-resonant harmonic.
  - **PASS iff** every normalized divisor stays ≥ 3·10⁻³ at osculating Λ for the R4 orders, and the floor × 10⁴ yr
    ≤ 10⁻⁵.
  - **FAIL:** an explicit Stage-I map already at R4.
- **G3 STAGE-II LADDER** (≤ 1 CPU-h). Great-inequality averaging in Stage-I variables to order 6 over the tube.
  **PASS iff** the gains are ≥ 6 per order through order 4 and ε₅₂ ≤ 0.15 over the tube.
- **G4 SUPPORT** (≤ 1 CPU-h). Pruned Poisson-series sizes at the rung's thresholds (E10 gives 10³–10⁴ fast
  harmonics per function at 10⁻¹²–10⁻¹⁴, before slow monomials). **PASS iff** the R4 certificate is
  ≤ 10⁸ coefficients after pruning.
- **G5 SHARD** (≤ 2 CPU-h; one targeted throwaway build, shared with X1's SX-2 and HD's rehearsal). One real-size
  pair-structured Fourier × Taylor product in `decide +kernel` and through a compiled native checker. It measures the
  kernel/native ratio. Gate 2 measured about ×24 end to end (25 min against about 10 h).
- **G6 MODEL GAP** (≤ 1 CPU-h). H̄ at mass order 3 against N-body: secular frequencies to ≤ 10⁻⁴, and the torus
  location inside δ/3. This decides whether the tube is placed on the right torus.

### 4.4 Stages, reuse and costs

| Stage | Content | Reuses | Lean (est.) | CPU (est.) |
|---|---|---|---:|---|
| S0 | owner decisions §6 | — | — | — |
| S1 | G1–G6 (Python) | `harmonics.py`, `order3.py`, `normal_form.py` (HD), `scripts/sjsu/gate2/` | — | ≤ 10 CPU-h |
| S2 | R3 statement, audit, freeze | FULL-A1 sketch (scoping note §1.2), LP definitions | 0.3–0.6k | — |
| S3 | R3 Lean: identity for N = 2 with kept part, pair-structured Fourier × Taylor checker, Kepler witness, box cover | `LieRemainder.lean` (N ≤ 2), `Bridge.lean`, HD layer, `KAM/CertificateSharp/Packed/`, `ApproxIntegral.lean` | 4–8k | builds |
| S4 | R3 production, kernel | — | — | 10²–2·10³ CPU-h kernel (pair-structured; 3·10³–2·10⁴ if 3-D blocks) |
| S5 | R4: N-generator identity, Stage-II generators, certified H̄ with tail, tube on H̄ + model-error term, native interface | Tube N2–N6 (gate 2), `numerical-certificate.lean` pattern (`lemma/sjsu-native`) | 6–12k | native 10–10³ CPU-h (kernel 10³–10⁵) |
| S6 | R5 | as S5 | +1–2k | native 10²–10⁴ |
| S7 | R6: explicit Stage-I map | `KAM/Canonical/{Flow,FlowInverse,Lie,Symplectic,CompositionSeries}.lean`, Tube N2 bracket transport | +5–15k | native 10³–10⁵ |

**How the costs were reached (estimate).**
- **Cells.** About 10–50 along the secular torus, mod rotation. That is comparable to HD's 50–200 over its AMD ball,
  because the tube is thin.
- **Products per cell.** HD's census (10⁴, 7.2·10⁴, 3.8·10⁵ at orders 2–4) × 5–10 for 9 local variables and three
  pairs.
- **Kernel time per product.** 0.5–1 s for 2-D blocks; 3-D blocks are only needed for the three-body content
  (E10: ≥ 189 harmonics above 10⁻¹⁰ in K₂), which can be bounded by norm products below the rung's budget.
- **All-in.** × 2–5.
- **Native.** ÷ 10–1000.

## 5. Experiments (question 4)

All of these are measured, at the stated sample points; none is an enclosure.

**E1. Integrator.**
- `sjsu_wh.c` ports `nbody.py`: SLG13 eq. (1), Wisdom–Holman democratic-heliocentric map, Yoshida order 4, Table 1
  read as Poincaré elements.
- After 1,000 yr at dt = 0.5 it agrees with `nbody.py` to 6.4·10⁻¹¹ AU in position and 7.8·10⁻¹² relative in
  momentum (`validate_vs_nbody.json`).
- Speed: 0.47 µs per DH step.

**E2. One Gyr** (`main_1e9_o4_dt1.*`, 25 CPU-min). See §2.10.
- Block means over 4416 yr have Λ ranges of 3.9·10⁻⁶, 9.2·10⁻⁶ and 4.5·10⁻⁷.
- AMD block means lie in [1.0254, 1.0307]·10⁻³.
- Linear slopes of Λ_j and C are about 2·10⁻¹⁹ per yr: noise.
- The sup rate of the block-mean z is 1.5, 2.5 and 0.17·10⁻⁶ per yr. Linear modal actions move at ≤ 3.4·10⁻⁹,
  3.1·10⁻⁹ and 2.3·10⁻¹⁰ per yr (`modal_rates.json`).
- dt = 1 and dt = 0.5 give the same 1-Myr maxima of e to ≤ 1.4·10⁻³ relative. Minima near zero differ more, up to
  5 % for e_U.

**E3. Lyapunov** (`sjsu_lyap.c`, tangent map by forward AD; `tlyap_*`, 41 CPU-min).
- 1 Gyr (dt = 1): s(10⁹) = 21.05, fit 1.08 ln t, T_L ≳ 7.8·10⁸ yr.
- 0.2 Gyr (dt = 0.5): fit 1.0004 ln t, T_L ≳ 1.2·10⁹ yr.
- Control with all masses ×10⁻¹²: s(2·10⁶) = 14.54, against 14.52 at real masses.
- Shadow-orbit artifact: `artifact_shadow_lyap/`, T_L ≈ 1.5–2.6·10⁴ yr at every mass scale, rounding fed by shear.

**E4. Frequency-map analysis** (`analyze_main.py`). 100 windows of 10 Myr; Hann window; refined peak of each modal
signal. g = (1.371996·10⁻⁴, 2.037895·10⁻⁵, 1.152687·10⁻⁵), with scatter and trends as in §2.10.

**E5. Harmonic census** (`harmonics.py`, `harmonics.json`).
- Grids 128 × 128 × 64 over the three mean longitudes at the nominal secular point (`xi_eta_secular` of the
  dataset).
- Finite differences 10⁻⁶ for slow derivatives; divisors from the N-body mean motions; A = Kepler Hessian.
- The 5:2 family, ε_L and ε_z, the three-body content of K₂ and the secular-direction rates are quoted in §§2.1–2.4.
- **Validation:** the order-0 sup rates reproduce the N-body Λ̇ to ≤ 3.4 %.

**E6. Order-0/1/2 rates** (`order3.py`, `order3.json`, `order3_analyze.json`). Nested central differences (inner
10⁻⁶; outer 10⁻⁵·Λ\* and 10⁻⁴ in z) for K₂, {a, χ₁}, {b, χ₁}, χ₂ and H₃. Table in §2.3. **Checks:**
- K₂ from this code equals `harmonics.py`'s order-2 term to 4 digits;
- F₁ annihilates the kept 5:2 to 5·10⁻¹⁸.

**E7. Great inequality alone** (`order3.py gi`). Gains ×13.4 and ×9.4 (§2.4).

**E8. Corners** (`run_points.py`, `run_points.json`, `gi_strength.json`, `census_corner.json`). §2.6. ε₅₂ on the AMD
sphere and along the orbit.

**E9. Divisor modulation** (`run_points.json`, field `divisor_modulation_nominal`). §2.5.

**E10. Fourier support** (`support_census.py`). Harmonics whose rate contribution exceeds τ:

| Function | τ = 10⁻¹⁰ | 10⁻¹² | 10⁻¹⁴ | 10⁻¹⁶ |
|---|---:|---:|---:|---:|
| f (pair harmonics; \|k\| up to 56) | 410 | 812 | 1,339 | 2,019 |
| K₂ (order-2 term), three-body | 379 (189) | 1,998 (1,475) | 5,867 (4,837) | 12,905 (11,216) |
| H₃ (order-3 term), three-body | 57 (2) | 949 (659) | 4,153 (3,401) | 11,438 (9,520) |

Each harmonic carries a polynomial in (z, z̄, L). With degree 8 in six complex variables and charge balance this is
about 10²–10³ monomials per harmonic (estimate). So R4 needs about 10⁶–10⁷ coefficients per function and R9 about
10⁸–10⁹.

**E11. Existing order study.** Re-read in §2.7.

## 6. Owner decisions and verdict (question 5)

1. **Trust level.**
   - (a) Kernel only: R3 is the ceiling.
   - (b) Native for R4 and beyond. This uses the representation-independent `numerical_certificate` pattern of
     `lemma/sjsu-native`, which adds one trust root: the compiler and `native_decide`'s reduction axiom.
   - **Recommended: (a) for R3, (b) for R4+,** with the native root stated in the docstring.
2. **Planar or spatial.** **Planar** (invariant subspace, honest). Spatial only after R4 (×3–10, and a 4-dof
   secular tube).
3. **Target.**
   - **Recommended:** R3 as the first full-problem theorem; R4 as the program's headline; R5/R6 only after G1/G3 pass
     at orders 4–6.
   - **10⁹ yr is not a target** for the full problem. Gate 2 remains the 5-Gyr statement, about the secular model.
4. **Model of record.** LP's frozen `movingHamiltonian` at n = 3, planar.
   - Masses from SLG13's reciprocals (as in the dataset and gate 2), or IAU/DE440 values.
   - **Recommended:** SLG13, so the full and secular theorems share data. Neptune and 1PN are excluded and named.
5. **Initial data and set.**
   - Data: SLG13 Table 1 read as Poincaré elements (as gate 2), or a JPL state projected on the invariable plane.
   - Set: a ρ-ball (R3), or for R4+ a positive-measure tube cross-section (all fast phases, all perihelion rotations,
     modal actions in windows).
   - **Recommended:** Table 1; the ball for R3, the tube for R4.
6. **Elements in the statement.**
   - LP's canonical heliocentric elements (velocity p/ν), or the osculating heliocentric elements of LP's osculating
     clauses.
   - **Recommended:** both, as in LP1, with the O(μ) conversion proved.
7. **Compute envelope.** Gates ≤ 10 CPU-h now. R3 production ≤ 2·10³ kernel CPU-h on the local lane, after G5. R4
   only with an explicit allocation (rented cores or native).
8. **Wording.** Never "the Solar System is stable for 10⁹ years". R3/R4 read "the planar Newtonian
   Sun–Jupiter–Saturn–Uranus model, for 10³ (10⁴) years". The README and headlines keep gate 2 labelled "secular
   model".
9. **Research producer.** Fund G1/G3 to orders 5–6 in high precision (a few weeks of one numerics worker)? That
   experiment decides between "10⁴ yr is the frontier" and "10⁶ yr is reachable".

**Verdict.**
- **10⁹ yr is not achievable for the full problem.** The full planar SJSU problem needs normal forms of order ≥ 7–8
  (fast) and ≥ 10 (great inequality) with rigorous remainders on a secular tube, plus a secular model at mass
  order ≥ 6.
  - The measured gains are already declining (154 → 43 and 13 → 9.4).
  - Frequency modulation forces explicit canonical maps.
  - Neither the floating-point producers nor the certificate scale exist.
- **The strongest honest results in reach:**
  - R3: a kernel-checked no-crossing theorem with explicit a- and e-windows for 10³ yr. It would be the first
    machine-checked bound on the full four-body problem at real masses.
  - R4: the same with two-sided secular eccentricity bands for 10⁴ yr, under native checking.
  - R5/R6 (10⁵–10⁶ yr): conditional on G1/G3.
  - The 5-Gyr result stays a theorem about the secular model `SJSU18-O2`.

## 7. Lean infrastructure (sketch; nothing built)

The project's hard rules, verbatim:
1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

R4 statement shape (sketch; the names after `sjsu` are proposed):

```lean
/-- R4 (sketch, not built): planar Newtonian SJSU for 10⁴ yr: existence, uniqueness, explicit two-sided
semi-major-axis and osculating-eccentricity bands. -/
theorem sjsu_full_bands (z₀ : Phase (3 * 2)) (hz₀ : z₀ ∈ sjsuInitialSet) :
    ∃ z : ℝ → Phase (3 * 2), z 0 = z₀ ∧
      IsMovingSolutionOn sjsuNu sjsuMu (Set.Icc (-sjsuT) sjsuT) z ∧
      MovingUniqueOn sjsuNu sjsuMu (Set.Icc (-sjsuT) sjsuT) z ∧
      ∀ t ∈ Set.Icc (-sjsuT) sjsuT, ∀ j,
        aLo j ≤ keplerAxis sjsuNu (z t) j ∧ keplerAxis sjsuNu (z t) j ≤ aHi j ∧
        eLo j ≤ planeLength (keplerEccVector sjsuNu (z t) j) ∧
        planeLength (keplerEccVector sjsuNu (z t) j) ≤ eHi j
```

**Status of the parts.**

| Piece | Status |
|---|---|
| First exit, existence and uniqueness (`ApproxIntegral.lean:198, 295`) | proved |
| Λ-drift bridge, no crossing (`Bridge.lean:85`, `NoCrossing.lean:121`) | proved |
| Order-1 and order-2 Lie remainder identities (`LieRemainder.lean:152, 187`) | proved |
| Rotation reduction (`Rotation.lean`) | proved |
| Tube chart and checker, gate 2 (`KAM/EffectiveStability/Tube/*`) | proved |
| Packed Fourier and jets (`KAM/CertificateSharp/Packed/`) | proved |
| Lie Taylor formula with remainder (`KAM/Canonical/Lie.lean`, `taylor_lie`) | proved |
| Flows and inverse (`Flow*.lean`, `FlowInverse.lean`) | proved, not in certificate form |

**New work, in order.**
1. **N-generator identity with a kept resonant part.** Generalizes `pb_approxIntegral₂`; Stage-II generators are
   further generators of the same identity. 1.5–3k lines.
2. **Pair-structured Poisson-series checker.** Fourier × Taylor, with d'Alembert charge, Kepler witness and Cauchy
   tails. Shared with HD and X1. 4–8k lines.
3. **Secular observables on a certified H̄.** The tube checker with a model-error term,
   |{F, H̄ − H̄_poly}| ≤ |∇F|·sup|∇(H̄ − H̄_poly)|. 0.5–1k lines plus the H̄ producer.
4. **Native interface.** On the `numerical_certificate` pattern: rates, faces, initial ball and element bands as
   fields over actual functions. 1–2k lines.
5. **For R6: an explicit Stage-I map.** Certified flow enclosure, inverse coverage and bracket transport.
   5–15k lines.

## 8. Literature (2018–2026 emphasis) and novelty

**Literature.**
- **Secular SJSU.** Sansottera–Locatelli–Giorgilli (2013); Giorgilli–Locatelli–Sansottera (2017).
  Kolmogorov–Nekhoroshev estimates of about 10¹⁰ yr near the secular torus. Not computer-assisted proofs; order two
  in the masses.
- **Full SJS, effective stability.** Giorgilli–Locatelli–Sansottera (2009, CMDA 104): times "comparable with the
  age of the universe" only with strong truncations. Not rigorous.
- **Full planar SJS, KAM.** Figueras–Haro (2024, J. Nonlinear Sci., arXiv:2403.10152). KAM continuation from Kepler
  to realistic masses; the existence conditions are checked numerically; the rigorous computer-assisted phase is
  announced. The closest work to a full-problem theorem.
- **Computer-assisted normal forms.**
  - Caracciolo–Locatelli (2020, JCD 7): rigorous Birkhoff remainders on Hénon–Heiles and the circular planar
    restricted three-body problem.
  - Locatelli–Caracciolo–Sansottera–Volpi (2022): Kolmogorov normal forms for exoplanets.
  - Caracciolo–Locatelli–Sansottera–Volpi (2022, MNRAS 510): librational tori, υ And.
  - Mastroianni–Locatelli (2023, CMDA 135) and arXiv:2311.01938: computer-assisted proofs of KAM tori in secular
    quasi-periodic restricted models of υ And b.
  - Guzzo–Caracciolo–Pinzari (2026, arXiv:2601.18268): sharper a-priori stability bounds from Birkhoff normal forms,
    compared inside computer-assisted proofs.
  - All of these are secular, restricted or low-dimensional. None treats the full four-body problem.
- **Nekhoroshev constants.** Niederman (1996, Nonlinearity 9) and Barbieri–Niederman (2018, arXiv:1810.05987): the
  constants are explicit but need masses far below Jupiter's for Solar-System times (secondary report: about 10⁻¹³).
- **Instability.** Clarke–Féjoz–Guàrdia (2024, ARMA): orbits of the three-planet problem along which a semi-major
  axis varies widely, on times polynomial in the masses. So no unconditional semi-major-axis stability theorem exists
  in general; theorems must be local in phase space, as here.
- **Chaos in the outer planets.** Murray–Holman (1999, Science; 2001, Nature); Hayes (2007, Nature Physics; 2008,
  MNRAS); Guzzo (2005, 2006, Icarus). The 5:2 structure: Michtchenko–Ferraz-Mello (2001, Icarus 149). Very long
  times: Zink–Batygin–Adams (2020, AJ 160).
- **AMD.** Laskar–Petit (2017, A&A 605) and Petit–Laskar–Boué (2017, A&A 607, AMD with first-order resonances).
  This plan's §2.6 shows why AMD alone is too coarse for SJSU.
- **Validated integration.** Taylor-model integrators (Berz–Makino line): short times only.
- **Classics the project already uses** (recalled, not re-fetched here):
  - Celletti–Chierchia (2007, Memoirs AMS): computer-assisted KAM for a restricted three-body model.
  - Gabern–Jorba–Locatelli (2005): a Kolmogorov normal form for Trojan models.
  - Locatelli–Giorgilli (2000, 2007): secular and planetary SJS tori.
  - Chierchia–Pinzari (2011) and Pinzari: planetary KAM and the planetary Birkhoff normal form, with asymptotic
    constants.
  - Volpi–Locatelli–Sansottera (2018): reverse KAM for exoplanet inclinations.
  - Delshams–Gonchenko–Gutiérrez: instability mechanisms, not a stability tool.
  - None gives a time bound for the full SJSU problem.

**Novelty, honestly.** Within these (non-exhaustive) searches, nothing bounds the orbits of the full SJS or SJSU
problem rigorously over any stated horizon.
- **R3** would be the first machine-checked such bound, for 10³ yr. It is short astronomically, and its value is the
  rigour.
- **R4** would add two-sided eccentricity bands for 10⁴ yr.
- **What was new in this task:**
  - the measured order-1/2 gains for SJSU;
  - the great inequality's pendulum parameter along the orbit and on the AMD sphere;
  - the divisor-modulation census;
  - the AMD-corner collapse;
  - the 1-Gyr regularity of this model.

## 9. Uncertainties, errata, deviations

**Uncertainties.**
- **Single-point rates.** Every rate is a sampled sup over the fast torus at a handful of slow points.
  HD 11964 found region sups 3–5× the samples and a rigorous-design factor of 1.5–5.
- **Extrapolations.** The gains at orders ≥ 3 (Stage I) and ≥ 3 (Stage II) are extrapolated. The orders of §4.2
  could move by ±1–2.
- **Finite differences.** Nested central differences limit order 2 to about 3–4 significant digits. Grids
  (128, 128, 64) alias at about 10⁻¹⁷ relative, possibly more at e_U = 0.22.
- **ε₅₂** is a one-harmonic pendulum proxy. The true separatrix geometry depends on eccentricity.
- **Costs.** Extrapolated from HD 11964 and LG00 laws. G5 must measure them.
- **Integrator.** The 1-Gyr regularity is for this model, this datum and this integrator (dt = 1 and 0.5 yr agree).
  Real-Solar-System chaos (with Neptune) is a different question.

**Suspected errata in pinned sources: none new.** SJSU-E1…E4 and the "λ₅" typo are already recorded.

**Repository notes (not pinned-source errata).**
- [`sjsu-model-recovery.md`](sjsu-model-recovery.md) §6.2 gives the N-body ω₂ = −2.03549·10⁻⁵ (3-Myr run). The
  1-Gyr windows here give 2.037895·10⁻⁵ with scatter 4·10⁻⁷, so the model's g₂ error is −0.47 %, not −0.35 %.
- [`sjsu-full-problem-scope.md`](sjsu-full-problem-scope.md) is superseded in three places:
  - FULL-A2 is non-convergent on the AMD ball, not merely costly (§2.6);
  - the "10²–10³ per order" gain becomes 154/43 measured (§2.3);
  - its §2.5 estimate of about 10³ yr for gate 2's F_j is confirmed in kind: the true orbit leaves gate 2's tube
    (§2.2).

**Deviations from the brief.**
- I wrote a C port of the repository integrator, and an AD tangent map instead of a Python shadow orbit. The shadow
  method's float64 artifact (§2.10) made it necessary.
- The plan replaces the scoping note's FULL-A2 rung by R4 (secular tube).

## Appendix A. Reproduction

All are run from `.drafts/sjsu-full-research/` with `nice -n 10`; Python needs numpy and the repository's
`applications/sjsu/scripts` (imported, not modified).

```sh
gcc -O3 -march=native -o sjsu_wh sjsu_wh.c -lm && gcc -O3 -march=native -o sjsu_lyap sjsu_lyap.c -lm
python3 validate_vs_nbody.py                              # E1 (needs ./sjsu_wh run 1000 0.5 4 2000 val_c1000)
./sjsu_wh run 1e9 1.0 4 4416 main_1e9_o4_dt1              # E2, 25 CPU-min
python3 analyze_main.py && python3 modal_rates.py && python3 torus_offset.py   # E2, E4, §2.2
./sjsu_lyap 1e9 1.0 4 1000 tlyap_1e9_dt1 1                # E3, 29 CPU-min
./sjsu_lyap 2e8 0.5 4 2000 tlyap_2e8_dt05 1 && python3 fit_lyap.py tlyap_1e9_dt1 tlyap_2e8_dt05
python3 harmonics.py                                      # E5, 1.5 CPU-min
python3 order3.py keep52,full && python3 order3.py gi order3_gi && python3 order3_analyze.py   # E6, E7
python3 run_points.py && python3 gi_strength.py && python3 census_corner.py                    # E8, E9
python3 support_census.py                                 # E10
```

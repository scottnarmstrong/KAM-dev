# LP-QUANT: can track LP's theorems be turned into a numerical certifier?

Date: 1 November 2026. Branch `lp-quant`. Python study, no Lean. Scripts in `scripts/lp_quant/`, raw numbers in
`scripts/lp_quant/results/`. Nothing here is a theorem or a certificate. Inputs are published nominal values, not enclosures.

## 1. Verdict

**Do not build "quantitative LP" on the normal-form engine, for any class of real system. Keep LP as the endpoint, and feed it a
direct drift certificate for the Λ alone.**

- **LP1 and LP2 certify nothing real.** Their literal constants give μ₀ ≈ 10⁻³⁹ for Sun–Jupiter–Saturn (SJS), against the actual 10⁻³·⁰.
  At the threshold the theorem's time is about `e·T₀ ≈ 10⁻¹⁰` time units. No test system has a usable time at its actual μ.
- **Optimizing every free parameter does not rescue it.** The best tier of the landed engine reaches μ ≈ 10⁻¹⁰·³ for any
  certificate and 10⁻¹⁴·² for 5 Gyr on SJS, which is 11 orders short. A hypothetical sharper engine reaches 10⁻¹¹·⁹, which is 9 short.
- **Trivial Gronwall beats the landed engine at 5 Gyr on every system.** `|Λ̇| ≤ μ sup|∂_λ f|` on the AMD ball, with the AMD budget
  from LP, reaches 10⁻¹²·⁰ on SJS. LP1's exponential only pays below about μ = 10⁻¹⁵. First-order averaging reaches about 10⁻⁸.
- **The Λ-only route is the live one.** With actual Fourier coefficients and no norms, the fast-angle normal form of each pair converges
  at actual masses on the actual AMD level, in every system except HD 1461. The AMD budget is not what binds: the tube that keeps
  resonances out is 160 to 18,000 times smaller than the budget.
- **Near 5:2 is the hard part, and it is specific.** On SJS with true frequencies, the 5:2 term is weak on the actual AMD level
  (strength 0.02) but strong at the high-e_S, anti-aligned part of the AMD ball (0.48), where a non-resonant step fails. A
  whole-ball certificate there needs a resonant block.

These last two points are estimates in a model with frozen slow variables and one pair at a time (section 5.5). They say where a certificate
could exist, not that one does.

| Class | log₁₀ μ actual | Lean literal μ₀ | best engine, 5 Gyr | T at actual μ, LP1 | Gronwall T at actual μ | Λ-only, 5 Gyr (estimate) | Recommendation |
|---|---:|---:|---:|---|---:|---|---|
| SJS (planar and spatial) | −3.0 | −39 | −14.2 | none | 5 yr | about 5 Newton steps, K ≈ 130; whole ball needs a resonant 5:2 block | research target; start at short horizons |
| J-S-U-N | −3.0 | −77 | −19.1 | none | 1.4 yr | K ≈ 325, U–N diverges on part of the ball; budget thin | not yet |
| Earth-mass, wide | −5.5 | −37, −53 | −14.9, −19.1 | none | 300–400 yr | 2 steps, K ≈ 60–70 | **first pilot** |
| Earth-mass, compact | −5.5 | −43, −63 | −16.4, −20.9 | none | 0.3–0.6 yr | 3–4 steps, K ≈ 420–580 | later |
| HD 11964 | −3.3 | −46 | −15.5 | none | 0.4 yr | 3 steps, K ≈ 73 | **best real target** |
| HD 109271, HD 69830 | −4.2 | −40, −58 | −16.0, −19.9 | none | 0.4 yr | 3–4 steps, K ≈ 130–150 | candidates, data permitting |
| HD 1461 | −4.7 | −45 | −17.0 | none | 0.03 yr | does not converge (near 7:3 at the upper-limit eccentricities) | no |
| HD 96700 | −4.4 | — | — | — | — | fails the strong AMD test, C/B = 2.6 | excluded |
| Mass-scaled SJS shape | any | −39 | −14.2 | see Table G | — | — | LP1 pays only below 10⁻¹⁵ |

## 2. The constant chain

Labels used in this section and in every table: **exact** (a closed formula on pinned inputs), **bounded** (a rigorous
inequality, up to outward rounding, which the Python does not do), **estimated** (a sampled supremum, which is a lower
estimate of the true sup, or a heuristic). Inputs are published nominal values, not enclosures.

Notation: `n` planets, `k` slow pairs of the engine (`k = n` planar, `2n` spatial), `D = 2n + 2k`.

### 2.1 The Lean proof (route L)

This is what `planar_safety_of_prograde` (`KAM/Planetary/StrongAMD/PlanarSafety/Prograde.lean:43`) actually builds. The spatial
twin is `KAM/Planetary/Spatial/SpatialSafety/Aligned.lean:75` with `k := n + n`
(`KAM/Planetary/Spatial/NonresonantReuse/Drift.lean:96`) and otherwise the same formulas.

| Step | Constant | Formula in the proof | Source | Status |
|---|---|---|---|---|
| 1 | `r_g` | any `r` with `Ω_B(4r) ≤ δ/16`; `U = cthickening (4 r_g) L_δ` | `exists_isSharedTube`, `AnalyticDomain/Core.lean:98` | **compactness** |
| 2 | `R, M` | `R`: radius of a sup-norm complex tube around the sharp core where `f` is holomorphic; `M = sup|f|` on the tube of radius `R/2` | `exists_strongTube`, `AnalyticDomain/Extension.lean:35` (track P's `tube`) | **compactness** |
| 3 | `I_min` | positive lower bound of the actions on `L_δ` | `lp_exists_lower_bound`, `NonresonantReuse/Drift.lean:42` | compactness (trivial) |
| 4 | widths | `s₀ = b₀ = R/16`, `rs = min(4r_g, R/4)`, `s = σ = s₀/π`, `w = 2b₀`, `ρ = min(rs, I_min)/2` | `lp_stopped_drift`, `Drift.lean:87-104` | exact given 1–3 |
| 5 | `L` | `Σ_i 3ν_i³/(2π(I_min/2)⁴)` | `lpKeplerLip`, `NonresonantReuse/Kepler.lean:38` | exact |
| 6 | `M₂` | `coth(πσ)ⁿ max(M,1)/(2π)`, so `ε = M₂ μ` | `lpM₂`, `NonresonantReuse/PertClass.lean:34`; `wbound_of_sup_bound` | exact given 2 |
| 7 | `κ` | `min(γ/(4π(L D₀+1)), γD₀/(512π(M₂+1)))^{1/(τ+1)}`, `D₀ = 1` | `exists_scale_kappa`, `NonresonantScale.lean:94` | exact |
| 8 | `μ₁` | `min(1, (κ/E)^{2(τ+1)}, B², (ρ/D₀)²)`, `E = 2 + 6/(πs)`, `B = w²/(64πksD₀)` | `lp_scale_choice`, `NonresonantScale.lean:153` | exact |
| 9 | `c, T₀` | `c = πsκ/6`, `T₀ = sD₀/(5M₂)` | same, line 154 | exact |
| 10 | `r₁` | any `r` below which `n r + Ω_B(r) ≤ δ/4` | `exists_budget_radius`, `PlanarSafety/Constants.lean:35` | **continuity modulus** |
| 11 | `d⋆, d_pair` | `min` of the barrier and osculating outputs; `d⋆` has the closed form (41), `a_min m²/(2I_max²)` with `m = δ/2`; `d_pair` is the minimum of the gaps over a compact set | `strongBarrier_physical`, `osculating_barrier`; `Geometry.lean`; MAIN L5 | `d⋆` exact; `d_pair` **compactness** |
| 12 | `A_osc, A_elem, μ₂` | explicit in `(d⋆, R, P, c, e⋆)`: `oscAperi`, `oscAa`, `oscAe` | `exists_osc_estimates`, `Osculating/Core.lean:29-48`, `Osculating.lean:98` | exact given 11 |
| 13 | `A_Λ, A_a` | `A_Λ = 1/2`, `A_a = (max(C,0)+1)(S+1)`, `S = Σ_k ν_k⁻²`, `C` a norm bound on `U` | `Prograde.lean:100` | exact |
| 14 | `μ₀` | `min(μ₁, μ₂, min(r₁, r_g)², d⋆/(2A_osc), d_pair/(4A_osc))` | `Prograde.lean:83` | exact given the above |

Since `a(τ+1) = 1/2`, step 8 gives, when the arithmetic term is the active one,

`μ₀ = (κ/E)^{2(τ+1)} ≈ γ² · (π s/6)^{2(τ+1)} · min( (4π(L+1))⁻², (512π(M₂+1))⁻² )`, and at `μ = μ₀` the exponent is
`c μ₀^{−a} = (2πs + 6)/6 ≈ 1`.

So **at the threshold the theorem gives only `T ≈ e·T₀`**, and `T₀ = s/(5M₂)` is far below one orbit. The exponential only starts below `μ₀`.

### 2.2 The engine, stripped of the choices (route E)

`KAM.Nekhoroshev.nonresonant` needs far less than the Diophantine statement. With `p = 2` (which is optimal: the window below
depends on `p²/(p−1)`), period-one frequencies `ω/(2π)`, and `ε = |μf/(2π)|_{r,s}`, its premises are

```text
(E1) K L r ≤ α/2        (E2) ε ≤ α r/(256 K)        (E3) 64π k s r ≤ w²        (E4) 2π K s ≥ 6
(E5) |t| ≤ s r/(5ε) · exp(2π K s/6)                  conclusion: drift ≤ r/2
```

`α = min_{0<|j|₁≤K} |j·ω|/(2π)` is a **finite** quantity. (E1) and (E2) leave a window for `r` exactly when

`μ ≤ α(K)² / (512 K² L F(s))`,   `F(s) = |f/(2π)|_{r,s}`.   **(W)**

(W) is the whole story. It is a Chirikov criterion with the constant 512, with the full norm `F` where the resonance width would use
the single harmonic `f_k`, and with `K ≥ 3/(πs)` forced by (E4). Everything below measures what each factor costs.

### 2.3 The paper route (route P)

MAIN Lemmas 9–12: `D = 2n + 2k`, `B_D = 16eD`, `q_D = min(c_D, 1/(6B_D), 1/64)`, `A = γ⁻¹max(1, (2τ/(es))^τ)`, condition
`A ε N^{τ+1} ≤ q_D` with the scaled vector-field size
`ε = max(3L_ω r/s, C_s μ G_λ/r, C_s μ G_I/s, C_s μ G_z/b)`, `C_s = ((1+e^{−s})/(1−e^{−s}))ⁿ`, and time `2^N/(8ε)`
(from (34); the theorem keeps only `2^{N/2}`). `c_D` is implicit in the source (audit note N5). The script takes
`q_D = 1/(96eD)`, the value at which the audit checked the bookkeeping. This route needs the all-orders Diophantine condition,
because `|k|^τ e^{−σs|k|/2}` is bounded over all `k`. It is **not** formalized (the Lean route is L/E) and it is the weaker one numerically.

### 2.4 Compactness steps, and how to replace them

| Compactness output | What it is | Numerical replacement here | How to certify it |
|---|---|---|---|
| `B(I)` (not compactness, a minimum) | convex 1-D contact problem (15) | bisection on `g'`; the tangent at the minimizer is a lower bound (`geometry.pair_contact`) | **bounded** now; exact-rational tangent certificate is cheap, a few lines per pair |
| `Ω_B`, `r_g`, `r₁` | modulus of `B` on `U` | `Lip(B) r` with the envelope gradient `∂_iB = D(u) − 2αI_jD'(v)(1+u)/I_i`, `∂_jB = D(v) + 2αD'(v)(1+u)` (checked against finite differences) | interval enclosure of the two contact equations on `U`; small |
| `d_pair`, sharp `d⋆` | minimum of a linear gap on a convex set | 1-D scan (`geometry.dpair_sharp`, `dstar_sharp`) | convex, tangent certificate |
| `R` | holomorphy radius of the tube | largest sampled radius with no Kepler or denominator singularity (`Ctx.tube_R`) | subdivision of the real ball with Lemma 8's inequalities; a Lean theorem must then replace `tube` |
| `M` | sup of `|f|` on the tube | random start plus ascent (`chart.sup_oracle`), objective both `|f|` and nearest singularity | interval subdivision in `4n` real dimensions planar; expensive; pair structure reduces it to 8 real dimensions per pair |
| `F(s)` (route E only) | Lean's `WBound` norm | FFT on sampled `J` of the ball, pair by pair (`chain.direct_norm`) | certified aliasing plus subdivision in `J`; expensive |
| `γ` | the all-orders infimum in (5) | minimum up to a finite order; **an upper estimate** | not certifiable from data, see 2.5 |

Lemma 8's own denominator criterion (`|w·w − |w₀|²| ≤ d²/2`) is a sufficient condition that is much narrower than the true
holomorphy radius. Section 3 gives both numbers.

### 2.5 The Diophantine hypothesis is the wrong interface for data

No finite precision decides condition (5). An interval of frequencies contains exact resonances. `γ(τ)` in the tables is the minimum
over `|k| ≤ 2·10⁴` (n = 2), `2000` (n = 3), `150` (n = 4), which is an upper estimate of the real infimum, and for SJS the
minimizer for `τ = 1.05` is already at `|k| ≈ 3800`. For HD 109271 the published decimal periods have an exact relation at `|k| ≈ 1.3·10⁵`, so the literal γ is 0. The theorem can only be applied to a *selected* exact Diophantine vector
inside the measurement box. Route E avoids this completely, because the engine only ever uses `|k|₁ ≤ K`. Any quantitative use of LP
must go through (E1)–(E5), not through the frozen statement.

## 3. Test systems

Pins are in `scripts/lp_quant/systems.py`. SJS and JSUN: IAU/DE405 mass ratios, Standish J2000 elements, Souami–Souchay inclinations to the
invariable plane. Exoplanets: the fits pinned in `docs/explorations/amd-crossing/A7-practical.md` §5, minimum masses, axes recomputed from the
periods. Earth-mass systems are synthetic, with frequencies in a real number field of degree n, so they have no rational relation.

The thresholds reproduce A7's independent table: C/B = 0.184, 0.485, 0.163, 0.138, 2.60 here against 0.186, 0.485, 0.163, 0.137, 2.60 there.
`B` is the convex contact minimum (15) by bisection on `g'`, with a tangent lower bound. The two agree to 10⁻¹⁶ (**bounded**, up to outward
rounding). `C = Σ I_i(1 − √(1−e²) cos i)`, with inclinations to the invariable plane (**exact** on the nominal inputs).

| System | n | μ | C (norm.) | B (norm.) | active | C/B | strong? | δ = B − C | d⋆ (41) | d⋆ sharp | d_pair sharp |
|---|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|
| SJS, Standish axes | 2 | 9.55e-04 | 4.01e-03 | 8.86e-02 | 0 | 0.045 | yes | 8.45e-02 | 8.94e-04 | 4.160 | 1.171 |
| SJS, calibrated | 2 | 9.55e-04 | 4.01e-03 | 8.92e-02 | 0 | 0.045 | yes | 8.52e-02 | 9.08e-04 | 4.152 | 1.177 |
| SJS, spatial | 2 | 9.55e-04 | 4.17e-03 | 8.86e-02 | 0 | 0.047 | yes | 8.44e-02 | 8.90e-04 | 4.159 | 1.169 |
| JSUN | 4 | 9.55e-04 | 4.25e-03 | 1.22e-02 | 2 | 0.347 | yes | 8.00e-03 | 8.00e-06 | 4.761 | 1.933 |
| JSUN, spatial | 4 | 9.55e-04 | 4.46e-03 | 1.22e-02 | 2 | 0.364 | yes | 7.79e-03 | 7.58e-06 | 4.758 | 1.877 |
| 2 Earths wide | 2 | 3.00e-06 | 4.96e-04 | 1.73e-01 | 0 | 0.003 | yes | 1.73e-01 | 1.71e-03 | 0.592 | 0.338 |
| 3 Earths wide | 3 | 3.00e-06 | 9.46e-04 | 1.72e-01 | 0 | 0.005 | yes | 1.71e-01 | 7.23e-04 | 0.593 | 0.336 |
| 2 Earths compact | 2 | 3.00e-06 | 1.04e-04 | 6.87e-03 | 0 | 0.015 | yes | 6.76e-03 | 4.86e-06 | 0.917 | 0.051 |
| 3 Earths compact | 3 | 3.00e-06 | 1.62e-04 | 5.33e-03 | 1 | 0.030 | yes | 5.16e-03 | 2.47e-06 | 0.926 | 0.049 |
| HD 109271 | 2 | 6.88e-05 | 1.13e-02 | 6.14e-02 | 0 | 0.184 | yes | 5.01e-02 | 1.26e-04 | 0.033 | 0.026 |
| HD 1461 | 2 | 1.90e-05 | 9.81e-03 | 2.02e-02 | 0 | 0.485 | yes | 1.04e-02 | 1.02e-05 | 0.042 | 0.007 |
| HD 11964 | 2 | 5.39e-04 | 9.41e-03 | 5.79e-02 | 0 | 0.163 | yes | 4.85e-02 | 2.14e-05 | 0.021 | 2.268 |
| HD 69830 | 3 | 6.32e-05 | 5.12e-03 | 3.72e-02 | 0 | 0.138 | yes | 3.21e-02 | 1.61e-05 | 0.039 | 0.026 |
| HD 96700 | 3 | 4.29e-05 | 2.39e-02 | 9.22e-03 | 0 | 2.596 | **no** | -1.47e-02 | — | — | — |

**Strong AMD stability.** Every system is strongly stable except HD 96700. That includes J-S-U-N, with C/B ≈ 0.35–0.36 and the U–N pair active: Saturn's
and Jupiter's AMD is what a light outer pair has to tolerate. HD 1461 passes only at its nominal upper-limit eccentricities, and A7's 99% limits
leave a much smaller margin. The closed form (41) for `d⋆` is 2.5 to 6 orders below the sharp value. It is never binding but should not be quoted
as a physical distance.

**The canonical axis is not the published axis, and at SJS that matters.** LP's split uses Kepler parameter one and canonical momenta, so
`ω(I⁰)` differs from the mean motion at O(μ). The first-order shift `μ ∂⟨f⟩/∂I` at SJS is (−8.6·10⁻⁵, +7.2·10⁻⁵) per time unit. Taking Standish's axes
as canonical gives `2ω_J − 5ω_S = −0.00125`, shifted to −0.0018, while the true value is −0.00113. Row "SJS, calibrated" chooses the canonical axes so that
the shifted frequencies are the true ones. Then the canonical divisor is **−0.00060**, shifted to −0.00115. So hypothesis (5) and the engine see a 5:2 divisor about
half the physical one. All SJS statements below use the calibrated row unless they say otherwise.

**Self-checks** (`scripts/lp_quant/check.py`):
- the chart reproduces energy, angular momentum and the symplectic form (residual 4·10⁻¹⁰, finite differences), and the spatial momenta (45);
- for μ ≤ μ₀, all seven conclusions of `lp_scale_choice` hold in 60-digit arithmetic with the chain's constants, so the mirror of that theorem is faithful;
- the envelope gradient of B agrees with finite differences;
- a direct integration of (1) over 20,000 yr keeps the AMD identity (13) up to the integrator's own error in L (1.5·10⁻⁵, equal to the two digits shown).

## 4. What LP1 and LP2 give

### 4.1 The numbers

Columns are log₁₀ μ. "Lean literal" is section 2.1. "Engine best" is section 2.2 with all landed-engine sharpenings. "Hypothetical engine" also replaces
the constants of the normal form lemma. "Gronwall" and "first order" are the elementary Λ-only certificates of section 5.2. `M`, `F` and every rate are
**estimated** (sampled sups); `γ` is an upper estimate. All other columns are exact formulas in those.

| System | actual | Lean literal μ₀ | Lean literal, 5 Gyr | paper, 5 Gyr | engine best μ₀ | engine best, 1 Myr | 1 Gyr | 5 Gyr | hypothetical engine, 5 Gyr | gap at 5 Gyr (orders) | Gronwall, 5 Gyr | first order, 5 Gyr | T at actual μ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| SJS, Standish axes | -3.0 | -39.4 | -46.3 | -26.4 | -10.3 | -11.3 | -14.0 | -14.2 | -11.9 | 11.2 | -12.0 | -7.9 | none |
| SJS, calibrated | -3.0 | -39.2 | -46.1 | -26.4 | -11.0 | -11.5 | -13.6 | -13.8 | -11.5 | 10.7 | -12.0 | -8.2 | none |
| SJS, spatial | -3.0 | -38.9 | -45.8 | -26.0 | -10.4 | -11.3 | -14.1 | -14.3 | -12.0 | 11.2 | — | — | none |
| JSUN | -3.0 | -76.8 | -91.7 | -48.8 | -18.3 | -18.3 | -18.4 | -19.1 | -15.2 | 16.1 | -12.5 | -10.5 | none |
| JSUN, spatial | -3.0 | -76.9 | -91.8 | -46.8 | -18.1 | -18.1 | -18.3 | -19.0 | -15.2 | 16.0 | — | — | none |
| 2 Earths wide | -5.5 | -36.8 | -43.8 | -25.6 | -11.3 | -12.7 | -14.7 | -14.9 | -12.2 | 9.3 | -12.6 | -9.7 | none |
| 3 Earths wide | -5.5 | -53.3 | -64.0 | -34.0 | -17.8 | -17.8 | -18.9 | -19.1 | -13.4 | 13.6 | -12.8 | -8.0 | none |
| 2 Earths compact | -5.5 | -43.0 | -50.1 | -30.2 | -13.2 | -14.5 | -16.2 | -16.4 | -13.6 | 10.8 | -15.5 | -15.2 | none |
| 3 Earths compact | -5.5 | -62.9 | -73.9 | -38.1 | -17.7 | -17.7 | -20.2 | -20.9 | -15.5 | 15.4 | -15.8 | -15.3 | none |
| HD 109271 | -4.2 | -39.8 | -46.9 | -28.0 | -10.8 | -14.2 | -15.8 | -16.0 | -12.4 | 11.9 | -14.2 | -9.7 | none |
| HD 1461 | -4.7 | -44.7 | -52.0 | -31.6 | -12.6 | -16.1 | -16.9 | -17.0 | -14.5 | 12.3 | -16.0 | -15.6 | none |
| HD 11964 | -3.3 | -46.4 | -53.6 | — | -13.4 | -14.4 | -15.3 | -15.5 | -13.0 | 12.2 | -13.3 | -8.2 | none |
| HD 69830 | -4.2 | -58.0 | -68.9 | -36.7 | -14.8 | -16.5 | -19.5 | -19.9 | -13.5 | 15.7 | -14.3 | -10.7 | none |

In the literal and engine columns LP2 is LP1 to within 0.5 orders: the slow dimension enters `k` and the domain, not the structure. Sampling the spatial chart gave almost the same `M`.

**SJS ledger, Lean literal** (best over δ, τ, R; δ = 0.0845, τ = 1.05):

| Quantity | Value | Comment |
|---|---:|---|
| `R` (sharp tube, sampled) | 0.0095 | Lemma 8's own criterion gives 1.2·10⁻⁴, and then μ₀ = 10⁻⁵⁴ |
| `s = σ`, `w` | 1.9·10⁻⁴, 0.0012 | `R/(16π)`, `R/8` |
| `M`, `M₂` | 1.66, 7.5·10⁵ | `M` near the singularity; `coth(πσ)²` costs 2.8·10⁵ |
| `L` | 10.7 | sharp value 0.0177, a factor 607 |
| `γ` | 0.0040 | minimizer `k = (1086, −2695)`, upper estimate |
| `κ`, `E` | 2.5·10⁻⁶, 1.0·10⁴ | |
| `c`, `T₀` | 2.5·10⁻¹⁰, 5.1·10⁻¹¹ | |
| `r_g`, `r₁` | 0.0016, 0.0075 | |
| limits on log₁₀ μ₀ | arithmetic −39.4, osculating −12.9, slow −9.5, tube −5.8, budget −5.6 | the arithmetic term decides |
| `A_Λ`, `A_a`, `A_osc` | 1/2, 43, 3.7·10⁹ | |
| `d⋆` (41), `d⋆` sharp, `d_pair` sharp | 8.9·10⁻⁴, 4.16, 1.17 | |

E0 of Program D rejected the older theorem by a necessary condition alone, at μ < 10⁻³². LP's literal constants are *not* better than that bound: 10⁻³⁹. The
linear averaging helps only after the widths are freed, at 10⁻²⁷ for 5 Gyr. LP3, the Diophantine-free variant, has the E0 problem directly: its radius
`(B₀μ)^{b_n}` must fit the budget, which alone forces B₀μ ≲ 10⁻²³ for n = 2 and 10⁻¹¹¹ for n = 4.

### 4.2 Where the orders go

| Step | SJS, Standish axes | JSUN | 3 Earths wide | 3 Earths compact | HD 1461 | HD 69830 |
|---|---:|---:|---:|---:|---:|---:|
| Lean literal | -46.3 | -91.7 | -64.0 | -73.9 | -52.0 | -68.9 |
| free D0, widths, s/sigma | -27.3 | — | -32.1 | -39.4 | -33.0 | -35.8 |
| sharp Lipschitz L | -24.5 | — | -30.4 | -37.7 | -31.6 | -33.7 |
| tailored AMD ball | -18.2 | -31.6 | -22.5 | -29.0 | -23.7 | -25.7 |
| finite-cutoff divisors alpha(K) | -16.7 | -27.8 | -20.9 | -27.4 | -21.5 | -23.5 |
| direct Fourier norm | -14.4 | -19.3 | -19.1 | -20.9 | -17.0 | -19.9 |
| constant subtracted | -14.2 | -19.1 | -19.1 | -20.9 | -17.0 | -19.9 |
| constants 2^7 pq -> 8, cutoff 6 -> 2 (hypothetical engine) | -11.9 | -15.2 | -13.4 | -15.5 | -14.5 | -13.5 |
| pair modes only (hypothetical engine) | — | -16.9 | -15.7 | -17.9 | — | -16.9 |

Reading the SJS column from the top:

| Step | Orders gained | What changes |
|---|---:|---|
| Free `D₀`, widths, `s/σ` | 19.0 | `lp_stopped_drift` fixes `D₀ = 1`, `s = σ = R/(16π)`; `E^{2(τ+1)}` punishes small `s` |
| Sharp `L` | 2.8 | `(I_min/2)⁴` and the sum over planets in `lpKeplerLip` |
| Tailored AMD ball | 6.3 | radius `C₀ + nr` instead of `B − δ/4`. The literal ball reaches 75% of the crossing threshold whatever `C₀` is. Strip 0.029 → 0.22 rad |
| Finite-cutoff divisors | 1.5 | `α(K)` instead of `γK^{−τ}` |
| Direct Fourier norm | 2.3 | `F` falls by 250: `coth(πσ)ⁿ` and the sup are replaced by the coefficients |
| Constant subtracted | 0.2 | |
| Hypothetical engine | 2.3 | constant 512 → 8, cutoff 6 → 2 |
| **Remaining at 5 Gyr** | **8.9** | |

The tail is structural: (W) has `F` where a resonance width has `f_k`. At the 5 Gyr optimum (`K = 495`, `s = 0.014`) the exponent `πKs/3` supplies only about 7 of the needed ln T ≈ 24. The prefactor `s r/(5ε)` supplies the other 17. So the exponential is barely in play at realistic horizons. For comparison, Barbieri–Niederman 2020
(A7 §3) reach ε = 10⁻¹¹·²⁵ at 5.75·10¹⁰ yr with a tailored single-block computation, in a different normalization. That sits at the hypothetical tier, which suggests the tier is honest and
that a norm-based single block saturates near 10⁻¹².

For n ≥ 3 the landed engine also inverts three-body divisors that `f` does not contain at first order: every mode of `f` has at most two nonzero indices. The
pair-only row is what that costs: 2 to 4 orders. The K grid stops at 160 for n = 4 and 1500 for n = 3. The JSUN optimum at the landed tier (K = 80) is interior; two intermediate tiers sit at the cap.

### 4.3 Very low masses

| log10 μ | T (yr) | K | r |
|---:|---:|---:|---:|
| -3 | — | — | — |
| -4 | — | — | — |
| -5 | — | — | — |
| -6 | — | — | — |
| -7 | — | — | — |
| -8 | — | — | — |
| -9 | — | — | — |
| -10 | — | — | — |
| -11 | 5.3e+05 | 90 | 6.3e-05 |
| -12 | 5.3e+06 | 90 | 6.3e-05 |
| -13 | 5.3e+07 | 90 | 6.3e-05 |
| -14 | 7.1e+08 | 377 | 1.1e-06 |
| -15 | 3.4e+14 | 1202 | 3.5e-07 |
| -16 | 1.3e+16 | 1202 | 3.5e-07 |
| -17 | 1.2e+31 | 3579 | 3.9e-08 |
| -18 | 4.8e+34 | 3579 | 3.9e-08 |
| -19 | 2.5e+36 | 3579 | 3.9e-08 |
| -20 | 1.4e+38 | 3579 | 3.9e-08 |
| -21 | 9.5e+65 | 8685 | 3.6e-10 |
| -22 | 8.7e+188 | 27682 | 1.1e-10 |
| -23 | 7.3e+298 | 88238 | 3.5e-11 |
| -24 | 7.3e+298 | 162999 | 1.9e-11 |

The mass-scaled SJS shape first gets any certificate at μ ≈ 10⁻¹¹, with T ≈ 5·10⁵ yr. Down to 10⁻¹⁴, T grows like 1/μ: this is the prefactor `s r/(5ε)`, not the exponential, and it is **below** Gronwall,
which already reaches 5 Gyr at 10⁻¹² where the engine gives 5·10⁶ yr. The exponential takes over between 10⁻¹⁴ and 10⁻¹⁵, which is about 10¹⁶ kg for a Sun-like star. The same map for 2 Earths compact starts at 10⁻¹⁴, and for 3 Earths wide at 10⁻¹⁸
(`results/E2c.json`, `results/E3w.json`). In the requested range μ = 10⁻⁶ to 10⁻¹²: none down to 10⁻¹⁰, 5·10⁵ yr at 10⁻¹¹, 5·10⁶ yr at 10⁻¹².

## 5. The Λ-only route

### 5.1 The argument and its Lean interface

`L` is exactly conserved, so `C(t) − C(0) = Σ(Λ_i(t) − Λ_i(0))` (LP Lemma 3). If `|Λ(t) − Λ(0)|_∞ ≤ r` up to T, and r fits the budget, then C(t) ≤ B(Λ(t)) − m and LP0 gives no crossing, whatever the eccentricities and inclinations do.

The interface already exists: `strongFirstExit_of_stopped_drift` (`KAM/Planetary/StrongAMD/Confinement.lean:170`, spatial twin in `KAM/Planetary/Spatial/Confinement.lean`). It takes exactly a stopped drift `hstop` plus
`n r + Ω_B(r) ≤ δ/4`, and returns existence, uniqueness and the barrier. No chart, no normal form and no Diophantine hypothesis is in its statement. LP1 discharges `hstop` with the engine; a Program C
certificate could discharge the same hypothesis instead. Note the helper's numbers: budget δ/4 and improved drift r/2, so the drift it asks for is `r_{δ/4}/2`, four times smaller than the
δ/2 budget below. That is 0.6 orders in μ at Gronwall level and a small edit to the helper.

The certificate must hold on the ball `Σ Γ ≤ C₀ + n r` at all phases, since nothing is assumed about the slow variables. On the stopped region the identity gives this containment automatically.

### 5.2 Budgets and elementary certificates

| System | r: n r+Ω_B ≤ δ/2 | δa/a of that r (innermost tightest) | r: n r+Ω_B ≤ δ/4 | r signed (δ/2) | r on energy shell (δ/2) | true osc. amp (μ sup ∂χ) |
|---|---:|---:|---:|---:|---:|---:|
| SJS, Standish axes | 1.48e-02 | 3.20e-02 | 7.45e-03 | 2.65e-02 | 4.16e-01 | 1.39e-03 |
| SJS, calibrated | 1.49e-02 | 3.22e-02 | 7.51e-03 | 2.68e-02 | 4.16e-01 | 2.05e-03 |
| SJS, spatial | 1.48e-02 | 3.20e-02 | 7.44e-03 | 2.65e-02 | 4.16e-01 | — |
| JSUN | 8.13e-04 | 8.12e-03 | 4.08e-04 | 9.70e-04 | 1.60e-03 | 1.50e-03 |
| JSUN, spatial | 7.92e-04 | 7.91e-03 | 3.97e-04 | 9.45e-04 | 1.55e-03 | — |
| 2 Earths wide | 2.49e-02 | 4.98e-02 | 1.26e-02 | 4.08e-02 | 4.50e-01 | 2.42e-06 |
| 3 Earths wide | 1.93e-02 | 3.86e-02 | 9.74e-03 | 2.75e-02 | 9.10e-02 | 5.66e-06 |
| 2 Earths compact | 1.45e-03 | 2.90e-03 | 7.26e-04 | 1.69e-03 | 4.50e-01 | 6.60e-05 |
| 3 Earths compact | 7.87e-04 | 1.57e-03 | 3.94e-04 | 8.59e-04 | 6.00e-03 | 1.60e-04 |
| HD 109271 | 6.38e-03 | 6.42e-02 | 3.24e-03 | 1.01e-02 | 8.93e-02 | 8.10e-05 |
| HD 1461 | 1.72e-03 | 1.36e-02 | 8.63e-04 | 2.61e-03 | 1.13e-01 | 2.81e-04 |
| HD 11964 | 8.08e-03 | 2.79e-01 | 4.04e-03 | 2.42e-02 | 2.42e-02 | 1.26e-04 |
| HD 69830 | 3.46e-03 | 4.38e-02 | 1.74e-03 | 4.92e-03 | 1.56e-02 | 2.75e-05 |

**(i) The margin δ** is Table A, column δ. **(ii) The allowed drift r** is the first column here, with `Ω_B(r) ≤ Lip(B) r` from the envelope gradient (**bounded** on the sampled tube). Three sharpenings:

- **Signed.** What erodes the margin is `Φ(I) = ΣI − B(I)`, since `C(t) − B(I(t)) = C(0) − B(I⁰) + Φ(I(t)) − Φ(I⁰)`. Up to 3× more room, and exact.
- **Energy shell.** `h(Λ) + μf` is exactly conserved, so Λ stays in a thin shell (thickness about `2μM`, ignored in that column; the search is capped at 0.45 I_min, which is what the values 0.416 and 0.45 are).
- **Per planet.** Needed for J-S-U-N, see below.

**J-S-U-N's sup-norm budget is smaller than the true oscillation.** r = 8.1·10⁻⁴ against an oscillation of Λ_J of about 1.5·10⁻³: the canonical Λ oscillates at O(μ) through the indirect term, and the margin is set by the light U–N pair. With per-planet radii the
20,000 yr excursions from direct integration fit, but only just: the worst-sign loss at the half-ranges is 0.0019 against δ/2 = 0.0040, leaving a factor 2.1. So JSUN needs `strongFirstExit_of_stopped_drift` generalized to a weighted drift (or to `ΣδΛ` directly), and its budget is thin.

**n = 2: the exact integrals do most of the work.** Along the energy curve, with C = C₀ + ΣδI:

| System | inward walk along the energy curve | outward walk |
|---|---|---|
| SJS, Standish axes | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 9.395 | margin closes at a₂ = 114.675 |
| SJS, calibrated | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 9.410 | margin closes at a₂ = 114.854 |
| SJS, spatial | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 9.392 | margin closes at a₂ = 114.675 |
| 2 Earths wide | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 2.186 | margin closes at a₂ = 6.149 |
| 2 Earths compact | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 1.175 | margin closes at a₂ = 4.358 |
| HD 109271 | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 0.182 | margin closes at a₂ = 0.397 |
| HD 1461 | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 0.097 | margin closes at a₂ = 0.377 |
| HD 11964 | AMD = 0 reached: excluded by the exact integrals alone at a₂ = 3.121 | margin closes at a₂ = 3.332 |

Inward motion is excluded for all time by `C ≥ 0` alone. Outward, the barrier survives until a₂ is far from its start (115 AU for SJS). This is Hill stability in AMD language, not new. So for n = 2 a certificate needs only a one-sided bound on the outer axis, which
relaxes the budget by a factor of about 100 at SJS (much less at HD 11964, see the table). It does not relax the time problem: such a tube crosses every resonance, so it helps Gronwall, not averaging.

**(iii) How hard is the drift bound?** Rates are in normalized action per time unit, all **estimated**.

| System | r budget | η for 5 Gyr at budget r | Gronwall T (yr) | first-order T (yr) | θ₁ | secular g | g / nearest divisor |
|---|---:|---:|---:|---:|---:|---:|---:|
| SJS, Standish axes | 1.48e-02 | 4.71e-13 | 5.3e+00 | 7.3e+00 | 0.30 | 1.41e-05 | 1.13e-02 |
| SJS, calibrated | 1.49e-02 | 4.75e-13 | 5.4e+00 | 7.4e+00 | 0.40 | 1.39e-05 | 2.32e-02 |
| JSUN | 8.13e-04 | 2.59e-14 | 1.4e+00 | 0.0e+00 | 1.33 | 1.44e-05 | 1.81e+00 |
| 2 Earths wide | 2.49e-02 | 7.93e-13 | 4.4e+02 | 1.7e+03 | 0.00 | 3.34e-07 | 1.94e-05 |
| 3 Earths wide | 1.93e-02 | 6.14e-13 | 2.8e+02 | 2.1e+03 | 0.00 | 3.56e-07 | 7.33e-04 |
| 2 Earths compact | 1.45e-03 | 4.61e-14 | 6.0e-01 | 6.4e-01 | 0.12 | 1.61e-05 | 5.10e-04 |
| 3 Earths compact | 7.87e-04 | 2.51e-14 | 2.5e-01 | 0.0e+00 | 0.71 | 3.29e-05 | 8.00e-01 |
| HD 109271 | 6.38e-03 | 1.98e-13 | 4.3e-01 | 1.7e-01 | 0.10 | 2.10e-04 | 2.94e-04 |
| HD 1461 | 1.72e-03 | 5.41e-14 | 2.6e-02 | 7.5e-02 | 0.26 | 2.94e-04 | 5.52e-04 |
| HD 11964 | 8.08e-03 | 2.43e-13 | 4.3e-01 | 1.9e+01 | 0.00 | 1.43e-06 | — |
| HD 69830 | 3.46e-03 | 1.19e-13 | 4.5e-01 | 1.4e+00 | 0.01 | 1.58e-04 | 2.16e-02 |

Gronwall gives a fraction of an orbit, as it must. Its point is the mass scaling: T ∝ 1/μ, hence the Gronwall column of Table C, reached with no normal form at all.

First-order averaging, `J = Λ + μ∂_iχ`, gives rate `μ²{∂_iχ, f}` on a tube free of low-order resonances. Uniformly on the ball, with product-of-sups bounds, it gains little at giant-planet masses (θ₁, the ratio of rates, is 0.3 to 1.3 there), because `∂_Λ∂_iχ` carries the double divisor. That
term and the slow bracket are of comparable size. In mass reach it beats Gronwall by 3 to 5 orders on wide systems and by almost nothing on compact ones, where the tube still holds unsolved modes.

### 5.3 Higher order with the actual coefficients

Norms are what kill the engine, so this drops them. `lambda_route.fast_newton` runs a Newton-type Lie normal form of one pair with the real coefficients: Fourier in the two fast angles, truncated Taylor in the actions from Cauchy circles, exact current frequencies
in the divisors, fixed μ. Slow variables are frozen. Each step removes the modes whose resonance lies outside the current displacement. Without that staging the first step fails at calibrated SJS, because the O(μ) displacement of Λ exceeds the distance to 5:2 (2·10⁻³ against 8·10⁻⁴).

Rows are the action rate at the sampled point after t steps. "Actual AMD" samples random perihelia at the published eccentricities. "Ball sphere" samples the sphere `C₀ + n·amp`.

| System | pair | samples | t=0 | 1 | 2 | 3 | 4 | 5 | 6 | samples not converged |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| SJS, calibrated | 0-1 | median, actual AMD | 5.0e-05 | 5.1e-07 | 5.1e-08 | 3.7e-10 | 2.0e-14 | 1.1e-23 | 3.4e-39 | 2/10 |
| SJS, calibrated | 0-1 | worst, ball sphere | 8.9e-05 | 2.8e-06 | 2.4e-06 | 1.3e-05 | 7.6e-05 | 1.3e-01 | 3.3e+03 | 2/10 |
| JSUN | 0-1 | median, actual AMD | 4.8e-05 | 3.3e-07 | 8.1e-09 | 2.9e-12 | 2.9e-19 | 2.0e-34 | 9.2e-50 | 0/10 |
| JSUN | 0-1 | worst, ball sphere | 7.2e-05 | 1.6e-06 | 2.4e-07 | 3.4e-09 | 8.2e-13 | 2.8e-20 | 1.3e-34 | 0/10 |
| JSUN | 1-2 | median, actual AMD | 1.3e-06 | 1.8e-09 | 3.0e-14 | 5.4e-23 | 3.0e-38 | 1.1e-53 | 5.1e-69 | 0/10 |
| JSUN | 1-2 | worst, ball sphere | 6.5e-06 | 1.7e-07 | 9.9e-09 | 1.1e-10 | 1.2e-14 | 1.6e-21 | 1.6e-35 | 0/10 |
| JSUN | 2-3 | median, actual AMD | 2.0e-07 | 1.3e-08 | 1.2e-11 | 1.7e-16 | 1.2e-26 | 5.5e-42 | 2.6e-57 | 3/10 |
| JSUN | 2-3 | worst, ball sphere | 1.8e-06 | 9.4e-07 | 1.5e-06 | 4.7e-06 | 4.8e-05 | 7.8e-02 | 4.3e+05 | 3/10 |
| 2 Earths wide | 0-1 | median, actual AMD | 1.7e-06 | 1.2e-11 | 3.3e-21 | 5.1e-36 | 2.4e-51 | 1.2e-66 | 5.7e-82 | 0/10 |
| 2 Earths wide | 0-1 | worst, ball sphere | 1.7e-06 | 1.2e-11 | 3.6e-21 | 5.8e-36 | 2.7e-51 | 1.5e-66 | 8.2e-82 | 0/10 |
| 2 Earths compact | 0-1 | median, actual AMD | 2.0e-05 | 4.4e-08 | 8.4e-13 | 2.9e-21 | 8.9e-37 | 3.6e-52 | 1.3e-67 | 0/10 |
| 2 Earths compact | 0-1 | worst, ball sphere | 5.4e-05 | 1.2e-07 | 1.7e-11 | 1.8e-18 | 6.6e-32 | 3.1e-47 | 1.0e-62 | 0/10 |
| HD 1461 | 0-1 | median, actual AMD | 2.0e-03 | 9.2e-05 | 3.8e-05 | 1.8e-05 | 3.5e-04 | 3.2e-02 | 2.3e+05 | 7/10 |
| HD 1461 | 0-1 | worst, ball sphere | 2.1e-03 | 1.1e-04 | 6.8e-05 | 2.0e-04 | 6.7e-04 | 3.7e+05 | 3.1e+06 | 7/10 |
| HD 11964 | 0-1 | median, actual AMD | 1.0e-04 | 2.8e-08 | 2.0e-15 | 3.3e-29 | 3.2e-44 | 1.5e-59 | 7.7e-75 | 0/10 |
| HD 11964 | 0-1 | worst, ball sphere | 2.7e-04 | 1.5e-07 | 5.3e-14 | 2.3e-27 | 8.5e-43 | 3.8e-58 | 1.8e-73 | 0/10 |
| HD 69830 | 0-1 | median, actual AMD | 2.1e-04 | 1.1e-07 | 1.3e-13 | 1.9e-24 | 8.3e-40 | 4.3e-55 | 1.8e-70 | 0/10 |
| HD 69830 | 0-1 | worst, ball sphere | 2.7e-04 | 4.9e-07 | 3.5e-12 | 2.1e-21 | 9.9e-37 | 3.9e-52 | 1.5e-67 | 0/10 |
| HD 69830 | 1-2 | median, actual AMD | 1.5e-04 | 1.4e-08 | 2.2e-16 | 1.3e-30 | 5.9e-46 | 2.9e-61 | 1.1e-76 | 0/10 |
| HD 69830 | 1-2 | worst, ball sphere | 1.7e-04 | 1.8e-08 | 3.3e-16 | 2.3e-30 | 1.1e-45 | 6.6e-61 | 2.4e-76 | 0/10 |

On the actual AMD level the series converges at actual masses in every system but HD 1461: SJS reaches 10⁻¹⁴ in 4 steps. One step is worth a factor of 100 at Jupiter mass and 10⁵ at Earth mass.

### 5.4 Resonances

| System | records (order: k, |k·ω|, action distance) | divisor with first-order shift; strength; converged (actual, sphere) | closure 1 Myr (r, K) | closure 1 Gyr | closure 5 Gyr (r, K, rate) | with effective ω, 5 Gyr |
|---|---|---|---|---|---|---|
| SJS, Standish axes | 3: (1, -2), 1.6e-02, 4.9e-02; 7: (2, -5), 1.3e-03, 1.6e-03 | 1.80e-03–1.81e-03; strength 0.00 (actual), 0.05 (sphere); converged 5/5, 5/5 | 2.2e-04, 75 | 4.5e-06, 124 | 4.5e-06, 131, 1.4e-16 | 7.1e-06, 129 |
| SJS, calibrated | 3: (1, -2), 1.7e-02, 5.0e-02; 7: (2, -5), 6.0e-04, 7.8e-04 | 1.15e-03–1.16e-03; strength 0.02 (actual), 0.48 (sphere); converged 5/5, 3/5 | 3.5e-04, 73 | 3.5e-04, 104 | 3.2e-04, 111, 1.0e-14 | 1.3e-05, 126 |
| JSUN | 16: (2, -3, 0, -11), 5.1e-05, 4.2e-05; 17: (2, -6, 5, -4), 1.8e-05, 8.9e-06; 21: (2, 1, -16, -2), 8.0e-06, 2.4e-06 | — | 5.6e-07, 223 | 5.6e-07, 306 | 5.6e-07, 325, 1.8e-17 | — |
| 2 Earths wide | 4: (1, -3), 7.3e-02, 1.5e-02; 17: (4, -13), 1.7e-02, 8.5e-04 | 1.73e-02–1.73e-02; strength 0.00 (actual), 0.00 (sphere); converged 5/5, 5/5 | 4.0e-04, 34 | 4.0e-04, 54 | 1.6e-04, 61, 5.0e-15 | 1.6e-04, 61 |
| 3 Earths wide | 11: (2, -7, 2), 5.4e-03, 5.0e-04; 17: (1, 1, -15), 1.1e-03, 2.0e-04; 39: (6, -14, -19), 4.9e-04, 1.7e-05 | — | 5.6e-04, 34 | 2.0e-05, 64 | 2.0e-05, 68, 6.4e-16 | — |
| 2 Earths compact | 9: (4, -5), 8.3e-02, 3.6e-03; 16: (7, -9), 5.1e-02, 1.3e-03; 25: (11, -14), 3.2e-02, 5.0e-04 | 3.15e-02–3.15e-02; strength 0.00 (actual), 0.00 (sphere); converged 5/5, 5/5 | 2.0e-06, 302 | 2.0e-06, 403 | 2.0e-06, 426, 6.4e-17 | 2.8e-06, 421 |
| 3 Earths compact | 15: (5, -8, 2), 3.4e-03, 9.6e-05; 25: (10, -3, -12), 5.8e-04, 1.0e-05; 39: (2, -18, 19), 4.1e-05, 5.4e-07 | — | 1.6e-07, 425 | 1.6e-07, 548 | 1.6e-07, 577, 5.0e-18 | — |
| HD 109271 | 5: (1, -4), 7.2e-01, 7.2e-04 | 7.20e-01–7.21e-01; strength 0.00 (actual), 0.00 (sphere); converged 5/5, 5/5 | 2.5e-06, 106 | 2.5e-06, 137 | 2.5e-06, 144, 7.8e-17 | 3.5e-07, 153 |
| HD 1461 | 3: (1, -2), 9.1e+00, 7.0e-03; 7: (2, -5), 8.6e+00, 3.0e-03; 10: (3, -7), 5.3e-01, 1.3e-04 | 5.21e-01–5.22e-01; strength 0.35 (actual), 0.44 (sphere); converged 1/5, 2/5 | 2.5e-07, 388 | 2.5e-07, 487 | 2.5e-07, 510, 7.9e-18 | 1.6e-07, 517 |
| HD 11964 |  | — | 2.5e-03, 38 | 5.0e-06, 69 | 5.0e-06, 73, 1.5e-16 | — |
| HD 69830 | 7: (1, -4, 2), 4.8e-01, 3.4e-04; 8: (1, -3, -4), 7.3e-03, 5.7e-06 | — | 6.3e-06, 90 | 6.3e-06, 119 | 6.3e-06, 126, 2.2e-16 | — |

"Strength" is the shift of the record divisor once its mode is solved, relative to the divisor. Well below 1, the mode is a perturbation. Near 1, width and distance are comparable and a plain step fails.

**Jupiter–Saturn 5:2.** Three separate facts:

1. **The divisor itself is stable.** With the first-order shift it is −0.00115 across the whole ball, matching the true −0.00113.
2. **On the actual AMD level the 5:2 term is weak**, strength 0.02, and all samples converge.
3. **On the ball sphere it is not.** At anti-aligned perihelia with e_S ≈ 0.11, the strength reaches 0.48 and 2 of 5 samples fail. There, solving the mode moves the divisor by half of itself. The third-order amplitude has grown by about 8 from its value at e_S = 0.054.

So a non-resonant certificate can hold on the observed secular state but not on the full AMD ball. Since the point of the route is to assume nothing about the slow variables, a whole-ball certificate must keep the 5:2 harmonic in the normal form. Then
`5Λ_J + 2Λ_S` is the approximate integral and energy confines the conjugate direction, with a width of order `√(μ f_k/ℓ_k)`, around 10⁻⁴, well inside the budget. That is the LP3 mechanism, done with coefficients instead of norms. It is more work, not a new obstruction.

A second fix is cheaper if acceptable: restrict the ball by an extra certified bound on `e_S`. That is exactly the secular assumption this route avoids, so it needs an owner decision.

**Other near-resonances.** HD 1461's 7:3 fails even on the actual AMD (strength 0.35), at the source's upper-limit eccentricities. U–N near 2:1 diverges on part of the ball in 3 of 10 samples. HD 109271's near 4:1 is harmless (strength 0.00), because the large divisor keeps the mode weak.

**What binds is the tube, not the AMD.** Modes that matter at rate r/T must have no resonance in the tube. Closure of that condition gives tubes 160 to 18,000 times smaller than the budget. Any r ≤ the tube works, and the tube is in the normal-form action J, not in Λ, so
it can be far smaller than the true oscillation of Λ. Closure varies strongly with arithmetic: the table's last column uses the shifted ω, the fourth to sixth the canonical ω, and 5 Gyr tubes differ by up to 25× for SJS. Treat r and K as order-of-magnitude.

### 5.5 What a certificate needs

| System | rate needed (closure) | tube r | modes up to K | Newton steps, actual AMD | Newton steps, ball sphere | budget r / tube r |
|---|---:|---:|---:|---:|---:|---:|
| SJS, Standish axes | 2.3e-16 | 7.1e-06 | 129 | 4 | 5 | 2.1e+03 |
| SJS, calibrated | 4.0e-16 | 1.3e-05 | 126 | 5 | diverges at some points | 1.2e+03 |
| JSUN | 1.8e-17 | 5.6e-07 | 325 | 4 | diverges at some points | 1.4e+03 |
| 2 Earths wide | 5.0e-15 | 1.6e-04 | 61 | 2 | 2 | 1.6e+02 |
| 3 Earths wide | 6.4e-16 | 2.0e-05 | 68 | 2 | 2 | 9.7e+02 |
| 2 Earths compact | 9.0e-17 | 2.8e-06 | 421 | 3 | 3 | 5.1e+02 |
| 3 Earths compact | 5.0e-18 | 1.6e-07 | 577 | 4 | 4 | 5.0e+03 |
| HD 109271 | 1.1e-17 | 3.5e-07 | 153 | 4 | 4 | 1.8e+04 |
| HD 1461 | 5.0e-18 | 1.6e-07 | 517 | no convergence | diverges at some points | 1.1e+04 |
| HD 11964 | 1.5e-16 | 5.0e-06 | 73 | 3 | 3 | 1.6e+03 |
| HD 69830 | 2.2e-16 | 6.3e-06 | 126 | 3 | 3 | 5.5e+02 |

**What these estimates leave out:**

1. **Slow coupling.** Frozen slow variables hide the term `∂_zχ·ż`, of relative size g/|k·ω| per order (Table E: 0.02 at SJS for 5:2, 10⁻³ and below for the main modes). That turns the Newton gain back into a linear one, so expect 5 to 6 ordinary orders at SJS rather than the steps shown. Rough estimate: mode (2,−5), rate 10⁻⁷, needs 4–5 orders to pass 10⁻¹⁶.
2. **Other planets.** One pair at a time. Three-body modes enter at second order, and J-S-U-N's three-planet near-commensurabilities are the known source of chaos in the outer system (Murray–Holman 1999, from memory, not re-checked here). Its K ≈ 325 is the least reliable row.
3. **Sampled sups.** 10 points are not a sup on a ball. Worst cases can be worse.
4. **Uniformity.** This is the main cost. The bound must hold on `n + 2n` real dimensions (planar) or `n + 4n` (spatial), with K ≈ 60 to 130 Fourier modes per direction. Pair structure brings a first-order term down to 6 dimensions. A polynomial in the slow variables needs degree about `|k₁+k₂|`,
   so a near-5:2 mode at |k| ≈ 130 needs degree ≈ 55. That is `C(59,4) ≈ 4.6·10⁵` coefficients for one harmonic, which is out of reach as polynomials and points to subdivision or Bessel-type bounds. By contrast, a wide low-mass pair at K ≈ 60 with e ≲ 0.03 has small harmonics at low degree.

No kernel cost was measured. Program C's rule stands: quote a kernel estimate only after a measured shard.

## 6. Recommendation

**Quantitative LP (engine route): no.** Not for planets, compact or wide. It starts to beat Gronwall only for bodies below about 2·10¹⁵ kg (μ ≈ 10⁻¹⁵). Do not freeze or build a certifier on the constants of LP1, LP2 or LP3.

**LP as endpoint: yes.** LP0, the threshold lemmas and `strongFirstExit_of_stopped_drift` are the valuable part: exact, cheap, and independent of averaging. Add exact-rational B lower bounds (tangent certificate) and a weighted-budget variant.

**Λ-only drift certificate: pilot it**, in this order. It is the Program C route with `n` observables plus exact `L`, and no secular model.

1. **Elementary instance.** A Gronwall certificate end to end, at a mass where it closes. It exercises the chain and proves nothing physical. Cost: small.
2. **Two wide low-mass planets at first or second order**, on the whole AMD ball. This decides the uniformity cost above with real measurements. If it fails here, stop.
3. **HD 11964** (μ = 5·10⁻⁴, C/B = 0.16, K ≈ 73, 3 steps): the most promising real target, subject to the data caveats. Spatial AMD and true masses are not pinned.
4. **SJS, on a horizon ladder** starting at 10⁴ to 10⁶ yr (K ≈ 72 at 1 Myr, tube 4·10⁻⁴), then a resonant 5:2 block.

Each step reports a certified T against the budget, so a failure is still a measured curve.

**Improvements that could change the verdict, and their cost** (estimates; gains are for SJS at 5 Gyr):

| Improvement | Gain | Cost | Changes the verdict? |
|---|---:|---|---|
| Parametrize `D₀` and widths in `lp_stopped_drift` | 19 orders | small Lean; but needs certified `R`, `M` | no |
| Sharp `lpKeplerLip` | 2.8 | one lemma | no |
| Ball as a parameter of drift and first exit | 6.3 | small Lean | no |
| Finite divisors instead of (5) | 1.5 | small Lean, finite check | no; removes the unverifiable hypothesis |
| Certified `M` by subdivision | enables the above | large numerics; 8 real dimensions per pair | no |
| Direct Fourier norm | 2.3 | large: certified aliasing and subdivision | no |
| New normal form lemma, sharper constants | 2.3 | months | no: ends near 10⁻¹² |
| Pair-only divisors, n ≥ 3 | 2–4 | new engine variant | no |
| Coefficient-aware first-order drift (Program C) | to about 10⁻⁸ | new checker | yes, for short horizons and low masses |
| Higher-order, whole-ball drift, with resonant block | to actual masses, per Table H | large, unknown: the uniformity cost | yes, if the pilot closes |

## 7. Owner questions

Conservative option taken in each case; nothing blocked.

1. **Whole-ball or secular-restricted?** For SJS a certificate on the observed AMD level looks far easier than on the whole ball, but needs a certified bound on `e_S`, i.e. a secular input. Taken: whole ball, as the brief's logic requires.
2. **Weighted budget.** May the LP lane generalize `strongFirstExit_of_stopped_drift` to per-planet radii and to the budget δ/2? Needed for JSUN. Taken: reported only; `docs/tracks/LP/**` and `KAM/Planetary/StrongAMD/**` untouched.
3. **Which data?** No enclosure was pinned for any system. Exoplanet masses are minimum masses and spatial AMD is unknown. Taken: nominal values, labelled.
4. **Is Program C's first instance this one?** This study suggests replacing the secular models with the Λ-only observables for the first planetary target. Taken: recommendation only.

## 8. Errata, deviations, uncertainties

**Errata in pinned sources: none found.** Every formula used from MAIN checked out, and the mirror of `lp_scale_choice` passes. Remarks, not defects: `c_D` in Lemma 10 is implicit (audit N5); at `μ = μ₀` the exponent is ≈ 1 by construction (section 2.1).

**A finding about hypothesis (5).** Published periods are decimals, so their ratio is exactly rational. HD 109271's input has an exact relation at `k = (26181, −103100)`: literally, γ = 0 and the theorem is vacuous for the data as published. `γ` here is the minimum up to |k| = 2·10⁴, standing for a Diophantine vector selected nearby.

**Deviations from the brief.** None in scope. Additions: the first-order and Gronwall columns, the calibrated SJS row. Spatial chain only for SJS and JSUN; the Λ route is planar throughout. The Lean literal route takes `A` to be a single point, so uncertainty boxes are not costed.

**Uncertainties.**

- `M` and `F` are sampled sups, hence lower estimates of the true sup. Every μ here is therefore an **optimistic** estimate for the LP routes, which only strengthens the negative verdict. Rates in section 5 are lower estimates too, which **weakens** the positive one.
- `γ` is an upper estimate, optimistic again.
- `q_D = 1/(96eD)` in route P assumes `c_D` does not bind.
- Newton staging and truncation (degree 12, N = 96, |k| ≤ 32 per angle) are numerical choices. The rates at t ≥ 5 are near what that resolution can support, and modes beyond the filter are not in the Newton rows (they are in Table F's tail).
- An earlier draft of this analysis read frequencies from non-converged samples and reported a spread of the 5:2 divisor over the ball. That spread was an artefact and is corrected in section 5.4.
- Run history: `run_all.py`, then `newton_only.py`, `reach.py`. Chain results all come from the final `chain.py`.

## 9. Reproduce

Heavy runs use the memory cap. From the repository root:

```sh
CAP="systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10"
$CAP python3 -I scripts/lp_quant/run_all.py --procs 8      # about 15 min; writes results/<key>.json
$CAP python3 -I scripts/lp_quant/newton_only.py --procs 7  # staged Newton, about 10 min
$CAP python3 -I scripts/lp_quant/reach.py                  # Gronwall and first-order reach
python3 -I scripts/lp_quant/report.py                      # results/summary.md, all tables, more rows than here
$CAP python3 -I scripts/lp_quant/check.py                  # self-checks
```

numpy and mpmath only. The chain rerun used 0.43 GB in total when measured.

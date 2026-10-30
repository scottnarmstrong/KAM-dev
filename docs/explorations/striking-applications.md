# Striking applications of a formally verified KAM certifier

30 October 2026. Feasibility study (brief APPS-SCOUT). Nothing here is a theorem or a certificate: the tori are double-precision
numerics, and every cost is a projection. All numbers come from `scripts/apps_scout/` (see Reproduction, §15).

## 1. Summary

- **The best target is the Moon's lock, at the true parameters.** A rigorous librational torus around the synchronous orbit is published
  only for ε about 5 times smaller than the Moon's (Celletti 1994). We computed such tori at the true ε, from 5° to 72° of libration. Under v1 they
  need about 40 digits and 4k Fourier modes, and one torus suffices.
- **Librational tori need no new KAM theorem.** In a polar chart around the synchronous orbit they are primary tori. The only new
  infrastructure is a `sqrt` primitive in `HamExpr` and a short chart lemma. The earlier notes assumed a normal form or a new G1.
- **Mercury's 3:2 resonance costs about the same as the Moon.** It has the same 3 full-precision products, and it works with the theorem we already
  have. We found no rigorous KAM statement for it at Mercury's true parameters. This is the cheapest high-value result, but one paper must be
  read first (§5.1).
- **Exact Kepler forcing needs no Kepler-equation analytics.** The eccentric-anomaly chart makes the exact spin–orbit forcing a rational `HamExpr`, using
  only the existing `div`. The bands agree with the truncated model to five digits. This removes an item from the brief's infrastructure list.
- **12 Victoria is within reach in Celletti–Chierchia's truncated model** (about 34 digits, 1.1k modes). The exact, untruncated restricted problem at the
  true mass ratio also converges numerically, at e up to 0.22 and also near L4 for Trojans, but it costs hundreds of CPU-hours per torus.
- **Sun–Jupiter–Saturn is infeasible in the kernel** by about 4 orders of magnitude in support, and about 6 in cost.
- **"Best in class" is not yet true against PlasmaLean.** On its own example PlasmaLean's proved tolerance is 10^−18.2. Our v1 at comparable data is
  10^−25 to 10^−30, and my v2 estimate is 10^−21 to 10^−24. Its theorem is much narrower, but the gap is real and has an identified cause (§8).

## 2. Ranked table

Thresholds are log₁₀ of the invariance error needed. "v2" is my estimate (§14), since SHARP-PLUS has no numbers yet. CPU-h is the whole theorem (2 tori for
rotational and asteroid barriers, 1 for a librational trap) at tier P, the SO-PACKFIX projection: **shard kernel time only**, not yet measured
for composition, Gram and torsion. Verdicts: *now* = the sealed theorem plus the SO pipeline; *after v1* = the sharp theorem being proved.

| # | Application | Theorem needed | log₁₀ e: cur / v1 / v2 | L v1 | S v1 | CPU-h: cur / v1 | Verdict | Time after prerequisites |
|---|---|---|---:|---:|---:|---:|---|---|
| 1 | **Moon locked forever**: true ε, one librational torus, 8.8° | iso, primary in polar chart + `sqrt` | −160 / −35 / −31 | 41 | 3.9k | 300–590 / 13–26 | **after v1** | 3–5 weeks |
| 2 | **Mercury's 3:2 trapped**: true e, ε; band ±0.0173 | iso, primary | −75 / −26 / −21 | 33 | 2.5k | 30–58 / 12–24 | **now** | 1–2 weeks |
| 3 | **12 Victoria confined**, CC07 truncated model | iso, primary + `sqrt` | −115 / −27 / −22 | 33 | 1.1k | 580–1140 / 28–53 | **after v1** | 3–4 weeks |
| 4 | **Moon spin band 2.65 %** (floor 2.617 %) | iso, primary | −111 / −36 / −28 | 43 | 3.5k | 48–92 / 12–23 | **now**; cheap after v1 | 1–2 weeks |
| 5 | **Golden circle of the standard map, k = 0.970** | maps a-posteriori theorem | n/a / ≈ −29 / – | 39 | 37k | n/a / 50–95 | **needs new theorem** | 6–9 weeks |
| 6 | Exact PCR3BP at the true mass ratio, e ≤ 0.22 | iso, primary + `sqrt` | −150 / −39 / −32 | 46 | 20–40k | 7k+ / 330–1300 | **after v2**, heroic | 2–3 months |
| 7 | Jupiter Trojans, exact PCR3BP, D ≤ 25° | iso, primary + `sqrt` | −167 / −43 / −35 | 49 | 18k | 12k+ / 490–950 | **after v2**, heroic | 2–3 months |
| 8 | Saturnian moons: rotational; Rhea librational | iso, primary | −76 / −25 / −21 | 32 | 0.8k | 10–20 / 4–8 | **now** | 1 week after #2 |
| 9 | Tokamak field-line barrier | iso, primary | −101 / −30 / −25 | 38 | 5.3k | 140–280 / 17–33 | **after v1** | 2 weeks |
| 10 | Hill's lunar problem, true m | iso, primary + `sqrt` | −175 / −51 / −43 | 59 | 27k | 6k+ / 350–680 | **after v2**; a better chart first | 2–3 months |
| 11 | Exact vacuum stellarator (PlasmaLean's example) | non-canonical form | – | – | ≈ 3k | – | **needs new theorem** | 2–3 months |
| 12 | Froeschlé map, n = 2 | maps theorem | see §7 | – | – | – | **needs new theorem** | after #5 |
| 13 | Planar Sun–Jupiter–Saturn | iso/first integrals, n = 3 | ≈ −75 at best | ≈ 85 | 10⁸ | ≥ 10⁷ | **infeasible in the kernel** | – |

Hénon–Heiles and galactic models are unranked: my continuation failed there, so I have no numbers (§12).

## 3. Why these rankings differ from the brief's expectations

Three findings changed the list.

**Polar charts make librational and Trojan tori primary.** Take any elliptic orbit and write the pair (Q, P) around it as
Q = a√(2I) sin 2πθ, P = √(2I)/a cos 2πθ, with a free scale a. This chart is exactly symplectic and explicit. A torus that winds once around the orbit is
then a primary torus in (θ, φ), and `IsPrimaryOnStrip` holds. So "librational, not available" in the brief should read "available, given `sqrt`". The same
device handles the radial oscillation of an asteroid with no Kepler equation, and Trojans with the exact polynomial shear r = ρ + G², θ = θ̃ + 2Gp.

**Exact Kepler forcing is an expression.** Kepler's equation is only hard in the direction ℓ ↦ u. The map φ = w − (e/2π) sin 2πw, J = U/(1 − e cos 2πw) goes the
easy way and is symplectic. On the level H = 0, the orbits of H are those of H̃ = ρH, with ρ = 1 − e cos 2πw = r/a. Every forcing term is then rational in cos 2πw and
sin 2πw, with the constant √(1 − e²), which is rational for a suitable e. The Lean work is a time-change lemma of a few hundred lines, not an analytic theory.

**Kernel cost is now a known scale.** SO-PACKFIX brought one heavy shard from OOM above 13.6 GB to 4.55 GB. Its projection is 15–29 CPU-h for both lunar tori. I use
7.5–14.5 CPU-h per torus as the unit (§14). At that price everything with N_full small and S below about 10⁴ is cheap, and cost is dominated by the count
of full-precision products rather than by digits.

## 4. Moon: permanent lock, and the spin band

### 4.1 Permanent synchronous lock (rank 1)

- **Model.** The seven-term model of the SO proposal §2.3 (e = 0.0549, ε = 3.45·10⁻⁴), in extended phase space on H = 0. The exact-Kepler model of §3 is a drop-in option.
- **Statement.** There is a real-analytic invariant 2-torus 𝒯, a polar graph around the synchronous orbit in (ψ, p, φ), ψ = q − φ, such that every solution
  starting inside 𝒯 exists for all t ∈ ℝ and satisfies, for all t, |2πψ(t)| ≤ 8.8° and |p(t) − 1| ≤ 0.0041. In words: the same face stays toward the Earth forever, in this model.
- **Why striking.**
  - Astronomers: this is the classical question, at the true parameters, and the angle itself is bounded, not only the spin rate.
  - Mathematicians: a KAM result at a true parameter where the published proof falls short by a factor of 5.
  - Formal methods: a kernel-checked statement anyone can state in one line.
- **Published.**
  - Celletti, ZAMP 45 (1994) 61–80, abstract: for the Moon, "the existence of trapping orbits for values of the perturbing oblateness parameter far from the real physical value by a factor ∼ 5"; for Rhea,
    "consistent with the astronomical measurements".
  - Her survey (mp_arc 07-303, §6.3): "a libration of 8°.79 for any ε ≤ ε_obs/5.26".
  - Celletti–Chierchia, RCD 3 (1998): the synchronous periodic orbit exists up to ε₀ = 7.1·10⁻⁴ at e = 0.0549 (Table 2); surrounding KAM surfaces only for "suitably small" parameters.
  - I found no later rigorous result at the true ε. This was a targeted search, not exhaustive. The 1994 paper itself is paywalled: I read the abstract and the survey, not the full text.
- **Theorem needed.** Isoenergetic, primary, in the chart. One torus suffices: it bounds a solid torus in the three-dimensional level.
- **Data** (chart scale a = 2.466, one torus, τ = 1, n = 2):

| Amplitude | ν | γ | width θ, φ | log₁₀ e cur / v1 / v2 | L cur / v1 / v2 | S cur / v1 / v2 | CPU-h cur / v1 |
|---:|---:|---:|---|---:|---:|---:|---:|
| 5.3° | 0.026113 | 0.0252 | 0.345, 0.448 | −172 / −37.3 / −33.3 | 182 / 44 / 40 | 74k / 4.3k / 3.6k | 350–670 / 15–28 |
| 8.8° | 0.026015 | 0.0251 | 0.304, 0.460 | −160 / −35.1 / −30.9 | 173 / 41 / 38 | 67k / 3.9k / 3.2k | 300–590 / 13–26 |
| 21.6° | 0.025241 | 0.0244 | 0.254, 0.488 | −131 / −31.2 / −27.1 | 144 / 38 / 34 | 53k / 3.6k / 3.0k | 210–410 / 13–26 |
| 46.4° | 0.021921 | 0.0212 | 0.171, 0.489 | −120 / −33.7 / −27.3 | 133 / 40 / 34 | 58k / 5.2k / 3.9k | 225–430 / 19–36 |
| 72.3° | 0.015719 | 0.0152 | 0.122, 0.500 | −113 / −40.1 / −31.2 | 123 / 47 / 38 | 67k / 9.8k / 6.3k | 250–480 / 32–62 |

  Each torus is a polar graph (min(1 + ∂u/∂θ) = 0.97–0.38) with the action away from 0 (X_min/X_mean > 0.74). The smallest cost is near 20°; smaller tori get weaker twist in scaled units. By the trend, 2° should need about 50 digits; I did not compute it.
- **New Lean.**
  - `HamExpr.sqrt` with its jet rule, ball arithmetic and a witness s² = b. PlasmaLean's `PolyExprS` isqrt node is a working template. About 1–1.5k lines, in new files.
  - Chart lemma: a torus of H∘Φ gives a torus of H. About 300 lines.
  - Single-torus trap: the interior of a polar graph is invariant, using `gen_barrier`. About 500–1000 lines.
- **Verdict: after v1.** The current theorem would need about 170 digits and 67k modes, which is out of range; v1 makes it routine. Timeline: 3–5 weeks after `KAM.Iso.Sharp.g1_sharp` and SHARP-A8.

### 4.2 Rotational band (rank 4)

- **Statement.** Two invariant graphs enclose every orbit with p(0) in an explicit window, and |p(t) − 1| ≤ b for all t.
- **Published.** Celletti 1990 (ZAMP 41, 174–204): tori trapping the resonance "for the natural values of the physical and orbital parameters". Benchmark band ≈ 3 % (`lunar-band-2p8-2p9.md`).
- **Data** (the barrier's max|p − 1| before certified margins; one torus; multiply CPU-h by 2):

| N in 1 ± 1/(N+g) | Band | γ | width ψ | log₁₀ e cur / v1 / v2 | L cur / v1 / v2 | S cur / v1 / v2 | CPU-h cur / v1 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 40 | 3.199 % | 0.0238 | 0.213 | −74 / −25.6 / −20.3 | 85 / 32 / 27 | 8.0k / 1.1k / 0.8k | 7–14 / 3–6 |
| 50 | 2.901 % | 0.0191 | 0.183 | −80 / −27.7 / −22.1 | 93 / 35 / 29 | 11k / 1.5k / 1.0k | 10–19 / 4–7 |
| 60 | 2.755 % | 0.0159 | 0.155 | −90 / −31.2 / −23.5 | 101 / 37 / 30 | 15k / 2.1k / 1.4k | 13–25 / 4–8 |
| 80 | 2.652 % | 0.0120 | 0.121 | −111 / −36.4 / −27.9 | 121 / 43 / 34 | 28k / 3.5k / 2.2k | 24–46 / 6–11 |
| 100 | 2.630 % | 0.0096 | 0.097 | −131 / −43.2 / −31.2 | 143 / 49 / 38 | 47k / 5.6k / 3.3k | 42–82 / 8–15 |
| 120 | 2.626 % | 0.0080 | 0.082 | −156 / −48.9 / −35.9 | 167 / 56 / 42 | 75k / 8.4k / 4.8k | 72–139 / 10–20 |

- This goes further than `lunar-band-2p8-2p9.md` proposed. The band reaches 2.65 % at N = 80, not 2.8–2.9 %, and the floor is 2.617 %. Beyond N = 80 the gain is below 0.03 points, so N = 80 is the natural stop.
- **Verdict: now, cheap after v1.** N = 60 is affordable under the current theorem (26–50 CPU-h); N = 80 is 48–92. Certified margins add about 0.1 point.

## 5. Mercury and the Saturnian moons

### 5.1 Mercury's 3:2 resonance (rank 2)

- **Model.** The spin–orbit equation at e = 0.2056, ε = 1.5·10⁻⁴ (Celletti–Chierchia 1998, Table 1), resonance p = 3/2, with exact Hansen coefficients (32 modes above 10⁻¹⁴, computed by FFT; rationalized for Lean) or the exact Kepler form of §3.
- **Statement.** Two invariant graphs trap the 3:2 resonance: for p(0) in an explicit window, |p(t) − 3/2| ≤ 0.0174 for all t. The separatrix half-width is 0.0140.
- **Why striking.** Mercury is the only body in a 3:2 spin–orbit lock, and it is the textbook case. It also uses e = 0.2, far from the Moon's small-eccentricity regime.
- **Published.**
  - Celletti–Chierchia 1998, Table 2: at Mercury's e, a 3:2 periodic orbit was proved only for ε ≤ 5.7·10⁻⁶, about 26 times below the physical value: "the existence of the three main resonances cannot be proved for 'realistic' values of the parameters".
  - Celletti 1990 Part II (ZAMP 41, 453–479): an abstract fragment mentions "remarks on higher order resonances and on the Mercury-Sun system". I could not read it. **Read this paper before any priority claim.**
  - Celletti–Chierchia 2000 is numerical, per `realistic-kam-and-finite-size.md`.
- **Data** (N = 74 / 89, one torus; multiply CPU-h by 2): γ = 0.0129 / 0.0108; widths 0.225 / 0.197 in ψ and 0.183 in φ. log₁₀ e: −75 / −26.4 / −21.3 at N = 74. L 87 / 33 / 28. S 17k / 2.5k / 1.7k. CPU-h 15–29 / 6–12.
- **N_full = 3**, the same as the Moon: all 32 modes are shifts of one character witness (traced by `count_products.py`).
- **Exact Kepler variant** (N = 74): same band to 5 digits; log₁₀ e −136 / −37.3 / −28.6, L 147 / 44 / 35, S 37k / 3.4k / 2.1k, N_full ≈ 9, CPU-h 93–181 / 8–16. Under v1 the exact model is affordable; under the current theorem it is not.
- **New Lean.** Almost none for the Hansen model: a new `HamExpr` and data. The Kepler form adds the time-change lemma.
- **Verdict: now.** Timeline: 1–2 weeks after SO-DATA-2 closes, because the generator and checker are unchanged.
- **Caveat.** ε is uncertain. From memory (unverified) recent geodesy gives ε ≈ 1.3·10⁻⁴. A SHARP-BOX certificate covering an ε interval would handle this and is a stronger statement.

### 5.2 Rhea, Dione, Enceladus (rank 8)

- **Published.** Celletti 1990 trapped the resonance at their true parameters; Celletti 1994 built librational tori for Rhea at true parameters.
- **Data.** ε comes from shapes, not from Celletti's table, which I could not obtain. Enceladus axes are from arXiv:1509.07555. Rhea and Dione axes are from memory and **unverified**. Treat these rows as order-of-magnitude.

| Body (N) | e | ε | Band / separatrix | γ | log₁₀ e cur / v1 / v2 | L cur / v1 / v2 | S v1 | CPU-h cur / v1 |
|---|---:|---:|---|---:|---:|---:|---:|---:|
| Rhea (12) | 0.00126 | 3.7·10⁻³ | 0.104 / 0.086 | 0.0765 | −75 / −25.1 / −20.3 | 86 / 32 / 27 | 0.7k | 5–9 / 2–4 |
| Dione (9) | 0.0022 | 5.6·10⁻³ | 0.132 / 0.106 | 0.100 | −76 / −25.0 / −20.7 | 87 / 32 / 27 | 0.8k | 6–11 / 2–4 |
| Enceladus (4) | 0.0047 | 2.8·10⁻² | 0.286 / 0.238 | 0.209 | −87 / −26.3 / −21.5 | 97 / 33 / 28 | 1.6k | 12–23 / 4–8 |

  Rhea librational at 33°: −113 / −29.2 / −25.1, L 124 / 36 / 32, S 1.6k, CPU-h 74–142 / 6–12.
- **Verdict: now**, as a batch with Mercury. Small e makes the φ-decay very fast (2.7 digits per mode). These reproduce known results in the kernel; they are not firsts in mathematics.

## 6. Restricted three-body problem

### 6.1 12 Victoria in the truncated model (rank 3)

- **Model.** H(L, G, ℓ, g) = −1/(2L²) − G − εf, with the 10-term f of Celletti's survey §6.4, a = L², e = √(1 − G²/L²), ε = 10⁻³.
- **Statement.** On the energy level E* = −1.769, two invariant tori with frequency ratios from L̃± = L_V ± 0.001 bound the observed (L_V, G_V) = (0.670, 0.654). Every orbit between them on that level stays between them forever.
- **Why striking.** The first asteroid confined for all time in a proof assistant. Reproduces a Memoir of the AMS in the kernel.
- **Published.** Celletti–Chierchia, Mem. AMS 187 (2007) no. 878: this exact result, with mass ratios up to 1/1000. Their computer programs are not in the text.
- **Check.** My tori satisfy L ∈ [0.66886, 0.66921] and [0.67087, 0.67121], bracketing 0.670, with s − 1 ≈ −2.3·10⁻⁴.
- **Data.** n = 2, τ = 1, γ = 0.25–0.88, widths 0.31 and 0.32. log₁₀ e −115 / −26.8 / −22.3, L 124 / 33 / 29, S 15k / 1.1k / 0.8k. N_full = 79 (traced, naive: each mode has a polynomial coefficient). CPU-h per torus 285–552 / 13–25 / 11–20.
- **New Lean.** `sqrt` only, shared with §4.1. The statement stays in Delaunay variables, so no Kepler map is needed.
- **Verdict: after v1.** It is a theorem about a truncated model. Say so in the statement.

### 6.2 The exact restricted problem at the true mass ratio (rank 6)

- **Model.** H = p_r²/2 + G²/(2r²) − G − (1 − μ)/r₁ − μ/r₂, μ = 9.5388·10⁻⁴, in the radial polar chart of §3. This has no truncation and no Kepler equation.
- **Statement.** As §6.1, for the exact Newtonian PCR3BP. This would be new: I found no CAP that leaves the truncated expansion.
- **Numerics.** Converged for a ≈ 2.2–2.45 AU at e = 0.06–0.22. At e = 0.22 continuation stalls at n ≈ 3.33, close to the 10:3 commensurability, and at n = [3;2,1̄] (a = 2.31 AU), for a reason I did not identify. The nobles at a = 2.36 and 2.21 AU converge. I did not establish whether either stall is genuine breakdown or numerical.
- **Data** (n = 2, τ = 1, one torus):

| Case | γ | width | log₁₀ e cur / v1 / v2 | L cur / v1 / v2 | S v1 / v2 | CPU-h v1 / v2 | Advice MB v1 |
|---|---:|---|---:|---:|---:|---:|---:|
| e = 0.06, n ≈ 3.33 | 0.18 | 0.13, 0.19 | −150 / −39.0 / −32.4 | 161 / 46 / 39 | 20k / 14k | 170–320 / 120–230 | 87 |
| e = 0.12, n ≈ 3.33 | 0.18 | 0.13, 0.16 | −152 / −40.5 / −32.9 | 163 / 47 / 39 | 29k / 20k | 240–470 / 170–320 | 130 |
| e = 0.16, a = 2.21 AU | 1.93 | 0.13, 0.13 | −149 / −38.4 / −31.4 | 160 / 45 / 38 | 25k / 17k | 210–400 / 150–280 | 110 |
| e = 0.22, a = 2.36 AU | 1.33 | 0.11, 0.11 | −154 / −40.7 / −32.6 | 167 / 48 / 39 | 40k / 27k | 340–650 / 230–440 | 180 |
| e = 0.22, a = 2.21 AU | 1.93 | 0.12, 0.11 | −155 / −40.2 / −32.4 | 168 / 47 / 39 | 34k / 24k | 290–560 / 200–385 | 155 |

  γ differs by frequency normalization; the ratio is what matters. N_full = 50 (traced).
- **Why it costs so much.** Jupiter's harmonics decay at only 0.3 digits per mode at r/r_J ≈ 0.5, so support is intrinsic rather than a chart artefact. Truncation is what made §6.1 cheap.
- **Verdict: after v2, heroic.** 300–1300 CPU-h and 200–400 MB of advice for one theorem. A real decision, not a default. Levers: sum-factorized jets for N_full, and a Levi-Civita chart (§10) to make the Kepler part flat.

### 6.3 Jupiter Trojans (rank 7)

- **Model.** The exact PCR3BP near L4, in the guiding-centre chart of §3: exact L4 centring, double polar chart.
- **Statement.** At the true μ, two tori on one energy level trap a tadpole orbit with libration half-amplitude D and eccentricity e.
- **Why striking.** Real asteroids, a stability question since Lagrange, and the indefinite quadratic form makes the energy surface argument subtle (Arnold's theorem). Rigorous here means a kernel-checked statement at a realistic amplitude.
- **Published.** Gabern–Jorba–Locatelli, Nonlinearity 18 (2005) 1705: Kolmogorov normal form worked for 23 of the first 34 Trojans, and a proof of nearby tori for "a high order expansion of the Hamiltonian" succeeded for 3. Caracciolo–Locatelli (arXiv:2102.05959): rigorous Birkhoff stability times. Giorgilli–Skokos 1997 and Guzzo–Caracciolo–Pinzari 2026: effective stability.
- **Data** (one torus): ω ≈ (0.9966, −0.080). Converged at (e, D) = (0.03, 5°), (0.05, 10°), (0.05, 15°), (0.05, 20°), (0.10, 25°). The cases (0.10, 10°), (0.10, 15°), (0.10, 20°) failed in my continuation, at amplitude fractions 0.55–1, which is not a statement about the tori.

| e, D | γ | width | log₁₀ e cur / v1 / v2 | L cur / v1 / v2 | S v1 / v2 | CPU-h v1 / v2 |
|---|---:|---|---:|---:|---:|---:|
| 0.03, 5° | 0.078 | 0.26, 0.24 | −169 / −41.0 / −35.5 | 182 / 48 / 42 | 12k / 9k | 170–320 / 130–245 |
| 0.05, 10° | 0.077 | 0.22, 0.19 | −167 / −42.7 / −34.9 | 177 / 49 / 42 | 18k / 13k | 245–475 / 175–340 |
| 0.05, 20° | 0.076 | 0.21, 0.12 | −149 / −41.1 / −33.9 | 161 / 48 / 41 | 24k / 17k | 330–640 / 230–445 |
| 0.10, 25° | 0.076 | 0.16, 0.11 | −154 / −46.9 / −36.3 | 166 / 53 / 43 | 46k / 30k | 650–1250 / 410–800 |

- N_full = 86 (traced). **Verdict: after v2, heroic.** A truncated-expansion version would be far cheaper, but then it reproduces rather than exceeds the literature.

## 7. Standard map and Froeschlé map (ranks 5, 12)

- **Statement.** The golden invariant circle of y′ = y − (k/2π) sin 2πx, x′ = x + y′ exists at k = 0.970, within 0.17 % of Greene's k_c = 0.971635.
- **Why striking.** The most famous KAM object. It is the natural benchmark, and a Lean theorem at k ≈ 0.97 would be hard to dismiss as a toy.
- **Published.** Figueras–Haro–Luque, FoCM 17 (2017): proved at ε = 0.9716, with 8.4M modes, ρ = 3.7·10⁻⁷, E ≤ 2.74·10⁻⁴¹; Table 5 gives ε up to 0.96 at N = 32768.
- **Width law.** My Newton runs give w(0.86) = 0.0266, w(0.92) = 0.0118, w(0.94) = 0.00724, w(0.96) = 0.00269, which fits w ≈ 0.235 (k_c − k) on this range. Beyond 0.96 this is extrapolation, and the true law near k_c is renormalization: the last rows are optimistic (FHL needed 4× more modes at 0.9716 than this law gives).
- **Reach**, with a theorem of FHL form, threshold γ⁴ρ⁴/C₁, C₁ between 10⁷ (FHL's implied value) and 10¹⁰ (a first Lean theorem), n = 1, N_full = 3 assumed:

| k | width | log₁₀ e | L | S | CPU-h (tier P) | Advice MB |
|---:|---:|---:|---:|---:|---:|---:|
| 0.96 | 2.7·10⁻³ | −22.5 to −25.5 | 31–35 | 4–5k | 7–13 | 2 |
| 0.970 | 3.8·10⁻⁴ | −26 to −29 | 35–39 | 34–37k | 50–95 | 15 |
| 0.971 | 1.5·10⁻⁴ | −28 to −31 | 37–41 | 91–100k | 125–250 | 45 |
| 0.9714 | 5.5·10⁻⁵ | −29 to −32 | 39–43 | 260–280k | 340–690 | 130 |
| 0.9716 | 8.3·10⁻⁶ | −33 to −36 | 43–46 | ≥ 2M | ≥ 2400 | ≥ 950 |

- **Reachable in the kernel: k ≈ 0.970–0.971.** One dimension is what makes this so cheap: the box equals the support.
- **Theorem needed.** A maps version of the a-posteriori theorem. No flow theorem applies directly, because a kicked Hamiltonian is not analytic. `KAM/Sharp/Engine` is abstract, so this is a new `Scheme` instance, plus the map cohomological equation with divisors |e^{2πik·ω} − 1|.
- **New Lean.** 4–6k lines for the theorem; 2–3k for a map checker, because composition is by the map rather than an `Expr` jet. Timeline 6–9 weeks.
- **Froeschlé** (n = 2 map, FHL Table 8): grids 128² to 1024×512, at 267–533 bits. Same theorem; a stretch after the standard map. Their C₁b_E/(γ⁴ρ⁴) ranges from 10⁻⁴¹ to 10⁻⁵, and support of order 10⁴–10⁵ is in range only for ε ≲ 0.02.

## 8. Magnetic confinement (ranks 9, 11)

**What PlasmaLean has, as of today (commit of 30 October; README, `KamTorusAExact.lean`, `notes/theory/after-kam.md`).** The exact non-axisymmetric vacuum field `field (1/4)` has a sealed
exact invariant torus with ι = (75 + √5)/562, within 10⁻¹⁰ of its Fourier model, and all-time confinement of field lines inside. It also has guiding-centre results. Data: 2 × 1463 coefficients at 90 bits; γ = 0.0687; strip r = 0.1257 rad;
δ₀ = r/7; κ ≈ 5.7·10⁹; e₀ = 5.83·10⁻²²; **tolerance δ₀⁴/(32κ) = 5.7·10⁻¹⁹**; peak 4.3 GB. The theorem covers polynomial (and inverse-square-root) divergence-free fields on T², a 1½-degree-of-freedom setting.

**Comparison on its own example.** Our constants at γ = 0.0687, ρ = 0.02 turns, with norms taken from its bounds (`run_mag.py`, not like for like):

| | log₁₀ tolerance |
|---|---:|
| PlasmaLean, proved | **−18.2** |
| Ours, current | −88 |
| Ours, v1 | −25.4 to −30.3 |
| Ours, v2 estimate | −21.3 to −24.3 |

So its theorem is 7–12 orders more tolerant than v1 here. There are three reasons:

1. It runs Newton in **ℓ¹ coefficient norms**, where the small-divisor bound is simply ‖u‖_{r−δ} ≤ ‖f‖_r/(eγδ). In our units that is c = 1/(4π²e) = 0.0093 against our `cohConstR` 0.316, because a sup-norm theorem must pay for Rüssmann's L² detour. See D12: we moved to sup norms for the frozen hypotheses.
2. Its constants are computed on the actual torus (‖T₀‖ ≤ 19.84, twist ≥ 0.22), not derived from a single M.
3. It has fewer unknowns: 2 functions on T², no Lagrangian frame and no bordered system.

Reason 1 alone is worth up to 6 orders if the theorem's other branches do not bind. **Our theorem has far wider scope**: any Hamiltonian expression, any n, isoenergetic. But the honest claim today is "most general", not "sharpest".

**What we can do.**
- **Tokamak models: straightforward.** Valvo–Locatelli (arXiv:2101.07785) give a polynomial field-line Hamiltonian H(ψ) = ψ − ¾ψ² + ⅓ψ³ − ¹⁄₁₆ψ⁴ + ε(cos(2θ − φ) + cos(3θ − 2φ)). It is a `HamExpr` today. Their CAP proves a torus for the *controlled* Hamiltonian at ε = 0.003 (62 CPU-h), with RI = 150, RII = 8500. My uncontrolled torus at ω = 0.618 converges to ε = 4.8·10⁻⁴ (stops at 6·10⁻⁴), and at [0;1,1,2,1̄] to 7.5·10⁻⁴, close to breakup in both cases, so decay is slow (0.07 and 0.11 digits per mode). Data at the first: log₁₀ e −101 / −29.6 / −25.0, L 117 / 38 / 33, S 49k / 5.3k / 4.0k, N_full ≈ 12 (hand count), CPU-h 144–279 / 17–33. **Verdict: after v1.** Note it is a model, not a device.
- **Exact stellarator field: needs a new theorem.** The field-line flow of `field (1/4)` has a non-canonical area form, and there is no closed-form canonical chart: the flux coordinate requires inverting an integral. Options: a general-ω version of the theorem (HL19 and FHL17 allow it; one third of the a-posteriori layer is touched), or an ELP-S-style theorem for divergence-free fields. Neither is worth doing to duplicate PlasmaLean. Field-line confinement is its result. Do not spend here unless the point is a physically different field, such as a Dommaschk field with shear or a real coil set, and then the numbers must beat its 10⁻¹⁹ tolerance.

## 9. Planar Sun–Jupiter–Saturn (rank 13)

- **The paper.** Figueras–Haro, *Sun-Jupiter-Saturn system may exist*, J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152. Model: planar, reduced to 3 degrees of freedom, a 3-torus in a 6-dimensional phase space, Delaunay variables. Grid 1024³ with 76 digits; 6·10⁹ coefficients; 194 GB RAM; one Newton step takes one week. Error ‖η^{DK}‖ = 3.6·10⁻⁵⁴, ‖η^N‖ = 1.7·10⁻⁵⁷. Numerically checked KAM thresholds 10⁻³⁸ and 10⁻⁴⁴. τ = 2.4, γ = 1.69·10⁻⁶, ρ = 0.1 (2π angles), c_{D²X} = 5·10¹⁰, ‖⟨T⟩⁻¹‖ = 354. The rigorous CAP is announced as in progress; I found no sign it has appeared.
- **Thresholds on their data** (`run_sjs.py`, period-1 conversion, integer τ; fixed-frequency form, an optimistic simplification of the real degeneracy):

| Hypotheses | log₁₀ e current | v1 | v2-type (split M, c_R = 0.05) |
|---|---:|---:|---:|
| One M = 5·10¹⁰, τ = 3 | −546 | −137 | −86 |
| One M = 5·10¹⁰, τ = 2 (cubic ω) | −535 | −124 | −75 |

  Their torus's error 3.6·10⁻⁵⁴ passes their own check but fails ours by more than 20 orders.
- **Support**, from their strips (0.52, 0.42, 0.32 in 2π angles): 6·10⁶ at L = 30, 3.7·10⁷ at L = 54, 1.2·10⁸ at L = 80. Box/support is 6 in three dimensions, against 2 at n = 2.
- **What it would take.** At L ≈ 85 and S ≈ 10⁸: factor 10⁴ in support over lunar, N_full ≥ 100 (Kepler charts for two planets, so ≥ 30× lunar), and a box factor 3 over the lunar unit. That is about 8·10⁵ lunar units, or about 10⁷ CPU-h, with over 1 TB of advice. **Infeasible in the kernel**: the gap is 4 orders of magnitude after every lever. It would need an untrusted-computation bridge outside the kernel, which is outside our trust boundary.
- **Feasible neighbour.** The secular model of Locatelli–Giorgilli (CMDA 78, 2000): 2 degrees of freedom, polynomial, proved with real data for two tori bounding the secular motion (survey §6.5). It connects to the sealed `secularBoxSafety`. I did not obtain the coefficients; a polar chart at the secular eigenmodes makes it a primary torus problem, and it should be of §4.1's size. This is a reasonable later target, but it is a theorem about an averaged, truncated system.

## 10. Hill's lunar problem (rank 10)

- **Model.** H = p_r²/2 + G²/(2r²) − mG − 1/r − m²r²(3cos²θ − 1)/2, at m = 0.0748, radial polar chart. Exact, three lines.
- **Statement.** Two tori on one Jacobi level bracket the Moon's eccentricity, in Hill's problem, at true m.
- **Why striking.** Hill's 1878 model is the origin of modern lunar theory and of Poincaré's periodic orbits. The rigorous result (Kummer 1979, via a citation I have not read) is near the primary, not at true m.
- **Check.** The computed frequencies imply a perigee rate of 0.0086 per mean motion, against the Moon's observed 0.00845. r ranges over [0.91, 1.08], with evection visible.
- **Data** (e₀ = 0.055): γ = 0.128; widths 0.10, 0.12; log₁₀ e −175 / −50.8 / −43.0; L 189 / 59 / 51; S 282k / 27k / 20k; N_full = 36; CPU-h per torus 3.2–6.3k / 176–340 / 128–248; σ_T ≈ 2600 at the best scales.
- **Why it is dear, and the fix.** The polar chart is poorly centred: the variation orbit shifts the circle relative to e, which limits decay to 0.3 digits per mode. A Levi-Civita chart should do better, and I recommend trying it first. There z = w², the regularized H̃ = r(H − E) is a *polynomial* of degree 6, and the Kepler torus is exactly flat in circular oscillator actions. Not computed.
- **Verdict: after v2**, with a new chart. Moderately priced if the chart works; do not fund before.

## 11. Others

- **Exact PCR3BP elliptic version, spatial problems:** n = 3 at least. By §9's scaling the support is 10⁶–10⁸. Infeasible in the kernel at present.
- **Figure-eight 3-body orbit:** Kapela–Simó (Nonlinearity 2017) proved KAM stability by twist at the periodic orbit with validated ODEs. A torus certificate would be n = 3 or more, far beyond budget. A different kind of theorem is needed; not recommended.
- **Dissipative spin–orbit (CCdlL13):** needs a conformally symplectic theorem; the engine would host it. Valuable mathematically, but real tidal parameters are about 10⁻⁸, and no rigorous CAP exists. Out of scope here.
- **Accelerator maps (Hénon map, thin-lens rings):** need the maps theorem. A 1-degree-of-freedom dynamic aperture would be a cheap follow-up to §7. In 2 degrees of freedom a torus is no barrier.
- **FPUT small chains:** n ≥ 3 at any meaningful size.

## 12. Hénon–Heiles and galactic models (unranked)

- **Hénon–Heiles.** Published: Barrio et al., Nonlinear Dyn. 102 (2020) 403, and Wilczak–Barrio, SIADS 2017, give CAPs of stable periodic orbits and surrounding tori (I saw the abstracts only). Caracciolo–Locatelli 2021: Birkhoff stability. It has no a-posteriori torus at E = 1/12 that I could find.
- **My attempt failed.** Continuation from the isotropic oscillator breaks at once, because the frequency (1, 2) is exactly resonant at t = 0. Loop tori need a Birkhoff-type chart. So I have no numbers, and I do not guess any.
- **Galactic.** A logarithmic or Miyamoto–Nagai potential in the meridional plane is 2 degrees of freedom, and a torus would be a rigorous "third integral" statement on a Cantor set, the question Hénon–Heiles was invented to ask. The Sun's orbit is nearly separable, so this could be cheap. It is not computed. It needs `log` or `sqrt`.

## 13. Recommended sequence

**1. Mercury and the Moon band (now → 2 weeks after SO-DATA-2).** Mercury's 3:2 at true parameters, the Moon at N = 80, and the Saturnian batch, all on the SO pipeline.
- Theory needs: nothing new. Use v1 (A7, A8) if landed; otherwise the current theorem still works at 30–92 CPU-h per result.
- Do first: read Celletti 1990 Part II; fix Mercury's ε; decide Hansen or Kepler form.

**2. The Moon locked forever at the true ε (3–5 weeks after v1 and A8).** The headline.
- Theory needs: `KAM.Iso.Sharp.g1_sharp` and the sharp checker; `HamExpr.sqrt` in the sharp certifier's own files (SO owns `KAM/Certificate`); chart lemma; single-torus trap.
- Stretch: the exact Kepler model, and a smaller amplitude.
- This is the one to publish.

**3. 12 Victoria (3–4 weeks after step 2), then a decision on the exact problem.** CC07's truncated tori first, as `sqrt` is already there. Then decide whether the exact PCR3BP is worth 300–1300 CPU-h and 200–400 MB, with v2 in hand.
- Theory needs: v1 for the truncated model; v2 for the exact one, with lower N_full.

**Parallel, independent:** the maps theorem and the golden circle at k = 0.970. It is the only item needing new KAM theory, and it is the one mathematicians will recognize at once. Start it when a theorem-prover slot is free; it does not block anything above.

**For SHARP-PLUS.**
- Replacing H_T gains 3 orders, then c_R gains 2 down to about 0.036, and after that `𝔠_sum/μ` and the ν-branch bind at about 10⁻²⁰ on R1 (`v2_levers.py`): pushing c_R lower gives under 1 order. Attack these branches next. Raising ν is free in a certificate.
- Consider an ℓ¹-norm instance of the engine, which is the source of PlasmaLean's advantage (§8). It needs composition bounds in ℓ¹, which the checker's majorants already provide. It is a new theorem, not a tweak.
- "Least crude in existence" must be measured against PlasmaLean's 10⁻¹⁸·² as well as HL19. **Beating it on its own example is not implied by any estimate here.**

## 14. Method, calibration and limits

**Numerics.** `kamlib.py` is a generic double-precision isoenergetic quasi-Newton solver (HL19; FH25 §3) for primary 2-tori of any H given as code, using truncated Taylor jets. It samples M, σ_K, σ_B, σ_T on the distinguished boundary, with slack 1.05 and margin μ = 1/160, as package R1. It searches over the strip ρ, time scale c and action scale λ. Scale searches minimize digits under v1.

**Validation on R1** (`run_moon_rot.py validate`):

| Quantity | Here | Published |
|---|---:|---:|
| p range, lower torus | 0.968007–0.981806 | 0.968007–0.98181 |
| σ_K raw | 1.3025 | 1.303 |
| σ_B raw | 1.8331 | 1.833 |
| σ_T raw | 1.022493 | 1.022493 |
| log₁₀ threshold, current (c = 7/4) | −74.36 | −74.51 (m = 39/20) |
| log₁₀ threshold, v1 | −24.96 | −24.98 |
| Digits L: current, v1 | 85, 32 | 86–88, ≈ 32 |
| S at L = 85 | 8.0k | 7.7k |
| CPU-h per torus, current | 7.2–14 | 7.5–14.5 (SO-PACKFIX) |

Other cross-checks: Moon bands match the pendulum table of `lunar-band-2p8-2p9.md`; Hansen coefficients match the seven-term series; Hill's perigee rate; CC07's L-bracket; the standard-map width against FHL's grids.

**Digits.** L = (−log₁₀ e + 3 + 2)/(1 − w), w = 2πρ/(ln 10 · a_min), a_min the slowest decay in digits per mode. Calibrated on SO-GEN2.

**Support.** S = 1.4·α·L², α fitted to counts at L = 8–12. The factor 1.4 calibrates α = 0.79 to SO's measured 1.1 at L = 88. For n = 2. This is the weakest number here: it extrapolates a double-precision fit by up to 40 digits.

**v2 estimate.** The v1 constants with: H_T = actual sup |T| + 1; M₂ alone in the quadratic term; c_R = 0.036 (FHL17 Table 4, classic). Each needs a proof that does not exist. Real v2 numbers replace this column.

**Cost.** Unit: a lunar torus at R1, 7.5–14.5 CPU-h (tier P). Scaling: slots × (0.05 + 0.1 w/896) ms, from SO-REPLAY2; low-precision stage held at 1/3 of the unit. Advice 4 MB per unit, ∝ S·bits·N_full.
- Tier P excludes composition, Gram and torsion, not yet measured on the fixed code.
- Cost is linear in N_full, and N_full comes from `count_products.py`. It gives 3 for the lunar client, matching SO-ADVCOUNT. Its counts are naive upper bounds: §4.1 uses 15 by hand against 40 traced, because modes share a witness; Kepler uses 9 against 38 because clock-only products have tiny support. Those two are hand counts.
- Advice scales are less certain than CPU: SO's 4 MB came from a tail-decay accounting I did not redo.

**Other limits.**
- Sampled sups, not enclosures. SO-GEN2 found σ_B 8 % above sampled through the ℓ¹ checker route. This costs ≤ 0.5 order at v1 and more at the current theorem.
- γ is the numerical infimum × 0.965 (the R1 ratio), not a proved constant. Quadratic Diophantine proofs exist (`QuadraticDiophantine.lean`).
- Hill and Trojan charts are not optimized.
- No torus here passed an interval check.
- Timelines are rough judgments from past package sizes.

**Literature limits.** "Published" entries rest on abstracts, surveys and preprints as stated. Celletti 1990/1994 full texts were not accessible. "First" claims mean a targeted search found nothing; each needs a proper check before publication.

## 15. Reproduction

All in `scripts/apps_scout/`, using Python with numpy and mpmath, under a few minutes each on 2 threads. Output goes to `results/*.json`.

| Command | Produces |
|---|---|
| `python3 run_moon_rot.py validate` | §14 validation |
| `python3 run_moon_rot.py moon` | §4.2 |
| `python3 run_moon_rot.py bodies` | §5 |
| `python3 run_moon_rot.py kepler` | exact Kepler rows |
| `python3 run_libration.py moon`, `rhea` | §4.1, Rhea librational |
| `python3 run_r3bp.py cc07`, `polar`, `polar2`, `trojan`, `hill` | §6, §10 |
| `python3 run_r3bp.py hh` | the failed Hénon–Heiles attempt |
| `python3 run_stdmap.py`, `run_stdmap.py reach` | §7 |
| `python3 run_mag.py` | §8 |
| `python3 run_sjs.py` | §9 |
| `python3 count_products.py` | N_full |
| `python3 v2_levers.py` | §13 feedback for SHARP-PLUS |
| `python3 table.py` | Appendix |

## Appendix: full table

Per torus. CPU-h is tier P. Generated by `table.py` (`results/table.md`). For the Moon's rows N_full = 3 (rotational) and 15 (librational, hand count).

| candidate (per torus unless noted) | γ | width θ₁, θ₂ | ρ (v1) | log₁₀ threshold cur / v1 / v2 est. | digits L cur / v1 / v2 | support S cur / v1 / v2 | N_full | CPU-h tier P cur / v1 / v2 | advice MB cur / v1 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Moon rotational N=40, band 3.20 % | 0.0238 | 0.213, 0.370 | 0.01 | -74 / -25.6 / -20.3 | 85 / 32 / 27 | 8024 / 1140 / 817 | 3 | 7.2–14.0 / 3.1–5.9 / 2.9–5.6 | 4 / 0.2 |
| Moon rotational N=50, band 2.90 % | 0.0191 | 0.183, 0.371 | 0.01 | -80 / -27.7 / -22.1 | 93 / 35 / 29 | 10872 / 1515 / 1043 | 3 | 9.6–18.5 / 3.6–6.9 / 3.4–6.5 | 5 / 0.3 |
| Moon rotational N=60, band 2.75 % | 0.0159 | 0.155, 0.371 | 0.005 | -90 / -31.2 / -23.5 | 101 / 37 / 30 | 15050 / 2051 / 1361 | 3 | 13–25 / 4.3–8.3 / 4.0–7.7 | 8 / 0.5 |
| Moon rotational N=80, band 2.65 % | 0.0120 | 0.121, 0.371 | 0.005 | -111 / -36.4 / -27.9 | 121 / 43 / 34 | 27588 / 3496 / 2197 | 3 | 24–46 / 5.9–11.4 / 5.3–10.2 | 18 / 0.9 |
| Moon rotational N=100, band 2.63 % | 0.0096 | 0.097, 0.372 | 0.0025 | -131 / -43.2 / -31.2 | 143 / 49 / 38 | 47038 / 5614 / 3348 | 3 | 42–82 / 7.9–15.3 / 6.8–13.1 | 35 / 1.6 |
| Moon rotational N=120, band 2.63 % | 0.0080 | 0.082, 0.376 | 0.0025 | -156 / -48.9 / -35.9 | 167 / 56 / 42 | 75210 / 8382 / 4827 | 3 | 72–139 / 10–20 / 8.4–16.3 | 65 / 2.6 |
| Moon librational, amplitude 5.3° | 0.0252 | 0.345, 0.448 | 0.014 | -172 / -37.3 / -33.3 | 182 / 44 / 40 | 73924 / 4339 / 3560 | 15 | 347–671 / 15–28 / 13–24 | 349 / 5.6 |
| Moon librational, amplitude 8.8° | 0.0251 | 0.304, 0.460 | 0.01 | -160 / -35.1 / -30.9 | 173 / 41 / 38 | 67086 / 3853 / 3173 | 15 | 304–588 / 13–26 / 12–23 | 301 / 4.7 |
| Moon librational, amplitude 7.6° | 0.0251 | 0.315, 0.455 | 0.014 | -166 / -35.3 / -31.5 | 177 / 42 / 38 | 69924 / 3972 / 3269 | 15 | 322–622 / 14–26 / 12–23 | 321 / 4.9 |
| Moon librational, amplitude 21.6° | 0.0244 | 0.254, 0.488 | 0.01 | -131 / -31.2 / -27.1 | 144 / 38 / 34 | 52574 / 3614 / 2951 | 15 | 213–412 / 13–26 / 12–23 | 198 / 4.0 |
| Moon librational, amplitude 27.9° | 0.0238 | 0.219, 0.491 | 0.01 | -125 / -30.8 / -27.1 | 136 / 38 / 34 | 50624 / 3872 / 3106 | 15 | 198–384 / 14–28 / 13–24 | 180 / 4.3 |
| Moon librational, amplitude 37.0° | 0.0226 | 0.197, 0.479 | 0.01 | -117 / -31.3 / -26.9 | 128 / 38 / 34 | 48862 / 4363 / 3373 | 15 | 186–359 / 16–31 / 14–26 | 165 / 4.9 |
| Moon librational, amplitude 46.4° | 0.0212 | 0.171, 0.489 | 0.005 | -120 / -33.7 / -27.3 | 133 / 40 / 34 | 58027 / 5224 / 3875 | 15 | 225–434 / 19–36 / 15–30 | 202 / 6.1 |
| Moon librational, amplitude 57.0° | 0.0191 | 0.154, 0.496 | 0.005 | -113 / -35.7 / -29.2 | 126 / 42 / 35 | 59047 / 6616 / 4684 | 15 | 222–429 / 23–44 / 18–35 | 196 / 8.1 |
| Moon librational, amplitude 72.3° | 0.0152 | 0.122, 0.500 | 0.005 | -113 / -40.1 / -31.2 | 123 / 47 / 38 | 66566 / 9799 / 6314 | 15 | 247–478 / 32–62 / 23–45 | 216 / 13.3 |
| Mercury N=89, band 0.0159 (sep. 0.0140) | 0.0108 | 0.197, 0.183 | 0.01 | -80 / -28.1 / -22.2 | 92 / 35 / 29 | 21393 / 3108 / 2103 | 3 | 19–36 / 7.2–13.9 / 6.8–13.1 | 11 / 0.7 |
| Mercury N=74, band 0.0173 (sep. 0.0140) | 0.0129 | 0.225, 0.183 | 0.01 | -75 / -26.4 / -21.3 | 87 / 33 / 28 | 16899 / 2478 / 1732 | 3 | 15–29 / 6.2–12.1 / 5.9–11.4 | 8 / 0.5 |
| Rhea N=14, band 0.0973 (sep. 0.0864) | 0.0660 | 0.170, 0.983 | 0.01 | -78 / -26.5 / -21.6 | 90 / 33 / 28 | 6497 / 893 / 638 | 3 | 5.7–11.1 / 2.2–4.3 / 2.1–4.1 | 3 / 0.2 |
| Rhea N=12, band 0.1040 (sep. 0.0864) | 0.0765 | 0.197, 0.982 | 0.01 | -75 / -25.1 / -20.3 | 86 / 32 / 27 | 5343 / 729 / 538 | 3 | 4.8–9.3 / 2.0–3.8 / 1.9–3.7 | 2 / 0.1 |
| Dione N=11, band 0.1205 (sep. 0.1058) | 0.0831 | 0.159, 0.882 | 0.01 | -80 / -26.7 / -21.6 | 91 / 34 / 28 | 7784 / 1076 / 761 | 3 | 6.9–13.3 / 2.6–5.1 / 2.5–4.8 | 4 / 0.2 |
| Dione N=9, band 0.1322 (sep. 0.1058) | 0.1003 | 0.191, 0.881 | 0.01 | -76 / -25.0 / -20.7 | 87 / 32 / 27 | 6348 / 833 / 613 | 3 | 5.7–11.0 / 2.3–4.4 / 2.2–4.2 | 3 / 0.2 |
| Enceladus N=5, band 0.2628 (sep. 0.2382) | 0.1718 | 0.125, 0.681 | 0.005 | -87 / -29.5 / -23.9 | 100 / 36 / 30 | 17923 / 2323 / 1627 | 3 | 16–30 / 5.2–10.0 / 4.8–9.4 | 10 / 0.5 |
| Enceladus N=4, band 0.2859 (sep. 0.2382) | 0.2090 | 0.164, 0.754 | 0.01 | -87 / -26.3 / -21.5 | 97 / 33 / 28 | 13944 / 1629 / 1168 | 3 | 12–23 / 4.1–7.9 / 3.9–7.5 | 7 / 0.3 |
| Rhea librational, amplitude 33.0° | 0.0765 | 0.204, 1.008 | 0.01 | -113 / -29.2 / -25.1 | 124 / 36 / 32 | 19674 / 1643 / 1279 | 15 | 74–142 / 6.3–12.2 / 5.5–10.6 | 65 / 1.8 |
| Rhea librational, amplitude 44.6° | 0.0709 | 0.176, 1.008 | 0.01 | -112 / -31.1 / -25.8 | 124 / 38 / 33 | 22634 / 2140 / 1557 | 15 | 85–164 / 7.8–15.1 / 6.5–12.5 | 74 / 2.4 |
| Rhea librational, amplitude 58.6° | 0.0618 | 0.152, 1.009 | 0.005 | -113 / -35.1 / -28.1 | 126 / 41 / 34 | 27734 / 2986 / 2039 | 15 | 105–202 / 10–20 / 8.1–15.7 | 92 / 3.6 |
| Moon exact Kepler N=40, band 0.0320 | 0.0238 | 0.213, 0.472 | 0.01 | -99 / -30.3 / -23.4 | 112 / 37 / 30 | 14252 / 1556 / 1010 | 9 | 31–61 / 4.6–8.8 / 3.8–7.4 | 25 / 1.0 |
| Moon exact Kepler N=60, band 0.0275 | 0.0159 | 0.155, 0.472 | 0.005 | -103 / -35.9 / -26.1 | 115 / 42 / 33 | 19787 / 2667 / 1650 | 9 | 44–85 / 6.9–13.3 / 5.4–10.5 | 36 / 2.0 |
| Mercury exact Kepler N=74, band 0.0173 | 0.0129 | 0.226, 0.307 | 0.01 | -136 / -37.3 / -28.6 | 147 / 44 / 35 | 37273 / 3369 / 2122 | 9 | 93–181 / 8.4–16.3 / 6.6–12.7 | 86 / 2.6 |
| CC07 truncated Victoria L+ | 0.8762 | 0.306, 0.321 | 0.01 | -115 / -26.8 / -22.3 | 124 / 33 / 29 | 15006 / 1054 / 831 | 79 | 285–552 / 13–25 / 11–20 | 258 / 5.5 |
| CC07 truncated Victoria L- | 0.2453 | 0.309, 0.323 | 0.01 | -117 / -28.5 / -23.0 | 126 / 35 / 30 | 15488 / 1177 / 876 | 79 | 297–574 / 15–28 / 11–21 | 270 / 6.5 |
| CC07 truncated Victoria L0 | 0.3179 | 0.308, 0.322 | 0.01 | -116 / -28.1 / -22.9 | 125 / 34 / 30 | 15310 / 1140 / 866 | 79 | 293–567 / 14–27 / 11–21 | 267 / 6.2 |
| Exact PCR3BP e=0.12 | 0.1790 | 0.128, 0.156 | 0.005 | -152 / -40.5 / -32.9 | 163 / 47 / 39 | 339612 / 28622 / 19834 | 50 | 4876–9427 / 241–467 / 167–323 | 4806 / 129.8 |
| Exact PCR3BP e=0.06 | 0.1790 | 0.131, 0.194 | 0.005 | -150 / -39.0 / -32.4 | 161 / 46 / 39 | 245238 / 19730 / 14306 | 50 | 3494–6754 / 166–321 / 121–233 | 3432 / 86.8 |
| Exact PCR3BP n=[3;3,1bar] e=0.22 | 1.3336 | 0.111, 0.110 | 0.005 | -154 / -40.7 / -32.6 | 167 / 48 / 39 | 483774 / 39967 / 27063 | 50 | 7046–13622 / 337–652 / 228–441 | 6989 / 183.0 |
| Exact PCR3BP n=[3;3,1bar] e=0.16 | 1.3336 | 0.117, 0.135 | 0.005 | -148 / -38.9 / -31.6 | 160 / 46 / 38 | 346619 / 28520 / 19802 | 50 | 4911–9495 / 240–464 / 167–324 | 4813 / 125.8 |
| Exact PCR3BP n=[3;2,1bar] e=0.16 | 1.8430 | 0.119, 0.134 | 0.005 | -148 / -38.3 / -31.3 | 160 / 45 / 38 | 334156 / 26872 / 18873 | 50 | 4729–9143 / 226–437 / 160–309 | 4632 / 117.2 |
| Exact PCR3BP n=[3;1,1,1bar] e=0.22 | 1.9300 | 0.121, 0.109 | 0.005 | -155 / -40.2 / -32.4 | 168 / 47 / 39 | 432161 / 34405 / 23598 | 50 | 6324–12226 / 290–561 / 199–385 | 6285 / 156.0 |
| Exact PCR3BP n=[3;1,1,1bar] e=0.16 | 1.9300 | 0.127, 0.134 | 0.005 | -149 / -38.4 / -31.4 | 160 / 45 / 38 | 308390 / 24639 / 17344 | 50 | 4371–8451 / 207–401 / 147–284 | 4284 / 107.3 |
| Trojan e=0.03 D=5 | 0.0776 | 0.256, 0.240 | 0.01 | -169 / -41.0 / -35.5 | 182 / 48 / 42 | 172869 / 12106 / 9370 | 86 | 4581–8857 / 167–323 / 127–245 | 4664 / 95.6 |
| Trojan e=0.05 D=10 | 0.0774 | 0.219, 0.190 | 0.005 | -167 / -42.7 / -34.9 | 177 / 49 / 42 | 231206 / 17694 / 13043 | 86 | 6025–11648 / 245–474 / 176–340 | 6093 / 142.2 |
| Trojan e=0.05 D=15 | 0.0580 | 0.217, 0.149 | 0.005 | -159 / -41.4 / -34.5 | 170 / 48 / 41 | 249468 / 19958 / 14447 | 86 | 6312–12202 / 275–532 / 194–376 | 6308 / 157.5 |
| Trojan e=0.05 D=20 | 0.0760 | 0.214, 0.122 | 0.005 | -149 / -41.1 / -33.9 | 161 / 48 / 41 | 269798 / 24154 / 17171 | 86 | 6578–12717 / 333–644 / 231–446 | 6472 / 190.8 |
| Trojan e=0.10 D=25 | 0.0760 | 0.160, 0.109 | 0.0025 | -154 / -46.9 / -36.3 | 166 / 53 / 43 | 450401 / 45920 / 30463 | 86 | 11240–21730 / 649–1254 / 413–798 | 11170 / 395.8 |
| Hill e0=0.055 | 0.1277 | 0.102, 0.121 | 0.005 | -175 / -50.8 / -43.0 | 189 / 59 / 51 | 282213 / 27136 / 20115 | 36 | 3234–6253 / 176–340 / 128–248 | 3318 / 107.0 |
| Hill e0=0.040 | 0.1277 | 0.068, 0.093 | 0.005 | -174 / -56.9 / -43.8 | 193 / 67 / 53 | 509875 / 61169 / 38023 | 36 | 5925–11454 / 409–790 / 243–470 | 6110 / 271.1 |
| Hill e0=0.070 | 0.1277 | 0.094, 0.116 | 0.005 | -175 / -53.0 / -43.8 | 190 / 61 / 51 | 278494 / 29031 / 20534 | 36 | 3196–6178 / 190–367 / 131–253 | 3280 / 118.9 |
| tokamak golden 0.618 ε=0.00048 | 0.5964 | 0.026, 0.042 | 0.0025 | -101 / -29.6 / -25.0 | 117 / 38 / 33 | 49181 / 5260 / 3957 | 12 | 144–279 / 17–33 / 15–28 | 122 / 4.8 |
| tokamak [0;1,1,2,1bar] ε=0.00075 | 0.4642 | 0.024, 0.041 | 0.0025 | -108 / -30.5 / -25.4 | 127 / 40 / 34 | 77098 / 7554 / 5555 | 12 | 235–455 / 24–46 / 20–39 | 206 / 7.1 |

## Sources

- Barrio et al., Nonlinear Dyn. 102 (2020) 403–416.
- Caracciolo, Locatelli, arXiv:2102.05959.
- Celletti, ZAMP 41 (1990) 174–204 and 453–479; ZAMP 45 (1994) 61–80, doi:10.1007/BF00942847 (abstract read).
- Celletti, *Perturbation theory in celestial mechanics*, mp_arc 07-303.
- Celletti, Chierchia, RCD 3 (1998), mp_arc 98-581; Mem. AMS 187 (2007) no. 878.
- Enciso, Luque, Peralta-Salas, JEMS 27 (2025) 2251–2291 (as cited in PlasmaLean).
- Figueras, Haro, Luque, FoCM 17 (2017) 1123, arXiv:1601.00084.
- Figueras, Haro, J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152.
- Gabern, Jorba, Locatelli, Nonlinearity 18 (2005) 1705–1734.
- Kapela, Simó, Nonlinearity 30 (2017) 965, arXiv:1105.3235.
- Locatelli, Giorgilli, CMDA 78 (2000) 47.
- PlasmaLean, <https://github.com/siddhartha-gadgil/PlasmaLean>, read 30 October 2026.
- Valvo, Locatelli, arXiv:2101.07785.
- Wilczak, Barrio, SIAM J. Appl. Dyn. Syst. (2017).

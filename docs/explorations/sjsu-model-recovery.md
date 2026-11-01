# Recovery of the degree-18 secular SJSU model (pilot phase 0)

1 November 2026. Branch `sjsu-p0`. Numerical research and data production only: no Lean source
or frozen declaration is touched, and nothing here is a certificate. The recovered model is
published as an open dataset in [`applications/sjsu/`](../../applications/sjsu/README.md)
(data CC BY 4.0, scripts Apache-2.0). It follows the scoping report
[sjsu-effective-stability](sjsu-effective-stability.md) (§§1, 4, 7 and its model hierarchy).

**Verdict.** The degree-18 planar secular SJSU Hamiltonian was regenerated from the published
recipe (SLG13 §§2–3, GLS17 §2): first-order expansion, the two Kolmogorov-like steps with
K_F = 8, and the resonant step for 3λ₁ − 5λ₂ − 7λ₃. It is published as **`SJSU18-O2`**, a
dense rotation-invariant polynomial with exactly 7,941 complex (38,466 real) coefficients,
written to 25 digits, and regression-tested. It is a well-defined *reconstruction*, not the
authors' file. It reproduces the printed quadratic coefficients to ≤ 7.7·10⁻⁴ and the linear
secular frequencies of Table 2 to ≤ 5.8·10⁻⁴. The printed quartic agrees only to 3–8 % for the
5:2-dominated terms, and its three-planet terms are absent at strict order two.

Four findings explain the gap and correct the scoping report's reading of the source:

1. **The printed Appendix A is not a strict order-two truncation.** Its three-planet quartic
   coefficients appear only at **third order in the masses**. With the Lie series kept to order
   3 they are reproduced to a median 2.9 %, closer than with the converged series (order 4–5).
2. **n\* includes the first-order frequency correction.** Read this way, SLG13 eq. (5) gives
   2n₁\* − 5n₂\* = −0.007099 rad/yr, matching the N-body great-inequality frequency −0.007115.
   The Kepler frequencies give −0.004374, which inflates the J–S quartic by about 40 %.
3. **SJSU-E1 is exactly a charge-±4 component of the printed quartic** (30 monomials, the
   largest 7.8·10⁻⁸). No computation obeying the d'Alembert rules can produce it, at any order.
4. **SJSU-E2 is sharper than reported.** Table 2 keeps the AMD of the *raw* Table 1 point to
   11 digits, but its modal amplitudes are inconsistent with the printed quadratic part (by
   15–64 %), and eq. (24) is a third, unrelated set. Even so, GLS17's eq. (37) frequencies are
   consistent with integrating from the Table 2 point: SJSU18-O2 gives them to 3.9 %, 0.5 %
   and 0.04 %.

| Label | Meaning |
|---|---|
| **measured** | computed in this task (exact rational, mpmath, long double or float64 arithmetic, as stated) |
| **literature** | stated in SLG13, GLS17 or LG00 |
| **estimated** | inference or engineering judgement |

## 1. Sources and pins

| Source | SHA-256 | Use |
|---|---|---|
| SLG13 journal article-in-press, `kam-tools/papers/slg13-sjsu-mcs/paper.pdf` | `915002b1…5147c` | §§2–3, Tables 1–2, eq. (24), Appendix A |
| SLG13 arXiv:1010.2609v1, **fetched now** to `kam-tools/papers/slg13-sjsu-arxiv-1010.2609v1/` | pdf `3a231dd1…6cfb`, text `c34af220…cc03` | same text; Appendix A identical (scoping check) |
| GLS17 supplied preprint, `kam-tools/papers/gls17-sjsu-rcd/paper.pdf` | `bb11bb4b…ce1d` | §2, Table 2, eq. (37) |
| GLS17 arXiv:1702.04894v1, **fetched now** to `kam-tools/papers/gls17-sjsu-arxiv-1702.04894v1/` | pdf `254d52fb…1cae`, text `1862e351…3afb` | same |
| LG00 (SJS analogue), `kam-tools/papers/lg00-sjs-cmda/paper.pdf` | `a4f1ace6…24a3` | §2.2: the order-two formula and the first-order initial map |

The two arXiv PDFs reproduce the hashes pinned in the scoping report byte for byte.
Each directory carries `paper.pdf`, `paper.txt` (`pdftotext -layout`) and `SHA256SUMS`.

## 2. Hamiltonian and conventions (step 1)

**Literature/measured.** The planar four-body Hamiltonian in canonical heliocentric variables,
SLG13 eq. (1): T⁽⁰⁾ + U⁽⁰⁾ + T⁽¹⁾ + U⁽¹⁾ with the indirect term T⁽¹⁾ = Σ r̃ᵢ·r̃ⱼ/m₀. The table
was checked against SLG13 eq. (2), the scoping report and the prototype's `{ξ, η} = −1`.

| Item | Convention used (all files) |
|---|---|
| Units, masses | AU, yr, G = 1, m₀ = 4π², m_j = m₀/M_j, M_j = 1047.355, 3498.5, 22902.98 (exact decimals) |
| Kepler part | Σ [r̃_j²/(2β_j) − β_jμ_j/r_j], β_j = m₀m_j/(m₀+m_j), μ_j = G(m₀+m_j) |
| Poincaré variables | Λ_j = β_j√(μ_j a_j), λ_j = M_j + ϖ_j, ξ_j = √(2Γ_j) cos ϖ_j, η_j = −√(2Γ_j) sin ϖ_j, Γ_j = Λ_j(1 − √(1−e_j²)) |
| Orientation | (λ_j, η_j) coordinates, (Λ_j, ξ_j) momenta: from q = √(2Γ) sin γ, p = √(2Γ) cos γ with γ = −ϖ conjugate to Γ; hence dη/dt = ∂H/∂ξ, dξ/dt = −∂H/∂η |
| Complex form | z_j = (ξ_j − iη_j)/√2 = √Γ_j e^{iϖ_j}, {z_j, z̄_j} = −i, ż = −i ∂H/∂z̄ |
| Bracket | {f, g} = Σ (f_λ g_L − f_L g_λ) − i Σ (f_z g_z̄ − f_z̄ g_z), L = Λ − Λ\* |
| d'Alembert | a term z^P z̄^Q e^{ik·λ} occurs only if |P| − |Q| + Σk = 0; the secular part is charge-balanced |
| Monomial order | real (ξ_J, ξ_S, ξ_U, η_J, η_S, η_U), as in `scripts/sjsu/slg13_quartic.json` |

The orientation matters at second order (it fixes the sign of the {·,·}_ξη terms). It follows
from SLG13 eq. (2), not from a fit. The Table 1 elements are read as **Poincaré elements**
(§5.2 gives the evidence).

## 3. First order in the masses (step 2)

**Method (measured).** For each pair, i inner,
1/|rᵢ − rⱼ| = (1/(2aⱼ)) Σ_k e^{ik(λᵢ−λⱼ)} Σ_n Dⁿb^{(k)}_{1/2}(α)/(n! 2ⁿ) Σ_m C(n,m) [σᵢ^m e^{ik(φᵢ−λᵢ)}] [(−σⱼ)^{n−m} e^{−ik(φⱼ−λⱼ)}/ρⱼ],
with D = α d/dα and σ = 2 log(r/a). The single-planet factors are **exact rational** series in
(u, ū, e^{iλ}), u = (ξ − iη)/√Λ, built from Bessel expansions and e e^{iϖ} = u√(1 − uū/4)
(`kepler_series.py`). The Laplace derivatives (n ≤ 19, k ≤ 18) are summed in mpmath.
r̃_j = (Λ_j/a_j) ∂_λ(ρ_j e^{iφ_j}) gives the indirect part. The Λ-dependence (a_j(Λ_j) and the
√Λ in u) gives the L-linear terms exactly. Truncation: degree ≤ 18, |k₁|+|k₂|+|k₃| ≤ 16.
In total, 1,077,382 complex terms in 12 s (long double).

**Validation (measured).**

| Check | Result |
|---|---|
| Kepler series vs direct Kepler solve (mpmath) | error ∝ e¹⁹: 2.5·10⁻²², 4.6·10⁻²⁸, 8.7·10⁻³⁴ at e = 0.06, 0.03, 0.015 |
| Laplace coefficients and α-derivatives vs quadrature | ≤ 6·10⁻⁴¹ |
| Every tested harmonic of f_ij (11 per pair, all three pairs, two amplitudes) vs an exact mpmath DFT of −Gmᵢmⱼ/|rᵢ−rⱼ| + r̃ᵢ·r̃ⱼ/m₀ on a 96×96 grid, values **and** ∂/∂Λ (central differences) | worst 3.4·10⁻¹⁹ of |F₀| (`check_expansion.py`) |
| Secular quadratic part vs the Laplace–Lagrange formula with b^{(1)}_{3/2}, b^{(2)}_{3/2} | ≤ 1.1·10⁻¹⁹ (long double), 2.3·10⁻⁴⁰ (mpmath, regression test) |

The pointwise sums differ from the true Hamiltonian by about 10⁻³: that is SLG13's |k| ≤ 16
truncation (the circular J–S series stops at Laplace index 8), not an expansion error.

## 4. Second order in the masses (step 3)

**Recipe (literature, SLG13 eqs. (5)–(12)).** f = f₀ + f₁ (L-independent and L-linear
perturbation), Z₀ = n\*·L + K₂(L), K₂'' = −3n_j/Λ_j.
χ₁: n\*·∂_λX₁ + [f₀]_{0<|k|≤8, deg≤6} = 0. χ₂: the same for ĥ₁ = f₁ + {X₁, K₂}.
At order two and L = 0 this gives
⟨f₀⟩ + ⟨{X₁,f} − ½{X₁,f₀ᵀ} + ½{X₁,{X₁,K₂}} + {X₂, f₀ − f₀ᵀ}⟩.
The resonant step takes h_res = [H₂]_{±(3,−5,−7)} (L⁰ to degree 11, L¹ to degree 9), χ_res of
degree 9, and the μ⁴ terms of eq. (12) with its printed weight ½. Brackets are exact, with no
magnitude cut-offs, and truncated only by the source's rules (`secular.py`; the vectorized,
bounded-memory bracket is in `sparse.py`).

**The frequency vector n\* (measured, interpretation).** SLG13 eq. (5) separates "the term which
is both linear in the actions and independent of all the other canonical variables (i.e.,
n\*·L)". In H⁽ᵀ⁾ that term includes the perturbation's ⟨∂f/∂L⟩ at zero eccentricity (LG00 did
the same explicitly). Both readings were tested:

| | n₁, n₂, n₃ (rad/yr) | 2n₁ − 5n₂ | n₁ − 7n₃ | 3n₁ − 5n₂ − 7n₃ |
|---|---|---|---|---|
| Kepler at Λ\* | 0.5297667, 0.2127815, 0.0745980 | −0.004374 | +0.007581 | +0.003207 |
| corrected (used) | 0.5297300, 0.2133119, 0.0748018 | −0.007099 | +0.006117 | −0.000982 |
| N-body mean motions (1e5 yr) | 0.5297296, 0.2133147, 0.0748025 | −0.007115 | +0.006112 | −0.001002 |

The J–S quartic coefficients are dominated (about 90 %) by second-order terms ∝ 1/(2n₁−5n₂).
With Kepler n\* they overshoot Appendix A by about 40 %; with corrected n\* they are 4–8 % off.
The corrected reading is adopted. It also makes the resonant divisor κ·n\* = −9.82·10⁻⁴ the
physical one; with Kepler n\* it is +3.2·10⁻³, about 10× weaker in the squared terms.

**Independent check of the engine (measured).** `lie_mimic.py` evaluates the same two steps as
an order-tracked Lie series. At N = 2 it reproduces `secular.py` to round-off at every
coefficient of degree ≤ 4.

## 5. Reference axes and the initial map (step 4)

### 5.1 a\* by the stated procedure

**Measured.** A planar SJSU N-body integration from Table 1: Wisdom–Holman map in democratic
heliocentric splitting, exactly SLG13's Hamiltonian (1). It is composed to fourth order, with
dt = 0.5 yr; the energy error is ≤ 10⁻⁷, and dt = 0.25 changes the averages by 10⁻⁸. The time
average of the Poincaré semi-major axes over 1 Myr is

  a\* = (5.202374655793598, 9.554443730484715, 19.21504720877541) AU

(`validation/astar.json`). The window dependence is ≤ 6.2·10⁻⁷ relative (3·10⁵ versus 10⁶ yr);
the heliocentric osculating averages differ by ≤ 1.3·10⁻⁵. SLG13 print neither their a\* nor
their integration length. 10 CPU-min.

### 5.2 Table 1 is read as Poincaré elements

**Measured.** Reading Table 1 instead as heliocentric osculating elements (with r̃ = m × the
barycentric velocity) gives the same positions but momenta about 10⁻³ different. The averaged
⟨a_S⟩ then moves to 9.595 AU, and 2n₁ − 5n₂ to −0.0007 rad/yr: essentially exact 5:2
resonance. That contradicts SLG13's statement that (6) is solvable, being non-resonant up to
order 8. The Poincaré reading reproduces the real great-inequality frequency.
**Estimated:** SLG13 used the Table 1 elements as Poincaré elements
(`validation/nbody_readings.json`).

### 5.3 Map to the secular variables and to Table 2

**Method.** old = Φ₁(Φ₂(new)) with Φ = exp(L_χ) id, so to first order (LG00's choice)
z_sec = z − i ∂(X₁+X₂)/∂z̄ at (λ, L = Λ − Λ\*, z). Second order was evaluated as a sensitivity
check. Then (ξ, η) = O(x, y), with O the orthogonal eigenvectors of the quadratic part.

**Measured** (`validation/table2_map_*.json`, `validation/table2_analysis.json`):

| | mode 1 | mode 2 | mode 3 |
|---|---|---|---|
| ν (SJSU18-O2), rad/yr | −1.1211691·10⁻⁴ | −1.9677076·10⁻⁵ | −1.1133726·10⁻⁵ |
| ν (Table 2, literature) | −1.1212725·10⁻⁴ | −1.9688445·10⁻⁵ | −1.1134564·10⁻⁵ |
| relative difference | 9.2·10⁻⁵ | 5.8·10⁻⁴ | 7.5·10⁻⁵ |
| R_j: Table 1, uncorrected | 0.025011 | 0.036298 | 0.007743 |
| R_j: Table 1, first-order secular | 0.025264 | 0.036570 | 0.007567 |
| R_j: Table 1, second-order secular | 0.025258 | 0.036571 | 0.007566 |
| R_j: Table 2 (literature) | 0.029640 | 0.031025 | 0.012726 |
| R_j: eq. (24) (literature) | 0.025558 | 0.030602 | 0.011223 |

The Lie correction moves the amplitudes by ≤ 2.3 %. The total AMD Σ R_j²/2 is 1.0015294·10⁻³
for the raw Table 1 point, **the same to 3.8·10⁻¹⁴ relative** for Table 2, 1.01644·10⁻³ for
the first-order secular point, and 8.578·10⁻⁴ for eq. (24).

## 6. Validation against the published numbers (step 5)

### 6.1 Appendix A, 78 coefficients

`validation/appendixA_comparison.csv` lists every printed coefficient against SJSU18-O2 and its
first- and second-order parts, plus the invariant projection of the printed value.
`validation/order_study_d4.csv` gives the values when the Lie steps are kept to mass order
N = 2…5 (degree 4).

| Group (count) | order 2 = SJSU18-O2: median / max | order 3: median / max | order 5 (converged): median / max |
|---|---|---|---|
| quadratic (12) | 3.2·10⁻⁴ / 7.7·10⁻⁴ | 3.0·10⁻⁴ / 7.7·10⁻⁴ | 2.9·10⁻⁴ / 9.7·10⁻⁴ |
| quartic, one planet (9) | 6.3·10⁻² / 7.9·10⁻² | 3.6·10⁻² / 7.6·10⁻² | 3.4·10⁻² / 6.8·10⁻² |
| quartic, J–S (13) | 6.4·10⁻² / 6.9·10⁻² | 4.8·10⁻² / 5.7·10⁻² | 4.3·10⁻² / 5.2·10⁻² |
| quartic, J–U (13) | 3.7·10⁻³ / 0.19 | 1.1·10⁻³ / 3.5·10⁻³ | 1.3·10⁻³ / 1.2·10⁻² |
| quartic, S–U (13) | 1.0·10⁻² / 8.4·10⁻² | 2.6·10⁻⁴ / 1.8·10⁻³ | 6.0·10⁻⁴ / 4.3·10⁻³ |
| quartic, three planets (18) | 1.0 / 1.2 (absent at order two) | 2.9·10⁻² / 0.62 | 6.9·10⁻² / 0.47 |

(The maxima of 0.47–0.62 in the last row come from the smallest printed coefficient,
ξ_Jξ_Uη_Sη_U = 5.4·10⁻⁸.)

No coefficient is reproduced to its printed digits (17 significant figures). That is expected:
the printed values are float64 output of a computation whose a\*, n\* and Lie truncation are
not published. **Measured conclusions:**

* **Order two cannot fit.** With a\* free, the order-two model fits the six quadratic
  coefficients only to 3.1·10⁻⁴ rms, and a\* drifts by 8·10⁻⁴ from the N-body average to
  (5.19817, 9.54832, 19.20532). With the two-planet quartic included, the fit runs away to
  (5.2534, 9.6528, 19.4739) at 4.4·10⁻² rms (`validation/fits/`).
* **Third order is needed for the three-planet terms.** At N = 3, ξ_J²ξ_Sξ_U, ξ_Jξ_S²ξ_U and
  ξ_Jξ_Sη_Sη_U agree to 1.8 %, 0.7 % and 0.5 %; ξ_J³ξ_U goes from +18.6 % (order two) to −0.17 %.
  N = 4 shifts the three-planet terms by 4–14 %, and N = 5 changes nothing above 2·10⁻³: the
  series has converged at degree 4. Yet **order 3 matches the printed table better than the
  converged series** for every group except the J–S quartic. **Estimated:** SLG13's Lie series
  was effectively cut near third order, a detail their text does not give.
  CPU time: 8 s at N = 3, 4 min at N = 4, 56 min at N = 5 (degree 4).
* **The 5:2 quartic is still off after convergence.** The J–S quartic stays 3.4–6.8 % from the
  printed values, and the implied rescalings of 1/(2n₁−5n₂) differ between monomials (1.04–1.08).
  So no single divisor or a\* change closes the gap (**estimated:** an undisclosed
  implementation detail). A degree-18 model at order ≥ 4 is out of reach here: N = 5 already
  costs about an hour at degree 4.

### 6.2 Frequencies (Table 2 ν; GLS17 eq. (37))

**Measured** (`freq_check.py`; RK4 with dt = 200 yr over 10⁷ yr, then a Hann-windowed refined
Fourier peak of x_j + iy_j). Relative deviation from GLS17 (37),
ω = (−1.51665·10⁻⁴, −2.05981·10⁻⁵, −1.16008·10⁻⁵):

| Model, initial point | ω₁ | ω₂ | ω₃ |
|---|---|---|---|
| SJSU18-O2, Table 2 (with our O) | +3.9·10⁻² | +4.8·10⁻³ | −4.3·10⁻⁴ |
| printed quartic, Table 2 | +0.114 | +1.6·10⁻² | +2.2·10⁻³ |
| SJSU18-O2, Table 1 first-order secular point | +0.110 | +1.5·10⁻² | +6.9·10⁻³ |
| printed quartic, raw Table 1 | +0.153 | +2.3·10⁻² | +8.2·10⁻³ |

The degree-6–18 content shifts the fast frequency by about 8 % at these amplitudes, toward
GLS17's value. GLS17's eq. (37) is consistent with the Table 2 point, not with the Table 1
point mapped as in §5.3. The remaining 3.9 % on ω₁ matches the 5:2 quartic gap of §6.1
(**estimated**).

### 6.3 Source issues: resolutions and new candidates

* **SJSU-E1 (resolved in kind).** Converted exactly to z, the printed quartic is a
  charge-balanced part plus charge-±2 residues of ≤ 1.5·10⁻¹⁶ (float rounding of ξ/η
  pairs) and a **charge-±4 part**: 30 monomials, real and reversible, the largest z_S²z_U²
  (−7.84·10⁻⁸), z_Jz_Sz_U² (5.99·10⁻⁸), z_J²z_S² (4.32·10⁻⁸)
  (`validation/appendixA_noninvariant.csv`). This part alone produces the nonzero AMD bracket.
  Charge ±4 cannot arise in any secular average of a d'Alembert series: our expansions and Lie
  series at N = 2…5 are invariant to round-off. It is a defect of the printed data, of
  unknown origin. A magnitude-based coefficient cut in the authors' real cos/sin
  representation is one possible mechanism (**estimated**). Our model is exactly invariant,
  so the AMD C = Σ zⱼz̄ⱼ is an exact first integral of SJSU18-O2, and the planar reduction of
  scoping §4 applies to it.
* **SJSU-E2 (sharpened).** See §5.3. Table 2 is an orthogonal image of the raw Table 1 point:
  its AMD agrees to 3.8·10⁻¹⁴. But its modal amplitudes are not those of Table 1 in the
  eigenbasis of the printed quadratic part (Procrustes residual 1.3·10⁻³ for any common
  orthogonal map; transposed or permuted bases, and first-order-only eigenvectors, miss by
  ≥ 14 %). Eq. (24) states R_j = √(x_j² + y_j²) from Table 2, but carries a different AMD.
  Eq. (37) is consistent with Table 2. **Owner/author question.**
* **SJSU-E3 (new).** SLG13 §3.2, last paragraph (journal p. 7): "we decided to calculate the
  generating functions χ₁ and χ₂ up to degree 9 (recall Eqs. (6) and (7))". But eqs. (6)–(7)
  sum j₂ ≤ 6, and GLS17 §2.2 says "up to degree 6". This is material: degree 9 changes the
  coefficients of degree ≥ 12 by a median of 22–69 % (`validation/sensitivity.json`). We use 6.
* **SJSU-E4 (new, possible imprecision).** SLG13 eq. (12) applies ½ to
  {χ_res, Σ_{j₂≥0} h_res_{0,j₂}}, but χ_res removes only degree 9. For the unremoved degree-11
  part the second-order Lie coefficient is 1. This affects degree 18 only (median 3 %, max
  ×320 on small coefficients). We follow the printed formula.
* **SJSU-E5 (new, description).** Appendix A is titled "up to order 2 in the masses", but its
  three-planet quartic coefficients require order ≥ 3 (§6.1). The H⁽ᴼ²⁾ of SLG13 must
  therefore keep Lie-series terms beyond order two.
* **Inherited typo, also in SLG13.** "3λ₁ − 5λ₅ − 7λ₃" (journal p. 7, three times; arXiv v1
  likewise), in addition to GLS17 p. 12.

## 7. Output (step 6)

**Measured.** [`applications/sjsu/data/sjsu18-o2.json`](../../applications/sjsu/data/sjsu18-o2.json)
is 3.2 MB, with SHA-256 in `data/MANIFEST.sha256` and its SOURCE file. It contains the complex
form (z), the real form (ξ, η), its four components, every parameter and choice, provenance,
precision and census.

| Census | complex (z, z̄) | real (ξ, η) |
|---|---|---|
| terms (degrees 2–18) | **7,941** = the charge-balanced bound Σ_{d=1}^{9} C(d+2,2)² | **38,466** = the reversible bound |
| by degree 2, 4, …, 18 | 9, 36, 100, 225, 441, 784, 1296, 2025, 3025 | 12, 66, 236, 651, 1512, 3108, 5832, 10197, 16852 |
| non-invariant / odd-η | 0 | 0 |

The polynomial is dense in the invariant reversible space: every allowed monomial occurs. The
scoping report's bounds are attained, and its "rotation symmetry" reduction is now an exact
property of the model, not an assumption. The dropped additive constant is
−5.3074·10⁻⁵ (recorded). Coefficient scales per degree: 9·10⁻⁵ (2), 1.8·10⁻² (4) …
1.4·10¹³ (18). At degree 18 the resonant μ⁴ part dominates.

**Precision (measured, `validation/precision.json`).** The published file is the mpmath
40-digit build (177 s). Against a 50-digit build it differs by ≤ 7.4·10⁻³⁶ at every degree,
so the 25 written digits are correctly rounded values of the model as defined. Cancellation
costs up to about 5 digits at degrees 14–18: long double reaches only 2.1·10⁻¹⁴, float64
3.4·10⁻¹¹. Before exact symmetrization the asymmetry c_PQ ≠ c_QP was ≤ 1.3·10⁻³⁶, and the
imaginary parts were 0.

**Regression test (measured).** `test_regression.py` checks the manifest, charge balance,
reversibility, components, complex↔real agreement, a from-scratch recomputation of degree ≤ 4
(5.2·10⁻¹⁷) and Laplace–Lagrange (2.4·10⁻¹⁹), all PASS in 1.5 s. `--full` recomputes all
7,941 coefficients in mpmath and agrees to 4.7·10⁻²⁵ (about 3 min).

**Sensitivity to open choices (measured, median / max relative change).**

| Variant | degrees 2–10 | 12–14 | 16–18 |
|---|---|---|---|
| χ degree 9 instead of 6 (SJSU-E3) | ≤ 10⁻¹⁶ | 0.22–0.69 / 2.6·10³ | 0.03–0.06 / 45 |
| Kepler n\* instead of corrected | 2.5·10⁻⁴–9·10⁻³ / 1.8 | 3·10⁻³ / 97 | 0.9–1.4 / 220 |
| eq. (12) weight 1 on the unremoved part (SJSU-E4) | 0 | 0 | 0.03 (degree 18) / 320 |
| a\* averaged over 3·10⁵ instead of 10⁶ yr | ≤ 10⁻⁵ / 3·10⁻³ | 10⁻⁵ / 0.2 | 3·10⁻³ / 0.4 |

So the coefficients of degree ≥ 12 are defined only up to these recipe choices, and the high
degrees are strongly resonance-dominated. A certificate built on SJSU18-O2 certifies *this*
polynomial; its relation to the true secular dynamics is a separate fidelity question
(scoping §4).

## 8. Deviations from the source, and choices

1. Strict order two in the masses for all degrees (SLG13's own numbers contain higher orders;
   §6.1). The order-3–5 values at degree 4 are given as a validation table, not as the model.
2. n\* corrected by ⟨∂f/∂L⟩ at zero eccentricity (interpretation of eq. (5); §4).
3. a\* from our N-body average (procedure as stated; value and length not published).
4. Table 1 read as Poincaré elements (§5.2).
5. χ₁, χ₂ to degree 6 (eqs. (6)–(7), GLS17); eq. (12) as printed.
6. The additive constant is dropped; reversibility and reality are enforced exactly after the
   check above.
7. No coefficient of the printed table was used as input. Appendix A is a test, not a fit.

## 9. Resources and reproduction

All heavy steps ran under `systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0
nice -n 10`, on ≤ 2 cores. Peak RSS was about 1 GB (the order study at N = 5). Measured CPU:
first-order expansion 12 s; model 17 s (long double) or 180 s (mpmath); N-body 10 min per Myr;
order study 1 h; precision check 10 min. Disk: about 60 MB under `~/kam-data/sjsu/`. Only the
model, small tables and scripts are committed; the first-order expansion (1.08 M terms) is
regenerable, and its hash is in `data/sjsu18-o2.SOURCE.txt`. Commands are in
[`applications/sjsu/README.md`](../../applications/sjsu/README.md#how-to-regenerate).

## 10. Owner questions

1. **Which model should phase 1 certify?** SJSU18-O2 (strict, published, well-defined), a
   higher-order Lie model closer to the printed numbers (truncation to be defined; degree 18 at
   order ≥ 3 needs a dedicated producer), or wait for the authors' file?
2. Send the draft email to the authors
   ([`SJSU-P0-email-draft.md`](../campaign/handoffs/SJSU-P0-email-draft.md))?
3. `CITATION.cff`: Zohar Komargodski's affiliation, and the public repository URL.
4. Should eq. (37)-type checks use Table 2 (as GLS17) or our Table 1 map (inconsistent with
   Table 2, §5.3) as the nominal initial point of later phases?

# SJSU gate 2: near-torus approximate integrals at the nominal point

2 November 2026. Lane SJSU (secular planar Sun–Jupiter–Saturn–Uranus), continuing
[sjsu-effective-stability.md](sjsu-effective-stability.md) §§2, 6 on the dataset
[`applications/sjsu`](../../applications/sjsu/README.md) (`SJSU18-O2`, v0.1.0).
Numerics only, in float64. **No certificate and no new frozen statement.** The companion
generic first-exit theorem (Lean, compiled) is described in §8.

**Verdict (measured, floating).** The phase-2 local numerical gate passes at the nominal
Table-1 point, using a *local torus chart*. The direct observables of the origin-centred chart
fail there, as the scout predicted.

- **Observables.** Literal Fourier–Taylor approximate integrals F₁, F₂, F₃ are built in modal
  polar coordinates by a Kolmogorov normal form plus a Birkhoff normal form around the nominal
  torus.
- **Bracket.** Their brackets with the **entire degree-18 Hamiltonian** are bounded on a tube of
  action width δ around that torus.
- **Confinement ratio.** This gives T = min_j (δ/2)/η_j:
  - ≈ **4.3·10¹² yr** at δ = 10⁻⁶;
  - ≥ 10¹⁰ yr for every tested δ from 10⁻⁸ to 3·10⁻⁶.
- **Margin.** That is a factor of 2–860 over the 5-Gyr research target across the range, about
  860 at its peak. Every truncation tail and the float64 noise floor are included as majorants.
- **Physical meaning.** For δ = 10⁻⁶ the tube keeps the eccentricities within these ranges
  (Uranus's AMD-only ceiling is 0.204):

  | Planet | Eccentricity range |
  |---|---|
  | Jupiter | [0.027, 0.061] |
  | Saturn | [0.011, 0.084] |
  | Uranus | [0.007, 0.062] |

| Evidence label | Meaning here |
|---|---|
| **measured** | float64 computation in this report's scripts; floating majorants, not enclosures |
| **estimated** | extrapolation or engineering judgement |
| **literature** | stated in the cited source |

## 1. Setting

**Hamiltonian and coordinates.**
- `SJSU18-O2`: 7,941 complex monomials z^a z̄^b, all rotation invariant, degrees 2–18.
- Conventions: {z_j, z̄_j} = −i, dz/dt = −i ∂H/∂z̄.
- The real symmetric quadratic block A is diagonalized by an orthogonal V (Jacobi): z = V w.
- Linear frequencies ν = (−1.12117, −0.196771, −0.111337)·10⁻⁴ rad/yr. The off-diagonal residual
  is 10⁻²⁰.

**Nominal point.** The nominal point is `xi_eta_secular` of
`validation/table2_map_poincare_order1.json` (the Table-1 policy decided on 1 November). Its
values:
- H(nominal) = −5.2298351635266·10⁻⁸, the same in z and w.
- Modal actions I⁰ = (3.1915, 6.6866, 0.28630)·10⁻⁴.
- AMD C = 1.0164·10⁻³.

**Integrals.**
- **Exact (proved, elementary).** The AMD C = Σ|z_j|² = Σ|w_j|² commutes with H exactly. Every
  monomial has Σk = 0, where k = a − b.
- **Measured.** The floating bracket {C, H} has coefficients up to 4.9·10⁻⁴. That is
  cancellation rounding on coefficients of size up to 1.4·10¹³ at degree 18.

**Size of the model at the nominal amplitude (measured).** Sum of |coefficient| times the modal
radii, per degree:

| Degree | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|---|
| Majorant | 4.9e-8 | 4.8e-9 | 2.1e-9 | 5.8e-11 | 9.5e-13 | 9.3e-15 | 5.4e-17 | 3.4e-19 | 1.7e-20 |

**The nominal orbit (measured).** RK4 over 4 Myr with h = 200 yr gives relative energy drift
9·10⁻⁸. The orbit is quasi-periodic, and frequency analysis of the modal coordinates gives
(1.35046651, 0.202832198, 0.115207067)·10⁻⁴ rad/yr. The modal actions oscillate as follows:

| Mode | Action range | Relative swing |
|---|---|---|
| Jupiter mode | [2.898, 3.370]·10⁻⁴ | about ±7.5% |
| Saturn mode | [6.489, 6.994]·10⁻⁴ | about ±3.6% |
| Uranus mode | [2.497, 3.305]·10⁻⁵ | about ±14% |

## 2. Why the origin chart fails on the full model

The scout's Birkhoff-about-the-origin observables (sjsu-effective-stability §3, eq. (4)) were
rerun on the full degree-18 model with the same polydisk geometry (`run_nf.py`).

**Measured, nominal r = 1:**
- K = 2: 1.7·10⁴ yr, at R = 1.3.
- K = 4, 6, 8: no positive gap on the tested R-grid.
- r = 0.3: 3.6·10⁵, 3.9·10⁷ and 7.5·10⁸ yr for K = 2, 6 and 8.

This is the scout's picture again, now on the recovered model.

**The reason (measured).**
- At the nominal amplitude the frequencies are shifted from their linear values by
  (2.29, 0.061, 0.039)·10⁻⁵ rad/yr.
- The smallest divisor of the origin normal form is |ν_S − ν_U| = 8.5·10⁻⁶.
- The amplitude-dependent shift of the first mode is about 2.7 times that divisor, so expanding
  about the circular state cannot reach the real orbit.

## 3. Construction (two stages)

Polar modal variables: w_j = √I_j e^{iq_j}, I_j = I*_j + p_j.

**Poisson structure.** The dataset's {w, w̄} = −i means {q_j, p_j} = −1. Every function depends
on the angles only through φ₁ = q₁ − q₃ and φ₂ = q₂ − q₃, because Σk = 0. Functions are stored
as Fourier–Taylor arrays c[m, k₁, k₂] (`ft.py`):
- p-degree ≤ L;
- Fourier hexagon |k₁| + |k₂| + |k₁ + k₂| ≤ K;
- products taken on an alias-free φ-grid.

**Engine check (measured).** H and three brackets agree with the polynomial engine to 12 digits
(`test_ft.py`).

**Stage 1 (`torus.py`): expansion about constant reference actions.**
- I* is the orbit mean, rescaled to the nominal AMD.
- H(I* + p, q) is expanded by binomial series to p-degree L.
- Kolmogorov steps remove the angle-dependent terms of p-degree 0 and 1, with the frequency
  left free and no translation step. Birkhoff steps then follow.
- F_j = p_j is pulled back through all generators.
- I* is recentred so that F(nominal) ≈ 0.
- **Measured:** Kolmogorov converges quadratically, with |A| going
  2.3e-10 → 7.3e-13 → 4.4e-17 → 1.2e-25 → 1.0e-40.
- **Measured:** the torus frequencies (1.35046694, 0.202832220, 0.115208141)·10⁻⁴ rad/yr agree
  with the 4-Myr frequency analysis to 3·10⁻⁷, 1·10⁻⁷ and 9·10⁻⁶ relative.

**The torus graph.** The torus through the nominal point is the graph p = τ(φ), obtained by
solving F(τ(φ), φ) = F(nominal) by Newton's method on a φ-grid. Its oscillation is about
±2.5·10⁻⁵ in the Jupiter and Saturn modes and about ±4·10⁻⁶ in the Uranus mode. This is the
"tube" that a constant-action expansion would have to straddle.

**Stage 2 (`torus2.py`): expansion about the torus graph.**
- **Lagrangian projection.** τ is projected onto its Lagrangian form c₀ + ∇_q S(φ). The
  non-gradient part has l¹ coefficient mass 8·10⁻¹⁹ (measured): the torus is Lagrangian to
  rounding.
- **Canonical shift.** The change (I, q) ↦ (u, q) with I = B₀(φ) + u and
  B₀ = I* + c₀ + ∇_q S is **exactly canonical**, since it is the time-one map of S(q).
- **Exact re-expansion.** H is re-expanded **exactly** about B₀(φ) at every grid angle. The
  binomial series in u uses the base B₀(φ), not a constant, so the action truncation now acts at
  the tube scale instead of the ±10% torus oscillation.
- Kolmogorov and Birkhoff are rerun with u-degree L ≤ 10 and Fourier K = 50. F_j = u_j is pulled
  back.
- **The literal observable** in the original variables is
  F_j(|w|² − B₀(φ), φ), with φ = (arg w₁ − arg w₃, arg w₂ − arg w₃).

**Measured, run `t2-L10-K50-LB8-v14`:**
- Kolmogorov |A|: 1.4e-18 → 3.4e-21 → 6.2e-26 → 6.3e-36.
- Birkhoff angle parts through degree 8, at ρ = 3·10⁻⁸: 6.8e-17 → … → 6.0e-36.
- Smallest divisor in the hexagon: |k·ω| = 8.5·10⁻⁷, at k = (1, −14, 13). This is the 1:14 ratio
  of the reduced frequencies.
- Total time 175 s on 18 cores.

## 4. What a certificate would check

The scheme is the mechanism of sjsu-effective-stability §2, with the tube playing the role of
the domain D.

**Tube.**
- τ̃(φ) is the stage-2 torus, F(τ̃(φ), φ) = c, where c = F(nominal); |τ̃| ≤ 5·10⁻¹³.
- T_κδ = {u = τ̃(φ) + v : |v_j| ≤ κδ}, with κ = 2.

**Sets.**
- D = {|F_j − c_j| < δ for all j} ∩ int T_κδ.
- Q = {|F_j − c_j| ≤ δ/2 for all j} ∩ T_κδ.
- Q contains the nominal point. It is a full-dimensional neighbourhood of the whole torus: all
  angles, a box of normalized actions, and a range of AMD values.

**Checks.**
1. **Tube inclusion (boundary separation).** On each face |v_j| = κδ we need
   |F_j − c_j| > δ. It suffices that κδ − ‖F_j − c_j − v_j‖ − δ > 0, with the norm being the
   majorant of the composed series. **Measured:** the margin is 0.58–0.82 δ for every δ in the
   table, for all three j. Hence ∂D lies on the F-faces only, as §2 (2) requires.
2. **Rates.** η_j ≥ sup over T_κδ of |{F_j, H}|, with H the full model.
   - **Measured** as a sum of four terms:
     - the majorant of the composed bracket series, truncated at v-degree 14 (Fourier coefficients
       of the grid composition);
     - plus the dropped degree > 14 products of F-derivatives and H-derivatives (degree-profile
       majorants);
     - plus binomial-tail majorants of ∂H beyond v-degree 14, with bases in [B_min, B_max] and the
       S-Hessian chain term;
     - plus everything below the float64 noise floor (next item).
   - **AMD check (measured).** The exact identity Σ_j {F_j, H} = 0 holds to 2·10⁻³¹.
3. **Noise floor.** The bracket values on the torus are about 4·10⁻²¹ (grid sup). The full-grid
   coefficient majorant is about 10⁻¹⁹. This is float64 rounding of H (|H| ≈ 5·10⁻⁸) spread over
   every Fourier mode by the spectral angle derivative. It scales with the grid (4× from 128² to
   256²) and is **counted in η** in the "full" column. A certificate in exact or interval
   arithmetic would remove it; that is an estimate.

## 5. Results

**Measured.** Run `t2-L10-K50-LB8-v14`: stage 2 with u-degree 10, Fourier K = 50, Birkhoff to
degree 8, v-degree 14 and κ = 2. In the table below:
- **T_full** counts the whole grid noise floor.
- **T_band80** sums the Fourier modes |k|₁ ≤ 80 instead. Both columns add the dropped-product
  and H-tail terms.
- **Remainder** is the measured Birkhoff-remainder contribution to η₃.

| δ (action) | T_full (yr) | T_band80 (yr) | Remainder (η₃) | Inclusion margin / δ |
|---:|---:|---:|---|---:|
| 1e-9 | 4.3e9 | 4.2e10 | below noise | 0.65 |
| 1e-8 | **4.3e10** | 4.2e11 | below noise | 0.65 |
| 1e-7 | **4.3e11** | 4.2e12 | below noise | 0.65 |
| 3e-7 | **1.3e12** | 1.3e13 | below noise | 0.63 |
| 1e-6 | **4.3e12** | 4.1e13 | 2e-22 at degree 9 | 0.65 |
| 3e-6 | **2.3e11** | 2.4e11 | 5e-18 at degree 9 | 0.63 |
| 1e-5 | 1.9e6 | 1.9e6 | series barely converge: κδ/B_U,min = 0.8 | 0.61 |

**Effect of the Birkhoff order (measured).** The lower-order run `t2-L8-K50-LB6-v12` gives the
same T for δ ≤ 3·10⁻⁷. After that:
- 2.7·10¹² yr at 10⁻⁶;
- 8.4·10⁹ yr at 3·10⁻⁶, where its degree-7 remainder dominates.

The working window grows with the Birkhoff order. The binding mode is Uranus, the smallest
action, with B_min = 2.5·10⁻⁵.

**Eccentricities (measured, vertex sampling of the δ = 10⁻⁶ tube).** e is computed from
Γ_j = |z_j|² = Λ*_j(1 − √(1 − e_j²)). Compare the AMD-only ceilings of
sjsu-effective-stability §4: 0.061, 0.096 and 0.204.

| Planet | Nominal e | Range on the torus | Range on the tube |
|---|---:|---:|---:|
| Jupiter | 0.04849 | [0.02708, 0.06085] | [0.02692, 0.06101] |
| Saturn | 0.05476 | [0.01082, 0.08414] | [0.01058, 0.08439] |
| Uranus | 0.04706 | [0.00826, 0.06071] | [0.00708, 0.06201] |

## 6. Independent validations

All of these are measured.

1. **Flow test (`verify_flow.py`).** The original degree-18 field was integrated by RK4
   (h = 20 yr, 100 kyr, energy drift 2·10⁻¹³). F_j was evaluated along the orbit.
   - From the nominal point: max |F_j(t) − F_j(0)| = (1.1, 0.17, 0.09)·10⁻¹⁶, while the modal
     actions swing by (2.9, 2.8, 0.26)·10⁻⁵.
   - From an off-torus start, with action offset (5, −5, 2)·10⁻⁷: F is conserved to 1·10⁻¹⁶, and
     the normalized offset u stays at (4.6, −4.6, 2.0)·10⁻⁷.
   - This checks the observables against the true dynamics, independently of the normal-form
     algebra, at the integrator's resolution.
2. **Frequencies.** Torus frequencies against the frequency analysis: see §3.
3. **Energy.** H re-expanded about B₀ reproduces H(nominal) to 1·10⁻²².
4. **Exact identities.** The AMD identity holds to 2·10⁻³¹; the Lagrangian test to 8·10⁻¹⁹.
5. **Robustness.**
   - Fourier order 40 vs 50 (run `t2-L10-K40-LB8-v14`): T_full is 4.23·10¹² vs 4.30·10¹² yr at
     δ = 10⁻⁶, and identical at 3·10⁻⁶.
   - u-degree 8 → 10 with Birkhoff order 6 → 8 changes T only through the degree-7 vs degree-9
     remainder (§5).
   - The full-grid noise floor scales with the grid (128² → 256²: ×4), as rounding noise must.

## 7. Comparison with the literature

**Literature.** GLS17 (§4.3 and Fig. 2) estimates about 10¹⁰ yr for action radius slightly
below 10⁻⁷. Their method is a Kolmogorov normal form followed by Birkhoff around the torus, with
majorants carried to action order 20 and the first omitted remainder term only. It is explicitly
not computer-assisted.

**Measured.** This report finds T ≥ 10¹⁰ yr from δ = 10⁻⁸ to 3·10⁻⁶ on the reconstructed
`SJSU18-O2`. The bound is **literal**: the bracket of fixed observables with the whole
polynomial, plus tails.

The two numbers concern different models and different radius conventions. They are consistent
in kind, and are **not** a reproduction of GLS17.

## 8. Consequences for phase 3 (certificate)

**The shape of the observables.** They are not polynomials in z. They are Fourier–Taylor
expressions in u_j = |w_j|² − B₀,j(φ) and e^{iφ}, with e^{iq_j} = w_j/|w_j|, where w = Vᵀz.
They are analytic on the tube, which stays at least 2.3·10⁻⁵ away from w_j = 0. The polynomial
certificate checker of sjsu-effective-stability §5 does not cover them.

**Estimated checker routes.**
- **(a)** A Lean Fourier–Taylor-model checker: exact rational coefficients, a φ-tube majorant,
  and composition with the trig polynomial B₀.
- **(b)** Multiply through by powers of |w_j| to get polynomial observables. They would be valid
  on the tube, but their size grows.

**Literal data size (measured).**
- Each F_j has 5.6·10⁵ stored coefficients, of which 2.0–2.3·10⁴ exceed 10⁻²⁵ in majorant
  weight at ρ = 10⁻⁶.
- S has 2,790 modes, 396 of them above 10⁻²⁰.
- Pruning changes F. The bracket must then be remeasured, but no step of the scheme depends on
  F being the exact normal-form pullback.

**First-exit theorem (proved, Lean).** `KAM/Application/Confinement/ApproxIntegral.lean` proves
a generic first-exit and continuation theorem from approximate integrals, for an open W with
compact closure of D. This is §2's (1)–(3) for any finite family F_j. It includes the Hamiltonian
case `hamiltonian_approxIntegrals_confinement`, which needs H to be C² on an open W, so it covers
W = {w_j ≠ 0} as needed here.
- Built on upstream `a535161d6` with `lake build KAM.Application.Confinement.ApproxIntegral`.
- `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` for all eight public
  theorems.
- The SJSU instance, i.e. checking its hypotheses for the literal F_j, is the phase-3 work.

**Owner decisions requested.**
1. Accept polar-coordinate Fourier–Taylor observables as the phase-3 route.
2. Fix the tube target. Recommendation: δ = 10⁻⁶ (relative width about 4% in the Uranus mode).
3. Choose between checker routes (a) and (b), with a sizing study before freezing.

## 9. Reproduce

Scripts are in [`scripts/sjsu/gate2`](../../scripts/sjsu/gate2/README.md). They need Python 3
with numpy; `poly.py` and `run_nf.py` use the standard library only.

```
python3 scripts/sjsu/gate2/run_nf.py --K 8                 # origin chart baseline (§2)
python3 scripts/sjsu/gate2/orbit.py 4e6 200                # orbit and frequency analysis
python3 scripts/sjsu/gate2/test_ft.py                      # engine check
python3 scripts/sjsu/gate2/torus.py --L 6 --K 30 --LB 3 --kol 5 --recenter 1 --G2 64 --Lu 3 --tag test
python3 scripts/sjsu/gate2/torus2.py --stage1 test --L 10 --K 50 --LB 8 --kol 4 --G2 128 --Lv 14 \
    --tag t2-L10-K50-LB8-v14                               # stage 2 and the table of §5 (~3 min)
python3 scripts/sjsu/gate2/verify_flow.py t2-L10-K50-LB8-v14 1e5 20            # §6.1
python3 scripts/sjsu/gate2/ecc.py t2-L10-K50-LB8-v14 1e-6 2                    # §5 eccentricities
```

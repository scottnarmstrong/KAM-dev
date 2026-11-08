# The Moon's spin rate stays within 2.755 % of its orbital rate forever (track SO, part 2)

**Status:** proved and sealed (proved on `main` 2026-10-31 08:18 UTC; frozen D49 and sealed D50 on 2026-10-31,
seal audit PASS WITH NOTES) · frozen ids `spinorbit.d40.lunar_spin_confinement.v1`, `spinorbit.d40.lunar_barriers.v1`,
`spinorbit.d40.lunarPLo_lt_lunarPHi.v1`, with the definitions `spinorbit.d40.{soEcc, soEps, soCoeffPoly, soA, soModes,
soV, soField, SoBarrier, lunarPLo, lunarPHi}.v1` · axioms: standard only (`propext`, `Classical.choice`, `Quot.sound`)

## In brief

The Moon turns once on its axis per orbit (synchronous rotation). In the classical spin–orbit model, a rigid,
slightly elongated Moon on a fixed elliptic orbit, the Earth's gravity gradient exerts a periodic torque on the
Moon's figure. The theorem shows that in this model, if the Moon's spin rate starts within 0.66 % of its orbital rate,
then it stays within 2.755 % of the orbital rate for all time, past and future, whatever the initial orientation.
The proof finds two invariant tori of the model by computer, one above and one below synchronous rotation, and has
Lean's kernel verify them through the certificate checker of part 1. Solutions cannot cross these tori, so they
stay trapped between them.

## Exactly what is proved

Lean: [`KAM.SpinOrbit.lunar_spin_confinement`](../../KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean#L32),
[`KAM.SpinOrbit.lunar_barriers`](../../KAM/Frozen/SpinOrbit/Theorems/LunarBarriers.lean#L33),
[`KAM.SpinOrbit.lunarPLo_lt_lunarPHi`](../../KAM/Frozen/SpinOrbit/Theorems/LunarWindow.lean#L28); definitions under
[`KAM/Frozen/SpinOrbit/Defs/`](../../KAM/Frozen/SpinOrbit/Defs/).

### The model

Units: angles in turns (one full rotation = 1), time t in orbital periods. The state is x = (q, p, φ) ∈ ℝ³: q is the
spin angle of the Moon's longest axis, p = q̇ is the spin rate divided by the orbital mean motion (synchronous
rotation is p = 1), and φ is the orbital phase (mean anomaly).

- Eccentricity e* = 549/10000 = 0.0549 ([`soEcc`](../../KAM/Frozen/SpinOrbit/Defs/SoEcc.lean)).
- Asphericity ε* = 69/200000 = 3.45·10⁻⁴, ε = (3/2)(B − A)/C with A < B < C the principal moments of inertia
  ([`soEps`](../../KAM/Frozen/SpinOrbit/Defs/SoEps.lean)).
- Seven forcing modes m = 1, …, 7 ([`soModes`](../../KAM/Frozen/SpinOrbit/Defs/SoModes.lean)) with coefficients
  A_m = A_m(e*) ([`soCoeffPoly`](../../KAM/Frozen/SpinOrbit/Defs/SoCoeffPoly.lean),
  [`soA`](../../KAM/Frozen/SpinOrbit/Defs/SoA.lean)), A_m = W(m/2, e)/2 in Celletti's notation:

  | m | A_m(e) | value at e* |
  |---|---|---|
  | 1 | −e/4 + e³/32 | −1.372·10⁻² |
  | 2 | 1/2 − 5e²/4 + 13e⁴/32 | 4.962·10⁻¹ |
  | 3 | 7e/4 − 123e³/32 | 9.544·10⁻² |
  | 4 | 17e²/4 − 115e⁴/12 | 1.272·10⁻² |
  | 5 | 845e³/96 − 32525e⁵/1536 | 1.446·10⁻³ |
  | 6 | 533e⁴/32 | 1.513·10⁻⁴ |
  | 7 | 228347e⁵/7680 | 1.483·10⁻⁵ |

- Potential ([`soV`](../../KAM/Frozen/SpinOrbit/Defs/SoV.lean)):
  V(q, φ) = −ε* Σ_{m=1}^{7} A_m cos(2π(2q − mφ)).
- Equations of motion ([`soField`](../../KAM/Frozen/SpinOrbit/Defs/SoField.lean)): q̇ = p, ṗ = −∂V/∂q(q, φ), φ̇ = 1,
  that is q̈ = −4π ε* Σ_m A_m sin(2π(2q − mφ)) with φ(t) = φ₀ + t. These are Hamilton's equations of the
  time-periodic Hamiltonian p²/2 + V(q, φ); with x = 2πq and τ = 2πt they are Celletti's equation
  d²x/dτ² = −ε Σ_m W(m/2, e) sin(2x − mτ).

A "solution" in the theorems is a map z : ℝ → ℝ³ with z′(t) = soField(z(t)) for every real t (a global solution).

### Theorem B: confinement of the spin rate (`lunar_spin_confinement`)

> For all real q₀, p₀, φ₀ with **0.9934 < p₀ < 1.0066** (`lunarPLo = 9934/10000`, `lunarPHi = 10066/10000`):
> 1. there is a global solution z with z(0) = (q₀, p₀, φ₀);
> 2. its spin rate satisfies **|p(t) − 1| ≤ 2755/100000** (2.755 %) **for every real t**;
> 3. every global solution y with y(0) = (q₀, p₀, φ₀) equals z.

No condition is placed on the angles q₀, φ₀. The constant 2755/100000 is uniform in the initial state and in t.

### Theorem A: the two barriers (`lunar_barriers`)

A barrier with values in [lo, hi] ([`SoBarrier lo hi`](../../KAM/Frozen/SpinOrbit/Defs/SoBarrier.lean)) is a function
P(q, φ) that is continuous, has period 1 in q and in φ, satisfies lo ≤ P ≤ hi, and is invariant: whenever y solves
the equations on an interval J and p = P(q, φ) holds at one time of J, it holds at every time of J.

> There are two barriers P₋ and P₊, both with values in **[0.97245, 1.02755]**, such that for all q, φ:
> P₋(q, φ) < P₊(q, φ), P₋(q, φ) < 0.9934 and 1.0066 < P₊(q, φ).

Since the graphs p = P±(q, φ) cannot be crossed, a solution starting between them stays between them, which with
the band gives Theorem B.

### The window lemma (`lunarPLo_lt_lunarPHi`)

9934/10000 < 10066/10000: the window of Theorem B is not empty.

## What is assumed and what is not claimed

- **Model, not the Moon.** The theorems concern this exact conservative model with exact rational parameters. It
  neglects tides and all dissipation, Fourier modes beyond m = 7 and eccentricity terms beyond the orders shown,
  variations of the orbit (the orbit is a fixed Kepler ellipse), the inclination of the spin axis (taken
  perpendicular to the orbital plane), and the uncertainty of e and ε. Nothing is asserted about the physical Moon.
- **No libration claim.** Only the spin rate is bounded; the orientation q − φ is not claimed to stay bounded (see
  part 3 for that).
- **Uniqueness** is stated among global solutions. Global existence holds for every initial state in the window.
- **Owner rulings.** The constant window replaces the graph-defined region of the source (ruling O1, D-SOF-2); the
  target band moved from 3 % (source) to 3.3 % (D30), then to about 2.7 % with barriers at N = 65 (D37, D38); the
  final literals 2.755 % and the window (0.9934, 1.0066) come from the certified data by fixed rounding rules, with
  the rule's tightness clause waived (D47); the window narrowed from the N = 40 window (0.9823, 1.0177), so the old
  and new statements do not imply each other (D-SOF-4, D40 Q10). Freeze D49, seal D50.
- The certified graphs actually lie in [0.97245, 0.99333] (lower) and [1.00668, 1.02755] (upper); the method's floor
  (the separatrix width) is about 2.62 %.

## Sources and proof

Model: A. Celletti, *Stability and Chaos in Celestial Mechanics* (Springer, 2010), eq. (7.55), and the project's
proposal and plan ([`SPIN-ORBIT-PLAN.md`](../campaign/design/SPIN-ORBIT-PLAN.md),
[`FREEZE-PROPOSAL-2.md`](../tracks/SO/FREEZE-PROPOSAL-2.md)). The proof works in the rotated frame Q₀ = q − φ, Q₁ = φ
with the Hamiltonian P₀²/2 − P₀ + P₁ + V(Q₀ + Q₁, Q₁) (time scaled by 2). Two invariant 2-tori with Diophantine
frequency vectors built from ν± = 1 ± 1/(65 + g), g = (√5 − 1)/2 (N = 65; Diophantine with τ = 1, γ = κ/67), were
computed numerically and checked by the v2 certifier `checkTorusCertificateV2 routeAV2` (refined route A, fixed-point
backend m/2⁹⁶; invariance errors 1.6·10⁻¹⁶ and 1.83·10⁻¹⁶, certified distances 5.78·10⁻¹¹ and 6.62·10⁻¹¹), see
[SO-1](SO-1.md). A separate graph certificate shows each torus is a graph p = P(q, φ) over both angles, and
invariance of the graph follows from uniqueness of solutions; global existence holds because the force is bounded
and Lipschitz. Assembly: [`lunar_barriers_65_v2` and `lunar_spin_confinement_65_v2`](../../KAM/SpinOrbit/LunarFinalR2V2.lean);
the frozen statements are proved by the providers in [`KAM/Provider/SpinOrbit/`](../../KAM/Provider/SpinOrbit/). The
certificate data, about 1,650 generated modules under [`KAM/SpinOrbit/Data/`](../../KAM/SpinOrbit/Data/), pass Lean's
kernel by `decide +kernel` and are built only in the opt-in library `KAMLunarBand` (D51). Decisions D30, D37, D38, D40, D44, D47, D49, D50 in [`DECISIONS.md`](../DECISIONS.md);
seal audit [`SO-FREEZE3-seal-audit.md`](../tracks/SO/audits/SO-FREEZE3-seal-audit.md).

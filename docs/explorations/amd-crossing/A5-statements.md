> Source: `RESEARCH/STATEMENTS.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Candidate statement contracts

These are **unapproved mathematical/Lean-shaped candidates**, not frozen declarations and not compiled Lean. They are intended to be converted to one-declaration anchor files only after owner choices, an independent statement audit, and elaboration checks in an authorized campaign. Current research was read-only against `/root/code/KAM` commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`.

The mathematical sources are LP17, [DOI 10.1051/0004-6361/201630022](https://doi.org/10.1051/0004-6361/201630022), §2.2 (9)–(11), §3 (26)–(39), §5.3; Nek77 Thm4.4 via `KAM.Nekhoroshev.partialConvex_nekhoroshev`; and `KAM/Nekhoroshev/Partial/NormalForm.lean:nf`, `Nonresonant.lean:nonresonant`. The added sharp-domain and osculating conclusions are campaign deductions, not literal published theorems.

## 1. Conventions and reusable definitions

All scalar vectors are `Fin n → ℝ`; the phase type is the existing `KAM.Planetary.Phase d = (Fin d → ℝ) × (Fin d → ℝ)`, positions first. Physical lengths use the Euclidean square-root formula, not the max norm on the ambient function space. The physical star has mass 1, planets have masses \(\mu m_i\), and \(G=1\). Require \(m_i>0\), \(m_i\le1\), and at least one \(m_i=1\). Thus \(\mu\) is the largest planet/star mass ratio. Canonical momenta are divided by \(\mu\); the existing `physicalAMD` is in these normalized action units, so physical AMD is \(\mu C\).

Reuse without changing meanings:

* `keplerEnergy`, `keplerAxis`, `keplerAction`, `keplerEccVector`, `ProgradeElliptic`, `physicalAMD`, `totalMomentum` for **planar canonical** elements;
* `IsMovingSolutionOn`, `MovingUniqueOn`, `actualMasses`, `barycentricPositions`, `barycentricVelocities`, `IsNewtonSolutionOn` for the planar moving-Sun/Newtonian conclusion;
* `KAM.IsDiophantine γ τ ω`, whose definition is \(\gamma/|k|_1^\tau\le|k\cdot\omega|\) for every nonzero integer k (`KAM/Frozen/Defs/IsDiophantine.lean`);
* `planetaryTimeExponent n = 2/(6n²−3n+14)` and `planetaryDriftExponent n = 3/(6n²−3n+14)` for the Nek77 route.

`totalMomentum` is scalar planar angular momentum. Neither it nor `IsNewtonSolutionOn` can silently be used as a spatial definition. Existing `keplerEccVector` uses canonical \(p_i/m_i\); its docstring does not establish the actual-velocity osculating bridge.

## 2. New definitions: exact intended bodies

The following list specifies every new public abbreviation/predicate used below. Auxiliary chart constructions in §8 are internal candidates. Guards are explicit in theorems; total Lean definitions may have irrelevant values outside their guarded domain.

### 2.1 Sharp geometry

1. **`OrderedAxes a`**: \((\forall i,0<a_i)\land(\forall i<j,a_i<a_j)\).
2. **`NormalizedMasses m`**: \((\forall i,0<m_i\land m_i\le1)\land\exists i,m_i=1\).
3. **`axisOfAction m I i`**: \((I_i/m_i)^2\).
4. **`circularAction m a i`**: \(m_i\sqrt{a_i}\).
5. **`eccDeficit u`**: \(1-\sqrt{1-u^2}\); theorem uses restrict \(u\in[0,1]\).
6. **`lpPairFeasible a i j`**: \(\{(u,v)\in[0,1]^2:a_i(1+u)\ge a_j(1-v)\}\).
7. **`lpPairThreshold m a i j`**: the infimum of the image of `lpPairFeasible` under \((u,v)\mapsto\mathrm{circularAction}_iD(u)+\mathrm{circularAction}_jD(v)\). For positive ordered axes and i<j it is an attained compact minimum. Do not use a numerically chosen critical root as the definition.
8. **`lpStrongThreshold m a`**: minimum of the finite set \(\{m_i\sqrt{a_i}:i\in\mathrm{Fin}\ n\}\cup\{\mathrm{lpPairThreshold}(i,j):j.val=i.val+1\}\). Require \(n\ge2\) in public results. Empty-index totalization is immaterial and must be documented when elaborated.
9. **`ActionCube m I0 r`**: \(\{I:\|I-I_0\|_\infty\le r\}\). **`ActionCubeAdmissible m I0 r`** means \(r\ge0\) and every I in that cube has \(I_i>0\) and `OrderedAxes (axisOfAction m I)`.
10. **`robustStrongThreshold m I0 r`**: \(\inf_{I\in\mathrm{ActionCube}} B(m,a(I))-nr\). Theorems require `ActionCubeAdmissible`; the compact minimum is then finite and attained.
11. **`PlanarLPInitial m A δ z0`**: `ProgradeElliptic m z0`, `keplerAxis m z0 ∈ A`, and `physicalAMD m z0 ≤ lpStrongThreshold m (keplerAxis m z0) - δ`.
12. **`CanonicalAnnuliSeparated m z`**, planar: every canonical periapse \(a_i(1-e_i)>0\), and \(a_i(1+e_i)<a_j(1-e_j)\) whenever `j.val = i.val+1`, with \(e_i=\mathrm{planeLength}(\mathrm{keplerEccVector}\ m\ z\ i)\). Spatial version uses the definitions in §2.2. This is stronger than mere nonintersection of differently oriented ellipses.

Lean-shaped compact minimum:

```lean
noncomputable def lpPairThreshold (m a : Fin n → ℝ) (i j : Fin n) : ℝ :=
  sInf ((fun uv : ℝ × ℝ =>
      circularAction m a i * eccDeficit uv.1 +
      circularAction m a j * eccDeficit uv.2) '' lpPairFeasible a i j)
```

This is a definition only. Attainment, nonemptiness and boundedness are theorem obligations, not fields assumed in a final stability premise.

### 2.2 Spatial counterparts

13. **`bodyVector3 q i`** extracts coordinates \(q_{3i},q_{3i+1},q_{3i+2}\) from `Fin (n*3) → ℝ`. **`spaceDot`**, **`spaceLength`**, **`spaceCross`** are the usual three-coordinate formulas; `spaceLength x = sqrt (∑ j, x j ^ 2)`.
14. **`spatialKeplerEnergy m z i`**: \(|p_i|^2/(2m_i)-m_i/|q_i|\). **`spatialKeplerAxis`**: \(-m_i/(2E_i)\). **`spatialKeplerAction`**: \(m_i\sqrt{a_i}\). **`spatialKeplerEccVector`**: \((|p_i|^2/m_i^2-1/|q_i|)q_i-(q_i\cdot p_i)p_i/m_i^2\).
15. **`spatialTotalMomentum z`**: \(\sum_i q_i\times p_i\in\mathbb R^3\). **`spatialAMD m z`**: \(\sum_i\Lambda_i-|\mathrm{spatialTotalMomentum}\ z|\).
16. **`SpatialElliptic m z`**: for every i, \(m_i>0\), \(|q_i|>0\), \(E_i<0\), and \(|q_i\times p_i|>0\). **`SpatialLPInitial`** is definition 11 with these spatial substitutions and the *same* scalar sharp threshold.
17. **`spatialMovingHamiltonian m μ`** is exactly formula (M) in PROOF-PLAN ([A4](A4-proof-plan.md)), with three-dimensional lengths/dots. **`IsSpatialMovingSolutionOn m μ J z`** means no stellar/pair collisions on J and `HasDerivAt z (hamiltonianVectorField (spatialMovingHamiltonian m μ) (z t)) t` for all \(t\in J\). **`SpatialMovingUniqueOn`** is uniqueness among such solutions with the same initial value on J, as in the existing planar definition.
18. **`barycentricPositions3`**: \(Q_0=-\mu\sum_i m_iq_i/(1+\mu\sum_i m_i)\), \(Q_{i+1}=Q_0+q_i\). **`barycentricVelocities3`**: \(V_0=-\mu\sum_i p_i\), \(V_{i+1}=p_i/m_i\). These are the center-of-mass-rest reconstruction for the canonical normalized momentum, not independent heliocentric Kepler velocities.
19. **`IsNewtonSolutionOn3 M J Q V`**: for all t in J, all bodies have distinct positions, \(\dot Q_i=V_i\), and \(\dot V_i=\sum_{j\ne i}M_j(Q_j-Q_i)/|Q_j-Q_i|^3\). Reuse the existing `actualMasses 1 m μ` for M.

### 2.3 Time, outcome and genuine osculating elements

20. **`expHorizon c a μ`**: \(\exp(c\mu^{-a})\); **`timeWindow T`**: `Set.Icc (-T) T`; **`nonresTimeExponent τ`**: \(1/(2(\tau+1))\). **`keplerFrequency a i`**: \(a_i^{-3/2}\), in radians per unit physical time.
21. **`PlanarLPOutcome m μ δ z0 T DΛ Da b d R eMax z`** is precisely the conjunction expanded in §5. It is a conclusion abbreviation, never an input assumption of Candidate B. **`SpatialLPOutcome`** is the literal spatial substitution listed there.
22. **`heliocentricVelocity m μ z i`**: \(p_i/m_i+\mu\sum_jp_j\), in dimension two or three as appropriate. **`osculatingAxis`**, **`osculatingEccVector`** use this velocity and \(\kappa_i=1+\mu m_i\) in (O2) of PROOF-PLAN. **`OsculatingAnnuliSeparated`** uses those axes and eccentricity-vector lengths in definition 12 and also requires negative osculating energy and eccentricity below one. No change to the existing canonical definitions is proposed.

## 3. Barrier theorems

The first contract is algebraic and dimension independent:

```lean
theorem lp_barrier_of_eccentricity_budget
    (hn : 2 ≤ n) (m a e : Fin n → ℝ) (C : ℝ)
    (hm : ∀ i, 0 < m i) (ha : OrderedAxes a)
    (he : ∀ i, e i ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : ∑ i, circularAction m a i * eccDeficit (e i) ≤ C)
    (hsafe : C < lpStrongThreshold m a) :
    (∀ i, 0 < a i * (1 - e i)) ∧
    (∀ i j, j.val = i.val + 1 → a i * (1 + e i) < a j * (1 - e j))
```

Physical adapters supply `hbudget` from the element/angular-momentum identities; no stability assumption is hidden in it. A quantitative compact corollary is essential:

For fixed n, positive m, compact nonempty A of ordered positive axes and \(\eta>0\), there exist \(d>0\), \(R>0\), \(0\le e_{max}<1\), **before a,e,C**, such that `a ∈ A`, `e ∈ [0,1]^n`, the budget inequality, and \(C\le B(m,a)-\eta\) imply all periapses \(\ge d\), all adjacent radial gaps \(\ge d\), all apoapses \(\le R\), and \(e_i\le e_{max}\). Empty feasible sets are harmless. This is a new compactness deduction from LP17, not a premise demanded from the owner.

Also freeze/approve separately as needed: compact attainment, positivity, continuity on positive masses/ordered axes, equality with the contact formulation, and equivalence of the all-star minimum to LP's innermost-star convention.

## 4. Candidate A: deterministic barrier, planar and spatial

Here a supplied action bound is deliberately the input of a deterministic implication. It is **not** an assumption to be carried into Candidate B.

For \(n\ge2\), positive m, an admissible action cube centered at \(I_0\) of radius r, and \(\eta>0\), take any interval J containing 0 and any path z on J. Assume:

1. planar `ProgradeElliptic m (z t)` for every \(t\in J\);
2. \(\Lambda(z0)=I_0\), \(\|\Lambda(z(t))-I_0\|_\infty\le r\);
3. \(L(z(t))=L(z0)\);
4. \(C(z0)\le\mathrm{robustStrongThreshold}(m,I_0,r)-\eta\).

Then \(C(z(t))\le B(m,a(z(t)))-\eta\) and `CanonicalAnnuliSeparated m (z t)` for every \(t\in J\). No equation of motion is needed for this algebraic version. Lean-shaped conclusion:

```lean
theorem planar_lp_barrier_on_action_tube ... :
  ∀ t ∈ J,
    physicalAMD m (z t) ≤ lpStrongThreshold m (keplerAxis m (z t)) - η ∧
    CanonicalAnnuliSeparated m (z t)
```

**Spatial Candidate A** replaces (1) by `SpatialElliptic`, uses spatial actions/AMD, and replaces (3) by vector angular-momentum conservation (norm conservation alone is sufficient for the inequality). Its conclusion uses `SpatialCanonicalAnnuliSeparated`. The proof is exactly \(C(t)\le C(0)+nr\) and the compact infimum definition.

An equivalent more convenient version assumes \(C(z0)\le B(m,a(z0))-\delta\) and \(nr+\Omega_B(r)\le\delta-\eta\). The modulus is on the specified admissible compact cube, not on the entire positive orthant.

**Continuation interpretation:** when applied to a maximal Newtonian solution, the regularity hypotheses above are used only on its initial regular interval. A stopped action estimate, (uniform) barrier bounds, and ODE continuation then rule out loss of ellipticity/prograde sign/collision or finite-time escape before the target horizon. Candidate A as written does not itself manufacture an action estimate or assert a solution exists for all of J. Candidate B below performs that additional argument and has no regularity-over-time premise.

## 5. Exact common conclusion for Candidate B

`PlanarLPOutcome ... z` means **all** of the following, with \(J=[-T,T]\):

* \(z(0)=z_0\), `IsMovingSolutionOn m μ J z`, and `MovingUniqueOn m μ J z`;
* `IsNewtonSolutionOn (actualMasses 1 m μ) J (fun t => barycentricPositions 1 m μ (z t).1) (fun t => barycentricVelocities 1 m μ (z t).2)`;
* for every \(t\in J\), `ProgradeElliptic m (z t)`, ordered canonical axes, \(L(z(t))=L(z0)\), and \(C(z(t))\le B(m,a(z(t)))-\delta/2\);
* for every i and t, \(e_i(t)\le eMax<1\), \(d\le a_i(t)(1-e_i(t))\), \(a_i(t)(1+e_i(t))\le R\), and every adjacent radial gap is at least d;
* for every i and t, \(|\Lambda_i(t)-\Lambda_i(0)|\le D_\Lambda\mu^b\), and \(|a_i(t)-a_i(0)|\le D_a\mu^b\).

These radial conclusions imply stellar and planet-pair physical distances bounded below by d and all barycentric pair distances bounded above by 2R. They need not be separately duplicated in a minimal frozen anchor. No planet is omitted from the AMD numerator.

`SpatialLPOutcome` substitutes definitions 14–19, including **vector** momentum conservation, and uses the same radial and drift conclusions. The interval predicate is intrinsic to the physical Hamiltonian; no assumption about a normal form, averaged flow, secular action, chart lifetime, or a supplied confinement witness occurs.

## 6. The three dynamical anchors

### 6.1 Planar strong-LP upgrade using Nek77

```lean
theorem planarStrongLPExponentialSafety
    (hn : 2 ≤ n) (m : Fin n → ℝ) (hm : NormalizedMasses m)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A) (hne : A.Nonempty)
    (haxes : ∀ a ∈ A, OrderedAxes a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ μstar c DΛ Da d R eMax : ℝ,
      0 < μstar ∧ 0 < c ∧ 0 < DΛ ∧ 0 < Da ∧ 0 < d ∧ 0 < R ∧
      0 ≤ eMax ∧ eMax < 1 ∧
      ∀ μ : ℝ, 0 < μ → μ < μstar →
      ∀ z0 : Phase (n * 2), PlanarLPInitial m A δ z0 →
      ∃ z : ℝ → Phase (n * 2),
        PlanarLPOutcome m μ δ z0
          (expHorizon c (planetaryTimeExponent n) μ)
          DΛ Da (planetaryDriftExponent n) d R eMax z
```

The source supplier is `partialConvex_nekhoroshev`, not an arithmetic theorem. There is **no nonresonance assumption**. This is a **new anchor**, not an amendment to `planetaryExponentialSafety`, whose `AMDBox` statement and bytes remain unchanged.

### 6.2 Planar nonresonant rate

```lean
theorem planarStrongLPNonresonantSafety
    (hn : 2 ≤ n) (m : Fin n → ℝ) (hm : NormalizedMasses m)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A) (hne : A.Nonempty)
    (haxes : ∀ a ∈ A, OrderedAxes a) (δ γ τ : ℝ)
    (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μstar c DΛ Da d R eMax : ℝ,
      0 < μstar ∧ 0 < c ∧ 0 < DΛ ∧ 0 < Da ∧ 0 < d ∧ 0 < R ∧
      0 ≤ eMax ∧ eMax < 1 ∧
      ∀ μ : ℝ, 0 < μ → μ < μstar →
      ∀ z0 : Phase (n * 2), PlanarLPInitial m A δ z0 →
      KAM.IsDiophantine γ τ (keplerFrequency (keplerAxis m z0)) →
      ∃ z : ℝ → Phase (n * 2),
        PlanarLPOutcome m μ δ z0
          (expHorizon c (nonresTimeExponent τ) μ)
          DΛ Da (1/2 : ℝ) d R eMax z
```

The arithmetic premise is only on the **initial** Kepler frequency. It is not imposed on every point of A or on the evolving frequency, and it contains no secular frequencies. The normal-form argument propagates only finite-cutoff divisor estimates on a small action ball. Fixing \(\tau=n-1/2\) gives a separate corollary with time exponent \(1/(2n+1)\).

### 6.3 Spatial Candidate B

Use exactly the quantifier order and fixed-data premises of §6.2, replace `Phase (n*2)` by `Phase (n*3)`, `PlanarLPInitial` by `SpatialLPInitial`, `keplerAxis` by `spatialKeplerAxis`, and `PlanarLPOutcome` by `SpatialLPOutcome`:

```lean
theorem spatialStrongLPNonresonantSafety ... :
  ∃ μstar c DΛ Da d R eMax : ℝ, PositiveConstants ... ∧
    ∀ μ : ℝ, 0 < μ → μ < μstar →
    ∀ z0 : Phase (n * 3), SpatialLPInitial m A δ z0 →
    KAM.IsDiophantine γ τ (keplerFrequency (spatialKeplerAxis m z0)) →
    ∃ z : ℝ → Phase (n * 3),
      SpatialLPOutcome m μ δ z0
        (expHorizon c (nonresTimeExponent τ) μ) DΛ Da (1/2 : ℝ) d R eMax z
```

`PositiveConstants ...` here is only typographical shorthand for the explicit conjunction in §6.2, not a proposed opaque definition. No initial reference plane or inclination bound is an extra premise: the invariable plane and the prograde chart domain are consequences of the strong threshold. The proof uses \(2n\) slow pairs but n fast angles. A spatial Nek77 analogue is a possible later corollary, not necessary to obtain Candidate B and not included as an additional mandatory campaign anchor.

## 7. Actual osculating no-crossing corollary

For each of §6.1–3, with **the same source premises**, there exist positive constants of the same dependencies (possibly smaller \(\mu_*\), d and larger bounds) such that the full corresponding LP outcome holds and

```lean
∀ t ∈ timeWindow (expHorizon c exponent μ),
  OsculatingAnnuliSeparated m μ (z t)
```

In full mathematics this includes \(E_i^{osc}(t)<0\), \(e_i^{osc}(t)<1\), \(a_i^{osc}(t)(1-e_i^{osc}(t))\ge d/2\), and
\[
 a_{i+1}^{osc}(t)(1-e_{i+1}^{osc}(t))-
 a_i^{osc}(t)(1+e_i^{osc}(t))\ge d/2>0.
\]

The standalone bridge lemma is: for any **fixed compact subset of the canonical elliptic collision-free phase domain**, with canonical energies bounded away from zero, there exist \(\mu_0,C_{osc}>0\), before \(\mu\) and z, such that for \(0<\mu<\mu_0\), all z in that compact set have negative osculating energies and the differences of canonical/osculating axes and eccentricity vectors are at most \(C_{osc}\mu\). This is a pointwise compact estimate; it introduces no error growing with the exponential horizon. Initial data specified in observational elements require a separate input-coordinate conversion with its own margin budget.

## 8. Internal definitions needed by the proof, not extra premises

* A family of action centers and slow sets \(S_c=\{A(x)\le B(m,a(I_c))-\delta/2\}\), with enlarged level \(B_c-\delta/4\); the normal-form block uses `PartialBlock` unchanged.
* A uniform safe-cylinder witness with **only geometric/analytic data** derived from fixed parameters: action/slow/angle collars, Fourier norm F, and complex frequency bound L. It is proved to exist, never requested as a public Candidate B hypothesis.
* Spatial Poincaré map on \(\Gamma_i=(\xi_i^2+\eta_i^2)/2<\Lambda_i\), \(Z_i=(u_i^2+v_i^2)/2<2(\Lambda_i-\Gamma_i)\), regular at circular/coplanar states; chart identities \(G_i=\Lambda_i-\Gamma_i\), \(H_i=G_i-Z_i\). The strong-domain proof uses the smaller region \(\Gamma_i+Z_i<\Lambda_i\).
* Proper rotation action on positions/momenta, with an alignment lemma for nonzero total angular momentum. This is a proof construction, not a reduction imposed on the public phase space.
* An internal stopped LP action-bound adapter and first-exit theorem, parallel to `Planetary/Exponential/Stopped.lean:stopped` and `AMD/Confinement.lean:amd`. Its stopping predicate must be expanded and discharged before sealing any §6 anchor.

## 9. Owner decision register

These are launch decisions, **not permission requests that interrupt this research**. Recommendations are explicit so the design is reviewable.

| Decision | Recommended contract | Consequence of another choice |
|---|---|---|
| Coordinates | Heliocentric canonical Poincaré, exact recoil Hamiltonian | Jacobi requires a different element/AMD dictionary and osculating bridge; do not switch mid-proof |
| Threshold | Strong LP threshold with fixed absolute normalized margin δ | Weak threshold permits stellar collision and does not give the required analytic compactness |
| Mass scaling | Star=G=1, physical masses \(\mu m_i\), fixed positive m, max m=1 | General star/G possible via an explicit dimensional rescaling corollary; no uniformity as mass ratios tend to zero |
| Arithmetic | Free \(\tau>n-1\), \(\gamma>0\) fixed, initial radian Kepler frequency | Add \(\tau=n-1/2\) corollary for the advertised exponent; period-one internal gamma is \(\gamma/(2\pi)\) |
| Time form | Symmetric \(|t|\le e^{c\mu^{-a}}\), normalized physical time | A prefactor is possible but must be declared; practical units need a length/time normalization |
| Crossing notion | Strict separation of instantaneous radial annuli; actual-velocity osculating corollary | Geometric nonintersection alone is weaker; finite stellar radii or physical planet radii require additional data |
| Initial data | Canonical full phase state; all planets included | Observational osculating boxes require a verified input adapter; RV minimum masses do not determine mutual inclinations |
| Uniformity | Compact A, fixed δ, masses and arithmetic constants; all phases/secular states | Letting δ vanish or axes escape a compact set changes the statement and can meet known instability regimes |
| Planar vs spatial sequence | Planar sharp-LP Nek77 anchor first, nonresonant planar second, spatial third | Spatial-first delays the cheapest meaningful theorem behind a substantial chart package |
| Relation to P-EXP-SAFE | New separately versioned anchor and provider | Existing frozen P-EXP-SAFE must not be edited or silently broadened |
| Quantitative deliverable | Separate finite-cutoff certificate theorem after qualitative closure | Numerical practicality does not follow from existential \(\mu_*\); actual-system certification needs observational/model scope |

The co-author should confirm that “no secular hypotheses” means unrestricted evolution inside the strong-AMD budget, rather than stability of the averaged motion; that fixed δ is acceptable; and whether the spatial/osculating statements are mandatory for the first paper or staged follow-ups. These choices are mathematically substantive and should be recorded before frozen signatures are approved.

# Strong-AMD exponential safety: the Laskar–Petit threshold (track LP)

**Status:** proved and sealed (frozen and sealed 2026-11-01: decision D62 for LP0–LP2 and the 34 characterization
theorems, D64 for the two LP3 statements) · 41 frozen theorems: the 7 headline anchors
`planetary.d59.planar_strongAMD_barrier.v1`, `planetary.d59.planar_strongAMD_exponentialSafety.v1`,
`planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1`,
`planetary.d59.spatial_strongAMD_exponentialSafety.v1`,
`planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1`,
`planetary.d59.planar_strongAMD_exponentialSafety_noArith.v1`,
`planetary.d59.spatial_strongAMD_exponentialSafety_noArith.v1`, plus 34 characterization theorems
(`planetary.d59.*`, listed below) · axioms: standard only (`propext`, `Classical.choice`, `Quot.sound`)

## In brief

The angular momentum deficit (AMD) of a planetary system measures how far its orbits are from being circular and
coplanar. Laskar and Petit (2017) observed that if the AMD is below a critical value, no exchange of eccentricity
and inclination between the planets can make two orbits touch or a planet reach the star, and conjectured that such
systems are stable in practice away from resonances. Track LP proves an asymptotic form of this mechanism for the
exact Newtonian problem of a star and n ≥ 2 planets, in the plane and in space: if the AMD starts a fixed margin below
the strong threshold, the planetary masses are small, and the initial mean motions are Diophantine, then for an
exponentially long time the semi-major axes barely move, the AMD stays below the threshold and the orbits stay in
ordered, separated annuli, so there is no collision and no orbit crossing. Nothing is assumed about the slow (secular)
dynamics, which may be chaotic. A second pair of theorems drops the Diophantine condition at the cost of
Nekhoroshev's weaker exponents.

## Exactly what is proved

### Setting and definitions

- **Model.** Units with G = 1 and star mass 1; planet masses μν_i with ν_i > 0. Heliocentric positions q_i ∈ ℝ^d
  (d = 2 or 3) and rescaled momenta p_i (physical momentum μp_i), symplectic form Σ dp_i ∧ dq_i, physical time:

  ```
  H_μ = Σ_i ( |p_i|²/(2ν_i) − ν_i/|q_i| ) + μ ( |Σ_i p_i|²/2 − Σ_{i<j} ν_i ν_j/|q_i − q_j| ).
  ```

  In the plane this is the frozen `movingHamiltonian 1 1 ν μ` of track P ([P.md](P.md)); in space it is
  `spatialHamiltonian ν μ`. A *moving solution on J* solves Hamilton's equations at every t ∈ J (two-sided
  derivatives, also at the ends of a closed interval) with q_i ≠ 0 and q_i ≠ q_j. It is *unique on J* if every moving
  solution on an open interval U ∋ 0 with the same initial state agrees with it on U ∩ J. The *barycentric
  reconstruction* x₀ = −μ(1 + μΣν_i)⁻¹ Σ ν_i q_i, x_i = x₀ + q_i, v₀ = −μΣp_i, v_i = p_i/ν_i must solve Newton's
  equations ẍ_j = Σ_{k≠j} M_k (x_k − x_j)/|x_k − x_j|³ with masses M = (1, μν₁, …, μν_n).
- **Canonical elements.** With v_i = p_i/ν_i: E_i = |v_i|²/2 − 1/|q_i| (Lean stores ν_iE_i), a_i = −1/(2E_i),
  Λ_i = ν_i √a_i, eccentricity vector e⃗_i = (|v_i|² − 1/|q_i|) q_i − (q_i·v_i) v_i, e_i = |e⃗_i|, perihelion and
  aphelion r_i^± = a_i(1 ± e_i), L_i = q_i × p_i, L = Σ L_i. **Strong AMD:** C = Σ_i Λ_i − |L| (absolute value of
  the scalar L in the plane, Euclidean length of the vector L in space). These are used on *canonical states*:
  q_i ≠ 0 and E_i < 0 for every i.
- **Osculating elements** (the ellipse through q_i tangent to the actual heliocentric velocity). V_i = p_i/ν_i + μΣ_j p_j,
  k_i = 1 + μν_i, E_i^osc = |V_i|²/2 − k_i/|q_i|, a_i^osc = −k_i/(2E_i^osc),
  e⃗_i^osc = ((|V_i|² − k_i/|q_i|) q_i − (q_i·V_i) V_i)/k_i, e_i^osc = |e⃗_i^osc|, r_i^{osc,±} = a_i^osc(1 ± e_i^osc).
  *Osculating states:* μ > 0, q_i ≠ 0, E_i^osc < 0 and e_i^osc < 1.
- **Chamber and thresholds.** a_i(Λ) = (Λ_i/ν_i)²; the chamber is 𝒬 = {Λ : Λ_i > 0, a₁(Λ) < ⋯ < a_n(Λ)};
  D(u) = 1 − √(1 − u²). For Λ ∈ 𝒬 and i < j,

  ```
  B_ij(Λ) = inf { Λ_i D(u) + Λ_j D(v) : u, v ∈ [0,1],  a_j(Λ)(1 − v) ≤ a_i(Λ)(1 + u) },
  B_cross(Λ) = min_{i} B_{i,i+1}(Λ),     B(Λ) = min( B_cross(Λ), min_i Λ_i ).
  ```

  B_ij is the least combined deficit at which the annuli of planets i and j can meet; Λ_i is the deficit of a radial
  orbit of planet i (e_i = 1). B is the *strong threshold*. All three are defined for n ≥ 2 on 𝒬.
- **Diophantine.** ω ∈ ℝ^n is (γ, τ)-Diophantine if |k·ω| ≥ γ/|k|₁^τ for all k ∈ ℤ^n \ {0}. The condition is
  imposed on the initial mean motions ω_i = ν_i³/Λ_i³ = a_i^(−3/2).
- **Norms.** ‖·‖ on vectors of actions or axes is the max norm.

### LP0: the sharp static barrier ([`planar_strongAMD_barrier`](../../KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean))

**Data:** n ≥ 2, ν_i > 0, a compact set U ⊂ 𝒬, a margin m > 0. **Conclusion:** there are d* > 0, d_pair > 0 and a
compact set K of planar states, each collision-free with all E_i < 0, such that

1. (static) for every Λ ∈ U and e ∈ [0,1]^n with Σ_i Λ_i D(e_i) ≤ B(Λ) − m: a_i(Λ)(1 − e_i) ≥ d* for all i, and
   a_{i+1}(Λ)(1 − e_{i+1}) − a_i(Λ)(1 + e_i) ≥ d_pair for i < n;
2. (dynamical states) every canonical state z with Λ(z) ∈ U and C(z) ≤ B(Λ(z)) − m lies in K and satisfies
   r_i^− ≥ d*, r_{i+1}^− − r_i^+ ≥ d_pair, |q_i| ≥ d*, |q_i − q_j| ≥ d_pair (i ≠ j), |L_i| ≥ m and L_i L > 0
   (every planet turns in the same sense as the total).

The constants depend only on (n, ν, U, m).

### LP1: planar exponential safety ([`planar_strongAMD_exponentialSafety`](../../KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean))

**Data:** n ≥ 2; ν with ν_i > 0, max_i ν_i = 1; a compact set 𝒜 of axis vectors with 0 < a₁ < ⋯ < a_n; δ > 0;
γ > 0; τ > n − 1.

**Conclusion.** There are positive constants μ₀, c, T₀, A_Λ, A_a, d*, d_pair, A_osc, A_el, depending only on the
data and satisfying A_osc μ₀ ≤ d*/2 and 2A_osc μ₀ ≤ d_pair/2, such that for every μ ∈ (0, μ₀] and every planar
canonical state z₀ with

```
a(z₀) ∈ 𝒜,    ω(Λ(z₀)) (γ, τ)-Diophantine,    C(z₀) ≤ B(Λ(z₀)) − δ,
```

and T = T₀ exp(c μ^(−1/(2(τ+1)))), there is a moving solution z on [−T, T] with z(0) = z₀, unique on [−T, T], whose
barycentric reconstruction solves Newton's equations on [−T, T], and for every t ∈ [−T, T] (all elements at time t,
all i ≠ j, adjacent pairs i < n):

- *AMD margin:* z(t) is a canonical state, Λ(t) ∈ 𝒬 and C(t) ≤ B(Λ(t)) − δ/2;
- *drift:* ‖Λ(t) − Λ(0)‖ ≤ A_Λ √μ, ‖a(t) − a(0)‖ ≤ A_a √μ, |C(t) − C(0)| ≤ n A_Λ √μ;
- *separation:* r_i^− ≥ d*, r_{i+1}^− − r_i^+ ≥ d_pair, |q_i| ≥ d*, |q_i − q_j| ≥ d_pair;
- *osculating orbits:* z(t) is an osculating state, a_i^osc > 0, r_i^{osc,−} ≤ |q_i| ≤ r_i^{osc,+},
  |a_i^osc − a_i| + |e⃗_i^osc − e⃗_i| ≤ A_el μ, |r_i^{osc,±} − r_i^±| ≤ A_osc μ, r_i^{osc,−} ≥ d*/2 and
  r_{i+1}^{osc,−} − r_i^{osc,+} ≥ d_pair/2.

### LP1-H, LP2, LP2-H

- **LP1-H** ([`planar_strongAMD_exponentialSafety_halfInteger`](../../KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean)):
  LP1 with τ = n − 1/2 fixed, so T = T₀ exp(c μ^(−1/(2n+1))).
- **LP2** ([`spatial_strongAMD_exponentialSafety`](../../KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean)):
  LP1 in space, word for word, with states in ℝ^{3n} × ℝ^{3n}, the spatial Hamiltonian and Newton equations, vector
  angular momenta (C = ΣΛ_i − |L| with |L| the Euclidean length) and the same thresholds and chamber. There is no
  prograde or small-inclination hypothesis.
- **LP2-H** ([`spatial_strongAMD_exponentialSafety_halfInteger`](../../KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean)):
  LP2 with τ = n − 1/2.

### LP3: no arithmetic condition

[`planar_strongAMD_exponentialSafety_noArith`](../../KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean) ·
[`spatial_strongAMD_exponentialSafety_noArith`](../../KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean).
LP1 and LP2 without γ, τ and without the Diophantine hypothesis, with Nekhoroshev's exponents
a_n = 2/(6n² − 3n + 14) and b_n = 3a_n/2 = 3/(6n² − 3n + 14):

```
T = T₀ exp(c μ^(−a_n)),   ‖Λ(t) − Λ(0)‖ ≤ A_Λ μ^(b_n),   ‖a(t) − a(0)‖ ≤ A_a μ^(b_n),   |C(t) − C(0)| ≤ n A_Λ μ^(b_n).
```

Every other clause (AMD margin δ/2, separations, osculating bounds of order μ, existence, uniqueness, Newton) is
unchanged; the constants depend on (n, ν, 𝒜, δ).

### Characterization theorems (34)

These pin down the meaning of the frozen definitions; each is a sealed frozen theorem.

- **Thresholds** ([`StrongAMD/Theorems`](../../KAM/Frozen/Planetary/StrongAMD/Theorems)): for Λ ∈ 𝒬 and i < j,
  B_ij(Λ) is attained: it is the least element of the set of values of Λ_i D(u) + Λ_j D(v) on the feasible set
  (`orderedPairThreshold_isLeast`), and that least value is unique (`orderedPairThreshold_existsUnique_value`);
  B_cross(Λ) is the least of the adjacent B_{i,i+1}(Λ) (`orderedCrossThreshold_isLeast`); B(Λ) is the least element
  of {B_{i,i+1}(Λ)} ∪ {Λ_i} (`orderedStrongThreshold_isLeast`).
- **Planar canonical states:** a_i > 0; e_i ≤ 1; r_i^− ≤ |q_i| ≤ r_i^+; C ≥ 0; Σ_i Λ_i D(e_i) ≤ C
  (`sourceKepler_axis_pos`, `sourceKepler_ecc_le_one`, `sourceKeplerPeri_le_planeLength`,
  `planeLength_le_sourceKeplerApo`, `sourceStrongAMD_nonneg`, `sum_action_mul_eccDeficit_le_sourceStrongAMD`).
- **Planar osculating states:** a_i^osc > 0; r_i^{osc,−} > 0; r_i^{osc,−} ≤ |q_i| ≤ r_i^{osc,+} (`sourceOscAxis_pos`,
  `sourceOscPeri_pos`, `sourceOscPeri_le_planeLength`, `planeLength_le_sourceOscApo`).
- **Spatial canonical states** ([`Spatial/Theorems`](../../KAM/Frozen/Planetary/Spatial/Theorems)): a_i > 0;
  Λ_i > 0; Λ_i² = ν_i² a_i; e_i² = 1 − |L_i|²/Λ_i²; 0 ≤ e_i ≤ 1; |L_i| = Λ_i √(1 − e_i²); |L_i| ≤ Λ_i;
  r_i^− ≤ |q_i| ≤ r_i^+; C ≥ 0; Σ_i Λ_i D(e_i) ≤ C (the twelve `spatialSourceKepler*`,
  `spatialSourcePlanetAngularMomentum_*`, `spatialSourceStrongAMD_nonneg`, `spatialSourceAction_mul_eccDeficit_le`).
- **Spatial osculating states:** k_i > 0; E_i^osc < 0; 0 ≤ e_i^osc < 1; a_i^osc > 0; r_i^{osc,−} > 0;
  r_i^{osc,−} ≤ |q_i| ≤ r_i^{osc,+} (the eight `spatialSourceOsc*`; E^osc < 0 and e^osc < 1 restate the carrier).

## What is assumed and what is not claimed

- **Owner rulings (D59).** The AMD is C = ΣΛ − |L|, orientation-free, with no prograde premise (deviation LP-D-01:
  track P's signed AMD ΣΛ − L forces L > 0). Every meaning-carrying definition lives on its source carrier (𝒬,
  canonical states, osculating states) with the characterizations above. The normalization max ν = 1 is kept in the
  safety anchors (a general-mass version is an ordinary theorem, not frozen). τ > n − 1 is free, with τ = n − 1/2 as
  a corollary. "No crossing" means the canonical annuli, all pair distances and the actual-velocity osculating annuli
  (with half gaps).
- **Hypotheses are on the initial state only:** canonical state, axes in 𝒜, AMD at least δ below B, and (LP1, LP2)
  Diophantine mean motions. There is no hypothesis on eccentricities, inclinations or the secular flow.
- **Not claimed.** The constants are not explicit, so nothing is certified for given masses (the inner Solar
  System is AMD-unstable by Laskar–Petit's own estimate). No chaotic orbit is constructed. Nothing is said beyond
  |t| ≤ T, or about states above the threshold. The geometric sharpness of B (at the threshold two orbits, or an orbit
  and the star, can touch) is argued in the paper but is not a Lean theorem (deviation LP-D-02); in Lean, B is the
  attained minimum of the static problem above. The model is the Newtonian point-mass problem with fixed mass ratios.
- **Other recorded deviations:** LP-D-03 (typing of the spatial chart), LP-D-04 (the normal form is obtained through
  the repository's finite-cutoff engine, route L13; the alternative Lemma 9–12 route of the source is not formalized).
  Candidate errata LP-E-01…08 in the source manuscript are listed in the README.

## Sources and proof

The conjecture: J. Laskar and A. C. Petit, *AMD-stability and the classification of planetary systems*, A&A 605, A72
(2017), §3 (thresholds §3.2, §5). Nekhoroshev 1977, Theorem 4.4 and §12 (for LP3). The proof was written for this
project: source manuscript [`docs/tracks/LP/source/MAIN.md`](../tracks/LP/source/MAIN.md) with its
[amendments](../tracks/LP/source/AMENDMENTS.md), audited PASS WITH NOTES; paper
[`papers/LP/main.pdf`](../../papers/LP/main.pdf); exploration and history
[`docs/explorations/amd-crossing/README.md`](../explorations/amd-crossing/README.md).

Proof route. Exact angular-momentum conservation gives C(t) − C(0) = Σ_i (Λ_i(t) − Λ_i(0)), so a slow drift of the
Kepler actions controls the total AMD whatever the eccentricities and inclinations do; no secular trajectory is
followed. The static barrier (LP0) solves the two-planet contact problem (minima attained, B continuous) and turns
C ≤ B − m into annulus separations. In regular Poincaré charts (planar, and spatial on the region prograde with
respect to L, which the AMD bound forces), on a complex neighbourhood of the whole allowed sublevel, the repository's
nonresonant normal form (track N) gives a stopped drift of order √μ over T₀ exp(c μ^(−1/(2(τ+1)))). A first-exit
argument on the threshold sublevel, using the conservation identity and the continuity of B, extends this to the full
interval; the osculating clauses follow from |V_i − p_i/ν_i| = O(μ). For LP3 the stopped drift comes instead from the
sealed partially convex Nekhoroshev theorem applied cell by cell. Freeze record:
[`docs/tracks/LP/FREEZE.md`](../tracks/LP/FREEZE.md) · dependency graph:
[`docs/graph/LP/DEPGRAPH.md`](../graph/LP/DEPGRAPH.md).

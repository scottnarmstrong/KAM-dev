# Planetary KAM, exponential safety and the secular box (track P)

**Status:** proved and sealed (frozen 2026-10-27, decisions D20 and D25; last seal 2026-10-29) · frozen ids
`planetary.properlyDegenerateKAM.v1`, `planetary.planarTwoPlanetKAM.v1`, `planetary.fixedSunPlanetaryKAM.v1`,
`planetary.d25.amdConfinement.v1`, `planetary.d25.planetaryExponentialSafety.v1`,
`planetary.d25.secularBoxSafety.v1`, `planetary.d25.secularBoxAtCitedMasses.v1` · axioms: standard only
(`propext`, `Classical.choice`, `Quot.sound`)

## In brief

A planetary system is a star and several much lighter planets attracting each other by Newton's law. Track P proves
seven statements about such systems in the plane. Three are KAM theorems: a general theorem for "properly degenerate"
Hamiltonians, and two applications to Newton's equations, which give a set of positive volume of initial conditions
whose motions are quasi-periodic for all time, never collide and keep all mutual distances bounded. Two are
exponential-time statements: for small planetary masses, every solution starting near circular, well separated orbits
stays safe for a time exp(c μ^(−a)). The last two concern the averaged (secular) Sun–Jupiter–Saturn model with an
explicit box of initial elements. The track LP statements, which sharpen the exponential result, are in
[LP.md](LP.md).

## Exactly what is proved

### Common setting

- **Coordinates.** A phase point is a pair (q, p) of vectors in ℝ^d × ℝ^d (positions first). For n planets in the
  plane d = 2n; q_i ∈ ℝ² is the heliocentric position of planet i and p_i ∈ ℝ² its rescaled momentum. Physical
  lengths |·| are Euclidean; "volume" is Lebesgue measure in these coordinates; the norm ‖·‖ on a coordinate space is
  the max norm.
- **Hamilton's equations.** z(t) = (q, p) solves Hamilton's equations for H at time t if H is differentiable at z(t)
  and z has derivative (∂H/∂p, −∂H/∂q) at t (a two-sided derivative, also at the ends of a closed interval).
- **Moving-Sun model** (Féjoz 2004 (28), G restored). With a gravitational constant G > 0, star mass m₀ > 0, planet
  weights m_i > 0 and mass ratio μ, the actual masses are (m₀, μm₁, …, μm_n) and

  ```
  H_mov(q,p) = Σ_i [ (1/m_i + μ/m₀)|p_i|²/2 − G m₀ m_i/|q_i| ] + μ Σ_{i<j} [ p_i·p_j/m₀ − G m_i m_j/|q_i − q_j| ].
  ```

  The barycentric reconstruction is x₀ = −μ(m₀ + μΣm_i)⁻¹ Σ m_i q_i, x_i = x₀ + q_i, v₀ = −(μ/m₀)Σ p_i,
  v_i = p_i/m_i. "Newton's equations" means ẋ_j = v_j and v̇_j = G Σ_{k≠j} M_k (x_k − x_j)/|x_k − x_j|³ with
  M = (m₀, μm₁, …, μm_n), with no two bodies at the same point.
- **Collision-free.** q_i ≠ 0 and q_i ≠ q_j for i ≠ j. **Pair bounds** PairBounds(d, D) for a list of points: every
  two distinct points are at distance in [d, D].
- **D25 conventions** (statements 4–7): G = m₀ = 1. A *moving solution on J* solves Hamilton's equations for
  H_mov = `movingHamiltonian 1 1 m μ` at every t ∈ J and is collision-free there. It is *unique on J* if every moving
  solution w on an open interval U ∋ 0 with w(0) = z(0) agrees with z on U ∩ J. The Kepler elements of planet i are
  E_i = |p_i|²/(2m_i) − m_i/|q_i|, a_i = −m_i/(2E_i), Λ_i = m_i √a_i, the eccentricity vector
  e⃗_i = (|p_i|²/m_i² − 1/|q_i|) q_i − (q_i·p_i/m_i²) p_i, L_i = q_i × p_i (a scalar), L = Σ L_i and the AMD
  A = Σ Λ_i − L. They use the velocity p_i/m_i of the zero-coupling Kepler split. *Prograde elliptic* means
  m_i > 0, q_i ≠ 0, E_i < 0 and L_i > 0 for every i.

### 1. Properly degenerate KAM ([`properlyDegenerateKAM`](../../KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean))

A corrected specialization of Chierchia–Pinzari 2011 Theorem 11.1 / 2010 Theorem 1.3. Phase points are
z = ((φ, q), (I, p)) with fast angles φ ∈ ℝ^a (period 2π), fast actions I ∈ ℝ^a, slow pairs (p_j, q_j), j ≤ b.
The cylinder is C_r = {I ∈ V, p_j² + q_j² < r² for all j}; its cell F_r adds 0 ≤ φ_i < 2π.

**Data** (all fixed first): a, b ≥ 1; V ⊂ ℝ^a open, connected and bounded; W open with closure V ⊂ W; a boundary
collar bound: there are A, d > 0 with vol{I : dist(I, ∂V) < t} ≤ A t for 0 < t < d; r₀, μ₀, B > 0; functions H₀(I),
P(μ, z), P₀(μ, I), Ω(μ, I) ∈ ℝ^b, β(μ, I) a b×b matrix. **Hypotheses:**
- P is jointly real-analytic in (μ, z) near [0, μ₀] × closure(C_{r₀}), and 2π-periodic in each φ_i on C_{r₀};
- H₀ is real-analytic on W, the frequency map ∇H₀ has open image of W and a C¹ inverse on it;
- for μ ∈ [0, μ₀], I ∈ V: the angle average P_av = (2π)^(−a) ∫_{[0,2π]^a} P dφ is defined (integrable for
  p_j² + q_j² < r₀²) and P_av = P₀ + Σ Ω_j R_j + ½ Σ β_ij R_i R_j + o(‖(p,q)‖⁴) with R_j = (p_j² + q_j²)/2
  (explicit ε–δ form with discs of radius δ ≤ r₀);
- β(μ, I) is symmetric and |det β(μ, I)| ≥ B on [0, μ₀] × V.

**Conclusion.** There are r* ∈ (0, min(r₀, 1)), C > 0, c > 0 such that for all r, μ with 0 < r < r*, 0 < μ < μ₀ and
μ < r⁶/(log(1/r))^c there is a set S with

```
S ⊂ C_r measurable,   0 < vol(S ∩ F_r),   (1 − C√r) vol(F_r) < vol(S ∩ F_r) < vol(F_r),
```

(the factor 1 − C√r is read as 0 when it is negative), and every point of S lies on an invariant torus of H = H₀(I) + μP(μ, z) contained in S: an analytic Lagrangian
immersion K : ℝ^{a+b} → C_r, winding by 2π in the fast angles under integer shifts (and periodic in the slow
directions), injective modulo these shifts, whose lines θ + tω solve Hamilton's equations, with ω (γ, τ)-Diophantine
for some γ > 0 and τ > a + b that may depend on the torus (|k·ω| ≥ γ/|k|₁^τ for k ∈ ℤ^{a+b} \ {0}),
‖ω_fast‖ ≤ C and ‖ω_slow‖ ≤ Cμ.

### 2. Two planets and a moving Sun ([`planarTwoPlanetKAM`](../../KAM/Frozen/Planetary/Theorems/PlanarTwoPlanetKAM.lean))

**Data:** G, m₀ > 0, m₁, m₂ > 0, axes 0 < a₀ < a₁ (only distinct ordered axes), η > 0. Let U_η be the set of phase
points within max-norm distance η of the circular torus {q_i = a_i(cos 2πφ_i, sin 2πφ_i),
p_i = m_i √(Gm₀/a_i)(−sin 2πφ_i, cos 2πφ_i)}.

**Conclusion.** There are μ₀ > 0 and 0 < d < D such that for every 0 < μ < μ₀ there is a measurable S ⊂ U_η ⊂ ℝ⁸ with
0 < vol S < ∞, such that every point of S lies on a torus K : ℝ⁴ → S of H_mov that is analytic, ℤ⁴-periodic,
embedded modulo ℤ⁴, an immersion, Lagrangian, with a (γ, τ)-Diophantine frequency ω ∈ ℝ⁴ (τ > 3), whose lines
t ↦ K(φ + tω) solve Hamilton's equations for all t ∈ ℝ; and along every such line the configuration is
collision-free, the barycentric reconstruction solves Newton's equations for all t ∈ ℝ, and all three mutual
distances (Sun included) stay in [d, D].

### 3. n planets around a fixed Sun ([`fixedSunPlanetaryKAM`](../../KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean))

The model is H_fix = Σ_i [|p_i|²/(2m_i) − G m₀ m_i/|q_i|] − ε Σ_{i<j} G m_i m_j/|q_i − q_j|: the Sun is fixed at the
origin and only the planet–planet attraction is scaled by ε. The equations are Q̇_i = V_i = p_i/m_i and
V̇_i = −G m₀ Q_i/|Q_i|³ + ε Σ_{j≠i} G m_j (Q_j − Q_i)/|Q_j − Q_i|³.

**Data:** n ≥ 2, G, m₀, m_i, a_i > 0 with a_i < a_j for i < j, η > 0. **Conclusion:** there are ε₀ > 0 and
0 < d < D such that for every 0 < ε < ε₀ there is a measurable S ⊂ U_η ⊂ ℝ^{4n}, 0 < vol S < ∞, filled by invariant
analytic Lagrangian 2n-tori of H_fix as in statement 2 (Diophantine with τ > 2n − 1), along which the motions solve
the fixed-centre equations for all t ∈ ℝ, are collision-free, and all distances among the Sun (at 0) and the planets
stay in [d, D].

### 4. AMD confinement, a conditional helper ([`amdConfinement`](../../KAM/Frozen/Planetary/Theorems/AmdConfinement.lean))

An *AMD box* B consists of weights m, action bounds ℓ < ℓ⁰ < u⁰ < u (per planet), an eccentricity ceiling e*, AMD
levels A₀ < A₁, a distance d and a radius R. It is *admissible* if all m_i, ℓ_i > 0, 0 < e* < 1, 0 < A₀ < A₁,
A₁ < ℓ_i(1 − √(1 − e*²)) for all i, d, R > 0, d ≤ (ℓ_i/m_i)²(1 − e*), (u_i/m_i)²(1 + e*) ≤ R, and
(u_i/m_i)²(1 + e*) + d ≤ (ℓ_j/m_j)²(1 − e*) for i < j (separated annuli). The region LowAMD(lo, hi, A) is the set of
prograde elliptic points with lo_i < Λ_i < hi_i and AMD < A.

**Hypotheses:** n ≥ 2; B admissible; μ, T, δ > 0; ℓ_i + 2δ < ℓ⁰_i and u⁰_i + 2δ < u_i; A₀ + 2nδ < A₁;
z₀ ∈ LowAMD(ℓ⁰, u⁰, A₀); and the **stopped action bound**: for every l ≤ 0 ≤ r (l < r) and every moving solution z on
[l, r] from z₀ that stays in LowAMD(ℓ, u, A₁) on [l, r], |Λ_i(z(t)) − Λ_i(z₀)| ≤ δ for t ∈ [l, r] ∩ [−T, T].

**Conclusion:** there is a moving solution z on [−T, T] with z(0) = z₀, unique on [−T, T], whose barycentric
reconstruction solves Newton's equations (G = 1) on [−T, T], and for every t ∈ [−T, T]: z(t) ∈ LowAMD(ℓ, u, A₁);
L(t) = L(0); |e⃗_i(t)| < e*; d ≤ |q_i(t)| ≤ R; all barycentric pair distances lie in [d, 2R]; AMD(t) ≤ A₀ + nδ; and
|Λ_i(t) − Λ_i(0)| ≤ δ.

### 5. Exponential safety ([`planetaryExponentialSafety`](../../KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean))

Planar moving-Sun specialization of Nekhoroshev 1977, Theorem 12.3, with a = 2/(6n² − 3n + 14) and
b = 3a/2 = 3/(6n² − 3n + 14) (n = 2: a = 1/16, b = 3/32).

**Hypotheses:** n ≥ 2 and an admissible AMD box B. Nothing else: no Diophantine condition, no stopped estimate.
**Conclusion:** there are μ* > 0, c > 0, C > 0 (depending on n and B only) such that for every 0 < μ < μ* and every
z₀ ∈ LowAMD(ℓ⁰, u⁰, A₀), with T = exp(c μ^(−a)), there is a moving solution on [−T, T] from z₀, unique there, with
Newtonian reconstruction, staying in LowAMD(ℓ, u, A₁), with L(t) = L(0), |e⃗_i| < e*, d ≤ |q_i| ≤ R and barycentric
pair distances in [d, 2R] (the clauses of statement 4), and

```
|a_i(t) − a_i(0)| ≤ C μ^b   for all |t| ≤ exp(c μ^(−a)) and every planet i.
```

### 6. The secular box ([`secularBoxSafety`](../../KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean))

Two planets, G = m₀ = 1, weights m = (1, s) with s ∈ [29/100, 31/100], any μ > 0. Coordinates
w = ((λ, ξ), (Λ, η)) ∈ ℝ⁸ with mean longitudes λ (radians), Γ_i = (ξ_i² + η_i²)/2, a_i = (Λ_i/m_i)², eccentricity
vector v_i = √((1 − Γ_i/(2Λ_i))/Λ_i) (ξ_i, η_i) and s_i = 1 − Γ_i/Λ_i. The orbit at eccentric longitude F is
q_i(F) = a_i[s_i u(F) − v_i + (v_i·u(F))/(1 + s_i) v_i], u(F) = (cos F, sin F), with the matching momentum p_i(F)
(`ellipseMomentum`). The model is the exact full double average

```
H_sec(w) = (2π)^(−2) ∫_{[0,2π]²} H_mov(q(F), p(F)) ∏_i (1 − v_i·u(F_i)) dF₁ dF₂,
```

which does not depend on λ. *Regular* means Λ_i > 0, 0 ≤ Γ_i < Λ_i, positive Jacobians and collision-free ellipses
for every F, integrability of the integrand and differentiability of H_sec at w. The **input box**: Λ_i > 0,
0 ≤ Γ_i < Λ_i, a_J ∈ [103/20, 21/4], a_S ∈ [189/20, 193/20], |v_J| ≤ 3/50, |v_S| ≤ 7/100 (all phases allowed).

**Conclusion:** for every w₀ in the box there is w : ℝ → ℝ⁸ with w(0) = w₀ solving Hamilton's equations for H_sec for
all t ∈ ℝ, equal on U to every solution on an open interval U ∋ 0 from w₀ that stays regular, and for every t ∈ ℝ:
w(t) is regular, Λ(t) = Λ(0), A(t) = Γ₁ + Γ₂ = A(0) < 16373/2500000, |v_i(t)| < 3/20, and for every F ∈ ℝ²:
1751/400 ≤ |q_i(F)| ≤ 4439/400, |q_S(F)| − |q_J(F)| ≥ 399/200, and the barycentric positions (Sun included) have
pair distances in [399/200, 4439/200].

### 7. The secular box at cited masses ([`secularBoxAtCitedMasses`](../../KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean))

Statement 6 with s = 476/1591 and μ = 4773/5000000 = 0.0009546 (so μs = 0.0002856), the decimal model masses of
Figueras–Haro, arXiv:2403.10152v1 §4.

## What is assumed and what is not claimed

- **Statement 1** is not a literal restatement of Chierchia–Pinzari. Owner-approved corrections (D20): the disc
  cylinder (from CP10's measure construction), the neighbourhood W of closure V, the boundary collar, symmetric β, and
  joint analyticity in μ (stronger than CP10's C¹ parameter dependence). The Diophantine constants may vary with the
  torus; the measure bound is on one fundamental cell.
- **Statements 2–3** are qualitative: no numerical μ₀ or ε₀, no density-one claim, positive measure only in the
  reduced 8- or 4n-dimensional coordinates. The fixed-Sun model is the repository's own (no published fixed-Sun
  theorem was located); only the planet–planet attraction is scaled by ε.
- **Statement 4** has a dynamical hypothesis, the stopped action bound. It is a conditional helper by explicit owner
  ruling (D25, Q-P-A3); it is not a source result on its own. Statement 5 has no such premise.
- **Statements 4–5** are planar, with G = m₀ = 1, fixed positive weights and prograde data in an explicitly separated
  low-AMD region (deviation D-P-A-1). The elements are those of the zero-coupling Kepler split (heliocentric position,
  barycentric velocity p_i/m_i), not the osculating heliocentric ellipse. The constants are asymptotic: nothing here
  certifies the actual Solar System. No exponent better than Nekhoroshev's is claimed.
- **Statements 6–7** concern the averaged model only: no statement about Newton's equations of the reconstructed
  ellipses and no transfer to the full three-body problem. The box is an illustrative canonical-element box, not an
  ephemeris uncertainty set; "cited masses" are model parameters, not measured values. No smallness of μ is needed.
- Spatial planetary KAM is not attempted (statement.md §P-SPATIAL is a sketch).

## Sources and proof

Sources: Chierchia–Pinzari, *Properly-degenerate KAM theory*, DCDS-S 3 (2010) (CP10) and *The planetary N-body
problem*, Invent. Math. 186 (2011) (CP11); Chierchia–Pusateri, ETDS 29 (2009) (CP09); Féjoz, ETDS 24 (2004), revised
2007, with its 2007 erratum; Rüssmann, R&C Dynamics 6 (2001); Nekhoroshev, Russ. Math. Surveys 32 (1977) §12;
Laskar–Petit, A&A 605 A72 (2017), App. B; Figueras–Haro, arXiv:2403.10152v1. Pins: [`sources.md`](../tracks/P/sources.md).

Proof route. Statement 1 follows CP10 §§3–4 (averaging, a two-scale KAM iteration on track N's normal-form engine, the
measure lemma). Statement 2 applies the sealed statement 1 to the planar secular Birkhoff form in a Poincaré chart
regular at circular orbits, with the planar torsion recomputed from the secular quartic form (Féjoz's and CP11's
printed coefficients have recorded errata) and transported back to Cartesian coordinates. Statement 3 uses the same
route for n = 2 (the secular averages of H_mov and H_fix differ by a function of the actions) and, for n ≥ 3, CP09
Theorem 4 with a quantitative analytic weak-nondegeneracy (Rüssmann-type) KAM theorem proved in the track.
Statement 4 combines the exact identity A(t) − A(0) = Σ(Λ_i(t) − Λ_i(0)) (angular momentum is conserved) with a
first-exit argument. Statement 5 discharges the stopped bound from the sealed partially convex Nekhoroshev theorem
(track N, Nekhoroshev 1977 Thm 4.4) on finitely many cells, then applies statement 4. Statements 6–7 use conservation of
Λ and of A in the averaged model and exact rational arithmetic.

Statements: [`docs/tracks/P/statement.md`](../tracks/P/statement.md) · blueprint:
[`blueprint-P/blueprint.pdf`](../../blueprint-P/blueprint.pdf) · dependency graph:
[`docs/graph/P/DEPGRAPH.md`](../graph/P/DEPGRAPH.md) · statement list: [`docs/STATEMENTS.md`](../STATEMENTS.md#track-p-planetary-systems).

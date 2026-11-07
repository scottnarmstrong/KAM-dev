# Isoenergetic KAM, all-time confinement and the restricted three-body problem (track I)

**Status:** proved and sealed (I-KEPLER on 2026-10-27; I-G1, I-HEAD and I-R3BP on 2026-10-28) · frozen ids
`iso.isoenergetic_kam.v1`, `iso.all_time_confinement.v1`, `iso.kepler_bordered_det.v1`,
`iso.restricted_near_circular.v1` · axioms: standard only (`propext`, `Classical.choice`, `Quot.sound`)

## In brief

In two degrees of freedom the phase space is four-dimensional and each energy level is three-dimensional, so a
two-dimensional invariant torus inside an energy level can act as a wall that orbits cannot cross. This track proves
a fixed-energy (isoenergetic) a-posteriori KAM theorem, uses it to show that for small analytic perturbations of an
isoenergetically non-degenerate system every orbit exists for all time and its actions stay within any prescribed
η of their initial value, and applies this to the restricted circular planar three-body problem: there is an
explicit open set of near-circular initial conditions whose solutions, for every small mass ratio, never collide
with either primary and never escape.

## Conventions

As in track K ([K.md](K.md)): z = (θ, I), period-1 angles, max norms, the complex strip T_ρ, the action
neighbourhood B_r, X_H = (∂_I H, −∂_θ H), ∇h the real gradient of Re h, (γ, τ)-Diophantine vectors, primary and
real-on-reals parameterizations, the Gram matrix, normal frame N, torsion T and invariance error
E = X_H(K) − DK·ω. The **bordered Hessian** of h at a real point I is the (n+1)×(n+1) real matrix
[[D²h(I), ∇h(I)], [∇h(I)ᵀ, 0]] (h replaced by Re h). A **solution on J in B** of a real Hamiltonian H is a curve
z : ℝ → ℝⁿ × ℝⁿ with, for every t ∈ J, action part in B, H differentiable at z(t), and z′(t) = X_H(z(t)).

## Exactly what is proved

### I-G1: isoenergetic a-posteriori KAM

[`KAM.Iso.isoenergetic_kam`](../../KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean)

Extra objects: the **extended torsion** T_H(θ) = [[T(θ), ω], [DH(K(θ))N(θ), 0]] (indexed by n + 1; the last row is
DH(K)N, not ωᵀ) and its entrywise average ⟨T_H⟩ over [0,1]ⁿ; the **energy average** ⟨H∘K⟩ over [0,1]ⁿ.

**Fixed first:** n ≥ 2, τ ≥ n − 1, 0 < ρ∞ < ρ, positive M, σ_K, σ_B, σ_T, μ, γ̄, ν, a number σ_ω > 1 and a nonzero
direction ω* ∈ ℝⁿ. **Constants:** there are C₁, C₂, C₃ > 0, depending only on these, such that for every open
D ⊆ ℂⁿ × ℂⁿ, H, K and reals s, γ, e, E₀:

1. D is invariant under integer angle shifts; H is holomorphic on D, 1-periodic in θ, real on real points; on D,
   |DH|, |X_H|, |DX_H|, |D²X_H|, |D²H| ≤ M.
2. K is holomorphic, primary and real on real θ on T_ρ; the ball of radius μ about K(θ) lies in D and
   |DK(θ)| ≤ σ_K − μ for θ ∈ T_ρ.
3. The Gram matrix is invertible on T_ρ with inverse bounded by σ_B − μ.
4. ⟨T_H⟩, computed at the frequency s·ω*, is invertible with |⟨T_H⟩⁻¹| ≤ σ_T − μ.
5. 1 < s < σ_ω, ν ≤ (s − 1)|ω*| and ν ≤ (σ_ω − s)|ω*|; 0 < γ ≤ γ̄; ω* is (γ, τ)-Diophantine.
6. e ≥ 0; |X_H(K(θ)) − DK(θ)(s·ω*)| ≤ e on T_ρ; |⟨H∘K⟩ − E₀| ≤ e; and C₁·e/(γ⁴ρ^{4τ}) < 1.

**Conclusion.** There are K∞ and s∞ with 1 < s∞ < σ_ω such that K∞ is holomorphic, primary and real on real θ on
T_{ρ∞}, and on T_{ρ∞}: K∞ is invariant with frequency s∞·ω*; H(K∞(θ)) = E₀ pointwise; the ball of radius μ/2 about
K∞(θ) lies in D; |DK∞| ≤ σ_K − μ/2; |K∞ − K| ≤ C₂·e/(γ²ρ^{2τ}); and |s∞ω* − sω*| ≤ C₃·e/(γ²ρ^{2τ}).
The frequency stays on the ray through ω*, so it stays Diophantine.

### I-HEAD: all-time confinement in two degrees of freedom

[`KAM.Iso.all_time_confinement`](../../KAM/Frozen/Iso/Theorems/AllTimeConfinement.lean)

**Data.** B ⊆ ℝ² open, bounded, nonempty; s₀, r₀ > 0; h holomorphic on B_{r₀}, real on its real points, with
det(bordered Hessian of h at I) ≠ 0 at every real I ∈ B_{r₀}; B′ open with compact closure contained in B; η > 0.

**Conclusion.** There is ε₀ > 0 (depending on the data) such that for every f and ε with f holomorphic on
T_{s₀} × B_{r₀}, 1-periodic in θ, real at real points with real action in B_{r₀}, 0 ≤ ε < ε₀ and |f| ≤ ε there, and
for every initial point z₀ = (θ₀, I₀) ∈ ℝ² × ℝ² with I₀ ∈ B′ (any angle), with H = Re(h + f) on real points:

- there is z : ℝ → ℝ² × ℝ² with z(0) = z₀ that is a solution of H on all of ℝ in B, and |I(t) − I₀| < η for every
  real t;
- every solution y of H on an open interval (a, b) ∋ 0 in B with y(0) = z₀ equals z on (a, b).

So every maximal solution through z₀ is global and confined; ε = 0 is included.

### I-KEPLER: the Kepler bordered determinant

[`KAM.Iso.kepler_bordered_det`](../../KAM/Frozen/Iso/Theorems/KeplerBorderedDet.lean)

For κ > 0, Ω > 0 and L > 0, the matrix
[[−3κ/L⁴, 0, κ/L³], [0, 0, −Ω], [κ/L³, −Ω, 0]] — the bordered Hessian of h(L, G) = −κ/(2L²) − ΩG — has determinant
exactly 3κΩ²/L⁴, which is positive. This is an algebraic identity about the displayed matrix; the ordinary Hessian of
h is singular.

### I-R3BP: the restricted circular planar three-body problem

[`KAM.Iso.restricted_near_circular`](../../KAM/Frozen/Iso/Theorems/RestrictedNearCircular.lean)

**Model.** Units with gravitational constant, primary separation, total primary mass and angular speed equal to 1.
Primaries of mass 1 − μ and μ sit at a₁ = (−μ, 0) and a₂ = (1 − μ, 0) in the rotating barycentric frame. On the
collision-free set (|q − a₁|₂ > 0, |q − a₂|₂ > 0; |·|₂ Euclidean), the exact Hamiltonian is
H_μ(q, p) = |p|₂²/2 + q₂p₁ − q₁p₂ − (1 − μ)/|q − a₁|₂ − μ/|q − a₂|₂ (p is canonical momentum), and a solution on J is a
curve that is collision-free at every t ∈ J and satisfies
q̇ = (p₁ + q₂, p₂ − q₁), ṗ = (p₂, −p₁) − (1 − μ)(q − a₁)/|q − a₁|₂³ − μ(q − a₂)/|q − a₂|₂³.

**Region.** For 0 < a₋ < a₊ and 0 < e₋ < e₊, NearCircular(a₋, a₊, e₋, e₊) is the set of (q, p) with osculating
Kepler elements (about the origin, for μ = 0) in the window: there are r, a, e with r > 0, r² = |q|₂², 0 < e < 1,
a₋ < a < a₊, e₋ < e < e₊, |p|₂²/2 − 1/r = −1/(2a), angular momentum ℓ = q₁p₂ − q₂p₁ > 0 (prograde) and ℓ² = a(1 − e²).

**Hypotheses.** 0 < a₋ < a₊, 0 < e₋ < e₊ < 1/4, a₊(1 + e₊) < 1 (the orbits stay inside the secondary's orbit).

**Conclusion.** The region is open in ℝ² × ℝ² and nonempty, and there are μ₀, d, R with 0 < μ₀ ≤ 1/2, d > 0, R > 0
such that for every 0 ≤ μ < μ₀ and every z₀ in the region there is a solution z on all of ℝ with z(0) = z₀ and, for
every t, |q(t) − a₁|₂ ≥ d, |q(t) − a₂|₂ ≥ d, |q(t)|₂ ≤ R and |p(t)|₂ ≤ R; every solution on an open interval
(a, b) ∋ 0 with the same initial point equals z there.

## What is assumed and what is not claimed

- **Owner rulings D19 (Q1–Q5), approved and frozen in D20:** the uniform constants of I-G1 fix the ray data ω*, σ_ω,
  ν, the bound γ̄ and the margin μ first (deviation D-I-G1-UNIFORM); dynamics are stated as an exhibited global
  solution plus agreement with every local solution, with no flow defined in advance; the bordered determinant is
  assumed nonzero on the real slice of B_{r₀} (the same radius as the analyticity domain); the physical region is the
  prograde interior annulus with e₊ < 1/4 and a₊(1 + e₊) < 1.
- **I-G1** specializes HL19 Theorem 3.6 to d = n, canonical structure and first integral c = H; it uses pointwise
  operator norms on open strips, ≤ instead of strict closeness inequalities, and states the energy identity
  pointwise. Sign corrections to HL19 are recorded as errata. Constants are not explicit (explicit ones are proved
  separately in `KAM.Iso.Sharp.g1_sharp`, outside the frozen statements).
- **I-HEAD** is a deduction of this formalization, not a theorem of HL19 or of Celletti–Chierchia; it is qualitative
  (ε₀ not explicit), needs no boundary regularity of B and no global injectivity of the frequency map, and is
  specific to n = 2.
- **I-R3BP** is a derived application: no numerical μ₀, d or R is given, and no claim is made about Solar-System
  masses. It covers prograde orbits inside the secondary's orbit with eccentricity in (e₋, e₊) ⊂ (0, 1/4); exactly
  circular, retrograde and exterior orbits are not covered. The region itself is not claimed invariant (the bounds d, R
  describe a larger compact collision-free set). μ = 0 is included. It is not the computer-assisted theorem of Celletti–
  Chierchia (2003/2007) for a truncated model.

## Sources and proof

Sources ([PAPERS.md](../PAPERS.md)): Haro–Luque (2019), Theorem 3.6 and Remark 3.7, pp. 18–19 (I-G1); Chierchia,
lecture notes on the restricted circular planar three-body problem (2005), p. 17 and (3.34)–(3.39) (I-KEPLER,
I-R3BP); Arnold (1963) for the isoenergetic mechanism. Track statement and source notes:
[tracks/I/statement.md](../tracks/I/statement.md), [tracks/I/notes.md](../tracks/I/notes.md).

**Proof route.** I-G1 runs the track-K Newton scheme with the bordered system of HL19 §6 (the bordered zero-mode
solve, proved in full where the source refers to analogous computations) and an energy identity showing that an
invariant torus with nonresonant frequency has constant energy. I-HEAD: at a torus θ ↦ (θ, I) of h the extended
torsion equals the bordered Hessian, so I-G1 applies with uniform constants on finitely many patches of the compact
set B̄′; on each energy level, Diophantine directions on both sides of the initial action give invariant tori that
bound a thin annulus in the local energy cylinder; ODE uniqueness forbids crossing, and continuation from a compact
set gives global existence. I-R3BP pulls the exact Hamiltonian back by an analytic Delaunay chart (κ = Ω = 1 at
μ = 0, determinant from I-KEPLER), applies I-HEAD with the O(μ) part as perturbation, and reads off d and R from the
compact safe region.

Blueprint: [blueprint-I/blueprint.pdf](../../blueprint-I/blueprint.pdf). Dependency graph (450 nodes, all resolved):
[docs/graph/I/DEPGRAPH.md](../graph/I/DEPGRAPH.md). Providers: `KAM/Provider/Iso/`.

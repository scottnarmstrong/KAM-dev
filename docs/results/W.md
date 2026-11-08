# Quasi-periodic solutions of the cubic wave equation (track W)

**Status:** proved and sealed (frozen 2026-10-30, D41; sealed 2026-11-01, D61) · frozen ids `wave.nlw2.v1` (theorem)
and the eleven definitions `wave.lam.v1`, `wave.sineMode.v1`, `wave.ellWeight.v1`, `wave.WaveSpace.v1`,
`wave.coeff.v1`, `wave.reconU.v1`, `wave.reconV.v1`, `wave.cubicGrad.v1`, `wave.linearTorus.v1`,
`wave.IsAnalyticTorusEmbedding.v1`, `wave.IsClassicalSolution.v1` · axioms: standard only (`propext`,
`Classical.choice`, `Quot.sound`)

## In brief

The equation u_tt = u_xx − m u − u³ on the interval [0, π], with u = 0 at both ends, is a nonlinear wave equation:
an infinite-dimensional Hamiltonian system. Without the cubic term every solution is a superposition of standing
waves sin(jx) oscillating at the frequencies λ_j = √(j² + m). The theorem shows that, for every mass m > 0, many of the
small two-mode solutions survive the nonlinearity: there is a large family of exact solutions that are
quasi-periodic in time with two independent frequencies, analytic in time and space, close to a superposition of the
first two standing waves. This is KAM theory for a partial differential equation, following Pöschel (1996).

## Exactly what is proved

Lean: [`KAM.Wave.nlw2`](../../KAM/Frozen/Wave/Theorems/Nlw2.lean); the definitions are under
[`KAM/Frozen/Wave/Defs/`](../../KAM/Frozen/Wave/Defs/) and [`KAM.IsDiophantine`](../../KAM/Frozen/Defs/IsDiophantine.lean).

### The objects

Modes are indexed by j = 1, 2, 3, …; the two "tangential" modes are j = 1, 2.

- **Linear frequencies** ([`lam`](../../KAM/Frozen/Wave/Defs/Lam.lean)): λ_j = √(j² + m).
- **Sine modes** ([`sineMode`](../../KAM/Frozen/Wave/Defs/SineMode.lean)): φ_j(x) = √(2/π) sin(jx).
- **Phase space** ([`WaveSpace`](../../KAM/Frozen/Wave/Defs/WaveSpace.lean),
  [`ellWeight`](../../KAM/Frozen/Wave/Defs/EllWeight.lean), [`coeff`](../../KAM/Frozen/Wave/Defs/Coeff.lean)): pairs of
  real sequences (q, p) = ((q_j), (p_j)) with finite weighted norm
  ‖q‖₁,₁ = (Σ_j (j e^j |q_j|)²)^{1/2}, and ‖(q, p)‖_E = max(‖q‖₁,₁, ‖p‖₁,₁). In Lean a point is stored as the pair
  of ℓ² sequences (j e^j q_j), (j e^j p_j); `coeff` recovers q_j and p_j. This is an isometric encoding of the space
  E = ℓ^{1,1} × ℓ^{1,1}.
- **Reconstruction** ([`reconU`](../../KAM/Frozen/Wave/Defs/ReconU.lean), [`reconV`](../../KAM/Frozen/Wave/Defs/ReconV.lean)):
  the displacement U(q)(x) = Σ_j q_j λ_j^{−1/2} φ_j(x) and the velocity V(p)(x) = Σ_j λ_j^{1/2} p_j φ_j(x).
- **Cubic gradient** ([`cubicGrad`](../../KAM/Frozen/Wave/Defs/CubicGrad.lean)):
  G(q)_l = λ_l^{−1/2} ∫₀^π U(q)(x)³ φ_l(x) dx, the gradient of ¼∫₀^π U(q)⁴.
  The equations of motion of the Hamiltonian ½Σ λ_j (q_j² + p_j²) + ¼∫ U(q)⁴ are q̇_j = λ_j p_j,
  ṗ_j = −λ_j q_j − G(q)_j.
- **Linear torus** ([`linearTorus`](../../KAM/Frozen/Wave/Defs/LinearTorus.lean)): for actions I = (I₀, I₁) with both
  entries positive and an angle θ ∈ ℝ² (period one), q_j = √(2I_{j−1}) cos(2πθ_{j−1}),
  p_j = −√(2I_{j−1}) sin(2πθ_{j−1}) for j = 1, 2, and q_j = p_j = 0 for j ≥ 3.
- **Analytic torus embedding** ([`IsAnalyticTorusEmbedding`](../../KAM/Frozen/Wave/Defs/IsAnalyticTorusEmbedding.lean)):
  a map K : ℝ² → E that is ℤ²-periodic, real analytic at every point, injective modulo ℤ² (K θ = K θ' only if
  θ − θ' ∈ ℤ²), and whose derivative is injective at every θ.
- **Classical solution** ([`IsClassicalSolution`](../../KAM/Frozen/Wave/Defs/IsClassicalSolution.lean)): u : ℝ × ℝ → ℝ
  has functions u_t, u_x, u_tt, u_xx, all continuous on ℝ × [0, π], such that at every t ∈ ℝ and x ∈ [0, π] they are the
  corresponding derivatives (time derivatives two-sided, space derivatives within [0, π], one-sided at the ends),
  u_tt = u_xx − m u − u³ holds, and u(t, 0) = u(t, π) = 0 for all t.
- **Diophantine** ([`IsDiophantine`](../../KAM/Frozen/Defs/IsDiophantine.lean)): ν ∈ ℝ² is (γ, τ)-Diophantine if
  |k·ν| ≥ γ/(|k₁| + |k₂|)^τ for every nonzero k ∈ ℤ².

Write r(I) = √(I₀ + I₁) for the amplitude, and P = (0, ∞)² for the open positive quadrant.

### The theorem

**For every m > 0** there exist numbers r₀ > 0, C > 0, τ > 1, a function η : ℝ → ℝ, a set Γ ⊆ ℝ² of actions, a
frequency map ν : ℝ² → ℝ² and a family of maps K : ℝ² → (ℝ² → E), such that:

- **(side conditions)** η ≥ 0 on (0, r₀) and η(r) → 0 as r → 0⁺; Γ is a Borel set with
  Γ ⊆ {I ∈ P : r(I) < r₀}; ν is continuous on Γ; (I, θ) ↦ K_I(θ) is continuous on Γ × ℝ².
- **(1) Density one at the origin.** vol(Γ ∩ B_h) / vol(P ∩ B_h) → 1 as h → 0⁺, where B_h = {I : max|I_i| < h} and
  vol is Lebesgue measure on ℝ².
- **(2) Two independent frequencies.** For every I ∈ Γ there is γ > 0 with ν(I) (γ, τ)-Diophantine (γ may depend on
  I; τ does not). ν(I) → (λ₁/(2π), λ₂/(2π)) as I → 0 within Γ.
- **(3) Small embedded tori.** For every I ∈ Γ: K_I is an analytic torus embedding, and for all θ ∈ ℝ²
  ‖K_I(θ) − linearTorus(I, θ)‖_E ≤ η(r(I))·r(I) and ‖K_I(θ)‖_E ≤ C·r(I).
- **(4) Exact invariance.** For every I ∈ Γ, θ ∈ ℝ² and j ≥ 1, along the line θ + tν(I):
  d/dt|_{t=0} q_j(K_I(θ + tν(I))) = λ_j p_j(K_I(θ)), and
  d/dt|_{t=0} p_j(K_I(θ + tν(I))) = −λ_j q_j(K_I(θ)) − G(q(K_I(θ)))_j.
  That is, the linear flow θ ↦ θ + tν(I) on the torus is carried by K_I to a solution of the coordinate equations
  of motion.
- **(5) PDE solutions.** For every I ∈ Γ and every initial phase θ₀ ∈ ℝ², the function
  u(t, x) = U(q(K_I(θ₀ + tν(I))))(x) satisfies:
  (t, x) ↦ u(t, x) is real analytic at every point of ℝ × [0, π]; u is a classical solution in the sense above;
  ∂_t u(t, x) = V(p(K_I(θ₀ + tν(I))))(x) for all t ∈ ℝ, x ∈ [0, π]; and
  |u(t, x)| + |∂_x u(t, x)| + |∂_t u(t, x)| ≤ C·r(I) for all t ∈ ℝ, x ∈ [0, π] (∂_x taken within [0, π]).
- **(6) Disjointness.** For I, I' ∈ Γ and θ, θ' ∈ ℝ², K_I(θ) = K_{I'}(θ') implies I = I' and θ − θ' ∈ ℤ². Distinct
  tori of the family are disjoint.

The only hypothesis is m > 0. All of r₀, C, τ, η, Γ, ν, K are existential and depend on m; none is given explicitly.
Since each solution in (5) is u(t) = U(K_I(θ₀ + tν)), it is quasi-periodic in t with frequency vector ν(I), and
by (2) its two frequencies are rationally independent.

## What is assumed and what is not claimed

- **Scope.** Only the nonlinearity u³ (the defocusing sign as written), Dirichlet conditions on [0, π], the two
  tangential modes j = 1, 2, and the weights a = p = 1 of the phase space. Every fixed m > 0 is covered.
- **Measure statement.** The family is parametrised by a Borel set of actions with density one at the origin. Nothing
  is claimed about general small initial data, about the set of initial data lying on these tori in the
  infinite-dimensional phase space, or about which actions outside Γ fail.
- **Declared weakenings relative to Pöschel's theorem** (ruling W-A2, D30 Q3): no linear (or other) stability of the
  tori; no Whitney or Lipschitz regularity of the family in I (only continuity of (I, θ) ↦ K_I(θ)); a Borel set of
  density one in place of a Cantor set; closeness o(r) to the linear torus in place of O(r^σ); period-one angles.
  The analytic embedding (3) and the disjointness (6) are retained.
- **Constants.** No explicit value of r₀, C, τ or η, and no lower bound on γ as I → 0 (γ may degenerate).
- **Encoding choices** (recorded in the statement audit, none changes content): the weighted-coordinate encoding of E;
  the derivative along ν stated coordinatewise rather than through the Fréchet derivative of K; the u_t bound written
  with V(p), which equals u_t by the preceding conjunct of (5).

## Sources and proof

The statement follows J. Pöschel, *Quasi-periodic solutions for a nonlinear wave equation*, Comment. Math. Helv. 71
(1996) 269–296 (Main Theorem with J = {1, 2}, and the Cantor manifold theorem p. 289), with the abstract KAM theorem of
J. Pöschel, Ann. Sc. Norm. Super. Pisa 23 (1996) 119–148, and S. Kuksin, J. Pöschel, Ann. of Math. 143 (1996) 149–179
for the measure and family arguments. The normalization was re-derived: the printed normal-form coefficients of the
wave paper are 16 times too large (erratum E-PDE-W-1); the corrected values are A_ii = 9/(8πλ_i²),
A_ij = 3/(2πλ_iλ_j).

The proof is organised in the blueprint [`blueprint-W/`](../../blueprint-W/) (parts W0–W8). It sets up the weighted
sequence spaces and shows the reconstruction U, V is bounded into C^k and turns the coordinate equations into the PDE
(W1–W2). A partial Birkhoff normal form puts the quartic term into integrable form on the first two modes, with a
nondegenerate twist (W3). The KAM part solves the homological equations with the normal frequencies, proves one KAM
step and iterates it to a limit (W4–W6). A measure estimate removes the resonant frequencies (W7). The assembly passes
to action–angle coordinates, builds the family over the density-one set, proves the embedding and disjointness, and
reconstructs the PDE solutions (W8). The Lean proof is in [`KAM/Wave/`](../../KAM/Wave/); it is assembled in
`KAM/Wave/Assembly/Nlw2Proof.lean` and enters the frozen file through the provider
`KAM/Provider/Wave/Nlw2.lean`.

Decisions: D30 (track adopted, scope Q1–Q4), D41 (statement approved and frozen), D53 (resourcing), D61 (seal), in
[`docs/DECISIONS.md`](../DECISIONS.md). The approved statement text and its audit notes are in
[`docs/tracks/W/W-STATEMENTS.md`](../tracks/W/W-STATEMENTS.md).

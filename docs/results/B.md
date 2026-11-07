# Finite-time effective stability (track B)

**Status:** proved and sealed (all three frozen and sealed in one pass on 2026-11-03; D72, D73) · frozen ids
`effectiveStability.d72.torus_confinement.v1`, `effectiveStability.d72.oscillator_confinement.v1`,
`effectiveStability.d73.henonHeiles_confinement.v1` · axioms: standard only (`propext`, `Classical.choice`,
`Quot.sound`)

## In brief

KAM tori confine motion for all time only in two degrees of freedom. In more degrees of freedom the practical
question is how long orbits stay close to where they started. The standard answer is a normal form: a change of
coordinates in which the actions change only through a small remainder, so that they drift at a bounded rate. Track B
proves this step formally, in a form that turns a finite computation (a certified normal form) into a theorem about
the true flow: existence, uniqueness and explicit action bounds up to an explicit time. Two general theorems cover
torus (action–angle) charts and Cartesian oscillator charts. A third applies the oscillator theorem, through an exact
computer certificate, to the Hénon–Heiles system for 10¹⁰ time units.

## Exactly what is proved

**Conventions.** Points of phase space are w = (w.1, w.2) ∈ ℝⁿ × ℝⁿ. Hamilton's equations use
[`KAM.hamiltonianVectorField`](../../KAM/Frozen/Defs/HamiltonianVectorField.lean): ẇ.1 = ∂H/∂w.2, ẇ.2 = −∂H/∂w.1
(so w.1 plays the role of angle or position q, w.2 of action or momentum p). A map Ψ is *symplectic* at w if its
derivative preserves [`KAM.symplecticForm`](../../KAM/Frozen/Defs/SymplecticForm.lean)
ω(u, v) = Σ_i (u.2_i v.1_i − u.1_i v.2_i). Oscillator actions are
[`oscillatorAction`](../../KAM/Frozen/Planetary/Defs/OscillatorAction.lean) I_j(q, p) = (p_j² + q_j²)/2.
In §1 and §2 the conclusion "a solution, unique on its interval (in V)" has this form (in §3 there is no V):

> there is T₁ > T and z : ℝ → ℝⁿ × ℝⁿ with z(0) = (initial point), z(t) ∈ V and ż(t) = X_H(z(t)) for all
> t ∈ (−T₁, T₁); and every y defined on an order-connected set I ∋ 0 with y(0) = (initial point), y(t) ∈ V and
> ẏ = X_H(y) on I agrees with z on I ∩ (−T₁, T₁).

### 1. Torus charts: `torus_confinement`

Lean: [`KAM.EffectiveStability.torus_confinement`](../../KAM/Frozen/EffectiveStability/TorusConfinement.lean).
Chart coordinates are w = (φ, J): lifted angles φ ∈ ℝⁿ and actions J ∈ ℝⁿ. Let C_c = {w : |J_j| < c_j for all j}.

**Data and hypotheses.** n ∈ ℕ; vectors a, b, η ∈ ℝⁿ and reals ε > 0, T ≥ 0, with η_j ≥ 0 and
a_j + T·η_j < b_j for every j. An open set V ⊆ ℝⁿ × ℝⁿ and H of class C² on V. Maps Ψ, Ψ⁻ : ℝⁿ × ℝⁿ → ℝⁿ × ℝⁿ with,
on the chart domain C_{b+ε}: Ψ of class C², Ψ(w) ∈ V, Ψ symplectic, and Ψ⁻(Ψ(w)) = w. Functions N : ℝⁿ → ℝ (no
regularity assumed) and R : ℝⁿ × ℝⁿ → ℝ, with R differentiable on C_{b+ε}, R(φ + k, J) = R(φ, J) for all k ∈ ℤⁿ on
C_{b+ε}, and

- H(Ψ(w)) = N(J) + R(w) on C_{b+ε};
- |∂R/∂φ_j (w)| ≤ η_j for every j and every w with |J_k| ≤ b_k for all k.

An initial chart point w₀ with |J_j(w₀)| ≤ a_j for all j.

**Conclusion.** The flow of H from Ψ(w₀) has a solution, unique on its interval (in V), on (−T₁, T₁) with T₁ > T;
and for every |t| ≤ T: z(t) = Ψ(Ψ⁻(z(t))) (the orbit stays in the chart image), and with J(t) the action part of
Ψ⁻(z(t)), for every j,

  |J_j(t) − J_j(w₀)| ≤ η_j·|t|  and  |J_j(t)| ≤ a_j + η_j·T.

### 2. Oscillator charts: `oscillator_confinement`

Lean: [`KAM.EffectiveStability.oscillator_confinement`](../../KAM/Frozen/EffectiveStability/OscillatorConfinement.lean).
Chart coordinates are Cartesian, w = (q, p), and the actions are I_j(w) = (p_j² + q_j²)/2. Let
D_c = {w : I_j(w) < c_j for all j}.

**Data and hypotheses.** As in §1, with D_{b+ε} in place of C_{b+ε}, these changes: there is no periodicity
hypothesis; the normal form reads H(Ψ(w)) = N(I(w)) + R(w) on D_{b+ε}; and the remainder bound is the bracket bound

  |{I_j, R}(w)| = |q_j ∂R/∂p_j (w) − p_j ∂R/∂q_j (w)| ≤ η_j  for every j and every w with I_k(w) ≤ b_k for all k.

The initial chart point satisfies I_j(w₀) ≤ a_j. Zero actions are allowed.

**Conclusion.** As in §1, with I_j in place of |J_j|: for |t| ≤ T, z(t) = Ψ(Ψ⁻(z(t))) and, with w(t) = Ψ⁻(z(t)),
|I_j(w(t)) − I_j(w₀)| ≤ η_j·|t| and I_j(w(t)) ≤ a_j + η_j·T.

### 3. The Hénon–Heiles system: `henonHeiles_confinement`

Lean: [`KAM.EffectiveStability.henonHeiles_confinement`](../../KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean)
(opt-in library `KAMHenonHeiles`). Take n = 2, z = (q, p) ∈ ℝ² × ℝ², and

  H(q, p) = (q₀² + p₀²)/2 − (√2/2)·(q₁² + p₁²)/2 + q₀² q₁ − q₁³/3,

that is H = I₀ − (√2/2) I₁ + q₀²q₁ − q₁³/3 with I_j = (q_j² + p_j²)/2.

**Hypothesis.** z₀ ∈ ℝ² × ℝ² with I₀(z₀) ≤ (1/12500)² and I₁(z₀) ≤ (1/12500)² (that is, ≤ 6.4·10⁻⁹).

**Conclusion.** There is T₁ > 10¹⁰ and a solution z of ż = X_H(z) on (−T₁, T₁) with z(0) = z₀; every solution y
through z₀ on an order-connected set I ∋ 0 agrees with z on I ∩ (−T₁, T₁); and for all |t| ≤ 10¹⁰ and j = 0, 1:

  I_j(z(t)) < 101/10¹⁰ = 1.01·10⁻⁸  and  |I_j(z(t)) − I_j(z₀)| ≤ 12/10¹⁰ = 1.2·10⁻⁹.

The quadratic part has frequencies 1 and −√2/2 of opposite signs, so conservation of energy alone does not bound the
orbits; the bound comes from the normal form.

## Supporting results (ordinary theorems, not frozen)

- **Confinement from approximate integrals.**
  [`KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement`](../../KAM/Application/Confinement/ApproxIntegral.lean)
  (2026-11-06). Let W ⊆ ℝⁿ × ℝⁿ be open, H of class C² on W, D open with compact closure in W, F_1, …, F_m
  differentiable on W, T ≥ 0, Q ⊆ D, and a, b, η ∈ ℝ^m. Assume |dF_j(z)·X_H(z)| ≤ η_j on the closure of D;
  a_j ≤ F_j ≤ b_j on Q; and every frontier point z of D has some j with F_j(z) < a_j − Tη_j or F_j(z) > b_j + Tη_j.
  Then for every z₀ ∈ Q the maximal solution in W through z₀ lives on an interval (T₋, T₊) with T₋ < −T and T₊ > T,
  and for |t| ≤ T it stays in D with |F_j(z(t)) − F_j(z₀)| ≤ η_j|t|. No independence of the F_j is needed.
  Variants: the whole-space case (`_univ`, D bounded) and drift bounds for observables close to affine combinations of
  the F_j. This theorem is the engine of the SJSU result ([SJSU.md](SJSU.md)).
- **Certified normal-form checkers.** `checkOscChain_sound`
  ([`OscillatorChainCheck.lean`](../../KAM/EffectiveStability/OscillatorChainCheck.lean)) and `checkTorusChain_sound`
  ([`TorusChainCheck.lean`](../../KAM/EffectiveStability/TorusChainCheck.lean)): Boolean checkers, evaluated in the
  kernel with exact rational arithmetic, for finite chains of Lie transforms in Cartesian and in Fourier–Taylor form.
  A passing certificate yields the hypotheses of §2 or §1.
- **From a certified torus to confinement near it.** `certifiedTorus_confinement`
  ([`CertifiedTorusRoute.lean`](../../KAM/EffectiveStability/CertifiedTorusRoute.lean)): for the exact invariant torus
  produced by a passing torus certificate (the certificates of the track SO checker), the conclusion of §1 holds in
  the chart built from that torus, provided finite route checks pass and η_j ≥ C₃B²/2 with the explicit Cauchy constant
  C₃ = 64(Mμ/2)/r³.

The two checkers and `certifiedTorus_confinement` stay unfrozen by decision (D72, citing D40: do not freeze an
evolving certificate format).

## What is assumed and what is not claimed

- **§1 and §2 are conditional theorems**: the chart, the normal form and the remainder bound are hypotheses. They say
  nothing about whether a good normal form exists for a given system; that is supplied case by case, as in §3.
- **Finite time only.** Nothing is claimed beyond |t| ≤ T (or 10¹⁰ in §3). The bounds are linear in t; there is no
  exponential (Nekhoroshev) time scale in these statements.
- **Uniqueness is relative to V** in §1–§2: two solutions are compared only while both stay in V.
- **Minimal premises (OD-B2).** N needs no regularity; Ψ⁻ needs no regularity and is only a left inverse on the chart
  domain; only the pulled-back remainder must be angle-periodic in §1.
- **§3 is a literal theorem** about the stated polynomial. Time is dimensionless. The certificate data stay inside the
  proof; the only premise is the action box.

## Sources and proof

§1 follows the action-derivative and escape-time argument of A. Giorgilli, U. Locatelli, M. Sansottera, *Secular
dynamics of a planar model of the Sun–Jupiter–Saturn–Uranus system* (arXiv:1702.04894), §4.3, (56)–(58). §2 follows
CL20 (arXiv:2102.05959), §4.1, (32)–(37); its Appendix B is the source of the Hénon–Heiles model. The continuation
argument, arbitrary symplectic charts and anisotropic margins are additions to the sources. Plan:
[`docs/explorations/program-b-plan.md`](../explorations/program-b-plan.md).

The proofs of §1–§2 transport the flow into the chart, bound the action drift by the remainder bound while the orbit
stays in the region where it holds (a stopped-drift argument), and use a first-exit argument with the margin
a_j + Tη_j < b_j to show that the orbit cannot leave the region before time T; continuation then extends the solution
past ±T. Implementations: [`TorusProof.lean`](../../KAM/EffectiveStability/TorusProof.lean),
[`OscillatorProof.lean`](../../KAM/EffectiveStability/OscillatorProof.lean). §3 applies the multi-step (chain) form of the oscillator theorem
(`oscillatorChain_physical_disc`) to a three-step Lie-transform certificate with exact coefficients in ℚ(√2), checked by `checkOscChain` inside Lean's kernel in
34 shards ([`KAM/EffectiveStability/HenonHeiles/`](../../KAM/EffectiveStability/HenonHeiles/)).

Decisions D71–D73 in [`docs/DECISIONS.md`](../DECISIONS.md); approved texts
[`docs/tracks/B/FREEZE-PROPOSAL.md`](../tracks/B/FREEZE-PROPOSAL.md) and
[`docs/tracks/B/FREEZE-PROPOSAL-HH.md`](../tracks/B/FREEZE-PROPOSAL-HH.md).

# A magnetic field-line barrier (MAG)

**Status:** proved, frozen and sealed (2026-11-10, D68; landed in ) · frozen theorem  · axioms: standard only (, , ) · independent seal audit SEAL-AUDIT-MAG-1 PASS WITH NOTES

## In brief

In a toroidal magnetic device, magnetic field lines can be described as the orbits of a Hamiltonian system with one and
a half degrees of freedom: the toroidal angle plays the role of time. An invariant torus of this system is a surface
that field lines cannot cross, a transport barrier. The frozen statement asserts that, for one explicit perturbed
model with a quadratic control term, such a barrier exists: an analytic surface p = P(q, φ) in a stated flux range
that separates field lines below it from field lines above it, for all time. **This statement is open in the
repository**: it is frozen, and no proof has been assembled.

## Exactly what is claimed (the frozen statement)

Lean: [`KAM.Magnetic.magnetic_barrier`](../../KAM/Frozen/Magnetic/Theorems/MagneticBarrier.lean); definitions in
[`KAM/Frozen/Magnetic/Defs/`](../../KAM/Frozen/Magnetic/Defs/).

### The model

Angles are measured in turns (period one) and are real lifts. q is the poloidal angle, φ the toroidal angle (the time
variable of the field-line flow), p the flux variable.

- **Amplitude** ([`magEps`](../../KAM/Frozen/Magnetic/Defs/MagEps.lean)): ε = 3/2500 = 0.0012.
- **Integrable part** ([`magH0`](../../KAM/Frozen/Magnetic/Defs/MagH0.lean)): h(p) = p − (3/4)p² + (1/3)p³ − (1/16)p⁴,
  a polynomial on all of ℝ.
- **Perturbation with control** ([`magV`](../../KAM/Frozen/Magnetic/Defs/MagV.lean)): with a = 2π(2q − φ) and
  b = 2π(3q − 2φ),

  V(q, φ) = ε(cos a + cos b) + (1427/3200) ε² A²,  A = (32000/2777) cos a − (96000/7669) cos b.

  The factor 1427/3200 equals −h''(7/20)/2, and the second term is the quadratic control term of the general formula
  of Chandre–Vittot–Ciraolo–Ghendrih–Lima at p_c = 7/20.
- **Field-line flow** ([`magField`](../../KAM/Frozen/Magnetic/Defs/MagField.lean)), on states x = (q, p, φ) ∈ ℝ × ℝ × ℝ:

  q̇ = h'(p),  ṗ = −∂V/∂q (q, φ),  φ̇ = 1.

- **Extended Hamiltonian** ([`magHamC`](../../KAM/Frozen/Magnetic/Defs/MagHamC.lean)): on ℂ² × ℂ² with angles (q, φ) and
  actions (p, J), H((q, φ), (p, J)) = J + h(p) + V(q, φ), the same formula with complex cosines. Its Hamiltonian
  vector field (q̇, φ̇) = (∂_p H, ∂_J H), (ṗ, J̇) = −(∂_q H, ∂_φ H) restricts on real points to the field-line flow,
  with J the dummy action conjugate to φ.
- **Rotation number** ([`magAlpha`](../../KAM/Frozen/Magnetic/Defs/MagAlpha.lean)):
  α = (7913 − √5)/13618 = (43 + 18φ_g)/(74 + 31φ_g) ≈ 0.58090, with φ_g the golden mean (a noble number).

### The statement

There exists P : ℝ × ℝ → ℝ such that

1. **The surface.** (q, φ) ↦ P(q, φ) is real analytic on ℝ²; P(q + 1, φ) = P(q, φ) and P(q, φ + 1) = P(q, φ); and
   8/25 ≤ P(q, φ) ≤ 39/100 for all q, φ.
2. **It is the action component of an exact invariant torus.** There exists K : ℂ² → ℂ² × ℂ² such that, on the complex
   strip T_ρ = {θ ∈ ℂ² : |Im θ₀| < ρ, |Im θ₁| < ρ} with ρ = 3/1000000:
   - K is holomorphic on T_ρ;
   - K is primary: K(θ + k) = K(θ) + (k, 0) for θ ∈ T_ρ, k ∈ ℤ²;
   - K maps real angles to real points;
   - K is exactly invariant with frequency (α, 1): X_H(K(θ)) = DK(θ)·(α, 1) for all θ ∈ T_ρ
     ([`invarianceError`](../../KAM/Frozen/Defs/InvarianceError.lean) = 0);
   - K lies on the energy level H = 0: H(K(θ)) = 0 for θ ∈ T_ρ;
   - for real θ = (θ₀, θ₁): the φ-component of K(θ) is θ₁ (the clock), and the p-component of K(θ) equals
     P(q-component of K(θ), θ₁).
3. **Field lines exist, are unique, and never cross the surface.** For every x₀ = (q₀, p₀, φ₀) ∈ ℝ³ there is
   z : ℝ → ℝ³ with z(0) = x₀ and ż(t) = F(z(t)) for every t ∈ ℝ (F the field-line flow); every y defined on an
   order-connected set I ∋ 0 with y(0) = x₀ and ẏ = F(y) on I equals z on I; and for every real t, writing
   z(t) = (q(t), p(t), φ(t)):
   - if p₀ < P(q₀, φ₀) then p(t) < P(q(t), φ(t));
   - if p₀ = P(q₀, φ₀) then p(t) = P(q(t), φ(t));
   - if p₀ > P(q₀, φ₀) then p(t) > P(q(t), φ(t)).

There are no hypotheses. The same P appears in 1, 2 and 3.

**Consequence.** Field lines starting with p₀ < 8/25 satisfy p(t) < 39/100 for all real t, and field lines starting
with p₀ > 39/100 satisfy p(t) > 8/25 for all real t.

## What is assumed and what is not claimed

- **Open.** The statement is frozen and has no proof in the repository (manifest state DRAFT_SORRY). It is sealed only
  after its certificate chain passes Lean's kernel, the landing checks pass and a dedicated seal audit passes (D68,
  with the procedure of D63).
- **One separating surface**, not a bounded slab and not two-sided confinement: field lines below the surface may
  have arbitrarily negative flux, and those above it arbitrarily large flux.
- **One exact model.** The model includes the quadratic control term; nothing is claimed for the uncontrolled model
  ε(cos a + cos b) alone. There is no truncation remainder: the claim is about exactly this Hamiltonian. The polynomial
  h on all of ℝ is a mathematical convention; the barrier lies inside the physical flux interval (0, 1).
- **Not claimed:** charged-particle or plasma confinement, plasma stability, realizability of the control by coils,
  optimality of the control, or absence of other barriers.
- **State type.** The state space ℝ × ℝ × ℝ is an owner-approved exception to the repository's `Fin n → ℝ` convention
  (D68), consistent with the sealed lunar statements.
- **ε.** The value 3/2500 is the owner-approved fallback (D66); the planning value 3/1000 was not attempted.

## Sources and planned proof

Model: C. Chandre, M. Vittot, G. Ciraolo, Ph. Ghendrih, R. Lima, *Control of stochasticity in magnetic field lines*,
arXiv:nlin/0504033v2 (2005), general formula (8) with their equilibrium and two modes (the specialized formula (14) of
that paper is not used); L. Valvo, U. Locatelli, *Hamiltonian control of magnetic field lines: computer assisted results
proving the existence of KAM barriers*, J. Comput. Dyn. 9 (2022) 505–527, for the safety-factor profile and the
rotation number. That paper's computer-assisted theorem concerns a truncated transformed Hamiltonian, not this model.

The planned route is the track SO certificate checker: a numerical candidate torus at frequency (α, 1), certified
through the sealed isoenergetic a-posteriori KAM theorem by a finite certificate checked inside Lean's kernel, followed by
a graph-transfer step that turns the exact torus into the graph P and the non-crossing statement. The numerical gate
passed (residual about 10⁻³⁷), and a certificate package with error 7.3·10⁻²² against a threshold of 10^−19.19 and a
graph range [0.3261, 0.3876] inside [8/25, 39/100] is recorded on branch `mag-pilot`. No kernel-checked certificate chain for it is on `main` yet.

Plan: [`docs/explorations/plan-magnetic-barrier.md`](../explorations/plan-magnetic-barrier.md); approved text and
audits: [`docs/explorations/mag/FREEZE-PROPOSAL.md`](../explorations/mag/FREEZE-PROPOSAL.md),
[`docs/explorations/mag/audits/`](../explorations/mag/audits/); decisions D66, D68, D69 in
[`docs/DECISIONS.md`](../DECISIONS.md).

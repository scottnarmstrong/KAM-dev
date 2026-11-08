# A certificate checker that turns numerical KAM tori into theorems (track SO, part 1)

**Status:** ordinary theorems (not frozen; owner ruling D40 Q4 left the certifiers' soundness theorems unfrozen) ·
complete since 2026-10-30 (checker D30; sharp certifier D36; v2 certifier D44, route B D46; kernel-scale fixes D34,
D39) · no frozen ids · the lunar theorems built on the v2 certifier use only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`)

## In brief

Computers find invariant tori of Hamiltonian systems to many digits, but a floating-point computation is not a
proof. This part of the project provides a checker written in Lean: a program that reads a finite certificate (a
Hamiltonian written as a formula, a candidate torus given by finitely many Fourier coefficients, and a list of
numerical bounds) and answers `true` or `false`. The checker is run inside Lean's kernel, so a `true` answer is
itself a checked fact. A soundness theorem, proved once and for all, says that whenever the checker answers `true`
the Hamiltonian has an exact analytic invariant torus near the candidate. Applying it to a specific system then only
requires running the checker on the data and proving that the chosen frequency is Diophantine.

## Exactly what is proved

### The certificate

A certificate `c : TorusCertificate n α` ([`KAM/Certificate/Defs.lean`](../../KAM/Certificate/Defs.lean#L91)) is pure
data (rational numbers and lists; no real numbers, no proofs). For n degrees of freedom it contains:

- **The Hamiltonian** `c.ham`, an expression in the language `HamExpr n`
  ([`Expr/Basic.lean`](../../KAM/Certificate/Expr/Basic.lean)): rational constants, π, the actions I_j, the Fourier
  modes cos(2π k·θ) and sin(2π k·θ), sums, products, quotients, natural powers, exp, sin, cos and a square root. It
  denotes a function H(θ, I) on ℂⁿ × ℂⁿ.
- **The domain** D = {(θ, I) : |Im θ_i| < ρ_H for all i, |I_i − c_i| < r_i for all i}, given by ρ_H, the centre c and
  the radii r.
- **A frequency box**: rational intervals [centre_i − radius_i, centre_i + radius_i], one per coordinate.
- **The candidate torus** K(θ), θ ∈ ℂⁿ, given by finite Fourier models (with rigorous error radii) of the angle
  displacement and of the actions.
- **Parameters** (all rational): τ ∈ ℕ, the strip widths ρ > ρ∞ > 0, the bounds M, σ_K, σ_B, σ_T, the margin μ,
  γ ≤ γ̄, the ray constants σ_ω > s > 1 and ν > 0, the error budget e ≥ 0, the energy E₀ and the claimed
  displacement bound `disp`.
- **Witnesses**: approximate inverses of the Gram matrix and of the torsion matrix, auxiliary data for the
  composition H ∘ K, two precision configurations, an enclosure of π, and Taylor-order settings.
- An arithmetic backend α: exact rationals or fixed-point numbers, each with a proof (`LawfulCertArith`) that its
  rounding is outward.

### The checker

[`checkTorusCertificate c`](../../KAM/Certificate/Defs.lean#L293) is the conjunction of eight Boolean sub-checks:
the parameters' signs and orderings and that the box excludes 0 (`checkStatic`); bounds ≤ M for DH, X_H, DX_H, D²X_H
and D²H on all of D, by ball arithmetic (`checkHamBounds`); that the μ-ball around K(θ) stays in D and ‖DK‖ ≤ σ_K − μ
on the strip |Im θ_i| < ρ (`checkEmbedding`); that the invariance error X_H(K(θ)) − DK(θ)·(sω) is at most e on the
strip, for every ω in the box (`checkInvariance`); that the average energy of H ∘ K is within e of E₀
(`checkEnergy`); invertibility and an inverse bound σ_B − μ for the Gram matrix (`checkGram`); invertibility and an
inverse bound σ_T − μ for the averaged extended torsion matrix (`checkTorsion`, the isoenergetic non-degeneracy); and
the smallness test C₁ e < γ⁴ ρ^{4τ}, C₂ e ≤ disp · γ² ρ^{2τ} with the explicit constants of the a-posteriori theorem
(`checkSmallness`).

### The soundness theorem

[`KAM.Certificate.checkTorusCertificate_sound`](../../KAM/Certificate/Soundness.lean#L62). For every n, every lawful
backend α and every certificate c:

> **If** `checkTorusCertificate c = true`, **and** ω* ∈ ℝⁿ lies in the frequency box of c, **and** ω* is
> (γ, τ)-Diophantine with the certificate's γ and τ, that is γ / (|k₁| + … + |kₙ|)^τ ≤ |k·ω*| for every nonzero
> k ∈ ℤⁿ ([`IsDiophantine`](../../KAM/Frozen/Defs/IsDiophantine.lean)),
>
> **then** there are a map K∞ : ℂⁿ → ℂⁿ × ℂⁿ and a real number s∞ such that, writing T_{ρ∞} for the strip
> {θ : |Im θ_i| < ρ∞ for all i}:
> 1. 1 < s∞ < σ_ω;
> 2. K∞ is holomorphic on T_{ρ∞}, is a primary torus there (K∞(θ + k) = K∞(θ) + (k, 0) for k ∈ ℤⁿ), and maps real
>    angles to real points;
> 3. **invariance:** X_H(K∞(θ)) = DK∞(θ)·(s∞ ω*) for all θ ∈ T_{ρ∞}, so the real torus K∞(ℝⁿ) is invariant and
>    carries quasi-periodic motion with frequency vector s∞ ω*;
> 4. **energy:** H(K∞(θ)) = E₀ for all θ ∈ T_{ρ∞};
> 5. the ball of radius μ/2 around each K∞(θ) lies in D, and ‖DK∞(θ)‖ ≤ σ_K − μ/2;
> 6. **closeness:** ‖K∞(θ) − K(θ)‖ ≤ disp for all θ ∈ T_{ρ∞}, and ‖s∞ ω* − s ω*‖ ≤ disp.

The conclusion is the proposition [`CertifiedTorus c ω*`](../../KAM/Certificate/Defs.lean#L356). Norms are Lean's
sup norms on ℂⁿ and the associated operator norms; X_H = (∂_I H, −∂_θ H). The torus is isoenergetic: the energy E₀
and the direction of ω* are fixed, and the speed along the direction is the output s∞. The Diophantine premise is
not checked by the program; it is a separate Lean proof for the frequency at hand (for example quadratic and cubic
irrationals, [`QuadraticDiophantineN.lean`](../../KAM/Certificate/QuadraticDiophantineN.lean),
[`CubicDiophantine.lean`](../../KAM/Certificate/CubicDiophantine.lean)).

### The sharp certifier

[`KAM.CertificateSharp.checkTorusCertificateSharp_sound`](../../KAM/CertificateSharp/Sound.lean#L38) has exactly the
same hypotheses (with `checkTorusCertificateSharp` in place of `checkTorusCertificate`) and the same conclusion
`CertifiedTorus c ω*`. It reads the same certificates and runs the same seven sub-checks; only the smallness test is
replaced by the threshold of the sharp isoenergetic theorem `KAM.Iso.Sharp.g1_sharp` (D36).

### The v2 certifier

[`KAM.CertificateSharp.V2.checkTorusCertificateV2_sound`](../../KAM/CertificateSharp/V2/Engine.lean#L118). The v2
certifier `checkTorusCertificateV2 E c w` runs the seven non-smallness sub-checks of `checkTorusCertificate` and then
the test of an *engine* E on a witness w. An engine (`EngineV2`) bundles a computable test with a proof that a
passing test, together with the other seven checks, gives `CertifiedTorus c ω*` for every Diophantine ω* in the box;
that proof is a field of each engine and is never a hypothesis of the theorem. The theorem states:

> For every engine E, certificate c and witness w: if `checkTorusCertificateV2 E c w = true`, ω* lies in the box and
> ω* is (γ, τ)-Diophantine, then `CertifiedTorus c ω*` (the same six conclusions as above).

The engines provided are built from the v2 a-posteriori theorems (D44, D46):

- [`routeAV2`](../../KAM/CertificateSharp/V2/RouteARefinedEngine.lean#L57): the sharp engine, route A with the
  frozen data, or route A with *refined* data (bounds measured from the certificate's models and frequency-specific
  small-divisor constants, checked against the models);
- [`routeV2All`](../../KAM/CertificateSharp/V2/RouteAll.lean#L51): the sharp engine, four forms of route A (frozen
  data, refined data, the lever L8′, the ℓ¹ entry step) and two forms of route B (the modified Newton step with a
  cubic tangential error, which requires ρ ≤ 1).

The witness names one route; the certifier tries no other. At the witness `Sum.inl ()` the v2 certifier is, by
definition, the sharp certifier (`checkTorusCertificateV2_routeV2All_sharp`, proved by `rfl`), so v2 never rejects a
certificate the sharp certifier accepts.

### The first certified tori

[`KAM.Certificate.toyCert3_torus`](../../KAM/Certificate/Tests/Toy3.lean#L53): for H = I₂ + I₀²/2 + I₁²/2 the
certificate passes the original checker inside the kernel, and `CertifiedTorus` holds at the frequency
(∛2/2, ∛4/2, 1/2) with γ = 1/12, τ = 2. A two-degree-of-freedom toy at (ν₋/2, 1/2), ν₋ = 1 − 1/(40 + g), g = (√5 − 1)/2,
is in [`Tests/Toy2.lean`](../../KAM/Certificate/Tests/Toy2.lean). Negative tests (certificates that must fail) are in
[`Tests/Negative.lean`](../../KAM/Certificate/Tests/Negative.lean). These toy Hamiltonians are integrable; they test the
pipeline, not KAM persistence.

## What is assumed and what is not claimed

- The soundness theorems have no hypotheses beyond the three listed: a passing check, the frequency in the box and
  the Diophantine property. Every analytic hypothesis of the a-posteriori theorem (holomorphy, periodicity,
  reality, derivative bounds, non-degeneracy, smallness) is derived from the sub-checks inside the proof.
- The checker certifies one torus at a time, for the Hamiltonian written in the certificate. Whether that expression
  models a physical system faithfully is the business of each application (parts 2 and 3, LG00).
- A `false` answer proves nothing: the candidate may still be close to a torus.
- The theorem says nothing about stability of nearby orbits by itself. Confinement statements (parts 2 and 3) need a
  further topological argument (barrier graphs) built on top of the torus.
- Running the checker on large certificates is expensive. Lunar-size kernel checks are opt-in builds outside the
  default library (D46, D51).

## Sources and proof

The soundness proof assembles every hypothesis of the explicit isoenergetic a-posteriori theorem
`KAM.Iso.Apost.g1_explicit` (the explicit-constant form behind the sealed frozen theorem `KAM.Iso.isoenergetic_kam`,
following Haro–Luque 2019, Theorem 3.1 and §3) from the eight sub-check contracts in
[`KAM/Certificate/Sound/`](../../KAM/Certificate/Sound/), then substitutes the checked bound `disp` for the theorem's
displacement C₂ e/(γ² ρ^{2τ}). The sharp and v2 certifiers replace only the final theorem: `KAM.Iso.Sharp.g1_sharp`
(D36) and the v2 theorems (route A `KAM.Iso.Sharp2.RouteA.iso_g1_v2A`; route B, after Figueras–Haro, `iso_g1_v2B_frozen`),
with the threshold rising from about 10⁻⁷⁵ (original) to about 10⁻²⁵ (sharp) and about 10⁻¹¹ (v2 route A with
refined data) on the lunar problem. Kernel-scale fixes changed only implementations, never signed statements:
packed Fourier products (D34), balanced traversals and outward dyadic rounding of balls (D39), a log-depth jet
compiler, and segmented proofs of a single check across many modules (SO-CSPLIT). Size: `KAM/Certificate` 90 modules
(22,540 lines), `KAM/CertificateSharp` 272 modules (52,656 lines). Plan:
[`SPIN-ORBIT-PLAN.md`](../campaign/design/SPIN-ORBIT-PLAN.md); decisions D30, D34, D36, D39, D44, D46 in
[`DECISIONS.md`](../DECISIONS.md).

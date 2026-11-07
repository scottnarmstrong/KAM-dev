# Rüssmann's KAM theorem under weak non-degeneracy (track R)

**Status:** proved and sealed (2026-10-30, decision D35) · frozen ids `russmann.russmann_kam.v1` (theorem) and
`russmann.russmannCover.v1` (definition) · axioms: standard only (`propext`, `Classical.choice`, `Quot.sound`)

## In brief

The classical KAM theorem ([K.md](K.md)) assumes that the frequency map I ↦ ∇h(I) of the integrable part is a local
diffeomorphism. Rüssmann showed that a much weaker condition suffices: the image of the frequency map must not lie in
any hyperplane through the origin. The Hessian of h may then be singular everywhere, as for h(I) = I₁ + I₂³/3. This
track proves that, under Rüssmann's condition, for every small analytic perturbation all of phase space except an
arbitrarily small fraction lies on invariant tori carrying quasi-periodic motion with Diophantine frequencies, close
to the unperturbed tori. The frequencies of the surviving tori may differ from ∇h.

## Conventions

As in track K ([K.md](K.md)): z = (θ, I) ∈ ℝⁿ × ℝⁿ, angles of period 1, max norms, the complex strip T_s, the complex
action neighbourhood B_r = {I ∈ ℂⁿ : |I − J| < r for some J ∈ B}, the fundamental domain [0,1)ⁿ × B with Lebesgue
volume on ℝ²ⁿ, the frequency map ∇h (real gradient of Re h at real points), (γ, τ)-Diophantine vectors, and
**invariant Lagrangian tori** (real-analytic, primary, embedded, Lagrangian, carrying the linear flow
t ↦ K(θ + tω) of H; see K.md for the five clauses).

**The Rüssmann cover** 𝒯_R(h, f, B, r₀, τ, δ) is the union of the images K(ℝⁿ) over all K, ω, γ > 0 and I₀ such
that: K is an invariant Lagrangian torus of H = Re(h + f) on real points with frequency ω; ω is (γ, τ)-Diophantine;
the action part of every K(θ) lies within r₀ of B; I₀ ∈ B; and |K(θ) − (θ, I₀)| ≤ δ for every θ. It is the track-K
cover without the clause ω = ∇h(I₀).

## Exactly what is proved

[`KAM.Russmann.russmann_kam`](../../KAM/Frozen/Russmann/Theorems/RussmannKam.lean), with the cover
[`KAM.Russmann.russmannCover`](../../KAM/Frozen/Russmann/Defs/RussmannCover.lean).

**Data, fixed first.**

- n ≥ 1; s₀ > 0; r₀ > 0;
- B ⊆ ℝⁿ open, connected (hence nonempty) and bounded;
- h holomorphic on B_{r₀} and real on its real points;
- **Rüssmann's condition:** for every c ∈ ℝⁿ with c ≠ 0 there is I ∈ B with c·∇h(I) ≠ 0.

**Conclusion.** There is τ > n − 1 (depending only on the data above) such that for every δ > 0 and every κ > 0 there
is ε₀ > 0 (depending on the data, τ, δ and κ) with the following property. For every f and ε with

- f holomorphic on T_{s₀} × B_{r₀}, 1-periodic in each angle, real on real points,
- |f(z)| ≤ ε for every z ∈ T_{s₀} × B_{r₀}, and ε ≤ ε₀,

one has

    vol( [0,1)ⁿ × B  ∖  𝒯_R(h, f, B, r₀, τ, δ) ) ≤ κ · vol([0,1)ⁿ × B).

**Quantifier order:** n, s₀, r₀, B, h; ∃ τ; ∀ δ > 0; ∀ κ > 0; ∃ ε₀; ∀ f, ε. The exponent τ is chosen once, before the
closeness δ, the exceptional fraction κ and the perturbation; the Diophantine constant γ of each torus is
unrestricted.

## What is assumed and what is not claimed

- **Ruling R1** ([tracks/R/RULINGS.md](../tracks/R/RULINGS.md), D35): the strong form "complement ≤ κ·volume for every
  κ > 0" (option Q1(d)); ∃ τ > n − 1 before δ, κ, f; n ≥ 1; B connected; Rüssmann's condition stated directly on the
  real set B; a new frozen cover without the frequency clause; ∀ δ before ∃ ε₀.
- **Deviations from Rüssmann 2001, Theorem 1.7** (D-R1 to D-R5, [tracks/R/statement.md](../tracks/R/statement.md)):
  - D-R1: the conclusion is a bound on the phase-space volume of the union of tori, not on the measure of a parameter
    set with a continuous family of conjugacies;
  - D-R2: ordinary power-law (γ, τ) Diophantine conditions, not Rüssmann's general approximation function;
  - D-R3: period-1 angles, max norms and a uniform complex neighbourhood T_{s₀} × B_{r₀}, as in track K (Rüssmann allows
    an arbitrary complex neighbourhood);
  - D-R4: only the maximal case p = q = 0 (Lagrangian tori of full dimension); lower-dimensional elliptic or
    hyperbolic tori are not claimed;
  - D-R5: closeness ≤ δ to the unperturbed tori is added; Rüssmann's theorem has no displacement bound.
- **No rate.** The theorem is qualitative: no relation between ε and κ, and no explicit τ, ε₀ or γ, is stated. The
  frequency of a surviving torus near {I = I₀} is not claimed to equal ∇h(I₀).
- **Analytic category only**; no finitely differentiable version.

## Sources and proof

Source ([PAPERS.md](../PAPERS.md)): H. Rüssmann, *Invariant tori in non-degenerate nearly integrable Hamiltonian
systems*, Regul. Chaotic Dyn. 6(2) (2001) 119–204, Theorem 1.7, p. 126, maximal case p = q = 0; the non-degeneracy
condition §1.1–1.2; the finite-order non-degeneracy lemma, Lemma 18.2.

**Proof route** ([tracks/R/PROOF-ROUTE.md](../tracks/R/PROOF-ROUTE.md)). All KAM content comes from track P's internal
quantitative weak-non-degeneracy theorem `KAM.Planetary.weak_kam_quantitative` (a re-proof of the maximal case with
power-law divisors, an explicit displacement and a bi-Lipschitz family of tori). The provider first applies
Rüssmann's finite-order non-degeneracy lemma on the compact set B̄ (analyticity and compactness give an order μ ≥ 1
and a positive amount of non-degeneracy) and sets τ = n·μ; it then chooses a compact K ⊂ B of nearly full measure,
derives the derivative bounds that track P's theorem needs, transfers the output family to the frozen torus predicate,
and obtains the strong form through a Lipschitz bound on the defect, a global Lipschitz extension and a displacement
Δ(ε) → 0. There is no separate source dependency graph for this track; the proof is in
`KAM/Russmann/` with provider `KAM/Provider/Russmann/RussmannKam.lean`.

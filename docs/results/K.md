# Positive-measure KAM theorem (track K)

**Status:** proved and sealed (G3 on 2026-10-27; G1, G2 and HEAD on 2026-10-27; HEAD-Q on 2026-10-28) ·
frozen ids `kam.kam_positive_measure.v1`, `kam.kam_positive_measure_qualitative.v1`, `kam.aposteriori_kam.v1`,
`kam.local_uniqueness_flow.v1`, `kam.volume_not_diophantine_le.v1` · axioms: standard only (`propext`,
`Classical.choice`, `Quot.sound`)

## In brief

A nearly integrable Hamiltonian system H = h(I) + f(θ, I) describes motion on a torus of angles θ times a domain of
actions I. When f = 0 every orbit winds quasi-periodically on a torus {I = const}. The KAM theorem says that, for
every small analytic perturbation f, most of these tori survive, slightly deformed. The main result here proves that
all of phase space except a set of volume at most C·ε^{1/4} lies on surviving invariant tori, where ε is the size of
f. Three supporting theorems are frozen separately: an a-posteriori KAM theorem (an approximately invariant torus lies
near an exactly invariant one), local uniqueness of invariant tori, and a measure bound for non-Diophantine
frequencies.

## Conventions used in every statement

- **Phase space.** A point is z = (θ, I) ∈ ℝⁿ × ℝⁿ. Angles have period 1, so Tⁿ = ℝⁿ/ℤⁿ. Complex points are in ℂⁿ × ℂⁿ.
- **Norms.** The max norm on ℝⁿ, ℂⁿ and their products; linear and multilinear maps carry the induced operator norm.
  For a matrix, the bound used is the maximum row sum maxᵢ Σⱼ |Mᵢⱼ|.
- **Domains.** The complex strip is T_ρ = {θ ∈ ℂⁿ : |Im θᵢ| < ρ for all i}. For B ⊆ ℝⁿ, the complex action
  neighbourhood is B_r = {I ∈ ℂⁿ : |I − J| < r for some J ∈ B}. The fundamental domain is [0,1)ⁿ × B. Volume is
  Lebesgue measure on ℝ²ⁿ.
- **Holomorphic** means complex differentiable on the stated set. "Real on real points" means the imaginary part
  vanishes at points with real coordinates.
- **Hamilton's equations** (form Σ dIᵢ ∧ dθᵢ): X_H = (∂_I H, −∂_θ H), so θ̇ = ∂_I H and İ = −∂_θ H.
- **Frequency map.** ∇h(I) is the real gradient of I ↦ Re h(I) at real points I.
- **Diophantine vectors.** ω ∈ ℝⁿ is (γ, τ)-Diophantine if |k·ω| ≥ γ/|k|₁^τ for every k ∈ ℤⁿ ∖ {0}, |k|₁ = Σ|kᵢ|.
- **Invariant Lagrangian torus** of a real Hamiltonian H with frequency ω: a map K : ℝⁿ → ℝⁿ × ℝⁿ that is
  1. real-analytic on all of ℝⁿ;
  2. primary: K(θ + k) = K(θ) + (k, 0) for every k ∈ ℤⁿ;
  3. embedded: K(θ′) = K(θ) + (k, 0) implies θ′ = θ + k, and DK(θ) is injective for every θ;
  4. Lagrangian: the symplectic form vanishes on DK(θ)u, DK(θ)v for all u, v;
  5. carries the linear flow: t ↦ K(θ + tω) solves ż = X_H(z) for every θ.
- **The KAM cover** 𝒯(h, f, B, r₀, τ, δ) is the union of the images K(ℝⁿ) over all K, ω, γ > 0 and I₀ such that K is an
  invariant Lagrangian torus of H = Re(h + f) restricted to real points, ω is (γ, τ)-Diophantine, the action part of
  every K(θ) lies within r₀ of B, I₀ ∈ B, ∇h(I₀) = ω, and |K(θ) − (θ, I₀)| ≤ δ for every θ. (γ is unrestricted.)

## Exactly what is proved

### HEAD: positive measure with a rate

[`KAM.kam_positive_measure`](../../KAM/Frozen/Theorems/KamPositiveMeasure.lean)

**Data, fixed first.** n ≥ 2; τ > n − 1; s₀ > 0; r₀ > 0; B ⊆ ℝⁿ open and bounded, with an inner boundary layer of
linear size: there is C_B such that |{I ∈ B : dist(I, ℝⁿ ∖ B) < δ}| ≤ C_B·δ for every δ > 0. The function h is
holomorphic on B_{r₀} and real on its real points. Non-degeneracy: there is L with |I − J| ≤ L·|∇h(I) − ∇h(J)| for all
I, J in the closure of B (the frequency map is injective on B̄ with a Lipschitz inverse).

**Conclusion.** There are C > 0 and ε₀ > 0, depending only on the data above, such that for every f and every ε with

- f holomorphic on T_{s₀} × B_{r₀}, 1-periodic in each angle, real on real points,
- |f(z)| ≤ ε for every z ∈ T_{s₀} × B_{r₀}, and ε ≤ ε₀,

the set of points of [0,1)ⁿ × B that do not lie on the KAM cover with closeness δ = C·√ε has volume at most C·ε^{1/4}:

    vol( [0,1)ⁿ × B  ∖  𝒯(h, f, B, r₀, τ, C·√ε) ) ≤ C·ε^{1/4}.

The same constant C appears in the closeness and in the measure bound. C and ε₀ are uniform in f.

### HEAD-Q: qualitative form, no boundary condition

[`KAM.kam_positive_measure_qualitative`](../../KAM/Frozen/Theorems/KamPositiveMeasureQualitative.lean)

Same data as HEAD without the boundary-layer hypothesis. For every κ > 0 there is ε₀ > 0 (depending on the data and κ)
such that for every f and ε as above with ε ≤ ε₀,

    vol( [0,1)ⁿ × B  ∖  𝒯(h, f, B, r₀, τ, κ) ) ≤ κ · vol([0,1)ⁿ × B).

Here κ is both the closeness of the tori to {I = I₀} and the relative size of the exceptional set.

### G1: a-posteriori KAM at a fixed frequency

[`KAM.aposteriori_kam`](../../KAM/Frozen/Theorems/AposterioriKam.lean)

Objects, for a holomorphic parameterization K : T_ρ → ℂⁿ × ℂⁿ, a Hamiltonian h on ℂⁿ × ℂⁿ and ω ∈ ℝⁿ (bilinear
transpose, not the Hermitian adjoint; Ω₀(u₁, u₂) = (−u₂, u₁)):
L(θ) = DK(θ); Gram matrix G(θ) = LᵀL; normal frame N = Ω₀ L G⁻¹; torsion T(θ) = Nᵀ Ω₀ (DX_h(K) N − DN[ω]); ⟨T⟩ its
average over θ ∈ [0,1]ⁿ; invariance error E(θ) = X_h(K(θ)) − DK(θ)ω.

**Parameters, fixed first:** n ≥ 2, τ ≥ n − 1, 0 < ρ∞ < ρ, and positive M, σ_K, σ_B, σ_T, μ, γ̄.
**Constants:** there are C₁, C₂ > 0 depending only on these parameters such that, for every 𝔅, h, K, ω, γ, e:

- **H1.** 𝔅 ⊆ ℂⁿ × ℂⁿ is open and invariant under integer angle shifts; h is holomorphic on 𝔅, 1-periodic in θ, real
  on real points, and on 𝔅: |Dh| ≤ M, |X_h| ≤ M, |DX_h| ≤ M, |D²X_h| ≤ M.
- **H2.** K is holomorphic on T_ρ, primary on T_ρ, real on real θ; for θ ∈ T_ρ the open ball of radius μ about K(θ)
  lies in 𝔅 and |DK(θ)| ≤ σ_K − μ.
- **H3.** G(θ) is invertible and |G(θ)⁻¹| ≤ σ_B − μ on T_ρ.
- **H4.** ⟨T⟩ is invertible and |⟨T⟩⁻¹| ≤ σ_T − μ.
- **H5.** 0 < γ ≤ γ̄ and ω is (γ, τ)-Diophantine.
- **Smallness.** |E(θ)| ≤ e on T_ρ and C₁·e/(γ⁴ρ^{4τ}) < 1.

**Conclusion.** There is K∞, holomorphic on T_{ρ∞}, primary, real on real θ, with on T_{ρ∞}: E∞ = X_h(K∞) − DK∞·ω = 0;
the ball of radius μ/2 about K∞(θ) lies in 𝔅; |DK∞| ≤ σ_K − μ/2; and |K∞ − K| ≤ C₂·e/(γ²ρ^{2τ}).

### G2: local uniqueness of invariant tori of flows, modulo phase

[`KAM.local_uniqueness_flow`](../../KAM/Frozen/Theorems/LocalUniquenessFlow.lean)

**Parameters, fixed first:** n ≥ 2, τ ≥ n − 1, ρ > 0, positive M, σ_K, σ_B, σ_T, μ. **Constant:** there is c > 0 depending
only on these, such that for every 𝔅, h, K₁, K₂, ω, γ: if 𝔅, h satisfy H1; K₁ satisfies H2–H4 on T_ρ; γ > 0 and ω is
(γ, τ)-Diophantine; E₁ = 0 on T_ρ; K₂ is holomorphic on T_ρ, primary, real on real θ, with K₂(T_ρ) ⊆ 𝔅 and E₂ = 0 on
T_ρ; and |K₁ − K₂| ≤ c·γ²ρ^{2τ} on T_ρ — then there is φ ∈ ℝⁿ with K₂(θ) = K₁(θ + φ) for every θ ∈ T_{ρ/2}.
(No upper bound γ̄ is needed here.)

### G3: measure of the non-Diophantine frequencies

[`KAM.volume_not_diophantine_le`](../../KAM/Frozen/Theorems/VolumeNotDiophantineLe.lean)

For every n, every τ > n − 1 and every bounded Ω ⊆ ℝⁿ there is C such that, for every α > 0,
vol{ω ∈ Ω : ω is not (α, τ)-Diophantine} ≤ C·α.

## What is assumed and what is not claimed

- **Analytic category only.** h and f are holomorphic on a uniform complex neighbourhood T_{s₀} × B_{r₀} (ruling D9,
  Q5). No finitely differentiable version is claimed.
- **Non-degeneracy** is the bi-Lipschitz-type lower bound on ∇h over B̄, not the pointwise condition det ∇²h ≠ 0; the
  pointwise condition alone does not imply it (it gives no global injectivity).
- **Rate ε^{1/4}, not √ε.** The optimal exponent 1/2 (Pöschel, Neishtadt) is not claimed; the route (decision D8,
  deviation D-MEAS-1) gives 1/4 with γ ~ ε^{1/4}. The constants C, ε₀, C₁, C₂, c are existential and not explicit.
  (Explicit constants for G1 are proved separately, outside the frozen statements: `KAM.Sharp.g1_sharp`.)
- **Regular boundary.** HEAD uses the inner boundary-layer reading of "regular boundary" approved in D11; convex or
  Lipschitz domains satisfy it. HEAD-Q needs no boundary condition.
- **Uniform G1.** HL19's constants depend on the input; here they depend only on the fixed parameters, through the
  margin μ and the bound γ ≤ γ̄ (ledger D-G1-1, D11). Without γ̄ the statement is false (a counterexample with
  h = ½|I|², K = (θ, 0), γ → ∞ was checked in Lean during the statement audit). Not transcribed from HL19: the
  estimate for first integrals, the bound on (DK∞)ᵀ and the H1 bound on DX_hᵀ (each implied up to a factor 2n).
- **G2 is a result of this formalization** (deviation D-UNIQ-1): no cited source states local uniqueness for flows;
  it adapts GJLV05 Theorem 2 (maps).
- **Specialization of HL19:** d = n (full-dimensional tori), canonical symplectic structure, primary tori.
- **Not claimed:** lower-dimensional or non-primary tori; the frequency of a torus differing from ∇h(I₀) (HEAD
  requires equality); any statement about the dynamics off the tori.

## Sources and proof

Statement sources ([PAPERS.md](../PAPERS.md)): Pöschel, *A lecture on the classical KAM theorem* (2001), Classical KAM
Theorem p. 6 and §1d p. 5 (HEAD, HEAD-Q, G3); Haro–Luque, J. Differential Equations (2019), Theorem 3.1 (G1);
de la Llave–González–Jorba–Villanueva, Nonlinearity 18 (2005), Theorem 2 (template for G2). Rulings: D1, D2, D8, D9,
D11; the planning statement is [docs/statement.md](../statement.md); the deviations are in
[ERRATA-AND-DEVIATIONS.md](../ERRATA-AND-DEVIATIONS.md).

**Proof route.** G1 is proved by the parameterization method in sup norms on complex strips (D12): cohomological
equations for Diophantine ω, the approximate Lagrangian frame and torsion, and a Newton iteration with nested strip
losses. G2 linearizes at K₁, fixes the phase by an average normalization, and uses a uniqueness constant independent
of γ. For HEAD, G1 is applied to the unperturbed torus θ ↦ (θ, (∇h)⁻¹ω) for each Diophantine ω, which gives a torus
for every such frequency; re-applying G1 and G2 gives Lipschitz dependence on ω with defect O(ε/γ⁴) (after Calleja–
Celletti–de la Llave 2013, Cor. 29–30); a McShane extension in action coordinates and a lipeomorphism argument (Pöschel
2001, Prop. 1–2; Biasco–Chierchia 2018) convert this, with G3, into the volume bound; γ ~ ε^{1/4} balances the terms.
HEAD-Q follows from the same construction without a rate.

Blueprint: [blueprint/blueprint.pdf](../../blueprint/blueprint.pdf). Dependency graph (453 nodes, all resolved):
[docs/graph/K/DEPGRAPH.md](../graph/K/DEPGRAPH.md). Providers: `KAM/Provider/*.lean`.

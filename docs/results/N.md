# Nekhoroshev stability and averaging (track N)

**Status:** proved and sealed (N-QC and N-ZERO on 2026-10-27; N-HEAD-C, N-AVERAGING-MEAN and N-AVERAGING-MOST on
2026-10-28; N-PARTIAL-CONVEX on 2026-10-29) · frozen ids `nekhoroshev.quasiConvex_nekhoroshev_complexBound.v1`,
`nekhoroshev.d25.partialConvex_nekhoroshev.v1`, `nekhoroshev.d28.averaging_mean.v1`,
`nekhoroshev.d28.averaging_most.v1`, `nekhoroshev.quasiConvex_isoenergetic_derivative.v1`,
`nekhoroshev.zero_perturbation.v1` · axioms: standard only (`propext`, `Classical.choice`, `Quot.sound`)

## In brief

KAM theory controls most orbits forever; Nekhoroshev theory controls every orbit for an exponentially long time.
The main theorem of this track proves that, for a quasi-convex analytic integrable Hamiltonian h perturbed by f of
size ε, the actions of every orbit move by at most C·ε^{1/(2n)} for times up to T·exp(c·ε^{−1/(2n)}), with constants
depending only on the dimension and on uniform bounds for h. A second theorem gives a stopped exponential estimate
when h is convex in some actions only and the remaining variables are arbitrary (the setting of planetary
problems). Two averaging theorems bound the action drift over the time 1/ε for most initial conditions. Two small
supporting theorems complete the set.

## Conventions

Phase point z = (θ, I), period-1 angles (except in N-PARTIAL-CONVEX, below), max norms, the complex strip T_s, the
complex action neighbourhood, X_H = (∂_I H, −∂_θ H) and the frequency map ∇h = gradient of Re h, all as in track K
([K.md](K.md)). Further definitions:

- **Domains.** B(R) is the open max-norm ball of radius R in ℝⁿ; B_s^ℂ = {I ∈ ℂⁿ : |I − J| < s for some J ∈ B(R)};
  its real points form the real ball B(R + s); D_s = T_s × B_s^ℂ.
- **Analytic integrable h** (`IsAnalyticIntegrable R s h`): h holomorphic on B_s^ℂ, continuous on its closure,
  bounded there (by some unspecified constant), real at real points, Re h of class C³ on the real points.
- **Analytic perturbation of size ε** (`IsAnalyticPerturbation R s ε f`): ε ≥ 0; f holomorphic on D_s, continuous on
  its closure, 1-periodic in θ, real at real points with real action in B(R + s), and |f| ≤ ε on D_s.
- **Quasi-convexity** QC(m) on an open set U: m > 0, Re h of class C² on U, and for every I ∈ U: ∇h(I) ≠ 0 and
  D²h(I)[v, v] ≥ m|v|² for every v with ∇h(I)·v = 0 (Euclidean dot product, max norm |v|).
- **Derivative bounds** B(M) on U: M > 0, U open, Re h of class C³ on U, and every coordinate partial derivative of
  order 1, 2 or 3 bounded by M in absolute value on U.
- **Complex Hessian bound:** h complex C² on B_s^ℂ and ‖D²h(z)‖ ≤ M_c (operator norm) for every z ∈ B_s^ℂ.
- **Solution on J in U** of a real Hamiltonian H: for every t ∈ J, I(t) ∈ U, H is differentiable at z(t) and
  z′(t) = X_H(z(t)) (two-sided derivative, also at endpoints of J).
- H = Re(h + f) restricted to real points.

## Exactly what is proved

### N-HEAD-C: quasi-convex Nekhoroshev theorem, exponents 1/(2n)

[`KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`](../../KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexNekhoroshevComplexBound.lean)

**Fixed first:** n ≥ 3 and R, s, M, m, M_c, ω_min > 0. **Constants:** there are C, T, c, ε₀ > 0, depending only on
these, with C·ε₀^{1/(2n)} ≤ R/4, such that for every h, f and ε with

- h analytic integrable; complex Hessian bound M_c; |∇h(I)| ≥ ω_min for every real I ∈ B(R);
- QC(m) and B(M) on the real ball B(R + s);
- f an analytic perturbation of size ε, with 0 < ε ≤ ε₀,

and every θ₀ ∈ ℝⁿ, I₀ ∈ B(R/2), writing T_ε = T·exp(c·ε^{−1/(2n)}):

1. there is a solution z of H on [−T_ε, T_ε] in B(R) with z(0) = (θ₀, I₀);
2. |I(t) − I₀| ≤ C·ε^{1/(2n)} for every |t| ≤ T_ε;
3. for every 0 ≤ L ≤ T_ε, every solution y on [−L, L] in B(R) with y(0) = (θ₀, I₀) equals z on [−L, L].

The constants are uniform in both h and f.

### N-PARTIAL-CONVEX: stopped Nekhoroshev estimate, convex in the fast actions

[`KAM.Nekhoroshev.partialConvex_nekhoroshev`](../../KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean)

**Setting.** n ≥ 2 fast degrees of freedom, k ≥ 1 slow ones. Positions (φ, q) ∈ ℝⁿ × ℝᵏ, momenta (I, p) ∈ ℝⁿ × ℝᵏ;
fast angles φ have period 2π, slow variables have no periodicity. The Hamiltonian is H_μ = h(I) + μ·Re P(φ, q, I, p).
Exponents a = 2/(6n² − 3n + 14) and b = 3/(6n² − 3n + 14) (Nekhoroshev's, all steepness indices one). The inner core
of a set U at depth d is {x ∈ U : the closed max-norm ball of radius d about x lies in U}.

**Fixed first:** open convex G, G′ ⊆ ℝⁿ with the collar condition: the closed max-norm ball of radius ρ about every
point of G lies in G′; an open slow domain D ⊆ ℝᵏ × ℝᵏ; ρ, g, m, M_c > 0; and h with:
h holomorphic and complex C² on the complex ρ-neighbourhood of G′, real at real points there, ‖D²h‖ ≤ M_c there; on
its real points U′, Re h of class C³, |∇h| ≥ g, and for one global sign σ ∈ {1, −1}, σ·D²h(I)[v, v] ≥ m·Σvᵢ².

**Conclusion.** There is μ₀ > 0 (depending on all the fixed data, including h) such that for every 0 < μ < μ₀, every P,
every C > 0 and every curve z, if

- P is holomorphic on the complex tube {real parts of fast actions in G′, real parts of slow (q, p) in D, all
  imaginary parts < ρ}, bounded by 1 there, real at real points, 2π-periodic in each fast angle;
- z is a solution of H_μ on [0, C] with fast actions in G;
- the initial fast action I(0) lies in the inner core of G at depth μ^b,

then for every t ∈ [0, min(C, μ⁻¹·exp(μ^{−a}))] such that (q(u), p(u)) lies in the inner core of D at depth μ^b for
all u ∈ [0, t]: |I(t) − I(0)| ≤ μ^b/2.

### N-AVERAGING-MEAN and N-AVERAGING-MOST: averaging over the time 1/ε

[`KAM.Nekhoroshev.averaging_mean`](../../KAM/Frozen/Nekhoroshev/Theorems/AveragingMean.lean) ·
[`KAM.Nekhoroshev.averaging_most`](../../KAM/Frozen/Nekhoroshev/Theorems/AveragingMost.lean)

**Common data.** n ≥ 2; R, s > 0; h analytic integrable; f an analytic perturbation of size 1; the frequency
condition holds on B(R) in one of two global forms: either D(∇h)(I) is surjective for every I ∈ B(R), or for every
I ∈ B(R), ∇h(I) ≠ 0 and (v, λ) ↦ D(∇h)(I)v + λ∇h(I) is surjective; K ⊆ ℝⁿ × ℝⁿ compact with all actions in B(R/2).
The Hamiltonian is H_ε = Re(h + ε·f). The error of a solution from x is sup over t ∈ [0, 1/ε] of |I(t) − I(0)|.

**MEAN.** There are A, ε₀ > 0 (depending on the common data) such that for every 0 < ε ≤ ε₀ and every family Φ
assigning to each x ∈ K a solution Φ(x, ·) of H_ε on [0, 1/ε] in B(R) with Φ(x, 0) = x: the error x ↦ err(x) is
integrable on K; ∫_K err ≤ A·√ε (unnormalized volume); and for every κ > 0 there is a measurable E ⊆ K with
vol E ≤ κ and |I(t) − I(0)| ≤ A√ε/κ for every x ∈ K ∖ E and t ∈ [0, 1/ε].

**MOST.** There are A, ε₀, η₀ > 0 with η₀ ≤ R/4 such that for every 0 < ε ≤ ε₀ and 0 < η ≤ η₀ there is a measurable
E ⊆ K with vol E ≤ A√ε/η such that every x ∈ K ∖ E has a solution z of H_ε on [0, 1/ε] in B(R) with z(0) = x and
|I(t) − I(0)| ≤ η for t ∈ [0, 1/ε]. Here existence is a conclusion, not a hypothesis.

### Supporting theorems

- **N-QC** [`quasiConvex_isoenergetic_derivative`](../../KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexIsoenergeticDerivative.lean):
  for any n, if h satisfies QC(m) on an open U, I ∈ U and λ > 0, then the derivative at (I, λ) of
  (J, μ) ↦ (Re h(J), μ∇h(J)) is a bijection ℝⁿ × ℝ → ℝ × ℝⁿ.
- **N-ZERO** [`zero_perturbation`](../../KAM/Frozen/Nekhoroshev/Theorems/ZeroPerturbation.lean): for any n and R, s > 0,
  h analytic integrable, f an analytic perturbation of size 0, θ₀ ∈ ℝⁿ and I₀ ∈ B(R/2), the curve
  t ↦ (θ₀ + t∇h(I₀), I₀) is a solution of H on all of ℝ in B(R) (it starts at (θ₀, I₀) and its action is constant).

## What is assumed and what is not claimed

- **N-HEAD-C carries two inputs beyond Bounemoura–Marco's class** (D20, deviation D-N-8): a uniform complex Hessian
  bound M_c and a frequency lower bound ω_min, both fixed before the constants. The headline with real bounds only
  (N-HEAD) is not frozen and not claimed: its route through Pöschel's theorem needs a complex Hessian bound that real
  C³ bounds do not give uniformly (source gap F-N1). n ≥ 3 (D17); n = 2 is not claimed impossible.
- **Rulings D18:** the size bound is pointwise |f| ≤ ε (BM11 uses a strict sup bound); ε = 0 is a separate theorem
  (N-ZERO); constants uniform in h and f; existence on the whole interval and uniqueness are stated. Only the
  classical endpoint exponent 1/(2n) is claimed: no improved trade-off, no Gevrey version, no optimality, no steep
  (non-convex) Hamiltonians.
- **N-PARTIAL-CONVEX (D25)** specializes Nekhoroshev 1977, Theorem 4.4, to a definite (convex or concave) fast
  Hessian on the enlarged domain G′, with h fixed and a complex Hessian bound (deviations D-N-ADD-1, -3, -4, -6). It is
  stopped: the solution on [0, C] with fast actions in G is a hypothesis, and the slow variables are only tested up to
  the queried time; long-time existence is not asserted. Its exponents are Nekhoroshev's a and b, not 1/(2n).
  Fast angles have period 2π here, unlike the period-1 convention elsewhere.
- **Averaging (D28)** is the analytic, Hamiltonian specialization of Arnold–Kozlov–Neishtadt Theorem 6.11 and
  Corollary 6.1; constants depend on the fixed h, f and K. MEAN quantifies over supplied solution families and
  assumes nothing about their error; MOST asserts existence on the good set. Neishtadt's printed proof step (17)
  interchanges a supremum and an integral; the proof uses a repaired argument (candidate erratum E-NAVG-NEI-17).
- Constants are existential, not explicit, in all six statements.

## Sources and proof

Sources ([PAPERS.md](../PAPERS.md)): Pöschel, Math. Z. 213 (1993), Theorem 1, pp. 190–191, via Bounemoura–Marco,
Nonlinearity 24 (2011), Theorem 2.1 and Lemma 3.3 (N-HEAD-C, N-QC); Nekhoroshev, Russian Math. Surveys 32 (1977),
Theorem 4.4, p. 30 (N-PARTIAL-CONVEX); Arnold–Kozlov–Neishtadt (2006), Theorem 6.11 and Corollary 6.1, p. 243, and
Neishtadt, Dokl. Akad. Nauk SSSR 226 (1976) (averaging). Track statement: [tracks/N/statement.md](../tracks/N/statement.md);
rulings D17, D18, D20, D25, D28.

**Proof route.** N-HEAD-C follows Pöschel's proof: a resonant normal form by Lie transforms (Iterative and Normal
Form Lemmas), stability estimates by energy conservation and quasi-convexity in nonresonant and resonant zones, the
geometry of resonances on maximal lattices, and the choice K = (ε₀/ε)^{1/(2n)}; conversions to period 1 and max
norms, and the ODE continuation and uniqueness, are proved explicitly. N-PARTIAL-CONVEX uses an extended normal form
and a convex energy argument on the collar G′ in place of the steepness lemma. The averaging theorems compare with
the averaged system, whose actions are constant, and use the frequency-rank condition to bound the volume of initial
data near resonances.

Blueprint: [blueprint-N/blueprint.pdf](../../blueprint-N/blueprint.pdf). Dependency graph (728 nodes, all resolved):
[docs/graph/N/DEPGRAPH.md](../graph/N/DEPGRAPH.md). Providers: `KAM/Provider/Nekhoroshev/`.

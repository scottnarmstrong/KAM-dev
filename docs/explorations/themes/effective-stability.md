# Effective stability and planetary lifetimes: ambition and programs A–D

[← Back to the catalogue](../README.md)

Five documents from 30 October 2026, written after Zohar's question about chaos and slow transport (is the Solar System
"chaotic according to KAM", and why does nothing happen for billions of years?). [ambition](../ambition.md) reframes the
question from "does this torus exist?" to "how far can any trajectory in a specified region travel before a specified
time?", which allows chaotic motion, and proposes four programs. The four program plans develop each into exact
candidate statements, small Python experiments, work packages and ready worker briefs. All five are proposals: nothing is
frozen, no Lean was built, and no owner decision on them is recorded in [DECISIONS.md](../../DECISIONS.md) as of
31 October.

Common conclusions. A uniform 5-Gyr theorem for the observed inner Solar System is not a credible near-term deliverable;
the numerical ensembles (about 1 % large Mercury eccentricity excursions over 5 Gyr, Lyapunov time about 5 Myr) are
evidence against it, though not a proof. A realistic first target is a certified time-versus-region curve for a pinned
secular model, with every tail and coordinate change bounded. LG00 is a good pilot for the tools but a weak headline
for the chaos question: it has two degrees of freedom, and LG00 (2000) already proved rigorous confining tori for it.

| Program | Question | First concrete milestone | Size of the reusable core |
|---|---|---|---|
| [A](../program-a-plan.md) | Make Nekhoroshev usable: explicit constants, then steep h | Checked 3-degree-of-freedom quasi-convex example | A1 4–10k Lean lines; A2 30–70k |
| [B](../program-b-plan.md) | Confinement near a torus or elliptic equilibrium from a finite normal form | Caracciolo–Locatelli's Hénon–Heiles example | 14–26k |
| [C](../program-c-plan.md) | Confinement from resonant approximate integrals | An original 13-term three-oscillator example | 11–25k |
| [D](../program-d-plan.md) | A 5-Gyr lifetime in a named planetary model | Secular SJSU action bounds; executable partial-convex gate | D1 9–18k; D2 10–22k beyond B |

## Ambition: certify slow transport, then a planetary lifetime

**[ambition.md](../ambition.md)** · 30 October 2026 · research note for Zohar and Scott · status: **proposed**

The note separates chaos from transport: a Lyapunov time measures how fast nearby orbits separate, not how fast actions
change by order one; and in three or more degrees of freedom the barrier argument for KAM tori fails by dimension count. It
recommends building a reusable, kernel-checked effective-stability certificate for a *region* of initial conditions:
it should accept finite normal forms, retained resonances and approximate integrals and return an explicit confinement
time in physical units. Four programs: A, quantitative Nekhoroshev with a certificate interface; B, effective stability
near a torus or an elliptic equilibrium; C, confinement from resonant approximate integrals; D, a numerical planetary
lifetime with explicit model boundaries. Recommendation: B1 + C as the main program, a secular Sun–Jupiter–Saturn–Uranus
lifetime (GLS17) as the application, A1 extracted along the way. A 5-Gyr certificate for the observed inner planets is
"a research destination with unresolved mathematics and numerical feasibility".

- **Numbers.** GLS17's numerical estimate: about 10¹⁰ yr at a normalized radius slightly below 10⁻⁷, against an
  observational uncertainty scale about 7·10⁻⁷; its intermediate expansion has 94,109,751 monomials; it is not a
  rigorous proof. Budget arithmetic: a margin of 10⁻³ over 5 Gyr, half reserved, needs a drift rate η ≤ 10⁻¹³ per year.
  Size estimates (handwritten Lean, factor-two uncertainty): A1 4–10k, A2 30–70k, B 12–25k + 12–25k, C 5–12k + 8–20k,
  D 10–25k each for D1 and D2.
- **What it inventories.** The repository already has explicit quasi-convex constants, the planetary exponent
  a = 2/(6n² − 3n + 14), an all-time secular SJS box, and the v2 routes; a second theorem that the same secular box
  lasts 5 Gyr "would add little".
- **Also.** A six-step gate table, six "quick choices" for Zohar and Scott, and a table of consequences for all twelve
  earlier explorations.
- **Later correction.** Its statement that "hybrid is a design" was overtaken: programs A–D (inspected at a later
  commit) report that the hybrid restart theorems have landed in Lean, with no hybrid certificate wiring yet.

## Program A: explicit stability certificates, then the steep theorem

**[program-a-plan.md](../program-a-plan.md)** · 30 October 2026 · research and implementation plan · status:
**proposed**

A1 is a small numerical interface to the existing quasi-convex Nekhoroshev theorem: a proposed root A-QC-WINDOW in
rational "window" form (no giant exponentials are computed), a sufficient finite certificate for polynomial h and
trigonometric f, and a checked three-degree-of-freedom example. A2 is the general steep theorem of
Guzzo–Chierchia–Benettin, with its literal constant map, a proposed A-STEEP, and a quartic test Hamiltonian that is steep
(indices 3) but not quasi-convex. The plan warns that neither certifies the observed planets: the Kepler Hamiltonian is
properly degenerate, so neither quasi-convexity nor steepness holds on the full action space. It ranks five
applications, from the A1 pilot to an inner-planet good set that A alone cannot deliver.

- **Numbers.** On a simple quadratic model the existing global threshold is about 1.16·10⁻³⁰ in the analytic perturbation
  norm. At perturbation 10⁻³⁶ the certified time (10^3.6) is far below a direct derivative bound (3.4·10²⁷): "exponential
  time need not mean a useful improvement at the threshold". Proposed pilot: perturbation 31·10⁻⁶⁰, action drift
  ≤ 10⁻¹¹ through |t| ≤ 10⁵⁰⁰ (dimensionless; exact rational comparisons passed in Python, not in Lean). Thresholds
  3.35·10⁻⁴¹, 1.94·10⁻⁶³, 6.32·10⁻⁸⁷ at n = 4, 6, 8. Steep quartic: ε₀ ≈ 1.9·10⁻¹⁶⁰. A1: 4–10k lines, 2–4 weeks;
  A2: 30–70k, 8–18 further weeks.
- **Candidate errata.** A-GCB-KAPPA (range of κⱼ in GCB), A-BN-MASS (a mass-ratio sentence in Barbieri–Niederman),
  A-BBGL-PSTEEP (a quasi-convex counterexample to "quasiconvex functions are P-steep" in the June 2026
  Bambusi–Barbieri–Giralt–Langella preprint, which would be the source of a forced extension A3).
- **Also.** Two ready worker briefs (A-P0 statement packet, A-P1 rational scalar engine) and five owner decisions.
- **Corrects** [ambition](../ambition.md): its "hybrid is a design" has been overtaken by code (the hybrid restart
  theorems have landed; no hybrid certificate wiring was found), and the LG00 scout's "missing sqrt" is stale. Programs
  B, C and D make the same two corrections.

## Program B: certified effective stability near a torus or an elliptic equilibrium

**[program-b-plan.md](../program-b-plan.md)** · 30 October 2026 · research and implementation plan · status:
**proposed**

B1 is a checker for finite canonical normalizations and their remainders, with two proposed theorems for an entire
initial region. B1-T: if H∘Ψ = N(J) + R on a canonical cylinder, |∂_φR| ≤ η and a + ηT < b, then every solution from
the inner box exists on [−T, T], is unique, and its actions drift by at most η|t|. B1-E is the Cartesian oscillator
version; it includes zero actions and needs no positive-definite energy, so mixed-sign elliptic equilibria are covered.
An optional B2 formalizes known near-torus results: exponential stability, doubly exponential stability under stable
steepness (Bounemoura–Fayad–Niederman), and doubly exponential stability for all but an exponentially small fraction
of data (Bounemoura–Farré). First instance: Caracciolo–Locatelli's mixed-sign Hénon–Heiles example. Ambitious
applications: a secular SJSU lifetime with D, and a restricted Sun–Jupiter Trojan lifetime.

- **Numbers.** Proposed Hénon–Heiles target: actions I_j(z₀) ≤ (1/12500)², unique solution through |t| ≤ 10¹⁰ model
  units, drift ≤ 1.2·10⁻⁹. An exact quartic normal form over ℚ(√2) was computed in 1.6 CPU-s (Python, not Lean).
  Dense monomial counts show why the 94-million-term GLS17 expansion cannot be rebuilt in a Python dictionary (3 GB even
  at 32 bytes per term). Core B0–B4: 14–26k Lean lines; Hénon–Heiles end to end in 5–9 weeks; a planetary lifetime is a
  further 3–6+ month research milestone.
- **Candidate errata.** Caracciolo–Locatelli (degree index; ν₂ = O(μ) should be O(√μ)); GLS17 (λ₅ printed for λ₂;
  a sum starting at j = 0). The ν₂ finding is also in [program-c-plan](../program-c-plan.md), which cites the same
  paper (arXiv:2102.05959) as "CL21" where this plan says "CL20".
- **Also.** Ready briefs B0 (exact statements) and B1 (finite-region dynamics); six owner decisions.

## Program C: certified confinement from resonant approximate integrals

**[program-c-plan.md](../program-c-plan.md)** · 30 October 2026 · research and implementation plan · status:
**proposed**

C1 is a general first-exit theorem. For a C¹ vector field X, observables F_j with |dF_j(X)| ≤ η_j on the closure of a
domain D, and every boundary point of D separated from the initial ranges by more than η_jT in some F_j, every solution
starting in Q exists on [−T, T], stays in D and has |F_j(z(t)) − F_j(z₀)| ≤ η_j|t|; periodic angles are allowed. The
derivative certificate can differentiate a numerically suggested polynomial integral against the *original* vector
field, so it needs neither an exact KAM torus nor a canonical inverse. C2 adds resonant and forced algebra; C3 a finite
good-set theorem that certifies a measure fraction of an initial box. The test case is an original 13-term
three-oscillator Hamiltonian with an indefinite quadratic part and an exact integral broken at size 10⁻⁸.

- **Numbers.** Proposed toy theorem: every point of a box of volume 1/64 stays in {S < 1/2} with |ΔS| ≤ 10⁻⁸|t| for
  |t| ≤ 10⁷. Exact replay of Mogavero–Hoang–Laskar's Table II (30 resonant combinations): rank 6, and the two proposed
  quasi-integrals annihilate every row; adding two weaker modes raises the rank to 8. A binary partition of 16 initial
  coordinates already costs about 1,092 CPU-h at 60 s per cell. Core 11–25k Lean lines; a modest planetary instance in
  10–14 weeks if the early gates close.
- **Obstacles stated.** The inner-planet degree-six coefficient table is not available in the papers; the two linear
  quasi-integrals leave one direction in (X₁, X₂) unconstrained, so boundary separation can fail even when the
  derivative bounds pass; filtered numerical diagnostics are not uniform derivative bounds.
- **Candidate errata.** E-C-CL21-1 (the ν₂ order, also reported by [program-b-plan](../program-b-plan.md) under the label
  CL20) and E-C-CL21-2 (a time-unit ambiguity, unresolved).
- **Also.** Ready briefs C0 and C1; six owner decisions.

## Program D: a checked planetary lifetime with a named model

**[program-d-plan.md](../program-d-plan.md)** · 30 October 2026 · planning report · status: **proposed**

D recommends a 5-Gyr secular action-confinement certificate for a precisely specified planar
Sun–Jupiter–Saturn–Uranus model (the degree-18 construction of GLS17), built on B's normal-form checker and C's boundary
method, plus a bounded task D1 that makes the existing partial-convex planetary theorem executable and publishes its
mass/time/region trade-off. Three findings shape it. The literal existing stopped estimate fails a realistic-mass test
before any analytic constant is computed. A long secular safety theorem alone may be too weak, because conservation of
the AMD already gives generous non-crossing margins for SJSU's nominal elements; the new result should bound individual
normal-form actions. SJSU has two effective secular degrees of freedom after reduction, so a four-giant secular model or
the full planar SJS problem is needed for three. On the observed inner Solar System: "not yet".

- **Numbers.** For an SJS-like box at μ = 4773/5000000, AMD allows action drift below 1/2000 but the stopped route
  needs at least 0.2605 (over 520 times too large); it would need μ < 10⁻³² ("a rejection of a sufficient formula, not
  evidence that the planets are unstable"). AMD alone bounds the SJSU eccentricities by about 0.061, 0.096 and 0.204, with
  radial gaps of about 3.1 and 4.8 au (a diagnostic). Proposed D2 target: action radius 10⁻⁷ inside 2·10⁻⁷ (source
  units), drift rate ≤ 10⁻¹⁷ per year over 5 Gyr, e_J, e_S < 3/20, e_U < 1/4. First-run ceilings: 1,000 CPU-h and 100 GB.
  D1 9–18k lines; D2 10–22k beyond B; weeks 1–14 conditional on B1.
- **Candidate errata.** GLS17 p. 12 (λ₅ for λ₂; summation from j = 0) and a new one at p. 25, (57): ρ^(l+1) should be ρ^l.
- **Also.** Ready briefs D-P0 (model charter, to be written as `program-d-model-charter.md`, which does not exist yet)
  and D-P1 (finite partial-convex gate); six owner decisions.

[← Back to the catalogue](../README.md)

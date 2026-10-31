# Ambition: certify slow transport, then a planetary lifetime

Research note, 30 October 2026. Repository snapshot:
377591e0fd09d8abe64d06e2a127cc570f7a80c5, branch ambition.

**Recommendation.** Build a reusable, kernel-checked effective-stability certificate for a
region of initial conditions. It should accept finite normal forms, retained resonances,
and approximate integrals, and return an explicit confinement time in physical units.
Use a source-backed secular planetary lifetime as the ambitious first application,
then a model with at least three degrees of freedom after exact symmetry reductions.
Treat a five-billion-year certificate for the observed inner Solar System as a research
destination with unresolved mathematics and numerical feasibility.

This changes the question from “does this invariant torus exist?” to “how far can any
trajectory in this specified region travel before this specified time?” It permits chaotic
motion. It also produces useful results if the strongest planetary target fails: a general
theorem, a reusable checker, and an honest time-versus-region-size curve.

These are proposed mathematical interfaces, not new frozen declarations or approved briefs.
No Lean proof, numerical closure, or model-to-observation correspondence is claimed here.

## 1. What Zohar is pointing at

### Chaos and slow transport describe different things

The phrase “chaotic according to KAM” needs a small correction. KAM proves persistence of
quasiperiodic invariant tori under specified hypotheses. It does not prove that an orbit
outside those tori is chaotic, or determine the transport rate of that orbit. The evidence
for chaos of the observed inner planets comes principally from numerical dynamics.

A Lyapunov time measures local exponential separation of nearby trajectories. It does not
measure the time needed for eccentricities or other actions to change by order one.
An orbit can lose phase predictability while remaining in a narrow region of action space.

For an autonomous Hamiltonian with n degrees of freedom, a Lagrangian invariant torus has
dimension n and a regular energy surface has dimension 2n−1. At n=2, suitably situated
tori can separate an energy surface and form barriers. At n≥3, their codimension in that
surface is at least two; the barrier argument no longer follows from that count alone.
Apply this dimension count after reducing additional conserved quantities and symmetries.
Resonance channels can
permit Arnold diffusion. Neither a positive numerical Lyapunov exponent nor the failure
of a barrier argument proves that a particular orbit diffuses macroscopically.

A useful exact target is therefore

$$
 \forall z_0\in Q,\quad
 \exists!\,z:[-T,T]\longrightarrow D,\qquad
 \dot z=X_H(z),\quad z(0)=z_0,\quad
 |A_j(z(t))-A_j(z_0)|\le \Delta_j.
$$

Here H, Q, D, the observables A_j, their tolerances, and the unit of T are specified.
The uniqueness clause means agreement of any two solutions on their common interval.
The theorem must establish existence throughout the interval, not assume it.
Q should have positive volume, or positive conditional measure on a specified energy
surface. One torus does not supply that conclusion.

The observables matter. A bound on semimajor axes alone need not prevent an eccentricity
excursion or collision. A physical safety theorem needs eccentricity, angular-momentum
deficit (AMD), or separation bounds as well, with the coordinate transfer proved.

### What the numerical evidence actually says

The following are numerical findings about particular force models and ensembles.

- The usual inner-system Lyapunov time is about 5 Myr, with substantial variation in
  finite-time estimates. Five Gyr is about 1,000 such times. Mogavero–Laskar's secular
  model uses quasiperiodically prescribed outer-planet forcing and reproduces several
  statistics of fuller integrations; it is not an exact reduction of the full system.
  See [ML21, §§2, 6–8](https://arxiv.org/abs/2105.14976v1).
- Laskar–Gastineau's 2,501 integrations over 5 Gyr found a small fraction, of order one
  percent, with large Mercury eccentricity excursions. This is not the same statistic
  as a one-percent collision probability. Their ensemble and its completed-run statistics
  are described in [LG09](https://doi.org/10.1038/nature08096) and
  [ML21, Appendix C](https://arxiv.org/abs/2105.14976v1).
  The g₁−g₅ secular resonance is an important destabilizing mechanism; relativistic
  perihelion precession materially affects the dynamics.
- Mogavero–Hoang–Laskar identify approximate symmetries and slowly varying quantities
  associated with the dominant resonances. Their numerical Lyapunov spectrum and
  resonance analysis help explain why fast local chaos can accompany slow transport.
  They do not constitute a uniform, rigorous bound on escape for an initial region.
  See [MHL23](https://arxiv.org/abs/2305.01683v1).
- Truncation is consequential. In the tested forced secular models, degree-four
  truncation almost suppresses the 5-Gyr instability, while degree-six terms restore
  much of it. Similar Lyapunov times do not imply similar rare-event statistics.
  See [HML22, §§3–4](https://arxiv.org/abs/2205.04170v1).

Consequently, “nothing happens for billions of years” should mean that most trajectories
in specified numerical ensembles remain macroscopically confined for that time, with rare
large excursions. It is not an established all-data theorem for the actual inner system.
A numerical ensemble frequency is also not automatically a Lebesgue measure statement
for a box of initial conditions.

A theorem allowing a small exceptional set is a natural ambition:

$$
 \nu(Q\setminus G)\le \delta\,\nu(Q),\qquad
 \forall z_0\in G,\ \forall |t|\le T:\ z(t)\in D.
$$

The measure ν, normalization, and initial set must be stated. Uncertified points in
Q\G are unresolved, not proved unstable. A deterministic escape bound does not prove
Brownian diffusion, a diffusion coefficient, or a first-passage distribution. Those would
need additional mathematical arguments about correlations or a justified stochastic model.

### Which rigorous theories address the question?

For H=h(I)+εf(θ,I), with an analytic norm bound on f and appropriate nondegeneracy of h,
Nekhoroshev theory supplies small action drift for exponentially long finite times.
It controls all initial data in an interior region, including resonant data. It does not
require those trajectories to lie on KAM tori.

Near an exact Diophantine torus, the small parameter can instead be distance r from the
torus. Finite normal forms then give exponentially small remainders. With additional
stable steepness one obtains double exponential stability for all sufficiently nearby
data; without that condition, a double exponential conclusion is available for almost
all nearby data in a quantitative sense. Programs B and C distinguish these statements.

These general results are rigorous mathematics. The missing step for a realistic planetary
claim is to verify their hypotheses, domains, constants, and coordinate transfers at
specific parameters and a useful initial region. This review found no such certified
5-Gyr theorem for the full observed inner Solar System. That is a scoped literature
finding, not a universal priority claim.

Proving that the same certified region contains genuinely chaotic dynamics would be an
additional result. The recommended stability theorem allows chaos; it does not itself
certify a positive Lyapunov exponent for the observed trajectory.

## 2. What the repository already supplies

The [manifest](../../manifest/frozen-anchors.json) at the stated commit records 134 sealed
definitions, 23 sealed theorems, and one draft theorem, W-NLW2. This is a manifest/source
inspection, not a fresh build or axiom audit. In particular, the following work should
not be proposed as if it were missing.

| Existing result or component | What it supplies | What remains for this proposal |
|---|---|---|
| [N-HEAD-C](../../KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexNekhoroshevComplexBound.lean) | Uniform quasi-convex drift and solution existence, n≥3, with exponent 1/(2n) | Concrete verification and evaluation; general steepness |
| [Explicit N constants](../../KAM/Nekhoroshev/Interfaces/Constants.lean) and [assembly](../../KAM/Nekhoroshev/Assembly/Headline.lean) | Literal definitions of C, c, T, ε₀ and a theorem using them | An executable outward enclosure and finite witnesses for analytic hypotheses |
| Partial convexity and averaging in N | Stopped fast-action control; mean and most-data estimates on the averaging timescale | Quantitative data for applications; no automatic iteration to Gyr times |
| [Planetary exponential safety](../../KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean) | Full planar moving-Sun Newtonian safety for all data in a fixed low-AMD region and sufficiently small mass parameter | A useful numerical mass threshold and time |
| [Planetary AMD confinement](../../KAM/Frozen/Planetary/Theorems/AmdConfinement.lean) | Transfer from a stopped action estimate to physical safety | Discharge that stopped estimate from the actual Hamiltonian |
| [Secular safety](../../KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean) and [cited masses](../../KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean) | All-time bounds for the exact first-order secular SJS model | Transfer to a different truncation or the full flow |
| K, I, R and [v2](../../KAM/CertificateSharp/V2/Engine.lean) | KAM existence, isoenergetic barriers, weaker nondegeneracy, checked finite data | A canonical neighborhood, transverse normal form, finite-region dynamics |
| [Canonical library](../../KAM/Canonical), [N normal forms](../../KAM/Nekhoroshev), [P charts](../../KAM/Planetary) | Exact flows, analytic estimates, averaging, physical reconstruction | Certificate-facing quantitative interfaces and numerical instances |

Several details change the plan.

**The quasi-convex constants are already explicit.** For example, the source defines
a Fourier conversion factor F=2π coth(πs/4)ⁿ, a threshold ε*, and

$$
 C=(r_0/A)(F/\varepsilon_*)^{1/(2n)},\qquad
 c=\frac{\pi s}{6\sqrt n}(\varepsilon_*/F)^{1/(2n)}.
$$

The public frozen theorem existentially packages constants, but the internal
HeadParams/head interface retains the formulas. The new work is certification and
useful estimates, not merely changing an existential theorem to a formula.
The actual N-HEAD-C requires both a complex Hessian bound and a positive frequency
lower bound. Older planning remarks without these hypotheses are not its statement.

**The planetary exponent differs.** The frozen full-model theorem uses

$$
 a_P=\frac{2}{6n^2-3n+14},\qquad b_P=\frac32a_P,
$$

with horizon exp(cμ⁻ᵃᴾ). The proposed 1/(2n) partial-planetary shortcut in an earlier
exploration was not established; the
[round-three refutation](almost-every-round3-refutation.md) supersedes it.
The partial convex theorem is stopped: its slow-domain assumption is required only up
to the queried time. That form is essential to the AMD first-exit argument.

The averaging result gives a mean running-maximum error of order √ε on its fixed
O(1/ε) horizon. If the initial region has volume V, Markov's inequality gives relative
bad volume at most A√ε/(ηV) at tolerance η. The normalization by V and the time
restriction cannot be omitted.

**The secular SJS result is already numerical and all-time.** It includes the exact
model literals μ=4773/5000000 and Saturn/Jupiter mass ratio 476/1591, eccentricity below
0.15, radial bounds 1751/400 and 4439/400, and a radial separation bound 399/200.
These constants belong to that model and its declared box; they are not an ephemeris
uncertainty enclosure. A second theorem saying only that this same secular box lasts
5 Gyr would add little.

**v2 is available; hybrid is a design.** Routes A and B are wired in
[RouteAll](../../KAM/CertificateSharp/V2/RouteAll.lean). The finite 1,176-case comparison
reported in the decisions is not universal dominance over all certificates.
The hybrid [restart design](../campaign/design/APOST-SHARP-V2-HYBRID.md) would check a
supplied correction and then apply a landed theorem. Its attractive floating estimates
are not a kernel-checked hybrid certificate. Ordinary twist and bordered isoenergetic
torsion must remain distinct. An infinite Diophantine claim still needs its own proof.

The current scale is substantial: 360,270 physical lines under KAM, including 34,055
under Nekhoroshev and 147,976 under Planetary. These counts include comments and
facades; they are a scale reference, not a measure of mathematical difficulty.
New estimates below are incremental handwritten Lean lines, with roughly factor-two
uncertainty. Generated certificate data and proof terms are separate costs.

## 3. Four programs

### A. General quantitative Nekhoroshev theory with a certificate interface

**Target A1: expose the existing quasi-convex theorem computationally.**
Fix n≥3 and rational enclosures for R,s,M,m,Mℂ,ωmin with positive margins.
A finite certificate for an expression H=h+f, with perturbation norm at most ε,
proves exactly the existing analytic,
complex-Hessian, derivative, frequency, and quasi-convexity hypotheses on their declared
domains. Its arithmetic output supplies rational bounds Ĉ, ĉ, T̂, ε̂₀ with

$$
 C\le\widehat C,\quad 0<\widehat c\le c,\quad
 0<\widehat T\le T,\quad 0<\widehat\varepsilon_0\le\varepsilon_0.
$$

For 0<ε≤ε̂₀ and the initial actions of the existing theorem, every solution exists on
the resulting interval and satisfies

$$
 \|I(t)-I(0)\|\le \widehat C\,\varepsilon^{1/(2n)},\qquad
 |t|\le \widehat T\exp(\widehat c\,\varepsilon^{-1/(2n)}).
$$

Initial-domain and endpoint inequalities must follow the existing theorem exactly.
One should also accept a rational requested time and check its logarithmic comparison,
rather than construct an enormous numerical exponential.

This is a sound checker for supported finite expressions and sufficient witnesses, not
a decision procedure for all analytic functions. For example, definite-Hessian or
bordered quadratic-form witnesses can discharge useful subclasses. Checking a finite
grid of Hessians without a variation bound cannot establish quasi-convexity.

**Target A2: the genuinely more general steep theorem.**
For n≥3 and a real analytic h on a uniform complex neighborhood of U, impose a positive
lower frequency bound and quantitative steepness: for every I∈U and every j-plane Λ,
1≤j≤n−1, orthogonal
to ∇h(I), require, in the source Euclidean norm,

$$
 \max_{0\le u\le\xi}
 \min_{\substack{v\in\Lambda\\ \|v\|_2=u}}
 \|\pi_\Lambda\nabla h(I+v)\|_2
 \ \ge C_j\xi^{\alpha_j}\qquad(0<\xi\le r).
$$

The complex neighborhood must contain the points used here. Fix the indices
α₁,…,αₙ₋₁≥1, positive steepness constants,
analytic widths and norm bounds before choosing f and ε. For H=h+εf with ‖f‖≤1,
seek explicit positive ε₀,R₀,T₀,c such that, for every 0<ε<ε₀ and every initial angle,

$$
 a=(2n\alpha_1\cdots\alpha_{n-2})^{-1},\qquad b=a/\alpha_{n-1},
$$
$$
 I(0)\in U^{-2R_0\varepsilon^b}
 \ \Longrightarrow\quad
 \|I(t)-I(0)\|\le R_0\varepsilon^b,\quad
 |t|\le T_0\varepsilon^{-1/2}\exp(c\varepsilon^{-a}).
$$

Here U⁻ᵈ denotes the interior erosion by d. Include existence and uniqueness and a
separate ε=0 case. This follows the scope and exponents of
[Guzzo–Chierchia–Benettin, Theorem 1](https://arxiv.org/abs/1403.6776v1);
period-one and max-norm conversions need explicit factors.

**Why it matters.** A2 extends the class of integrable Hamiltonians beyond quasi-convexity;
A1 makes an already deep result usable by computational dynamicists. This would be a
formalization and certification contribution to established mathematics. It would not
prove that the unreduced planetary Kepler Hamiltonian is steep: its independence of
the slow variables is a real degeneracy.

**Reuse and obstacles.** N supplies analytic normal forms, resonance lattices, geometry,
continuation and most of the quantitative language. The hard new part of A2 is steep
resonance geometry, including possible folds of the frequency map. Certifying steepness
of a specific polynomial over every relevant subspace is a separate difficult task;
sampling subspaces is insufficient. A strong sufficient algebraic criterion is a better
first computational interface than a purported general steepness algorithm.

**Size and resources.** A1: about 4–10k lines. A2: another 30–70k, with low confidence.
Budget 10–80 CPU-hours for a focused rebuild of the eventual small interfaces and test
suite, and 1–10 CPU-hours for a modest A1 instance; these are engineering allocations,
not measurements or bounds on the whole theorem campaign. Target below 8 GB RSS per
process. Abstract proof development is plausible on this machine through small modules.
Numerical usefulness of the raw global constants is uncertain even after all checks pass.

**First milestone.** A concrete three-degree-of-freedom quasi-convex polynomial/trigonometric
Hamiltonian, with a checked rational perturbation threshold, drift radius and time,
using the existing HeadParams theorem. Report how its certified time deteriorates with
region size. Begin A2 only after selecting a source statement and an application that
actually needs steepness.

### B. Effective stability around a torus or elliptic equilibrium

**Target B1: a finite normal-form certificate.**
Let Ψ be a certified canonical diffeomorphism on a neighborhood of
𝕋ⁿ×$\overline{B_R}$, and let

$$
 H\circ\Psi=N(J)+\mathcal R(\varphi,J),\qquad
 \sup_{\mathbb T^n\times B_R}\|\partial_\varphi\mathcal R\|\le\eta .
$$

All norms and the canonical convention are fixed. For 0<r<R, T≥0 and ηT<R−r,
prove that every initial point in Ψ(𝕋ⁿ×Bᵣ) has a unique solution for |t|≤T and

$$
 \|J(t)-J(0)\|\le\eta|t|,\qquad \|J(t)\|<R.
$$

If the original action projection differs from J by at most d on the chart, derive
original-action drift at most 2d+η|t|. Closure of the chart must lie in the regular
domain of the original Hamiltonian, so the first-exit argument proves continuation.
An analogous Cartesian oscillator version uses I_j=(p_j²+q_j²)/2 and bounds on
{I_j,ℛ}; it avoids singular action-angle coordinates at an elliptic equilibrium.

The difficult content is a checker that proves these premises from finite data:
generating Hamiltonians, finite polynomial/Fourier arrays, divisor bounds, analytic
tails, and chart margins. A truncated polynomial substitution is not automatically an
exact symplectic map. Use actual time-one Lie flows with bounded discarded tails, or
another exactly justified canonical construction. Include every rounding, truncation
and initial residual in ℛ.

For a fixed finite T, an approximate torus can be enough: its defect is part of the
remainder budget. An exact KAM torus is needed for the usual statements as r→0.
This lets the first finite-time application proceed without waiting for the most
expensive exact-torus certificate.

**Target B2: general near-torus theorems.**
For analytic H=ω·I+O(I²) on a uniform complex neighborhood in canonical coordinates,
and a Diophantine ω with γ>0 and τ≥n−1, first formalize an all-data bound
$\|I(t)\|\le2r$ for sufficiently small r,
$\|I(0)\|\le r$, and $|t|\le\exp(c r^{-1/(\tau+1)})$.
The finite-order and analytic-tail machinery is the reusable part.

Two stronger successors have different hypotheses and conclusions:

- If the Birkhoff polynomial of degree $\lfloor n^2/2+2\rfloor$ is quantitatively
  stably steep, obtain the same all-data confinement through
  $\exp(\exp(c r^{-1/(\tau+1)}))$ in the analytic case.
  This is the scope of [BFN16, Theorem A](https://arxiv.org/abs/1601.01783v1).
  Ordinary invertible twist alone does not establish its stable-steepness premise.
- For a fixed analytic H around an exact Diophantine torus, seek an open good set Gᵣ
  with relative excluded volume at most $\exp(-c r^{-1/(\tau+1)})$, and action
  drift at most Cr² through the same double exponential timescale.
  [Bounemoura–Farré, Theorem A](https://arxiv.org/abs/2105.01297v1) does this without
  a twist or steepness hypothesis. Its constants depend on a finite Birkhoff jet whose
  determining order is itself Hamiltonian-dependent. It is not already an executable
  uniform bound for every input Hamiltonian.

The latter theorem is an attractive answer if Zohar mainly wants a general “almost all
nearby data” theorem. It does not say that an arbitrary observed chaotic orbit belongs
to Gᵣ. Nor should its elliptic-equilibrium analogue be attributed to that theorem:
the paper discusses that extension separately.

**Why it matters.** This connects the repository's certified tori to stability of
neighborhoods, including points off the tori. It serves celestial mechanics, accelerator
dynamics and Hamiltonian numerical analysis. Finite Birkhoff certificates already have
rigorous computer-assisted precedents, notably
[Caracciolo–Locatelli](https://arxiv.org/abs/2102.05959v1); the contribution sought here
is a reusable Lean checker and new checked instances, not the invention of the method.

**Reuse and obstacles.** Reuse N/P Lie flows, analytic tails, and certificate arithmetic.
The v2 output is an embedding and bounds, not a ready-made canonical tubular chart.
Constructing that chart with controlled inverses and derivatives is substantial work.
For one finite normalization only finitely many divisors need checking; a theorem using
an exact Diophantine torus still needs the infinite arithmetic statement.
Normal-form order must be optimized at the chosen radius: increasing order indefinitely
can worsen the remainder.

The January 2026 [Guzzo–Caracciolo–Pinzari preprint](https://arxiv.org/abs/2601.18268v1)
offers a useful later refinement: exploit nonresonant remainder monomials to improve
the usual inverse-remainder time estimate. Its stated rigorous result concerns finite
nonresonance; the paper explicitly leaves a corresponding general resonant extension
open. Do not silently apply that sharpening to Program C.

**Size and resources.** Shared finite-normal-form checker: 12–25k lines; controlled
torus/elliptic adapters: another 12–25k. A complete asymptotic all-data theorem could add
15–35k; the almost-all double exponential theorem could add 20–45k instead or afterward,
with overlap to be measured. For a small 2–3 degree-of-freedom instance, reserve
10–100 kernel CPU-hours, subject to a first-shard measurement. Keep each arithmetic
shard below 8 GB. High-dimensional, high-order data can dominate these proof costs by
orders of magnitude; no planetary runtime is established by these allocations.

**First milestone.** Check one complete finite Lie normalization, including its analytic
tail and physical-coordinate displacement, on a small polynomial Hamiltonian, and obtain
a strict improvement over the direct vector-field confinement time. A published
Caracciolo–Locatelli example is a suitable source-controlled pilot. The three-mode FPU
example in the 2026 paper is another possible action-drift benchmark; its positive
quadratic energy already gives local Lyapunov stability, so it would not itself be the
“chaotic planetary stability” flagship.

### C. Certified confinement from resonant approximate integrals

**Target C1: a general barrier theorem from small derivatives.**
This is the most direct mathematical translation of the approximate symmetries in MHL23.
It also makes the library useful beyond perturbations of globally integrable Hamiltonians.

Let X be a locally Lipschitz vector field on an open Ω, let D be a bounded open region
with compact closure contained in Ω, and let Q⊂D be the initial set. Supply C¹ functions
F₁,…,Fₘ on Ω, initial ranges [aⱼ,bⱼ], derivative bounds ηⱼ≥0 and T>0 such that

$$
 F_j(Q)\subset[a_j,b_j],\qquad
 |dF_j(X)(x)|\le\eta_j\quad(x\in\overline D),
$$
$$
 \forall y\in\partial D,\quad
 \exists j:\ \operatorname{dist}(F_j(y),[a_j,b_j])>\eta_jT.
$$

Then every solution starting in Q exists on [−T,T], stays in D, and satisfies
$|F_j(z(t))-F_j(z_0)|\le\eta_j|t|$.
The same compactness argument works on a periodic cylinder; compactness is taken
modulo its angle lattice.

This is a concrete, reusable theorem. The boundary separation is a static inequality,
not an assumption that trajectories stay in D. The practical checker must verify it
on all boundary faces, with subdivisions if necessary.

**Target C2: obtain those quantities from a resonant normal form.**
Given an exact canonical transformation and

$$
 H\circ\Psi=Z_{\mathrm{res}}+\mathcal R,\qquad
 \{F_j,Z_{\mathrm{res}}\}=0,
$$

check the polynomial identities, derivative bounds on $\{F_j,\mathcal R\}$, and
boundary inequalities. Retain the strong resonances in Zres. Never divide by their
small divisors or discard them because a nonresonant checker is easier.
The retained dynamics may be complicated; its integrals can nevertheless restrict
motion transverse to the resonances.

For a prescribed quasiperiodic forcing, work on physical variables and the compact
forcing torus, using $X\cdot\nabla_xF+\omega_{\rm ext}\cdot\partial_\phi F$.
Physical energy or AMD is not automatically conserved in that forced subsystem.
Adding dummy conjugate actions does not make an invalid physical conservation law valid.

**Target C3: a finite, measurable good region.**
Partition a specified rational initial box Q into cells. Accept a finite family of
cells for which C1/C2 closes, and certify that their union has measure at least
(1−δ)ν(Q). Account for overlaps, boundary measure and coordinate Jacobians.
For a density other than canonical volume, certify its bounds or its integrals.
This yields a meaningful finite-time measure statement without claiming ergodicity
or a stochastic law. The existing N mean estimate alone gives neither repeated
independent blocks nor an unlimited extension of its O(1/ε) horizon.

**Why it matters.** This could make approximate conservation laws extracted by numerical
research into rigorous transport constraints. It is more flexible than requiring a
whole domain to satisfy steepness, and it reaches resonant dynamics directly. The
elementary derivative/first-exit theorem is not the novelty; the hard contribution is
a sound normal-form and boundary certificate that closes on an interesting model.

**Reuse and obstacles.** Reuse the B finite-expression and tail machinery, P's AMD
first-exit structure, and K's measure/change-of-variable tools. The central difficulty
is quantitative: a small derivative in a plot can be much too large after multiplication
by 5 Gyr, and a few approximate integrals may fail to separate every escape boundary.
For example, with dimensionless margin d=10⁻³ and T=5×10⁹ yr, reserving half the margin
requires η≤10⁻¹³ yr⁻¹. This arithmetic illustration is not an estimate for any planet.

C1 is useful even if no normal form is available, because one can directly certify
dF(X). For the inner planets, however, evaluating a high-degree forced secular model
and controlling the discarded interactions is substantial. The mathematical certificate
could fail for a physically important region; that is a result to report, not a reason
to shrink or simplify the model silently.

**Size and resources.** On top of B's shared core, estimate 5–12k lines for C1/C3 and
8–20k for a useful resonant/forced adapter and boundary checker. A low-dimensional
example might cost 10–200 kernel CPU-hours. A complete inner-planet model and a finely
resolved good-set cover have no credible runtime estimate yet. The current machine
can support small independent cells under 8 GB each, executed serially; a large
cell count can still make total time prohibitive. More memory alone does not solve
that combinatorial problem.

**First milestone.** In an explicitly specified polynomial resonant Hamiltonian,
certify one nontrivial approximate integral, every exit face, and a time improvement
over direct action estimates. Then pin one selected inner-planet resonance model and
reproduce its proposed approximate integrals algebraically. Do not start with the
claim that 99% of a full observational region survives 5 Gyr.

### D. A numerical planetary lifetime, with explicit model boundaries

There are two distinct outputs here: a general explicit planetary interface and a
specific lifetime. A secular lifetime is not automatically a full-model lifetime.

**Target D1: quantitative partial-convexity plus AMD for the full planar model.**
For the already defined moving-Sun Hamiltonian, construct a numerical certificate that
verifies its complex domain, separation margins, perturbation norm and the constants
needed by the stopped theorem at a given positive mass μ. It must produce Δ and T
such that the fast-action bound follows from the Hamiltonian, and satisfy the existing
AMD and inner/outer-box margin inequalities. Then apply the already proved physical
transfer to conclude unique Newtonian motion, eccentricity bounds and collision
exclusion through T.

A reusable output would compute an interval lower bound on T and an upper bound on
drift for every supported admissible AMDBox. The final theorem assumes accepted finite
data and source hypotheses; it does not assume StoppedActionBound as an unexplained
premise. That conditional helper already exists.

**Target D2: the first substantial lifetime instance.**
The source-backed candidate is the secular Sun–Jupiter–Saturn–Uranus model of GLS17.
There is an important qualification: a planar three-planet secular Hamiltonian has
three degrees of freedom before rotational reduction and two after fixing AMD and
quotienting the common perihelion angle. This reduction is described explicitly in
[Migaszewski–Goździewski, §3](https://arxiv.org/abs/0803.3246v1).
For the selected truncation, verify the symmetry as an exact polynomial identity.
Thus SJSU is a serious lifetime/checker application, but its raw dimension does not
prove that reduced KAM barriers are unavailable.

If the first flagship must require at least three effective degrees of freedom,
use a symmetry-reduced planar four-giant secular model including Neptune, or the
already reduced full planar SJS model. The former has three secular degrees of freedom
after the same one-angle reduction, but lacks the equally mature source calculation
used here. It needs a new feasibility scout; the SJSU timing estimates do not transfer.

The precise proposed theorem schema is: for a fixed, versioned secular Hamiltonian
Hsec and a fixed compact positive-volume region Q*, with a certified canonical chart
Ψ into Hsec coordinates,

$$
 \forall z_0\in Q_*,\quad \exists!\,z,\quad
 \dot z=X_{H_{\rm sec}}(z),\ z(0)=z_0,\quad
 z(t)\in D_*\quad(|t|\le 5\,000\,000\,000\ {\rm yr}),
$$

together with explicit bounds on secular action drift and eccentricities. Where
non-crossing ellipses are claimed, prove radial separation for all reconstructed
fast phases. For a secular model those are geometric reconstructions, not a proof
that the corresponding full Newtonian trajectories follow them.

This schema is exact in Hsec,Q*,D*; the coefficient table, canonical chart, radii and
eccentricity thresholds are **not selected or frozen by this note**. Inventing them
would conceal the main feasibility issue. The first model milestone must publish them
as rational literals or rigorously enclosed physical coefficients, fix the time unit,
and set a minimum acceptable region before optimizing certificates. A nonempty
arbitrarily tiny box is a technical success, but not enough for the flagship.

[GLS17](https://arxiv.org/abs/1702.04894v1) is an attractive starting point, not a
certificate to replay blindly. Its secular SJSU calculation estimates roughly 10¹⁰ yr
at a normalized radius slightly below 10⁻⁷. Its comparison with observational
uncertainty is approximate and larger, about 7×10⁻⁷. Its normal-form and tail computation
is not a rigorous proof. The reported intermediate expansion has 94,109,751 monomials.
The actual analytic model, every truncation, and the preimage of Q* must therefore
be independently specified and bounded.

A practical first acceptance target is the source-scale radius near 10⁻⁷, with an
explicit chart and a useful eccentricity tolerance, followed by the full curve T(r).
That numerical radius is only a scout target until its coordinate normalization has
been pinned. We should ask whether it is scientifically worthwhile before committing
to a large formalization.

**Target D3: transfer upward in model fidelity.**
For planar full SJS, one possible route is a local finite normal form around the FH25
candidate, followed by B or C and the existing planetary reconstruction. Alternatively,
D1 might close on a low-AMD box without any torus certificate.
For either route, use the full Hamiltonian in the remainder estimate. A secular result
plus a formal O(μ²) error, with no uniform constants and domain, is not a 5-Gyr transfer.

The later inner-planet target should fix either the full Newtonian/relativistic force
model or a specified forced secular Hamiltonian, include the interactions responsible
for rare excursions, and ask for a chosen good-set fraction and time. Degree-four
stability would not answer the degree-six transport question. A reduced resonance model
can be a valuable theorem, provided its scope is stated.

**Why it matters.** A machine-checked 5-Gyr statement for an explicit nontrivial secular
region would be a substantial demonstration for celestial mechanicians and formal
verification researchers. A full SJS result at specified masses would be a further
step. A statement about the observed inner planets additionally requires a rigorous
initial uncertainty set and force-model correspondence. Neither rational mass literals
nor a plot near a nominal ephemeris provides that correspondence.

**Reuse and obstacles.** P already proves the hard qualitative geometry and physical
transfer. Its [stopped assembly](../../KAM/Planetary/Exponential/Stopped.lean) obtains
some analytic tubes and uniform bounds through compactness; those witnesses still need
effective bounds for D1. The difficult numerical stages include Laplace/Kepler
coefficients, canonical transformations, tiny secular divisors, and rigorous remainder
control across the full requested region.

**Size and resources.** D1 may require 10–25k additional lines for quantitative
planetary bounds. D2 may need another 10–25k model/coordinate lines beyond B/C and
large certificate data; an inner-planet forced model could add 20–50k before useful
bounds exist. These overlap rather than add mechanically.

A small secular certificate merits a provisional 100–1,000 kernel CPU-hour allocation
only after a measured sample supports it. There is no measured budget yet for the full
GLS17 expansion. Full SJS is more expensive: the existing
[SJS feasibility report](sjs-feasibility.md) estimates 10,000–33,000 CPU-hours for one
earlier route and several million retained coefficients. Its much cheaper GMP/hybrid
figures assume unimplemented arithmetic or unverified extrapolation. Some proposed
single products need 28–56 GB, and FH25's numerical torus generation used about 194 GB.
Those computations do not fit the present 10-GB/process and 32-GB/user limits.

**First milestone.** Pin Hsec,Q*,D* and a physical time conversion; reproduce a small
rigorous remainder calculation and one kernel arithmetic shard. Publish the resulting
T(r) estimate before promising 5 Gyr. If that estimate fails, change the agreed target
openly or report the obstruction. Keep full SJS and the full inner system behind
separate mathematical and resource decisions.

## 4. Recommended order and fit with the active work

**Pursue B1+C as the main new program, with D2 as its intended application.**
Extract the inexpensive A1 interface along the way. Treat the almost-all near-torus
theorem as the strongest alternative general-theory project if that is Zohar's priority.
Do not start the entire general steep theorem merely because its name matches the
motivation: it is a major project and does not by itself resolve proper degeneracy or
actual planetary masses.

The work can proceed through the following concrete gates.

| Order | Deliverable | Decision it enables |
|---|---|---|
| 1 | Finish the current lunar certificate and validate one small v2 arithmetic workload under the current cap | Reliable numerical primitives and actual kernel costs |
| 2 | A1 numerical interface; B1 finite normal-form/continuation theorem; one full small example | A reusable effective-stability checker |
| 3 | C resonant invariants and boundary certificates; choose and pin the secular planetary target | Evidence that resonant transport bounds can close |
| 4 | One planetary T(r) curve with verified tails and chart displacement | Whether a 5-Gyr, scientifically useful region is attainable |
| 5 | Final D2 certificate and physical observables within its stated model | A substantial lifetime theorem |
| 6 | Full SJS transfer or a selected inner-planet resonance/measure problem | Increased physical fidelity, with a new feasibility assessment |

These are mathematical dependencies, not a request to launch concurrent agents or builds.

**SO lunar work.** Preserve the latest decisions: the tightened rotational target is
around 2.714% with N=65, and the libration route uses an exact symplectic polar chart
around the periodic orbit. Do not insert a new Birkhoff-normalization prerequisite
into that task. Its certificate arithmetic and chart work are valuable calibration for
the new program, but lunar spin–orbit stability does not answer planetary orbital chaos.

**v2 and hybrid.** Use the landed route that closes most cheaply on the actual data.
First measure a small representative check under 8 GB. A hybrid correction may reduce
Fourier support and supplies useful validated-Taylor infrastructure, but it is not a
prerequisite for the finite normal-form theorem. Splitting source modules does not fix
a single oversized arithmetic reduction. The reported 19.2-GB RefinedRefR1 core is
outside this machine's limit and should not be rerun here.

**LG00.** Retain it as a compact planetary validation case: 69 rational monomials,
two secular degrees of freedom, and an established a-posteriori/isoenergetic route.
The scout's Route-A supports of roughly 545–680 coefficients and 3–75 CPU-hours per
torus are projections, not a completed interval replay. The sqrt primitive and v2
wiring are now present; earlier notes listing them as missing are stale.
Two suitably placed tori on the same energy surface can give confinement, whereas
one certified torus alone cannot trap every neighboring initial condition.
This makes LG00 a good checker pilot, but a weak headline for the new chaos question.

**Full SJS.** Keep the [FH25 route](https://arxiv.org/abs/2403.10152v1) as a later
high-fidelity application. Its numerical approximation is valuable input, not a
finished rigorous certificate. There is no reason to make the entire new stability
library wait for its multi-million-mode calculation. Conversely, a successful 2D lunar
hybrid run does not validate a 3D planetary runtime extrapolation.

**The two demonstrations.** The
[latest proposal](next-demonstrations.md) selects a magnetic field-line barrier and
Mercury 3:2 spin confinement. They have distinct value as accessible uses of the
certifier. The magnetic result concerns an explicitly chosen field-line Hamiltonian;
the Mercury result concerns rotation with a prescribed orbit. Neither is a proof of
Mercury's orbital safety. Their projected 40–180 and 16–80 kernel CPU-hours,
respectively, are still planning estimates. Finish or advance them on their own merits;
they are neither substitutes for D2 nor mathematical prerequisites for it.

**W and other scope.** The nonlinear wave theorem is already an active frozen draft.
PDE KAM and leapfrogging need different analytic infrastructure. They should not be
relabelled as the answer to the planetary transport problem.

### Computation must be designed around the actual limits

All new timings above are speculative allocations until measured; none was benchmarked
in this research task. The prior scouts themselves report calibration uncertainty
reaching about 20×. More accurate constants can save far more work than a faster
evaluator, so numerical scouting should precede expensive proof-term generation.

Use outward dyadic balls, bounded blocks of sparse polynomial/Fourier operations, and
ordinary kernel-checked soundness lemmas. Keep untrusted numerical generation separate
from checked identities and inequalities. Use exact Lie-flow and analytic-tail theorems
to avoid materializing every formal coefficient. Before scaling a data set, measure
coefficient count, bit width, kernel time, peak RSS and proof artifact size for one
representative block, including loading and reduction of its dependencies.

The working target is <8 GB RSS per Lean process, leaving headroom below the 10-GB kill
threshold; Python should also remain below about 8 GB. Observe the 32-GB user cap and
the single targeted build rule. A larger machine helps only when the execution policy
also permits larger processes, or when expensive generation is moved to an explicitly
authorized resource. Extra RAM does not repair a mathematical tail estimate.

A practical proposal should require all of the following before advertising a planetary
lifetime: a named model and source, a fixed initial region and observables, a measured
small certificate, certified coordinate/domain margins, a complete remainder budget,
and physical time conversion. These are parts of the theorem and its feasibility,
not an additional approval procedure.

## 5. Quick choices for Zohar and Scott

1. **Which main result matters most?** A general effective-stability checker with a
   planetary example (recommended); the almost-all double exponential near-torus
   theorem; or a full general steep Nekhoroshev formalization?
2. **What should “planetary” mean for the first flagship?** An explicitly stated
   secular SJSU model (recommended first instance); at least three degrees of freedom
   after exact reductions, such as full planar SJS; or only the inner planets count?
3. **Which guarantee is most valuable?** All initial data in a modest fixed region;
   at least 99% of a larger specified region; or a shorter certified time for the
   full observational uncertainty set?
4. **Is 5 Gyr the right first target, and what minimum region is scientifically
   worthwhile?** For the SJSU scout, is a source-scale radius near 10⁻⁷ acceptable
   once its physical meaning is quantified, or must the full uncertainty set fit?
5. **How much computation should a final certificate justify?** About 100 CPU-hours;
   about 1,000; or a separately resourced larger campaign? The current 10-GB/process
   limit remains a hard constraint in every case.
6. **Does Zohar want a proof of chaotic dynamics as well as confinement?** The proposed
   theorem controls transport while allowing chaos. A rigorous chaos statement for a
   chosen orbit or invariant set is an additional target.

## 6. Evidence, uncertainties, and handoff

The review read the repository rules, PLAN, DECISIONS, TRACKS, README, frozen manifest
and relevant frozen statements, the N/P implementations, v2 theorem/checker interfaces,
and hybrid design. All twelve pre-existing exploration files were considered:

| Exploration | Consequence for this proposal |
|---|---|
| [planetary-and-nekhoroshev](planetary-and-nekhoroshev.md) | Proper degeneracy and quantifier order remain central |
| [almost-every-shorter-times](almost-every-shorter-times.md) | Distinguish parameter prevalence, initial-data measure and numerical ensembles |
| [almost-every-round2](almost-every-round2.md) | Useful AMD strategy; proposed stronger exponent not inherited |
| [almost-every-round3-refutation](almost-every-round3-refutation.md) | Preserve stopped hypotheses and the source planetary exponent |
| [realistic-kam-and-finite-size](realistic-kam-and-finite-size.md) | A torus and a physical initial region are different deliverables |
| [lunar-spin-orbit-certificate-proposal](lunar-spin-orbit-certificate-proposal.md) | Reuse certificate architecture and exact model discipline |
| [lunar-band-2p8-2p9](lunar-band-2p8-2p9.md) | Read together with later N=65 decisions |
| [pde-kam-and-leapfrogging](pde-kam-and-leapfrogging.md) | Preserve the separate W campaign |
| [striking-applications](striking-applications.md) | Superseded hardware/route claims are not current feasibility evidence |
| [sjs-feasibility](sjs-feasibility.md) | Full SJS is a large numerical campaign, with incompatible old memory assumptions |
| [sjs-lg00-scout](sjs-lg00-scout.md) | Small exact polynomial pilot; distinguish model, chart and certificate |
| [next-demonstrations](next-demonstrations.md) | Keep magnetic and Mercury-spin applications distinct from orbital stability |

The primary external papers are linked at the claims they support. Versioned PDFs and
text extractions were downloaded only to /tmp/ambition-astra/papers; sources.json there
records their URLs and SHA-256 hashes. The new 2026 preprint is treated as a proposed
optional improvement, not established project infrastructure. The Nature source itself
was not obtained as a local full-text PDF; the numerical count and qualification above
were checked against the authors' later ML21 treatment.

**Uncertainties.** No new theorem was frozen, no numerical torus or normal form was
generated, and no certificate was replayed. The size/cost estimates are architectural
judgments, with the strongest uncertainty in high-dimensional tails, model extraction,
steepness certification, and the size of a physically interesting good set. Nothing in
this note establishes a successful 5-Gyr numerical instance. That is the proposed work.

**Source defects and deviations.** One previously reported source defect was rechecked
on the rendered PDF: BFN16 arXiv v1, Definition 1, printed/PDF p. 3, concludes
“(θ(0), I(0)) ∈ V₂r T” for a time interval. The repeated initial time makes that
clause tautological; the intended conclusion uses (θ(t),I(t)), as the next page's
action-coordinate version confirms. This is carried from
[the earlier note](almost-every-shorter-times.md), not a new priority claim, and awaits
the orchestrator's source-ledger process. No other new suspected defect in a pinned
source was identified here. Existing ledger findings are not re-audited.

Proposed deviations are explicit: analytic rather than full Gevrey scope for B2;
existence/uniqueness and first-exit conclusions added to source estimate formulations;
period-one/max-norm conversions; finite certificate interfaces; and a staged secular
model before a full planetary theorem. These are planning choices, not modifications
to frozen claims. The only validation deviation in this task is the skipped ABI phase
required by the no-Lean/no-repository-scratch instruction.

**Files and checks.** The sole project deliverable is docs/explorations/ambition.md.
Scratch research and check receipts are under /tmp/ambition-astra. No Lean files,
frozen files, manifest, generated roots or README were changed. No GitHub operation
was performed.

Ran scripts/lint_sources.sh with a scratch python3 wrapper that adds Python's -B
(no bytecode writes) and refuses only scripts/abi_hashes.py. That subprocess would
write .lake/abi-scratch and invoke Lean, contrary to this brief. Actual output:

~~~text
check_lean_modules: PASS (1815 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI SKIPPED: AMBITION prohibits Lean execution and repository scratch writes.
lint exit: 1
~~~

All other lint phases completed without diagnostics. This is a partial lint run,
not a passing full lint. No Lake build, Lean probe or #print axioms was run.
Axioms of new results: not applicable; this change contains no Lean declaration.
Existing results' axiom status was not independently rechecked.

Document checks: all 31 local Markdown links resolve; the four program sections and
math/code delimiters pass structural checks; no trailing whitespace. The staged
whitespace check, git diff --cached --check, exits 0 with no output. Only this document
is staged for the ambition commit.

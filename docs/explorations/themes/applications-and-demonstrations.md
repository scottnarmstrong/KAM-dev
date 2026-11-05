# Applications of the certifier and the next demonstrations

[← Back to the catalogue](../README.md)

Four documents from 30 October 2026 on where else the certificate checker could be used. The applications scout ranked
13 targets. The next-demonstrations study selected two of them, a magnetic field-line barrier and Mercury's 3:2 spin
confinement, and corrected two of the scout's claims. The two plans turn these into campaigns with exact statements,
module lists and resource gates. No owner decision on the two demonstrations is recorded in
[DECISIONS.md](../../DECISIONS.md) as of 31 October; the Moon-lock target that the scout ranked first was started the
same day as part 3 of track SO (D42, D45). Sun–Jupiter–Saturn, rank 13 in the scout, has its own
[theme page](sun-jupiter-saturn.md).

| Document | Status | One line |
|---|---|---|
| [striking-applications](../striking-applications.md) | scouted; partly superseded | 13 targets ranked by digits, support and CPU-hours |
| [next-demonstrations](../next-demonstrations.md) | scouted; proposed | Magnetic barrier first, Mercury 3:2 second; corrects the scout |
| [plan-magnetic-barrier](../plan-magnetic-barrier.md) | proposed; numerical gate failed so far | One uncrossable graph at ε = 0.003; MP solves miss 10⁻²⁵ by 6 orders |
| [plan-mercury-32](../plan-mercury-32.md) | proposed; numerical evidence favourable | Spin within 0.018 of 3/2 for all time, exact Kepler forcing |

The [31 October plasma-route assessment](#plasma-physics-routes-review-31-october-2026)
below distinguishes controlled field-line models, device-derived fields and
particle dynamics. The accompanying [certifier fixes](../../campaign/design/CERTIFIER-V2-FIXES.md)
and [improvements](../../campaign/design/CERTIFIER-V2-IMPROVEMENTS.md) separate
confirmed issues from proposed extensions. They identify no fundamental defect
in SO-2 or SO-3 and do not supersede the lunar campaigns.

## Striking applications of a formally verified KAM certifier

**[striking-applications.md](../striking-applications.md)** · 30 October 2026 · feasibility study (APPS-SCOUT;
double-precision tori, projected costs) · status: **scouted**, **partly superseded**

The scout ranks 13 applications by required invariance error, digits, Fourier support and kernel CPU-hours, under the
then-current theorem, the sharp theorem ("v1") and an estimated v2. Three findings changed the expected list. Librational
tori around the synchronous orbit become primary tori in an explicit polar chart, so the Moon's permanent lock at the
true parameters needs no new KAM theorem, only a `sqrt` primitive and a chart lemma. Exact Kepler forcing becomes a
rational expression through an eccentric-anomaly chart and a time change. Cost is dominated by the number of
full-precision products rather than by digits. It judged planar Sun–Jupiter–Saturn infeasible in the kernel and found
the certifier not yet better than PlasmaLean on PlasmaLean's own example.

- **Numbers and verdicts.** Moon locked forever (8.8° libration): required error 10⁻¹⁶⁰ under the current theorem,
  10⁻³⁵ under v1; 41 digits, 3.9k modes, 13–26 CPU-h under v1; "the one to publish". Mercury 3:2: band ±0.0173,
  6–12 CPU-h per torus under v1. Moon spin band: 2.65 % at N = 80, floor 2.617 %. 12 Victoria in Celletti–Chierchia's
  truncated model: 33 digits, 1.1k modes. Exact restricted problem and Trojans: hundreds of CPU-hours per torus. Golden
  circle of the standard map at k = 0.970: needs a maps theorem (6–9 weeks). Sun–Jupiter–Saturn: about 10⁸ coefficients
  and at least 10⁷ CPU-h, "infeasible in the kernel" by about 4 orders in support and 6 in cost. PlasmaLean's proved
  tolerance 10⁻¹⁸·² against our v1 10⁻²⁵ to 10⁻³⁰ at comparable data.
- **Recommended sequence.** Mercury, the Moon band and the Saturnian moons first; then the Moon lock; then 12 Victoria;
  a maps theorem in parallel.
- **Superseded or corrected later.**
  - Sun–Jupiter–Saturn: [sjs-feasibility](../sjs-feasibility.md) (route B plus packed arithmetic, 34–351 CPU-h) and
    [sjs-plan](../sjs-plan.md) (synodic chart plus a packed layer, 15–300 CPU-h) replace the infeasibility verdict.
  - Mercury: [next-demonstrations](../next-demonstrations.md) points out that Celletti–Falcolini (1992) already
    constructed rigorous Mercury trapping tori, so "first rigorous Mercury trapping result" would be wrong. The scout had
    flagged that Celletti 1990 Part II must be read first.
  - Magnetic: the scout's uncontrolled calculation is not the controlled ε = 0.003 problem
    ([next-demonstrations](../next-demonstrations.md)).
  - PlasmaLean: the [repository README](../../../README.md) now reports a v2 example at PlasmaLean's frequency and
    strip with tolerance 3.72·10⁻¹⁷, 65 times PlasmaLean's proved tolerance, at assumed canonical data.
  - The `sqrt` primitive has since landed (D45). [ambition](../ambition.md) says the scout's "superseded hardware/route
    claims are not current feasibility evidence".
- **What it corrects.** Its polar-chart observation (§3) overtakes the remark in
  [lunar-band-2p8-2p9](../lunar-band-2p8-2p9.md) that librational barriers need a Birkhoff normal form or a new G1; D45
  chose the polar-chart route.

## The next two KAM demonstrations

**[next-demonstrations.md](../next-demonstrations.md)** · 30 October 2026 · research and numerical feasibility study
(IDEAS-NEXT); no torus certified · status: **scouted**, **proposed**

The study recommends (1) an impenetrable surface in a controlled magnetic field-line model at ε = 0.003, using the
general quadratic-control formula (8) of Chandre et al., and (2) all-time confinement of Mercury's spin near the 3:2
resonance with untruncated Kepler forcing, at Celletti–Chierchia's 1998 benchmark values e = 0.2056, ε = 0.00015. Both
use the existing canonical isoenergetic theorem and certifier in two degrees of freedom, with the bordered twist. The
magnetic case opens a new application area; Mercury gives a named result with small data. Fresh double-precision tori
reach about twelve digits, not the 25-digit strip error the certificates need; multiprecision enclosures are the next
gate.

- **Numbers.** Magnetic: 512² grid, residual 1.41·10⁻¹², flux range 0.28555–0.43001, sampled sufficient tolerance
  about 1.17·10⁻²³ (target error 10⁻²⁵), 10–16k Fourier keys, 40–180 CPU-h per torus, 1.6–3.1k Lean lines. Mercury:
  residuals 1.3–1.4·10⁻¹², spin deviation at most 0.017348, tolerances 3.80·10⁻²³ and 3.12·10⁻²³, 1.5–2.5k keys,
  8–40 CPU-h per torus (16–80 for the pair), 1.4–2.8k Lean lines. All thresholds use sampled bounds.
- **Corrections to the scout.** Celletti–Falcolini (1992) already has rigorous Mercury trapping tori; the scout's
  magnetic run was uncontrolled; Valvo–Locatelli's Theorem 2 concerns the truncated transformed Hamiltonian H⁽⁰⁾.
- **Not selected,** with reasons: Sun–Jupiter–Saturn and LG00 (assigned separately), Moon lock (active in SO), golden
  standard-map circle and accelerator maps (need a maps theorem), real-coil stellarator, FPUT, Hénon–Heiles, Trojans,
  kicked rotor, fluid particle paths, PDE tori, leapfrogging.
- **Candidate errata.** IDEA-VL-1, IDEA-VL-2 (Valvo–Locatelli), IDEA-CH-1, IDEA-CH-2 (Chandre et al.).
- **Later.** [plan-magnetic-barrier](../plan-magnetic-barrier.md) finds the magnetic numerical gate fails at the tested
  resolutions and that Mercury now has the stronger evidence; [plan-mercury-32](../plan-mercury-32.md) notes that the
  suggested 512×192 grid does not fit the radix-two FFT in use. Two links in the document point to local absolute paths
  and do not resolve on GitHub.

## Plan: a magnetic field-line barrier at ε = 0.003

**[plan-magnetic-barrier.md](../plan-magnetic-barrier.md)** · 30 October 2026 · campaign plan (DEMO-PLANS); planning
evidence, not an approved statement · status: **proposed**; first numerical gate **failed at the tested resolutions**

The plan fixes the exact model (quartic h, the general-(8) quadratic control with exact rational coefficients,
ε = 3/1000, frequency (7913 − √5)/13618 with Diophantine constant 1/10 still to be proved) and a public theorem: one
real-analytic periodic invariant graph p = P(q, φ) with 57/200 ≤ P ≤ 431/1000 whose graph field lines cannot cross, in
both time directions. One surface separates two regions; it does not bound the flux on both sides. It proposes a
separate KAM-demos repository, a module list, a multiprecision producer, a sharded kernel plan and worker packages
M0–M6. It recommends funding the multiprecision/finite-certificate gate before any full kernel run.

- **Numbers and verdicts.** Multiprecision pilots: at 512² the weighted residual stalls near 2.01·10⁻¹¹; at 1024² the
  real-grid residual reaches 8.88·10⁻²⁴ but the weighted residual stalls near 5.12·10⁻¹⁹, more than six orders short of
  10⁻²⁵ — "a failed numerical gate at the tested resolutions, not a certified barrier or a disproof of one". The
  coefficient-triangle bound at 512² even gives a negative slope bound, so the graph check needs paid SOS residuals.
  Next step: a 2048×1024 or streamed scan; fallback, a separately labelled ε = 0.0012 pilot (an owner decision).
  Budget: 40–180 CPU-h, 3–15 calendar days of kernel time, 2.0–3.1k Lean lines, 3–5 weeks with several owners.
- **Disagreement.** It reverses the ranking of [next-demonstrations](../next-demonstrations.md): "Mercury currently has
  stronger direct-certificate numerical evidence".

## Plan: Mercury's 3:2 spin-rate confinement with exact Kepler forcing

**[plan-mercury-32.md](../plan-mercury-32.md)** · 30 October 2026 · campaign plan (DEMO-PLANS); not an approved
statement · status: **proposed**; multiprecision evidence **favourable**, no certificate yet

The proposed theorem: for every initial orientation and orbital phase and every initial spin p₀ ∈ [373/250, 377/250]
(units of the orbital mean motion), the solution exists for all real time, is unique, and |p(t) − 3/2| ≤ 9/500. Two
invariant graphs, periodic on a double orbital cover, are the barriers. The exact model uses e = 257/1250 and
ε = 3/20000 (historical benchmark literals, not current measurements), the eccentric anomaly as clock, a time change on
the zero-energy level, and the exact constant √(1 − e²) through the landed `sqrt` node. It claims neither capture,
libration of the resonant angle, nor the first rigorous Mercury trapping result.

- **Numbers.** Finite multiprecision candidates with about 1.58k union keys per sign reach weighted residuals
  4.73·10⁻²⁷ and 4.38·10⁻²⁷, about a factor 4 below the 2·10⁻²⁶ allocation; "not a passing certificate". Sampled
  tolerances 3.80·10⁻²³ and 3.12·10⁻²³. Budget: 8–40 CPU-h per torus, 16–80 for both, 1–7 calendar days; 2.2–3.7k Lean
  lines plus 0.8–1.3k shared with the magnetic plan; 2–4 weeks. The 0.018 band is 1.2 % of the resonant spin 1.5.
- **Gaps found.** The Python certificate producer has no `sqrt` branch yet (see the LOCK-SQRT receipt); the
  `spin_kepler` function in `scripts/apps_scout/models.py` uses a floating-point square root, so its output is a
  numerical diagnostic, not an exact certificate expression.
- **Corrects** [next-demonstrations](../next-demonstrations.md) on the 512×192 grid (radix-two FFT).

## Plasma physics routes: review, 31 October 2026

Assessment at `bbf13193ed4dd15dfe141e2f7cd9902b48b818ea`; recommendations,
not an adopted campaign or a new plasma certificate. This extends the four
application studies above. The existing magnetic plan remains the source of
its exact model, candidate statement and measured numerical gate.

The certifier has a plausible plasma application path, but "a plasma torus"
can describe different mathematical objects and physical conclusions. Choose
the dynamics and observable before choosing the theorem extension.

| Route | Object to certify | Fit to present certifier | Additional work |
|---|---|---|---|
| Controlled field-line Hamiltonian | A two-dimensional invariant surface that separates field-line trajectories | Closest fit: canonical autonomous extension of a periodically forced system | Complete the finite certificate, graph transfer and non-crossing theorem |
| Field from actual coils or an equilibrium representation | A surface for the explicitly represented magnetic field | Requires a certified reduction/chart, or an appropriate geometric theorem | Field representation, derivative/remainder bounds, chart domain and physical-coordinate transfer |
| Guiding-centre or full particle dynamics | Phase-space invariant tori and specified particle observables | A different application; canonical reduction or a noncanonical extension may be needed | Symplectic/reduction data, additional frequencies where appropriate, and a separate confinement argument |

### Controlled field-line models: the first integration case

Use the [exact quadratic-control model](../plan-magnetic-barrier.md), whose
autonomous Hamiltonian has the form `J + h(p) + V(q,phi)`. It fits the present
expression language and isoenergetic engine. Its two-frequency clock structure
also fits the specialized sharp small-divisor sites.

The proposed output is a separating graph `p=P(q,phi)` and a theorem that its
field lines cannot cross it. One such surface supplies separation, not
two-sided flux confinement by itself. A torus-existence result needs the
graph, embedding and dynamical transfer arguments before it becomes that
physical barrier statement.

The existing plan's 1024² pilot reaches a weighted residual around
`5.12e-19`, against its proposed `1e-25` allocation. This is a failed numerical
gate at the tested settings, not a disproof of the barrier. Investigate the
support, strip and enclosure budgets before committing another large kernel
run. Compare the existing A variants and hybrid at checked data; do not assume
that either a sharper formula or extra resolution automatically closes the gap.

A smaller-perturbation pilot would be a separately labelled model/target.
Retain the existing owner decision process for changing the planned physical
statement. Mercury's stronger numerical readiness does not make this plasma
route uninteresting; it changes the sensible order of costly application runs.

Valvo–Locatelli provide a relevant computer-assisted magnetic-barrier precedent
and public numerical code. Compare exact Hamiltonians and truncation conventions
before comparing thresholds or making novelty claims; the existing plan records
specific source/model distinctions. [Primary paper](https://arxiv.org/abs/2101.07785)

### Device-derived fields: certify the model as well as the torus

For a coil or equilibrium application, identify the exact mathematical field
being certified. A sampled grid and a visually smooth interpolant are not an
analytic enclosure of the physical model. The application package should carry:

- A finite analytic field or vector-potential representation, with certified
  derivatives and explicit remainder bounds on the relevant complex domain.
- The divergence/symplectic structure needed by the chosen formulation. A
  vector potential with `B=curl A` is one possible representation, not a
  requirement for every route.
- A valid coordinate chart and all denominator/branch bounds. If toroidal
  angle is used as time, certify that the corresponding field component stays
  away from zero on the stated domain and account for the time change.
- Transfer of the invariant surface and its separation property back to the
  original spatial coordinates, including any claimed distance to a boundary.
- A precise scope for uncertain coil parameters or equilibrium coefficients:
  one exact model, or an explicitly quantified family with uniform checks.

Start with one modest analytic device-field model and one chart. Use that
example to decide whether certified canonical reduction or a noncanonical
theorem is the better investment. The present review did not establish which
approach is cheaper for a particular device.

### Particle dynamics: a separate certificate and conclusion

A magnetic field-line barrier is not automatically a charged-particle
confinement theorem. Guiding-centre drift and full-orbit motion live in phase
space and have different equations. Fix the approximation, conserved
quantities, symplectic structure and requested observable for the chosen model.

The practical gaps include sharp certification for more than two frequencies
and either usable canonical charts or a suitable noncanonical extension.
The current enhanced-site checker requires `n=2`, `tau=1`, and an exact clock;
the classical fallback is more general. Thus this is a sharpness/reuse gap,
not a claim that the current engine is unsound outside lunar applications.

For higher-dimensional phase space, an invariant torus usually does not
separate an energy surface into confined regions. To conclude something about
a set of nearby particles, add the required family, geometry or finite-time
stability estimate. Collisions, dissipation and time-dependent model errors
must enter the stated dynamics or a separate controlled approximation.

Keep candidate generation open to external numerical methods. Ruth, Kulik and
Burby describe reconstruction of higher-dimensional tori from trajectories;
this is a candidate-generation option to investigate, not an interval or Lean
certificate. Its output would still need refinement, exact frequency data and
all the existing checker obligations. [Primary paper](https://arxiv.org/abs/2505.08715)

### Recommended plasma milestones

1. Reproduce a small controlled field-line example through the existing
   certifier, graph transfer and non-crossing statement. Separate this cheap
   regression from the harder proposed `epsilon=0.003` target.
2. Close or revise that target's numerical gate on explicit evidence before
   scheduling its full kernel replay.
3. Build one device-derived analytic field package with a certified chart and
   model-error budget. Use its measured needs to select further mathematics.
4. Pursue particle tori as a distinct application, with three-frequency
   certification and physical-observable transfer where required.

These milestones can reuse the lunar checker, arithmetic and barrier work.
They do not imply that SO-2 or SO-3 is fundamentally flawed, nor that the
already reported SO-2 kernel run should be repeated for this assessment.

[← Back to the catalogue](../README.md)

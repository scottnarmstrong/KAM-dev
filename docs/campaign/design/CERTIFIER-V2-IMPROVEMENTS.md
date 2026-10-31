# Certifier v2: improvements for reusable physical applications

Date: 31 October 2026. Assessment anchored to
`bbf13193ed4dd15dfe141e2f7cd9902b48b818ea`.
Status: recommendations; no new theorem approved, implementation commissioned,
or application certificate claimed by this document.
Companion: [confirmed fixes and lunar clarification](CERTIFIER-V2-FIXES.md).
Application discussion: [plasma physics routes](../../explorations/themes/applications-and-demonstrations.md#plasma-physics-routes-review-31-october-2026).

Keep the proved A/B architecture and its checked-witness boundary. Prioritize
exposing useful existing mathematics, controlling certificate cost, and making
physical applications reproducible. These are opportunities for improvement,
not evidence that SO-2 or SO-3 has a fundamental defect.

In particular, the campaign log reports SO-2's working-branch kernel success
and SO-3's emitted-book CHECK success on 31 October. The companion records the
exact scope and pending audit/integration steps. Finishing a public application
means carrying that work through its remaining gates, not starting it over.

## 1. Certify the structured bounds already supported by route B

The theorem's [RefHypB](../../../KAM/Sharp2/RouteB/Data.lean), lines 186–192,
accepts independent bounds on `hamComm` and its segment Lipschitz constant.
The arithmetic records also carry independent `cTh`, `cDTh`.

The [checker adapter](../../../KAM/CertificateSharp/V2/RouteBCore.lean),
lines 76–83, instead fixes them to `2*M1`, `2*M2`. The current
[refHypB_of](../../../KAM/CertificateSharp/V2/RouteBRefined.lean) deliberately
proves those generic bounds. For structured Hamiltonians, evaluating the
commutator before taking absolute values can preserve useful cancellation.

**Work:** add numerical claims and sound checks for the commutator and its
derivative/Lipschitz bound, then generalize the checker-to-theorem bridge.
The Newton theorem already accommodates these inputs. Arbitrarily inserting
smaller numbers without these checks would be invalid.

**Gate:** on a fixed application package, establish rigorously smaller bounds,
identify the previously binding inequality, and measure the acceptance margin
and extra checking cost. If that inequality does not bind, do not claim a
useful threshold improvement merely because a component bound is smaller.

## 2. Refine the isoenergetic energy-row bound

`RunBWit.num` sets `y0 = p.M * w.sN`. The existing `HamFacts.dh` already gives
a separate uniform bound on the Hamiltonian gradient. A smaller such bound
could improve the energy-row estimates.

**This is a theorem-interface extension, not a checker-only substitution.**
[iso_g1_branch_B](../../../KAM/Iso/Sharp2/RouteB.lean), line 44, requires
`N.y0 = M * N.sN`; the run record and step proof consume that equality.
Introduce a separately certified `Mh1`, generalize the run/step/branch proofs,
and only then connect the refined checker data.

**Gate:** retain the old branch as a specialization; prove the generalized
branch at default limits; compare its margin and cost on the same certificate.

## 3. Select routes in the producer and optimize total checking cost

[routeV2All](../../../KAM/CertificateSharp/V2/RouteAll.lean) dispatches the
provided witness; it does not search other routes. That is an appropriate
trusted interface. Add producer-side selection over the baseline, A variants,
the weighted-ℓ¹ entry, B variants, and the existing hybrid.

The hybrid is already wired as
[routeV2Hyb](../../../KAM/CertificateSharp/Hybrid/Iso.lean). Earlier exploration
claims that it has no checker wiring are historical. The remaining question
is which applications benefit from it at actual certificate cost.

**Work:** use named route constructors and emit diagnostics for each attempted
route: required residual, achieved residual enclosure, displacement, binding
budget, support, precision, predicted replay cost, and measured cost when
available. Keep the passing baseline witness as a fallback.

Search strip widths, coordinate choices, precision, truncation and prefix
length together. Maximize useful margin subject to the resource budget, or
minimize replay cost subject to a chosen margin. A better theorem threshold
alone is not evidence of a faster certificate.

**Gate:** compare routes on identical model/candidate inputs with all claims
checked. Preserve an already passing baseline. Report resource-limited and
mathematically inconclusive runs separately from actual acceptance.

## 4. Extend sharp frequency certification beyond the lunar specialization

The enhanced [siteOk](../../../KAM/CertificateSharp/V2/SmallDivQ.lean),
lines 49–61, requires `n=2`, `tau=1`, and an exact positive last-coordinate
clock. Classical sites support the general route. The specialization suits
the lunar applications; it restricts sharpness for broader applications.

**Work:** develop an affordable three-frequency finite-part/tail checker,
including higher Diophantine exponents, then evaluate whether a general
dimension implementation is justified. Connect it to frequency selection:
numerical frequencies, exact nearby algebraic targets, enclosure, infinite
Diophantine witness, and the resulting torus displacement. Reuse the existing
quadratic/cubic constructions where applicable.

**Gate:** a genuine three-frequency example with every coordinate used, a
proved infinite tail, and resource measurements. Reject unsupported shapes
explicitly in producer tools until then. A floating-point frequency box by
itself does not establish the Diophantine premise.

## 5. Bound arithmetic and replay costs

Balanced summation bounds recursion depth but does not bound the bit length
of exact rational accumulators. [Heavy-test receipts](../../../kernel-tests/README.md)
record R1 cases above the machine's per-process memory limit. These historical
costs must not be confused with the later sharded SO-DATA3 success.

**Work:** build on existing fixed-point, outward-rounded and packed arithmetic;
extend it to remaining expensive small-divisor operations. Reuse independently
checked intermediate results, partition large checks into replayable shards,
and retain explicit budgets for rounding and truncation errors.

Coordinate with the existing [SO segmentation design](../../tracks/SO/design/SO-CSPLIT.md)
and [measured gate](../../tracks/SO/studies/SO-CSPLIT-GATE.md). Do not duplicate
the ongoing implementation or replace measured application evidence with an
unvalidated cost estimate.

**Gate:** representative forced computations under the current memory limit,
with wall/CPU time, peak RSS, output size and enclosure width. Extrapolate only
from the operations and representation actually measured. Heavy application
replays remain opt-in under the repository's resource rules.

## 6. Build a small perturbed-model regression suite

The combined A/B tests ultimately use the integrable T2 Hamiltonian. They are
good controls, but do not provide broad coverage of nontrivial Fourier
composition and residual cancellation. Existing lunar work supplies larger
application evidence; a cheap regression should complement it.

**Work:** add a small periodically forced Hamiltonian with interacting Fourier
modes and a complete certificate. Exercise applicable A/B routes, then vary
frequency separation, twist conditioning, support and precision. Add mutations
of coefficients, residual claims, frame bounds, ray room, schedules,
denominator separation and square-root domains. Test equivalent coordinate
and time normalizations through their checked transformations.

**Gate:** inexpensive default tests detect malformed advice and input-convention
drift; positive controls still pass. Track time and memory alongside margins.
Do not turn the full lunar replay into a mandatory routine build.

## 7. Package the model-to-physical-conclusion interface

The project already has Kepler charts, planetary transport, graph and barrier
arguments. The missing reusable product is a common application contract that
connects such ingredients to certificate data and physical observables.

| Component | Required information |
|---|---|
| Model | Exact equations, parameters or parameter set, units and normalization |
| Coordinates | Chart, valid domain, symplectic identity or justified time change |
| Approximation | Fourier/model truncation and rigorous remainder budgets |
| Frequency | Exact target, enclosure and infinite Diophantine witness |
| Certificate | Candidate, route, witness, checked margins and replay receipts |
| Physical output | Observable bounds, initial set, quantifiers and time interval |

[CertifiedTorus](../../../KAM/Certificate/Defs.lean), lines 356–368, is an
isoenergetic conclusion at `sinf • omegaStar`. A fixed-frequency certificate
API would be additional capability. The lunar clock and barrier bridges are
legitimate consumers of the present API; they do not require that replacement.

Expose reusable adapters for graph/embedding assertions, separation and
non-crossing, and observables in original coordinates. In higher dimensions,
one torus generally does not enclose a region on the energy surface. Bounds
for uncertain initial conditions therefore need additional families, geometry
or finite-time stability arguments, as contemplated in
[programs B](../../explorations/program-b-plan.md),
[C](../../explorations/program-c-plan.md), and
[D](../../explorations/program-d-plan.md).

Parameter uncertainty requires a stated quantifier and a checked model family;
it cannot be represented by silently replacing exact literals with empirical
error bars. Non-Hamiltonian effects require an appropriate separate theorem
or finite-time error analysis.

**Gate:** one complete application can be reproduced from its model package
through a physical theorem, with every approximation and coordinate map named.
Use SO-2/SO-3's existing progress as the first integration opportunity.

## 8. Provide a reproducible public workflow

At the reviewed revision, no checked-in GitHub Actions workflow or Python
dependency manifest was found. Many producer entry points are research scripts.

**Work:** pin Python dependencies, document a minimal candidate-to-certificate
workflow, provide named route/failure diagnostics, and add inexpensive CI for
the mirror comparisons and small Lean fixtures. Keep theorem infrastructure,
producer tools, examples and expensive data/replay targets clearly separated.
No new service or large full-library build is required for a first useful CI job.

**Gate:** an independent user can reproduce a small perturbed example from a
fresh checkout using documented commands, and can identify exactly what a
physical application proves from its public receipt. This is more useful than
using line counts or campaign percentages as the principal reuse milestone.

## Recommended order

1. Apply the [confirmed fixes](CERTIFIER-V2-FIXES.md), observing lunar landing
   holds; establish cheap regression checks.
2. Carry SO-2/SO-3 through their already planned audit, integration and final
   statement gates. Publish reproducible model/certificate receipts.
3. Integrate route selection and measure whether structured B bounds or the
   existing hybrid buy useful application gains.
4. Use a controlled magnetic field-line model as the first plasma integration
   case, subject to its numerical gate; see the
   [plasma-route assessment](../../explorations/themes/applications-and-demonstrations.md#plasma-physics-routes-review-31-october-2026).
5. Prioritize three-frequency certification and the chosen physical-model
   adapters before expanding into unrelated theorem families.

This is a proposed order of investment. It does not change existing campaign
authorizations, claim universal A/B dominance, or certify a new physical model.

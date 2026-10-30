# W-w1b delta review

Reviewer: sol-delta-W-w1b (independent reviewer sol-delta-W-batch2).

Verdict: FAIL.

Scope: rule 9 applied to this slice: only records still PROPOSED on entry. REVIEWED node and coverage records are out of scope; prerequisites and consumers were read only as context. No graph acceptance or proof status is changed by this report.

The corrected Picard hypotheses use 0 < M < delta, and the parameter argument uses the common convex ball and the explicit Gronwall external. The contour-shift record passes as a faithfully exposed SOURCE_GAP: K dec-shift only records the sign-chosen shift, while W invokes arbitrary eta. Its intended import is not certified as a discharged application.

## Node verdicts

| id | verdict | spans or reason |
| --- | --- | --- |
| stepW:w1:recanalytic | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682 |
| stepW:w1:recder | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691 |
| stepW:w1:dcbound | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764 |
| stepW:w1:hamargin | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816 |
| bpW:w1:flow | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866; blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L868-L902 |
| stepW:w1:picard | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875 |
| stepW:w1:picardholo | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888 |
| stepW:w1:flowlim | FAIL | L890-L891 passes to the limit under the Bochner integral, directly consuming bpW:w1:ext-integral (L103-L108), but DEPS and EDGE omit it. The dependencies of picard do not replace this direct use. |
| stepW:w1:flowpar | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901 |
| stepW:w1:shift | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974 |
| stepW:w1:orthants | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983 |

## Coverage verdicts

| id | verdict | spans |
| --- | --- | --- |
| stepW:w1:recanalytic | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682 |
| stepW:w1:recder | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691 |
| stepW:w1:dcbound | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764 |
| stepW:w1:hamargin | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816 |
| bpW:w1:flow | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866 |
| stepW:w1:picard | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875 |
| stepW:w1:picardholo | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888 |
| stepW:w1:flowlim | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894 |
| stepW:w1:flowpar | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901 |
| stepW:w1:shift | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974 |
| stepW:w1:orthants | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983 |

all other coverage items PASS (within the PROPOSED delta scope only; previously REVIEWED items are not re-reviewed). Each pending disposition maps its source unit to the correct node or nodes, including the route mapping and curvature preamble where applicable. Node contract or edge failures above do not invalidate these coverage mappings.

## Complete replacement blocks

Correction for stepW:w1:flowlim:

```text
NODE: stepW:w1:flowlim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
CONTRACT_ID: stepW:w1:flowlim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the iterates converge uniformly to phi, a C^1 solution of the integral equation; uniqueness among solutions in V; phi^t holomorphic with the derivative bound; this proves (i), (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:picard, bpW:w1:ext-ode, bpW:w1:uniform-limit, stepW:w1:picardholo, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L890-L890 | geometric convergence of the iterates
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L891-L891 | uniqueness of ODE solutions for Lipschitz fields
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy of the uniform limit
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy and bounds of the iterates
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L890-L891 | uniform convergence of the Picard integrands permits passage to the limit under the Bochner integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w1b+sol-delta-W-w1b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects and deviations

blueprint-W/parts/w1-sequences.tex L973-L974: "apply the contour shift of track K's bp:p1:fourier-basic". That lemma (p1-analysis.tex L757-L768) has no contour-shift statement. The intended dec-shift at L800-L811 is scoped by L792-L798 to t_j = -rho_prime sgn(k_j); the arbitrary-eta extension is not supplied. This is already faithfully recorded in stepW:w1:shift, so it is not a new topology FAIL.

No mathematical repair is supplied. Validation: all six W corpus hashes and the K import hash match their pin files. Report row counts and complete replacement fields are checked with read-only Python; no git, lake, Lean, or lint was run. Only this batch's seven requested review reports are written.

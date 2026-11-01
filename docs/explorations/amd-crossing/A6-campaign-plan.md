> Source: `RESEARCH/CAMPAIGN-PLAN.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`. Paths `_sources/…` refer to `RESEARCH/_sources/` in the workspace.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Launch plan: strong-LP upgrade, nonresonant rate, spatial extension

This is a proposed campaign, not an authorization to modify the current repository in this research turn. All work here was read-only against `/root/code/KAM` commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`; deliverables were written only under RESEARCH. No workers, builds or source changes were launched. The planning workflow follows the project's lean-project-architecture planning guidance: approve exact source-backed interfaces, keep frozen anchors separate from implementation, and audit statement fidelity independently of compilation.

## 1. Recommended sequence and gates

### Phase 0 — freeze the mathematical contract, not the implementation

Use `STATEMENTS.md` ([A5](A5-statements.md)) as the owner decision packet and `PROOF-PLAN.md` ([A4](A4-proof-plan.md)) as the proof design. Resolve coordinate convention, normalized masses, fixed AMD margin, compact action/axis set, free τ versus the advertised specialization, crossing notion, and mandatory spatial scope. Ask the co-author for the intended publication claim and any known prior-art theorem matching the sharp domain. Obtain Niederman 1996 and inspect Pinzari 2013 before claiming novelty; the independent proof route need not wait for a novelty verdict.

Write a line-addressable source manuscript with complete lemmas, not only a list of ingredients. Proposed future source: `blueprint-AMD/parts/` with `a0-conventions.tex`, `a1-threshold.tex`, `a2-domain.tex`, `a3-nek77.tex`, `a4-nonresonant.tex`, `a5-spatial.tex`, `a6-osculating.tex`. These paths are proposals, not files created here. Incorporate the concrete arguments and constants from PROOF-PLAN, preserving every item marked open risk.

**Go gate:** owner-approved literal definitions/statements; independent audit of normalization, quantifiers, strong threshold, and physical crossing; a reviewed proof of the planar enlarged product domain. Only then elaborate anchor candidates, review their binder/body semantics, record hashes and freeze them. Existing P-EXP-SAFE stays untouched. A source gap may be explicitly retained in the graph but cannot be counted as a proved supplier.

### Phase 1 — cheapest meaningful milestone: planar strong-LP safety with Nek77

Build the attained threshold API, the exact barrier and compactness theorem, full slow-ball analytic domains, and the revised first-exit adapter. Reuse the exact moving-Sun Hamiltonian, planar Poincaré charts, `ComplexTube.tube`, Kepler Hessian data, and `partialConvex_nekhoroshev`.

**Deliverable:** the new planar anchor in STATEMENTS §6.1, with no mean-motion arithmetic assumption and no secular-confinement assumption, time exponent \(2/(6n^2-3n+14)\), axis drift exponent \(3/(6n^2-3n+14)\), and the strong threshold applied to the whole system's AMD. Candidate A is an earlier useful submilestone, but it is not the dynamical completion gate.

**Stop/go gate:** demonstrate coverage of every state in the specified compact strong sublevel, not only states that fit the old common-eccentricity AMDBox. Audit the center-dependent slow level and fixed collar. Check the actual provider chain has discharged all stopped hypotheses. Accept only after exact source comparison, authorized serialized build, standard axiom check, and frozen-hash check.

### Phase 2 — nonresonant planar exponent

Use `KAM/Nekhoroshev/Partial/NormalForm.lean:nf` and `Partial/Nonresonant.lean:nonresonant` directly. Build the period-one/physical-time adapter, finite-cutoff Diophantine estimate, and parameter algebra from PROOF-PLAN (E1)–(E3). Reuse all Phase 1 geometry and continuation machinery.

**Deliverable:** STATEMENTS §6.2, with \(a=1/[2(\tau+1)]\), drift \(O(\sqrt\mu)\), and an optional corollary \(\tau=n-1/2\) giving \(1/(2n+1)\).

**Stop/go gate:** audit every factor of \(2\pi\), the slow scaling coefficient, norm convention, inverse-map cost, and constants-before-initial-data quantifiers. Do not build a duplicate Pöschel engine. If the existing API proves awkward, first write a narrow adapter; any genuinely missing theorem must be named and sourced before expanding scope.

### Phase 3 — spatial Candidate B

Build spatial element/vector-momentum identities, a regular spatial Poincaré chart, and the spatial Newtonian reconstruction. Use a fixed rotation aligning initial total angular momentum. Prove that the full enlarged four-square slow ball is safe even off the \(L_x=L_y=0\) level; then reuse the same N theorem with \(k=2n\).

**Deliverable:** STATEMENTS §6.3 with intrinsic phase-space premises, no externally imposed inclination or secular stability assumption, and the same fast exponent as Phase 2.

**Stop/go gate:** independent audit of chart coverage at zero eccentricity and zero inclination, symplecticity, \(\Gamma+Z\) identity, and absence of a hidden small-eccentricity hypothesis. If the chart proof covers only a smaller set, report the exact missing domain rather than weakening the approved theorem silently.

### Phase 4 — actual-velocity osculating bridge

This can start alongside Phase 2 and complete planar first. Prove the exact velocity formula, the compact \(O(\mu)\) element comparison with gravitational parameter \(1+\mu m_i\), and the preservation of radial gaps. Export the no-crossing statement using the actual osculating convention. For later observational applications, add a reverse input-coordinate conversion.

**Stop/go gate:** verify that “osculating” is not just the name of the existing canonical eccentricity vector; check no time-growing error was introduced. The mathematical safety theorem may close earlier, but the requested physical-element corollary is a distinct completion item.

### Phase 5 — explicit certificate pilot

Run this as a separate practical track after early screening, not as a promised consequence of Phases 1–4. First try one two-planet model from PRACTICAL, preferably HD 109271 or HD 1461, using a fixed fit and explicitly bounded inclination/mass assumptions. Prove a finite-cutoff certificate soundness theorem, optimize domain estimates numerically, and then generate rational/interval evidence checked by the kernel.

**Stop/go gate:** one target, one declared physical model, one input box, and a literal ledger of domain, divisor, norm, remainder and AMD-margin inequalities. If the first substantive inequality fails at actual mass, report it and the certified smaller-mass threshold. Do not replace a full unaveraged claim with a truncated secular model without changing the theorem name and scope.

## 2. Packages, dependencies and prospective ownership

Owners below are launch roles, not workers currently running. Each prover's result needs a distinct auditor; the integrator must not substitute a build for mathematical/source review. Use the repository's current model-role policy in `docs/DECISIONS.md` at launch rather than hard-coding an obsolete model roster here.

| Package | Concrete output | Dependencies | Prover / independent auditor | New Lean estimate |
|---|---|---|---|---:|
| A0 | Exact normalization and statement adapters; definition bodies audited | Owner contract | Integrator / statement auditor | 300–600 |
| A1 | Pair compact minimum, contact equality, positivity, continuity, strong equivalence | Scalar defs | Geometry prover / geometry auditor | 1,200–2,000 |
| A2 | Planar and abstract spatial AMD barrier, uniform radial compactness, Candidate A | A1, existing planar elements | Geometry prover / dynamics auditor | 800–1,400 |
| A3 | Center-dependent full slow balls, safe enlarged product, uniform complex domain/norm | A2, existing chart/tube | Analytic-domain prover / analytic auditor | 1,000–2,000 |
| A4 | New stopped adapter, no-exit/continuation, Nek77 strong-LP provider | A0–A3, existing N/P engines | Dynamics prover / source auditor | 1,200–2,200 |
| A5 | Diophantine cutoff, period/scaling adapter, explicit parameter algebra, nonresonant provider | A3–A4, existing `nf`/`nonresonant` | Dynamics prover / arithmetic-source auditor | 1,500–3,000 |
| S1 | 3D elements, cross products, momentum conservation, model/export dictionary | Model decisions; A1 usable independently | Spatial geometry prover / mechanics auditor | 2,000–3,500 |
| S2 | Regular spatial Poincaré chart, symplecticity, analytic and onto results | S1; pinned source construction | Chart prover / chart auditor | 4,000–7,000 |
| S3 | Rotation alignment, full spatial slow-ball safety, domain/flow adapters, final provider | A2–A5, S1–S2 | Spatial dynamics prover / independent statement auditor | 3,000–6,000 |
| O1 | Actual velocity/osculating formulas, compact comparison, no-crossing corollary | A2/A4; S1 for space | Mechanics prover / geometry auditor | 1,000–2,000 |
| C1 | Finite-cutoff analytic certificate specification and soundness | A1/A3/A5, explicit source | Certificate prover / numerical analyst auditor | 4,000–8,000 |
| C2 | Rational input box, interval domain/norm estimates, emitter and checked sample | C1, target screening | Numerical analyst / independent data auditor | 3,000–7,000 plus data |

Phase 1: approximately **5–9k** new lines. Phase 2: **2–4k** including adapters/review fixes. Spatial: **9–17k**. Osculating bridge: **1–2k**. Thus the qualitative campaign is roughly **17–32k** new lines, with overlap removed during implementation. Explicit certification adds roughly **7–15k** hand-written code plus potentially much larger generated evidence. These are planning ranges, not deadlines or promises.

Calibration: current `KAM/Nekhoroshev` is 34,055 lines, including 12,472 in `Partial`; current `KAM/Planetary` is 147,974, but its AMD + Exponential directories total only 4,174. Poincaré is 3,957 and Newtonian 2,836; the separate Kepler library is 5,116. Counts came from `wc -l`, excluding certificate data trees and generated root imports, with comments/blanks included. Details and non-overlapping totals are in GAP-ANALYSIS ([A3](A3-gap-analysis.md)) and `_sources/repo-line-counts.json`.

## 3. Work that can begin before new frozen anchors

Once a proof campaign is separately authorized, infrastructure does not need to wait for the final headline signature:

* A1 can develop the compact-minimum scalar API with transparent provisional definitions and prove equivalence to LP's relative threshold. No dynamical claim is frozen by doing so.
* Abstract finite-dimensional budget/radial lemmas in A2 can be proved independently of the Newtonian flow.
* S1 can build dimension-three Kepler identities and cross-product conservation using `Fin 3 → ℝ`; the coordinate normalization must first be fixed.
* The analytic team can extract a generic family-uniform version of the existing compact periodic extension theorem, and verify its precise hypothesis fit.
* O1 can prove the canonical-to-actual-velocity algebra and compact continuity estimates.
* The numerical analyst can screen published fits, solve pair minimizations with rigorous bounds, and identify the first failed normal-form inequality. This is exploratory evidence, not a final certificate.

Do not pre-freeze an outcome predicate containing a normal-form witness, a stopped confinement hypothesis, or a completed conclusion. Infrastructure remains reviewable implementation; public anchors wait for source/statement approval.

## 4. Parallelism and integration discipline

With four available roles, a useful launch allocation is geometry prover, analytic-domain prover, spatial-infrastructure prover, and independent reviewer/integrator. A3's generic analytic work and S1 can proceed while A1/A2 are underway; A4 waits for A3; A5 waits for the same geometric interface; S2 is the spatial critical path. Audit each bounded package before its consumers depend on it.

Only **one Lean/Lake process at a time**, with `LEAN_NUM_THREADS=1`, under the current machine restrictions; parallel work means reasoning/editing in disjoint owned files, not simultaneous builds. This research brief prohibited all builds and edits, and that restriction was observed. Future integration must respect the repository's module system, 1,500-line file cap, no axiom/admit/unsafe placeholders, no heartbeat evasions, frozen manifests, and explicit ownership. Avoid touching generated `KAM.lean` merely to make a report look current.

Prefer small interfaces around geometric witnesses and original-variable stopped bounds. Keep public source premises outside provider internals. The integrator owns anchor sealing and the final exported statement; the spatial chart team should not change the normalization unilaterally. Numerical generated data belong in their own tree and are excluded from hand-written-size progress metrics.

## 5. Source and dependency-graph plan

The existing source ancestors are `blueprint-P/parts/p14a-amd-expsafe.tex` and Track N's `p11b-partial-nf.tex` / `p11c-partial-stability.tex`. Reuse the exact nodes `bpP:p14:expsafe`, `bpN:p11:nf`, `bpN:p11:nonresonant` and the partial-convex anchor where appropriate; do not copy their entire descendant graphs into a second foundation.

The proposed new blueprint must contain individually labeled nodes for:

1. absolute/relative threshold dictionary, attained contact minimum and continuity;
2. angular-momentum/eccentricity budget and quantitative compact barrier;
3. local full-product enlargement, uniform family compactness, complex extension, Fourier norm;
4. existing N theorem instantiation, scale conversion, preimage/transfer, and source-to-parameter arithmetic;
5. **separate** first-fast-exit, first-slow-exit, moving-threshold and physical continuation steps;
6. spatial chart coverage/regularity/symplecticity, frame alignment, off-level safety;
7. actual-velocity osculating comparison and final radial-gap transfer.

PROOF-PLAN is the present design source, but its open-risk items are not yet a complete audited proof manuscript. Before graph extraction, turn them into proofs or explicit source-gap nodes. After frozen signature approval, use the project's source-level graph workflow with independent extractor/reviewer roles, direct `DEPS`/`EDGE` receipts, exact line locators, parameter/constant scopes, and a retained findings ledger. A structural graph PASS does not close a source gap. A compiling provider does not authorize a changed theorem statement.

## 6. Risks and responses

| Risk | Concrete detection and response |
|---|---|
| False novelty | Obtain Ni96 and full Pinzari13; advertise a formalized refinement until exact containment is resolved |
| Hidden small-eccentricity restriction | Test the source proof on the full \(C\le B-\delta\) region, including allowed moderate/high eccentricity and circular strata |
| Uniformity lost by one global slow ball | Use center-indexed levels and finite/compact parameter uniformity; retain all prescribed initial states |
| Secular coordinates treated as passive | Consume the existing extended `nf` with its slow-bracket inequality; never use ordinary Pöschel unchanged |
| First-exit circularity | Audit the stopped interval and strict improvement before endpoint continuation; keep original AMD in the estimate |
| Spatial chart excludes e=0 or i=0 | Require regular Poincaré variables and a precise onto theorem; do not patch by imposing positive eccentricity/inclination |
| Physical/canonical confusion | Keep separate definitions; prove exact velocity and \(O(\mu)\) comparison once |
| Numerical failure at actual mass | Screen before building a large checker; report failed divisor/norm/collar inequality and achieved mass/time honestly |
| Observational premise unavailable | Declare fit/epoch, masses/inclinations and included bodies; posterior credibility is not a deterministic all-data theorem |
| Source drift during long campaign | Pin commits and source hashes, audit only owned changes, and preserve frozen contracts |

## 7. Owner and co-author handoff

The owner has a concrete choice packet in STATEMENTS §9 and a practical assessment in PRACTICAL ([A7](A7-practical.md)). Recommended approval is the three staged qualitative anchors plus the osculating corollary, with the explicit certificate pilot as a separately budgeted experiment. The co-author's most valuable contributions are: confirming the intended LP-conjecture interpretation; supplying any known sharp-domain prior art; checking the spatial full-ball argument; and deciding whether an isolated published exoplanet model is a useful first practical target even before an observationally robust certificate is possible.

Completion requires all requested stages, or an explicitly revised owner scope. Phase 1 is a useful theorem in its own right, but it must not be presented as spatial Candidate B or as an actual-mass astronomical application.

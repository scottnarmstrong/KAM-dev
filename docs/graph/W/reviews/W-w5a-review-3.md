# W-w5a: independent delta 7 source review

Reviewer: `sol-delta7-W-w5a` (codex-1).

Verdict: **FAIL**.

Scope: 12 PROPOSED nodes and 3 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w5:t-comp | FAIL | The repaired symmetry proof consumes DP(w)=varpi(X_P(w),.) and holomorphy of X_P from the definition of the smoothing Hamiltonian class (W5 L105-L110), directly at L304. omega supplies continuity of the form, not this defining derivative identity. Add the direct class edge; the repaired mathematics itself is closed. |
| stepW:w5:s-out | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L367-L372 |
| bpW:w5:flow | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L380-L395; blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L396-L420 |
| stepW:w5:f-flow | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L400-L403 |
| stepW:w5:f-par | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L404-L409 |
| stepW:w5:f-der | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L410-L413 |
| stepW:w5:f-image | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L414-L415 |
| stepW:w5:f-real | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L416-L419 |
| stepW:w5:c-skew | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L450-L453 |
| bpW:w5:ext-symm | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-symm@L57-L61 |
| bpW:w5:ext-sqrt | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-sqrt@L62-L66 |
| bpW:w5:ext-triangle | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-triangle@L67-L70 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w5:ext-symm | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-symm@L57-L61 |
| bpW:w5:ext-sqrt | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-sqrt@L62-L66 |
| bpW:w5:ext-triangle | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-triangle@L67-L70 |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

The two symmetry repairs apply ext-symm over C to an actual second derivative, without assuming symmetry: t-comp differentiates the defining DP identity using holomorphic X_P; c-skew uses s-class and differentiates DF, then uses antisymmetry of varpi. t-comp's ext-symm and omega edges are genuine; the additional class edge is required below. c-skew's three dependencies suffice for its repaired argument.

s-out now consumes lie(iv), not merely lie(ii); the weight guard holds at a=p=1 and the generalization supplies the p_+ version. Its norm estimates use the input bound, lattice estimate and W4 homological outputs at the cited sites.

The delta-6 flow revisions correctly treat V,U,delta,M,L as application data whose hypotheses are proved, rather than assuming their derived inequalities. f-margin supplies the W1 ball/field hypotheses. f-flow uses the time integral into P^{p_+} and differentiation under the integral; its sharp sup estimate is |t| M_F. f-par uses the two-parameter W1 flow bound and Cauchy estimates on the same convex ball; the combined norm uses the sup-plus-weighted-Lipschitz input bound. f-der uses the sigma/8 ball, f-flow and f-par; f-image unpacks that increment; f-real uses uniqueness, realness and periodic coefficients. No enlarged parameter domain or parameter-diameter assumption is introduced.

All three new W5 external statements match L57-L70, including the near-point derivative hypotheses for symmetry, the positive-real-part slit-plane condition for the principal square root, and continuity into a Banach space for the triangular identity. Their records are leaves with EXTERNAL initial Lean status; their coverage items map exactly to them.

## Replacement fragments

### stepW:w5:t-comp (owner: W-w5a)

The repaired symmetry proof consumes DP(w)=varpi(X_P(w),.) and holomorphy of X_P from the definition of the smoothing Hamiltonian class (W5 L105-L110), directly at L304. omega supplies continuity of the form, not this defining derivative identity. Add the direct class edge; the repaired mathematics itself is closed.

```text
NODE: stepW:w5:t-comp
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L299-L307
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L299-L307
CONTRACT_ID: stepW:w5:t-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:taylor: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); s, r > 0; p_+ in [p+1/2, p+1]; P(.,xi) in S_{p_+}(D(s,r)) real, 1-periodic in each theta_i, ¦X_P¦^lambda_{r,D(s,r)} <= eps; S_t, T_t the scalings; a, b, g, H and R as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:taylor (for all such P; eta in (0,1/8] for (iv)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: a, b, g holomorphic; H a Cauchy integral, holomorphic, bounded, symmetric; the z-blocks; reality and periodicity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:cauchy, bpW:w4:index, bpW:w3:ext-integral, bpW:w1:ext-onevar, stepW:w5:t-est, bpW:w5:ext-symm, bpW:w5:omega, bpW:w5:class
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L301-L301 | the derivative as a Cauchy integral
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L302-L302 | bound
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L306-L306 | substitution u, v in z, zbar
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L301-L301 | differentiate the Cauchy integral with respect to theta
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L300-L300 | Cauchy integral representation of the directional derivative
EDGE: stepW:w5:t-est | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L303-L305 | the proof explicitly invokes t-est for the sharper bound on H
EDGE: bpW:w5:ext-symm | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L305-L305 | symmetry of D^2P with K = C
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L304-L304 | DP(w) = varpi(X_P(w), .)
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L304-L305 | the smoothing Hamiltonian definition supplies DP = varpi(X_P, .) on a neighbourhood and holomorphy of X_P, needed for the second-derivative symmetry application
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+claude-suborch-W-gapfix+sol-delta7-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5a`: exit 0; `W-w5a: 53 nodes, 181 edges, 77 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w5a

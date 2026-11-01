# W-w5b: independent delta 7 source review

Reviewer: `sol-delta7-W-w5b` (codex-1).

Verdict: **PASS**.

Scope: 4 PROPOSED nodes and 0 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w5:n-exp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L491-L498 |
| stepW:w5:p-inv | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L526-L533 |
| stepW:w5:p-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L537-L543 |
| stepW:w5:a-hol | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L662-L666 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

`n-exp`: the continuous integrand is {hat N-R,F}(phi^tau w); the new triangular-integral external is invoked at the consumer L495. Combining its (1-tau) factor with R(Phi w)-R(w) gives precisely {(1-tau)hat N+tau R,F}; the sign and constant hat a_0 agree. FTC and flow/flow-calc are genuine direct uses. No Fubini input or unbounded X_N pullback is assumed.

`p-inv`: output rescaling contributes eta^(-2); smallness gives the half-unit operator perturbation and inverse norm <=2. The derivative difference retains |xi-zeta|, and the resolvent identity gives lambda|Delta inverse|<=4|xi-zeta|. Each dependency supplies the displayed norm comparison, derivative estimate, inverse theorem or smallness.

`p-ass`: the inverse-difference term contributes 4|Y|, the direct parameter term 2 lambda|Y|^L, and the transport term |Y|/2 because lambda|Delta phi|<=sigma|xi-zeta|/8. Adding the sup bound 2|Y| gives 13|Y|/2+2 lambda|Y|^L <=7|Y|^lambda. Its flow-parameter edge is a direct use at L540. No factor of parameter distance is lost, and lambda=0 does not require division by lambda.

`a-hol`: Re(xi_i+y_i)>0 supplies the slit-plane guard and excludes zero. The principal square root composes with the affine argument, the exponentials are entire, and the normal part is linear. On the real torus the recovered q_i,p_i give the frozen clockwise linearTorus with the factors sqrt(2) and 2 pi. ext-sqrt, coords and linearTorus are genuine uses. These repaired gaps are closed.

## Replacement fragments

None.

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5b`: exit 0; `W-w5b: 32 nodes, 122 edges, 48 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w5b

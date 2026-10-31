# W-w1b: Batch B delta review 5

Reviewer: sol-delta5-W-w1b. Verdict: **FAIL**.

Delta 5 scope: only the one PROPOSED kam-conventions coverage item, with its restored node and the touched W4 index consumer. Read W1 L943-L949 and every W4-W8 occurrence. W4 L87 is inside the convention statement L59-L103 and uses the conjugate-coordinate exchange. It is not an excluded outline or source note, so the stated exclusion reason fails rule 11.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes 76bfab07bc0e078fc4207c122a15b89e7071f3daa12d1571405a23b825a04edc; coverage 00ec9a10400e5b04087c8ade1c9f3ec18fac5860cf2b42966b3ac53a508cd633.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w4:index | FAIL | Rule 11: the coordinate convention cites kam-conventions inside its statement at L87; this is a direct use, not excluded prose. (Touched cross-slice consumer.) |
| bpW:w1:kam-conventions | FAIL | Missing node; source re-read: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L943-L949. Complete addition below. |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w1:kam-conventions | FAIL | W4 index cites this claim inside its convention statement (w4-homological.tex L87), so exclusion violates rule 11. |

all other coverage items PASS within the assigned PROPOSED delta scope; already REVIEWED records outside that scope were not reopened.

Assigned delta records checked: 0 nodes and 1 coverage items. Cross-slice replacement blocks above are limited to consumers touched by the failed exclusions.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: bpW:w4:index
KIND: definition
TITLE: Normal modes, reindexing, coordinates
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:index@L59-L103
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:index
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, p >= 0
SOURCE_QUANTIFIERS: a, p
SOURCE_CONCLUSION: convention: bar p = p+1; tangential modes 1,2, normal modes J = j+2 indexed by the P96-K index j >= 1; the space l^N_{a,q} of (z_j)_{j>=1} with ¦¦z¦¦_{a,q}^2 = sum omega_{a,q}(j+2)^2 ¦z_j¦^2 (wave weights; realized in lp with the entries J = 1,2 zero); max norm on C^2, ¦k¦_1 on Z^2; the unweighted pairing <x,x'>_0 with (bpW:w4:pairing) ¦<x,x'>_0¦ <= ¦¦x¦¦_{a,q} ¦¦x'¦¦_{a,q'} for q + q' >= 0; z = (u+iv)/sqrt2, zbar = (u-iv)/sqrt2 with (bpW:w4:zu); period-one angle theta (x = 2 pi theta), strip T_s, domain D(s,r); symplectic form 2 pi sum dtheta ^ dy + sum du ^ dv and Hamilton's equations (bpW:w4:hameq); angular frequencies omega, nu = omega/(2 pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w1:tails, bpW:w0:z, bpW:w1:kam-space, bpW:w1:kam-conventions
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L69-L69 | weighted coordinates at weight (a,q)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L70-L70 | the convention for normal-mode sequences (entries J = 1,2 zero)
EDGE: bpW:w0:z | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L86-L86 | the W0 convention z = (q + ip)/sqrt2
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L93-L93 | the domain D(s,r) of Definition bpW:w1:kam-space
EDGE: bpW:w1:kam-conventions | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L87-L87 | the W0/P96-K conjugate-coordinate exchange cited inside the convention
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta5-W-w1b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The pointer to Lemma bpW:w4:lie(iv) (guard (G)) at L61-L62 and to Remark bpW:w4:weights are forward pointers; not edges.
```

```text
NODE: bpW:w1:kam-conventions
KIND: claim
TITLE: Coordinate exchange and sum/max norms used in W4
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L943-L949
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:kam-conventions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the W0 complex-coordinate convention and the W1 KAM domain
SOURCE_QUANTIFIERS: for normal phase coordinates and their norms as stated
SOURCE_CONCLUSION: P96-K's z=(u-iv)/sqrt2 and zbar=(u+iv)/sqrt2 exchange the W0 z and zbar; the normal form <omega,y>+<Omega,z zbar> and smallness norms are invariant under this exchange; W4-W6 retain the W0 convention; D(s,r) uses ¦¦u¦¦+¦¦v¦¦, between the product max norm and twice that norm
CONSTANT_SCOPE: the sum/max comparison factor is at most 2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w1:kam-space, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L945-L945 | the W0 convention used in the exchange
EDGE: bpW:w1:kam-space | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L947-L948 | the domain uses the sum of the normal component norms
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L948-L948 | the frozen WaveSpace product max norm occurs directly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-delta5-W-w1b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Restored because bpW:w4:index cites the coordinate-exchange claim at w4-homological.tex L87 inside its convention statement. The P96-K convention is source comparison, not a new external theorem.
```

```text
ITEM: bpW:w1:kam-conventions
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L943-L949
DISPOSITION: NODE bpW:w1:kam-conventions
REASON: the coordinate-exchange claim is directly cited inside the statement of bpW:w4:index at L87; prose and source-note mentions remain provenance
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2+sol-delta5-W-w1b
REVIEWER: -
```

## W4-W8 exclusion search

All reachability exclusions in the wave-2 SPEC were searched by label and mathematical content: reconstruction#rescaling; pde-equiv/time/ident/converse; formal-birkhoff; duffing/ext-lindstedt; w4:k0/k0one/k0diff. No downstream statement/proof use was found. W4 k0 is mentioned only in its own proof, its source note, the excluded melnikov-check remark and the excluded interface summary; downstream k=0 bounds use W7 sep.

The rechecked remark uses divide as follows: w1:kam-conventions is used in W4 index L87; w3:class-remark is used in W6 t-an L374 (FAIL proposals in their owning delta reports). w3:interface appears in inputs/section prose, source notes and excluded remarks; w0n:kappa appears in W7 source L207 and excluded interface L783; wh:weakenings appears in source notes W6 L165/W8 L601 and outline W8 L34. operator-fourier, w2:hyp, w2:constants, w2:hidden and wh:reading have no W4-W8 citations.

## Suspected blueprint errata and deviations

No new suspected blueprint defect. The coordinate-exchange remark is consumed in W4; the exclusion reason is the defect.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.

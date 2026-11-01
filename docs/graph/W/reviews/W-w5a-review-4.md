# W-w5a: independent delta 8 source review

Reviewer: `sol-delta8-W-W-w5a`.

Verdict: **PASS**.

Scope: only the 1 requested PROPOSED delta-7 replacement record(s), under SPEC through “2026-10-31, delta 7” and REVIEW-BRIEF rules 1-11, especially delta rule 9. This is a source-field and dependency review, not proof completion. The reviewer tag is distinct from all earlier review tags.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| stepW:w5:t-comp | PASS | blueprint-W/parts/w5-kamstep.tex L35-L39, L57-L61, L89-L119, L265-L285, L299-L307, L314-L320; blueprint-W/parts/w4-homological.tex L69-L113; blueprint-W/parts/w1-sequences.tex L89-L98, L749-L787; blueprint-W/parts/w3-birkhoff.tex L73-L82 |

## Coverage verdicts

No coverage item is reopened by this delta. All other coverage items PASS within the requested delta scope; previously REVIEWED coverage is not re-certified.

## Source and dependency findings

The step's fields inherit the Taylor lemma's data and quantifier scope, retain the local coefficient definitions, and record holomorphy, boundedness, symmetry, the complex-coordinate blocks, reality and periodicity. They do not turn derivative symmetry into a hypothesis. Statement and proof locators both cover exactly Components, L299-L307.

The new class edge at L304-L305 is direct: S_{p_+} supplies DP(w) = varpi(X_P(w), .) throughout the open domain and a holomorphic X_P. Consequently the derivative of DP is W -> varpi(DX_P(w)W, .), using the continuous bilinear form of omega. Thus both neighbourhood differentiation and differentiation of the derivative required by ext-symm are supplied, with K=C. The class locator L105-L119 and ext-symm locator L57-L61 match these premises.

The retained deriv-continuous, ext-onevar and ext-integral uses support the Cauchy representation and its differentiation; cauchy and t-est support the bounds. The index edge is consumed in the substitution at L306-L307; omega is consumed at L304. All nine EDGE locators point inside this consumer's proof. These are prerequisite uses, not additional source hypotheses.

## Replacement fragments

None: every in-scope record PASSes.

## Checks

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all 11 pinned source files reported `OK`.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5a
W-w5a: 53 nodes, 182 edges, 77 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. This checks the existing graph structure; it does not mark these records REVIEWED or certify Lean proofs.

A search of current non-draft `*.nodes.md` packets and `DEPGRAPH.md` found no `bpW:w7:melnikov` references. Its coverage exclusion remains administrative context, outside this delta. None of the four reviewed records has a stale Melnikov dependency, edge, source-field citation or note.

## Suspected blueprint errata

None newly suspected in the reviewed delta. The four delta-7 findings were packet transcription/topology corrections; this review does not reopen previously recorded source errata.

## Handoff

Only the three requested delta-8 review files were written. Packets, graph databases, source files, frozen files and manifest were not edited. No implementation Lean was read. No Lean, Lake, build, axiom probe, source lint or state-changing git command was run. Previously REVIEWED records were read only as dependency/use-site context and are not re-certified.

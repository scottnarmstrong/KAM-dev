# W-w6: independent delta 8 source review

Reviewer: `sol-delta8-W-W-w6`.

Verdict: **PASS**.

Scope: only the 2 requested PROPOSED delta-7 replacement record(s), under SPEC through “2026-10-31, delta 7” and REVIEW-BRIEF rules 1-11, especially delta rule 9. This is a source-field and dependency review, not proof completion. The reviewer tag is distinct from all earlier review tags.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w6:prep-step | PASS | blueprint-W/parts/w6-iteration.tex L22-L27, L211-L271; blueprint-W/parts/w7-measure.tex L127-L131, L211-L231, L255-L264; blueprint-W/parts/w4-homological.tex L194-L208; blueprint-W/parts/w5-kamstep.tex L105-L119, L328-L348, L474-L489, L565-L588 |
| stepW:w6:p-lipp | PASS | blueprint-W/parts/w6-iteration.tex L220-L245, L260-L263; blueprint-W/parts/w5-kamstep.tex L89-L93, L328-L348, L380-L403, L565-L588 |

## Coverage verdicts

No coverage item is reopened by this delta. All other coverage items PASS within the requested delta scope; previously REVIEWED coverage is not re-certified.

## Source and dependency findings

prep-step: the source fields retain Borel Pi, the alpha bound, the positive epsilon majorant, the smoothing input on Pi minus Xi, the modified exponents and the chosen radii. SOURCE_CONCLUSION now records the onto property of D Phi_P stated at L229 and the actual zones(i) divisor inequality of L232-L235. The remaining frequency, transformation and perturbation conclusions agree with clauses (ii)-(v); constants retain the scope of constants, which depends on m only.

The new wave edge at L234-L235 is a direct, explicit use of wave(ii)'s Dirichlet/P96-K weight comparison. Its supplier is L194-L208, particularly L203-L206. For difference modes the shifted labels give min(i,j)+2=min(I,J), beta=1/4 and p+1-p_+=1/2=2 beta. For the other modes the weight comparison supplies the unmodified condition. The zones(i) premises are already present, and outside Xi each strict zone inequality fails. No admissible-family or excluded melnikov premise is needed. The proof's data and step nodes supply smallness and the modified-step application. The retained edges to constants, constdef, zones, omega0, class, step, new-ham and the six proof steps point to their actual uses.

p-lipp: the hypotheses are the enclosing preparatory lemma's premises and local definitions; the sharp sup estimate remains a conclusion. f-flow gives |phi^1-id| <= M_F, while step(v) supplies parameter Lipschitz control. The flow domain U contains D_0 because s_0=s-5 sigma_P and eta_P<=1/8. Modified data identifies M_F=M_{F,P}. The new omega edge is consumed at L263: its q>=p comparison, with q=p_+=p+1/2 and the same r, gives |.|_{p,r}<=|.|_{p_+,r}, transferring Lipschitz control to the asserted norm. All five dependencies have consumer use sites L260-L263. No frozen-lam edge is needed for the bare parameter weight lambda.

## Replacement fragments

None: every in-scope record PASSes.

## Checks

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all 11 pinned source files reported `OK`.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w6
W-w6: 47 nodes, 178 edges, 70 coverage items, 0 problems
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

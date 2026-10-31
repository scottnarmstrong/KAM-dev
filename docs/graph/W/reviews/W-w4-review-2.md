# W-w4: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w4` (codex-1).
Verdict: **FAIL**.

Scope: 20 PROPOSED nodes and 19 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| bpW:w4:index | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L59-L103 |
| bpW:w4:ops | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L117-L128 |
| bpW:w4:taylor | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L132-L151 |
| bpW:w4:wave | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L184-L198; blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L200-L214 |
| stepW:w4:linimg | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308 |
| stepW:w4:deriv | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314 |
| stepW:w4:fpar | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316 |
| stepW:w4:member | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374 |
| stepW:w4:divlip | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379 |
| bpW:w4:schur | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L387-L402; blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L404-L416 |
| stepW:w4:schurrep | FAIL | L409-L413 directly identifies elements of the operator and bilinear spaces and the map Lambda of ops; add that defining dependency while retaining the Riesz SOURCE_GAP. |
| stepW:w4:solvecoef | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445 |
| stepW:w4:solvediff | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451 |
| stepW:w4:solvecomm | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457 |
| stepW:w4:solvelin | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460 |
| stepW:w4:lieder | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536 |
| bpW:w4:lemma1 | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L608-L633; blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L635-L708 |
| stepW:w4:divops | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644 |
| bpW:w4:from-w3 | FAIL | L778 and L790 directly use the shifted wave weights omega_{a,p}(j+2); the index-convention edge does not replace the frozen ellWeight symbol edge. |
| bpW:w4:lie-sec#guard | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L478 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w4:index | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L59-L103 |
| bpW:w4:ops | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L117-L128 |
| bpW:w4:taylor | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L132-L151 |
| bpW:w4:wave | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L184-L198 |
| stepW:w4:linimg | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308 |
| stepW:w4:deriv | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314 |
| stepW:w4:fpar | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316 |
| stepW:w4:member | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374 |
| stepW:w4:divlip | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379 |
| bpW:w4:schur | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L387-L402 |
| stepW:w4:schurrep | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L408-L413 |
| stepW:w4:solvecoef | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445 |
| stepW:w4:solvediff | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451 |
| stepW:w4:solvecomm | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457 |
| stepW:w4:solvelin | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460 |
| stepW:w4:lieder | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536 |
| bpW:w4:lemma1 | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L608-L633 |
| stepW:w4:divops | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644 |
| bpW:w4:from-w3 | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L774-L793 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### stepW:w4:schurrep (owner: W-w4)

L409-L413 directly identifies elements of the operator and bilinear spaces and the map Lambda of ops; add that defining dependency while retaining the Riesz SOURCE_GAP.

```text
NODE: stepW:w4:schurrep
KIND: step
TITLE: Representatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L408-L413
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L408-L413
CONTRACT_ID: stepW:w4:schurrep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:schur: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:schur (for all such d, c, mu, nu, A); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the weighted matrix of M in L is that of its representative; bounded weighted matrices are exactly elements of L; the bilinear case via Riesz on l^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight, bpW:w4:ops
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L410-L410 | the representative tau o M o kappa
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L410-L410 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L409-L413 | the spaces L and B, their matrix entries and Lambda are the objects being represented
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4+sol-delta6-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L412-L413 invokes the isometric operator representation of a complex bilinear form by Riesz on l2. No proof or permitted external in the pinned corpus supplies that representation; ext-lp states Hilbert completeness and coordinates, not Riesz representation. Keep this obligation in the step rather than assuming it.
```

### bpW:w4:from-w3 (owner: W-w4)

L778 and L790 directly use the shifted wave weights omega_{a,p}(j+2); the index-convention edge does not replace the frozen ellWeight symbol edge.

```text
NODE: bpW:w4:from-w3
KIND: claim
TITLE: From W3
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L774-L793
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L774-L793
CONTRACT_ID: bpW:w4:from-w3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the Birkhoff coordinates of Theorem bpW:w3:main; Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2))
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: z_j = w_{j+2}, zbar_j = w_{-(j+2)}, on real points u_j = q_{j+2}, v_j = p_{j+2}; ¦¦hat w¦¦^2 = ¦¦z¦¦^2 + ¦¦zbar¦¦^2 = ¦¦u¦¦^2 + ¦¦v¦¦^2 with the wave weights; (b) ¦¦hat w¦¦ <= ¦¦u¦¦ + ¦¦v¦¦ <= sqrt2 ¦¦hat w¦¦; (c) the smoothing class of W3 gives normal gradients in l^N_{a,bar p}; (d) Omega restricted to the normal part is sum du ^ dv and dz = -i H_zbar agrees with X_P(w)_l = -i sgn(l) DP(w) e_{-l}; ownership ruling: W5 owns the action-angle substitution, the domain check and the norm comparisons
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:space, bpW:w3:coords, bpW:w4:index, bpW:w3:omega, bpW:w3:hamfield-def, bpW:w4:taylor, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L775-L775 | the Birkhoff map
EDGE: bpW:w3:space | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L776-L776 | the coordinates w_l
EDGE: bpW:w3:coords | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L777-L777 | u_j = q_{j+2}, v_j = p_{j+2}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L779-L779 | the wave weights
EDGE: bpW:w3:omega | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L782-L782 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L783-L783 | X_P
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L782-L782 | the smoothing gradients required by the Taylor class
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L778-L779 | the frozen wave weights occur directly in the asserted equality of normal norms
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4+sol-delta6-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its identifications are consumed by W5 (action-angle substitution); the ownership ruling and the pointer to Remark bpW:w3:interface are administrative.
```

## Source-gap disposition

The following records faithfully expose the pinned source obligations and do not add them to SOURCE_HYPOTHESES: `stepW:w4:schurrep`. All retain `LEAN_NOTE: -`. A topology PASS does not certify their mathematics. The schurrep replacement, if present, changes only a defining dependency.

## Suspected blueprint defects

- `blueprint-W/parts/w4-homological.tex:412-413`: "with the same norm (Riesz on l2)". The isometric bilinear/operator representation is invoked without a proof or a permitted external; schurrep faithfully preserves this source obligation.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w4`: exit 0; `W-w4: 57 nodes, 161 edges, 102 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w4

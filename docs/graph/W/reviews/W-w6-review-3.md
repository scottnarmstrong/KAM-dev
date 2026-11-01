# W-w6: independent delta 7 source review

Reviewer: `sol-delta7-W-w6` (codex-1).

Verdict: **FAIL**.

Scope: 6 PROPOSED nodes and 0 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| bpW:w6:prep-step | FAIL | SOURCE_CONCLUSION still cites the now-excluded bpW:w7:melnikov(i), whereas repaired clause (i) derives the bound from zones(i). It also omits the stated onto property of D Phi_P (L229). Retain that conclusion, record the actual divisor bound, and add the direct wave(ii) dependency explicitly consumed at L235 for the weight comparison. |
| stepW:w6:p-div | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L254 |
| stepW:w6:p-lipp | FAIL | The sharp sup bound and all four added dependencies are valid. The final norm comparison at L263 also directly consumes omega (q=p_+); add that dependency rather than leaving its supplier only on upstream paths. |
| bpW:w6:freq-lip | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L300-L310; blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L311-L323 |
| stepW:w6:fl-borel | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L322 |
| bpW:w6:to-w8 | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L392-L422 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

`prep-step` and `p-div`: zones(i) needs Borel Pi and 0<alpha<=alpha_0, both already present. Negating each strict S_kl inequality on Pi minus Xi gives the non-strict lower bound. For difference modes the weight is |I-J|min(I,J)^(-1/4), with min(i,j)+2=min(I,J); the other Dirichlet weights dominate the P96-K weights. The loss condition is p+1-p_+=1/2=2 beta. No admissible-family premise or use of the excluded Melnikov corollary is required. The gap is closed; prep-step's stale transcription and missing direct comparison edge are repaired below.

`p-lipp`: the sharp sup estimate comes from f-flow, rather than the 2 M_F combined norm. The W5 flow domain U contains D_0 since s_0=s-5 sigma_P and eta_P<=1/8. In modified step data M_F=c_F^natural epsilon/(hat alpha sigma_P^(t^natural-1))=M_{F,P}. The Lipschitz property uses step(v). These four edges are genuine; the additional norm-comparison edge is given below.

`freq-lip`: the three epsilon constants are <=alpha, while theta<=theta_0 is chosen from m-dependent constants before alpha. This matches family(H1)-(H2), whose theta is not required to be <=alpha. The constants edge is a direct use at L308.

`fl-borel`: omega0 is affine on all R^2 and l has finite support, so each S_kl is Pi intersect an open sublevel set. Countability of Z and ext-borel give Pi minus Xi Borel, then convergence(i) recursively gives D_nu; the already established Lipschitz bounds provide continuity. No family admissibility is invoked to prove its own Borel premise. The new zones, omega0, ext-borel and indexdef edges are direct uses, and the old measurable edge is correctly absent.

`to-w8`: the added applicable edge is explicitly consumed at L405-L407 for every epsilon_0 in the stated interval. The source retains the same theta across the interval and states the two sharp starting-size formulas. The retained measure, shell, frequency and transport dependencies are invoked at their listed sites; the returned weak invariance has precisely the premises of transport-tori-weak. No starting-size conclusion is promoted to a hypothesis.

## Replacement fragments

### bpW:w6:prep-step (owner: W-w6)

SOURCE_CONCLUSION still cites the now-excluded bpW:w7:melnikov(i), whereas repaired clause (i) derives the bound from zones(i). It also omits the stated onto property of D Phi_P (L229). Retain that conclusion, record the actual divisor bound, and add the direct wave(ii) dependency explicitly consumed at L235 for the weight comparison.

```text
NODE: bpW:w6:prep-step
KIND: lemma
TITLE: Preparatory step; P96-K \S6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L246-L271
CONTRACT_ID: bpW:w6:prep-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: one step of Theorem bpW:w5:step in the modified case (beta = 1/4, p_+ = p + 1/2, level hat alpha) applies on Pi minus Xi and gives Phi_P : D_0 = D(s_0,r_0) -> D(s,r) symplectic, real, holomorphic, with D Phi_P mapping P^{p_+} onto itself, with (N + P) o Phi_P = N_0 + P_0 + const and the weak conjugacy, and (i) for xi in Pi minus Xi and (k,l) in Z, ¦<k,omega^0> + <l,Omega^0>¦ >= hat alpha hat w(l)/A_k by Definition bpW:w7:zones(i), giving the modified bound with beta = 1/4 for difference modes and (H_hat alpha) otherwise via the Dirichlet-to-P96-K weight comparison of bpW:w4:wave(ii); (ii) the frequency shift bounds and (bpW:w5:freq) with M_omega + M_Omega <= 2M; (iii) ¦Phi_P - id¦_{p_+,r,D_0} <= M_{F,P} and Lipschitz in xi; (iv) sup ¦X_{P_0}¦_{p_+,r_0,D_0} <= eps^flat_0 = 2 C^natural_2 eps^{4/3}(hat alpha sigma_P^{t^natural})^{-1/3} <= gamma_1 check alpha; (v) ¦X_{P_0}¦^{lambda_0}_{r_0,D_0} <= eps^flat_0 with lambda_0 = check alpha/M_0
CONSTANT_SCOPE: as in Definition bpW:w6:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w7:constdef, bpW:w7:zones, bpW:w7:omega0, bpW:w5:class, bpW:w5:step, bpW:w5:new-ham, stepW:w6:p-data, stepW:w6:p-div, stepW:w6:p-step, stepW:w6:p-lipp, stepW:w6:p-size, stepW:w6:p-gap, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L220 | s, sigma_P, gamma, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L221-L221 | (C4) alpha_0
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L222-L222 | the preparatory set Xi
EDGE: bpW:w7:omega0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | the unperturbed frequencies
EDGE: bpW:w5:class | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | S_{p+1} and the lambda-norm
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L228-L228 | W5's step (modified)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L230-L230 | (iii) weak conjugacy
EDGE: stepW:w6:p-data | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L247-L247 | proof step
EDGE: stepW:w6:p-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L250-L252 | proof step
EDGE: stepW:w6:p-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L255-L255 | proof step
EDGE: stepW:w6:p-lipp | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L260-L263 | proof step
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L264-L264 | proof step
EDGE: stepW:w6:p-gap | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L268-L268 | proof step
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L234-L235 | (ii) the Dirichlet weights dominate the P96-K weights in the stated divisor conclusion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+claude-suborch-W-gapfix+sol-delta7-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w6:p-lipp (owner: W-w6)

The sharp sup bound and all four added dependencies are valid. The final norm comparison at L263 also directly consumes omega (q=p_+); add that dependency rather than leaving its supplier only on upstream paths.

```text
NODE: stepW:w6:p-lipp
KIND: step
TITLE: Transformation
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263
CONTRACT_ID: stepW:w6:p-lipp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): ¦Phi_P - id¦_{p_+,r,D_0} <= M_F = M_{F,P} by the sharper sup estimate of Step stepW:w5:f-flow (¦phi^1 - id¦_{p_+,r} <= M_F on U containing D_0), and Phi_P is Lipschitz in xi by the Lipschitz part of Theorem bpW:w5:step(v), with ¦.¦_{p,r} <= ¦.¦_{p_+,r}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, stepW:w5:f-flow, bpW:w5:flow, bpW:w5:data, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263 | (v)
EDGE: stepW:w5:f-flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L261 | the sharper sup estimate ¦phi^1 - id¦ <= M_F
EDGE: bpW:w5:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L261-L261 | the lemma whose step is used
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L262-L262 | M_F = M_{F,P} in the modified case
EDGE: bpW:w5:omega | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L263-L263 | the comparison ¦.¦_{p,r} <= ¦.¦_{p_+,r} transfers the parameter Lipschitz property to the asserted norm
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+claude-suborch-W-gapfix+sol-delta7-W-w6
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
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w6`: exit 0; `W-w6: 47 nodes, 176 edges, 70 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w6

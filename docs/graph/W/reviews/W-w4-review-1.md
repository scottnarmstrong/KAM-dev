# W-w4: slice review 1
Reviewer: sol-review-W-W-w4
Verdict: FAIL

Source-only refutation review against the eleven files pinned by CORPUS.sha256 (all hashes matched). Read SPEC including wave 2 extraction, REVIEW-BRIEF rules 1-11, AGENTS, PLAN and DECISIONS. No implementation Lean, builds, lake, repository lint or state-changing git was used. The tables cover every packet node; PASS concerns topology and source transcription only.

Bare lambda in W5/W6 is the parameter weight. phi^t in W5 is a flow, not sineMode. Normal indices are j=J-2, and the weights stay at J. Parent proofs are represented by their child steps; a prerequisite used inside a child is not duplicated on the parent solely because its PROOF_SOURCE spans that child.

## Node table

| Node | Verdict | Evidence or reason |
|---|---|---|
| bpW:w4:ext-roots | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-roots@L43-L44; proof - |
| bpW:w4:ext-parallelogram | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-parallelogram@L45-L46; proof - |
| bpW:w4:ext-exp | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-exp@L47-L49; proof - |
| bpW:w4:ext-intparts | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-intparts@L50-L52; proof - |
| bpW:w4:index | FAIL | Missing direct edge to bpW:w0:ellap#ellWeight at L67. |
| bpW:w4:ops | FAIL | Missing direct edge to bpW:w0:ellap#ellWeight at L125. |
| bpW:w4:taylor | FAIL | Missing direct edge to bpW:w1:kam-space at L146. |
| bpW:w4:melnikov | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L157-L178; proof - |
| bpW:w4:wave | FAIL | L190-L191 restricts the finite frequency-tail constant to the case when the displayed supremum is finite; the packet drops that qualification. |
| stepW:w4:waveLip | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L201-L205; proof blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L201-L205 |
| stepW:w4:waveTail | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L206-L209; proof blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L206-L209 |
| stepW:w4:waveIdx | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L210-L213; proof blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L210-L213 |
| bpW:w4:w1-requests | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L275-L293; proof blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L275-L293 |
| bpW:w4:fourier-ops | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L295-L304; proof blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L306-L317 |
| stepW:w4:linimg | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. |
| stepW:w4:deriv | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. |
| stepW:w4:fpar | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. |
| bpW:w4:lattice | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L320-L335; proof blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L337-L355 |
| stepW:w4:count | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:count@L338-L340; proof blueprint-W/parts/w4-homological.tex#stepW:w4:count@L338-L340 |
| stepW:w4:coth | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L341-L343; proof blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L341-L343 |
| stepW:w4:wsum | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L344-L346; proof blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L344-L346 |
| stepW:w4:bw | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L347-L354; proof blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L347-L354 |
| bpW:w4:divisors | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L361-L367; proof blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L369-L380 |
| stepW:w4:member | FAIL | Missing direct edge to bpW:w4:melnikov at L372. |
| stepW:w4:divlip | FAIL | Missing direct edge to bpW:w4:melnikov at L377. |
| bpW:w4:schur | FAIL | Missing direct edge to bpW:w0:ellap#ellWeight at L393. |
| stepW:w4:schurtr | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L405-L407; proof blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L405-L407 |
| stepW:w4:schurrep | FAIL | SOURCE_GAP: L412-L413 invokes the isometric operator representation of a complex bilinear form by Riesz on l2. No proof or permitted external in the pinned corpus supplies that representation; ext-lp states Hilbert completeness and coordinates, not Riesz representation. Keep this obligation in the step rather than assuming it. Missing direct edge to bpW:w0:ellap#ellWeight at L410. |
| stepW:w4:schurdiag | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L414-L415; proof blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L414-L415 |
| bpW:w4:solve | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L421-L439; proof blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L441-L461 |
| stepW:w4:solvecoef | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. |
| stepW:w4:solvediff | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. |
| stepW:w4:solvecomm | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. The boundedness premise for the derivative data in solve(iii) must remain explicit in this step. |
| stepW:w4:solvelin | FAIL | The appended m > 0 identifies the enclosing Fourier norm majorant m with the wave mass and introduces a positivity restriction absent from this local statement. Missing direct edge to bpW:w3:ext-tsum at L459. |
| bpW:w4:lie | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L480-L508; proof blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L510-L537 |
| stepW:w4:liebd | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L511-L515; proof blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L511-L515 |
| stepW:w4:liebr | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L516-L519; proof blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L516-L519 |
| stepW:w4:liecoef | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L520-L527; proof blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L520-L527 |
| stepW:w4:lieder | FAIL | Missing direct edge to bpW:w3:ext-multilinear at L531. Missing direct edge to bpW:w0:ellap#ellWeight at L529. |
| bpW:w4:extract | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L547-L551; proof blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L553-L559 |
| bpW:w4:components | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L563-L573; proof blueprint-W/parts/w4-homological.tex#bpW:w4:components@L575-L601 |
| stepW:w4:testpts | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L576-L581; proof blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L576-L581 |
| stepW:w4:first | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:first@L582-L586; proof blueprint-W/parts/w4-homological.tex#stepW:w4:first@L582-L586 |
| stepW:w4:angle | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L587-L595; proof blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L587-L595 |
| stepW:w4:polar | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L596-L600; proof blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L596-L600 |
| bpW:w4:lemma1 | FAIL | Missing direct edge to bpW:w4:index at L609. |
| stepW:w4:divops | FAIL | The L643 mention checks the hypotheses of solve; it does not consume its conclusion (SPEC Edges). |
| stepW:w4:class | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L645-L649; proof blueprint-W/parts/w4-homological.tex#stepW:w4:class@L645-L649 |
| stepW:w4:equation | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L650-L659; proof blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L650-L659 |
| stepW:w4:Fcomp | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L660-L673; proof blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L660-L673 |
| stepW:w4:assembly | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L674-L686; proof blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L674-L686 |
| stepW:w4:lip | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L687-L692; proof blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L687-L692 |
| stepW:w4:Nhat | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L693-L699; proof blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L693-L699 |
| stepW:w4:real | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:real@L700-L707; proof blueprint-W/parts/w4-homological.tex#stepW:w4:real@L700-L707 |
| bpW:w4:lemma2 | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L721-L729; proof blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L731-L735 |
| bpW:w4:from-w3 | FAIL | Missing direct edge to bpW:w4:taylor at L782. |
| bpW:w4:lie-sec#guard | FAIL | Missing direct edge to bpW:w0:ellap#ellWeight at L475. |

## Coverage

all other coverage items PASS

Every labelled unit and unlabelled prose item was checked against the raw slice. The existing mappings remain valid after the node replacements. SOURCE_GAP findings above are carried in their existing substantive step/claim nodes; their existing inventory items therefore still cover them.

Reachability exclusions k0/k0one/k0diff PASS: searching W4-W8 found k0 only in its own excluded summary and the ledger; the downstream zero-mode proof is W7 separation, not this lemma. The counterexample, comparisons and interface pointers remain excluded as provenance/administration.

## Complete replacement blocks

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
DEPS: bpW:w1:transport, bpW:w1:tails, bpW:w0:z, bpW:w1:kam-space, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L69-L69 | weighted coordinates at weight (a,q)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L70-L70 | the convention for normal-mode sequences (entries J = 1,2 zero)
EDGE: bpW:w0:z | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L86-L86 | the W0 convention z = (q + ip)/sqrt2
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L93-L93 | the domain D(s,r) of Definition bpW:w1:kam-space
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L67-L67 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The pointer to Lemma bpW:w4:lie(iv) (guard (G)) at L61-L62 and to Remark bpW:w4:weights are forward pointers; not edges.
```

```text
NODE: bpW:w4:ops
KIND: definition
TITLE: Normal operators and their norms
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L117-L128
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ops
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2))
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines L (bounded linear maps l^N_{a,p} -> l^N_{a,bar p}, operator norm), matrices M_ij = <M e_j, e_i>_0, transpose and symmetry; the bilinear norm and the space B of bounded bilinear forms; Lambda : L -> B, Lambda M(z,z') = <Mz,z'>_0 with ¦¦Lambda M¦¦_bil <= ¦¦M¦¦; the dual norm ¦¦c¦¦_* and the space l^N_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L118-L118 | the spaces l^N_{a,q}, the pairing and (bpW:w4:pairing)
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L125-L125 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w4:taylor
KIND: definition
TITLE: Taylor Hamiltonians
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L132-L151
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s > 0; r > 0 for the field norm
SOURCE_QUANTIFIERS: s, r
SOURCE_CONCLUSION: defines the class T_s of R = a + <b,y> + <c^+,z>_0 + <c^-,zbar>_0 + <Pz,z>_0 + <Qz,zbar>_0 + <P'zbar,zbar>_0 (bpW:w4:R) with components a, b, c^+-, P, P', Q, Q^T complex differentiable, 1-periodic and bounded on T_s, P, P' symmetric; the derivatives R_y, R_theta, R_z, R_zbar, R_u, R_v; the field X_R = (R_y/(2pi), -R_theta/(2pi), R_v, -R_u) and ¦X_R¦_r; reality; the mean [g] = hat g_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w4:ops, bpW:w1:kam-space
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L139-L139 | the spaces and the coordinates z, zbar, u, v
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L138-L138 | the operator space L
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L146-L146 | the field norm is identified with this domain/norm definition
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w4:wave
KIND: lemma
TITLE: The wave frequencies
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L184-L198
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L200-L214
CONTRACT_ID: bpW:w4:wave
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every Pi subset R^2
SOURCE_CONCLUSION: (i) (bpW:w4:freq) holds with M_omega = 9/(8 pi lambda_1^2) + 3/(2 pi lambda_1 lambda_2), M_Omega = (3/(2pi))(1/lambda_1 + 1/lambda_2), M_0 = m/2 + (3/(2pi)) sup_Pi ¦<b,xi>¦ when that supremum is finite; P96-K Assumption B holds with d = 1, delta = -1, bar Omega_j = j + 2; (ii) <l> <= <l>^w <= 3<l> for 1 <= ¦l¦ <= 2 unless sum l_j = 0 (then equal), so (H_alpha) with <l>^w implies (H_alpha), and (H_alpha) implies the <l>^w-conditions with alpha/3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w4:melnikov, stepW:w4:waveLip, stepW:w4:waveTail, stepW:w4:waveIdx, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L187-L187 | the matrix A
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L189-L189 | (bpW:w4:freq) and (H_alpha)
EDGE: stepW:w4:waveLip | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L201-L201 | proof step
EDGE: stepW:w4:waveTail | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L206-L206 | proof step
EDGE: stepW:w4:waveIdx | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L210-L210 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L185-L185 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:linimg
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308
CONTRACT_ID: stepW:w4:linimg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta)
SOURCE_CONCLUSION: (i): Lambda commutes with the integral defining hat f_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ext-intparts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L308-L308 | continuous linear maps commute with Bochner integrals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314
CONTRACT_ID: stepW:w4:deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: i, k
SOURCE_CONCLUSION: (ii): d_{theta_i} f complex differentiable and periodic; (d_{theta_i} f)^_k = 2 pi i k_i hat f_k by periodic integration by parts and Fubini
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar, bpW:w4:ext-intparts, bpW:w1:ext-rect
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L310-L310 | derivatives of holomorphic maps (in theta_i)
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L313-L313 | periodic integration by parts
EDGE: bpW:w1:ext-rect | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L314-L314 | Fubini for continuous functions on [0,1]^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:fpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316
CONTRACT_ID: stepW:w4:fpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: xi, zeta
SOURCE_CONCLUSION: (iii): (F1) applied to f(.,xi) - f(.,zeta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L316-L316 | (F1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:member
KIND: step
TITLE: Membership
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374
CONTRACT_ID: stepW:w4:member
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:divisors: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); (H_alpha)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:divisors (for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2); within the step: divisors; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each divisor is <k,omega> + <l,Omega> with (k,l) in Z and <l> = w; (H_alpha) gives the lower bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:melnikov
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#stepW:w4:member@L372-L372 | the exclusions defining the divisors and Z are used to prove membership
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:divlip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379
CONTRACT_ID: stepW:w4:divlip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:divisors: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); (H_alpha)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:divisors (for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦delta(xi) - delta(zeta)¦ <= (¦k¦_1 + 2) M ¦xi - zeta¦; dividing by ¦delta(xi) delta(zeta)¦ gives the Lipschitz bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:member, bpW:w4:melnikov
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:member | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L378-L378 | the lower bound alpha w/A_k
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L377-L377 | direct use of the frequency Lipschitz hypothesis (freq)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w4:schur
KIND: lemma
TITLE: Hadamard division of operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L387-L402
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L404-L416
CONTRACT_ID: bpW:w4:schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for all such d, c, mu, nu, A
SOURCE_CONCLUSION: (mu_i d_ij A_ij nu_j) is bounded with norm <= c K_S N_A; (i) H_d : M -> (d_ij M_ij) is bounded L -> L with norm <= c K_S and H_d(M)^T = H_{d^T}(M^T); (ii) the same on bilinear forms B -> B, Lambda o H_d = H_d o Lambda; (iii) for diagonal d the bound is c, in particular (i+2)¦M_ii¦ <= ¦¦M¦¦ for M in L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ops, stepW:w4:schurtr, stepW:w4:schurrep, stepW:w4:schurdiag, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L394-L394 | L, B, Lambda
EDGE: stepW:w4:schurtr | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L405-L405 | proof step
EDGE: stepW:w4:schurrep | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L408-L408 | proof step
EDGE: stepW:w4:schurdiag | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L414-L414 | proof step
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L393-L393 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

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
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L410-L410 | the representative tau o M o kappa
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L410-L410 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L412-L413 invokes the isometric operator representation of a complex bilinear form by Riesz on l2. No proof or permitted external in the pinned corpus supplies that representation; ext-lp states Hilbert completeness and coordinates, not Riesz representation. Keep this obligation in the step rather than assuming it.
```

```text
NODE: stepW:w4:solvecoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445
CONTRACT_ID: stepW:w4:solvecoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: k
SOURCE_CONCLUSION: (i): sum ¦¦T_k hat f_k¦¦ e^{2 pi ¦k¦_1 (s-sigma)} <= kappa m B^W_sigma/alpha and (F2) with s' = s - sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L443-L443 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L445-L445 | (iv)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:solvediff
KIND: step
TITLE: Differences
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451
CONTRACT_ID: stepW:w4:solvediff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: xi, zeta
SOURCE_CONCLUSION: (ii): the coefficient differences are bounded and summed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L448-L448 | (iii)
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L448-L448 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L450-L450 | B^W_sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:solvecomm
KIND: step
TITLE: Commutation
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457
CONTRACT_ID: stepW:w4:solvecomm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}; for part (iii), partial_{theta_i} f is bounded on T_s (L433)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: i
SOURCE_CONCLUSION: (iii): termwise differentiation gives d_{theta_i} S f = S(d_{theta_i} f)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, stepW:w4:solvecoef, bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L453-L453 | (ii)
EDGE: stepW:w4:solvecoef | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L454-L454 | summability
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L456-L456 | termwise differentiation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:solvelin
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460
CONTRACT_ID: stepW:w4:solvelin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data)
SOURCE_CONCLUSION: (iv): Lambda commutes with absolutely convergent sums
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L460-L460 | (i)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L459-L459 | continuous linear maps commute with norm-absolutely convergent sums
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:lieder
KIND: step
TITLE: The guarded derivative
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536
CONTRACT_ID: stepW:w4:lieder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lie: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lie (for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): under (G) N_Omega is bounded bilinear, N a continuous polynomial with the displayed derivative; DN . X_F = <<N,F>>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie-sec#guard, bpW:w1:embed, bpW:w4:index, stepW:w4:liebr, bpW:w3:ext-multilinear, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L529-L529 | (G)
EDGE: bpW:w1:embed | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L533-L533 | l^N_{a,bar p} subset l^N_{a,p}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L532-L532 | (bpW:w4:hameq): the components of X_F
EDGE: stepW:w4:liebr | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L536-L536 | (ii)
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L531-L531 | differentiate the bounded bilinear polynomial and its linear part
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L529-L529 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w4:lemma1
KIND: theorem
TITLE: P96-K Lemma~1 for the wave setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L608-L633
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L635-L708
CONTRACT_ID: bpW:w4:lemma1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every xi in Pi
SOURCE_CONCLUSION: (i) F in T_{s-sigma} with hat a_{F,0} = 0, hat b_{F,0} = 0, (hat Q_{F,0})_jj = 0; real if R is real (hat omega in R^2, hat Omega_j in R); (ii) L_N F + hat N = R - hat a_0, equivalently R + <<N,F>> = hat N + hat a_0, and under (G) (in particular a = p = 1) R + DN . X_F = hat N + hat a_0; (iii) ¦X_F¦_r <= C_1 B eps/alpha and ¦X_{F(xi)} - X_{F(zeta)}¦_r <= (C_1 B/alpha)(eps^L + 2M eps/alpha)¦xi - zeta¦ on D(s-sigma,r); (iv) ¦hat omega¦ <= 2 pi eps, sup (j+2)¦hat Omega_j¦ <= eps (likewise for differences), ¦X_{hat N}¦_r <= 2 eps and the Lipschitz analogue on D(s,r)
CONSTANT_SCOPE: C_1 = 7 + 10 K_S < 36 absolute; B = B^W_sigma depends on tau, sigma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, bpW:w4:melnikov, bpW:w4:lie, bpW:w4:lie-sec#guard, bpW:w4:lattice, bpW:w4:schur, stepW:w4:divops, stepW:w4:class, stepW:w4:equation, stepW:w4:Fcomp, stepW:w4:assembly, stepW:w4:lip, stepW:w4:Nhat, stepW:w4:real, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L611-L611 | the class T_s
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L614-L614 | divisors and (H_alpha)
EDGE: bpW:w4:lie | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L624-L624 | L_N and the weak bracket
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L626-L626 | the guard (G)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L620-L620 | B^W_sigma
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L620-L620 | K_S
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L636-L636 | proof step
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L645-L645 | proof step
EDGE: stepW:w4:equation | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L650-L650 | proof step
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L660-L660 | proof step
EDGE: stepW:w4:assembly | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L674-L674 | proof step
EDGE: stepW:w4:lip | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L687-L687 | proof step
EDGE: stepW:w4:Nhat | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L693-L693 | proof step
EDGE: stepW:w4:real | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L700-L700 | proof step
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L609-L609 | the theorem explicitly assumes this convention
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w4:divops
KIND: step
TITLE: Division operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644
CONTRACT_ID: stepW:w4:divops
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: k, xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the division operators T_k satisfy the hypotheses of Lemma bpW:w4:solve with kappa = 1 (a, b, c^+-) and kappa = K_S (P, Q, Q^T, P')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:divisors, bpW:w4:schur, bpW:w1:multiplier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:divisors | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L640-L640 | divisor bounds
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L642-L642 | Hadamard maps
EDGE: bpW:w1:multiplier | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L643-L643 | diagonal multipliers
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

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
DEPS: bpW:w3:main, bpW:w3:space, bpW:w3:coords, bpW:w4:index, bpW:w3:omega, bpW:w3:hamfield-def, bpW:w4:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L775-L775 | the Birkhoff map
EDGE: bpW:w3:space | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L776-L776 | the coordinates w_l
EDGE: bpW:w3:coords | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L777-L777 | u_j = q_{j+2}, v_j = p_{j+2}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L779-L779 | the wave weights
EDGE: bpW:w3:omega | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L782-L782 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L783-L783 | X_P
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L782-L782 | the smoothing gradients required by the Taylor class
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its identifications are consumed by W5 (action-angle substitution); the ownership ruling and the pointer to Remark bpW:w3:interface are administrative.
```

```text
NODE: bpW:w4:lie-sec#guard
KIND: definition
TITLE: The guard (G) and the weak-bracket setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L478
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L478
CONTRACT_ID: bpW:w4:lie-sec#guard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega)
SOURCE_QUANTIFIERS: a, p
SOURCE_CONCLUSION: defines the formal normal form N = <omega(xi),y> + sum Omega_j z_j zbar_j and the guard (G) gamma_{a,p} = sup_j (j+2)/omega_{a,p}(j+2)^2 < infinity (bpW:w4:guard); records that the series of N need not converge for a = p = 0, that (G) holds iff a > 0 or p >= 1/2, and gamma_{1,1} = e^{-6}/3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w4:melnikov, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L474-L474 | the wave weights omega_{a,p}(j+2)
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L469 | omega, Omega
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L475-L475 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L469-L478 with the display label bpW:w4:guard (SPEC section-data rule); consumed by Lemma bpW:w4:lie(iv) and Theorem bpW:w4:lemma1(ii).
```

## Validation

- `sha256sum -c docs/graph/W/CORPUS.sha256`: all eleven source files OK.
- Permitted `inp_depgraph_slice_check.py docs/graph/W/packets W-w4`: 57 nodes, 148 edges, 102 coverage items, 0 problems (original packets).
- Review-format check: 57 unique packet-node verdicts, 20 complete FAIL replacements; exact required fields; DEPS/EDGE agreement; existing edge targets; source ranges valid; no trailing whitespace.
- Combined read-only packet overlay with all four reports: no dependency cycles. Packets were not modified.

## Suspected blueprint errata and source gaps

1. `w4-homological.tex:412-413`: "representing beta, with the same norm (Riesz on l2)" invokes an unlisted standard theorem without a blueprint proof. This is a source-input gap, recorded in `stepW:w4:schurrep`, not permission to add a new external leaf.
The P96-K issues already quoted in L826-L831 remain paper errata/provenance, separately from blueprint defects. No paper was opened or independently re-audited.

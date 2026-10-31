# W-w3: Batch B delta review 5

Reviewer: sol-delta5-W-w3. Verdict: **FAIL**.

Delta 5 scope: four PROPOSED weak-transport nodes and eight PROPOSED coverage items only, plus the W6 consumer touched by the newly found use. Read w3-birkhoff.tex L771-L778,L810-L920 and W1 diag/embedding/space statements. The weak equation is upgraded pointwise using the inverse multiplier, without assuming differentiability into W+. At a=0 the inherited transport result uses T(Q,Q,Q); its G_q identification remains restricted to a>0, as in transport-tori L815-L816. The W8 consumer has a=p=1. The direct citation of class-remark in W6 L374 is a use under rule 11, even though the fact is also proved by flow.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes 2f59142072d9d4cca158d947ac37395929e24c06dc437908048cb636b0d46f4a; coverage e6a45ae26679133c09f05ffc9cb80d204cb8849ac8a8310613dbdac626081cc1.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w3:transport-tori-weak | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L844-L866 |
| stepW:w3:wk-lin | FAIL | The operator bound uses (1+m) and m > 0 itself; the direct positive-carrier dependency is missing. |
| stepW:w3:wk-reg | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858 |
| stepW:w3:wk-transport | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865 |
| stepW:w6:t-an | FAIL | Rule 11: the proof cites the regularity remark for Gamma's analyticity; replacing that use by a different supplier does not justify excluding the cited claim. (Touched cross-slice consumer.) |
| bpW:w3:class-remark | FAIL | Missing node; source re-read: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778. Complete addition below. |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w3:class-remark | FAIL | W6 t-an cites this claim inside its proof (w6-iteration.tex L374), so exclusion violates rule 11. |
| bpW:w3:interface | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface@L872-L920 |
| bpW:w3:transport-tori-weak | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842 |
| stepW:w3:wk-lin | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849 |
| stepW:w3:wk-reg | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858 |
| stepW:w3:wk-transport | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865 |
| w3-birkhoff:prose-L826-L829 | PASS | blueprint-W/parts/w3-birkhoff.tex#prose@L826-L829 |
| w3-birkhoff:source-L867 | PASS | blueprint-W/parts/w3-birkhoff.tex#source@L867-L868 |

all other coverage items PASS within the assigned PROPOSED delta scope; already REVIEWED records outside that scope were not reopened.

Assigned delta records checked: 4 nodes and 8 coverage items. Cross-slice replacement blocks above are limited to consumers touched by the failed exclusions.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: stepW:w3:wk-lin
KIND: step
TITLE: The linear field on W
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849
CONTRACT_ID: stepW:w3:wk-lin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:transport-tori-weak: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; for w in W, X_Lambda(w) = (-i lambda'_l w_l)_{l != 0} in W_{a,p-1}; nu in R^2; Psi : R^2 -> B_{rho_1} differentiable as a map into W with D Psi(theta) nu = X_Lambda(Psi(theta)) + X_{bar G}(Psi(theta)) + X_{G^nor}(Psi(theta)) + X_K(Psi(theta)) in W_{a,p-1} for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:transport-tori-weak (all such nu, Psi; every theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_Lambda : W -> W_{a,p-1} is bounded with norm <= sqrt(1+m) and agrees with Lemma bpW:w3:Lambda on W+; the other three fields take values in W+ subset W subset W_{a,p-1} with norm-one inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:diag, bpW:w3:Lambda, bpW:w3:main, bpW:w1:embed, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:diag | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L846-L846 | (i) with p-1 in place of p and r = 1
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L848-L848 | agreement on W+
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L849-L849 | (ii), (iii): the fields of bar G, G^nor, K take values in W+
EDGE: bpW:w1:embed | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L849-L849 | norm-one inclusions
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L847-L847 | m > 0 in the sqrt(1+m) multiplier bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-w2+sol-delta5-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w6:t-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
CONTRACT_ID: stepW:w6:t-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) real analyticity via Corollary bpW:w1:torus-analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:coords, bpW:w1:torus-analytic, bpW:w3:class-remark
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L374 | (i) Gamma analytic, (iv) real
EDGE: bpW:w3:coords | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L375-L375 | Z
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L376-L376 | real-analytic tori from complex strips
EDGE: bpW:w3:class-remark | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L374 | the regularity claim explicitly cited for Gamma analytic, hence holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta5-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The cited regularity remark is retained as bpW:w3:class-remark. The flow edge remains a direct use at L376 for reality.
```

```text
NODE: bpW:w3:class-remark
KIND: claim
TITLE: Regularity class used by the W6 torus proof
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:class-remark
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data: m > 0, a >= 0, p >= 1/2, J = {1,2}; the normal-form objects Gamma,K,X_K
SOURCE_QUANTIFIERS: on the complex ball B_{rho_1}, and on its real form as stated
SOURCE_CONCLUSION: Gamma,K,X_K are complex analytic on B_{rho_1}; Gamma and K arise from compositions of power series, X_{K_1} from composition and operator inversion, X_{K_2} from Yseries; their real restrictions are real analytic; analyticity implies holomorphy in the sense of W1, so W1 Cauchy estimates apply
CONSTANT_SCOPE: rho_1 and the preceding constants retain their W3 dependence on m,a,p; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:main, bpW:w3:Yseries, bpW:w3:real-restrict, bpW:w1:holomorphic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L773 | Gamma has its analytic power series
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L774 | K and X_K are analytic
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | the explicit series for X_{K_2}
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | real restrictions are analytic
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L776-L777 | the definition of holomorphy to which analyticity is applied
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-delta5-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Restored because stepW:w6:t-an cites this fact at w6-iteration.tex L374 inside a proof. Source topology only; no Lean proof status inferred.
```

```text
ITEM: bpW:w3:class-remark
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
DISPOSITION: NODE bpW:w3:class-remark
REASON: the regularity claim is directly cited inside stepW:w6:t-an; retained with dependencies on its W3 suppliers
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2+sol-delta5-W-w3
REVIEWER: -
```

## W4-W8 exclusion search

All reachability exclusions in the wave-2 SPEC were searched by label and mathematical content: reconstruction#rescaling; pde-equiv/time/ident/converse; formal-birkhoff; duffing/ext-lindstedt; w4:k0/k0one/k0diff. No downstream statement/proof use was found. W4 k0 is mentioned only in its own proof, its source note, the excluded melnikov-check remark and the excluded interface summary; downstream k=0 bounds use W7 sep.

The rechecked remark uses divide as follows: w1:kam-conventions is used in W4 index L87; w3:class-remark is used in W6 t-an L374 (FAIL proposals in their owning delta reports). w3:interface appears in inputs/section prose, source notes and excluded remarks; w0n:kappa appears in W7 source L207 and excluded interface L783; wh:weakenings appears in source notes W6 L165/W8 L601 and outline W8 L34. operator-fourier, w2:hyp, w2:constants, w2:hidden and wh:reading have no W4-W8 citations.

## Suspected blueprint errata and deviations

No new suspected blueprint defect. The regularity remark is a true source claim consumed by W6; its exclusion is a graph defect. No new Lean theorem or source proof has been supplied.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.

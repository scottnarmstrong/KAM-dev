# W-w8b: slice review 1

Reviewer: sol-review-W-w8b. Verdict: **FAIL**.

Read w8-assembly.tex L411-L650 in full, plus the earlier shell constructions, W2 uniqueness/orbit inputs, W3 real change and W7 density/Diophantine inputs. Checked energy cancellation in weighted coordinates, both time directions of Gronwall, winding, separation of shells, common C in clauses (3)/(5), and the frozen order of witnesses. Only genuine indexed lam/frozen lam uses require symbol edges; phase phi does not.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes f90782d6a523c0eb6fcdb5928b6e3992dc607dbc0db54cd1d47959ccd212f9cd; coverage 867e604667c467600ed336d0e7f01b75616d1a0906d5337d94ff676f3aa28c89.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w8:patch | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L413-L420 |
| bpW:w8:patch-local | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L424-L428; blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L429-L434 |
| stepW:w8:pl-dis | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431; blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431 |
| stepW:w8:pl-id | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433; blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433 |
| bpW:w8:patch-cont | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L447-L450; blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L451-L460 |
| stepW:w8:pc-borel | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452; blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 |
| stepW:w8:pc-incl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454; blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454 |
| stepW:w8:pc-nu | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456; blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456 |
| stepW:w8:pc-K | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459; blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459 |
| bpW:w8:unique | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L465-L467; blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L468-L487 |
| stepW:w8:u-raw | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473; blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473 |
| stepW:w8:u-reg | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474; blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474 |
| stepW:w8:u-energy | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480; blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480 |
| stepW:w8:u-ineq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483; blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483 |
| stepW:w8:u-gron | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486; blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486 |
| bpW:w8:winding | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L491-L494; blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L495-L500 |
| stepW:w8:w-mod | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497; blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497 |
| stepW:w8:w-const | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498; blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498 |
| stepW:w8:w-rate | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499; blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499 |
| bpW:w8:nu-injective | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L503-L505; blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L506-L514 |
| stepW:w8:ni-same | FAIL | The proof step drops the enclosing implication premise nu(I) = nu(I') from its context. |
| stepW:w8:ni-diff | FAIL | The proof step drops the enclosing implication premise nu(I) = nu(I') from its context. |
| bpW:w8:injective | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L517-L520; blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L521-L538 |
| stepW:w8:in-orbit | FAIL | The proof step drops the enclosing implication premise K_I(theta) = K_{I'}(theta') from its context. |
| stepW:w8:in-birk | FAIL | The proof step drops the enclosing implication premise K_I(theta) = K_{I'}(theta') from its context. |
| stepW:w8:in-freq | FAIL | The proof step drops the enclosing implication premise K_I(theta) = K_{I'}(theta') from its context. |
| stepW:w8:in-act | FAIL | The proof step drops the enclosing implication premise K_I(theta) = K_{I'}(theta') from its context. |
| stepW:w8:in-ang | FAIL | The proof step drops the enclosing implication premise K_I(theta) = K_{I'}(theta') from its context. |
| bpW:w8:nlw2-proof | FAIL | The proof explicitly uses frozen lam and IsDiophantine but has neither direct symbol edge. |
| stepW:w8:p-pos | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557 |
| stepW:w8:p-etapos | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558 |
| stepW:w8:p-etalim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559 |
| stepW:w8:p-meas | FAIL | The text directly cites pc-borel as well as patch-cont; its named-step edge is missing. |
| stepW:w8:p-incl | FAIL | The text directly cites pc-incl as well as patch-cont; its named-step edge is missing. |
| stepW:w8:p-nucont | FAIL | The text directly cites pc-nu as well as patch-cont; its named-step edge is missing. |
| stepW:w8:p-Kcont | FAIL | The text directly cites pc-K as well as patch-cont; its named-step edge is missing. |
| stepW:w8:p-dens | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574 |
| stepW:w8:p-dioph | FAIL | The displayed frozen IsDiophantine assertion needs its anchor edge. |
| stepW:w8:p-lim | FAIL | lam occurs explicitly in the target limit; the convergence alpha_n -> 0 also consumes the shell definition. |
| stepW:w8:p-emb | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584 |
| stepW:w8:p-close | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588 |
| stepW:w8:p-size | FAIL | The proof transfers a shell K estimate to the patched K, without the patch-local dependency. |
| stepW:w8:p-inv | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592 |
| stepW:w8:p-pde | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595 |
| stepW:w8:p-inj | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596 |
| stepW:w8:p-assembly | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598; blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598 |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w8:patch | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L413-L420 |
| bpW:w8:patch-local | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L424-L428 |
| stepW:w8:pl-dis | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431 |
| stepW:w8:pl-id | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433 |
| bpW:w8:boundaries | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L438-L445 |
| bpW:w8:patch-cont | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L447-L450 |
| stepW:w8:pc-borel | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 |
| stepW:w8:pc-incl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454 |
| stepW:w8:pc-nu | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456 |
| stepW:w8:pc-K | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459 |
| bpW:w8:unique | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L465-L467 |
| stepW:w8:u-raw | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473 |
| stepW:w8:u-reg | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474 |
| stepW:w8:u-energy | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480 |
| stepW:w8:u-ineq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483 |
| stepW:w8:u-gron | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486 |
| bpW:w8:winding | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L491-L494 |
| stepW:w8:w-mod | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497 |
| stepW:w8:w-const | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498 |
| stepW:w8:w-rate | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499 |
| bpW:w8:nu-injective | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L503-L505 |
| stepW:w8:ni-same | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 |
| stepW:w8:ni-diff | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513 |
| bpW:w8:injective | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L517-L520 |
| stepW:w8:in-orbit | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527 |
| stepW:w8:in-birk | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530 |
| stepW:w8:in-freq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534 |
| stepW:w8:in-act | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 |
| stepW:w8:in-ang | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537 |
| bpW:w8:nlw2-proof | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L547-L551 |
| stepW:w8:p-pos | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557 |
| stepW:w8:p-etapos | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558 |
| stepW:w8:p-etalim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559 |
| stepW:w8:p-meas | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 |
| stepW:w8:p-incl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562 |
| stepW:w8:p-nucont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 |
| stepW:w8:p-Kcont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565 |
| stepW:w8:p-dens | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574 |
| stepW:w8:p-dioph | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578 |
| stepW:w8:p-lim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582 |
| stepW:w8:p-emb | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584 |
| stepW:w8:p-close | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588 |
| stepW:w8:p-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590 |
| stepW:w8:p-inv | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592 |
| stepW:w8:p-pde | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595 |
| stepW:w8:p-inj | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596 |
| stepW:w8:p-assembly | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598 |
| bpW:w8:deviations | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L628-L650 |
| heading:bpW:w8:patch-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-sec@L411-L411 |
| heading:bpW:w8:inj-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:inj-sec@L463-L463 |
| heading:bpW:w8:proof-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:proof-sec@L545-L545 |
| heading:bpW:w8:check | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:check@L626-L626 |
| w8-assembly:source-L421 | PASS | blueprint-W/parts/w8-assembly.tex#source@L421-L421 |
| w8-assembly:source-L435 | PASS | blueprint-W/parts/w8-assembly.tex#source@L435-L435 |
| w8-assembly:source-L461 | PASS | blueprint-W/parts/w8-assembly.tex#source@L461-L461 |
| w8-assembly:source-L488 | PASS | blueprint-W/parts/w8-assembly.tex#source@L488-L488 |
| w8-assembly:source-L501 | PASS | blueprint-W/parts/w8-assembly.tex#source@L501-L501 |
| w8-assembly:source-L515 | PASS | blueprint-W/parts/w8-assembly.tex#source@L515-L515 |
| w8-assembly:source-L539 | PASS | blueprint-W/parts/w8-assembly.tex#source@L539-L539 |
| w8-assembly:source-L600 | PASS | blueprint-W/parts/w8-assembly.tex#source@L600-L600 |
| w8-assembly:prose-L603-L624 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L603-L624 |

all other coverage items PASS.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: bpW:w8:nlw2-proof
KIND: theorem
TITLE: Proof of W-NLW2
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L547-L551
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L552-L599
CONTRACT_ID: bpW:w8:nlw2-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: Theorem bpW:wh:nlw2 (KAM.Wave.nlw2) holds exactly as frozen: the witnesses r_0, C, tau, eta of Definition bpW:w8:const and Gamma, nu, K of Definition bpW:w8:patch, chosen in this order and depending on m only, satisfy every conjunct
CONSTANT_SCOPE: all witnesses depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w8:patch, bpW:w8:shells, bpW:w8:shell-iter, stepW:w8:p-pos, stepW:w8:p-etapos, stepW:w8:p-etalim, stepW:w8:p-meas, stepW:w8:p-incl, stepW:w8:p-nucont, stepW:w8:p-Kcont, stepW:w8:p-dens, stepW:w8:p-dioph, stepW:w8:p-lim, stepW:w8:p-emb, stepW:w8:p-close, stepW:w8:p-size, stepW:w8:p-inv, stepW:w8:p-pde, stepW:w8:p-inj, stepW:w8:p-assembly, bpW:w0:periodone#linearTorus, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:w0:basis#lam, bpW:wh:dioph#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | r_0, C, tau, eta
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | Gamma, nu, K
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | the shell data
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | the shell iteration
EDGE: stepW:w8:p-pos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L556-L556 | proof step
EDGE: stepW:w8:p-etapos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L558-L558 | proof step
EDGE: stepW:w8:p-etalim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L559-L559 | proof step
EDGE: stepW:w8:p-meas | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L560-L560 | proof step
EDGE: stepW:w8:p-incl | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L561-L561 | proof step
EDGE: stepW:w8:p-nucont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L563-L563 | proof step
EDGE: stepW:w8:p-Kcont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L564-L564 | proof step
EDGE: stepW:w8:p-dens | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L566-L566 | proof step
EDGE: stepW:w8:p-dioph | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L575-L575 | proof step
EDGE: stepW:w8:p-lim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L579-L579 | proof step
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L583-L583 | proof step
EDGE: stepW:w8:p-close | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L585-L585 | proof step
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L589-L589 | proof step
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L591-L591 | proof step
EDGE: stepW:w8:p-pde | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L593-L593 | proof step
EDGE: stepW:w8:p-inj | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L596-L596 | proof step
EDGE: stepW:w8:p-assembly | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L597-L597 | proof step
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L585-L585 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L584-L584 | the frozen IsAnalyticTorusEmbedding occurs directly here
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L582-L582 | the frozen frequency-limit vector uses lam
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L577-L577 | the frozen IsDiophantine conclusion in clause (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: [pre-extract: dropped reference to bpW:wh:nlw2, which part w8-assembly proves or sets up]
```

```text
NODE: stepW:w8:p-dioph
KIND: step
TITLE: Clause (2), Diophantine
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578
CONTRACT_ID: stepW:w8:p-dioph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (2): KAM.IsDiophantine gamma_I 24 (nu I) with gamma_I = check alpha_n/(8 pi) > 0
CONSTANT_SCOPE: gamma_I = check alpha_n/(8 pi) is chosen after I in its unique shell; tau = 24 was fixed after m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w7:dioph, bpW:w8:patch-local, bpW:w7:dioph-use, bpW:wh:dioph#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L575 | (iii)
EDGE: bpW:w7:dioph | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L576-L576 | Diophantine conversion
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L577-L577 | nu(I) = omega^(n)_*(I)/(2 pi)
EDGE: bpW:w7:dioph-use | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L578-L578 | gamma chosen after I
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L577-L577 | IsDiophantine gamma_I 24 (nu I) occurs directly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-lim
KIND: step
TITLE: Clause (2), frequency limit
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
CONTRACT_ID: stepW:w8:p-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (2): Tendsto nu (nhdsWithin 0 Gamma) (nhds fun i => lam m hm (i : Nat).succPNat / (2 * pi))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:limit, bpW:w8:patch-local, bpW:w8:freq-shell, bpW:w8:etor, bpW:w0:basis#lam, bpW:w8:shells
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:limit | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L579 | frequency limit
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L580-L580 | omega_* = omega^(n)_* on Gamma_n
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | (iii) e_n <= alpha_n
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | eps^(n)_omega <= alpha_n
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L582-L582 | lam m hm (i : Nat).succPNat occurs directly
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | alpha_n = (2^{-n} t_0)^{95/64} tends to zero
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-size
KIND: step
TITLE: Clause (3), size
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590
CONTRACT_ID: stepW:w8:p-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma, theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (3): ¦¦K_I(theta)¦¦ <= C_3 r(I) <= C r(I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-close, bpW:w8:shells, bpW:w8:shell-data, bpW:w7:shell-geom, bpW:w8:const, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | ¦¦K¦¦ <= 2 rho_n
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | rho_n
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | (i) rho_n^2 <= 2 c_A t_n
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L590-L590 | (iii)
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L590-L590 | C_3, C
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | K_I = K^(n)_I on its shell
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-meas
KIND: step
TITLE: \Lean{MeasurableSet $\Gamma$}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560
CONTRACT_ID: stepW:w8:p-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: MeasurableSet Gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 | via Step stepW:w8:pc-borel
EDGE: stepW:w8:pc-borel | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 | the explicitly cited Borel proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-incl
KIND: step
TITLE: $\Gamma\subseteq\{I\mid(\forall i,0<I_i)\wedge r(I)<r_0\}$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562
CONTRACT_ID: stepW:w8:p-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Gamma subset {I ¦ (forall i, 0 < I_i) and r(I) < r_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-incl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L561 | via Step stepW:w8:pc-incl
EDGE: stepW:w8:pc-incl | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L562-L562 | the explicitly cited inclusion proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-nucont
KIND: step
TITLE: \Lean{ContinuousOn $\nu$ $\Gamma$}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563
CONTRACT_ID: stepW:w8:p-nucont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ContinuousOn nu Gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-nu
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 | via Step stepW:w8:pc-nu
EDGE: stepW:w8:pc-nu | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 | the explicitly cited frequency continuity proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:p-Kcont
KIND: step
TITLE: \Lean{ContinuousOn (Function.uncurry K) ($\Gamma$ $\times^s$ Set.univ)}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565
CONTRACT_ID: stepW:w8:p-Kcont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ContinuousOn (Function.uncurry K) (Gamma x^s Set.univ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-K
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L564 | via Step stepW:w8:pc-K
EDGE: stepW:w8:pc-K | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L565-L565 | the explicitly cited family continuity proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:ni-same
KIND: step
TITLE: Same shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
CONTRACT_ID: stepW:w8:ni-same
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family; the enclosing implication premise nu(I) = nu(I'); local choices I in Gamma_n, I' in Gamma_{n'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n = n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:ni-diff
KIND: step
TITLE: Different shells
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
CONTRACT_ID: stepW:w8:ni-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family; the enclosing implication premise nu(I) = nu(I'); local choices I in Gamma_n, I' in Gamma_{n'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n != n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: omega^(n)_*(I) != omega^(n')_*(I')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:freqcoords, bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (ii) separation
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (iv)
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L511-L511 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:in-orbit
KIND: step
TITLE: Orbits
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527
CONTRACT_ID: stepW:w8:in-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family; the enclosing implication premise K_I(theta) = K_{I'}(theta'); local choices I in Gamma_n, I' in Gamma_{n'}, nu = nu(I), nu' = nu(I'), Psi = tilde Psi^(n)_I, Psi' = tilde Psi^(n')_{I'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y(t) = K_I(theta + t nu) and Y'(t) = K_{I'}(theta' + t nu') coincide
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding, bpW:w8:shell-inv, bpW:w8:patch-local, bpW:w2:orbit, bpW:w8:unique
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L524 | analyticity
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | (i) invariance
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | K_I = K^(n)_I, nu = nu^(n)_*
EDGE: bpW:w2:orbit | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | orbits are coefficient solutions
EDGE: bpW:w8:unique | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L527-L527 | uniqueness
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:in-birk
KIND: step
TITLE: Birkhoff coordinates
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530
CONTRACT_ID: stepW:w8:in-birk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family; the enclosing implication premise K_I(theta) = K_{I'}(theta'); local choices I in Gamma_n, I' in Gamma_{n'}, nu = nu(I), nu' = nu(I'), Psi = tilde Psi^(n)_I, Psi' = tilde Psi^(n')_{I'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Psi(theta + t nu) = Psi'(theta' + t nu') for all t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:in-orbit, bpW:w8#data, bpW:w8:torus-shape, bpW:w3:gamma-real, bpW:w3:coords, bpW:w8:Kshell
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:in-orbit | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L528 | Y = Y'
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | tau_E injective
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | (v)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | (iii)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L530-L530 | Z bijective
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L528 | K^(n)_I
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:in-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534
CONTRACT_ID: stepW:w8:in-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family; the enclosing implication premise K_I(theta) = K_{I'}(theta'); local choices I in Gamma_n, I' in Gamma_{n'}, nu = nu(I), nu' = nu(I'), Psi = tilde Psi^(n)_I, Psi' = tilde Psi^(n')_{I'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: nu(I) = nu(I')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:torus-shape, bpW:w8:winding, stepW:w8:in-birk
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L531 | (i), (ii)
EDGE: bpW:w8:winding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L533-L533 | winding
EDGE: stepW:w8:in-birk | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L531 | equal tori
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:in-act
KIND: step
TITLE: Actions
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535
CONTRACT_ID: stepW:w8:in-act
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family; the enclosing implication premise K_I(theta) = K_{I'}(theta'); local choices I in Gamma_n, I' in Gamma_{n'}, nu = nu(I), nu' = nu(I'), Psi = tilde Psi^(n)_I, Psi' = tilde Psi^(n')_{I'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:nu-injective, stepW:w8:in-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:nu-injective | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 | injectivity of nu
EDGE: stepW:w8:in-freq | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 | nu(I) = nu(I')
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:in-ang
KIND: step
TITLE: Angles
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537
CONTRACT_ID: stepW:w8:in-ang
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family; the enclosing implication premise K_I(theta) = K_{I'}(theta'); local choices I in Gamma_n, I' in Gamma_{n'}, nu = nu(I), nu' = nu(I'), Psi = tilde Psi^(n)_I, Psi' = tilde Psi^(n')_{I'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: theta - theta' in Z^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding, stepW:w8:in-act, bpW:w8:patch-local, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L537-L537 | third conjunct
EDGE: stepW:w8:in-act | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | I = I'
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | K_I = K^(n)_I
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint errata and deviations

No new suspected blueprint defect. The source states the equality premises used by the implication proofs; the graph step contexts omitted them.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.

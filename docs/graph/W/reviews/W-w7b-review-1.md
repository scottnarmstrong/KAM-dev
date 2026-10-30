# W-w7b: slice review 1

Reviewer: sol-review-W-w7b. Verdict: **FAIL**.

Read w7-measure.tex L460-L791 in full, with W7a context. Checked the preparatory 8/11 exponent, iterative 2/3 exponent, combined 32/47 exponent, shell trimming, ENNReal denominator, per-I Diophantine constant and period-one rescaling. No sineMode edge is warranted by phase phi; bare lambda in the source comparisons is the P96-K parameter.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes a02f1e7e6ccbd02d8b7cdb8a607323a7d4fc3dbdfddb65d8fb8694cbceec5f9f; coverage 3a91e9bffe5143b80c28c1a45a8976e4be7665ea4f1ef4665cf52e892ee37303.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w7:prep | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L462-L464; blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L465-L504 |
| stepW:w7:prep-0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468; blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468 |
| stepW:w7:prep-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473; blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473 |
| stepW:w7:prep-minus-group | FAIL | n <= ¦k¦/vartheta and the premise for applying zone are used without their suppliers. |
| stepW:w7:prep-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493; blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493 |
| stepW:w7:prep-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496; blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496 |
| stepW:w7:prep-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499; blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499 |
| stepW:w7:prep-sum | FAIL | The proof uses A_k's fixed exponent and C_P's definition without edges. |
| bpW:w7:iter | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L510-L514; blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L515-L544 |
| stepW:w7:it-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520; blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520 |
| stepW:w7:it-group | FAIL | The grouping uses nonempty-zone largek before the drift estimate, without that dependency. |
| stepW:w7:it-j0 | FAIL | The zone application outside X needs dichotomy, and the rounding/power comparison consumes the stated real-power external. |
| stepW:w7:it-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536; blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536 |
| stepW:w7:it-sum | FAIL | The lattice bound uses tau=24 and A_k, without their definition edge. |
| stepW:w7:it-X | FAIL | The number of iteration levels for each exceptional k comes from count(ii), and the cutoff comes from Xdef. |
| bpW:w7:measurable | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L550-L553; blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L554-L560 |
| stepW:w7:meas-cont | FAIL | The continuity claim uses phi_kl on its frequency-pair domain, defined in basic#data, without that edge. |
| stepW:w7:meas-union | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559; blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559 |
| bpW:w7:measure | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L563-L570; blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L571-L579 |
| stepW:w7:assemble | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576; blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576 |
| stepW:w7:return | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578; blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578 |
| bpW:w7:melnikov | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L585-L596; blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L597-L599 |
| bpW:w7:shells | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shells@L608-L612 |
| bpW:w7:shell-geom | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L616-L620; blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L621-L632 |
| stepW:w7:partition | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624; blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624 |
| stepW:w7:layer | FAIL | The strip-area and union bound use the listed measure externals but DEPS is empty. |
| stepW:w7:shell-size | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631; blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631 |
| bpW:w7:density | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L635-L642; blueprint-W/parts/w7-measure.tex#bpW:w7:density@L643-L657 |
| stepW:w7:den | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645; blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645 |
| stepW:w7:upper | FAIL | The ratio bound uses monotonicity and a positive finite denominator without either edge. |
| stepW:w7:lower | FAIL | The shell union estimate, denominator and subtraction/division identities are consumed without edges. |
| stepW:w7:limit | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656; blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656 |
| bpW:w7:shell-est | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L661-L667; blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L668-L673 |
| bpW:w7:exponents | FAIL | The source field turns the preceding measure theorem into a premise; the remark instead derives its fraction estimate from that result. |
| bpW:w7:dioph | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L697-L701; blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L702-L708 |
| stepW:w7:dioph-base | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705; blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705 |
| stepW:w7:dioph-scale | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707; blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707 |
| bpW:w7:dioph-use | FAIL | The cited final-frequency result supplies the displayed divisor bound; this is a use in a retained claim, not an excluded forward pointer. |
| bpW:w7:limit | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L720-L725; blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L726-L734 |
| stepW:w7:lim-index | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729; blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729 |
| stepW:w7:lim-est | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733; blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733 |
| bpW:w7:density-sec#data | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:density-sec@L604-L606 |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w7:prep | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L462-L464 |
| stepW:w7:prep-0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468 |
| stepW:w7:prep-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473 |
| stepW:w7:prep-minus-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481 |
| stepW:w7:prep-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493 |
| stepW:w7:prep-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496 |
| stepW:w7:prep-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499 |
| stepW:w7:prep-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503 |
| bpW:w7:iter | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L510-L514 |
| stepW:w7:it-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520 |
| stepW:w7:it-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526 |
| stepW:w7:it-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532 |
| stepW:w7:it-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536 |
| stepW:w7:it-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540 |
| stepW:w7:it-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543 |
| bpW:w7:measurable | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L550-L553 |
| stepW:w7:meas-cont | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557 |
| stepW:w7:meas-union | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559 |
| bpW:w7:measure | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L563-L570 |
| stepW:w7:assemble | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576 |
| stepW:w7:return | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578 |
| bpW:w7:melnikov | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L585-L596 |
| bpW:w7:shells | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shells@L608-L612 |
| bpW:w7:shell-geom | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L616-L620 |
| stepW:w7:partition | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624 |
| stepW:w7:layer | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629 |
| stepW:w7:shell-size | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631 |
| bpW:w7:density | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L635-L642 |
| stepW:w7:den | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645 |
| stepW:w7:upper | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647 |
| stepW:w7:lower | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653 |
| stepW:w7:limit | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656 |
| bpW:w7:shell-est | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L661-L667 |
| bpW:w7:exponents | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691 |
| bpW:w7:dioph | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L697-L701 |
| stepW:w7:dioph-base | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705 |
| stepW:w7:dioph-scale | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707 |
| bpW:w7:dioph-use | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718 |
| bpW:w7:limit | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L720-L725 |
| stepW:w7:lim-index | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729 |
| stepW:w7:lim-est | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733 |
| bpW:w7:errata | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:errata@L739-L777 |
| bpW:w7:interface | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:interface@L781-L791 |
| heading:bpW:w7:prep-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:prep-sec@L460-L460 |
| heading:bpW:w7:iter-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:iter-sec@L508-L508 |
| heading:bpW:w7:main-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:main-sec@L548-L548 |
| heading:bpW:w7:density-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:density-sec@L602-L602 |
| heading:bpW:w7:dioph-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-sec@L695-L695 |
| heading:bpW:w7:check | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:check@L737-L737 |
| heading:bpW:w7:summary | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:summary@L779-L779 |
| w7-measure:source-L505 | PASS | blueprint-W/parts/w7-measure.tex#source@L505-L505 |
| w7-measure:source-L545 | PASS | blueprint-W/parts/w7-measure.tex#source@L545-L545 |
| w7-measure:source-L561 | PASS | blueprint-W/parts/w7-measure.tex#source@L561-L561 |
| w7-measure:source-L580 | PASS | blueprint-W/parts/w7-measure.tex#source@L580-L580 |
| w7-measure:source-L600 | PASS | blueprint-W/parts/w7-measure.tex#source@L600-L600 |
| w7-measure:source-L613 | PASS | blueprint-W/parts/w7-measure.tex#source@L613-L613 |
| w7-measure:source-L633 | PASS | blueprint-W/parts/w7-measure.tex#source@L633-L633 |
| w7-measure:source-L658 | PASS | blueprint-W/parts/w7-measure.tex#source@L658-L658 |
| w7-measure:source-L674 | PASS | blueprint-W/parts/w7-measure.tex#source@L674-L674 |
| w7-measure:source-L692 | PASS | blueprint-W/parts/w7-measure.tex#source@L692-L692 |
| w7-measure:source-L709 | PASS | blueprint-W/parts/w7-measure.tex#source@L709-L709 |
| w7-measure:source-L735 | PASS | blueprint-W/parts/w7-measure.tex#source@L735-L735 |
| w7-measure:prose-L604-L606 | PASS | blueprint-W/parts/w7-measure.tex#prose@L604-L606 |

all other coverage items PASS.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: stepW:w7:prep-minus-group
KIND: step
TITLE: $\Lambda^-$, grouping
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481
CONTRACT_ID: stepW:w7:prep-minus-group
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: grouping of the Lambda^- zones by n = i - j and the inclusion S_{k,ij} subset Q_{knj} subset Q_{knj_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone, bpW:w7:unpert-bounds, bpW:w7:largek, bpW:w7:dichotomy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L477-L477 | zone estimate
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L479-L479 | (iii)
EDGE: bpW:w7:largek | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L476-L477 | nonempty S forces n <= ¦k¦/vartheta
EDGE: bpW:w7:dichotomy | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L477-L478 | outside X supplies the zone lemma's lower bound on ¦k¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:it-group
KIND: step
TITLE: $\Lambda^-$, grouping with drift
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526
CONTRACT_ID: stepW:w7:it-group
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: R^nu_{k,ij} subset Q_{knj}, decreasing in j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:unpert-bounds, bpW:w7:largek
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L522-L522 | (H2)
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L522-L522 | (iii)
EDGE: bpW:w7:largek | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L522-L522 | n <= ¦k¦/vartheta, otherwise the zone is empty
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:it-j0
KIND: step
TITLE: $\Lambda^-$, choice of $j_0$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532
CONTRACT_ID: stepW:w7:it-j0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with j_0 = ceil((A_k/check alpha)^{1/3}) the bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone, stepW:w7:it-group, bpW:w7:dichotomy, bpW:w7:ext-ennreal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L528-L528 | zone estimate
EDGE: stepW:w7:it-group | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L529-L529 | the grouping
EDGE: bpW:w7:dichotomy | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L528-L530 | outside X discharges the nonconstant-psi premise of zone
EDGE: bpW:w7:ext-ennreal | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L528-L532 | ceil rounding and real-power comparisons for j_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:prep-sum
KIND: step
TITLE: Sum over $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503
CONTRACT_ID: stepW:w7:prep-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over k gives the bound with C_P; Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:count, bpW:w7:measurable, stepW:w7:prep-0, stepW:w7:prep-plus, stepW:w7:prep-n, stepW:w7:prep-X, bpW:w7:indexdef, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L502-L502 | (iii)
EDGE: bpW:w7:measurable | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L503-L503 | Borel
EDGE: stepW:w7:prep-0 | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | l = 0
EDGE: stepW:w7:prep-plus | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | Lambda^+
EDGE: stepW:w7:prep-n | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | Lambda^-
EDGE: stepW:w7:prep-X | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L502-L502 | X
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | A_k >= ¦k¦^24
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L502-L502 | the coefficient C_P of (C5)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:it-X
KIND: step
TITLE: Exceptional zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543
CONTRACT_ID: stepW:w7:it-X
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the exceptional zones; Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xzones, bpW:w7:measurable, bpW:w7:count, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xzones | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L542-L542 | a = check alpha
EDGE: bpW:w7:measurable | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L543-L543 | Borel
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L542-L542 | each k occurs for at most ¦k¦ levels
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L542-L542 | ¦k¦ < K_* on X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:it-sum
KIND: step
TITLE: Sum over $\nu$ and $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540
CONTRACT_ID: stepW:w7:it-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over nu and k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:count, stepW:w7:it-n, stepW:w7:it-plus, bpW:w7:indexdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L538-L538 | (ii), (iii)
EDGE: stepW:w7:it-n | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L539-L539 | per k
EDGE: stepW:w7:it-plus | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L539-L539 | per k
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L539-L539 | tau = 24 and A_k >= ¦k¦^24
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:layer
KIND: step
TITLE: Boundary layer
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629
CONTRACT_ID: stepW:w7:layer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:shell-geom: the shells of Definition bpW:w7:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:shell-geom (k; 0 < a <= t_k); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) the boundary layer bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-ball, bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-ball | blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L628-L629 | areas of the rectangular strips and squares
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L628-L629 | finite subadditivity and monotonicity for the covering
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:upper
KIND: step
TITLE: Upper bound
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647
CONTRACT_ID: stepW:w7:upper
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); within the step: h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the ratio is <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel, stepW:w7:den, bpW:w7:ext-ennreal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L647-L647 | measure monotonicity for Gamma cap B_h subset (0,h)^2
EDGE: stepW:w7:den | blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L647-L647 | the denominator is h^2 in (0,infinity)
EDGE: bpW:w7:ext-ennreal | blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L647-L647 | division preserves the ratio bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:lower
KIND: step
TITLE: Lower bound
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653
CONTRACT_ID: stepW:w7:lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); within the step: h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb(Gamma cap B_h) >= h^2(1 - bar eps_k/q^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-geom, bpW:w7:ext-borel, stepW:w7:den, bpW:w7:ext-ennreal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L650-L650 | (i)
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L651-L653 | measure of the countable shell cover and complement
EDGE: stepW:w7:den | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L653-L653 | the denominator and box measure are h^2
EDGE: bpW:w7:ext-ennreal | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L653-L653 | the finite-measure complement and quotient identities
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:dioph-use
KIND: claim
TITLE: Use in clause (2)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718
CONTRACT_ID: bpW:w7:dioph-use
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the final parameter set of a shell in W6's wave iteration; per-shell levels alpha_k as in the preceding shell setting
SOURCE_QUANTIFIERS: I in that shell's part of Gamma
SOURCE_CONCLUSION: W6 final-freq supplies ¦<k,omega_*>¦ >= check alpha/(2 A_k); with c = check alpha/2, gamma_I = check alpha_k/(8 pi) > 0 gives IsDiophantine gamma_I 24 nu(I) on the shell; gamma_I is chosen per shell and tends to zero with its level
CONSTANT_SCOPE: gamma_I per shell
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:dioph, bpW:w6:final-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:dioph | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L715-L715 | with c = check alpha/2
EDGE: bpW:w6:final-freq | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L714-L715 | the final l=0 divisor bound supplying c = check alpha/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Retained because W8 consumes the explicit per-shell gamma_I. The W6 final-frequency lemma is a direct supplier of the displayed bound; this node is not used to prove that W6 result.
```

```text
NODE: bpW:w7:exponents
KIND: claim
TITLE: Scaling with the action radius; admissible choices of $\alpha$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691
CONTRACT_ID: bpW:w7:exponents
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: an action box of side t > 0 with tangential amplitude of order sqrt(t); KP96 scaling t = r^{2 lambda}, lambda = 2/3, and KAM smallness alpha >= c_1 t^{3/2}
SOURCE_QUANTIFIERS: t -> 0
SOURCE_CONCLUSION: the excluded fraction is <= C alpha^{32/47}/t; density needs alpha = o(t^{47/32}); the admissible window is t^{3/2} <~ alpha = o(t^{47/32}); the explicit choice alpha(t) = t^{95/64} gives alpha^{32/47}/t = t^{1/94} -> 0, t^{3/2}/alpha = t^{1/64} -> 0 and alpha(t) <= t for t <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:measure, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:measure | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L679-L679 | the exponent 32/47
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L678-L678 | N_A, D_A
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: W8 cites it (4x) for the choice alpha(t) = t^{95/64}.
```

```text
NODE: stepW:w7:meas-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557
CONTRACT_ID: stepW:w7:meas-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:measurable: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:measurable (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each phi_kl is continuous on its Borel domain
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:omega0, bpW:w7:family, bpW:w7:basic#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L556-L556 | affine
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L556-L556 | (H1)-(H2)
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L557-L557 | the phase phi_kl and its frequency-pair domain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint errata and deviations

No new suspected blueprint defect. W7 L739-L777 records the source's existing P96-K findings; those are provenance, not newly verified paper errata in this review.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.
